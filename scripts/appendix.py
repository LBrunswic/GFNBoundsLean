#!/usr/bin/env python3
"""Build an appendix that is an account of the Lean development.

Not of `app_doubling.tex`. The appendix's prose proofs are not machine-checked and are not the
reliable artifact; the development is. So the statements here are the Lean statements, the
sketches are drawn from the Lean proofs, and both are checked against the environment rather
than taken on trust.

Three inputs:

  * `docs/lean-facts.json`   written by `scripts/lean_facts.lean` from the compiled environment:
                             types, docstrings, axioms, and the project constants each proof
                             term actually invokes.
  * `blueprint/exposition/`  the authored English, one file per headline theorem.
  * `scripts/proof_skeleton.py`  the shape of each proof, read from source.

The point of the arrangement is the lint. A sketch may not cite a lemma the proof does not
invoke, and may not silently drop one it does; an exposition file whose theorem has changed
shape since it was written is stale and says so. "Derived from the Lean proof" is therefore a
property this checks, not a claim it makes.

Usage:
    python3 scripts/appendix.py                    # regenerate content.tex
    python3 scripts/appendix.py --paper            # also the paper-ready fragment
    python3 scripts/appendix.py --skeleton <decl>  # the Lean-derived draft, to seed a file
    python3 scripts/appendix.py --lint             # the six gates
    python3 scripts/appendix.py --check            # fail if content.tex is out of date
"""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import dataclass
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from proof_skeleton import skeleton  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


@dataclass
class Chapter:
    """One namespace of the development, read as one chapter of the appendix."""
    id: str
    namespace: str            # e.g. "GFNBounds.Doubling", without the trailing dot
    title: str
    label: str
    sections: list[tuple[str, list[str]]]
    front: str = ""           # file in the exposition directory, or ""
    differences: str = ""

    @property
    def ns(self) -> str:
        return self.namespace + "."

    @property
    def headlines(self) -> list[str]:
        return [self.ns + n for _, names in self.sections for n in names]


@dataclass
class Config:
    """Where everything lives and what the document contains.

    Defaults reproduce the Doubling-only appendix exactly; `--config` supplies any other shape.
    Threading this through `emit`/`lint`/`write_graph` is what let the generator grow past one
    namespace without a second implementation.
    """
    chapters: list[Chapter]
    facts: Path = ROOT / "docs" / "lean-facts.json"
    expo: Path = ROOT / "blueprint" / "exposition"
    out: Path = ROOT / "blueprint" / "src" / "content.tex"
    out_paper: Path = ROOT / "blueprint" / "appendix_H.tex"
    out_graph: Path = ROOT / "docs" / "lean-graph.dot"
    lean_root: Path = ROOT
    title_macro: str = "\\appendixHtitle"
    title_plain: str = ("The doubling graph: an unbounded diffusion operator at finite "
                        "backward length")
    label: str = "app:doubling"

    @property
    def headlines(self) -> list[str]:
        return [d for c in self.chapters for d in c.headlines]

    def chapter_of(self, decl: str) -> Chapter | None:
        return next((c for c in self.chapters if decl.startswith(c.ns)), None)

    @property
    def single(self) -> bool:
        """One chapter needs no nesting level, so it keeps the headings it always had."""
        return len(self.chapters) == 1


# The document, in the order it reads.  Each headline theorem is a `main_*` of Main.lean; the
# grouping is the development's own, not the appendix's.
DOUBLING_SECTIONS: list[tuple[str, list[str]]] = [
    ("The chain, and when it settles", [
        "main_irreducible",
        "main_phase",
    ]),
    ("The invariant measure", [
        "main_invariant_measure",
        "main_constant_determined",
        "main_constant_functional",
    ]),
    ("The backward length", [
        "main_sigmaBar_eq",
        "main_sigmaBar_le",
    ]),
    ("The diffusion operator", [
        "main_unbounded",
        "main_unbounded_infty",
        "main_unbounded_two",
        "main_rate",
    ]),
    ("Flow matching", [
        "main_unsolvable",
    ]),
    ("The truncation", [
        "main_truncation_irreducible",
        "main_truncation_bhat",
        "main_truncation_sqrtK",
    ]),
]

DEFAULT_CONFIG = Config(chapters=[
    Chapter(id="doubling", namespace="GFNBounds.Doubling",
            title="The doubling graph", label="sec:doubling_results",
            sections=DOUBLING_SECTIONS, front="_front.tex",
            differences="_differences.tex"),
])


def load_config(path: Path | None) -> Config:
    """Read `appendix.toml`, or return the built-in Doubling configuration.

    The built-in is not a fallback so much as the regression test: with no `--config`, this
    generator must still produce exactly the file it produced before it learned about chapters.
    """
    if path is None:
        return DEFAULT_CONFIG
    import tomllib
    raw = tomllib.loads(path.read_text())
    base = path.resolve().parent
    paths = raw.get("paths", {})

    def where(key: str, default: Path) -> Path:
        return (base / paths[key]).resolve() if key in paths else default

    chapters = []
    for c in raw.get("chapter", []):
        chapters.append(Chapter(
            id=c["id"], namespace=c["namespace"], title=c["title"],
            label=c.get("label", f"sec:{c['id']}_results"),
            sections=[(s["title"], s["decls"]) for s in c.get("section", [])],
            front=c.get("front", ""), differences=c.get("differences", ""),
        ))
    if not chapters:
        sys.exit(f"{path}: no [[chapter]] entries")
    doc = raw.get("document", {})
    return Config(
        chapters=chapters,
        facts=where("facts", DEFAULT_CONFIG.facts),
        expo=where("exposition", DEFAULT_CONFIG.expo),
        out=where("out", DEFAULT_CONFIG.out),
        out_paper=where("out_paper", DEFAULT_CONFIG.out_paper),
        out_graph=where("out_graph", DEFAULT_CONFIG.out_graph),
        lean_root=where("lean_root", DEFAULT_CONFIG.lean_root),
        title_macro=doc.get("title_macro", DEFAULT_CONFIG.title_macro),
        title_plain=doc.get("title_plain", DEFAULT_CONFIG.title_plain),
        label=doc.get("label", DEFAULT_CONFIG.label),
    )


STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Language that belongs in the repository, not in a published appendix.
DENYLIST = [
    (r"\d{4}-\d\d-\d\d", "a date"),
    (r"\bbucket [A-D]\b", "a difficulty bucket"),
    (r"\bsorry\b", "the word sorry"),
    (r"\.lean\b", "a source file name"),
    (r"machine-checked", "the phrase machine-checked"),
    (r"\bDEFERRED\b", "the word DEFERRED"),
    (r"\bHARD\b", "the word HARD"),
    (r"⚠", "a warning sign"),
    (r"paper-map", "the paper map"),
    (r"trace_check", "the trace checker"),
    (r"\bcertifying\b", "the word certifying"),
    (r"\boverclaim\b", "the word overclaim"),
]

CITE = re.compile(r"\[\[([A-Za-z0-9_.']+)\]\]")


# --------------------------------------------------------------------------
# inputs
# --------------------------------------------------------------------------

def load_facts(cfg: Config) -> dict:
    if not cfg.facts.exists():
        sys.exit(f"{cfg.facts} is missing; run `lake env lean scripts/lean_facts.lean`")
    return json.loads(cfg.facts.read_text())["declarations"]


def sig_hash(facts: dict, decl: str) -> str:
    return hashlib.sha256(facts[decl]["type"].encode("utf8")).hexdigest()[:16]


def is_named_result(rec: dict) -> bool:
    """The house marker: a docstring opening in bold is the library calling this a result."""
    return (rec.get("doc") or "").lstrip().startswith("**")


def work_deps(facts: dict, decl: str) -> list[str]:
    """What the proof invokes that the statement does not already mention.

    A theorem's type is its statement, so constants shared by type and value are vocabulary.
    What is left is the argument.
    """
    rec = facts[decl]
    vocab = set(rec["uses_type"])
    return [u for u in rec["uses_value"] if u not in vocab]


def closure(facts: dict, decl: str) -> set[str]:
    """Every project declaration the proof rests on, unfolded all the way down."""
    seen: set[str] = set()
    stack = [decl]
    while stack:
        d = stack.pop()
        for u in facts.get(d, {}).get("uses_value", []):
            if u not in seen:
                seen.add(u)
                stack.append(u)
    return seen


def reachable(facts: dict, decl: str, depth: int = 3) -> set[str]:
    """Everything the proof rests on, to a bounded depth of unfolding."""
    seen, frontier = set(), {decl}
    for _ in range(depth):
        nxt = set()
        for d in frontier:
            for u in facts.get(d, {}).get("uses_value", []):
                if u not in seen:
                    seen.add(u)
                    nxt.add(u)
        frontier = nxt
        if not frontier:
            break
    return seen


# --------------------------------------------------------------------------
# the exposition layer
# --------------------------------------------------------------------------

def read_exposition(cfg: Config, decl: str) -> dict | None:
    path = cfg.expo / f"{decl}.md"
    if not path.exists():
        return None
    text = path.read_text(encoding="utf8")
    meta: dict[str, str] = {}
    if text.startswith("---"):
        head, _, text = text[3:].partition("---")
        for line in head.strip().split("\n"):
            if ":" in line:
                k, _, v = line.partition(":")
                meta[k.strip()] = v.strip()
    body: dict[str, str] = {}
    current = None
    for line in text.split("\n"):
        m = re.match(r"^##\s+(\w+)\s*$", line)
        if m:
            current = m.group(1)
            body[current] = ""
        elif current:
            body[current] += line + "\n"
    return {"meta": meta, **{k: v.strip() for k, v in body.items()}, "path": path}


def render_citations(cfg: Config, text: str, facts: dict, here: Chapter | None = None) -> str:
    """`[[GFNBounds.Doubling.foo]]` -> a rendered reference to the declaration.

    Within a chapter the namespace is dropped, as it always was. Across chapters it is not: a
    bare `main_rate` stops being unique the moment a second namespace joins the document, so a
    citation reaching out of its chapter keeps the last two components (`Doubling.main_rate`).
    """
    def one(m):
        name = m.group(1)
        owner = cfg.chapter_of(name)
        if here is not None and owner is not here and owner is not None:
            short = ".".join(name.split(".")[-2:])
        else:
            short = name.replace(here.ns if here else "", "")
        return "\\leanref{%s}" % short.replace("_", r"\_")
    return CITE.sub(one, text)


# --------------------------------------------------------------------------
# the Lean-derived draft, for seeding an exposition file
# --------------------------------------------------------------------------

def print_skeleton(cfg: Config, facts: dict, decl: str) -> None:
    full = decl if decl in facts else next(
        (c.ns + decl for c in cfg.chapters if c.ns + decl in facts), decl)
    rec = facts.get(full)
    if rec is None:
        sys.exit(f"unknown declaration: {decl}")
    named = {k for k, v in facts.items() if is_named_result(v)}
    shorts = {k.split(".")[-1] for k in named}

    print(f"---\ndeclaration: {full}\nsig_sha256: {sig_hash(facts, full)}\n---")
    print("\n## statement\n")
    print(f"% Lean type:\n%   {rec['type']}")
    print(f"% docstring:\n%   {' '.join((rec['doc'] or '').split())}")
    print("\n## relation\n%   (how this bears on the main text)")
    print("\n## sketch\n")

    s = skeleton(rec["module"], full, shorts)
    for st in s["steps"]:
        if st["plumbing"]:
            continue
        print(f"%  step  {st['name']}: {st['claim'][:100]}")
        if st["invokes"]:
            print(f"%        via {', '.join(st['invokes'])}")
    if s["conclusion"]:
        print(f"%  concludes: {s['conclusion'][:200]}")

    print("%\n%  named results this proof invokes:")
    for u in work_deps(facts, full):
        if is_named_result(facts.get(u, {})):
            lead = " ".join((facts[u]["doc"] or "").split())
            print(f"%    [[{u}]]")
            print(f"%        {lead[:110]}")


# --------------------------------------------------------------------------
# the gates
# --------------------------------------------------------------------------

def unattached(cfg: Config, facts: dict) -> list[str]:
    """Gate 7: a certified named theorem that no chapter reaches.

    The house rule is that the appendix accounts for the development. A theorem the library
    itself calls a result (docstring opening in bold), living in a namespace the document
    covers, but reachable from no headline, is a result the paper silently omits -- which is
    the one failure this arrangement cannot detect any other way.
    """
    covered: set[str] = set()
    for decl in cfg.headlines:
        covered |= closure(facts, decl) | {decl}
    out = []
    for name, rec in facts.items():
        if not name.startswith(tuple(c.ns for c in cfg.chapters)):
            continue
        if rec.get("kind") == "theorem" and is_named_result(rec) and name not in covered:
            out.append(name)
    return sorted(out)


def lint(cfg: Config, facts: dict, strict_unattached: bool = False) -> list[str]:
    problems: list[str] = []
    for decl in cfg.headlines:
        if decl not in facts:
            problems.append(f"{decl}: not in the environment")
            continue
        rec = facts[decl]

        extra = set(rec["axioms"]) - STD_AXIOMS
        if extra:
            problems.append(f"{decl}: rests on {sorted(extra)}")

        expo = read_exposition(cfg, decl)
        if expo is None:
            problems.append(f"{decl}: no exposition file — write "
                            f"{(cfg.expo / (decl + '.md'))}")
            continue
        for section in ("statement", "relation", "sketch"):
            if not expo.get(section):
                problems.append(f"{decl}: exposition has no '{section}' section")

        want = sig_hash(facts, decl)
        got = expo["meta"].get("sig_sha256")
        if got != want:
            problems.append(f"{decl}: statement has changed since the text was written "
                            f"(recorded {got}, current {want})")

        cited = set(CITE.findall(expo.get("sketch", "") + expo.get("statement", "")
                                 + expo.get("relation", "")))
        support = reachable(facts, decl)
        for c in sorted(cited):
            if c not in facts:
                problems.append(f"{decl}: cites {c}, which is not a declaration")
            elif c not in support and c != decl:
                problems.append(f"{decl}: cites {c}, which its proof does not invoke")

        for u in work_deps(facts, decl):
            rec_u = facts.get(u, {})
            # Definitions are vocabulary a sketch may or may not want to name; a *theorem* the
            # proof leans on is a step, and leaving it out misrepresents the argument.
            if (is_named_result(rec_u) and rec_u.get("kind") == "theorem"
                    and u not in cited):
                problems.append(f"{decl}: proof invokes {u} and the sketch does not name it")

    for path in (cfg.out, cfg.out_paper):
        body = path.read_text() if path.exists() else ""
        stripped = re.sub(r"^%.*$", "", body, flags=re.M)
        for pat, what in DENYLIST:
            for m in re.finditer(pat, stripped):
                line = stripped[: m.start()].count("\n") + 1
                problems.append(f"{path.name}:{line}: {what}")

    orphans = unattached(cfg, facts)
    if orphans:
        listed = (cfg.expo.parent / "UNATTACHED")
        known = set(listed.read_text().split()) if listed.exists() else set()
        new = [o for o in orphans if o not in known]
        for o in new:
            msg = f"{o}: a named theorem no chapter reaches"
            problems.append(msg) if strict_unattached else print(
                f"lint: warning: {msg}", file=sys.stderr)
    return problems


# --------------------------------------------------------------------------
# emitting
# --------------------------------------------------------------------------

def esc(s: str) -> str:
    return (s.replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("&", r"\&")
             .replace("%", r"\%").replace("#", r"\#").replace("$", r"\$")
             .replace("{", r"\{").replace("}", r"\}").replace("^", r"\textasciicircum{}")
             .replace("~", r"\textasciitilde{}"))


def preamble(cfg: Config, facts: dict, paper_mode: bool) -> str:
    head = (f"\\section{{{cfg.title_macro}}}\\label{{{cfg.label}}}" if paper_mode else
            f"\\section{{{cfg.title_plain}}}\\label{{{cfg.label}}}")
    if cfg.single:
        # One chapter carries the document, so its front matter is the document's and there is
        # no nesting level to introduce.
        front = cfg.expo / cfg.chapters[0].front if cfg.chapters[0].front else None
        text = front.read_text(encoding="utf8").strip() if front and front.exists() else ""
        return head + "\n\n" + text + "\n"
    return head + "\n"


def emit(cfg: Config, facts: dict, paper_mode: bool) -> tuple[str, list[str]]:
    out = [preamble(cfg, facts, paper_mode)]
    missing: list[str] = []

    for chapter in cfg.chapters:
        if cfg.single:
            out.append(f"\n\\subsection{{The results}}\\label{{{chapter.label}}}\n")
        else:
            out.append(f"\n\\subsection{{{chapter.title}}}\\label{{{chapter.label}}}\n")
            front = cfg.expo / chapter.front if chapter.front else None
            if front and front.exists():
                out.append(front.read_text(encoding="utf8").strip() + "\n")

        for title, names in chapter.sections:
            out.append(f"\n\\subsubsection{{{title}}}\n")
            for short in names:
                decl = chapter.ns + short
                expo = read_exposition(cfg, decl)
                if expo is None:
                    missing.append(decl)
                    continue
                out.append(f"\n\\begin{{theorem}}\n  \\label{{thm:{short}}}")
                if not paper_mode:
                    out.append(f"  \\lean{{{decl}}}\\leanok")
                out.append(render_citations(cfg, expo["statement"], facts, chapter))
                out.append("\\end{theorem}\n")
                out.append("\\begin{proof}")
                if not paper_mode:
                    out.append("  \\leanok")
                out.append(render_citations(cfg, expo["sketch"], facts, chapter))
                out.append("\\end{proof}\n")
                out.append("\\noindent "
                           + render_citations(cfg, expo["relation"], facts, chapter) + "\n")

        diffs = cfg.expo / chapter.differences if chapter.differences else None
        if diffs and diffs.exists():
            out.append("\n" + diffs.read_text(encoding="utf8").strip() + "\n")

    out.append(index_section(cfg, facts))
    return "\n".join(out) + "\n", missing


def index_section(cfg: Config, facts: dict) -> str:
    rows = []
    for chapter in cfg.chapters:
        if not cfg.single:
            rows.append("\\multicolumn{4}{@{}l}{\\itshape %s} \\\\" % esc(chapter.title))
        for _, names in chapter.sections:
            for short in names:
                decl = chapter.ns + short
                rec = facts[decl]
                deep = closure(facts, decl)
                named = sum(1 for u in deep if is_named_result(facts.get(u, {})))
                rows.append("\\ref{thm:%s} & \\texttt{\\small %s} & %d & %d \\\\"
                            % (short, esc(short), named, len(deep)))
    body = "\n".join(rows)
    ns_list = [f"\\texttt{{{esc(c.namespace)}}}" for c in cfg.chapters]
    namespaces = ("namespace " + ns_list[0] if len(ns_list) == 1
                  else "namespaces " + ", ".join(ns_list[:-1]) + " and " + ns_list[-1])
    return rf"""
\subsection{{The development}}\label{{sec:doubling_development}}

Each result above is a declaration of a Lean~4 development checked against Mathlib
\texttt{{v4.31.0}}. Table~\ref{{tab:doubling_decls}} gives the correspondence. Every one of them
has been verified to rest on no axiom beyond Lean's own \texttt{{propext}},
\texttt{{Classical.choice}} and \texttt{{Quot.sound}}, and the development contains no unproved
goal.

\begin{{table}}[htb]
\centering
\small
\begin{{tabular}}{{@{{}}l l r r@{{}}}}
\hline
result & declaration & named results & declarations \\
\hline
{body}
\hline
\end{{tabular}}
\caption{{The results of this appendix as declarations of the Lean development, in the
{namespaces}. The last two columns count what each proof rests on,
unfolded to the bottom of the development: the declarations it reaches, and how many of those
are results the development names rather than steps internal to one.}}
\label{{tab:doubling_decls}}
\end{{table}}
"""


def write_graph(cfg: Config, facts: dict) -> Path:
    """The verified dependency graph: the headline results and what their proofs invoke.

    Edges are `uses_value` from the compiled environment, so an arrow means the proof term of
    the tail really does mention the head. Nodes are the fifteen results and the declarations
    the development itself names as results; the plumbing beneath them is counted in the
    closing table, not drawn.
    """
    lines = ["digraph development {",
             '  rankdir=LR; bgcolor="transparent";',
             '  node [shape=box, fontname="Helvetica", fontsize=10];',
             '  edge [color="#555555", arrowsize=0.7];']

    def node_id(name: str) -> str:
        """Unique across chapters. `main_rate` stops being unique at the second namespace."""
        c = cfg.chapter_of(name)
        if cfg.single or c is None:
            return name.replace(cfg.chapters[0].ns, "")
        return ".".join(name.split(".")[-2:])

    drawn: set[str] = set()
    fills = ["#d8ecd8", "#dbe6f5", "#f5e6d0", "#e8dcf0", "#f0dcdc"]
    for i, chapter in enumerate(cfg.chapters):
        if not cfg.single:
            lines.append(f'  subgraph cluster_{chapter.id} {{')
            lines.append(f'    label="{chapter.title}"; fontname="Helvetica"; '
                         f'fontsize=11; color="#999999";')
        for decl in chapter.headlines:
            nid = node_id(decl)
            indent = "    " if not cfg.single else "  "
            lines.append(f'{indent}"{nid}" [style=filled, fillcolor="{fills[i % len(fills)]}", '
                         f'fontsize=11];')
            drawn.add(nid)
        if not cfg.single:
            lines.append("  }")

    for chapter in cfg.chapters:
        for decl in chapter.headlines:
            for u in work_deps(facts, decl):
                rec = facts.get(u, {})
                if not is_named_result(rec) or rec.get("kind") != "theorem":
                    continue
                us, ds = node_id(u), node_id(decl)
                if us not in drawn:
                    lines.append(f'  "{us}" [fillcolor="#eeeeee", style=filled];')
                    drawn.add(us)
                # An edge leaving its chapter is drawn heavier: those are the places where one
                # part of the development actually stands on another, and they are the story.
                owner = cfg.chapter_of(u)
                cross = owner is not None and owner is not chapter
                attr = ' [penwidth=2.0, color="#333333"]' if cross else ""
                lines.append(f'  "{ds}" -> "{us}"{attr};')
    lines.append("}")
    cfg.out_graph.parent.mkdir(parents=True, exist_ok=True)
    cfg.out_graph.write_text("\n".join(lines) + "\n")
    return cfg.out_graph


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--skeleton", metavar="DECL",
                   help="print the Lean-derived draft for one theorem")
    p.add_argument("--lint", action="store_true", help="run the gates")
    p.add_argument("--check", action="store_true", help="fail if content.tex is out of date")
    p.add_argument("--paper", action="store_true", help="also write the paper-ready fragment")
    p.add_argument("--graph", action="store_true",
                   help="write docs/lean-graph.dot, the verified dependency graph")
    p.add_argument("--config", metavar="TOML", type=Path,
                   help="chapter configuration; without it, the built-in Doubling appendix")
    p.add_argument("--strict-unattached", action="store_true",
                   help="fail, rather than warn, on a named theorem no chapter reaches")
    args = p.parse_args()

    cfg = load_config(args.config)
    facts = load_facts(cfg)

    def rel(path: Path) -> str:
        try:
            return str(path.relative_to(ROOT))
        except ValueError:
            return str(path)

    if args.skeleton:
        print_skeleton(cfg, facts, args.skeleton)
        return 0

    if args.lint:
        problems = lint(cfg, facts, strict_unattached=args.strict_unattached)
        if problems:
            print("lint: %d problem(s)" % len(problems), file=sys.stderr)
            for q in problems:
                print("  " + q, file=sys.stderr)
            return 1
        print(f"lint: clean — {len(cfg.headlines)} results in {len(cfg.chapters)} chapter(s), "
              "statements current, every sketch supported by the proof it describes")
        return 0

    text, missing = emit(cfg, facts, paper_mode=False)
    if missing:
        print("missing exposition — write these files:", file=sys.stderr)
        for m in missing:
            print(f"  {cfg.expo / (m + '.md')}", file=sys.stderr)
        return 1

    if args.check:
        stale = []
        if not cfg.out.exists() or cfg.out.read_text() != text:
            stale.append(rel(cfg.out))
        if args.paper:
            ptext, _ = emit(cfg, facts, paper_mode=True)
            if not cfg.out_paper.exists() or cfg.out_paper.read_text() != ptext:
                stale.append(rel(cfg.out_paper))
        if stale:
            print(f"out of date: {', '.join(stale)}; run scripts/appendix.py", file=sys.stderr)
            return 1
        print("appendix up to date")
        return 0

    cfg.out.parent.mkdir(parents=True, exist_ok=True)
    cfg.out.write_text(text)
    print(f"wrote {rel(cfg.out)} — {len(cfg.headlines)} results")

    if args.paper:
        ptext, _ = emit(cfg, facts, paper_mode=True)
        cfg.out_paper.parent.mkdir(parents=True, exist_ok=True)
        cfg.out_paper.write_text(ptext)
        print(f"wrote {rel(cfg.out_paper)} — paper-ready fragment")
    if args.graph:
        g = write_graph(cfg, facts)
        print(f"wrote {rel(g)} — the verified dependency graph")
    return 0


if __name__ == "__main__":
    sys.exit(main())
