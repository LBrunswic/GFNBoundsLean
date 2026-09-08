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
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from proof_skeleton import skeleton  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
FACTS = ROOT / "docs" / "lean-facts.json"
EXPO = ROOT / "blueprint" / "exposition"
OUT = ROOT / "blueprint" / "src" / "content.tex"
OUT_PAPER = ROOT / "blueprint" / "appendix_H.tex"

NS = "GFNBounds.Doubling."

# The document, in the order it reads.  Each headline theorem is a `main_*` of Main.lean; the
# grouping is the development's own, not the appendix's.
SECTIONS: list[tuple[str, list[str]]] = [
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

HEADLINES = [NS + n for _, names in SECTIONS for n in names]

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

def load_facts() -> dict:
    if not FACTS.exists():
        sys.exit("docs/lean-facts.json is missing; run `lake env lean scripts/lean_facts.lean`")
    return json.loads(FACTS.read_text())["declarations"]


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

def read_exposition(decl: str) -> dict | None:
    path = EXPO / f"{decl}.md"
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


def render_citations(text: str, facts: dict) -> str:
    """`[[GFNBounds.Doubling.foo]]` -> a rendered reference to the declaration."""
    def one(m):
        name = m.group(1)
        return "\\leanref{%s}" % name.replace(NS, "").replace("_", r"\_")
    return CITE.sub(one, text)


# --------------------------------------------------------------------------
# the Lean-derived draft, for seeding an exposition file
# --------------------------------------------------------------------------

def print_skeleton(facts: dict, decl: str) -> None:
    rec = facts.get(decl) or facts.get(NS + decl)
    if rec is None:
        sys.exit(f"unknown declaration: {decl}")
    full = decl if decl in facts else NS + decl
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

def lint(facts: dict) -> list[str]:
    problems: list[str] = []
    for decl in HEADLINES:
        if decl not in facts:
            problems.append(f"{decl}: not in the environment")
            continue
        rec = facts[decl]

        extra = set(rec["axioms"]) - STD_AXIOMS
        if extra:
            problems.append(f"{decl}: rests on {sorted(extra)}")

        expo = read_exposition(decl)
        if expo is None:
            problems.append(f"{decl}: no exposition file — write "
                            f"blueprint/exposition/{decl}.md")
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

    body = OUT.read_text() if OUT.exists() else ""
    stripped = re.sub(r"^%.*$", "", body, flags=re.M)
    for pat, what in DENYLIST:
        for m in re.finditer(pat, stripped):
            line = stripped[: m.start()].count("\n") + 1
            problems.append(f"content.tex:{line}: {what}")
    return problems


# --------------------------------------------------------------------------
# emitting
# --------------------------------------------------------------------------

def esc(s: str) -> str:
    return (s.replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("&", r"\&")
             .replace("%", r"\%").replace("#", r"\#").replace("$", r"\$")
             .replace("{", r"\{").replace("}", r"\}").replace("^", r"\textasciicircum{}")
             .replace("~", r"\textasciitilde{}"))


def preamble(facts: dict, paper_mode: bool) -> str:
    front = EXPO / "_front.tex"
    text = front.read_text(encoding="utf8").strip() if front.exists() else ""
    head = ("\\section{\\appendixHtitle}\\label{app:doubling}" if paper_mode else
            "\\section{The doubling graph: an unbounded diffusion operator at finite "
            "backward length}\\label{app:doubling}")
    return head + "\n\n" + text + "\n"


def emit(facts: dict, paper_mode: bool) -> tuple[str, list[str]]:
    out = [preamble(facts, paper_mode)]
    missing: list[str] = []

    out.append("\n\\subsection{The results}\\label{sec:doubling_results}\n")
    for title, names in SECTIONS:
        out.append(f"\n\\subsubsection{{{title}}}\n")
        for short in names:
            decl = NS + short
            expo = read_exposition(decl)
            if expo is None:
                missing.append(decl)
                continue
            out.append(f"\n\\begin{{theorem}}\n  \\label{{thm:{short}}}")
            if not paper_mode:
                out.append(f"  \\lean{{{decl}}}\\leanok")
            out.append(render_citations(expo["statement"], facts))
            out.append("\\end{theorem}\n")
            out.append("\\begin{proof}")
            if not paper_mode:
                out.append("  \\leanok")
            out.append(render_citations(expo["sketch"], facts))
            out.append("\\end{proof}\n")
            out.append("\\noindent " + render_citations(expo["relation"], facts) + "\n")

    diffs = EXPO / "_differences.tex"
    if diffs.exists():
        out.append("\n" + diffs.read_text(encoding="utf8").strip() + "\n")
    out.append(index_section(facts))
    return "\n".join(out) + "\n", missing


def index_section(facts: dict) -> str:
    rows = []
    for _, names in SECTIONS:
        for short in names:
            decl = NS + short
            rec = facts[decl]
            deep = closure(facts, decl)
            named = sum(1 for u in deep if is_named_result(facts.get(u, {})))
            rows.append("\\ref{thm:%s} & \\texttt{\\small %s} & %d & %d \\\\"
                        % (short, esc(short), named, len(deep)))
    body = "\n".join(rows)
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
namespace \texttt{{GFNBounds.Doubling}}. The last two columns count what each proof rests on,
unfolded to the bottom of the development: the declarations it reaches, and how many of those
are results the development names rather than steps internal to one.}}
\label{{tab:doubling_decls}}
\end{{table}}
"""


def write_graph(facts: dict) -> Path:
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
    drawn: set[str] = set()
    for decl in HEADLINES:
        short = decl.replace(NS, "")
        lines.append(f'  "{short}" [style=filled, fillcolor="#d8ecd8", fontsize=11];')
        drawn.add(short)
    for decl in HEADLINES:
        for u in work_deps(facts, decl):
            rec = facts.get(u, {})
            if not is_named_result(rec) or rec.get("kind") != "theorem":
                continue
            us = u.replace(NS, "")
            if us not in drawn:
                lines.append(f'  "{us}" [fillcolor="#eeeeee", style=filled];')
                drawn.add(us)
            lines.append(f'  "{decl.replace(NS, "")}" -> "{us}";')
    lines.append("}")
    out = ROOT / "docs" / "lean-graph.dot"
    out.write_text("\n".join(lines) + "\n")
    return out


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--skeleton", metavar="DECL",
                   help="print the Lean-derived draft for one theorem")
    p.add_argument("--lint", action="store_true", help="run the gates")
    p.add_argument("--check", action="store_true", help="fail if content.tex is out of date")
    p.add_argument("--paper", action="store_true", help="also write the paper-ready fragment")
    p.add_argument("--graph", action="store_true",
                   help="write docs/lean-graph.dot, the verified dependency graph")
    args = p.parse_args()

    facts = load_facts()

    if args.skeleton:
        print_skeleton(facts, args.skeleton)
        return 0

    if args.lint:
        problems = lint(facts)
        if problems:
            print("lint: %d problem(s)" % len(problems), file=sys.stderr)
            for q in problems:
                print("  " + q, file=sys.stderr)
            return 1
        print(f"lint: clean — {len(HEADLINES)} results, statements current, "
              "every sketch supported by the proof it describes")
        return 0

    text, missing = emit(facts, paper_mode=False)
    if missing:
        print("missing exposition — write these files:", file=sys.stderr)
        for m in missing:
            print(f"  blueprint/exposition/{m}.md", file=sys.stderr)
        return 1

    if args.check:
        if not OUT.exists() or OUT.read_text() != text:
            print("blueprint/src/content.tex is out of date; run scripts/appendix.py",
                  file=sys.stderr)
            return 1
        print("appendix content.tex up to date")
        return 0

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text)
    print(f"wrote {OUT.relative_to(ROOT)} — {len(HEADLINES)} results")

    if args.paper:
        ptext, _ = emit(facts, paper_mode=True)
        OUT_PAPER.write_text(ptext)
        print(f"wrote {OUT_PAPER.relative_to(ROOT)} — paper-ready fragment")
    if args.graph:
        g = write_graph(facts)
        print(f"wrote {g.relative_to(ROOT)} — the verified dependency graph")
    return 0


if __name__ == "__main__":
    sys.exit(main())
