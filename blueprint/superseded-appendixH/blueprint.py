#!/usr/bin/env python3
"""Generate a draft replacement for Appendix H from the appendix and the library.

The draft is the appendix itself, carried over in document order — its opening, its
sectioning, its statements, its connective prose, its measurements — with exactly one
substitution: each of the 33 prose proofs is replaced by a short authored sketch from
`blueprint/exposition/`, the detail delegated to the Lean development.

Two outputs, from the same walk:

  content.tex     standalone, for `leanblueprint pdf` and `leanblueprint web`; the 22
                  references that leave Appendix H are named rather than resolved, and
                  the statements carry the invisible \\lean / \\leanok / \\uses that drive
                  the dependency graph.
  appendix_H.tex  paper-ready (`--paper`); external \\ref's left intact, no blueprint
                  macros, ready to replace app_doubling.tex through /writer.

Nothing here paraphrases the paper: statements and prose are copied character for
character. What is authored lives in `blueprint/exposition/`, one file per proof.

Usage:
    python3 scripts/blueprint.py            # regenerate content.tex
    python3 scripts/blueprint.py --paper    # also write blueprint/appendix_H.tex
    python3 scripts/blueprint.py --lint     # fail on lab-register language
    python3 scripts/blueprint.py --check    # fail if content.tex is out of date
    python3 scripts/blueprint.py --report   # what was matched to what
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = Path("/home/maxbrain/Dropbox/GFN Bounds/app_doubling.tex")
EXPO = ROOT / "blueprint" / "exposition"
OUT = ROOT / "blueprint" / "src" / "content.tex"
OUT_PAPER = ROOT / "blueprint" / "appendix_H.tex"

APPENDIX_TITLE = ("The doubling graph: an unbounded diffusion operator "
                  "at finite backward length")

# The 22 labels Appendix H reaches for outside itself.  The standalone build names them;
# `--paper` leaves the \ref alone.  This dict is also the checklist of what has to resolve
# when the draft is spliced back into the paper.
EXTERNAL = {
    "app:divergence": "the appendix on divergence",
    "app:notation": "the notation appendix",
    "def:loop_closure": "the definition of the loop closure",
    "def:path_connected": "the definition of path-connectedness",
    "eq:counterexample_graph": "the counter-example graph",
    "eq:morozov_variables": "the variables of Morozov et al.",
    "eq:occupation": "the occupation identity",
    "equ:stable_bound": "the stable bound",
    "equ:stable_constants": "the stable constants",
    "lem:adjoint": "the adjoint lemma",
    "lem:lift_mixing": "the lifting lemma",
    "lem:sigma_mixing": "the mixing lemma",
    "prop:morozov_rate": "the rate of Morozov et al.",
    "sec:cv_divergence": "the section on divergence",
    "sec:experiments": "the experimental section",
    "theo:IL_CV_bound": "the imitation-learning bound",
    "theo:RL_CV_bound_full": "the reinforcement-learning bound",
    "theo:db_stable_frozen": "the frozen detailed-balance theorem",
    "theo:db_stable_frozen_full": "the frozen detailed-balance theorem",
    "theo:universality_L2": "the $L^2$ universality theorem",
    "theo:universality_L2_full": "the $L^2$ universality theorem",
    "theo:universality_graphs": "the universality theorem for graphs",
}

CITATIONS = {
    "morozov2025revisiting": "Morozov et al.\\ (2025)",
    "levin2017markov": "Levin and Peres (2017)",
    "brezis2011functional": "Brezis (2011)",
}

# `Definition~\ref{...}` reads badly once the target is named rather than numbered.
KIND_BEFORE = re.compile(
    r"(?:Definition|Lemma|Theorem|Proposition|Corollary|Remark|Appendix|Section)s?~?\s*"
    r"(?=\\extref)")

# `the counter-example graph \extref{the counter-example graph …}`: the paper names
# the target and so does the substitution, so one of the two copies has to go.
DUPLICATED = re.compile(r"(?P<phrase>[\w$\\{}^-]+(?:\s+[\w$\\{}^-]+){0,4})\s+\\extref\{(?P=phrase)"
                        r"(?=[,.\s}])")

ENV = r"(definition|lemma|proposition|theorem|corollary|remark)"
ENV_OPEN = re.compile(r"\\begin\{" + ENV + r"\}")

KIND_WORD = {"definition": "Definition", "lemma": "Lemma", "proposition": "Proposition",
             "theorem": "Theorem", "corollary": "Corollary", "remark": "Remark"}

STATUS_WORD = {"closed": "complete", "partial": "partial", "open": "---"}

# Language that belongs in the repository and not in a published appendix.  `--lint` fails
# on any of it: this is what keeps the certification register out of the draft.
DENYLIST = [
    (r"\d{4}-\d\d-\d\d", "a date"),
    (r"\bbucket [A-D]\b", "a difficulty bucket"),
    (r"\bsorry\b", "the word sorry"),
    (r"\.lean\b", "a Lean file name"),
    (r"machine-checked", "the phrase machine-checked"),
    (r"\brecorded\b", "the word recorded"),
    (r"\bDEFERRED\b", "the word DEFERRED"),
    (r"\bHARD\b", "the word HARD"),
    (r"⚠", "a warning sign"),
    (r"paper-map", "the paper map"),
    (r"trace_check", "the trace checker"),
    (r"\bcertifying\b", "the word certifying"),
    (r"\bscaffold\b", "the scaffold"),
    (r"\boverclaim\b", "the word overclaim"),
    (r"\bblueprint\b", "the word blueprint"),
    (r"app_doubling", "the source file name"),
]


# --------------------------------------------------------------------------
# inputs
# --------------------------------------------------------------------------

def load():
    pm = json.loads((ROOT / "paper-map.json").read_text())
    rm = json.loads((ROOT / "docs" / "repo-map.json").read_text())
    tex = PAPER.read_text(encoding="utf8").split("\n")
    return pm, rm, tex


def decl_index(rm):
    """Index the library's declarations.

    `docs/repo-map.json` records a declaration's `full` name relative to the innermost
    `namespace` line it could parse, so both `Decay.qm` and
    `GFNBounds.Doubling.exp_neg_two_mul_le_one_sub` occur; paper-map.json always writes the
    absolute name.  Match on a whole-component suffix.
    """
    by_full, by_tail = {}, {}
    for f in rm["files"]:
        for c in f["decls"]:
            if c["name"] == "_":
                continue
            rec = dict(c, file=f["file"])
            by_full.setdefault(c["full"], rec)
            by_tail.setdefault(c["name"], []).append(rec)
    return by_full, by_tail


def resolve(full, by_full, by_tail, files):
    if full in by_full:
        return by_full[full]
    for cand, rec in by_full.items():
        if full.endswith("." + cand):
            return rec
    for rec in by_tail.get(full.split(".")[-1], []):
        if rec["file"] in files:
            return rec
    return None


def principal(label, body, decls, by_full, by_tail, files):
    """The declaration that carries this statement, if one stands out.

    The library's house style names the paper label, or an equation label of the statement,
    in the bold lead of the docstring: ``**`eq:doubling_product`.** …``.  That is the signal
    used here; nothing else is as reliable.
    """
    keys = {label} | set(re.findall(r"\\label\{([^}]*)\}", body))
    scored = []
    for full in decls:
        rec = resolve(full, by_full, by_tail, files)
        if rec is None:
            continue
        doc = rec["doc"] or ""
        head = doc.split("\n")[0]
        score = 0
        if any(k in doc for k in keys):
            score += 10
        if any(k in head for k in keys):
            score += 10
        if any(k in head[:80] for k in keys):
            score += 5
        if doc.startswith("**"):
            score += 3
        if rec["kind"] in ("theorem", "lemma"):
            score += 1
        scored.append((score, rec))
    scored.sort(key=lambda x: -x[0])
    return scored[0][1] if scored else None


# --------------------------------------------------------------------------
# the appendix, cut into pieces
# --------------------------------------------------------------------------

def proof_regions(tex, spans):
    """(start, end, label) for all 33 proof blocks, in-line and out-of-line."""
    out = []
    open_re = re.compile(r"^\s*\\begin\{proof\}(?:\[[^\]]*\\ref\{([^}]*)\}[^\]]*\])?")
    i = 0
    while i < len(tex):
        m = open_re.match(tex[i])
        if m:
            start = i + 1
            end = next(j + 1 for j in range(i, len(tex))
                       if tex[j].strip() == r"\end{proof}")
            owner = m.group(1) or next(
                (lab for (a, b), lab in spans.items() if a <= start <= b), None)
            out.append((start, end, owner))
            i = end
        i += 1
    return out


def statement_body(tex, span):
    """The statement environment's own text, for the principal-declaration heuristic."""
    text = "\n".join(tex[span[0] - 1: span[1]])
    env = ENV_OPEN.search(text).group(1)
    close = f"\\end{{{env}}}"
    return env, text[: text.index(close)]


def rewrite(text):
    """Standalone build: name what leaves the appendix, spell out the citations."""
    text = re.sub(r"\\(?:eq|c)?ref\{([^}]*)\}",
                  lambda m: ("\\extref{%s}" % EXTERNAL[m.group(1)]
                             if m.group(1) in EXTERNAL else m.group(0)),
                  text)
    text = KIND_BEFORE.sub("", text)
    text = DUPLICATED.sub(r"\\extref{\g<phrase>", text)
    text = re.sub(r"\\cite[tp]?\{([^}]*)\}",
                  lambda m: CITATIONS.get(m.group(1), m.group(1)), text)
    # plasTeX renders a float it cannot express in HTML by compiling it with
    # pdflatex in a temporary directory, where leanblueprint's own blueprint.sty
    # cannot be found, and the run then dies before the dependency graph is
    # written.  \onlyprint is the graphic in the pdf and a pointer on the web.
    text = re.sub(r"\\includegraphics(?:\[[^\]]*\])?\{([^}]*)\}",
                  r"\\onlyprint{\1}", text)
    return text


def esc(s):
    return (s.replace("\\", r"\textbackslash{}").replace("_", r"\_")
             .replace("&", r"\&").replace("%", r"\%").replace("#", r"\#")
             .replace("$", r"\$"))


# --------------------------------------------------------------------------
# emitting
# --------------------------------------------------------------------------

def sketch(label, missing):
    path = EXPO / f"{label.replace(':', '_')}.tex"
    if not path.exists():
        missing.append(path)
        return "\\emph{[sketch missing]}"
    return path.read_text(encoding="utf8").strip()


def annotations(s):
    """The blueprint's invisible marks: which declarations, how far, what it rests on."""
    out = []
    if s["decls"]:
        out.append("\\lean{%s}" % ", ".join(s["decls"]))
    if s["status"] == "closed":
        out.append("\\leanok")
    elif s["status"] == "open":
        out.append("\\notready")
    return "".join(out)


def formal_table(stmts, kinds, names):
    rows = []
    for s in stmts:
        lab = s["label"]
        decl = names.get(lab)
        rows.append("%s~\\ref{%s} & %s & %s \\\\" % (
            KIND_WORD[kinds[lab]], lab,
            ("\\texttt{\\small %s}" % esc(decl)) if decl else "---",
            STATUS_WORD[s["status"]]))
    body = "\n".join(rows)
    return rf"""
\subsection{{The formal development}}\label{{sec:doubling_formal}}

Table~\ref{{tab:doubling_formal}} records, for each statement of this appendix, the
declaration of the Lean development that carries it and whether the formalisation covers
the statement in full. \emph{{Partial}} marks a statement one of whose clauses is a
property of the backward chain as a stochastic process rather than of the recursions this
appendix works with; the three remarks marked \emph{{---}} are commentary, one of them
explicitly a formal computation that the appendix does not prove.

\begin{{table}}[htb]
\centering
\small
\begin{{tabular}}{{@{{}}l l l@{{}}}}
\hline
statement & formal counterpart & formalised \\
\hline
{body}
\hline
\end{{tabular}}
\caption{{Each statement of this appendix and its counterpart in the Lean
development, whose declarations live in the namespace \texttt{{GFNBounds.Doubling}}.}}
\label{{tab:doubling_formal}}
\end{{table}}
"""


def build(args, paper_mode):
    pm, rm, tex = load()
    by_full, by_tail = decl_index(rm)
    stmts = pm["statements"]
    spans = {tuple(s["tex_span"]): s["label"] for s in stmts}
    by_label = {s["label"]: s for s in stmts}

    kinds, names, bodies = {}, {}, {}
    for s in stmts:
        env, body = statement_body(tex, s["tex_span"])
        kinds[s["label"]] = env
        bodies[s["label"]] = body
        rec = principal(s["label"], body, s["decls"], by_full, by_tail, s["lean_files"])
        if rec:
            names[s["label"]] = rec["full"].split(".")[-1]

    # Every label the appendix defines, mapped to the statement that defines it, so that
    # \uses points at nodes of the graph and not at equations inside them.
    owner, order = {}, {}
    for n, s in enumerate(stmts):
        owner[s["label"]] = s["label"]
        order[s["label"]] = n
        for lab in re.findall(r"\\label\{([^}]*)\}", bodies[s["label"]]):
            owner.setdefault(lab, s["label"])

    proofs = proof_regions(tex, spans)
    proof_start = {p[0]: p for p in proofs}
    stmt_start = {a: lab for (a, b), lab in spans.items()}
    missing = []

    out = []
    i = 1
    while i <= len(tex):
        line = tex[i - 1]

        if i == 1:                                   # the file's own header comment
            i += 1
            continue

        if i == 2:                                   # \section{\appendixHtitle}
            out.append(line if paper_mode
                       else "\\section{%s}\\label{app:doubling}" % APPENDIX_TITLE)
            i += 1
            continue

        if i == 12:                                  # the blank after the opening
            out.append(line)
            out.append(formalisation_note(missing))
            out.append("")
            i += 1
            continue

        if i in proof_start:
            start, end, label = proof_start[i]
            uses = []
            if label:
                src = "\n".join(tex[start - 1: end])
                uses = sorted({owner[r] for r in
                               re.findall(r"\\(?:eq|c)?ref\{([^}]*)\}", src)
                               if owner.get(r) and owner[r] != label
                               and order.get(owner[r], 99) < order.get(label, 99)},
                              key=lambda x: order[x])
            head = ("\\begin{proof}[Proof sketch]" if label in by_label
                    else "\\begin{proof}[Proof sketch, Theorem \\ref{%s}]" % label)
            if not paper_mode:
                marks = []
                if label and by_label.get(label, {}).get("status") == "closed":
                    marks.append("\\leanok")
                if uses:
                    marks.append("\\uses{%s}" % ", ".join(uses))
                head += "".join(marks)
            out.append(head)
            out.append(sketch(label, missing))
            out.append("\\end{proof}")
            i = end + 1
            continue

        if i in stmt_start and not paper_mode:
            lab = stmt_start[i]
            uses = sorted({owner[r] for r in
                           re.findall(r"\\(?:eq|c)?ref\{([^}]*)\}", bodies[lab])
                           if owner.get(r) and owner[r] != lab
                           and order.get(owner[r], 99) < order[lab]},
                          key=lambda x: order[x])
            mark = annotations(by_label[lab])
            if uses:
                mark += "\\uses{%s}" % ", ".join(uses)
            out.append(re.sub(r"(\\label\{" + re.escape(lab) + r"\})",
                              r"\1" + mark.replace("\\", "\\\\"), line, count=1))
            i += 1
            continue

        out.append(line)
        i += 1

    text = "\n".join(out)
    if not paper_mode:
        text = rewrite(text)
    text += "\n" + formal_table(stmts, kinds, names) + "\n"
    return text, missing, stmts, names


def formalisation_note(missing):
    path = EXPO / "_formalisation.tex"
    if not path.exists():
        missing.append(path)
        return ""
    return path.read_text(encoding="utf8").strip()


def lint(text):
    """Fail on language that belongs in the repository, not in a published appendix."""
    stripped = re.sub(r"^%.*$", "", text, flags=re.M)
    bad = []
    for pat, what in DENYLIST:
        for m in re.finditer(pat, stripped):
            line = stripped[: m.start()].count("\n") + 1
            ctx = " ".join(stripped[max(0, m.start() - 60): m.start() + 60].split())
            bad.append(f"  line {line}: {what} — …{ctx}…")
    return bad


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check", action="store_true",
                   help="fail if content.tex is out of date instead of writing it")
    p.add_argument("--lint", action="store_true",
                   help="fail on certification-register language in the output")
    p.add_argument("--paper", action="store_true",
                   help="also write blueprint/appendix_H.tex, the paper-ready fragment")
    p.add_argument("--report", action="store_true",
                   help="print which declaration was matched to which statement")
    args = p.parse_args()

    if not PAPER.exists():
        print(f"appendix not found: {PAPER}", file=sys.stderr)
        return 2

    text, missing, stmts, names = build(args, paper_mode=False)

    if missing:
        print("missing authored text — write these files:", file=sys.stderr)
        for m in sorted(set(missing)):
            print(f"  {m.relative_to(ROOT)}", file=sys.stderr)
        return 1

    if args.lint:
        bad = lint(text)
        if bad:
            print("lint: certification-register language in the draft:", file=sys.stderr)
            print("\n".join(bad), file=sys.stderr)
            return 1
        print("lint: clean")
        return 0

    if args.check:
        if not OUT.exists() or OUT.read_text() != text:
            print("blueprint/src/content.tex is out of date; "
                  "run python3 scripts/blueprint.py", file=sys.stderr)
            return 1
        print("blueprint content.tex up to date")
        return 0

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text)
    n = {"closed": 0, "partial": 0, "open": 0}
    for s in stmts:
        n[s["status"]] += 1
    print(f"wrote {OUT.relative_to(ROOT)} — {len(stmts)} statements, "
          f"{n['closed']} complete / {n['partial']} partial / {n['open']} not formalised")

    if args.paper:
        ptext, _, _, _ = build(args, paper_mode=True)
        OUT_PAPER.write_text(ptext)
        print(f"wrote {OUT_PAPER.relative_to(ROOT)} — paper-ready fragment")

    if args.report:
        print()
        for s in stmts:
            print(f"  {s['label']:38s} {s['status']:8s} {names.get(s['label'], '---')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
