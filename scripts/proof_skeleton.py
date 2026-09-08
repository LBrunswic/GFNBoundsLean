#!/usr/bin/env python3
"""Read the shape of a Lean proof out of its source.

`docs/lean-facts.json` says which declarations a proof term invokes; it says nothing about the
order they are invoked in, or about the intermediate claims the author chose to state. Both are
in the source, and both are what makes a sketch readable rather than a list.

This module extracts, for one declaration:

  * the `have` chain — each intermediate claim with the type the author wrote for it, in order;
  * whether each step is *plumbing*, meaning it is closed by an arithmetic or normalisation
    tactic and carries no mathematical content worth a sentence;
  * the concluding step (`exact`, `refine`, `apply`, or a bare term after `:=`).

It is a parser over text, so it is approximate where the environment is exact. Everything it
produces is a *draft* for a human, and the claims that end up in the appendix are checked
against `uses_value` from the environment, not against this.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# A step closed only by one of these has no mathematical content to report: it is arithmetic,
# normalisation, or bookkeeping that the author did not have to think about.
PLUMBING = {
    "linarith", "nlinarith", "positivity", "omega", "norm_num", "push_cast", "ring",
    "ring_nf", "decide", "simp", "simpa", "trivial", "rfl", "aesop", "gcongr", "bound",
    "field_simp", "constructor", "exact?", "measurability", "fun_prop", "norm_cast",
}

DECL_START = re.compile(
    r"^(?P<kind>theorem|lemma|noncomputable def|def|abbrev|instance|structure|inductive)\s+"
    r"(?P<name>[^\s({\[:]+)")

HAVE = re.compile(r"^(?P<indent>\s*)have\s+(?P<name>\S+)?\s*(?::\s*(?P<type>.*?))?\s*:=\s*(?P<rhs>.*)$")
OBTAIN = re.compile(r"^(?P<indent>\s*)obtain\s+(?P<pat>.+?)\s*:=\s*(?P<rhs>.*)$")
CONCLUDE = re.compile(r"^\s*(?P<tac>exact|refine|apply|calc)\b\s*(?P<rest>.*)$")


def source_of(module: str) -> Path:
    """`GFNBounds.Doubling.Main` -> the file that declares it."""
    return ROOT / (module.replace(".", "/") + ".lean")


def declaration_block(path: Path, name: str) -> list[str]:
    """The lines of one declaration.

    It ends at the next declaration *or* at the docstring or section comment introducing one:
    a term-mode proof otherwise swallows the prose that follows it.
    """
    short = name.split(".")[-1]
    lines = path.read_text(encoding="utf8").split("\n")
    start = None
    for i, line in enumerate(lines):
        m = DECL_START.match(line)
        if m and m.group("name").split(".")[-1] == short:
            start = i
            continue
        if start is not None and (m or line.startswith(("/--", "/-!", "@[", "end ", "section ",
                                                       "namespace "))):
            return lines[start:i]
    return lines[start:] if start is not None else []


def _identifiers(rhs: str, following: list[str], indent: str) -> set[str]:
    """Every identifier in a step: its rhs, plus any more-indented block under it."""
    body = [rhs]
    for line in following:
        if not line.strip():
            continue
        if len(line) - len(line.lstrip()) <= len(indent):
            break
        body.append(line)
    text = " ".join(body)
    return set(re.findall(r"[A-Za-z_][A-Za-z_0-9']*", text))


def skeleton(module: str, name: str, named: set[str] | None = None) -> dict:
    """The proof's shape: its stated intermediate claims and how it concludes.

    `named` is the set of short names of declarations the library marks as results — a
    docstring opening with the house bold lead. A step that invokes one of those is
    substantive; a step that invokes none is plumbing, whatever tactic closes it. That is a
    better rule than looking at tactic names, because a step closed by `omega` after pulling in
    a positivity field is still bookkeeping.
    """
    named = named or set()
    path = source_of(module)
    if not path.exists():
        return {"steps": [], "conclusion": "", "error": f"no source at {path}"}
    block = declaration_block(path, name)
    if not block:
        return {"steps": [], "conclusion": "", "error": f"{name} not found in {path}"}

    # The signature runs to the `:= by` or `:=` that opens the proof.
    body_at = next((i for i, l in enumerate(block) if re.search(r":=\s*(by)?\s*$", l)
                    or ":= by " in l), None)
    body = block[body_at + 1:] if body_at is not None else []

    steps, conclusion = [], ""
    for i, line in enumerate(body):
        m = HAVE.match(line) or OBTAIN.match(line)
        if m:
            g = m.groupdict()
            indent, rhs = g["indent"], g.get("rhs", "")
            toks = _identifiers(rhs, body[i + 1:], indent)
            short = {t.split(".")[-1] for t in toks}
            claim = (g.get("type") or "").strip()
            # A `have` whose type continues on the next lines: pull them in.
            if claim.endswith((":=", "by")) or (claim and not rhs.strip()):
                claim = claim.rstrip(":= by").strip()
            if not claim:                       # `have h := f x`, no type ascribed
                claim = " ".join(rhs.split())[:120]
            steps.append({
                "name": (g.get("name") or g.get("pat") or "").strip(),
                "claim": claim,
                "invokes": sorted(short & named),
                "plumbing": not (short & named),
                "line": (body_at or 0) + i + 2,
            })
            continue
        c = CONCLUDE.match(line)
        if c and not conclusion:
            conclusion = " ".join((c.group("tac") + " " + c.group("rest")).split())

    if not conclusion and body_at is not None:
        # A term-mode proof: everything after `:=` is the conclusion.
        tail = block[body_at:]
        head = re.sub(r"^.*?:=\s*", "", tail[0])
        conclusion = " ".join((" ".join([head] + tail[1:])).split())

    return {"steps": steps, "conclusion": conclusion[:600], "error": None}


if __name__ == "__main__":
    import json
    import sys

    facts = json.loads((ROOT / "docs" / "lean-facts.json").read_text())["declarations"]
    for target in sys.argv[1:]:
        rec = facts.get(target)
        if rec is None:
            print(f"unknown declaration: {target}")
            continue
        named = {k.split(".")[-1] for k, v in facts.items()
                 if (v.get("doc") or "").lstrip().startswith("**")}
        s = skeleton(rec["module"], target, named)
        print(f"\n### {target}")
        if s["error"]:
            print("  ", s["error"])
            continue
        for st in s["steps"]:
            if st["plumbing"]:
                continue
            print(f"  step  {st['name']:12s} {st['claim'][:76]}")
            if st["invokes"]:
                print(f"        via {', '.join(st['invokes'])}")
        print(f"  concludes  {s['conclusion'][:160]}")
