#!/usr/bin/env python3
"""Fail if any audited declaration rests on `sorryAx` or an unexpected axiom.

`sorry` is already a compile error inside `GFNBounds`, but that only catches a `sorry` written
there. This catches the laundering case: a closed theorem whose proof term reaches a `sorry`
through an import. Reads the build log produced by `make check`.
"""
import re, sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# `\S+?` rather than `[^']+`: Lean names may end in a prime (`incr_le'`), which `[^']+` cannot
# cross — until 2026-09-07 three primed declarations were silently skipped by this audit.
LINE = re.compile(r"'(\S+?)' depends on axioms: \[([^\]]*)\]")


def main(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    hits = LINE.findall(text)
    if not hits:
        print("FAIL: no `#print axioms` output in %s — did GFNBounds.Audit build?" % path)
        sys.exit(1)
    bad = False
    for name, axioms in hits:
        ax = {a.strip() for a in axioms.split(",") if a.strip()}
        extra = ax - ALLOWED
        if extra:
            print("FAIL: %s depends on %s" % (name, ", ".join(sorted(extra))))
            bad = True
    if bad:
        sys.exit(1)
    print("axiom_audit: %d declarations, all within {propext, Classical.choice, Quot.sound}"
          % len(hits))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "build.log")
