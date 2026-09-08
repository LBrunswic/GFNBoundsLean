#!/usr/bin/env python3
"""Every module under `GFNBounds/` must be reachable from the root module `GFNBounds.lean`.

The lakefile globs `GFNBounds.*`, so an unlisted module still *builds*; but `scripts/AxiomSweep.lean`
imports the root and sweeps only what the root reaches, and `GFNBounds/Audit.lean` lists by hand.
A module reachable from neither is built and never audited. This check closes that hole.
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIB = os.path.join(ROOT, "GFNBounds")
IMPORT = re.compile(r"^import\s+(GFNBounds(?:\.\w+)*)\s*$", re.M)


def module_name(path):
    rel = os.path.relpath(path, ROOT)[:-len(".lean")]
    return rel.replace(os.sep, ".")


def main():
    mods = {}
    for dirpath, _, names in os.walk(LIB):
        for n in names:
            if n.endswith(".lean"):
                p = os.path.join(dirpath, n)
                mods[module_name(p)] = IMPORT.findall(open(p, encoding="utf-8").read())
    root_path = os.path.join(ROOT, "GFNBounds.lean")
    mods["GFNBounds"] = IMPORT.findall(open(root_path, encoding="utf-8").read())
    seen, stack = set(), ["GFNBounds"]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(mods.get(m, []))
    unreached = sorted(set(mods) - seen - {"GFNBounds"})
    for m in unreached:
        print("FAIL: %s is not reachable from GFNBounds.lean — add an import, or it is never audited"
              % m)
    if unreached:
        sys.exit(1)
    print("root_closure: %d modules, all reachable from GFNBounds.lean" % (len(mods) - 1))


if __name__ == "__main__":
    main()
