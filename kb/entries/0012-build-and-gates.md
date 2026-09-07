---
id: 0012
title: Iterate on one module; `make check` is the gate
kind: workflow
tags: [build, audit, lake]
confidence: established
sources: [Makefile]
created: 2026-09-07
---
## When

Every editing loop.

## Do

```
lake build GFNBounds.Doubling.Tail     # one module — this is the iteration loop
make check                             # the gate: build + scaffold + the audits
```

`make check` runs, in order: `lake build GFNBounds` (tee to `build.log`), `lake build
GFNBoundsScaffold`, then `sorry_audit.py`, `axiom_audit.py build.log`, `trace_check.py`,
`coverage.py`, `repo_map.py`, `kb.py lint` and `kb.py index`. All of them must pass before handing work
back.

`lake exe cache get` if Mathlib oleans are missing. Do **not** create a git worktree for parallel
work: `.lake/` is 7.5 GB and a worktree would re-fetch all of it. Two sessions in this tree must
own **disjoint files**.

## Why

A full `lake build GFNBounds` recompiles the dependency cone and is slow; a module target is the
difference between a ten-second loop and a five-minute one. And the audits are not decoration —
`axiom_audit` is the only check that catches a laundered `sorry` reached through an import, and
`trace_check` is the only one that catches the paper moving under the formalization.
