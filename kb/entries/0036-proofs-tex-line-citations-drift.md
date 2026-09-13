---
id: 0036
title: Line citations to `proofs.tex` in docstrings drift silently when the draft moves
kind: pitfall
tags: [docs, traceability, fidelity]
confidence: established
sources: [GFNBounds/Balance/Flow.lean:14, GFNBounds/Balance/MassIdentity.lean:6, scripts/trace_check.py]
created: 2026-09-13
---
## When

Writing or editing a docstring that cites `proofs.tex:NNN`, or touching a module whose docstring does.

## Do

Anchor on the `\label` (the bold-backtick label line is machine-read; the line number is not), and
re-read the cited lines whenever the file is touched — treat a bare line number as advisory. When
correcting drift, check that every old value sits in one shifted block before applying an offset:
a citation written after the draft moved is already current, and shifting it breaks it.

## Why

`trace_check` digests the map's spans, not the docstrings' line numbers. The 2026-09-13 draft
repairs moved Appendix A's convergence block by 21 lines, and the audit of that day's flow repair
found six stale citations in files edited the same day (`Flow.lean`, `BoundaryBlowup.lean`,
`MassIdentity.lean`, corrected in the repair commit). Roughly 500 such citations exist across the
library; the durable fix — citing labels, not lines — is a convention change and gets its own pass.
