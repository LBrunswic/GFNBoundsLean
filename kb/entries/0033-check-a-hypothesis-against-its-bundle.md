---
id: 0033
title: Check each carried hypothesis against the rest of the bundle, and certify a bundle by an iff
kind: pattern
tags: [hypotheses, structures, redundancy, fidelity]
confidence: established
sources: [GFNBounds/Balance/LocalConvergenceMixing.lean:45, GFNBounds/Core/UniversalityKernelBound.lean:58]
created: 2026-09-13
---
## When

A theorem carries a library structure (`Core.Mixing`) or a hypothesis the paper states
(`hb`, a finite operator norm) next to others (`hinv`, `hK`).

## Do

Ask whether the other hypotheses already imply it. If so, prove the implication and drop it, or
carry it with a SCOPE note naming the redundancy and whether it is proved. For a bundled
structure, a checklist row saying "the fields add nothing" is not enough: prove
`Bundle ↔ paper's condition` under the remaining hypotheses (`mixing_densOp_iff_summable`).

## Why

`Core.Mixing` packages `ΠP = PΠ = Π`, which the paper derives; the iff shows `hmx` assumes only
summability of `‖Pⁿ − Π‖`. `hb` in `theo:universality_L2_full` is redundant under invariance
(norm `≤ 1` for every `p`) — also a paper finding, since the paper states the norm hypothesis.
