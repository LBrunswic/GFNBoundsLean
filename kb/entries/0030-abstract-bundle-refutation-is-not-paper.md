---
id: 0030
title: A refutation at the generality of an abstract bundle is not a refutation of the paper
kind: pitfall
tags: [fidelity, abstraction, review]
confidence: established
sources: [GFNBounds/Balance/WeightedL2Norm.lean:37, GFNBounds/Balance/WeightedL2Norm.lean:55]
created: 2026-09-13
---
## When

A counterexample or "the paper's claim is false" finding is proved against a library structure
(`Core.Mixing P Π`) that abstracts the paper's objects.

## Do

Re-check it at the paper's instance before recording a paper finding. State the abstract result
under an oblique name that says what it is (`not_forall_beta_zero_eq_one`) and prove the paper's
claim at the instance alongside (`beta_zero_densOp_meanOp`).

## Why

"`β̂₀ = 1` is false" held for arbitrary `Core.Mixing` data, where `Π` need not be the orthogonal
projection onto constants; for the paper's `Π` on at least two states `‖I − Π‖ = 1` and `β̂₀ = 1`
is true. The finding had been written into the graduation notes as a paper finding before the audit
caught it.
