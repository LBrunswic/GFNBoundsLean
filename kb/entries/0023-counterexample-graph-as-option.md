---
id: 0023
title: A counter-example graph is cheapest as `Option (Option (Fin N))`, not `Fin (N+2)`
kind: pattern
tags: [finite-graphs, fintype, big-operators, counterexamples]
confidence: established
sources: [GFNBounds/Graph/CycleDivergence.lean:248, GFNBounds/Graph/CycleExample.lean:26]
created: 2026-09-12
---
## When

Building a concrete `MarkedGraph` with `N` internal states and the two marks, at a **variable**
`N`.

## Do

Take `Option (Option (Fin N))`: `none = s₀`, `some none = s_f`, `some (some i) = xᵢ`.
`Fintype` and `DecidableEq` come free, `Fintype.sum_option` twice gives the single
sum-splitting lemma everything else rides on, and a cycle's wrap-around is `Fin N`'s own
`i + 1` rather than a `Fin.val` case split.

Build flows as `Finset.sum`s of one `unitEdge a b := if u = a ∧ v = b then 1 else 0`, whose two
marginals are one-liners; then every inflow/outflow computation is `Finset.sum_comm` plus
`Finset.sum_ite_eq'`.

Caveat at this pin: `ring` fails on `Fin (M+2)` (`ring_nf made no progress`). `sub_add_cancel`,
`eq_sub_of_add_eq`, `zero_ne_one` and `one_ne_zero` all work.

## Why

`Fin (N+2)` forces `Fin.val` case splits for the marks *and* for the wrap, and has no clean sum
decomposition. `Graph/CycleExample.lean` could afford it only because `N` was the literal `5`
and `decide` closed the side conditions; at a variable `N` nothing is decidable and that route
does not scale. `theo:no_bound_divergence` needs the graph for every `N ≥ 2`, and the encoding
`N = M + 2` also supplies `x₁ ≠ x₂` and `N − 1 ≠ 0` as instances, both of which the construction
consumes.
