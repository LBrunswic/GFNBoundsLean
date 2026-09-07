---
id: 0010
title: Bundle a bound as a structure field, not as an `iSup` or an `∃`
kind: convention
tags: [design, structures]
confidence: established
sources: [GFNBounds/Doubling/Setting.lean:180, GFNBounds/Doubling/DecayNotation.lean:52]
created: 2026-09-07
---
## When

Introducing a new parameter that the mathematics only ever uses through an inequality.

## Do

Follow `Setting.epsMax`: a field with `eps_le : ∀ ⦃j⦄, 1 ≤ j → eps j ≤ epsMax` and
`epsMax_lt_one`, **not** `⨆ j, eps j`. Likewise `Decay` bundles `c` together with a non-zero root
`p` of the Cramér equation and the derived `p_gt_one`, so no consumer re-derives it.

Note the strict-implicit binders `⦃j⦄` on the `∀ j, 1 ≤ j → …` fields: they let `S.eps_pos hj`
elaborate without naming `j`.

## Why

The appendix only ever uses `ε(j) ≤ ε_max < 1`. An `iSup` in `ℝ` would drag `BddAbove` bookkeeping
through every single proof that touches `ε`, in exchange for a fact nothing consumes. The same
reasoning puts positivity of `λ` in `Stat` as a field rather than a theorem: every statement
downstream of `lem:doubling_irreducible` quantifies over "an invariant probability", so positivity
belongs in the hypothesis, and the existence question (`prop:doubling_phase`) stays separate — and
open — without blocking anything.
