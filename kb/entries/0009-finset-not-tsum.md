---
id: 0009
title: Prefer `Finset.sum` to `tsum`; the `Setting` fields are shaped to let you
kind: pattern
tags: [summability, tsum, finset]
confidence: established
sources: [GFNBounds/Doubling/Setting.lean:178]
created: 2026-09-07
---
## When

Any expression involving the target row `P̂_B(s_f → ·)`, the cut window, or a block of the ladder.

## Do

- The target row is **finitely supported by hypothesis**: `S.row_supp : row j ≠ 0 → 1 ≤ j ∧ j ≤ d`,
  and `S.row_sum : ∑ j ∈ Finset.Icc 1 S.d, S.row j = 1`. So `pstar_sink` is a `Finset.sum` and
  never a `tsum`.
- The window is a `Finset`: `window m = Finset.Ico ((m + 1) / 2) m`, with `mem_window` its `Ico`
  membership lemma.
- Where a `tsum` is unavoidable (the norm estimates), the four Mathlib lemmas this library
  actually leans on are `Summable.of_norm_bounded`, `Summable.mul_left`, `Summable.tsum_sub` and
  `Summable.tsum_le_tsum` — plus `Stat.summable_mul` locally, see [[0003-stat-inv-needs-bounded]].

## Why

`row_supp` being a hypothesis rather than a derived fact kills a whole class of summability side
conditions before it can appear — it is one of the three modelling decisions argued in
`Setting.lean`'s docstring. Introducing a `tsum` where a `Finset.sum` would do re-imports exactly
the obligations the design removed, and the `Finset` API (`sum_congr`, `sum_le_sum`, `mul_sum`,
`sum_nonneg`) is far better populated than the `tsum` one.
