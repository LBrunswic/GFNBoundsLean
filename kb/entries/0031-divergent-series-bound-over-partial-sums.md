---
id: 0031
title: Bound against a possibly divergent series by quantifying over real bounds of its partial sums
kind: pattern
tags: [tsum, ennreal, unbounded, quantifiers]
confidence: established
sources: [GFNBounds/Doubling/OperatorFiniteSum.lean:104, GFNBounds/Doubling/OperatorFiniteSum.lean:151]
created: 2026-09-13
---
## When

The paper writes `‖X‖ ≤ ∑ₙ aₙ` with `aₙ ≥ 0` and the sum possibly `+∞` (the inequality then being
vacuous), and `tsum` in `ℝ` returns `0` on a non-summable family.

## Do

State it as `∀ B : ℝ, (∀ N, ∑ n < N, aₙ ≤ B) → ‖X‖ ≤ B`. It is vacuous exactly when the sum is
infinite, needs no `Summable` hypothesis, and cannot be misread through `tsum`'s junk value.
Derive the `ℝ≥0∞` form `‖X‖ₑ ≤ ∑' n, aₙ` as a corollary when a consumer wants it.

## Why

A `Summable` hypothesis narrows the statement to the finite case, and a bare `tsum` in `ℝ` makes
the divergent case false rather than vacuous. `resolvent_eq_tsum_of_bdd` and
`Stat.bhat_le_sum_betaHat` (`lem:doubling_operator`(3)) use the partial-sum form.
