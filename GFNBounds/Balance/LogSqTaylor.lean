import GFNBounds.Balance.Lojasiewicz

/-!
# A second-order Taylor bound on `g'` for `g = (log x)²`, near `x = 1`

**No paper label.** This file certifies nothing: it is support, one elementary inequality about
`GFNBounds.Balance.logSqDeriv` that a downstream file in the frozen-policy convergence block
needs, and it is recorded here so that no `sorry` has to stand for it later. The generator
`g = (log x)²` it is about is the paper's practical one — the `g` of `cor:global_lojasiewicz`,
and the one `logSqDeriv` was introduced for in `GFNBounds/Balance/Lojasiewicz.lean`, whose
docstring carries that label and certifies it. **This file does not**: the statement below is
not any displayed inequality of the paper, it is not a step of any proof in it, and it must not
be cited as one.

What the paper does say about this `g`, and what fixes the two constants it is read against
(`GFNBounds/Balance/Lojasiewicz.lean` quotes the surrounding statement in full):

> (`proofs.tex:792`) […] *strictly unimodal*; e.g. `(log x)²` and `(x − 1)²` […]

and, for the second derivative at `1` that the `2` below is,

> (`proofs.tex:613`) […] `g` is `C³` on `[1−a, 1+a]` for some `a ∈ (0,1)` […]

`g'(x) = 2 log x / x` is `logSqDeriv`, `g''(1) = 2`, and `g'''(x) = 2(2 log x − 3)/x³`. On
`[1/2, 3/2]` one has `|2 log x − 3| ≤ 5` and `x^{-3} ≤ 8`, so `|g'''| ≤ 80` and Taylor's
remainder gives `|g'(y) − 2(y−1)| ≤ 40(y−1)²`. **That is not the route taken**: the constant `40`
is kept because it is the one the downstream statement was written against, but the proof below
is elementary and delivers `12`, from `log y ≤ y − 1` and `(y−1)/y ≤ log y` alone. See SCOPE.

## Hypothesis checklist

| where the shape comes from | here |
|---|---|
| `g` is `C³` on `[1−a, 1+a]`, `a ∈ (0,1)` (`proofs.tex:613`) | ⚠ **not used**: no derivative of any order is taken below, and `logSqDeriv` is a *definition* — `2 log x / x` — not a derivative, exactly as in `GFNBounds/Balance/Lojasiewicz.lean` |
| `g''(1) = 2` for `g = (log x)²` | ✓ appears as the coefficient `2` of `(y − 1)`, asserted by the statement and not computed |
| `M₃ := sup_{[1−a,1+a]}∣g'''∣`, and the `a` that bounds it | ⚠ **replaced by the interval `∣y−1∣ ≤ 1/2`** and the explicit constant `40`. No `M₃` is defined and no supremum is taken |
| the radius `∣y − 1∣ ≤ 1/2` | ✓ the hypothesis `hy`, chosen so that `1/2 ≤ y ≤ 3/2` and `1/y ≤ 2` |

## SCOPE (disclosed)

* **`logSqDeriv` is `2 log x / x` by definition, not by differentiation.** Nothing in this file
  or in `GFNBounds/Balance/Lojasiewicz.lean` proves that it is the derivative of `logSq`; the
  identification is the paper's (`proofs.tex:809`). So `logSqDeriv_taylor` is a statement about
  the function `2 log x / x`, and reading it as "the second-order Taylor expansion of `g'`" is
  the same modelling step the rest of the `Balance` layer already takes.
* **The constant `40` is not the best this proof gives.** The route below yields `12`:
  `|log y − (y−1)| ≤ 2(y−1)²` on `[1/2, 3/2]` from the two one-sided logarithm bounds, hence
  `|log y − y(y−1)| ≤ 3(y−1)²`, hence `|g'(y) − 2(y−1)| = 2|log y − y(y−1)|/y ≤ 12(y−1)²`.
  The statement is kept at `40` because that is the constant the downstream file was written
  against and because `40` is what the Taylor argument of the paper's own reading delivers;
  `logSqDeriv_taylor_twelve` records the sharper form, and `logSqDeriv_taylor` is its corollary.
  Numerically the true supremum of `|g'(y) − 2(y−1)|/(y−1)²` on `[1/2, 3/2]` is about `7.09`,
  attained at `y = 1/2`, so neither constant is sharp and `12` is not claimed to be.
* **Nothing here is a Taylor theorem.** `Mathlib.Analysis.Calculus.Taylor` is not imported and
  `taylor_mean_remainder_bound` is not used, so no derivative, no `ContDiff` hypothesis and no
  one-sided remainder appears. The two inputs are `Real.log_le_sub_one_of_pos` and
  `GFNBounds.Balance.sub_one_le_mul_log`, both already in the library.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

/-- **`|log y − (y−1)| ≤ 2(y−1)²` for `|y − 1| ≤ 1/2`.**

Both halves are one-sided logarithm bounds the library already has: `log y ≤ y − 1` is
`Real.log_le_sub_one_of_pos`, and `(y−1)/y ≤ log y` is `sub_one_le_mul_log` divided by `y`. The
second gives `log y − (y−1) ≥ −(y−1)²/y ≥ −2(y−1)²`, the factor `2` being `1/y` at `y = 1/2`. -/
theorem abs_log_sub_le_two_sq {y : ℝ} (hy : |y - 1| ≤ 1 / 2) :
    |Real.log y - (y - 1)| ≤ 2 * (y - 1) ^ 2 := by
  have hb := abs_le.mp hy
  have hy0 : 0 < y := by linarith [hb.1]
  have hup : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
  have hlow : (y - 1) / y ≤ Real.log y := by
    rw [div_le_iff₀ hy0]
    have h := sub_one_le_mul_log hy0
    linarith
  have hid : (y - 1) / y - (y - 1) = -((y - 1) ^ 2 / y) := by
    field_simp
    ring
  have hfrac : (y - 1) ^ 2 / y ≤ 2 * (y - 1) ^ 2 := by
    rw [div_le_iff₀ hy0]
    nlinarith [mul_nonneg (sq_nonneg (y - 1)) (show (0:ℝ) ≤ 2 * y - 1 by linarith [hb.1])]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith
  · nlinarith [sq_nonneg (y - 1)]

/-- **The sharper form of `logSqDeriv_taylor`, with `12` in place of `40`.**

`g'(y) − 2(y−1) = 2(log y − (y−1) − (y−1)²)/y`, because `y(y−1) = (y−1) + (y−1)²`; the numerator
is at most `3(y−1)²` in absolute value by `abs_log_sub_le_two_sq`, and `1/y ≤ 2`. -/
theorem logSqDeriv_taylor_twelve {y : ℝ} (hy : |y - 1| ≤ 1 / 2) :
    |logSqDeriv y - 2 * (y - 1)| ≤ 12 * (y - 1) ^ 2 := by
  have hb := abs_le.mp hy
  have hy0 : 0 < y := by linarith [hb.1]
  have hyne : y ≠ 0 := hy0.ne'
  have hkey : logSqDeriv y - 2 * (y - 1)
      = 2 * (Real.log y - (y - 1) - (y - 1) ^ 2) / y := by
    simp only [logSqDeriv]
    field_simp
    ring
  have hnum : |2 * (Real.log y - (y - 1) - (y - 1) ^ 2)| ≤ 6 * (y - 1) ^ 2 := by
    have h := abs_le.mp (abs_log_sub_le_two_sq hy)
    refine abs_le.mpr ⟨by nlinarith [sq_nonneg (y - 1)], by nlinarith [sq_nonneg (y - 1)]⟩
  rw [hkey, abs_div, abs_of_pos hy0, div_le_iff₀ hy0]
  nlinarith [hnum, mul_nonneg (sq_nonneg (y - 1)) (show (0:ℝ) ≤ y - 1 / 2 by linarith [hb.1])]

/-- **`|g'(y) − 2(y−1)| ≤ 40(y−1)²` on `|y − 1| ≤ 1/2`, for `g = (log x)²`** — the second-order
bound on `logSqDeriv` at `1`, with `g''(1) = 2` as the linear coefficient.

The constant is the Taylor one (`|g'''| ≤ 80` on `[1/2, 3/2]`, remainder `≤ 40(y−1)²`) and is
deliberately generous: `logSqDeriv_taylor_twelve` proves the same bound with `12`. -/
theorem logSqDeriv_taylor {y : ℝ} (hy : |y - 1| ≤ 1 / 2) :
    |logSqDeriv y - 2 * (y - 1)| ≤ 40 * (y - 1) ^ 2 :=
  le_trans (logSqDeriv_taylor_twelve hy) (by nlinarith [sq_nonneg (y - 1)])

end GFNBounds.Balance
