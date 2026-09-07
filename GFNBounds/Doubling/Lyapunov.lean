import GFNBounds.Doubling.Drift
import GFNBounds.Doubling.Cramer

/-!
# The Lyapunov drifts of the phase diagram

**`prop:doubling_phase`, Steps 2, 3, 4, 6 and 8** — `app_doubling.tex:510–624`
(Proposition 99 of the ICLR build), and `theo:doubling_main`(1).

> In the setting of Definition `def:doubling_setting`, let `(c,s)` lie in the standing range and
> let `X` be the loop-closed backward chain on the infinite graph. Then `X` is irreducible, and:
> (1) if `s > 1`, then `X` is positive recurrent; (2) if `s < 1`, then `X` is transient;
> (3) if `s = 1`, then `X` is positive recurrent for `0 < c < 1`, with `E(σ | X₀ = j) = j/(1−c)`
> at every ladder state `j ≥ 1`; for every `1 ≤ c < 2`, `E(σ | X₀ = j) = +∞` and `X` is not
> positive recurrent; and `X` is null recurrent for `1 ≤ c < 1/ln 2` and transient for
> `1/ln 2 < c < 2`.
>
> (Step 2) For `t > 0` define `W_t` on the whole loop closure by `W_t(j) := (j+1)^{−t}` at a
> ladder state `j` and `W_t(s₀) = W_t(s_f) := 1`. There is a constant `Ξ_t < +∞` depending on `t`
> alone such that, at every ladder state `j ≥ 1`, `eq:doubling_Wdrift` holds:
> `E(W_t(X₁) | X₀ = j) − W_t(j) = (j+1)^{−t−1}[t − c(1−2^{−t})(j+1)^{1−s}] + Υ_t(j)` with
> `|Υ_t(j)| ≤ Ξ_t((j+1)^{−t−2} + ε(j)(j+1)^{−t−1})`.

## What this file is, and what it is not

`prop:doubling_phase` is a statement **about a chain**: positive recurrence, null recurrence and
transience. Mathlib v4.31.0 has no discrete-time Markov-chain recurrence theory, so the
conclusions themselves are out of reach here and remain in
`GFNBoundsScaffold.Doubling.Phase`. What is *not* about a chain is the analysis the proof runs
before it invokes Foster's criterion and the bounded-supermartingale transience criterion: the
one-step drifts of the three test functions `V₁ = j` (Step 3), `W_t = (j+1)^{−t}` (Steps 2, 4, 8)
and `V₂ = log(j+1)` (Step 6), and the *sign* of each of them past an explicit ladder index. Those
are identities and inequalities between real numbers, and they are what this file proves.

The one-step conditional expectation `E(f(X₁) | X₀ = j)` is `pstar S cap f (.lad j)`, which is how
`GFNBounds.Doubling.Drift` already reads `prop:doubling_drift`; no trajectory measure is needed.

## SCOPE (disclosed)

* **The chain conclusions are not proved, and are not stated.** No declaration here says
  "positive recurrent", "null recurrent" or "transient". What is delivered is, for each of the
  four Lyapunov steps, an inequality of the form "for every ladder `m` past an explicit `m₀`, the
  drift of the test function at `m` has the required sign", which is precisely the hypothesis
  Foster's criterion and the transience criterion consume. Steps 1, 5 and 7 are elsewhere:
  Step 1 is `lem:doubling_irreducible` (`Irreducible.lean`), Step 5 is
  `lem:doubling_supersolution` (`Supersolution.lean`), and Step 7 needs optional stopping
  (`prop:doubling_length`, open).
* **Step 2 is proved in an effective form, and it is stronger than the paper's.** The paper's
  `Ξ_t` is non-effective ("a constant depending on `t` alone"). Here `Ξ_t = max(3t/2 + C_t/4, C_t)`
  with `C_t = 2t + 4t²`, valid at every ladder `m` with `4t ≤ m+1`; that side condition is the
  price of an explicit constant and is disclosed in the hypothesis. The paper states the expansion
  with no lower bound on `j`, its `O(·)` remainders being asymptotic.
* **Steps 4, 6 and the `s > 1` half of Step 3 are proved without the expansion at all**, by exact
  identities: the `t = 1` drift is the rational function `Wpow_one_drift`, the `V₂` drift is
  bounded by two logarithm inequalities, and the `V₁` drift is `prop:doubling_drift` itself. Those
  three are therefore free of the `4t ≤ m+1` restriction and of `Ξ`.
* **Row (d) of the phase diagram, `c = 1/ln 2`, is open in the paper** (`app_doubling.tex:626`)
  and is not touched. Step 8's hypothesis is the strict `t ln 2 < c ln 2 − 1`, which is
  `0 < t < c − 1/ln 2` and is empty exactly when `c ≤ 1/ln 2`.
* `φ(t) := c(1 − 2^{−t}) − t` of Step 8 is `−ψ(−t)` for the `ψ` of `lem:doubling_cramer_root`
  (`phi_eq_neg_psi`), so the admissible `t` are the negatives of the interval between the two
  Cramér roots. `phi_pos` does not go through that root: it gives the explicit window
  `0 < t < c − 1/ln 2` from `2^t ≥ 1 + t ln 2` alone.

## Hypothesis checklist against `prop:doubling_phase`

| paper hypothesis | here |
|---|---|
| standing range `s ≥ 0`, `0 < c < 2^s` | ⚠ weakened: each step carries only what it uses — `0 < c` and `1 < s` (Step 3), `0 < c` and `s < 1` (Step 4), `0 ≤ c` and `c ln 2 < 1` (Step 6), `0 ≤ c` and `0 < t < c − 1/ln 2` (Step 8) |
| the loop closure | ⚠ weakened: stated for any `cap`, at a ladder state whose doubling edge survives |
| ladder state `j ≥ 1` | ✓ carried (`hm`) |
| `ε = ε_{c,s}` | ✓ carried, pointwise on the ladder (`heps`) |
| Step 2's `Ξ_t` depends on `t` alone | ✓ carried and made explicit; ⚠ strengthened by the side condition `4t ≤ m+1` |
| Foster's criterion, the transience criterion, optional stopping, the strong Markov property | ✗ not available; the conclusions they yield are not stated |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-! ## The two test functions -/

/-- `W_t` of Step 2: `(j+1)^{−t}` at a ladder state, `1` at the sink.

`W_t(s₀) = 1` needs no separate clause: `s₀ = lad 0` and `(0+1)^{−t} = 1`. -/
noncomputable def Wpow (t : ℝ) : St → ℝ
  | .lad j => ((j : ℝ) + 1) ^ (-t)
  | .sink => 1

@[simp] theorem Wpow_lad (t : ℝ) (j : ℕ) : Wpow t (.lad j) = ((j : ℝ) + 1) ^ (-t) := rfl
@[simp] theorem Wpow_sink (t : ℝ) : Wpow t .sink = 1 := rfl

theorem Wpow_src (t : ℝ) : Wpow t .src = 1 := by
  simp [Wpow]

/-- `V₂` of Step 6: `log(j+1)` at a ladder state, `0` at the sink. Again `V₂(s₀) = 0` is
automatic. -/
noncomputable def logHeight : St → ℝ
  | .lad j => Real.log ((j : ℝ) + 1)
  | .sink => 0

@[simp] theorem logHeight_lad (j : ℕ) : logHeight (.lad j) = Real.log ((j : ℝ) + 1) := rfl
@[simp] theorem logHeight_sink : logHeight .sink = 0 := rfl

theorem logHeight_src : logHeight .src = 0 := by
  simp [logHeight]

variable {S : Setting} {cap : Option ℕ}

theorem cast_pred {m : ℕ} (hm : 1 ≤ m) : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
  have h : (1 : ℕ) ≤ m := hm
  push_cast [Nat.cast_sub h]; ring

/-! ## The exact one-step drifts

These are the displays the paper's Step 2 and Step 6 start from, before any expansion: the chain
doubles to `2m` with probability `ε(m)` and decrements to `m−1` otherwise. -/

/-- The exact one-step drift of `W_t` at a ladder state carrying its doubling edge. This is the
first display of Step 2. -/
theorem Wpow_pstar_sub (t : ℝ) {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m) :
    pstar S cap (Wpow t) (.lad m) - Wpow t (.lad m)
      = S.eps m * ((2 * (m : ℝ) + 1) ^ (-t) - ((m : ℝ) + 1) ^ (-t))
        + (1 - S.eps m) * ((m : ℝ) ^ (-t) - ((m : ℝ) + 1) ^ (-t)) := by
  rw [pstar_lad_of_hasDouble hm hD]
  simp only [Wpow_lad]
  rw [cast_pred hm]
  push_cast
  ring_nf

/-- The exact one-step drift of `V₂ = log(j+1)`. This is the first display of Step 6. -/
theorem logHeight_pstar_sub {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m) :
    pstar S cap logHeight (.lad m) - logHeight (.lad m)
      = S.eps m * (Real.log (2 * (m : ℝ) + 1) - Real.log ((m : ℝ) + 1))
        + (1 - S.eps m) * (Real.log (m : ℝ) - Real.log ((m : ℝ) + 1)) := by
  rw [pstar_lad_of_hasDouble hm hD]
  simp only [logHeight_lad]
  rw [cast_pred hm]
  push_cast
  ring_nf

/-! ## The analytic engine of Step 2

The paper's `(1 − x)^{−t} = 1 + tx + O(x²)` with a remainder "bounded in terms of `t` alone",
made two-sided and explicit. `remC t = 2t + 4t²` is that constant. -/

/-- The tangent-line lower bound `(1 − x)^{−t} ≥ 1 + tx`. -/
theorem one_add_mul_le_one_sub_rpow_neg {t x : ℝ} (ht : 0 ≤ t) (hx1 : x < 1) :
    1 + t * x ≤ (1 - x) ^ (-t) := by
  have hpos : (0:ℝ) < 1 - x := by linarith
  rw [Real.rpow_def_of_pos hpos]
  have hlog : Real.log (1 - x) ≤ -x := by
    have := Real.log_le_sub_one_of_pos hpos; linarith
  have h : t * x ≤ Real.log (1 - x) * (-t) := by nlinarith
  calc 1 + t * x ≤ Real.exp (t * x) := by
        have := Real.add_one_le_exp (t * x); linarith
    _ ≤ _ := Real.exp_le_exp.mpr h

/-- The explicit second-order constant of the expansion, `C_t = 2t + 4t²`. -/
noncomputable def remC (t : ℝ) : ℝ := 2 * t + 4 * t ^ 2

theorem remC_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ remC t := by
  unfold remC; positivity

/-- The matching upper bound `(1 − x)^{−t} ≤ 1 + tx + C_t x²`, on `0 ≤ x ≤ 1/2` with `tx ≤ 1/4`.

The two side conditions are what buys the constant: `−log(1−x) ≤ x + 2x²` needs `x ≤ 1/2`, and
`exp y ≤ 1 + y + y²` needs `y ≤ 1`, which `tx ≤ 1/4` supplies. -/
theorem one_sub_rpow_neg_le {t x : ℝ} (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (htx : t * x ≤ 1/4) : (1 - x) ^ (-t) ≤ 1 + t * x + remC t * x ^ 2 := by
  have hpos : (0:ℝ) < 1 - x := by linarith
  set y : ℝ := t * (x + 2 * x ^ 2) with hy
  have h1 : -Real.log (1 - x) ≤ (1 - x)⁻¹ - 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (1 - x)⁻¹) (by positivity)
    rwa [Real.log_inv] at h
  have h2 : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  have h3 : x / (1 - x) ≤ x + 2 * x ^ 2 := by rw [div_le_iff₀ hpos]; nlinarith
  have h4 : -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by rw [h2] at h1; linarith
  have hlogle : Real.log (1 - x) * (-t) ≤ y := by rw [hy]; nlinarith
  have hy0 : 0 ≤ y := by positivity
  have hxx : x + 2 * x ^ 2 ≤ 2 * x := by nlinarith
  have hy1 : y ≤ 1 := by rw [hy]; nlinarith
  have hexp : Real.exp y ≤ 1 + y + 3/4 * y ^ 2 := by
    have h := Real.exp_bound' hy0 hy1 (n := 2) (by norm_num)
    simp [Finset.sum_range_succ] at h
    nlinarith [h]
  have hysq : y ^ 2 ≤ 4 * t ^ 2 * x ^ 2 := by
    have hsq : (x + 2 * x ^ 2) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith
    have hyy : y ^ 2 = t ^ 2 * (x + 2 * x ^ 2) ^ 2 := by rw [hy]; ring
    nlinarith [sq_nonneg t]
  rw [Real.rpow_def_of_pos hpos, remC]
  calc Real.exp (Real.log (1 - x) * (-t)) ≤ Real.exp y := Real.exp_le_exp.mpr hlogle
    _ ≤ 1 + y + 3/4 * y ^ 2 := hexp
    _ ≤ 1 + t * x + (2 * t + 4 * t ^ 2) * x ^ 2 := by rw [hy]; nlinarith

/-- `2j+1 = 2(j+1)(1 − 1/(2(j+1)))`, the paper's first factorisation, at the level of `rpow`. -/
theorem shift_double (t : ℝ) {u : ℝ} (hu1 : 1 ≤ u) :
    (2 * u - 1) ^ (-t) = (2:ℝ) ^ (-t) * u ^ (-t) * (1 - 1/(2*u)) ^ (-t) := by
  have hu : (0:ℝ) < u := by linarith
  have h2u : (0:ℝ) < 2 * u := by linarith
  have hnn : (0:ℝ) ≤ 1 - 1/(2*u) := by
    have h : 1/(2*u) ≤ 1 := by rw [div_le_one h2u]; linarith
    linarith
  have hfac : 2 * u - 1 = (2 * u) * (1 - 1/(2*u)) := by field_simp
  rw [hfac, Real.mul_rpow (by linarith) hnn, Real.mul_rpow (by norm_num) hu.le]

/-- `j = (j+1)(1 − 1/(j+1))`, the paper's second factorisation. -/
theorem shift_dec (t : ℝ) {u : ℝ} (hu1 : 1 ≤ u) :
    (u - 1) ^ (-t) = u ^ (-t) * (1 - 1/u) ^ (-t) := by
  have hu : (0:ℝ) < u := by linarith
  have hnn : (0:ℝ) ≤ 1 - 1/u := by
    have h : 1/u ≤ 1 := by rw [div_le_one hu]; linarith
    linarith
  have hfac : u - 1 = u * (1 - 1/u) := by field_simp
  rw [hfac, Real.mul_rpow hu.le hnn]

/-- The remainder of Step 2, collected: `|e·h·a + (1−e)·b − e·t·x₂|` is at most the sum of the
three bounds, for `e, h ∈ [0,1]` and `a, b` in their windows. -/
theorem drift_remainder_bound {e a b tt xone xtwo C h : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (ha0 : 0 ≤ a) (hahi : a ≤ tt * xone + C * xone ^ 2)
    (hb0 : 0 ≤ b) (hbhi : b ≤ C * xtwo ^ 2)
    (ht0 : 0 ≤ tt) (hx2 : 0 ≤ xtwo) (hC : 0 ≤ C) (hx1 : 0 ≤ xone) :
    |e * h * a + (1 - e) * b - e * tt * xtwo|
      ≤ e * (tt * xone + C * xone ^ 2) + C * xtwo ^ 2 + e * tt * xtwo := by
  have hub : e * h * a + (1 - e) * b - e * tt * xtwo
      ≤ e * (tt * xone + C * xone ^ 2) + C * xtwo ^ 2 + e * tt * xtwo := by
    have h1a : e * h * a ≤ e * a := by nlinarith [mul_nonneg he0 ha0]
    have h1b : e * a ≤ e * (tt * xone + C * xone ^ 2) := mul_le_mul_of_nonneg_left hahi he0
    have h2a : (1 - e) * b ≤ b := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg he0 ht0) hx2, le_trans h1a h1b, le_trans h2a hbhi]
  have hlb : -(e * (tt * xone + C * xone ^ 2) + C * xtwo ^ 2 + e * tt * xtwo)
      ≤ e * h * a + (1 - e) * b - e * tt * xtwo := by
    have h1 : 0 ≤ e * h * a := by positivity
    have h2 : 0 ≤ (1 - e) * b := by nlinarith
    have h3 : 0 ≤ e * (tt * xone + C * xone ^ 2) := mul_nonneg he0 (by positivity)
    have h4 : 0 ≤ C * xtwo ^ 2 := by positivity
    nlinarith
  exact abs_le.mpr ⟨hlb, hub⟩

/-- **Step 2, the real-analytic core.** The drift of `u ↦ u^{−t}` under one step that multiplies
`u` by `2 − 1/u` with probability `e` and by `1 − 1/u` otherwise, against its first-order term,
with an explicit remainder. -/
theorem Wdrift_core {t e u : ℝ} (ht : 0 ≤ t) (hu2 : 2 ≤ u) (hmt : 4 * t ≤ u)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |e * ((2 * u - 1) ^ (-t) - u ^ (-t)) + (1 - e) * ((u - 1) ^ (-t) - u ^ (-t))
        - u ^ (-t) * (t / u - e * (1 - (2:ℝ) ^ (-t)))|
      ≤ (3 * t / 2 + remC t / 4) * e * (u ^ (-t) / u) + remC t * (u ^ (-t) / u ^ 2) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hut : (0:ℝ) < u ^ (-t) := Real.rpow_pos_of_pos hu0 _
  have hCC : 0 ≤ remC t := remC_nonneg ht
  have hx1_0 : (0:ℝ) ≤ 1 / (2 * u) := by positivity
  have hx2_0 : (0:ℝ) ≤ 1 / u := by positivity
  have hx2_half : 1 / u ≤ 1/2 := by rw [div_le_div_iff₀ hu0 (by norm_num)]; linarith
  have hx1_half : 1 / (2 * u) ≤ 1/2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hx2_t : t * (1 / u) ≤ 1/4 := by
    rw [mul_one_div, div_le_div_iff₀ hu0 (by norm_num)]; linarith
  have hx1_t : t * (1 / (2 * u)) ≤ 1/4 := by
    have h : (1:ℝ) / (2 * u) ≤ 1 / u := by rw [div_le_div_iff₀ (by linarith) hu0]; linarith
    nlinarith
  have hAlo := one_add_mul_le_one_sub_rpow_neg (t := t) (x := 1 / (2 * u)) ht (by linarith)
  have hAhi := one_sub_rpow_neg_le (t := t) (x := 1 / (2 * u)) ht hx1_0 hx1_half hx1_t
  have hBlo := one_add_mul_le_one_sub_rpow_neg (t := t) (x := 1 / u) ht (by linarith)
  have hBhi := one_sub_rpow_neg_le (t := t) (x := 1 / u) ht hx2_0 hx2_half hx2_t
  have hh0 : (0:ℝ) ≤ (2:ℝ) ^ (-t) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hh1 : (2:ℝ) ^ (-t) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr ht)
  have hid : e * ((2 * u - 1) ^ (-t) - u ^ (-t)) + (1 - e) * ((u - 1) ^ (-t) - u ^ (-t))
        - u ^ (-t) * (t / u - e * (1 - (2:ℝ) ^ (-t)))
      = u ^ (-t) * (e * (2:ℝ) ^ (-t) * ((1 - 1 / (2 * u)) ^ (-t) - 1)
          + (1 - e) * ((1 - 1 / u) ^ (-t) - 1 - t * (1 / u)) - e * t * (1 / u)) := by
    rw [shift_double t hu1, shift_dec t hu1]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos hut]
  have hb := drift_remainder_bound (e := e) (a := (1 - 1 / (2 * u)) ^ (-t) - 1)
      (b := (1 - 1 / u) ^ (-t) - 1 - t * (1 / u)) (tt := t) (xone := 1 / (2 * u))
      (xtwo := 1 / u) (C := remC t) (h := (2:ℝ) ^ (-t))
      he0 he1 hh0 hh1 (by nlinarith) (by linarith) (by nlinarith) (by linarith)
      ht hx2_0 hCC hx1_0
  have hfin : e * (t * (1 / (2 * u)) + remC t * (1 / (2 * u)) ^ 2) + remC t * (1 / u) ^ 2
        + e * t * (1 / u)
      ≤ (3 * t / 2 + remC t / 4) * e * (1 / u) + remC t * (1 / u ^ 2) := by
    have hdiff : ((3 * t / 2 + remC t / 4) * e * (1 / u) + remC t * (1 / u ^ 2))
        - (e * (t * (1 / (2 * u)) + remC t * (1 / (2 * u)) ^ 2) + remC t * (1 / u) ^ 2
            + e * t * (1 / u)) = e * remC t * (u - 1) / (4 * u ^ 2) := by
      field_simp
      ring
    have hnn : 0 ≤ e * remC t * (u - 1) / (4 * u ^ 2) :=
      div_nonneg (mul_nonneg (mul_nonneg he0 hCC) (by linarith)) (by positivity)
    linarith
  calc u ^ (-t) * |e * (2:ℝ) ^ (-t) * ((1 - 1 / (2 * u)) ^ (-t) - 1)
          + (1 - e) * ((1 - 1 / u) ^ (-t) - 1 - t * (1 / u)) - e * t * (1 / u)|
      ≤ u ^ (-t) * (e * (t * (1 / (2 * u)) + remC t * (1 / (2 * u)) ^ 2) + remC t * (1 / u) ^ 2
          + e * t * (1 / u)) := mul_le_mul_of_nonneg_left hb hut.le
    _ ≤ u ^ (-t) * ((3 * t / 2 + remC t / 4) * e * (1 / u) + remC t * (1 / u ^ 2)) :=
        mul_le_mul_of_nonneg_left hfin hut.le
    _ = (3 * t / 2 + remC t / 4) * e * (u ^ (-t) / u) + remC t * (u ^ (-t) / u ^ 2) := by
        field_simp

theorem rpow_div_self {u : ℝ} (hu : 0 < u) (t : ℝ) : u ^ (-t) / u = u ^ (-t - 1) := by
  rw [Real.rpow_sub hu, Real.rpow_one]

theorem rpow_div_sq {u : ℝ} (hu : 0 < u) (t : ℝ) : u ^ (-t) / u ^ 2 = u ^ (-t - 2) := by
  have h2 : u ^ ((2:ℕ) : ℝ) = u ^ (2:ℕ) := Real.rpow_natCast u 2
  have hc : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
  rw [hc] at h2
  rw [Real.rpow_sub hu, h2]

/-- **Step 2 at a `Setting`, for a free `ε`.** -/
theorem Wpow_drift_expansion {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m)
    (hmt : 4 * t ≤ (m : ℝ) + 1) :
    |pstar S cap (Wpow t) (.lad m) - Wpow t (.lad m)
        - ((m:ℝ) + 1) ^ (-t) * (t / ((m:ℝ) + 1) - S.eps m * (1 - (2:ℝ) ^ (-t)))|
      ≤ (3 * t / 2 + remC t / 4) * S.eps m * (((m:ℝ) + 1) ^ (-t) / ((m:ℝ) + 1))
        + remC t * (((m:ℝ) + 1) ^ (-t) / ((m:ℝ) + 1) ^ 2) := by
  have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hu2 : (2:ℝ) ≤ (m:ℝ) + 1 := by linarith
  have he0 : 0 ≤ S.eps m := (S.eps_pos hm).le
  have he1 : S.eps m ≤ 1 := le_trans (S.eps_le hm) S.epsMax_lt_one.le
  have hcore := Wdrift_core (t := t) (e := S.eps m) (u := (m:ℝ) + 1) ht hu2 hmt he0 he1
  have h1 : 2 * ((m:ℝ) + 1) - 1 = 2 * (m:ℝ) + 1 := by ring
  have h2 : ((m:ℝ) + 1) - 1 = (m:ℝ) := by ring
  rw [h1, h2] at hcore
  rw [Wpow_pstar_sub t hm hD]
  exact hcore

/-- The paper's `Ξ_t`, made explicit. -/
noncomputable def Xi (t : ℝ) : ℝ := max (3 * t / 2 + remC t / 4) (remC t)

theorem Xi_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Xi t :=
  le_trans (remC_nonneg ht) (le_max_right _ _)

/-- **`eq:doubling_Wdrift`.** The Lyapunov expansion of Step 2 on the family `ε_{c,s}`, with the
explicit `Ξ_t` of `Xi`, at every ladder state `m ≥ 1` with `4t ≤ m+1`. -/
theorem Wdrift_family {c s t : ℝ} (ht : 0 ≤ t)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = epsCS c s j)
    {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m) (hmt : 4 * t ≤ (m:ℝ) + 1) :
    |pstar S cap (Wpow t) (.lad m) - Wpow t (.lad m)
        - ((m:ℝ) + 1) ^ (-t - 1) * (t - c * (1 - (2:ℝ) ^ (-t)) * ((m:ℝ) + 1) ^ (1 - s))|
      ≤ Xi t * (((m:ℝ) + 1) ^ (-t - 2) + S.eps m * ((m:ℝ) + 1) ^ (-t - 1)) := by
  have hu0 : (0:ℝ) < (m:ℝ) + 1 := base_pos m
  have he0 : 0 ≤ S.eps m := (S.eps_pos hm).le
  have h1 : ((m:ℝ) + 1) ^ (-t) / ((m:ℝ) + 1) = ((m:ℝ) + 1) ^ (-t - 1) := rpow_div_self hu0 t
  have hA : ((m:ℝ) + 1) ^ (-t) * (t / ((m:ℝ) + 1)) = t * ((m:ℝ) + 1) ^ (-t - 1) := by
    rw [← h1]; ring
  have hB : ((m:ℝ) + 1) ^ (-t) * (c / ((m:ℝ) + 1) ^ s) = c * ((m:ℝ) + 1) ^ (-t - s) := by
    rw [Real.rpow_sub hu0]; ring
  have hC : ((m:ℝ) + 1) ^ (-t - 1) * ((m:ℝ) + 1) ^ (1 - s) = ((m:ℝ) + 1) ^ (-t - s) := by
    rw [← Real.rpow_add hu0]; congr 1; ring
  have hmain : ((m:ℝ) + 1) ^ (-t) * (t / ((m:ℝ) + 1) - S.eps m * (1 - (2:ℝ) ^ (-t)))
      = ((m:ℝ) + 1) ^ (-t - 1) * (t - c * (1 - (2:ℝ) ^ (-t)) * ((m:ℝ) + 1) ^ (1 - s)) := by
    calc ((m:ℝ) + 1) ^ (-t) * (t / ((m:ℝ) + 1) - S.eps m * (1 - (2:ℝ) ^ (-t)))
        = ((m:ℝ) + 1) ^ (-t) * (t / ((m:ℝ) + 1))
          - ((m:ℝ) + 1) ^ (-t) * (c / ((m:ℝ) + 1) ^ s) * (1 - (2:ℝ) ^ (-t)) := by
          rw [heps m hm, epsCS]; ring
      _ = t * ((m:ℝ) + 1) ^ (-t - 1)
          - c * ((m:ℝ) + 1) ^ (-t - s) * (1 - (2:ℝ) ^ (-t)) := by rw [hA, hB]
      _ = ((m:ℝ) + 1) ^ (-t - 1) * (t - c * (1 - (2:ℝ) ^ (-t)) * ((m:ℝ) + 1) ^ (1 - s)) := by
          rw [← hC]; ring
  have hbase := Wpow_drift_expansion (S := S) (cap := cap) ht hm hD hmt
  rw [hmain] at hbase
  refine le_trans hbase ?_
  rw [h1, rpow_div_sq hu0 t]
  have hp1 : (0:ℝ) < ((m:ℝ) + 1) ^ (-t - 1) := Real.rpow_pos_of_pos hu0 _
  have hp2 : (0:ℝ) < ((m:ℝ) + 1) ^ (-t - 2) := Real.rpow_pos_of_pos hu0 _
  have hle1 : 3 * t / 2 + remC t / 4 ≤ Xi t := le_max_left _ _
  have hle2 : remC t ≤ Xi t := le_max_right _ _
  have e1 : (3 * t / 2 + remC t / 4) * S.eps m * ((m:ℝ) + 1) ^ (-t - 1)
      ≤ Xi t * (S.eps m * ((m:ℝ) + 1) ^ (-t - 1)) := by
    have hnn : 0 ≤ S.eps m * ((m:ℝ) + 1) ^ (-t - 1) := mul_nonneg he0 hp1.le
    nlinarith
  have e2 : remC t * ((m:ℝ) + 1) ^ (-t - 2) ≤ Xi t * ((m:ℝ) + 1) ^ (-t - 2) :=
    mul_le_mul_of_nonneg_right hle2 hp2.le
  nlinarith

/-! ## Step 3: `s > 1`, the drift of `V₁` is at most `−1/2` past an explicit index -/

/-- The drift of the ladder height at `m` is at most `−1/2` as soon as `c(m+1)^{1−s} ≤ 1/2`.
This is `prop:doubling_drift` read at the family. -/
theorem height_drift_le_neg_half {c s : ℝ} (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = epsCS c s j)
    {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m)
    (hthr : c * ((m:ℝ) + 1) ^ (1 - s) ≤ 1/2) :
    pstar S cap height (.lad m) - height (.lad m) ≤ -(1/2) := by
  rw [height_pstar_sub hm hD, heps m hm, drift_family]
  linarith

/-- An explicit index past which `(m+1)^e ≥ c`, for `c, e > 0`: take `m₀ ≥ c^{1/e}`. -/
theorem exists_threshold_rpow {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → c ≤ ((m:ℝ) + 1) ^ e := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (c ^ (1/e))
  refine ⟨m₀, fun m hm => ?_⟩
  have hcast : (m₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hb : c ^ (1/e) ≤ (m:ℝ) + 1 := by linarith
  have h0 : (0:ℝ) ≤ c ^ (1/e) := (Real.rpow_pos_of_pos hc _).le
  have h := Real.rpow_le_rpow h0 hb he.le
  rwa [← Real.rpow_mul hc.le, one_div, inv_mul_cancel₀ he.ne', Real.rpow_one] at h

/-- **Step 3, the Foster input.** For `s > 1` the drift of `V₁` is at most `−1/2` off a finite
initial segment of the ladder, and the segment is explicit: `m₀ ≥ (2c)^{1/(s−1)}`. -/
theorem exists_height_drift_neg {c s : ℝ} (hc : 0 < c) (hs : 1 < s)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = epsCS c s j) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 1 ≤ m → HasDouble cap m →
      pstar S cap height (.lad m) - height (.lad m) ≤ -(1/2) := by
  obtain ⟨m₀, hm₀⟩ := exists_threshold_rpow (c := 2 * c) (e := s - 1) (by linarith) (by linarith)
  refine ⟨m₀, fun m hm hm1 hD => ?_⟩
  refine height_drift_le_neg_half heps hm1 hD ?_
  have hu0 : (0:ℝ) < (m:ℝ) + 1 := base_pos m
  have hb := hm₀ m hm
  have hpow : ((m:ℝ) + 1) ^ (1 - s) = (((m:ℝ) + 1) ^ (s - 1))⁻¹ := by
    rw [show (1 : ℝ) - s = -(s - 1) by ring, Real.rpow_neg hu0.le]
  have hpos : (0:ℝ) < ((m:ℝ) + 1) ^ (s - 1) := Real.rpow_pos_of_pos hu0 _
  rw [hpow, mul_inv_le_iff₀ hpos]
  linarith

/-! ## Step 4: `s < 1`, `W_1` is a supermartingale past an explicit index

At `t = 1` the drift is an exact rational function of `m`, so this step needs neither the
expansion of Step 2 nor the constant `Ξ`. -/

theorem Wpow_one_lad (j : ℕ) : Wpow 1 (.lad j) = ((j:ℝ) + 1)⁻¹ := by
  rw [Wpow_lad, Real.rpow_neg_one]

/-- **The exact `t = 1` drift.** Its sign is the sign of `2m+1 − ε(m)(m+1)²`. -/
theorem Wpow_one_drift {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m) :
    pstar S cap (Wpow 1) (.lad m) - Wpow 1 (.lad m)
      = (2 * (m:ℝ) + 1 - S.eps m * ((m:ℝ) + 1) ^ 2)
          / ((m:ℝ) * ((m:ℝ) + 1) * (2 * (m:ℝ) + 1)) := by
  have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  rw [pstar_lad_of_hasDouble hm hD, Wpow_one_lad, Wpow_one_lad, Wpow_one_lad, cast_pred hm]
  have h0 : (m:ℝ) ≠ 0 := by linarith
  have h1 : (m:ℝ) + 1 ≠ 0 := by linarith
  have h2 : 2 * (m:ℝ) + 1 ≠ 0 := by linarith
  have h3 : ((2 * m : ℕ) : ℝ) + 1 = 2 * (m:ℝ) + 1 := by push_cast; ring
  have h4 : (m:ℝ) - 1 + 1 = (m:ℝ) := by ring
  rw [h3, h4]
  field_simp
  ring

/-- The exact criterion of Step 4: `W_1` has non-positive drift at `m` iff
`ε(m)(m+1)² ≥ 2m+1`. -/
theorem Wpow_one_drift_nonpos {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m)
    (hthr : 2 * (m:ℝ) + 1 ≤ S.eps m * ((m:ℝ) + 1) ^ 2) :
    pstar S cap (Wpow 1) (.lad m) - Wpow 1 (.lad m) ≤ 0 := by
  have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  rw [Wpow_one_drift hm hD]
  apply div_nonpos_of_nonpos_of_nonneg (by linarith)
  positivity

/-- On the family, `c(m+1)^{1−s} ≥ 2` suffices for that criterion. -/
theorem eps_family_sq {c s : ℝ} {m : ℕ} (hm : 1 ≤ m) (hthr : 2 ≤ c * ((m:ℝ) + 1) ^ (1 - s)) :
    2 * (m:ℝ) + 1 ≤ epsCS c s m * ((m:ℝ) + 1) ^ 2 := by
  have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hu0 : (0:ℝ) < (m:ℝ) + 1 := base_pos m
  have hkey : epsCS c s m * ((m:ℝ) + 1) ^ 2 = c * ((m:ℝ) + 1) ^ (1 - s) * ((m:ℝ) + 1) := by
    rw [epsCS, Real.rpow_sub hu0, Real.rpow_one]
    field_simp
  rw [hkey]
  nlinarith

/-- **Step 4, the transience input.** For `s < 1` and `c > 0`, `W_1` has non-positive drift at
every ladder state past `m₀ ≥ (2/c)^{1/(1−s)}`. -/
theorem exists_Wpow_one_drift_nonpos {c s : ℝ} (hc : 0 < c) (hs : s < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = epsCS c s j) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 1 ≤ m → HasDouble cap m →
      pstar S cap (Wpow 1) (.lad m) - Wpow 1 (.lad m) ≤ 0 := by
  obtain ⟨m₀, hm₀⟩ := exists_threshold_rpow (c := 2/c) (e := 1 - s) (by positivity) (by linarith)
  refine ⟨m₀, fun m hm hm1 hD => ?_⟩
  refine Wpow_one_drift_nonpos hm1 hD ?_
  rw [heps m hm1]
  refine eps_family_sq hm1 ?_
  have hb := hm₀ m hm
  rw [div_le_iff₀ hc] at hb
  linarith [hb]

/-! ## Step 6: `s = 1`, `c ln 2 < 1`, the drift of `V₂` is non-positive past an explicit index -/

/-- **The Foster input of Step 6**, from two exact logarithm inequalities:
`log(2m+1) − log(m+1) ≤ log 2` and `log m − log(m+1) ≤ −1/(m+1)`. -/
theorem logHeight_drift_nonpos {c : ℝ} (hc0 : 0 ≤ c) {m : ℕ} (hm : 1 ≤ m)
    (hD : HasDouble cap m) (heps : S.eps m = c / ((m:ℝ) + 1))
    (hthr : c ≤ (1 - c * Real.log 2) * ((m:ℝ) + 1)) :
    pstar S cap logHeight (.lad m) - logHeight (.lad m) ≤ 0 := by
  have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hu0 : (0:ℝ) < (m:ℝ) + 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hclu : c ≤ (m:ℝ) + 1 := by nlinarith [mul_nonneg hc0 hlog2.le]
  have heps0 : 0 ≤ S.eps m := (S.eps_pos hm).le
  have heps1 : S.eps m ≤ 1 := by rw [heps, div_le_one hu0]; exact hclu
  have L1 : Real.log (2 * (m:ℝ) + 1) - Real.log ((m:ℝ) + 1) ≤ Real.log 2 := by
    have h : Real.log (2 * (m:ℝ) + 1) ≤ Real.log (2 * ((m:ℝ) + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hu0)] at h
    linarith
  have L2 : Real.log (m:ℝ) - Real.log ((m:ℝ) + 1) ≤ -(1 / ((m:ℝ) + 1)) := by
    have hd : Real.log ((m:ℝ) / ((m:ℝ) + 1)) = Real.log (m:ℝ) - Real.log ((m:ℝ) + 1) :=
      Real.log_div (by linarith) (ne_of_gt hu0)
    have h := Real.log_le_sub_one_of_pos (x := (m:ℝ) / ((m:ℝ) + 1)) (by positivity)
    rw [hd] at h
    have hcalc : (m:ℝ) / ((m:ℝ) + 1) - 1 = -(1 / ((m:ℝ) + 1)) := by field_simp; ring
    linarith [hcalc ▸ h]
  rw [logHeight_pstar_sub hm hD]
  have hA : S.eps m * (Real.log (2 * (m:ℝ) + 1) - Real.log ((m:ℝ) + 1))
      ≤ S.eps m * Real.log 2 := mul_le_mul_of_nonneg_left L1 heps0
  have hB : (1 - S.eps m) * (Real.log (m:ℝ) - Real.log ((m:ℝ) + 1))
      ≤ (1 - S.eps m) * (-(1 / ((m:ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left L2 (by linarith)
  have hfin : S.eps m * Real.log 2 + (1 - S.eps m) * (-(1 / ((m:ℝ) + 1))) ≤ 0 := by
    rw [heps]
    have h1 : c / ((m:ℝ) + 1) ≤ 1 - c * Real.log 2 := by rw [div_le_iff₀ hu0]; linarith
    have h2 : (0:ℝ) < 1 / ((m:ℝ) + 1) := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    have h4 : c / ((m:ℝ) + 1) * Real.log 2 = c * Real.log 2 * (1 / ((m:ℝ) + 1)) := by
      field_simp
    nlinarith [h3, h4]
  linarith

/-- **Step 6, the Foster input, with an explicit index**: `m₀ ≥ c/(1 − c ln 2)`. -/
theorem exists_logHeight_drift_nonpos {c : ℝ} (hc0 : 0 ≤ c)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = epsCS c 1 j) (hclog : c * Real.log 2 < 1) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 1 ≤ m → HasDouble cap m →
      pstar S cap logHeight (.lad m) - logHeight (.lad m) ≤ 0 := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (c / (1 - c * Real.log 2))
  refine ⟨m₀, fun m hm hm1 hD => ?_⟩
  have hcast : (m₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpos : (0:ℝ) < 1 - c * Real.log 2 := by linarith
  refine logHeight_drift_nonpos hc0 hm1 hD ?_ ?_
  · rw [heps m hm1, epsCS, Real.rpow_one]
  · rw [← div_le_iff₀' hpos]
    linarith

/-! ## Step 8: `s = 1`, `c ln 2 > 1`, `W_t` is a strict supermartingale past an explicit index -/

/-- `φ(t) = c(1 − 2^{−t}) − t` of Step 8. -/
noncomputable def phi (c t : ℝ) : ℝ := c * (1 - (2:ℝ) ^ (-t)) - t

/-- `φ` is `ψ` of `lem:doubling_cramer_root` reflected: `φ(t) = −ψ(−t)`. The admissible `t` of
Step 8 are therefore the negatives of the open interval between the two Cramér roots. -/
theorem phi_eq_neg_psi (c t : ℝ) : phi c t = -psi c (-t) := by
  unfold phi psi; ring

/-- **`φ(t) > 0` for `0 < t < c − 1/ln 2`**, from `2^t ≥ 1 + t ln 2` alone. The window is empty
exactly when `c ≤ 1/ln 2`, which is where the paper leaves the classification open. -/
theorem phi_pos {c t : ℝ} (hc0 : 0 ≤ c) (ht : 0 < t)
    (hlt : t * Real.log 2 < c * Real.log 2 - 1) : 0 < phi c t := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden : (0:ℝ) < 1 + t * Real.log 2 := by positivity
  have h2t : (1:ℝ) + t * Real.log 2 ≤ (2:ℝ) ^ t := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have h := Real.add_one_le_exp (Real.log 2 * t)
    have hc : Real.log 2 * t = t * Real.log 2 := by ring
    linarith [hc ▸ h]
  have h2tpos : (0:ℝ) < (2:ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hinv : (2:ℝ) ^ (-t) ≤ 1 / (1 + t * Real.log 2) := by
    rw [Real.rpow_neg (by norm_num), inv_le_iff_one_le_mul₀ h2tpos, one_div, inv_mul_eq_div,
      le_div_iff₀ hden]
    linarith
  have hstep : c * (1 - 1 / (1 + t * Real.log 2)) - t ≤ phi c t := by
    unfold phi; nlinarith
  have hkey : 0 < c * (1 - 1 / (1 + t * Real.log 2)) - t := by
    have hid : c * (1 - 1 / (1 + t * Real.log 2)) - t
        = t * (c * Real.log 2 - 1 - t * Real.log 2) / (1 + t * Real.log 2) := by
      field_simp
      ring
    rw [hid]
    apply div_pos _ hden
    nlinarith
  linarith

/-- **Step 8, the transience input at a fixed `m`.** At `s = 1`, if `Ξ_t(1+c) < φ(t)(m+1)` then
`W_t` strictly decreases in expectation at `m`. -/
theorem Wpow_drift_neg_at_one {c t : ℝ} (ht : 0 < t)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = epsCS c 1 j) {m : ℕ} (hm : 1 ≤ m)
    (hD : HasDouble cap m) (hmt : 4 * t ≤ (m:ℝ) + 1)
    (hthr : Xi t * (1 + c) < phi c t * ((m:ℝ) + 1)) :
    pstar S cap (Wpow t) (.lad m) - Wpow t (.lad m) < 0 := by
  have hu0 : (0:ℝ) < (m:ℝ) + 1 := base_pos m
  have hbase := Wdrift_family (S := S) (cap := cap) (c := c) (s := 1) ht.le heps hm hD hmt
  rw [show (1:ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one] at hbase
  have hepsm : S.eps m = c / ((m:ℝ) + 1) := by rw [heps m hm, epsCS, Real.rpow_one]
  have hrel : ((m:ℝ) + 1) ^ (-t - 2) = ((m:ℝ) + 1) ^ (-t - 1) / ((m:ℝ) + 1) := by
    rw [show (-t - 2 : ℝ) = (-t - 1) - 1 by ring, Real.rpow_sub hu0, Real.rpow_one]
  have hepspow : S.eps m * ((m:ℝ) + 1) ^ (-t - 1) = c * ((m:ℝ) + 1) ^ (-t - 2) := by
    rw [hepsm, hrel]; ring
  have hup : ((m:ℝ) + 1) ^ (-t - 1) = ((m:ℝ) + 1) * ((m:ℝ) + 1) ^ (-t - 2) := by
    rw [hrel]; field_simp
  have hp2 : (0:ℝ) < ((m:ℝ) + 1) ^ (-t - 2) := Real.rpow_pos_of_pos hu0 _
  have habs := abs_le.mp hbase
  have hle : pstar S cap (Wpow t) (.lad m) - Wpow t (.lad m)
      ≤ ((m:ℝ) + 1) ^ (-t - 1) * (t - c * (1 - (2:ℝ) ^ (-t)))
        + Xi t * (((m:ℝ) + 1) ^ (-t - 2) + S.eps m * ((m:ℝ) + 1) ^ (-t - 1)) := by
    linarith [habs.2]
  rw [hepspow] at hle
  have hcollect : ((m:ℝ) + 1) ^ (-t - 1) * (t - c * (1 - (2:ℝ) ^ (-t)))
      + Xi t * (((m:ℝ) + 1) ^ (-t - 2) + c * ((m:ℝ) + 1) ^ (-t - 2))
      = (Xi t * (1 + c) - phi c t * ((m:ℝ) + 1)) * ((m:ℝ) + 1) ^ (-t - 2) := by
    rw [hup]; unfold phi; ring
  rw [hcollect] at hle
  have hneg : (Xi t * (1 + c) - phi c t * ((m:ℝ) + 1)) * ((m:ℝ) + 1) ^ (-t - 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hp2
  linarith

/-- **Step 8, the transience input, with an explicit index.** For `0 < t < c − 1/ln 2` the
function `W_t` strictly decreases in expectation at every ladder state past
`m₀ ≥ max(4t, Ξ_t(1+c)/φ(t) + 1)`. -/
theorem exists_Wpow_drift_neg {c t : ℝ} (hc0 : 0 ≤ c) (ht : 0 < t)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = epsCS c 1 j)
    (hlt : t * Real.log 2 < c * Real.log 2 - 1) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 1 ≤ m → HasDouble cap m →
      pstar S cap (Wpow t) (.lad m) - Wpow t (.lad m) < 0 := by
  have hphi := phi_pos hc0 ht hlt
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (max (4 * t) (Xi t * (1 + c) / phi c t + 1))
  refine ⟨m₀, fun m hm hm1 hD => ?_⟩
  have hcast : (m₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmax := le_trans hm₀ hcast
  have h4t : 4 * t ≤ (m:ℝ) + 1 := by
    have := le_trans (le_max_left (4 * t) (Xi t * (1 + c) / phi c t + 1)) hmax
    linarith
  have hdiv : Xi t * (1 + c) / phi c t + 1 ≤ (m:ℝ) := by
    exact le_trans (le_max_right (4 * t) (Xi t * (1 + c) / phi c t + 1)) hmax
  have hlt' : Xi t * (1 + c) / phi c t < (m:ℝ) + 1 := by linarith
  refine Wpow_drift_neg_at_one ht heps hm1 hD h4t ?_
  rw [div_lt_iff₀ hphi] at hlt'
  linarith [hlt']

/-! ## The remaining non-chain input to the transience criterion

`W_t` is positive, bounded by `1`, and strictly decreasing along the ladder, so it takes past any
finite initial segment a value strictly below its infimum on that segment — the hypothesis "taking
somewhere off that set a value below its infimum on it" of Steps 4 and 8. -/

theorem Wpow_pos (t : ℝ) (x : St) : 0 < Wpow t x := by
  rcases x with j | _
  · exact Real.rpow_pos_of_pos (base_pos j) _
  · norm_num

theorem Wpow_le_one {t : ℝ} (ht : 0 ≤ t) (x : St) : Wpow t x ≤ 1 := by
  rcases x with j | _
  · refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (neg_nonpos.mpr ht)
    have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith
  · norm_num

theorem Wpow_antitone {t : ℝ} (ht : 0 ≤ t) {i j : ℕ} (h : i ≤ j) :
    Wpow t (.lad j) ≤ Wpow t (.lad i) := by
  refine Real.rpow_le_rpow_of_nonpos (base_pos i) ?_ (neg_nonpos.mpr ht)
  have : (i:ℝ) ≤ (j:ℝ) := Nat.cast_le.mpr h
  linarith

theorem Wpow_strictAnti {t : ℝ} (ht : 0 < t) {i j : ℕ} (h : i < j) :
    Wpow t (.lad j) < Wpow t (.lad i) := by
  refine Real.rpow_lt_rpow_of_neg (base_pos i) ?_ (neg_neg_of_pos ht)
  have : (i:ℝ) < (j:ℝ) := Nat.cast_lt.mpr h
  linarith

/-- Past the finite set `{s₀, s_f, 1, …, j₀}`, `W_t` is strictly below its infimum on it. -/
theorem Wpow_below_inf {t : ℝ} (ht : 0 < t) (j₀ : ℕ) (x : St)
    (hx : x = .sink ∨ ∃ j, j ≤ j₀ ∧ x = .lad j) :
    Wpow t (.lad (j₀ + 1)) < Wpow t x := by
  rcases hx with rfl | ⟨j, hj, rfl⟩
  · rw [Wpow_sink]
    have h1 : Wpow t (.lad (j₀ + 1)) < Wpow t (.lad 0) := Wpow_strictAnti ht (by omega)
    have h2 : Wpow t (St.lad 0) ≤ 1 := Wpow_le_one ht.le _
    linarith
  · exact lt_of_lt_of_le (Wpow_strictAnti ht (by omega)) (Wpow_antitone ht.le hj)

end GFNBounds.Doubling
