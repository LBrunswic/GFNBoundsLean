import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import GFNBounds.Doubling.Expansion
import GFNBounds.Doubling.R0Bound

/-!
# The expansion of `R_α` to second order, with explicit constants

**`lem:doubling_expansion`** — `app_doubling.tex:858–963`
and **`rem:doubling_parity`** — `app_doubling.tex:965–978`.

> (expansion) In the setting of `def:doubling_setting` and `def:doubling_decay_notation`, put
> `A₀ := p(p+3+2τ(p−1))/(2(p+1)(τ−1))`, `A₁ := A₀ − cτ`, `Γ := (τ(p−1)+1)/((τ−1)(p+1))`.
> Then `A₁ = p(p+3−4τ)/(2(p+1)(τ−1))`, `0 < Γ < 1`, `A₀ > 0 > A₁`, and for every `α ∈ ℝ`, as
> `m → ∞`,
> `R_α(m) = 1 + (A_{δ(m)} + Γα)/m + O(m^{−2})`  (`eq:doubling_Rexp`),
> with an implied constant depending on `c` and `α` alone.
>
> (parity) In the notation of `def:doubling_decay_notation`, and with the coefficients `A₀`, `A₁`
> of `lem:doubling_expansion`, the two parities of `eq:doubling_Rexp` differ at order `1/m` by
> `(A₀−A₁)/m = cτ/m`, which is half of the heaviest summand `2cτ/m + O(m^{−2})` of
> `eq:doubling_R` relative to `Φ₀(m)`. Heuristically, the window at odd `m` starts half a step
> later than `m/2`, at `(m+1)/2`, and in a continuum reading of the window sum that half step
> removes half of that summand. Call a positive sequence `(x_j)_{j≥1}` a *supersolution* of
> `eq:doubling_avg` if `x_m ≥ Σ_{j∈W(m)} q_m(j) x_j` for every large enough integer `m`, and a
> *subsolution* of it if the reverse inequality holds for every large enough integer `m`. By
> `eq:doubling_Rexp` at `α = 0` and `eq:doubling_signs`, the pure power `Φ₀(j) = j^{−p}` has
> `R₀(m) > 1` at every large even `m` and `R₀(m) < 1` at every large odd `m`, so it is neither a
> supersolution nor a subsolution of `eq:doubling_avg`.

## What is proved, and where

| paper clause | Lean |
|---|---|
| closed form of `A₁`; `0 < Γ < 1`; `A₀ > 0 > A₁` | `Decay.A_one_eq`, `Gamma_pos`, `Gamma_lt_one`, `A_zero_pos`, `A_one_neg` (in `GFNBounds/Doubling/Expansion.lean`, strict) |
| `eq:doubling_Rexp`, effective | `Decay.Rexp`: `|R_α(m) − 1 − (A_{δ(m)} + Γα)/m| ≤ 16τ(p+3)²(1+|α|)²/m²` for every `m ≥ 1` with `2|α| ≤ m` |
| `eq:doubling_Rexp`, as `O(m^{−2})` | `Decay.Rexp_isBigO` |
| "implied constant depending on `c` and `α` alone" | `Decay.cR_congr` (`p_congr`: `p = p_*(c)`) |
| gap `(A₀−A₁)/m = cτ/m` | `Decay.A_gap` (strict) |
| heaviest summand, `2cτ/m + O(m^{−2})` | `Decay.wm_le_foot` (the heaviest is at `⌈m/2⌉`), `Decay.wm_foot_expansion` (`|w_m(⌈m/2⌉) − 2cτ/m| ≤ 2τ(p+3)/m²`) |
| `R₀(m) > 1` at large even `m` | `Decay.Ralpha_zero_gt_one_of_even`, `Decay.R0_gt_one_of_even`: every even `m > 16τ(p+3)²/A₀` |
| `R₀(m) < 1` at large odd `m` | `Decay.Ralpha_zero_lt_one_of_odd`, `Decay.R0_lt_one_of_odd`: every odd `m > 16τ(p+3)²/(−A₁)` |
| super/subsolution | `Decay.IsSupersolution`, `Decay.IsSubsolution` |
| `Φ₀` neither | `Decay.not_isSupersolution_Phi_zero`, `Decay.not_isSubsolution_Phi_zero` |

## SCOPE (disclosed)

**The `O(m^{−2})` is explicit** (rule 3). `Decay.cR α = 16 τ (p+3)² (1+|α|)²`, valid at *every*
integer `m ≥ 1` with `2|α| ≤ m` — every `m` at which the paper defines `R_α(m)`
(`m > max(d, 2|α|)` forces both), so nothing is lost by stating it there, and `d` does not occur in
`R_α`. The constant is crude: against exact window sums (mpmath, `c ∈ {0.05, 0.3, 0.5, 0.9, 0.99}`,
`α ∈ {0, 0.5, −3, 10}`, admissible `m < 80`) the error times `m²` stays below `0.0024 · cR α`,
and at `m = 3000` it is of order `10⁻²`–`30` against a `cR` of order `10³`–`10⁷`. The parity thresholds
inherit it. The heaviest-summand bound `2τ(p+3)/m²` is tighter (ratio up to `0.74`, `m < 200`).
It depends on `c` alone through `p` and `τ`; `cR_congr` and `parity_thresholds_congr` certify
that, since `Decay` carries `p` as a field.

**Step 2 is not the paper's Step 2.** The paper applies Euler–Maclaurin to `t^{−r}` and bounds the
remainder by complete monotonicity, `|E| ≤ (r/12)(a^{−r−1} + b^{−r−1})`. That remainder bound is
not certified here. Instead Mathlib's trapezoidal rule (`trapezoidal_error_le_of_c2`), applied on
each unit interval `[j, j+1]`, gives `window_sum_second`:
`Σ_{j=a}^{b−1} j^{−r} = (a^{1−r} − b^{1−r})/(r−1) + (a^{−r} − b^{−r})/2 + E` with
`|E| ≤ r(r+1)/12 · Σ_{j=a}^{b−1} j^{−r−2}`, which is `O(m^{−r−1})` on the window, the order the
paper's Step 3 consumes. Steps 1 (`pf_eq`, `abs_ePf_le`) and 3 (`T_expansion`, `Ralpha_eq`,
`coeff_identity`) follow the paper, every `O(·)` replaced by an explicit bound; the ceiling enters
through `u = 2⌈m/2⌉/m = 1 + δ(m)/m` and the Bernoulli bounds
`1 − qy ≤ (1+y)^{−q} ≤ 1 − qy + q²y²`.

**Modelling choices.**
* `A_{δ(m)}` is `Decay.Ad m := if δ(m) = 0 then A₀ else A₁`; `Ad_eq` gives `A₀ − cτδ(m)`.
* `R₀` exists twice in the library: `Decay.R0` (`R0Bound.lean`, the total window weight) and
  `Decay.Ralpha 0` (`eq:doubling_R` at `α = 0`). `R0_eq_Ralpha_zero` identifies them at `m ≥ 1`,
  and the parity statements are given on both.
* `Φ₀` is `Decay.Phi 0`, i.e. `j ↦ j^{−p−1}·j`, which is `j^{−p}` and positive at `j ≥ 1`
  (`Phi_zero_pos`); at `j = 0` it is `0`, an index outside the paper's range that no window
  `W(m)`, `m ≥ 1`, contains.
* `IsSupersolution`/`IsSubsolution` are predicates on any `ℕ → ℝ`; the paper's word *positive* is
  not in them. Both uses here are negative statements about `Φ₀`, which is positive on `j ≥ 1`, so
  the omission neither weakens nor strengthens them. "For every large enough integer `m`" is
  `∃ M, ∀ m ≥ M`. Neither predicate is empty on positive sequences: `2^j` is a supersolution
  (`isSupersolution_two_pow`) and `1/(j!)²` a subsolution (`isSubsolution_inv_factorial_sq`).
* The heuristic continuum sentence of `rem:doubling_parity` is marked heuristic in the paper and is
  not a target.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1` | ✓ carried, as the shape of `Decay.eps` |
| `0 < c < 1` | ✓ carried (`Decay.c_pos`, `Decay.c_lt_one`) |
| `p = p_*`, `τ = 2^p` | ✓ carried (`Decay.root`, `Decay.p_ne`, `Decay.tau`); inhabited, `nonempty_decay` |
| `α ∈ ℝ` arbitrary | ✓ carried |
| `m > max(d, 2|α|)` (domain of `R_α`) | ⚠ weakened to `1 ≤ m`, `2|α| ≤ m`: implied by the paper's, see SCOPE |
| "as `m → ∞`" | ✓ both forms: explicit bound at every admissible `m` (`Rexp`), and `=O[atTop]` (`Rexp_isBigO`) |
| positive sequence `(x_j)` (super/subsolution) | ⚠ not in the predicate; immaterial to the two negative claims, see SCOPE |
| "large even/odd `m`" | ✓ explicit thresholds `16τ(p+3)²/A₀`, `16τ(p+3)²/(−A₁)` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Set intervalIntegral

/-! ## Step 2: the window sum to second order, by the trapezoidal rule -/

section Trapezoid

/-- **One trapezoid.** For `s > 0`, `s ≠ 1`, `t > 0`, the trapezoidal rule on `[t, t+1]` for
`x ↦ x^{−s}`, whose integral is `(t^{1−s} − (t+1)^{1−s})/(s−1)`, errs by at most
`s(s+1) t^{−s−2}/12`. -/
theorem trap_unit {s t : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) (ht : 0 < t) :
    |(t ^ (-s) + (t + 1) ^ (-s)) / 2 - (t ^ (1 - s) - (t + 1) ^ (1 - s)) / (s - 1)|
      ≤ s * (s + 1) * t ^ (-s - 2) / 12 := by
  set f : ℝ → ℝ := fun x => x ^ (-s) with hf
  have hlt : t < t + 1 := by linarith
  have hI : uIcc t (t + 1) = Icc t (t + 1) := uIcc_of_le hlt.le
  have hpos : ∀ x ∈ uIcc t (t + 1), 0 < x := by
    intro x hx; rw [hI] at hx; linarith [hx.1]
  have hc2 : ContDiffOn ℝ 2 f (uIcc t (t + 1)) := fun x hx =>
    (Real.contDiffAt_rpow_const_of_ne (hpos x hx).ne').contDiffWithinAt
  have hbound : ∀ x, |iteratedDerivWithin 2 f (uIcc t (t + 1)) x|
      ≤ s * (s + 1) * t ^ (-s - 2) := by
    intro x
    by_cases hx : x ∈ uIcc t (t + 1)
    · have hud : UniqueDiffOn ℝ (uIcc t (t + 1)) := by rw [hI]; exact uniqueDiffOn_Icc hlt
      rw [iteratedDerivWithin_eq_iteratedDeriv hud
        (Real.contDiffAt_rpow_const_of_ne (hpos x hx).ne') hx, iteratedDeriv_eq_iterate,
        Real.iter_deriv_rpow_const]
      have htx : t ≤ x := by rw [hI] at hx; exact hx.1
      have hev : (descPochhammer ℝ 2).eval (-s) = s * (s + 1) := by
        simp only [descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
          one_mul, Nat.cast_zero, Nat.cast_one, sub_zero]
        ring
      rw [hev]
      have hnn : 0 ≤ s * (s + 1) := by positivity
      have hx0 := hpos x hx
      rw [abs_of_nonneg (by positivity)]
      have he : (-s - ((2 : ℕ) : ℝ)) = -s - 2 := by norm_num
      rw [he]
      exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos ht htx (by linarith)) hnn
    · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure]
      · rw [abs_zero]; positivity
      · rwa [hI, closure_Icc, ← hI]
  have h := trapezoidal_error_le_of_c2 hc2 hbound (N := 1) one_pos
  have hint : ∫ x in t..(t + 1), f x = (t ^ (1 - s) - (t + 1) ^ (1 - s)) / (s - 1) := by
    rw [hf]
    have hne : (-s : ℝ) ≠ -1 := by intro h; apply hs1; linarith
    have hzero : (0 : ℝ) ∉ uIcc t (t + 1) := fun h => (lt_irrefl 0) (hpos 0 h)
    rw [integral_rpow (Or.inr ⟨hne, hzero⟩)]
    have e : (-s + 1 : ℝ) = 1 - s := by ring
    rw [e]
    have h1 : (1 - s) ≠ 0 := by intro h; apply hs1; linarith
    have h2 : (s - 1) ≠ 0 := by intro h; apply hs1; linarith
    field_simp
    ring
  rw [trapezoidal_error, trapezoidal_integral_one, hint] at h
  have e2 : (t + 1 - t) = 1 := by ring
  have e3 : |(t + 1) - t| ^ 3 * (s * (s + 1) * t ^ (-s - 2)) / (12 * ((1 : ℕ) : ℝ) ^ 2)
      = s * (s + 1) * t ^ (-s - 2) / 12 := by
    rw [e2]; norm_num
  rw [e3, e2] at h
  have e4 : (1 : ℝ) / 2 * (f t + f (t + 1)) = (t ^ (-s) + (t + 1) ^ (-s)) / 2 := by
    rw [hf]; ring
  rw [e4] at h
  exact h

/-- **`eq:doubling_em`, effectively.** For `s > 1` and integers `1 ≤ a ≤ b`,
`Σ_{j=a}^{b−1} j^{−s} = (a^{1−s} − b^{1−s})/(s−1) + (a^{−s} − b^{−s})/2 + E` with
`|E| ≤ s(s+1)/12 · Σ_{j=a}^{b−1} j^{−s−2}`. -/
theorem window_sum_second {s : ℝ} (hs : 1 < s) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-s)
        - ((a : ℝ) ^ (1 - s) - (b : ℝ) ^ (1 - s)) / (s - 1)
        - ((a : ℝ) ^ (-s) - (b : ℝ) ^ (-s)) / 2|
      ≤ s * (s + 1) / 12 * ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-s - 2) := by
  have hs0 : 0 < s := by linarith
  have hs1 : s ≠ 1 := ne_of_gt hs
  set f : ℕ → ℝ := fun j => (j : ℝ) ^ (-s) with hf
  set F : ℕ → ℝ := fun j => (j : ℝ) ^ (1 - s) / (s - 1) with hF
  have hcast : ∀ j : ℕ, (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := fun j => by push_cast; ring
  have hkey : ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-s)
        - ((a : ℝ) ^ (1 - s) - (b : ℝ) ^ (1 - s)) / (s - 1)
        - ((a : ℝ) ^ (-s) - (b : ℝ) ^ (-s)) / 2
      = ∑ j ∈ Finset.Ico a b,
          (((j : ℝ) ^ (-s) + ((j : ℝ) + 1) ^ (-s)) / 2
            - ((j : ℝ) ^ (1 - s) - ((j : ℝ) + 1) ^ (1 - s)) / (s - 1)) := by
    have t1 := telescope_Ico f hab
    have t2 := telescope_Ico F hab
    simp only [hf, hF, hcast] at t1 t2
    have hsplit : ∀ j ∈ Finset.Ico a b,
        (((j : ℝ) ^ (-s) + ((j : ℝ) + 1) ^ (-s)) / 2
            - ((j : ℝ) ^ (1 - s) - ((j : ℝ) + 1) ^ (1 - s)) / (s - 1))
          = (j : ℝ) ^ (-s) - ((j : ℝ) ^ (-s) - ((j : ℝ) + 1) ^ (-s)) / 2
            - ((j : ℝ) ^ (1 - s) / (s - 1) - ((j : ℝ) + 1) ^ (1 - s) / (s - 1)) := by
      intro j _
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, t1, t2]
    ring
  rw [hkey]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj1 : 1 ≤ j := le_trans ha (Finset.mem_Ico.mp hj).1
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have h := trap_unit hs0 hs1 hjpos
  have e : s * (s + 1) * (j : ℝ) ^ (-s - 2) / 12 = s * (s + 1) / 12 * (j : ℝ) ^ (-s - 2) := by
    ring
  rw [e] at h
  exact h

/-- Every term of the window lies below its first:
`Σ_{j=a}^{b−1} j^{−q} ≤ (b−a) a^{−q}` for `q ≥ 0`. -/
theorem sum_Ico_rpow_le {q : ℝ} (hq : 0 ≤ q) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-q) ≤ ((b : ℝ) - (a : ℝ)) * (a : ℝ) ^ (-q) := by
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hle : ∀ j ∈ Finset.Ico a b, (j : ℝ) ^ (-q) ≤ (a : ℝ) ^ (-q) := by
    intro j hj
    have hja : (a : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hj).1
    exact rpow_le_rpow_of_nonpos hapos hja (by linarith)
  refine le_trans (Finset.sum_le_sum hle) ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hab]

end Trapezoid

/-! ## Bernoulli bounds on `(1+y)^{−q}` -/

section Bernoulli

/-- `1 − qy ≤ (1+y)^{−q}` for `q, y ≥ 0`. -/
theorem one_sub_le_rpow_neg {q y : ℝ} (hq : 0 ≤ q) (hy : 0 ≤ y) : 1 - q * y ≤ (1 + y) ^ (-q) := by
  have h := rpow_ge_tangent (q := -q) (u := 1 + y) (by linarith) (by linarith)
  have e : 1 + -q * (1 + y - 1) = 1 - q * y := by ring
  linarith [h, e.le, e.ge]

/-- `(1+y)^{−q} ≤ 1` for `q, y ≥ 0`. -/
theorem rpow_neg_le_one {q y : ℝ} (hq : 0 ≤ q) (hy : 0 ≤ y) : (1 + y) ^ (-q) ≤ 1 :=
  rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

/-- `(1+y)^{−q} ≤ 1 − qy + q²y²` for `q ≥ 1`, `y ≥ 0`: Bernoulli gives `(1+y)^q ≥ 1 + qy`, and
`(1+z)⁻¹ ≤ 1 − z + z²` for `z ≥ 0`. -/
theorem rpow_neg_le_quad {q y : ℝ} (hq : 1 ≤ q) (hy : 0 ≤ y) :
    (1 + y) ^ (-q) ≤ 1 - q * y + q ^ 2 * y ^ 2 := by
  have hb := one_add_mul_self_le_rpow_one_add (s := y) (by linarith) hq
  have hz : 0 ≤ q * y := by positivity
  have hpos : 0 < 1 + q * y := by linarith
  rw [rpow_neg (by linarith)]
  have h1 : ((1 + y) ^ q)⁻¹ ≤ (1 + q * y)⁻¹ := inv_anti₀ hpos hb
  have h2 : (1 + q * y)⁻¹ ≤ 1 - q * y + q ^ 2 * y ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith [pow_nonneg hz 3]
  linarith

end Bernoulli

namespace Decay

variable (D : Decay)

/-! ## The foot of the window, exactly -/

section Foot

/-- `2⌈m/2⌉ = m + δ(m)`. -/
theorem two_foot (m : ℕ) : 2 * ((m + 1) / 2) = m + delta m := by
  rw [delta]; omega

theorem delta_cases (m : ℕ) : (delta m : ℝ) = 0 ∨ (delta m : ℝ) = 1 := by
  have h := delta_lt_two m
  rcases Nat.lt_succ_iff_lt_or_eq.mp h with h0 | h1
  · left; have : delta m = 0 := by omega
    rw [this]; norm_num
  · right; rw [h1]; norm_num

/-- `u(m) := 1 + δ(m)/m = 2⌈m/2⌉/m`. -/
noncomputable def ufoot (m : ℕ) : ℝ := 1 + (delta m : ℝ) / (m : ℝ)

theorem foot_eq {m : ℕ} (hm : 1 ≤ m) :
    (((m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) / 2 * ufoot m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h : ((2 * ((m + 1) / 2) : ℕ) : ℝ) = ((m + delta m : ℕ) : ℝ) := by rw [two_foot]
  push_cast at h
  rw [ufoot]
  field_simp
  linarith

theorem one_le_ufoot (m : ℕ) : 1 ≤ ufoot m := by
  rw [ufoot]
  have : 0 ≤ (delta m : ℝ) / (m : ℝ) := by positivity
  linarith

/-- `(a)^e = m^e 2^{−e} u^e` for the foot `a = ⌈m/2⌉`. -/
theorem foot_rpow {m : ℕ} (hm : 1 ≤ m) (e : ℝ) :
    (((m + 1) / 2 : ℕ) : ℝ) ^ e = (m : ℝ) ^ e * (2 : ℝ) ^ (-e) * ufoot m ^ e := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hu : (0 : ℝ) ≤ ufoot m := le_trans zero_le_one (one_le_ufoot m)
  rw [foot_eq hm, Real.mul_rpow (by positivity) hu, Real.div_rpow hmpos.le (by norm_num),
    rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]

theorem mpow_mul_rpow {m : ℕ} (hm : 1 ≤ m) (k : ℝ) :
    (m : ℝ) ^ D.p * (m : ℝ) ^ (-D.p - k) = (m : ℝ) ^ (-k) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [← rpow_add hmpos]
  congr 1
  ring

theorem two_rpow_p_add (k : ℕ) : (2 : ℝ) ^ (-(-D.p - k)) = D.tau * 2 ^ k := by
  have e : (-(-D.p - k) : ℝ) = D.p + k := by ring
  rw [e, rpow_add (by norm_num), rpow_natCast, tau]

theorem m_rpow_neg_nat {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (m : ℝ) ^ (-(k : ℝ)) = ((m : ℝ)⁻¹) ^ k := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [rpow_neg hmpos.le, rpow_natCast, inv_pow]

/-- **The foot, rescaled.** `m^p ⌈m/2⌉^{−p−k} = τ 2^k m^{−k} u^{−p−k}`. -/
theorem mpow_foot {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (m : ℝ) ^ D.p * (((m + 1) / 2 : ℕ) : ℝ) ^ (-D.p - k)
      = D.tau * 2 ^ k * ((m : ℝ)⁻¹) ^ k * ufoot m ^ (-D.p - k) := by
  rw [foot_rpow hm, ← mul_assoc, ← mul_assoc, D.mpow_mul_rpow hm, m_rpow_neg_nat hm,
    D.two_rpow_p_add]
  ring

end Foot

/-! ## The coefficients -/

/-- `A_{δ(m)}`: `A₀` at even `m`, `A₁` at odd `m`. -/
noncomputable def Ad (m : ℕ) : ℝ := if delta m = 0 then D.A0 else D.A1

theorem Ad_eq (m : ℕ) : D.Ad m = D.A0 - D.c * D.tau * (delta m : ℝ) := by
  rw [Ad]
  rcases Nat.lt_succ_iff_lt_or_eq.mp (delta_lt_two m) with h0 | h1
  · have h : delta m = 0 := by omega
    rw [if_pos h, h]; norm_num
  · have h : delta m ≠ 0 := by omega
    rw [if_neg h, h1, A1]; norm_num

/-- `Θ_α(δ) := (2τ−1)/2 − τδ + (α−1)(2τ−1)/(p+1)`, the coefficient of `m^{−p−1}` in Step 3. -/
noncomputable def Theta (α : ℝ) (m : ℕ) : ℝ :=
  (2 * D.tau - 1) / 2 - D.tau * (delta m : ℝ) + (α - 1) * (2 * D.tau - 1) / (D.p + 1)

/-- **Step 3's coefficient identity.** `cΘ_α(δ) + c − α = A_δ + Γα`, by `c = p/(τ−1)`. -/
theorem coeff_identity (α : ℝ) (m : ℕ) :
    D.c * D.Theta α m + D.c - α = D.Ad m + D.Gam * α := by
  have hτ := D.tau_sub_one_pos
  have hp1 := D.p_add_one_pos
  have hc : D.c = D.p / (D.tau - 1) := by
    have h := D.cramer
    have hp := D.p_ne
    field_simp at h
    field_simp
    linarith
  rw [D.Ad_eq, Theta, A0, Gam, hc]
  field_simp
  ring

/-! ## Step 1: partial fractions -/

section PartialFractions

/-- `e_α(j) := (1−α) j^{−p−2}/(j+1)` of `eq:doubling_pf`, written `(1−α) j^{−p−1}/(j(j+1))`. -/
noncomputable def ePf (α : ℝ) (j : ℕ) : ℝ :=
  (1 - α) * (j : ℝ) ^ (-D.p - 1) / ((j : ℝ) * ((j : ℝ) + 1))

/-- **`eq:doubling_pf`.** `Φ_α(j)/(j+1) = j^{−p−1} + (α−1) j^{−p−2} + e_α(j)` for `j ≥ 1`. -/
theorem pf_eq (α : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    D.Phi α j / ((j : ℝ) + 1)
      = (j : ℝ) ^ (-D.p - 1) + (α - 1) * (j : ℝ) ^ (-D.p - 2) + D.ePf α j := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hJ2 : (j : ℝ) ^ (-D.p - 2) = (j : ℝ) ^ (-D.p - 1) / (j : ℝ) := by
    have h := rpow_sub_one_eq (q := -D.p - 1) hjpos
    rw [show (-D.p - 1 - 1 : ℝ) = -D.p - 2 by ring] at h
    exact h
  rw [Phi, ePf, hJ2]
  field_simp
  ring

/-- **`eq:doubling_pf`, the bound.** `|e_α(j)| ≤ |1−α| j^{−p−3}`. -/
theorem abs_ePf_le (α : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    |D.ePf α j| ≤ |1 - α| * (j : ℝ) ^ (-D.p - 3) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hJ3 : (j : ℝ) ^ (-D.p - 3) = (j : ℝ) ^ (-D.p - 1) / ((j : ℝ) * (j : ℝ)) := by
    have h := rpow_sub (x := (j : ℝ)) hjpos (-D.p - 1) 2
    rw [show (-D.p - 1 - 2 : ℝ) = -D.p - 3 by ring, rpow_two] at h
    rw [h, pow_two]
  have hJ : (0 : ℝ) < (j : ℝ) ^ (-D.p - 1) := rpow_pos_of_pos hjpos _
  rw [ePf, hJ3, abs_div, abs_mul, abs_of_pos hJ,
    abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ) * ((j : ℝ) + 1)), mul_div_assoc]
  have hjj : (j : ℝ) * (j : ℝ) ≤ (j : ℝ) * ((j : ℝ) + 1) := by nlinarith
  have hdiv : (j : ℝ) ^ (-D.p - 1) / ((j : ℝ) * ((j : ℝ) + 1))
      ≤ (j : ℝ) ^ (-D.p - 1) / ((j : ℝ) * (j : ℝ)) :=
    div_le_div_of_nonneg_left hJ.le (by positivity) hjj
  exact mul_le_mul_of_nonneg_left hdiv (abs_nonneg _)

end PartialFractions

/-! ## Step 3: the rescaled window sum -/

section Rescaled

theorem poly_one {p : ℝ} (hp : 1 < p) : 2 * p + 1 + (p + 1) * (p + 2) / 3 ≤ (p + 3) ^ 2 := by
  nlinarith

theorem poly_two {p : ℝ} (hp : 1 < p) : 8 + 2 * (p + 2) * (p + 3) / 3 ≤ (p + 3) ^ 2 := by
  have h : 0 ≤ (p + 9) * (p - 1) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- `T_α(m) := m^p Σ_{j∈W(m)} Φ_α(j)/(j+1)`, the rescaled window sum of Step 3. -/
noncomputable def Tsum (α : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ D.p * ∑ j ∈ window m, D.Phi α j / ((j : ℝ) + 1)

/-- The constant of `T_expansion`: `τ(p+3)²(1+|α−1|)`. -/
noncomputable def cT (α : ℝ) : ℝ := D.tau * (D.p + 3) ^ 2 * (1 + |α - 1|)

set_option maxHeartbeats 1000000 in
/-- **Step 3, the rescaled window sum.** For every `m ≥ 1`,
`|T_α(m) − (τ−1)/p − Θ_α(δ(m))/m| ≤ τ(p+3)²(1+|α−1|)/m²`. -/
theorem T_expansion (α : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    |D.Tsum α m - (D.tau - 1) / D.p - D.Theta α m / (m : ℝ)| ≤ D.cT α / (m : ℝ) ^ 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hp := D.p_gt_one
  have hppos := D.p_pos
  have hτ2 := D.tau_gt_two
  have hτpos := D.tau_pos
  set a : ℕ := (m + 1) / 2 with ha
  have ha1 : 1 ≤ a := one_le_foot hm
  have ham : a ≤ m := foot_le_self hm
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have hwin : window m = Finset.Ico a m := rfl
  set x : ℝ := (m : ℝ)⁻¹ with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hm)
  set δ : ℝ := (delta m : ℝ) with hδ
  have hδc := delta_cases m
  rw [← hδ] at hδc
  set y : ℝ := δ * x with hy
  have hy0 : 0 ≤ y := by rcases hδc with h | h <;> rw [hy, h] <;> linarith
  have hyx : y ≤ x := by rcases hδc with h | h <;> rw [hy, h] <;> linarith
  have hy2 : y ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hy0 hyx 2
  have hxy : x * y ≤ x ^ 2 := by nlinarith
  set u : ℝ := ufoot m with hu
  have huy : u = 1 + y := by rw [hu, ufoot, hy, hx, div_eq_mul_inv]
  set μ : ℝ := (m : ℝ) ^ D.p with hμ
  have hμpos : 0 < μ := rpow_pos_of_pos hmpos _
  -- the rescaled powers of `m`
  have hM0 : μ * (m : ℝ) ^ (-D.p) = 1 := by
    rw [hμ, ← rpow_add hmpos]; simp only [add_neg_cancel, rpow_zero]
  have hM1 : μ * (m : ℝ) ^ (-D.p - 1) = x := by
    have h := D.mpow_mul_rpow hm 1
    rw [rpow_neg_one] at h; exact h
  have hM2 : μ * (m : ℝ) ^ (-D.p - 2) = x ^ 2 := by
    have h := D.mpow_mul_rpow hm ((2 : ℕ) : ℝ)
    rw [m_rpow_neg_nat hm] at h; push_cast at h; exact h
  -- the rescaled powers of the foot
  have hP0 : μ * (a : ℝ) ^ (-D.p) = D.tau * (1 + y) ^ (-D.p) := by
    have h := D.mpow_foot hm 0
    simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one] at h
    rw [← huy]; exact h
  have hP1 : μ * (a : ℝ) ^ (-D.p - 1) = 2 * D.tau * x * (1 + y) ^ (-D.p - 1) := by
    have h := D.mpow_foot hm 1
    simp only [Nat.cast_one, pow_one] at h
    rw [← huy, h]; ring
  have hP2 : μ * (a : ℝ) ^ (-D.p - 2) = 4 * D.tau * x ^ 2 * (1 + y) ^ (-D.p - 2) := by
    have h := D.mpow_foot hm 2
    push_cast at h
    rw [← huy, h]; ring
  have hma : (m : ℝ) - (a : ℝ) ≤ (m : ℝ) / 2 := by linarith [foot_le m]
  have hma0 : 0 ≤ (m : ℝ) - (a : ℝ) := by
    have : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ham
    linarith
  have hQ : ∀ k : ℕ, μ * (((m : ℝ) - (a : ℝ)) * (a : ℝ) ^ (-D.p - k))
      ≤ D.tau * 2 ^ k * x ^ k * ((m : ℝ) / 2) := by
    intro k
    have h := D.mpow_foot hm k
    have hule : (1 + y) ^ (-D.p - k) ≤ 1 := by
      have e : (-D.p - k : ℝ) = -(D.p + k) := by ring
      rw [e]; exact rpow_neg_le_one (by positivity) hy0
    have hunn : 0 ≤ (1 + y) ^ (-D.p - k) := rpow_nonneg (by linarith) _
    have huy' : ufoot m = 1 + y := huy
    rw [huy'] at h
    have hA : μ * (a : ℝ) ^ (-D.p - k) ≤ D.tau * 2 ^ k * x ^ k := by
      rw [h]
      have : 0 ≤ D.tau * 2 ^ k * x ^ k := by positivity
      nlinarith
    have hA0 : 0 ≤ μ * (a : ℝ) ^ (-D.p - k) := by positivity
    calc μ * (((m : ℝ) - (a : ℝ)) * (a : ℝ) ^ (-D.p - k))
        = ((m : ℝ) - (a : ℝ)) * (μ * (a : ℝ) ^ (-D.p - k)) := by ring
      _ ≤ ((m : ℝ) / 2) * (D.tau * 2 ^ k * x ^ k) := mul_le_mul hma hA hA0 (by positivity)
      _ = D.tau * 2 ^ k * x ^ k * ((m : ℝ) / 2) := by ring
  have hmx : (m : ℝ) * x = 1 := by rw [hx]; field_simp
  have hQ3 : μ * (((m : ℝ) - (a : ℝ)) * (a : ℝ) ^ (-D.p - 3)) ≤ 4 * D.tau * x ^ 2 := by
    have h := hQ 3
    push_cast at h
    have e : D.tau * 2 ^ 3 * x ^ 3 * ((m : ℝ) / 2) = 4 * D.tau * x ^ 2 * ((m : ℝ) * x) := by ring
    rw [e, hmx, mul_one] at h; exact h
  have hQ4 : μ * (((m : ℝ) - (a : ℝ)) * (a : ℝ) ^ (-D.p - 4)) ≤ 8 * D.tau * x ^ 2 := by
    have h := hQ 4
    push_cast at h
    have e : D.tau * 2 ^ 4 * x ^ 4 * ((m : ℝ) / 2) = 8 * D.tau * x ^ 2 * x * ((m : ℝ) * x) := by
      ring
    rw [e, hmx, mul_one] at h
    have : 8 * D.tau * x ^ 2 * x ≤ 8 * D.tau * x ^ 2 := by
      have : 0 ≤ 8 * D.tau * x ^ 2 := by positivity
      nlinarith
    linarith
  -- Step 1, summed over the window
  have hSe : |∑ j ∈ window m, D.ePf α j|
      ≤ |1 - α| * (((m : ℝ) - (a : ℝ)) * (a : ℝ) ^ (-D.p - 3)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h1 : ∑ j ∈ window m, |D.ePf α j| ≤ ∑ j ∈ window m, |1 - α| * (j : ℝ) ^ (-D.p - 3) :=
      Finset.sum_le_sum fun j hj => D.abs_ePf_le α (one_le_of_mem_window' hm hj)
    refine le_trans h1 ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h2 := sum_Ico_rpow_le (q := D.p + 3) (by linarith) (b := m) ha1 ham
    rw [show (-(D.p + 3) : ℝ) = -D.p - 3 by ring] at h2
    rw [hwin]; exact h2
  have hsumPf : ∑ j ∈ window m, D.Phi α j / ((j : ℝ) + 1)
      = ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 1)
        + (α - 1) * ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 2)
        + ∑ j ∈ window m, D.ePf α j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj => D.pf_eq α (one_le_of_mem_window' hm hj)
  -- Step 2, at `r = p + 1` and `r = p + 2`
  have hW1 := window_sum_second (s := D.p + 1) (by linarith) ha1 ham
  rw [show (-(D.p + 1) : ℝ) = -D.p - 1 by ring, show (1 - (D.p + 1) : ℝ) = -D.p by ring,
    show (D.p + 1 - 1 : ℝ) = D.p by ring, show (-D.p - 1 - 2 : ℝ) = -(D.p + 3) by ring] at hW1
  have hW1' := sum_Ico_rpow_le (q := D.p + 3) (by linarith) (b := m) ha1 ham
  have hW2 := window_sum_second (s := D.p + 2) (by linarith) ha1 ham
  rw [show (-(D.p + 2) : ℝ) = -D.p - 2 by ring, show (1 - (D.p + 2) : ℝ) = -D.p - 1 by ring,
    show (D.p + 2 - 1 : ℝ) = D.p + 1 by ring, show (-D.p - 2 - 2 : ℝ) = -(D.p + 4) by ring]
    at hW2
  have hW2' := sum_Ico_rpow_le (q := D.p + 4) (by linarith) (b := m) ha1 ham
  rw [show (-(D.p + 3) : ℝ) = -D.p - 3 by ring] at hW1 hW1'
  rw [show (-(D.p + 4) : ℝ) = -D.p - 4 by ring] at hW2 hW2'
  rw [← hwin] at hW1 hW1' hW2 hW2'
  set S1 : ℝ := ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 1) with hS1
  set S2 : ℝ := ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 2) with hS2
  set Se : ℝ := ∑ j ∈ window m, D.ePf α j with hSeDef
  set E1 : ℝ := S1 - ((a : ℝ) ^ (-D.p) - (m : ℝ) ^ (-D.p)) / D.p
      - ((a : ℝ) ^ (-D.p - 1) - (m : ℝ) ^ (-D.p - 1)) / 2 with hE1
  set E2 : ℝ := S2 - ((a : ℝ) ^ (-D.p - 1) - (m : ℝ) ^ (-D.p - 1)) / (D.p + 1)
      - ((a : ℝ) ^ (-D.p - 2) - (m : ℝ) ^ (-D.p - 2)) / 2 with hE2
  set Q3 : ℝ := ((m : ℝ) - (a : ℝ)) * (a : ℝ) ^ (-D.p - 3) with hQ3def
  set Q4 : ℝ := ((m : ℝ) - (a : ℝ)) * (a : ℝ) ^ (-D.p - 4) with hQ4def
  have hS3le : ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 3) ≤ Q3 := hW1'
  have hS4le : ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 4) ≤ Q4 := hW2'
  have hc1 : 0 ≤ (D.p + 1) * (D.p + 1 + 1) / 12 := by positivity
  have hc2 : 0 ≤ (D.p + 2) * (D.p + 2 + 1) / 12 := by positivity
  have hE1b : |μ * E1| ≤ (D.p + 1) * (D.p + 2) / 3 * D.tau * x ^ 2 := by
    rw [abs_mul, abs_of_pos hμpos]
    have h1 : |E1| ≤ (D.p + 1) * (D.p + 1 + 1) / 12 * Q3 :=
      le_trans hW1 (mul_le_mul_of_nonneg_left hS3le hc1)
    calc μ * |E1| ≤ μ * ((D.p + 1) * (D.p + 1 + 1) / 12 * Q3) :=
          mul_le_mul_of_nonneg_left h1 hμpos.le
      _ = (D.p + 1) * (D.p + 1 + 1) / 12 * (μ * Q3) := by ring
      _ ≤ (D.p + 1) * (D.p + 1 + 1) / 12 * (4 * D.tau * x ^ 2) :=
          mul_le_mul_of_nonneg_left hQ3 hc1
      _ = (D.p + 1) * (D.p + 2) / 3 * D.tau * x ^ 2 := by ring
  have hE2b : |μ * E2| ≤ 2 * (D.p + 2) * (D.p + 3) / 3 * D.tau * x ^ 2 := by
    rw [abs_mul, abs_of_pos hμpos]
    have h1 : |E2| ≤ (D.p + 2) * (D.p + 2 + 1) / 12 * Q4 :=
      le_trans hW2 (mul_le_mul_of_nonneg_left hS4le hc2)
    calc μ * |E2| ≤ μ * ((D.p + 2) * (D.p + 2 + 1) / 12 * Q4) :=
          mul_le_mul_of_nonneg_left h1 hμpos.le
      _ = (D.p + 2) * (D.p + 2 + 1) / 12 * (μ * Q4) := by ring
      _ ≤ (D.p + 2) * (D.p + 2 + 1) / 12 * (8 * D.tau * x ^ 2) :=
          mul_le_mul_of_nonneg_left hQ4 hc2
      _ = 2 * (D.p + 2) * (D.p + 3) / 3 * D.tau * x ^ 2 := by ring
  have hSeb : |μ * Se| ≤ |α - 1| * (4 * D.tau * x ^ 2) := by
    rw [abs_mul, abs_of_pos hμpos, abs_sub_comm α 1]
    calc μ * |Se| ≤ μ * (|1 - α| * Q3) := mul_le_mul_of_nonneg_left hSe hμpos.le
      _ = |1 - α| * (μ * Q3) := by ring
      _ ≤ |1 - α| * (4 * D.tau * x ^ 2) := mul_le_mul_of_nonneg_left hQ3 (abs_nonneg _)
  -- the foot terms
  set Z0 : ℝ := μ * (a : ℝ) ^ (-D.p) - D.tau + D.tau * D.p * y with hZ0
  set Z1 : ℝ := μ * (a : ℝ) ^ (-D.p - 1) - 2 * D.tau * x with hZ1
  set Z2 : ℝ := μ * (a : ℝ) ^ (-D.p - 2) - x ^ 2 with hZ2
  have hZ0b : |Z0 / D.p| ≤ D.tau * D.p * x ^ 2 := by
    have hlo := one_sub_le_rpow_neg (q := D.p) hppos.le hy0
    have hhi := rpow_neg_le_quad (q := D.p) hp.le hy0
    have hZ0e : Z0 = D.tau * ((1 + y) ^ (-D.p) - 1 + D.p * y) := by rw [hZ0, hP0]; ring
    rw [abs_div, abs_of_pos hppos, div_le_iff₀ hppos, hZ0e, abs_mul, abs_of_pos hτpos]
    have h0 : 0 ≤ (1 + y) ^ (-D.p) - 1 + D.p * y := by linarith
    rw [abs_of_nonneg h0]
    have h1 : (1 + y) ^ (-D.p) - 1 + D.p * y ≤ D.p ^ 2 * x ^ 2 := by
      have : D.p ^ 2 * y ^ 2 ≤ D.p ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hy2 (by positivity)
      linarith
    calc D.tau * ((1 + y) ^ (-D.p) - 1 + D.p * y) ≤ D.tau * (D.p ^ 2 * x ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hτpos.le
      _ = D.tau * D.p * x ^ 2 * D.p := by ring
  have hZ1b : |Z1| ≤ 2 * D.tau * (D.p + 1) * x ^ 2 := by
    have e : (-D.p - 1 : ℝ) = -(D.p + 1) := by ring
    have hlo := one_sub_le_rpow_neg (q := D.p + 1) (by linarith) hy0
    have hhi := rpow_neg_le_one (q := D.p + 1) (by linarith) hy0
    rw [← e] at hlo hhi
    have hZ1e : Z1 = 2 * D.tau * x * ((1 + y) ^ (-D.p - 1) - 1) := by rw [hZ1, hP1]; ring
    rw [hZ1e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * D.tau * x),
      abs_of_nonpos (by linarith)]
    have h1 : -((1 + y) ^ (-D.p - 1) - 1) ≤ (D.p + 1) * x := by
      have : (D.p + 1) * y ≤ (D.p + 1) * x := mul_le_mul_of_nonneg_left hyx (by positivity)
      linarith
    calc 2 * D.tau * x * -((1 + y) ^ (-D.p - 1) - 1) ≤ 2 * D.tau * x * ((D.p + 1) * x) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * D.tau * (D.p + 1) * x ^ 2 := by ring
  have hZ2b : |Z2| ≤ 4 * D.tau * x ^ 2 := by
    have e : (-D.p - 2 : ℝ) = -(D.p + 2) := by ring
    have hhi := rpow_neg_le_one (q := D.p + 2) (by linarith) hy0
    have hnn : 0 ≤ (1 + y) ^ (-(D.p + 2)) := rpow_nonneg (by linarith) _
    rw [← e] at hhi hnn
    have hZ2e : Z2 = 4 * D.tau * x ^ 2 * (1 + y) ^ (-D.p - 2) - x ^ 2 := by rw [hZ2, hP2]
    have hx2 : 0 < x ^ 2 := by positivity
    have hA : 4 * D.tau * x ^ 2 * (1 + y) ^ (-D.p - 2) ≤ 4 * D.tau * x ^ 2 := by
      have : 0 ≤ 4 * D.tau * x ^ 2 := by positivity
      nlinarith
    have hB : 0 ≤ 4 * D.tau * x ^ 2 * (1 + y) ^ (-D.p - 2) := by positivity
    have hx4 : x ^ 2 ≤ 4 * D.tau * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 4 * D.tau by linarith) hx2.le
      linarith
    rw [hZ2e, abs_le]
    constructor <;> linarith
  -- the identity
  have hΘ : D.Theta α m / (m : ℝ) = D.Theta α m * x := by rw [hx, div_eq_mul_inv]
  have hρ : D.Tsum α m - (D.tau - 1) / D.p - D.Theta α m * x
      = Z0 / D.p + Z1 / 2 + μ * E1 + (α - 1) * (Z1 / (D.p + 1) + Z2 / 2 + μ * E2)
        + μ * Se := by
    have hppne : D.p ≠ 0 := hppos.ne'
    have hp1ne : D.p + 1 ≠ 0 := by linarith
    have hpp : D.p * D.p⁻¹ = 1 := mul_inv_cancel₀ hppne
    rw [Tsum, hsumPf, hZ0, hZ1, hZ2, hE1, hE2, Theta, hy, ← hδ]
    linear_combination (-1 / D.p) * hM0 + (-1 / 2 - (α - 1) / (D.p + 1)) * hM1
      + (-(α - 1) / 2) * hM2 + (-(D.tau * δ * x)) * hpp
  rw [hΘ, hρ]
  have hZ1p : |Z1 / (D.p + 1)| ≤ 2 * D.tau * x ^ 2 := by
    have hp1 : 0 < D.p + 1 := by linarith
    rw [abs_div, abs_of_pos hp1, div_le_iff₀ hp1]
    linarith [hZ1b, show 2 * D.tau * (D.p + 1) * x ^ 2 = 2 * D.tau * x ^ 2 * (D.p + 1) by ring]
  have hZ12 : |Z1 / 2| ≤ D.tau * (D.p + 1) * x ^ 2 := by
    rw [abs_div, abs_two]; linarith
  have hZ22 : |Z2 / 2| ≤ 2 * D.tau * x ^ 2 := by
    rw [abs_div, abs_two]; linarith
  set bW : ℝ := 2 * D.tau * x ^ 2 + 2 * D.tau * x ^ 2
      + 2 * (D.p + 2) * (D.p + 3) / 3 * D.tau * x ^ 2
    with hbW
  have hW : |Z1 / (D.p + 1) + Z2 / 2 + μ * E2| ≤ bW := by
    refine le_trans (abs_add_le _ _) ?_
    have := abs_add_le (Z1 / (D.p + 1)) (Z2 / 2)
    linarith
  have hαW : |(α - 1) * (Z1 / (D.p + 1) + Z2 / 2 + μ * E2)| ≤ |α - 1| * bW := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hW (abs_nonneg _)
  have htot : |Z0 / D.p + Z1 / 2 + μ * E1 + (α - 1) * (Z1 / (D.p + 1) + Z2 / 2 + μ * E2)
      + μ * Se| ≤ D.tau * D.p * x ^ 2 + D.tau * (D.p + 1) * x ^ 2
        + (D.p + 1) * (D.p + 2) / 3 * D.tau * x ^ 2 + |α - 1| * bW
        + |α - 1| * (4 * D.tau * x ^ 2) := by
    have h1 := abs_add_le (Z0 / D.p) (Z1 / 2)
    have h2 := abs_add_le (Z0 / D.p + Z1 / 2) (μ * E1)
    have h3 := abs_add_le (Z0 / D.p + Z1 / 2 + μ * E1)
      ((α - 1) * (Z1 / (D.p + 1) + Z2 / 2 + μ * E2))
    have h4 := abs_add_le (Z0 / D.p + Z1 / 2 + μ * E1
      + (α - 1) * (Z1 / (D.p + 1) + Z2 / 2 + μ * E2)) (μ * Se)
    linarith
  have hgoal : D.cT α / (m : ℝ) ^ 2 = D.tau * (D.p + 3) ^ 2 * (1 + |α - 1|) * x ^ 2 := by
    rw [cT, hx, inv_pow, div_eq_mul_inv]
  rw [hgoal]
  refine le_trans htot ?_
  set K : ℝ := D.tau * x ^ 2 with hK
  set A : ℝ := |α - 1| with hA
  have hK0 : 0 ≤ K := by positivity
  have hA0 : 0 ≤ A := abs_nonneg _
  have hpoly1 := poly_one hp
  have hpoly2 := poly_two hp
  have k1 := mul_le_mul_of_nonneg_left hpoly1 hK0
  have k2 := mul_le_mul_of_nonneg_left hpoly2 (mul_nonneg hA0 hK0)
  have e1 : D.tau * D.p * x ^ 2 + D.tau * (D.p + 1) * x ^ 2
      + (D.p + 1) * (D.p + 2) / 3 * D.tau * x ^ 2 + A * bW + A * (4 * D.tau * x ^ 2)
      = K * (2 * D.p + 1 + (D.p + 1) * (D.p + 2) / 3)
        + A * K * (8 + 2 * (D.p + 2) * (D.p + 3) / 3) := by
    rw [hbW, hK]; ring
  have e2 : D.tau * (D.p + 3) ^ 2 * (1 + A) * x ^ 2
      = K * (D.p + 3) ^ 2 + A * K * (D.p + 3) ^ 2 := by
    rw [hK]; ring
  rw [e1, e2]
  linarith

end Rescaled

/-! ## `eq:doubling_Rexp` -/

section Rexp

/-- `R_α(m) = c/(1−ε(m)) · T_α(m) / (1 + α/m)`. -/
theorem Ralpha_eq (α : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    D.Ralpha α m = D.c / (1 - D.eps m) * D.Tsum α m / (1 + α * (m : ℝ)⁻¹) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne : (1 : ℝ) - D.eps m ≠ 0 := (D.one_sub_eps_pos hm).ne'
  have hsum : ∑ j ∈ window m, D.qm m j * D.Phi α j
      = D.c / (1 - D.eps m) * ∑ j ∈ window m, D.Phi α j / ((j : ℝ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hb : ((j : ℝ) + 1) ≠ 0 := (base_pos j).ne'
    rw [D.qm_eq]
    field_simp
  have hPhim : D.Phi α m = ((m : ℝ) ^ D.p)⁻¹ * (1 + α * (m : ℝ)⁻¹) := by
    rw [Phi, rpow_sub hmpos, rpow_neg hmpos.le, rpow_one]
    field_simp
  have hμ : (0 : ℝ) < (m : ℝ) ^ D.p := rpow_pos_of_pos hmpos _
  rw [Ralpha, hsum, hPhim, Tsum]
  field_simp

theorem abs_Theta_le (α : ℝ) (m : ℕ) : |D.Theta α m| ≤ D.tau * (2 + |α - 1|) := by
  have hτ2 := D.tau_gt_two
  have hp := D.p_gt_one
  have hp1 : 0 < D.p + 1 := by linarith
  have h1 : |(2 * D.tau - 1) / 2 - D.tau * (delta m : ℝ)| ≤ D.tau := by
    rcases delta_cases m with h | h <;> rw [h, abs_le] <;> constructor <;> linarith
  have h2 : |(α - 1) * (2 * D.tau - 1) / (D.p + 1)| ≤ |α - 1| * D.tau := by
    rw [mul_div_assoc, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_div, abs_of_pos hp1, abs_of_pos (by linarith), div_le_iff₀ hp1]
    nlinarith
  have h3 := abs_add_le ((2 * D.tau - 1) / 2 - D.tau * (delta m : ℝ))
    ((α - 1) * (2 * D.tau - 1) / (D.p + 1))
  rw [Theta]
  nlinarith [abs_nonneg (α - 1)]

theorem T0_le : (D.tau - 1) / D.p ≤ D.tau := by
  have hp := D.p_gt_one
  have hτ2 := D.tau_gt_two
  rw [div_le_iff₀ D.p_pos]
  nlinarith

/-- `|K − c − c²/m| ≤ 1/m²` for `K = c/(1−ε(m))`. -/
theorem K_sub_le {m : ℕ} (hm : 1 ≤ m) :
    |D.c / (1 - D.eps m) - D.c - D.c ^ 2 * (m : ℝ)⁻¹| ≤ ((m : ℝ)⁻¹) ^ 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hc := D.c_pos
  have hc1 := D.c_lt_one
  have hden : 0 < (m : ℝ) + 1 - D.c := by linarith
  have hid : D.c / (1 - D.eps m) - D.c - D.c ^ 2 * (m : ℝ)⁻¹
      = -(D.c ^ 2 * (1 - D.c)) / ((m : ℝ) * ((m : ℝ) + 1 - D.c)) := by
    rw [D.eps_eq]
    have h1 : (1 : ℝ) - D.c / ((m : ℝ) + 1) = ((m : ℝ) + 1 - D.c) / ((m : ℝ) + 1) := by
      field_simp
    rw [h1]
    field_simp
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < D.c ^ 2 * (1 - D.c)),
    abs_of_pos (by positivity), inv_pow, div_le_iff₀ (by positivity)]
  have hc2 : D.c ^ 2 * (1 - D.c) ≤ 1 := by
    have : D.c ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hm2 : ((m : ℝ) ^ 2)⁻¹ * ((m : ℝ) * ((m : ℝ) + 1 - D.c)) ≥ 1 := by
    rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- The constant of `eq:doubling_Rexp`: `16 τ (p+3)² (1+|α|)²`. -/
noncomputable def cR (α : ℝ) : ℝ := 16 * D.tau * (D.p + 3) ^ 2 * (1 + |α|) ^ 2

theorem const_combine {τ P s t Θa B La : ℝ} (hτ : 2 ≤ τ) (hP : 16 ≤ P) (hs : 0 ≤ s)
    (ht : t ≤ 1 + s) (hΘa : Θa ≤ τ * (2 + t)) (hB : B = τ * P * (1 + t))
    (hLa : La ≤ Θa + 1 + s) :
    2 * (τ + 2 * Θa + 3 * B + s * La) ≤ 16 * τ * P * (1 + s) ^ 2 := by
  have hτ0 : 0 ≤ τ := by linarith
  have hΘa' : Θa ≤ τ * (3 + s) := le_trans hΘa (by nlinarith)
  have hB' : B ≤ τ * P * (2 + s) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsLa : s * La ≤ s * (τ * (3 + s) + 1 + s) :=
    mul_le_mul_of_nonneg_left (by linarith) hs
  have hτP : 16 * τ ≤ τ * P := by nlinarith
  have k1 : 2 * (τ + 2 * (τ * (3 + s)) + 3 * (τ * P * (2 + s)) + s * (τ * (3 + s) + 1 + s))
      ≤ 16 * τ * P * (1 + s) ^ 2 := by
    have e : 16 * τ * P * (1 + s) ^ 2 - 2 * (τ + 2 * (τ * (3 + s)) + 3 * (τ * P * (2 + s))
        + s * (τ * (3 + s) + 1 + s))
        = τ * P * (4 + 26 * s + 16 * s ^ 2) - (2 * τ + 12 * τ + 4 * τ * s + 6 * τ * s
          + 2 * τ * s ^ 2 + 2 * s + 2 * s ^ 2) := by ring
    have h16 : 16 * τ * (4 + 26 * s + 16 * s ^ 2) ≤ τ * P * (4 + 26 * s + 16 * s ^ 2) :=
      mul_le_mul_of_nonneg_right hτP (by positivity)
    have hs1 : 2 * s ≤ τ * s := by nlinarith
    have hs2 : 2 * s ^ 2 ≤ τ * s ^ 2 := by nlinarith
    nlinarith [mul_nonneg hτ0 hs, mul_nonneg hτ0 (sq_nonneg s)]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **`eq:doubling_Rexp`, effectively.** For every `α ∈ ℝ` and every integer `m ≥ 1` with
`2|α| ≤ m`,
`|R_α(m) − 1 − (A_{δ(m)} + Γα)/m| ≤ 16 τ (p+3)² (1+|α|)² / m²`. -/
theorem Rexp (α : ℝ) {m : ℕ} (hm : 1 ≤ m) (hα : 2 * |α| ≤ (m : ℝ)) :
    |D.Ralpha α m - 1 - (D.Ad m + D.Gam * α) / (m : ℝ)| ≤ D.cR α / (m : ℝ) ^ 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hc := D.c_pos
  have hc1 := D.c_lt_one
  have hτ2 := D.tau_gt_two
  have hp := D.p_gt_one
  set x : ℝ := (m : ℝ)⁻¹ with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hm)
  have hαx : |α| * x ≤ 1 / 2 := by
    rw [hx, ← div_eq_mul_inv, div_le_iff₀ hmpos]; linarith
  set v : ℝ := 1 + α * x with hv
  have hv2 : 1 / 2 ≤ v := by
    have : -(|α| * x) ≤ α * x := by
      have h := neg_abs_le α
      nlinarith
    linarith
  have hvpos : 0 < v := by linarith
  set K : ℝ := D.c / (1 - D.eps m) with hK
  set T : ℝ := D.Tsum α m with hT
  set Θ : ℝ := D.Theta α m with hΘ
  set T0 : ℝ := (D.tau - 1) / D.p with hT0
  set B : ℝ := D.cT α with hB
  set ρ : ℝ := T - T0 - Θ * x with hρ
  have hρb : |ρ| ≤ B * x ^ 2 := by
    have h := D.T_expansion α hm
    rw [← hT, ← hΘ, ← hT0, ← hB, div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← hx] at h
    exact h
  set L : ℝ := D.Ad m + D.Gam * α with hL
  have hLid : L = D.c * Θ + D.c - α := by rw [hL, hΘ, D.coeff_identity]
  have hR : D.Ralpha α m = K * T / v := D.Ralpha_eq α hm
  have hcT0 : D.c * T0 = 1 := D.cramer
  have hvR : v * D.Ralpha α m = K * T := by rw [hR]; field_simp
  have hkey : v * (D.Ralpha α m - 1 - L * x)
      = (K - D.c - D.c ^ 2 * x) * T + D.c ^ 2 * x * (Θ * x + ρ) + D.c * ρ - α * L * x ^ 2 := by
    rw [hρ, hLid]
    linear_combination hvR + (1 + D.c * x) * hcT0
  -- the pieces
  have hKb : |K - D.c - D.c ^ 2 * x| ≤ x ^ 2 := D.K_sub_le hm
  have hΘb := D.abs_Theta_le α m
  rw [← hΘ] at hΘb
  have hT0b : T0 ≤ D.tau := D.T0_le
  have hT0pos : 0 ≤ T0 := by rw [hT0]; exact div_nonneg (by linarith) D.p_pos.le
  have hB0 : 0 ≤ B := by rw [hB, cT]; positivity
  have hTb : |T| ≤ D.tau + |Θ| + B := by
    have e : T = T0 + Θ * x + ρ := by rw [hρ]; ring
    have h1 : |Θ * x| ≤ |Θ| := by
      rw [abs_mul, abs_of_pos hx0]; exact mul_le_of_le_one_right (abs_nonneg _) hx1
    have h2 : |ρ| ≤ B := by
      have : B * x ^ 2 ≤ B := mul_le_of_le_one_right hB0 (by nlinarith)
      linarith
    rw [e]
    have := abs_add_le (T0 + Θ * x) ρ
    have := abs_add_le T0 (Θ * x)
    rw [abs_of_nonneg hT0pos] at *
    linarith
  have hLb : |L| ≤ |Θ| + 1 + |α| := by
    rw [hLid]
    have h1 : |D.c * Θ| ≤ |Θ| := by
      rw [abs_mul, abs_of_pos hc]; exact mul_le_of_le_one_left (abs_nonneg _) hc1.le
    have := abs_add_le (D.c * Θ + D.c) (-α)
    have := abs_add_le (D.c * Θ) D.c
    rw [abs_neg, abs_of_pos hc] at *
    rw [sub_eq_add_neg]
    linarith
  -- the bound on `v · error`
  have hx2 : 0 ≤ x ^ 2 := by positivity
  have hvE : |v * (D.Ralpha α m - 1 - L * x)|
      ≤ x ^ 2 * (D.tau + 2 * |Θ| + 3 * B + |α| * |L|) := by
    rw [hkey]
    have t1 : |(K - D.c - D.c ^ 2 * x) * T| ≤ x ^ 2 * (D.tau + |Θ| + B) := by
      rw [abs_mul]; exact mul_le_mul hKb hTb (abs_nonneg _) hx2
    have hc2 : D.c ^ 2 ≤ 1 := by nlinarith
    have t2 : |D.c ^ 2 * x * (Θ * x + ρ)| ≤ x ^ 2 * (|Θ| + B) := by
      have hin : |Θ * x + ρ| ≤ x * (|Θ| + B) := by
        have := abs_add_le (Θ * x) ρ
        have h1 : |Θ * x| = x * |Θ| := by rw [abs_mul, abs_of_pos hx0, mul_comm]
        have h2 : B * x ^ 2 ≤ x * B := by
          have : x ^ 2 ≤ x := by nlinarith
          nlinarith
        nlinarith
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ D.c ^ 2), abs_of_pos hx0]
      have h3 : D.c ^ 2 * x * |Θ * x + ρ| ≤ 1 * x * (x * (|Θ| + B)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hc2 hx0.le) hin (abs_nonneg _)
          (by positivity)
      nlinarith
    have t3 : |D.c * ρ| ≤ x ^ 2 * B := by
      rw [abs_mul, abs_of_pos hc]
      have : D.c * |ρ| ≤ |ρ| := mul_le_of_le_one_left (abs_nonneg _) hc1.le
      nlinarith
    have t4 : |α * L * x ^ 2| = x ^ 2 * (|α| * |L|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hx2]; ring
    have s1 := abs_add_le ((K - D.c - D.c ^ 2 * x) * T) (D.c ^ 2 * x * (Θ * x + ρ))
    have s2 := abs_add_le ((K - D.c - D.c ^ 2 * x) * T + D.c ^ 2 * x * (Θ * x + ρ)) (D.c * ρ)
    have s3 := abs_sub ((K - D.c - D.c ^ 2 * x) * T + D.c ^ 2 * x * (Θ * x + ρ) + D.c * ρ)
      (α * L * x ^ 2)
    nlinarith
  have hE : |D.Ralpha α m - 1 - L * x| ≤ 2 * (x ^ 2 * (D.tau + 2 * |Θ| + 3 * B + |α| * |L|)) := by
    rw [abs_mul, abs_of_pos hvpos] at hvE
    have hE0 := abs_nonneg (D.Ralpha α m - 1 - L * x)
    nlinarith
  have hconst : 2 * (D.tau + 2 * |Θ| + 3 * B + |α| * |L|) ≤ D.cR α := by
    rw [cR]
    have hsub : |α - 1| ≤ 1 + |α| := by
      have := abs_sub α 1
      rw [abs_one] at this; linarith
    exact const_combine hτ2.le (by nlinarith) (abs_nonneg α) hsub hΘb
      (by rw [hB, cT]) hLb
  have hgoal : D.cR α / (m : ℝ) ^ 2 = D.cR α * x ^ 2 := by
    rw [hx, inv_pow, div_eq_mul_inv]
  have hLx : L / (m : ℝ) = L * x := by rw [hx, div_eq_mul_inv]
  rw [hLx, hgoal]
  nlinarith

end Rexp

/-! ## `rem:doubling_parity` -/

section Parity

/-- `Φ₀(j) = j^{−p}` is positive on `j ≥ 1`. -/
theorem Phi_zero_pos {j : ℕ} (hj : 1 ≤ j) : 0 < D.Phi 0 j := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  rw [Phi, add_zero]; positivity

/-- `R₀(m)` of `R0Bound.lean` (the total window weight) is `eq:doubling_R` at `α = 0`. -/
theorem R0_eq_Ralpha_zero {m : ℕ} (hm : 1 ≤ m) : D.R0 m = D.Ralpha 0 m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hPm : D.Phi 0 m ≠ 0 := (D.Phi_zero_pos hm).ne'
  rw [R0, Ralpha, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast one_le_of_mem_window' hm hj
  rw [wm, mul_div_assoc]
  congr 1
  rw [Phi, Phi, add_zero, add_zero, Real.div_rpow hmpos.le hjpos.le]
  rw [rpow_sub hjpos, rpow_sub hmpos, rpow_one, rpow_one, rpow_neg hjpos.le, rpow_neg hmpos.le]
  field_simp

/-- `cR 0 = 16 τ (p+3)²`. -/
theorem cR_zero : D.cR 0 = 16 * D.tau * (D.p + 3) ^ 2 := by
  rw [cR, abs_zero, add_zero, one_pow, mul_one]

/-- **`rem:doubling_parity`, even `m`.** `R₀(m) > 1` at every even `m > 16τ(p+3)²/A₀`. -/
theorem Ralpha_zero_gt_one_of_even {m : ℕ} (hm : 1 ≤ m) (hev : delta m = 0)
    (hth : D.cR 0 / D.A0 < (m : ℝ)) : 1 < D.Ralpha 0 m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hA0 := D.A_zero_pos
  have h := D.Rexp 0 hm (by rw [abs_zero, mul_zero]; exact hmpos.le)
  have hAd : D.Ad m = D.A0 := by rw [Ad, if_pos hev]
  rw [hAd, mul_zero, add_zero] at h
  have hlo := (abs_le.mp h).1
  have hC : D.cR 0 < (m : ℝ) * D.A0 := by rwa [div_lt_iff₀ hA0] at hth
  have hgap : D.cR 0 / (m : ℝ) ^ 2 < D.A0 / (m : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hmpos]
    nlinarith
  linarith

/-- **`rem:doubling_parity`, odd `m`.** `R₀(m) < 1` at every odd `m > 16τ(p+3)²/(−A₁)`. -/
theorem Ralpha_zero_lt_one_of_odd {m : ℕ} (hm : 1 ≤ m) (hodd : delta m = 1)
    (hth : D.cR 0 / (-D.A1) < (m : ℝ)) : D.Ralpha 0 m < 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hA1 : 0 < -D.A1 := by linarith [D.A_one_neg]
  have h := D.Rexp 0 hm (by rw [abs_zero, mul_zero]; exact hmpos.le)
  have hAd : D.Ad m = D.A1 := by rw [Ad, if_neg (by omega)]
  rw [hAd, mul_zero, add_zero] at h
  have hhi := (abs_le.mp h).2
  have hC : D.cR 0 < (m : ℝ) * -D.A1 := by rwa [div_lt_iff₀ hA1] at hth
  have hgap : D.cR 0 / (m : ℝ) ^ 2 < -D.A1 / (m : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hmpos]
    nlinarith
  have e : D.A1 / (m : ℝ) = -(-D.A1 / (m : ℝ)) := by ring
  linarith

/-- `rem:doubling_parity`, even `m`, on `R₀` as `R0Bound.lean` defines it. -/
theorem R0_gt_one_of_even {m : ℕ} (hm : 1 ≤ m) (hev : delta m = 0)
    (hth : D.cR 0 / D.A0 < (m : ℝ)) : 1 < D.R0 m := by
  rw [D.R0_eq_Ralpha_zero hm]; exact D.Ralpha_zero_gt_one_of_even hm hev hth

/-- `rem:doubling_parity`, odd `m`, on `R₀` as `R0Bound.lean` defines it. -/
theorem R0_lt_one_of_odd {m : ℕ} (hm : 1 ≤ m) (hodd : delta m = 1)
    (hth : D.cR 0 / (-D.A1) < (m : ℝ)) : D.R0 m < 1 := by
  rw [D.R0_eq_Ralpha_zero hm]; exact D.Ralpha_zero_lt_one_of_odd hm hodd hth

/-- A positive sequence `(x_j)_{j≥1}` is a **supersolution** of `eq:doubling_avg` if
`x_m ≥ Σ_{j∈W(m)} q_m(j) x_j` for every large enough integer `m`. -/
def IsSupersolution (x : ℕ → ℝ) : Prop :=
  ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∑ j ∈ window m, D.qm m j * x j ≤ x m

/-- A positive sequence `(x_j)_{j≥1}` is a **subsolution** of `eq:doubling_avg` if
`x_m ≤ Σ_{j∈W(m)} q_m(j) x_j` for every large enough integer `m`. -/
def IsSubsolution (x : ℕ → ℝ) : Prop :=
  ∃ M : ℕ, ∀ m : ℕ, M ≤ m → x m ≤ ∑ j ∈ window m, D.qm m j * x j

/-- `R_0(m) = Σ_{j∈W(m)} q_m(j) Φ₀(j) / Φ₀(m)`, so `R₀(m) > 1` iff the average exceeds `Φ₀(m)`. -/
theorem sum_qm_Phi_zero {m : ℕ} (hm : 1 ≤ m) :
    ∑ j ∈ window m, D.qm m j * D.Phi 0 j = D.Ralpha 0 m * D.Phi 0 m := by
  rw [Ralpha, div_mul_cancel₀ _ (D.Phi_zero_pos hm).ne']

/-- **`rem:doubling_parity`.** The pure power `Φ₀(j) = j^{−p}` is not a supersolution of
`eq:doubling_avg`. -/
theorem not_isSupersolution_Phi_zero : ¬ D.IsSupersolution (D.Phi 0) := by
  rintro ⟨M, hM⟩
  set N : ℕ := ⌈D.cR 0 / D.A0⌉₊ with hN
  set m : ℕ := 2 * (M + N + 1) with hmdef
  have hm1 : 1 ≤ m := by omega
  have hev : delta m = 0 := by rw [delta]; omega
  have hth : D.cR 0 / D.A0 < (m : ℝ) := by
    have h1 : D.cR 0 / D.A0 ≤ (N : ℝ) := Nat.le_ceil _
    have h2 : (N : ℝ) < (m : ℝ) := by exact_mod_cast (show N < m by omega)
    linarith
  have hgt := D.Ralpha_zero_gt_one_of_even hm1 hev hth
  have hle := hM m (by omega)
  rw [D.sum_qm_Phi_zero hm1] at hle
  have hpos := D.Phi_zero_pos hm1
  nlinarith

/-- **`rem:doubling_parity`.** The pure power `Φ₀(j) = j^{−p}` is not a subsolution of
`eq:doubling_avg`. -/
theorem not_isSubsolution_Phi_zero : ¬ D.IsSubsolution (D.Phi 0) := by
  rintro ⟨M, hM⟩
  set N : ℕ := ⌈D.cR 0 / (-D.A1)⌉₊ with hN
  set m : ℕ := 2 * (M + N + 1) + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hodd : delta m = 1 := by rw [delta]; omega
  have hth : D.cR 0 / (-D.A1) < (m : ℝ) := by
    have h1 : D.cR 0 / (-D.A1) ≤ (N : ℝ) := Nat.le_ceil _
    have h2 : (N : ℝ) < (m : ℝ) := by exact_mod_cast (show N < m by omega)
    linarith
  have hlt := D.Ralpha_zero_lt_one_of_odd hm1 hodd hth
  have hge := hM m (by omega)
  rw [D.sum_qm_Phi_zero hm1] at hge
  have hpos := D.Phi_zero_pos hm1
  nlinarith

/-! ### The heaviest summand -/

/-- The summands `w_m(j) = q_m(j)Φ₀(j)/Φ₀(m)` of `eq:doubling_R` at `α = 0` decrease along the
window, so the heaviest is the first, at `j = ⌈m/2⌉`. -/
theorem wm_le_foot {m j : ℕ} (hm : 1 ≤ m) (hj : j ∈ window m) :
    D.wm m j ≤ D.wm m ((m + 1) / 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have ha1 : 1 ≤ (m + 1) / 2 := one_le_foot hm
  have hapos : (0 : ℝ) < (((m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast ha1
  have hja : (((m + 1) / 2 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (mem_window.mp hj).1
  have hK : 0 < D.c / (1 - D.eps m) := div_pos D.c_pos (D.one_sub_eps_pos hm)
  have hq : ∀ i : ℕ, D.qm m i = D.c / (1 - D.eps m) / ((i : ℝ) + 1) := fun i => by
    rw [D.qm_eq, div_div, mul_comm]
  rw [wm, wm, hq, hq]
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left hK.le (by positivity) (by linarith)
  · exact rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hmpos.le hapos hja)
      D.p_pos.le
  · exact rpow_nonneg (by positivity) _
  · exact div_nonneg hK.le (by positivity)

set_option maxHeartbeats 1000000 in
/-- **`rem:doubling_parity`, the heaviest summand.** `|w_m(⌈m/2⌉) − 2cτ/m| ≤ 2τ(p+3)/m²` for
every `m ≥ 1`; the parity gap `(A₀ − A₁)/m = cτ/m` (`A_gap`) is half of its leading term. -/
theorem wm_foot_expansion {m : ℕ} (hm : 1 ≤ m) :
    |D.wm m ((m + 1) / 2) - 2 * D.c * D.tau / (m : ℝ)|
      ≤ 2 * D.tau * (D.p + 3) / (m : ℝ) ^ 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hc := D.c_pos
  have hc1 := D.c_lt_one
  have hτ2 := D.tau_gt_two
  have hp := D.p_gt_one
  set a : ℕ := (m + 1) / 2 with ha
  have ha1 : 1 ≤ a := one_le_foot hm
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  set x : ℝ := (m : ℝ)⁻¹ with hx
  have hx0 : 0 < x := by positivity
  have hmx : (m : ℝ) * x = 1 := by rw [hx]; field_simp
  set y : ℝ := (delta m : ℝ) * x with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyx : y ≤ x := by
    rcases delta_cases m with h | h <;> rw [hy, h] <;> linarith
  -- `(m/a)^p = τ (1+y)^{−p}`
  have hP : ((m : ℝ) / (a : ℝ)) ^ D.p = D.tau * (1 + y) ^ (-D.p) := by
    have h := D.mpow_foot hm 0
    simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one] at h
    rw [Real.div_rpow hmpos.le hapos.le, div_eq_mul_inv, ← rpow_neg hapos.le]
    have e : (1 + (delta m : ℝ) / (m : ℝ)) = 1 + y := by rw [hy, hx, div_eq_mul_inv]
    rw [ufoot, e] at h
    exact h
  have hlo1 := one_sub_le_rpow_neg (q := D.p) D.p_pos.le hy0
  have hhi1 := rpow_neg_le_one (q := D.p) D.p_pos.le hy0
  have hPlo : D.tau * (1 - D.p * x) ≤ ((m : ℝ) / (a : ℝ)) ^ D.p := by
    rw [hP]
    have : 1 - D.p * x ≤ (1 + y) ^ (-D.p) := by nlinarith
    exact mul_le_mul_of_nonneg_left this D.tau_pos.le
  have hPhi : ((m : ℝ) / (a : ℝ)) ^ D.p ≤ D.tau := by
    rw [hP]; nlinarith [D.tau_pos]
  have hPnn : 0 ≤ ((m : ℝ) / (a : ℝ)) ^ D.p := by positivity
  -- `1/(a+1)` between `2x(1−3x)` and `2x`
  have hInvHi : 1 / ((a : ℝ) + 1) ≤ 2 * x := by
    have h := foot_le m
    rw [← ha] at h
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hInvLo : 2 * x * (1 - 3 * x) ≤ 1 / ((a : ℝ) + 1) := by
    have h := le_foot m
    rw [← ha] at h
    rw [le_div_iff₀ (by positivity)]
    have h2 : (a : ℝ) + 1 ≤ ((m : ℝ) + 3) / 2 := by linarith
    have h3 : 2 * x * (1 - 3 * x) * (((m : ℝ) + 3) / 2) = 1 - 9 * x ^ 2 := by
      have e : 2 * x * (1 - 3 * x) * (((m : ℝ) + 3) / 2)
          = (1 - 3 * x) * ((m : ℝ) * x) + 3 * x * (1 - 3 * x) := by ring
      rw [e, hmx]; ring
    rcases le_or_gt (1 - 3 * x) 0 with hneg | hpos
    · have : 2 * x * (1 - 3 * x) ≤ 0 := by nlinarith
      nlinarith
    · have h4 : 2 * x * (1 - 3 * x) * ((a : ℝ) + 1) ≤ 2 * x * (1 - 3 * x) * (((m : ℝ) + 3) / 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith
  have hInvNn : 0 ≤ 1 / ((a : ℝ) + 1) := by positivity
  -- the constant `K = c/(1−ε(m))`
  set K : ℝ := D.c / (1 - D.eps m) with hK
  have hKb := D.K_sub_le hm
  rw [← hK, ← hx] at hKb
  have hKlo : D.c ≤ K := by
    rw [hK, le_div_iff₀ (D.one_sub_eps_pos hm)]
    nlinarith [D.eps_pos m]
  have hKhi : K ≤ D.c + 2 * x := by
    have h := (abs_le.mp hKb).2
    have hx1 : x ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hm)
    nlinarith
  have hK0 : 0 ≤ K := le_trans hc.le hKlo
  have hw : D.wm m a = K * (1 / ((a : ℝ) + 1)) * ((m : ℝ) / (a : ℝ)) ^ D.p := by
    rw [wm, D.qm_eq, hK]; field_simp
  have htarget : 2 * D.tau * (D.p + 3) / (m : ℝ) ^ 2 = 2 * D.tau * (D.p + 3) * x ^ 2 := by
    rw [hx, inv_pow, div_eq_mul_inv]
  have hlead : 2 * D.c * D.tau / (m : ℝ) = 2 * D.c * D.tau * x := by rw [hx, div_eq_mul_inv]
  rw [hw, htarget, hlead, abs_le]
  constructor
  · rcases le_or_gt 1 ((D.p + 3) * x) with hbig | hsmall
    · have h0 : 0 ≤ K * (1 / ((a : ℝ) + 1)) * ((m : ℝ) / (a : ℝ)) ^ D.p :=
        mul_nonneg (mul_nonneg hK0 hInvNn) hPnn
      have h1 : 2 * D.c * D.tau * x ≤ 2 * D.tau * (D.p + 3) * x ^ 2 := by
        have h2 : 2 * D.tau * x * D.c ≤ 2 * D.tau * x * ((D.p + 3) * x) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have e1 : 2 * D.tau * x * D.c = 2 * D.c * D.tau * x := by ring
        have e2 : 2 * D.tau * x * ((D.p + 3) * x) = 2 * D.tau * (D.p + 3) * x ^ 2 := by ring
        linarith
      linarith
    · have hpx : 0 ≤ D.p * x := by positivity
      have e3 : (D.p + 3) * x = D.p * x + 3 * x := by ring
      have h13 : 0 ≤ 1 - 3 * x := by linarith
      have h1p : 0 ≤ 1 - D.p * x := by linarith
      have hA : D.c * (2 * x * (1 - 3 * x)) ≤ K * (1 / ((a : ℝ) + 1)) :=
        mul_le_mul hKlo hInvLo (by positivity) hK0
      have hB : D.c * (2 * x * (1 - 3 * x)) * (D.tau * (1 - D.p * x))
          ≤ K * (1 / ((a : ℝ) + 1)) * ((m : ℝ) / (a : ℝ)) ^ D.p :=
        mul_le_mul hA hPlo (by have := D.tau_pos; positivity) (mul_nonneg hK0 hInvNn)
      have hC : 2 * D.c * D.tau * x - 2 * D.tau * (D.p + 3) * x ^ 2
          ≤ D.c * (2 * x * (1 - 3 * x)) * (D.tau * (1 - D.p * x)) := by
        have e : D.c * (2 * x * (1 - 3 * x)) * (D.tau * (1 - D.p * x))
            = 2 * D.c * D.tau * x - 2 * D.c * D.tau * (D.p + 3) * x ^ 2
              + 6 * D.c * D.tau * D.p * x ^ 3 := by ring
        rw [e]
        have h6 : 0 ≤ 6 * D.c * D.tau * D.p * x ^ 3 := by positivity
        have h7 : 2 * D.c * D.tau * (D.p + 3) * x ^ 2 ≤ 2 * D.tau * (D.p + 3) * x ^ 2 := by
          have hnn : 0 ≤ 2 * D.tau * (D.p + 3) * x ^ 2 := by positivity
          have h8 := mul_le_mul_of_nonneg_right hc1.le hnn
          have e8 : 2 * D.c * D.tau * (D.p + 3) * x ^ 2
              = D.c * (2 * D.tau * (D.p + 3) * x ^ 2) := by
            ring
          linarith
        linarith
      linarith
  · have hA : K * (1 / ((a : ℝ) + 1)) ≤ (D.c + 2 * x) * (2 * x) :=
      mul_le_mul hKhi hInvHi hInvNn (by positivity)
    have hB : K * (1 / ((a : ℝ) + 1)) * ((m : ℝ) / (a : ℝ)) ^ D.p
        ≤ (D.c + 2 * x) * (2 * x) * D.tau :=
      mul_le_mul hA hPhi hPnn (by positivity)
    have e : (D.c + 2 * x) * (2 * x) * D.tau = 2 * D.c * D.tau * x + 4 * D.tau * x ^ 2 := by ring
    have h4 : 4 * D.tau * x ^ 2 ≤ 2 * D.tau * (D.p + 3) * x ^ 2 := by
      have : 0 ≤ 2 * D.tau * x ^ 2 := by positivity
      nlinarith
    linarith

/-! ### Inhabitation: neither predicate is empty on positive sequences -/

theorem qm_le_one {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j) : D.qm m j ≤ 1 := by
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h1 := D.eps_le_half hm
  have hc1 := D.c_lt_one
  have hden : 1 ≤ ((j : ℝ) + 1) * (1 - D.eps m) := by nlinarith
  rw [D.qm_eq, div_le_one (by linarith)]
  linarith

/-- **Witness.** The positive sequence `2^j` is a supersolution of `eq:doubling_avg`
(at every `m ≥ 1`). -/
theorem isSupersolution_two_pow : D.IsSupersolution (fun j => (2 : ℝ) ^ j) := by
  refine ⟨1, fun m hm => ?_⟩
  have h1 : ∑ j ∈ window m, D.qm m j * (2 : ℝ) ^ j ≤ ∑ j ∈ window m, (2 : ℝ) ^ j := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hq := D.qm_le_one hm (one_le_of_mem_window' hm hj)
    have h2 : (0 : ℝ) ≤ 2 ^ j := by positivity
    nlinarith
  have h2 : ∑ j ∈ window m, (2 : ℝ) ^ j ≤ ∑ j ∈ Finset.range m, (2 : ℝ) ^ j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j _ _ => by positivity)
    rw [Finset.mem_range]; exact (mem_window.mp hj).2
  have h3 := geom_sum_mul (2 : ℝ) m
  norm_num at h3
  linarith

/-- **Witness.** The positive sequence `1/(j!)²` is a subsolution of `eq:doubling_avg`
(at every `m ≥ max(2, 1/c)`). -/
theorem isSubsolution_inv_factorial_sq :
    D.IsSubsolution (fun j => (((j.factorial : ℕ) : ℝ) ^ 2)⁻¹) := by
  have hc := D.c_pos
  refine ⟨⌈D.c⁻¹⌉₊ + 2, fun m hm => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hm1 : 1 ≤ n + 1 := by omega
  have hn1 : 1 ≤ n := by omega
  have hmem : n ∈ window (n + 1) := by rw [mem_window]; omega
  have hnn : ∀ j ∈ window (n + 1), 0 ≤ D.qm (n + 1) j * (((j.factorial : ℕ) : ℝ) ^ 2)⁻¹ :=
    fun j _ => mul_nonneg (D.qm_pos hm1 j).le (by positivity)
  have hsingle := Finset.single_le_sum hnn hmem
  refine le_trans ?_ hsingle
  have hF : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfac : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hcn : 1 ≤ D.c * ((n : ℝ) + 1) := by
    have h1 : D.c⁻¹ ≤ (⌈D.c⁻¹⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈D.c⁻¹⌉₊ + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at h2
    have h3 : D.c⁻¹ ≤ (n : ℝ) + 1 := by linarith
    have := mul_le_mul_of_nonneg_left h3 hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at this
  have hq : D.c / ((n : ℝ) + 1) ≤ D.qm (n + 1) n := by
    rw [D.qm_eq]
    have he1 := D.one_sub_eps_pos hm1
    have he2 := D.eps_pos (n + 1)
    apply div_le_div_of_nonneg_left hc.le (mul_pos (base_pos n) he1)
    have hb := base_pos n
    nlinarith
  show (((((n + 1).factorial : ℕ) : ℝ)) ^ 2)⁻¹ ≤ _
  rw [hfac]
  have hsq : ((((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ)) ^ 2)⁻¹
      = (D.c / ((n : ℝ) + 1)) * ((((n.factorial : ℕ) : ℝ) ^ 2)⁻¹)
        * (1 / (D.c * ((n : ℝ) + 1))) := by
    field_simp
  rw [hsq]
  have hA : 0 ≤ (D.c / ((n : ℝ) + 1)) * ((((n.factorial : ℕ) : ℝ) ^ 2)⁻¹) := by positivity
  have hB : 1 / (D.c * ((n : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hcn
  calc (D.c / ((n : ℝ) + 1)) * ((((n.factorial : ℕ) : ℝ) ^ 2)⁻¹) * (1 / (D.c * ((n : ℝ) + 1)))
      ≤ (D.c / ((n : ℝ) + 1)) * ((((n.factorial : ℕ) : ℝ) ^ 2)⁻¹) * 1 :=
        mul_le_mul_of_nonneg_left hB hA
    _ ≤ D.qm (n + 1) n * (((n.factorial : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right hq (by positivity)

end Parity

/-! ## The `O(·)` form -/

/-- **`eq:doubling_Rexp`, in the paper's `O(m^{-2})` form**, with the constant `cR α` of `Rexp`
as its implied constant. -/
theorem Rexp_isBigO (α : ℝ) :
    (fun m : ℕ => D.Ralpha α m - 1 - (D.Ad m + D.Gam * α) / (m : ℝ))
      =O[Filter.atTop] (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) := by
  refine Asymptotics.IsBigO.of_bound (D.cR α) (Filter.eventually_atTop.2 ⟨⌈2 * |α|⌉₊ + 1,
    fun m hm => ?_⟩)
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hα : 2 * |α| ≤ (m : ℝ) := by
    have h1 : 2 * |α| ≤ (⌈2 * |α|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 * |α|⌉₊ + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    push_cast at h2
    linarith
  have h := D.Rexp α hm1 hα
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) ^ 2)⁻¹), ← div_eq_mul_inv]
  exact h

/-! ## The constants depend on `c` alone -/

/-- `p = p_*(c)`: two decay bundles with the same `c` carry the same exponent. -/
theorem p_congr {D D' : Decay} (h : D.c = D'.c) : D.p = D'.p :=
  cramer_root_unique D.c_pos D.p_ne D'.p_ne D.root (h ▸ D'.root)

/-- **The implied constant of `eq:doubling_Rexp` depends on `c` and `α` alone.** -/
theorem cR_congr {D D' : Decay} (h : D.c = D'.c) (α : ℝ) : D.cR α = D'.cR α := by
  rw [cR, cR, tau, tau, p_congr h]

/-- The parity thresholds `16τ(p+3)²/A₀` and `16τ(p+3)²/(−A₁)` depend on `c` alone. -/
theorem parity_thresholds_congr {D D' : Decay} (h : D.c = D'.c) :
    D.cR 0 / D.A0 = D'.cR 0 / D'.A0 ∧ D.cR 0 / (-D.A1) = D'.cR 0 / (-D'.A1) := by
  have hp := p_congr h
  refine ⟨?_, ?_⟩
  · rw [cR_congr h, A0, A0, tau, tau, hp]
  · rw [cR_congr h, A1, A1, A0, A0, tau, tau, hp, h]

/-! ## `Decay` is inhabited -/

/-- **Witness.** The bundle every statement here quantifies over is inhabited: at `c = 1/2` the
Cramér equation has a non-zero root. -/
theorem nonempty_decay : Nonempty Decay := by
  have hlog : (1 / 2 : ℝ) * Real.log 2 ≠ 1 := by
    have := Real.log_two_lt_d9
    intro h; linarith
  obtain ⟨p, hp0, hroot, -⟩ := cramer_root_exists (c := 1 / 2) (by norm_num) hlog
  exact ⟨⟨1 / 2, p, by norm_num, by norm_num, hp0, hroot⟩⟩

end Decay

end GFNBounds.Doubling
