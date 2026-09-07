import GFNBounds.Doubling.R0Bound

/-!
# `lem:doubling_escape`, Step 1: the descent halves at a uniform rate

**`lem:doubling_escape`** — `app_doubling.tex:1026–1108`.

> Let `s = 1` and `0 < c < 1`, in the notation of `def:doubling_setting` and
> `def:doubling_decay_notation`, with the integer `ℓ₁` of `lem:doubling_descent`. Put
> `γ := √τ/(2(√τ+1))`, so that `0 < γ < ½`, and `c₅ := 6/γ²`. Then there is an integer
> `ℓ₂ ≥ 2ℓ₁`, depending on `c` and `d` alone, such that for every `ℓ ≥ ℓ₂` the descent chain
> `(Y_n)` of `lem:doubling_descent` at the level `ℓ` satisfies
> `P(Y₁ ≤ y/√2 | Y₀ = y) ≥ γ` for every `y ≥ 2ℓ`  (`eq:doubling_escape`),
> and, for every `i ≥ 1` and every `y ∈ I_i(ℓ)`, the exit time `ς := inf{n : Y_n ∉ I_i(ℓ)}` obeys
> `P(ς > 2r) ≤ (1−γ²)^r`, `E(ς) ≤ 2/γ²` and `E(ζ^ς) ≤ 1 + c₅(ζ−1)` (`eq:doubling_sojourn`).

## SCOPE (disclosed)

**Only Step 1 is in this file** — `eq:doubling_escape`, the analytic half. Step 2's three
sojourn bounds, `eq:doubling_sojourn`, are statements about the law of an exit time; they are
proved in `Sojourn.lean`, which models that law by the survival recursion `Decay.surv` and takes
`Decay.escape` below as its only input. Nothing here depends on that file.

Step 1 is stated here without a chain, exactly as the transition law of `lem:doubling_descent`
defines it: `P(Y₁ = j | Y₀ = y) = w_y(j)/R₀(y)` for `j ∈ W(y)`, so

  `P(Y₁ ≤ y/√2 | Y₀ = y)  =  (Σ_{j ∈ W(y), j ≤ y/√2} w_y(j)) / R₀(y)`,

and that quotient is what `Decay.escape` bounds below by `γ`. `Decay.escape_sum` is the
un-normalised half, `Σ_{j=⌈y/2⌉}^{⌊y/√2⌋} w_y(j) ≥ 2γ − 4cτ/y`, which is the paper's display.

**The threshold is explicit.** The paper's `ℓ₂` is non-effective, inheriting `c₄` and `ℓ₁` from
`lem:doubling_descent`. With `R0Bound.lean`'s effective `c₄ = 16cτ` the three requirements the
paper imposes on `ℓ₂` — that `y ≥ 2ℓ₂` force `⌈y/2⌉ ≤ ⌊y/√2⌋ ≤ y−1`, `4cτ/y ≤ γ/2` and
`c₄/y ≤ ½` — all follow from the single condition

  `y ≥ 32 c τ`,

because `cτ = p_* + c > 1` and `γ > ¼`. So `ℓ₂ := max(d+1, ⌈16cτ⌉)` works, and it is already
`≥ ℓ₁`; the paper's `ℓ₂ ≥ 2ℓ₁` is not needed. That is `Decay.ell2` and `Decay.escape_of_level`.

**No integral.** The paper's Step 1 compares `Σ (j+1)^{−p−1}` with `∫ t^{−p−1} dt`. Here
`sum_shift_ge` does the same comparison by telescoping against `t ↦ (t+1)^{−p}`, in the manner of
`WindowSum.lean`; the resulting bound `((a+1)^{−p} − (b+2)^{−p})/p` is the paper's, term for term.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1` | ✓ carried, as the shape of `Decay.eps` |
| `0 < c < 1` | ✓ carried (`Decay.c_pos`, `Decay.c_lt_one`) |
| `p = p_*` the Cramér root, `τ = 2^{p_*}` | ✓ carried (`Decay.root`, `Decay.tau`) |
| `ℓ₁` of `lem:doubling_descent` | ⚠ replaced by the effective `y ≥ 32cτ`; strictly weaker, since `ℓ₁ ≥ 32cτ` there |
| `ℓ ≥ ℓ₂` and `y ≥ 2ℓ` | ✓ carried, in `escape_of_level`; `escape` takes the sharper `32cτ ≤ y` |
| `γ = √τ/(2(√τ+1))`, `0 < γ < ½` | ✓ carried (`Decay.gam`, `gam_pos`, `gam_lt_half`) |
| `c₅ = 6/γ²` and `eq:doubling_sojourn` | ✗ not proved — Step 2, see SCOPE |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-- **Shifted window comparison.** `((a+1)^{−r} − (b+1)^{−r})/r ≤ Σ_{j ∈ [a,b)} (j+1)^{−r−1}`.

The companion of `sum_window_ge`, telescoped against `t ↦ (t+1)^{−r}` instead of `t ↦ t^{−r}`.
It is what replaces the paper's `∫_{a+1}^{b+2} t^{−p−1} dt`, and unlike `sum_window_ge` it needs
no positivity of the left endpoint. -/
theorem sum_shift_ge {r : ℝ} (hr : 0 < r) {a b : ℕ} (hab : a ≤ b) :
    (((a : ℝ) + 1) ^ (-r) - ((b : ℝ) + 1) ^ (-r)) / r
      ≤ ∑ j ∈ Finset.Ico a b, ((j : ℝ) + 1) ^ (-r - 1) := by
  have hstep : ∀ j ∈ Finset.Ico a b,
      (((j : ℝ) + 1) ^ (-r) - (((j + 1 : ℕ) : ℝ) + 1) ^ (-r)) / r ≤ ((j : ℝ) + 1) ^ (-r - 1) := by
    intro j _
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hcast : (((j + 1 : ℕ)) : ℝ) + 1 = ((j : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast, div_le_iff₀ hr]
    have := incr_le' hr hjpos
    linarith
  have hsum := Finset.sum_le_sum hstep
  rw [← Finset.sum_div, telescope_Ico (fun j : ℕ => (((j : ℝ) + 1) ^ (-r))) hab] at hsum
  exact hsum

/-- `√2 < 1.415`. -/
theorem sqrt_two_lt : Real.sqrt 2 < 1.415 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- `1 < √2`. -/
theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := by linarith [one_lt_sqrt_two]

namespace Decay

variable (D : Decay)

/-! ### `√τ`, `γ`, and the two constants they satisfy -/

/-- `√τ`. -/
noncomputable def sqTau : ℝ := Real.sqrt D.tau

theorem sqTau_sq : D.sqTau ^ 2 = D.tau := Real.sq_sqrt D.tau_pos.le

theorem one_lt_sqTau : 1 < D.sqTau := by
  have h : Real.sqrt 1 < Real.sqrt D.tau :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith [D.tau_gt_two])
  rw [Real.sqrt_one] at h
  exact h

theorem sqTau_pos : 0 < D.sqTau := lt_trans one_pos D.one_lt_sqTau

/-- `(√2)^{p_*} = √τ`. -/
theorem sqrt_two_rpow : (Real.sqrt 2) ^ D.p = D.sqTau := by
  rw [sqTau, tau, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  ring_nf

/-- **`γ := √τ/(2(√τ+1))`** of `lem:doubling_escape`. -/
noncomputable def gam : ℝ := D.sqTau / (2 * (D.sqTau + 1))

theorem gam_pos : 0 < D.gam := by
  have h := D.sqTau_pos
  rw [gam]; positivity

/-- `γ < ½`, as the statement of `lem:doubling_escape` asserts. -/
theorem gam_lt_half : D.gam < 1 / 2 := by
  have h := D.sqTau_pos
  rw [gam, div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `γ > ¼`, which is what makes the threshold `32cτ` cover `4cτ/y ≤ γ/2`. Not in the paper. -/
theorem quarter_lt_gam : 1 / 4 < D.gam := by
  have h := D.one_lt_sqTau
  rw [gam, div_lt_div_iff₀ (by norm_num) (by positivity)]
  linarith

/-- `c(τ−1) = p_*`, the Cramér equation cleared of its denominator. -/
theorem cramer_mul : D.c * (D.tau - 1) = D.p := by
  have hc := D.cramer
  have hp := D.p_pos
  field_simp at hc
  linarith

/-- `cτ > 1`: indeed `cτ = p_* + c` and `p_* > 1`. Not in the paper; it is what makes the
threshold `32cτ` automatically larger than the absolute constants Step 1 needs. -/
theorem one_lt_ctau : 1 < D.c * D.tau := by
  have h := D.cramer_mul
  have := D.p_gt_one
  have := D.c_pos
  nlinarith

theorem ctau_pos : 0 < D.c * D.tau := lt_trans one_pos D.one_lt_ctau

/-- **`2γ = c(τ−√τ)/p_*`**, the identity that turns the paper's window bound into `2γ`. -/
theorem two_gam_eq : D.c * ((D.tau - D.sqTau) / D.p) = 2 * D.gam := by
  have hs := D.sqTau_sq
  have h1 := D.one_lt_sqTau
  have hcram := D.cramer_mul
  have hcne : D.c ≠ 0 := D.c_pos.ne'
  rw [gam, ← hcram, ← hs]
  have ht1 : D.sqTau ^ 2 - 1 ≠ 0 := by nlinarith
  have ht2 : D.sqTau + 1 ≠ 0 := by linarith
  field_simp
  ring

/-! ### The two endpoint estimates -/

/-- `(x/2)^{−p_*} = τ x^{−p_*}`. -/
theorem half_rpow' {x : ℝ} (hx : 0 < x) : (x / 2) ^ (-D.p) = D.tau * x ^ (-D.p) := by
  rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), tau,
    div_eq_mul_inv, inv_inv]
  ring

/-- **The foot of the halving window.** With `a = ⌈y/2⌉`, `(a+1)^{−p} ≥ τ y^{−p}(1 − 4p/y)`.
This is the paper's `a+1 ≤ (y/2)(1+4/y)` followed by `(1+x)^{−p} ≥ 1 − px`. -/
theorem foot_shift_ge {y : ℕ} (hy : 1 ≤ y) :
    D.tau * (y : ℝ) ^ (-D.p) * (1 - 4 * D.p / (y : ℝ))
      ≤ ((((y + 1) / 2 : ℕ) : ℝ) + 1) ^ (-D.p) := by
  have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hppos := D.p_pos
  have hale : ((((y + 1) / 2 : ℕ) : ℝ) + 1) ≤ ((y : ℝ) + 4) / 2 := by
    have := le_foot y
    linarith
  have hstep : (((y : ℝ) + 4) / 2) ^ (-D.p) ≤ ((((y + 1) / 2 : ℕ) : ℝ) + 1) ^ (-D.p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hale (by linarith)
  refine le_trans ?_ hstep
  rw [D.half_rpow' (by linarith : (0:ℝ) < (y : ℝ) + 4)]
  have hsplit : ((y : ℝ) + 4) = (y : ℝ) * (1 + 4 / (y : ℝ)) := by field_simp
  have hprod : ((y : ℝ) + 4) ^ (-D.p) = (y : ℝ) ^ (-D.p) * (1 + 4 / (y : ℝ)) ^ (-D.p) := by
    rw [hsplit, Real.mul_rpow hypos.le (by positivity)]
  rw [hprod]
  have htan : 1 - 4 * D.p / (y : ℝ) ≤ (1 + 4 / (y : ℝ)) ^ (-D.p) := by
    have h := rpow_ge_tangent (q := -D.p) (u := 1 + 4 / (y : ℝ))
      (by linarith) (by positivity)
    have he : 1 + -D.p * ((1 + 4 / (y : ℝ)) - 1) = 1 - 4 * D.p / (y : ℝ) := by
      field_simp; ring
    linarith [h, he.symm.le, he.le]
  have hyp : (0 : ℝ) < (y : ℝ) ^ (-D.p) := Real.rpow_pos_of_pos hypos _
  have h1 : (y : ℝ) ^ (-D.p) * (1 - 4 * D.p / (y : ℝ))
      ≤ (y : ℝ) ^ (-D.p) * (1 + 4 / (y : ℝ)) ^ (-D.p) :=
    mul_le_mul_of_nonneg_left htan hyp.le
  calc D.tau * (y : ℝ) ^ (-D.p) * (1 - 4 * D.p / (y : ℝ))
      = D.tau * ((y : ℝ) ^ (-D.p) * (1 - 4 * D.p / (y : ℝ))) := by ring
    _ ≤ D.tau * ((y : ℝ) ^ (-D.p) * (1 + 4 / (y : ℝ)) ^ (-D.p)) :=
        mul_le_mul_of_nonneg_left h1 D.tau_pos.le

/-- **The head of the halving window.** Any `z ≥ y/√2` has `z^{−p} ≤ √τ y^{−p}`. -/
theorem head_shift_le {y : ℕ} (hy : 1 ≤ y) {z : ℝ} (hz : (y : ℝ) / Real.sqrt 2 ≤ z) :
    z ^ (-D.p) ≤ D.sqTau * (y : ℝ) ^ (-D.p) := by
  have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hwpos : (0 : ℝ) < (y : ℝ) / Real.sqrt 2 := div_pos hypos sqrt_two_pos
  have hstep : z ^ (-D.p) ≤ ((y : ℝ) / Real.sqrt 2) ^ (-D.p) :=
    Real.rpow_le_rpow_of_nonpos hwpos hz (by linarith [D.p_pos])
  refine le_trans hstep (le_of_eq ?_)
  have hsne : D.sqTau ≠ 0 := D.sqTau_pos.ne'
  rw [Real.div_rpow hypos.le sqrt_two_pos.le, Real.rpow_neg sqrt_two_pos.le, D.sqrt_two_rpow]
  field_simp

/-! ### The weight of one window index, from below -/

/-- `w_y(j) ≥ c y^{p}(j+1)^{−p−1}`, the paper's first inequality of Step 1. -/
theorem wm_ge_shift {y j : ℕ} (hy : 1 ≤ y) (hj : 1 ≤ j) :
    D.c * (y : ℝ) ^ D.p * (((j : ℝ) + 1) ^ (-D.p - 1)) ≤ D.wm y j := by
  have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hApos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have heps := D.one_sub_eps_pos hy
  have heps1 : 1 - D.eps y ≤ 1 := by linarith [D.eps_pos y]
  have hypp : (0 : ℝ) < (y : ℝ) ^ D.p := Real.rpow_pos_of_pos hypos _
  have hpow : ((y : ℝ) / (j : ℝ)) ^ D.p = (y : ℝ) ^ D.p * (j : ℝ) ^ (-D.p) := by
    rw [Real.div_rpow hypos.le hjpos.le, Real.rpow_neg hjpos.le, div_eq_mul_inv]
  -- `(j+1)^{-p-1} = (j+1)^{-p}/(j+1) ≤ j^{-p}/(j+1)`
  have hshift : ((j : ℝ) + 1) ^ (-D.p - 1) ≤ (j : ℝ) ^ (-D.p) / ((j : ℝ) + 1) := by
    rw [rpow_sub_one_eq hApos]
    have : ((j : ℝ) + 1) ^ (-D.p) ≤ (j : ℝ) ^ (-D.p) :=
      Real.rpow_le_rpow_of_nonpos hjpos (by linarith) (by linarith [D.p_pos])
    exact div_le_div_of_nonneg_right this hApos.le
  have hcy : (0 : ℝ) ≤ D.c * (y : ℝ) ^ D.p := mul_nonneg D.c_pos.le hypp.le
  have h1 : D.c * (y : ℝ) ^ D.p * (((j : ℝ) + 1) ^ (-D.p - 1))
      ≤ D.c * (y : ℝ) ^ D.p * ((j : ℝ) ^ (-D.p) / ((j : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hshift hcy
  refine le_trans h1 ?_
  rw [wm, D.qm_eq, hpow]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have hnn : (0 : ℝ) ≤ (j : ℝ) ^ (-D.p) := Real.rpow_nonneg hjpos.le _
  have hkey : D.c * (y : ℝ) ^ D.p * ((j : ℝ) ^ (-D.p) / ((j : ℝ) + 1)) * (((j:ℝ) + 1) * (1 - D.eps y))
      = (D.c * ((y : ℝ) ^ D.p * (j : ℝ) ^ (-D.p))) * (1 - D.eps y) := by
    field_simp
  rw [hkey]
  have hpp : (0 : ℝ) ≤ D.c * ((y : ℝ) ^ D.p * (j : ℝ) ^ (-D.p)) :=
    mul_nonneg D.c_pos.le (mul_nonneg hypp.le hnn)
  nlinarith [hpp, heps1]

/-! ### `eq:doubling_escape` -/

/-- The halving window `{j : ⌈y/2⌉ ≤ j ≤ ⌊y/√2⌋}`, as an interval of integers. -/
noncomputable def halveIco (y : ℕ) : Finset ℕ :=
  Finset.Ico ((y + 1) / 2) (⌊(y : ℝ) / Real.sqrt 2⌋₊ + 1)

section Escape

variable {y : ℕ}

/-- The threshold used throughout: `32cτ ≤ y` forces `y > 32`, since `cτ > 1`. -/
theorem thirty_two_lt (hy : 32 * D.c * D.tau ≤ (y : ℝ)) : (32 : ℝ) < (y : ℝ) := by
  have := D.one_lt_ctau
  nlinarith

theorem one_le_of_thr (hy : 32 * D.c * D.tau ≤ (y : ℝ)) : 1 ≤ y := by
  have h := D.thirty_two_lt hy
  have : (1 : ℝ) ≤ (y : ℝ) := by linarith
  exact_mod_cast this

/-- `⌊y/√2⌋ < y`. -/
theorem floor_lt_self (hy : 32 * D.c * D.tau ≤ (y : ℝ)) :
    ⌊(y : ℝ) / Real.sqrt 2⌋₊ < y := by
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith [D.thirty_two_lt hy]
  have h1 : ((⌊(y : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) ≤ (y : ℝ) / Real.sqrt 2 :=
    Nat.floor_le (by positivity)
  have h2 : (y : ℝ) / Real.sqrt 2 < (y : ℝ) := div_lt_self hypos one_lt_sqrt_two
  have : ((⌊(y : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) < (y : ℝ) := lt_of_le_of_lt h1 h2
  exact_mod_cast this

/-- `⌈y/2⌉ ≤ ⌊y/√2⌋`: the halving window is non-empty. -/
theorem foot_le_floor (hy : 32 * D.c * D.tau ≤ (y : ℝ)) :
    (y + 1) / 2 ≤ ⌊(y : ℝ) / Real.sqrt 2⌋₊ := by
  have hy32 := D.thirty_two_lt hy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hfoot : ((((y + 1) / 2 : ℕ)) : ℝ) ≤ ((y : ℝ) + 1) / 2 := le_foot y
  have hflo : (y : ℝ) / Real.sqrt 2 < ((⌊(y : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hcmp : (y : ℝ) / 1.415 ≤ (y : ℝ) / Real.sqrt 2 :=
    div_le_div_of_nonneg_left hypos.le sqrt_two_pos sqrt_two_lt.le
  have hlin : ((y : ℝ) + 1) / 2 + 1 ≤ (y : ℝ) / 1.415 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1.415)]
    linarith
  have : ((((y + 1) / 2 : ℕ)) : ℝ) ≤ ((⌊(y : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) := by linarith
  exact_mod_cast this

set_option maxHeartbeats 800000 in
/-- **`lem:doubling_escape`, Step 1, un-normalised.** The paper's display

  `Σ_{j=⌈y/2⌉}^{⌊y/√2⌋} w_y(j) ≥ 2γ − 4cτ/y`. -/
theorem escape_sum (hy : 32 * D.c * D.tau ≤ (y : ℝ)) :
    2 * D.gam - 4 * D.c * D.tau / (y : ℝ) ≤ ∑ j ∈ halveIco y, D.wm y j := by
  have hy1 : 1 ≤ y := D.one_le_of_thr hy
  have hy32 := D.thirty_two_lt hy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hppos := D.p_pos
  set a : ℕ := (y + 1) / 2 with ha
  set b : ℕ := ⌊(y : ℝ) / Real.sqrt 2⌋₊ with hb
  have hab : a ≤ b := D.foot_le_floor hy
  have ha1 : 1 ≤ a := one_le_foot hy1
  -- the shifted comparison over `[a, b+1)`
  have hshift := sum_shift_ge (r := D.p) hppos (a := a) (b := b + 1) (by omega)
  have hcast : (((b + 1 : ℕ) : ℝ) + 1) = (b : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hshift
  set S : ℝ := ∑ j ∈ Finset.Ico a (b + 1), ((j : ℝ) + 1) ^ (-D.p - 1) with hS
  set T1 : ℝ := ((a : ℝ) + 1) ^ (-D.p) with hT1
  set T2 : ℝ := ((b : ℝ) + 2) ^ (-D.p) with hT2
  set Y : ℝ := (y : ℝ) ^ (-D.p) with hY
  set Yp : ℝ := (y : ℝ) ^ D.p with hYp
  have hYY : Yp * Y = 1 := by rw [hYp, hY, ← Real.rpow_add hypos]; simp
  have hYppos : (0 : ℝ) < Yp := Real.rpow_pos_of_pos hypos _
  -- the two endpoint estimates
  have hE1 : D.tau * Y * (1 - 4 * D.p / (y : ℝ)) ≤ T1 := D.foot_shift_ge hy1
  have hE2 : T2 ≤ D.sqTau * Y := by
    refine D.head_shift_le hy1 ?_
    have h1 : (y : ℝ) / Real.sqrt 2 < (b : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  -- from below, term by term
  have hterm : ∀ j ∈ Finset.Ico a (b + 1),
      D.c * Yp * (((j : ℝ) + 1) ^ (-D.p - 1)) ≤ D.wm y j := by
    intro j hj
    have hja : a ≤ j := (Finset.mem_Ico.mp hj).1
    exact D.wm_ge_shift hy1 (le_trans ha1 hja)
  have hlow : D.c * Yp * S ≤ ∑ j ∈ halveIco y, D.wm y j := by
    rw [halveIco, ← ha, ← hb, hS, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  -- the analytic chain
  have hcyp : (0 : ℝ) ≤ D.c * Yp := mul_nonneg D.c_pos.le hYppos.le
  have hchain1 : D.c * Yp * ((T1 - T2) / D.p) ≤ D.c * Yp * S :=
    mul_le_mul_of_nonneg_left hshift hcyp
  have hnum : D.tau * Y * (1 - 4 * D.p / (y : ℝ)) - D.sqTau * Y ≤ T1 - T2 := by linarith
  have hchain2 : D.c * Yp * ((D.tau * Y * (1 - 4 * D.p / (y : ℝ)) - D.sqTau * Y) / D.p)
      ≤ D.c * Yp * ((T1 - T2) / D.p) := by
    refine mul_le_mul_of_nonneg_left ?_ hcyp
    exact div_le_div_of_nonneg_right hnum hppos.le
  have hexp : D.c * Yp * ((D.tau * Y * (1 - 4 * D.p / (y : ℝ)) - D.sqTau * Y) / D.p)
      = (Yp * Y) * (D.c * ((D.tau - D.sqTau) / D.p) - 4 * D.c * D.tau / (y : ℝ)) := by
    field_simp
    ring
  rw [hexp, hYY, one_mul, D.two_gam_eq] at hchain2
  linarith

/-- **`eq:doubling_escape`.** `P(Y₁ ≤ y/√2 | Y₀ = y) ≥ γ`, the transition law of
`lem:doubling_descent` being `w_y(j)/R₀(y)` on `W(y)`. -/
theorem escape (hy : 32 * D.c * D.tau ≤ (y : ℝ)) :
    D.gam ≤ (∑ j ∈ halveIco y, D.wm y j) / D.R0 y := by
  have hy1 : 1 ≤ y := D.one_le_of_thr hy
  have hy32 := D.thirty_two_lt hy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hct := D.ctau_pos
  -- `|R₀ − 1| ≤ 16cτ/y ≤ ½`
  have hR := D.R0_sub_one_le hy1
  rw [abs_le] at hR
  have h16 : 16 * D.c * D.tau / (y : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hypos]; linarith
  have hR0up : D.R0 y ≤ 3 / 2 := by linarith [hR.2]
  have hR0pos : (0 : ℝ) < D.R0 y := by linarith [hR.1]
  -- `4cτ/y ≤ 1/8 < γ/2`
  have h4 : 4 * D.c * D.tau / (y : ℝ) ≤ 1 / 8 := by
    rw [div_le_iff₀ hypos]; linarith
  have hg := D.quarter_lt_gam
  have hgpos := D.gam_pos
  have hsum := D.escape_sum hy
  rw [le_div_iff₀ hR0pos]
  have : D.gam * D.R0 y ≤ D.gam * (3 / 2) := mul_le_mul_of_nonneg_left hR0up hgpos.le
  linarith

/-- The interval `halveIco y` is exactly `{j ∈ W(y) : j√2 ≤ y}`, so `escape` really does bound
the transition probability of `eq:doubling_escape`. -/
theorem halveIco_eq_filter (hy : 32 * D.c * D.tau ≤ (y : ℝ)) :
    halveIco y = (window y).filter (fun j : ℕ => (j : ℝ) * Real.sqrt 2 ≤ (y : ℝ)) := by
  have hby := D.floor_lt_self hy
  have hy32 := D.thirty_two_lt hy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  ext j
  simp only [halveIco, Finset.mem_Ico, Finset.mem_filter, mem_window]
  constructor
  · rintro ⟨h1, h2⟩
    have hjb : j ≤ ⌊(y : ℝ) / Real.sqrt 2⌋₊ := by omega
    have hjr : (j : ℝ) ≤ (y : ℝ) / Real.sqrt 2 :=
      (Nat.le_floor_iff (by positivity)).mp hjb
    refine ⟨⟨h1, by omega⟩, ?_⟩
    rw [← le_div_iff₀ sqrt_two_pos] at *
    exact hjr
  · rintro ⟨⟨h1, _⟩, h3⟩
    refine ⟨h1, ?_⟩
    have hjr : (j : ℝ) ≤ (y : ℝ) / Real.sqrt 2 := by
      rw [le_div_iff₀ sqrt_two_pos]; exact h3
    have : j ≤ ⌊(y : ℝ) / Real.sqrt 2⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hjr
    omega

/-- **`eq:doubling_escape`, in the paper's own words.** -/
theorem escape_filter (hy : 32 * D.c * D.tau ≤ (y : ℝ)) :
    D.gam ≤
      (∑ j ∈ (window y).filter (fun j : ℕ => (j : ℝ) * Real.sqrt 2 ≤ (y : ℝ)), D.wm y j)
        / D.R0 y := by
  rw [← D.halveIco_eq_filter hy]
  exact D.escape hy

end Escape

/-! ### The explicit threshold `ℓ₂` -/

/-- **`ℓ₂`, made effective.** `ℓ₂ := max(d+1, ⌈16cτ⌉)`, so that `y ≥ 2ℓ ≥ 2ℓ₂` gives `y ≥ 32cτ`,
which is all three of the paper's requirements at once. -/
noncomputable def ell2 (D : Decay) (d : ℕ) : ℕ := max (d + 1) ⌈16 * D.c * D.tau⌉₊

theorem lt_ell2 (d : ℕ) : d < D.ell2 d := lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_left _ _)

theorem thr_of_level {d ℓ y : ℕ} (hℓ : D.ell2 d ≤ ℓ) (hy : 2 * ℓ ≤ y) :
    32 * D.c * D.tau ≤ (y : ℝ) := by
  have h1 : (16 : ℝ) * D.c * D.tau ≤ (⌈16 * D.c * D.tau⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈16 * D.c * D.tau⌉₊ : ℝ) ≤ (D.ell2 d : ℝ) := by
    exact_mod_cast le_max_right (d + 1) ⌈16 * D.c * D.tau⌉₊
  have h3 : ((D.ell2 d : ℕ) : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have h4 : (2 : ℝ) * (ℓ : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  linarith

/-- **`eq:doubling_escape` at the level `ℓ`**, exactly as `lem:doubling_escape` states it:
for every `ℓ ≥ ℓ₂` and every `y ≥ 2ℓ`, `P(Y₁ ≤ y/√2 | Y₀ = y) ≥ γ`. -/
theorem escape_of_level {d ℓ y : ℕ} (hℓ : D.ell2 d ≤ ℓ) (hy : 2 * ℓ ≤ y) :
    D.gam ≤
      (∑ j ∈ (window y).filter (fun j : ℕ => (j : ℝ) * Real.sqrt 2 ≤ (y : ℝ)), D.wm y j)
        / D.R0 y :=
  D.escape_filter (D.thr_of_level hℓ hy)

end Decay

end GFNBounds.Doubling
