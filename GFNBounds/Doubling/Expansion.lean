import GFNBounds.Doubling.DecayNotation

/-!
# The coefficients of the expansion of `R_α`

**`lem:doubling_expansion`** — `app_doubling.tex:848–953`
and **`rem:doubling_parity`** — `app_doubling.tex:955–963`.

> Put `A₀ := p(p+3+2τ(p−1))/(2(p+1)(τ−1))`, `A₁ := A₀ − cτ`, `Γ := (τ(p−1)+1)/((τ−1)(p+1))`.
> Then `A₁ = p(p+3−4τ)/(2(p+1)(τ−1))`, `0 < Γ < 1`, `A₀ > 0 > A₁`, and for every `α`, as
> `m → ∞`, `R_α(m) = 1 + (A_{δ(m)} + Γα)/m + O(m^{-2})`.
>
> (parity) the two parities of `eq:doubling_Rexp` differ at order `1/m` by `(A₀−A₁)/m = cτ/m`.

## SCOPE (disclosed)

**Step 4 of the proof is here; Steps 1–3 are not.** What is proved:

* the closed form of `A₁` (`A_one_eq`), which needs `c(τ−1) = p`;
* `eq:doubling_signs`, `0 < Γ < 1` and `A₀ > 0 > A₁` (`Gamma_pos`, `Gamma_lt_one`, `A_zero_pos`,
  `A_one_neg`), each from one of the four inequalities of `eq:doubling_cramer_ineq`;
* the parity gap `A₀ − A₁ = cτ` of `rem:doubling_parity` (`A_gap`), which is the definition.

What is **not** proved is `eq:doubling_Rexp` itself. Its Step 2 is Euler–Maclaurin for `t^{−r}`
with the complete-monotonicity remainder bound, and mathlib v4.31.0 has neither. This is the one
analytic wall of the appendix, and everything the expansion feeds — `eq:doubling_R0`, hence
`lem:doubling_escape`, `lem:doubling_product` and the unconditional form of
`theo:doubling_decay` — is carried downstream as a hypothesis rather than assumed here. The two
inequalities actually consumed are `½ ≤ R₀(m) ≤ 2` and `|R₀(m) − 1| ≤ c₄/m`.

`rem:doubling_parity`'s second sentence — that `Φ₀` is neither a super- nor a sub-solution — reads
off `eq:doubling_Rexp` and is not available.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

variable (D : Decay)

/-- `A₀` of `eq:doubling_AB`. -/
noncomputable def A0 : ℝ :=
  D.p * (D.p + 3 + 2 * D.tau * (D.p - 1)) / (2 * (D.p + 1) * (D.tau - 1))

/-- `A₁ := A₀ − cτ` of `eq:doubling_AB`. -/
noncomputable def A1 : ℝ := D.A0 - D.c * D.tau

/-- `Γ` of `eq:doubling_AB`. -/
noncomputable def Gam : ℝ := (D.tau * (D.p - 1) + 1) / ((D.tau - 1) * (D.p + 1))

theorem tau_sub_one_pos : 0 < D.tau - 1 := by
  have := D.tau_gt_two; linarith

theorem p_add_one_pos : 0 < D.p + 1 := by
  have := D.p_gt_one; linarith

/-- `c τ = p τ/(τ−1)`, from `c(τ−1) = p`. -/
theorem c_mul_tau : D.c * D.tau = D.p * D.tau / (D.tau - 1) := by
  have h := D.cramer
  have hτ := D.tau_sub_one_pos
  have hp : D.p ≠ 0 := D.p_ne
  field_simp at h ⊢
  nlinarith [h]

/-- **The closed form of `A₁`.** `A₁ = p(p+3−4τ)/(2(p+1)(τ−1))`. -/
theorem A_one_eq : D.A1 = D.p * (D.p + 3 - 4 * D.tau) / (2 * (D.p + 1) * (D.tau - 1)) := by
  have hτ := D.tau_sub_one_pos
  have hp1 := D.p_add_one_pos
  rw [A1, A0, D.c_mul_tau]
  field_simp
  ring

/-- **`rem:doubling_parity`.** The two parities differ at order `1/m` by `A₀ − A₁ = cτ`. -/
theorem A_gap : D.A0 - D.A1 = D.c * D.tau := by rw [A1]; ring

/-- **`eq:doubling_signs`, `Γ > 0`.** -/
theorem Gamma_pos : 0 < D.Gam := by
  have hτ := D.tau_sub_one_pos
  have hp1 := D.p_add_one_pos
  have hp := D.p_gt_one
  have hτ0 := D.tau_pos
  refine div_pos ?_ (by positivity)
  nlinarith

/-- **`eq:doubling_signs`, `Γ < 1`.** The gap is `2τ − p − 2 > 0`, the third inequality of
`eq:doubling_cramer_ineq`. -/
theorem Gamma_lt_one : D.Gam < 1 := by
  have hτ := D.tau_sub_one_pos
  have hp1 := D.p_add_one_pos
  obtain ⟨-, -, h2τ, -⟩ := cramer_ineq D.c_pos D.c_lt_one D.p_ne D.root
  have hden : 0 < (D.tau - 1) * (D.p + 1) := by positivity
  rw [Gam, div_lt_one hden]
  have hτdef : D.tau = (2 : ℝ) ^ D.p := rfl
  rw [hτdef]
  nlinarith [h2τ]

/-- **`eq:doubling_signs`, `A₀ > 0`.** -/
theorem A_zero_pos : 0 < D.A0 := by
  have hτ0 := D.tau_pos
  have hτ := D.tau_sub_one_pos
  have hp := D.p_gt_one
  have hp1 := D.p_add_one_pos
  refine div_pos ?_ (by positivity)
  have h2 : 0 < 2 * D.tau * (D.p - 1) := mul_pos (by positivity) (by linarith)
  exact mul_pos (by linarith) (by linarith)

/-- **`eq:doubling_signs`, `A₁ < 0`.** The sign is `p + 3 − 4τ < 0`, the fourth inequality of
`eq:doubling_cramer_ineq`. -/
theorem A_one_neg : D.A1 < 0 := by
  have hτ := D.tau_sub_one_pos
  have hp := D.p_gt_one
  have hp1 := D.p_add_one_pos
  obtain ⟨-, -, -, h4τ⟩ := cramer_ineq D.c_pos D.c_lt_one D.p_ne D.root
  have hτdef : D.tau = (2 : ℝ) ^ D.p := rfl
  rw [D.A_one_eq]
  apply div_neg_of_neg_of_pos _ (by positivity)
  rw [hτdef] at *
  nlinarith [h4τ]

end Decay

end GFNBounds.Doubling
