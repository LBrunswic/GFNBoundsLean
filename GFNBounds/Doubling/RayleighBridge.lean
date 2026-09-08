import GFNBounds.Doubling.AdjointL2

/-!
# From the `L²(λ)` Rayleigh inequality to the mass layer

No paper label of its own. The unboundedness results of `Unbounded.lean` live in the ℝ mass
layer (`Stat.mass 2 f = ‖f‖²_{L²(λ)}`, over bounded mean-zero `f : St → ℝ`), while the diffusion
operator of `lem:doubling_operator` and `lem:doubling_truncation_irreducible` lives on Mathlib's
`Lp ℝ 2 L.mu`. This file is the one-way bridge the umbrella theorem needs: a bounded left inverse
`S` of `Id − P⋆` on `L²(λ)`, or more generally any constant `B` with
`‖F − ΠF‖ ≤ B‖F − P⋆F‖` on `L²(λ)`, yields `mass 2 f ≤ B² · mass 2 ((Id−P⋆)f)` for every bounded
mean-zero `f`. Read against `Stat.no_bounded_inverse` at `p = 2` it says no such `S` exists on the
loop closure; read against `Stat.sqrtK` on the truncation it turns `‖S‖` into `B̂_K`.

The bridge holds at every `cap`, i.e. on the loop closure and on every truncation.

## SCOPE (disclosed)

* Only the direction *operator bound ⇒ mass inequality* is stated; it is the only one consumed.
* A bounded `f` is in `L²(λ)` because `λ` is a probability (`memLp_two_of_bounded`); the class of
  `f` has zero `λ`-mean exactly when `f` does, and its defect class is the class of the pointwise
  defect (`coeFn_sub_pstarL2_toLp`), both by `Stat.ae_iff_eq`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology

namespace Stat

variable {S : Setting} {cap : Option ℕ} (L : Stat S cap)

/-- A bounded function is in `L²(λ)`: `λ` is a probability. -/
theorem memLp_two_of_bounded {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) : MemLp f 2 L.mu := by
  obtain ⟨C, hC⟩ := hf
  rw [L.memLp_two_iff]
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) (L.summable.mul_left (C ^ 2))
  · exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (L.nonneg x)
  · have h2 : |f x| ^ (2 : ℝ) ≤ C ^ 2 := by
      rw [Real.rpow_two, sq, sq]
      exact mul_self_le_mul_self (abs_nonneg _) (hC x)
    exact mul_le_mul_of_nonneg_right h2 (L.nonneg x)

/-- The `L²` norm squared of a class is the `mass` of any of its representatives, at every `cap`. -/
theorem norm_sq_eq_mass_of_ae {F : Lp ℝ 2 L.mu} {g : St → ℝ} (h : ⇑F =ᵐ[L.mu] g)
    (hg : MemLp g 2 L.mu) : ‖F‖ ^ 2 = L.mass 2 g := by
  rw [Lp.norm_def, ← L.toReal_eLpNorm_two_sq hg, eLpNorm_congr_ae h]

/-- The `λ`-mean of a class is the `λ`-mean of any of its representatives, at every `cap`. -/
theorem tsum_lam_mul_congr_ae {F : Lp ℝ 2 L.mu} {g : St → ℝ} (h : ⇑F =ᵐ[L.mu] g) :
    ∑' x, L.lam x * (F : St → ℝ) x = ∑' x, L.lam x * g x := by
  refine tsum_congr fun x => ?_
  by_cases hx : OnChain cap x
  · rw [L.ae_iff_eq.mp h x hx]
  · rw [L.vanish hx, zero_mul, zero_mul]

/-- The defect class of the class of `f` is the class of the pointwise defect. -/
theorem coeFn_sub_pstarL2_toLp (hrow : RowOnChain S cap) {f : St → ℝ} (hf : MemLp f 2 L.mu) :
    ⇑(hf.toLp f - L.pstarL2 hrow (hf.toLp f)) =ᵐ[L.mu] fun x => f x - pstar S cap f x := by
  have hcong : ∀ x, OnChain cap x → pstar S cap ⇑(hf.toLp f) x = pstar S cap f x :=
    fun _ hx => pstar_congr_onChain hrow (L.ae_iff_eq.mp (MemLp.coeFn_toLp hf)) hx
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (L.pstarL2 hrow (hf.toLp f)), MemLp.coeFn_toLp hf,
    L.coeFn_pstarL2 hrow (hf.toLp f), L.ae_eq_of_onChain hcong] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4]

/-- A bounded left inverse `S` of `Id − P⋆` on `L²(λ)`, `S(Id − P⋆) = Id − Π`, bounds the
mean-zero part of every class by `‖S‖` times its defect. -/
theorem rayleigh_of_leftInverse (hrow : RowOnChain S cap)
    {Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu}
    (hS : Sop * (1 - L.pstarL2 hrow) = 1 - L.piL2) (F : Lp ℝ 2 L.mu) :
    ‖F - L.piL2 F‖ ≤ ‖Sop‖ * ‖F - L.pstarL2 hrow F‖ := by
  have h : (Sop * (1 - L.pstarL2 hrow)) F = (1 - L.piL2) F := by rw [hS]
  have hl : (Sop * (1 - L.pstarL2 hrow)) F = Sop (F - L.pstarL2 hrow F) := by
    show Sop ((1 - L.pstarL2 hrow) F) = _
    congr 1
  have hr : (1 - L.piL2) F = F - L.piL2 F := by simp
  rw [hl, hr] at h
  rw [← h]
  exact ContinuousLinearMap.le_opNorm _ _

/-- **The bridge.** If `‖F − ΠF‖ ≤ B‖F − P⋆F‖` on `L²(λ)`, then every bounded mean-zero `f` has
`mass 2 f ≤ B² · mass 2 ((Id − P⋆)f)`. -/
theorem mass_le_of_rayleighL2 (hrow : RowOnChain S cap) {B : ℝ}
    (hB : ∀ F : Lp ℝ 2 L.mu, ‖F - L.piL2 F‖ ≤ B * ‖F - L.pstarL2 hrow F‖)
    {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) (hmean : ∑' x, L.lam x * f x = 0) :
    L.mass 2 f ≤ B ^ 2 * L.mass 2 (fun x => f x - pstar S cap f x) := by
  have hfL : MemLp f 2 L.mu := L.memLp_two_of_bounded hf
  have hpi : L.piL2 (hfL.toLp f) = 0 := by
    rw [piL2_apply, L.inner_oneLp, L.tsum_lam_mul_congr_ae (MemLp.coeFn_toLp hfL), hmean,
      zero_smul]
  have h1 : ‖hfL.toLp f‖ ≤ B * ‖hfL.toLp f - L.pstarL2 hrow (hfL.toLp f)‖ := by
    have := hB (hfL.toLp f)
    rwa [hpi, sub_zero] at this
  have hF2 : ‖hfL.toLp f‖ ^ 2 = L.mass 2 f :=
    L.norm_sq_eq_mass_of_ae (MemLp.coeFn_toLp hfL) hfL
  have hD2 : ‖hfL.toLp f - L.pstarL2 hrow (hfL.toLp f)‖ ^ 2
      = L.mass 2 (fun x => f x - pstar S cap f x) :=
    L.norm_sq_eq_mass_of_ae (L.coeFn_sub_pstarL2_toLp hrow hfL)
      (hfL.sub (L.memLp_two_pstar hfL))
  rw [← hF2, ← hD2, ← mul_pow, sq, sq]
  exact mul_self_le_mul_self (norm_nonneg _) h1

/-- The bridge, fed by a left inverse: `mass 2 f ≤ ‖S‖² · mass 2 ((Id − P⋆)f)`. -/
theorem mass_le_of_leftInverse (hrow : RowOnChain S cap)
    {Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu} (hS : Sop * (1 - L.pstarL2 hrow) = 1 - L.piL2)
    {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) (hmean : ∑' x, L.lam x * f x = 0) :
    L.mass 2 f ≤ ‖Sop‖ ^ 2 * L.mass 2 (fun x => f x - pstar S cap f x) :=
  L.mass_le_of_rayleighL2 hrow (L.rayleigh_of_leftInverse hrow hS) hf hmean

end Stat

end GFNBounds.Doubling
