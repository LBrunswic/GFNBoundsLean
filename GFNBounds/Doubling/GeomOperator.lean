import GFNBounds.Doubling.GeomPoincare
import GFNBounds.Doubling.OperatorFinite

/-!
# A finite diffusion constant on the infinite doubling graph

On the loop closure, under the tail hypothesis `L(k) ≤ B λ_k` of `GeomPoincare.lean`,
`Id − P⋆ + Π` is invertible on `L²(λ)` and the diffusion operator `S := (Id − P⋆ + Π)^{-1} − Π`
satisfies `eq:doubling_resolvent` — so `B̂ = ‖S‖ < +∞`, the negation of the convention
`B̂ = +∞` that `UnboundedL2.no_diffusionOp` certifies under the growth condition (★).

1. The range of `Id − P⋆` is closed: `Id − P⋆` is bounded below on `ker Π` (`Stat.coercive`), so
   its restriction to the complete space `ker Π` is antilipschitz; and the range is the image of
   `ker Π`, a class and its mean-zero part having the same defect.
2. Closed and dense in `ker Π` (`Unsolvable.topologicalClosure_defectRange`), it is `ker Π`.
3. `Id − P⋆ + Π` is therefore injective (a kernel vector is mean-zero, then `0` by coercivity) and
   surjective (`Y = (Y − ΠY) + ΠY`, the first term a defect), hence invertible by the open mapping
   theorem, and `OperatorFinite.resolvent_identities_of_inverse` gives the identities.

## SCOPE (disclosed)

Loop closure only. The tail hypothesis is carried; `GeomFamily.lean` discharges it for a
geometrically decaying doubling probability. Not a statement of the paper: the geometric row of
the policy table, proposed 2026-09-19.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal

variable {S : Setting}

namespace Stat

variable (L : Stat S none)

theorem coerK_nonneg {B : ℝ} (hB : ∀ k, 1 ≤ k → L.tailMass k ≤ B * L.lam (.lad k)) :
    0 ≤ L.coerK B := by
  have h0 := L.pos (x := St.lad 0) trivial
  have h1 : 0 < 1 - S.epsMax := by linarith [S.epsMax_lt_one]
  have hB0 : 0 ≤ B := by
    have h1' := hB 1 le_rfl
    have := L.tailMass_pos 1
    have := L.pos (x := St.lad 1) trivial
    by_contra hneg; push Not at hneg; nlinarith
  unfold coerK
  positivity

/-- `Π` kills every defect. -/
theorem piL2_defect (F : Lp ℝ 2 L.mu) : L.piL2 (L.defect F) = 0 := by
  have h : L.defect F ∈ L.kerPi := L.defectRange_le_kerPi ⟨F, rfl⟩
  rw [piL2_apply, Submodule.mem_orthogonal_singleton_iff_inner_right.mp h, zero_smul]

theorem piL2_eq_zero_iff {F : Lp ℝ 2 L.mu} : L.piL2 F = 0 ↔ F ∈ L.kerPi := by
  rw [kerPi, Submodule.mem_orthogonal_singleton_iff_inner_right, piL2_apply]
  constructor
  · intro h
    have := congrArg (fun G => ⟪L.oneLp, G⟫_ℝ) h
    simp only [real_inner_smul_right, L.inner_oneLp_self, mul_one, inner_zero_right] at this
    exact this
  · intro h; rw [h, zero_smul]

/-- **The range of `Id − P⋆` is `ker Π`.** -/
theorem defectRange_eq_kerPi {B : ℝ} (hB : ∀ k, 1 ≤ k → L.tailMass k ≤ B * L.lam (.lad k)) :
    L.defectRange = L.kerPi := by
  haveI : CompleteSpace L.kerPi := by
    unfold kerPi; exact (Submodule.isClosed_orthogonal _).completeSpace_coe
  let D : L.kerPi →L[ℝ] Lp ℝ 2 L.mu := L.defect.comp L.kerPi.subtypeL
  have hK := L.coerK_nonneg hB
  have hanti : AntilipschitzWith ⟨L.coerK B, hK⟩ D :=
    ContinuousLinearMap.antilipschitz_of_bound D fun x => L.coercive hB x.2
  have hclosedD : IsClosed (Set.range D) := hanti.isClosed_range D.uniformContinuous
  have hrange : Set.range D = (L.defectRange : Set (Lp ℝ 2 L.mu)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1, rfl⟩
    · rintro ⟨F, rfl⟩
      refine ⟨⟨F - ⟪L.oneLp, F⟫_ℝ • L.oneLp, L.sub_mean_mem_kerPi F⟩, ?_⟩
      show L.defect (F - ⟪L.oneLp, F⟫_ℝ • L.oneLp) = L.defect F
      exact L.defect_sub_mean F
  have hclosed : IsClosed (L.defectRange : Set (Lp ℝ 2 L.mu)) := hrange ▸ hclosedD
  rw [← L.topologicalClosure_defectRange]
  exact (IsClosed.submodule_topologicalClosure_eq hclosed).symm

/-- **`Id − P⋆ + Π` is invertible on `L²(λ)`.** -/
theorem exists_inverse_of_tail {B : ℝ} (hB : ∀ k, 1 ≤ k → L.tailMass k ≤ B * L.lam (.lad k)) :
    ∃ R : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
      (1 - L.pstarL2 (rowOnChain_none S) + L.piL2) * R = 1
      ∧ R * (1 - L.pstarL2 (rowOnChain_none S) + L.piL2) = 1 := by
  set A : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu := 1 - L.pstarL2 (rowOnChain_none S) + L.piL2 with hA
  have hAapp : ∀ F, A F = L.defect F + L.piL2 F := fun F => rfl
  have hK := L.coerK_nonneg hB
  have hker : LinearMap.ker (A : Lp ℝ 2 L.mu →ₗ[ℝ] Lp ℝ 2 L.mu) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro F hF
    have hF' : L.defect F + L.piL2 F = 0 := (hAapp F).symm.trans hF
    have hpi : L.piL2 F = 0 := by
      have := congrArg L.piL2 hF'
      have hpp : L.piL2 (L.piL2 F) = L.piL2 F := congrArg (fun T => T F) L.piL2_mul_piL2
      rwa [map_add, L.piL2_defect, zero_add, hpp, map_zero] at this
    have hdef : L.defect F = 0 := by rw [hpi, add_zero] at hF'; exact hF'
    have hmem : F ∈ L.kerPi := (L.piL2_eq_zero_iff).mp hpi
    have := L.coercive hB hmem
    rw [hdef, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.mp this
  have hran : LinearMap.range (A : Lp ℝ 2 L.mu →ₗ[ℝ] Lp ℝ 2 L.mu) = ⊤ := by
    rw [eq_top_iff]
    intro Y _
    have hY0 : Y - ⟪L.oneLp, Y⟫_ℝ • L.oneLp ∈ L.defectRange := by
      rw [L.defectRange_eq_kerPi hB]; exact L.sub_mean_mem_kerPi Y
    obtain ⟨G, hG⟩ := hY0
    set G₀ := G - ⟪L.oneLp, G⟫_ℝ • L.oneLp
    have hG₀ : L.defect G₀ = Y - ⟪L.oneLp, Y⟫_ℝ • L.oneLp := by
      rw [L.defect_sub_mean]; exact hG
    have hpiG₀ : L.piL2 G₀ = 0 := (L.piL2_eq_zero_iff).mpr (L.sub_mean_mem_kerPi G)
    refine ⟨G₀ + ⟪L.oneLp, Y⟫_ℝ • L.oneLp, ?_⟩
    show A (G₀ + ⟪L.oneLp, Y⟫_ℝ • L.oneLp) = Y
    rw [hAapp, map_add, map_add, map_smul, map_smul, L.defect_oneLp, smul_zero, add_zero, hG₀,
      hpiG₀, zero_add, piL2_apply, real_inner_self_eq_norm_sq, L.norm_oneLp, one_pow, one_smul]
    abel
  let e := ContinuousLinearEquiv.ofBijective A hker hran
  refine ⟨(e.symm : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu), ?_, ?_⟩
  · ext1 F
    show A (e.symm F) = F
    exact e.apply_symm_apply F
  · ext1 F
    show e.symm (A F) = F
    exact e.symm_apply_apply F

/-- **A finite diffusion constant.** Under `L(k) ≤ B λ_k`, `Id − P⋆ + Π` is invertible on
`L²(λ)` and `S := (Id − P⋆ + Π)^{-1} − Π` satisfies `eq:doubling_resolvent`:
`(Id − P⋆)S = S(Id − P⋆) = Id − Π` and `ΠS = SΠ = 0`. Its norm is `B̂ < +∞`. -/
theorem exists_diffusionOp_of_tail {B : ℝ}
    (hB : ∀ k, 1 ≤ k → L.tailMass k ≤ B * L.lam (.lad k)) :
    ∃ R : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
      (1 - L.pstarL2 (rowOnChain_none S) + L.piL2) * R = 1
      ∧ R * (1 - L.pstarL2 (rowOnChain_none S) + L.piL2) = 1
      ∧ (1 - L.pstarL2 (rowOnChain_none S)) * (R - L.piL2) = 1 - L.piL2
      ∧ (R - L.piL2) * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2
      ∧ L.piL2 * (R - L.piL2) = 0
      ∧ (R - L.piL2) * L.piL2 = 0 := by
  obtain ⟨R, hMR, hRM⟩ := L.exists_inverse_of_tail hB
  obtain ⟨e1, e2, e3, e4⟩ := resolvent_identities_of_inverse L.piL2_mul_piL2
    (L.piL2_mul_pstarL2 (rowOnChain_none S)) (L.pstarL2_mul_piL2 (rowOnChain_none S)) hMR hRM
  exact ⟨R, hMR, hRM, e1, e2, e3, e4⟩

end Stat

end GFNBounds.Doubling
