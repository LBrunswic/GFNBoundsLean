import GFNBounds.Doubling.GeomOperator
import GFNBounds.Doubling.Main
import GFNBounds.Core.Universality

/-!
# Weak universality on the infinite doubling chain

Wherever the loop closure of the doubling graph has an invariant probability `λ`, the frozen
family is weakly `L²(λ)`-universal: every pair of square-integrable densities of equal mass is
joined by flows of arbitrarily small residual. This is the operator statement
`Core.WeaklyUniversal` for the chain's density action `P` on `L²(λ)`, and for its adjoint `P⋆`, with
the mean projection `Π`.

The range of `Id − P⋆` is dense in the mean-zero classes (`topologicalClosure_defectRange`), so
every mean-zero target is approached by defects of square-integrable functions, of either sign. A
flow needs a non-negative one, and adding a constant is free: `P⋆` fixes the constants, so a
constant has zero defect. Approximate the function by a simple function, which is bounded, and add
its bound: the result is non-negative and its defect has moved by at most twice the
approximation error, since `‖Id − P⋆‖ ≤ 2`.

Strong universality fails on the same chains: `main_unsolvable` exhibits a pair with no exact
solution in `L²(λ)`. So on the positive recurrent rows the chain is weakly but not strongly
`L²(λ)`-universal, and the summable-mixing hypothesis of the general theorem, which fails there,
is sufficient and not necessary.

## What is proved

| | |
|---|---|
| **`weaklyUniversal_of_dense`** | a contraction of `L²(λ)` fixing the constants, whose defect range is dense in the mean-zero classes, is weakly universal |
| **`weaklyUniversal_pstarL2`** | `Core.WeaklyUniversal P⋆ Π` on `L²(λ)`, `P⋆` the function action, for every invariant probability of the loop closure |
| **`topologicalClosure_densDefectRange`** | the range of `Id − P`, `P` the density action, is dense in the mean-zero classes: a vector orthogonal to it is a fixed point of `P⋆`, hence a constant |
| **`weaklyUniversal_densL2`** | `Core.WeaklyUniversal P Π` on `L²(λ)`, `P` the density action: the main text's reading |
| **`weaklyUniversal_family`** | on the rows `s = 1`, `0 < c < 1` of the family the invariant probability exists, and the frozen family there is weakly `L²(λ)`-universal in both readings |

## Hypothesis checklist

| hypothesis | here |
|---|---|
| the loop closure | `cap = none` |
| an invariant probability | `L : Stat S none`; it exists on the rows `s = 1`, `c < 1` (`main_phase`) |
| the operator of the universality statement | `pstarL2`, the action of `P⋆` on `L²(λ)`, and `piL2`, the mean projection |

## SCOPE (disclosed)

* **Both readings are stated.** The main text's weak universality is about the density action
  `P` of the star backward policy, the kernel read backward and the free density as its inflow;
  this chapter's operator is its adjoint `P⋆`. `weaklyUniversal_densL2` is the first,
  `weaklyUniversal_pstarL2` the second.
* **No `sorry`.**

Provenance: mathlib tag `v4.31.0`, pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

variable {S : Setting}

namespace Stat

variable (L : Stat S none)

/-- **A contraction fixing the constants, whose defect range is dense in `ker Π`, is weakly
`L²(λ)`-universal.** Approximate a mean-zero target by a defect, the function by a simple one,
and add the simple function's bound: the defect does not see the constant. -/
theorem weaklyUniversal_of_dense {Q : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu} (hQ : ‖Q‖ ≤ 1)
    (hQ1 : Q L.oneLp = L.oneLp)
    (hdense : (LinearMap.range (((1 : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu) - Q
      : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu) : Lp ℝ 2 L.mu →ₗ[ℝ] Lp ℝ 2 L.mu)).topologicalClosure
        = L.kerPi) :
    Core.WeaklyUniversal Q L.piL2 := by
  set T : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu := 1 - Q with hT
  have hTapp : ∀ F, T F = F - Q F := fun F => rfl
  have hTnorm : ∀ F, ‖T F‖ ≤ 2 * ‖F‖ := by
    intro F
    have hQF : ‖Q F‖ ≤ 1 * ‖F‖ := Q.le_of_opNorm_le hQ F
    rw [hTapp]
    calc ‖F - Q F‖ ≤ ‖F‖ + ‖Q F‖ := norm_sub_le _ _
      _ ≤ 2 * ‖F‖ := by linarith
  have hT1 : T L.oneLp = 0 := by rw [hTapp, hQ1, sub_self]
  intro θ hθ ε hε
  have hθk : θ ∈ L.kerPi := (L.piL2_eq_zero_iff).mp hθ
  have hnθ : -θ ∈ (LinearMap.range (T : Lp ℝ 2 L.mu →ₗ[ℝ] Lp ℝ 2 L.mu)).topologicalClosure := by
    rw [hdense]
    exact L.kerPi.neg_mem hθk
  have hcl : -θ ∈ closure ((LinearMap.range (T : Lp ℝ 2 L.mu →ₗ[ℝ] Lp ℝ 2 L.mu) :
      Submodule ℝ (Lp ℝ 2 L.mu)) : Set (Lp ℝ 2 L.mu)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hnθ
  obtain ⟨G, hGmem, hG⟩ := Metric.mem_closure_iff.mp hcl (ε / 8) (by positivity)
  obtain ⟨F, hFG⟩ := LinearMap.mem_range.mp hGmem
  have hFG' : T F = G := hFG
  have hdense2 :=
    MeasureTheory.Lp.simpleFunc.dense (E := ℝ) (μ := L.mu) (p := 2) (by norm_num)
  obtain ⟨F', hF'mem, hF'⟩ := Metric.mem_closure_iff.mp (hdense2 F) (ε / 16) (by positivity)
  let g : Lp.simpleFunc ℝ 2 L.mu := ⟨F', hF'mem⟩
  obtain ⟨C, hC⟩ := (Lp.simpleFunc.toSimpleFunc g).exists_forall_norm_le
  refine ⟨F' + C • L.oneLp, ?_, ?_⟩
  · rw [← Lp.coeFn_nonneg]
    have h1 : (Lp.simpleFunc.toSimpleFunc g : St → ℝ) =ᵐ[L.mu] F' :=
      Lp.simpleFunc.toSimpleFunc_eq_toFun g
    filter_upwards [h1, Lp.coeFn_add F' (C • L.oneLp), Lp.coeFn_smul C L.oneLp, L.coeFn_oneLp]
      with x h1x hadd hsmul hone
    simp only [Pi.zero_apply, hadd, Pi.add_apply, hsmul, Pi.smul_apply, hone, smul_eq_mul,
      mul_one]
    have hx := hC x
    rw [h1x, Real.norm_eq_abs] at hx
    linarith [neg_abs_le (F' x)]
  · have hdef : T (F' + C • L.oneLp) = T F' := by
      rw [map_add, map_smul, hT1, smul_zero, add_zero]
    have hD : Core.defect Q θ (F' + C • L.oneLp) = -(T F' + θ) := by
      show Q (F' + C • L.oneLp) - (F' + C • L.oneLp) - θ = -(T F' + θ)
      rw [← hdef, hTapp]
      abel
    have hθG : ‖T F + θ‖ < ε / 8 := by
      rw [hFG', ← sub_neg_eq_add, ← dist_eq_norm, dist_comm]
      exact hG
    have hFF : ‖F' - F‖ < ε / 16 := by
      rw [← dist_eq_norm, dist_comm]
      exact hF'
    have hsmall : ‖T F' + θ‖ < ε / 4 := by
      have hsplit : T F' + θ = (T F + θ) + T (F' - F) := by
        rw [map_sub]
        abel
      have h2 := hTnorm (F' - F)
      calc ‖T F' + θ‖ ≤ ‖T F + θ‖ + ‖T (F' - F)‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ < ε / 8 + 2 * (ε / 16) := by linarith
        _ = ε / 4 := by ring
    have hres := Core.residuals_le_two_norm_defect Q θ (F' + C • L.oneLp)
    rw [hD, norm_neg] at hres
    linarith

/-- **Weak `L²(λ)`-universality for `P⋆`**, the function action of this chapter. -/
theorem weaklyUniversal_pstarL2 :
    Core.WeaklyUniversal (L.pstarL2 (rowOnChain_none S)) L.piL2 :=
  L.weaklyUniversal_of_dense (L.norm_pstarL2_le (rowOnChain_none S))
    (L.pstarLp_oneLp (rowOnChain_none S)) L.topologicalClosure_defectRange

/-- `P1 = 1`: the density action fixes the constants, `λ` being invariant. -/
theorem densL2_oneLp : L.densL2 (rowOnChain_none S) L.oneLp = L.oneLp := by
  have h : L.densL2 (rowOnChain_none S) (L.piL2 L.oneLp) = L.piL2 L.oneLp :=
    congrArg (fun T => T L.oneLp) (L.densL2_mul_piL2 (rowOnChain_none S))
  rwa [piL2_apply, L.inner_oneLp_self, one_smul] at h

/-- **The range of `Id − P` is dense in `ker Π`**, `P` the density action: a vector orthogonal to
it is a fixed point of the adjoint `P⋆`, hence a constant. -/
theorem topologicalClosure_densDefectRange :
    (LinearMap.range (((1 : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu) - L.densL2 (rowOnChain_none S)
      : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu) : Lp ℝ 2 L.mu →ₗ[ℝ] Lp ℝ 2 L.mu)).topologicalClosure
        = L.kerPi := by
  set R := LinearMap.range (((1 : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu) - L.densL2 (rowOnChain_none S)
      : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu) : Lp ℝ 2 L.mu →ₗ[ℝ] Lp ℝ 2 L.mu) with hR
  have horth : Rᗮ = ℝ ∙ L.oneLp := by
    refine le_antisymm (fun g hg => ?_) ?_
    · have hall : ∀ y : Lp ℝ 2 L.mu, ⟪y, g - L.pstarL2 (rowOnChain_none S) g⟫_ℝ = 0 := by
        intro y
        have h0 : ⟪y - L.densL2 (rowOnChain_none S) y, g⟫_ℝ = 0 :=
          (Submodule.mem_orthogonal _ _).mp hg _ ⟨y, rfl⟩
        rw [inner_sub_left, L.inner_densL2_left] at h0
        rw [inner_sub_right]
        exact h0
      have hfix : L.pstarLp g = g := by
        have h := hall (g - L.pstarL2 (rowOnChain_none S) g)
        rw [real_inner_self_eq_norm_sq] at h
        have h' : g - L.pstarL2 (rowOnChain_none S) g = 0 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
          exact norm_eq_zero.mp this
        rw [sub_eq_zero] at h'
        rw [← L.pstarL2_apply (rowOnChain_none S)]
        exact h'.symm
      rw [L.eq_smul_oneLp_of_fixed hfix]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal]
      rintro _ ⟨y, rfl⟩
      show ⟪y - L.densL2 (rowOnChain_none S) y, L.oneLp⟫_ℝ = 0
      rw [inner_sub_left, L.inner_densL2_left, pstarL2_apply, L.pstarLp_oneLp (rowOnChain_none S),
        sub_self]
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth, kerPi]

/-- **Weak `L²(λ)`-universality for `P`**, the density action: the main text's reading, the kernel
taken as the star backward policy and the free density as its inflow. -/
theorem weaklyUniversal_densL2 :
    Core.WeaklyUniversal (L.densL2 (rowOnChain_none S)) L.piL2 :=
  L.weaklyUniversal_of_dense (L.norm_densL2_le (rowOnChain_none S)) L.densL2_oneLp
    L.topologicalClosure_densDefectRange

end Stat

/-- **On the positive recurrent rows the frozen family is weakly `L²(λ)`-universal.** For
`ε = ε_{c,1}` with `0 < c < 1` the loop closure has an invariant probability, and for it
the operator statement holds. -/
theorem weaklyUniversal_family {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hS : ∀ j, S.eps j = epsCS c 1 j) :
    ∃ L : Stat S none, Core.WeaklyUniversal (L.densL2 (rowOnChain_none S)) L.piL2
      ∧ Core.WeaklyUniversal (L.pstarL2 (rowOnChain_none S)) L.piL2 := by
  obtain ⟨-, hpos, -, -⟩ := main_phase hc hS
  obtain ⟨L⟩ := hpos rfl hc1
  exact ⟨L, L.weaklyUniversal_densL2, L.weaklyUniversal_pstarL2⟩

end GFNBounds.Doubling
