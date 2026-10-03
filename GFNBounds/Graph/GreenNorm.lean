import GFNBounds.Graph.SlowMode

/-!
# The best coercivity constant is the norm of the Green operator

On the loop closure of a finite path-connected marked graph whose backward policy is positive on
its edges and held fixed, let `P` be the density action on `L²(λ)`, `Π` the mean, and
`S = (I − P + Π)^{-1} − Π` the Green operator. Then `‖S‖` is the least coercivity constant: the
least `c` with `‖h − Πh‖ ≤ c‖Ah‖` for every `h`, `A = P − I`. With it, the exact curvature at a
constant weight reads `g''(1)w/‖S‖²`.

`L²(λ)` is read through the weighting isometry of `Balance.WeightedL2`, so that `S` is a
continuous linear map of `EuclideanSpace ℝ V` and `‖S‖` its operator norm. `I − P + Π` is
injective by coercivity, hence invertible in finite dimension. The resolvent identities
`(I − P)S = S(I − P) = I − Π` and `ΠS = 0` follow from `ΠP = PΠ = Π = Π²`, and the two
inequalities follow from them: `h − Πh = S(I − P)h` gives `‖S‖` as a coercivity constant, and
`Sv` has mean zero with `(I − P)Sv = v − Πv`, so any coercivity constant bounds `S`.

## What is proved

| | |
|---|---|
| `isUnit_of_injective_euclid` | an injective endomorphism of `EuclideanSpace ℝ V` is a unit |
| `resolventOp`, `greenOp` | `I − P + Π` and `S = (I − P + Π)^{-1} − Π`, on `EuclideanSpace ℝ V` |
| `resolvent_injective` | `I − P + Π` is injective |
| `greenOp_resolvent` | `(I − P)S = I − Π`, `S(I − P) = I − Π`, `ΠS = 0` |
| **`isLeast_greenOp_norm`** | `‖S‖` is the least coercivity constant |
| **`curvature_exact_green`** | at a constant weight the best curvature constant is `g''(1)w/‖S‖²` |

## Hypothesis checklist

| hypothesis | here |
|---|---|
| a finite path-connected marked graph, a policy positive on its edges, `λ` its invariant probability | `hpc`, `hpos`, `hl` |
| `P`, `Π` on `L²(λ)` | `Balance.densOp lam B.phat`, `Balance.meanOp lam`, conjugated by the weighting |
| the norm of `S` | the operator norm on `EuclideanSpace ℝ V`, which the weighting identifies with that of `L²(λ)` |

## SCOPE (disclosed)

* **No `sorry`.**

Provenance: mathlib tag `v4.31.0`, pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : MarkedGraph V}

namespace BackwardPolicy

variable {B : BackwardPolicy G}

omit [DecidableEq V] in
/-- **An injective endomorphism of `EuclideanSpace ℝ V` is a unit**, the space being
finite-dimensional. -/
theorem isUnit_of_injective_euclid {T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V}
    (hinj : Function.Injective T) : IsUnit T := by
  let e := LinearEquiv.ofInjectiveEndo (T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) hinj
  have hcoe : ∀ v, e v = T v := fun v =>
    congrFun (LinearEquiv.coe_ofInjectiveEndo (T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) hinj) v
  refine ⟨⟨T, LinearMap.toContinuousLinearMap
    (e.symm : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V), ?_, ?_⟩, rfl⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    show T (e.symm v) = v
    rw [← hcoe, e.apply_symm_apply]
  · refine ContinuousLinearMap.ext fun v => ?_
    show e.symm (T v) = v
    rw [← hcoe, e.symm_apply_apply]

/-- `I − P + Π` on `L²(λ)`, read through the weighting, `P` the density action of the loop
closure and `Π` the mean. -/
noncomputable def resolventOp (B : BackwardPolicy G) (lam : V → ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  1 - Balance.densOp lam B.phat + Balance.meanOp lam

/-- **The Green operator** of the loop closure on `L²(λ)`, read through the weighting:
`S = (I − P + Π)^{-1} − Π`. -/
noncomputable def greenOp (B : BackwardPolicy G) (lam : V → ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  Ring.inverse (B.resolventOp lam) - Balance.meanOp lam

/-- **`I − P + Π` is injective**: `Π` kills its image of `v` down to `Πv`, so `Πv = 0`, then
`Av = 0`, and coercivity leaves `v = 0`. -/
theorem resolvent_injective (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) :
    Function.Injective (B.resolventOp lam) := by
  have hK := Core.phat_isMarkov B
  have hlam : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have htot : ∑ x, lam x = 1 := hl.total
  obtain ⟨Bstar, -, hB⟩ := bestCoerc_exists hpc hpos hl
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨a, rfl⟩ := Balance.exists_wtL2 hlam v
  have hsplit : B.resolventOp lam (Balance.wtL2 lam a)
      = (1 - Balance.densOp lam B.phat) (Balance.wtL2 lam a)
        + Balance.meanOp lam (Balance.wtL2 lam a) := rfl
  have hPiP : Balance.meanOp lam (Balance.densOp lam B.phat (Balance.wtL2 lam a))
      = Balance.meanOp lam (Balance.wtL2 lam a) :=
    congrArg (fun F => F (Balance.wtL2 lam a)) (Balance.meanOp_mul_densOp hK hlam)
  have hPiv : Balance.meanOp lam (Balance.wtL2 lam a) = 0 := by
    have h1 := congrArg (Balance.meanOp lam) hv
    rw [map_zero, hsplit, map_add, Balance.meanOp_idem hlam htot] at h1
    have h2 : Balance.meanOp lam ((1 - Balance.densOp lam B.phat) (Balance.wtL2 lam a)) = 0 := by
      show Balance.meanOp lam (Balance.wtL2 lam a - Balance.densOp lam B.phat (Balance.wtL2 lam a))
        = 0
      rw [map_sub, hPiP, sub_self]
    rw [h2, zero_add] at h1
    exact h1
  have hm : meanL2 lam a = 0 := by
    rw [Balance.meanOp_wtL2 hlam, ← Balance.wtL2_zero lam] at hPiv
    exact congrFun (Balance.wtL2_injective hlam hPiv) G.src
  have hPv : (1 - Balance.densOp lam B.phat) (Balance.wtL2 lam a) = 0 := by
    rw [hsplit, hPiv, add_zero] at hv
    exact hv
  rw [Balance.one_sub_densOp_wtL2 hlam, neg_eq_zero] at hPv
  have hA : nrmL2 lam (Balance.Aop B.phat lam a) = 0 := by
    rw [← Balance.norm_wtL2 hnn, hPv, norm_zero]
  have hp := mem_coercSet.mp hB.1 a
  rw [hA, mul_zero, perpL2_of_mean_zero hm] at hp
  have h0 : nrmL2 lam a = 0 := le_antisymm hp (nrmL2_nonneg _ _)
  rw [← Balance.norm_wtL2 hnn, norm_eq_zero] at h0
  exact h0

/-- **The resolvent identities**: `(I − P)S = I − Π`, `S(I − P) = I − Π` and `ΠS = 0`. -/
theorem greenOp_resolvent (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) :
    (1 - Balance.densOp lam B.phat) * B.greenOp lam = 1 - Balance.meanOp lam
      ∧ B.greenOp lam * (1 - Balance.densOp lam B.phat) = 1 - Balance.meanOp lam
      ∧ Balance.meanOp lam * B.greenOp lam = 0 := by
  have hK := Core.phat_isMarkov B
  have hinv := Core.isInvariant_of_isInvProb B hl
  have hlam : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have htot : ∑ x, lam x = 1 := hl.total
  have hT := isUnit_of_injective_euclid (resolvent_injective hpc hpos hl)
  have hPP : Balance.meanOp lam * Balance.meanOp lam = Balance.meanOp lam :=
    ContinuousLinearMap.ext fun u => Balance.meanOp_idem hlam htot u
  have hPiP := Balance.meanOp_mul_densOp hK hlam
  have hPPi := Balance.densOp_mul_meanOp hinv hlam
  obtain ⟨T, hTdef⟩ : ∃ T, B.resolventOp lam = T := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U, Ring.inverse T = U := ⟨_, rfl⟩
  have hS : B.greenOp lam = U - Balance.meanOp lam := by
    rw [greenOp, hTdef, hUdef]
  rw [hTdef] at hT
  have hTU : T * U = 1 := by
    rw [← hUdef]
    exact Ring.mul_inverse_cancel T hT
  have hUT : U * T = 1 := by
    rw [← hUdef]
    exact Ring.inverse_mul_cancel T hT
  have h1P : 1 - Balance.densOp lam B.phat = T - Balance.meanOp lam := by
    rw [← hTdef, resolventOp]
    abel
  have hTPi : T * Balance.meanOp lam = Balance.meanOp lam := by
    rw [← hTdef, resolventOp, add_mul, sub_mul, one_mul, hPPi, hPP, sub_self, zero_add]
  have hPiT : Balance.meanOp lam * T = Balance.meanOp lam := by
    rw [← hTdef, resolventOp, mul_add, mul_sub, mul_one, hPiP, hPP, sub_self, zero_add]
  have hUPi : U * Balance.meanOp lam = Balance.meanOp lam :=
    calc U * Balance.meanOp lam = U * (T * Balance.meanOp lam) := by rw [hTPi]
      _ = U * T * Balance.meanOp lam := (mul_assoc _ _ _).symm
      _ = Balance.meanOp lam := by rw [hUT, one_mul]
  have hPiU : Balance.meanOp lam * U = Balance.meanOp lam :=
    calc Balance.meanOp lam * U = Balance.meanOp lam * T * U := by rw [hPiT]
      _ = Balance.meanOp lam * (T * U) := mul_assoc _ _ _
      _ = Balance.meanOp lam := by rw [hTU, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hS, h1P, sub_mul, mul_sub, mul_sub, hTU, hTPi, hPiU, hPP, sub_self, sub_zero]
  · rw [hS, h1P, sub_mul, mul_sub, mul_sub, hUT, hUPi, hPiT, hPP, sub_self, sub_zero]
  · rw [hS, mul_sub, hPiU, hPP, sub_self]

/-- **The best coercivity constant is the norm of the Green operator.** On the loop closure of a
finite path-connected marked graph with a policy positive on its edges, `‖S‖` is the least `c`
with `‖h − Πh‖ ≤ c‖Ah‖` for every `h`. -/
theorem isLeast_greenOp_norm (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) : IsLeast (B.coercSet lam) ‖B.greenOp lam‖ := by
  obtain ⟨h1, h2, h3⟩ := greenOp_resolvent hpc hpos hl
  have hlam : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have htot : ∑ x, lam x = 1 := hl.total
  refine ⟨mem_coercSet.mpr fun f => ?_, fun C hC => ?_⟩
  · have hf : Balance.wtL2 lam (Balance.perpL2 lam f)
        = B.greenOp lam (-Balance.wtL2 lam (Balance.Aop B.phat lam f)) := by
      rw [← Balance.one_sub_densOp_wtL2 hlam, ← Balance.sub_meanOp_wtL2 hlam]
      have h2x : B.greenOp lam ((1 - Balance.densOp lam B.phat) (Balance.wtL2 lam f))
          = Balance.wtL2 lam f - Balance.meanOp lam (Balance.wtL2 lam f) :=
        congrArg (fun F => F (Balance.wtL2 lam f)) h2
      exact h2x.symm
    rw [← Balance.norm_wtL2 hnn (Balance.perpL2 lam f), hf,
      ← Balance.norm_wtL2 hnn (Balance.Aop B.phat lam f),
      ← norm_neg (Balance.wtL2 lam (Balance.Aop B.phat lam f))]
    exact (B.greenOp lam).le_opNorm _
  · have hC' := mem_coercSet.mp hC
    obtain ⟨g0, hg0⟩ := exists_perp_pos hpc hpos hl
    have hC0 : 0 ≤ C := by
      by_contra hneg
      have hle := hC' g0
      have hA0 := nrmL2_nonneg lam (Balance.Aop B.phat lam g0)
      nlinarith
    refine (B.greenOp lam).opNorm_le_bound hC0 fun v => ?_
    obtain ⟨a, ha⟩ := Balance.exists_wtL2 hlam (B.greenOp lam v)
    have hPia : Balance.meanOp lam (Balance.wtL2 lam a) = 0 := by
      rw [ha]
      exact congrArg (fun F => F v) h3
    have hm : meanL2 lam a = 0 := by
      rw [Balance.meanOp_wtL2 hlam, ← Balance.wtL2_zero lam] at hPia
      exact congrFun (Balance.wtL2_injective hlam hPia) G.src
    have h1v : (1 - Balance.densOp lam B.phat) (Balance.wtL2 lam a)
        = v - Balance.meanOp lam v := by
      rw [ha]
      exact congrArg (fun F => F v) h1
    rw [Balance.one_sub_densOp_wtL2 hlam] at h1v
    obtain ⟨b, rfl⟩ := Balance.exists_wtL2 hlam v
    rw [Balance.sub_meanOp_wtL2 hlam] at h1v
    have hnA : nrmL2 lam (Balance.Aop B.phat lam a) = nrmL2 lam (Balance.perpL2 lam b) := by
      rw [← Balance.norm_wtL2 hnn (Balance.Aop B.phat lam a),
        ← Balance.norm_wtL2 hnn (Balance.perpL2 lam b), ← h1v, norm_neg]
    calc ‖B.greenOp lam (Balance.wtL2 lam b)‖ = nrmL2 lam a := by
          rw [← ha, Balance.norm_wtL2 hnn]
      _ = nrmL2 lam (Balance.perpL2 lam a) := by rw [perpL2_of_mean_zero hm]
      _ ≤ C * nrmL2 lam (Balance.Aop B.phat lam a) := hC' a
      _ = C * nrmL2 lam (Balance.perpL2 lam b) := by rw [hnA]
      _ ≤ C * nrmL2 lam b :=
          mul_le_mul_of_nonneg_left (Balance.nrmL2_perpL2_le hnn htot b) hC0
      _ = C * ‖Balance.wtL2 lam b‖ := by rw [Balance.norm_wtL2 hnn]

/-- **The exact curvature at a constant weight, at the norm of the Green operator.** With
`w ≡ w₀ ≥ 0` and `g''(1) ≥ 0`, the best constant `c` with `c‖h − Πh‖² ≤ ⟨h, Hh⟩` for every `h` is
`g''(1)w₀/‖S‖²`. -/
theorem curvature_exact_green (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) {g2 w0 : ℝ} (hg2 : 0 ≤ g2) (hw0 : 0 ≤ w0) :
    IsGreatest (B.curvSet lam (fun _ => w0) g2) (g2 * w0 / ‖B.greenOp lam‖ ^ 2) := by
  obtain ⟨Bstar, hBpos, hB⟩ := bestCoerc_exists hpc hpos hl
  rw [← hB.unique (isLeast_greenOp_norm hpc hpos hl)]
  exact curvature_exact_frozen hl hBpos hB hg2 hw0

end BackwardPolicy

end GFNBounds.Graph
