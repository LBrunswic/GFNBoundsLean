import GFNBounds.Graph.BestConstant
import GFNBounds.Balance.WeightedL2
import GFNBounds.Balance.LocalEnergy

/-!
# The slow mode: the best curvature constant is the slowest rate of linearized training

On the loop closure of a finite path-connected marked graph whose backward policy is positive on
its edges and held fixed, linearized training is the flow `ḣ = −Hh` of `H = g''(1)A†M_wA` on
`L²(λ)`. Its slowest rate is the best curvature constant `c⋆`, the greatest `c` with
`c‖h − Πh‖² ≤ ⟨h, Hh⟩` for every `h`:

* every linearized trajectory contracts at least at `c⋆`, `‖h_t − Πh_t‖ ≤ e^{−c⋆t}‖h_0 − Πh_0‖`;
* some direction contracts at exactly `c⋆`: a slow mode `h₀`, of mean zero and norm one, with
  `Hh₀ = c⋆h₀`, along which the trajectory is `e^{−c⋆t}h₀`;
* `c⋆` lies between `g''(1)w_min/B̂²` and `g''(1)w_max/B̂²`, `B̂` the least coercivity constant.

The slow mode minimizes `⟨h, Hh⟩` on the unit sphere of the mean-zero functions, which is compact
because the state space is finite. The minimizer is an eigenvector by the first-order condition:
along `h₀ + te`, `e = Hh₀ − c⋆h₀`, the quadratic `2t‖e‖² + O(t²)` stays non-negative, so `e = 0`.
No spectral theorem is invoked. The lower bound on every trajectory is Grönwall's inequality
applied to `‖h_t − Πh_t‖²`.

## What is proved

| | |
|---|---|
| `curvSet`, `mem_curvSet` | the curvature constants at the weight `w` |
| `quad_perpL2`, `quad_nonneg` | `⟨h, Hh⟩ = ⟨h^⊥, Hh^⊥⟩ ≥ 0` |
| `eq_zero_of_quad_nonneg` | a quadratic `2bt + at²`, non-negative for every `t`, has `b = 0` |
| **`exists_slowMode`** | the best curvature constant exists, and is the eigenvalue of a mean-zero eigenvector of norm one |
| **`linear_decay`** | every linearized trajectory contracts at least at any curvature constant |
| `slowMode_trajectory` | along the slow mode the linearized trajectory is `e^{−c⋆t}h₀` |
| **`slowest_rate_frozen`** | all of it on the loop closure, with `c⋆` between `g''(1)w_min/B̂²` and `g''(1)w_max/B̂²` |

## Hypothesis checklist

| hypothesis | here |
|---|---|
| a finite path-connected marked graph, a policy positive on its edges, `λ` its invariant probability | `hpc`, `hpos`, `hl` |
| the weight | `wmin ≤ w ≤ wsup`, `0 ≤ wmin`; `g''(1) ≥ 0` |
| linearized training | a curve `u` with `∂_t u_t(x) = −(Hu_t)(x)` at every `t ≥ 0`, hypothesised of a given curve |
| `B̂` | the least coercivity constant, `bestCoerc_exists` |

## SCOPE (disclosed)

* **Linearized training only.** The rate is that of `ḣ = −Hh`; the full dynamics inherits half of
  it near balance (`local_convergence_frozen`), and that half is not shown to be sharp.
* **The Green operator is not formed.** `B̂` is the least coercivity constant, not `‖S‖`.
* **No `sorry`.**

Provenance: mathlib tag `v4.31.0`, pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : MarkedGraph V}

namespace BackwardPolicy

variable {B : BackwardPolicy G}

/-- **The curvature constants** at the weight `w`: the `c` with `c‖h − Πh‖² ≤ ⟨h, Hh⟩` for every
`h`, `H = g''(1)A†M_wA`. -/
def curvSet (B : BackwardPolicy G) (lam w : V → ℝ) (g2 : ℝ) : Set ℝ :=
  {c | ∀ h : V → ℝ, c * nrmL2 lam (Balance.perpL2 lam h) ^ 2
    ≤ ipL2 lam h (Balance.linHess B.phat lam w g2 h)}

theorem mem_curvSet {lam w : V → ℝ} {g2 c : ℝ} :
    c ∈ B.curvSet lam w g2
      ↔ ∀ h : V → ℝ, c * nrmL2 lam (Balance.perpL2 lam h) ^ 2
        ≤ ipL2 lam h (Balance.linHess B.phat lam w g2 h) :=
  Iff.rfl

/-- The unit sphere of the mean-zero functions of `L²(λ)`. -/
def unitPerp (lam : V → ℝ) : Set (V → ℝ) :=
  {h | meanL2 lam h = 0} ∩ {h | ipL2 lam h h = 1}

omit [DecidableEq V] in
theorem mem_unitPerp {lam h : V → ℝ} :
    h ∈ unitPerp lam ↔ meanL2 lam h = 0 ∧ ipL2 lam h h = 1 :=
  Iff.rfl

omit [DecidableEq V] in
/-- `⟨a + tb, c + td⟩ = ⟨a, c⟩ + t(⟨a, d⟩ + ⟨b, c⟩) + t²⟨b, d⟩`. -/
theorem ipL2_add_smul (lam a b c d : V → ℝ) (t : ℝ) :
    ipL2 lam (fun x => a x + t * b x) (fun x => c x + t * d x)
      = ipL2 lam a c + t * (ipL2 lam a d + ipL2 lam b c) + t ^ 2 * ipL2 lam b d := by
  simp only [ipL2, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

omit [DecidableEq V] in
/-- `⟨sa, sa⟩ = s²⟨a, a⟩`. -/
theorem ipL2_smul_smul (lam a : V → ℝ) (s : ℝ) :
    ipL2 lam (fun x => s * a x) (fun x => s * a x) = s ^ 2 * ipL2 lam a a := by
  simp only [ipL2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

omit [DecidableEq V] in
/-- `⟨sh, H(sh)⟩ = s²⟨h, Hh⟩`. -/
theorem quad_smul (K : V → V → ℝ) (lam w : V → ℝ) (g2 s : ℝ) (h : V → ℝ) :
    ipL2 lam (fun x => s * h x) (Balance.linHess K lam w g2 (fun x => s * h x))
      = s ^ 2 * ipL2 lam h (Balance.linHess K lam w g2 h) := by
  rw [Balance.linHess_smul]
  simp only [ipL2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

omit [DecidableEq V] in
/-- `⟨h^⊥, f⟩ = ⟨h, f⟩` when `Πf = 0`. -/
theorem ipL2_perpL2_of_mean_zero {lam h f : V → ℝ} (hf : meanL2 lam f = 0) :
    ipL2 lam (Balance.perpL2 lam h) f = ipL2 lam h f := by
  have hexp : ∀ x, lam x * (Balance.perpL2 lam h x * f x)
      = lam x * (h x * f x) - meanL2 lam h * (lam x * f x) := fun x => by
    rw [Balance.perpL2_apply]
    ring
  have hf' : ∑ x, lam x * f x = 0 := hf
  simp only [ipL2]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hf', mul_zero, sub_zero]

omit [DecidableEq V] in
/-- A mean-zero function is its own centred part. -/
theorem perpL2_of_mean_zero {lam h : V → ℝ} (hm : meanL2 lam h = 0) :
    Balance.perpL2 lam h = h := by
  funext x
  rw [Balance.perpL2_apply, hm, sub_zero]

omit [DecidableEq V] in
/-- **`⟨h, Hh⟩ = ⟨h^⊥, Hh^⊥⟩`**: `H` kills the constants, and its image has mean zero. -/
theorem quad_perpL2 {K : V → V → ℝ} {lam w : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (g2 : ℝ) (h : V → ℝ) :
    ipL2 lam (Balance.perpL2 lam h) (Balance.linHess K lam w g2 (Balance.perpL2 lam h))
      = ipL2 lam h (Balance.linHess K lam w g2 h) := by
  rw [Balance.linHess_perpL2 hinv hlam g2 h]
  exact ipL2_perpL2_of_mean_zero
    (Balance.meanL2_linHess (Balance.invariant_of_isInvariant hinv) w g2 h)

omit [DecidableEq V] in
/-- **`⟨h, Hh⟩ ≥ 0`** for a non-negative weight. -/
theorem quad_nonneg {K : V → V → ℝ} {lam w : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hKnn : ∀ x y, 0 ≤ K x y) (hw0 : ∀ x, 0 ≤ w x) {g2 : ℝ} (hg2 : 0 ≤ g2) (h : V → ℝ) :
    0 ≤ ipL2 lam h (Balance.linHess K lam w g2 h) := by
  have h1 := Balance.linHess_coercive hinv hKnn (wmin := 0) hw0 hg2 h
  rwa [mul_zero, zero_mul] at h1

/-- **A quadratic that never goes negative has no linear term**: `2bt + at² ≥ 0` for every `t`
and `b ≥ 0` force `b = 0`, by evaluating at `t = −b/(|a| + 1)`. -/
theorem eq_zero_of_quad_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : ∀ t : ℝ, 0 ≤ 2 * b * t + a * t ^ 2) :
    b = 0 := by
  by_contra hne
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hne)
  have hden : 0 < |a| + 1 := by positivity
  have hs0 : 0 < b / (|a| + 1) := div_pos hbpos hden
  have hsa : b / (|a| + 1) * a ≤ b / (|a| + 1) * |a| :=
    mul_le_mul_of_nonneg_left (le_abs_self a) hs0.le
  have hsabs : b / (|a| + 1) * |a| < b := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [abs_nonneg a]
  have hlt := mul_lt_mul_of_pos_left (hsa.trans_lt hsabs) hs0
  have hval := h (-(b / (|a| + 1)))
  nlinarith [mul_pos hbpos hs0]

/-- **The slow mode exists.** The best curvature constant `c⋆` exists, and it is the eigenvalue
of an eigenvector `h₀` of `H` of mean zero and norm one: `Hh₀ = c⋆h₀`. The eigenvector minimizes
`⟨h, Hh⟩` on the compact unit sphere of the mean-zero functions; the first-order condition makes
it an eigenvector. -/
theorem exists_slowMode (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam w : V → ℝ}
    (hl : B.IsInvProb lam) (hw0 : ∀ x, 0 ≤ w x) {g2 : ℝ} (hg2 : 0 ≤ g2) :
    ∃ c : ℝ, IsGreatest (B.curvSet lam w g2) c
      ∧ ∃ h0 : V → ℝ, meanL2 lam h0 = 0 ∧ nrmL2 lam h0 = 1
        ∧ ∀ x, Balance.linHess B.phat lam w g2 h0 x = c * h0 x := by
  have hK := Core.phat_isMarkov B
  have hinv := Core.isInvariant_of_isInvProb B hl
  have hlam : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have htot : ∑ x, lam x = 1 := hl.total
  -- the quadratic form is continuous
  let L : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
    { toFun := Balance.linHess B.phat lam w g2
      map_add' := fun a b => Balance.linHess_add B.phat lam w g2 a b
      map_smul' := fun s a => Balance.linHess_smul B.phat lam w g2 s a }
  have hcL : Continuous fun h : V → ℝ => Balance.linHess B.phat lam w g2 h :=
    L.continuous_of_finiteDimensional
  have hcq : Continuous fun h : V → ℝ => ipL2 lam h (Balance.linHess B.phat lam w g2 h) := by
    show Continuous fun h : V → ℝ => ∑ x, lam x * (h x * Balance.linHess B.phat lam w g2 h x)
    exact continuous_finsetSum _ fun x _ =>
      continuous_const.mul ((continuous_apply x).mul ((continuous_apply x).comp hcL))
  -- the sphere is compact and nonempty
  have hcm : Continuous fun h : V → ℝ => meanL2 lam h := by
    show Continuous fun h : V → ℝ => ∑ x, lam x * h x
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_apply x)
  have hci : Continuous fun h : V → ℝ => ipL2 lam h h := by
    show Continuous fun h : V → ℝ => ∑ x, lam x * (h x * h x)
    exact continuous_finsetSum _ fun x _ =>
      continuous_const.mul ((continuous_apply x).mul (continuous_apply x))
  have hSc : IsClosed (unitPerp lam) :=
    (isClosed_eq hcm continuous_const).inter (isClosed_eq hci continuous_const)
  have hR : 0 ≤ ∑ y, (1 + 1 / lam y) :=
    Finset.sum_nonneg fun y _ => add_nonneg zero_le_one (div_nonneg zero_le_one (hlam y).le)
  have hSb : Bornology.IsBounded (unitPerp lam) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨∑ y, (1 + 1 / lam y), fun h hh => ?_⟩
    have hn : ∑ y, lam y * (h y * h y) = 1 := (mem_unitPerp.mp hh).2
    refine (pi_norm_le_iff_of_nonneg hR).mpr fun x => ?_
    rw [Real.norm_eq_abs]
    have hx : lam x * (h x * h x) ≤ 1 :=
      calc lam x * (h x * h x) ≤ ∑ y, lam y * (h y * h y) :=
            Finset.single_le_sum (f := fun y => lam y * (h y * h y))
              (fun y _ => mul_nonneg (hnn y) (mul_self_nonneg (h y))) (Finset.mem_univ x)
        _ = 1 := hn
    have hx2 : h x * h x ≤ 1 / lam x := by
      rw [le_div_iff₀ (hlam x)]
      linarith [hx]
    have habs : |h x| ≤ 1 + h x * h x := by
      nlinarith [abs_mul_abs_self (h x), abs_nonneg (h x), sq_nonneg (|h x| - 1)]
    have hsingle : 1 + 1 / lam x ≤ ∑ y, (1 + 1 / lam y) :=
      Finset.single_le_sum (f := fun y => 1 + 1 / lam y)
        (fun y _ => add_nonneg zero_le_one (div_nonneg zero_le_one (hlam y).le))
        (Finset.mem_univ x)
    linarith
  have hScpt : IsCompact (unitPerp lam) := Metric.isCompact_of_isClosed_isBounded hSc hSb
  have hnorm : ∀ h : V → ℝ, 0 < nrmL2 lam (Balance.perpL2 lam h) →
      (fun x => (nrmL2 lam (Balance.perpL2 lam h))⁻¹ * Balance.perpL2 lam h x) ∈ unitPerp lam := by
    intro h hr
    refine mem_unitPerp.mpr ⟨?_, ?_⟩
    · rw [Balance.meanL2_const_mul, Balance.meanL2_perpL2 htot, mul_zero]
    · rw [ipL2_smul_smul, ← sq_nrmL2 hnn, inv_pow, inv_mul_cancel₀ (pow_pos hr 2).ne']
  obtain ⟨h1, hh1⟩ := exists_perp_pos hpc hpos hl
  have hSne : (unitPerp lam).Nonempty := ⟨_, hnorm h1 hh1⟩
  -- the minimizer
  obtain ⟨h0, hh0, hmin⟩ := hScpt.exists_isMinOn hSne hcq.continuousOn
  obtain ⟨hm0, hn0⟩ := mem_unitPerp.mp hh0
  have hp0 : Balance.perpL2 lam h0 = h0 := perpL2_of_mean_zero hm0
  have hsq0 : nrmL2 lam h0 ^ 2 = 1 := by rw [sq_nrmL2 hnn, hn0]
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, ipL2 lam h0 (Balance.linHess B.phat lam w g2 h0) = c := ⟨_, rfl⟩
  -- its value is a curvature constant
  have hcurv : ∀ h : V → ℝ, c * nrmL2 lam (Balance.perpL2 lam h) ^ 2
      ≤ ipL2 lam h (Balance.linHess B.phat lam w g2 h) := by
    intro h
    rcases (nrmL2_nonneg lam (Balance.perpL2 lam h)).lt_or_eq with hr | hr
    · have hle : ipL2 lam h0 (Balance.linHess B.phat lam w g2 h0)
          ≤ ipL2 lam (fun x => (nrmL2 lam (Balance.perpL2 lam h))⁻¹ * Balance.perpL2 lam h x)
            (Balance.linHess B.phat lam w g2
              (fun x => (nrmL2 lam (Balance.perpL2 lam h))⁻¹ * Balance.perpL2 lam h x)) :=
        isMinOn_iff.mp hmin _ (hnorm h hr)
      rw [hcdef, quad_smul B.phat lam w g2 (nrmL2 lam (Balance.perpL2 lam h))⁻¹
        (Balance.perpL2 lam h), quad_perpL2 hinv hlam g2 h] at hle
      calc c * nrmL2 lam (Balance.perpL2 lam h) ^ 2
          ≤ (nrmL2 lam (Balance.perpL2 lam h))⁻¹ ^ 2
              * ipL2 lam h (Balance.linHess B.phat lam w g2 h)
              * nrmL2 lam (Balance.perpL2 lam h) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = ipL2 lam h (Balance.linHess B.phat lam w g2 h) := by
            rw [inv_pow, mul_right_comm, inv_mul_cancel₀ (pow_pos hr 2).ne', one_mul]
    · rw [← hr, zero_pow two_ne_zero, mul_zero]
      exact quad_nonneg hinv hK.nonneg hw0 hg2 h
  -- the first-order condition: the minimizer is an eigenvector
  obtain ⟨e, hex⟩ : ∃ e : V → ℝ, ∀ x, e x = Balance.linHess B.phat lam w g2 h0 x - c * h0 x :=
    ⟨_, fun x => rfl⟩
  have hme : meanL2 lam e = 0 := by
    have h1 : meanL2 lam e = meanL2 lam (Balance.linHess B.phat lam w g2 h0)
        - c * meanL2 lam h0 := by
      simp only [meanL2, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by rw [hex x]; ring
    rw [h1, Balance.meanL2_linHess (Balance.invariant_of_isInvariant hinv), hm0, mul_zero,
      sub_zero]
  have hee : ipL2 lam e (Balance.linHess B.phat lam w g2 h0)
      = ipL2 lam e e + c * ipL2 lam e h0 := by
    simp only [ipL2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hex x]
    ring
  have hsym : ipL2 lam h0 (Balance.linHess B.phat lam w g2 e)
      = ipL2 lam e (Balance.linHess B.phat lam w g2 h0) := by
    rw [Balance.linHess_symm hinv hK.nonneg w g2 h0 e, Balance.ipL2_comm]
  have hHt : ∀ t : ℝ, Balance.linHess B.phat lam w g2 (fun x => h0 x + t * e x)
      = fun x => Balance.linHess B.phat lam w g2 h0 x + t * Balance.linHess B.phat lam w g2 e x := by
    intro t
    rw [Balance.linHess_add, Balance.linHess_smul]
  have hquad : ∀ t : ℝ, 0 ≤ 2 * ipL2 lam e e * t
      + (ipL2 lam e (Balance.linHess B.phat lam w g2 e) - c * ipL2 lam e e) * t ^ 2 := by
    intro t
    have hmt : meanL2 lam (fun x => h0 x + t * e x) = 0 := by
      rw [Balance.meanL2_add, Balance.meanL2_const_mul, hm0, hme, mul_zero, add_zero]
    have hc := hcurv (fun x => h0 x + t * e x)
    rw [perpL2_of_mean_zero hmt, sq_nrmL2 hnn, hHt t, ipL2_add_smul, ipL2_add_smul, hn0,
      Balance.ipL2_comm lam h0 e, hsym, hee, hcdef] at hc
    nlinarith [hc]
  have hE0 : ipL2 lam e e = 0 :=
    eq_zero_of_quad_nonneg (ipL2_self_nonneg hnn e) hquad
  have hzero : ∀ x, e x = 0 := by
    intro x
    have hterm : lam x * (e x * e x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ => mul_nonneg (hnn y) (mul_self_nonneg (e y)))).mp hE0 x (Finset.mem_univ x)
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (hlam x).ne'
    · exact mul_self_eq_zero.mp h
  refine ⟨c, ⟨mem_curvSet.mpr hcurv, fun c' hc' => ?_⟩, h0, hm0, ?_, fun x => ?_⟩
  · have h2 := mem_curvSet.mp hc' h0
    rw [hp0, hsq0, mul_one, hcdef] at h2
    exact h2
  · show Real.sqrt (ipL2 lam h0 h0) = 1
    rw [hn0, Real.sqrt_one]
  · have := hex x
    rw [hzero x] at this
    linarith

omit [DecidableEq V] in
/-- **`d/dt‖h_t^⊥‖² = −2⟨h_t, Hh_t⟩`** along linearized training `ḣ = −Hh`: the mean is
conserved, because the image of `H` has mean zero. -/
theorem hasDerivAt_perp_sq_linear {K : V → V → ℝ} {lam w : V → ℝ} {g2 : ℝ}
    (hinv : Core.IsInvariant lam K) (hnn : ∀ x, 0 ≤ lam x) {u : ℝ → V → ℝ}
    (hu : ∀ t, 0 ≤ t → ∀ x, HasDerivAt (fun s => u s x) (-Balance.linHess K lam w g2 (u t) x) t)
    (s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (fun r : ℝ => nrmL2 lam (Balance.perpL2 lam (u r)) ^ 2)
      (-(2 * ipL2 lam (u s) (Balance.linHess K lam w g2 (u s)))) s := by
  have hmH : meanL2 lam (Balance.linHess K lam w g2 (u s)) = 0 :=
    Balance.meanL2_linHess (Balance.invariant_of_isInvariant hinv) w g2 (u s)
  have hD0 : ∑ y, lam y * -Balance.linHess K lam w g2 (u s) y = 0 := by
    have h1 : ∑ y, lam y * Balance.linHess K lam w g2 (u s) y = 0 := hmH
    simp only [mul_neg, Finset.sum_neg_distrib, h1, neg_zero]
  have hmd : HasDerivAt (fun r : ℝ => ∑ y, lam y * u r y)
      (∑ y, lam y * -Balance.linHess K lam w g2 (u s) y) s :=
    HasDerivAt.fun_sum fun y _ => (hu s hs y).const_mul (lam y)
  have hdp : ∀ x, HasDerivAt (fun r : ℝ => Balance.perpL2 lam (u r) x)
      (-Balance.linHess K lam w g2 (u s) x) s := by
    intro x
    have h1 := (hu s hs x).sub hmd
    rw [hD0, sub_zero] at h1
    exact h1
  have hsq : (fun r : ℝ => nrmL2 lam (Balance.perpL2 lam (u r)) ^ 2)
      = fun r : ℝ => ∑ x, lam x * (Balance.perpL2 lam (u r) x * Balance.perpL2 lam (u r) x) := by
    funext r
    rw [sq_nrmL2 hnn]
    rfl
  rw [hsq]
  have hsum : HasDerivAt
      (fun r : ℝ => ∑ x, lam x * (Balance.perpL2 lam (u r) x * Balance.perpL2 lam (u r) x))
      (∑ x, lam x * (-Balance.linHess K lam w g2 (u s) x * Balance.perpL2 lam (u s) x
        + Balance.perpL2 lam (u s) x * -Balance.linHess K lam w g2 (u s) x)) s :=
    HasDerivAt.fun_sum fun x _ => HasDerivAt.const_mul (lam x) ((hdp x).fun_mul (hdp x))
  have hval : (∑ x, lam x * (-Balance.linHess K lam w g2 (u s) x * Balance.perpL2 lam (u s) x
        + Balance.perpL2 lam (u s) x * -Balance.linHess K lam w g2 (u s) x))
      = -(2 * ipL2 lam (u s) (Balance.linHess K lam w g2 (u s))) := by
    rw [← ipL2_perpL2_of_mean_zero (h := u s) hmH]
    simp only [ipL2, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rwa [hval] at hsum

omit [DecidableEq V] in
/-- **Every linearized trajectory contracts at least at a curvature constant.** If
`c‖h^⊥‖² ≤ ⟨h, Hh⟩` for every `h`, every curve with `ḣ = −Hh` satisfies
`‖h_t^⊥‖ ≤ e^{−ct}‖h_0^⊥‖`, by Grönwall's inequality on `‖h_t^⊥‖²`. -/
theorem linear_decay {K : V → V → ℝ} {lam w : V → ℝ} {g2 c : ℝ}
    (hinv : Core.IsInvariant lam K) (hnn : ∀ x, 0 ≤ lam x)
    (hc : ∀ h : V → ℝ, c * nrmL2 lam (Balance.perpL2 lam h) ^ 2
      ≤ ipL2 lam h (Balance.linHess K lam w g2 h))
    {u : ℝ → V → ℝ}
    (hu : ∀ t, 0 ≤ t → ∀ x, HasDerivAt (fun s => u s x) (-Balance.linHess K lam w g2 (u t) x) t) :
    ∀ t, 0 ≤ t → nrmL2 lam (Balance.perpL2 lam (u t))
      ≤ Real.exp (-(c * t)) * nrmL2 lam (Balance.perpL2 lam (u 0)) := by
  intro t ht
  set F : ℝ → ℝ := fun s => nrmL2 lam (Balance.perpL2 lam (u s)) ^ 2 with hF
  set Dv : ℝ → ℝ := fun s => -(2 * ipL2 lam (u s) (Balance.linHess K lam w g2 (u s))) with hDv
  have hFd : ∀ s : ℝ, 0 ≤ s → HasDerivAt F (Dv s) s :=
    fun s hs => hasDerivAt_perp_sq_linear hinv hnn hu s hs
  have hFbound : ∀ s ∈ Set.Ico (0:ℝ) t, Dv s ≤ -(2 * c) * F s + 0 := by
    intro s _
    have h1 := hc (u s)
    simp only [hDv, hF, add_zero]
    linarith
  have hcont : ContinuousOn F (Set.Icc 0 t) :=
    fun s hs => ((hFd s hs.1).continuousAt).continuousWithinAt
  have hslope : ∀ s ∈ Set.Ico (0:ℝ) t, ∀ r : ℝ, Dv s < r →
      ∃ᶠ z in nhdsWithin s (Set.Ioi s), (z - s)⁻¹ * (F z - F s) < r := by
    intro s hs r hr
    have := (hFd s hs.1).hasDerivWithinAt.liminf_right_slope_le hr
    simpa [slope, vsub_eq_sub] using this
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (f := F) (f' := Dv) (δ := F 0)
    (K := -(2 * c)) (ε := 0) hcont hslope le_rfl hFbound t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0] at hgron
  have hexp : F 0 * Real.exp (-(2 * c) * (t - 0))
      = (Real.exp (-(c * t)) * nrmL2 lam (Balance.perpL2 lam (u 0))) ^ 2 := by
    have hsplit : Real.exp (-(2 * c) * (t - 0)) = Real.exp (-(c * t)) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [hsplit, hF]
    ring
  rw [hexp] at hgron
  have hnn' : 0 ≤ Real.exp (-(c * t)) * nrmL2 lam (Balance.perpL2 lam (u 0)) :=
    mul_nonneg (Real.exp_nonneg _) (nrmL2_nonneg _ _)
  have hroot := Real.sqrt_le_sqrt hgron
  rwa [hF, Real.sqrt_sq (nrmL2_nonneg _ _), Real.sqrt_sq hnn'] at hroot

omit [DecidableEq V] in
/-- **Along a slow mode, linearized training is `e^{−ct}h₀`**: if `Hh₀ = ch₀`, the curve
`t ↦ e^{−ct}h₀` solves `ḣ = −Hh`, and when `h₀` has mean zero and norm one its centred part has
norm `e^{−ct}`. -/
theorem slowMode_trajectory {K : V → V → ℝ} {lam w h0 : V → ℝ} {g2 c : ℝ}
    (heig : ∀ x, Balance.linHess K lam w g2 h0 x = c * h0 x) :
    (∀ t x, HasDerivAt (fun s => Real.exp (-(c * s)) * h0 x)
        (-Balance.linHess K lam w g2 (fun y => Real.exp (-(c * t)) * h0 y) x) t)
    ∧ (meanL2 lam h0 = 0 → nrmL2 lam h0 = 1 → ∀ t,
        nrmL2 lam (Balance.perpL2 lam (fun y => Real.exp (-(c * t)) * h0 y))
          = Real.exp (-(c * t))) := by
  refine ⟨fun t x => ?_, fun hm hn t => ?_⟩
  · have hlin : HasDerivAt (fun s : ℝ => -(c * s)) (-(c * 1)) t :=
      ((hasDerivAt_id' t).const_mul c).neg
    have h1 := hlin.exp.mul_const (h0 x)
    have hval : Real.exp (-(c * t)) * -(c * 1) * h0 x
        = -Balance.linHess K lam w g2 (fun y => Real.exp (-(c * t)) * h0 y) x := by
      rw [Balance.linHess_smul]
      simp only [heig]
      ring
    rwa [hval] at h1
  · have hmt : meanL2 lam (fun y => Real.exp (-(c * t)) * h0 y) = 0 := by
      rw [Balance.meanL2_const_mul, hm, mul_zero]
    rw [perpL2_of_mean_zero hmt, Balance.nrmL2_smul, hn, mul_one,
      abs_of_pos (Real.exp_pos _)]

/-- **The slowest rate of linearized training is the best curvature constant.** On the loop
closure of a finite path-connected marked graph, with the policy positive on its edges and frozen,
and `B̂` the least coercivity constant, there is a `c⋆` such that:
* `c⋆` is the best curvature constant, and lies between `g''(1)w_min/B̂²` and `g''(1)w_max/B̂²`;
* every linearized trajectory satisfies `‖h_t^⊥‖ ≤ e^{−c⋆t}‖h_0^⊥‖`;
* a slow mode `h₀`, of mean zero and norm one with `Hh₀ = c⋆h₀`, contracts at exactly `c⋆`. -/
theorem slowest_rate_frozen (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam w : V → ℝ}
    (hl : B.IsInvProb lam) {g2 wmin wsup : ℝ} (hwmin : ∀ x, wmin ≤ w x)
    (hwsup : ∀ x, w x ≤ wsup) (hwmin0 : 0 ≤ wmin) (hg2 : 0 ≤ g2) {Bstar : ℝ}
    (hBpos : 0 < Bstar) (hB : IsLeast (B.coercSet lam) Bstar) :
    ∃ c : ℝ, IsGreatest (B.curvSet lam w g2) c
      ∧ g2 * wmin / Bstar ^ 2 ≤ c ∧ c ≤ g2 * wsup / Bstar ^ 2
      ∧ (∀ u : ℝ → V → ℝ,
          (∀ t, 0 ≤ t → ∀ x,
            HasDerivAt (fun s => u s x) (-Balance.linHess B.phat lam w g2 (u t) x) t) →
          ∀ t, 0 ≤ t → nrmL2 lam (Balance.perpL2 lam (u t))
            ≤ Real.exp (-(c * t)) * nrmL2 lam (Balance.perpL2 lam (u 0)))
      ∧ ∃ h0 : V → ℝ, meanL2 lam h0 = 0 ∧ nrmL2 lam h0 = 1
        ∧ (∀ x, Balance.linHess B.phat lam w g2 h0 x = c * h0 x)
        ∧ (∀ t x, HasDerivAt (fun s => Real.exp (-(c * s)) * h0 x)
            (-Balance.linHess B.phat lam w g2 (fun y => Real.exp (-(c * t)) * h0 y) x) t)
        ∧ ∀ t, nrmL2 lam (Balance.perpL2 lam (fun y => Real.exp (-(c * t)) * h0 y))
            = Real.exp (-(c * t)) := by
  have hinv := Core.isInvariant_of_isInvProb B hl
  have hlam : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hw0 : ∀ x, 0 ≤ w x := fun x => hwmin0.trans (hwmin x)
  have hwsup0 : 0 ≤ wsup := (hw0 G.src).trans (hwsup G.src)
  obtain ⟨c, hc, h0, hm0, hn0, heig⟩ := exists_slowMode hpc hpos hl hw0 hg2
  obtain ⟨ha, hb⟩ := curvature_two_sided_frozen (B := B) hl hwmin hwsup hwmin0 hg2
  have hlow : g2 * wmin / Bstar ^ 2 ≤ c :=
    hc.2 (mem_curvSet.mpr (ha Bstar hBpos (mem_coercSet.mp hB.1)))
  have hup : c ≤ g2 * wsup / Bstar ^ 2 := by
    rcases le_or_gt c 0 with hc0 | hc0
    · exact hc0.trans (div_nonneg (mul_nonneg hg2 hwsup0) (sq_nonneg _))
    · have hle : Bstar ≤ Real.sqrt (g2 * wsup / c) :=
        hB.2 (mem_coercSet.mpr (hb c hc0 (mem_curvSet.mp hc.1)))
      have hsq : Bstar ^ 2 ≤ g2 * wsup / c := by
        have h2 := pow_le_pow_left₀ hBpos.le hle 2
        rwa [Real.sq_sqrt (div_nonneg (mul_nonneg hg2 hwsup0) hc0.le)] at h2
      rw [le_div_iff₀ hc0] at hsq
      rw [le_div_iff₀ (pow_pos hBpos 2)]
      calc c * Bstar ^ 2 = Bstar ^ 2 * c := mul_comm _ _
        _ ≤ g2 * wsup := hsq
  obtain ⟨htraj, hnorm⟩ := slowMode_trajectory (lam := lam) heig
  exact ⟨c, hc, hlow, hup,
    fun u hu => linear_decay hinv (fun x => (hlam x).le) (mem_curvSet.mp hc.1) hu,
    h0, hm0, hn0, heig, htraj, hnorm hm0 hn0⟩

end BackwardPolicy

end GFNBounds.Graph
