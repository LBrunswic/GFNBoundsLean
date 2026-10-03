import GFNBounds.Graph.Diffusion
import GFNBounds.Balance.TrainingSpeed

/-!
# The best coercivity constant, and the exact curvature at a constant weight

On the loop closure of a finite path-connected marked graph whose backward policy is positive on
its edges and held fixed, the coercivity constants `B` with `‖h − Πh‖ ≤ B‖Ah‖` for every `h` form a
set with a least element `B̂`, which is positive: the best coercivity constant exists. At a constant
training weight `w`, the curvature of the loss transverse to the balanced flow, read as the best
constant `c` with `c‖h − Πh‖² ≤ ⟨h, Hh⟩`, is then exactly `g''(1)w/B̂²`.

This makes the main text's "exactly" a statement about a certified object: `B̂` is the least
coercivity constant, and the curvature is pinned to it. That `B̂` is also the norm of the Green
operator is the identification of the main text, which is not made here.

## What is proved

| | |
|---|---|
| **`exists_perp_pos`** | some function has a centred part of positive norm: the indicator of the sink |
| **`bestCoerc_exists`** | the set of coercivity constants has a least element, and it is positive |
| **`curvature_exact_frozen`** | at a constant weight `w`, the best curvature constant is `g''(1)w/B̂²`, `B̂` the least coercivity constant |

## Hypothesis checklist

| hypothesis | here |
|---|---|
| a finite path-connected marked graph, a policy positive on its edges, `λ` its invariant probability | `hpc`, `hpos`, `hl` |
| the coercivity constants | `coercSet B lam`, the `B` with `‖h − Πh‖ ≤ B‖Ah‖` for every `h` |
| the curvature | `ipL2 lam h (linHess B.phat lam w g2 h)`, the quadratic form of `H = g''(1)A†M_wA` |
| a constant weight | `w ≡ w₀ ≥ 0`, `g''(1) ≥ 0` |

## SCOPE (disclosed)

* **The Green operator is not formed.** `B̂` is the least element of the set of coercivity
  constants; its identification with `‖(I − P + Π)^{-1} − Π‖` is not made.
* **No `sorry`.**

Provenance: mathlib tag `v4.31.0`, pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : MarkedGraph V}

namespace BackwardPolicy

variable {B : BackwardPolicy G}

/-- **The coercivity constants** of the loop closure: the `c` with `‖h − Πh‖ ≤ c‖Ah‖` for every
`h`, `A = P − I`. -/
def coercSet (B : BackwardPolicy G) (lam : V → ℝ) : Set ℝ :=
  {c | ∀ h : V → ℝ, nrmL2 lam (Balance.perpL2 lam h) ≤ c * nrmL2 lam (Balance.Aop B.phat lam h)}

theorem mem_coercSet {lam : V → ℝ} {c : ℝ} :
    c ∈ B.coercSet lam
      ↔ ∀ h : V → ℝ, nrmL2 lam (Balance.perpL2 lam h) ≤ c * nrmL2 lam (Balance.Aop B.phat lam h) :=
  Iff.rfl

/-- **A function with a centred part of positive norm**: the indicator of the sink, whose mean
`λ(s_f)` is strictly between `0` and `1`. -/
theorem exists_perp_pos (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) : ∃ h : V → ℝ, 0 < nrmL2 lam (Balance.perpL2 lam h) := by
  have hlam : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hmean : meanL2 lam (fun x => if x = G.snk then (1 : ℝ) else 0) = lam G.snk := by
    simp [meanL2]
  have hlt : lam G.snk < 1 := by
    have htot : ∑ x, lam x = 1 := hl.total
    have h2 : lam G.src + lam G.snk ≤ ∑ x, lam x := by
      rw [← Finset.sum_pair G.src_ne_snk]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun x _ _ => (hlam x).le
    linarith [hlam G.src]
  refine ⟨fun x => if x = G.snk then (1 : ℝ) else 0, Real.sqrt_pos.mpr ?_⟩
  have hp : Balance.perpL2 lam (fun x => if x = G.snk then (1 : ℝ) else 0) G.snk
      = 1 - lam G.snk := by
    rw [Balance.perpL2_apply, hmean, if_pos rfl]
  have h1 : 0 < 1 - lam G.snk := by linarith
  have hterm : 0 < lam G.snk
      * (Balance.perpL2 lam (fun x => if x = G.snk then (1 : ℝ) else 0) G.snk
        * Balance.perpL2 lam (fun x => if x = G.snk then (1 : ℝ) else 0) G.snk) := by
    rw [hp]
    exact mul_pos (hlam G.snk) (mul_pos h1 h1)
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (f := fun x => lam x * (Balance.perpL2 lam (fun x => if x = G.snk then (1 : ℝ) else 0) x
      * Balance.perpL2 lam (fun x => if x = G.snk then (1 : ℝ) else 0) x))
    (fun x _ => mul_nonneg (hlam x).le (mul_self_nonneg _)) (Finset.mem_univ G.snk))

/-- **The best coercivity constant exists.** The set of coercivity constants of the loop closure
has a least element, and it is positive. -/
theorem bestCoerc_exists (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) : ∃ Bstar : ℝ, 0 < Bstar ∧ IsLeast (B.coercSet lam) Bstar := by
  obtain ⟨uH, hhit⟩ := exists_isHitExp (B := B) hpc hpos
  have hne : (B.coercSet lam).Nonempty :=
    ⟨_, mem_coercSet.mpr (Balance.hcoer_of_graph hpc hpos hl hhit)⟩
  obtain ⟨h0, hh0⟩ := exists_perp_pos hpc hpos hl
  have hA0 : 0 < nrmL2 lam (Balance.Aop B.phat lam h0) := by
    rcases (nrmL2_nonneg lam (Balance.Aop B.phat lam h0)).lt_or_eq with hlt | heq
    · exact hlt
    · have h := Balance.hcoer_of_graph hpc hpos hl hhit h0
      rw [← heq, mul_zero] at h
      linarith
  have hlow : ∀ c ∈ B.coercSet lam,
      nrmL2 lam (Balance.perpL2 lam h0) / nrmL2 lam (Balance.Aop B.phat lam h0) ≤ c := by
    intro c hc
    rw [div_le_iff₀ hA0]
    exact mem_coercSet.mp hc h0
  have hbdd : BddBelow (B.coercSet lam) := ⟨_, hlow⟩
  refine ⟨sInf (B.coercSet lam), lt_of_lt_of_le (div_pos hh0 hA0) (le_csInf hne hlow), ?_,
    fun c hc => csInf_le hbdd hc⟩
  refine mem_coercSet.mpr fun h => ?_
  rcases (nrmL2_nonneg lam (Balance.Aop B.phat lam h)).lt_or_eq with hApos | hAz
  · have hle : nrmL2 lam (Balance.perpL2 lam h) / nrmL2 lam (Balance.Aop B.phat lam h)
        ≤ sInf (B.coercSet lam) :=
      le_csInf hne fun c hc => by
        rw [div_le_iff₀ hApos]
        exact mem_coercSet.mp hc h
    rwa [div_le_iff₀ hApos] at hle
  · obtain ⟨c, hc⟩ := hne
    have h1 := mem_coercSet.mp hc h
    rw [← hAz, mul_zero] at h1 ⊢
    exact h1

/-- **The exact curvature at a constant weight.** With `w ≡ w₀ ≥ 0`, `g''(1) ≥ 0` and `B̂` the least
coercivity constant, the best constant `c` with `c‖h − Πh‖² ≤ ⟨h, Hh⟩` for every `h` is
`g''(1)w₀/B̂²`. -/
theorem curvature_exact_frozen {lam : V → ℝ} (hl : B.IsInvProb lam) {Bstar : ℝ}
    (hBpos : 0 < Bstar) (hB : IsLeast (B.coercSet lam) Bstar) {g2 w0 : ℝ} (hg2 : 0 ≤ g2)
    (hw0 : 0 ≤ w0) :
    IsGreatest {c : ℝ | ∀ h : V → ℝ, c * nrmL2 lam (Balance.perpL2 lam h) ^ 2
        ≤ ipL2 lam h (Balance.linHess B.phat lam (fun _ => w0) g2 h)} (g2 * w0 / Bstar ^ 2) := by
  obtain ⟨ha, hb⟩ := curvature_two_sided_frozen (B := B) (w := fun _ => w0) (wmin := w0)
    (wsup := w0) hl (fun _ => le_rfl) (fun _ => le_rfl) hw0 hg2
  refine ⟨ha Bstar hBpos (mem_coercSet.mp hB.1), fun c hc => ?_⟩
  rcases le_or_gt c 0 with hc0 | hc0
  · exact hc0.trans (div_nonneg (mul_nonneg hg2 hw0) (sq_nonneg _))
  · have hcoer := hb c hc0 hc
    have hle : Bstar ≤ Real.sqrt (g2 * w0 / c) := hB.2 (mem_coercSet.mpr hcoer)
    have hsq : Bstar ^ 2 ≤ g2 * w0 / c := by
      have h2 := pow_le_pow_left₀ hBpos.le hle 2
      rwa [Real.sq_sqrt (div_nonneg (mul_nonneg hg2 hw0) hc0.le)] at h2
    rw [le_div_iff₀ hc0] at hsq
    rw [le_div_iff₀ (pow_pos hBpos 2)]
    calc c * Bstar ^ 2 = Bstar ^ 2 * c := mul_comm _ _
      _ ≤ g2 * w0 := hsq

end BackwardPolicy

end GFNBounds.Graph
