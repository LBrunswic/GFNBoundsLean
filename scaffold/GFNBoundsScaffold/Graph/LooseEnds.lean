import GFNBounds.Doubling.Remarks
import GFNBounds.Graph.CycleExample
import GFNBounds.Graph.MorozovConsume
import GFNBounds.Balance.TrainingSpeedAssembled

/-!
# Loose ends (draft header)
-/

namespace GFNBounds.Doubling.Remarks

open Filter Topology

section PathLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The trajectories `(X₀, …, Xₙ)` of length `n` started at `x`. -/
def paths (x : V) (n : ℕ) : Finset (Fin (n + 1) → V) :=
  Finset.univ.filter fun γ => γ 0 = x

/-- The mass `∏_{i<n} T(Xᵢ → Xᵢ₊₁)` of a trajectory. -/
noncomputable def trajMass (K : V → V → ℝ) {n : ℕ} (γ : Fin (n + 1) → V) : ℝ :=
  ∏ i : Fin n, K (γ i.castSucc) (γ i.succ)

/-- `E(θ(Xₙ) | X₀ = x)`, against the finite path law. -/
noncomputable def condExp (K : V → V → ℝ) (θ : V → ℝ) (n : ℕ) (x : V) : ℝ :=
  ∑ γ ∈ paths x n, trajMass K γ * θ (γ (Fin.last n))

theorem paths_eq_map (x : V) (n : ℕ) :
    paths x n = Finset.univ.map ⟨Fin.cons x, Fin.cons_right_injective (α := fun _ => V) x⟩ := by
  ext γ
  simp only [paths, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro h
    exact ⟨Fin.tail γ, by rw [← h, Fin.cons_self_tail]⟩
  · rintro ⟨ω, rfl⟩
    exact Fin.cons_zero (α := fun _ => V) x ω

theorem condExp_eq_sum_cons (K : V → V → ℝ) (θ : V → ℝ) (n : ℕ) (x : V) :
    condExp K θ n x
      = ∑ ω : Fin n → V, trajMass K (Fin.cons x ω : Fin (n + 1) → V)
          * θ ((Fin.cons x ω : Fin (n + 1) → V) (Fin.last n)) := by
  rw [condExp, paths_eq_map, Finset.sum_map]
  rfl

omit [Fintype V] [DecidableEq V] in
theorem trajMass_cons_cons (K : V → V → ℝ) {n : ℕ} (x y : V) (ω : Fin n → V) :
    trajMass K (Fin.cons x (Fin.cons y ω : Fin (n + 1) → V) : Fin (n + 2) → V)
      = K x y * trajMass K (Fin.cons y ω : Fin (n + 1) → V) := by
  simp only [trajMass]
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
  rfl

theorem condExp_succ (K : V → V → ℝ) (θ : V → ℝ) (n : ℕ) (x : V) :
    condExp K θ (n + 1) x = ∑ y, K x y * condExp K θ n y := by
  rw [condExp_eq_sum_cons, ← (Fin.consEquiv fun _ : Fin (n + 1) => V).sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [condExp_eq_sum_cons, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  change trajMass K (Fin.cons x (Fin.cons y ω : Fin (n + 1) → V) : Fin (n + 2) → V)
      * θ ((Fin.cons x (Fin.cons y ω : Fin (n + 1) → V) : Fin (n + 2) → V) (Fin.last (n + 1))) = _
  rw [trajMass_cons_cons, ← Fin.succ_last, Fin.cons_succ, mul_assoc]

theorem condExp_zero (K : V → V → ℝ) (θ : V → ℝ) (x : V) : condExp K θ 0 x = θ x := by
  rw [condExp_eq_sum_cons, Fintype.sum_unique]
  simp only [trajMass, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  rfl

theorem condExp_eq_iterate (K : V → V → ℝ) (θ : V → ℝ) :
    ∀ n x, condExp K θ n x = (Core.funAct K)^[n] θ x := by
  intro n
  induction n with
  | zero => intro x; rw [condExp_zero]; rfl
  | succ n ih =>
    intro x
    rw [condExp_succ, Function.iterate_succ_apply', Core.funAct_apply]
    exact Finset.sum_congr rfl fun y _ => by rw [ih]

omit [Fintype V] [DecidableEq V] in
theorem trajMass_nonneg {K : V → V → ℝ} (hK : ∀ x y, 0 ≤ K x y) {n : ℕ} (γ : Fin (n + 1) → V) :
    0 ≤ trajMass K γ :=
  Finset.prod_nonneg fun _ _ => hK _ _

omit [DecidableEq V] in
theorem funAct_one {K : V → V → ℝ} (hK : Core.IsMarkov K) :
    Core.funAct K (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext x
  rw [Core.funAct_apply]
  simp only [mul_one]
  exact hK.row_sum x

theorem sum_trajMass {K : V → V → ℝ} (hK : Core.IsMarkov K) (n : ℕ) (x : V) :
    ∑ γ ∈ paths x n, trajMass K γ = 1 := by
  have h := condExp_eq_iterate K (fun _ => (1 : ℝ)) n x
  rw [Function.iterate_fixed (funAct_one hK)] at h
  simpa only [condExp, mul_one] using h

theorem condExp_one_eq_funAct (K : V → V → ℝ) (f : V → ℝ) (x : V) :
    condExp K f 1 x = Core.funAct K f x := by
  rw [condExp_eq_iterate]
  rfl

theorem unwtL2_funOp_pow_wtL2 {K : V → V → ℝ} {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    (θ : V → ℝ) (n : ℕ) (x : V) :
    Balance.unwtL2 lam ((funOp lam K ^ n) (Balance.wtL2 lam θ)) x = condExp K θ n x := by
  rw [funOp_pow_wtL2 hlam, Balance.unwtL2_wtL2 hlam, condExp_eq_iterate]

theorem diffusion_apply_eq_series_condExp {K : V → V → ℝ} {lam : V → ℝ}
    (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1)
    {U : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V}
    (hconv : Tendsto (partialSum (funOp lam K) (Balance.meanOp lam)) atTop (𝓝 U))
    (θ : V → ℝ) (x : V) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (condExp K θ n x - Graph.meanL2 lam θ)) atTop
      (𝓝 (Balance.unwtL2 lam ((Ring.inverse (1 - funOp lam K + Balance.meanOp lam) - Balance.meanOp lam)
        (Balance.wtL2 lam θ)) x)) := by
  simpa only [condExp_eq_iterate] using diffusion_apply_eq_series hK hinv hlam htot hconv θ x

/-- Inhabitation of the path law and of the restated series, on the flip chain at `3/4`. -/
theorem flip_condExp_series_check :
    (∀ n x, ∑ γ ∈ paths x n, trajMass (flipK (3 / 4)) γ = 1)
      ∧ ∀ (θ : Fin 2 → ℝ) (x : Fin 2),
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
            (condExp (flipK (3 / 4)) θ n x - Graph.meanL2 Balance.twoStateLam θ)) atTop
          (𝓝 (Balance.unwtL2 Balance.twoStateLam
            ((Ring.inverse (1 - funOp Balance.twoStateLam (flipK (3 / 4))
                + Balance.meanOp Balance.twoStateLam) - Balance.meanOp Balance.twoStateLam)
              (Balance.wtL2 Balance.twoStateLam θ)) x)) := by
  have hK := flipK_isMarkov (q := 3 / 4) (by norm_num) (by norm_num)
  obtain ⟨U, hU⟩ := diffusion_series_converges_check
  exact ⟨sum_trajMass hK, fun θ x => diffusion_apply_eq_series_condExp hK (flipK_isInvariant _)
    Balance.twoStateLam_pos Balance.twoStateLam_sum hU θ x⟩

end PathLaw

end GFNBounds.Doubling.Remarks

namespace GFNBounds.Graph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : MarkedGraph V} {B : BackwardPolicy G}

section InducedFlow

/-- The internal states `𝒱 ∖ {s₀, s_f}`. -/
def internal (G : MarkedGraph V) : Finset V := univ.filter fun x => x ≠ G.src ∧ x ≠ G.snk

theorem sum_eq_internal_add (G : MarkedGraph V) (F : V → ℝ) :
    ∑ x, F x = (∑ x ∈ internal G, F x) + F G.src + F G.snk := by
  have hc : univ.filter (fun x => ¬ (x ≠ G.src ∧ x ≠ G.snk)) = {G.src, G.snk} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, ne_eq, not_and, not_not]
    constructor
    · intro h
      by_cases hx : x = G.src
      · exact Or.inl hx
      · exact Or.inr (h hx)
    · rintro (h | h) h'
      · exact absurd h h'
      · exact h
  rw [← sum_filter_add_sum_filter_not univ (fun x => x ≠ G.src ∧ x ≠ G.snk), hc,
    sum_pair G.src_ne_snk, internal, add_assoc]

omit [DecidableEq V] in
/-- The flow into the sink along the edges of `G`: `∑_s F(s_f) π_←(s_f → s) = F(s_f)`. -/
theorem snk_inflow (B : BackwardPolicy G) (F : V → ℝ) :
    ∑ s, F G.snk * B.pb G.snk s = F G.snk := by
  rw [← mul_sum, B.row_sum (Ne.symm G.src_ne_snk), mul_one]

/-- **Morozov's identity in this library's reading**: an invariant measure `F` of the loop-closed
backward chain carries total mass `F(s_f)·σ̄` on the internal states. -/
theorem internal_flow_eq (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam gr uH F : V → ℝ} (hl : B.IsInvProb lam) (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hF : ∀ y, ∑ x, F x * B.phat x y = F y) :
    ∑ x ∈ internal G, F x = F G.snk * B.sigmaBar uH := by
  have hsum := sum_eq_internal_add G F
  have hsm : ∀ x, F x = (∑ z, F z) * lam x := BackwardPolicy.eq_smul_lam_of_invariant hpc hpos hl hF
  have hsrc : lam G.src = 1 / (2 + B.sigmaBar uH) := BackwardPolicy.lam_src_eq hpc hpos hl hg hhit
  have hsnk : lam G.snk = 1 / (2 + B.sigmaBar uH) := BackwardPolicy.lam_snk_eq hpc hpos hl hg hhit
  have hd : 0 < 2 + B.sigmaBar uH := BackwardPolicy.two_add_sigmaBar_pos hhit
  set c := ∑ z, F z with hc
  have hFs : F G.src = c / (2 + B.sigmaBar uH) := by rw [hsm, hsrc]; ring
  have hFf : F G.snk = c / (2 + B.sigmaBar uH) := by rw [hsm, hsnk]; ring
  have hint : ∑ x ∈ internal G, F x = c - F G.src - F G.snk := by linarith
  rw [hint, hFs, hFf]
  field_simp
  ring

/-- **No circulation can be added at fixed sink flow**: two invariant measures of the loop-closed
backward chain with the same value at `s_f` coincide. -/
theorem flow_eq_of_snk_eq (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam F F' : V → ℝ} (hl : B.IsInvProb lam)
    (hF : ∀ y, ∑ x, F x * B.phat x y = F y) (hF' : ∀ y, ∑ x, F' x * B.phat x y = F' y)
    (hsnk : F G.snk = F' G.snk) : F = F' := by
  have h1 := BackwardPolicy.eq_smul_lam_of_invariant hpc hpos hl hF
  have h2 := BackwardPolicy.eq_smul_lam_of_invariant hpc hpos hl hF'
  have hp : 0 < lam G.snk := hl.pos hpc hpos G.snk
  have hs : (∑ z, F z) = ∑ z, F' z := by
    have := hsnk
    rw [h1 G.snk, h2 G.snk] at this
    exact mul_right_cancel₀ (ne_of_gt hp) this
  funext x
  rw [h1 x, h2 x, hs]

end InducedFlow

namespace CycleExample

/-- The internal states of the five-vertex cycle are `x₁, x₂, x₃`. -/
theorem internal_cyc : internal cyc = {1, 2, 3} := by decide

/-- **`rem:cycle_no_stalemate`, the example identity**: every flow `F` balanced for the frozen
loop-closed backward policy has total flow `F(s_f)·3/(1−p)` through the internal states. -/
theorem cycle_internal_flow {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {F : Fin 5 → ℝ}
    (hF : ∀ y, ∑ x, F x * (pol hp0 hp1).phat x y = F y) :
    ∑ x ∈ internal cyc, F x = F cyc.snk * (3 / (1 - p))
      ∧ F 1 + F 2 + F 3 = F 4 * (3 / (1 - p)) := by
  have h := internal_flow_eq pathConnected (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1)
    (isGreen hp0 hp1) (isHitExp hp0 hp1) hF
  rw [sigmaBar_eq] at h
  refine ⟨h, ?_⟩
  rw [internal_cyc] at h
  have e : ∑ x ∈ ({1, 2, 3} : Finset (Fin 5)), F x = F 1 + F 2 + F 3 := by
    rw [sum_insert (by decide), sum_insert (by decide), sum_singleton, add_assoc]
  rw [← e]
  exact h

/-- The flow of each cycle state, and the flow at the source. -/
theorem cycle_flow_values {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {F : Fin 5 → ℝ}
    (hF : ∀ y, ∑ x, F x * (pol hp0 hp1).phat x y = F y) :
    F 1 = F 4 / (1 - p) ∧ F 2 = F 4 / (1 - p) ∧ F 3 = F 4 / (1 - p) ∧ F 0 = F 4 := by
  have hne : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  have e0 := hF 0
  have e1 := hF 1
  have e2 := hF 2
  have e4 := hF 4
  simp only [Fin.sum_univ_five, phat_eq hp0 hp1, kern] at e0 e1 e2 e4
  simp only [Fin.isValue, mul_zero, zero_add, add_zero, mul_one] at e0 e1 e2 e4
  refine ⟨?_, ?_, ?_, by linarith⟩
  · field_simp; linarith
  · field_simp; rw [e1, ← e4, ← e0]
  · field_simp; rw [e2, e1, ← e4, ← e0]

/-- Inhabitation: the invariant probability is such a flow, and at `p = 1/2` the identity reads
`3λ(x₁) = λ(s_f)·6`. -/
theorem cycle_internal_flow_check {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∑ x ∈ internal cyc, lam p x = lam p cyc.snk * (3 / (1 - p)) :=
  (cycle_internal_flow hp0 hp1 (isInvProb hp0 hp1).inv).1

end CycleExample

section FMC3On

/-- **`prop:morozov_rate`*(3)*, flow matching, `theo:local_convergence_full` flow clause, with
existence**: at `B̂ := B̂_σ` and `λ_min := min λ`, for `g` `C³` on the closed window `[1−a,1+a]`
(one-sided at the ends) with derivative `gd` there, from every `h₀` with `‖h₀‖_{L²(λ)} ≤ ε₀` the
nonlinear flow-matching gradient flow on the loop closure **exists**, is unique, stays in the
window, and converges to a balanced `c_∞λ` at rate `ϱ_σ/2`, with
`ϱ_σ = g''(1) w_min min_x N(x)/(σ_*²(2+σ̄))` written out.
`TrainingSpeedAssembled.local_convergence_full_exists` at `B̂ := B̂_σ`. -/
theorem local_convergence_sigma_C3On {lam gr uH wf : V → ℝ} {g gd : ℝ → ℝ} {a wsup wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (Balance.winC3 a))
    (hgd : ∀ y ∈ Balance.winC3 a, HasDerivWithinAt g (gd y) (Balance.winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |wf x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ wf x)
    {h0 : V → ℝ}
    (hnorm0 : nrmL2 lam h0
      ≤ Balance.eps0W g a wmin wsup (Balance.BhatSigma G uH lam) (minOver G lam)) :
    ∃ h : ℝ → V → ℝ, h 0 = h0
      ∧ Balance.IsGradientFlow B.phat lam (fun z => lam z * wf z) gd (fun s x => 1 + h s x)
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < 1 + h t x
          ∧ |Balance.ratio B.phat lam (fun z => 1 + h t z) x - 1| ≤ 2 * a / 3)
      ∧ (∀ h' : ℝ → V → ℝ, h' 0 = h0 →
          Balance.IsGradientFlow B.phat lam (fun z => lam z * wf z) gd (fun s x => 1 + h' s x) →
          ∀ t : ℝ, 0 ≤ t → h' t = h t)
      ∧ ∃ cinf : ℝ, Balance.Balanced B.phat lam (fun _ => cinf)
          ∧ |cinf - 1 - meanL2 lam h0|
              ≤ Balance.CW g a wmin wsup * nrmL2 lam (Balance.perpL2 lam h0) ^ 2
          ∧ ∀ t : ℝ, 0 ≤ t → nrmL2 lam (fun x => h t x - (cinf - 1))
              ≤ 2 * Real.exp (-(deriv (deriv g) 1 * wmin * minOver G (visits G gr)
                    / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)) * t / 2))
                  * nrmL2 lam (Balance.perpL2 lam h0) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  obtain ⟨h, hh0, hflow, hwin, huniq, cinf, hbal, hc, hdecay⟩ :=
    Balance.local_convergence_full_exists
      ((Core.phat_isMarkov B).toIsMarkovOn lam) (Core.isInvariant_of_isInvProb B hl) hp hl.total
      (minOver_pos hp) (fun x => minOver_le lam x) ha hC3 hgd hg1 hg2 hwsup hwmin0 hwmin
      (Balance.one_le_BhatSigma hpc hpos hl hhit) (Balance.hcoer_of_graph hpc hpos hl hhit) hnorm0
  refine ⟨h, hh0, hflow, hwin, huniq, cinf, hbal, hc, fun t ht => ?_⟩
  have key := hdecay t ht
  simp only [Balance.rhoL] at key
  rwa [rate_eq_visits hpc hpos hl hg hhit] at key

/-- **`prop:morozov_rate`*(3)*, flow matching, `theo:local_convergence_full` descent clause**: at
`B̂ := B̂_σ`, for `g` `C³` on the closed window, for `0 ≤ γ ≤ γ₀` and `‖h₀‖ ≤ ε₀` (`ε₀` read at
`λ_min := min λ`), the descent is well defined at every step and contracts `‖h_k − Πh_k‖` by
`1 − γϱ_σ/4`, `ϱ_σ` written out. `TrainingSpeedAssembled.local_convergence_gd_C3On` at
`B̂ := B̂_σ`. -/
theorem local_convergence_gd_sigma_C3On {lam gr uH wf : V → ℝ} {g gd : ℝ → ℝ}
    {hk : ℕ → V → ℝ} {a wsup wmin gam : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (Balance.winC3 a))
    (hgd : ∀ y ∈ Balance.winC3 a, HasDerivWithinAt g (gd y) (Balance.winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |wf x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ wf x)
    (hstep : ∀ k : ℕ, hk (k + 1) = fun x =>
      hk k x - gam * Balance.lossGrad B.phat lam (fun z => lam z * wf z) gd (fun z => 1 + hk k z) x)
    (hgam0 : 0 ≤ gam) (hgam : gam ≤ Balance.gamma0W g a wmin wsup (Balance.BhatSigma G uH lam))
    (hnorm0 : nrmL2 lam (hk 0)
      ≤ Balance.eps0W g a wmin wsup (Balance.BhatSigma G uH lam) (minOver G lam)) :
    ∀ k : ℕ, ((∀ x, 0 < 1 + hk k x)
      ∧ (∀ x, |Balance.ratio B.phat lam (fun z => 1 + hk k z) x - 1| ≤ 2 * a / 3)
      ∧ ∀ d : V → ℝ,
          HasDerivAt
            (fun t : ℝ => Balance.loss B.phat lam (fun z => lam z * wf z)
              (fun x => 1 + hk k x + t * d x) g)
            (ipL2 lam (Balance.lossGrad B.phat lam (fun z => lam z * wf z) gd
              fun z => 1 + hk k z) d) 0)
      ∧ nrmL2 lam (Balance.perpL2 lam (hk (k + 1)))
          ≤ (1 - gam * (deriv (deriv g) 1 * wmin * minOver G (visits G gr)
                / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH))) / 4)
              * nrmL2 lam (Balance.perpL2 lam (hk k)) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  intro k
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := Balance.local_convergence_gd_C3On
    ((Core.phat_isMarkov B).toIsMarkovOn lam) (Core.isInvariant_of_isInvProb B hl) hp hl.total
    (minOver_pos hp) (fun x => minOver_le lam x) ha hC3 hgd hg1 hg2 hwsup hwmin0 hwmin
    (Balance.one_le_BhatSigma hpc hpos hl hhit) (Balance.hcoer_of_graph hpc hpos hl hhit) hstep
    hgam0 hgam hnorm0 k
  refine ⟨⟨h1, h2, h3⟩, ?_⟩
  simp only [Balance.rhoL] at h4
  rwa [rate_eq_visits hpc hpos hl hg hhit] at h4

/-- The paper's radius `ε₀` for the flow-matching loss on `s₀ → s_f`, at `g = (log x)²`,
`a = 1/2`, `w ≡ 1`. -/
noncomputable def arEps0FM : ℝ :=
  Balance.eps0W Balance.logSq (1/2) 1 1 (Balance.BhatSigma ar arLeveled.lvl arLam) (minOver ar arLam)

theorem arEps0FM_pos : 0 < arEps0FM :=
  (Balance.constW_bounds (lam := arLam) (w := fun _ : Fin 2 => (1:ℝ))
    arIsInvProb.total (by rw [ar_minOver_lam]; norm_num) (by norm_num)
    Balance.logSq_C3On_bundle.1 Balance.logSq_C3On_bundle.2.2.2 (fun _ => by norm_num) one_pos
    (fun _ => le_rfl)
    (Balance.one_le_BhatSigma arPathConnected arPositiveOnEdges arIsInvProb
      arLeveled.isHitExp)).1.1

/-- The indicator of the sink. -/
noncomputable def arSnkInd : Fin 2 → ℝ := fun x => if x = ar.snk then 1 else 0

/-- **`local_convergence_sigma_C3On`, inhabited off balance.** On `s₀ → s_f`, at `g = (log x)²`,
`a = 1/2`, `w ≡ 1`, from `h₀ = ε₀𝟙_{s_f}`, whose deviation from its mean has positive norm, the
flow-matching gradient flow exists and converges to a balanced flow at rate `ϱ_σ/2 = 1/2`. -/
theorem ar_local_convergence_FM_witness :
    0 < nrmL2 arLam (Balance.perpL2 arLam fun x => arEps0FM * arSnkInd x)
      ∧ ∃ h : ℝ → Fin 2 → ℝ, h 0 = (fun x => arEps0FM * arSnkInd x)
        ∧ Balance.IsGradientFlow arPol.phat arLam (fun z => arLam z * 1) Balance.logSqDeriv
            (fun s x => 1 + h s x)
        ∧ ∃ cinf : ℝ, Balance.Balanced arPol.phat arLam (fun _ => cinf)
            ∧ ∀ t : ℝ, 0 ≤ t
              → nrmL2 arLam (fun x => h t x - (cinf - 1))
                ≤ 2 * Real.exp (-(1 * t / 2))
                  * nrmL2 arLam (Balance.perpL2 arLam fun x => arEps0FM * arSnkInd x) := by
  have he := arEps0FM_pos
  have hmean : meanL2 arLam (fun x => arEps0FM * arSnkInd x) = arEps0FM / 2 := by
    simp only [meanL2, Fin.sum_univ_two, arLam, arSnkInd, ar]
    norm_num
    ring
  have hperp : Balance.perpL2 arLam (fun x => arEps0FM * arSnkInd x)
      = fun x => if x = ar.snk then arEps0FM / 2 else -(arEps0FM / 2) := by
    funext x
    rw [Balance.perpL2_apply, hmean]
    fin_cases x
    · simp only [arSnkInd, ar, Fin.zero_eta, Fin.isValue, zero_ne_one, if_false, mul_zero]
      ring
    · simp only [arSnkInd, ar, Fin.mk_one, Fin.isValue, if_true, mul_one]
      ring
  have hpos : 0 < nrmL2 arLam (Balance.perpL2 arLam fun x => arEps0FM * arSnkInd x) := by
    rw [hperp]
    apply Real.sqrt_pos.mpr
    simp only [ipL2, Fin.sum_univ_two, arLam, ar]
    norm_num
    positivity
  have hnorm0 : nrmL2 arLam (fun x => arEps0FM * arSnkInd x) ≤ arEps0FM := by
    have hip : ipL2 arLam (fun x => arEps0FM * arSnkInd x) (fun x => arEps0FM * arSnkInd x)
        = arEps0FM ^ 2 / 2 := by
      simp only [ipL2, Fin.sum_univ_two, arLam, arSnkInd, ar]
      norm_num
      ring
    rw [nrmL2, hip]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  obtain ⟨h, hh0, hflow, -, -, cinf, hbal, -, hdecay⟩ := local_convergence_sigma_C3On
    (wf := fun _ => (1:ℝ)) arPathConnected arPositiveOnEdges arIsInvProb arIsGreen
    arLeveled.isHitExp (by norm_num) Balance.logSq_C3On_bundle.1 Balance.logSq_C3On_bundle.2.1
    Balance.logSq_C3On_bundle.2.2.1 Balance.logSq_C3On_bundle.2.2.2 (fun _ => by norm_num)
    one_pos (fun _ => le_rfl) hnorm0
  refine ⟨hpos, h, hh0, hflow, cinf, hbal, fun t ht => ?_⟩
  have key := hdecay t ht
  obtain ⟨hs, hb, hm, -, -⟩ := ar_leveled_check
  rw [Balance.logSq_deriv2_one, hs, hb, hm] at key
  convert key using 4
  norm_num

end FMC3On

end GFNBounds.Graph
