import GFNBounds.Balance.LocalConvergenceClose

/-!
# Training with the backward policy frozen: the gradient as a diffusion, and the local rate

**`theo:gd_diffusion`** (statement `cv_divergence.tex:147–153`, through its twin
**`theo:gd_diffusion_full`**) and **`theo:local_convergence`** (statement
`cv_divergence.tex:170–174`, through its twin **`theo:local_convergence_full`**), stated on the
object a practitioner trains: a finite marked graph whose backward policy is held fixed.

> Near the balanced flow, and for any generator of class `C³` near `1`, the gradient field of a
> balance loss linearizes to the backward policy's diffusion applied twice, so that training
> relaxes the current flow guess by diffusing it through the frozen backward policy.

> On a finite state space, and from an explicit neighbourhood of the unit-mass balanced flow, the
> rate above upgrades to the full nonlinear dynamics.

The kernel of both statements is the loop closure `B.phat` of a backward policy positive on the
edges of a finite path-connected marked graph, and `λ` is its invariant probability, positive at
every state. With the policy frozen a flow is its state mass `μ`, and the flow-matching loss on
states is `𝓛_{g,ν}(μ) = ∑ ν g(r)` with `r` the balance ratio of the loop closure at `μ`.

## What is proved

| | |
|---|---|
| **`gd_diffusion_frozen`** | `theo:gd_diffusion` on the loop closure: at the state mass `(1+h)λ`, `|h| ≤ ε ≤ a/4`, the ratio is `1 + Ah/(1+h)`; the loss has the `L²(λ)` gradient `D(h)` along every direction; `‖D(h) − Hh‖ ≤ Kε‖Ah‖`, `H = g''(1)A†M_wA`, `K = 2C₄ + C₅` at `Γ₃` and `max |w|`; and `‖Ah‖ ≤ 2‖h‖` |
| **`local_convergence_frozen`** | `theo:local_convergence` on the loop closure, at any coercivity constant `B̂ ≥ 1` on `L²(λ)`: the explicit `ε₀`, `C`, `γ₀`; the gradient flow from `(1+h₀)λ` exists, is the gradient, is unique, stays positive and in the window, and converges to a balanced `c_∞λ` at rate `ϱ/2`; gradient descent below `γ₀` is well defined and contracts `‖h_k − Πh_k‖` by `1 − γϱ/4`, `ϱ = g''(1)w_min/B̂²` |
| **`curvature_two_sided_frozen`** | the curvature of `H` transverse to balance and the coercivity constant determine each other: a coercivity constant `B̂` gives the curvature `g''(1)w_min/B̂²`, and a curvature `c > 0` gives the coercivity constant `√(g''(1)w_max/c)`; at the best `B̂` the best curvature lies between `g''(1)w_min/B̂²` and `g''(1)w_max/B̂²` |

## Hypothesis checklist

| paper hypothesis / claim | here |
|---|---|
| loop closure of a finite path-connected marked graph, policy positive on its edges, `λ` its invariant probability | ✓ `[Fintype V]`, `hpc`, `hpos`, `hl : B.IsInvProb lam`; the kernel is `B.phat` |
| `g` `C³` near `1`, `g'(1) = 0 < g''(1)` | ✓ `hC3 : ContDiffOn ℝ 3 g (winC3 a)` on the closed window, `hgd` a derivative of `g` within it, `hg1`, `hg2` |
| `ν = wλ`, `0 ≤ w` bounded | ✓ `ν := λw`; `‖w‖_∞` read as `max |w|` (`supAbsOf`) |
| the linear part `H = g''(1)A†M_wA` | ✓ `Balance.linHess`, with `A = P − I` (`Balance.Aop`) and `A†` its `L²(λ)` adjoint |
| `H` is the only homogeneous linearization | ✗ here; stated for a general kernel by `theo_gd_diffusion_full` |
| the reversible case, `H = g''(1)(I − P)²` | ✗ here: no loop closure of a marked graph is reversible, so the clause is empty on graphs; stated for a general kernel by `theo_gd_diffusion_full` |
| detailed balance, through the edge lift | ✗ here; `theo_gd_diffusion_DB` and `local_convergence_full_DB_paper` for a general kernel |
| a coercivity constant `B̂ ≥ 1` of the backward chain | ✓ `hB1`, `hcoer`; the norm of the Green operator gives the best rate, the hitting-time constant of `prop:morozov_rate` a guaranteed one |

## SCOPE (disclosed)

* **The orientation of the ratio.** The balance ratio of the loop closure at the state mass `μ`
  is `d(μπ̂)/dμ`: with the policy frozen, `μ` is the inflow of each state and `μπ̂` its outflow,
  so `r` is outflow over inflow, the reciprocal of the ratio of the flow-matching loss written
  with inflow over outflow. That loss at generator `g` is this one at the generator `x ↦ g(1/x)`,
  which has the same first two derivatives at `1` when `g'(1) = 0`, and is `(log x)²` again when
  `g` is.
* **The marks.** The loss is summed over every state of the loop closure, the source and the sink
  included: there it compares the flow through the wrap edge with the initial and the terminal
  mass.
* **The constants** are the printed formulas: `Balance.Kexp`, `Balance.eps0W`, `Balance.CW`,
  `Balance.gamma0W`, `Balance.rhoL`, with `Γ₃ = Balance.Gamma3W g a` and `min λ`, `max |w|` the
  actual extrema.
* **Inhabitation** of the hypotheses of `local_convergence_frozen` off balance, at `B̂ := B̂_σ`:
  `MorozovFM.ar_local_convergence_FM_witness` on `s₀ → s_f`.
* **No `sorry`.**

Provenance: mathlib tag `v4.31.0`, pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

open Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : MarkedGraph V}

namespace BackwardPolicy

variable {B : BackwardPolicy G}

/-- **`theo:gd_diffusion`, on a finite marked graph with the backward policy frozen**: on the loop
closure, at the state mass `(1+h)λ` with `|h| ≤ ε ≤ a/4`, the ratio is `1 + Ah/(1+h)`, the loss has
the `L²(λ)` gradient `D(h)` along every direction, and `‖D(h) − Hh‖ ≤ Kε‖Ah‖ ≤ 2Kε‖h‖`,
`H = g''(1)A†M_wA`, `K = 2C₄ + C₅` at `Γ₃` and `max |w|`. -/
theorem gd_diffusion_frozen {lam w h : V → ℝ} {g gd : ℝ → ℝ} {a eps : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (ha : 0 < a) (ha1 : a < 1) (hC3 : ContDiffOn ℝ 3 g (Balance.winC3 a))
    (hgd : ∀ y ∈ Balance.winC3 a, HasDerivWithinAt g (gd y) (Balance.winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (heps0 : 0 < eps) (heps : eps ≤ a / 4) (hh : ∀ x, |h x| ≤ eps) :
    (∀ x, Balance.ratio B.phat lam (fun z => 1 + h z) x - 1
        = Balance.Aop B.phat lam h x / (1 + h x))
    ∧ (∀ d : V → ℝ, HasDerivAt
        (fun t : ℝ => Balance.loss B.phat lam (fun z => lam z * w z)
          (fun x => 1 + h x + t * d x) g)
        (ipL2 lam (Balance.lossGrad B.phat lam (fun z => lam z * w z) gd fun z => 1 + h z) d) 0)
    ∧ nrmL2 lam (fun x =>
        Balance.lossGrad B.phat lam (fun z => lam z * w z) gd (fun z => 1 + h z) x
          - Balance.linHess B.phat lam w (deriv (deriv g) 1) h x)
      ≤ Balance.Kexp (deriv (deriv g) 1) a (Balance.Gamma3W g a) (Balance.supAbsOf w) * eps
          * nrmL2 lam (Balance.Aop B.phat lam h)
    ∧ nrmL2 lam (Balance.Aop B.phat lam h) ≤ 2 * nrmL2 lam h := by
  have hK := (Core.phat_isMarkov B).toIsMarkovOn lam
  have hinv := Core.isInvariant_of_isInvProb B hl
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have heps' : eps ≤ min a 1 / 4 := by rwa [min_eq_left ha1.le]
  have hu : ∀ x, 0 < 1 + h x := fun x => by
    have hx := abs_le.mp (hh x)
    linarith
  refine ⟨fun x => Balance.ratio_one_add_sub_one hinv (hp x).ne' (hu x).ne', fun d => ?_, ?_,
    Balance.nrmL2_Aop_le_two (Core.phat_isMarkov B) hinv h⟩
  · have hgr : ∀ x, HasDerivAt g (gd (Balance.ratio B.phat lam (fun z => 1 + h z) x))
        (Balance.ratio B.phat lam (fun z => 1 + h z) x) := fun x => by
      have hr := Balance.abs_ratio_sub_one_le_two_a_div_three hK.nonneg hinv hh heps0.le heps'
        (hp x).ne'
      have hy : Balance.ratio B.phat lam (fun z => 1 + h z) x ∈ Set.Ioo (1 - a) (1 + a) :=
        ⟨by linarith [(abs_le.mp hr).1], by linarith [(abs_le.mp hr).2]⟩
      exact (hgd _ (Set.Ioo_subset_Icc_self hy)).hasDerivAt (Balance.mem_nhds_winC3 hy)
    exact Balance.hasDerivAt_loss_ipL2_local (nu := fun z => lam z * w z)
      (Balance.invariant_of_isInvariant hinv) hK.nonneg hp hu hgr d
  · have hexp := Balance.gradient_expansion hK hinv hp hg2.le (Balance.Gamma3W_nonneg ha hC3)
      ha.le ((abs_nonneg _).trans (Balance.abs_le_supAbsOf w G.src)) (Balance.abs_le_supAbsOf w)
      (Balance.taylor_bundle_of_C3On ha hC3 hgd hg1) hh heps0.le heps'
    have hA : Balance.Aop B.phat lam (Balance.perpL2 lam h) = Balance.Aop B.phat lam h :=
      funext fun y => Balance.Aop_perpL2 hinv h (hp y).ne'
    rwa [Balance.linHess_perpL2 hinv hp, hA] at hexp

/-- **`theo:local_convergence`, on a finite marked graph with the backward policy frozen**: for the
loop closure and any coercivity constant `B̂ ≥ 1` on `L²(λ)`, the explicit `ε₀`, `C`, `γ₀`; the
gradient flow from `(1+h₀)λ` exists, is the gradient, is unique, stays positive, and converges to
`c_∞λ` at rate `ϱ/2`; gradient descent contracts by `1 − γϱ/4`, `ϱ = g''(1)w_min/B̂²`. -/
theorem local_convergence_frozen {lam w : V → ℝ} {g gd : ℝ → ℝ} {a wmin Bhat : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (Balance.winC3 a))
    (hgd : ∀ y ∈ Balance.winC3 a, HasDerivWithinAt g (gd y) (Balance.winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      nrmL2 lam (Balance.perpL2 lam f) ≤ Bhat * nrmL2 lam (Balance.Aop B.phat lam f)) :
    ((∃ x, lam x = Balance.lamMinOf lam) ∧ (∀ x, Balance.lamMinOf lam ≤ lam x)
        ∧ 1 ≤ Balance.Cinf (Balance.lamMinOf lam))
    ∧ (Balance.eps0W g a wmin (Balance.supAbsOf w) Bhat (Balance.lamMinOf lam)
          ∈ Set.Ioc 0 (a / (16 * Balance.Cinf (Balance.lamMinOf lam)))
        ∧ 1 ≤ Balance.CW g a wmin (Balance.supAbsOf w)
        ∧ 0 < Balance.gamma0W g a wmin (Balance.supAbsOf w) Bhat)
    ∧ ∀ h0 : V → ℝ,
      nrmL2 lam h0 ≤ Balance.eps0W g a wmin (Balance.supAbsOf w) Bhat (Balance.lamMinOf lam) →
      (∃ h : ℝ → V → ℝ, h 0 = h0
        ∧ Balance.IsGradientFlow B.phat lam (fun z => lam z * w z) gd (fun s x => 1 + h s x)
        ∧ (∀ t : ℝ, 0 ≤ t → ∀ d : V → ℝ, HasDerivAt
            (fun s : ℝ => Balance.loss B.phat lam (fun z => lam z * w z)
              (fun x => 1 + h t x + s * d x) g)
            (ipL2 lam (Balance.lossGrad B.phat lam (fun z => lam z * w z) gd
              fun z => 1 + h t z) d) 0)
        ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < 1 + h t x
            ∧ |Balance.ratio B.phat lam (fun z => 1 + h t z) x - 1| ≤ 2 * a / 3)
        ∧ (∀ h' : ℝ → V → ℝ, h' 0 = h0 →
            Balance.IsGradientFlow B.phat lam (fun z => lam z * w z) gd (fun s x => 1 + h' s x) →
            ∀ t : ℝ, 0 ≤ t → h' t = h t)
        ∧ ∃ cinf : ℝ, Balance.Balanced B.phat lam (fun _ => cinf)
            ∧ |cinf - 1 - meanL2 lam h0|
                ≤ Balance.CW g a wmin (Balance.supAbsOf w) * nrmL2 lam (Balance.perpL2 lam h0) ^ 2
            ∧ (∀ t : ℝ, 0 ≤ t → nrmL2 lam (fun x => h t x - (cinf - 1))
                ≤ 2 * Real.exp (-(Balance.rhoL (deriv (deriv g) 1) wmin Bhat * t / 2))
                    * nrmL2 lam (Balance.perpL2 lam h0))
            ∧ Tendsto (fun t => nrmL2 lam (fun x => h t x - (cinf - 1))) atTop (𝓝 0))
      ∧ ∀ gam : ℝ, 0 < gam → gam ≤ Balance.gamma0W g a wmin (Balance.supAbsOf w) Bhat →
        ∀ hk : ℕ → V → ℝ, hk 0 = h0 →
        (∀ k : ℕ, hk (k + 1) = fun x => hk k x
          - gam * Balance.lossGrad B.phat lam (fun z => lam z * w z) gd (fun z => 1 + hk k z) x) →
        ∀ k : ℕ, ((∀ x : V, 0 < 1 + hk k x)
          ∧ (∀ x : V, |Balance.ratio B.phat lam (fun z => 1 + hk k z) x - 1| ≤ 2 * a / 3)
          ∧ ∀ d : V → ℝ, HasDerivAt
              (fun t : ℝ => Balance.loss B.phat lam (fun z => lam z * w z)
                (fun x => 1 + hk k x + t * d x) g)
              (ipL2 lam (Balance.lossGrad B.phat lam (fun z => lam z * w z) gd
                fun z => 1 + hk k z) d) 0)
          ∧ nrmL2 lam (Balance.perpL2 lam (hk (k + 1)))
              ≤ (1 - gam * Balance.rhoL (deriv (deriv g) 1) wmin Bhat / 4)
                  * nrmL2 lam (Balance.perpL2 lam (hk k)) :=
  Balance.local_convergence_full_paper ((Core.phat_isMarkov B).toIsMarkovOn lam)
    (Core.isInvariant_of_isInvProb B hl) (fun x => hl.pos hpc hpos x) hl.total
    ha hC3 hgd hg1 hg2 hwmin0 hwmin hB1 hcoer

/-- **The curvature transverse to balance is of order `1/B̂²`, from both sides.** On the loop
closure of a frozen backward policy, with `H = g''(1)A†M_wA` and `w_min ≤ w ≤ w_max`:
(a) a coercivity constant `B̂` gives the curvature `g''(1)w_min/B̂²`; (b) conversely, a curvature
`c > 0` gives the coercivity constant `√(g''(1)w_max/c)`. So no curvature exceeds
`g''(1)w_max/B̂²` at the best `B̂`, and with `w` constant the two bounds meet. -/
theorem curvature_two_sided_frozen {lam w : V → ℝ} {g2 wmin wsup : ℝ}
    (hl : B.IsInvProb lam) (hwmin : ∀ x, wmin ≤ w x) (hwsup : ∀ x, w x ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hg2 : 0 ≤ g2) :
    (∀ Bhat : ℝ, 0 < Bhat →
        (∀ h : V → ℝ, nrmL2 lam (Balance.perpL2 lam h)
          ≤ Bhat * nrmL2 lam (Balance.Aop B.phat lam h)) →
        ∀ h : V → ℝ, g2 * wmin / Bhat ^ 2 * nrmL2 lam (Balance.perpL2 lam h) ^ 2
          ≤ ipL2 lam h (Balance.linHess B.phat lam w g2 h))
    ∧ (∀ c : ℝ, 0 < c →
        (∀ h : V → ℝ, c * nrmL2 lam (Balance.perpL2 lam h) ^ 2
          ≤ ipL2 lam h (Balance.linHess B.phat lam w g2 h)) →
        ∀ h : V → ℝ, nrmL2 lam (Balance.perpL2 lam h)
          ≤ Real.sqrt (g2 * wsup / c) * nrmL2 lam (Balance.Aop B.phat lam h)) := by
  have hK := Core.phat_isMarkov B
  have hinv := Core.isInvariant_of_isInvProb B hl
  refine ⟨fun Bhat hB hcoer h => ?_, fun c hc hcurv h => ?_⟩
  · have hp0 : 0 ≤ nrmL2 lam (Balance.perpL2 lam h) := nrmL2_nonneg _ _
    have hB2 : 0 < Bhat ^ 2 := pow_pos hB 2
    have hsq : nrmL2 lam (Balance.perpL2 lam h) ^ 2
        ≤ Bhat ^ 2 * nrmL2 lam (Balance.Aop B.phat lam h) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hp0 (hcoer h) 2
    calc g2 * wmin / Bhat ^ 2 * nrmL2 lam (Balance.perpL2 lam h) ^ 2
        ≤ g2 * wmin / Bhat ^ 2 * (Bhat ^ 2 * nrmL2 lam (Balance.Aop B.phat lam h) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (div_nonneg (mul_nonneg hg2 hwmin0) hB2.le)
      _ = g2 * wmin * nrmL2 lam (Balance.Aop B.phat lam h) ^ 2 := by
          rw [div_mul_eq_mul_div, div_eq_iff hB2.ne']
          ring
      _ ≤ ipL2 lam h (Balance.linHess B.phat lam w g2 h) :=
          Balance.linHess_coercive hinv hK.nonneg hwmin hg2 h
  · have hup : ipL2 lam h (Balance.linHess B.phat lam w g2 h)
        ≤ g2 * wsup * nrmL2 lam (Balance.Aop B.phat lam h) ^ 2 := by
      rw [Balance.ipL2_linHess hinv hK.nonneg w g2 h h,
        sq_nrmL2 hinv.nonneg (Balance.Aop B.phat lam h)]
      have hle : ipL2 lam (fun y => w y * Balance.Aop B.phat lam h y) (Balance.Aop B.phat lam h)
          ≤ wsup * ipL2 lam (Balance.Aop B.phat lam h) (Balance.Aop B.phat lam h) := by
        simp only [ipL2, Finset.mul_sum]
        refine Finset.sum_le_sum fun x _ => ?_
        have hrw1 : lam x * (w x * Balance.Aop B.phat lam h x * Balance.Aop B.phat lam h x)
            = (lam x * (Balance.Aop B.phat lam h x * Balance.Aop B.phat lam h x)) * w x := by
          ring
        have hrw2 : wsup * (lam x * (Balance.Aop B.phat lam h x * Balance.Aop B.phat lam h x))
            = (lam x * (Balance.Aop B.phat lam h x * Balance.Aop B.phat lam h x)) * wsup := by
          ring
        rw [hrw1, hrw2]
        exact mul_le_mul_of_nonneg_left (hwsup x)
          (mul_nonneg (hinv.nonneg x) (mul_self_nonneg _))
      calc g2 * ipL2 lam (fun y => w y * Balance.Aop B.phat lam h y) (Balance.Aop B.phat lam h)
          ≤ g2 * (wsup * ipL2 lam (Balance.Aop B.phat lam h) (Balance.Aop B.phat lam h)) :=
            mul_le_mul_of_nonneg_left hle hg2
        _ = g2 * wsup * ipL2 lam (Balance.Aop B.phat lam h) (Balance.Aop B.phat lam h) := by
            ring
    have hsq : nrmL2 lam (Balance.perpL2 lam h) ^ 2
        ≤ g2 * wsup / c * nrmL2 lam (Balance.Aop B.phat lam h) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      exact (mul_comm _ _).trans_le ((hcurv h).trans hup)
    have hA0 : 0 ≤ nrmL2 lam (Balance.Aop B.phat lam h) := nrmL2_nonneg _ _
    have hp0 : 0 ≤ nrmL2 lam (Balance.perpL2 lam h) := nrmL2_nonneg _ _
    calc nrmL2 lam (Balance.perpL2 lam h)
        = Real.sqrt (nrmL2 lam (Balance.perpL2 lam h) ^ 2) := (Real.sqrt_sq hp0).symm
      _ ≤ Real.sqrt (g2 * wsup / c * nrmL2 lam (Balance.Aop B.phat lam h) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (g2 * wsup / c) * nrmL2 lam (Balance.Aop B.phat lam h) := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hA0]

end BackwardPolicy

end GFNBounds.Graph
