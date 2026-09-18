import GFNBounds.Graph.MorozovConsume
import GFNBounds.Balance.TrainingSpeedAssembled

/-!
# The flow-matching half of item *(3)* with `C³` on the window and the flow proved to exist

**`prop:morozov_rate`** — statement `proofs.tex:930–953`, proof `proofs.tex:955–972` (draft commit
`3194054`; the label is the anchor, kb 0036). This file is the **flow-matching sentence of item
*(3)*** read through `theo:local_convergence_full` in its strongest library form — `g` `C³` on the
closed window only, and the nonlinear gradient flow **proved to exist** rather than hypothesised.
It mirrors `GFNBounds/Graph/MorozovDB.lean`'s `local_convergence_full_DB_sigma` /
`local_convergence_gd_DB_sigma` for the detailed-balance half. Items *(1)*, *(2)* are
`Morozov.lean`, the flow-matching half of *(3)* is `MorozovConsume.lean` (`one_le_BhatSigma`,
`hcoer_of_graph`, `rate_eq_visits`, `local_convergence_sigma`); all are consumed, none restated.
The row is closed in A without this file: it is **support**, and its purpose is kb 0025 — it
inhabits the flow-matching flow hypothesis of `local_convergence_sigma` from an unbalanced start.

> *(3)* `B̂_σ ≥ 1`; hence, for the flow-matching loss on `Ĝ`, `B̂ := B̂_σ` meets the hypothesis of
> Theorems `theo:db_stable_frozen_full` and `theo:local_convergence_full` and of Proposition
> `prop:no_distant_equilibrium`*(3)* — a constant `B̂ ≥ 1` satisfying `eq:coercivity` for the
> backward chain — and the rate `ϱ` of those theorems is then
> `ϱ_σ = g''(1) w_min min_x N(x) / (σ_*² (2 + σ̄))`.

## What is proved

| | |
|---|---|
| **`local_convergence_sigma_C3On`** | `theo:local_convergence_full`, flow clause, for the FM loss on the loop closure at `B̂ := B̂_σ`, `λ_min := min λ`: from every `h₀` with `‖h₀‖_{L²(λ)} ≤ ε₀` the gradient flow **exists**, is unique on `[0,∞)`, stays in the window, and converges to a balanced `c_∞λ` at rate `ϱ_σ/2`, `ϱ_σ` in the printed form (via `rate_eq_visits`) |
| **`local_convergence_gd_sigma_C3On`** | the descent clause at the same constants: well defined at every step, contraction `1 − γϱ_σ/4` of `‖h_k − Πh_k‖` |
| `arEps0FM`, `arEps0FM_pos`, `arSnkInd` | the radius `ε₀` on `s₀ → s_f` at `g = (log x)²`, `a = 1/2`, `w ≡ 1`, and its positivity |
| **`ar_local_convergence_FM_witness`** | inhabitation off balance: on `MorozovConsume.ar`, from `h₀ = ε₀𝟙_{s_f}` (whose centred part has positive norm) the flow exists and converges at rate `ϱ_σ/2 = 1/2` |

## Hypothesis checklist

| paper hypothesis / claim | here |
|---|---|
| loop closure of a finite path-connected marked graph, policy positive on its edges, `λ` its invariant probability | ✓ `[Fintype V]`, `hpc`, `hpos`, `hl : B.IsInvProb lam`; the kernel is `B.phat` |
| `σ`, `σ̄`, `N` | ⚠ **characterized, not constructed** (`IsHitExp uH`, `sigmaBar`, `IsGreen gr`, `visits`), inherited from `Morozov.lean` |
| `B̂ := B̂_σ ≥ 1` meets `eq:coercivity` | ✓ consumed: `Balance.one_le_BhatSigma`, `Balance.hcoer_of_graph` |
| `g` `C³` near `1`, `g'(1) = 0`, `g''(1) > 0` | ✓ `hC3 : ContDiffOn ℝ 3 g (winC3 a)` on the closed window, one-sided at `1 ± a`; `hgd` a derivative of `g` within the window; `hg1`, `hg2` |
| `ν = wλ`, `w ≥ w_min > 0`, `‖w‖_∞` | ✓ `hwmin0`, `hwmin`; `‖w‖_∞` read as a bound `wsup` (`hwsup`) |
| the radius `ε₀`, read at `λ_min` | ✓ `Balance.eps0W g a wmin wsup B̂_σ (min λ)` |
| the step `γ₀` | ✓ `Balance.gamma0W g a wmin wsup B̂_σ`, no `λ_min` (as in `MorozovDB.lean`'s finding) |
| the rate `ϱ_σ` | ✓ written out in the printed form |
| the gradient flow | ✓ **proved to exist**, uniquely on `[0,∞)` (`TrainingSpeedAssembled.local_convergence_full_exists`) |

## SCOPE (disclosed)

* **Support, not a new claim.** The row is closed in A by `MorozovConsume.lean`; this file restates
  nothing the paper says beyond it. What it adds is the instantiation of the two strongest
  `theo:local_convergence_full` forms of `TrainingSpeedAssembled.lean` at `B̂ := B̂_σ` — `C³` only on
  the window instead of a Taylor hypothesis, and **existence** of the flow proved — and one
  unbalanced start at which the flow hypothesis is met.
* **Inherited readings**: `IsGradientFlow` asks the ODE for `t ≥ 0` with a two-sided derivative at
  `0` (`Balance/Flow.lean`, repaired 2026-09-13); `logSqDeriv` is `2 log x / x`, tied to `logSq` by
  `Balance.hasDerivAt_logSq`; `σ`, `σ̄`, `N` as in `Morozov.lean`.
* **No `sorry`.**

## Inhabitation (kb 0025)

`ar_local_convergence_FM_witness` meets every hypothesis of `local_convergence_sigma_C3On` on
`s₀ → s_f`, at `g = (log x)²` (`Balance.logSq_C3On_bundle`), `a = 1/2`, `w ≡ 1`, from
`h₀ = ε₀𝟙_{s_f}`, whose centred part is not zero — so the flow it produces starts off balance.
The descent clause's recursion `hstep` is inhabited by definition.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : MarkedGraph V} {B : BackwardPolicy G}

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
