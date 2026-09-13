import GFNBounds.Balance.TrainingSpeed
import GFNBounds.Balance.WeightedL2

/-!
# The three downstream theorems, re-read at `B̂_σ`: item *(3)* as a certificate of its own

**`prop:morozov_rate`** — statement `proofs.tex:834–856`, proof `proofs.tex:858–873`;
this file is **item *(3)*** (`proofs.tex:851–856`) and the closing paragraph (`proofs.tex:857`).
Items *(1)* and *(2)* are `GFNBounds/Graph/Morozov.lean` and are consumed, not restated.

> *(3)* consequently every occurrence of `B̂` in Theorems `theo:db_stable_frozen`,
> `theo:local_convergence` and `theo:global_dichotomy` may be replaced by `B̂_σ`: the training
> rate is at least
>
>   `ϱ_σ = g''(1) w_min min_x N(x) / (σ_*² (2 + σ̄))`.
>
> The constant `B̂_σ` is finite without any aperiodicity assumption — on a leveled graph, where
> every trajectory has the same length `t_m` (the autoregressive case), the loop-closed chain is
> periodic and `B̂ = +∞` while `B̂_σ ≤ (t_m+1)√((2+t_m)/min_x N(x))`.

> (proof of *(3)*) Lemma `lem:sigma_mixing` enters the proofs of Theorems
> `theo:db_stable_frozen`, `theo:local_convergence` and `theo:global_dichotomy` only through the
> coercivity inequality `‖h − Πh‖ ≤ B̂‖(I−P)h‖`; item *(2)* provides the same inequality with
> `B̂_σ`, and the substitution propagates verbatim.

## Why this file exists, and what in it is new

`GFNBounds/Graph/Morozov.lean` closed items *(1)* and *(2)* and **declined item *(3)***, on the
stated ground that "none of the three [downstream theorems] is in this library, and `ϱ_σ` is
likewise not stated". Two of the three are now in it —
`theo:db_stable_frozen_full` (`GFNBounds/Balance/WeightedL2.lean`, both halves) and
`theo:local_convergence_full` (`GFNBounds/Balance/LocalConvergence.lean`, closed) — and both take
`B̂` as a *parameter* with the coercivity as an explicit hypothesis, so the paper's "the
substitution propagates verbatim" is, here, literally instantiation.

**Most of the work was already done, in a different place and for a different purpose.**
`GFNBounds/Balance/TrainingSpeed.lean` performed exactly this substitution *inside* the assembly
of `theo:training_speed_full`: `BhatSigma`, `rhoSigma`, `hcoer_of_graph`, `one_le_BhatSigma`,
`rhoL_eq_rhoSigma` and `rhoSigma_eq_visits` are its declarations, and `local_convergence_full` is
invoked there at `Bhat := B̂_σ`. What this file adds is small and is listed honestly:

| | |
|---|---|
| `bhatSigma_eq_visits` | **new** — the bridge between the *two printed forms* of `B̂_σ`: `TrainingSpeed.BhatSigma = σ_*/√λ_min` (`proofs.tex:931`) against item *(2)*'s `σ_*√((2+σ̄)/min N)` (`proofs.tex:849`). Two closed theorems were each stated in one of them and nothing said they were the same constant |
| `rhoSigma_eq_visits'` | **new only in generality** — `TrainingSpeed.rhoSigma_eq_visits` is its `g''(1) = 2` case, which is all `theo:training_speed_full` needed; Theorems 9 and 10 are stated at a general `g''(1)`, and item *(3)*'s `ϱ_σ` prints `g''(1)` |
| `rate_eq_visits` | plumbing: the same equality at the raw `g''(1)w_min/B̂_σ²` the two `WeightedL2` theorems print |
| `stable_frozen_discrete_sigma`, `stable_frozen_decay_sigma` | **new** — `theo:db_stable_frozen_full`'s two halves at `B̂_σ`. `TrainingSpeed` never touches Theorem 9 |
| `hrho_of_step` | **new, and the one non-mechanical step**: `stable_frozen_discrete_finite` carries a side hypothesis `ε ϱ ≤ 1` that neither the paper nor `TrainingSpeed` discharges. At `B̂ = B̂_σ` it is *free*, because `1 ≤ B̂_σ` makes `ϱ_σ ≤ g''(1)w_min ≤ 4g''(1)‖w‖_∞`, so the paper's own step condition implies it |
| `local_convergence_sigma` | **re-exposure** — `theo:local_convergence_full` at `B̂_σ`, stated as its own theorem. `TrainingSpeed.training_speed_full` already invokes it this way, buried in an assembly at `g''(1) = 2`, `a = 1/2`, `M₃ = 24`; here it is the general instantiation and it is quotable |
| `morozov_rate_three` | **new as a statement**, not as mathematics: item *(3)* in one place, the coercivity and the three substituted conclusions together |
| `bsigma_leveled_le` | **the bridge only** — `Morozov.Leveled.bsigma_le` already proves the closing paragraph's bound, in the `σ_*√((2+σ̄)/min N)` form. This restates it at `BhatSigma`, which is the constant the substituted theorems actually consume |
| `ar`, `arPol`, `arLeveled`, `ar_leveled_check` | **new** — the two-vertex leveled graph `s₀ → s_f`, the first inhabitant of `Morozov.Leveled` in this library, with `σ_* = t_m = 1`, `σ̄ = 0`, `N_min = 1` and `B̂_σ = √2` against the leveled bound `2√3` |
| `cycle_morozov_consume_check*` | the constants **evaluated** on `rem:cycle_no_stalemate`'s five-vertex cycle, both forms of `B̂_σ` agreeing at `14√2` |

## Hypothesis checklist — `prop:morozov_rate` *(3)*

| paper hypothesis | here |
|---|---|
| the setting of *(1)*–*(2)*: the loop closure of a **finite** path-connected marked graph, backward policy positive on its edges, `λ` its invariant probability | ✓ `[Fintype V]`, `hpc`, `hpos`, `hl : B.IsInvProb lam`; the kernel is `B.phat` |
| `σ`, `σ̄`, `N` | ⚠ **characterized, not constructed** — `B.IsHitExp uH`, `B.sigmaBar uH`, `B.IsGreen gr`, `visits G gr`, inherited verbatim from `GFNBounds/Graph/Morozov.lean`'s disclosed modelling step. No chain exists in this library |
| "every occurrence of `B̂` in Theorem `theo:db_stable_frozen`" | ✓ **both halves**, `stable_frozen_discrete_sigma` and `stable_frozen_decay_sigma`, at the paper's `ϱ_σ` written out |
| "… in Theorem `theo:local_convergence`" | ✓ `local_convergence_sigma`, at `ϱ_σ/2` in the exponent, `C = C₇` |
| "… in Theorem `theo:global_dichotomy`" | ⚠ **not claimed** — see SCOPE, first bullet |
| `ϱ_σ = g''(1) w_min min N/(σ_*²(2+σ̄))` | ✓ written out in every conclusion below, not abbreviated to a named constant |
| the substitution needs only that item *(2)* "provides the same inequality" | ✓ `TrainingSpeed.hcoer_of_graph` is the only bridge used, and it is `coercivity_lamMin` |
| "`B̂_σ` is finite without any aperiodicity assumption" | ✓ no `Core.Mixing`, no spectral gap, no aperiodicity and no lazification appears in any signature below |
| the leveled bound `B̂_σ ≤ (t_m+1)√((2+t_m)/min N)` | ✓ `bsigma_leveled_le`, from `Morozov.Leveled.bsigma_le`, and inhabited by `arLeveled` |
| "the loop-closed chain is periodic and `B̂ = +∞`" | ⚠ **not stated** — see SCOPE, second bullet |
| `ε ϱ_σ ≤ 1`, a hypothesis of the Lean Theorem 9 that the paper does not write | ⚠ **discharged, not assumed** (`hrho_of_step`) — it follows from the paper's own `ε ≤ (4g''(1)‖w‖_∞)^{-1}` once `1 ≤ B̂_σ` |

## SCOPE (disclosed)

* **`theo:global_dichotomy_full`'s convergence half is NOT claimed here.** The paper's item *(3)*
  names three theorems; this file substitutes into two. `theo:global_dichotomy_full` is `partial`
  in `paper-map.json` — only item *(1)*'s mass identity is closed
  (`GFNBounds/Balance/MassIdentity.lean`) — and its convergence half runs through
  `prop:no_distant_equilibrium`*(3)*, whose compactness/boundary-blow-up/LaSalle layer is not
  formalized anywhere in this library. **What is worth recording is where `B̂` actually occurs in
  that theorem**: nowhere in its statement. It occurs in `prop:no_distant_equilibrium`*(3)*'s
  *proof*, at `‖u − Πu‖ ≤ B̂δ‖u₀‖` and the entry radius `δ₀ := ε₀m₀/(B̂‖u₀‖)`
  (`proofs.tex:813`) — and that construction **is** already carried out at `B̂_σ`, by
  `TrainingSpeed.entry_and_rescale` and `TrainingSpeed.delta0Sq_le_half`. So the substitution
  into Theorem 12 is done for the quantitative entry and undone for the convergence; only the
  latter is missing, and nothing here pretends otherwise.
* **`B̂ = +∞` on a leveled graph is not certified**, mirroring the flag
  `GFNBounds/Graph/Morozov.lean` already raises: the operator-norm layer that would say
  `‖P^n − Π‖ ↛ 0` is `CLAUDE.md`'s obstruction 2. `bsigma_leveled_le` therefore exhibits a
  *finite* `B̂_σ` on the graphs where the paper says `B̂` is infinite, and says nothing about `B̂`.
  The half of the closing paragraph that carries the contrast is thus the half that is missing.
* **The leveled instance is the two-vertex graph `s₀ → s_f`, and nothing larger.**
  `Morozov.Leveled` had no inhabitant anywhere in the library; `ar` supplies one, which is what
  makes `Leveled.bsigma_le` and `bsigma_leveled_le` certified non-vacuous. It is the
  autoregressive case at `t_m = 1` and its loop closure is genuinely periodic, but it is a
  minimal witness, not a family: no statement below is about leveled graphs of arbitrary depth.
* **`theo:local_convergence_full`'s `C ≥ 1` is `C₇`, and may be below `1`** — inherited, with the
  finding recorded in `GFNBounds/Balance/LocalConvergence.lean`. Nothing here repairs it.
* **The linearization of `theo:db_stable_frozen_full` is a hypothesis, not a derivation** —
  inherited from `GFNBounds/Balance/WeightedL2.lean`: the descent recursion and the decay are
  stated for a curve driven by `H = g''(1)A^†M_wA`, which comes from `theo:gd_diffusion_full`.
  Substituting `B̂_σ` for `B̂` changes nothing about that boundary and does not launder it.
* **Finite state space**, as everywhere in `GFNBounds.Graph` and `GFNBounds.Balance`: `∫·dλ` is
  `∑ x, lam x * ·`, and `‖·‖_{L²(λ)}`, `Π` are `Graph.nrmL2`, `Graph.meanL2`.
* **Scaffold placement.** This file is `sorry`-free; it sits in `scaffold/` because graduation is
  the master session's decision (kb 0011), and because certifying a new item of an existing
  label means a `paper-map.json` edit this session does not own.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : MarkedGraph V} {B : BackwardPolicy G}

/-! ### The two printed forms of `B̂_σ` are the same constant

`proofs.tex:849` prints `B̂_σ = σ_*√((2+σ̄)/min_x N(x))` and `proofs.tex:931` prints
`B̂_σ = σ_*/√λ_min`. `Morozov.coercivity_morozov` delivers the first, `Morozov.coercivity_lamMin`
and `TrainingSpeed.BhatSigma` the second, and item *(1)* — `λ_min = min N/(2+σ̄)` — is what makes
them equal. -/

/-- **`B̂_σ = σ_*√((2+σ̄)/min N)`** (`proofs.tex:849`) for the constant
`TrainingSpeed.BhatSigma = σ_*/√λ_min` (`proofs.tex:931`) that the substituted theorems consume.
Pure rearrangement on top of `prop:morozov_rate`*(1)*: no positivity is needed, `Real.sqrt_inv`
and `inv_div` holding unconditionally. -/
theorem bhatSigma_eq_visits {lam gr uH : V → ℝ} (hpc : G.PathConnected)
    (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam) (hg : B.IsGreen gr)
    (hhit : B.IsHitExp uH) :
    Balance.BhatSigma G uH lam
      = sigmaStar G uH * Real.sqrt ((2 + B.sigmaBar uH) / minOver G (visits G gr)) := by
  rw [Balance.BhatSigma, Balance.minOver_lam_eq hpc hpos hl hg hhit, div_eq_mul_inv,
    ← Real.sqrt_inv, inv_div]

/-- **`ϱ_σ = g''(1)w_min min N/(σ_*²(2+σ̄))`** (`proofs.tex:854`), at a general `g''(1)`.
`TrainingSpeed.rhoSigma_eq_visits` is the `g''(1) = 2` case, which is all
`theo:training_speed_full` needed; Theorems 9 and 10 are stated at a general generator. -/
theorem rhoSigma_eq_visits' {lam gr uH : V → ℝ} {g2 wmin : ℝ} (hpc : G.PathConnected)
    (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam) (hg : B.IsGreen gr)
    (hhit : B.IsHitExp uH) :
    Balance.rhoSigma g2 wmin (minOver G lam) (sigmaStar G uH)
      = g2 * wmin * minOver G (visits G gr)
        / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)) := by
  rw [Balance.rhoSigma, Balance.minOver_lam_eq hpc hpos hl hg hhit, ← mul_div_assoc, div_div,
    mul_comm (2 + B.sigmaBar uH)]

/-- The same equality at the raw quotient `g''(1)w_min/B̂_σ²` that `theo:db_stable_frozen_full`'s
two halves print. -/
theorem rate_eq_visits {lam gr uH : V → ℝ} {g2 wmin : ℝ} (hpc : G.PathConnected)
    (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam) (hg : B.IsGreen gr)
    (hhit : B.IsHitExp uH) :
    g2 * wmin / Balance.BhatSigma G uH lam ^ 2
      = g2 * wmin * minOver G (visits G gr)
        / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)) := by
  have h1 : Balance.rhoL g2 wmin (Balance.BhatSigma G uH lam)
      = Balance.rhoSigma g2 wmin (minOver G lam) (sigmaStar G uH) :=
    Balance.rhoL_eq_rhoSigma (minOver_pos fun x => hl.pos hpc hpos x)
  simp only [Balance.rhoL] at h1
  rw [h1, rhoSigma_eq_visits' hpc hpos hl hg hhit]

/-! ### `theo:db_stable_frozen_full` at `B̂_σ` -/

/-- **The side hypothesis `ε ϱ_σ ≤ 1` is free at `B̂_σ`.** `stable_frozen_discrete_finite` asks
for it and the paper writes only `ε ≤ (4g''(1)‖w‖_{L^∞})^{-1}`; since `1 ≤ B̂_σ`
(`TrainingSpeed.one_le_BhatSigma`) we have `ϱ_σ ≤ g''(1)w_min ≤ 4g''(1)‖w‖_{L^∞}`, so the
paper's condition implies it. -/
theorem hrho_of_step {Bhat g2 wmin wsup eps : ℝ} (hB1 : 1 ≤ Bhat) (hg2 : 0 ≤ g2)
    (hwmin0 : 0 ≤ wmin) (hws : wmin ≤ wsup) (heps : 0 ≤ eps)
    (hepsL : eps * (4 * g2 * wsup) ≤ 1) :
    eps * (g2 * wmin / Bhat ^ 2) ≤ 1 := by
  have hwsup0 : 0 ≤ wsup := le_trans hwmin0 hws
  have hB2 : 1 ≤ Bhat ^ 2 := by nlinarith
  have hle1 : g2 * wmin / Bhat ^ 2 ≤ g2 * wmin :=
    div_le_self (mul_nonneg hg2 hwmin0) hB2
  have hle2 : g2 * wmin ≤ g2 * wsup := mul_le_mul_of_nonneg_left hws hg2
  have hgw : 0 ≤ g2 * wsup := mul_nonneg hg2 hwsup0
  have hfour : (4:ℝ) * g2 * wsup = 4 * (g2 * wsup) := by ring
  have hle3 : g2 * wmin / Bhat ^ 2 ≤ 4 * g2 * wsup := by rw [hfour]; linarith
  exact le_trans (mul_le_mul_of_nonneg_left hle3 heps) hepsL

/-- **`theo:db_stable_frozen_full`, the discrete half, at `B̂_σ`** — `prop:morozov_rate`*(3)* for
`theo:db_stable_frozen`. Along `h_{k+1} = h_k − εHh_k` the normalization `Πh_k` is conserved and
`‖h_k^⊥‖` contracts by `1 − εϱ_σ` per step, with

  `ϱ_σ = g''(1) w_min min_x N(x)/(σ_*²(2+σ̄))`

written out. No mixing, spectral-gap or aperiodicity hypothesis appears. -/
theorem stable_frozen_discrete_sigma {lam gr uH wf : V → ℝ} {g2 wmin wsup eps : ℝ}
    {h : ℕ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (heps : 0 ≤ eps) (hepsL : eps * (4 * g2 * wsup) ≤ 1)
    (hstep : ∀ k x, h (k + 1) x = h k x - eps * Balance.linHess B.phat lam wf g2 (h k) x) :
    (∀ k, meanL2 lam (h k) = meanL2 lam (h 0)) ∧
      ∀ k, nrmL2 lam (Balance.perpL2 lam (h k))
        ≤ (1 - eps * (g2 * wmin * minOver G (visits G gr)
              / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)))) ^ k
          * nrmL2 lam (Balance.perpL2 lam (h 0)) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hws : wmin ≤ wsup := le_trans (hwmin G.src) (hwsup G.src)
  have hwsup0 : 0 ≤ wsup := le_trans hwmin0 hws
  have hB1 : 1 ≤ Balance.BhatSigma G uH lam := Balance.one_le_BhatSigma hpc hpos hl hhit
  have hBpos : 0 < Balance.BhatSigma G uH lam := lt_of_lt_of_le zero_lt_one hB1
  have key := Balance.stable_frozen_discrete_finite
    (K := B.phat) (lam := lam) (w := wf) (Bhat := Balance.BhatSigma G uH lam)
    ⟨B.phat_nonneg, B.phat_row_sum⟩ ⟨fun x => (hp x).le, hl.inv⟩ hp hl.total
    hg2 hwmin0 hwmin hwsup hwsup0 hBpos (Balance.hcoer_of_graph hpc hpos hl hhit)
    heps hepsL (hrho_of_step hB1 hg2 hwmin0 hws heps hepsL) hstep
  rwa [rate_eq_visits hpc hpos hl hg hhit] at key

/-- **`theo:db_stable_frozen_full`, the continuous half, at `B̂_σ`.** Along `ḣ = −Hh` the
normalization is conserved and `‖h_t^⊥‖ ≤ e^{−ϱ_σ t}‖h_0^⊥‖`, with `ϱ_σ` written out. -/
theorem stable_frozen_decay_sigma {lam gr uH wf : V → ℝ} {g2 wmin : ℝ} {h : ℝ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ wf x)
    (hflow : ∀ t : ℝ, HasDerivAt h (fun x => -(Balance.linHess B.phat lam wf g2 (h t) x)) t) :
    (∀ t : ℝ, meanL2 lam (h t) = meanL2 lam (h 0)) ∧
      ∀ t : ℝ, 0 ≤ t → nrmL2 lam (Balance.perpL2 lam (h t))
        ≤ Real.exp (-(g2 * wmin * minOver G (visits G gr)
              / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)) * t))
          * nrmL2 lam (Balance.perpL2 lam (h 0)) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hB1 : 1 ≤ Balance.BhatSigma G uH lam := Balance.one_le_BhatSigma hpc hpos hl hhit
  have hBpos : 0 < Balance.BhatSigma G uH lam := lt_of_lt_of_le zero_lt_one hB1
  have key := Balance.stable_frozen_decay_finite
    (K := B.phat) (lam := lam) (w := wf) (Bhat := Balance.BhatSigma G uH lam)
    ⟨fun x => (hp x).le, hl.inv⟩ B.phat_nonneg hp hl.total hg2 hwmin0 hwmin hBpos
    (Balance.hcoer_of_graph hpc hpos hl hhit) hflow
  rwa [rate_eq_visits hpc hpos hl hg hhit] at key

/-! ### `theo:local_convergence_full` at `B̂_σ` -/

/-- **`theo:local_convergence_full` at `B̂_σ`** — `prop:morozov_rate`*(3)* for
`theo:local_convergence`, stated on its own rather than inside an assembly. From every
`μ₀ = (1+h₀)λ` with `‖h₀‖ ≤ ε₀` (the paper's `ε₀`, read at `B̂_σ` and `C_∞ = λ_min^{−1/2}`) the
nonlinear gradient flow converges to a balanced `c_∞λ` at rate `ϱ_σ/2`, with `ϱ_σ` written out.

`TrainingSpeed.training_speed_full` already invokes `local_convergence_full` at `B̂_σ`, but only
at `g''(1) = 2`, `a = 1/2`, `M₃ = 24` and inside its own conclusion; this is the general
instantiation. -/
theorem local_convergence_sigma {lam gr uH wf : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |wf x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ wf x)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hflow : Balance.IsGradientFlow B.phat lam (fun z => lam z * wf z) gd fun s x => 1 + h s x)
    (hnorm0 : nrmL2 lam (h 0)
      ≤ Balance.eps0
          (Balance.epsW a g2 wmin (Balance.Kexp g2 a M3 wsup) (Balance.BhatSigma G uH lam))
          (Balance.Cinf (minOver G lam))
          (Balance.C7 (Balance.C6 (Balance.Cg g2 a M3) wsup) g2 wmin)
          (Balance.rhoL g2 wmin (Balance.BhatSigma G uH lam))
          (Balance.C6 (Balance.Cg g2 a M3) wsup)) :
    ∃ cinf : ℝ,
      |cinf - 1 - meanL2 lam (h 0)|
          ≤ Balance.C7 (Balance.C6 (Balance.Cg g2 a M3) wsup) g2 wmin
            * nrmL2 lam (Balance.perpL2 lam (h 0)) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → nrmL2 lam (fun x => h t x - (cinf - 1))
            ≤ 2 * Real.exp (-(g2 * wmin * minOver G (visits G gr)
                    / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)) * t / 2))
                * nrmL2 lam (Balance.perpL2 lam (h 0)) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hB1 : 1 ≤ Balance.BhatSigma G uH lam := Balance.one_le_BhatSigma hpc hpos hl hhit
  obtain ⟨cinf, hc, hdecay⟩ := Balance.local_convergence_full
    (K := B.phat) (lam := lam) (w := wf) (gd := gd) (h := h)
    (g2 := g2) (a := a) (M3 := M3) (wsup := wsup) (wmin := wmin)
    (Bhat := Balance.BhatSigma G uH lam) (lamMin := minOver G lam)
    ⟨B.phat_nonneg, fun {x} _ => B.phat_row_sum x⟩ ⟨fun x => (hp x).le, hl.inv⟩ hp hl.total
    (minOver_pos hp) (fun x => minOver_le lam x) hg2 hM3 ha hwsup hwmin0 hwmin hB1
    (Balance.hcoer_of_graph hpc hpos hl hhit) htaylor hflow hnorm0
  refine ⟨cinf, hc, ?_⟩
  simp only [Balance.rhoL] at hdecay
  rwa [rate_eq_visits hpc hpos hl hg hhit] at hdecay

/-! ### Item *(3)*, as one statement -/

/-- **`prop:morozov_rate`*(3)*** (`proofs.tex:851–856`): the coercivity at `B̂_σ` in both of the
paper's printed forms, and the substitution carried out in the two downstream theorems this
library has — `theo:db_stable_frozen_full` (both halves) and `theo:local_convergence_full` — at
the training rate

  `ϱ_σ = g''(1) w_min min_x N(x)/(σ_*²(2+σ̄))`.

**What this does not cover.** The paper names a third theorem, `theo:global_dichotomy`. Its
convergence half is not in this library — `theo:global_dichotomy_full` is `partial`, only item
*(1)*'s mass identity being closed — and it is not claimed here. `B̂` does not occur in that
theorem's statement at all; it occurs in `prop:no_distant_equilibrium`*(3)*'s proof, in the entry
radius `δ₀ = ε₀m₀/(B̂‖u₀‖)`, and *that* substitution is already carried out at `B̂_σ` by
`TrainingSpeed.entry_and_rescale`. What is missing is the compactness/LaSalle layer, not the
substitution. See the module SCOPE. -/
theorem morozov_rate_three {lam gr uH wf : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup wmin eps : ℝ} {hd : ℕ → V → ℝ} {hc : ℝ → V → ℝ} {h : ℝ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |wf x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ wf x)
    (heps : 0 ≤ eps) (hepsL : eps * (4 * g2 * wsup) ≤ 1)
    (hstep : ∀ k x, hd (k + 1) x = hd k x - eps * Balance.linHess B.phat lam wf g2 (hd k) x)
    (hcflow : ∀ t : ℝ, HasDerivAt hc (fun x => -(Balance.linHess B.phat lam wf g2 (hc t) x)) t)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hflow : Balance.IsGradientFlow B.phat lam (fun z => lam z * wf z) gd fun s x => 1 + h s x)
    (hnorm0 : nrmL2 lam (h 0)
      ≤ Balance.eps0
          (Balance.epsW a g2 wmin (Balance.Kexp g2 a M3 wsup) (Balance.BhatSigma G uH lam))
          (Balance.Cinf (minOver G lam))
          (Balance.C7 (Balance.C6 (Balance.Cg g2 a M3) wsup) g2 wmin)
          (Balance.rhoL g2 wmin (Balance.BhatSigma G uH lam))
          (Balance.C6 (Balance.Cg g2 a M3) wsup)) :
    -- the constant, in the two printed forms, and `1 ≤ B̂_σ`
    (Balance.BhatSigma G uH lam
        = sigmaStar G uH * Real.sqrt ((2 + B.sigmaBar uH) / minOver G (visits G gr)))
      ∧ 1 ≤ Balance.BhatSigma G uH lam
      -- item *(2)*, in the form the three theorems consume
      ∧ (∀ f : V → ℝ, nrmL2 lam (Balance.perpL2 lam f)
          ≤ Balance.BhatSigma G uH lam * nrmL2 lam (Balance.Aop B.phat lam f))
      -- `theo:db_stable_frozen_full`, discrete half, at `ϱ_σ`
      ∧ ((∀ k, meanL2 lam (hd k) = meanL2 lam (hd 0)) ∧
          ∀ k, nrmL2 lam (Balance.perpL2 lam (hd k))
            ≤ (1 - eps * (g2 * wmin * minOver G (visits G gr)
                  / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)))) ^ k
              * nrmL2 lam (Balance.perpL2 lam (hd 0)))
      -- `theo:db_stable_frozen_full`, continuous half, at `ϱ_σ`
      ∧ ((∀ t : ℝ, meanL2 lam (hc t) = meanL2 lam (hc 0)) ∧
          ∀ t : ℝ, 0 ≤ t → nrmL2 lam (Balance.perpL2 lam (hc t))
            ≤ Real.exp (-(g2 * wmin * minOver G (visits G gr)
                  / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)) * t))
              * nrmL2 lam (Balance.perpL2 lam (hc 0)))
      -- `theo:local_convergence_full`, at `ϱ_σ/2`
      ∧ ∃ cinf : ℝ,
          |cinf - 1 - meanL2 lam (h 0)|
              ≤ Balance.C7 (Balance.C6 (Balance.Cg g2 a M3) wsup) g2 wmin
                * nrmL2 lam (Balance.perpL2 lam (h 0)) ^ 2
            ∧ ∀ t : ℝ, 0 ≤ t → nrmL2 lam (fun x => h t x - (cinf - 1))
                ≤ 2 * Real.exp (-(g2 * wmin * minOver G (visits G gr)
                        / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)) * t / 2))
                    * nrmL2 lam (Balance.perpL2 lam (h 0)) :=
  ⟨bhatSigma_eq_visits hpc hpos hl hg hhit,
    Balance.one_le_BhatSigma hpc hpos hl hhit,
    Balance.hcoer_of_graph hpc hpos hl hhit,
    stable_frozen_discrete_sigma hpc hpos hl hg hhit hg2.le hwmin0.le hwmin
      (fun x => le_of_abs_le (hwsup x)) heps hepsL hstep,
    stable_frozen_decay_sigma hpc hpos hl hg hhit hg2.le hwmin0.le hwmin hcflow,
    local_convergence_sigma hpc hpos hl hg hhit hg2 hM3 ha hwsup hwmin0 hwmin htaylor hflow
      hnorm0⟩

/-! ### The closing paragraph: the leveled graph -/

/-- **`B̂_σ ≤ (t_m+1)√((2+t_m)/min_x N(x))` on a leveled graph** (`proofs.tex:857`), for the
constant `TrainingSpeed.BhatSigma` that the substituted theorems consume, with `t_m := ℓ(s_f)`.

`Morozov.Leveled.bsigma_le` is the bound; all this adds is `bhatSigma_eq_visits`, which says the
quantity it bounds is the one Theorems 9 and 10 are read at. **The other half of the paper's
sentence — that `B̂ = +∞` there, the loop-closed chain being periodic — is not certified**; see
the module SCOPE. -/
theorem bsigma_leveled_le {lam gr : V → ℝ} (L : Leveled G) (hpc : G.PathConnected)
    (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam) (hg : B.IsGreen gr) :
    Balance.BhatSigma G L.lvl lam
      ≤ (L.lvl G.snk + 1) * Real.sqrt ((2 + L.lvl G.snk) / minOver G (visits G gr)) := by
  have hhit : B.IsHitExp L.lvl := L.isHitExp
  rw [bhatSigma_eq_visits hpc hpos hl hg hhit]
  exact L.bsigma_le (B := B) hpc
    (minOver_pos fun x => hg.visits_pos hpc hpos hl hhit x)

/-! ### A leveled instance: the two-vertex autoregressive graph

`Morozov.Leveled` has no inhabitant anywhere in the strict library, so `Leveled.bsigma_le` and
`bsigma_leveled_le` were uncertified against vacuity. The smallest leveled graph is `s₀ → s_f`:
one generation step, the autoregressive case at `t_m = 1`. Its loop closure is the swap
`s₀ ↔ s_f`, **periodic of period 2** — exactly the situation the closing paragraph cites.

Computed by hand first: `λ = (1/2,1/2)`; the hitting time is the height, `σ = (0,1)`, so
`σ_* = 1 = t_m` and `σ̄ = 0 = t_m − 1`; the killed occupation measure is `0`, so `N ≡ 1`,
`N_min = 1` and `2 + σ̄ = 2`, and `λ_min = N_min/(2+σ̄) = 1/2` checks. Hence
`B̂_σ = σ_*/√λ_min = √2 ≈ 1.414`, against the paper's leveled bound
`(t_m+1)√((2+t_m)/N_min) = 2√3 ≈ 3.464`.

**That `B̂ = +∞` here is not certified** — the operator-norm layer is obstruction 2; see the
module SCOPE. What is certified is a graph carrying a finite `B̂_σ`, with no aperiodicity
hypothesis available anywhere. -/

section LeveledExample

/-- The single edge `s₀ → s_f`. -/
def arEdgeB : Fin 2 → Fin 2 → Bool
  | 0, 1 => true
  | _, _ => false

/-- The edge relation of the two-vertex graph, as a decidable `Prop`. -/
def ArEdge (x y : Fin 2) : Prop := arEdgeB x y = true

instance : DecidableRel ArEdge := fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- **The smallest leveled marked graph**: `𝒱 = {s₀, s_f}` with the single edge `s₀ → s_f`. -/
def ar : MarkedGraph (Fin 2) where
  Edge := ArEdge
  src := 0
  snk := 1
  src_ne_snk := by decide
  no_edge_into_src := by decide
  no_edge_out_of_snk := by decide

/-- The two-vertex graph is path-connected. -/
theorem arPathConnected : ar.PathConnected := by
  have e01 : ar.Edge 0 1 := rfl
  intro s
  fin_cases s
  · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.single e01⟩
  · exact ⟨Relation.ReflTransGen.single e01, Relation.ReflTransGen.refl⟩

/-- `π_←(s_f → s₀) = 1`: the only row the backward policy constrains. -/
noncomputable def arPb : Fin 2 → Fin 2 → ℝ
  | 1, 0 => 1
  | _, _ => 0

/-- The backward policy of the two-vertex graph. -/
noncomputable def arPol : BackwardPolicy ar where
  pb := arPb
  nonneg := by
    intro s s'
    fin_cases s <;> fin_cases s' <;> norm_num [arPb]
  row_sum := by
    intro s hs
    fin_cases s <;> simp_all [Fin.sum_univ_two, arPb, ar]
  supp := by
    intro s s' hs hne
    fin_cases s <;> fin_cases s' <;> simp_all [arPb, ar, ArEdge, arEdgeB]

/-- The policy is positive on the single edge. -/
theorem arPositiveOnEdges : arPol.PositiveOnEdges := by
  intro s s' h
  fin_cases s <;> fin_cases s' <;> simp_all [arPol, arPb, ar, ArEdge, arEdgeB]

/-- The loop-closed kernel: the swap `s₀ ↔ s_f`, whose square is the identity. -/
noncomputable def arKern : Fin 2 → Fin 2 → ℝ
  | 0, 1 => 1
  | 1, 0 => 1
  | _, _ => 0

/-- **`def:loop_closure` on the two-vertex graph**: `π̂_←` is the swap. -/
theorem arPhat_eq : arPol.phat = arKern := by
  funext s s'
  fin_cases s <;> fin_cases s' <;> rfl

/-- The height `ℓ = (0,1)`, so `t_m = ℓ(s_f) = 1`. -/
def arLvl : Fin 2 → ℝ
  | 0 => 0
  | 1 => 1

/-- **The two-vertex graph is leveled**, at `t_m = 1`. -/
def arLeveled : Leveled ar where
  lvl := arLvl
  lvl_src := rfl
  lvl_edge := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [ar, ArEdge, arEdgeB, arLvl]

/-- The invariant probability `λ = (1/2, 1/2)`. -/
noncomputable def arLam : Fin 2 → ℝ := fun _ => 1 / 2

theorem arIsInvProb : arPol.IsInvProb arLam := by
  refine ⟨fun x => by norm_num [arLam], by norm_num [Fin.sum_univ_two, arLam], fun y => ?_⟩
  rw [arPhat_eq]
  fin_cases y <;> norm_num [Fin.sum_univ_two, arLam, arKern]

/-- The killed occupation measure is `0`, so `N ≡ 1`. -/
def arGreen : Fin 2 → ℝ := fun _ => 0

theorem arIsGreen : arPol.IsGreen arGreen := by
  refine ⟨rfl, fun y hy => ?_⟩
  rw [BackwardPolicy.densMap_apply, arPhat_eq]
  fin_cases y
  · exact absurd rfl hy
  · norm_num [Fin.sum_univ_two, arGreen, arKern, ar]

theorem ar_minOver_lam : minOver ar arLam = 1 / 2 :=
  le_antisymm (minOver_le _ 0) (le_minOver fun _ => le_rfl)

theorem ar_minOver_visits : minOver ar (visits ar arGreen) = 1 := by
  refine le_antisymm (le_of_le_of_eq (minOver_le _ 0) ?_) (le_minOver fun x => ?_)
  · norm_num [visits, arGreen, ar]
  · fin_cases x <;> norm_num [visits, arGreen, ar]

/-- **The closing paragraph, on an instance.** On the two-vertex leveled graph `σ_* = t_m = 1`,
`σ̄ = t_m − 1 = 0`, `N_min = 1` and `B̂_σ = √2`, comfortably inside the paper's leveled bound
`(t_m+1)√((2+t_m)/N_min) = 2√3`. The chain is the swap, hence periodic; that `B̂ = +∞` is not
certified here. -/
theorem ar_leveled_check :
    sigmaStar ar arLeveled.lvl = 1
      ∧ arPol.sigmaBar arLeveled.lvl = 0
      ∧ minOver ar (visits ar arGreen) = 1
      ∧ Balance.BhatSigma ar arLeveled.lvl arLam = Real.sqrt 2
      ∧ Balance.BhatSigma ar arLeveled.lvl arLam
          ≤ (arLeveled.lvl ar.snk + 1)
            * Real.sqrt ((2 + arLeveled.lvl ar.snk) / minOver ar (visits ar arGreen)) := by
  have hsnk : arLeveled.lvl ar.snk = 1 := rfl
  have hsig : sigmaStar ar arLeveled.lvl = 1 := by
    rw [arLeveled.sigmaStar_eq arPathConnected, hsnk]
  have hbar : arPol.sigmaBar arLeveled.lvl = 0 := by
    rw [arLeveled.sigmaBar_eq (B := arPol), hsnk]; norm_num
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
    rw [show (1:ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have hB : Balance.BhatSigma ar arLeveled.lvl arLam = Real.sqrt 2 := by
    rw [Balance.BhatSigma, hsig, ar_minOver_lam, hs2]
    field_simp
    linarith [h2]
  exact ⟨hsig, hbar, ar_minOver_visits, hB,
    bsigma_leveled_le arLeveled arPathConnected arPositiveOnEdges arIsInvProb arIsGreen⟩

end LeveledExample

/-! ### The five-vertex cycle: both forms of `B̂_σ`, and `ϱ_σ`, evaluated

`GFNBounds/Graph/CycleExample.lean`'s `rem:cycle_no_stalemate` graph. Computed by hand first, at
`p = 1/2`: `λ = (1/8, 1/4, 1/4, 1/4, 1/8)` so `λ_min = 1/8`; `σ_* = (4−p)/(1−p) = 7`;
`σ̄ = 3/(1−p) = 6`, so `2+σ̄ = 8`; `N_min = 1`, and `λ_min = N_min/(2+σ̄)` checks. The two printed
forms then give the **same** number: `σ_*/√λ_min = 7/√(1/8) = 14√2` and
`σ_*√((2+σ̄)/N_min) = 7√8 = 14√2 ≈ 19.80`. At `g''(1) = 2`, `w_min = 1`,
`ϱ_σ = 2·1·1/(49·8) = 1/196`, and at the paper's largest admissible step
`ε = (4g''(1)‖w‖_{L^∞})^{-1} = 1/8` the per-step contraction factor is
`1 − εϱ_σ = 1567/1568`. -/

section CycleCheck

open CycleExample

/-- **Both printed forms of `B̂_σ`, and `ϱ_σ`, on the cycle in closed form in `p`.** The first
conjunct is `bhatSigma_eq_visits` instantiated, the second evaluates it against
`CycleExample.bSigma_eq`, and the third is item *(3)*'s printed `ϱ_σ` at `g''(1) = 2`,
`w_min = 1` — which agrees with `TrainingSpeed.cycle_training_speed_check`'s
`2(1−p)³/((5−2p)(4−p)²)`, computed there from the `σ_*/√λ_min` form. -/
theorem cycle_morozov_consume_check {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Balance.BhatSigma cyc (hitExp p) (lam p)
        = sigmaStar cyc (hitExp p)
            * Real.sqrt ((2 + (pol hp0 hp1).sigmaBar (hitExp p))
              / minOver cyc (visits cyc (green p)))
      ∧ Balance.BhatSigma cyc (hitExp p) (lam p)
          = (4 - p) / (1 - p) * Real.sqrt ((5 - 2 * p) / (1 - p))
      ∧ 2 * 1 * minOver cyc (visits cyc (green p))
            / (sigmaStar cyc (hitExp p) ^ 2 * (2 + (pol hp0 hp1).sigmaBar (hitExp p)))
          = 2 * (1 - p) ^ 3 / ((5 - 2 * p) * (4 - p) ^ 2) := by
  have h1 : (0:ℝ) < 1 - p := by linarith
  have hbridge := bhatSigma_eq_visits (B := pol hp0 hp1) pathConnected
    (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1) (isGreen hp0 hp1) (isHitExp hp0 hp1)
  refine ⟨hbridge, hbridge.trans (bSigma_eq hp0 hp1), ?_⟩
  rw [minOver_visits_eq hp0 hp1, sigmaStar_eq hp0 hp1, two_add_sigmaBar_eq hp0 hp1]
  field_simp

/-- **The numbers at `p = 1/2`.** `B̂_σ = 14√2` in both printed forms, `ϱ_σ = 1/196`, and the
discrete contraction factor at the paper's maximal step `ε = 1/8` is `1567/1568`. The first
conjunct is `TrainingSpeed.cycle_training_speed_check_half`, reused. -/
theorem cycle_morozov_consume_check_half :
    Balance.BhatSigma cyc (hitExp (1/2)) (lam (1/2)) = 14 * Real.sqrt 2
      ∧ (4 - (1/2:ℝ)) / (1 - 1/2) * Real.sqrt ((5 - 2 * (1/2)) / (1 - 1/2))
          = 14 * Real.sqrt 2
      ∧ 2 * (1 - (1/2:ℝ)) ^ 3 / ((5 - 2 * (1/2)) * (4 - (1/2)) ^ 2) = 1/196
      ∧ (1:ℝ) - (1/8) * (1/196) = 1567/1568 := by
  have hp0 : (0:ℝ) < 1/2 := by norm_num
  have hp1 : (1:ℝ)/2 < 1 := by norm_num
  have hB : Balance.BhatSigma cyc (hitExp (1/2)) (lam (1/2)) = 14 * Real.sqrt 2 :=
    Balance.cycle_training_speed_check_half.2.2.2.1
  refine ⟨hB, ?_, by norm_num, by norm_num⟩
  rw [← (cycle_morozov_consume_check hp0 hp1).2.1, hB]

end CycleCheck

end GFNBounds.Graph

