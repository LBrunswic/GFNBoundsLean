import GFNBounds.Graph.MorozovConsume
import GFNBounds.Balance.LiftFinite
import GFNBounds.Balance.TrainingSpeedAssembled

/-!
# The detailed-balance half of item *(3)*, and an infinite mixing sum on leveled graphs

**`prop:morozov_rate`** — statement `proofs.tex:930–953`, proof `proofs.tex:955–972` (draft commit
`3194054`). This file is the **detailed-balance sentence of item *(3)*** (`proofs.tex:950`), with its
proof (`proofs.tex:969`, last two sentences), and the **leveled-graph half of the closing
paragraph** (`proofs.tex:952`), with its proof (`proofs.tex:971`). Items *(1)*, *(2)* are
`GFNBounds/Graph/Morozov.lean`; the flow-matching half of *(3)* is
`GFNBounds/Graph/MorozovConsume.lean`; `lem:lift_coercivity` is `GFNBounds/Balance/LiftFinite.lean`.
All are consumed, none restated.

> *(3)* […] For the detailed-balance loss, `B̂ := 1 + B̂_σ` meets the hypothesis of the same two
> theorems [`theo:db_stable_frozen_full` and `theo:local_convergence_full`] for `T = K₂`, the edge
> lift of `π̂_←` (Definition `def:edge_lift`), with `λ₂` in place of `λ`, and their rate is then
> `g''(1)w_min/(1+B̂_σ)²`; the radius and the step of Theorem `theo:local_convergence_full` still
> depend on `min_E λ₂`, through `C_∞`.
>
> The constant `B̂_σ` is finite without any aperiodicity assumption: on a leveled graph, where
> every trajectory has the same length `t_m` (the autoregressive case), the loop-closed chain is
> periodic and the mixing sum `∑_{n≥0}‖P^n − Π‖_{L²(λ)}` is `+∞`, while
> `B̂_σ ≤ (t_m+1)√((2+t_m)/min_x N(x))`.

> (proof) For the detailed-balance loss, Lemma `lem:lift_coercivity` with `C := B̂_σ`, whose
> hypothesis for `π̂_←` is *(2)*, shows that `1 + B̂_σ`, which is at least `1`, satisfies
> `eq:coercivity` for `K₂` on `L²(λ₂)`, and `g''(1)w_min/(1+B̂_σ)²` is the corresponding rate by
> definition.
>
> *The last assertion.* On a leveled graph all excursions have length exactly `t_m+2`, so the
> chain is periodic of period `t_m+2` and `‖P^n − Π‖` does not tend to `0`, whence the mixing sum
> is `+∞`; while `σ ≤ t_m` deterministically on the graph's states and `σ(s_f) ≤ t_m+1`, so
> `σ_* ≤ t_m+1` and `σ̄ ≤ t_m`.

## What is proved

| | |
|---|---|
| `one_le_one_add_BhatSigma`, `hcoer_edge_of_graph` | `1 ≤ 1 + B̂_σ`, and `eq:coercivity` for `K₂` on `L²(λ₂)` over `E` at `1 + B̂_σ` — `LiftFinite.lift_coercivity_edgeSupport` at `C := B̂_σ`, its hypothesis `TrainingSpeed.hcoer_of_graph` (item *(2)*) |
| `edge_setting`, `wrapEdge`, `lamMinE`, `lamMinE_le`, `lamMinE_pos` | on the loop closure, `K₂` is Markov on `E`, `λ₂` invariant, positive, a probability; `E ∋ (s_f,s₀)` is non-empty, so `min_E λ₂` exists and is positive |
| **`morozov_rate_three_DB`** | the DB sentence as one statement: `1 + B̂_σ` in item *(2)*'s printed form, `≥ 1`, coercive for `K₂`, and the setting facts the two theorems take — `K₂` Markov and **irreducible** on `E`, `λ₂` an invariant positive probability, `0 < min_E λ₂` |
| **`stable_frozen_discrete_DB_sigma`**, **`stable_frozen_decay_DB_sigma`** | `theo:db_stable_frozen_full`, both halves, for `T = K₂` on `E`, `λ₂`, rate `g''(1)w_min/(1+B̂_σ)²` written out; the Lean side condition `εϱ ≤ 1` discharged by `MorozovConsume.hrho_of_step` |
| **`local_convergence_full_DB_sigma`**, **`local_convergence_gd_DB_sigma`** | `theo:local_convergence_full`, flow and descent clauses, for the DB loss at `B̂ = 1 + B̂_σ`, `λ_min = min_E λ₂` exactly, `g` `C³` on the closed window (one-sided at `1 ± a`), rate `ϱ = g''(1)w_min/(1+B̂_σ)²` written out; the flow clause **proves** existence and uniqueness of the flow from every `h₀` in the `ε₀`-ball (`TrainingSpeedAssembled.local_convergence_full_DB_exists`, `…_gd_DB_C3On`) |
| `edge_reach_fst`, **`edge_reach_all`** | `K₂` is irreducible on `E` (from `Setting.breach_all`) |
| `Leveled.one_le_lvl_snk`, `Leveled.phat_pos_shift`, `Leveled.cyc`, `Leveled.cyc_iff` | every positive step of `π̂_←` lowers the height by `1` modulo `ℓ(s_f)+1` |
| `Leveled.classFn`, `Leveled.densAct_classFn`, `Leveled.iterate_densAct_classFn`, `Leveled.nrmL2_classFn_neg` | the density action rotates the cyclic classes, isometrically on class functions |
| **`Leveled.one_le_beta`** | `‖P^n − Π‖_{L²(λ)} ≥ 1` for **every** `n`: "`‖P^n − Π‖` does not tend to `0`" |
| **`Leveled.not_summable_beta`**, **`Leveled.mixing_sum_eq_top`**, **`Leveled.not_mixing`** | "the mixing sum `∑_{n≥0}‖P^n − Π‖_{L²(λ)}` is `+∞`": not summable; `= ⊤` in `ℝ≥0∞`; `Core.Mixing` fails |
| `Leveled.pow_phat_nonneg`, `Leveled.pow_phat_pos_shift`, `Leveled.reach_pow_pos`, **`Leveled.periodic`** | "the chain is periodic of period `t_m+2`": `t_m := ℓ(s_f) − 1 ∈ ℕ`, `P̂^{t_m+2}(s₀,s₀) > 0`, and `P̂^n(s₀,s₀) > 0 ⇒ (t_m+2) ∣ n` |
| **`Leveled.bsigma_eq_paper`**, **`Leveled.bhatSigma_leveled_eq`** | the printed bound `B̂_σ ≤ (t_m+1)√((2+t_m)/min N)` holds **with equality** at `t_m = ℓ(s_f) − 1` |
| `hessPi`, `exists_linFlow`, `linDescent`, `linDescent_step` | the linearized flow `ḣ = −Hh` (by `exp(−tH)`) and descent (by recursion) exist from every `h₀`, on any finite space |
| `ar_edgeMeasureE`, `ar_lamMinE`, `ar_bhatSigma`, **`ar_DB_check`**, `arWrapInd`, `ar_perp_wrapInd_pos`, **`ar_stable_frozen_DB_witness`**, `arEps0`, `arEps0_pos`, **`ar_local_convergence_DB_witness`**, **`ar_leveled_mixing_check`** | inhabitation on `MorozovConsume.ar` (`s₀ → s_f`): `1 + B̂_σ = 1 + √2`, `min_E λ₂ = 1/2`; both linearized DB dynamics, and the nonlinear DB flow at `(log x)²` from `ε₀𝟙_{(s_f,s₀)}`, all from unbalanced starts; `t_m = 0`, period `2`, `β_n ≥ 1`, mixing sum `⊤`, `B̂_σ = √2` |
| `tri`, `triPol`, `triLeveled`, `triLam`, …, **`tri_leveled_mixing_check`** | a leveled graph with one internal state, `s₀ → x → s_f`: `t_m = 1`, period `3`, `β_n ≥ 1`, mixing sum `⊤` |

## Hypothesis checklist — the DB sentence of item *(3)*

| paper hypothesis / claim | here |
|---|---|
| the setting of *(1)*–*(2)*: loop closure of a finite path-connected marked graph, backward policy positive on its edges, `λ` its invariant probability | ✓ `[Fintype V]`, `hpc`, `hpos`, `hl : B.IsInvProb lam`; the kernel is `B.phat` |
| `σ`, `σ̄`, `N` | ⚠ **characterized, not constructed** (`IsHitExp uH`, `sigmaBar`, `IsGreen gr`, `visits`), inherited from `Morozov.lean`'s disclosed modelling step |
| `B̂_σ = σ_*√((2+σ̄)/min_x N(x))` | ✓ `Balance.BhatSigma G uH lam = σ_*/√λ_min`, equal to the printed form by `MorozovConsume.bhatSigma_eq_visits` (first conjunct of `morozov_rate_three_DB`) |
| `1 + B̂_σ ≥ 1` | ✓ `one_le_one_add_BhatSigma` |
| `1 + B̂_σ` satisfies `eq:coercivity` for `K₂` on `L²(λ₂)` | ✓ `hcoer_edge_of_graph`, on functions on `E`; see SCOPE for `E` versus `𝒮²` |
| "via `lem:lift_coercivity` with `C := B̂_σ`, hypothesis *(2)*" | ✓ exactly: `lift_coercivity_edgeSupport (C := B̂_σ) … (hcoer_of_graph …)` |
| `T = K₂` with `λ₂` meets the remaining hypotheses of the two theorems | ✓ `edge_setting`: Markov on `E`, `λ₂` invariant, `λ₂ > 0`, `∑λ₂ = 1`; and the ergodicity `theo:local_convergence_full`'s proof uses (`m_t` a scalar) is proved, `edge_reach_all`, a conjunct of `morozov_rate_three_DB` |
| "their rate is then `g''(1)w_min/(1+B̂_σ)²`" | ✓ written out in all four conclusions |
| "the radius […] still depend[s] on `min_E λ₂`, through `C_∞`" | ✓ `ε₀ = eps0W … (1+B̂_σ) (min_E λ₂)`; `min_E λ₂` is `lamMinE`, the exact minimum — not a lower bound |
| "the […] step still depend[s] on `min_E λ₂`, through `C_∞`" | ✗ **not so, and not claimed**: `γ₀ = gamma0W g a w_min ‖w‖_∞ (1+B̂_σ)` contains no `λ_min`, in the Lean and in the paper (Step 6, `proofs.tex:701`: `γ₀ = g''(1)w_min/(2L²)`, `L = 2g''(1)‖w‖_∞ + Kε`, `ε = min(a/4, ε₁)`). The descent clause depends on `min_E λ₂` only through the set of initializations `‖h₀‖ ≤ ε₀`. **Finding** on the wording of `proofs.tex:950`; see SCOPE |
| `g` `C³` on `[1−a,1+a]`, `g(1) = g'(1) = 0`, `g''(1) > 0`, `w ≥ w_min > 0` | ✓ `hC3 : ContDiffOn ℝ 3 g (winC3 a)` on the closed window, one-sided at `1 ± a`, with `hgd` a derivative of `g` within the window; otherwise as `TrainingSpeedAssembled`'s checklist (`g(1) = 0` unused, `‖w‖_∞` read as a bound `wsup`) |
| the nonlinear flow | ✓ **proved to exist**, uniquely, from every `h₀` in the ball (flow clause); the descent is a recursion `hstep` (inhabited by definition) |
| the linearized dynamics of `theo:db_stable_frozen_full` | ⚠ hypothesised, as in the theorem instantiated; **inhabited** — see SCOPE, Inhabitation |

## Hypothesis checklist — the closing paragraph

| paper hypothesis / claim | here |
|---|---|
| "a leveled graph, where every trajectory has the same length `t_m`" | ⚠ `Morozov.Leveled`: a height `ℓ` with `ℓ(s₀) = 0` rising by `1` along every edge. Under path-connectedness this is equivalent to all `s₀ ⤳ s_f` walks having one length; the equivalence is not formalized (inherited reading, `Morozov.lean` SCOPE) |
| `t_m` | ✓ `ℓ(s_f) − 1`, the number of **internal** states on a trajectory — the convention the paper's own proof forces (period `t_m+2`, `σ(s_f) ≤ t_m+1`); proved a natural number in `Leveled.periodic`. See SCOPE, first bullet |
| "the loop-closed chain is periodic", "of period `t_m+2`" | ✓ `Leveled.periodic`: return times to `s₀` are exactly the multiples of `t_m+2` that carry mass — `P̂^{t_m+2}(s₀,s₀) > 0` and `P̂^n(s₀,s₀) > 0 ⇒ (t_m+2) ∣ n`; `P̂^n` is `Matrix.of B.phat ^ n` |
| "`‖P^n − Π‖` does not tend to `0`" | ✓ stronger: `1 ≤ ‖P^n − Π‖` for every `n` (`Leveled.one_le_beta`) |
| `P` the density action on `L²(λ)`, `Π` the mean | ✓ `Balance.densOp lam B.phat`, `Balance.meanOp lam` on `EuclideanSpace ℝ V` through the weighting isometry — the operators `Core.Mixing` and `theo:db_stable_frozen_full`'s Lean sum |
| "the mixing sum `∑_{n≥0}‖P^n − Π‖_{L²(λ)}` is `+∞`" | ✓ `Leveled.mixing_sum_eq_top` (`∑' ofReal β_n = ⊤` in `ℝ≥0∞`), `Leveled.not_summable_beta`, `Leveled.not_mixing` |
| aperiodicity | ✓ not assumed; the point of the paragraph |
| `B̂_σ ≤ (t_m+1)√((2+t_m)/min_x N(x))` | ✓ **with equality** (`Leveled.bhatSigma_leveled_eq`) |

## SCOPE (disclosed)

* **The period convention.** The paper describes `t_m` as "the same length of every trajectory"
  and its proof uses excursions of length `t_m + 2` and `σ(s_f) ≤ t_m + 1`. With the height `ℓ`
  of `Morozov.Leveled`, an excursion from `s₀` is the wrap step plus `ℓ(s_f)` backward steps, so
  the period is `ℓ(s_f) + 1`, which is `t_m + 2` exactly when **`t_m = ℓ(s_f) − 1`**, the number of
  internal states — the paper's `τ` counting. This file uses that convention throughout. It
  **differs from the docstrings of `Morozov.Leveled` and `MorozovConsume.bsigma_leveled_le`**, which
  read `t_m := ℓ(s_f)`: their bound is still true there (looser by one step), but under that
  reading the paper's "period `t_m+2`" would be false (the period is `ℓ(s_f)+1`). Under the
  convention used here the printed bound is an equality.
* **`E`, not `𝒮²`, for `theo:db_stable_frozen_full`'s DB instance.** That theorem's DB sentence takes
  `K₂` with `λ₂` on `𝒮²`; `theo:local_convergence_full` takes it on `E`. The Lean
  `stable_frozen_*_finite` need a positive weight, so both DB instances are stated on `E`, where
  `λ₂ > 0`. Nothing is lost: `λ₂` vanishes off `E`, so `L²(λ₂)` on `𝒮²` and on `E` are the same
  space, and `LiftFinite.coercive_restrict` carries the coercivity from `𝒮²` (where
  `lift_coercivity_finite` proves it) to `E` with the same constant.
* **The linearized dynamics of `theo:db_stable_frozen_full` are a hypothesis**, as in
  `WeightedL2.lean`, which this inherits: the curve is driven by `H = g''(1)A^†M_wA` on `E`, whose
  identification with the linearization of the DB loss is `theo:gd_diffusion_full`
  (`C3Wrappers.loss_edgeE_eq_db` identifies the losses, not their Hessians).
* **`Π` is the mean**, `λ` and `λ₂` being probabilities (`hl.total`, `edgeMeasureE_total`).
* **`β_n` is read on `EuclideanSpace`.** `Core.Mixing.beta (densOp λ P̂) (meanOp λ) n` is the
  operator norm of `P^n − Π` conjugated by `wtL2`, an isometry onto `L²(λ)` since `λ > 0`; this is
  the reading every mixing statement of the library uses (`LiftFinite.opNorm_densDeviation_eq_beta`
  identifies it with the seminorm operator norm). `∑ = +∞` is stated in `ℝ≥0∞` and as
  non-summability, never through `Core.Mixing.B`, which is a real `tsum` and would return `0`
  (kb 0031).
* **Finding: the step does not depend on `min_E λ₂`.** `proofs.tex:950` says "the radius and the
  step of Theorem `theo:local_convergence_full` still depend on `min_E λ₂`, through `C_∞`". The
  radius does (`ε₀ ≤ a/(16C_∞)`); the step `γ₀` does not — Step 6 (`proofs.tex:701`) builds it from
  `g''(1)`, `‖w‖_∞`, `K` and `ε = min(a/4, ε₁)`, none of which involves `C_∞`, and the Lean
  `gamma0W` has no `λ_min` argument. The descent clause sees `min_E λ₂` only through its set of
  admissible initializations. The Lean states what is true; the sentence should say "the radius".
* **Inhabitation (kb 0025).** The graph bundle (`hpc`, `hpos`, `hl`, `hhit`, `hg`) is inhabited
  by `MorozovConsume.ar` and `CycleExample.cyc`; `Leveled` by `MorozovConsume.arLeveled` (period
  `2`) and by `tri`, `s₀ → x → s_f` (period `3`, one internal state). The linearized descent is
  inhabited from every start by `linDescent`, the linearized flow by `exists_linFlow`
  (`h_t = e^{−tH}h₀`); `ar_stable_frozen_DB_witness` runs both halves from the unbalanced
  `𝟙_{(s_f,s₀)}`, whose deviation from its mean has positive norm. The nonlinear flow clause has
  no flow hypothesis; its `C³`-on-the-window bundle is inhabited by `(log x)²`
  (`TrainingSpeedAssembled.logSq_C3On_bundle`), and `ar_local_convergence_DB_witness` runs it from
  the unbalanced `ε₀𝟙_{(s_f,s₀)}` with `ε₀ > 0` (`arEps0_pos`). The descent step `hstep` of
  `local_convergence_gd_DB_sigma` is a recursion, inhabited by definition.
* **Dropped on repointing (2026-09-14).** `exists_flow_DB_logSq`, `isGradientFlow_congr_pos` and
  `local_convergence_DB_logSq` (DB flow existence for `(log x)²` via `FlowExistence`, and the flow
  clause at `(log x)²` built on it) are subsumed by `local_convergence_full_DB_sigma`, which now
  proves existence for every generator `C³` on the window. Their one extra content — existence
  from every `h₀ > −1`, outside the ball — is not part of `prop:morozov_rate` and was removed.
* **`Leveled.periodic` states the period of `s₀`.** The chain being irreducible
  (`Setting.breach_all`), every state has the same period; that class property of periods is not
  formalized, and the paper uses only its consequence `‖P^n − Π‖ ↛ 0`, which is proved directly.
* **Finite state space**, as everywhere in `GFNBounds.Graph` and `GFNBounds.Balance`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : MarkedGraph V} {B : BackwardPolicy G}

section DB

/-- The wrap pair `(s_f, s₀)` lies in the edge set: `π̂_←(s₀ → s_f) = 1`. -/
def wrapEdge (B : BackwardPolicy G) : Balance.EdgeSet B.phat :=
  ⟨(G.snk, G.src), by simp only [B.phat_src_snk]; norm_num⟩

/-- **`prop:morozov_rate`*(3)*, detailed balance: `1 + B̂_σ ≥ 1`** (`proofs.tex:969`, "which is at
least `1`"). -/
theorem one_le_one_add_BhatSigma {lam uH : V → ℝ} (hpc : G.PathConnected)
    (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH) :
    1 ≤ 1 + Balance.BhatSigma G uH lam := by
  have := Balance.BhatSigma_pos hpc hpos hl hhit
  linarith

/-- **`prop:morozov_rate`*(3)*, detailed balance: `1 + B̂_σ` satisfies `eq:coercivity` for `K₂` on
`L²(λ₂)`** (`proofs.tex:969`), on functions on the edge set `E`: `lem:lift_coercivity` at
`C := B̂_σ`, whose hypothesis for `π̂_←` is item *(2)*. -/
theorem hcoer_edge_of_graph {lam uH : V → ℝ} (hpc : G.PathConnected)
    (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (f : Balance.EdgeSet B.phat → ℝ) :
    nrmL2 (Balance.edgeMeasureE B.phat lam) (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) f)
      ≤ (1 + Balance.BhatSigma G uH lam)
        * nrmL2 (Balance.edgeMeasureE B.phat lam)
            (Balance.Aop (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam) f) :=
  Balance.lift_coercivity_edgeSupport (Core.phat_isMarkov B) (Core.isInvariant_of_isInvProb B hl)
    (Balance.BhatSigma_pos hpc hpos hl hhit).le (Balance.hcoer_of_graph hpc hpos hl hhit) f

/-- On the loop closure, `K₂` is a Markov kernel on `E` and `λ₂` a positive invariant probability
there: the facts `C3Wrappers` proves, collected at `π̂_←`. -/
theorem edge_setting {lam : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) :
    Core.IsMarkov (Balance.edgeKernelE B.phat)
      ∧ Core.IsInvariant (Balance.edgeMeasureE B.phat lam) (Balance.edgeKernelE B.phat)
      ∧ (∀ e, 0 < Balance.edgeMeasureE B.phat lam e)
      ∧ ∑ e, Balance.edgeMeasureE B.phat lam e = 1 := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hpos2 : ∀ e, 0 < Balance.edgeMeasureE B.phat lam e := Balance.edgeMeasureE_pos hp
  refine ⟨(Balance.edgeKernelE_isMarkovOn (lam := lam) B.phat_nonneg B.phat_row_sum).toIsMarkov
      hpos2, Balance.edgeMeasureE_isInvariant B.phat_nonneg hl.nonneg
      (Balance.invariant_of_isInvariant (Core.isInvariant_of_isInvProb B hl)), hpos2,
    Balance.edgeMeasureE_total B.phat_nonneg B.phat_row_sum hl.total⟩

/-- `λ_min := min_E λ₂`, the exact minimum at which the paper reads `C_∞` for the DB loss. -/
noncomputable def lamMinE (B : BackwardPolicy G) (lam : V → ℝ) : ℝ :=
  Finset.univ.inf' ⟨wrapEdge B, Finset.mem_univ _⟩ (Balance.edgeMeasureE B.phat lam)

theorem lamMinE_le (lam : V → ℝ) (e : Balance.EdgeSet B.phat) :
    lamMinE B lam ≤ Balance.edgeMeasureE B.phat lam e :=
  Finset.inf'_le _ (Finset.mem_univ e)

theorem lamMinE_pos {lam : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) : 0 < lamMinE B lam := by
  obtain ⟨e, -, he⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    ⟨wrapEdge B, Finset.mem_univ _⟩ (Balance.edgeMeasureE B.phat lam)
  rw [lamMinE, he]
  exact (edge_setting hpc hpos hl).2.2.1 e

/-- **`prop:morozov_rate`*(3)*, detailed balance, `theo:db_stable_frozen_full` discrete half**:
for `T = K₂` on `E` with `λ₂`, the linearized descent conserves `Π₂h_k` and contracts
`‖h_k − Π₂h_k‖_{L²(λ₂)}` by `1 − ε g''(1)w_min/(1 + B̂_σ)²` per step. -/
theorem stable_frozen_discrete_DB_sigma {lam uH : V → ℝ} {w : Balance.EdgeSet B.phat → ℝ}
    {g2 wmin wsup eps : ℝ} {h : ℕ → Balance.EdgeSet B.phat → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH)
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ e, wmin ≤ w e) (hwsup : ∀ e, w e ≤ wsup)
    (heps : 0 ≤ eps) (hepsL : eps * (4 * g2 * wsup) ≤ 1)
    (hstep : ∀ k e, h (k + 1) e = h k e - eps * Balance.linHess (Balance.edgeKernelE B.phat)
      (Balance.edgeMeasureE B.phat lam) w g2 (h k) e) :
    (∀ k, meanL2 (Balance.edgeMeasureE B.phat lam) (h k)
        = meanL2 (Balance.edgeMeasureE B.phat lam) (h 0)) ∧
      ∀ k, nrmL2 (Balance.edgeMeasureE B.phat lam)
          (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) (h k))
        ≤ (1 - eps * (g2 * wmin / (1 + Balance.BhatSigma G uH lam) ^ 2)) ^ k
          * nrmL2 (Balance.edgeMeasureE B.phat lam)
              (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) (h 0)) := by
  obtain ⟨hK, hinv, hp2, htot2⟩ := edge_setting hpc hpos hl
  have hB1 := one_le_one_add_BhatSigma hpc hpos hl hhit
  have hws : wmin ≤ wsup := le_trans (hwmin (wrapEdge B)) (hwsup (wrapEdge B))
  exact Balance.stable_frozen_discrete_finite hK hinv hp2 htot2 hg2 hwmin0 hwmin hwsup
    (le_trans hwmin0 hws) (lt_of_lt_of_le zero_lt_one hB1) (hcoer_edge_of_graph hpc hpos hl hhit)
    heps hepsL (hrho_of_step hB1 hg2 hwmin0 hws heps hepsL) hstep

/-- **`prop:morozov_rate`*(3)*, detailed balance, `theo:db_stable_frozen_full` continuous half**:
along `ḣ = −Hh` for `T = K₂` on `E`, `Π₂h_t` is conserved and
`‖h_t − Π₂h_t‖ ≤ e^{−g''(1)w_min t/(1+B̂_σ)²}‖h_0 − Π₂h_0‖`. -/
theorem stable_frozen_decay_DB_sigma {lam uH : V → ℝ} {w : Balance.EdgeSet B.phat → ℝ}
    {g2 wmin : ℝ} {h : ℝ → Balance.EdgeSet B.phat → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH)
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ e, wmin ≤ w e)
    (hflow : ∀ t : ℝ, HasDerivAt h (fun e => -(Balance.linHess (Balance.edgeKernelE B.phat)
      (Balance.edgeMeasureE B.phat lam) w g2 (h t) e)) t) :
    (∀ t : ℝ, meanL2 (Balance.edgeMeasureE B.phat lam) (h t)
        = meanL2 (Balance.edgeMeasureE B.phat lam) (h 0)) ∧
      ∀ t : ℝ, 0 ≤ t → nrmL2 (Balance.edgeMeasureE B.phat lam)
          (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) (h t))
        ≤ Real.exp (-(g2 * wmin / (1 + Balance.BhatSigma G uH lam) ^ 2 * t))
          * nrmL2 (Balance.edgeMeasureE B.phat lam)
              (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) (h 0)) := by
  obtain ⟨hK, hinv, hp2, htot2⟩ := edge_setting hpc hpos hl
  have hB1 := one_le_one_add_BhatSigma hpc hpos hl hhit
  exact Balance.stable_frozen_decay_finite hinv hK.nonneg hp2 htot2 hg2 hwmin0 hwmin
    (lt_of_lt_of_le zero_lt_one hB1) (hcoer_edge_of_graph hpc hpos hl hhit) hflow

/-- **`prop:morozov_rate`*(3)*, detailed balance, `theo:local_convergence_full` flow clause**: on
`E` with `λ₂`, at `B̂ := 1 + B̂_σ` and `λ_min := min_E λ₂` (`C_∞ = λ_min^{−1/2}`), for `g` `C³` on
the closed window `[1−a,1+a]` (one-sided at the ends) with derivative `gd` there, from every
`h₀` with `‖h₀‖_{L²(λ₂)} ≤ ε₀` the nonlinear DB gradient flow **exists**, is unique, stays in the
window, and converges to a balanced `c_∞λ₂` at rate `ϱ/2`, `ϱ = g''(1)w_min/(1+B̂_σ)²` written out.
`TrainingSpeedAssembled.local_convergence_full_DB_exists` at `B̂ := 1 + B̂_σ`. -/
theorem local_convergence_full_DB_sigma {lam uH : V → ℝ} {w : Balance.EdgeSet B.phat → ℝ}
    {g gd : ℝ → ℝ} {a wsup wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (Balance.winC3 a))
    (hgd : ∀ y ∈ Balance.winC3 a, HasDerivWithinAt g (gd y) (Balance.winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ e, |w e| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ e, wmin ≤ w e)
    {h0 : Balance.EdgeSet B.phat → ℝ}
    (hnorm0 : nrmL2 (Balance.edgeMeasureE B.phat lam) h0
      ≤ Balance.eps0W g a wmin wsup (1 + Balance.BhatSigma G uH lam) (lamMinE B lam)) :
    ∃ h : ℝ → Balance.EdgeSet B.phat → ℝ, h 0 = h0
      ∧ Balance.IsGradientFlow (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam)
          (fun e => Balance.edgeMeasureE B.phat lam e * w e) gd (fun s e => 1 + h s e)
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ e, 0 < 1 + h t e
          ∧ |Balance.ratio (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam)
              (fun z => 1 + h t z) e - 1| ≤ 2 * a / 3)
      ∧ (∀ h' : ℝ → Balance.EdgeSet B.phat → ℝ, h' 0 = h0 →
          Balance.IsGradientFlow (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam)
            (fun e => Balance.edgeMeasureE B.phat lam e * w e) gd (fun s e => 1 + h' s e) →
          ∀ t : ℝ, 0 ≤ t → h' t = h t)
      ∧ ∃ cinf : ℝ,
          Balance.Balanced (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam)
            (fun _ => cinf)
          ∧ |cinf - 1 - meanL2 (Balance.edgeMeasureE B.phat lam) h0|
              ≤ Balance.CW g a wmin wsup
                * nrmL2 (Balance.edgeMeasureE B.phat lam)
                    (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) h0) ^ 2
          ∧ ∀ t : ℝ, 0 ≤ t
            → nrmL2 (Balance.edgeMeasureE B.phat lam) (fun e => h t e - (cinf - 1))
              ≤ 2 * Real.exp (-(deriv (deriv g) 1 * wmin / (1 + Balance.BhatSigma G uH lam) ^ 2
                    * t / 2))
                  * nrmL2 (Balance.edgeMeasureE B.phat lam)
                      (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) h0) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  exact Balance.local_convergence_full_DB_exists
    ((Core.phat_isMarkov B).toIsMarkovOn lam) (Core.isInvariant_of_isInvProb B hl) hp hl.total
    (lamMinE_pos hpc hpos hl) (lamMinE_le lam) ha hC3 hgd hg1 hg2 hwsup hwmin0 hwmin
    (one_le_one_add_BhatSigma hpc hpos hl hhit) (hcoer_edge_of_graph hpc hpos hl hhit) hnorm0

/-- **`prop:morozov_rate`*(3)*, detailed balance, `theo:local_convergence_full` descent clause**:
on `E` with `λ₂`, at `B̂ := 1 + B̂_σ`, for `g` `C³` on the closed window, for `0 ≤ γ ≤ γ₀` and
`‖h₀‖ ≤ ε₀` (`ε₀` read at `λ_min := min_E λ₂`; `γ₀` does not involve `λ_min`) the descent is well
defined at every step and contracts `‖h_k − Π₂h_k‖` by `1 − γϱ/4`, `ϱ = g''(1)w_min/(1+B̂_σ)²`.
`TrainingSpeedAssembled.local_convergence_gd_DB_C3On` at `B̂ := 1 + B̂_σ`. -/
theorem local_convergence_gd_DB_sigma {lam uH : V → ℝ} {w : Balance.EdgeSet B.phat → ℝ}
    {g gd : ℝ → ℝ} {hk : ℕ → Balance.EdgeSet B.phat → ℝ} {a wsup wmin gam : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (Balance.winC3 a))
    (hgd : ∀ y ∈ Balance.winC3 a, HasDerivWithinAt g (gd y) (Balance.winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ e, |w e| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ e, wmin ≤ w e)
    (hstep : ∀ k : ℕ, hk (k + 1) = fun e =>
      hk k e - gam * Balance.lossGrad (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam)
        (fun z => Balance.edgeMeasureE B.phat lam z * w z) gd (fun z => 1 + hk k z) e)
    (hgam0 : 0 ≤ gam)
    (hgam : gam ≤ Balance.gamma0W g a wmin wsup (1 + Balance.BhatSigma G uH lam))
    (hnorm0 : nrmL2 (Balance.edgeMeasureE B.phat lam) (hk 0)
      ≤ Balance.eps0W g a wmin wsup (1 + Balance.BhatSigma G uH lam) (lamMinE B lam)) :
    ∀ k : ℕ, ((∀ e, 0 < 1 + hk k e)
      ∧ (∀ e, |Balance.ratio (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam)
            (fun z => 1 + hk k z) e - 1| ≤ 2 * a / 3)
      ∧ ∀ d : Balance.EdgeSet B.phat → ℝ,
          HasDerivAt
            (fun t : ℝ => Balance.loss (Balance.edgeKernelE B.phat)
              (Balance.edgeMeasureE B.phat lam)
              (fun z => Balance.edgeMeasureE B.phat lam z * w z) (fun e => 1 + hk k e + t * d e) g)
            (ipL2 (Balance.edgeMeasureE B.phat lam)
              (Balance.lossGrad (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam)
                (fun z => Balance.edgeMeasureE B.phat lam z * w z) gd
                fun z => 1 + hk k z) d) 0)
      ∧ nrmL2 (Balance.edgeMeasureE B.phat lam)
            (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) (hk (k + 1)))
          ≤ (1 - gam * (deriv (deriv g) 1 * wmin / (1 + Balance.BhatSigma G uH lam) ^ 2) / 4)
              * nrmL2 (Balance.edgeMeasureE B.phat lam)
                  (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) (hk k)) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  exact Balance.local_convergence_gd_DB_C3On
    ((Core.phat_isMarkov B).toIsMarkovOn lam) (Core.isInvariant_of_isInvProb B hl) hp hl.total
    (lamMinE_pos hpc hpos hl) (lamMinE_le lam) ha hC3 hgd hg1 hg2 hwsup hwmin0 hwmin
    (one_le_one_add_BhatSigma hpc hpos hl hhit) (hcoer_edge_of_graph hpc hpos hl hhit) hstep
    hgam0 hgam hnorm0

/-- From a pair `e`, every state `v` reachable from `e.1.1` by `π̂_←` is the first component of a
pair reachable from `e` by `K₂`. -/
theorem edge_reach_fst {e : Balance.EdgeSet B.phat} {v : V} (hv : B.BReach e.1.1 v) :
    ∃ e1 : Balance.EdgeSet B.phat, e1.1.1 = v
      ∧ Relation.ReflTransGen (fun a b => 0 < Balance.edgeKernelE B.phat a b) e e1 := by
  induction hv with
  | refl => exact ⟨e, rfl, Relation.ReflTransGen.refl⟩
  | @tail u v _ huv ih =>
      obtain ⟨e1, he1, hr⟩ := ih
      refine ⟨⟨(v, u), huv⟩, rfl, hr.tail ?_⟩
      show 0 < Balance.edgeKernel B.phat e1.1.1 e1.1.2 v u
      simp only [Balance.edgeKernel, he1, if_true]
      exact huv

/-- **`prop:morozov_rate`*(3)*, detailed balance: `K₂` is irreducible on `E`** when the backward
chain is — from `(s,s')`, follow a positive path `s ⤳ w` of `π̂_←` through the pairs it
traverses, then step to `(z,w)`. The ergodicity `theo:local_convergence_full` uses of `T = K₂`
(`m_t` a scalar) is thus a property of the graph, not an assumption. -/
theorem edge_reach_all (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (e e' : Balance.EdgeSet B.phat) :
    Relation.ReflTransGen (fun a b => 0 < Balance.edgeKernelE B.phat a b) e e' := by
  obtain ⟨e1, he1, hr⟩ := edge_reach_fst (B.breach_all hpc hpos e.1.1 e'.1.2)
  refine hr.tail ?_
  show 0 < Balance.edgeKernel B.phat e1.1.1 e1.1.2 e'.1.1 e'.1.2
  simp only [Balance.edgeKernel, he1, if_true]
  exact e'.2

/-- **`prop:morozov_rate`*(3)*, the detailed-balance sentence, as one statement**
(`proofs.tex:969`): `B̂ := 1 + B̂_σ`, with `B̂_σ = σ_*√((2+σ̄)/min_x N(x))` as item *(2)* prints it,
is at least `1` and satisfies `eq:coercivity` for `T = K₂` on `L²(λ₂)` over the finite edge set
`E`, on which `K₂` is an irreducible Markov kernel, `λ₂` an invariant probability, positive,
with `0 < min_E λ₂`. These are the hypotheses `theo:db_stable_frozen_full` and
`theo:local_convergence_full` take of `(T, λ, B̂)`; their conclusions at the rate
`g''(1)w_min/(1+B̂_σ)²` are `stable_frozen_discrete_DB_sigma`, `stable_frozen_decay_DB_sigma`,
`local_convergence_full_DB_sigma` and `local_convergence_gd_DB_sigma`, whose radius is read at
`C_∞ = (min_E λ₂)^{−1/2}`; their step `γ₀` does not involve `min_E λ₂`. -/
theorem morozov_rate_three_DB {lam uH gr : V → ℝ} (hpc : G.PathConnected)
    (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (hg : B.IsGreen gr) :
    1 + Balance.BhatSigma G uH lam
        = 1 + sigmaStar G uH * Real.sqrt ((2 + B.sigmaBar uH) / minOver G (visits G gr))
      ∧ 1 ≤ 1 + Balance.BhatSigma G uH lam
      ∧ (∀ f : Balance.EdgeSet B.phat → ℝ,
          nrmL2 (Balance.edgeMeasureE B.phat lam)
              (Balance.perpL2 (Balance.edgeMeasureE B.phat lam) f)
            ≤ (1 + Balance.BhatSigma G uH lam)
              * nrmL2 (Balance.edgeMeasureE B.phat lam)
                  (Balance.Aop (Balance.edgeKernelE B.phat) (Balance.edgeMeasureE B.phat lam) f))
      ∧ Core.IsMarkov (Balance.edgeKernelE B.phat)
      ∧ Core.IsInvariant (Balance.edgeMeasureE B.phat lam) (Balance.edgeKernelE B.phat)
      ∧ (∀ e, 0 < Balance.edgeMeasureE B.phat lam e)
      ∧ ∑ e, Balance.edgeMeasureE B.phat lam e = 1
      ∧ (∀ e e' : Balance.EdgeSet B.phat,
          Relation.ReflTransGen (fun a b => 0 < Balance.edgeKernelE B.phat a b) e e')
      ∧ 0 < lamMinE B lam
      ∧ ∀ e, lamMinE B lam ≤ Balance.edgeMeasureE B.phat lam e :=
  let hs := edge_setting hpc hpos hl
  ⟨by rw [bhatSigma_eq_visits hpc hpos hl hg hhit], one_le_one_add_BhatSigma hpc hpos hl hhit,
    hcoer_edge_of_graph hpc hpos hl hhit, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2,
    edge_reach_all hpc hpos, lamMinE_pos hpc hpos hl, lamMinE_le lam⟩

end DB

section LeveledMixing

namespace Leveled

variable (L : Leveled G)

omit [Fintype V] [DecidableEq V] in
/-- `ℓ(s_f) ≥ 1`: a walk from `s₀` to `s_f ≠ s₀` ends with an edge. -/
theorem one_le_lvl_snk (hpc : G.PathConnected) : 1 ≤ L.lvl G.snk := by
  rcases Relation.ReflTransGen.cases_tail (hpc G.snk).1 with h | ⟨y, hy, he⟩
  · exact absurd h.symm G.src_ne_snk
  · have h1 := L.lvl_mono hy
    rw [L.lvl_src] at h1
    rw [L.lvl_edge he]
    linarith

/-- Every backward step drops the height by one modulo `ℓ(s_f) + 1`: off `s₀` it drops by
exactly one, and the wrap `s₀ → s_f` goes from `0` to `ℓ(s_f) = 0 − 1 + (ℓ(s_f)+1)`. -/
theorem phat_pos_shift {x y : V} (hxy : 0 < B.phat x y) :
    ∃ m : ℤ, L.lvl y = L.lvl x - 1 + m * (L.lvl G.snk + 1) := by
  by_cases hx : x = G.src
  · subst hx
    have hy : y = G.snk := by
      by_contra hne
      rw [B.phat_src_of_ne hne] at hxy
      exact lt_irrefl 0 hxy
    subst hy
    exact ⟨1, by rw [L.lvl_src]; push_cast; ring⟩
  · have hedge : G.Edge y x := B.supp hx (by rw [← B.phat_of_ne_src hx]; exact hxy.ne')
    exact ⟨0, by rw [L.lvl_edge hedge]; push_cast; ring⟩

omit [Fintype V] [DecidableEq V] in
/-- The **cyclic class** `j` (mod `ℓ(s_f)+1`) of the height. -/
def cyc (j : ℤ) (x : V) : Prop := ∃ k : ℤ, L.lvl x = j + k * (L.lvl G.snk + 1)

/-- A positive backward step moves class `j` to class `j − 1`, and only there. -/
theorem cyc_iff {x y : V} (hxy : 0 < B.phat x y) (j : ℤ) : L.cyc j x ↔ L.cyc (j - 1) y := by
  obtain ⟨m, hm⟩ := L.phat_pos_shift hxy
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + m, by rw [hm, hk]; push_cast; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k - m, by
      have : L.lvl x = L.lvl y + 1 - m * (L.lvl G.snk + 1) := by linarith
      rw [this, hk]; push_cast; ring⟩

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- The function equal to `α` on class `j` and to `β` off it. -/
noncomputable def classFn (j : ℤ) (α β : ℝ) : V → ℝ := fun x => if L.cyc j x then α else β

/-- The density action rotates the classes: `P(α𝟙_j + β𝟙_{¬j}) = α𝟙_{j−1} + β𝟙_{¬(j−1)}`,
because every state feeding a state of class `j − 1` is of class `j`, and `λπ̂_← = λ`. -/
theorem densAct_classFn {lam : V → ℝ} (hl : B.IsInvProb lam) (hp : ∀ x, 0 < lam x) (j : ℤ)
    (α β : ℝ) :
    Core.densAct lam B.phat (L.classFn j α β) = L.classFn (j - 1) α β := by
  funext y
  have hterm : ∀ x, lam x * B.phat x y * L.classFn j α β x
      = lam x * B.phat x y * L.classFn (j - 1) α β y := by
    intro x
    rcases (B.phat_nonneg x y).lt_or_eq with h | h
    · by_cases hc : L.cyc j x
      · have hc' := (L.cyc_iff h j).mp hc
        simp only [classFn, if_pos hc, if_pos hc']
      · have hc' : ¬ L.cyc (j - 1) y := fun h' => hc ((L.cyc_iff h j).mpr h')
        simp only [classFn, if_neg hc, if_neg hc']
    · rw [← h, mul_zero, zero_mul, zero_mul]
  rw [Core.densAct_apply, Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_mul, hl.inv y]
  exact mul_div_cancel_left₀ _ (hp y).ne'

theorem iterate_densAct_classFn {lam : V → ℝ} (hl : B.IsInvProb lam) (hp : ∀ x, 0 < lam x)
    (α β : ℝ) (n : ℕ) :
    (Core.densAct lam B.phat)^[n] (L.classFn 0 α β) = L.classFn (-(n : ℤ)) α β := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, L.densAct_classFn hl hp]
      congr 1
      push_cast
      ring

/-- The density action preserves `λ`-integrals, iterated. -/
theorem sum_iterate_densAct {lam : V → ℝ} (hp : ∀ x, 0 < lam x)
    (n : ℕ) (a : V → ℝ) :
    ∑ x, lam x * (Core.densAct lam B.phat)^[n] a x = ∑ x, lam x * a x := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := Balance.meanL2_densAct (Core.phat_isMarkov B) hp ((Core.densAct lam B.phat)^[k] a)
      simp only [meanL2] at this
      rw [this, ih]

omit [Fintype V] [DecidableEq V] in
theorem classFn_mul_self (j : ℤ) (α β : ℝ) (x : V) :
    L.classFn j α β x * L.classFn j α β x = L.classFn j (α * α) (β * β) x := by
  by_cases hc : L.cyc j x
  · simp only [classFn, if_pos hc]
  · simp only [classFn, if_neg hc]

/-- The rotation is an isometry on the class functions: `‖P^n f_0‖ = ‖f_0‖`. -/
theorem nrmL2_classFn_neg {lam : V → ℝ} (hl : B.IsInvProb lam) (hp : ∀ x, 0 < lam x)
    (α β : ℝ) (n : ℕ) :
    nrmL2 lam (L.classFn (-(n : ℤ)) α β) = nrmL2 lam (L.classFn 0 α β) := by
  simp only [nrmL2, ipL2, L.classFn_mul_self]
  rw [← L.iterate_densAct_classFn hl hp, sum_iterate_densAct (B := B) hp]

omit [Fintype V] [DecidableEq V] in
theorem cyc_zero_src : L.cyc 0 G.src := ⟨0, by rw [L.lvl_src]; push_cast; ring⟩

omit [Fintype V] [DecidableEq V] in
theorem not_cyc_zero_snk (hpc : G.PathConnected) : ¬ L.cyc 0 G.snk := by
  rintro ⟨k, hk⟩
  have h1 := L.one_le_lvl_snk hpc
  rcases le_or_gt k 0 with hk0 | hk0
  · have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    push_cast at hk
    nlinarith
  · have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    push_cast at hk
    nlinarith

/-- The `λ`-mass of class `0`. -/
noncomputable def mass0 (lam : V → ℝ) : ℝ := ∑ x, lam x * L.classFn 0 1 0 x

/-- The test function `𝟙_0 − λ(class 0)`, of mean zero. -/
noncomputable def testFn (lam : V → ℝ) : V → ℝ := L.classFn 0 (1 - L.mass0 lam) (-L.mass0 lam)

omit [DecidableEq V] in
theorem testFn_apply (lam : V → ℝ) (x : V) :
    L.testFn lam x = L.classFn 0 1 0 x - L.mass0 lam := by
  by_cases hc : L.cyc 0 x
  · simp only [testFn, classFn, if_pos hc]
  · simp only [testFn, classFn, if_neg hc]; ring

theorem sum_testFn {lam : V → ℝ} (hl : B.IsInvProb lam) : ∑ x, lam x * L.testFn lam x = 0 := by
  simp only [L.testFn_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hl.total,
    one_mul, mass0, sub_self]

theorem lam_snk_le_one_sub_mass0 {lam : V → ℝ} (hpc : G.PathConnected) (hl : B.IsInvProb lam) :
    lam G.snk ≤ 1 - L.mass0 lam := by
  have hs : ∀ x, 0 ≤ 1 - L.classFn 0 1 0 x := fun x => by
    by_cases hc : L.cyc 0 x
    · simp only [classFn, if_pos hc]; norm_num
    · simp only [classFn, if_neg hc]; norm_num
  have hsnk : L.classFn 0 1 0 G.snk = 0 := by simp only [classFn, if_neg (L.not_cyc_zero_snk hpc)]
  have hsum : 1 - L.mass0 lam = ∑ x, lam x * (1 - L.classFn 0 1 0 x) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hl.total, mass0]
  have := Finset.single_le_sum (f := fun x => lam x * (1 - L.classFn 0 1 0 x))
    (fun x _ => mul_nonneg (hl.nonneg x) (hs x)) (Finset.mem_univ G.snk)
  simp only [hsnk, sub_zero, mul_one] at this
  linarith

theorem nrmL2_testFn_pos {lam : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) : 0 < nrmL2 lam (L.testFn lam) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hsrc : L.testFn lam G.src = 1 - L.mass0 lam := by
    simp only [testFn, classFn, if_pos L.cyc_zero_src]
  have hm : 0 < 1 - L.mass0 lam := lt_of_lt_of_le (hp G.snk) (L.lam_snk_le_one_sub_mass0 hpc hl)
  have hip : 0 < ipL2 lam (L.testFn lam) (L.testFn lam) := by
    have := Finset.single_le_sum (f := fun x => lam x * (L.testFn lam x * L.testFn lam x))
      (fun x _ => mul_nonneg (hl.nonneg x) (mul_self_nonneg _)) (Finset.mem_univ G.src)
    have hpos' : 0 < lam G.src * (L.testFn lam G.src * L.testFn lam G.src) := by
      rw [hsrc]; exact mul_pos (hp G.src) (mul_pos hm hm)
    simp only [ipL2]
    linarith
  exact Real.sqrt_pos.mpr hip

include L in
/-- **`prop:morozov_rate`, closing paragraph: `‖P^n − Π‖_{L²(λ)} ≥ 1` for every `n` on a leveled
graph** (`proofs.tex:971`, "the chain is
periodic […] and `‖P^n − Π‖` does not tend to `0`"): the mean-zero class function
`𝟙_0 − λ(class 0)` is rotated isometrically by `P`. `β_n` is `Core.Mixing.beta`, the operator norm
of `P^n − Π` on `L²(λ)` through the weighting isometry. -/
theorem one_le_beta {lam : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (n : ℕ) :
    1 ≤ Core.Mixing.beta (Balance.densOp lam B.phat) (Balance.meanOp lam) n := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hp x).le
  set T := Balance.densOp lam B.phat ^ n - Balance.meanOp lam with hT
  have happ : T (Balance.wtL2 lam (L.testFn lam))
      = Balance.wtL2 lam (Balance.densDeviation B.phat lam n (L.testFn lam)) :=
    Balance.densDeviation_wtL2 hp B.phat n (L.testFn lam)
  have hdev : Balance.densDeviation B.phat lam n (L.testFn lam) = L.classFn (-(n : ℤ))
      (1 - L.mass0 lam) (-L.mass0 lam) := by
    rw [Balance.densDeviation_eq, L.sum_testFn hl]
    funext y
    rw [sub_zero, testFn, L.iterate_densAct_classFn hl hp]
  have hle := T.le_opNorm (Balance.wtL2 lam (L.testFn lam))
  rw [happ, Balance.norm_wtL2 hnn, Balance.norm_wtL2 hnn, hdev, L.nrmL2_classFn_neg hl hp] at hle
  have h0 := L.nrmL2_testFn_pos hpc hpos hl
  rw [testFn] at h0
  exact le_of_mul_le_mul_right (by rw [one_mul]; exact hle) h0

include L in
/-- **`prop:morozov_rate`, closing paragraph: the mixing coefficients `‖P^n − Π‖` are not
summable on a leveled graph.** -/
theorem not_summable_beta {lam : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) :
    ¬ Summable (fun n : ℕ => ‖Balance.densOp lam B.phat ^ n - Balance.meanOp lam‖) := by
  intro hs
  have ht := hs.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds one_pos))
  exact absurd (L.one_le_beta hpc hpos hl N) (not_le.mpr (hN N le_rfl))

include L in
/-- **`prop:morozov_rate`, closing paragraph: the mixing sum `∑_{n≥0} ‖P^n − Π‖_{L²(λ)}` is `+∞`
on a leveled graph** (`proofs.tex:952`), in `ℝ≥0∞`,
where the value `+∞` is a value and not `tsum`'s junk `0`. -/
theorem mixing_sum_eq_top {lam : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) :
    ∑' n : ℕ, ENNReal.ofReal (Core.Mixing.beta (Balance.densOp lam B.phat) (Balance.meanOp lam) n)
      = ⊤ := by
  refine top_le_iff.mp ?_
  calc (⊤ : ENNReal) = ∑' _ : ℕ, (1 : ENNReal) :=
        (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun n => by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (L.one_le_beta hpc hpos hl n)

include L in
/-- **`prop:morozov_rate`, closing paragraph: summable mixing fails on a leveled graph**:
`Core.Mixing (P, Π)` does not hold. -/
theorem not_mixing {lam : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) : ¬ Core.Mixing (Balance.densOp lam B.phat) (Balance.meanOp lam) :=
  fun hmx => L.not_summable_beta hpc hpos hl hmx.summable

/-! ### Periodicity: the return times to `s₀` are the multiples of `t_m + 2` -/

/-- Entries of powers of a non-negative matrix are non-negative. -/
theorem pow_phat_nonneg (n : ℕ) (x y : V) : 0 ≤ (Matrix.of B.phat ^ n) x y := by
  induction n generalizing y with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih z) (B.phat_nonneg z y)

/-- An `n`-step backward transition drops the height by `n` modulo `ℓ(s_f) + 1`. -/
theorem pow_phat_pos_shift (n : ℕ) {x y : V} (hxy : 0 < (Matrix.of B.phat ^ n) x y) :
    ∃ j : ℤ, L.lvl y = L.lvl x - n + j * (L.lvl G.snk + 1) := by
  induction n generalizing y with
  | zero =>
      rw [pow_zero, Matrix.one_apply] at hxy
      split_ifs at hxy with h
      · exact ⟨0, by rw [h]; push_cast; ring⟩
      · exact absurd hxy (lt_irrefl 0)
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply] at hxy
      obtain ⟨z, -, hz⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
        (f := fun _ => (0:ℝ)) (by simpa only [Finset.sum_const_zero] using hxy)
      have hz1 : 0 < (Matrix.of B.phat ^ k) x z :=
        lt_of_le_of_ne (pow_phat_nonneg k x z) fun h => by
          rw [← h, zero_mul] at hz; exact lt_irrefl 0 hz
      have hz2 : 0 < B.phat z y :=
        lt_of_le_of_ne (B.phat_nonneg z y) fun h => by
          simp only [Matrix.of_apply, ← h, mul_zero] at hz; exact lt_irrefl 0 hz
      obtain ⟨j, hj⟩ := ih hz1
      obtain ⟨m, hm⟩ := L.phat_pos_shift hz2
      exact ⟨j + m, by rw [hm, hj]; push_cast; ring⟩

/-- Along a walk `s₀ ⤳ y` of `G` the height is a natural number `k`, and the backward chain goes
from `y` to `s₀` in `k` steps with positive probability. -/
theorem reach_pow_pos (hpos : B.PositiveOnEdges) {y : V} (hy : G.Reach G.src y) :
    ∃ k : ℕ, L.lvl y = k ∧ 0 < (Matrix.of B.phat ^ k) y G.src := by
  classical
  induction hy with
  | refl =>
      refine ⟨0, by rw [L.lvl_src]; norm_num, ?_⟩
      rw [pow_zero, Matrix.one_apply_eq]
      norm_num
  | @tail x y _ he ih =>
      obtain ⟨k, hk, hpk⟩ := ih
      refine ⟨k + 1, by rw [L.lvl_edge he, hk]; push_cast; ring, ?_⟩
      rw [pow_succ', Matrix.mul_apply]
      have hyx : 0 < B.phat y x := B.phat_pos_of_edge hpos he
      have hle := Finset.single_le_sum (f := fun z => Matrix.of B.phat y z
        * (Matrix.of B.phat ^ k) z G.src)
        (fun z _ => mul_nonneg (B.phat_nonneg y z) (pow_phat_nonneg k z G.src))
        (Finset.mem_univ x)
      have hpos' : 0 < Matrix.of B.phat y x * (Matrix.of B.phat ^ k) x G.src := by
        simp only [Matrix.of_apply]; exact mul_pos hyx hpk
      exact lt_of_lt_of_le hpos' hle

/-- **`prop:morozov_rate`, closing paragraph: the loop-closed chain of a leveled graph is periodic,
of period `t_m + 2`**
(`proofs.tex:971`, "all excursions have length exactly `t_m+2`, so the chain is periodic of period
`t_m+2`"), with the paper's `t_m := ℓ(s_f) − 1`, the number of internal states on a trajectory:
`t_m` is a natural number, the chain returns to `s₀` in `t_m + 2` steps with positive probability,
and every `n` with `P̂^n(s₀ → s₀) > 0` is a multiple of `t_m + 2`. The period of `s₀` is therefore
exactly `t_m + 2 ≥ 2`. -/
theorem periodic (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) :
    ∃ tm : ℕ, L.lvl G.snk = tm + 1
      ∧ 0 < (Matrix.of B.phat ^ (tm + 2)) G.src G.src
      ∧ ∀ n : ℕ, 0 < (Matrix.of B.phat ^ n) G.src G.src → tm + 2 ∣ n := by
  obtain ⟨k, hk, hpk⟩ := L.reach_pow_pos hpos (hpc G.snk).1
  have h1 := L.one_le_lvl_snk hpc
  obtain ⟨tm, rfl⟩ : ∃ tm, k = tm + 1 := by
    refine ⟨k - 1, ?_⟩
    have : (1:ℝ) ≤ k := hk ▸ h1
    have hk1 : 1 ≤ k := by exact_mod_cast this
    omega
  refine ⟨tm, by rw [hk]; push_cast; ring, ?_, fun n hn => ?_⟩
  · rw [show tm + 2 = 1 + (tm + 1) by ring, pow_add, pow_one, Matrix.mul_apply]
    have hle := Finset.single_le_sum (f := fun z => Matrix.of B.phat G.src z
        * (Matrix.of B.phat ^ (tm + 1)) z G.src)
        (fun z _ => mul_nonneg (B.phat_nonneg _ z) (pow_phat_nonneg _ z G.src))
        (Finset.mem_univ G.snk)
    have hpos' : 0 < Matrix.of B.phat G.src G.snk * (Matrix.of B.phat ^ (tm + 1)) G.snk G.src := by
      simp only [Matrix.of_apply, B.phat_src_snk, one_mul]; exact hpk
    exact lt_of_lt_of_le hpos' hle
  · obtain ⟨j, hj⟩ := L.pow_phat_pos_shift n hn
    rw [hk] at hj
    have hz : (n : ℤ) = j * ((tm : ℤ) + 2) := by
      have : (n : ℝ) = j * ((tm : ℝ) + 2) := by push_cast at hj; linarith
      exact_mod_cast this
    have hd : ((tm + 2 : ℕ) : ℤ) ∣ (n : ℤ) := ⟨j, by rw [hz]; push_cast; ring⟩
    exact Int.natCast_dvd_natCast.mp hd

/-- **`prop:morozov_rate`, closing paragraph: the bound on `B̂_σ`, in the paper's convention
`t_m = ℓ(s_f) − 1`, is an equality**: `σ_* = t_m + 1` and `σ̄ = t_m`, so
`σ_*√((2+σ̄)/N) = (t_m+1)√((2+t_m)/N)` for every
`N` — in particular at `N = min_x N(x)`. -/
theorem bsigma_eq_paper (hpc : G.PathConnected) (N : V → ℝ) :
    sigmaStar G L.lvl * Real.sqrt ((2 + B.sigmaBar L.lvl) / minOver G N)
      = ((L.lvl G.snk - 1) + 1) * Real.sqrt ((2 + (L.lvl G.snk - 1)) / minOver G N) := by
  rw [L.sigmaStar_eq hpc, L.sigmaBar_eq (B := B), sub_add_cancel]

/-- **`prop:morozov_rate`, closing paragraph: `B̂_σ = (t_m+1)√((2+t_m)/min_x N(x))` on a leveled
graph**, `t_m := ℓ(s_f) − 1`: the
closing paragraph's `B̂_σ ≤ (t_m+1)√((2+t_m)/min_x N(x))` holds with equality, for the constant
`TrainingSpeed.BhatSigma = σ_*/√λ_min` the substituted theorems consume. -/
theorem bhatSigma_leveled_eq {lam gr : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen gr) :
    Balance.BhatSigma G L.lvl lam
      = ((L.lvl G.snk - 1) + 1)
        * Real.sqrt ((2 + (L.lvl G.snk - 1)) / minOver G (visits G gr)) := by
  rw [bhatSigma_eq_visits hpc hpos hl hg L.isHitExp, L.bsigma_eq_paper hpc]

end Leveled

end LeveledMixing

/-! ### Inhabitation (kb 0025)

The linearized dynamics of `theo:db_stable_frozen_full` are hypothesised by the theorems above as
a recursion and as an ODE. Both have solutions from every initialization, on every finite state
space: the recursion by definition, the ODE by the exponential of `−H`. -/

section LinearDynamics

variable {α : Type*} [Fintype α]

/-- `H = g''(1)A^†M_wA` on `α → ℝ`, bundled as a continuous linear map. -/
noncomputable def hessPi (K : α → α → ℝ) (lam w : α → ℝ) (g2 : ℝ) : (α → ℝ) →L[ℝ] (α → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := Balance.linHess K lam w g2
      map_add' := fun a b => Balance.linHess_add K lam w g2 a b
      map_smul' := fun c a => Balance.linHess_smul K lam w g2 c a }

theorem hessPi_apply (K : α → α → ℝ) (lam w : α → ℝ) (g2 : ℝ) (a : α → ℝ) :
    hessPi K lam w g2 a = Balance.linHess K lam w g2 a := rfl

/-- The linearized gradient flow `ḣ = −Hh` has a solution from every `h₀`: `h_t = e^{−tH}h₀`. -/
theorem exists_linFlow (K : α → α → ℝ) (lam w : α → ℝ) (g2 : ℝ) (h0 : α → ℝ) :
    ∃ h : ℝ → α → ℝ, h 0 = h0
      ∧ ∀ t : ℝ, HasDerivAt h (fun x => -(Balance.linHess K lam w g2 (h t) x)) t := by
  refine ⟨fun t => NormedSpace.exp (t • -hessPi K lam w g2) h0, ?_, fun t => ?_⟩
  · simp only [zero_smul, NormedSpace.exp_zero]
    rfl
  · have hA := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-hessPi K lam w g2) t
    have hc := (ContinuousLinearMap.apply ℝ (α → ℝ) h0).hasFDerivAt.comp_hasDerivAt t hA
    exact hc.congr_deriv (funext fun x => rfl)

/-- The linearized gradient descent `h_{k+1} = h_k − εHh_k` from `h₀`, by recursion. -/
noncomputable def linDescent (K : α → α → ℝ) (lam w : α → ℝ) (g2 eps : ℝ) (h0 : α → ℝ) :
    ℕ → α → ℝ
  | 0 => h0
  | k + 1 => fun x => linDescent K lam w g2 eps h0 k x
      - eps * Balance.linHess K lam w g2 (linDescent K lam w g2 eps h0 k) x

theorem linDescent_step (K : α → α → ℝ) (lam w : α → ℝ) (g2 eps : ℝ) (h0 : α → ℝ) (k : ℕ)
    (x : α) :
    linDescent K lam w g2 eps h0 (k + 1) x = linDescent K lam w g2 eps h0 k x
      - eps * Balance.linHess K lam w g2 (linDescent K lam w g2 eps h0 k) x := rfl

end LinearDynamics

/-! ### Witnesses on the two-vertex autoregressive graph `s₀ → s_f`

`MorozovConsume.ar`: the loop closure is the swap `s₀ ↔ s_f`, `λ = (1/2,1/2)`, `B̂_σ = √2`. Its edge
set is `E = {(s_f,s₀), (s₀,s_f)}` with `λ₂ ≡ 1/2`, and `K₂` is again the swap. Computed by hand
first: `1 + B̂_σ = 1 + √2 ≈ 2.414`; `min_E λ₂ = 1/2`; the DB rate at `g''(1) = 2`, `w ≡ 1` is
`2/(1+√2)² ≈ 0.343`. The graph is leveled at `ℓ(s_f) = 1`, so `t_m = 0` and the period is `2`. -/

section ArWitness

theorem ar_edgeMeasureE (e : Balance.EdgeSet arPol.phat) :
    Balance.edgeMeasureE arPol.phat arLam e = 1 / 2 := by
  rcases e with ⟨⟨s, s'⟩, hs⟩
  simp only [Balance.edgeMeasureE, Balance.edgeMeasure, arPhat_eq, arLam] at hs ⊢
  fin_cases s <;> fin_cases s' <;> (try norm_num [arKern] at hs) <;> norm_num [arKern]

theorem ar_lamMinE : lamMinE arPol arLam = 1 / 2 :=
  le_antisymm ((lamMinE_le arLam (wrapEdge arPol)).trans_eq (ar_edgeMeasureE _))
    (Finset.le_inf' _ _ fun e _ => (ar_edgeMeasureE e).ge)

theorem ar_bhatSigma : Balance.BhatSigma ar arLeveled.lvl arLam = Real.sqrt 2 :=
  ar_leveled_check.2.2.2.1

/-- **`prop:morozov_rate`*(3)*, detailed balance, on an instance**: on `s₀ → s_f`,
`1 + B̂_σ = 1 + √2 ≥ 1` is a
coercivity constant of `K₂` on `L²(λ₂)` over `E`, and `min_E λ₂ = 1/2`. -/
theorem ar_DB_check :
    1 + Balance.BhatSigma ar arLeveled.lvl arLam = 1 + Real.sqrt 2
      ∧ 1 ≤ 1 + Balance.BhatSigma ar arLeveled.lvl arLam
      ∧ (∀ f : Balance.EdgeSet arPol.phat → ℝ,
          nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
              (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) f)
            ≤ (1 + Real.sqrt 2)
              * nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
                  (Balance.Aop (Balance.edgeKernelE arPol.phat)
                    (Balance.edgeMeasureE arPol.phat arLam) f))
      ∧ lamMinE arPol arLam = 1 / 2 := by
  obtain ⟨-, h1, h2, -⟩ := morozov_rate_three_DB arPathConnected arPositiveOnEdges arIsInvProb
    arLeveled.isHitExp arIsGreen
  refine ⟨by rw [ar_bhatSigma], h1, fun f => ?_, ar_lamMinE⟩
  have := h2 f
  rwa [ar_bhatSigma] at this

/-- The indicator of the wrap pair `(s_f, s₀)`. -/
noncomputable def arWrapInd : Balance.EdgeSet arPol.phat → ℝ :=
  fun e => if e = wrapEdge arPol then 1 else 0

/-- `arWrapInd` is not balanced: its deviation from its mean has positive norm. -/
theorem ar_perp_wrapInd_pos :
    0 < nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
      (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd) := by
  have hmean : meanL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd = 1 / 2 := by
    simp only [meanL2, arWrapInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ (wrapEdge arPol), if_pos (Finset.mem_univ _),
      ar_edgeMeasureE]
  have hval : Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd (wrapEdge arPol)
      = 1 / 2 := by
    rw [Balance.perpL2_apply, hmean]
    simp only [arWrapInd, if_true]
    norm_num
  have hip : 0 < ipL2 (Balance.edgeMeasureE arPol.phat arLam)
      (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd)
      (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd) := by
    have hle := Finset.single_le_sum (f := fun e => Balance.edgeMeasureE arPol.phat arLam e
        * (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd e
          * Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd e))
      (fun e _ => mul_nonneg (by rw [ar_edgeMeasureE]; norm_num) (mul_self_nonneg _))
      (Finset.mem_univ (wrapEdge arPol))
    have hpos : 0 < Balance.edgeMeasureE arPol.phat arLam (wrapEdge arPol)
        * (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd (wrapEdge arPol)
          * Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd (wrapEdge arPol)) := by
      rw [hval, ar_edgeMeasureE]; norm_num
    simp only [ipL2]
    linarith
  exact Real.sqrt_pos.mpr hip

/-- **`prop:morozov_rate`*(3)*, detailed balance: the linearized dynamics, inhabited off
balance.** On `s₀ → s_f`, from the unbalanced
`h₀ = 𝟙_{(s_f,s₀)}`, with `g''(1) = 2`, `w ≡ 1` and the paper's largest step `ε = 1/8`: the descent
and the flow exist, and `stable_frozen_discrete_DB_sigma`, `stable_frozen_decay_DB_sigma` deliver
their contractions at `ϱ = 2/(1+√2)²`. -/
theorem ar_stable_frozen_DB_witness :
    0 < nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
        (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd)
      ∧ (∀ k, nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
            (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam)
              (linDescent (Balance.edgeKernelE arPol.phat) (Balance.edgeMeasureE arPol.phat arLam)
                (fun _ => 1) 2 (1/8) arWrapInd k))
          ≤ (1 - 1/8 * (2 * 1 / (1 + Real.sqrt 2) ^ 2)) ^ k
            * nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
                (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd))
      ∧ ∃ h : ℝ → Balance.EdgeSet arPol.phat → ℝ, h 0 = arWrapInd
          ∧ (∀ t : ℝ, HasDerivAt h (fun e => -(Balance.linHess (Balance.edgeKernelE arPol.phat)
              (Balance.edgeMeasureE arPol.phat arLam) (fun _ => 1) 2 (h t) e)) t)
          ∧ ∀ t : ℝ, 0 ≤ t → nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
              (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) (h t))
            ≤ Real.exp (-(2 * 1 / (1 + Real.sqrt 2) ^ 2 * t))
              * nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
                  (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd) := by
  refine ⟨ar_perp_wrapInd_pos, fun k => ?_, ?_⟩
  · have key := (stable_frozen_discrete_DB_sigma (w := fun _ => (1:ℝ)) (g2 := 2) (wmin := 1)
      (wsup := 1) (eps := 1/8) arPathConnected arPositiveOnEdges arIsInvProb arLeveled.isHitExp
      (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl) (by norm_num) (by norm_num)
      (linDescent_step _ _ _ _ _ arWrapInd)).2 k
    rwa [ar_bhatSigma] at key
  · obtain ⟨h, hh0, hflow⟩ := exists_linFlow (Balance.edgeKernelE arPol.phat)
      (Balance.edgeMeasureE arPol.phat arLam) (fun _ => 1) 2 arWrapInd
    refine ⟨h, hh0, hflow, fun t ht => ?_⟩
    have key := (stable_frozen_decay_DB_sigma (w := fun _ => (1:ℝ)) (g2 := 2) (wmin := 1)
      arPathConnected arPositiveOnEdges arIsInvProb arLeveled.isHitExp (by norm_num) (by norm_num)
      (fun _ => le_rfl) hflow).2 t ht
    rwa [ar_bhatSigma, hh0] at key

/-- **`prop:morozov_rate`, closing paragraph, on an instance.** On `s₀ → s_f`: `t_m = 0`, the loop
closure is periodic of
period `2`, `‖P^n − Π‖ ≥ 1` for every `n`, and the mixing sum is `+∞`, while `B̂_σ = √2` is
finite and equal to `(t_m+1)√((2+t_m)/min N) = √2`. -/
theorem ar_leveled_mixing_check :
    arLeveled.lvl ar.snk - 1 = 0
      ∧ 0 < (Matrix.of arPol.phat ^ 2) ar.src ar.src
      ∧ (∀ n : ℕ, 0 < (Matrix.of arPol.phat ^ n) ar.src ar.src → 2 ∣ n)
      ∧ (∀ n : ℕ, 1 ≤ Core.Mixing.beta (Balance.densOp arLam arPol.phat) (Balance.meanOp arLam) n)
      ∧ ∑' n : ℕ, ENNReal.ofReal
          (Core.Mixing.beta (Balance.densOp arLam arPol.phat) (Balance.meanOp arLam) n) = ⊤
      ∧ Balance.BhatSigma ar arLeveled.lvl arLam
          = ((arLeveled.lvl ar.snk - 1) + 1)
            * Real.sqrt ((2 + (arLeveled.lvl ar.snk - 1)) / minOver ar (visits ar arGreen)) := by
  obtain ⟨tm, htm, hpow, hdvd⟩ := arLeveled.periodic arPathConnected arPositiveOnEdges
  have hsnk : arLeveled.lvl ar.snk = 1 := rfl
  have htm0 : tm = 0 := by
    rw [hsnk] at htm
    exact_mod_cast (show (tm : ℝ) = 0 by linarith)
  subst htm0
  exact ⟨by rw [hsnk]; norm_num, hpow, hdvd,
    arLeveled.one_le_beta arPathConnected arPositiveOnEdges arIsInvProb,
    arLeveled.mixing_sum_eq_top arPathConnected arPositiveOnEdges arIsInvProb,
    arLeveled.bhatSigma_leveled_eq arPathConnected arPositiveOnEdges arIsInvProb arIsGreen⟩

/-- The paper's radius `ε₀` for the DB loss on `s₀ → s_f`, at `g = (log x)²`, `a = 1/2`, `w ≡ 1`. -/
noncomputable def arEps0 : ℝ :=
  Balance.eps0W Balance.logSq (1/2) 1 1 (1 + Balance.BhatSigma ar arLeveled.lvl arLam)
    (lamMinE arPol arLam)

theorem arEps0_pos : 0 < arEps0 :=
  (Balance.constW_bounds (lam := Balance.edgeMeasureE arPol.phat arLam)
    (w := fun _ : Balance.EdgeSet arPol.phat => (1:ℝ))
    (edge_setting arPathConnected arPositiveOnEdges arIsInvProb).2.2.2
    (lamMinE_pos arPathConnected arPositiveOnEdges arIsInvProb) (by norm_num)
    Balance.logSq_C3On_bundle.1 Balance.logSq_C3On_bundle.2.2.2 (fun _ => by norm_num) one_pos
    (fun _ => le_rfl)
    (one_le_one_add_BhatSigma arPathConnected arPositiveOnEdges arIsInvProb
      arLeveled.isHitExp)).1.1

/-- **`prop:morozov_rate`*(3)*, detailed balance: the nonlinear flow clause, inhabited off
balance.** On `s₀ → s_f`, at `g = (log x)²`, `a = 1/2`, `w ≡ 1`, from the unbalanced
`h₀ = ε₀𝟙_{(s_f,s₀)}`, inside the paper's ball (`‖h₀‖ = ε₀/√2`), the DB gradient flow exists and
converges to a balanced flow at rate `2/(2(1+√2)²)`. -/
theorem ar_local_convergence_DB_witness :
    0 < nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
        (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) fun e => arEps0 * arWrapInd e)
      ∧ ∃ h : ℝ → Balance.EdgeSet arPol.phat → ℝ, h 0 = (fun e => arEps0 * arWrapInd e)
        ∧ Balance.IsGradientFlow (Balance.edgeKernelE arPol.phat)
            (Balance.edgeMeasureE arPol.phat arLam)
            (fun e => Balance.edgeMeasureE arPol.phat arLam e * 1) Balance.logSqDeriv
            (fun s e => 1 + h s e)
        ∧ ∃ cinf : ℝ,
            Balance.Balanced (Balance.edgeKernelE arPol.phat) (Balance.edgeMeasureE arPol.phat arLam)
              (fun _ => cinf)
            ∧ ∀ t : ℝ, 0 ≤ t
              → nrmL2 (Balance.edgeMeasureE arPol.phat arLam) (fun e => h t e - (cinf - 1))
                ≤ 2 * Real.exp (-(2 * 1 / (1 + Real.sqrt 2) ^ 2 * t / 2))
                  * nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
                      (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam)
                        fun e => arEps0 * arWrapInd e) := by
  have hperp : Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam)
      (fun e => arEps0 * arWrapInd e)
      = fun e => arEps0 * Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd e := by
    funext e
    rw [Balance.perpL2_apply, Balance.perpL2_apply, Balance.meanL2_const_mul]
    ring
  have hpos : 0 < nrmL2 (Balance.edgeMeasureE arPol.phat arLam)
      (Balance.perpL2 (Balance.edgeMeasureE arPol.phat arLam) fun e => arEps0 * arWrapInd e) := by
    rw [hperp, Balance.nrmL2_smul, abs_of_pos arEps0_pos]
    exact mul_pos arEps0_pos ar_perp_wrapInd_pos
  have hind : nrmL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd ≤ 1 := by
    have hip : ipL2 (Balance.edgeMeasureE arPol.phat arLam) arWrapInd arWrapInd = 1 / 2 := by
      simp only [ipL2, arWrapInd, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (wrapEdge arPol), if_pos (Finset.mem_univ _),
        ar_edgeMeasureE, if_pos rfl]
    rw [nrmL2, hip, Real.sqrt_le_one]
    norm_num
  have hnorm0 : nrmL2 (Balance.edgeMeasureE arPol.phat arLam) (fun e => arEps0 * arWrapInd e)
      ≤ arEps0 := by
    rw [Balance.nrmL2_smul, abs_of_pos arEps0_pos]
    nlinarith [arEps0_pos]
  obtain ⟨h, hh0, hflow, -, -, cinf, hbal, -, hdecay⟩ := local_convergence_full_DB_sigma
    (w := fun _ => (1:ℝ)) arPathConnected arPositiveOnEdges arIsInvProb arLeveled.isHitExp
    (by norm_num) Balance.logSq_C3On_bundle.1 Balance.logSq_C3On_bundle.2.1
    Balance.logSq_C3On_bundle.2.2.1 Balance.logSq_C3On_bundle.2.2.2 (fun _ => by norm_num)
    one_pos (fun _ => le_rfl) hnorm0
  refine ⟨hpos, h, hh0, hflow, cinf, hbal, fun t ht => ?_⟩
  have key := hdecay t ht
  rwa [ar_bhatSigma, Balance.logSq_deriv2_one] at key

end ArWitness

/-! ### A leveled witness with one internal state: `s₀ → x → s_f`, period `3`

Computed by hand first: the loop closure is the 3-cycle `s₀ → s_f → x → s₀`, `λ ≡ 1/3`, heights
`ℓ = (0,1,2)`, so `t_m = ℓ(s_f) − 1 = 1` and every excursion has length `3 = t_m + 2`. -/

section Tri

/-- The edges `0 → 1 → 2`. -/
def triEdgeB : Fin 3 → Fin 3 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | _, _ => false

/-- The edge relation of the three-vertex path. -/
def TriEdge (x y : Fin 3) : Prop := triEdgeB x y = true

instance : DecidableRel TriEdge := fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- **The path `s₀ → x → s_f`**, one internal state. -/
def tri : MarkedGraph (Fin 3) where
  Edge := TriEdge
  src := 0
  snk := 2
  src_ne_snk := by decide
  no_edge_into_src := by decide
  no_edge_out_of_snk := by decide

theorem triPathConnected : tri.PathConnected := by
  have e01 : tri.Edge 0 1 := rfl
  have e12 : tri.Edge 1 2 := rfl
  intro s
  fin_cases s
  · exact ⟨Relation.ReflTransGen.refl, (Relation.ReflTransGen.single e01).tail e12⟩
  · exact ⟨Relation.ReflTransGen.single e01, Relation.ReflTransGen.single e12⟩
  · exact ⟨(Relation.ReflTransGen.single e01).tail e12, Relation.ReflTransGen.refl⟩

/-- `π_←(x → s₀) = π_←(s_f → x) = 1`. -/
noncomputable def triPb (s s' : Fin 3) : ℝ :=
  if (s.val = 1 ∧ s'.val = 0) ∨ (s.val = 2 ∧ s'.val = 1) then 1 else 0

/-- The backward policy of the three-vertex path. -/
noncomputable def triPol : BackwardPolicy tri where
  pb := triPb
  nonneg := by
    intro s s'
    unfold triPb
    split_ifs <;> norm_num
  row_sum := by
    intro s hs
    fin_cases s
    · exact absurd rfl hs
    all_goals rw [Fin.sum_univ_three]; norm_num [triPb]
  supp := by
    intro s s' hs hne
    fin_cases s <;> fin_cases s' <;> simp_all [triPb, tri, TriEdge, triEdgeB]

theorem triPositiveOnEdges : triPol.PositiveOnEdges := by
  intro s s' h
  fin_cases s <;> fin_cases s' <;> simp_all [triPol, triPb, tri, TriEdge, triEdgeB]

/-- The heights `ℓ(x) = x`, i.e. `(0,1,2)`. -/
noncomputable def triLvl (x : Fin 3) : ℝ := ((x : ℕ) : ℝ)

/-- **The three-vertex path is leveled**, at `ℓ(s_f) = 2`. -/
noncomputable def triLeveled : Leveled tri where
  lvl := triLvl
  lvl_src := by simp [triLvl, tri]
  lvl_edge := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [tri, TriEdge, triEdgeB, triLvl]
    all_goals norm_num

/-- The uniform law `λ ≡ 1/3`. -/
noncomputable def triLam : Fin 3 → ℝ := fun _ => 1 / 3

theorem triIsInvProb : triPol.IsInvProb triLam := by
  refine ⟨fun x => by norm_num [triLam], by norm_num [Fin.sum_univ_three, triLam], fun y => ?_⟩
  fin_cases y <;>
    simp [Fin.sum_univ_three, triLam, BackwardPolicy.phat, triPol, triPb, tri]

/-- **`prop:morozov_rate`, closing paragraph, on a leveled graph with an internal state.** On
`s₀ → x → s_f`: `t_m = 1`, the loop closure returns to `s₀` in `3` steps and only at multiples of
`3`, `‖P^n − Π‖ ≥ 1` for every `n`, and the mixing sum is `+∞`. -/
theorem tri_leveled_mixing_check :
    triLeveled.lvl tri.snk - 1 = 1
      ∧ 0 < (Matrix.of triPol.phat ^ 3) tri.src tri.src
      ∧ (∀ n : ℕ, 0 < (Matrix.of triPol.phat ^ n) tri.src tri.src → 3 ∣ n)
      ∧ (∀ n : ℕ, 1 ≤ Core.Mixing.beta (Balance.densOp triLam triPol.phat) (Balance.meanOp triLam) n)
      ∧ ∑' n : ℕ, ENNReal.ofReal
          (Core.Mixing.beta (Balance.densOp triLam triPol.phat) (Balance.meanOp triLam) n) = ⊤ := by
  obtain ⟨tm, htm, hpow, hdvd⟩ := triLeveled.periodic triPathConnected triPositiveOnEdges
  have hsnk : triLeveled.lvl tri.snk = 2 := by
    simp [triLeveled, triLvl, tri]
  have htm1 : tm = 1 := by
    rw [hsnk] at htm
    exact_mod_cast (show (tm : ℝ) = 1 by linarith)
  subst htm1
  exact ⟨by rw [hsnk]; norm_num, hpow, hdvd,
    triLeveled.one_le_beta triPathConnected triPositiveOnEdges triIsInvProb,
    triLeveled.mixing_sum_eq_top triPathConnected triPositiveOnEdges triIsInvProb⟩

end Tri

end GFNBounds.Graph
