import GFNBounds.Balance.BoundaryBlowup
import GFNBounds.Balance.RatioBridge
import GFNBounds.Balance.LogSqTaylor
import GFNBounds.Graph.Morozov
import GFNBounds.Graph.CycleExample

/-!
# The training-speed theorem, assembled: two phases, and every constant in `σ_*`, `σ̄`, `N_min`

**`theo:training_speed_full`** — statement `proofs.tex:900–920`, proof `proofs.tex:922–934`.
It quotes `prop:no_distant_equilibrium` (`proofs.tex:787–814`), `cor:global_lojasiewicz`
(`proofs.tex:875–898`) and `prop:morozov_rate` (`proofs.tex:834–873`), and reads
`theo:local_convergence_full` (`proofs.tex:612–657`) at the rescaled entry point.
(The bold-backtick form of the label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> In the setting above, let `g = (log x)²` — the generator of the practical DB and TB losses —
> and let `ν = wλ` with `w ≥ w_min > 0`. Then the invariant measure of the backward chain is the
> visit ratio, `λ(x) = N(x)/(2+σ̄)`, so `λ_min = N_min/(2+σ̄)`, and, from *every* initialization
> `μ₀ ∼ λ`, the gradient flow of `𝓛_{g,ν}` converges to the balanced flow of its sphere, in two
> phases:
> *(1)* **global phase** — the loss obeys a Łojasiewicz inequality `−𝓛̇ ≥ κ²𝓛²`, hence decays at
> the universal rate `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1} + κ²t)^{−1}`, with
> `κ := w_min λ_min^{1/2}/(‖u₀‖_{L²(λ)}‖w‖_{L^∞}M)` and `M := max(1, √(𝓛(μ₀)/(w_min λ_min)))`;
> *(2)* **local phase** — after an explicit time `T₀`, the flow enters the neighbourhood of
> Theorem `theo:local_convergence` and converges exponentially at rate `ϱ_σ/(2m₁²)` —
> `m₁ ∈ [m₀, ‖u₀‖]` the flow's mass at the crossover, so exactly `ϱ_σ/2` once the entry point is
> rescaled to unit mass — where `ϱ_σ = g''(1)w_min λ_min/σ_*² = 2w_min N_min/(σ_*²(2+σ̄))`.
>
> Every constant's dependence on the graph and the backward policy runs through `σ_*`, `σ̄` and
> `N_min` alone; the initialization enters through `‖u₀‖`, `m₀` and `𝓛(μ₀)`, and the training
> measure through `w_min` and `‖w‖_{L^∞}`. **No mixing, spectral-gap or aperiodicity hypothesis
> is used.**

> (proof, global phase) The generator `g = (log x)²` is strictly unimodal, so Proposition
> `prop:no_distant_equilibrium`*(3)* applies: the gradient flow from any `μ₀ ∼ λ` stays in a
> compact subset of its sphere and converges to the balanced flow of that sphere. Inequality
> `eq:global_phase`, with the stated `M` and `κ`, is Corollary `cor:global_lojasiewicz`.

> (proof, local phase) By `prop:no_distant_equilibrium`*(3)* again, all ratios are within `δ` of
> `1` after a time at most `𝓛(μ₀)/c(δ)²` with `c(δ) = w_min λ_min^{3/2}δ²/(2‖u₀‖)`, and the
> choice `δ₀ = ε₀m₀/(B̂_σ‖u₀‖)` places the rescaled flow inside the neighbourhood of Theorem
> `theo:local_convergence`; the crossover time is therefore
> `T₀ = 𝓛(μ₀)/c(δ₀)² = 4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)` […] Theorem
> `theo:local_convergence` then gives the exponential decay at rate `ϱ/2` in the rescaled time;
> rescaling the entry point to unit mass divides the gradient field by `m₁` (homogeneity) and
> hence dilates time by `m₁²` […] every occurrence of `B̂` may be replaced by
> `B̂_σ = σ_*/λ_min^{1/2}`, and `ϱ` by `ϱ_σ = g''(1)w_min/B̂_σ²`.

## Why this file exists

Everything the theorem consumes was closed elsewhere: `theo:universality_graphs`*(1)*
(`GFNBounds/Graph/Setting.lean`, through `IsInvProb.pos`), `prop:morozov_rate`*(1)*–*(2)*
(`GFNBounds/Graph/Morozov.lean`), `cor:global_lojasiewicz` at the printed `κ` and `M`
(`GFNBounds/Balance/MassAscent.lean`), the invariant sphere and the monotone mass ascent
(`GFNBounds/Balance/Flow.lean`, `MassAscent.lean`), the entry time and the homogeneity
(`MassAscent.lean`), the ratio-to-density conversion (`GFNBounds/Balance/RatioBridge.lean`), the
local exponential phase (`GFNBounds/Balance/LocalConvergence.lean`), the `(log x)²` Taylor
bound (`GFNBounds/Balance/LogSqTaylor.lean`) and — since 2026-09-13 — the positivity of the
trajectory itself (`GFNBounds/Balance/BoundaryBlowup.lean`, `flow_pos_graph`), which
`training_speed_full_of_pos` spends to remove the theorem's last hypothesis about the
trajectory. **This file is the assembly**, and the work in it
is making the hypotheses honest: three of them the paper never states, and all three are
discharged here rather than added.

## What is proved

| | |
|---|---|
| `BhatSigma`, `rhoSigma`, `T0`, `eps0Sq` | the constants, as the paper's printed formulas (kb 0007). `RatioBridge.delta0`, `MassAscent.cDelta` and `LocalConvergence.eps0/epsW/Cinf` are reused, not restated |
| `minOver_div_const`, **`minOver_lam_eq`** | **`λ_min = N_min/(2+σ̄)`** (`proofs.tex:906`), from `prop:morozov_rate`*(1)* |
| `one_le_sigmaStar`, `minOver_le_one`, **`one_le_BhatSigma`**, `BhatSigma_pos` | **`1 ≤ B̂_σ` derived, not assumed** — `σ_* ≥ 1` because the hitting time from `s_f` is `1 + Qσ` with `σ ≥ 0`, and `λ_min ≤ 1` because `λ` is a probability. `LocalConvergence.lean` and `RatioBridge.lean` both *add* this hypothesis; it is nobody's no longer |
| **`hcoer_of_graph`** | the coercivity hypothesis every downstream file takes, discharged from `Graph.BackwardPolicy.coercivity_lamMin` at `B̂ := B̂_σ`. The two shapes are reconciled by `L2Toolkit.nrmL2_neg`: `coercivity_lamMin` is stated at `h − Ph`, and `Aop` is `Ph − h` |
| `rhoL_eq_rhoSigma`, `rhoSigma_eq_visits` | `ϱ = g''(1)w_min/B̂_σ² = g''(1)w_min λ_min/σ_*²`, and `= 2w_min N_min/(σ_*²(2+σ̄))` at `g''(1) = 2` — the theorem's two printed forms of `ϱ_σ` |
| **`T0_eq`** | **`T₀ = 4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)`** (`proofs.tex:929`), **exact, exponent for exponent** |
| `flow_translate`, `flow_unit_mass` | the two shims `LocalConvergence.lean` leaves to the caller: time translation, and the unit-mass rescaling that divides the gradient field by `m₁` and dilates time by `m₁²`. Both are `MassAscent.flow_rescale`, at `c = 1` and at `c = m₁` |
| `eps0_le_half`, **`eps0Sq_le_half`**, `eps0Sq_pos` | `ε₀ ≤ 1/2` — in fact `ε₀ ≤ 1/16`, since `ε ≤ 1/4`, `C_∞ ≥ 1` and `C₇ ≥ 0` |
| **`delta0Sq_le_half`** | **`δ₀ ≤ 1/2`**, the side condition `MassAscent.entry_time` imposes on its `δ` and `proofs.tex:927` does not check |
| **`logSqDeriv_taylor_half`** | the `C³` side condition, as the Taylor bound Theorem 10 consumes: `a = 1/2`, `g''(1) = 2`, **`M₃ = 24`** — `LogSqTaylor.logSqDeriv_taylor_twelve`, sharper than the `M₃ = 80` the paper's own third-derivative reading gives |
| **`entry_and_rescale`** | `proofs.tex:927–930` in one statement: a crossover `t₁ ≤ T₀` with every ratio within `δ₀`, `m₀ ≤ m₁ ≤ ‖u₀‖`, the rescaled curve again a gradient flow, and its deviation starting inside the `ε₀`-ball |
| **`training_speed_full`** | **the theorem** — the visit-ratio identity, the global Łojasiewicz decay at the printed `κ` and `M`, and the local exponential phase at rate `ϱ_σ/(2m₁²)` in the *original* time variable, with the limit a constant density and hence balanced. Conditional on positivity of the trajectory on `[0,∞)` |
| **`training_speed_full_of_pos`** | **the same conclusion, unconditional on the trajectory**: `hu0 : ∀ x, 0 < u 0 x` — the paper's own "from *every* initialization `μ₀ ∼ λ`" — plus the edge floor `BoundaryBlowup.flow_pos_graph` needs |
| **`training_speed_full_of_init`** | **the same conclusion on the paper's own hypotheses, and no others**: the edge floor is discharged too, by `exists_edgeFloor`, which is never vacuous on a finite state space. Nothing about the trajectory, no mixing constant, no spectral gap, no aperiodicity — only path-connectedness, a positive backward policy, `λ` invariant, `ν = wλ` with `w ≥ w_min > 0`, `μ₀ ∼ λ`, and the flow itself |
| `cycle_minOver_lam`, **`cycle_training_speed_check`**, **`cycle_training_speed_check_half`** | the constants **evaluated** on `rem:cycle_no_stalemate`'s five-vertex cycle: `λ_min = (1−p)/(5−2p)` and `ϱ_σ = 2(1−p)³/((5−2p)(4−p)²)`; at `p = 1/2`, `λ_min = 1/8`, `σ_* = 7`, `N_min = 1`, `B̂_σ = 14√2`, `ϱ_σ = 1/196`, and `T₀ = 3.147…×10¹⁶` at `𝓛(μ₀) = ‖u₀‖ = m₀ = w_min = 1` and `ε₀ = 1/100` |

## Hypothesis checklist — `theo:training_speed_full`

| paper hypothesis | here |
|---|---|
| "in the setting above": the loop closure of a **finite** path-connected marked graph with a backward policy positive on its edges | ✓ `hpc : G.PathConnected`, `hpos : B.PositiveOnEdges`, `[Fintype V]`; the kernel is `B.phat`, the loop closure itself |
| `λ` its invariant probability | ✓ `hl : B.IsInvProb lam`, inhabited by `Graph.BackwardPolicy.exists_invProb`. `λ > 0` is `IsInvProb.pos`, i.e. `theo:universality_graphs`*(1)* |
| `σ(x)` a hitting time, `N(x)` an expected visit count | ⚠ **carried as the linear systems `prop:morozov_rate` is formalized through**: `hhit : B.IsHitExp uH` and `hg : B.IsGreen gr`, inhabited by `exists_isHitExp` and `exists_isGreen`. Reading them as chain objects is `GFNBounds/Graph/Morozov.lean`'s disclosed modelling step |
| `g = (log x)²` | ✓ `logSq`, `logSqDeriv`. ⚠ `logSqDeriv` is the *definition* `2 log x/x`, not a derivative — inherited from `GFNBounds/Balance/Lojasiewicz.lean` |
| `ν = wλ` with `w ≥ w_min > 0` | ✓ `nu = fun x => lam x * wf x`, `hwmin : 0 < wmin`, `hw : ∀ x, wmin ≤ wf x` |
| the `‖w‖_{L^∞}` that `κ` and `C₆` name | ⚠ **a parameter** `wsup` with `hwsup : ∀ x, wf x ≤ wsup`, not a supremum; the theorem names it without hypothesising it |
| "from **every** initialization `μ₀ ∼ λ`" | ✓ `training_speed_full_of_pos` takes `hu0 : ∀ x, 0 < u 0 x` and nothing about the trajectory, `BoundaryBlowup.flow_pos_graph` — item *(3)*'s compactness sentence, proved — supplying the rest. and `training_speed_full_of_init` discharges the edge floor as well (`exists_edgeFloor`), leaving **no hypothesis the paper does not have**. `training_speed_full` keeps the conditional form, with `hu` now ranged over `[0,∞)`, and is what `MorozovConsume` cites. See SCOPE, first bullet |
| the gradient flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` | ⚠ `hflow : IsGradientFlow B.phat lam (λw) logSqDeriv u`, hypothesised of a given curve; no existence theorem, as everywhere in `GFNBounds.Balance` |
| `eq:occupation`: `λ(x) = N(x)/(2+σ̄)`, hence `λ_min = N_min/(2+σ̄)` | ✓ conjuncts *(i)* and *(ii)* of the theorem below |
| "converges to the balanced flow of its sphere" | ⚠ **read as the displayed estimate plus the limit's balance**: `‖u_t/m₁ − c_∞‖_{L²(λ)} → 0` geometrically, and `Balanced B.phat lam (fun _ => c_∞)`. No statement about `μ_t` as a measure is made, and the sphere is not named in the conclusion |
| global phase: `−𝓛̇ ≥ κ²𝓛²` and `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1}+κ²t)^{−1}` at the printed `κ` and `M` | ✓ **verbatim** `MassAscent.global_lojasiewicz_flow'`'s display, `M` and `κ` the printed formulas |
| "after an explicit time `T₀`" | ⚠ **`∃ t₁ ∈ [0,T₀]`**, not "after `T₀`, forever". Inherited from `MassAscent.entry_time`, whose budget argument bounds the total off-band time; permanence past `t₁` is `theo:local_convergence_full`'s and *is* delivered, for every `t ≥ t₁` |
| `T₀ = 4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)` | ✓ `T0_eq`, exact |
| local rate `ϱ_σ/(2m₁²)`, with `m₁ ∈ [m₀,‖u₀‖]` | ✓ both, and the decay is stated in the original time variable |
| `ϱ_σ = g''(1)w_min λ_min/σ_*² = 2w_min N_min/(σ_*²(2+σ̄))` | ✓ `rhoSigma`, `rhoL_eq_rhoSigma`, `rhoSigma_eq_visits` |
| `B̂_σ = σ_*/λ_min^{1/2}` and `δ₀ = ε₀m₀/(B̂_σ‖u₀‖)` | ✓ `BhatSigma`, `RatioBridge.delta0` |
| `1 ≤ B̂_σ` | ⚠ **not in the paper, and required by two files that add it as a hypothesis** — `one_le_BhatSigma` **derives** it here, from `σ_* ≥ 1` and `λ_min ≤ 1` |
| `ε₀ ≤ 1/2` and `δ₀ ≤ 1/2` | ⚠ **not in the paper**: `proofs.tex:927` reads `entry_time` at `δ₀` without checking `entry_time`'s own `δ ∈ (0,½]`. Both **proved** (`eps0Sq_le_half`, `delta0Sq_le_half`) |
| `g` is `C³` on `[1−a,1+a]` with `M₃` its third-derivative bound — Theorem `theo:local_convergence`'s hypothesis, which this theorem invokes without checking | ⚠ **discharged here at `a = 1/2`, `M₃ = 24`** (`logSqDeriv_taylor_half`), in the weakened Taylor form `Expansion.lean` consumes. The paper's own reading gives `M₃ = 80`; `24` is sharper and is the one taken |
| "No mixing, spectral-gap or aperiodicity hypothesis is used" | ✓ **literally true of the signature below**: no `Core.Mixing`, no `B̂ = ∑β̂_n`, no spectral gap, no aperiodicity, and no lazification. The coercivity is *derived* from hitting times at `s₀` (`hcoer_of_graph`) |

## SCOPE (disclosed)

* **Half of the compactness/LaSalle layer is now proved, and it is the half this theorem
  needs.** `prop:no_distant_equilibrium`*(3)* gets the trajectory's positivity from the boundary
  blow-up of `𝓛` — "if `u(x) → 0` at some state while `‖u‖ = ‖u₀‖`, strong connectedness provides
  an edge from a non-vanishing state into the vanishing region, whose ratio explodes" — and only
  then invokes LaSalle's principle. **The blow-up is formalized**, in
  `GFNBounds/Balance/BoundaryBlowup.lean`, in the quantitative form `u_t ≥ u_min > 0` on
  `[0,∞)`; `flow_pos_graph` is that statement on the loop closure of a finite path-connected
  marked graph, and `training_speed_full_of_pos` is this theorem with `hu` discharged by it, from
  `hu0 : ∀ x, 0 < u 0 x` alone. **LaSalle is not**: Mathlib v4.31.0 has no `ω`-limit set, and
  `BoundaryBlowup.mass_tendsto` delivers only that the mass converges. That costs nothing here,
  because what is claimed is the *quantitative* route, which needs only the positivity: the entry
  time (`MassAscent.entry_time`) and `theo:local_convergence_full`. **The convergence half of
  `prop:no_distant_equilibrium`*(3)* is still not proved, not used and not laundered**: the
  convergence in conjunct *(iii)* below is Theorem `theo:local_convergence_full`'s, with its own
  proof and its own constants.
* **What discharging `hu` costs.** `flow_pos_graph` replaces it with `hu0` **plus** an edge floor
  `0 < p_min ≤ 1` with `p_min ≤ π̂_←(y→z)` on every edge carrying mass — a constant the paper does
  not name, and which `BoundaryBlowup.exists_edgeFloor` shows always exists on a finite state
  space. `training_speed_full` is therefore kept in its conditional form beside
  `training_speed_full_of_pos`, and is what `MorozovConsume` and the map's row still cite; its
  `hu` is ranged over `[0,∞)`, which is where `flow_pos_graph` proves it (kb `0022`, resolved
  2026-09-13).
* **The crossover is an existence, not a permanence.** `∃ t₁ ∈ [0,T₀]` is what the loss-budget
  argument delivers; the flow could in principle leave the band and return, and only the local
  theorem forbids it — which it then does, for every `t ≥ t₁`.
* **Finite state space**, as everywhere in `GFNBounds.Balance` and `GFNBounds.Graph`: `∫·dλ` is
  `∑ x, lam x * ·`, and `⟪·∣·⟫_λ`, `‖·‖_λ`, `Π` are `Graph.ipL2`, `Graph.nrmL2`, `Graph.meanL2`.
  The paper's own statement is on a finite state space, so nothing is weakened by this.
* **`D` is `Flow.lossGrad`, which is a definition.** That it represents `∇^λ𝓛_{g,ν}` is
  `theo:first_variation_full`, disclosed in `GFNBounds/Balance/FirstVariation.lean`; nothing
  below re-derives it.
* **`theo:universality_graphs`*(2)* is quoted by the proof and is not consumed here.** The
  opening paragraph recalls that the balanced flow exists and is unique up to scale; the
  assembly uses only `λ > 0`, which is *(1)*. Existence and uniqueness live in
  `GFNBounds/Graph/Universality.lean` and are not restated.
* **The theorem's `C ≥ 1` and the shape of the basin are `theo:local_convergence_full`'s**, with
  the findings recorded there (the proof produces `C₇`, which may be below `1`; `ε₀` is the
  paper's and not the wider basin `LocalEnergy.mean_cauchy_on_sharp` would allow). This file
  changes neither, and states the theorem on the paper's `ε₀`.
* **`sorry`-free and axiom-clean.** `#print axioms` on `training_speed_full`,
  `training_speed_full_of_pos`, `entry_and_rescale`, `T0_eq`, `one_le_BhatSigma`, `hcoer_of_graph`, `minOver_lam_eq`,
  `delta0Sq_le_half`, `eps0Sq_le_half`, `flow_translate`, `flow_unit_mass`,
  `logSqDeriv_taylor_half`, `rhoL_eq_rhoSigma`, `rhoSigma_eq_visits`,
  `cycle_training_speed_check` and `cycle_training_speed_check_half` returns
  `[propext, Classical.choice, Quot.sound]`. Graduated into the strict library on 2026-09-12.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The three constants -/

/-- **`B̂_σ := σ_*/√λ_min`** (`proofs.tex:931`). -/
noncomputable def BhatSigma (G : Graph.MarkedGraph V) (uH lam : V → ℝ) : ℝ :=
  Graph.sigmaStar G uH / Real.sqrt (Graph.minOver G lam)

omit [DecidableEq V] in
theorem BhatSigma_eq (G : Graph.MarkedGraph V) (uH lam : V → ℝ) :
    BhatSigma G uH lam = Graph.sigmaStar G uH / Real.sqrt (Graph.minOver G lam) := rfl

/-- **`ϱ_σ := g''(1) w_min λ_min/σ_*²`** (`proofs.tex:919`). -/
noncomputable def rhoSigma (g2 wmin lamMin sigmaStar : ℝ) : ℝ :=
  g2 * wmin * lamMin / sigmaStar ^ 2

/-- **`T₀ := 𝓛(μ₀)/c(δ₀)²`** (`proofs.tex:929`). -/
noncomputable def T0 (L0 cDel : ℝ) : ℝ := L0 / cDel ^ 2

/-! ### `λ_min = N_min/(2+σ̄)` -/

omit [DecidableEq V] in
/-- Dividing a function by a positive constant divides its minimum by it. -/
theorem minOver_div_const {G : Graph.MarkedGraph V} {f h : V → ℝ} {c : ℝ} (hc : 0 < c)
    (hfh : ∀ x, f x = h x / c) : Graph.minOver G f = Graph.minOver G h / c := by
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V) h ⟨G.src, Finset.mem_univ _⟩
  have hmin : Graph.minOver G h = h x0 :=
    le_antisymm (Graph.minOver_le h x0) (Graph.le_minOver fun z => hx0 z (Finset.mem_univ z))
  refine le_antisymm ?_ (Graph.le_minOver fun x => ?_)
  · rw [hmin, ← hfh x0]
    exact Graph.minOver_le f x0
  · rw [hfh x, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Graph.minOver_le h x) (inv_nonneg.mpr hc.le)

/-- **`λ_min = N_min/(2+σ̄)`** (`proofs.tex:906`), from `prop:morozov_rate`*(1)*. -/
theorem minOver_lam_eq {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam g uH : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hhit : B.IsHitExp uH) :
    Graph.minOver G lam = Graph.minOver G (Graph.visits G g) / (2 + B.sigmaBar uH) :=
  minOver_div_const (Graph.BackwardPolicy.two_add_sigmaBar_pos hhit)
    (Graph.BackwardPolicy.lam_eq_visits_div hpc hpos hl hg hhit)

/-! ### `1 ≤ B̂_σ` -/

/-- `1 ≤ σ_*`: the hitting time of `s₀` from `s_f` is `1 + Qσ ≥ 1`, and `σ_*` is a maximum. -/
theorem one_le_sigmaStar {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G} {uH : V → ℝ}
    (hhit : B.IsHitExp uH) : 1 ≤ Graph.sigmaStar G uH := by
  have hsnk : uH G.snk = 1 + B.qact uH G.snk := hhit.2 G.snk (Ne.symm G.src_ne_snk)
  have hq : (0:ℝ) ≤ B.qact uH G.snk :=
    Graph.BackwardPolicy.le_qact (fun y => hhit.nonneg y) G.snk
  exact le_trans (by linarith) (Graph.le_sigmaStar uH G.snk)

omit [DecidableEq V] in
/-- `λ_min ≤ 1` on a probability `λ`. -/
theorem minOver_le_one {G : Graph.MarkedGraph V} {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x)
    (htot : ∑ x, lam x = 1) : Graph.minOver G lam ≤ 1 := by
  refine le_trans (Graph.minOver_le lam G.src) ?_
  rw [← htot]
  exact Finset.single_le_sum (f := lam) (fun i _ => hnn i) (Finset.mem_univ G.src)

/-- **`1 ≤ B̂_σ`** — derived, not assumed: `σ_* ≥ 1` and `λ_min ≤ 1`, so `√λ_min ≤ 1 ≤ σ_*`. -/
theorem one_le_BhatSigma {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G} {lam uH : V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH) : 1 ≤ BhatSigma G uH lam := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hmin : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hle1 : Graph.minOver G lam ≤ 1 := minOver_le_one (fun x => (hp x).le) hl.total
  have hsq : Real.sqrt (Graph.minOver G lam) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hle1
  have hsqpos : 0 < Real.sqrt (Graph.minOver G lam) := Real.sqrt_pos.mpr hmin
  rw [BhatSigma, le_div_iff₀ hsqpos, one_mul]
  exact le_trans hsq (one_le_sigmaStar hhit)

theorem BhatSigma_pos {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G} {lam uH : V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH) : 0 < BhatSigma G uH lam :=
  lt_of_lt_of_le zero_lt_one (one_le_BhatSigma hpc hpos hl hhit)

/-! ### The coercivity hypothesis, discharged -/

/-- **`hcoer` at `B̂ := B̂_σ`**, from `prop:morozov_rate`*(2)* in its `σ_*/√λ_min` form. -/
theorem hcoer_of_graph {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G} {lam uH : V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH) (f : V → ℝ) :
    Graph.nrmL2 lam (perpL2 lam f)
      ≤ BhatSigma G uH lam * Graph.nrmL2 lam (Aop B.phat lam f) := by
  have hneg : Aop B.phat lam f = fun y => -((fun z => f z - B.pdens lam f z) y) := by
    funext y
    show Core.densAct lam B.phat f y - f y = -(f y - B.pdens lam f y)
    have hpd : Core.densAct lam B.phat f y = B.pdens lam f y := rfl
    rw [hpd]; ring
  rw [perpL2_eq, hneg, nrmL2_neg, BhatSigma]
  exact Graph.BackwardPolicy.coercivity_lamMin hpc hpos hl hhit f

/-! ### `ϱ_σ` is `ϱ` read at `B̂_σ` -/

omit [DecidableEq V] in
/-- **`ϱ = g''(1)w_min/B̂_σ² = g''(1)w_min λ_min/σ_*²`** (`proofs.tex:919`, `:931`). -/
theorem rhoL_eq_rhoSigma {G : Graph.MarkedGraph V} {uH lam : V → ℝ} {g2 wmin : ℝ}
    (hlmin0 : 0 < Graph.minOver G lam) :
    rhoL g2 wmin (BhatSigma G uH lam)
      = rhoSigma g2 wmin (Graph.minOver G lam) (Graph.sigmaStar G uH) := by
  have hs : Real.sqrt (Graph.minOver G lam) ^ 2 = Graph.minOver G lam :=
    Real.sq_sqrt hlmin0.le
  rw [rhoL, rhoSigma, BhatSigma, div_pow, hs, div_div_eq_mul_div]

/-- **`ϱ_σ = 2 w_min N_min/(σ_*²(2+σ̄))`** (`proofs.tex:919`) at `g''(1) = 2`. -/
theorem rhoSigma_eq_visits {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam g uH : V → ℝ} {wmin : ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hhit : B.IsHitExp uH) :
    rhoSigma 2 wmin (Graph.minOver G lam) (Graph.sigmaStar G uH)
      = 2 * wmin * Graph.minOver G (Graph.visits G g)
        / (Graph.sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)) := by
  have hsb : (0:ℝ) < 2 + B.sigmaBar uH := Graph.BackwardPolicy.two_add_sigmaBar_pos hhit
  rw [rhoSigma, minOver_lam_eq hpc hpos hl hg hhit]
  field_simp

/-! ### `T₀`, in the paper's printed form -/

/-- **`T₀ = 4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)`** (`proofs.tex:929`), exact. -/
theorem T0_eq {L0 wmin lamMin U0 eps0 m0 sigStar : ℝ} (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hU0 : 0 < U0) (heps0 : 0 < eps0) (hm0 : 0 < m0)
    (hsig : 0 < sigStar) :
    T0 L0 (cDelta wmin lamMin U0 (delta0 eps0 m0 (sigStar / Real.sqrt lamMin) U0))
      = 4 * L0 * U0 ^ 6 * sigStar ^ 4 / (wmin ^ 2 * eps0 ^ 4 * m0 ^ 4 * lamMin ^ 5) := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ lamMin = s ^ 2 :=
    ⟨Real.sqrt lamMin, Real.sqrt_pos.mpr hlmin0, (Real.sq_sqrt hlmin0.le).symm⟩
  rw [T0, cDelta, delta0, Real.sqrt_sq hs0.le]
  field_simp
  ring

/-! ### The two shims the caller owes `theo:local_convergence_full` -/

omit [DecidableEq V] in
/-- **Time translation**: `s ↦ u_{t₁+s}` is again a gradient flow. `MassAscent.flow_rescale` at
`c = 1`; Theorem 10's statements start their curve at `0`, and the assembly enters at `t₁`. -/
theorem flow_translate {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd u) (t₁ : ℝ) :
    IsGradientFlow K lam nu gd (fun s x => u (t₁ + s) x) := by
  simpa using flow_rescale hflow (c := 1) one_pos t₁

omit [DecidableEq V] in
/-- **The rescaling to unit mass** (`proofs.tex:813`, `:930`): dividing the state by `m` and
dilating time by `m²` again solves the ODE. `MassAscent.flow_rescale` at `c = m`. -/
theorem flow_unit_mass {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd u) {m : ℝ} (hm : 0 < m) (t₁ : ℝ) :
    IsGradientFlow K lam nu gd (fun s x => u (t₁ + m ^ 2 * s) x / m) := by
  simpa [div_eq_inv_mul] using flow_rescale hflow hm t₁

/-! ### The basin radius at `g = (log x)²` -/

/-- **`ε₀` of `theo:local_convergence_full`, instantiated at `g = (log x)²`**: `a = 1/2`,
`g''(1) = 2`, `M₃ = 24` (the sharper of the two constants `LogSqTaylor` supplies). -/
noncomputable def eps0Sq (wmin wsup Bhat lamMin : ℝ) : ℝ :=
  eps0 (epsW (1/2) 2 wmin (Kexp 2 (1/2) 24 wsup) Bhat) (Cinf lamMin)
    (C7 (C6 (Cg 2 (1/2) 24) wsup) 2 wmin) (rhoL 2 wmin Bhat) (C6 (Cg 2 (1/2) 24) wsup)

omit [DecidableEq V] in
/-- **`ε₀ ≤ 1/2`** for any basin radius of Step 4 whose window is `≤ 1/4`: `ε₀ ≤ ε/(2C_∞(2+C₇))`
with `ε ≤ 1/4`, `C_∞ ≥ 1` and `C₇ ≥ 0`, so in fact `ε₀ ≤ 1/16`. -/
theorem eps0_le_half {eW Ci c7 rho c6 : ℝ} (heW : eW ≤ 1/4) (hCi : 1 ≤ Ci) (hc7 : 0 ≤ c7) :
    eps0 eW Ci c7 rho c6 ≤ 1/2 := by
  refine le_trans (eps0_le_basin eW Ci c7 rho c6) ?_
  have hden : (4:ℝ) ≤ 2 * Ci * (2 + c7) := by nlinarith
  have hdpos : (0:ℝ) < 2 * Ci * (2 + c7) := by linarith
  rw [div_le_iff₀ hdpos]
  linarith

omit [DecidableEq V] in
/-- **`ε₀ ≤ 1/2` at `g = (log x)²`** — the side condition `MassAscent.entry_time` needs of `δ₀`
and the paper never states, discharged rather than assumed. -/
theorem eps0Sq_le_half {lam : V → ℝ} {lamMin wmin wsup Bhat : ℝ}
    (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x) (htot : ∑ x, lam x = 1)
    (hwmin : 0 < wmin) (hwsup : 0 < wsup) :
    eps0Sq wmin wsup Bhat lamMin ≤ 1/2 := by
  refine eps0_le_half ?_ (one_le_Cinf hlmin0 hlmin htot)
    (C7_nonneg (C6_pos (by norm_num) (by norm_num) (by norm_num) hwsup).le (by positivity))
  exact le_trans (epsW_le_window (1/2) 2 wmin (Kexp 2 (1/2) 24 wsup) Bhat) (by norm_num)

theorem eps0Sq_pos {lamMin wmin wsup Bhat : ℝ} (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hwsup : 0 < wsup) (hB : 0 < Bhat) :
    0 < eps0Sq wmin wsup Bhat lamMin :=
  eps0_pos (epsW_pos (by norm_num) (by norm_num) hwmin
      (Kexp_pos (by norm_num) (by norm_num) (by norm_num) hwsup) hB)
    (Cinf_pos hlmin0)
    (C7_nonneg (C6_pos (by norm_num) (by norm_num) (by norm_num) hwsup).le (by positivity))
    (rhoL_pos (by linarith) hB) (C6_pos (by norm_num) (by norm_num) (by norm_num) hwsup)

/-- **`δ₀ ≤ 1/2`** — the side condition `MassAscent.entry_time` imposes on its `δ` and which
`proofs.tex:927` reads `entry_time` at `δ₀` without checking. It holds at `ε₀ = ε₀Sq`, and
`m₀ ≤ ‖u₀‖` (Cauchy–Schwarz) and `B̂_σ ≥ 1` are what buy it. -/
theorem delta0Sq_le_half {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH u0 : V → ℝ} {wmin wsup : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH) (hwmin : 0 < wmin) (hwsup : 0 < wsup) (hu0 : ∀ x, 0 < u0 x) :
    delta0 (eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
        (Graph.meanL2 lam u0) (BhatSigma G uH lam) (Graph.nrmL2 lam u0) ≤ 1/2 := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hB1 : 1 ≤ BhatSigma G uH lam := one_le_BhatSigma hpc hpos hl hhit
  have hm0 : 0 < Graph.meanL2 lam u0 :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (hu0 i)) ⟨G.src, Finset.mem_univ _⟩
  have hmU : Graph.meanL2 lam u0 ≤ Graph.nrmL2 lam u0 :=
    (mean_le_nrmL2_iff_const hp hl.total (fun x => (hu0 x).le)).1
  exact delta0_le_half
    (eps0Sq_pos hlmin0 hwmin hwsup (lt_of_lt_of_le zero_lt_one hB1)).le
    (eps0Sq_le_half hlmin0 (fun x => Graph.minOver_le lam x) hl.total hwmin hwsup)
    hm0 hB1 hmU

/-! ### The entry time, and the entry point rescaled to unit mass -/

/-- **`proofs.tex:927–930` in one statement**: at a crossover time `t₁ ≤ T₀` every ratio is
within `δ₀` of `1`, the mass has risen to `m₁ ∈ [m₀, ‖u₀‖]`, and the curve
`s ↦ u_{t₁+m₁²s}/m₁` is again a gradient flow whose deviation from `1` starts inside the
`ε₀`-ball of `theo:local_convergence_full`. -/
theorem entry_and_rescale {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH wf : V → ℝ} {wmin eps0 : ℝ} {u : ℝ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x) (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (heps0 : 0 < eps0) (heps1 : eps0 ≤ 1/2)
    (hflow : IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u) :
    ∃ t₁ ∈ Set.Icc (0:ℝ)
        (T0 (lossVal lam wf logSq (ratio B.phat lam (u 0)))
          (cDelta wmin (Graph.minOver G lam) (Graph.nrmL2 lam (u 0))
            (delta0 eps0 (Graph.meanL2 lam (u 0)) (BhatSigma G uH lam)
              (Graph.nrmL2 lam (u 0))))),
      (∀ x, |ratio B.phat lam (u t₁) x - 1|
          < delta0 eps0 (Graph.meanL2 lam (u 0)) (BhatSigma G uH lam) (Graph.nrmL2 lam (u 0)))
        ∧ Graph.meanL2 lam (u 0) ≤ Graph.meanL2 lam (u t₁)
        ∧ Graph.meanL2 lam (u t₁) ≤ Graph.nrmL2 lam (u 0)
        ∧ 0 < Graph.meanL2 lam (u t₁)
        ∧ IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv
            (fun s x => u (t₁ + Graph.meanL2 lam (u t₁) ^ 2 * s) x / Graph.meanL2 lam (u t₁))
        ∧ Graph.meanL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1) = 0
        ∧ Graph.nrmL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1) ≤ eps0 := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hp x).le
  have htot : ∑ x, lam x = 1 := hl.total
  have hinv : Invariant B.phat lam := hl.inv
  have hKnn : ∀ x y, 0 ≤ B.phat x y := fun x y => B.phat_nonneg x y
  have hlmin : ∀ x, Graph.minOver G lam ≤ lam x := fun x => Graph.minOver_le lam x
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hnu : ∀ x, 0 < lam x * wf x := fun x => mul_pos (hp x) (lt_of_lt_of_le hwmin (hw x))
  have hm0 : 0 < Graph.meanL2 lam (u 0) :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (hu 0 le_rfl i)) ⟨G.src, Finset.mem_univ _⟩
  have hmU : Graph.meanL2 lam (u 0) ≤ Graph.nrmL2 lam (u 0) :=
    (mean_le_nrmL2_iff_const hp htot (fun x => (hu 0 le_rfl x).le)).1
  have hU0 : 0 < Graph.nrmL2 lam (u 0) := lt_of_lt_of_le hm0 hmU
  have hB1 : 1 ≤ BhatSigma G uH lam := one_le_BhatSigma hpc hpos hl hhit
  have hB : 0 < BhatSigma G uH lam := lt_of_lt_of_le zero_lt_one hB1
  have hd0 : 0 < delta0 eps0 (Graph.meanL2 lam (u 0)) (BhatSigma G uH lam)
      (Graph.nrmL2 lam (u 0)) := delta0_pos heps0 hm0 hB hU0
  have hd1 : delta0 eps0 (Graph.meanL2 lam (u 0)) (BhatSigma G uH lam)
      (Graph.nrmL2 lam (u 0)) ≤ 1/2 := delta0_le_half heps0.le heps1 hm0 hB1 hmU
  obtain ⟨t₁, ht₁mem, hratio⟩ :=
    entry_time hinv hKnn hp htot hu hlmin hlmin0 hwmin hw hU0 hflow hd0 hd1
  have ht₁0 : 0 ≤ t₁ := ht₁mem.1
  have hmono : Graph.meanL2 lam (u 0) ≤ Graph.meanL2 lam (u t₁) :=
    mass_monotone_flow hinv hKnn hp hu hnu logSqDeriv_strictlyUnimodal hflow
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht₁0) ht₁0
  have hsphere : Graph.nrmL2 lam (u t₁) = Graph.nrmL2 lam (u 0) :=
    nrmL2_const_of_flow hp hu hflow t₁ ht₁0
  have hm1pos : 0 < Graph.meanL2 lam (u t₁) := lt_of_lt_of_le hm0 hmono
  have hm1U : Graph.meanL2 lam (u t₁) ≤ Graph.nrmL2 lam (u 0) := by
    rw [← hsphere]
    exact (mean_le_nrmL2_iff_const hp htot (fun x => (hu t₁ ht₁0 x).le)).1
  obtain ⟨hmean0, hrad⟩ :=
    exists_delta_for_radius (K := B.phat) (lam := lam) (u := u t₁)
      (Bhat := BhatSigma G uH lam) (m0 := Graph.meanL2 lam (u 0))
      (U0 := Graph.nrmL2 lam (u 0)) (eps0 := eps0)
      hnn htot (fun x => (hu t₁ ht₁0 x).ne') hB hU0 (hcoer_of_graph hpc hpos hl hhit)
      heps0 hm0 hmono hsphere (fun x => (hratio x).le)
  exact ⟨t₁, ht₁mem, hratio, hmono, hm1U, hm1pos,
    flow_unit_mass hflow hm1pos t₁, hmean0, hrad⟩

/-! ### The `C³` side condition the paper leaves unstated -/

omit [Fintype V] [DecidableEq V] in
/-- **`htaylor` at `a = 1/2`, `g''(1) = 2`, `M₃ = 24`** — the `C³` hypothesis of
`theo:local_convergence_full` as the Taylor bound it is used through, for `g = (log x)²`.
`M₃ = 80` also works (`LogSqTaylor.logSqDeriv_taylor`, the constant the paper's own
`|g'''| ≤ 80` on `[1/2,3/2]` gives); `24` is sharper and is the one taken. -/
theorem logSqDeriv_taylor_half (y : ℝ) (hy : |y - 1| ≤ 1/2) :
    |logSqDeriv y - 2 * (y - 1)| ≤ 24 / 2 * (y - 1) ^ 2 := by
  refine le_trans (logSqDeriv_taylor_twelve hy) (le_of_eq ?_)
  norm_num

/-! ### The theorem -/

/-- **`theo:training_speed_full`** (`proofs.tex:900–920`, proof `:922–934`), assembled. -/
theorem training_speed_full {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam gr uH wf : V → ℝ} {wmin wsup : ℝ} {u : ℝ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x)
    (hflow : IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u) :
    (∀ x, lam x = Graph.visits G gr x / (2 + B.sigmaBar uH))
      ∧ Graph.minOver G lam
          = Graph.minOver G (Graph.visits G gr) / (2 + B.sigmaBar uH)
      ∧ (∀ t : ℝ, 0 ≤ t →
          lossVal lam wf logSq (ratio B.phat lam (u t))
            ≤ ((lossVal lam wf logSq (ratio B.phat lam (u 0)))⁻¹
                + (wmin * Real.sqrt (Graph.minOver G lam)
                    / (Graph.nrmL2 lam (u 0) * wsup
                        * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam (u 0))
                            / (wmin * Graph.minOver G lam))))) ^ 2 * t)⁻¹)
      ∧ ∃ t₁ ∈ Set.Icc (0:ℝ)
          (T0 (lossVal lam wf logSq (ratio B.phat lam (u 0)))
            (cDelta wmin (Graph.minOver G lam) (Graph.nrmL2 lam (u 0))
              (delta0 (eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
                (Graph.meanL2 lam (u 0)) (BhatSigma G uH lam) (Graph.nrmL2 lam (u 0))))),
          Graph.meanL2 lam (u 0) ≤ Graph.meanL2 lam (u t₁)
            ∧ Graph.meanL2 lam (u t₁) ≤ Graph.nrmL2 lam (u 0)
            ∧ Graph.nrmL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)
                ≤ eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam)
            ∧ ∃ cinf : ℝ, Balanced B.phat lam (fun _ => cinf) ∧ ∀ t : ℝ, t₁ ≤ t →
                Graph.nrmL2 lam (fun x => u t x / Graph.meanL2 lam (u t₁) - cinf)
                  ≤ 2 * Real.exp (-(rhoSigma 2 wmin (Graph.minOver G lam)
                          (Graph.sigmaStar G uH) * (t - t₁)
                        / (2 * Graph.meanL2 lam (u t₁) ^ 2)))
                    * Graph.nrmL2 lam
                        (perpL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hp x).le
  have htot : ∑ x, lam x = 1 := hl.total
  have hinv : Invariant B.phat lam := hl.inv
  have hKnn : ∀ x y, 0 ≤ B.phat x y := fun x y => B.phat_nonneg x y
  have hlmin : ∀ x, Graph.minOver G lam ≤ lam x := fun x => Graph.minOver_le lam x
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hwfpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  have hwsupp : 0 < wsup := lt_of_lt_of_le (hwfpos G.src) (hwsup G.src)
  have hwabs : ∀ x, |wf x| ≤ wsup := fun x => by
    rw [abs_of_pos (hwfpos x)]; exact hwsup x
  have hm0 : 0 < Graph.meanL2 lam (u 0) :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (hu 0 le_rfl i)) ⟨G.src, Finset.mem_univ _⟩
  have hmU : Graph.meanL2 lam (u 0) ≤ Graph.nrmL2 lam (u 0) :=
    (mean_le_nrmL2_iff_const hp htot (fun x => (hu 0 le_rfl x).le)).1
  have hU0 : 0 < Graph.nrmL2 lam (u 0) := lt_of_lt_of_le hm0 hmU
  have hB1 : 1 ≤ BhatSigma G uH lam := one_le_BhatSigma hpc hpos hl hhit
  have hB : 0 < BhatSigma G uH lam := lt_of_lt_of_le zero_lt_one hB1
  have heps0 : 0 < eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam) :=
    eps0Sq_pos hlmin0 hwmin hwsupp hB
  have heps1 : eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam) ≤ 1/2 :=
    eps0Sq_le_half hlmin0 hlmin htot hwmin hwsupp
  refine ⟨Graph.BackwardPolicy.lam_eq_visits_div hpc hpos hl hg hhit,
    minOver_lam_eq hpc hpos hl hg hhit,
    global_lojasiewicz_flow' hinv hKnn hp htot hu hlmin hlmin0 hwmin hw hwsup hU0 hflow, ?_⟩
  obtain ⟨t₁, ht₁mem, -, hmono, hm1U, hm1pos, hflow1, hmean0, hrad⟩ :=
    entry_and_rescale hpc hpos hl hhit hu hwmin hw heps0 heps1 hflow
  refine ⟨t₁, ht₁mem, hmono, hm1U, hrad, ?_⟩
  -- the rescaled deviation, and Theorem 10 applied to it
  set m₁ : ℝ := Graph.meanL2 lam (u t₁) with hm₁def
  have hm₁ne : m₁ ≠ 0 := hm1pos.ne'
  have hdev0 : (fun x => u (t₁ + m₁ ^ 2 * 0) x / m₁ - 1)
      = fun x => u t₁ x / m₁ - 1 := by
    funext x; norm_num
  have hflow2 : IsGradientFlow B.phat lam (fun z => lam z * wf z) logSqDeriv
      (fun s x => 1 + (u (t₁ + m₁ ^ 2 * s) x / m₁ - 1)) := by
    have heq : (fun s x => 1 + (u (t₁ + m₁ ^ 2 * s) x / m₁ - 1))
        = fun s x => u (t₁ + m₁ ^ 2 * s) x / m₁ := by
      funext s x; ring
    rw [heq]
    exact hflow1
  obtain ⟨cinf, -, hdecay⟩ :=
    local_convergence_full (K := B.phat) (lam := lam) (w := wf) (gd := logSqDeriv)
      (h := fun s x => u (t₁ + m₁ ^ 2 * s) x / m₁ - 1)
      (g2 := 2) (a := 1/2) (M3 := 24) (wsup := wsup) (wmin := wmin)
      (Bhat := BhatSigma G uH lam) (lamMin := Graph.minOver G lam)
      ⟨hKnn, fun {x} _ => B.phat_row_sum x⟩ ⟨hnn, hl.inv⟩ hp htot hlmin0 hlmin
      (by norm_num) (by norm_num) (by norm_num) hwabs hwmin hw hB1
      (hcoer_of_graph hpc hpos hl hhit) (fun y hy => logSqDeriv_taylor_half y hy) hflow2
      (by rw [hdev0]; exact hrad)
  refine ⟨cinf, balanced_const hinv cinf, fun t ht => ?_⟩
  have hs0 : 0 ≤ (t - t₁) / m₁ ^ 2 := div_nonneg (by linarith) (sq_nonneg m₁)
  have hts : t₁ + m₁ ^ 2 * ((t - t₁) / m₁ ^ 2) = t := by
    field_simp
    ring
  have hfun : (fun x => u (t₁ + m₁ ^ 2 * ((t - t₁) / m₁ ^ 2)) x / m₁ - 1 - (cinf - 1))
      = fun x => u t x / m₁ - cinf := by
    funext x; rw [hts]; ring
  have hrho : rhoL 2 wmin (BhatSigma G uH lam)
      = rhoSigma 2 wmin (Graph.minOver G lam) (Graph.sigmaStar G uH) :=
    rhoL_eq_rhoSigma hlmin0
  have hexp : rhoL 2 wmin (BhatSigma G uH lam) * ((t - t₁) / m₁ ^ 2) / 2
      = rhoSigma 2 wmin (Graph.minOver G lam) (Graph.sigmaStar G uH) * (t - t₁)
          / (2 * m₁ ^ 2) := by
    rw [hrho]; ring
  have h := hdecay ((t - t₁) / m₁ ^ 2) hs0
  rw [hfun, hexp, hdev0] at h
  exact h

/-- **`theo:training_speed_full` from a positive initialization alone** — the paper's own
"from *every* initialization `μ₀ ∼ λ`" (`proofs.tex:906`), with no hypothesis on the trajectory
at any later time.

`training_speed_full`'s `hu` is discharged by `BoundaryBlowup.flow_pos_graph`, i.e. by
`prop:no_distant_equilibrium`*(3)*'s compactness sentence, at the cost of the edge floor that
sentence's quantitative form needs: `0 < p_min ≤ 1` with `p_min ≤ π̂_←(y→z)` on every edge
carrying mass. `BoundaryBlowup.exists_edgeFloor` says such a `p_min` always exists on a finite
state space, so the hypothesis costs a constant and not a case. -/
theorem training_speed_full_of_pos {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam gr uH wf : V → ℝ} {wmin wsup pmin : ℝ} {u : ℝ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (hpmin : ∀ y z : V, 0 < B.phat y z → pmin ≤ B.phat y z)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u) :
    (∀ x, lam x = Graph.visits G gr x / (2 + B.sigmaBar uH))
      ∧ Graph.minOver G lam
          = Graph.minOver G (Graph.visits G gr) / (2 + B.sigmaBar uH)
      ∧ (∀ t : ℝ, 0 ≤ t →
          lossVal lam wf logSq (ratio B.phat lam (u t))
            ≤ ((lossVal lam wf logSq (ratio B.phat lam (u 0)))⁻¹
                + (wmin * Real.sqrt (Graph.minOver G lam)
                    / (Graph.nrmL2 lam (u 0) * wsup
                        * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam (u 0))
                            / (wmin * Graph.minOver G lam))))) ^ 2 * t)⁻¹)
      ∧ ∃ t₁ ∈ Set.Icc (0:ℝ)
          (T0 (lossVal lam wf logSq (ratio B.phat lam (u 0)))
            (cDelta wmin (Graph.minOver G lam) (Graph.nrmL2 lam (u 0))
              (delta0 (eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
                (Graph.meanL2 lam (u 0)) (BhatSigma G uH lam) (Graph.nrmL2 lam (u 0))))),
          Graph.meanL2 lam (u 0) ≤ Graph.meanL2 lam (u t₁)
            ∧ Graph.meanL2 lam (u t₁) ≤ Graph.nrmL2 lam (u 0)
            ∧ Graph.nrmL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)
                ≤ eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam)
            ∧ ∃ cinf : ℝ, Balanced B.phat lam (fun _ => cinf) ∧ ∀ t : ℝ, t₁ ≤ t →
                Graph.nrmL2 lam (fun x => u t x / Graph.meanL2 lam (u t₁) - cinf)
                  ≤ 2 * Real.exp (-(rhoSigma 2 wmin (Graph.minOver G lam)
                          (Graph.sigmaStar G uH) * (t - t₁)
                        / (2 * Graph.meanL2 lam (u t₁) ^ 2)))
                    * Graph.nrmL2 lam
                        (perpL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)) :=
  training_speed_full hpc hpos hl hg hhit hwmin hw hwsup
    (flow_pos_graph (lamMin := Graph.minOver G lam) hpc hpos hl
      (fun x => Graph.minOver_le lam x)
      (Graph.minOver_pos fun x => hl.pos hpc hpos x) hpmin0 hpmin1 hpmin hwmin hw hu0 hflow)
    hflow

/-! ### The five-vertex cycle: the constants evaluated

`GFNBounds/Graph/CycleExample.lean`'s `rem:cycle_no_stalemate` graph, which already pins
`σ_*`, `σ̄`, `λ` and `N` in closed form. Computed by hand first, at `p = 1/2`: `λ` is
`(1/8, 1/4, 1/4, 1/4, 1/8)`, so `λ_min = 1/8`; `σ_* = (4−p)/(1−p) = 7`; `2 + σ̄ = 8` and
`N_min = 1`, so `λ_min = N_min/(2+σ̄)` checks; `B̂_σ = 7/√(1/8) = 14√2 ≈ 19.8`; and
`ϱ_σ = 2·1·(1/8)/49 = 1/196` at `w_min = 1`. -/




section CycleCheck

open Graph.CycleExample

/-- `λ_min = (1−p)/(5−2p)` on the five-vertex cycle, attained at `s₀` and `s_f`. -/
theorem cycle_minOver_lam {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Graph.minOver cyc (lam p) = (1 - p) / (5 - 2 * p) := by
  have hd : (0:ℝ) < 5 - 2 * p := by linarith
  have key : ∀ a b : ℝ, a ≤ b → a / (5 - 2 * p) ≤ b / (5 - 2 * p) := by
    intro a b hab
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hab (inv_nonneg.mpr hd.le)
  refine le_antisymm (le_of_le_of_eq (Graph.minOver_le _ 0) (by norm_num [lam]))
    (Graph.le_minOver fun x => ?_)
  fin_cases x <;> simp only [lam] <;>
    first
      | exact le_rfl
      | exact key _ _ (by linarith)

/-- **The graph half of `theo:training_speed_full` on the cycle**, in closed form in `p`:
`λ_min = N_min/(2+σ̄)`, `B̂_σ ≥ 1`, and `ϱ_σ = 2(1−p)³/((5−2p)(4−p)²) > 0` at `w_min = 1`. -/
theorem cycle_training_speed_check {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Graph.minOver cyc (lam p) = (1 - p) / (5 - 2 * p)
      ∧ Graph.minOver cyc (lam p)
          = Graph.minOver cyc (Graph.visits cyc (green p))
              / (2 + (pol hp0 hp1).sigmaBar (hitExp p))
      ∧ 1 ≤ BhatSigma cyc (hitExp p) (lam p)
      ∧ rhoSigma 2 1 (Graph.minOver cyc (lam p)) (Graph.sigmaStar cyc (hitExp p))
          = 2 * (1 - p) ^ 3 / ((5 - 2 * p) * (4 - p) ^ 2)
      ∧ 0 < rhoSigma 2 1 (Graph.minOver cyc (lam p)) (Graph.sigmaStar cyc (hitExp p)) := by
  have h1 : (0:ℝ) < 1 - p := by linarith
  have hd : (0:ℝ) < 5 - 2 * p := by linarith
  have h4 : (0:ℝ) < 4 - p := by linarith
  have hmin := cycle_minOver_lam hp0 hp1
  have hsig := sigmaStar_eq hp0 hp1
  refine ⟨hmin,
    minOver_lam_eq pathConnected (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1)
      (isGreen hp0 hp1) (isHitExp hp0 hp1),
    one_le_BhatSigma pathConnected (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1)
      (isHitExp hp0 hp1), ?_, ?_⟩
  · rw [rhoSigma, hmin, hsig]
    field_simp
  · rw [rhoSigma, hmin, hsig]
    positivity

/-- **The constants at `p = 1/2`, and `T₀` on a concrete instance.** With `w_min = 1`,
`𝓛(μ₀) = 1`, `‖u₀‖ = 1`, `m₀ = 1` and `ε₀ = 1/100` the crossover time is
`T₀ = 4·7⁴·10⁸·8⁵ = 3.147…×10¹⁶` — finite, positive, and an honest picture of how loose the
bound is. -/
theorem cycle_training_speed_check_half :
    Graph.minOver cyc (lam (1/2)) = 1/8
      ∧ Graph.sigmaStar cyc (hitExp (1/2)) = 7
      ∧ Graph.minOver cyc (Graph.visits cyc (green (1/2))) = 1
      ∧ BhatSigma cyc (hitExp (1/2)) (lam (1/2)) = 14 * Real.sqrt 2
      ∧ rhoSigma 2 1 (1/8) 7 = 1/196
      ∧ T0 1 (cDelta 1 (1/8) 1 (delta0 (1/100) 1 (7 / Real.sqrt (1/8)) 1))
          = 31470387200000000 := by
  have hp0 : (0:ℝ) < 1/2 := by norm_num
  have hp1 : (1:ℝ)/2 < 1 := by norm_num
  have hmin : Graph.minOver cyc (lam (1/2)) = 1/8 := by
    rw [cycle_minOver_lam hp0 hp1]; norm_num
  have hsig : Graph.sigmaStar cyc (hitExp (1/2)) = 7 := by
    rw [sigmaStar_eq hp0 hp1]; norm_num
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs8 : Real.sqrt (1/8 : ℝ) = Real.sqrt 2 / 4 := by
    rw [show (1:ℝ)/8 = (Real.sqrt 2 / 4) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  refine ⟨hmin, hsig, minOver_visits_eq hp0 hp1, ?_, by norm_num [rhoSigma], ?_⟩
  · rw [BhatSigma, hmin, hsig, hs8]
    field_simp
    linarith [h2]
  · rw [T0_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) < 7)]
    norm_num

end CycleCheck

/-! ### The theorem on the paper's own hypotheses

`training_speed_full_of_pos` still asks for an edge floor `p_min`, which the paper never names.
On a finite state space one always exists (`BoundaryBlowup.exists_edgeFloor`), so it is
discharged rather than assumed. -/

section Unconditional

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`theo:training_speed_full` with no hypothesis the paper does not have.** What remains is
the paper's own setting: a finite path-connected marked graph, a backward policy positive on its
edges, `λ` its invariant probability, `ν = wλ` with `w ≥ w_min > 0`, and an initialization
`μ₀ ∼ λ` — the theorem's own *"from **every** initialization `μ₀ ∼ λ`"*.

The trajectory hypothesis that stood here until 2026-09-13 is discharged by
`flow_pos_graph`, the compactness half of `prop:no_distant_equilibrium`*(3)*; the edge floor by
`exists_edgeFloor`. What is **not** discharged, and is disclosed in SCOPE: that the gradient flow
exists. Every statement in this layer is conditional on a given curve, as the paper's own proofs
are. -/
theorem training_speed_full_of_init {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam gr uH wf : V → ℝ} {wmin wsup : ℝ} {u : ℝ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u) :
    (∀ x, lam x = Graph.visits G gr x / (2 + B.sigmaBar uH))
      ∧ Graph.minOver G lam
          = Graph.minOver G (Graph.visits G gr) / (2 + B.sigmaBar uH)
      ∧ (∀ t : ℝ, 0 ≤ t →
          lossVal lam wf logSq (ratio B.phat lam (u t))
            ≤ ((lossVal lam wf logSq (ratio B.phat lam (u 0)))⁻¹
                + (wmin * Real.sqrt (Graph.minOver G lam)
                    / (Graph.nrmL2 lam (u 0) * wsup
                        * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam (u 0))
                            / (wmin * Graph.minOver G lam))))) ^ 2 * t)⁻¹)
      ∧ ∃ t₁ ∈ Set.Icc (0:ℝ)
          (T0 (lossVal lam wf logSq (ratio B.phat lam (u 0)))
            (cDelta wmin (Graph.minOver G lam) (Graph.nrmL2 lam (u 0))
              (delta0 (eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
                (Graph.meanL2 lam (u 0)) (BhatSigma G uH lam) (Graph.nrmL2 lam (u 0))))),
          Graph.meanL2 lam (u 0) ≤ Graph.meanL2 lam (u t₁)
            ∧ Graph.meanL2 lam (u t₁) ≤ Graph.nrmL2 lam (u 0)
            ∧ Graph.nrmL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)
                ≤ eps0Sq wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam)
            ∧ ∃ cinf : ℝ, Balanced B.phat lam (fun _ => cinf) ∧ ∀ t : ℝ, t₁ ≤ t →
                Graph.nrmL2 lam (fun x => u t x / Graph.meanL2 lam (u t₁) - cinf)
                  ≤ 2 * Real.exp (-(rhoSigma 2 wmin (Graph.minOver G lam)
                          (Graph.sigmaStar G uH) * (t - t₁)
                        / (2 * Graph.meanL2 lam (u t₁) ^ 2)))
                    * Graph.nrmL2 lam
                        (perpL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)) := by
  obtain ⟨pmin, hpmin0, hpmin1, hpmin⟩ := exists_edgeFloor B.phat
  exact training_speed_full_of_pos hpc hpos hl hg hhit hwmin hw hwsup
    hpmin0 hpmin1 hpmin hu0 hflow

end Unconditional

end GFNBounds.Balance
