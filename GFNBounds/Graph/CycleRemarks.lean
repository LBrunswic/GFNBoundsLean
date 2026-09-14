import GFNBounds.Graph.CycleDivergence
import GFNBounds.Graph.CycleBlowup
import GFNBounds.Balance.FlowExistence
import GFNBounds.Balance.WeightedL2Norm

/-!
# The cyclic counter-example at every target, and the closing claims of the five-vertex cycle

**`lem:cycle_counterexample`** — statement `proofs.tex:385–391`, proof `proofs.tex:393–404`.

**`rem:cycle_no_stalemate`** — `proofs.tex:910–912`.

(Line numbers against draft commit `3194054`/`216ce34`; the labels are the anchors, kb 0036.)

> (`lem:cycle_counterexample`) Let `N ≥ 2` and let `𝒞_N` be the graph with states `x₁,…,x_N`,
> cycle edges `xᵢ → x_{i+1 mod N}`, an initial edge `s₀ → x₁` and a terminal edge `xᵢ → s_f` for
> every `i`. Let `F̂` be the unit-mass flow routed `s₀ → x₁ → x₂ → s_f`, let `γ` be the unit
> circulation on the cycle, equal to `1` on each edge `xᵢ → x_{i+1 mod N}` and to `0` elsewhere,
> and set `F_k := F̂ + kγ` for every integer `k ≥ 0`. Then:
> 1. every `F_k` satisfies the flow-matching constraint `equ:FM_const` with terminal flow
>    `δ_{x₂}`, and its sampler satisfies `s_τ(F_k) ∼ δ_{x₂}`; hence
>    `TV(s_τ(F_k) ‖ target) = 1 − target(x₂)` for every `k` and every probability measure `target`
>    on `{x₁,…,x_N}`;
> 2. let `target` be a probability measure and `ν_train` a finite measure on `{x₁,…,x_N}`, and let
>    `𝓛(F) := ∫ g(ρ_F) dν_train` be a divergence-based FM loss in the sense of
>    `brunswic2024theory` §4.1: `ρ_F := (F_init + f_←)/(target + f_→)` is the ratio of the inflow
>    side to the outflow side of `equ:FM_const`, `F_init` being the initial flow and `f_←`, `f_→`
>    the flows of `F` into and out of each state along the cycle edges, and `g : ℝ₊ → ℝ₊` vanishes
>    exactly at `1`. If `g` is continuous at `1`, then `𝓛(F_k)` is defined for `k ≥ 1` and tends
>    to `0` as `k → ∞`.
>
> (proof of *(2)*) […] `ρ_{F_k}(xᵢ) = (aᵢ + k)/(bᵢ + k)`,
> `|ρ_{F_k}(xᵢ) − 1| = |aᵢ − bᵢ|/(bᵢ + k) ≤ max_j |a_j − b_j|/k` […]

> (`rem:cycle_no_stalemate`) Take the marked graph with vertices `{s₀,x₁,x₂,x₃,s_f}`, edges
> `s₀ → x₁`, the cycle `x₁ → x₂ → x₃ → x₁`, and `x₃ → s_f`, loop-closed as in Definition
> `def:loop_closure`; freeze the backward policy `π_←(x₁ → x₃) = p`, `π_←(x₁ → s₀) = 1 − p` with
> `p ∈ (0,1)`, all other rows being deterministic — at `p = 1` the edge `s₀ → x₁` carries no
> backward probability, at `p = 0` the edge `x₃ → x₁` carries none, and in either case the mixing
> sum `∑ₙ β̂ₙ` is `+∞`. The expected backward-trajectory length is `3/(1−p) < ∞`: the condition of
> `morozov2025revisiting` holds; by their Proposition 3.12 the flow induced by the frozen backward
> policy has total flow through the internal states `F(s_f)·3/(1−p)`, `F(s_f)` its flow into the
> sink, so the balanced flow carries no exploding circulation. The invariant measure gives equal
> mass `q` to the three cycle states and `(1−p)q` to `s₀` and `s_f`. Over-inflate the cycle:
> `u := dμ/dλ` equals `M > 1` on `{x₁,x₂,x₃}` and `1` elsewhere. The ratios are then
> `r(x₁) = r(x₂) = r(s_f) = 1`, `r(x₃) = p + (1−p)/M` and `r(s₀) = M`; as `M → ∞`, `r(x₃) → p`, and
> heuristically the frozen-policy constraint appears as a persistent leak ratio `p` at the junction
> `x₃`. For `g = (log x)²` the inflation force `|g'(r)r| = 2|log r|` equals `2 log M` at the starved
> source `s₀`, is largest there over the states for every `M > 1`, and increases with `M`. The
> configuration is not a critical point of `𝓛_{g,ν}` for any `ν` of positive density (Proposition
> `prop:no_distant_equilibrium`*(1)*, `r(x₃)` being different from `1`). At fixed `ν` the gradient
> field is homogeneous of degree `−1`, so, for a flow `μ₀ ∼ λ` with gradient flow `(μ_t)_{t≥0}` and
> for `α > 0`, the gradient flow from `αμ₀`, which exists by Proposition
> `prop:no_distant_equilibrium`*(3)*, is `t ↦ αμ_{t/α²}`: a trajectory started at norm `Θ(M)` runs
> `Θ(M²)` times slower than the normalized one. Numerically, the transient is of order `M²` — its
> duration `t_M`, the first time every ratio lies within `1/10` of `1`, has `t_M/M² ≈ 0.720` for
> `M = 10,…,320` at `p = 1/2` and `w ≡ 1` — after which the exponential phase of Theorem
> `theo:local_convergence` takes over. As `p → 1`, the expected backward-trajectory length, the
> mixing sum `∑ₙ β̂ₙ` — `β̂ₙ ≥ |ζ_p|ⁿ` for `ζ_p` an eigenvalue of the transition matrix of the
> backward chain, similar to the density action for `p < 1`, chosen continuous in `p` with
> `ζ_p = e^{2iπ/3}` at `p = 1` — and the constant `B̂_σ` of Proposition `prop:morozov_rate` tend to
> `+∞`, while the rate `ϱ` of Theorem `theo:db_stable_frozen_full` read at the mixing sum
> `B̂ = ∑ₙ β̂ₙ`, the rate `ϱ_σ` of Proposition `prop:morozov_rate` and the constant of Corollary
> `cor:global_lojasiewicz` tend to `0`; numerically, the smallest constant satisfying
> `eq:coercivity` stays below `1.62`.

## What is proved

### `lem:cycle_counterexample` — generalizing `GFNBounds/Graph/CycleDivergence.lean`

`CycleDivergence.lean` proves items *(1)*–*(2)* only at the target of `theo:no_bound_divergence`
(`targetC δ`) and along real `k → ∞`. Here they hold for every probability target and along the
integers, on the same `cycGraph`, `Fhat`, `gammaC`, `Fk`, `fmRatio`, `fmLossTarget`, `termLaw`,
`tvFin`.

| | |
|---|---|
| `extT` | a probability on `{x₁,…,x_N}` as a function on the vertices, `0` at the marks |
| `Fk_src_x`, `Fk_x_snk`, `Fk_FM_const` | initial flow `δ_{x₁}`, terminal flow `δ_{x₂}`, and `equ:FM_const` with its four terms |
| `tvFin_termLaw_Fk_gen` | `TV(δ_{x₂} ‖ target) = 1 − target(x₂)` for every probability target |
| `bG`, `fmRatio_Fk_gen` | `bᵢ = target(xᵢ) + 𝟙_{i=1}`, and `ρ_{F_k}(xᵢ) = (aᵢ + k)/(bᵢ + k)` |
| `den_pos_and_ratio_pos` | "defined for `k ≥ 1`": the denominator is positive and `ρ ∈ (0,∞)` |
| `abs_fmRatio_Fk_sub_one` | the proof's display, `= |aᵢ−bᵢ|/(bᵢ+k) ≤ max_j|a_j−b_j|/k`, and further `≤ 1/k` |
| `fmLossTarget_Fk_tendsto_zero_gen` | `𝓛(F_k) → 0` along the integers, every target, every weight |
| **`cycle_counterexample`** | **items *(1)* and *(2)* assembled** (sampler clause excepted) |
| `cycle_counterexample_check` | inhabitation at `N = 2`, uniform target, `g = (x−1)²` |

### `rem:cycle_no_stalemate` — the clauses `CycleExample.lean` and `CycleBlowup.lean` did not have

| clause | declaration |
|---|---|
| the force equals `2 log M` at `s₀`, is largest there (strictly), increases with `M` | **`inflation_force_max_mono`** (with `force_eq`, `ratio_x3_bounds`) |
| not a critical point for any `ν > 0` — on the Fréchet reading, kb 0035 | **`not_critical`** (the mass reading is `CycleExample.no_stalemate`) |
| homogeneity `D(αμ) = α⁻¹D(μ)` | `Balance.lossGrad_smul` (strict, reused) |
| the gradient flow from `αμ₀` exists and is `t ↦ αμ_{t/α²}` | **`rescaled_flow`** (any finite chain, any `g'` `C¹` on `(0,∞)`), **`cycle_rescaled_flow`** (`(log x)²`), **`cycle_rescaled_flow_sq`** (`(x−1)²`), `isGradientFlow_scale` |
| "started at norm `Θ(M)` runs `Θ(M²)` times slower" | **`entryTimes_scale`** (entry times into `|r−1| < δ` scale by exactly `α²`), `nrmL2_scale` (initial norm by `α`) |
| at `p ∈ {0,1}`: the edge carries no backward probability, and `∑ₙ β̂ₙ = +∞` | **`mixing_sum_endpoints`** (`β̂_{5k} ≥ 1` at `p = 0`, `β̂_{3k} ≥ 1` at `p = 1`; `lam p` the unique invariant probability there) |
| on `(0,1)` the mixing sum is finite — the presupposition of "`ϱ` read at the mixing sum" | **`betaCyc_summable`**, **`betaCyc_le_geometric`** (`β̂ₙ ≤ (2/r¹⁵)rⁿ`, `r = 1 − min(p,1−p)¹⁶/32`), **`mixing_cycle`** (`Core.Mixing`), **`mixing_B_coercive`** (`B̂ ≥ 1` satisfies `eq:coercivity`) |
| the mixing sum tends to `+∞` as `p → 1` | **`mixing_B_tendsto_atTop`** (in `ℝ`), `mixing_sum_tendsto_top` (in `[0,∞]`), **`mixing_sum_gt`** (explicit: `1 − 1/(8K²) < p < 1`, `K = ⌊2|C|⌋₊ + 1`, gives `∑_{n<3K} β̂ₙ > C`) |
| `ϱ = g''(1)w_min/B̂²` read at the mixing sum tends to `0` | **`rho_mixing_tendsto`**, `rho_mixing_ennreal_tendsto` |
| `ϱ_σ → 0` | **`rhoSigma_cycle_tendsto`** (both library forms) |
| the constant `κ` of `cor:global_lojasiewicz` tends to `0` | **`kappa_cycle_tendsto`** (fixed `u₀`), `kappa_cycle_tendsto_fixed_measure` (fixed `μ₀`), `kappa_cycle_tendsto_gen` |
| the closing sentence in one statement | **`cycle_no_stalemate_limits`** |
| `betaCyc` is the paper's `β̂ₙ` of the remark's chain | `betaCyc_eq` (`kern p = (pol p).phat`), `CycleExample.invProb_eq` |

Already certified elsewhere and not restated: the backward-trajectory length `3/(1−p)`
(`CycleExample.sigmaBar_eq`), the invariant measure (`CycleExample.invProb_paper`), the five ratios
(`CycleExample.ratio_*`), `3/(1−p) → ∞` and `B̂_σ → ∞` (`CycleBlowup.three_div_one_sub_tendsto_atTop`,
`CycleBlowup.sigmaBar_blowup`, `CycleBlowup.bhatSigma_cycle_tendsto`).

**The mixing-sum route.** `β̂ₙ = ‖Pⁿ − Π‖` is the library's `Core.Mixing.beta` of `Balance.densOp`
and `Balance.meanOp` at `lam p`, `kern p` (`betaCyc`). On `[0,1)` the density action is the shift
`shiftK`, `P(a) = (a₁, a₂, a₃, pa₁ + (1−p)a₄, a₀)`, an `L²(λ)` contraction. *Blow-up:* the test
density `v = 𝟙_{x₁} − 𝟙_{x₂}` has `Πv = 0` and `‖P³v − v‖² ≤ 2(1−p)‖v‖²` (`three_step_defect`), so
`β̂_{3k} ≥ ‖P^{3k}v‖/‖v‖ ≥ 1 − k√(2(1−p)) ≥ 1/2` for `k ≤ K` once `8K²(1−p) ≤ 1`. *Endpoints:* `P⁵v = v`
at `p = 0`, `P³v = v` at `p = 1`. *Summability on `(0,1)`:* the reversed chain's matrix `Q` has
`Q¹⁶ ≥ min(p,1−p)¹⁶` entrywise along explicit paths through `x₃` (cycles of length `3` and `5`,
`QLb_16`); a variance identity turns the minorization into `‖P¹⁶ − Π‖ ≤ √(1 − min(p,1−p)¹⁶)`
(`variance_contract`, `norm_pow16_sub_meanOp_le`), and `Pⁿ⁺¹⁶ − Π = (P¹⁶ − Π)(Pⁿ − Π)` gives the
geometric bound. No eigenvalue appears.

## SCOPE (disclosed)

### `lem:cycle_counterexample`

* **The sampler clause `s_τ(F_k) ∼ δ_{x₂}` is not certified.** It is `theo:sampling_theorem`
  (Phase 3); as in `CycleDivergence.lean`, the total variation is measured against the normalized
  terminal flow `termLaw`, which that theorem identifies with the law of `s_τ`. "Hence `TV = 1 −
  target(x₂)`" is certified for `termLaw` (`tvFin_termLaw_Fk_gen`), and `termLaw_Fk` shows it is
  `δ_{x₂}`.
* **Stronger than printed, in the safe direction.** `g : ℝ → ℝ` needs only `g(1) = 0` and continuity
  at `1`; "`g ≥ 0`" and "vanishes *exactly* at `1`" are not used and not carried. `ν_train` is any
  real weight on the vertices (only its values on `{x₁,…,x_N}` enter), not required finite or
  non-negative. The display's `max_j|a_j−b_j|/k` is further bounded by `1/k`.
* **"`𝓛(F_k)` is defined for `k ≥ 1`"** is read as: the denominator `target + f_→` of `ρ_{F_k}` is
  positive and `ρ_{F_k}` lies in `(0,∞)`, the domain of `g`, at every internal state. Lean's
  division being total, "defined" has no other formal content.
* **Modelling inherited from `CycleDivergence.lean`**: `N = M + 2`; vertices
  `Option (Option (Fin N))`; the target in the denominator of `ρ`; `k : ℕ` enters the real-parameter
  family `Fk` through its cast.

### `rem:cycle_no_stalemate`

* **The endpoints `p ∈ {0,1}`.** No `BackwardPolicy` object is built at the endpoints (one could
  be: `BackwardPolicy` needs only `0 ≤ p ≤ 1`, but `CycleExample.pol` is used with
  `PositiveOnEdges` on `(0,1)`); that `kern 0` and `kern 1` are the loop closure of a policy on
  `cyc` is matched **by formula**, not by a Lean statement: the loop-closed
  kernel is `CycleExample.kern p`, the same formula (`CycleExample.phat_eq` on `(0,1)`), shown Markov
  and `lam p`-invariant, with `lam p` the only invariant probability (`invProb_endpoint_unique`,
  which does not even ask non-negativity). At `p = 1`, `λ(s₀) = λ(s_f) = 0`: the library's
  `√λ`-weighting then maps those coordinates to `0`, and the certificate `β̂_{3k} ≥ 1` comes from a
  test vector supported on the cycle, a genuine element of `L²(λ)`. "`∑ₙ β̂ₙ = +∞`" is certified as
  `¬ Summable` and as `∑' ofReal β̂ₙ = ⊤` in `[0,∞]`.
* **"As `p → 1`"** is read as `p → 1⁻` (`𝓝[<] 1`), the only side on which the policy is defined.
* **The eigenvalue parenthetical is a claim and is not formalized** (it keeps the row out of A).
  "`β̂ₙ ≥ |ζ_p|ⁿ` for `ζ_p` an eigenvalue … `ζ_p = e^{2iπ/3}` at `p = 1`" is not marked heuristic; the blow-up is certified by the
  elementary test-vector route above instead, with no complex spectral theory. The parenthetical
  itself is not contradicted (the characteristic polynomial of `P` is `z⁵ − pz² − (1−p)`, whose roots
  at `p = 1` are `0, 0` and the cube roots of unity), but no Lean statement carries it.
* **Summability on `(0,1)` is proved, not assumed** — the paper presupposes it in "the rate `ϱ` of
  Theorem `theo:db_stable_frozen_full` read at the mixing sum", which is a rate only for a finite
  coercivity constant. Only the flow-matching instance `ϱ = g''(1)w_min/B̂²` is stated; the
  detailed-balance instances (`1 + B̂`, `1 + B̂_σ`) are not.
* **What is held fixed as `p → 1`.** `g''(1) ≥ 0` is a constant; `w_min` is a constant or, in
  `rho_mixing_tendsto` and `rhoSigma_cycle_tendsto`, any family eventually in `[0, W]`. For `κ`:
  fixed positive `u₀` (`kappa_cycle_tendsto`), fixed positive `μ₀` with `u₀ = μ₀/λ_p`
  (`kappa_cycle_tendsto_fixed_measure`), or any family with `‖u₀(p)‖_{L²(λ_p)}` bounded below
  (`kappa_cycle_tendsto_gen`); the initial loss `𝓛(μ₀)` and `‖w‖_∞ ≥ w_min` are arbitrary. `κ` is the
  printed formula as `Balance.global_lojasiewicz_static` writes it, with `λ_min = Graph.minOver cyc
  (lam p)`.
* **The rescaled flow.** Existence is stated on the five-vertex cycle with `ν = wλ`,
  `w ≥ w_min > 0`, for both generators of `prop:no_distant_equilibrium`*(3)*; the identity
  `v_t = αu_{t/α²}` holds for any two positive flows from `u₀` and `αu₀` (`rescaled_flow`, on any
  finite invariant kernel, `g'` `C¹` on `(0,∞)`). "Runs `Θ(M²)` times slower than the normalized
  one" is certified as the exact law behind it: initial norm `×α`, entry times into
  `{|r − 1| < δ}` `×α²`, first entry time `×α²` (`sInf`, which is `0` for an empty set on both sides).
  **That the over-inflated `uInfl M` has a transient of order `M²` is not certified**: `uInfl M` is
  `M` on the cycle and `1` at the marks, not `M` times a fixed flow, and its normalization
  degenerates as `M → ∞`; the paper marks that sentence "Numerically", and `0.720` is not a target.
* **Not certified**: the example identity inside the Proposition 3.12 sentence, "total flow
  through the internal states `F(s_f)·3/(1−p)`" (a few lines from `invProb_paper`), and its reading
  "no exploding circulation" — claims, left open (no ruling exempts them). **Not certification
  targets**: the citation of Proposition 3.12 of `morozov2025revisiting` itself, the numbers `0.720` and `1.62`, and the heuristic "persistent leak
  ratio". **Not stated here**: "after which the exponential phase of Theorem
  `theo:local_convergence` takes over", which sits in the numerical sentence (the two-phase
  structure is `theo:training_speed_full`'s, certified on marked graphs in `TrainingSpeed.lean`).
* **Inherited**: `IsGradientFlow` asks a two-sided derivative at `t = 0` (`FlowExistence.lean`);
  `logSqDeriv` is the definition `2 log x/x`, tied to `logSq` by `Balance.hasDerivAt_logSq`.
* **No `sorry`.**

## Hypothesis checklist — `lem:cycle_counterexample`

| paper hypothesis | here |
|---|---|
| `N ≥ 2`, `𝒞_N`, `F̂`, `γ`, `F_k = F̂ + kγ` | ✓ inherited: `N = M + 2`, `cycGraph`, `Fhat`, `gammaC`, `Fk` |
| `k` an integer `≥ 0` | ✓ `k : ℕ`, cast into `Fk` |
| `target` a probability on `{x₁,…,x_N}` | ✓ `t : Fin N → ℝ`, `∀ i, 0 ≤ t i`, `∑ t = 1`, extended by `extT` |
| `ν_train` a finite measure on `{x₁,…,x_N}` | ⚠ weakened to any real weight (unused) |
| `𝓛(F) = ∫ g(ρ_F) dν_train`, `ρ_F = (F_init + f_←)/(target + f_→)` | ✓ `fmLossTarget`, `fmRatio` (identified with `Balance.loss` by `CycleDivergence.fmLossTarget_eq_loss`) |
| `g : ℝ₊ → ℝ₊` vanishing exactly at `1` | ⚠ weakened: `g : ℝ → ℝ`, `g 1 = 0` only |
| `g` continuous at `1` | ✓ `ContinuousAt g 1` |
| `equ:FM_const` with terminal flow `δ_{x₂}` | ✓ `Fk_FM_const`, `Fk_x_snk`, `Fk_src_x` |
| `s_τ(F_k) ∼ δ_{x₂}` (by `theo:sampling_theorem`) | ✗ **not certified** — Phase 3; `termLaw_Fk` in its place |
| "`𝓛(F_k)` defined for `k ≥ 1`" | ✓ read as positivity of the denominator and of `ρ` |

## Hypothesis checklist — `rem:cycle_no_stalemate` (the clauses of this file)

| paper hypothesis | here |
|---|---|
| the five-vertex marked graph, loop-closed, `π_←(x₁→x₃) = p`, `π_←(x₁→s₀) = 1−p`, `p ∈ (0,1)` | ✓ `CycleExample.cyc`, `pol`, `kern`; `kern p` at the endpoints |
| `λ` the invariant probability | ✓ `lam p` (`CycleExample.invProb_eq` on `(0,1)`, `invProb_endpoint_unique` at `{0,1}`) |
| `β̂ₙ = ‖Pⁿ − Π‖_{L²(λ)}` | ✓ `betaCyc` = `Core.Mixing.beta (densOp (lam p) (kern p)) (meanOp (lam p))` |
| `g = (log x)²` (force, criticality) | ✓ `logSqDeriv`, `logSq` |
| `ν` of positive density | ✓ `∀ x, 0 < nu x` |
| `M > 1` | ✓ `1 < M` |
| "for a flow `μ₀ ∼ λ` with gradient flow `(μ_t)`", `α > 0` | ✓ `u 0 = u0`, `∀ x, 0 < u0 x`, `IsGradientFlow`, positivity on `[0,∞)`, `0 < α` |
| "exists by Proposition `prop:no_distant_equilibrium`*(3)*" | ✓ `existsUnique_flow_logSq_graph`, `existsUnique_flow_sq_graph`, with `ν = wλ`, `w ≥ w_min > 0` |
| `p → 1` | ✓ `𝓝[<] 1` |
| `ϱ = g''(1)w_min/B̂²` | ✓ `Balance.rhoL`, `g''(1) ≥ 0` a constant, `w_min` eventually in `[0,W]` |
| `ϱ_σ` | ✓ `Balance.rhoL … (BhatSigma …)` and `Balance.rhoSigma` |
| `κ` of `cor:global_lojasiewicz` | ✓ the printed formula; see SCOPE for what is held fixed |

## Inhabitation (kb 0025)

`cycle_counterexample_check` meets every hypothesis of `cycle_counterexample` (`N = 2`, uniform
target, `g = (x − 1)²`). `cycle_rescaled_flow_check` exhibits, at `p = 1/2`, `w ≡ 1`, from the
non-balanced `uInfl 2` and `α = 3`, both gradient flows `rescaled_flow` quantifies over; more
generally `cycle_rescaled_flow`/`_sq` produce them from every positive start. `mixing_cycle`
inhabits `Core.Mixing` at every `p ∈ (0,1)` on a density action that is not a projection.
`kappa_cycle_tendsto` and `kappa_cycle_tendsto_fixed_measure` discharge the lower-bound hypothesis of
`kappa_cycle_tendsto_gen`; constant weights discharge the family hypotheses of
`rho_mixing_tendsto` and `rhoSigma_cycle_tendsto` (`cycle_no_stalemate_limits`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph
namespace CycleRemarks

open Filter Topology
open scoped Pointwise

/-! ## `lem:cycle_counterexample` -/

section Counterexample

open CycleDivergence

variable {M : ℕ}

/-- A measure on the internal states `{x₁,…,x_N}`, extended by `0` at the two marks. -/
def extT (M : ℕ) (t : Fin (M + 2) → ℝ) : cycV M → ℝ
  | none => 0
  | some none => 0
  | some (some i) => t i

@[simp] theorem extT_srcC (t : Fin (M + 2) → ℝ) : extT M t (srcC M) = 0 := rfl

@[simp] theorem extT_snkC (t : Fin (M + 2) → ℝ) : extT M t (snkC M) = 0 := rfl

@[simp] theorem extT_x (t : Fin (M + 2) → ℝ) (i : Fin (M + 2)) : extT M t (xC M i) = t i := rfl

/-- The initial flow of `F_k` is `δ_{x₁}`. -/
theorem Fk_src_x (k : ℝ) (i : Fin (M + 2)) :
    Fk M k (srcC M) (xC M i) = if i = 0 then 1 else 0 := by
  have hg : gammaC M (srcC M) (xC M i) = 0 := by
    rw [gammaC_apply]
    exact Finset.sum_eq_zero fun j _ => unitEdge_eq_zero_of_ne_left (srcC_ne_xC j) _
  simp only [Fk, hg, mul_zero, add_zero, Fhat_apply]
  rw [unitEdge_left, unitEdge_eq_zero_of_ne_left (srcC_ne_xC 0),
    unitEdge_eq_zero_of_ne_left (srcC_ne_xC 1)]
  simp only [xC_inj, add_zero]

/-- The terminal flow of `F_k` is `δ_{x₂}`. -/
theorem Fk_x_snk (k : ℝ) (i : Fin (M + 2)) :
    Fk M k (xC M i) (snkC M) = if i = 1 then 1 else 0 := by
  rw [Fk_snkC]
  simp only [xC_inj]

/-- **`equ:FM_const` at every internal state, written with its four terms.** -/
theorem Fk_FM_const (k : ℝ) (i : Fin (M + 2)) :
    Fk M k (srcC M) (xC M i) + ∑ j, Fk M k (xC M j) (xC M i)
      = Fk M k (xC M i) (snkC M) + ∑ j, Fk M k (xC M i) (xC M j) := by
  have h := Fk_flowMatching (M := M) k (xC M i) (mem_internal_iff.mpr ⟨i, rfl⟩)
  simp only [edgeInflow, edgeOutflow] at h
  rw [sum_cycV, sum_cycV, Fk_snk_row, Fk_srcC, zero_add, zero_add] at h
  exact h

theorem le_one_of_prob {t : Fin (M + 2) → ℝ} (ht : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (i : Fin (M + 2)) : t i ≤ 1 := by
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)

/-- **`TV(δ_{x₂} ‖ target) = 1 − target(x₂)`** for every probability `target` on `{x₁,…,x_N}`. -/
theorem tvFin_termLaw_Fk_gen (k : ℝ) {t : Fin (M + 2) → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hsum : ∑ i, t i = 1) :
    tvFin (termLaw (cycGraph M) (Fk M k)) (extT M t) = 1 - t 1 := by
  have hterm : ∀ i : Fin (M + 2),
      |(if xC M i = xC M 1 then (1 : ℝ) else 0) - extT M t (xC M i)|
        = t i + (if i = 1 then 1 - 2 * t i else 0) := by
    intro i
    simp only [xC_inj, extT_x]
    by_cases hi : i = 1
    · subst hi
      rw [if_pos rfl, if_pos rfl, abs_of_nonneg (by linarith [le_one_of_prob ht hsum 1])]
      ring
    · rw [if_neg hi, if_neg hi, zero_sub, abs_neg, abs_of_nonneg (ht i), add_zero]
  have hsrc : |(if srcC M = xC M 1 then (1 : ℝ) else 0) - extT M t (srcC M)| = 0 := by
    rw [if_neg (srcC_ne_xC 1), extT_srcC, sub_zero, abs_zero]
  have hsnk : |(if snkC M = xC M 1 then (1 : ℝ) else 0) - extT M t (snkC M)| = 0 := by
    rw [if_neg (snkC_ne_xC 1), extT_snkC, sub_zero, abs_zero]
  simp only [tvFin, termLaw_Fk]
  rw [sum_cycV, hsrc, hsnk, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i,
    Finset.sum_add_distrib, hsum, Finset.sum_ite_eq' Finset.univ (1 : Fin (M + 2)),
    if_pos (Finset.mem_univ _)]
  ring

/-- The denominators `bᵢ = target(xᵢ) + 𝟙_{i=1}` of `proofs.tex:396`, for a general target. -/
def bG (t : Fin (M + 2) → ℝ) (i : Fin (M + 2)) : ℝ := t i + if i = 0 then 1 else 0

/-- **`ρ_{F_k}(xᵢ) = (aᵢ + k)/(bᵢ + k)`** for every target. -/
theorem fmRatio_Fk_gen (k : ℝ) (t : Fin (M + 2) → ℝ) (j : Fin (M + 2)) :
    fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M j) = (aC M j + k) / (bG t j + k) := by
  rw [fmRatio, edgeInflow_Fk_x, foutC_Fk_x, extT_x, bG, add_assoc]

theorem aC_nonneg (j : Fin (M + 2)) : 0 ≤ aC M j := by
  unfold aC; split_ifs <;> norm_num

theorem bG_nonneg {t : Fin (M + 2) → ℝ} (ht : ∀ i, 0 ≤ t i) (j : Fin (M + 2)) : 0 ≤ bG t j := by
  unfold bG; split_ifs <;> linarith [ht j]

/-- **"`𝓛(F_k)` is defined for `k ≥ 1`"**: the denominator `target + f_→` of the ratio is
positive at every internal state, and the ratio lies in `(0,∞)`, the domain of `g`. -/
theorem den_pos_and_ratio_pos {t : Fin (M + 2) → ℝ} (ht : ∀ i, 0 ≤ t i) {k : ℕ} (hk : 1 ≤ k)
    (j : Fin (M + 2)) :
    0 < extT M t (xC M j) + ∑ v ∈ (cycGraph M).internal, Fk M k (xC M j) v
      ∧ 0 < fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M j) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb := bG_nonneg ht j
  have ha := aC_nonneg (M := M) j
  refine ⟨?_, ?_⟩
  · rw [foutC_Fk_x, extT_x]
    have : 0 ≤ (if j = 0 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    linarith [ht j]
  · rw [fmRatio_Fk_gen]
    exact div_pos (by linarith) (by linarith)

theorem abs_aC_sub_bG_le {t : Fin (M + 2) → ℝ} (ht : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (j : Fin (M + 2)) : |aC M j - bG t j| ≤ 1 := by
  have h1 := le_one_of_prob ht hsum j
  have h0 := ht j
  rw [abs_le]
  unfold aC bG
  by_cases hj0 : j = 0
  · rw [if_pos hj0, if_pos hj0]; constructor <;> linarith
  · by_cases hj1 : j = 1
    · rw [if_neg hj0, if_pos hj1, if_neg hj0]; constructor <;> linarith
    · rw [if_neg hj0, if_neg hj1, if_neg hj0]; constructor <;> linarith

/-- **The display of `proofs.tex:396`**, with the constant made explicit:
`|ρ_{F_k}(xᵢ) − 1| = |aᵢ − bᵢ|/(bᵢ + k) ≤ max_j |a_j − b_j|/k ≤ 1/k` for `k ≥ 1`. -/
theorem abs_fmRatio_Fk_sub_one {t : Fin (M + 2) → ℝ} (ht : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    {k : ℕ} (hk : 1 ≤ k) (i : Fin (M + 2)) :
    |fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M i) - 1| = |aC M i - bG t i| / (bG t i + k)
      ∧ |aC M i - bG t i| / (bG t i + k)
          ≤ (Finset.univ.sup' Finset.univ_nonempty fun j => |aC M j - bG t j|) / k
      ∧ (Finset.univ.sup' Finset.univ_nonempty fun j => |aC M j - bG t j|) / k ≤ 1 / k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hb := bG_nonneg ht i
  have hden : 0 < bG t i + k := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [fmRatio_Fk_gen, div_sub_one hden.ne', abs_div, abs_of_pos hden]
    congr 1
    ring_nf
  · have hle : |aC M i - bG t i|
        ≤ Finset.univ.sup' Finset.univ_nonempty fun j => |aC M j - bG t j| :=
      Finset.le_sup' (fun j => |aC M j - bG t j|) (Finset.mem_univ i)
    calc |aC M i - bG t i| / (bG t i + k) ≤ |aC M i - bG t i| / k :=
          div_le_div_of_nonneg_left (abs_nonneg _) hk0 (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hle hk0.le
  · refine div_le_div_of_nonneg_right ?_ hk0.le
    exact Finset.sup'_le _ _ fun j _ => abs_aC_sub_bG_le ht hsum j

/-- **`𝓛(F_k) → 0` as `k → ∞` through the integers**, for every target and every training
measure, when `g` is continuous at `1` with `g(1) = 0`. -/
theorem fmLossTarget_Fk_tendsto_zero_gen (g : ℝ → ℝ) (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (nu : cycV M → ℝ) (t : Fin (M + 2) → ℝ) :
    Tendsto (fun k : ℕ => fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) atTop (𝓝 0) := by
  have hterm : ∀ x ∈ (cycGraph M).internal,
      Tendsto (fun k : ℕ => nu x * g (fmRatio (cycGraph M) (extT M t) (Fk M k) x))
        atTop (𝓝 (nu x * g 1)) := by
    intro x hx
    obtain ⟨j, rfl⟩ := mem_internal_iff.mp hx
    have hr : Tendsto (fun k : ℕ => fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M j))
        atTop (𝓝 1) := by
      simp only [fmRatio_Fk_gen]
      exact (tendsto_affine_ratio (aC M j) (bG t j)).comp tendsto_natCast_atTop_atTop
    exact (hgc.tendsto.comp hr).const_mul (nu (xC M j))
  have hsum := tendsto_finsetSum (cycGraph M).internal hterm
  simp only [hg1, mul_zero, Finset.sum_const_zero] at hsum
  exact hsum

end Counterexample

/-! ## `rem:cycle_no_stalemate`: the force, and the configuration is not critical -/

section Force

open CycleExample Balance

/-- `|g'(r)r| = 2|log r|` for `g = (log x)²` and `r > 0`. -/
theorem force_eq {r : ℝ} (hr : 0 < r) : |logSqDeriv r * r| = 2 * |Real.log r| := by
  rw [logSqDeriv, div_mul_cancel₀ _ hr.ne', abs_mul, abs_two]

/-- `1/M < r(x₃) < 1` for `M > 1`. -/
theorem ratio_x3_bounds {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 1 < M) :
    1 / M < ratio (pol hp0 hp1).phat (lam p) (uInfl M) 3
      ∧ ratio (pol hp0 hp1).phat (lam p) (uInfl M) 3 < 1 := by
  have hM0 : (0 : ℝ) < M := by linarith
  rw [ratio_x3 hp0 hp1 hM0]
  refine ⟨?_, ?_⟩
  · have h : p / M < p := div_lt_self hp0 hM
    have e : 1 / M = p / M + (1 - p) / M := by field_simp; ring
    linarith
  · have h : (1 - p) / M < 1 - p := div_lt_self (by linarith) hM
    linarith

/-- **`rem:cycle_no_stalemate`, the inflation force**: for `g = (log x)²` and `M > 1`, the force
`|g'(r)r| = 2|log r|` equals `2 log M` at the starved source `s₀`, is **strictly** smaller at
every other state — so it is largest at `s₀` — and, at `s₀`, strictly increases with `M` on
`(1, ∞)`. -/
theorem inflation_force_max_mono {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ M : ℝ, 1 < M → ∀ x : Fin 5,
      |logSqDeriv (ratio (pol hp0 hp1).phat (lam p) (uInfl M) x)
          * ratio (pol hp0 hp1).phat (lam p) (uInfl M) x|
        = 2 * |Real.log (ratio (pol hp0 hp1).phat (lam p) (uInfl M) x)|)
    ∧ (∀ M : ℝ, 1 < M →
      |logSqDeriv (ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0)
          * ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0| = 2 * Real.log M)
    ∧ (∀ M : ℝ, 1 < M → ∀ x : Fin 5, x ≠ 0 →
      |logSqDeriv (ratio (pol hp0 hp1).phat (lam p) (uInfl M) x)
          * ratio (pol hp0 hp1).phat (lam p) (uInfl M) x|
        < |logSqDeriv (ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0)
          * ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0|)
    ∧ StrictMonoOn (fun M : ℝ => |logSqDeriv (ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0)
          * ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0|) (Set.Ioi 1) := by
  have hrpos : ∀ M : ℝ, 1 < M → ∀ x, 0 < ratio (pol hp0 hp1).phat (lam p) (uInfl M) x :=
    fun M hM => ratio_pos (invariant_of_isInvProb (isInvProb hp0 hp1)) (pol hp0 hp1).phat_nonneg
      (lam_pos hp1) (uInfl_pos (by linarith))
  have hsrc : ∀ M : ℝ, 1 < M →
      |logSqDeriv (ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0)
          * ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0| = 2 * Real.log M := by
    intro M hM
    rw [force_eq (hrpos M hM 0), ratio_src hp0 hp1 (by linarith),
      abs_of_pos (Real.log_pos hM)]
  refine ⟨fun M hM x => force_eq (hrpos M hM x), hsrc, ?_, ?_⟩
  · intro M hM x hx
    have hM0 : (0 : ℝ) < M := by linarith
    have hlogM := Real.log_pos hM
    rw [hsrc M hM, force_eq (hrpos M hM x)]
    fin_cases x
    · exact absurd rfl hx
    · rw [show ((⟨1, by norm_num⟩ : Fin 5)) = 1 from rfl, ratio_x1 hp0 hp1 hM0, Real.log_one,
        abs_zero]
      linarith
    · rw [show ((⟨2, by norm_num⟩ : Fin 5)) = 2 from rfl, ratio_x2 hp0 hp1 hM0, Real.log_one,
        abs_zero]
      linarith
    · rw [show ((⟨3, by norm_num⟩ : Fin 5)) = 3 from rfl]
      obtain ⟨hlo, hhi⟩ := ratio_x3_bounds hp0 hp1 hM
      have hr3 := hrpos M hM 3
      have hneg : Real.log (ratio (pol hp0 hp1).phat (lam p) (uInfl M) 3) < 0 :=
        Real.log_neg hr3 hhi
      have hgt : Real.log (1 / M) < Real.log (ratio (pol hp0 hp1).phat (lam p) (uInfl M) 3) :=
        Real.log_lt_log (by positivity) hlo
      rw [one_div, Real.log_inv] at hgt
      rw [abs_of_neg hneg]
      linarith
    · rw [show ((⟨4, by norm_num⟩ : Fin 5)) = 4 from rfl, ratio_snk hp0 hp1 hM0, Real.log_one,
        abs_zero]
      linarith
  · intro M₁ hM₁ M₂ hM₂ h12
    simp only [Set.mem_Ioi] at hM₁ hM₂
    dsimp only
    rw [hsrc M₁ hM₁, hsrc M₂ hM₂]
    have := Real.log_lt_log (by linarith) h12
    linarith

/-- **`rem:cycle_no_stalemate`, "the configuration is not a critical point of `𝓛_{g,ν}` for any
`ν` of positive density"**, on the Fréchet reading (kb 0035): the directional derivatives of the
loss at the over-inflated density do not all vanish. The route is the remark's:
`prop:no_distant_equilibrium`*(1)* — a critical point is balanced
(`Balance.balanced_of_hasDerivAt_zero_graph`) — and `r(x₃) ≠ 1`. -/
theorem not_critical {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 1 < M) {nu : Fin 5 → ℝ}
    (hnu : ∀ x, 0 < nu x) :
    ¬ ∀ d : Fin 5 → ℝ, HasDerivAt
        (fun t : ℝ => loss (pol hp0 hp1).phat (lam p) nu (fun x => uInfl M x + t * d x) logSq) 0 0 := by
  intro hcrit
  have hM0 : (0 : ℝ) < M := by linarith
  have hbal := balanced_of_hasDerivAt_zero_graph pathConnected (positiveOnEdges hp0 hp1)
    (isInvProb hp0 hp1) (uInfl_pos hM0) hnu (fun y hy => hasDerivAt_logSq hy)
    strictlyUnimodal_logSqDeriv hcrit
  have h1 := (ratio_eq_one_iff_balanced
    (fun y => mul_pos (lam_pos hp1 y) (uInfl_pos hM0 y))).mpr hbal 3
  exact absurd h1 (ratio_x3_bounds hp0 hp1 hM).2.ne

end Force

/-! ## `rem:cycle_no_stalemate`: the rescaled flow -/

section Rescale

open Balance

variable {V : Type*} [Fintype V]

/-- **`t ↦ α μ_{t/α²}` is a gradient flow** whenever `t ↦ μ_t` is (`Balance.flow_rescale` at
`c = α⁻¹`, `t₁ = 0`). -/
theorem isGradientFlow_scale {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd u) {α : ℝ} (hα : 0 < α) :
    IsGradientFlow K lam nu gd (fun t x => α * u (t / α ^ 2) x) := by
  have h := flow_rescale hflow (inv_pos.mpr hα) le_rfl
  have heq : (fun s x => α⁻¹⁻¹ * u (0 + α⁻¹ ^ 2 * s) x) = fun t x => α * u (t / α ^ 2) x := by
    funext s x
    rw [inv_inv, zero_add, inv_pow, inv_mul_eq_div]
  rwa [heq] at h

/-- **`rem:cycle_no_stalemate`, the rescaled flow, on any finite chain**: for a positive gradient
flow `(μ_t)_{t≥0}` and `α > 0`, the curve `t ↦ αμ_{t/α²}` is a positive gradient flow started at
`αμ₀`, and every positive gradient flow started at `αμ₀` is that curve on `[0,∞)`. Any `g'` that
is `C¹` on `(0,∞)`. -/
theorem rescaled_flow {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hgd : ∀ y : ℝ, 0 < y → ContDiffAt ℝ 1 gd y) {u : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd u) (hpos : ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
    {α : ℝ} (hα : 0 < α) :
    IsGradientFlow K lam nu gd (fun t x => α * u (t / α ^ 2) x)
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < α * u (t / α ^ 2) x)
      ∧ ∀ v : ℝ → V → ℝ, v 0 = (fun x => α * u 0 x) → IsGradientFlow K lam nu gd v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = fun x => α * u (t / α ^ 2) x := by
  have hsc := isGradientFlow_scale hflow hα
  have hscpos : ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < α * u (t / α ^ 2) x :=
    fun t ht x => mul_pos hα (hpos _ (by positivity) x)
  refine ⟨hsc, hscpos, fun v hv0 hv hvpos t ht => ?_⟩
  have h0 : v 0 = (fun t x => α * u (t / α ^ 2) x) 0 := by
    rw [hv0]; funext x; show α * u 0 x = α * u (0 / α ^ 2) x; rw [zero_div]
  exact isGradientFlow_unique hinv hK hlam hgd hv hsc hvpos hscpos h0 t ht

/-- The times at which every ratio lies within `δ` of `1`. -/
def entryTimes (K : V → V → ℝ) (lam : V → ℝ) (u : ℝ → V → ℝ) (δ : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ ∀ x, |ratio K lam (u t) x - 1| < δ}

/-- **"A trajectory started at norm `αM` runs `α²` times slower"**: the rescaled flow reaches the
band `|r − 1| < δ` exactly at the times `α²t`, `t` a time the original one does, and its first
such time is `α²` times the original one — the ratios being scale-invariant. -/
theorem entryTimes_scale {K : V → V → ℝ} {lam : V → ℝ} {u : ℝ → V → ℝ} {α : ℝ} (hα : 0 < α)
    (δ : ℝ) :
    entryTimes K lam (fun t x => α * u (t / α ^ 2) x) δ = α ^ 2 • entryTimes K lam u δ
      ∧ sInf (entryTimes K lam (fun t x => α * u (t / α ^ 2) x) δ)
          = α ^ 2 * sInf (entryTimes K lam u δ) := by
  have hα2 : (0 : ℝ) < α ^ 2 := by positivity
  have hset : entryTimes K lam (fun t x => α * u (t / α ^ 2) x) δ = α ^ 2 • entryTimes K lam u δ := by
    ext t
    simp only [entryTimes, Set.mem_setOf_eq, ratio_smul hα.ne', Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨ht, hr⟩
      exact ⟨t / α ^ 2, ⟨div_nonneg ht hα2.le, hr⟩, mul_div_cancel₀ t hα2.ne'⟩
    · rintro ⟨s, ⟨hs, hr⟩, rfl⟩
      refine ⟨mul_nonneg hα2.le hs, ?_⟩
      rwa [mul_div_cancel_left₀ s hα2.ne']
  refine ⟨hset, ?_⟩
  rw [hset, Real.sInf_smul_of_nonneg hα2.le, smul_eq_mul]

end Rescale

section RescaleCycle

open CycleExample Balance

/-- **`rem:cycle_no_stalemate`, the rescaled flow, on the five-vertex cycle** for `g = (log x)²`
and `ν = wλ`, `w ≥ w_min > 0`: from any `μ₀ ∼ λ` and any `α > 0` the gradient flows from `μ₀` and
from `αμ₀` exist (`prop:no_distant_equilibrium`*(3)*, `existsUnique_flow_logSq_graph`), and for
any two such positive flows `u`, `v`, `v_t = αu_{t/α²}` on `[0,∞)`; the first entry time into
`|r − 1| < δ` of the second is `α²` times that of the first. -/
theorem cycle_rescaled_flow {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {wf : Fin 5 → ℝ} {wmin : ℝ}
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) {u0 : Fin 5 → ℝ} (hu0 : ∀ x, 0 < u0 x)
    {α : ℝ} (hα : 0 < α) :
    (∃ u : ℝ → Fin 5 → ℝ, u 0 = u0
      ∧ IsGradientFlow (pol hp0 hp1).phat (lam p) (fun x => lam p x * wf x) logSqDeriv u
      ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
    ∧ (∃ v : ℝ → Fin 5 → ℝ, v 0 = (fun x => α * u0 x)
      ∧ IsGradientFlow (pol hp0 hp1).phat (lam p) (fun x => lam p x * wf x) logSqDeriv v
      ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x)
    ∧ ∀ u v : ℝ → Fin 5 → ℝ, u 0 = u0 → v 0 = (fun x => α * u0 x) →
      IsGradientFlow (pol hp0 hp1).phat (lam p) (fun x => lam p x * wf x) logSqDeriv u →
      IsGradientFlow (pol hp0 hp1).phat (lam p) (fun x => lam p x * wf x) logSqDeriv v →
      (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x) → (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) →
      (∀ t : ℝ, 0 ≤ t → v t = fun x => α * u (t / α ^ 2) x)
        ∧ ∀ δ : ℝ, sInf (entryTimes (pol hp0 hp1).phat (lam p) v δ)
            = α ^ 2 * sInf (entryTimes (pol hp0 hp1).phat (lam p) u δ) := by
  have hαu0 : ∀ x, 0 < α * u0 x := fun x => mul_pos hα (hu0 x)
  obtain ⟨u, hu0', hflow, hpos, -⟩ :=
    existsUnique_flow_logSq_graph pathConnected (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1)
      hwmin hw hu0
  obtain ⟨v, hv0', hvflow, hvpos, -⟩ :=
    existsUnique_flow_logSq_graph pathConnected (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1)
      hwmin hw hαu0
  refine ⟨⟨u, hu0', hflow, hpos⟩, ⟨v, hv0', hvflow, hvpos⟩, ?_⟩
  intro u v hu0 hv0 hu hv hupos hvpos
  have hinv := invariant_of_isInvProb (isInvProb hp0 hp1)
  have hgd : ∀ y : ℝ, 0 < y → ContDiffAt ℝ 1 logSqDeriv y := logSqFlowGenerator.contDiffAt
  obtain ⟨-, -, huniq⟩ := rescaled_flow hinv (pol hp0 hp1).phat_nonneg (lam_pos hp1) hgd hu hupos hα
  have hvt := huniq v (by rw [hv0, hu0]) hv hvpos
  refine ⟨hvt, fun δ => ?_⟩
  have hset : entryTimes (pol hp0 hp1).phat (lam p) v δ
      = entryTimes (pol hp0 hp1).phat (lam p) (fun t x => α * u (t / α ^ 2) x) δ := by
    ext t
    simp only [entryTimes, Set.mem_setOf_eq]
    constructor
    · rintro ⟨ht, hr⟩; exact ⟨ht, by rwa [← hvt t ht]⟩
    · rintro ⟨ht, hr⟩; exact ⟨ht, by rwa [hvt t ht]⟩
  rw [hset]
  exact (entryTimes_scale hα δ).2

end RescaleCycle

/-! ## `rem:cycle_no_stalemate`: the mixing sum -/

section OperatorShelf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A contraction's powers are contractions. -/
theorem norm_pow_apply_le {P : E →L[ℝ] E} (hP : ∀ w, ‖P w‖ ≤ ‖w‖) (n : ℕ) (w : E) :
    ‖(P ^ n) w‖ ≤ ‖w‖ := by
  induction n with
  | zero => rw [pow_zero, one_apply_eq_self]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact (hP _).trans ih

/-- `‖P^{mk}v − v‖ ≤ k‖P^m v − v‖` for a contraction `P`. -/
theorem norm_pow_mul_apply_sub_le {P : E →L[ℝ] E} (hP : ∀ w, ‖P w‖ ≤ ‖w‖) (m k : ℕ) (v : E) :
    ‖(P ^ (m * k)) v - v‖ ≤ k * ‖(P ^ m) v - v‖ := by
  induction k with
  | zero => rw [mul_zero, pow_zero, one_apply_eq_self, sub_self, norm_zero,
      Nat.cast_zero, zero_mul]
  | succ k ih =>
    have hsplit : (P ^ (m * (k + 1))) v - v
        = (P ^ (m * k)) ((P ^ m) v - v) + ((P ^ (m * k)) v - v) := by
      rw [mul_add, mul_one, pow_add, mul_apply_eq_comp, map_sub]
      abel
    rw [hsplit, Nat.cast_succ, add_mul, one_mul]
    calc ‖(P ^ (m * k)) ((P ^ m) v - v) + ((P ^ (m * k)) v - v)‖
        ≤ ‖(P ^ (m * k)) ((P ^ m) v - v)‖ + ‖(P ^ (m * k)) v - v‖ := norm_add_le _ _
      _ ≤ ‖(P ^ m) v - v‖ + k * ‖(P ^ m) v - v‖ :=
          add_le_add (norm_pow_apply_le hP _ _) ih
      _ = k * ‖(P ^ m) v - v‖ + ‖(P ^ m) v - v‖ := add_comm _ _

/-- A fixed point of `P^m` is a fixed point of every `P^{mk}`. -/
theorem pow_mul_apply_eq_self {P : E →L[ℝ] E} {m : ℕ} {v : E} (h : (P ^ m) v = v) (k : ℕ) :
    (P ^ (m * k)) v = v := by
  induction k with
  | zero => rw [mul_zero, pow_zero, one_apply_eq_self]
  | succ k ih => rw [mul_add, mul_one, pow_add, mul_apply_eq_comp, h, ih]

/-- `‖P^n v‖ ≤ β̂_n ‖v‖` for `v` killed by the projection. -/
theorem norm_pow_apply_le_beta {P Pi : E →L[ℝ] E} {v : E} (hPi : Pi v = 0) (n : ℕ) :
    ‖(P ^ n) v‖ ≤ Core.Mixing.beta P Pi n * ‖v‖ := by
  have h := (P ^ n - Pi).le_opNorm v
  rwa [sub_apply, hPi, sub_zero] at h

/-- A sub-sum along the multiples of `m` bounds the partial sum of a non-negative sequence. -/
theorem sum_range_mul_le {β : ℕ → ℝ} (hβ : ∀ n, 0 ≤ β n) {m : ℕ} (hm : 0 < m) (K : ℕ) :
    ∑ k ∈ Finset.range K, β (m * k) ≤ ∑ n ∈ Finset.range (m * K), β n := by
  induction K with
  | zero => rw [Finset.range_zero, Finset.sum_empty, mul_zero, Finset.range_zero, Finset.sum_empty]
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, mul_one, Finset.sum_range_add]
    have hsingle : β (m * K) ≤ ∑ j ∈ Finset.range m, β (m * K + j) := by
      have := Finset.single_le_sum (f := fun j => β (m * K + j)) (fun j _ => hβ _)
        (Finset.mem_range.mpr hm)
      simpa only [add_zero] using this
    linarith

end OperatorShelf

section MixingCycle

open CycleExample Balance

/-- **`β̂_n = ‖Pⁿ − Π‖_{L²(λ)}`** for the loop-closed backward chain of the remark at `p`, `P` its
density action and `Π` the `λ`-mean projection — `Core.Mixing.beta` of the library's `densOp`,
`meanOp`, at the kernel `kern p` and the measure `lam p`. -/
noncomputable def betaCyc (p : ℝ) (n : ℕ) : ℝ :=
  Core.Mixing.beta (densOp (lam p) (kern p)) (meanOp (lam p)) n

theorem betaCyc_nonneg (p : ℝ) (n : ℕ) : 0 ≤ betaCyc p n := Core.Mixing.beta_nonneg _ _ n

/-- The loop-closed kernel is Markov on `[0,1]`. -/
theorem kern_isMarkov {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Core.IsMarkov (kern p) where
  nonneg := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, kern] <;> linarith
  row_sum := by
    intro x
    fin_cases x <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.sum_univ_five, kern] <;> ring

/-- `lam p` is invariant for `kern p` on `[0,1]`, endpoints included. -/
theorem lam_isInvariant {p : ℝ} (hp1 : p ≤ 1) : Core.IsInvariant (lam p) (kern p) where
  nonneg := by
    intro x
    have hd : (0 : ℝ) < 5 - 2 * p := by linarith
    fin_cases x <;> simp only [lam] <;> apply div_nonneg <;> linarith
  inv := by
    intro y
    fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.sum_univ_five, kern, lam] <;> ring

/-- **At `p ∈ {0,1}`, `lam p` is the only invariant probability of `kern p`**: the mixing sum there
is read against the right measure. -/
theorem invProb_endpoint_unique {p : ℝ} (hp : p = 0 ∨ p = 1) {m : Fin 5 → ℝ}
    (hinv : ∀ y, ∑ x, m x * kern p x y = m y) (hsum : ∑ x, m x = 1) : m = lam p := by
  have h0 := hinv 0
  have h1 := hinv 1
  have h2 := hinv 2
  have h3 := hinv 3
  have h4 := hinv 4
  rw [Fin.sum_univ_five] at hsum
  rcases hp with rfl | rfl
  · simp only [Fin.sum_univ_five, kern] at h0 h1 h2 h3 h4
    funext x
    fin_cases x <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, lam] <;> norm_num <;>
      linarith
  · simp only [Fin.sum_univ_five, kern] at h0 h1 h2 h3 h4
    funext x
    fin_cases x <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, lam] <;> norm_num <;>
      linarith

/-- The density action of `kern p` for `p < 1`, in closed form: a shift along
`s₀ ← x₁ ← x₂ ← x₃ ← {x₁ (p), s_f (1−p)}`, `s_f ← s₀`. -/
noncomputable def shiftK (p : ℝ) (a : Fin 5 → ℝ) : Fin 5 → ℝ
  | 0 => a 1
  | 1 => a 2
  | 2 => a 3
  | 3 => p * a 1 + (1 - p) * a 4
  | 4 => a 0

theorem densAct_kern {p : ℝ} (hp1 : p < 1) (a : Fin 5 → ℝ) :
    Core.densAct (lam p) (kern p) a = shiftK p a := by
  have hprod : ∀ y, lam p y * shiftK p a y = ∑ x, lam p x * kern p x y * a x := by
    intro y
    fin_cases y <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.sum_univ_five, kern, lam, shiftK] <;>
      ring
  funext y
  rw [Core.densAct_apply, ← hprod y, mul_div_cancel_left₀ _ (lam_pos hp1 y).ne']

theorem densOp_pow_wtL2 {p : ℝ} (hp1 : p < 1) (n : ℕ) (a : Fin 5 → ℝ) :
    (densOp (lam p) (kern p) ^ n) (wtL2 (lam p) a) = wtL2 (lam p) ((shiftK p)^[n] a) := by
  induction n with
  | zero => rw [pow_zero, one_apply_eq_self, Function.iterate_zero, id]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, densOp_wtL2 (lam_pos hp1),
      densAct_kern hp1, Function.iterate_succ_apply']

/-- The density action is an `L²(λ)`-contraction for `p ∈ [0,1)`. -/
theorem densOp_contraction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (w : EuclideanSpace ℝ (Fin 5)) :
    ‖densOp (lam p) (kern p) w‖ ≤ ‖w‖ := by
  obtain ⟨a, rfl⟩ := exists_wtL2 (lam_pos hp1) w
  have hinv := lam_isInvariant hp1.le
  rw [densOp_wtL2 (lam_pos hp1), norm_wtL2 hinv.nonneg, norm_wtL2 hinv.nonneg]
  exact Core.nrmL2_densAct_le (kern_isMarkov hp0 hp1.le) hinv a

/-- The test density `𝟙_{x₁} − 𝟙_{x₂}`, of `λ`-mean zero. -/
def testA : Fin 5 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => -1
  | 3 => 0
  | 4 => 0

theorem meanL2_testA (p : ℝ) : Graph.meanL2 (lam p) testA = 0 := by
  simp only [Graph.meanL2, Fin.sum_univ_five, testA, lam]
  ring

theorem ipL2_testA (p : ℝ) : Graph.ipL2 (lam p) testA testA = 2 / (5 - 2 * p) := by
  simp only [Graph.ipL2, Fin.sum_univ_five, testA, lam]
  ring

theorem meanOp_testA {p : ℝ} (hp1 : p < 1) : meanOp (lam p) (wtL2 (lam p) testA) = 0 := by
  rw [meanOp_wtL2 (lam_pos hp1), meanL2_testA, wtL2_zero]

theorem norm_wtL2_sq {p : ℝ} (hp1 : p ≤ 1) (a : Fin 5 → ℝ) :
    ‖wtL2 (lam p) a‖ ^ 2 = Graph.ipL2 (lam p) a a := by
  have hnn := (lam_isInvariant hp1).nonneg
  rw [norm_wtL2 hnn, Graph.nrmL2, Real.sq_sqrt (Graph.ipL2_self_nonneg hnn a)]

/-- Three steps of the shift move `𝟙_{x₁} − 𝟙_{x₂}` by `δ₃ = (0, p−1, 1−p, 1−p, −1)`. -/
def delta3 (p : ℝ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => p - 1
  | 2 => 1 - p
  | 3 => 1 - p
  | 4 => -1

theorem shiftK_three_sub (p : ℝ) :
    (fun x => (shiftK p)^[3] testA x - testA x) = delta3 p := by
  funext x
  show shiftK p (shiftK p (shiftK p testA)) x - testA x = delta3 p x
  fin_cases x <;>
    simp only [shiftK, testA, delta3] <;> ring

theorem ipL2_delta3 (p : ℝ) :
    Graph.ipL2 (lam p) (delta3 p) (delta3 p) = (1 - p) * (4 - 3 * p) / (5 - 2 * p) := by
  simp only [Graph.ipL2, Fin.sum_univ_five, delta3, lam]
  ring

/-- **The three-step defect is `O(√(1−p))`**: `‖P³v − v‖² ≤ 2(1−p)‖v‖²` for `v = 𝟙_{x₁} − 𝟙_{x₂}`
in `L²(λ)`, on `[0,1)`. -/
theorem three_step_defect {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ‖(densOp (lam p) (kern p) ^ 3) (wtL2 (lam p) testA) - wtL2 (lam p) testA‖ ^ 2
      ≤ 2 * (1 - p) * ‖wtL2 (lam p) testA‖ ^ 2 := by
  have hd : (0 : ℝ) < 5 - 2 * p := by linarith
  rw [densOp_pow_wtL2 hp1, ← wtL2_sub, shiftK_three_sub, norm_wtL2_sq hp1.le,
    norm_wtL2_sq hp1.le, ipL2_delta3, ipL2_testA]
  rw [show 2 * (1 - p) * (2 / (5 - 2 * p)) = 4 * (1 - p) / (5 - 2 * p) by ring]
  refine div_le_div_of_nonneg_right ?_ hd.le
  nlinarith

/-- **`β̂_{3k} ≥ 1/2` for `k ≤ K` once `8K²(1−p) ≤ 1`.** -/
theorem betaCyc_three_mul_ge_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) {K : ℕ}
    (hK : 8 * (K : ℝ) ^ 2 * (1 - p) ≤ 1) {k : ℕ} (hk : k ≤ K) :
    1 / 2 ≤ betaCyc p (3 * k) := by
  set P := densOp (lam p) (kern p) with hP
  set v := wtL2 (lam p) testA with hv
  have hd : (0 : ℝ) < 5 - 2 * p := by linarith
  have hvsq : ‖v‖ ^ 2 = 2 / (5 - 2 * p) := by rw [hv, norm_wtL2_sq hp1.le, ipL2_testA]
  have hv0 : 0 < ‖v‖ := by
    have h2 : 0 < ‖v‖ ^ 2 := by rw [hvsq]; positivity
    exact lt_of_le_of_ne (norm_nonneg v) (fun h => by rw [← h] at h2; norm_num at h2)
  set x := ‖(P ^ 3) v - v‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have hdef : x ^ 2 ≤ 2 * (1 - p) * ‖v‖ ^ 2 := three_step_defect hp0 hp1
  have hKx : (K : ℝ) * x ≤ ‖v‖ / 2 := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hsq : ((K : ℝ) * x) ^ 2 ≤ (‖v‖ / 2) ^ 2 := by
      have h1 : ((K : ℝ) * x) ^ 2 = (K : ℝ) ^ 2 * x ^ 2 := by ring
      have h2 : (K : ℝ) ^ 2 * x ^ 2 ≤ (K : ℝ) ^ 2 * (2 * (1 - p) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdef (by positivity)
      have h3 : (K : ℝ) ^ 2 * (2 * (1 - p) * ‖v‖ ^ 2) ≤ (‖v‖ / 2) ^ 2 := by
        have : (K : ℝ) ^ 2 * (2 * (1 - p) * ‖v‖ ^ 2) = (8 * (K : ℝ) ^ 2 * (1 - p)) * (‖v‖ ^ 2 / 4) := by
          ring
        rw [this, show (‖v‖ / 2) ^ 2 = 1 * (‖v‖ ^ 2 / 4) by ring]
        exact mul_le_mul_of_nonneg_right hK (by positivity)
      linarith
    by_contra hcon'
    have hcon := lt_of_not_ge hcon'
    have : (‖v‖ / 2) ^ 2 < ((K : ℝ) * x) ^ 2 := by
      have hv2 : 0 ≤ ‖v‖ / 2 := by positivity
      nlinarith
    linarith
  have hsub : ‖(P ^ (3 * k)) v - v‖ ≤ ‖v‖ / 2 := by
    calc ‖(P ^ (3 * k)) v - v‖ ≤ k * x :=
          norm_pow_mul_apply_sub_le (densOp_contraction hp0 hp1) 3 k v
      _ ≤ K * x := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hx0
      _ ≤ ‖v‖ / 2 := hKx
  have hlow : ‖v‖ / 2 ≤ ‖(P ^ (3 * k)) v‖ := by
    have h := norm_sub_norm_le v ((P ^ (3 * k)) v)
    rw [norm_sub_rev] at h
    linarith
  have hbeta : ‖(P ^ (3 * k)) v‖ ≤ betaCyc p (3 * k) * ‖v‖ :=
    norm_pow_apply_le_beta (meanOp_testA hp1) (3 * k)
  have : 1 / 2 * ‖v‖ ≤ betaCyc p (3 * k) * ‖v‖ := by linarith
  exact le_of_mul_le_mul_right this hv0

/-- **`∑_{n<3K} β̂_n ≥ K/2` once `8K²(1−p) ≤ 1`.** -/
theorem betaCyc_partial_sum_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) {K : ℕ}
    (hK : 8 * (K : ℝ) ^ 2 * (1 - p) ≤ 1) :
    (K : ℝ) / 2 ≤ ∑ n ∈ Finset.range (3 * K), betaCyc p n := by
  have h1 : ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ≤ ∑ k ∈ Finset.range K, betaCyc p (3 * k) :=
    Finset.sum_le_sum fun k hk =>
      betaCyc_three_mul_ge_half hp0 hp1 hK (Finset.mem_range.mp hk).le
  have h2 := sum_range_mul_le (betaCyc_nonneg p) (by norm_num : 0 < 3) K
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  linarith

/-- The explicit number of blocks `K(C) := ⌊2|C|⌋₊ + 1`. -/
noncomputable def blowK (C : ℝ) : ℕ := ⌊2 * |C|⌋₊ + 1

/-- **`rem:cycle_no_stalemate`, the mixing sum tends to `+∞` as `p → 1`, with an explicit
threshold**: if `1 − 1/(8K(C)²) < p < 1` (and `p ≥ 0`), then the partial sum of `β̂_n` over
`n < 3K(C)` exceeds `C`. -/
theorem mixing_sum_gt {C p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hpδ : 1 - 1 / (8 * (blowK C : ℝ) ^ 2) < p) :
    C < ∑ n ∈ Finset.range (3 * blowK C), betaCyc p n := by
  have hK1 : (1 : ℝ) ≤ blowK C := by
    unfold blowK; push_cast; linarith [(Nat.cast_nonneg ⌊2 * |C|⌋₊ : (0 : ℝ) ≤ _)]
  have hKpos : (0 : ℝ) < 8 * (blowK C : ℝ) ^ 2 := by nlinarith
  have hK : 8 * (blowK C : ℝ) ^ 2 * (1 - p) ≤ 1 := by
    have h : 1 - p < 1 / (8 * (blowK C : ℝ) ^ 2) := by linarith
    rw [lt_div_iff₀ hKpos] at h
    linarith
  have hsum := betaCyc_partial_sum_ge hp0 hp1 hK
  have hfl : 2 * |C| < (blowK C : ℝ) := by
    unfold blowK
    push_cast
    exact Nat.lt_floor_add_one (2 * |C|)
  have hC : C ≤ |C| := le_abs_self C
  linarith

theorem eventually_mixing_threshold (C : ℝ) :
    ∀ᶠ p in 𝓝[<] (1 : ℝ), 0 ≤ p ∧ p < 1 ∧ 1 - 1 / (8 * (blowK C : ℝ) ^ 2) < p := by
  have hKpos : (0 : ℝ) < 1 / (8 * (blowK C : ℝ) ^ 2) := by
    have : (0 : ℝ) < blowK C := by unfold blowK; positivity
    positivity
  have hlt : max 0 (1 - 1 / (8 * (blowK C : ℝ) ^ 2)) < 1 := max_lt (by norm_num) (by linarith)
  filter_upwards [Ioo_mem_nhdsLT hlt] with p hp
  exact ⟨(le_max_left _ _).trans hp.1.le, hp.2, lt_of_le_of_lt (le_max_right _ _) hp.1⟩

/-- **The mixing sum tends to `+∞` as `p → 1⁻`**, partial-sum form (kb 0031): for every `C` the
partial sums eventually exceed `C`. No summability is assumed anywhere. -/
theorem mixing_sum_eventually_gt (C : ℝ) :
    ∀ᶠ p in 𝓝[<] (1 : ℝ), ∃ N : ℕ, C < ∑ n ∈ Finset.range N, betaCyc p n := by
  filter_upwards [eventually_mixing_threshold C] with p hp
  exact ⟨3 * blowK C, mixing_sum_gt hp.1 hp.2.1 hp.2.2⟩

/-- **The mixing sum `∑ₙ β̂ₙ`, read in `[0,∞]`, tends to `+∞` as `p → 1⁻`.** -/
theorem mixing_sum_tendsto_top :
    Tendsto (fun p : ℝ => ∑' n, ENNReal.ofReal (betaCyc p n)) (𝓝[<] 1) (𝓝 ⊤) := by
  refine ENNReal.tendsto_nhds_top fun m => ?_
  filter_upwards [mixing_sum_eventually_gt (m : ℝ)] with p hp
  obtain ⟨N, hN⟩ := hp
  have hS : ENNReal.ofReal (∑ n ∈ Finset.range N, betaCyc p n)
      = ∑ n ∈ Finset.range N, ENNReal.ofReal (betaCyc p n) :=
    ENNReal.ofReal_sum_of_nonneg fun n _ => betaCyc_nonneg p n
  calc (m : ENNReal) = ENNReal.ofReal (m : ℝ) := (ENNReal.ofReal_natCast m).symm
    _ < ENNReal.ofReal (∑ n ∈ Finset.range N, betaCyc p n) :=
        (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (Nat.cast_nonneg m) hN)).mpr hN
    _ = ∑ n ∈ Finset.range N, ENNReal.ofReal (betaCyc p n) := hS
    _ ≤ ∑' n, ENNReal.ofReal (betaCyc p n) := ENNReal.sum_le_tsum _

/-- **The rate `ϱ = g''(1)w_min/B̂²` read at the mixing sum tends to `0` as `p → 1⁻`**, in `[0,∞]`,
where `c/∞ = 0`: no summability is assumed. `c` stands for `g''(1)w_min`. -/
theorem rho_mixing_ennreal_tendsto (c : ℝ) :
    Tendsto (fun p : ℝ => ENNReal.ofReal c / (∑' n, ENNReal.ofReal (betaCyc p n)) ^ 2)
      (𝓝[<] 1) (𝓝 0) := by
  have h2 : Tendsto (fun p : ℝ => (∑' n, ENNReal.ofReal (betaCyc p n)) ^ 2) (𝓝[<] 1) (𝓝 ⊤) := by
    have h := ((ENNReal.continuous_pow 2).tendsto ⊤).comp mixing_sum_tendsto_top
    rwa [ENNReal.top_pow two_ne_zero] at h
  have h := ENNReal.Tendsto.const_div (a := ENNReal.ofReal c) h2 (Or.inr ENNReal.ofReal_ne_top)
  rwa [ENNReal.div_top] at h

/-! ### The endpoints `p ∈ {0,1}` -/

theorem not_summable_of_one_le {β : ℕ → ℝ} {m : ℕ} (hm : 0 < m) (h : ∀ k, 1 ≤ β (m * k)) :
    ¬ Summable β := by
  intro hs
  have h0 := hs.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds one_pos))
  have := hN (m * N) (Nat.le_mul_of_pos_left N hm)
  linarith [h N]

theorem tsum_ofReal_eq_top_of_one_le {β : ℕ → ℝ} (hβ : ∀ n, 0 ≤ β n) {m : ℕ} (hm : 0 < m)
    (h : ∀ k, 1 ≤ β (m * k)) : ∑' n, ENNReal.ofReal (β n) = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  set K := ⌈(r : ℝ)⌉₊ with hK
  have h1 : ∑ k ∈ Finset.range K, (1 : ℝ) ≤ ∑ k ∈ Finset.range K, β (m * k) :=
    Finset.sum_le_sum fun k _ => h k
  have h2 := sum_range_mul_le hβ hm K
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
  have hr : (r : ℝ) ≤ ∑ n ∈ Finset.range (m * K), β n :=
    (Nat.le_ceil (r : ℝ)).trans (h1.trans h2)
  calc (r : ENNReal) = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (∑ n ∈ Finset.range (m * K), β n) := ENNReal.ofReal_le_ofReal hr
    _ = ∑ n ∈ Finset.range (m * K), ENNReal.ofReal (β n) :=
        ENNReal.ofReal_sum_of_nonneg fun n _ => hβ n
    _ ≤ ∑' n, ENNReal.ofReal (β n) := ENNReal.sum_le_tsum _

theorem ipL2_testA_pos {p : ℝ} (hp1 : p ≤ 1) : 0 < ‖wtL2 (lam p) testA‖ := by
  have hd : (0 : ℝ) < 5 - 2 * p := by linarith
  have h2 : 0 < ‖wtL2 (lam p) testA‖ ^ 2 := by
    rw [norm_wtL2_sq hp1, ipL2_testA]; positivity
  exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at h2; norm_num at h2)

theorem one_le_beta_of_fixed {P Pi : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 5)}
    {v : EuclideanSpace ℝ (Fin 5)} (hv : 0 < ‖v‖) (hPi : Pi v = 0) {n : ℕ} (hfix : (P ^ n) v = v) :
    1 ≤ Core.Mixing.beta P Pi n := by
  have h := norm_pow_apply_le_beta (P := P) hPi n
  rw [hfix] at h
  have : 1 * ‖v‖ ≤ Core.Mixing.beta P Pi n * ‖v‖ := by linarith
  exact le_of_mul_le_mul_right this hv

/-- **At `p = 0` the chain is the deterministic `5`-cycle**: `β̂_{5k} ≥ 1` for every `k`. -/
theorem betaCyc_zero_ge (k : ℕ) : 1 ≤ betaCyc 0 (5 * k) := by
  have hfix5 : (densOp (lam 0) (kern 0) ^ 5) (wtL2 (lam 0) testA) = wtL2 (lam 0) testA := by
    rw [densOp_pow_wtL2 (by norm_num)]
    congr 1
    funext x
    show shiftK 0 (shiftK 0 (shiftK 0 (shiftK 0 (shiftK 0 testA)))) x = testA x
    fin_cases x <;> simp only [shiftK, testA] <;> ring
  exact one_le_beta_of_fixed (ipL2_testA_pos (by norm_num)) (meanOp_testA (by norm_num))
    (pow_mul_apply_eq_self hfix5 k)

/-- The density action of `kern 1` in closed form: on `λ = (0, 1/3, 1/3, 1/3, 0)` the two marks
carry no mass and the cycle is a deterministic rotation. -/
def shift1 (a : Fin 5 → ℝ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => a 2
  | 2 => a 3
  | 3 => a 1
  | 4 => 0

/-- `a` cut to the support of `lam 1`. -/
def cutA (a : Fin 5 → ℝ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => a 1
  | 2 => a 2
  | 3 => a 3
  | 4 => 0

theorem unwt_wt_one (a : Fin 5 → ℝ) : unwtL2 (lam 1) (wtL2 (lam 1) a) = cutA a := by
  have hs : Real.sqrt (1 / (5 - 2 * 1)) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hz : Real.sqrt ((1 - 1) / (5 - 2 * 1)) = 0 := by norm_num
  funext x
  fin_cases x <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, unwtL2_apply, wtL2_apply,
    lam, cutA]
  · rw [hz, zero_mul, zero_div]
  · exact mul_div_cancel_left₀ _ hs
  · exact mul_div_cancel_left₀ _ hs
  · exact mul_div_cancel_left₀ _ hs
  · rw [hz, zero_mul, zero_div]

theorem densOp_one_wtL2 (a : Fin 5 → ℝ) :
    densOp (lam 1) (kern 1) (wtL2 (lam 1) a) = wtL2 (lam 1) (shift1 a) := by
  show wtL2 (lam 1) (Core.densAct (lam 1) (kern 1) (unwtL2 (lam 1) (wtL2 (lam 1) a))) = _
  rw [unwt_wt_one]
  congr 1
  funext y
  fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Core.densAct_apply,
    Fin.sum_univ_five, kern, lam, cutA, shift1] <;> norm_num

theorem meanOp_one_testA : meanOp (lam 1) (wtL2 (lam 1) testA) = 0 := by
  show wtL2 (lam 1) (fun _ => Graph.meanL2 (lam 1) (unwtL2 (lam 1) (wtL2 (lam 1) testA))) = 0
  rw [unwt_wt_one]
  have h : Graph.meanL2 (lam 1) (cutA testA) = 0 := by
    simp only [Graph.meanL2, Fin.sum_univ_five, lam, cutA, testA]
    norm_num
  rw [h, wtL2_zero]

/-- **At `p = 1` the cycle `x₁ → x₃ → x₂ → x₁` closes**: `β̂_{3k} ≥ 1` for every `k`. -/
theorem betaCyc_one_ge (k : ℕ) : 1 ≤ betaCyc 1 (3 * k) := by
  have hfix3 : (densOp (lam 1) (kern 1) ^ 3) (wtL2 (lam 1) testA) = wtL2 (lam 1) testA := by
    rw [pow_succ', pow_succ', pow_one, mul_apply_eq_comp, mul_apply_eq_comp, densOp_one_wtL2,
      densOp_one_wtL2, densOp_one_wtL2]
    rfl
  exact one_le_beta_of_fixed (ipL2_testA_pos le_rfl) meanOp_one_testA (pow_mul_apply_eq_self hfix3 k)

/-- **`rem:cycle_no_stalemate`, the endpoints**: at `p = 1` the edge `s₀ → x₁` carries no backward
probability, at `p = 0` the edge `x₃ → x₁` carries none; at both, `kern p` is Markov, `lam p` is its
invariant probability and the only one, and the mixing sum `∑ₙ β̂ₙ` is `+∞` — the coefficients
are not summable, and their sum in `[0,∞]` is `⊤`. -/
theorem mixing_sum_endpoints :
    kern 1 1 0 = 0 ∧ kern 0 1 3 = 0
      ∧ ∀ p : ℝ, p = 0 ∨ p = 1 →
        Core.IsMarkov (kern p) ∧ Core.IsInvariant (lam p) (kern p) ∧ ∑ x, lam p x = 1
          ∧ (∀ m : Fin 5 → ℝ, (∀ y, ∑ x, m x * kern p x y = m y) → ∑ x, m x = 1 → m = lam p)
          ∧ ¬ Summable (betaCyc p) ∧ ∑' n, ENNReal.ofReal (betaCyc p n) = ⊤ := by
  refine ⟨by simp only [kern]; norm_num, by simp only [kern], fun p hp => ?_⟩
  have hp01 : 0 ≤ p ∧ p ≤ 1 := by rcases hp with rfl | rfl <;> norm_num
  have hsum : ∑ x, lam p x = 1 := by
    have hd : (5 : ℝ) - 2 * p ≠ 0 := ne_of_gt (by linarith)
    simp only [Fin.sum_univ_five, lam]
    rw [← add_div, ← add_div, ← add_div, ← add_div, div_eq_one_iff_eq hd]
    ring
  have hge : ∃ m : ℕ, 0 < m ∧ ∀ k, 1 ≤ betaCyc p (m * k) := by
    rcases hp with rfl | rfl
    · exact ⟨5, by norm_num, betaCyc_zero_ge⟩
    · exact ⟨3, by norm_num, betaCyc_one_ge⟩
  obtain ⟨m, hm, hmk⟩ := hge
  exact ⟨kern_isMarkov hp01.1 hp01.2, lam_isInvariant hp01.2, hsum,
    fun m' hinv hs => invProb_endpoint_unique hp hinv hs, not_summable_of_one_le hm hmk,
    tsum_ofReal_eq_top_of_one_le (betaCyc_nonneg p) hm hmk⟩

end MixingCycle

section MixingSummable

open CycleExample Balance

/-! ### Summable mixing on `(0,1)`: a Doeblin minorization in `L²(λ)`

On `(0,1)` the chain is irreducible and aperiodic (cycles of lengths `3` and `5` through `x₃`), so
its mixing sum is finite; this is what makes "the rate read at the mixing sum" a rate. The route is
elementary: the function action `Q` of the reversed chain has `Q¹⁶ ≥ ε¹⁶` entrywise,
`ε = min(p, 1−p)` (explicit paths through `x₃`), a variance identity turns that minorization into
`‖P¹⁶ − Π‖ ≤ √(1 − ε¹⁶)`, and `Pⁿ⁺¹⁶ − Π = (P¹⁶ − Π)(Pⁿ − Π)` gives geometric decay. -/

/-- The forward (reversed) transition matrix: `shiftK p a = Q *ᵥ a`. -/
def Qm (p : ℝ) : Fin 5 → Fin 5 → ℝ
  | 0, 1 => 1
  | 1, 2 => 1
  | 2, 3 => 1
  | 3, 1 => p
  | 3, 4 => 1 - p
  | 4, 0 => 1
  | _, _ => 0

/-- `Q` as a matrix. -/
def Qmat (p : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of (Qm p)

theorem shiftK_eq_mulVec (p : ℝ) (a : Fin 5 → ℝ) : shiftK p a = (Qmat p).mulVec a := by
  funext y
  simp only [Matrix.mulVec, dotProduct, Qmat, Matrix.of_apply, Fin.sum_univ_five]
  fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, shiftK, Qm] <;> ring

theorem shiftK_iterate_eq (p : ℝ) (n : ℕ) (a : Fin 5 → ℝ) :
    (shiftK p)^[n] a = (Qmat p ^ n).mulVec a := by
  induction n with
  | zero => rw [Function.iterate_zero, id, pow_zero, Matrix.one_mulVec]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, shiftK_eq_mulVec, Matrix.mulVec_mulVec, pow_succ']

theorem Qmat_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y x : Fin 5) : 0 ≤ Qmat p y x := by
  simp only [Qmat, Matrix.of_apply]
  fin_cases y <;> fin_cases x <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Qm] <;>
    linarith

theorem Qmat_pow_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (y x : Fin 5) :
    0 ≤ (Qmat p ^ n) y x := by
  induction n generalizing y with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (Qmat_nonneg hp0 hp1 y z) (ih z)

theorem Qmat_row (p : ℝ) (y : Fin 5) : ∑ x, Qmat p y x = 1 := by
  simp only [Qmat, Matrix.of_apply, Fin.sum_univ_five]
  fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Qm] <;> ring

theorem Qmat_pow_row (p : ℝ) (n : ℕ) (y : Fin 5) : ∑ x, (Qmat p ^ n) y x = 1 := by
  induction n generalizing y with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  | succ n ih =>
    simp only [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ih, mul_one]
    exact Qmat_row p y

theorem Qmat_inv (p : ℝ) (x : Fin 5) : ∑ y, lam p y * Qmat p y x = lam p x := by
  simp only [Qmat, Matrix.of_apply, Fin.sum_univ_five]
  fin_cases x <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Qm, lam] <;> ring

theorem Qmat_pow_inv (p : ℝ) (n : ℕ) (x : Fin 5) : ∑ y, lam p y * (Qmat p ^ n) y x = lam p x := by
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  | succ n ih =>
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h : ∀ z, ∑ y, lam p y * ((Qmat p ^ n) y z * Qmat p z x)
        = (∑ y, lam p y * (Qmat p ^ n) y z) * Qmat p z x := by
      intro z
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring
    simp only [h, ih]
    exact Qmat_inv p x

/-- `ε = min(p, 1−p)`. -/
noncomputable def epsQ (p : ℝ) : ℝ := min p (1 - p)

/-- `εⁿ ≤ Qⁿ(y,x)`. -/
def QLb (p : ℝ) (n : ℕ) (y x : Fin 5) : Prop := epsQ p ^ n ≤ (Qmat p ^ n) y x

theorem QLb_chain {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {a b : ℕ} {y z x : Fin 5}
    (h1 : QLb p a y z) (h2 : QLb p b z x) : QLb p (a + b) y x := by
  have he : 0 ≤ epsQ p := le_min hp0.le (by linarith)
  unfold QLb at *
  rw [pow_add, pow_add, Matrix.mul_apply]
  calc epsQ p ^ a * epsQ p ^ b ≤ (Qmat p ^ a) y z * (Qmat p ^ b) z x :=
        mul_le_mul h1 h2 (pow_nonneg he _) (Qmat_pow_nonneg hp0.le hp1.le a y z)
    _ ≤ ∑ w, (Qmat p ^ a) y w * (Qmat p ^ b) w x :=
        Finset.single_le_sum (f := fun w => (Qmat p ^ a) y w * (Qmat p ^ b) w x)
          (fun w _ => mul_nonneg (Qmat_pow_nonneg hp0.le hp1.le a y w)
            (Qmat_pow_nonneg hp0.le hp1.le b w x)) (Finset.mem_univ z)

theorem QLb_edge {p : ℝ} {y x : Fin 5} (h : epsQ p ≤ Qm p y x) :
    QLb p 1 y x := by
  unfold QLb
  rw [pow_one, pow_one]
  exact h

theorem eps_le_one (p : ℝ) : epsQ p ≤ 1 := by
  unfold epsQ
  rcases le_total p (1 - p) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith [min_le_left p (1 - p), min_le_right p (1 - p)]

theorem QLb_01 {p : ℝ} : QLb p 1 0 1 := QLb_edge (eps_le_one p)
theorem QLb_12 {p : ℝ} : QLb p 1 1 2 := QLb_edge (eps_le_one p)
theorem QLb_23 {p : ℝ} : QLb p 1 2 3 := QLb_edge (eps_le_one p)
theorem QLb_31 {p : ℝ} : QLb p 1 3 1 :=
  QLb_edge (min_le_left p (1 - p))
theorem QLb_34 {p : ℝ} : QLb p 1 3 4 :=
  QLb_edge (min_le_right p (1 - p))
theorem QLb_40 {p : ℝ} : QLb p 1 4 0 := QLb_edge (eps_le_one p)

theorem QLb_refl {p : ℝ} (y : Fin 5) : QLb p 0 y y := by
  unfold QLb
  rw [pow_zero, pow_zero, Matrix.one_apply_eq]

/-- Steps from `y` to `x₃`. -/
def dTo3 : Fin 5 → ℕ
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 4

/-- Steps from `x₃` to `x`. -/
def eFrom3 : Fin 5 → ℕ
  | 0 => 2
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 1

theorem QLb_to3 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (y : Fin 5) : QLb p (dTo3 y) y 3 := by
  fin_cases y
  · exact QLb_chain hp0 hp1 (QLb_chain hp0 hp1 (QLb_01 (p := p)) (QLb_12 (p := p))) (QLb_23 (p := p))
  · exact QLb_chain hp0 hp1 (QLb_12 (p := p)) (QLb_23 (p := p))
  · exact QLb_23
  · exact QLb_refl 3
  · exact QLb_chain hp0 hp1 (QLb_chain hp0 hp1 (QLb_chain hp0 hp1 (QLb_40 (p := p))
      (QLb_01 (p := p))) (QLb_12 (p := p))) (QLb_23 (p := p))

theorem QLb_from3 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : Fin 5) : QLb p (eFrom3 x) 3 x := by
  fin_cases x
  · exact QLb_chain hp0 hp1 (QLb_34 (p := p)) (QLb_40 (p := p))
  · exact QLb_31
  · exact QLb_chain hp0 hp1 (QLb_31 (p := p)) (QLb_12 (p := p))
  · exact QLb_refl 3
  · exact QLb_34

theorem QLb_c3 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : QLb p 3 3 3 :=
  QLb_chain hp0 hp1 (QLb_chain hp0 hp1 (QLb_31 (p := p)) (QLb_12 (p := p))) (QLb_23 (p := p))

theorem QLb_c5 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : QLb p 5 3 3 :=
  QLb_chain hp0 hp1 (QLb_chain hp0 hp1 (QLb_34 (p := p)) (QLb_40 (p := p))) (QLb_to3 hp0 hp1 0)

theorem QLb_mid {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) (h1 : 10 ≤ m) (h2 : m ≤ 16) :
    QLb p m 3 3 := by
  have c3 := QLb_c3 hp0 hp1
  have c5 := QLb_c5 hp0 hp1
  interval_cases m
  · exact QLb_chain hp0 hp1 c5 c5
  · exact QLb_chain hp0 hp1 (QLb_chain hp0 hp1 c3 c3) c5
  · exact QLb_chain hp0 hp1 (QLb_chain hp0 hp1 c3 c3) (QLb_chain hp0 hp1 c3 c3)
  · exact QLb_chain hp0 hp1 (QLb_chain hp0 hp1 c3 c5) c5
  · exact QLb_chain hp0 hp1 (QLb_chain hp0 hp1 (QLb_chain hp0 hp1 c3 c3) c3) c5
  · exact QLb_chain hp0 hp1 (QLb_chain hp0 hp1 c5 c5) c5
  · exact QLb_chain hp0 hp1 (QLb_chain hp0 hp1 c3 c3) (QLb_chain hp0 hp1 c5 c5)

/-- **The Doeblin minorization**: `Q¹⁶(y,x) ≥ min(p,1−p)¹⁶` at every pair of states. -/
theorem QLb_16 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (y x : Fin 5) : QLb p 16 y x := by
  have hr : ∀ y x : Fin 5, 10 ≤ 16 - dTo3 y - eFrom3 x ∧ 16 - dTo3 y - eFrom3 x ≤ 16
      ∧ dTo3 y + (16 - dTo3 y - eFrom3 x) + eFrom3 x = 16 := by decide
  obtain ⟨h1, h2, h3⟩ := hr y x
  have h := QLb_chain hp0 hp1 (QLb_chain hp0 hp1 (QLb_to3 hp0 hp1 y) (QLb_mid hp0 hp1 _ h1 h2))
    (QLb_from3 hp0 hp1 x)
  rwa [h3] at h

/-- **The variance inequality**: a row-stochastic `R ≥ 0` with `λR = λ` and `R(y,x) ≥ δλ(x)`
contracts the `λ`-mean-zero functions in `L²(λ)` by `1 − δ`. -/
theorem variance_contract {R : Fin 5 → Fin 5 → ℝ} {l h : Fin 5 → ℝ} {δ : ℝ}
    (hrow : ∀ y, ∑ x, R y x = 1) (hinv : ∀ x, ∑ y, l y * R y x = l x) (hl : ∀ x, 0 ≤ l x)
    (hlsum : ∑ x, l x = 1) (hδ0 : 0 ≤ δ) (hmin : ∀ y x, δ * l x ≤ R y x)
    (hmean : ∑ x, l x * h x = 0) :
    ∑ y, l y * (∑ x, R y x * h x) ^ 2 ≤ (1 - δ) * ∑ x, l x * h x ^ 2 := by
  set S := ∑ x, l x * h x ^ 2 with hS
  have key : ∀ y, (∑ x, R y x * h x) ^ 2 ≤ ∑ x, R y x * h x ^ 2 - δ * S := by
    intro y
    set m := ∑ x, R y x * h x with hm
    have hpos : 0 ≤ ∑ x, (R y x - δ * l x) * (h x - m) ^ 2 :=
      Finset.sum_nonneg fun x _ => mul_nonneg (by linarith [hmin y x]) (sq_nonneg _)
    have hexp : ∑ x, (R y x - δ * l x) * (h x - m) ^ 2
        = ∑ x, R y x * h x ^ 2 - 2 * m * ∑ x, R y x * h x + m ^ 2 * ∑ x, R y x
          - δ * (S - 2 * m * ∑ x, l x * h x + m ^ 2 * ∑ x, l x) := by
      simp only [hS, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hexp, ← hm, hrow y, hmean, hlsum] at hpos
    have hδ : 0 ≤ δ * m ^ 2 := mul_nonneg hδ0 (sq_nonneg m)
    linarith
  calc ∑ y, l y * (∑ x, R y x * h x) ^ 2 ≤ ∑ y, l y * (∑ x, R y x * h x ^ 2 - δ * S) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (key y) (hl y)
    _ = ∑ x, (∑ y, l y * R y x) * h x ^ 2 - δ * S * ∑ y, l y := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        congr 1
        · exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
        · exact Finset.sum_congr rfl fun y _ => by ring
    _ = (1 - δ) * S := by
        simp only [hinv, hlsum]
        rw [hS]
        ring

theorem lam_sum (p : ℝ) (hp1 : p < 1) : ∑ x, lam p x = 1 := by
  have hd : (5 : ℝ) - 2 * p ≠ 0 := ne_of_gt (by linarith)
  simp only [Fin.sum_univ_five, lam]
  rw [← add_div, ← add_div, ← add_div, ← add_div, div_eq_one_iff_eq hd]
  ring

/-- `∑ λ(a − m)² = ∑ λa² − m²` for `m = ∑ λa`, `λ` a probability. -/
theorem sum_sq_sub_mean {l a : Fin 5 → ℝ} (hlsum : ∑ x, l x = 1) :
    ∑ x, l x * (a x - ∑ z, l z * a z) ^ 2 = ∑ x, l x * a x ^ 2 - (∑ z, l z * a z) ^ 2 := by
  set m := ∑ z, l z * a z with hm
  have h : ∀ x, l x * (a x - m) ^ 2 = l x * a x ^ 2 - 2 * m * (l x * a x) + m ^ 2 * l x :=
    fun x => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hm, hlsum]
  ring

/-- `‖Π‖ ≤ 1` on `L²(λ)`. -/
theorem meanOp_norm_apply_le {p : ℝ} (hp1 : p < 1) (w : EuclideanSpace ℝ (Fin 5)) :
    ‖meanOp (lam p) w‖ ≤ ‖w‖ := by
  obtain ⟨a, rfl⟩ := exists_wtL2 (lam_pos hp1) w
  rw [meanOp_wtL2 (lam_pos hp1)]
  have hnn : ∀ x, 0 ≤ lam p x := fun x => (lam_pos hp1 x).le
  have h1 : ‖wtL2 (lam p) (fun _ => Graph.meanL2 (lam p) a)‖ ^ 2 = Graph.meanL2 (lam p) a ^ 2 := by
    rw [norm_wtL2_sq hp1.le]
    simp only [Graph.ipL2, ← Finset.sum_mul, lam_sum p hp1]
    ring
  have h2 : Graph.meanL2 (lam p) a ^ 2 ≤ ‖wtL2 (lam p) a‖ ^ 2 := by
    rw [norm_wtL2_sq hp1.le]
    have h := sum_sq_sub_mean (a := a) (lam_sum p hp1)
    have h0 : 0 ≤ ∑ x, lam p x * (a x - ∑ z, lam p z * a z) ^ 2 :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hnn x) (sq_nonneg _)
    simp only [Graph.meanL2, Graph.ipL2]
    have e : ∀ x, lam p x * (a x * a x) = lam p x * a x ^ 2 := fun x => by ring
    simp only [e]
    linarith
  rw [← h1] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- **The `L²(λ)` Doeblin step**: `‖P¹⁶ − Π‖ ≤ √(1 − min(p,1−p)¹⁶)` on `(0,1)`. -/
theorem norm_pow16_sub_meanOp_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ‖densOp (lam p) (kern p) ^ 16 - meanOp (lam p)‖ ≤ Real.sqrt (1 - epsQ p ^ 16) := by
  have he0 : 0 ≤ epsQ p := le_min hp0.le (by linarith)
  have hδ1 : epsQ p ^ 16 ≤ 1 := pow_le_one₀ he0 (eps_le_one p)
  have hlsum := lam_sum p hp1
  have hnn : ∀ x, 0 ≤ lam p x := fun x => (lam_pos hp1 x).le
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun w => ?_
  obtain ⟨a, rfl⟩ := exists_wtL2 (lam_pos hp1) w
  set m0 := Graph.meanL2 (lam p) a with hm0
  set h : Fin 5 → ℝ := fun x => a x - m0 with hh
  have happ : (densOp (lam p) (kern p) ^ 16 - meanOp (lam p)) (wtL2 (lam p) a)
      = wtL2 (lam p) (fun y => ∑ x, (Qmat p ^ 16) y x * h x) := by
    rw [sub_apply, densOp_pow_wtL2 hp1, meanOp_wtL2 (lam_pos hp1), ← wtL2_sub,
      shiftK_iterate_eq]
    congr 1
    funext y
    simp only [Matrix.mulVec, dotProduct, hh, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Qmat_pow_row, one_mul]
    rw [hm0]
  have hvar := variance_contract (R := fun y x => (Qmat p ^ 16) y x) (l := lam p) (h := h)
    (δ := epsQ p ^ 16) (fun y => Qmat_pow_row p 16 y) (fun x => Qmat_pow_inv p 16 x) hnn hlsum
    (pow_nonneg he0 _)
    (fun y x => by
      have hq : epsQ p ^ 16 ≤ (Qmat p ^ 16) y x := QLb_16 hp0 hp1 y x
      have hlx : lam p x ≤ 1 := by
        rw [← hlsum]
        exact Finset.single_le_sum (fun z _ => hnn z) (Finset.mem_univ x)
      nlinarith [pow_nonneg he0 16])
    (by
      simp only [hh, hm0, Graph.meanL2, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlsum,
        one_mul, sub_self])
  have hhsq : ∑ x, lam p x * h x ^ 2 ≤ ‖wtL2 (lam p) a‖ ^ 2 := by
    rw [norm_wtL2_sq hp1.le]
    have h1 := sum_sq_sub_mean (a := a) hlsum
    simp only [hh, hm0, Graph.meanL2, Graph.ipL2]
    have e : ∀ x, lam p x * (a x * a x) = lam p x * a x ^ 2 := fun x => by ring
    simp only [e]
    nlinarith [sq_nonneg (∑ z, lam p z * a z)]
  have hsq : ‖(densOp (lam p) (kern p) ^ 16 - meanOp (lam p)) (wtL2 (lam p) a)‖ ^ 2
      ≤ (1 - epsQ p ^ 16) * ‖wtL2 (lam p) a‖ ^ 2 := by
    rw [happ, norm_wtL2_sq hp1.le]
    simp only [Graph.ipL2]
    have e : ∀ y, lam p y * ((∑ x, (Qmat p ^ 16) y x * h x) * (∑ x, (Qmat p ^ 16) y x * h x))
        = lam p y * (∑ x, (Qmat p ^ 16) y x * h x) ^ 2 := fun y => by ring
    simp only [e]
    calc _ ≤ (1 - epsQ p ^ 16) * ∑ x, lam p x * h x ^ 2 := hvar
      _ ≤ _ := mul_le_mul_of_nonneg_left hhsq (by linarith)
  have hle : ‖(densOp (lam p) (kern p) ^ 16 - meanOp (lam p)) (wtL2 (lam p) a)‖
      ≤ Real.sqrt ((1 - epsQ p ^ 16) * ‖wtL2 (lam p) a‖ ^ 2) :=
    (Real.le_sqrt (norm_nonneg _) (by have := sq_nonneg ‖wtL2 (lam p) a‖; nlinarith)).mpr hsq
  rwa [Real.sqrt_mul (by linarith), Real.sqrt_sq (norm_nonneg _)] at hle

theorem densOp_pow_mul_meanOp {p : ℝ} (hp1 : p < 1) (n : ℕ) :
    densOp (lam p) (kern p) ^ n * meanOp (lam p) = meanOp (lam p) := by
  induction n with
  | zero => rw [pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ, mul_assoc, densOp_mul_meanOp (lam_isInvariant hp1.le) (lam_pos hp1), ih]

theorem meanOp_mul_densOp_pow {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (n : ℕ) :
    meanOp (lam p) * densOp (lam p) (kern p) ^ n = meanOp (lam p) := by
  induction n with
  | zero => rw [pow_zero, mul_one]
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, meanOp_mul_densOp (kern_isMarkov hp0 hp1.le) (lam_pos hp1), ih]

theorem meanOp_mul_self {p : ℝ} (hp1 : p < 1) : meanOp (lam p) * meanOp (lam p) = meanOp (lam p) :=
  ContinuousLinearMap.ext fun u => meanOp_idem (lam_pos hp1) (lam_sum p hp1) u

/-- `Pⁿ⁺¹⁶ − Π = (P¹⁶ − Π)(Pⁿ − Π)`, hence `β̂_{n+16} ≤ ‖P¹⁶ − Π‖ β̂_n`. -/
theorem betaCyc_add16_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    betaCyc p (n + 16) ≤ ‖densOp (lam p) (kern p) ^ 16 - meanOp (lam p)‖ * betaCyc p n := by
  have hid : densOp (lam p) (kern p) ^ (n + 16) - meanOp (lam p)
      = (densOp (lam p) (kern p) ^ 16 - meanOp (lam p))
        * (densOp (lam p) (kern p) ^ n - meanOp (lam p)) := by
    rw [sub_mul, mul_sub, mul_sub, densOp_pow_mul_meanOp hp1, meanOp_mul_densOp_pow hp0.le hp1,
      meanOp_mul_self hp1, add_comm n 16, pow_add]
    abel
  unfold betaCyc Core.Mixing.beta
  rw [hid]
  exact norm_mul_le _ _

theorem betaCyc_le_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (n : ℕ) : betaCyc p n ≤ 2 := by
  unfold betaCyc Core.Mixing.beta
  have h1 : ‖densOp (lam p) (kern p) ^ n‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      rw [one_mul]; exact norm_pow_apply_le (densOp_contraction hp0 hp1) n w
  have h2 : ‖meanOp (lam p)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      rw [one_mul]; exact meanOp_norm_apply_le hp1 w
  calc _ ≤ ‖densOp (lam p) (kern p) ^ n‖ + ‖meanOp (lam p)‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

/-- The geometric rate `r(p) := 1 − min(p,1−p)¹⁶/32`. -/
noncomputable def rateQ (p : ℝ) : ℝ := 1 - epsQ p ^ 16 / 32

/-- **`β̂_n ≤ (2/r¹⁵) rⁿ`** with the explicit `r = 1 − min(p,1−p)¹⁶/32 < 1`, on `(0,1)`. -/
theorem betaCyc_le_geometric {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    betaCyc p n ≤ 2 / rateQ p ^ 15 * rateQ p ^ n := by
  have he0 : 0 < epsQ p := lt_min hp0 (by linarith)
  have hδ0 : 0 < epsQ p ^ 16 := pow_pos he0 16
  have hδ1 : epsQ p ^ 16 ≤ 1 := pow_le_one₀ he0.le (eps_le_one p)
  have hr0 : 0 < rateQ p := by unfold rateQ; linarith
  have hr1 : rateQ p ≤ 1 := by unfold rateQ; linarith
  -- `‖P¹⁶ − Π‖ ≤ r¹⁶`
  have hq : ‖densOp (lam p) (kern p) ^ 16 - meanOp (lam p)‖ ≤ rateQ p ^ 16 := by
    refine (norm_pow16_sub_meanOp_le hp0 hp1).trans ?_
    have hs : Real.sqrt (1 - epsQ p ^ 16) ≤ 1 - epsQ p ^ 16 / 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hb := one_add_mul_le_pow (a := -(epsQ p ^ 16 / 32)) (by linarith) 16
    have : 1 - epsQ p ^ 16 / 2 ≤ rateQ p ^ 16 := by
      unfold rateQ
      push_cast at hb
      linarith
    linarith
  have hqn : 0 ≤ ‖densOp (lam p) (kern p) ^ 16 - meanOp (lam p)‖ := norm_nonneg _
  have hblock : ∀ k j : ℕ, betaCyc p (16 * k + j) ≤ 2 * (rateQ p ^ 16) ^ k := by
    intro k j
    induction k with
    | zero => rw [mul_zero, zero_add, pow_zero, mul_one]; exact betaCyc_le_two hp0.le hp1 j
    | succ k ih =>
      have e : 16 * (k + 1) + j = (16 * k + j) + 16 := by ring
      rw [e]
      calc betaCyc p (16 * k + j + 16)
          ≤ ‖densOp (lam p) (kern p) ^ 16 - meanOp (lam p)‖ * betaCyc p (16 * k + j) :=
            betaCyc_add16_le hp0 hp1 _
        _ ≤ rateQ p ^ 16 * (2 * (rateQ p ^ 16) ^ k) :=
            mul_le_mul hq ih (betaCyc_nonneg p _) (pow_nonneg hr0.le _)
        _ = 2 * (rateQ p ^ 16) ^ (k + 1) := by ring
  have hn := hblock (n / 16) (n % 16)
  rw [Nat.div_add_mod] at hn
  have hexp : rateQ p ^ (16 * (n / 16) + 15) ≤ rateQ p ^ n :=
    pow_le_pow_of_le_one hr0.le hr1 (by omega)
  have hr15 : 0 < rateQ p ^ 15 := pow_pos hr0 15
  calc betaCyc p n ≤ 2 * (rateQ p ^ 16) ^ (n / 16) := hn
    _ = 2 / rateQ p ^ 15 * rateQ p ^ (16 * (n / 16) + 15) := by
        rw [pow_add, ← pow_mul]; field_simp
    _ ≤ 2 / rateQ p ^ 15 * rateQ p ^ n :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Summable mixing on `(0,1)`**: the paper's `B̂ = ∑ₙ β̂ₙ` is finite at every `p ∈ (0,1)`. -/
theorem betaCyc_summable {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Summable (betaCyc p) := by
  have he0 : 0 < epsQ p := lt_min hp0 (by linarith)
  have hr0 : 0 ≤ rateQ p := by
    unfold rateQ; have := pow_le_one₀ he0.le (eps_le_one p) (n := 16); linarith
  have hr1 : rateQ p < 1 := by unfold rateQ; have := pow_pos he0 16; linarith
  exact Summable.of_nonneg_of_le (betaCyc_nonneg p) (betaCyc_le_geometric hp0 hp1)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left _)

/-- **`Core.Mixing` holds on the remark's chain at every `p ∈ (0,1)`**: the hypothesis bundle of
`lem:sigma_mixing` and of `LocalConvergenceMixing`, inhabited on a chain whose density action is
not a projection. -/
theorem mixing_cycle {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Core.Mixing (densOp (lam p) (kern p)) (meanOp (lam p)) where
  proj_left := meanOp_mul_densOp (kern_isMarkov hp0.le hp1.le) (lam_pos hp1)
  proj_right := densOp_mul_meanOp (lam_isInvariant hp1.le) (lam_pos hp1)
  summable := betaCyc_summable hp0 hp1

end MixingSummable

section Rates

open CycleExample Balance

/-- **`rem:cycle_no_stalemate`, `ϱ_σ → 0` as `p → 1⁻`**: the rate of `prop:morozov_rate`*(3)*,
`ϱ_σ = g''(1)w_min/B̂_σ² = g''(1)w_min λ_min/σ_*²`, in both library forms, for `g''(1) ≥ 0` and
any `w_min(p)` eventually in `[0, W]`. -/
theorem rhoSigma_cycle_tendsto {g2 W : ℝ} (hg2 : 0 ≤ g2) {wmin : ℝ → ℝ}
    (hw : ∀ᶠ p in 𝓝[<] (1 : ℝ), 0 ≤ wmin p ∧ wmin p ≤ W) :
    Tendsto (fun p => rhoL g2 (wmin p) (BhatSigma cyc (hitExp p) (lam p))) (𝓝[<] 1) (𝓝 0)
      ∧ Tendsto (fun p => rhoSigma g2 (wmin p) (Graph.minOver cyc (lam p))
          (Graph.sigmaStar cyc (hitExp p))) (𝓝[<] 1) (𝓝 0) := by
  have hbd : Tendsto (fun p => rhoL g2 W (BhatSigma cyc (hitExp p) (lam p))) (𝓝[<] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp bhatSigma_cycle_tendsto)
  have h1 : Tendsto (fun p => rhoL g2 (wmin p) (BhatSigma cyc (hitExp p) (lam p))) (𝓝[<] 1)
      (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hbd
    · filter_upwards [hw] with p hp
      exact div_nonneg (mul_nonneg hg2 hp.1) (sq_nonneg _)
    · filter_upwards [hw] with p hp
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp.2 hg2) (sq_nonneg _)
  refine ⟨h1, h1.congr' ?_⟩
  filter_upwards [eventually_mem_Ioo_zero_one] with p hp
  have hmin : 0 < Graph.minOver cyc (lam p) := by
    rw [cycle_minOver_lam hp.1 hp.2]
    exact div_pos (by linarith [hp.2]) (by linarith [hp.2])
  exact rhoL_eq_rhoSigma hmin

/-- **`rem:cycle_no_stalemate`, the constant of `cor:global_lojasiewicz` tends to `0` as `p → 1⁻`**:
`κ = w_min λ_min^{1/2}/(‖u₀‖_{L²(λ)} ‖w‖_∞ M)`, `M = max(1, √(𝓛(μ₀)/(w_min λ_min)))`, for families
`w_min(p) ≤ ‖w‖_∞(p)`, `u₀(p)`, `𝓛(μ₀)(p)` whose only constraint is that `‖u₀(p)‖_{L²(λ_p)}` stays
eventually above some `n₀ > 0`. -/
theorem kappa_cycle_tendsto_gen {wmin wsup L0 : ℝ → ℝ} {u0 : ℝ → Fin 5 → ℝ} {n0 : ℝ}
    (hn0 : 0 < n0)
    (hev : ∀ᶠ p in 𝓝[<] (1 : ℝ), 0 < wmin p ∧ wmin p ≤ wsup p ∧ n0 ≤ Graph.nrmL2 (lam p) (u0 p)) :
    Tendsto (fun p => wmin p * Real.sqrt (Graph.minOver cyc (lam p))
        / (Graph.nrmL2 (lam p) (u0 p) * wsup p
          * max 1 (Real.sqrt (L0 p / (wmin p * Graph.minOver cyc (lam p))))))
      (𝓝[<] 1) (𝓝 0) := by
  have hbound : Tendsto (fun p : ℝ => Real.sqrt (1 - p) / n0) (𝓝[<] 1) (𝓝 0) := by
    have hc : Continuous fun p : ℝ => Real.sqrt (1 - p) / n0 :=
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).div_const _
    have h := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa only [sub_self, Real.sqrt_zero, zero_div] using h
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_mem_Ioo_zero_one, hev] with p hp hq
    obtain ⟨hw0, hws, hn⟩ := hq
    have hN : 0 < Graph.nrmL2 (lam p) (u0 p) := hn0.trans_le hn
    have hM : (1 : ℝ) ≤ max 1 (Real.sqrt (L0 p / (wmin p * Graph.minOver cyc (lam p)))) :=
      le_max_left _ _
    have hs : 0 ≤ Real.sqrt (Graph.minOver cyc (lam p)) := Real.sqrt_nonneg _
    have hwsup : 0 < wsup p := hw0.trans_le hws
    positivity
  · filter_upwards [eventually_mem_Ioo_zero_one, hev] with p hp hq
    obtain ⟨hp0, hp1⟩ := hp
    obtain ⟨hw0, hws, hn⟩ := hq
    have hd : (0 : ℝ) < 5 - 2 * p := by linarith
    have hmin : Graph.minOver cyc (lam p) = (1 - p) / (5 - 2 * p) := cycle_minOver_lam hp0 hp1
    set m := Graph.minOver cyc (lam p) with hmdef
    set N := Graph.nrmL2 (lam p) (u0 p) with hNdef
    set Mx := max 1 (Real.sqrt (L0 p / (wmin p * m))) with hMx
    have hM1 : (1 : ℝ) ≤ Mx := le_max_left _ _
    have hwsup : 0 < wsup p := hw0.trans_le hws
    have hNpos : 0 < N := hn0.trans_le hn
    have hsm : Real.sqrt m ≤ Real.sqrt (1 - p) := by
      refine Real.sqrt_le_sqrt ?_
      rw [hmin, div_le_iff₀ hd]
      nlinarith
    have hstep1 : wmin p * Real.sqrt m / (N * wsup p * Mx) ≤ Real.sqrt m / N := by
      have hden : N * wmin p ≤ N * wsup p * Mx := by
        have : wmin p ≤ wsup p * Mx := by nlinarith
        nlinarith
      calc wmin p * Real.sqrt m / (N * wsup p * Mx) ≤ wmin p * Real.sqrt m / (N * wmin p) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = Real.sqrt m / N := by field_simp
    have hstep2 : Real.sqrt m / N ≤ Real.sqrt (1 - p) / n0 :=
      div_le_div₀ (Real.sqrt_nonneg _) hsm hn0 hn
    exact hstep1.trans hstep2

/-- **`κ → 0` at a fixed positive `u₀`** and fixed `0 < w_min ≤ ‖w‖_∞`: `‖u₀‖_{L²(λ_p)} ≥ u₀(x₁)/√5`. -/
theorem kappa_cycle_tendsto {wmin wsup : ℝ} (hwmin : 0 < wmin) (hws : wmin ≤ wsup)
    {u0 : Fin 5 → ℝ} (hu0 : ∀ x, 0 < u0 x) (L0 : ℝ → ℝ) :
    Tendsto (fun p => wmin * Real.sqrt (Graph.minOver cyc (lam p))
        / (Graph.nrmL2 (lam p) u0 * wsup
          * max 1 (Real.sqrt (L0 p / (wmin * Graph.minOver cyc (lam p))))))
      (𝓝[<] 1) (𝓝 0) := by
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  refine kappa_cycle_tendsto_gen (wmin := fun _ => wmin) (wsup := fun _ => wsup)
    (u0 := fun _ => u0) (L0 := L0) (div_pos (hu0 1) h5) ?_
  filter_upwards [eventually_mem_Ioo_zero_one] with p hp
  obtain ⟨hp0, hp1⟩ := hp
  have hd : (0 : ℝ) < 5 - 2 * p := by linarith
  refine ⟨hwmin, hws, ?_⟩
  have hip : lam p 1 * (u0 1 * u0 1) ≤ Graph.ipL2 (lam p) u0 u0 :=
    Finset.single_le_sum (f := fun x => lam p x * (u0 x * u0 x))
      (fun x _ => mul_nonneg (lam_pos hp1 x).le (mul_self_nonneg _)) (Finset.mem_univ 1)
  have hlam1 : u0 1 ^ 2 / 5 ≤ lam p 1 * (u0 1 * u0 1) := by
    show u0 1 ^ 2 / 5 ≤ 1 / (5 - 2 * p) * (u0 1 * u0 1)
    rw [one_div_mul_eq_div, sq]
    exact div_le_div_of_nonneg_left (mul_self_nonneg _) hd (by linarith)
  rw [Graph.nrmL2, div_le_iff₀ h5,
    ← Real.sqrt_mul (Graph.ipL2_self_nonneg (fun x => (lam_pos hp1 x).le) u0),
    ← Real.sqrt_sq (hu0 1).le]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **`κ → 0` at a fixed initial measure `μ₀ = u₀λ_p`**, `μ₀ > 0` fixed: `u₀(p) = μ₀/λ_p` and
`‖u₀(p)‖_{L²(λ_p)} ≥ μ₀(x₁)√3`. -/
theorem kappa_cycle_tendsto_fixed_measure {wmin wsup : ℝ} (hwmin : 0 < wmin) (hws : wmin ≤ wsup)
    {mu0 : Fin 5 → ℝ} (hmu0 : ∀ x, 0 < mu0 x) (L0 : ℝ → ℝ) :
    Tendsto (fun p => wmin * Real.sqrt (Graph.minOver cyc (lam p))
        / (Graph.nrmL2 (lam p) (fun x => mu0 x / lam p x) * wsup
          * max 1 (Real.sqrt (L0 p / (wmin * Graph.minOver cyc (lam p))))))
      (𝓝[<] 1) (𝓝 0) := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine kappa_cycle_tendsto_gen (wmin := fun _ => wmin) (wsup := fun _ => wsup)
    (u0 := fun p x => mu0 x / lam p x) (L0 := L0) (mul_pos (hmu0 1) h3) ?_
  filter_upwards [eventually_mem_Ioo_zero_one] with p hp
  obtain ⟨hp0, hp1⟩ := hp
  have hd : (0 : ℝ) < 5 - 2 * p := by linarith
  refine ⟨hwmin, hws, ?_⟩
  have hl1 : lam p 1 = 1 / (5 - 2 * p) := rfl
  have hip : lam p 1 * (mu0 1 / lam p 1 * (mu0 1 / lam p 1))
      ≤ Graph.ipL2 (lam p) (fun x => mu0 x / lam p x) (fun x => mu0 x / lam p x) :=
    Finset.single_le_sum (f := fun x => lam p x * (mu0 x / lam p x * (mu0 x / lam p x)))
      (fun x _ => mul_nonneg (lam_pos hp1 x).le (mul_self_nonneg _)) (Finset.mem_univ 1)
  have hval : lam p 1 * (mu0 1 / lam p 1 * (mu0 1 / lam p 1)) = mu0 1 ^ 2 * (5 - 2 * p) := by
    rw [hl1]; field_simp
  have hge : (mu0 1 * Real.sqrt 3) ^ 2 ≤ mu0 1 ^ 2 * (5 - 2 * p) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [sq_nonneg (mu0 1)]
  rw [Graph.nrmL2, ← Real.sqrt_sq (mul_pos (hmu0 1) h3).le]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **At every `p ∈ (0,1)` the mixing sum `B̂ = ∑ₙ β̂ₙ` is a coercivity constant `≥ 1`** — the
hypothesis `eq:coercivity` of `theo:db_stable_frozen_full` — so `ϱ = g''(1)w_min/B̂²` is that
theorem's rate. -/
theorem mixing_B_coercive {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    1 ≤ Core.Mixing.B (densOp (lam p) (kern p)) (meanOp (lam p))
      ∧ ∀ f : Fin 5 → ℝ, Graph.nrmL2 (lam p) (perpL2 (lam p) f)
          ≤ Core.Mixing.B (densOp (lam p) (kern p)) (meanOp (lam p))
            * Graph.nrmL2 (lam p) (Aop (kern p) (lam p) f) :=
  ⟨one_le_B_densOp (lam_pos hp1) (mixing_cycle hp0 hp1),
    mixing_coercivity_finite (lam_isInvariant hp1.le) (lam_pos hp1) (mixing_cycle hp0 hp1)⟩

/-- **`rem:cycle_no_stalemate`, "the mixing sum tends to `+∞`"**, in `ℝ`: the (finite) mixing sum
`B̂(p) = ∑ₙ β̂ₙ(p)` tends to `+∞` as `p → 1⁻`. -/
theorem mixing_B_tendsto_atTop :
    Tendsto (fun p : ℝ => Core.Mixing.B (densOp (lam p) (kern p)) (meanOp (lam p))) (𝓝[<] 1)
      atTop := by
  refine tendsto_atTop.2 fun C => ?_
  filter_upwards [mixing_sum_eventually_gt C, eventually_mem_Ioo_zero_one] with p hp hp01
  obtain ⟨N, hN⟩ := hp
  exact hN.le.trans ((betaCyc_summable hp01.1 hp01.2).sum_le_tsum (Finset.range N)
    fun n _ => betaCyc_nonneg p n)

/-- **`rem:cycle_no_stalemate`, "the rate `ϱ` of `theo:db_stable_frozen_full` read at the mixing sum
tends to `0`"**, in `ℝ` at the genuine (summable) mixing sum: `g''(1) ≥ 0`, `w_min(p)` eventually in
`[0, W]`. -/
theorem rho_mixing_tendsto {g2 W : ℝ} (hg2 : 0 ≤ g2) {wmin : ℝ → ℝ}
    (hw : ∀ᶠ p in 𝓝[<] (1 : ℝ), 0 ≤ wmin p ∧ wmin p ≤ W) :
    Tendsto (fun p => rhoL g2 (wmin p) (Core.Mixing.B (densOp (lam p) (kern p)) (meanOp (lam p))))
      (𝓝[<] 1) (𝓝 0) := by
  have hbd : Tendsto (fun p => rhoL g2 W (Core.Mixing.B (densOp (lam p) (kern p)) (meanOp (lam p))))
      (𝓝[<] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp mixing_B_tendsto_atTop)
  refine squeeze_zero' ?_ ?_ hbd
  · filter_upwards [hw] with p hp
    exact div_nonneg (mul_nonneg hg2 hp.1) (sq_nonneg _)
  · filter_upwards [hw] with p hp
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp.2 hg2) (sq_nonneg _)

end Rates

/-! ## The rescaled flow for `(x − 1)²`, and inhabitation -/

section Instances

open CycleExample Balance

/-- **`rem:cycle_no_stalemate`, the rescaled flow, on the five-vertex cycle, for `g = (x − 1)²`** —
the other generator `prop:no_distant_equilibrium`*(3)* names. -/
theorem cycle_rescaled_flow_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {wf : Fin 5 → ℝ} {wmin : ℝ}
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) {u0 : Fin 5 → ℝ} (hu0 : ∀ x, 0 < u0 x)
    {α : ℝ} (hα : 0 < α) :
    (∃ u : ℝ → Fin 5 → ℝ, u 0 = u0
      ∧ IsGradientFlow (pol hp0 hp1).phat (lam p) (fun x => lam p x * wf x) (fun x => 2 * (x - 1)) u
      ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
    ∧ (∃ v : ℝ → Fin 5 → ℝ, v 0 = (fun x => α * u0 x)
      ∧ IsGradientFlow (pol hp0 hp1).phat (lam p) (fun x => lam p x * wf x) (fun x => 2 * (x - 1)) v
      ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x)
    ∧ ∀ u v : ℝ → Fin 5 → ℝ, u 0 = u0 → v 0 = (fun x => α * u0 x) →
      IsGradientFlow (pol hp0 hp1).phat (lam p) (fun x => lam p x * wf x) (fun x => 2 * (x - 1)) u →
      IsGradientFlow (pol hp0 hp1).phat (lam p) (fun x => lam p x * wf x) (fun x => 2 * (x - 1)) v →
      (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x) → (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) →
      (∀ t : ℝ, 0 ≤ t → v t = fun x => α * u (t / α ^ 2) x)
        ∧ ∀ δ : ℝ, sInf (entryTimes (pol hp0 hp1).phat (lam p) v δ)
            = α ^ 2 * sInf (entryTimes (pol hp0 hp1).phat (lam p) u δ) := by
  have hαu0 : ∀ x, 0 < α * u0 x := fun x => mul_pos hα (hu0 x)
  obtain ⟨u, hu0', hflow, hpos, -⟩ :=
    existsUnique_flow_sq_graph pathConnected (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1)
      hwmin hw hu0
  obtain ⟨v, hv0', hvflow, hvpos, -⟩ :=
    existsUnique_flow_sq_graph pathConnected (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1)
      hwmin hw hαu0
  refine ⟨⟨u, hu0', hflow, hpos⟩, ⟨v, hv0', hvflow, hvpos⟩, ?_⟩
  intro u v hu0 hv0 hu hv hupos hvpos
  have hinv := invariant_of_isInvProb (isInvProb hp0 hp1)
  obtain ⟨-, -, huniq⟩ := rescaled_flow hinv (pol hp0 hp1).phat_nonneg (lam_pos hp1)
    sqFlowGenerator.contDiffAt hu hupos hα
  have hvt := huniq v (by rw [hv0, hu0]) hv hvpos
  refine ⟨hvt, fun δ => ?_⟩
  have hset : entryTimes (pol hp0 hp1).phat (lam p) v δ
      = entryTimes (pol hp0 hp1).phat (lam p) (fun t x => α * u (t / α ^ 2) x) δ := by
    ext t
    simp only [entryTimes, Set.mem_setOf_eq]
    constructor
    · rintro ⟨ht, hr⟩; exact ⟨ht, by rwa [← hvt t ht]⟩
    · rintro ⟨ht, hr⟩; exact ⟨ht, by rwa [hvt t ht]⟩
  rw [hset]
  exact (entryTimes_scale hα δ).2

/-- **The start is at norm `α‖u₀‖`**: `‖αu₀‖_{L²(λ)} = α‖u₀‖_{L²(λ)}`, so "started at norm `Θ(M)`" is
`α = Θ(M)` in `cycle_rescaled_flow`. -/
theorem nrmL2_scale {V : Type*} [Fintype V] (lam u0 : V → ℝ) {α : ℝ} (hα : 0 < α) :
    Graph.nrmL2 lam (fun x => α * u0 x) = α * Graph.nrmL2 lam u0 := by
  rw [nrmL2_smul, abs_of_pos hα]

/-- **Inhabitation (kb 0025) of `cycle_rescaled_flow`'s flow hypotheses off balance**: at `p = 1/2`,
`w ≡ 1`, from the over-inflated `uInfl 2` (`r(s₀) = 2 ≠ 1`) and at `α = 3`, both flows exist and
the second is the first rescaled. -/
theorem cycle_rescaled_flow_check :
    ∃ u v : ℝ → Fin 5 → ℝ, u 0 = uInfl 2 ∧ v 0 = (fun x => 3 * uInfl 2 x)
      ∧ IsGradientFlow (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2))
          (fun x => lam (1 / 2) x * 1) logSqDeriv u
      ∧ IsGradientFlow (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2))
          (fun x => lam (1 / 2) x * 1) logSqDeriv v
      ∧ ¬ Balanced (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2)) (u 0)
      ∧ ∀ t : ℝ, 0 ≤ t → v t = fun x => 3 * u (t / 3 ^ 2) x := by
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 : ℝ) / 2 < 1 := by norm_num
  obtain ⟨⟨u, hu0, hu, hupos⟩, ⟨v, hv0, hv, hvpos⟩, hrel⟩ :=
    cycle_rescaled_flow hp0 hp1 (wf := fun _ => (1 : ℝ)) (wmin := 1) one_pos (fun _ => le_rfl)
      (uInfl_pos (M := 2) (by norm_num)) (α := 3) (by norm_num)
  refine ⟨u, v, hu0, hv0, hu, hv, ?_, (hrel u v hu0 hv0 hu hv hupos hvpos).1⟩
  rw [hu0, ← ratio_eq_one_iff_balanced
    (fun y => mul_pos (lam_pos hp1 y) (uInfl_pos (M := 2) (by norm_num) y))]
  intro h
  have h0 := h 0
  rw [ratio_src hp0 hp1 (by norm_num)] at h0
  norm_num at h0

end Instances


/-! ## The two labels, assembled -/

section Assembled

open CycleDivergence

/-- **`lem:cycle_counterexample`** (`proofs.tex:385–404`), items *(1)* and *(2)* on `𝒞_N`,
`N = M + 2`, for every integer `k ≥ 0`, every probability target `t` on `{x₁,…,x_N}` and every
training weight `ν`, the sampler clause excepted (SCOPE).

*(1)* `F_k` is non-negative, rides on the edges, satisfies `equ:FM_const` at every internal state
with initial flow `δ_{x₁}` and terminal flow `δ_{x₂}`, its normalized terminal flow is `δ_{x₂}`,
and `TV(δ_{x₂} ‖ t) = 1 − t(x₂)`.

*(2)* For `g` continuous at `1` with `g(1) = 0`: for `k ≥ 1` the denominator of `ρ_{F_k}` is
positive and `ρ_{F_k} ∈ (0,∞)` at every internal state, with `|ρ_{F_k} − 1| ≤ 1/k`, and
`𝓛(F_k) → 0` as `k → ∞`. -/
theorem cycle_counterexample (M : ℕ) :
    (∀ k : ℕ,
      (∀ u v, 0 ≤ Fk M k u v) ∧ (∀ u v, Fk M k u v ≠ 0 → (cycGraph M).Edge u v)
      ∧ (∀ i, Fk M k (srcC M) (xC M i) + ∑ j, Fk M k (xC M j) (xC M i)
          = Fk M k (xC M i) (snkC M) + ∑ j, Fk M k (xC M i) (xC M j))
      ∧ (∀ i, Fk M k (srcC M) (xC M i) = if i = 0 then 1 else 0)
      ∧ (∀ i, Fk M k (xC M i) (snkC M) = if i = 1 then 1 else 0)
      ∧ (∀ x, termLaw (cycGraph M) (Fk M k) x = if x = xC M 1 then 1 else 0)
      ∧ ∀ t : Fin (M + 2) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i = 1 →
          tvFin (termLaw (cycGraph M) (Fk M k)) (extT M t) = 1 - t 1)
    ∧ ∀ t : Fin (M + 2) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i = 1 →
      ∀ (nu : cycV M → ℝ) (g : ℝ → ℝ), g 1 = 0 → ContinuousAt g 1 →
        (∀ k : ℕ, 1 ≤ k → ∀ i,
          0 < extT M t (xC M i) + ∑ v ∈ (cycGraph M).internal, Fk M k (xC M i) v
          ∧ 0 < fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M i)
          ∧ |fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M i) - 1| ≤ 1 / k)
        ∧ Tendsto (fun k : ℕ => fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) atTop (𝓝 0) := by
  refine ⟨fun k => ⟨Fk_nonneg (Nat.cast_nonneg k), fun _ _ h => Fk_supp h, Fk_FM_const k,
    Fk_src_x k, Fk_x_snk k, termLaw_Fk k, fun t ht hsum => tvFin_termLaw_Fk_gen k ht hsum⟩,
    fun t ht hsum nu g hg1 hgc => ⟨fun k hk i => ?_, fmLossTarget_Fk_tendsto_zero_gen g hg1 hgc nu t⟩⟩
  obtain ⟨hden, hpos⟩ := den_pos_and_ratio_pos ht hk i
  obtain ⟨h1, h2, h3⟩ := abs_fmRatio_Fk_sub_one ht hsum hk i
  exact ⟨hden, hpos, by rw [h1]; exact h2.trans h3⟩

/-- **Inhabitation of `cycle_counterexample`'s hypotheses** at `N = 2`: the uniform target
`(1/2, 1/2)` is a probability, `g = (x − 1)²` is continuous at `1` and vanishes there, and the
loss of `F_k` against the uniform weight tends to `0` while its terminal law stays at total
variation `1/2`. -/
theorem cycle_counterexample_check :
    (∀ k : ℕ, tvFin (termLaw (cycGraph 0) (Fk 0 k)) (extT 0 fun _ => 1 / 2) = 1 / 2)
      ∧ Tendsto (fun k : ℕ => fmLossTarget (cycGraph 0) (fun x => (x - 1) ^ 2) (fun _ => 1)
          (extT 0 fun _ => 1 / 2) (Fk 0 k)) atTop (𝓝 0) := by
  have ht : ∀ i : Fin 2, (0 : ℝ) ≤ (fun _ => 1 / 2) i := fun _ => by norm_num
  have hsum : ∑ i : Fin 2, (fun _ => (1 : ℝ) / 2) i = 1 := by
    simp only [Fin.sum_univ_two]; norm_num
  obtain ⟨h1, h2⟩ := cycle_counterexample 0
  refine ⟨fun k => ?_, (h2 _ ht hsum _ _ (by norm_num) (by fun_prop)).2⟩
  rw [(h1 k).2.2.2.2.2.2 _ ht hsum]
  norm_num

end Assembled

section AssembledRemark

open CycleExample Balance

/-- On `(0,1)` the kernel `kern p` of `betaCyc` **is** the loop closure of the remark's frozen
policy, and `lam p` its unique invariant probability (`CycleExample.phat_eq`, `invProb_eq`). -/
theorem betaCyc_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    betaCyc p n = Core.Mixing.beta (densOp (lam p) (pol hp0 hp1).phat) (meanOp (lam p)) n := by
  rw [phat_eq]
  rfl

/-- **`rem:cycle_no_stalemate`, the closing sentence** (`proofs.tex:911`), as `p → 1⁻`: the expected
backward-trajectory length `σ̄ = 3/(1−p)`, the mixing sum `B̂ = ∑ₙ β̂ₙ` — finite on `(0,1)` and a
coercivity constant there — and `B̂_σ` tend to `+∞`, while the rate `ϱ = g''(1)w_min/B̂²` of
`theo:db_stable_frozen_full` read at the mixing sum, the rate `ϱ_σ = g''(1)w_min/B̂_σ²` and the
constant `κ` of `cor:global_lojasiewicz` tend to `0` (here `g''(1) ≥ 0`, `w_min`, `‖w‖_∞` and `u₀`
held fixed; `rho_mixing_tendsto`, `rhoSigma_cycle_tendsto` and `kappa_cycle_tendsto_gen` let them
move). -/
theorem cycle_no_stalemate_limits :
    Tendsto (fun p : ℝ => 3 / (1 - p)) (𝓝[<] 1) atTop
      ∧ (∀ p : ℝ, 0 < p → p < 1 → Summable (betaCyc p)
          ∧ 1 ≤ Core.Mixing.B (densOp (lam p) (kern p)) (meanOp (lam p)))
      ∧ Tendsto (fun p : ℝ => Core.Mixing.B (densOp (lam p) (kern p)) (meanOp (lam p))) (𝓝[<] 1)
          atTop
      ∧ Tendsto (fun p => BhatSigma cyc (hitExp p) (lam p)) (𝓝[<] 1) atTop
      ∧ (∀ g2 wmin : ℝ, 0 ≤ g2 → 0 ≤ wmin →
          Tendsto (fun p => rhoL g2 wmin (Core.Mixing.B (densOp (lam p) (kern p)) (meanOp (lam p))))
            (𝓝[<] 1) (𝓝 0)
          ∧ Tendsto (fun p => rhoL g2 wmin (BhatSigma cyc (hitExp p) (lam p))) (𝓝[<] 1) (𝓝 0))
      ∧ ∀ wmin wsup : ℝ, 0 < wmin → wmin ≤ wsup → ∀ u0 : Fin 5 → ℝ, (∀ x, 0 < u0 x) →
          ∀ L0 : ℝ → ℝ, Tendsto (fun p => wmin * Real.sqrt (Graph.minOver cyc (lam p))
            / (Graph.nrmL2 (lam p) u0 * wsup
              * max 1 (Real.sqrt (L0 p / (wmin * Graph.minOver cyc (lam p)))))) (𝓝[<] 1) (𝓝 0) :=
  ⟨three_div_one_sub_tendsto_atTop,
    fun _ hp0 hp1 => ⟨betaCyc_summable hp0 hp1, (mixing_B_coercive hp0 hp1).1⟩,
    mixing_B_tendsto_atTop, bhatSigma_cycle_tendsto,
    fun g2 wmin hg2 hw =>
      ⟨rho_mixing_tendsto (g2 := g2) (wmin := fun _ => wmin) (W := wmin) hg2
          (Eventually.of_forall fun _ => ⟨hw, le_rfl⟩),
        (rhoSigma_cycle_tendsto (g2 := g2) (wmin := fun _ => wmin) (W := wmin) hg2
          (Eventually.of_forall fun _ => ⟨hw, le_rfl⟩)).1⟩,
    fun _ _ hwmin hws _ hu0 L0 => kappa_cycle_tendsto hwmin hws hu0 L0⟩

end AssembledRemark

end CycleRemarks
end GFNBounds.Graph
