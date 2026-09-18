import GFNBounds.Silva.Explicit
import GFNBounds.Silva.NoUniform
import GFNBounds.Graph.CycleDivergence
import GFNBounds.Graph.CycleRemarks
import GFNBounds.Doubling.Setting

/-!
# The hypotheses, the constant and the path space of the Silva bound: three remarks of Appendix B

**`rem:silva_hypotheses`** — `silva_comparison.tex:52–62` (a remark; no proof environment).

**`rem:silva_model_constant`** — `silva_comparison.tex:64–78` (a remark; no proof environment).

**`rem:path_space`** — `silva_comparison.tex:110–116` (a remark; no proof environment).

Read against draft commit `3194054` (the working tree at `216ce34`; the labels are the anchors,
kb 0036). The three remarks were rewritten on 2026-09-14 so that every sentence is a claim or
visibly heuristic; attributions to Silva et al. are marked and are not targets.

> (`rem:silva_hypotheses`) The proof above isolates the hypotheses under which Equation
> `eq:silva_bound` operates; they are used, but not all stated, in `silvageneralization`.
> 1. *Full support of `p_{E,T}`.* The change-of-measure step divides by `p_{E,T}` under a
>    uniformly weighted sum; off full support, `χ²(q_{E,T}‖p_{E,T}) = +∞` and the right side of
>    Proposition `prop:silva_explicit` is `+∞`, or `∞·0` when `𝓔(p_F) = 0`. Heuristically, `χ²`
>    plays here, in `L²` form, the role of the factor `‖dln‖_{L^∞}` in Theorem `theo:RL_CV_bound`.
> 2. *Full support of the trained `p_F`.* If `p_F(τ) = 0` for a trajectory `τ` into a terminal
>    state `x` with `p_{E,T}(x) > 0` and `p_B(τ|x) > 0`, then `𝓔(p_F) = +∞`: the bound holds but
>    carries no information. `silvageneralization` remove this with the `α`-mixture realizability
>    device of their Lemma B.1, which they invoke only for their Theorem 5.2.
> 3. *Domination by the backward policy.* The identity `p_T(x) = 𝔼_{p_B(·|x)}[p_F/p_B]` requires
>    `p_B(·|x)` to dominate forward trajectories into `x` — automatic for the uniform `p_B` that
>    `silvageneralization` fix throughout, an assumption under the extension to learnable `p_B`
>    they mention.
> 4. *The constant depends on the trained model, boundedly on each fixed graph.*
>    `M = max_{τ,x} p_F(τ)/p_B(τ|x)` is a maximum over the *learned* forward policy; it is
>    quantified in Remark `rem:silva_model_constant` below.
> 5. *Constant of the log-Lipschitz step.* The step `(a−b)² ≲ (log a − log b)²` is justified in
>    Lemma D.1 of `silvageneralization` for arguments in `(0,1]` after rescaling by `M`; since
>    `π(x) ≤ M` is not implied by the definition of `M` (on a star, `s_o` with `K ≥ 3` terminal
>    children, the uniform forward policy has `M = 1/K`, while a target with `π(x) = ½` at one
>    child has `‖π‖_∞ = ½ > M`), a sufficient rescaling constant is `M' = max(M, ‖π‖_∞)`, as in
>    Proposition `prop:silva_explicit`.
> 6. *Structural axioms.* Finiteness of `𝒳`, the uniform horizon `t_m`, and acyclicity (derived
>    from the finitely-absorbing axiom) are standing hypotheses of their framework; the prefactor
>    `|𝒳|/2` is absorbed into `≲` in their statement.

> (`rem:silva_model_constant`) Heuristically, the reading of Proposition `prop:silva_explicit`
> hinges on its constant: the proposition is a statement about a *fixed* model, while a convergence
> guarantee for training must hold uniformly along a minimizing sequence — and `M'` is a maximum
> over the very policy being trained. On a fixed graph that dependence is bounded: since
> `p_F(τ) ≤ 1` and
> `‖π‖_∞ ≤ 1`, every forward policy has
> `M' ≤ max(1, max_{τ,x : p_B(τ|x)>0} 1/p_B(τ|x))`.
> On a tree, `p_B(τ|x) = 1` and `M ≤ 1`; on a state graph with several backward paths into a
> terminal state, `M` can exceed `1` but stays at most that bound. Consider the ladder graph of
> depth `n`: `n+1` states in a row, two parallel edges at each of the `n` stages, and the last
> state `x` as the only terminal state, so that `π(x) = p_{E,T}(x) = 1`, `x` has `2ⁿ` incoming
> trajectories, the uniform backward policy gives `p_B(τ|x) = 2⁻ⁿ` for each, and `M' ≤ 2ⁿ`. At
> the balanced solution, `p_F(τ) = π(x)p_B(τ|x)` and `M = ‖π‖_∞ = 1`. But already at the level
> of trajectory distributions (before imposing Markov realizability of `p_F`), a distribution
> placing mass `c` on a single trajectory `τ₀` has `M ≥ c 2ⁿ`, while the corresponding term of the
> residual `𝓔(p_F)` is `2⁻ⁿ (log(c 2ⁿ))² → 0` as `n → ∞`: the residual weights the trajectory on
> which the constant is large by `p_B(τ₀|x) = 2⁻ⁿ`. With `c := 1 − e^{−√(ε/2)}` and the remaining
> mass `1 − c` spread uniformly over the other trajectories, `𝓔(p_F) → ε/2` as `n → ∞`;
> consequently, over trajectory distributions,
> `sup{M'(p_F) : 𝓔(p_F) ≤ ε} ≥ (1 − e^{−√(ε/2)}) 2ⁿ`
> for every `ε > 0` and every `n` large enough: on `{𝓔 ≤ ε}` the constant reaches the order of its
> fixed-graph bound, and no constant is uniform in the depth. This computation does not quantify
> the growth of the same supremum over Markov forward policies. On a directed cycle entered at one
> state and terminal at every state, Lemma `lem:cycle_counterexample` rules out any model-free
> bound tending to `0` with the loss for the divergence-based FM losses of `brunswic2024theory`
> with a generator continuous at `1` (Remark `rem:path_space`), a class that does not contain the
> idealized residual `𝓔(p_F)`.

> (`rem:path_space`) Heuristically, the graph-dependence of all these bounds is measured by the
> size of the *path space*. In Proposition `prop:silva_no_uniform`(i), since for a backward policy
> of full support `p_B(·|x)` is a probability charging each of the `P(x)` trajectories into `x`,
> one has `min_τ p_B(τ|x) ≤ 1/P(x)` and therefore `1/w_min ≥ max_{x∈𝒳} P(x)/p_{E,T}(x)`, and the
> constant `M'` of Proposition `prop:silva_explicit` satisfies `sup_{p_F} M' ≥ max_{x∈𝒳} P(x)`, the
> supremum running over full-support forward policies. When a cycle lies on the trajectories into
> a state `x`, these are infinitely many, so `inf_τ p_B(τ|x) = 0` and `sup_{p_F} M' = +∞`. Let
> `𝒞_N` be the directed cycle on states `x₁,…,x_N` of Lemma `lem:cycle_counterexample`, entered at
> `x₁` and terminal at every state: on `𝒞_N` with a fixed training distribution, `|𝒳| = N` and
> `χ²(q_{E,T}‖p_{E,T})` do not depend on the flow, while on the counter-example graph
> `eq:counterexample_graph`, whose terminal set is infinite, `|𝒳| = ∞` and `χ²(q_{E,T}‖p_{E,T})` is
> undefined, there being no uniform distribution on an infinite set. For the divergence-based FM
> losses of `brunswic2024theory` with a generator continuous at `1`, acyclicity cannot be dropped:
> on `𝒞_N`, for a target `κ ≠ δ_{x₂}`, Lemma `lem:cycle_counterexample` supplies flows whose loss
> tends to `0` for every training distribution while their terminal law stays `δ_{x₂}`, at total
> variation `1 − κ(x₂) > 0` from `κ`, so no model-free bound tending to `0` with the loss holds.
> The idealized residual `𝓔(p_F)` lies outside that class, and whether the acyclicity hypothesis of
> `silvageneralization` can be dropped from their bound the lemma does not decide; what this remark
> establishes for that bound is the graph-dependence of its constants through the path space.

## Claim by claim

| sentence | declaration |
|---|---|
| **silva_hypotheses (1)** `χ² = +∞` off full support | `chiSqE_unif_eq_top` |
| (1) the right side is `+∞` | `rhsE_eq_top_of_not_full_support` |
| (1) "or `∞·0` when `𝓔 = 0`" | `one_add_chiSqE_eq_top` (the two factors only; see SCOPE) |
| (1) the extended reading is the proposition's | `chiSqE_eq_ofReal`, `residualE_eq_ofReal`, `rhsE_ofReal`, `tv_le_rhsE` |
| (1) "Heuristically, `χ²` plays … `‖dln‖_∞`" | — heuristic, not a target |
| (2) `𝓔(p_F) = +∞` | `residualE_eq_top_of_pF_zero` |
| (2) "the bound holds but carries no information" | `rhsE_eq_top_of_residual_top`, `tv_le_rhsE_of_pF_zero` |
| (3) the identity requires domination (and holds under it) | `identity_iff_domination` |
| (3) automatic for the uniform `p_B` | `uniformBackProb_pos`, `identity_of_uniformBackward` |
| (3) an assumption for a learnable `p_B` | `identity_fails_without_domination` |
| (4) bounded on each fixed graph; depends on the model | `mPrime_le_fixedGraph`; `ladder_balanced` vs `ladder_mVal_exceeds_one` |
| (5) star: `M = 1/K < ½ = ‖π‖_∞`, so `π(x) ≤ M` is not implied | `star_mVal_lt_piInf` |
| (5) `M'` is a sufficient rescaling constant | `GFNBounds.Silva.logLipschitz` (strict, `Silva/Explicit.lean`) |
| (2)'s device, (6), the Lemma D.1 attribution | — attributions to Silva et al., not targets |
| **silva_model_constant** `M' ≤ max(1, max 1/p_B)` | `mPrime_le_fixedGraph`, `mPrime_le_fixedGraph_of_prob` |
| on a tree `p_B = 1`, `M ≤ 1` | `tree_pB_eq_one`, `tree_mVal_le_one` |
| `M` can exceed `1`, stays below the bound | `ladder_mVal_exceeds_one` |
| ladder: `2ⁿ` trajectories, `p_B = 2⁻ⁿ`, `M' ≤ 2ⁿ` | `card_ladderTraj`, `ladderPB_eq`, `ladderPB_sum`, `ladder_mPrime_le` |
| balanced solution: `M = ‖π‖_∞ = 1` | `ladder_balanced` |
| mass `c` on `τ₀`: `M ≥ c2ⁿ`, term `2⁻ⁿ(log c2ⁿ)² → 0` | `ladder_mVal_ge`, `ladder_term_eq`, `tendsto_ladder_term` |
| `𝓔(p_F) → ε/2` | `ladder_residual_ladderPFc`, `tendsto_ladder_residual`, `tendsto_ladder_residual_eps` |
| `sup{M' : 𝓔 ≤ ε} ≥ (1 − e^{−√(ε/2)}) 2ⁿ`, `n` large | `ladder_witness`, `ladder_sSup_ge` (with `ladder_pF_ne_zero_of_residualE_ne_top`) |
| no constant uniform in the depth | `ladder_no_uniform_constant` |
| "does not quantify … over Markov forward policies" | — a disclaimer, nothing to certify |
| the cycle rules out a model-free bound | `cycle_no_model_free_bound`, `cycle_no_bound_along_Fk`, `cycle_no_bound_punctured` |
| "a class that does not contain `𝓔(p_F)`" | `residual_not_divergence_FM_loss` (the diamond family) |
| **path_space** `min_τ p_B(τ|x) ≤ 1/P(x)` | `exists_pB_le_inv_pathCount` |
| `1/w_min ≥ max_x P(x)/p_{E,T}(x)` | `pathCount_div_le_inv_wMin`, `sup_pathCount_div_le_inv_wMin` |
| `sup_{p_F} M' ≥ max_x P(x)`, full-support forward policies | `sup_pathCount_le_sSup_mPrime_markov` (Markov); `sup_pathCount_le_sSup_mPrime` (trajectory laws) |
| a cycle on the trajectories into `x`: infinitely many | `walksInto_infinite` |
| `inf_τ p_B(τ|x) = 0` | `iInf_eq_zero_of_summable`, `iInf_pB_walksInto_eq_zero` |
| `sup_{p_F} M' = +∞` | `exists_ratio_gt_walksInto`, `exists_ratio_gt` (trajectory laws; see SCOPE) |
| on `𝒞_N`: `|𝒳| = N`, `χ²` independent of the flow | `GFNBounds.Graph.CycleDivergence.card_internal`; definitional |
| counter-example graph: terminal set infinite, no uniform law | `doubling_terminal_infinite`, `doubling_no_uniform_terminal_law`, `not_hasSum_const_one` |
| `κ ≠ δ_{x₂}`: loss `→ 0` for every `ν`, terminal law `δ_{x₂}`, TV `1 − κ(x₂) > 0` | `cycle_flows_target` (via the strict `CycleRemarks.fmRatio_Fk_gen`, `fmLossTarget_Fk_tendsto_zero_gen`, `tvFin_termLaw_Fk_gen`, `den_pos_and_ratio_pos`, and `target_x2_lt_one`) |
| so no model-free bound tending to `0` with the loss | `cycle_no_model_free_bound`, `cycle_no_bound_along_Fk`, `cycle_no_bound_punctured` |
| "the idealized residual lies outside that class" | `residual_not_divergence_FM_loss` |
| "the lemma does not decide", the heuristic lead | — nothing to certify; see SCOPE |
| ladder consistency: `sup M' = 2ⁿ`, `1/w_min ≥ 2ⁿ` | `ladder_sSup_mPrime_eq` |

## SCOPE (disclosed)

* **Extended reals (ruling R19's default).** `χ²` and `𝓔` are `ℝ≥0∞`-valued here (`chiSqE`,
  `residualE`), and so is the right side `rhsE c χ² 𝓔 = c·((1+χ²)𝓔)^{1/2}` of
  `prop:silva_explicit`, with `c = (|𝒳|/2)M'` a real prefactor. A state with `p = 0 < q`
  contributes `+∞` to `χ²`; `(log(a/b))²` is `+∞` as soon as `a = 0` or `b = 0` (`logSqE`) — at
  `a = b = 0` the paper's expression is undefined and `+∞` is a convention, unreachable under
  `π > 0` on the support of `p_B`. The real library vocabulary is recovered on full support by
  `chiSqE_eq_ofReal`, `residualE_eq_ofReal`, `rhsE_ofReal`, and `tv_le_rhsE` shows the
  extended-real bound is `prop:silva_explicit` itself there. **`∞·0` is not given a value**: Lean's
  `ℝ≥0∞` sets `∞·0 = 0`, the paper leaves the form undefined, so `one_add_chiSqE_eq_top` states only
  that the factors are `+∞` and `0`.
* **Trajectories are an abstract finite type**, as in `Silva/Explicit.lean` and
  `Silva/NoUniform.lean`: `into : T → X` sends a trajectory to its terminal state, and
  "`p_B(·|x)` lives on the trajectories into `x`" is the hypothesis `p_B(τ|x) ≠ 0 → into τ = x`.
  A *tree* is `into` injective (one trajectory per terminal state). The *ladder* is its trajectory
  space `Fin n → Bool` with the backward factor `½` at each stage (`ladderPB`); its states and
  parallel edges are not modelled — a `Finset`-successor graph cannot carry parallel edges — so
  "`x` has `2ⁿ` incoming trajectories" is by construction (`card_ladderTraj`). The *star* of item
  (5) is the one-parent kernel `deltaPB (Fin K)` of `Silva/NoUniform.lean`.
* **The uniform backward policy** of item (3) is `uniformBackProb`, the product along a path of
  `1/#parents`; only its positivity on paths of the graph is proved and used. That it sums to `1`
  over the trajectories into `x` is **not** proved.
* **"Forward policy".** `rem:silva_model_constant` itself works over trajectory distributions and
  says so; its statements here are over trajectory laws `p_F : T → ℝ`. In `rem:path_space`,
  `sup_{p_F} M' ≥ max_x P(x)` is certified **over full-support Markov forward policies**
  (`sup_pathCount_le_sSup_mPrime_markov`): trajectories are paths `path t` of a graph with
  successor sets `succ`, each visiting a state at most once (as on a DAG — carried as a hypothesis,
  not derived from acyclicity), a policy is positive on every edge and a probability on the
  successors of every non-sink state, and `p_F(t) = pathProb pol (path t)`. The class does not
  assert `∑_t p_F(t) = 1` — not used, and it would need `T` to be exactly the complete
  trajectories of a finitely absorbing DAG. **⚠ `sup_{p_F} M' = +∞` on a cycle is certified over
  full-support trajectory laws only** (`exists_ratio_gt`): a supremum over a larger class, so a
  weaker statement than over Markov policies, which is not formalized. `= +∞` is delivered as
  `∀ R, ∃ p_F, ∃ τ, p_F(τ)/p_B(τ|x) > R` (and `M' ≥` that ratio), `M'` having no value on an
  infinite trajectory set; `exists_ratio_gt` also asks a full-support probability `ν` on the
  trajectories; on the walks into `x` it is `p_B(·|x)` itself (`exists_ratio_gt_walksInto`), and a
  full-support probability on the walks of `𝒞₂` is constructed (`exists_pos_hasSum_one`,
  `inhabit_cycle_ratio`).
* **Suprema are over full-support laws.** The `sSup` sets in `ladder_sSup_ge` and
  `pathCount_le_sSup_mPrime` range over full-support `p_F`, where the real `residual` is the
  paper's `𝓔`. For `rem:path_space` the paper restricts to full support itself; on the ladder,
  `ladder_pF_ne_zero_of_residualE_ne_top` shows every law with `𝓔 ≤ ε` has full support, so
  nothing is lost. The sets are bounded above (`ladder_mPrime_le`, `mPrime_le_of_le_one`), so each
  `sSup` is a genuine supremum.
* **Cycles and walks.** A trajectory into `x` is a walk `s₀ → ⋯ → x` (`walksInto`, a list with
  `IsChain`); "a cycle lies on the trajectories into `x`" is read as: some walk from `s₀` to `x`
  visits a state `v` carrying a nonempty closed walk `v → ⋯ → v`. `iInf_pB_walksInto_eq_zero`
  holds for **every** probability on the walks.
* **The counter-example graph's terminal set** is read from the figure `eq:counterexample_graph`
  (every ladder state `j ≥ 1` has a terminal edge) as the range of `j ↦ St.lad (j+1)` in
  `GFNBounds.Doubling.Setting`; that layer models the backward chain `pstar`, not an edge
  relation, so the terminal edges themselves are not a Lean object.
* **`𝒞_N` and its loss are `GFNBounds.Graph.CycleDivergence`'s**, with its disclosures inherited:
  the ratio `ρ = (F_init + f_←)/(κ + f_→)` carries the target in the denominator; the total
  variation is taken against the **normalized terminal flow**, its identification with the
  sampler `s_τ` being `theo:sampling_theorem`, cited and not certified; `N ≥ 2` is `N = M + 2`;
  `g : ℝ₊ → ℝ₊` is `g : ℝ → ℝ` with `g ≥ 0` on `(0,∞)`. The target is the paper's: a probability
  `t` on `{x₁,…,x_N}`, extended by `0` at the marks (`CycleRemarks.extT`), and the closed forms
  at that target are the strict `GFNBounds.Graph.CycleRemarks` lemmas.
* **"No model-free bound tending to `0` with the loss"**, only where the loss is defined. A bound
  is `Φ : ℝ → ℝ` with `TV ≤ Φ(𝓛)`; asking it on more flows makes its negation weaker, so the flows
  are restricted to those on which neither the loss nor the terminal law is a junk value. Along
  `F_k` this is `k ∈ ℕ`, `k ≥ 1` (the paper's "`𝓛(F_k)` is defined for `k ≥ 1`", where
  `den_pos_and_ratio_pos` gives every denominator `κ + f_→` and every ratio positive, and the
  terminal mass is `1`); over flows (`cycle_no_model_free_bound`) it is the nonnegative,
  edge-carried, flow-matching flows with every denominator positive and positive terminal mass.
  With `Φ(L) → 0` as `L → 0` through `L ≥ 0` (`𝓝[≥] 0`, which forces `Φ(0) = 0`) the bound is
  refuted for **every** `ν ≥ 0` and every `g ≥ 0` continuous at `1` with `g(1) = 0`, already along
  `(F_k)_{k≥1}` (`cycle_no_bound_along_Fk`). With the punctured limit (`𝓝[>] 0`) it is refuted
  along `(F_k)_{k≥1}` when `ν(x₂) > 0` and `g > 0` off `1` (`cycle_no_bound_punctured`); where the
  loss vanishes identically along `F_k` (e.g. `ν = 0`) the punctured reading refutes nothing along
  them — see the report's precision note.
* **"The idealized residual lies outside that class"** is certified on the diamond DAG
  (`residual_not_divergence_FM_loss`): the unit-mass edge flows of the full-support Markov policies
  `diamondPol q` have ratio `1` and positive denominators at every state against `δ_x`, so every
  divergence-based FM loss (any `g` with `g(1) = 0`, any `ν`) vanishes on the family, while the
  residual of the same models is `½(log 2q)² + ½(log 2(1−q))² > 0` for `q ≠ ½`; no such loss
  equals `𝓔` on the family. The flow is given explicitly (`diamondFlow`), its trajectory law as
  `pathProb (diamondPol q)` along `diamondPath`; that the edge flow is the policy's is by the
  definitions, not derived by a flow-from-policy construction.
* **Not formalized, and why.** "Whether the acyclicity hypothesis … can be dropped the lemma does not decide",
  "This computation does not quantify … over Markov forward policies": statements about what is
  not proved, with nothing to certify. The heuristic leads of `rem:silva_model_constant` and
  `rem:path_space` and item (1)'s `χ²`/`‖dln‖_∞` analogy are marked heuristic. Attributions to
  Silva et al. (item (2)'s Lemma B.1 device, item (5)'s Lemma D.1, item (6)) are not targets.
* **No `sorry`, no axiom.** Every declaration below is closed.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒳`, trajectories finite | ✓ `[Fintype X] [Fintype T]` |
| DAG, horizon `t_m`, acyclicity (item 6) | ⚠ not modelled — no step consumes them; paths visit each state once (Markov form) |
| (1) off full support: some `p_{E,T}(x₀) = 0` | ✓ `h0`; `q_{E,T}` uniform, positive |
| (1) right side `+∞`: `𝓔 ≠ 0`, positive prefactor | ✓ `hE`, `hc` |
| (2) `p_F(τ) = 0`, `p_{E,T}(x) > 0`, `p_B(τ|x) > 0` | ✓ `hF0`, `hET`, `hB` |
| (3) `p_B(·|x)` on the trajectories into `x` | ✓ `hBsupp`; `p_F ≥ 0` ✓ `hF` |
| (3) uniform `p_B` | ⚠ `uniformBackProb` along graph paths; normalization not proved |
| (5) star, `K ≥ 3` children, uniform `p_F`, `π(x₀) = ½` | ✓ `hK`, `fun _ => 1/K`, `hx₀`; `π` a probability (`hπ0`, `hπ1`) |
| model_constant: `p_F ≤ 1`, `‖π‖_∞ ≤ 1` | ✓ `hF1`, `hπ1` (and the probability form) |
| tree | ⚠ `into` injective + `p_B(·|x)` a probability on the trajectories into `x` |
| ladder of depth `n`, uniform `p_B`, `π = p_{E,T} = 1` | ⚠ trajectory space `Fin n → Bool`, `ladderPB`, `ladderOne`; graph not modelled |
| "over trajectory distributions" | ✓ `p_F : LadderTraj n → ℝ`, full support (no loss on `{𝓔 ≤ ε}`) |
| `c := 1 − e^{−√(ε/2)}`, rest uniform | ✓ `ladderPFc n c` |
| "every `n` large enough" | ✓ `∀ᶠ n in atTop` |
| path_space: `p_B(·|x)` full support on the `P(x)` trajectories into `x` | ✓ `hBsupp`, `hBpos`, `hB1` |
| `p_{E,T}` full support (for `w_min > 0`) | ✓ `hET` |
| "full-support forward policies" | ✓ Markov (`hchain`, `hnodup`, policy positive and stochastic); also trajectory laws |
| a cycle lies on the trajectories into `x` | ✓ `hw`, `hv`, `hcne`, `hcE`, `hc` |
| `p_B(·|x)` a probability on infinitely many trajectories | ✓ `HasSum pB 1` / `Summable`, `[Infinite]` or `hinf` |
| `sup M' = +∞` over forward policies | ⚠ trajectory laws only; `ν := p_B(·|x)` on the walks into `x` |
| `𝒞_N`, `N ≥ 2` | ✓ `cycGraph M`, `N = M + 2` |
| `κ` a probability on `{x₁,…,x_N}`, `κ ≠ δ_{x₂}` | ✓ `extT M t` with `ht0`, `hsum`, `ht` |
| "`𝓛(F_k)` is defined for `k ≥ 1`" | ✓ `k : ℕ`, `1 ≤ k`; flows with positive denominators and terminal mass |
| training distribution `ν` | ✓ any `ν ≥ 0` (`hnu`); punctured form also `ν(x₂) > 0` |
| `g : ℝ₊ → ℝ₊`, continuous at `1`, zero exactly at `1` | ✓ `hg0` (on `(0,∞)`), `hgc`, `hg1`; `g > 0` off `1` (`hgpos`) only where used |
| "does not contain `𝓔`": the FM class | ✓ any `g` with `g(1) = 0`, any `ν` (wider than the class) |
| `s_τ(F_k) ∼ δ_{x₂}` (`theo:sampling_theorem`) | ✗ not certified — normalized terminal flow, as in `CycleDivergence` |

## Inhabitation (kb 0025)

Every hypothesis bundle a main theorem assumes is met on an explicit instance, in the section
`Inhabitation`: `inhabit_not_full_support` (item 1), `inhabit_pF_zero` (item 2),
`inhabit_uniformBackward` (item 3), `inhabit_tree` (the star of `prop:silva_no_uniform`(ii)),
`ladder_sSup_mPrime_eq` (the path-space hypotheses on the ladder, where the lower bound
`sup M' ≥ 2ⁿ` meets the fixed-graph bound and `sup M' = 2ⁿ` exactly), `inhabit_markov_diamond`
(the Markov hypotheses on the diamond DAG, `P(x) = 2`), `inhabit_cycle_walks` (a cycle on the
walks into `x₂` of `𝒞₂`), `inhabit_cycle_ratio` (a full-support `p_B` on those walks, with
`inf p_B = 0` and unbounded ratios), `inhabit_geometric` (infinite support on `ℕ`), and
`inhabit_cycle_no_bound` (`g(r) = (r−1)²`, `ν ≡ 1`, `κ` uniform on `{x₁,…,x_N}`, both readings).
`residual_not_divergence_FM_loss` carries no hypothesis. Item (5) takes `K ≥ 3`, a probability
`π` and a child with `π(x₀) = ½`, inhabited by `inhabit_star` (`K = 3`, `π = (½, ¼, ¼)`); the
ladder family and the ladder witnesses carry no hypothesis beyond `ε > 0`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Silva.Remarks

open Finset Filter Topology
open scoped ENNReal

/-! ## `M`, `‖π‖_∞` and `M'` as values -/

section Values

variable {X T : Type*} [Fintype X] [Fintype T]

/-- `M := max{ p_F(τ)/p_B(τ|x) : p_B(τ|x) > 0 }` of `silva_comparison.tex:32`, as a value. -/
noncomputable def mVal (pB : X → T → ℝ) (pF : T → ℝ) (hs : (wSupport pB).Nonempty) : ℝ :=
  (wSupport pB).sup' hs fun p => pF p.2 / pB p.1 p.2

/-- `‖π‖_∞ = max_x π(x)`, as a value. -/
noncomputable def piInf (π : X → ℝ) (hX : (univ : Finset X).Nonempty) : ℝ :=
  univ.sup' hX π

/-- `M' := max(M, ‖π‖_∞)` of `silva_comparison.tex:32`, as a value. -/
noncomputable def mPrime (pB : X → T → ℝ) (pF : T → ℝ) (π : X → ℝ)
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty) : ℝ :=
  max (mVal pB pF hs) (piInf π hX)

theorem mem_wSupport {pB : X → T → ℝ} {x : X} {t : T} (ht : 0 < pB x t) :
    (x, t) ∈ wSupport pB := by
  simp only [wSupport, mem_filter, mem_univ, true_and]
  exact ht

theorem ratio_le_mVal {pB : X → T → ℝ} (pF : T → ℝ) (hs : (wSupport pB).Nonempty) {x : X}
    {t : T} (ht : 0 < pB x t) : pF t / pB x t ≤ mVal pB pF hs :=
  Finset.le_sup' (fun p : X × T => pF p.2 / pB p.1 p.2) (mem_wSupport ht)

theorem mVal_le_mPrime (pB : X → T → ℝ) (pF : T → ℝ) (π : X → ℝ)
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty) :
    mVal pB pF hs ≤ mPrime pB pF π hs hX :=
  le_max_left _ _

/-- The value `M'` and the library's `MprimeLe` agree: `M' ≤ c ↔ MprimeLe pB pF π c`. -/
theorem mPrime_le_iff (pB : X → T → ℝ) (pF : T → ℝ) (π : X → ℝ)
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty) (c : ℝ) :
    mPrime pB pF π hs hX ≤ c ↔ MprimeLe pB pF π c := by
  simp only [mPrime, mVal, piInf, max_le_iff, Finset.sup'_le_iff, MprimeLe, mem_univ,
    true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x t ht => h1 (x, t) (mem_wSupport ht), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => ?_, h2⟩
    simp only [wSupport, mem_filter, mem_univ, true_and] at hp
    exact h1 p.1 p.2 hp

end Values

/-! ## `rem:silva_hypotheses` -/

section ExtendedReals

variable {X T : Type*} [Fintype X] [Fintype T]

/-- `χ²(q‖p)` in `[0,∞]`: a state with `p = 0 < q` contributes `+∞`, a state with
`p = q = 0` contributes `0`. -/
noncomputable def chiSqE (q p : X → ℝ) : ℝ≥0∞ :=
  ∑ x, if p x = 0 then (if q x = 0 then 0 else ⊤) else ENNReal.ofReal ((q x - p x) ^ 2 / p x)

/-- On full support `chiSqE` is the library's real `chiSq`. -/
theorem chiSqE_eq_ofReal {q p : X → ℝ} (hp : ∀ x, 0 < p x) :
    chiSqE q p = ENNReal.ofReal (chiSq q p) := by
  rw [chiSq, ENNReal.ofReal_sum_of_nonneg fun x _ => div_nonneg (sq_nonneg _) (hp x).le]
  exact Finset.sum_congr rfl fun x _ => by rw [if_neg (hp x).ne']

/-- **`rem:silva_hypotheses`(1)**: off full support of `p_{E,T}`,
`χ²(q_{E,T}‖p_{E,T}) = +∞`. -/
theorem chiSqE_unif_eq_top {pET : X → ℝ} {x₀ : X} (h0 : pET x₀ = 0) :
    chiSqE (unif X) pET = ⊤ := by
  haveI : Nonempty X := ⟨x₀⟩
  have hc : (Fintype.card X : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ENNReal.sum_eq_top.mpr ⟨x₀, mem_univ _, ?_⟩
  simp only [h0, if_true, unif, hc, if_false]

/-- `log(a/b)²` in `[0,∞]`, with `log 0 = −∞` and `log(+∞) = +∞`: it is `+∞` as soon as `a = 0`
or `b = 0`. (At `a = b = 0` the paper's expression is undefined; `+∞` is a convention, and the
case never arises with `π > 0` on the support of `p_B`.) -/
noncomputable def logSqE (a b : ℝ) : ℝ≥0∞ :=
  if a = 0 ∨ b = 0 then ⊤ else ENNReal.ofReal (Real.log (a / b) ^ 2)

/-- The residual `𝓔(p_F)` of `silva_comparison.tex:24–26` in `[0,∞]`. The factor `p_B(τ|x)`
kills the terms off its support (`0 · ∞ = 0` in `ℝ≥0∞`). -/
noncomputable def residualE (pET π : X → ℝ) (pB : X → T → ℝ) (pF : T → ℝ) : ℝ≥0∞ :=
  ∑ x, ENNReal.ofReal (pET x) * ∑ t, ENNReal.ofReal (pB x t) * logSqE (pF t) (π x * pB x t)

/-- On the setting of `prop:silva_explicit` (`π > 0`, `p_F > 0` on the support of `p_B`),
`residualE` is the library's real `residual`. -/
theorem residualE_eq_ofReal {pET π : X → ℝ} {pB : X → T → ℝ} {pF : T → ℝ}
    (hET : ∀ x, 0 ≤ pET x) (hπ : ∀ x, 0 < π x) (hB : ∀ x t, 0 ≤ pB x t)
    (hF : ∀ x t, 0 < pB x t → 0 < pF t) :
    residualE pET π pB pF = ENNReal.ofReal (residual pET π pB pF) := by
  have hin : ∀ x, ∑ t, ENNReal.ofReal (pB x t) * logSqE (pF t) (π x * pB x t)
      = ENNReal.ofReal (∑ t, pB x t * logRatio π pB pF x t ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg fun t _ => mul_nonneg (hB x t) (sq_nonneg _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases (hB x t).eq_or_lt with h | h
    · rw [← h, ENNReal.ofReal_zero, zero_mul, zero_mul, ENNReal.ofReal_zero]
    · have hF' := hF x t h
      rw [logSqE, if_neg (not_or.mpr ⟨hF'.ne', (mul_pos (hπ x) h).ne'⟩),
        ← ENNReal.ofReal_mul h.le, logRatio]
  have hin_nn : ∀ x, 0 ≤ ∑ t, pB x t * logRatio π pB pF x t ^ 2 := fun x =>
    Finset.sum_nonneg fun t _ => mul_nonneg (hB x t) (sq_nonneg _)
  rw [residual, ENNReal.ofReal_sum_of_nonneg fun x _ => mul_nonneg (hET x) (hin_nn x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hin x, ← ENNReal.ofReal_mul (hET x)]

/-- **`rem:silva_hypotheses`(2)**: if `p_F(τ) = 0` for a trajectory `τ` into `x` with
`p_{E,T}(x) > 0` and `p_B(τ|x) > 0`, then `𝓔(p_F) = +∞`. -/
theorem residualE_eq_top_of_pF_zero {pET π : X → ℝ} {pB : X → T → ℝ} {pF : T → ℝ}
    {x₀ : X} {t₀ : T} (hET : 0 < pET x₀) (hB : 0 < pB x₀ t₀) (hF0 : pF t₀ = 0) :
    residualE pET π pB pF = ⊤ := by
  refine ENNReal.sum_eq_top.mpr ⟨x₀, mem_univ _, ?_⟩
  have hin : ∑ t, ENNReal.ofReal (pB x₀ t) * logSqE (pF t) (π x₀ * pB x₀ t) = ⊤ := by
    refine ENNReal.sum_eq_top.mpr ⟨t₀, mem_univ _, ?_⟩
    rw [logSqE, if_pos (Or.inl hF0)]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr hB).ne'
  rw [hin]
  exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr hET).ne'

/-- The right side `c · [(1 + χ²) 𝓔]^{1/2}` of `prop:silva_explicit` in `[0,∞]`, with
`c = (|𝒳|/2) M'` the (finite, nonnegative) prefactor. -/
noncomputable def rhsE (c : ℝ) (chi E : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal c * ((1 + chi) * E) ^ (1 / 2 : ℝ)

/-- On finite values `rhsE` is the real right side of `prop:silva_explicit`. -/
theorem rhsE_ofReal {c chi E : ℝ} (hchi : 0 ≤ chi) (hE : 0 ≤ E) :
    rhsE c (ENNReal.ofReal chi) (ENNReal.ofReal E)
      = ENNReal.ofReal (c * Real.sqrt ((1 + chi) * E)) := by
  have h1 : (1 : ℝ≥0∞) + ENNReal.ofReal chi = ENNReal.ofReal (1 + chi) := by
    rw [ENNReal.ofReal_add zero_le_one hchi, ENNReal.ofReal_one]
  rcases le_or_gt 0 c with hc | hc
  · rw [rhsE, h1, ← ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (by linarith) hE) (by norm_num), ← ENNReal.ofReal_mul hc, Real.sqrt_eq_rpow]
  · rw [rhsE, ENNReal.ofReal_of_nonpos hc.le, zero_mul, ENNReal.ofReal_of_nonpos]
    exact mul_nonpos_of_nonpos_of_nonneg hc.le (Real.sqrt_nonneg _)

/-- **`prop:silva_explicit` read in `[0,∞]`**: under the proposition's hypotheses the
extended-real bound holds, with `chiSqE` and `residualE`. So the extended-real reading of the
two remarks below is a reading of the proposition, not of a parallel statement. -/
theorem tv_le_rhsE {pET π pT : X → ℝ} {pB : X → T → ℝ} {pF : T → ℝ} {M Pinf : ℝ}
    (hET_pos : ∀ x, 0 < pET x) (hET_sum : ∑ x, pET x = 1)
    (hπ_pos : ∀ x, 0 < π x)
    (hB_nonneg : ∀ x τ, 0 ≤ pB x τ) (hB_sum : ∀ x, ∑ τ, pB x τ = 1)
    (hF_pos : ∀ x τ, 0 < pB x τ → 0 < pF τ)
    (hdom : ∀ x, pT x = ∑ τ, pB x τ * (pF τ / pB x τ))
    (hM : ∀ x τ, 0 < pB x τ → pF τ / pB x τ ≤ M)
    (hPinf : ∀ x, π x ≤ Pinf) :
    ENNReal.ofReal (tv pT π) ≤ rhsE ((Fintype.card X : ℝ) / 2 * max M Pinf)
      (chiSqE (unif X) pET) (residualE pET π pB pF) := by
  have hres_nn : 0 ≤ residual pET π pB pF :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hET_pos x).le
      (Finset.sum_nonneg fun t _ => mul_nonneg (hB_nonneg x t) (sq_nonneg _))
  rw [chiSqE_eq_ofReal hET_pos, residualE_eq_ofReal (fun x => (hET_pos x).le) hπ_pos hB_nonneg
    hF_pos, rhsE_ofReal (chiSq_nonneg fun x => (hET_pos x).le) hres_nn]
  exact ENNReal.ofReal_le_ofReal (tv_le_sqrt_residual hET_pos hET_sum hπ_pos hB_nonneg hB_sum
    hF_pos hdom hM hPinf)

/-- **`rem:silva_hypotheses`(1), the right side**: off full support of `p_{E,T}` and with
`𝓔(p_F) ≠ 0`, the right side of `prop:silva_explicit` is `+∞` (for a positive prefactor). -/
theorem rhsE_eq_top_of_not_full_support {c : ℝ} (hc : 0 < c) {pET : X → ℝ} {x₀ : X}
    (h0 : pET x₀ = 0) {E : ℝ≥0∞} (hE : E ≠ 0) :
    rhsE c (chiSqE (unif X) pET) E = ⊤ := by
  rw [rhsE, chiSqE_unif_eq_top h0, add_top, ENNReal.top_mul hE,
    ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']

/-- **`rem:silva_hypotheses`(1), the case `𝓔(p_F) = 0`**: the product under the root is
`(1 + χ²)·𝓔` with `1 + χ² = +∞` and `𝓔 = 0` — the paper's `∞·0`. Nothing more is claimed:
`ℝ≥0∞`'s convention `∞·0 = 0` is not the paper's reading, which leaves the form undefined. -/
theorem one_add_chiSqE_eq_top {pET : X → ℝ} {x₀ : X} (h0 : pET x₀ = 0) :
    1 + chiSqE (unif X) pET = ⊤ := by
  rw [chiSqE_unif_eq_top h0, add_top]

/-- **`rem:silva_hypotheses`(2), "the bound holds but carries no information"**: when
`𝓔(p_F) = +∞` the right side of `prop:silva_explicit` is `+∞` (for a positive prefactor), so the
bound holds for every `p_T` and says nothing. -/
theorem rhsE_eq_top_of_residual_top {c : ℝ} (hc : 0 < c) (chi : ℝ≥0∞) :
    rhsE c chi ⊤ = ⊤ := by
  have h1 : (1 : ℝ≥0∞) + chi ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos le_self_add)
  rw [rhsE, ENNReal.mul_top h1, ENNReal.top_rpow_of_pos (by norm_num),
    ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']

theorem tv_le_rhsE_of_pF_zero {pET π pT : X → ℝ} {pB : X → T → ℝ} {pF : T → ℝ} {c : ℝ}
    (hc : 0 < c) {x₀ : X} {t₀ : T} (hET : 0 < pET x₀) (hB : 0 < pB x₀ t₀) (hF0 : pF t₀ = 0) :
    rhsE c (chiSqE (unif X) pET) (residualE pET π pB pF) = ⊤ ∧
      ENNReal.ofReal (tv pT π) ≤ rhsE c (chiSqE (unif X) pET) (residualE pET π pB pF) := by
  rw [residualE_eq_top_of_pF_zero hET hB hF0, rhsE_eq_top_of_residual_top hc]
  exact ⟨rfl, le_top⟩

end ExtendedReals

/-! ### Item (3): the domination identity -/

section Domination

variable {X T : Type*} [Fintype T] [DecidableEq X]

/-- The terminal marginal `p_T(x) = ∑_{τ into x} p_F(τ)` of a trajectory weight `p_F`, where
`into τ` is the terminal state of `τ`. -/
noncomputable def termMarginal (into : T → X) (pF : T → ℝ) (x : X) : ℝ :=
  ∑ t ∈ univ.filter (fun t => into t = x), pF t

/-- **`rem:silva_hypotheses`(3)**: for a backward policy `p_B(·|x)` living on the trajectories
into `x`, the identity `p_T(x) = 𝔼_{p_B(·|x)}[p_F/p_B]` holds **if and only if** `p_B(·|x)`
dominates the forward trajectories into `x` (`p_B(τ|x) = 0 ⇒ p_F(τ) = 0`). The "if" is the
identity under domination; the "only if" is "requires". -/
theorem identity_iff_domination (into : T → X) {pB : X → T → ℝ} {pF : T → ℝ}
    (hF : ∀ t, 0 ≤ pF t) (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (x : X) :
    termMarginal into pF x = ∑ t, pB x t * (pF t / pB x t) ↔
      ∀ t, into t = x → pB x t = 0 → pF t = 0 := by
  classical
  set g : T → ℝ := fun t => if into t = x ∧ pB x t = 0 then pF t else 0 with hg
  have hsplit : termMarginal into pF x = ∑ t, pB x t * (pF t / pB x t) + ∑ t, g t := by
    rw [termMarginal, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hB : pB x t = 0
    · simp only [hg, hB, zero_mul, zero_add, and_true]
    · have hin : into t = x := hBsupp x t hB
      simp only [hg, hin, hB, and_false, if_false, if_true, add_zero]
      field_simp
  have hg0 : ∀ t ∈ (univ : Finset T), 0 ≤ g t := fun t _ => by
    simp only [hg]
    split_ifs
    exacts [hF t, le_rfl]
  rw [hsplit]
  constructor
  · intro h t hin hB
    have hsum : ∑ t, g t = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg hg0).mp hsum t (mem_univ t)
    simpa only [hg, hin, hB, and_self, if_true] using this
  · intro h
    have hsum : ∑ t, g t = 0 := Finset.sum_eq_zero fun t _ => by
      simp only [hg]
      split_ifs with hc
      · exact h t hc.1 hc.2
      · rfl
    rw [hsum, add_zero]

/-- The probability that the **uniform backward policy** retraces the path `s₀ → s₁ → ⋯ → s_n`
from its last state: the product over its steps of `1/#parents(s_{i+1})`. -/
noncomputable def uniformBackProb {S : Type*} (parents : S → Finset S) : List S → ℝ
  | [] => 1
  | [_] => 1
  | _ :: b :: l => ((parents b).card : ℝ)⁻¹ * uniformBackProb parents (b :: l)

/-- Along a path of the graph (each state a parent of the next) the uniform backward policy
charges the path. -/
theorem uniformBackProb_pos {S : Type*} (parents : S → Finset S) :
    ∀ l : List S, l.IsChain (fun a b => a ∈ parents b) → 0 < uniformBackProb parents l
  | [], _ => by simp only [uniformBackProb]; norm_num
  | [_], _ => by simp only [uniformBackProb]; norm_num
  | a :: b :: l, h => by
      rw [List.isChain_cons_cons] at h
      have hc : (0 : ℝ) < ((parents b).card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨a, h.1⟩)
      simp only [uniformBackProb]
      exact mul_pos (inv_pos.mpr hc) (uniformBackProb_pos parents (b :: l) h.2)

/-- **`rem:silva_hypotheses`(3), "automatic for the uniform `p_B`"**: the backward policy that
charges each trajectory into `x` with its uniform retracing probability dominates every forward
trajectory weight, so the identity holds for every nonnegative `p_F`. -/
theorem identity_of_uniformBackward {S : Type*} (parents : S → Finset S) (into : T → X)
    (path : T → List S) (hpath : ∀ t, (path t).IsChain (fun a b => a ∈ parents b))
    {pF : T → ℝ} (hF : ∀ t, 0 ≤ pF t) (x : X) :
    termMarginal into pF x
      = ∑ t, (if into t = x then uniformBackProb parents (path t) else 0) *
          (pF t / if into t = x then uniformBackProb parents (path t) else 0) := by
  refine (identity_iff_domination into (pB := fun x t =>
      if into t = x then uniformBackProb parents (path t) else 0) hF ?_ x).mpr ?_
  · intro x t h
    by_contra hne
    exact h (if_neg hne)
  · intro t hin h
    simp only [hin, if_true] at h
    exact absurd h (uniformBackProb_pos parents _ (hpath t)).ne'

/-- **`rem:silva_hypotheses`(3), "an assumption under the extension to learnable `p_B`"**: a
backward policy that is a probability but vanishes on a charged forward trajectory breaks the
identity. One terminal, two trajectories, `p_B = (1,0)`, `p_F = (½,½)`: `p_T = 1` while
`𝔼_{p_B}[p_F/p_B] = ½`. -/
theorem identity_fails_without_domination :
    ∃ (pB : Unit → Bool → ℝ) (pF : Bool → ℝ),
      (∀ t, 0 ≤ pF t) ∧ ∑ t, pF t = 1 ∧ (∀ t, 0 ≤ pB () t) ∧ ∑ t, pB () t = 1 ∧
        termMarginal (fun _ => ()) pF () ≠ ∑ t, pB () t * (pF t / pB () t) := by
  refine ⟨fun _ t => if t then 1 else 0, fun _ => 1 / 2, fun _ => by norm_num,
    by simp only [Fintype.sum_bool]; norm_num, fun t => by cases t <;> norm_num,
    by simp only [Fintype.sum_bool]; norm_num, ?_⟩
  simp only [termMarginal, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  norm_num

end Domination

/-! ### Item (5): the star, where `π(x) ≤ M` fails -/

section Star

/-- **`rem:silva_hypotheses`(5)**: on a star `s_o` with `K ≥ 3` terminal children
(`p_B(τ|x) = 1`, the one-parent kernel `deltaPB`), the uniform forward policy has `M = 1/K`, while
a target with `π(x₀) = ½` at one child has `‖π‖_∞ = ½ > M`. So `π(x) ≤ M` is not implied by the
definition of `M`. -/
theorem star_mVal_lt_piInf {K : ℕ} (hK : 3 ≤ K) {π : Fin K → ℝ} (hπ0 : ∀ x, 0 ≤ π x)
    (hπ1 : ∑ x, π x = 1) {x₀ : Fin K} (hx₀ : π x₀ = 1 / 2)
    (hs : (wSupport (deltaPB (Fin K))).Nonempty) (hX : (univ : Finset (Fin K)).Nonempty) :
    mVal (deltaPB (Fin K)) (fun _ => (K : ℝ)⁻¹) hs = (K : ℝ)⁻¹ ∧
      piInf π hX = 1 / 2 ∧
      mVal (deltaPB (Fin K)) (fun _ => (K : ℝ)⁻¹) hs < piInf π hX := by
  have hM : mVal (deltaPB (Fin K)) (fun _ => (K : ℝ)⁻¹) hs = (K : ℝ)⁻¹ := by
    refine le_antisymm (Finset.sup'_le _ _ fun p hp => ?_) ?_
    · simp only [wSupport, mem_filter, mem_univ, true_and, deltaPB_pos_iff] at hp
      simp only [deltaPB, hp, if_true, div_one, le_refl]
    · have h := ratio_le_mVal (fun _ => (K : ℝ)⁻¹) hs
        (show 0 < deltaPB (Fin K) x₀ x₀ by rw [deltaPB, if_pos rfl]; exact one_pos)
      simpa only [deltaPB, if_true, div_one] using h
  have hP : piInf π hX = 1 / 2 := by
    refine le_antisymm (Finset.sup'_le _ _ fun x _ => ?_) ?_
    · by_cases hx : x = x₀
      · rw [hx, hx₀]
      · have hpair : π x + π x₀ ≤ ∑ y, π y := by
          rw [← Finset.sum_pair hx]
          exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ => hπ0 y
        linarith
    · rw [← hx₀]
      exact Finset.le_sup' π (mem_univ x₀)
  refine ⟨hM, hP, ?_⟩
  rw [hM, hP]
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  rw [inv_lt_comm₀ (by linarith) (by norm_num)]
  linarith

/-- **Inhabitation of `star_mVal_lt_piInf`** (kb 0025): `K = 3` children, `π = (½, ¼, ¼)`, so
`M = 1/3 < ½ = ‖π‖_∞`. -/
theorem inhabit_star :
    ∃ (π : Fin 3 → ℝ) (hs : (wSupport (deltaPB (Fin 3))).Nonempty)
      (hX : (univ : Finset (Fin 3)).Nonempty),
      (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1 ∧ π 0 = 1 / 2 ∧
        mVal (deltaPB (Fin 3)) (fun _ => ((3 : ℕ) : ℝ)⁻¹) hs < piInf π hX := by
  refine ⟨![1/2, 1/4, 1/4], ⟨(0, 0), mem_wSupport (by rw [deltaPB, if_pos rfl]; exact one_pos)⟩,
    univ_nonempty, ?_, ?_, rfl, ?_⟩
  · intro x; fin_cases x <;> norm_num
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]; norm_num
  · refine (star_mVal_lt_piInf le_rfl ?_ ?_ (x₀ := 0) rfl _ _).2.2
    · intro x; fin_cases x <;> norm_num
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]; norm_num

end Star

/-! ## `rem:silva_model_constant` -/

section FixedGraph

variable {X T : Type*} [Fintype X] [Fintype T]

/-- A probability weight is at most `1` pointwise. -/
theorem le_one_of_sum_eq_one {Y : Type*} [Fintype Y] {p : Y → ℝ} (h0 : ∀ y, 0 ≤ p y)
    (h1 : ∑ y, p y = 1) (y : Y) : p y ≤ 1 := by
  rw [← h1]
  exact Finset.single_le_sum (fun y _ => h0 y) (mem_univ y)

/-- **`rem:silva_model_constant`, the fixed-graph bound**: since `p_F(τ) ≤ 1` and `‖π‖_∞ ≤ 1`,
every forward trajectory law has `M' ≤ max(1, max_{τ,x : p_B(τ|x) > 0} 1/p_B(τ|x))`. -/
theorem mPrime_le_fixedGraph (pB : X → T → ℝ) {pF : T → ℝ} {π : X → ℝ}
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty)
    (hF1 : ∀ t, pF t ≤ 1) (hπ1 : ∀ x, π x ≤ 1) :
    mPrime pB pF π hs hX ≤ max 1 ((wSupport pB).sup' hs fun p => 1 / pB p.1 p.2) := by
  refine max_le (Finset.sup'_le _ _ fun p hp => ?_) (Finset.sup'_le _ _ fun x _ => ?_)
  · have hp' : 0 < pB p.1 p.2 := by
      simpa only [wSupport, mem_filter, mem_univ, true_and] using hp
    calc pF p.2 / pB p.1 p.2 ≤ 1 / pB p.1 p.2 := div_le_div_of_nonneg_right (hF1 _) hp'.le
      _ ≤ (wSupport pB).sup' hs (fun p => 1 / pB p.1 p.2) :=
          Finset.le_sup' (fun p : X × T => 1 / pB p.1 p.2) hp
      _ ≤ _ := le_max_right _ _
  · exact (hπ1 x).trans (le_max_left _ _)

/-- The fixed-graph bound for probability laws: `p_F` and `π` nonnegative and summing to `1`. -/
theorem mPrime_le_fixedGraph_of_prob (pB : X → T → ℝ) {pF : T → ℝ} {π : X → ℝ}
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty)
    (hF0 : ∀ t, 0 ≤ pF t) (hF1 : ∑ t, pF t = 1) (hπ0 : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1) :
    mPrime pB pF π hs hX ≤ max 1 ((wSupport pB).sup' hs fun p => 1 / pB p.1 p.2) :=
  mPrime_le_fixedGraph pB hs hX (le_one_of_sum_eq_one hF0 hF1) (le_one_of_sum_eq_one hπ0 hπ1)

omit [Fintype X] in
/-- **`rem:silva_model_constant`, on a tree `p_B(τ|x) = 1`**: when each terminal state has at most
one trajectory (`into` injective) and `p_B(·|x)` is a probability on the trajectories into `x`,
`p_B(τ|x) = 1` on its support. -/
theorem tree_pB_eq_one {into : T → X} (hinj : Function.Injective into) {pB : X → T → ℝ}
    (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (hB1 : ∀ x, ∑ t, pB x t = 1) {x : X} {t : T}
    (ht : 0 < pB x t) : pB x t = 1 := by
  rw [← hB1 x, Finset.sum_eq_single t]
  · intro t' _ ht'
    by_contra hne
    exact ht' (hinj ((hBsupp x t' hne).trans (hBsupp x t ht.ne').symm))
  · intro h
    exact absurd (mem_univ t) h

/-- **`rem:silva_model_constant`, on a tree `M ≤ 1`**. -/
theorem tree_mVal_le_one {into : T → X} (hinj : Function.Injective into) {pB : X → T → ℝ}
    (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (hB1 : ∀ x, ∑ t, pB x t = 1) {pF : T → ℝ}
    (hF1 : ∀ t, pF t ≤ 1) (hs : (wSupport pB).Nonempty) :
    mVal pB pF hs ≤ 1 := by
  refine Finset.sup'_le _ _ fun p hp => ?_
  have hp' : 0 < pB p.1 p.2 := by
    simpa only [wSupport, mem_filter, mem_univ, true_and] using hp
  rw [tree_pB_eq_one hinj hBsupp hB1 hp', div_one]
  exact hF1 _

end FixedGraph

section Ladder

/-- The trajectories of the **ladder graph of depth `n`** into its only terminal state `x`: one
of the two parallel edges at each of the `n` stages. -/
abbrev LadderTraj (n : ℕ) := Fin n → Bool

/-- The uniform backward policy on the ladder: `½` at each of the `n` stages. The terminal type
is `Unit` (the single terminal state `x`). -/
noncomputable def ladderPB (n : ℕ) : Unit → LadderTraj n → ℝ :=
  fun _ _ => ∏ _i : Fin n, (2 : ℝ)⁻¹

/-- The constant `1` on the single terminal state: the ladder's `π(x)` and `p_{E,T}(x)`. -/
noncomputable def ladderOne : Unit → ℝ := fun _ => 1

theorem ladderPB_eq (n : ℕ) (x : Unit) (t : LadderTraj n) :
    ladderPB n x t = ((2 : ℝ) ^ n)⁻¹ := by
  simp only [ladderPB, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]

/-- `x` has `2ⁿ` incoming trajectories. -/
theorem card_ladderTraj (n : ℕ) : Fintype.card (LadderTraj n) = 2 ^ n := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem ladderPB_pos (n : ℕ) (x : Unit) (t : LadderTraj n) : 0 < ladderPB n x t := by
  rw [ladderPB_eq]
  positivity

/-- The uniform backward policy is a probability on the `2ⁿ` trajectories into `x`. -/
theorem ladderPB_sum (n : ℕ) (x : Unit) : ∑ t, ladderPB n x t = 1 := by
  simp only [ladderPB_eq, Finset.sum_const, Finset.card_univ, card_ladderTraj, nsmul_eq_mul]
  push_cast
  field_simp

theorem ladder_wSupport_nonempty (n : ℕ) : (wSupport (ladderPB n)).Nonempty :=
  ⟨((), fun _ => false), mem_wSupport (ladderPB_pos n () _)⟩

theorem unit_univ_nonempty : (univ : Finset Unit).Nonempty := univ_nonempty

/-- `max_{τ,x} 1/p_B(τ|x) = 2ⁿ` on the ladder. -/
theorem ladder_sup_inv_pB (n : ℕ) :
    (wSupport (ladderPB n)).sup' (ladder_wSupport_nonempty n)
      (fun p => 1 / ladderPB n p.1 p.2) = 2 ^ n := by
  refine le_antisymm (Finset.sup'_le _ _ fun p _ => ?_) ?_
  · rw [ladderPB_eq, one_div, inv_inv]
  · have h := Finset.le_sup' (fun p : Unit × LadderTraj n => 1 / ladderPB n p.1 p.2)
      (mem_wSupport (ladderPB_pos n () fun _ => false))
    simpa only [ladderPB_eq, one_div, inv_inv] using h

/-- **`rem:silva_model_constant`, the ladder: `M' ≤ 2ⁿ`** for every forward trajectory law, as
the instance of the fixed-graph bound. -/
theorem ladder_mPrime_le (n : ℕ) {pF : LadderTraj n → ℝ} (hF0 : ∀ t, 0 ≤ pF t)
    (hF1 : ∑ t, pF t = 1) :
    mPrime (ladderPB n) pF ladderOne (ladder_wSupport_nonempty n) unit_univ_nonempty ≤ 2 ^ n := by
  have h := mPrime_le_fixedGraph_of_prob (ladderPB n) (ladder_wSupport_nonempty n)
    unit_univ_nonempty hF0 hF1 (π := ladderOne) (fun _ => zero_le_one)
    (by simp only [ladderOne, Fintype.sum_unique])
  rwa [ladder_sup_inv_pB, max_eq_right (one_le_pow₀ one_le_two)] at h

/-- **`rem:silva_model_constant`, the balanced solution**: `p_F(τ) = π(x) p_B(τ|x)` has
`M = ‖π‖_∞ = 1`. -/
theorem ladder_balanced (n : ℕ) :
    mVal (ladderPB n) (fun t => ladderOne () * ladderPB n () t) (ladder_wSupport_nonempty n) = 1 ∧
      piInf ladderOne unit_univ_nonempty = 1 := by
  refine ⟨le_antisymm (Finset.sup'_le _ _ fun p _ => ?_) ?_, ?_⟩
  · simp only [ladderPB_eq, ladderOne, one_mul]
    rw [div_self (by positivity)]
  · have h := ratio_le_mVal (fun t => ladderOne () * ladderPB n () t)
      (ladder_wSupport_nonempty n) (ladderPB_pos n () fun _ => false)
    rwa [ladderOne, one_mul, div_self (ladderPB_pos n () _).ne'] at h
  · refine le_antisymm (Finset.sup'_le _ _ fun x _ => le_of_eq rfl) ?_
    exact Finset.le_sup' ladderOne (mem_univ ())

/-- **`rem:silva_model_constant`: mass `c` on one trajectory gives `M ≥ c 2ⁿ`**. -/
theorem ladder_mVal_ge {n : ℕ} (pF : LadderTraj n → ℝ) (t₀ : LadderTraj n) :
    pF t₀ * 2 ^ n ≤ mVal (ladderPB n) pF (ladder_wSupport_nonempty n) := by
  have h := ratio_le_mVal pF (ladder_wSupport_nonempty n) (ladderPB_pos n () t₀)
  rwa [ladderPB_eq, div_inv_eq_mul] at h

/-- The residual on the ladder: one term per trajectory, `2⁻ⁿ (log(p_F(τ) 2ⁿ))²`. -/
theorem ladder_residual_eq (n : ℕ) (pF : LadderTraj n → ℝ) :
    residual ladderOne ladderOne (ladderPB n) pF
      = ∑ t, ((2 : ℝ) ^ n)⁻¹ * Real.log (pF t * 2 ^ n) ^ 2 := by
  rw [residual, Fintype.sum_unique]
  simp only [ladderOne, one_mul, logRatio, ladderPB_eq, div_inv_eq_mul]

/-- **`rem:silva_model_constant`: the term of `𝓔` on the concentrated trajectory**,
`p_{E,T}(x) p_B(τ₀|x) (log(p_F(τ₀)/(π(x)p_B(τ₀|x))))² = 2⁻ⁿ (log(c 2ⁿ))²` for `p_F(τ₀) = c`. -/
theorem ladder_term_eq {n : ℕ} (pF : LadderTraj n → ℝ) (t₀ : LadderTraj n) :
    ladderOne () * (ladderPB n () t₀ * logRatio ladderOne (ladderPB n) pF () t₀ ^ 2)
      = ((2 : ℝ) ^ n)⁻¹ * Real.log (pF t₀ * 2 ^ n) ^ 2 := by
  simp only [ladderOne, one_mul, logRatio, ladderPB_eq, div_inv_eq_mul]

/-- **`rem:silva_model_constant`: `2⁻ⁿ (log(c 2ⁿ))² → 0`** as `n → ∞`, for every `c > 0`. -/
theorem tendsto_ladder_term {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * Real.log (c * 2 ^ n) ^ 2) atTop (𝓝 0) := by
  have h : ∀ n : ℕ, ((2 : ℝ) ^ n)⁻¹ * Real.log (c * 2 ^ n) ^ 2
      = Real.log c ^ 2 * ((n : ℝ) ^ 0 / 2 ^ n) + 2 * Real.log c * Real.log 2 * ((n : ℝ) ^ 1 / 2 ^ n)
        + Real.log 2 ^ 2 * ((n : ℝ) ^ 2 / 2 ^ n) := by
    intro n
    rw [Real.log_mul hc.ne' (by positivity), Real.log_pow]
    field_simp
    ring
  simp only [h]
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (one_lt_two (α := ℝ))
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (one_lt_two (α := ℝ))
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two (α := ℝ))
  have := ((h0.const_mul (Real.log c ^ 2)).add (h1.const_mul (2 * Real.log c * Real.log 2))).add
    (h2.const_mul (Real.log 2 ^ 2))
  simpa only [mul_zero, add_zero] using this

end Ladder

section LadderFamily

/-- The trajectory `τ₀` on which the mass is concentrated. -/
def ladderT0 (n : ℕ) : LadderTraj n := fun _ => false

/-- **The trajectory law of `rem:silva_model_constant`**: mass `c` on `τ₀` and the remaining
mass `1 − c` spread uniformly over the other `2ⁿ − 1` trajectories. -/
noncomputable def ladderPFc (n : ℕ) (c : ℝ) : LadderTraj n → ℝ :=
  fun t => if t = ladderT0 n then c else (1 - c) / ((2 : ℝ) ^ n - 1)

theorem two_pow_sub_one_pos {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by
  have : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hn
  linarith

/-- A sum over the ladder's trajectories of a function taking one value on `τ₀` and another
elsewhere. -/
theorem sum_ladder_split (n : ℕ) (a b : ℝ) :
    ∑ t : LadderTraj n, (if t = ladderT0 n then a else b) = a + ((2 : ℝ) ^ n - 1) * b := by
  rw [← Finset.add_sum_erase _ _ (mem_univ (ladderT0 n)), if_pos rfl]
  have h : ∀ t ∈ (univ : Finset (LadderTraj n)).erase (ladderT0 n),
      (if t = ladderT0 n then a else b) = b := fun t ht => if_neg (Finset.ne_of_mem_erase ht)
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_erase_of_mem (mem_univ _),
    Finset.card_univ, card_ladderTraj, nsmul_eq_mul, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring

theorem ladderPFc_pos {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (t : LadderTraj n) : 0 < ladderPFc n c t := by
  simp only [ladderPFc]
  split_ifs
  · exact hc0
  · exact div_pos (by linarith) (two_pow_sub_one_pos hn)

theorem ladderPFc_sum {n : ℕ} (hn : 1 ≤ n) (c : ℝ) : ∑ t, ladderPFc n c t = 1 := by
  simp only [ladderPFc]
  rw [sum_ladder_split]
  field_simp [(two_pow_sub_one_pos hn).ne']
  ring

/-- The residual of the family, in closed form. -/
theorem ladder_residual_ladderPFc (n : ℕ) (c : ℝ) :
    residual ladderOne ladderOne (ladderPB n) (ladderPFc n c)
      = ((2 : ℝ) ^ n)⁻¹ * Real.log (c * 2 ^ n) ^ 2 +
        ((2 : ℝ) ^ n - 1) * (((2 : ℝ) ^ n)⁻¹ *
          Real.log ((1 - c) / ((2 : ℝ) ^ n - 1) * 2 ^ n) ^ 2) := by
  rw [ladder_residual_eq]
  have h : ∀ t : LadderTraj n, ((2 : ℝ) ^ n)⁻¹ * Real.log (ladderPFc n c t * 2 ^ n) ^ 2
      = if t = ladderT0 n then ((2 : ℝ) ^ n)⁻¹ * Real.log (c * 2 ^ n) ^ 2 else
          ((2 : ℝ) ^ n)⁻¹ * Real.log ((1 - c) / ((2 : ℝ) ^ n - 1) * 2 ^ n) ^ 2 := by
    intro t
    simp only [ladderPFc]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun t _ => h t, sum_ladder_split]

/-- **`rem:silva_model_constant`: `𝓔(p_F) → (log(1 − c))²`** along the family, for `0 < c < 1`. -/
theorem tendsto_ladder_residual {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (fun n : ℕ => residual ladderOne ladderOne (ladderPB n) (ladderPFc n c)) atTop
      (𝓝 (Real.log (1 - c) ^ 2)) := by
  simp only [ladder_residual_ladderPFc]
  set u : ℕ → ℝ := fun n => ((2 : ℝ) ^ n)⁻¹ with hu
  have hu0 : Tendsto u atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h1c : (1 : ℝ) - c ≠ 0 := by linarith
  -- the second term, as a continuous function of `u n`
  have hcont : Tendsto (fun n => (1 - u n) * Real.log ((1 - c) / (1 - u n)) ^ 2) atTop
      (𝓝 ((1 - 0) * Real.log ((1 - c) / (1 - 0)) ^ 2)) := by
    have hden : Tendsto (fun n => 1 - u n) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hu0
    have hq : Tendsto (fun n => (1 - c) / (1 - u n)) atTop (𝓝 ((1 - c) / (1 - 0))) :=
      tendsto_const_nhds.div hden (by norm_num)
    have hlog := (Real.continuousAt_log (by rw [sub_zero, div_one]; exact h1c)).tendsto.comp hq
    exact hden.mul (hlog.pow 2)
  simp only [sub_zero, div_one, one_mul] at hcont
  have hsum := (tendsto_ladder_term hc0).add hcont
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have h3 : (2 : ℝ) ^ n - 1 ≠ 0 := (two_pow_sub_one_pos hn).ne'
  have e1 : (1 - c) / ((2 : ℝ) ^ n - 1) * 2 ^ n = (1 - c) / (1 - u n) := by
    simp only [hu]
    field_simp
  have e2 : ((2 : ℝ) ^ n - 1) * ((2 : ℝ) ^ n)⁻¹ = 1 - u n := by
    simp only [hu]
    field_simp
  simp only [e1, ← mul_assoc, e2]

/-- With `c := 1 − e^{−√(ε/2)}`, `(log(1 − c))² = ε/2`. -/
theorem log_one_sub_cEps_sq {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (1 - (1 - Real.exp (-Real.sqrt (ε / 2)))) ^ 2 = ε / 2 := by
  rw [sub_sub_cancel, Real.log_exp, neg_sq, Real.sq_sqrt (by linarith)]

theorem cEps_pos {ε : ℝ} (hε : 0 < ε) : 0 < 1 - Real.exp (-Real.sqrt (ε / 2)) := by
  have : Real.exp (-Real.sqrt (ε / 2)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.sqrt_pos.mpr (by linarith)))
  linarith

theorem cEps_lt_one (ε : ℝ) : 1 - Real.exp (-Real.sqrt (ε / 2)) < 1 := by
  have := Real.exp_pos (-Real.sqrt (ε / 2))
  linarith

/-- **`rem:silva_model_constant`: `𝓔(p_F) → ε/2`** for `c := 1 − e^{−√(ε/2)}`. -/
theorem tendsto_ladder_residual_eps {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => residual ladderOne ladderOne (ladderPB n)
      (ladderPFc n (1 - Real.exp (-Real.sqrt (ε / 2))))) atTop (𝓝 (ε / 2)) := by
  have h := tendsto_ladder_residual (cEps_pos hε) (cEps_lt_one ε)
  rwa [log_one_sub_cEps_sq hε.le] at h

/-- **`rem:silva_model_constant`, the display**: for every `ε > 0` and every `n` large enough
there is a full-support trajectory law on the ladder with `𝓔(p_F) ≤ ε` and
`M' ≥ (1 − e^{−√(ε/2)}) 2ⁿ`. -/
theorem ladder_witness {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ pF : LadderTraj n → ℝ, (∀ t, 0 < pF t) ∧ ∑ t, pF t = 1 ∧
      residual ladderOne ladderOne (ladderPB n) pF ≤ ε ∧
      (1 - Real.exp (-Real.sqrt (ε / 2))) * 2 ^ n ≤
        mPrime (ladderPB n) pF ladderOne (ladder_wSupport_nonempty n) unit_univ_nonempty := by
  have hlt : ∀ᶠ n in atTop, residual ladderOne ladderOne (ladderPB n)
      (ladderPFc n (1 - Real.exp (-Real.sqrt (ε / 2)))) < ε :=
    (tendsto_ladder_residual_eps hε).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hlt, eventually_ge_atTop 1] with n hn h1
  refine ⟨ladderPFc n (1 - Real.exp (-Real.sqrt (ε / 2))),
    ladderPFc_pos h1 (cEps_pos hε) (cEps_lt_one ε), ladderPFc_sum h1 _, hn.le, ?_⟩
  refine le_trans ?_ (mVal_le_mPrime _ _ _ _ _)
  have h := ladder_mVal_ge (ladderPFc n (1 - Real.exp (-Real.sqrt (ε / 2)))) (ladderT0 n)
  simpa only [ladderPFc, if_true] using h

/-- On the ladder a trajectory law with finite residual has no zero: `p_B > 0` on every trajectory
and `p_{E,T}(x) = 1`, so a zero of `p_F` makes `𝓔 = +∞` (`rem:silva_hypotheses`(2)). The suprema
below run over full-support laws, and this is why that restriction loses nothing on
`{𝓔 ≤ ε}`. -/
theorem ladder_pF_ne_zero_of_residualE_ne_top {n : ℕ} {pF : LadderTraj n → ℝ}
    (h : residualE ladderOne ladderOne (ladderPB n) pF ≠ ⊤) (t : LadderTraj n) : pF t ≠ 0 :=
  fun h0 => h (residualE_eq_top_of_pF_zero (x₀ := ()) (show (0 : ℝ) < 1 from one_pos)
    (ladderPB_pos n () t) h0)

/-- **`rem:silva_model_constant`, the display in the paper's supremum form**:
`sup{M'(p_F) : 𝓔(p_F) ≤ ε} ≥ (1 − e^{−√(ε/2)}) 2ⁿ` for `n` large, the supremum over full-support
trajectory laws on the ladder (bounded above by `2ⁿ`, `ladder_mPrime_le`). -/
theorem ladder_sSup_ge {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (1 - Real.exp (-Real.sqrt (ε / 2))) * 2 ^ n ≤
      sSup {m : ℝ | ∃ pF : LadderTraj n → ℝ, (∀ t, 0 < pF t) ∧ ∑ t, pF t = 1 ∧
        residual ladderOne ladderOne (ladderPB n) pF ≤ ε ∧
        m = mPrime (ladderPB n) pF ladderOne (ladder_wSupport_nonempty n) unit_univ_nonempty} := by
  filter_upwards [ladder_witness hε] with n ⟨pF, hpos, hsum, hres, hge⟩
  refine le_csSup_of_le ⟨2 ^ n, ?_⟩ ⟨pF, hpos, hsum, hres, rfl⟩ hge
  rintro m ⟨pF', hpos', hsum', -, rfl⟩
  exact ladder_mPrime_le n (fun t => (hpos' t).le) hsum'

/-- **`rem:silva_model_constant`, "no constant is uniform in the depth"**: for every `ε > 0` no
`C` bounds `M'` over all depths `n` and all full-support trajectory laws with `𝓔(p_F) ≤ ε`. -/
theorem ladder_no_uniform_constant {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ C : ℝ, ∀ (n : ℕ) (pF : LadderTraj n → ℝ), (∀ t, 0 < pF t) → ∑ t, pF t = 1 →
      residual ladderOne ladderOne (ladderPB n) pF ≤ ε →
      mPrime (ladderPB n) pF ladderOne (ladder_wSupport_nonempty n) unit_univ_nonempty ≤ C := by
  rintro ⟨C, hC⟩
  have hgrow : Tendsto (fun n : ℕ => (1 - Real.exp (-Real.sqrt (ε / 2))) * (2 : ℝ) ^ n) atTop
      atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).const_mul_atTop (cEps_pos hε)
  obtain ⟨n, ⟨pF, hpos, hsum, hres, hge⟩, hbig⟩ :=
    ((ladder_witness hε).and (hgrow.eventually_gt_atTop C)).exists
  linarith [hC n pF hpos hsum hres]

/-- **`rem:silva_model_constant`, "`M` can exceed `1`"** on a graph with several backward paths
into a terminal state: the depth-`1` ladder with mass `¾` on one of its two trajectories has
`M ≥ 3/2`, while `M' ≤ 2 = max(1, 1/min p_B)`. -/
theorem ladder_mVal_exceeds_one :
    ∃ pF : LadderTraj 1 → ℝ, (∀ t, 0 < pF t) ∧ ∑ t, pF t = 1 ∧
      1 < mVal (ladderPB 1) pF (ladder_wSupport_nonempty 1) ∧
      mPrime (ladderPB 1) pF ladderOne (ladder_wSupport_nonempty 1) unit_univ_nonempty ≤ 2 := by
  refine ⟨ladderPFc 1 (3 / 4), ladderPFc_pos le_rfl (by norm_num) (by norm_num),
    ladderPFc_sum le_rfl _, ?_, ?_⟩
  · have h := ladder_mVal_ge (ladderPFc 1 (3 / 4)) (ladderT0 1)
    simp only [ladderPFc, if_true] at h
    linarith
  · have h := ladder_mPrime_le 1 (pF := ladderPFc 1 (3 / 4))
      (fun t => (ladderPFc_pos le_rfl (by norm_num) (by norm_num) t).le) (ladderPFc_sum le_rfl _)
    simpa only [pow_one] using h

end LadderFamily

/-! ## `rem:path_space` -/

section PathCount

variable {X T : Type*} [Fintype X] [Fintype T] [DecidableEq X]

/-- `P(x)`, the number of trajectories into `x`. -/
noncomputable def pathCount (into : T → X) (x : X) : ℕ :=
  (univ.filter fun t => into t = x).card

omit [Fintype X] in
/-- **`rem:path_space`, `min_τ p_B(τ|x) ≤ 1/P(x)`**: a probability `p_B(·|x)` charging each of the
`P(x)` trajectories into `x` (and nothing else) gives one of them mass at most `1/P(x)`. -/
theorem exists_pB_le_inv_pathCount (into : T → X) {pB : X → T → ℝ} {x : X}
    (hBsupp : ∀ t, pB x t ≠ 0 → into t = x) (hB1 : ∑ t, pB x t = 1) :
    0 < pathCount into x ∧ ∃ t, into t = x ∧ pB x t ≤ 1 / (pathCount into x : ℝ) := by
  classical
  set s := univ.filter fun t => into t = x with hsdef
  have hsum : ∑ t ∈ s, pB x t = 1 := by
    rw [← hB1, hsdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (hBsupp t (Ne.symm hne))
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hP : 0 < pathCount into x := Finset.card_pos.mpr hne
  refine ⟨hP, ?_⟩
  by_contra hcon
  push Not at hcon
  have hlt : ∑ t ∈ s, (1 / (pathCount into x : ℝ)) < ∑ t ∈ s, pB x t :=
    Finset.sum_lt_sum_of_nonempty hne fun t ht => by
      simp only [hsdef, mem_filter, mem_univ, true_and] at ht
      exact hcon t ht
  rw [Finset.sum_const, nsmul_eq_mul, hsum] at hlt
  have hPr : (0 : ℝ) < (pathCount into x : ℝ) := Nat.cast_pos.mpr hP
  have : (s.card : ℝ) * (1 / (pathCount into x : ℝ)) = 1 := by
    rw [pathCount, ← hsdef] at hPr ⊢
    field_simp
  linarith

/-- **`rem:path_space`, `1/w_min ≥ P(x)/p_{E,T}(x)` for every `x`**, for a full-support backward
policy and a full-support training law. -/
theorem pathCount_div_le_inv_wMin (into : T → X) {pET : X → ℝ} {pB : X → T → ℝ}
    (hs : (wSupport pB).Nonempty) (hET : ∀ x, 0 < pET x)
    (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (hBpos : ∀ x t, into t = x → 0 < pB x t)
    (hB1 : ∀ x, ∑ t, pB x t = 1) (x : X) :
    (pathCount into x : ℝ) / pET x ≤ 1 / wMin pET pB hs := by
  obtain ⟨hP, t, hin, hle⟩ := exists_pB_le_inv_pathCount into (hBsupp x) (hB1 x)
  have hPr : (0 : ℝ) < (pathCount into x : ℝ) := Nat.cast_pos.mpr hP
  have hw : wMin pET pB hs ≤ pET x / (pathCount into x : ℝ) :=
    calc wMin pET pB hs ≤ pET x * pB x t := wMin_le hs (hBpos x t hin)
      _ ≤ pET x * (1 / (pathCount into x : ℝ)) := mul_le_mul_of_nonneg_left hle (hET x).le
      _ = pET x / (pathCount into x : ℝ) := by ring
  have h := one_div_le_one_div_of_le (wMin_pos hs hET) hw
  rwa [one_div_div] at h

/-- **`rem:path_space`, the display**: `1/w_min ≥ max_x P(x)/p_{E,T}(x)`. -/
theorem sup_pathCount_div_le_inv_wMin (into : T → X) {pET : X → ℝ} {pB : X → T → ℝ}
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty) (hET : ∀ x, 0 < pET x)
    (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (hBpos : ∀ x t, into t = x → 0 < pB x t)
    (hB1 : ∀ x, ∑ t, pB x t = 1) :
    univ.sup' hX (fun x => (pathCount into x : ℝ) / pET x) ≤ 1 / wMin pET pB hs :=
  Finset.sup'_le _ _ fun x _ =>
    pathCount_div_le_inv_wMin into hs hET hBsupp hBpos hB1 x

omit [DecidableEq X] in
/-- The `M'` values are bounded above over forward trajectory laws with `p_F ≤ 1`, by
`max(max 1/p_B, ‖π‖_∞)` — so the suprema below are suprema of bounded sets. -/
theorem mPrime_le_of_le_one (pB : X → T → ℝ) {pF : T → ℝ} (π : X → ℝ)
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty) (hF1 : ∀ t, pF t ≤ 1) :
    mPrime pB pF π hs hX ≤
      max ((wSupport pB).sup' hs fun p => 1 / pB p.1 p.2) (piInf π hX) := by
  refine max_le_max (Finset.sup'_le _ _ fun p hp => ?_) le_rfl
  have hp' : 0 < pB p.1 p.2 := by
    simpa only [wSupport, mem_filter, mem_univ, true_and] using hp
  exact (div_le_div_of_nonneg_right (hF1 _) hp'.le).trans
    (Finset.le_sup' (fun p : X × T => 1 / pB p.1 p.2) hp)

/-- From `(1 − η)^L P ≤ S` for every `η ∈ (0,1)`, `P ≤ S`. -/
theorem le_of_forall_one_sub_pow_mul_le {P S : ℝ} (L : ℕ)
    (h : ∀ η : ℝ, 0 < η → η < 1 → (1 - η) ^ L * P ≤ S) : P ≤ S := by
  have hcont : Tendsto (fun η : ℝ => (1 - η) ^ L * P) (𝓝[>] 0) (𝓝 ((1 - 0) ^ L * P)) :=
    ((((continuous_const.sub continuous_id).pow L).mul continuous_const).tendsto 0).mono_left
      nhdsWithin_le_nhds
  rw [sub_zero, one_pow, one_mul] at hcont
  refine le_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with η hη
  exact h η hη.1 hη.2

/-- **`rem:path_space`, `sup_{p_F} M' ≥ P(x)`**, the supremum over full-support forward
**trajectory laws** (see SCOPE; the Markov form is `pathCount_le_sSup_mPrime_markov`). -/
theorem pathCount_le_sSup_mPrime [Nonempty T] (into : T → X) {pB : X → T → ℝ} (π : X → ℝ)
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty)
    (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (hBpos : ∀ x t, into t = x → 0 < pB x t)
    (hB1 : ∀ x, ∑ t, pB x t = 1) (x : X) :
    (pathCount into x : ℝ) ≤ sSup {m : ℝ | ∃ pF : T → ℝ, (∀ t, 0 < pF t) ∧ ∑ t, pF t = 1 ∧
      m = mPrime pB pF π hs hX} := by
  classical
  obtain ⟨hP, t₀, hin, hle⟩ := exists_pB_le_inv_pathCount into (hBsupp x) (hB1 x)
  have hPr : (0 : ℝ) < (pathCount into x : ℝ) := Nat.cast_pos.mpr hP
  have hB0 : 0 < pB x t₀ := hBpos x t₀ hin
  have hbdd : BddAbove {m : ℝ | ∃ pF : T → ℝ, (∀ t, 0 < pF t) ∧ ∑ t, pF t = 1 ∧
      m = mPrime pB pF π hs hX} := by
    refine ⟨max ((wSupport pB).sup' hs fun p => 1 / pB p.1 p.2) (piInf π hX), ?_⟩
    rintro m ⟨pF, hpos, hsum, rfl⟩
    exact mPrime_le_of_le_one pB π hs hX
      (le_one_of_sum_eq_one (fun t => (hpos t).le) hsum)
  have hcard : (0 : ℝ) < (Fintype.card T : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine le_of_forall_one_sub_pow_mul_le 1 fun η hη0 hη1 => ?_
  rw [pow_one]
  set pF : T → ℝ := fun t => (1 - η) * (if t = t₀ then 1 else 0) + η / (Fintype.card T : ℝ)
    with hpF
  have hpos : ∀ t, 0 < pF t := fun t => by
    simp only [hpF]
    have : 0 ≤ (1 - η) * (if t = t₀ then (1 : ℝ) else 0) :=
      mul_nonneg (by linarith) (by split_ifs <;> norm_num)
    have : 0 < η / (Fintype.card T : ℝ) := div_pos hη0 hcard
    linarith
  have hsum : ∑ t, pF t = 1 := by
    simp only [hpF, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  refine le_csSup_of_le hbdd ⟨pF, hpos, hsum, rfl⟩ ?_
  refine le_trans ?_ (mVal_le_mPrime _ _ _ _ _)
  refine le_trans ?_ (ratio_le_mVal pF hs hB0)
  have hpF0 : (1 - η) ≤ pF t₀ := by
    simp only [hpF, if_true, mul_one]
    have : 0 < η / (Fintype.card T : ℝ) := div_pos hη0 hcard
    linarith
  have hinv : (pathCount into x : ℝ) ≤ 1 / pB x t₀ := by
    rw [le_div_iff₀ hB0]
    rw [le_div_iff₀ hPr] at hle
    linarith
  calc (1 - η) * (pathCount into x : ℝ) ≤ (1 - η) * (1 / pB x t₀) :=
        mul_le_mul_of_nonneg_left hinv (by linarith)
    _ = (1 - η) / pB x t₀ := by ring
    _ ≤ pF t₀ / pB x t₀ := div_le_div_of_nonneg_right hpF0 hB0.le

/-- **`rem:path_space`, `sup_{p_F} M' ≥ max_x P(x)`** over full-support trajectory laws. -/
theorem sup_pathCount_le_sSup_mPrime [Nonempty T] (into : T → X) {pB : X → T → ℝ} (π : X → ℝ)
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty)
    (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (hBpos : ∀ x t, into t = x → 0 < pB x t)
    (hB1 : ∀ x, ∑ t, pB x t = 1) :
    univ.sup' hX (fun x => (pathCount into x : ℝ)) ≤
      sSup {m : ℝ | ∃ pF : T → ℝ, (∀ t, 0 < pF t) ∧ ∑ t, pF t = 1 ∧
        m = mPrime pB pF π hs hX} :=
  Finset.sup'_le _ _ fun x _ => pathCount_le_sSup_mPrime into π hs hX hBsupp hBpos hB1 x

end PathCount

section Markov

variable {S : Type*} [DecidableEq S]

/-- The state following `s` on the path `l`, if any. -/
def nextOn : List S → S → Option S
  | [], _ => none
  | [_], _ => none
  | a :: b :: l, s => if s = a then some b else nextOn (b :: l) s

/-- The probability a forward policy `pol` assigns to a path `s₀ → s₁ → ⋯ → s_n`: the product
over its steps of `pol(s_i → s_{i+1})`. For a Markov forward policy this is `p_F(τ)`. -/
noncomputable def pathProb (pol : S → S → ℝ) : List S → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: l => pol a b * pathProb pol (b :: l)

omit [DecidableEq S] in
/-- A step of a stochastic, positive policy along an edge has probability at most `1`. -/
theorem pol_le_one {succ : S → Finset S} {pol : S → S → ℝ}
    (hpos : ∀ s, ∀ s' ∈ succ s, 0 < pol s s')
    (hsum : ∀ s, (succ s).Nonempty → ∑ s' ∈ succ s, pol s s' = 1) {s s' : S}
    (h : s' ∈ succ s) : pol s s' ≤ 1 := by
  rw [← hsum s ⟨s', h⟩]
  exact Finset.single_le_sum (fun y hy => (hpos s y hy).le) h

omit [DecidableEq S] in
theorem pathProb_mem_Icc {succ : S → Finset S} {pol : S → S → ℝ}
    (hpos : ∀ s, ∀ s' ∈ succ s, 0 < pol s s')
    (hsum : ∀ s, (succ s).Nonempty → ∑ s' ∈ succ s, pol s s' = 1) :
    ∀ l : List S, l.IsChain (fun a b => b ∈ succ a) → 0 ≤ pathProb pol l ∧ pathProb pol l ≤ 1
  | [], _ => by simp only [pathProb]; norm_num
  | [_], _ => by simp only [pathProb]; norm_num
  | a :: b :: l, h => by
      rw [List.isChain_cons_cons] at h
      obtain ⟨h0, h1⟩ := pathProb_mem_Icc hpos hsum (b :: l) h.2
      simp only [pathProb]
      exact ⟨mul_nonneg (hpos a b h.1).le h0,
        mul_le_one₀ (pol_le_one hpos hsum h.1) h0 h1⟩

theorem nextOn_rel {R : S → S → Prop} :
    ∀ {l : List S} {s b : S}, l.IsChain R → nextOn l s = some b → R s b
  | [], _, _, _, h => by simp only [nextOn, reduceCtorEq] at h
  | [_], _, _, _, h => by simp only [nextOn, reduceCtorEq] at h
  | a :: c :: l, s, b, hc, h => by
      rw [List.isChain_cons_cons] at hc
      simp only [nextOn] at h
      split_ifs at h with hsa
      · obtain rfl := Option.some.inj h
        rw [hsa]
        exact hc.1
      · exact nextOn_rel hc.2 h

/-- On a path visiting each state at most once, the state after `a` is `b` whenever `a, b` are
consecutive on it. -/
theorem nextOn_of_infix :
    ∀ {l : List S} {a b : S}, l.Nodup → [a, b] <:+: l → nextOn l a = some b
  | [], _, _, _, h => absurd h.length_le (by simp only [List.length_cons, List.length_nil]; omega)
  | [_], _, _, _, h => absurd h.length_le (by simp only [List.length_cons, List.length_nil]; omega)
  | c :: d :: l, a, b, hnd, h => by
      simp only [nextOn]
      rw [List.infix_cons_iff] at h
      rcases h with hpre | hinf
      · rw [List.cons_prefix_cons] at hpre
        obtain ⟨rfl, hpre'⟩ := hpre
        rw [List.cons_prefix_cons] at hpre'
        obtain ⟨rfl, -⟩ := hpre'
        simp only [if_true]
      · have hac : a ≠ c := by
          rintro rfl
          exact (List.nodup_cons.mp hnd).1 (hinf.subset List.mem_cons_self)
        rw [if_neg hac]
        exact nextOn_of_infix hnd.of_cons hinf

/-- **The policy concentrated on a path `l`**: at a state of `l` it follows `l` with probability
`1 − η` and spreads `η` uniformly over the successors; elsewhere it is uniform. -/
noncomputable def concPolicy (succ : S → Finset S) (l : List S) (η : ℝ) (s s' : S) : ℝ :=
  match nextOn l s with
  | some b => (1 - η) * (if s' = b then 1 else 0) + η / ((succ s).card : ℝ)
  | none => 1 / ((succ s).card : ℝ)

theorem concPolicy_pos (succ : S → Finset S) (l : List S) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (s : S) : ∀ s' ∈ succ s, 0 < concPolicy succ l η s s' := by
  intro s' hs'
  have hc : (0 : ℝ) < ((succ s).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨s', hs'⟩)
  unfold concPolicy
  split
  · rename_i b _
    have : 0 ≤ (1 - η) * (if s' = b then (1 : ℝ) else 0) :=
      mul_nonneg (by linarith) (by split_ifs <;> norm_num)
    have : 0 < η / ((succ s).card : ℝ) := div_pos hη0 hc
    linarith
  · exact div_pos one_pos hc

theorem concPolicy_sum (succ : S → Finset S) {l : List S}
    (hl : l.IsChain (fun a b => b ∈ succ a)) (η : ℝ) (s : S) (hs : (succ s).Nonempty) :
    ∑ s' ∈ succ s, concPolicy succ l η s s' = 1 := by
  have hc : ((succ s).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hs).ne'
  unfold concPolicy
  split
  · rename_i b hb
    have hmem : b ∈ succ s := nextOn_rel hl hb
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', if_pos hmem,
      Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring
  · rw [Finset.sum_const, nsmul_eq_mul]
    field_simp

/-- Along its own path the concentrated policy has probability at least `(1 − η)^{#steps}`. -/
theorem pathProb_concPolicy_ge (succ : S → Finset S) {l : List S} (hnd : l.Nodup) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∀ m : List S, m <:+: l → (1 - η) ^ (m.length - 1) ≤ pathProb (concPolicy succ l η) m
  | [], _ => by simp only [pathProb, List.length_nil, zero_tsub, pow_zero, le_refl]
  | [_], _ => by simp only [pathProb, List.length_singleton, tsub_self, pow_zero, le_refl]
  | a :: b :: r, hm => by
      have hab : nextOn l a = some b :=
        nextOn_of_infix hnd ((List.prefix_append [a, b] r).isInfix.trans hm)
      have hpol : 1 - η ≤ concPolicy succ l η a b := by
        have : 0 ≤ η / ((succ a).card : ℝ) := div_nonneg hη0 (Nat.cast_nonneg _)
        simp only [concPolicy, hab, if_true, mul_one]
        linarith
      have ih := pathProb_concPolicy_ge succ hnd hη0 hη1 (b :: r)
        ((List.suffix_cons a (b :: r)).isInfix.trans hm)
      simp only [List.length_cons, add_tsub_cancel_right] at ih ⊢
      simp only [pathProb]
      rw [pow_succ']
      exact mul_le_mul hpol ih (pow_nonneg (by linarith) _) (le_trans (by linarith) hpol)

/-- **`rem:path_space`, `sup_{p_F} M' ≥ P(x)` over full-support Markov forward policies.**
Trajectories `t` are paths `path t` of a graph with successor sets `succ`, each visiting a state
at most once (as on a DAG), and a Markov policy `pol` — positive on every edge, a probability on
the successors of every non-sink state — gives `p_F(t) = pathProb pol (path t)`. -/
theorem pathCount_le_sSup_mPrime_markov {X T : Type*} [Fintype X] [Fintype T] [DecidableEq X]
    (succ : S → Finset S) (path : T → List S)
    (hchain : ∀ t, (path t).IsChain (fun a b => b ∈ succ a)) (hnodup : ∀ t, (path t).Nodup)
    (into : T → X) {pB : X → T → ℝ} (π : X → ℝ)
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty)
    (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (hBpos : ∀ x t, into t = x → 0 < pB x t)
    (hB1 : ∀ x, ∑ t, pB x t = 1) (x : X) :
    (pathCount into x : ℝ) ≤ sSup {m : ℝ | ∃ pol : S → S → ℝ,
      (∀ s, ∀ s' ∈ succ s, 0 < pol s s') ∧
      (∀ s, (succ s).Nonempty → ∑ s' ∈ succ s, pol s s' = 1) ∧
      m = mPrime pB (fun t => pathProb pol (path t)) π hs hX} := by
  obtain ⟨hP, t₀, hin, hle⟩ := exists_pB_le_inv_pathCount into (hBsupp x) (hB1 x)
  have hPr : (0 : ℝ) < (pathCount into x : ℝ) := Nat.cast_pos.mpr hP
  have hB0 : 0 < pB x t₀ := hBpos x t₀ hin
  have hbdd : BddAbove {m : ℝ | ∃ pol : S → S → ℝ,
      (∀ s, ∀ s' ∈ succ s, 0 < pol s s') ∧
      (∀ s, (succ s).Nonempty → ∑ s' ∈ succ s, pol s s' = 1) ∧
      m = mPrime pB (fun t => pathProb pol (path t)) π hs hX} := by
    refine ⟨max ((wSupport pB).sup' hs fun p => 1 / pB p.1 p.2) (piInf π hX), ?_⟩
    rintro m ⟨pol, hpos, hsum, rfl⟩
    exact mPrime_le_of_le_one pB π hs hX fun t =>
      (pathProb_mem_Icc hpos hsum (path t) (hchain t)).2
  have hinv : (pathCount into x : ℝ) ≤ 1 / pB x t₀ := by
    rw [le_div_iff₀ hB0]
    rw [le_div_iff₀ hPr] at hle
    linarith
  refine le_of_forall_one_sub_pow_mul_le ((path t₀).length - 1) fun η hη0 hη1 => ?_
  set pol := concPolicy succ (path t₀) η with hpol
  refine le_csSup_of_le hbdd ⟨pol, concPolicy_pos succ _ hη0 hη1.le,
    concPolicy_sum succ (hchain t₀) η, rfl⟩ ?_
  refine le_trans ?_ (mVal_le_mPrime _ _ _ _ _)
  refine le_trans ?_ (ratio_le_mVal (fun t => pathProb pol (path t)) hs hB0)
  have hge := pathProb_concPolicy_ge succ (hnodup t₀) hη0.le hη1.le (path t₀)
    (List.infix_refl _)
  have hpow : 0 ≤ (1 - η) ^ ((path t₀).length - 1) := pow_nonneg (by linarith) _
  calc (1 - η) ^ ((path t₀).length - 1) * (pathCount into x : ℝ)
      ≤ (1 - η) ^ ((path t₀).length - 1) * (1 / pB x t₀) := mul_le_mul_of_nonneg_left hinv hpow
    _ = (1 - η) ^ ((path t₀).length - 1) / pB x t₀ := by ring
    _ ≤ pathProb pol (path t₀) / pB x t₀ := div_le_div_of_nonneg_right hge hB0.le

/-- **`rem:path_space`, `sup_{p_F} M' ≥ max_x P(x)`** over full-support Markov forward policies. -/
theorem sup_pathCount_le_sSup_mPrime_markov {X T : Type*} [Fintype X] [Fintype T]
    [DecidableEq X] (succ : S → Finset S) (path : T → List S)
    (hchain : ∀ t, (path t).IsChain (fun a b => b ∈ succ a)) (hnodup : ∀ t, (path t).Nodup)
    (into : T → X) {pB : X → T → ℝ} (π : X → ℝ)
    (hs : (wSupport pB).Nonempty) (hX : (univ : Finset X).Nonempty)
    (hBsupp : ∀ x t, pB x t ≠ 0 → into t = x) (hBpos : ∀ x t, into t = x → 0 < pB x t)
    (hB1 : ∀ x, ∑ t, pB x t = 1) :
    univ.sup' hX (fun x => (pathCount into x : ℝ)) ≤ sSup {m : ℝ | ∃ pol : S → S → ℝ,
      (∀ s, ∀ s' ∈ succ s, 0 < pol s s') ∧
      (∀ s, (succ s).Nonempty → ∑ s' ∈ succ s, pol s s' = 1) ∧
      m = mPrime pB (fun t => pathProb pol (path t)) π hs hX} :=
  Finset.sup'_le _ _ fun x _ => pathCount_le_sSup_mPrime_markov succ path hchain hnodup into π
    hs hX hBsupp hBpos hB1 x

end Markov

section Cycle

variable {S : Type*}

/-- The walks from `s₀` to `x` in the graph with edge relation `E`: the trajectories into `x`. -/
def walksInto (E : S → S → Prop) (s₀ x : S) : Set (List S) :=
  {l | l.head? = some s₀ ∧ l.getLast? = some x ∧ l.IsChain E}

/-- `w₂` with the cycle `c` (a closed walk from `v`) inserted `k` times after `v`. -/
def pumpRest (c w₂ : List S) (k : ℕ) : List S := (List.replicate k c).flatten ++ w₂

theorem pumpRest_succ (c w₂ : List S) (k : ℕ) :
    pumpRest c w₂ (k + 1) = c ++ pumpRest c w₂ k := by
  simp only [pumpRest, List.replicate_succ, List.flatten_cons, List.append_assoc]

theorem length_pumpRest (c w₂ : List S) (k : ℕ) :
    (pumpRest c w₂ k).length = k * c.length + w₂.length := by
  induction k with
  | zero => simp only [pumpRest, List.replicate_zero, List.flatten_nil, List.nil_append,
      zero_mul, zero_add]
  | succ k ih => rw [pumpRest_succ, List.length_append, ih]; ring

theorem getLast?_cons_self_of {v : S} {c : List S} (hc : c.getLast? = some v) :
    (v :: c).getLast? = some v := by
  rw [List.getLast?_cons, hc]
  rfl

theorem isChain_pumpRest {E : S → S → Prop} {v : S} {c w₂ : List S}
    (hcE : (v :: c).IsChain E) (hc : c.getLast? = some v) (hw₂ : (v :: w₂).IsChain E) :
    ∀ k, (v :: pumpRest c w₂ k).IsChain E
  | 0 => by simpa only [pumpRest, List.replicate_zero, List.flatten_nil, List.nil_append]
      using hw₂
  | k + 1 => by
      have ih := isChain_pumpRest hcE hc hw₂ k
      rw [pumpRest_succ, ← List.cons_append]
      refine hcE.append ih.tail fun a ha b hb => ?_
      rw [getLast?_cons_self_of hc, Option.mem_def, Option.some.injEq] at ha
      subst ha
      exact ih.rel_head? hb

theorem getLast?_pumpRest {v : S} {c w₂ : List S} (hc : c.getLast? = some v) :
    ∀ k, (v :: pumpRest c w₂ k).getLast? = (v :: w₂).getLast?
  | 0 => by simp only [pumpRest, List.replicate_zero, List.flatten_nil, List.nil_append]
  | k + 1 => by
      have ih := getLast?_pumpRest (w₂ := w₂) hc k
      rw [pumpRest_succ, ← List.cons_append, List.getLast?_append, getLast?_cons_self_of hc,
        ← ih, ← List.singleton_append, List.getLast?_append]
      rfl

/-- **`rem:path_space`, "when a cycle lies on the trajectories into `x`, these are infinitely
many"**: if a walk from `s₀` to `x` visits a state `v` that lies on a cycle (a nonempty closed
walk `v → ⋯ → v`), the walks from `s₀` to `x` form an infinite set. -/
theorem walksInto_infinite {E : S → S → Prop} {s₀ x v : S} {w : List S}
    (hw : w ∈ walksInto E s₀ x) (hv : v ∈ w) {c : List S} (hcne : c ≠ [])
    (hcE : (v :: c).IsChain E) (hc : c.getLast? = some v) :
    (walksInto E s₀ x).Infinite := by
  obtain ⟨w₁, w₂, rfl⟩ := List.mem_iff_append.mp hv
  obtain ⟨hhead, hlast, hchain⟩ := hw
  have hsplit := List.isChain_split.mp hchain
  refine Set.infinite_of_injective_forall_mem (f := fun k => w₁ ++ v :: pumpRest c w₂ k) ?_ ?_
  · intro k k' hkk
    have hlen := congrArg List.length hkk
    simp only [List.length_append, List.length_cons, length_pumpRest] at hlen
    have hcl : 0 < c.length := List.length_pos_iff.mpr hcne
    have : k * c.length = k' * c.length := by omega
    exact (Nat.mul_left_inj hcl.ne').mp this
  · intro k
    refine ⟨?_, ?_, ?_⟩
    · rw [List.head?_append] at hhead ⊢
      simpa only [List.head?_cons] using hhead
    · rw [List.getLast?_append] at hlast ⊢
      rw [getLast?_pumpRest hc]
      exact hlast
    · exact List.isChain_split.mpr ⟨hsplit.1, isChain_pumpRest hcE hc hsplit.2 k⟩

/-- **`rem:path_space`, `inf_τ p_B(τ|x) = 0`**: a summable nonnegative family on an infinite index
set — in particular a probability `p_B(·|x)` on infinitely many trajectories — has infimum `0`. -/
theorem iInf_eq_zero_of_summable {ι : Type*} [Infinite ι] {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) : ⨅ i, p i = 0 := by
  refine le_antisymm ?_ (le_ciInf hp)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨i, hi⟩ := (hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)).exists
  rw [zero_add]
  exact lt_of_le_of_lt (ciInf_le ⟨0, Set.forall_mem_range.mpr hp⟩ i) hi

/-- **`rem:path_space`, the two combined**: on a graph where a cycle lies on a walk into `x`,
every probability `p_B(·|x)` on the walks into `x` has `inf_τ p_B(τ|x) = 0`. -/
theorem iInf_pB_walksInto_eq_zero {E : S → S → Prop} {s₀ x v : S} {w : List S}
    (hw : w ∈ walksInto E s₀ x) (hv : v ∈ w) {c : List S} (hcne : c ≠ [])
    (hcE : (v :: c).IsChain E) (hc : c.getLast? = some v)
    {pB : walksInto E s₀ x → ℝ} (hB0 : ∀ τ, 0 ≤ pB τ) (hB1 : HasSum pB 1) :
    ⨅ τ, pB τ = 0 := by
  haveI := (walksInto_infinite hw hv hcne hcE hc).to_subtype
  exact iInf_eq_zero_of_summable hB0 hB1.summable

/-- **`rem:path_space`, `sup_{p_F} M' = +∞`**: when `p_B(·|x)` charges infinitely many
trajectories, for every `R` some full-support trajectory law `p_F` has a ratio
`p_F(τ)/p_B(τ|x) > R` at a charged `τ` — so `M' ≥ M > R`. `ν` is any full-support probability
on the trajectories (for instance `p_B(·|x)` itself when every trajectory runs into `x`). -/
theorem exists_ratio_gt {ι : Type*} {pB : ι → ℝ} (hB0 : ∀ i, 0 ≤ pB i) (hBs : Summable pB)
    (hinf : {i | 0 < pB i}.Infinite) {ν : ι → ℝ} (hν0 : ∀ i, 0 < ν i) (hν1 : HasSum ν 1)
    (R : ℝ) :
    ∃ pF : ι → ℝ, (∀ i, 0 < pF i) ∧ HasSum pF 1 ∧ ∃ i, 0 < pB i ∧ R < pF i / pB i := by
  classical
  haveI := hinf.to_subtype
  have hsub : Summable fun i : {i | 0 < pB i} => pB i := hBs.subtype _
  have hε : (0 : ℝ) < 1 / (2 * (|R| + 1)) := by positivity
  obtain ⟨⟨i, hi⟩, hlt⟩ := (hsub.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)).exists
  simp only [Set.mem_setOf_eq] at hi hlt
  refine ⟨fun j => (if j = i then 1 else 0) / 2 + ν j / 2, fun j => ?_, ?_, i, hi, ?_⟩
  · have : 0 ≤ (if j = i then (1 : ℝ) else 0) / 2 := by split_ifs <;> norm_num
    have := hν0 j
    linarith
  · have h := ((hasSum_ite_eq i (1 : ℝ)).div_const 2).add (hν1.div_const 2)
    rwa [show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num] at h
  · simp only [if_true]
    rw [lt_div_iff₀ hi]
    have h1 : pB i * (2 * (|R| + 1)) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hlt
    have := hν0 i
    have hR : R ≤ |R| := le_abs_self R
    have hpos : 0 ≤ pB i * |R| := mul_nonneg (hB0 i) (abs_nonneg R)
    nlinarith

/-- **`rem:path_space`, `sup_{p_F} M' = +∞` on the walks into `x`**: on a graph where a cycle lies
on a walk into `x`, for every probability `p_B(·|x)` charging each walk into `x` and every `R`, some
full-support trajectory law `p_F` on those walks has `p_F(τ)/p_B(τ|x) > R` at some walk `τ` — so
`M' ≥ M > R`. This is `exists_ratio_gt` with `ν := p_B(·|x)`. -/
theorem exists_ratio_gt_walksInto {E : S → S → Prop} {s₀ x v : S} {w : List S}
    (hw : w ∈ walksInto E s₀ x) (hv : v ∈ w) {c : List S} (hcne : c ≠ [])
    (hcE : (v :: c).IsChain E) (hc : c.getLast? = some v)
    {pB : walksInto E s₀ x → ℝ} (hBpos : ∀ τ, 0 < pB τ) (hB1 : HasSum pB 1) (R : ℝ) :
    ∃ pF : walksInto E s₀ x → ℝ, (∀ τ, 0 < pF τ) ∧ HasSum pF 1 ∧
      ∃ τ, 0 < pB τ ∧ R < pF τ / pB τ := by
  haveI := (walksInto_infinite hw hv hcne hcE hc).to_subtype
  refine exists_ratio_gt (fun τ => (hBpos τ).le) hB1.summable ?_ hBpos hB1 R
  simpa only [hBpos, Set.setOf_true] using Set.infinite_univ

/-- **`rem:path_space`, "there being no uniform distribution on an infinite set"**: no constant
function on an infinite type sums to `1`. -/
theorem not_hasSum_const_one {ι : Type*} [Infinite ι] (c : ℝ) : ¬ HasSum (fun _ : ι => c) 1 := by
  intro h
  have hc : c = 0 := (summable_const_iff c).mp h.summable
  subst hc
  exact one_ne_zero (h.unique hasSum_zero)

/-- **`rem:path_space`, the counter-example graph `eq:counterexample_graph`**: its ladder states
`1, 2, 3, …` — the states with a terminal edge to `s_f` — form an infinite set, and no uniform
probability exists on it. -/
theorem doubling_terminal_infinite :
    (Set.range fun j : ℕ => GFNBounds.Doubling.St.lad (j + 1)).Infinite :=
  Set.infinite_range_of_injective fun a b h => by
    simpa only [GFNBounds.Doubling.St.lad.injEq, Nat.add_right_cancel_iff] using h

theorem doubling_no_uniform_terminal_law (c : ℝ) :
    ¬ HasSum (fun _ : Set.range (fun j : ℕ => GFNBounds.Doubling.St.lad (j + 1)) => c) 1 := by
  haveI := doubling_terminal_infinite.to_subtype
  exact not_hasSum_const_one c

end Cycle

section CycleNoBound

open GFNBounds.Graph GFNBounds.Graph.CycleDivergence GFNBounds.Graph.CycleRemarks

variable {M : ℕ}

/-- A probability `κ` on `{x₁,…,x_N}` other than `δ_{x₂}` has `κ(x₂) < 1`. (`Fin (M+2)` index `1`
is the paper's `x₂`.) -/
theorem target_x2_lt_one {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) : t 1 < 1 := by
  classical
  refine lt_of_le_of_ne (le_one_of_prob ht0 hsum 1) fun h1 => ht (funext fun i => ?_)
  by_cases hi : i = 1
  · rw [if_pos hi, hi, h1]
  · rw [if_neg hi]
    have hrest : ∑ j ∈ univ.erase (1 : Fin (M + 2)), t j = 0 := by
      rw [← Finset.add_sum_erase _ t (mem_univ (1 : Fin (M + 2))), h1] at hsum
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => ht0 j).mp hrest i
      (Finset.mem_erase.mpr ⟨hi, mem_univ i⟩)

/-- The terminal mass of `F_k` is `1`, so its terminal law is not a junk value. -/
theorem termMass_Fk_pos (k : ℝ) : 0 < ∑ y, Fk M k y (cycGraph M).snk := by
  rw [cycGraph_snk, sum_termFlow_Fk]
  exact one_pos

/-- **`rem:path_space`, the flows `lem:cycle_counterexample` supplies**: on `𝒞_N`, `N = M + 2`,
for a probability target `κ ≠ δ_{x₂}` on `{x₁,…,x_N}`, the flows `F_k`, `k ∈ ℕ`, are
nonnegative, carried by the edges and exactly flow-matching; for `k ≥ 1` every denominator
`κ + f_→` and every ratio is positive (the loss is defined) and the terminal mass is `1`; their loss
tends to `0` for every training weight; their terminal law is `δ_{x₂}`, at total variation
`1 − κ(x₂) > 0` from `κ`. -/
theorem cycle_flows_target {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) :
    (∀ k : ℕ, ∀ u v, 0 ≤ Fk M k u v) ∧
    (∀ k : ℕ, ∀ u v, Fk M k u v ≠ 0 → (cycGraph M).Edge u v) ∧
    (∀ k : ℕ, ∀ x ∈ (cycGraph M).internal, edgeInflow (Fk M k) x = edgeOutflow (Fk M k) x) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ j,
      0 < extT M t (xC M j) + ∑ v ∈ (cycGraph M).internal, Fk M k (xC M j) v ∧
        0 < fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M j)) ∧
    (∀ k : ℕ, 0 < ∑ y, Fk M k y (cycGraph M).snk) ∧
    (∀ nu : cycV M → ℝ,
      Tendsto (fun k : ℕ => fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) atTop (𝓝 0)) ∧
    (∀ k : ℕ, termLaw (cycGraph M) (Fk M k) = fun v => if v = xC M 1 then 1 else 0) ∧
    (∀ k : ℕ, tvFin (termLaw (cycGraph M) (Fk M k)) (extT M t) = 1 - t 1) ∧
    0 < 1 - t 1 :=
  ⟨fun k => Fk_nonneg (Nat.cast_nonneg k), fun _ _ _ h => Fk_supp h, fun k => Fk_flowMatching k,
    fun _ hk j => den_pos_and_ratio_pos ht0 hk j, fun k => termMass_Fk_pos k,
    fun nu => fmLossTarget_Fk_tendsto_zero_gen g hg1 hgc nu t,
    fun k => funext (termLaw_Fk (k : ℝ)), fun k => tvFin_termLaw_Fk_gen (k : ℝ) ht0 hsum,
    by linarith [target_x2_lt_one ht0 hsum ht]⟩

theorem loss_Fk_nonneg {g : ℝ → ℝ} (hg0 : ∀ r, 0 < r → 0 ≤ g r) {nu : cycV M → ℝ}
    (hnu : ∀ v, 0 ≤ nu v) {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k) := by
  refine Finset.sum_nonneg fun x hx => ?_
  obtain ⟨j, rfl⟩ := mem_internal_iff.mp hx
  exact mul_nonneg (hnu _) (hg0 _ (den_pos_and_ratio_pos ht0 hk j).2)

/-- **`rem:path_space`, "no model-free bound tending to `0` with the loss holds"** (and the same
sentence of `rem:silva_model_constant`), along the flows `F_k` where the loss is defined
(`k ≥ 1`): for every training weight `ν ≥ 0`, every generator `g ≥ 0` on `(0,∞)` continuous at `1`
with `g(1) = 0`, and every probability `κ ≠ δ_{x₂}` on `{x₁,…,x_N}`, no `Φ` with `Φ(L) → 0` as
`L → 0` through `L ≥ 0` (so `Φ(0) = 0`) bounds `TV(terminal law ‖ κ) ≤ Φ(𝓛)` along `(F_k)_{k≥1}`.
-/
theorem cycle_no_bound_along_Fk {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (hg0 : ∀ r, 0 < r → 0 ≤ g r) {nu : cycV M → ℝ} (hnu : ∀ v, 0 ≤ nu v)
    {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) :
    ¬ ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ k : ℕ, 1 ≤ k →
        tvFin (termLaw (cycGraph M) (Fk M k)) (extT M t) ≤
          Φ (fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) := by
  rintro ⟨Φ, hΦ, hbound⟩
  have hL : Tendsto (fun k : ℕ => fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) atTop
      (𝓝[≥] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨fmLossTarget_Fk_tendsto_zero_gen g hg1 hgc nu t,
      (eventually_ge_atTop 1).mono fun k hk => loss_Fk_nonneg hg0 hnu ht0 hk⟩
  have hle : 1 - t 1 ≤ 0 := ge_of_tendsto (hΦ.comp hL) ((eventually_ge_atTop 1).mono fun k hk => by
    have := hbound k hk
    rwa [tvFin_termLaw_Fk_gen (k : ℝ) ht0 hsum] at this)
  linarith [target_x2_lt_one ht0 hsum ht]

/-- **The same, over the flow-matching flows on `𝒞_N` on which the loss and the terminal law are
defined** — the reading "model-free": no `Φ` bounds the total variation by the loss over the
nonnegative, edge-carried, exactly flow-matching flows with every denominator `κ + f_→` positive
and positive terminal mass. Implied by `cycle_no_bound_along_Fk`, the `F_k` with `k ≥ 1` lying in
that class. -/
theorem cycle_no_model_free_bound {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (hg0 : ∀ r, 0 < r → 0 ≤ g r) {nu : cycV M → ℝ} (hnu : ∀ v, 0 ≤ nu v)
    {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) :
    ¬ ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ F : cycV M → cycV M → ℝ, (∀ u v, 0 ≤ F u v) →
        (∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v) →
        (∀ x ∈ (cycGraph M).internal, edgeInflow F x = edgeOutflow F x) →
        (∀ x ∈ (cycGraph M).internal, 0 < extT M t x + ∑ v ∈ (cycGraph M).internal, F x v) →
        0 < ∑ y, F y (cycGraph M).snk →
        tvFin (termLaw (cycGraph M) F) (extT M t) ≤
          Φ (fmLossTarget (cycGraph M) g nu (extT M t) F) := by
  rintro ⟨Φ, hΦ, hbound⟩
  refine cycle_no_bound_along_Fk hg1 hgc hg0 hnu ht0 hsum ht ⟨Φ, hΦ, fun k hk => ?_⟩
  refine hbound (Fk M k) (Fk_nonneg (Nat.cast_nonneg k)) (fun _ _ h => Fk_supp h)
    (Fk_flowMatching k) (fun x hx => ?_) (termMass_Fk_pos k)
  obtain ⟨j, rfl⟩ := mem_internal_iff.mp hx
  exact (den_pos_and_ratio_pos ht0 hk j).1

/-- **The punctured reading**: if `Φ` is only asked to tend to `0` as `L → 0` with `L > 0`, the
conclusion still holds along `(F_k)_{k≥1}` when `ν(x₂) > 0` and `g > 0` off `1` — the source class
has `g` vanishing exactly at `1` — since `ρ_k(x₂) = (1+k)/(κ(x₂)+k) ≠ 1` for `κ(x₂) ≠ 1`, so the
loss never vanishes. (Where the loss vanishes identically along `F_k`, e.g. `ν = 0`, the punctured
reading refutes nothing along them.) -/
theorem cycle_no_bound_punctured {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (hg0 : ∀ r, 0 < r → 0 ≤ g r) (hgpos : ∀ r, 0 < r → r ≠ 1 → 0 < g r)
    {nu : cycV M → ℝ} (hnu : ∀ v, 0 ≤ nu v) (hnu2 : 0 < nu (xC M 1))
    {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) :
    ¬ ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[>] 0) (𝓝 0) ∧
      ∀ k : ℕ, 1 ≤ k →
        tvFin (termLaw (cycGraph M) (Fk M k)) (extT M t) ≤
          Φ (fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) := by
  rintro ⟨Φ, hΦ, hbound⟩
  have hx2 : t 1 < 1 := target_x2_lt_one ht0 hsum ht
  have hpos : ∀ k : ℕ, 1 ≤ k → 0 < fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k) := by
    intro k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hmem : xC M 1 ∈ (cycGraph M).internal := mem_internal_iff.mpr ⟨1, rfl⟩
    have hne : fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M 1) ≠ 1 := by
      rw [fmRatio_Fk_gen]
      simp only [aC, bG, if_neg (zero_ne_one_fin M).symm, if_true, add_zero]
      rw [Ne, div_eq_one_iff_eq (by linarith [ht0 1])]
      intro h
      linarith
    have hterm : 0 < nu (xC M 1) * g (fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M 1)) :=
      mul_pos hnu2 (hgpos _ (den_pos_and_ratio_pos ht0 hk 1).2 hne)
    refine lt_of_lt_of_le hterm ?_
    refine Finset.single_le_sum
      (f := fun x => nu x * g (fmRatio (cycGraph M) (extT M t) (Fk M k) x)) (fun x hx => ?_) hmem
    obtain ⟨j, rfl⟩ := mem_internal_iff.mp hx
    exact mul_nonneg (hnu _) (hg0 _ (den_pos_and_ratio_pos ht0 hk j).2)
  have hL : Tendsto (fun k : ℕ => fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) atTop
      (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨fmLossTarget_Fk_tendsto_zero_gen g hg1 hgc nu t,
      (eventually_ge_atTop 1).mono fun k hk => hpos k hk⟩
  have hle : 1 - t 1 ≤ 0 := ge_of_tendsto (hΦ.comp hL) ((eventually_ge_atTop 1).mono
    fun k hk => by
      have := hbound k hk
      rwa [tvFin_termLaw_Fk_gen (k : ℝ) ht0 hsum] at this)
  linarith

end CycleNoBound

/-! ## The idealized residual is not a divergence-based FM loss

`rem:silva_model_constant` and `rem:path_space` both say that the class of divergence-based FM
losses of `brunswic2024theory` "does not contain the idealized residual `𝓔(p_F)`". The certificate:
on the diamond DAG `s₀ → a, s₀ → b, a → x, b → x` with `p_B = ½` and target `δ_x`, the unit-mass
edge flow of the Markov policy that goes to `a` with probability `q` has flow-matching ratio `1` at
every state, so **every** divergence-based FM loss vanishes on the whole family, for every `ν` and
every `g` with `g(1) = 0`; while `𝓔 = ½(log 2q)² + ½(log 2(1−q))² > 0` for `q ≠ ½`. -/

section DiamondResidual

open GFNBounds.Graph GFNBounds.Graph.CycleDivergence

/-- The successor sets of the diamond DAG `s₀ → a, s₀ → b, a → x, b → x` on `Fin 4`. -/
def diamondSucc : Fin 4 → Finset (Fin 4) := ![{1, 2}, {3}, {3}, ∅]

/-- The two trajectories of the diamond. -/
def diamondPath : Bool → List (Fin 4) := fun b => if b then [0, 2, 3] else [0, 1, 3]

/-- The edges of the diamond as a marked graph on `Fin 6`: `0 = s₀` (source mark), `1 = o` (the
DAG's root), `2 = a`, `3 = b`, `4 = x` (the terminal state), `5 = s_f`. -/
def diamondEdges : Finset (Fin 6 × Fin 6) := {(0, 1), (1, 2), (1, 3), (2, 4), (3, 4), (4, 5)}

/-- The diamond DAG as a `MarkedGraph`. -/
def diamondGraph : MarkedGraph (Fin 6) where
  Edge u v := (u, v) ∈ diamondEdges
  src := 0
  snk := 5
  src_ne_snk := by decide
  no_edge_into_src := by decide
  no_edge_out_of_snk := by decide

/-- The unit-mass edge flow of the Markov policy sending `o → a` with probability `q`,
`o → b` with `1 − q`, and deterministic elsewhere. -/
noncomputable def diamondFlow (q : ℝ) (u v : Fin 6) : ℝ :=
  if u = 0 ∧ v = 1 then 1 else if u = 1 ∧ v = 2 then q else if u = 1 ∧ v = 3 then 1 - q
  else if u = 2 ∧ v = 4 then q else if u = 3 ∧ v = 4 then 1 - q else if u = 4 ∧ v = 5 then 1
  else 0

/-- The target `δ_x`. -/
noncomputable def diamondTarget : Fin 6 → ℝ := fun v => if v = 4 then 1 else 0

theorem diamondGraph_internal : diamondGraph.internal = {1, 2, 3, 4} := by
  decide

/-- The Markov forward policy of the family on `Fin 4` (`0 = o, 1 = a, 2 = b, 3 = x`, the
numbering of `diamondSucc`). -/
noncomputable def diamondPol (q : ℝ) (s s' : Fin 4) : ℝ :=
  if s = 0 ∧ s' = 1 then q else if s = 0 ∧ s' = 2 then 1 - q else 1

/-- The trajectory law of the family: `p_F(o → a → x) = q`, `p_F(o → b → x) = 1 − q`, the
probabilities the Markov policy `diamondPol q` gives the two paths `diamondPath`. -/
theorem pathProb_diamondPol (q : ℝ) (b : Bool) :
    pathProb (diamondPol q) (diamondPath b) = if b then 1 - q else q := by
  cases b <;> simp only [diamondPath, Bool.false_eq_true, ↓reduceIte, Fin.isValue, pathProb,
    diamondPol, and_self, one_ne_zero, Fin.reduceEq, and_false, mul_one]

theorem diamond_ratio_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ x ∈ diamondGraph.internal,
      0 < diamondTarget x + ∑ v ∈ diamondGraph.internal, diamondFlow q x v ∧
        fmRatio diamondGraph diamondTarget (diamondFlow q) x = 1 := by
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  intro x hx
  rw [diamondGraph_internal] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [fmRatio, edgeInflow, diamondGraph_internal]
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [diamondTarget, Fin.isValue, Fin.reduceEq, ↓reduceIte, diamondFlow, one_ne_zero,
      false_and, true_and, mem_insert, mem_singleton, or_self, or_true, not_false_eq_true,
      sum_insert, sum_singleton, add_zero, add_sub_cancel, zero_add, zero_lt_one, sub_pos, and_true,
      and_false, sum_ite_eq', mem_univ, ne_eq, div_self, div_self_eq_one₀, and_self,
      Fin.sum_univ_six] <;>
    first
    | exact ⟨hq0, hq0.ne'⟩
    | exact ⟨by linarith, h1q⟩

/-- **`rem:silva_model_constant` and `rem:path_space`, "a class that does not contain the
idealized residual"**: on the diamond family every divergence-based FM loss (any `g` with
`g(1) = 0`, any `ν`) vanishes identically, with every denominator positive, while the idealized
residual `𝓔(p_F) = ½(log 2q)² + ½(log 2(1−q))²` of the same models does not; hence no such loss
equals `𝓔` on the family. -/
theorem residual_not_divergence_FM_loss :
    (∀ (g : ℝ → ℝ) (nu : Fin 6 → ℝ), g 1 = 0 → ∀ q : ℝ, 0 < q → q < 1 →
      fmLossTarget diamondGraph g nu diamondTarget (diamondFlow q) = 0) ∧
    (∀ q : ℝ, 0 < q → q < 1 →
      residual (fun _ : Unit => (1 : ℝ)) (fun _ => 1) (fun (_ : Unit) (_ : Bool) => (1 : ℝ) / 2)
          (fun b => pathProb (diamondPol q) (diamondPath b))
        = 2⁻¹ * Real.log (2 * q) ^ 2 + 2⁻¹ * Real.log (2 * (1 - q)) ^ 2) ∧
    (∀ q : ℝ, 0 < q → q < 1 → q ≠ 1 / 2 →
      0 < residual (fun _ : Unit => (1 : ℝ)) (fun _ => 1)
        (fun (_ : Unit) (_ : Bool) => (1 : ℝ) / 2)
        (fun b => pathProb (diamondPol q) (diamondPath b))) ∧
    ¬ ∃ (g : ℝ → ℝ) (nu : Fin 6 → ℝ), g 1 = 0 ∧ ∀ q : ℝ, 0 < q → q < 1 →
      residual (fun _ : Unit => (1 : ℝ)) (fun _ => 1) (fun (_ : Unit) (_ : Bool) => (1 : ℝ) / 2)
          (fun b => pathProb (diamondPol q) (diamondPath b))
        = fmLossTarget diamondGraph g nu diamondTarget (diamondFlow q) := by
  have hloss : ∀ (g : ℝ → ℝ) (nu : Fin 6 → ℝ), g 1 = 0 → ∀ q : ℝ, 0 < q → q < 1 →
      fmLossTarget diamondGraph g nu diamondTarget (diamondFlow q) = 0 := by
    intro g nu hg1 q hq0 hq1
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [(diamond_ratio_one hq0 hq1 x hx).2, hg1, mul_zero]
  have hres : ∀ q : ℝ, 0 < q → q < 1 →
      residual (fun _ : Unit => (1 : ℝ)) (fun _ => 1) (fun (_ : Unit) (_ : Bool) => (1 : ℝ) / 2)
          (fun b => pathProb (diamondPol q) (diamondPath b))
        = 2⁻¹ * Real.log (2 * q) ^ 2 + 2⁻¹ * Real.log (2 * (1 - q)) ^ 2 := by
    intro q _ _
    simp only [residual, logRatio, pathProb_diamondPol, Fintype.sum_unique, Fintype.sum_bool,
      if_true, Bool.false_eq_true, if_false, one_mul]
    have e1 : (1 - q) / (1 / 2) = 2 * (1 - q) := by ring
    have e2 : q / (1 / 2) = 2 * q := by ring
    rw [e1, e2]
    ring
  have hpos : ∀ q : ℝ, 0 < q → q < 1 → q ≠ 1 / 2 →
      0 < residual (fun _ : Unit => (1 : ℝ)) (fun _ => 1)
        (fun (_ : Unit) (_ : Bool) => (1 : ℝ) / 2)
        (fun b => pathProb (diamondPol q) (diamondPath b)) := by
    intro q hq0 hq1 hq
    rw [hres q hq0 hq1]
    have hl : Real.log (2 * q) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (fun h => hq (by linarith))
    have : 0 < Real.log (2 * q) ^ 2 := by positivity
    have := sq_nonneg (Real.log (2 * (1 - q)))
    linarith
  refine ⟨hloss, hres, hpos, ?_⟩
  rintro ⟨g, nu, hg1, heq⟩
  have h := heq (1 / 4) (by norm_num) (by norm_num)
  rw [hloss g nu hg1 _ (by norm_num) (by norm_num)] at h
  exact (hpos (1 / 4) (by norm_num) (by norm_num) (by norm_num)).ne' h

end DiamondResidual

/-! ## Inhabitation (kb 0025): every hypothesis bundle above holds on an explicit instance -/

section Inhabitation

/-- Item (1): a training law with a zero, on `Bool`. -/
theorem inhabit_not_full_support :
    chiSqE (unif Bool) (fun b => if b then 1 else 0) = ⊤ ∧
      rhsE 1 (chiSqE (unif Bool) (fun b => if b then 1 else 0)) 1 = ⊤ :=
  ⟨chiSqE_unif_eq_top (x₀ := false) (by simp only [Bool.false_eq_true, if_false]),
    rhsE_eq_top_of_not_full_support one_pos (x₀ := false)
      (by simp only [Bool.false_eq_true, if_false]) one_ne_zero⟩

/-- Item (2): one terminal, two trajectories charged `½` each, `p_F = (0, 1)`. -/
theorem inhabit_pF_zero :
    residualE (fun _ : Unit => (1 : ℝ)) (fun _ => 1) (fun (_ : Unit) (_ : Bool) => (1 : ℝ) / 2)
      (fun b => if b then 1 else 0) = ⊤ :=
  residualE_eq_top_of_pF_zero (x₀ := ()) (t₀ := false) one_pos (by norm_num)
    (by simp only [Bool.false_eq_true, if_false])

/-- Item (3): the uniform backward policy on the two-state path `false → true`. -/
theorem inhabit_uniformBackward :
    termMarginal (fun _ : Unit => ()) (fun _ => (1 : ℝ)) ()
      = ∑ _t : Unit, (if () = () then uniformBackProb
            (fun s : Bool => if s then {false} else ∅) [false, true] else 0) *
          (1 / if () = () then uniformBackProb
            (fun s : Bool => if s then {false} else ∅) [false, true] else 0) :=
  identity_of_uniformBackward (fun s : Bool => if s then {false} else ∅) (fun _ : Unit => ())
    (fun _ => [false, true]) (fun _ => by decide) (fun _ => zero_le_one) ()

/-- The one-parent kernel on a nonempty type charges its diagonal. -/
theorem wSupport_deltaPB_nonempty {Y : Type*} [Fintype Y] [DecidableEq Y] (y : Y) :
    (wSupport (deltaPB Y)).Nonempty :=
  ⟨(y, y), mem_wSupport (by rw [deltaPB, if_pos rfl]; exact one_pos)⟩

/-- The tree hypotheses hold for the star of `prop:silva_no_uniform`(ii) (`into = id`), and give
`M ≤ 1` there. -/
theorem inhabit_tree (K : ℕ) (hK : 0 < K) :
    mVal (deltaPB (Star K)) (starPF K) (wSupport_deltaPB_nonempty (Sum.inl false)) ≤ 1 :=
  tree_mVal_le_one (into := id) Function.injective_id
    (fun x t h => by
      by_contra hne
      exact h (by simp only [deltaPB]; exact if_neg hne))
    deltaPB_sum (le_one_of_sum_eq_one (fun t => (starPF_pos hK t).le) (starPF_sum hK)) _

/-- The ladder has `P(x) = 2ⁿ`. -/
theorem ladder_pathCount (n : ℕ) : pathCount (fun _ : LadderTraj n => ()) () = 2 ^ n := by
  rw [pathCount, Finset.filter_true_of_mem (fun _ _ => rfl), Finset.card_univ, card_ladderTraj]

/-- **`rem:path_space` on the ladder, and a consistency check with
`rem:silva_model_constant`**: the lower bound `sup M' ≥ P(x) = 2ⁿ` meets the fixed-graph upper
bound `M' ≤ 2ⁿ`, so over full-support trajectory laws `sup M' = 2ⁿ` exactly, and
`1/w_min ≥ 2ⁿ`. -/
theorem ladder_sSup_mPrime_eq (n : ℕ) :
    sSup {m : ℝ | ∃ pF : LadderTraj n → ℝ, (∀ t, 0 < pF t) ∧ ∑ t, pF t = 1 ∧
      m = mPrime (ladderPB n) pF ladderOne (ladder_wSupport_nonempty n) unit_univ_nonempty}
      = 2 ^ n ∧
    (2 : ℝ) ^ n ≤ 1 / wMin ladderOne (ladderPB n) (ladder_wSupport_nonempty n) := by
  have hBsupp : ∀ (x : Unit) (t : LadderTraj n), ladderPB n x t ≠ 0 → () = x :=
    fun x _ _ => Subsingleton.elim _ _
  have hBpos : ∀ (x : Unit) (t : LadderTraj n), () = x → 0 < ladderPB n x t :=
    fun x t _ => ladderPB_pos n x t
  have hP := ladder_pathCount n
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine csSup_le ?_ ?_
    · exact ⟨_, fun _ => ((2 : ℝ) ^ n)⁻¹, fun _ => by positivity,
        by simpa only [ladderPB_eq] using ladderPB_sum n (), rfl⟩
    · rintro m ⟨pF, hpos, hsum, rfl⟩
      exact ladder_mPrime_le n (fun t => (hpos t).le) hsum
  · have h := pathCount_le_sSup_mPrime (fun _ : LadderTraj n => ()) ladderOne
      (ladder_wSupport_nonempty n) unit_univ_nonempty hBsupp hBpos (ladderPB_sum n) ()
    rwa [hP, Nat.cast_pow, Nat.cast_ofNat] at h
  · have h := pathCount_div_le_inv_wMin (fun _ : LadderTraj n => ()) (pET := ladderOne)
      (ladder_wSupport_nonempty n) (fun _ => one_pos) hBsupp hBpos (ladderPB_sum n) ()
    rwa [hP, ladderOne, div_one, Nat.cast_pow, Nat.cast_ofNat] at h

theorem diamondPB_wSupport_nonempty :
    (wSupport (fun (_ : Unit) (_ : Bool) => (1 : ℝ) / 2)).Nonempty :=
  ⟨((), false), mem_wSupport (by norm_num)⟩

/-- **The Markov hypotheses hold on the diamond DAG**, whose terminal `x` has `P(x) = 2`: the
Markov-policy supremum of `M'` is at least `2`. -/
theorem inhabit_markov_diamond :
    (2 : ℝ) ≤ sSup {m : ℝ | ∃ pol : Fin 4 → Fin 4 → ℝ,
      (∀ s, ∀ s' ∈ diamondSucc s, 0 < pol s s') ∧
      (∀ s, (diamondSucc s).Nonempty → ∑ s' ∈ diamondSucc s, pol s s' = 1) ∧
      m = mPrime (fun (_ : Unit) (_ : Bool) => (1 : ℝ) / 2) (fun t => pathProb pol (diamondPath t))
        (fun _ => 1) diamondPB_wSupport_nonempty unit_univ_nonempty} := by
  have h := pathCount_le_sSup_mPrime_markov diamondSucc diamondPath
    (fun t => by cases t <;> decide) (fun t => by cases t <;> decide)
    (fun _ : Bool => ()) (pB := fun _ _ => (1 : ℝ) / 2) (fun _ => 1) diamondPB_wSupport_nonempty
    unit_univ_nonempty
    (fun x _ _ => Subsingleton.elim _ _) (fun _ _ _ => by norm_num)
    (fun _ => by simp only [Fintype.sum_bool]; norm_num) ()
  have hP : pathCount (fun _ : Bool => ()) () = 2 := by
    rw [pathCount, Finset.filter_true_of_mem (fun _ _ => rfl), Finset.card_univ,
      Fintype.card_bool]
  rwa [hP, Nat.cast_ofNat] at h

open GFNBounds.Graph GFNBounds.Graph.CycleDivergence in
/-- **The cycle hypotheses hold on `𝒞₂`**: the walk `s₀ → x₁ → x₂` visits `x₁`, which lies on the
cycle `x₁ → x₂ → x₁`, so the walks into `x₂` are infinitely many. -/
theorem inhabit_cycle_walks :
    (walksInto (cycGraph 0).Edge (srcC 0) (xC 0 1)).Infinite := by
  have e1 : (cycGraph 0).Edge (srcC 0) (xC 0 0) := Or.inl ⟨rfl, rfl⟩
  have e2 : (cycGraph 0).Edge (xC 0 0) (xC 0 1) := Or.inr (Or.inr ⟨0, rfl, rfl⟩)
  have e3 : (cycGraph 0).Edge (xC 0 1) (xC 0 0) := Or.inr (Or.inr ⟨1, rfl, rfl⟩)
  refine walksInto_infinite (w := [srcC 0, xC 0 0, xC 0 1]) (v := xC 0 0) (c := [xC 0 1, xC 0 0])
    ⟨rfl, rfl, ?_⟩ (List.mem_cons_of_mem _ List.mem_cons_self) (List.cons_ne_nil _ _) ?_ rfl
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨e1, e2⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨e2, e3⟩

/-- Every nonempty countable type carries a full-support probability: `2^{-encode i}`, normalized. -/
theorem exists_pos_hasSum_one {ι : Type*} [Countable ι] [Nonempty ι] :
    ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ HasSum p 1 := by
  classical
  letI := Encodable.ofCountable ι
  set w : ι → ℝ := fun i => (1 / 2 : ℝ) ^ (Encodable.encode i) with hw
  have hs : Summable w :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      Encodable.encode_injective
  have hpos : ∀ i, 0 < w i := fun i => by positivity
  have hS : 0 < ∑' i, w i :=
    hs.tsum_pos (fun i => (hpos i).le) (Classical.arbitrary ι) (hpos _)
  refine ⟨fun i => w i / ∑' i, w i, fun i => div_pos (hpos i) hS, ?_⟩
  have h := hs.hasSum.div_const (∑' i, w i)
  rwa [div_self hS.ne'] at h

open GFNBounds.Graph GFNBounds.Graph.CycleDivergence in
/-- **The cycle bundle of `exists_ratio_gt_walksInto` and `iInf_pB_walksInto_eq_zero` holds on
`𝒞₂`**: the walks into `x₂` carry a full-support probability `p_B`, and for it `inf p_B = 0` and
every `R` is exceeded by a ratio `p_F/p_B`. -/
theorem inhabit_cycle_ratio :
    ∃ pB : walksInto (cycGraph 0).Edge (srcC 0) (xC 0 1) → ℝ, (∀ τ, 0 < pB τ) ∧ HasSum pB 1 ∧
      (⨅ τ, pB τ) = 0 ∧
      ∀ R : ℝ, ∃ pF : walksInto (cycGraph 0).Edge (srcC 0) (xC 0 1) → ℝ, (∀ τ, 0 < pF τ) ∧
        HasSum pF 1 ∧ ∃ τ, 0 < pB τ ∧ R < pF τ / pB τ := by
  have e1 : (cycGraph 0).Edge (srcC 0) (xC 0 0) := Or.inl ⟨rfl, rfl⟩
  have e2 : (cycGraph 0).Edge (xC 0 0) (xC 0 1) := Or.inr (Or.inr ⟨0, rfl, rfl⟩)
  have e3 : (cycGraph 0).Edge (xC 0 1) (xC 0 0) := Or.inr (Or.inr ⟨1, rfl, rfl⟩)
  have hw : [srcC 0, xC 0 0, xC 0 1] ∈ walksInto (cycGraph 0).Edge (srcC 0) (xC 0 1) := by
    refine ⟨rfl, rfl, ?_⟩
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨e1, e2⟩
  have hv : xC 0 0 ∈ [srcC 0, xC 0 0, xC 0 1] := List.mem_cons_of_mem _ List.mem_cons_self
  have hcE : [xC 0 0, xC 0 1, xC 0 0].IsChain (cycGraph 0).Edge := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨e2, e3⟩
  haveI : Nonempty (walksInto (cycGraph 0).Edge (srcC 0) (xC 0 1)) := ⟨⟨_, hw⟩⟩
  obtain ⟨pB, hpos, hsum⟩ :=
    exists_pos_hasSum_one (ι := walksInto (cycGraph 0).Edge (srcC 0) (xC 0 1))
  exact ⟨pB, hpos, hsum,
    iInf_pB_walksInto_eq_zero hw hv (List.cons_ne_nil _ _) hcE rfl (fun τ => (hpos τ).le) hsum,
    exists_ratio_gt_walksInto hw hv (List.cons_ne_nil _ _) hcE rfl hpos hsum⟩

/-- The geometric law `2^{-(n+1)}` on `ℕ` inhabits the infinite-support hypotheses: its infimum is
`0` and its ratios are unbounded. -/
theorem inhabit_geometric :
    (⨅ n : ℕ, (1 : ℝ) / 2 / 2 ^ n) = 0 ∧
      ∀ R : ℝ, ∃ pF : ℕ → ℝ, (∀ n, 0 < pF n) ∧ HasSum pF 1 ∧
        ∃ n, 0 < (1 : ℝ) / 2 / 2 ^ n ∧ R < pF n / ((1 : ℝ) / 2 / 2 ^ n) := by
  have hs : HasSum (fun n : ℕ => (1 : ℝ) / 2 / 2 ^ n) 1 := hasSum_geometric_two' 1
  have hpos : ∀ n : ℕ, 0 < (1 : ℝ) / 2 / 2 ^ n := fun n => by positivity
  refine ⟨iInf_eq_zero_of_summable (fun n => (hpos n).le) hs.summable, fun R => ?_⟩
  exact exists_ratio_gt (fun n => (hpos n).le) hs.summable
    (by simpa only [hpos, Set.setOf_true] using Set.infinite_univ) hpos hs R

open GFNBounds.Graph GFNBounds.Graph.CycleDivergence GFNBounds.Graph.CycleRemarks in
/-- **The no-bound hypotheses hold on every `𝒞_N`**: `g(r) = (r − 1)²`, `ν ≡ 1` and the uniform
target on `{x₁,…,x_N}`, which is not `δ_{x₂}`. -/
theorem inhabit_cycle_no_bound (M : ℕ) :
    (¬ ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ F : cycV M → cycV M → ℝ, (∀ u v, 0 ≤ F u v) →
        (∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v) →
        (∀ x ∈ (cycGraph M).internal, edgeInflow F x = edgeOutflow F x) →
        (∀ x ∈ (cycGraph M).internal,
          0 < extT M (fun _ => 1 / ((M : ℝ) + 2)) x + ∑ v ∈ (cycGraph M).internal, F x v) →
        0 < ∑ y, F y (cycGraph M).snk →
        tvFin (termLaw (cycGraph M) F) (extT M fun _ => 1 / ((M : ℝ) + 2)) ≤
          Φ (fmLossTarget (cycGraph M) (fun r => (r - 1) ^ 2) (fun _ => 1)
            (extT M fun _ => 1 / ((M : ℝ) + 2)) F)) ∧
    (¬ ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[>] 0) (𝓝 0) ∧
      ∀ k : ℕ, 1 ≤ k →
        tvFin (termLaw (cycGraph M) (Fk M k)) (extT M fun _ => 1 / ((M : ℝ) + 2)) ≤
          Φ (fmLossTarget (cycGraph M) (fun r => (r - 1) ^ 2) (fun _ => 1)
            (extT M fun _ => 1 / ((M : ℝ) + 2)) (Fk M k))) := by
  have hM : (0 : ℝ) < (M : ℝ) + 2 := by positivity
  have hg1 : (fun r : ℝ => (r - 1) ^ 2) 1 = 0 := by norm_num
  have hgc : ContinuousAt (fun r : ℝ => (r - 1) ^ 2) 1 :=
    ((continuous_id.sub continuous_const).pow 2).continuousAt
  have hg0 : ∀ r : ℝ, 0 < r → 0 ≤ (fun r : ℝ => (r - 1) ^ 2) r := fun r _ => sq_nonneg _
  have hgpos : ∀ r : ℝ, 0 < r → r ≠ 1 → 0 < (fun r : ℝ => (r - 1) ^ 2) r :=
    fun r _ hr => by
      have : r - 1 ≠ 0 := sub_ne_zero.mpr hr
      positivity
  have ht0 : ∀ i : Fin (M + 2), 0 ≤ (fun _ => 1 / ((M : ℝ) + 2)) i := fun _ => by positivity
  have hsum : ∑ i : Fin (M + 2), (fun _ => 1 / ((M : ℝ) + 2)) i = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have ht : (fun _ : Fin (M + 2) => 1 / ((M : ℝ) + 2)) ≠ fun i => if i = 1 then 1 else 0 := by
    intro h
    have h1 := congrFun h 1
    simp only [if_true] at h1
    rw [div_eq_one_iff_eq hM.ne'] at h1
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  exact ⟨cycle_no_model_free_bound hg1 hgc hg0 (fun _ => zero_le_one) ht0 hsum ht,
    cycle_no_bound_punctured hg1 hgc hg0 hgpos (fun _ => zero_le_one) one_pos ht0 hsum ht⟩

end Inhabitation

end GFNBounds.Silva.Remarks
