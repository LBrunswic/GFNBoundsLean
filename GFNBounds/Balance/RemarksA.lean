import GFNBounds.Balance.FreezingGeneral
import GFNBounds.Balance.WeightedL2Norm
import GFNBounds.Balance.FlowExistence
import GFNBounds.Graph.Universality
import GFNBounds.Graph.MorozovConsume
import GFNBounds.Balance.C3Wrappers
import GFNBounds.Graph.CycleRemarks
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Three remarks of Appendix A: freezing, visit ratios, and periodic loop closures

**`rem:freezing`** — `proofs.tex:870–872` (a remark; no proof environment).
**`rem:visit_ratio`** — `proofs.tex:1095–1101` (a remark; no proof environment).
**`rem:graphs_vs_L2`** — `proofs.tex:1177–1179` (a remark; no proof environment).

(Spans at draft commit `216ce34`, the rewrite of 2026-09-14; line citations drift, `kb/entries/0036`.
The bold-backtick form of each label is what `scripts/trace_check.py` and the paper-side ledger
machine-read.) Every sentence of the three remarks not visibly marked heuristic is read as a
claim; the table below says where each lands.

> (`rem:freezing`) *(i)* Convexity excludes the mechanism: if `g` is convex, `g'` is nondecreasing,
> and `g' ≡ 0` on `[α,β] ⊂ (0,1)` would make `g` nondecreasing on `[β,1]`, contradicting
> `g(β) > 0 = g(1)` (symmetrically above `1`). Moreover, a convex differentiable `g` has `g' ≤ 0`
> on `(0,1)`, so `|g'(x₀)| ≤ ε` at a single `x₀ < 1` forces `|g'| ≤ ε` on `[x₀,1]`, hence
> `g ≤ ε(1−x₀)` there. Real-analytic generators exclude exact freezing too, by the identity
> theorem: `g' ≡ 0` on an interval would make `g` constant on `(0,+∞)`. Heuristically, […]. The
> generators admitted by Brunswic et al. are not required to be convex, and `(log x)²` is not
> convex, `g''(x) = 2(1−log x)/x²` being negative for `x > e`; it saturates one-sidedly only
> (`g' → 0` at `+∞` but `|g'| → ∞` at `0⁺`), and it is strictly unimodal, so it has no spurious
> critical point (Proposition `prop:no_distant_equilibrium`*(1)*).
> *(ii)* For `δ ∈ (0,1/4)`, take `(a,b,c,d) = (1−2δ, 1−δ, 1+δ, 1+2δ)` in Proposition
> `prop:nonlinear_freezing`. On the two-state chain of its item *(2)*, every flow `μ = (1,1−η)`
> with `2δ < η < 4δ/(1+4δ)` has ratios `r = (1−η/2, (1−η/2)/(1−η)) ∈ U⁻ × U⁺`, so it is frozen by
> item *(1)*, at distance `O(δ)` from the balanced ray; at `δ = 1/10`, `η = 1/4` gives
> `r = (0.875, 1.1667)`. Every admissible generator `C³` on `[1,1+δ]` with `g''(1) = 2` and
> `g' ≡ 0` on `[1+δ,1+2δ]` has `g'(1) = g'(1+δ) = 0`, […] whence `sup_{[1,1+δ]}|g'''| ≥ 4/δ`; and
> since the frozen flows above do not converge, the radius `ε₀` of Theorem
> `theo:local_convergence_full` must depend on `g` beyond `g''(1)`.
> *(iii)* The freezing configurations are invisible to the linearization at balance. With
> `φ_{p,q}` as in Proposition `prop:nonlinear_freezing` and `0 < θ < min(1−b, c−1)`, the functions
> `ζ := φ_{a,b}φ_{c,d}` and `ξ := φ_{1−θ,1+θ}` are `C^∞` and non-negative, with the disjoint zero
> sets `[a,b] ∪ [c,d]` and `[1−θ,1+θ]`, so `m := 2ζ/(ζ+ξ)` is `C^∞` with values in `[0,2]`, equals
> `2` on `[1−θ,1+θ]` and vanishes exactly on `[a,b] ∪ [c,d]`. The generator
> `g(x) := ∫₁ˣ m(t)(t−1) dt` is then admissible, with `g''(1) = 2` and `g' ≡ 0` on the bands, so
> item *(1)* of that proposition applies to it, and it equals `(x−1)²` on `[1−θ,1+θ]` — which the
> generator constructed in the proposition does on no neighbourhood of `1`.
> *(iv)* For every admissible differentiable strictly unimodal generator, every critical point of
> `𝓛_{g,ν}` is balanced when `ν` has positive density (`prop:no_distant_equilibrium`*(1)*); global
> convergence is proved, on finite state spaces, for `(log x)²` and `(x−1)²` only
> (`prop:no_distant_equilibrium`*(3)*), a bounded strictly unimodal generator not being covered;
> infinite state spaces are not addressed.

> (`rem:visit_ratio`) Convergence itself uses no mixing constant (`theo:training_speed_full`).
> Heuristically, […]. *Far from balance*, the mass identity gives a lower bound state by state: in
> the setting of `theo:training_speed_full`, with `u_max := max_x dμ/dλ(x)`, for a region `U` on
> which `|r−1| ≥ δ` with `δ ∈ (0,1/2]`, the contribution of `U` to the gradient mass is
> `∫_U |g'(r)(1−r)| (dν/dμ) dλ ≥ (w_min/u_max)·(δ²/2)·∑_{x∈U} N(x)/(2+σ̄)`: *the contribution of an
> out-of-equilibrium state to this lower bound is proportional to its visit ratio `N(x)/(2+σ̄)`*.
> […] heuristically […] — a lower bound on the gradient mass bounds that time from neither side;
> Corollary `cor:global_lojasiewicz` aggregates the mass identity into the global `𝓛⁻¹`-decay in
> time. *Near balance* the mixing constant takes over: the exponential rate is
> `ϱ = g''(1)w_min/B̂²` for the linearized gradient flow (`theo:db_stable_frozen_full`) and `ϱ/2`
> for the nonlinear one (`theo:local_convergence_full`). Heuristically, […]. The constant `B̂_σ`
> of Proposition `prop:morozov_rate` […] bounds the coercivity constant — `B̂_σ ≥ ‖S‖` wherever the
> operator `S` of Lemma `lem:sigma_mixing` is defined — and not the mixing sum `B̂`, which is `+∞`
> on a leveled graph where `B̂_σ` is finite.

> (`rem:graphs_vs_L2`) Theorem `theo:universality_graphs` is more precise than Theorem
> `theo:universality_L2` applied to the loop-closed chain — exactness, and uniqueness of the
> balanced flow — and less demanding: it needs only the irreducibility of a finite chain, whereas
> the summable-mixing hypothesis of Theorem `theo:universality_L2` fails when the loop closure is
> periodic (the loop closure of a single directed path is a directed cycle). When `π̂_←` is
> moreover aperiodic, the finite irreducible chain is geometrically ergodic, its `L²`-mixing
> coefficients are summable, and Theorem `theo:db_stable_frozen_full` gives the rate
> `g''(1)w_min/B̂²` of the linearized gradient descent toward the balanced ray of item *(2)*.
> Proposition `prop:morozov_rate` removes the aperiodicity hypothesis, replacing `B̂` by the
> hitting-time constant `B̂_σ`. Heuristically, the uniqueness up to scale in *(2)* is the static
> counterpart of the conservation of `Πh_t` in Theorem `theo:db_stable_frozen_full`: the balanced
> locus is one-dimensional, and the linearized training moves transversally to it, whereas along
> the nonlinear gradient flow of a strictly unimodal generator the total mass increases
> (Proposition `prop:no_distant_equilibrium`*(2)*).

## What is proved

| paper sentence | here |
|---|---|
| *(i)* convex ⇒ no flat band `[α,β] ⊂ (0,1)` or `⊂ (1,∞)` | `convex_no_flat_band`, from the sharper `convex_deriv_ne_zero` (`g' ≠ 0` at every `x ≠ 1`) |
| *(i)* convex ⇒ `g' ≤ 0` on `(0,1)`, `|g'| ≤ ε` and `g ≤ ε(1−x₀)` on `[x₀,1]` | `convex_small_deriv` (with `deriv_one_eq_zero`) |
| *(i)* analytic: `g' ≡ 0` on an interval ⇒ `g` constant on `(0,∞)`; no exact freezing | `analytic_const_of_flat`, `analytic_admissible_no_flat` |
| *(i)* `(log x)²`: `g'' = 2(1−log x)/x²`, negative on `(e,∞)`, not convex | `deriv_deriv_logSq`, `deriv_deriv_logSq_neg`, `logSq_not_convexOn` |
| *(i)* `g' → 0` at `+∞`, `|g'| → ∞` at `0⁺` | `tendsto_logSqDeriv_atTop`, `tendsto_abs_logSqDeriv_nhdsGT_zero` |
| *(i)* strictly unimodal ⇒ no spurious critical point | `logSq_critical_balanced` |
| *(ii)* the bands, the window, the ratios, frozen by item *(1)*, distance `O(δ)` | `deltaBands`, `etaVec_mem_frozen`, `freezing_two_frozen` (distance `√2·η < 4√2·δ` in `L²(λ)`) |
| *(ii)* `δ = 1/10`, `η = 1/4`: `r = (0.875, 1.1667)` | `freezing_two_example` (`7/6`, within `1/20000` of `1.1667`) |
| *(ii)* `sup_{[1,1+δ]}|g'''| ≥ 4/δ` | `third_deriv_bound` (every bound `M`), `third_deriv_sSup` (the supremum); met by the bands' own generator, `deltaBands_third_deriv` |
| *(ii)* `ε₀` must depend on `g` beyond `g''(1)` | `radius_not_uniform_in_generator` (no uniform radius exists), `frozen_near_balance`; and on the certified radius itself, `eps0C3_deltaBands_small` |
| *(iii)* `ζ`, `ξ`, `m = 2ζ/(ζ+ξ)`: `C^∞`, `[0,2]`, `= 2` near `1`, zero set exactly the bands | `freezing_three_multiplier` |
| *(iii)* `g` admissible, `g''(1) = 2`, `g' ≡ 0` on the bands, `= (x−1)²` on `[1−θ,1+θ]` | `freezing_three_generator` |
| *(iii)* item *(1)* applies | `freezing_three_item_one` |
| *(iii)* invisible to the linearization at balance | `freezing_three_invisible`: where every ratio is in `[1−θ,1+θ]`, loss and gradient density are those of `(x−1)²` |
| *(iii)* the proposition's generator is `(x−1)²` on no neighbourhood of `1` | `freezing_g_ne_sq_near_one` |
| *(iv)* critical ⇒ balanced | `freezing_four_critical` |
| *(iv)* global convergence for `(log x)²` | `freezing_four_logSq_converges` (marked-graph loop closures; see SCOPE); both halves on every finite ergodic chain: `GlobalConvergenceFinite.no_distant_equilibrium_three_{logSq,sq}_of_ergodic` |
| visit_ratio: convergence uses no mixing constant | `freezing_four_logSq_converges` carries no mixing hypothesis |
| visit_ratio: the displayed lower bound, and that it is a part of the gradient mass | `visit_ratio_mass_lower` |
| visit_ratio: `B̂_σ ≥ ‖S‖` wherever `S` is defined | `visit_ratio_norm_S_le`, via `norm_S_le_of_coercive`, `coercivity_morozov_op` |
| visit_ratio: `B̂ = +∞` on a leveled graph where `B̂_σ` is finite | `leveled_mixing_fails`, `leveled_bsigma_finite_mixing_infinite` |
| graphs_vs_L2: summable mixing fails when the loop closure is periodic | `graphs_vs_L2_periodic` (from `mixing_fails_of_periodicAt`, `mixing_fails_of_cyclic`): `β̂_{dk} ≥ 1`, `∑ β̂ₙ = +∞` in `ℝ≥0∞`, not summable, `¬ Core.Mixing` |
| graphs_vs_L2: the loop closure of a directed path is a directed cycle | `pathPolicy_phat`; periodic, `path_witness` |
| graphs_vs_L2: aperiodic ⇒ geometrically ergodic, summable `L²` mixing | `mixing_of_aperiodic` (`β̂ₙ ≤ (2/r^{N−1})rⁿ`, `r = 1 − ε/(2N)`), `graphs_vs_L2_aperiodic` |
| graphs_vs_L2: `theo:db_stable_frozen_full` gives the rate of linearized descent | `graphs_vs_L2_rate` |
| graphs_vs_L2: `prop:morozov_rate` removes aperiodicity | `graphs_vs_L2_rate_sigma` |
| graphs_vs_L2: the balanced locus is one-dimensional; `Πh` conserved; the nonlinear mass increases | `graphs_vs_L2_balanced_ray`; the first conjunct of `graphs_vs_L2_rate`; `graphs_vs_L2_mass_monotone` |
| periodicity = return-time gcd `≠ 1` | `periodicAt_iff_setGcd` |

Witnesses: `sq_convexOn`, `sq_convex_small_deriv`, `sq_analyticOnNhd`, `sq_no_flat`
(`(x−1)²` inhabits the convex and analytic bundles); `thetaOK_twoStateBands`; `path_witness`
(`PeriodicAt` and the cyclic classes); `triangle_witness` (an aperiodic marked graph, on which
`Core.Mixing` holds and `visit_ratio_norm_S_le` applies).

## SCOPE (disclosed)

* **Finite state spaces throughout**, as everywhere in `GFNBounds.Balance`; the three remarks
  speak of finite graphs or of the finite two-state chain, except *(iv)*'s and
  `rem:visit_ratio`'s pointers to theorems whose general forms are other rows' business.
* **"Admissible" is carried only as far as it is used**: `g(1) = 0` and `g > 0` on `(0,∞) ∖ {1}`.
  Neither the quadratic growth bound nor `g''(1) = 2` enters *(i)*; `third_deriv_bound` carries
  `g''(1) = 2` as `g2 1 = 2`. *Convex* is `ConvexOn ℝ (Ioi 0) g`; *differentiable* is
  differentiability at every point of `(0,∞)`.
* **"Real-analytic"** is `AnalyticOnNhd ℝ g (Ioi 0)`; *an interval* is a non-degenerate open
  interval `(p,q) ⊂ (0,∞)` — a closed band `[α,β]`, `α < β`, contains one.
* **"`C³` on `[1,1+δ]`"** is carried as within-derivatives `g' → g''` and `g'' → g'''` on
  `[1,1+δ]` and a derivative of `g` at `1` (presupposed by the remark's `g'(1) = 0`; an
  admissible generator is only continuous); continuity of `g'''` is not used. The supremum form assumes `|g'''|` bounded on
  `[1,1+δ]`, which continuity would give.
* **The distance to the balanced ray** is measured in `L²(λ)` from the density `(2, 2(1−η))` of
  `μ = (1,1−η)` to the balanced density `2·𝟙`; it is `√2·η < 4√2·δ`, an explicit `O(δ)`.
* **"The radius must depend on `g` beyond `g''(1)`"** is stated twice. `radius_not_uniform_in_generator`:
  on the two-state chain with `w ≡ 1` (so `B̂ = 1`, `C_∞ = √2`, `w_min = ‖w‖_∞ = 1` fixed), no
  `ε₀ > 0` makes every gradient flow started within `ε₀` of `λ` converge to a balanced flow for
  all the generators of `prop:nonlinear_freezing` (which all have `g''(1) = 2`).
  `eps0C3_deltaBands_small`: the certified radius `eps0C3` of `local_convergence_full_C3`, all its
  other arguments fixed, is below every `ε > 0` at some band width. **Modelling note**: the frozen
  flows the remark exhibits, `μ = (1,1−η)`, are at distance `O(δ)` from the *ray* but not from `λ`
  (their `h = (1, 1−2η)`); the argument needs their rescaling `(1+h)λ`, `h = (0,−η)`, which is
  frozen too since ratios are scale-invariant. The remark leaves this rescaling implicit.
* **"Invisible to the linearization at balance"** is read as: on the set of flows whose ratios all
  lie in `[1−θ,1+θ]` — a neighbourhood of the balanced ray — the loss and its gradient density
  coincide with those of `(x−1)²`.
* ***(iv)*, the `(x−1)²` half of global convergence is not here** (Phase 2F), and the `(log x)²`
  half is certified on loop closures of finite path-connected marked graphs, the setting of
  `FlowExistence.no_distant_equilibrium_three_of_init`, not on every finite ergodic
  `(𝒮̂, λ, T)`. Both halves on every finite ergodic chain are
  `GlobalConvergenceFinite.no_distant_equilibrium_three_{logSq,sq}_of_ergodic`. "A bounded strictly
  unimodal generator not being covered; infinite state spaces
  are not addressed" are statements about the scope of the paper and carry nothing to certify.
  "The generators admitted by Brunswic et al. are not required to be convex" is a statement about
  a source and is not formalized.
* **`rem:visit_ratio`'s near-balance sentence is a pointer**: the linearized rate `ϱ` is
  `WeightedL2.stable_frozen_decay_finite` / `stable_frozen_discrete_mixing`, the nonlinear `ϱ/2` is
  `C3Wrappers.local_convergence_full_C3`; `cor:global_lojasiewicz` is its own row. They are not
  restated here. "A lower bound on the gradient mass bounds that time from neither side" sits in
  a heuristic clause and is not formalized. The lower bound is certified at every `μ ∼ λ`, not
  only along a trajectory.
* **`B̂_σ ≥ ‖S‖`** is proved where `lem:sigma_mixing` defines `S`: under summable mixing
  (`Core.Mixing (P, Π)`), `S = ∑ₙ(Pⁿ − Π)` in operator norm on `L²(λ)`.
* **`B̂ = +∞`** is stated as `∑' n, ENNReal.ofReal β̂ₙ = ⊤` together with `¬ Summable β̂` and
  `¬ Core.Mixing`: `Core.Mixing.B` is a real `tsum`, which Lean sets to `0` on a non-summable
  sequence, so it is not the right object to equate with `+∞`.
* **"Periodic"** is `PeriodicAt K x₀ d`: some `d ≥ 2` divides every return time to `x₀`.
  `periodicAt_iff_setGcd` proves it is exactly "the gcd of the return times is not `1`" (Mathlib's
  `Nat.setGcd`); aperiodic is its negation. For the leveled graph the cyclic classes are built
  directly, with period `ℓ(s_f) + 1` in `Morozov.Leveled`'s convention (the paper's `t_m + 2`,
  `Morozov.lean`'s SCOPE discusses the one-step shift).
* **"Geometrically ergodic"** is delivered as the `L²(λ)` statement the remark consumes,
  `β̂ₙ ≤ (2/r^{N−1}) rⁿ` with `r = 1 − ε/(2N) < 1`, `ε = min Kᴺ > 0`. `N` comes from Schur's
  theorem on numerical semigroups (`Nat.exists_mem_closure_of_ge`) and is **not effective**; given
  `N` and `ε` the constants are explicit (`beta_le_geometric_of_floor`).
* **The rate sentence** is certified for the linearized **descent** (the remark's word), via
  `WeightedL2.stable_frozen_discrete_mixing`; the flow half is `stable_frozen_decay_finite`.
* **"The uniqueness in *(2)* is the static counterpart of the conservation of `Πh_t`" and "the
  linearized training moves transversally to it"** are heuristic and not formalized; the three
  facts they relate are.
* **Not certified**: "`theo:universality_graphs` is more precise and less demanding than
  `theo:universality_L2`" as a comparison; its content — exactness, uniqueness, no aperiodicity —
  is `theo:universality_graphs`' own row, and the failure of the other theorem's hypothesis is
  `graphs_vs_L2_periodic`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `g` convex | `ConvexOn ℝ (Ioi 0) g` |
| `g` differentiable | `∀ x, 0 < x → DifferentiableAt ℝ g x` |
| `g` admissible | ⚠ only `g 1 = 0` and `∀ x, 0 < x → x ≠ 1 → 0 < g x`; see SCOPE |
| `g` real-analytic | `AnalyticOnNhd ℝ g (Ioi 0)` |
| `g' ≡ 0` on an interval | `∀ x ∈ Ioo p q, deriv g x = 0`, `0 < p < q` |
| `δ ∈ (0,1/4)`, `2δ < η < 4δ/(1+4δ)` | ✓ verbatim |
| the two-state chain | `Freezing.twoStateK`, `twoStateLam` |
| `g` `C³` on `[1,1+δ]`, `g''(1) = 2`, `g' ≡ 0` on `[1+δ,1+2δ]` | ⚠ derivative chain `g1, g2, g3` (see SCOPE), `g2 1 = 2`, `∀ x ∈ Icc (1+δ) (1+2δ), g1 x = 0` |
| `0 < θ < min(1−b, c−1)` | `ThetaOK F θ` |
| `ν` of positive density | `∀ x, 0 < nu x` |
| setting of `theo:training_speed_full` | loop closure of a finite path-connected marked graph, `IsInvProb`, `IsGreen`, `IsHitExp`, `u > 0`, `w ≥ w_min ≥ 0`; `g = (log x)²` as `logSqDeriv` |
| `U` with `|r−1| ≥ δ`, `δ ∈ (0,1/2]` | `U : Finset V`, `∀ x ∈ U, δ ≤ |ratio − 1|`, `0 < δ ≤ 1/2` |
| `S` defined | `Core.Mixing (densOp lam B.phat) (meanOp lam)` |
| leveled graph | `Morozov.Leveled` |
| loop closure periodic | `PeriodicAt B.phat x₀ d` (≡ return-time gcd `≠ 1`) |
| loop closure aperiodic | `¬ ∃ d, PeriodicAt B.phat x₀ d` |
| finite irreducible chain | `Core.IsMarkov K`, `Core.IsInvariant lam K`, `lam > 0`, `∑ lam = 1`, `∀ x y, ∃ n, ReachIn K n x y` |
| step `ε ≤ (4g''(1)‖w‖_∞)⁻¹` | `eps * (4 * g2 * wsup) ≤ 1` |
| strictly unimodal generator, gradient flow | `StrictlyUnimodal gd`, `IsGradientFlow`, positivity along the flow |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance.RemarksA

open Filter Topology Set
open scoped ContDiff

/-! ## `rem:freezing` (i): convexity, analyticity, and `(log x)²` -/

section FreezingOne

/-- **A convex admissible generator has `g' ≠ 0` off `1`.** -/
theorem convex_deriv_ne_zero {g : ℝ → ℝ} (hconv : ConvexOn ℝ (Ioi 0) g)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g x) (hg1 : g 1 = 0)
    (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    deriv g x ≠ 0 := by
  intro h0
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · have hs := hconv.deriv_le_slope (mem_Ioi.2 hx) (mem_Ioi.2 one_pos) hlt (hdiff x hx)
    rw [h0, slope_def_field, hg1] at hs
    have hd : 0 < 1 - x := by linarith
    have := (le_div_iff₀ hd).1 hs
    linarith [hgpos x hx hx1]
  · have hs := hconv.slope_le_deriv (mem_Ioi.2 one_pos) (mem_Ioi.2 hx) hgt (hdiff x hx)
    rw [h0, slope_def_field, hg1] at hs
    have hd : 0 < x - 1 := by linarith
    have := (div_le_iff₀ hd).1 hs
    linarith [hgpos x hx hx1]

/-- **`rem:freezing`*(i)*, first sentence**: a convex admissible generator has no flat band
`[α, β] ⊂ (0,1)` or `[α, β] ⊂ (1,∞)`. -/
theorem convex_no_flat_band {g : ℝ → ℝ} (hconv : ConvexOn ℝ (Ioi 0) g)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g x) (hg1 : g 1 = 0)
    (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) {α β : ℝ} (hαβ : α ≤ β) (hα : 0 < α)
    (hside : β < 1 ∨ 1 < α) :
    ¬ ∀ x ∈ Icc α β, deriv g x = 0 := by
  intro h
  have hβ1 : β ≠ 1 := by
    rcases hside with h1 | h1
    · exact h1.ne
    · exact (lt_of_lt_of_le h1 hαβ).ne'
  exact convex_deriv_ne_zero hconv hdiff hg1 hgpos (hα.trans_le hαβ) hβ1
    (h β ⟨hαβ, le_rfl⟩)

/-- `g'(1) = 0` for a differentiable admissible generator: `1` is a minimum. -/
theorem deriv_one_eq_zero {g : ℝ → ℝ} (hd : DifferentiableAt ℝ g 1) (hg1 : g 1 = 0)
    (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) : deriv g 1 = 0 := by
  have hmin : IsLocalMin g 1 := by
    filter_upwards [Ioi_mem_nhds (one_pos : (0:ℝ) < 1)] with x hx
    rcases eq_or_ne x 1 with h | h
    · rw [h]
    · rw [hg1]; exact (hgpos x hx h).le
  exact hmin.hasDerivAt_eq_zero hd.hasDerivAt

/-- **`rem:freezing`*(i)*, second sentence**: a convex differentiable admissible generator has
`g' ≤ 0` on `(0,1)`, and `|g'(x₀)| ≤ ε` at one `x₀ < 1` forces `|g'| ≤ ε` and
`g ≤ ε(1 − x₀)` on `[x₀, 1]`. -/
theorem convex_small_deriv {g : ℝ → ℝ} (hconv : ConvexOn ℝ (Ioi 0) g)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g x) (hg1 : g 1 = 0)
    (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) :
    (∀ x : ℝ, 0 < x → x < 1 → deriv g x ≤ 0) ∧
      ∀ {x₀ ε : ℝ}, 0 < x₀ → x₀ < 1 → |deriv g x₀| ≤ ε →
        ∀ x ∈ Icc x₀ 1, |deriv g x| ≤ ε ∧ g x ≤ ε * (1 - x₀) := by
  have hmono : MonotoneOn (deriv g) (Ioi 0) :=
    hconv.monotoneOn_deriv fun x hx => hdiff x hx
  have h1 : deriv g 1 = 0 := deriv_one_eq_zero (hdiff 1 one_pos) hg1 hgpos
  have hle : ∀ x : ℝ, 0 < x → x ≤ 1 → deriv g x ≤ 0 := fun x hx hx1 => by
    have := hmono (mem_Ioi.2 hx) (mem_Ioi.2 one_pos) hx1
    rwa [h1] at this
  refine ⟨fun x hx hx1 => hle x hx hx1.le, fun {x₀ ε} hx₀ hx₀1 hε x hx => ?_⟩
  obtain ⟨hxl, hxr⟩ := hx
  have hxpos : 0 < x := hx₀.trans_le hxl
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hε
  have hd0 : deriv g x₀ ≤ deriv g x := hmono (mem_Ioi.2 hx₀) (mem_Ioi.2 hxpos) hxl
  have hdx : deriv g x ≤ 0 := hle x hxpos hxr
  have hdx0 : deriv g x₀ ≤ 0 := hle x₀ hx₀ hx₀1.le
  have habs : |deriv g x| ≤ ε := by
    rw [abs_of_nonpos hdx]
    rw [abs_of_nonpos hdx0] at hε
    linarith
  refine ⟨habs, ?_⟩
  rcases eq_or_lt_of_le hxr with hx1 | hx1
  · rw [hx1, hg1]; exact mul_nonneg hε0 (by linarith)
  · have hs := hconv.deriv_le_slope (mem_Ioi.2 hxpos) (mem_Ioi.2 one_pos) hx1 (hdiff x hxpos)
    rw [slope_def_field, hg1] at hs
    have hd : 0 < 1 - x := by linarith
    have hgx : g x ≤ -deriv g x * (1 - x) := by
      have := (le_div_iff₀ hd).1 hs
      linarith
    have hab : -deriv g x ≤ ε := by rw [abs_of_nonpos hdx] at habs; exact habs
    calc g x ≤ -deriv g x * (1 - x) := hgx
      _ ≤ ε * (1 - x) := mul_le_mul_of_nonneg_right hab hd.le
      _ ≤ ε * (1 - x₀) := mul_le_mul_of_nonneg_left (by linarith) hε0

/-- **`rem:freezing`*(i)*, third sentence**: a generator real-analytic on `(0,∞)` whose derivative
vanishes on a non-degenerate interval `(p, q) ⊂ (0,∞)` is constant on `(0,∞)`. -/
theorem analytic_const_of_flat {g : ℝ → ℝ} (han : AnalyticOnNhd ℝ g (Ioi 0)) {p q : ℝ}
    (hp : 0 < p) (hpq : p < q) (hflat : ∀ x ∈ Ioo p q, deriv g x = 0) :
    ∀ x y : ℝ, 0 < x → 0 < y → g x = g y := by
  have hdan : AnalyticOnNhd ℝ (deriv g) (Ioi 0) := han.deriv
  set z₀ : ℝ := (p + q) / 2 with hz₀
  have hz₀mem : z₀ ∈ Ioo p q := ⟨by rw [hz₀]; linarith, by rw [hz₀]; linarith⟩
  have hev : deriv g =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [Ioo_mem_nhds hz₀mem.1 hz₀mem.2] with x hx
    exact hflat x hx
  have hzero : EqOn (deriv g) 0 (Ioi 0) :=
    hdan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioi
      (mem_Ioi.2 (hp.trans hz₀mem.1)) hev
  intro x y hx hy
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi han.differentiableOn hzero
    (mem_Ioi.2 hx) (mem_Ioi.2 hy)

/-- **`rem:freezing`*(i)*: real-analytic admissible generators cannot freeze exactly** — no
admissible `g` real-analytic on `(0,∞)` has `g' ≡ 0` on a non-degenerate interval of `(0,∞)`. -/
theorem analytic_admissible_no_flat {g : ℝ → ℝ} (han : AnalyticOnNhd ℝ g (Ioi 0))
    (hg1 : g 1 = 0) (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) {p q : ℝ} (hp : 0 < p)
    (hpq : p < q) : ¬ ∀ x ∈ Ioo p q, deriv g x = 0 := by
  intro hflat
  have h := analytic_const_of_flat han hp hpq hflat 1 2 one_pos two_pos
  have h2 := hgpos 2 two_pos (by norm_num)
  linarith

/-! ### `(log x)²` -/

/-- **`g''(x) = 2(1 − log x)/x²`** for `g = (log x)²`, as the derivative of `logSqDeriv`. -/
theorem hasDerivAt_logSqDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt logSqDeriv (2 * (1 - Real.log x) / x ^ 2) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h : HasDerivAt (fun y : ℝ => 2 * Real.log y / y)
      ((2 * x⁻¹ * x - 2 * Real.log x * 1) / x ^ 2) x :=
    (hlog.const_mul 2).div (hasDerivAt_id' x) hx.ne'
  refine h.congr_deriv ?_
  field_simp

/-- **`rem:freezing`*(i)*: `g''(x) = 2(1 − log x)/x²`** for `g = (log x)²`, as the second
derivative of `logSq` itself. -/
theorem deriv_deriv_logSq {x : ℝ} (hx : 0 < x) :
    deriv (deriv logSq) x = 2 * (1 - Real.log x) / x ^ 2 := by
  have hev : deriv logSq =ᶠ[𝓝 x] logSqDeriv := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (hasDerivAt_logSq hy).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_logSqDeriv hx).deriv

/-- **`rem:freezing`*(i)*: `g'' < 0` on `(e, ∞)`** for `g = (log x)²`. -/
theorem deriv_deriv_logSq_neg {x : ℝ} (hx : Real.exp 1 < x) : deriv (deriv logSq) x < 0 := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans hx
  rw [deriv_deriv_logSq hx0]
  have hlog : 1 < Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hx
  have hx2 : 0 < x ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hx2

/-- **`rem:freezing`*(i)*: `(log x)²` is not convex** on `(0,∞)`: its derivative would be monotone,
and `g'(e) = 2/e > 4/e² = g'(e²)` since `e > 2`. -/
theorem logSq_not_convexOn : ¬ ConvexOn ℝ (Ioi 0) logSq := by
  intro hconv
  have hmono := hconv.monotoneOn_deriv fun x hx => (hasDerivAt_logSq hx).differentiableAt
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have he2 : (0:ℝ) < Real.exp 2 := Real.exp_pos 2
  have hle : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.2 (by norm_num)
  have h := hmono (mem_Ioi.2 he) (mem_Ioi.2 he2) hle
  rw [(hasDerivAt_logSq he).deriv, (hasDerivAt_logSq he2).deriv] at h
  simp only [logSqDeriv, Real.log_exp] at h
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [hexp2, div_le_div_iff₀ he (mul_pos he he)] at h
  have hgt : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  nlinarith

/-- **`rem:freezing`*(i)*: `g' → 0` at `+∞`** for `g = (log x)²`. -/
theorem tendsto_logSqDeriv_atTop : Tendsto logSqDeriv atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards with x
  simp only [logSqDeriv, pow_one, one_mul, add_zero]
  ring

/-- **`rem:freezing`*(i)*: `|g'| → ∞` at `0⁺`** for `g = (log x)²`. -/
theorem tendsto_abs_logSqDeriv_nhdsGT_zero :
    Tendsto (fun x => |logSqDeriv x|) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun x => -(2 * Real.log x)) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.const_mul_atBot two_pos)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [Ioo_mem_nhdsGT (one_pos : (0:ℝ) < 1)] with x hx
  obtain ⟨hx0, hx1⟩ := hx
  have hlog : Real.log x < 0 := Real.log_neg hx0 hx1
  have hq : logSqDeriv x < 0 := div_neg_of_neg_of_pos (by linarith) hx0
  rw [abs_of_neg hq, logSqDeriv]
  rw [neg_le_neg_iff, div_le_iff₀ hx0]
  nlinarith

/-- **`rem:freezing`*(i)*: `(log x)²` has no spurious critical point** — it is strictly unimodal,
so by `prop:no_distant_equilibrium`*(1)* every flow at which every directional derivative of
`𝓛_{(log x)², ν}` vanishes is balanced, for `ν` of positive density. -/
theorem logSq_critical_balanced {V : Type*} [Fintype V] {K : V → V → ℝ} {lam nu u : V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hnu : ∀ x, 0 < nu x)
    (hcrit : ∀ d : V → ℝ,
      HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) logSq) 0 0) :
    Balanced K lam u :=
  balanced_of_hasDerivAt_zero hinv hK hlam hu hnu (fun _ hy => hasDerivAt_logSq hy)
    logSqDeriv_strictlyUnimodal hcrit

end FreezingOne

/-! ## `rem:freezing` (ii): frozen flows at distance `O(δ)`, and `sup|g'''| ≥ 4/δ` -/

section FreezingTwo

/-- **The bands of `rem:freezing`*(ii)***: `(a,b,c,d) = (1−2δ, 1−δ, 1+δ, 1+2δ)` for
`δ ∈ (0, 1/4)`. -/
noncomputable def deltaBands (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 4) : FreezingBands where
  a := 1 - 2 * δ
  b := 1 - δ
  c := 1 + δ
  d := 1 + 2 * δ
  a_pos := by linarith
  a_lt_b := by linarith
  b_lt_one := by linarith
  one_lt_c := by linarith
  c_lt_d := by linarith

/-- The density `(s, s(1−η))` against `λ = (1/2,1/2)`: at `s = 2` the flow `μ = (1, 1−η)` of the
remark, at `s = 1` the flow `(1+h)λ` with `h = (0, −η)`. -/
noncomputable def etaVec (s η : ℝ) : Fin 2 → ℝ := ![s, s * (1 - η)]

theorem etaVec_pos {s η : ℝ} (hs : 0 < s) (hη : η < 1) (x : Fin 2) : 0 < etaVec s η x := by
  fin_cases x
  · show 0 < s; exact hs
  · show 0 < s * (1 - η); exact mul_pos hs (by linarith)

/-- `r(0) = 1 − η/2` on the two-state chain. -/
theorem ratio_etaVec_zero {s η : ℝ} (hs : 0 < s) :
    ratio twoStateK twoStateLam (etaVec s η) 0 = 1 - η / 2 := by
  have hs' : s ≠ 0 := hs.ne'
  simp only [ratio, pushMass, twoStateK, twoStateLam, etaVec, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- `r(1) = (1 − η/2)/(1 − η)` on the two-state chain. -/
theorem ratio_etaVec_one {s η : ℝ} (hs : 0 < s) (hη : η < 1) :
    ratio twoStateK twoStateLam (etaVec s η) 1 = (1 - η / 2) / (1 - η) := by
  have hs' : s ≠ 0 := hs.ne'
  have h1 : (1:ℝ) - η ≠ 0 := by intro h; linarith
  simp only [ratio, pushMass, twoStateK, twoStateLam, etaVec, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- **The window of `rem:freezing`*(ii)***: for `2δ < η < 4δ/(1+4δ)` the two ratios lie in
`U⁻ = (1−2δ, 1−δ)` and `U⁺ = (1+δ, 1+2δ)`. -/
theorem etaVec_mem_frozen {δ η s : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 4) (hs : 0 < s)
    (hη1 : 2 * δ < η) (hη2 : η < 4 * δ / (1 + 4 * δ)) :
    etaVec s η ∈ frozen twoStateK twoStateLam (deltaBands δ h0 h1).bands := by
  have hd : 0 < 1 + 4 * δ := by linarith
  have hη2' : η * (1 + 4 * δ) < 4 * δ := (lt_div_iff₀ hd).1 hη2
  have hηlt1 : η < 1 := by nlinarith
  have hpos1 : 0 < 1 - η := by linarith
  refine ⟨etaVec_pos hs hηlt1, ?_⟩
  intro x
  fin_cases x
  · left
    show ratio twoStateK twoStateLam (etaVec s η) 0 ∈ Ioo (1 - 2 * δ) (1 - δ)
    rw [ratio_etaVec_zero hs]
    constructor <;> nlinarith
  · right
    show ratio twoStateK twoStateLam (etaVec s η) 1 ∈ Ioo (1 + δ) (1 + 2 * δ)
    rw [ratio_etaVec_one hs hηlt1]
    constructor
    · rw [lt_div_iff₀ hpos1]; nlinarith
    · rw [div_lt_iff₀ hpos1]; nlinarith

/-- **`rem:freezing`*(ii)*, the frozen flows**: for `δ ∈ (0,1/4)` and `2δ < η < 4δ/(1+4δ)`, the
flow `μ = (1, 1−η)` on the two-state chain (density `u = (2, 2(1−η))` against `λ`) has
`r = (1 − η/2, (1−η/2)/(1−η)) ∈ U⁻ × U⁺`; so item *(1)* of `prop:nonlinear_freezing` freezes it
for the generator of the bands `(1−2δ, 1−δ, 1+δ, 1+2δ)` — its gradient density vanishes for
every training measure, the loss has Fréchet derivative `0` there for every `ν`, and every
gradient-descent step fixes it — and it lies at `L²(λ)`-distance `√2·η < 4√2·δ` from the
balanced flow `2·𝟙` of the balanced ray. -/
theorem freezing_two_frozen {δ η : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 4) (hη1 : 2 * δ < η)
    (hη2 : η < 4 * δ / (1 + 4 * δ)) :
    ratio twoStateK twoStateLam (etaVec 2 η) 0 = 1 - η / 2
      ∧ ratio twoStateK twoStateLam (etaVec 2 η) 1 = (1 - η / 2) / (1 - η)
      ∧ etaVec 2 η ∈ frozen twoStateK twoStateLam (deltaBands δ h0 h1).bands
      ∧ (∀ (w : Fin 2 → ℝ) (x : Fin 2),
          lossGradDensity twoStateK twoStateLam (etaVec 2 η) w (deriv (deltaBands δ h0 h1).g) x
            = 0)
      ∧ (∀ nu : Fin 2 → ℝ, HasFDerivAt
          (fun u' => loss twoStateK twoStateLam nu u' (deltaBands δ h0 h1).g)
          (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (etaVec 2 η))
      ∧ (∀ (w : Fin 2 → ℝ) (eps : ℝ), (fun x => etaVec 2 η x - eps *
          lossGradDensity twoStateK twoStateLam (etaVec 2 η) w (deriv (deltaBands δ h0 h1).g) x)
            = etaVec 2 η)
      ∧ Balanced twoStateK twoStateLam (fun _ => 2)
      ∧ Graph.nrmL2 twoStateLam (fun x => etaVec 2 η x - 2) = Real.sqrt 2 * η
      ∧ Real.sqrt 2 * η < 4 * Real.sqrt 2 * δ := by
  set F := deltaBands δ h0 h1 with hF
  have hd : 0 < 1 + 4 * δ := by linarith
  have hη2' : η * (1 + 4 * δ) < 4 * δ := (lt_div_iff₀ hd).1 hη2
  have hηlt1 : η < 1 := by nlinarith
  have hη0 : 0 < η := by linarith
  have hmem := etaVec_mem_frozen h0 h1 two_pos hη1 hη2
  have hgd : ∀ z ∈ F.bands, deriv F.g z = 0 := fun _ hz => F.deriv_g_eq_zero_of_mem_bands' hz
  refine ⟨ratio_etaVec_zero two_pos, ratio_etaVec_one two_pos hηlt1, hmem,
    fun w x => freezing_critical hmem.2 hgd x, fun nu => ?_, fun w eps => ?_, ?_, ?_, ?_⟩
  · exact hasFDerivAt_loss_zero_of F (fun x _ => (F.differentiable_g x).hasDerivAt) hgd
      twoStateLam_pos hmem nu
  · exact freezing_descent_stationary hmem.2 hgd eps
  · intro y
    simp only [pushMass, twoStateK, twoStateLam, Fin.sum_univ_two]
    ring
  · have hval : Graph.ipL2 twoStateLam (fun x => etaVec 2 η x - 2) (fun x => etaVec 2 η x - 2)
        = (Real.sqrt 2 * η) ^ 2 := by
      simp only [Graph.ipL2, twoStateLam, etaVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    rw [Graph.nrmL2, hval, Real.sqrt_sq (by positivity)]
  · have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
    have : η < 4 * δ := by nlinarith
    nlinarith

/-- **`rem:freezing`*(ii)*, the numerical instance**: at `δ = 1/10`, `η = 1/4` lies in the window
and gives `r = (0.875, 7/6)`, `7/6 = 1.1667` to four decimals. -/
theorem freezing_two_example :
    2 * (1 / 10 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 4 * (1 / 10) / (1 + 4 * (1 / 10))
      ∧ ratio twoStateK twoStateLam (etaVec 2 (1 / 4)) 0 = 0.875
      ∧ ratio twoStateK twoStateLam (etaVec 2 (1 / 4)) 1 = 7 / 6
      ∧ |ratio twoStateK twoStateLam (etaVec 2 (1 / 4)) 1 - 1.1667| < 1 / 20000 := by
  have h1 : ratio twoStateK twoStateLam (etaVec 2 (1 / 4)) 1 = 7 / 6 := by
    rw [ratio_etaVec_one two_pos (by norm_num)]; norm_num
  refine ⟨by norm_num, by norm_num, ?_, h1, ?_⟩
  · rw [ratio_etaVec_zero two_pos]; norm_num
  · rw [h1, abs_lt]; constructor <;> norm_num

/-- **`rem:freezing`*(ii)*, the third-derivative bound**: an admissible generator, differentiable
at `1`, with `g''` and `g'''` on `[1, 1+δ]`, `g''(1) = 2` and `g' ≡ 0` on `[1+δ, 1+2δ]` has
`|g'''| ≤ M` on `[1, 1+δ]` only for `M ≥ 4/δ`. -/
theorem third_deriv_bound {g g1 g2 g3 : ℝ → ℝ} {δ M : ℝ} (hδ : 0 < δ)
    (hg1 : g 1 = 0) (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x)
    (hd0 : HasDerivAt g (g1 1) 1)
    (hd1 : ∀ x ∈ Icc 1 (1 + δ), HasDerivWithinAt g1 (g2 x) (Icc 1 (1 + δ)) x)
    (hd2 : ∀ x ∈ Icc 1 (1 + δ), HasDerivWithinAt g2 (g3 x) (Icc 1 (1 + δ)) x)
    (hflat : ∀ x ∈ Icc (1 + δ) (1 + 2 * δ), g1 x = 0) (h2 : g2 1 = 2)
    (hM : ∀ x ∈ Icc 1 (1 + δ), |g3 x| ≤ M) :
    4 / δ ≤ M := by
  set D := Icc (1:ℝ) (1 + δ) with hD
  have hint : interior D = Ioo 1 (1 + δ) := interior_Icc
  have hmemD : ∀ x ∈ Ioo (1:ℝ) (1 + δ), x ∈ D := fun x hx => Ioo_subset_Icc_self hx
  have h10 : g1 1 = 0 := by
    have hmin : IsLocalMin g 1 := by
      filter_upwards [Ioi_mem_nhds (one_pos : (0:ℝ) < 1)] with x hx
      rcases eq_or_ne x 1 with h | h
      · rw [h]
      · rw [hg1]; exact (hgpos x hx h).le
    exact hmin.hasDerivAt_eq_zero hd0
  have h1d : g1 (1 + δ) = 0 := hflat _ ⟨le_rfl, by linarith⟩
  have h1D : (1:ℝ) ∈ D := ⟨le_rfl, by linarith⟩
  have hdD : (1 + δ) ∈ D := ⟨by linarith, le_rfl⟩
  -- `ψ = g'' + M(x − 1)` is nondecreasing on `[1, 1+δ]`
  have hψ : MonotoneOn (fun x => g2 x + M * (x - 1)) D := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => g3 x + M * 1)
      (convex_Icc _ _) ?_ ?_ ?_
    · intro x hx
      exact ((hd2 x hx).continuousWithinAt).add
        (continuousWithinAt_const.mul (continuousWithinAt_id.sub continuousWithinAt_const))
    · intro x hx
      rw [hint] at hx ⊢
      exact ((hd2 x (hmemD x hx)).mono Ioo_subset_Icc_self).add
        ((((hasDerivAt_id' x).sub_const 1).const_mul M).hasDerivWithinAt)
    · intro x hx
      rw [hint] at hx
      have := hM x (hmemD x hx)
      have := neg_abs_le (g3 x)
      linarith
  have hψge : ∀ x ∈ D, 2 ≤ g2 x + M * (x - 1) := fun x hx => by
    have := hψ h1D hx hx.1
    simpa only [h2, sub_self, mul_zero, add_zero] using this
  -- `φ = g' − 2(x−1) + M(x−1)²/2` is nondecreasing on `[1, 1+δ]`
  have hφ : MonotoneOn (fun x => g1 x - 2 * (x - 1) + M * (x - 1) ^ 2 / 2) D := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun x => g2 x - 2 * 1 + M * (↑(2:ℕ) * (x - 1) ^ (2 - 1) * 1) / 2)
      (convex_Icc _ _) ?_ ?_ ?_
    · intro x hx
      exact (((hd1 x hx).continuousWithinAt).sub
        (continuousWithinAt_const.mul (continuousWithinAt_id.sub continuousWithinAt_const))).add
        ((continuousWithinAt_const.mul
          ((continuousWithinAt_id.sub continuousWithinAt_const).pow 2)).div_const 2)
    · intro x hx
      rw [hint] at hx ⊢
      have hA := (hd1 x (hmemD x hx)).mono Ioo_subset_Icc_self
      have hB := (((hasDerivAt_id' x).sub_const 1).const_mul 2).hasDerivWithinAt
        (s := Ioo 1 (1 + δ))
      have hC := (((((hasDerivAt_id' x).sub_const 1).pow 2).const_mul M).div_const
        2).hasDerivWithinAt (s := Ioo 1 (1 + δ))
      exact (hA.sub hB).add hC
    · intro x hx
      rw [hint] at hx
      have := hψge x (hmemD x hx)
      simp only [Nat.cast_ofNat, mul_one]
      linarith
  have hfin := hφ h1D hdD (by linarith)
  simp only [h10, h1d, sub_self, mul_zero, zero_sub, add_sub_cancel_left] at hfin
  rw [div_le_iff₀ hδ]
  nlinarith

end FreezingTwo

/-! ### The third-derivative bound, as a supremum, and on the generator of the bands -/

section FreezingTwoSup

/-- **`rem:freezing`*(ii)*: `sup_{[1,1+δ]} |g'''| ≥ 4/δ`**, the supremum form of
`third_deriv_bound`, for a `|g'''|` bounded on `[1, 1+δ]`. -/
theorem third_deriv_sSup {g g1 g2 g3 : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hg1 : g 1 = 0) (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x)
    (hd0 : HasDerivAt g (g1 1) 1)
    (hd1 : ∀ x ∈ Icc 1 (1 + δ), HasDerivWithinAt g1 (g2 x) (Icc 1 (1 + δ)) x)
    (hd2 : ∀ x ∈ Icc 1 (1 + δ), HasDerivWithinAt g2 (g3 x) (Icc 1 (1 + δ)) x)
    (hflat : ∀ x ∈ Icc (1 + δ) (1 + 2 * δ), g1 x = 0) (h2 : g2 1 = 2)
    (hbdd : BddAbove ((fun x => |g3 x|) '' Icc 1 (1 + δ))) :
    4 / δ ≤ sSup ((fun x => |g3 x|) '' Icc 1 (1 + δ)) :=
  third_deriv_bound hδ hg1 hgpos hd0 hd1 hd2 hflat h2 fun _ hx =>
    le_csSup hbdd (mem_image_of_mem _ hx)

/-- **The bound is met by the generator of the bands**: for `F = deltaBands δ`, the `C^∞`
admissible generator of `prop:nonlinear_freezing` at `(1−2δ, 1−δ, 1+δ, 1+2δ)` has
`sup_{[1,1+δ]} |g'''| ≥ 4/δ` — so the hypothesis bundle of `third_deriv_sSup` is inhabited,
at every `δ ∈ (0, 1/4)`. -/
theorem deltaBands_third_deriv {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 4) :
    4 / δ ≤ sSup ((fun x => |deriv (deriv (deriv (deltaBands δ h0 h1).g)) x|) ''
      Icc 1 (1 + δ)) := by
  set F := deltaBands δ h0 h1 with hF
  obtain ⟨hdg, hc1⟩ := contDiff_infty_iff_deriv.1 F.contDiff_g
  obtain ⟨hdg1, hc2⟩ := contDiff_infty_iff_deriv.1 hc1
  obtain ⟨hdg2, hc3⟩ := contDiff_infty_iff_deriv.1 hc2
  refine third_deriv_sSup h0 F.g_one (fun x _ hx => F.g_pos hx) (hdg 1).hasDerivAt
    (fun x _ => (hdg1 x).hasDerivAt.hasDerivWithinAt)
    (fun x _ => (hdg2 x).hasDerivAt.hasDerivWithinAt) (fun x hx => ?_) F.deriv_deriv_g_one ?_
  · exact F.deriv_g_eq_zero_of_mem_bands (Or.inr hx)
  · exact isCompact_Icc.bddAbove_image hc3.continuous.abs.continuousOn

end FreezingTwoSup

/-! ### The radius of the local convergence theorem cannot depend on `g''(1)` alone -/

section FreezingTwoRadius

/-- **Frozen flows arbitrarily close to balance, at `g''(1) = 2`**: for every `ε > 0` some
`C^∞` admissible generator with `g''(1) = 2` (the generator of `deltaBands`) has, on the two-state
chain — `β̂ₙ = 0` for `n ≥ 1`, `B̂ = 1` — a flow `(1+h)λ` with `‖h‖_{L²(λ)} ≤ ε` which is not
balanced and whose constant curve is a gradient flow for every training measure. -/
theorem frozen_near_balance {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 4) (h : Fin 2 → ℝ),
      ContDiff ℝ ∞ (deltaBands δ h0 h1).g ∧ deriv (deriv (deltaBands δ h0 h1).g) 1 = 2
      ∧ Graph.nrmL2 twoStateLam h ≤ ε
      ∧ ¬ Balanced twoStateK twoStateLam (fun x => 1 + h x)
      ∧ ∀ nu : Fin 2 → ℝ, IsGradientFlow twoStateK twoStateLam nu (deriv (deltaBands δ h0 h1).g)
          (fun _ x => 1 + h x) := by
  set δ : ℝ := min (1 / 24) (ε / 6) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ24 : δ ≤ 1 / 24 := min_le_left _ _
  have hδε : δ ≤ ε / 6 := min_le_right _ _
  have hδ1 : δ < 1 / 4 := lt_of_le_of_lt hδ24 (by norm_num)
  have hη1 : 2 * δ < 3 * δ := by linarith
  have hη2 : 3 * δ < 4 * δ / (1 + 4 * δ) := by
    rw [lt_div_iff₀ (by linarith)]; nlinarith
  set F := deltaBands δ hδ0 hδ1 with hF
  have hmem := etaVec_mem_frozen hδ0 hδ1 one_pos hη1 hη2
  have hveq : (fun x => 1 + ![0, -(3 * δ)] x) = etaVec 1 (3 * δ) := by
    funext x
    fin_cases x
    · simp only [etaVec, Fin.zero_eta, Matrix.cons_val_zero, add_zero]
    · simp only [etaVec, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]
      ring
  refine ⟨δ, hδ0, hδ1, ![0, -(3 * δ)], F.contDiff_g, F.deriv_deriv_g_one, ?_, ?_, ?_⟩
  · have hval : Graph.ipL2 twoStateLam ![0, -(3 * δ)] ![0, -(3 * δ)] = (3 * δ) ^ 2 / 2 := by
      simp only [Graph.ipL2, twoStateLam, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    rw [Graph.nrmL2, hval]
    calc Real.sqrt ((3 * δ) ^ 2 / 2) ≤ Real.sqrt ((3 * δ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (3 * δ)])
      _ = 3 * δ := Real.sqrt_sq (by linarith)
      _ ≤ ε := by linarith
  · rw [hveq]
    intro hbal
    have hr := (ratio_eq_one_iff_balanced
      (fun y => mul_pos (twoStateLam_pos y) (etaVec_pos one_pos (by linarith) y))).2 hbal 0
    rw [ratio_etaVec_zero one_pos] at hr
    linarith
  · intro nu t _ x
    rw [hveq]
    have hz : lossGrad twoStateK twoStateLam nu (deriv F.g) (etaVec 1 (3 * δ)) x = 0 :=
      freezing_critical hmem.2 (fun _ hz => F.deriv_g_eq_zero_of_mem_bands' hz) x
    rw [hz, neg_zero]
    exact hasDerivAt_const t _

/-- **`rem:freezing`*(ii)*, last clause: the radius `ε₀` of `theo:local_convergence_full` must
depend on `g` beyond `g''(1)`.** On the two-state chain with `w ≡ 1` — so `B̂ = 1`,
`C_∞ = √2`, `w_min = ‖w‖_∞ = 1`, all fixed — no single `ε₀ > 0` makes every gradient flow started
within `ε₀` of `λ` in `L²(λ)` converge to a balanced flow, uniformly over the `C^∞` admissible
generators with `g''(1) = 2` of `prop:nonlinear_freezing`. -/
theorem radius_not_uniform_in_generator :
    ¬ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (F : FreezingBands) (u : ℝ → Fin 2 → ℝ),
      IsGradientFlow twoStateK twoStateLam twoStateLam (deriv F.g) u →
      Graph.nrmL2 twoStateLam (fun x => u 0 x - 1) ≤ ε₀ →
      ∃ c : Fin 2 → ℝ, Balanced twoStateK twoStateLam c ∧ Tendsto u atTop (𝓝 c) := by
  rintro ⟨ε₀, hε₀, hconv⟩
  obtain ⟨δ, h0, h1, h, -, -, hnrm, hnbal, hflow⟩ := frozen_near_balance hε₀
  have hnrm' : Graph.nrmL2 twoStateLam (fun x => (fun _ x => 1 + h x : ℝ → Fin 2 → ℝ) 0 x - 1)
      ≤ ε₀ := by
    have he : (fun x => (fun _ x => 1 + h x : ℝ → Fin 2 → ℝ) 0 x - 1) = h := by
      funext x; ring
    rw [he]; exact hnrm
  obtain ⟨c, hc, hlim⟩ := hconv _ _ (hflow twoStateLam) hnrm'
  have hvc : (fun x => 1 + h x) = c := tendsto_nhds_unique tendsto_const_nhds hlim
  exact hnbal (hvc ▸ hc)

end FreezingTwoRadius

/-! ### The certified radius of `theo:local_convergence_full` shrinks with the band width -/

section RadiusCertified

/-- **`rem:freezing`*(ii)*, last clause, on the certified radius itself**: the radius
`ε₀ = eps0C3 g a w_min ‖w‖_∞ B̂ λ_min` of `C3Wrappers.local_convergence_full_C3`, evaluated on the
two-state chain (`a = 1/2`, `w ≡ 1`, `B̂ = 1`, `λ_min = 1/2` — every argument but `g` fixed) at the
`C^∞` admissible generators of `deltaBands` (all with `g''(1) = 2`), takes values below every
`ε > 0`: a frozen flow within `ε` of `λ` is not balanced, so the theorem cannot apply to it. -/
theorem eps0C3_deltaBands_small {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 4),
      eps0C3 (deltaBands δ h0 h1).g (1 / 2) 1 1 1 (1 / 2) < ε := by
  obtain ⟨δ, h0, h1, h, -, hg2, hnrm, hnbal, hflow⟩ := frozen_near_balance hε
  refine ⟨δ, h0, h1, lt_of_lt_of_le (not_le.1 fun hle => hnbal ?_) hnrm⟩
  set F := deltaBands δ h0 h1 with hF
  have hK : Core.IsMarkov twoStateK :=
    ⟨fun _ _ => by norm_num [twoStateK], twoStateK_row⟩
  have hinv : Core.IsInvariant twoStateLam twoStateK :=
    ⟨fun x => (twoStateLam_pos x).le, twoStateK_invariant⟩
  have hC3 : ∀ y ∈ Icc (1 - 1 / 2 : ℝ) (1 + 1 / 2), ContDiffAt ℝ 3 F.g y := fun y _ =>
    F.contDiff_g.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have hd1 : deriv F.g 1 = 0 := by rw [F.deriv_g]; ring
  have hcoer : ∀ f : Fin 2 → ℝ, Graph.nrmL2 twoStateLam (perpL2 twoStateLam f)
      ≤ 1 * Graph.nrmL2 twoStateLam (Aop twoStateK twoStateLam f) := fun f => by
    rw [twoState_Aop_eq_neg_perp, nrmL2_neg, one_mul]
  have hflow' : IsGradientFlow twoStateK twoStateLam (fun z => twoStateLam z * (fun _ => (1:ℝ)) z)
      (deriv F.g) fun _ x => 1 + h x := hflow _
  obtain ⟨cinf, -, hdec⟩ := local_convergence_full_C3 (h := fun _ => h) (w := fun _ => (1:ℝ))
    (a := 1 / 2) (wsup := 1) (wmin := 1) (Bhat := 1) (lamMin := 1 / 2)
    (hK.toIsMarkovOn twoStateLam) hinv twoStateLam_pos twoStateLam_sum (by norm_num)
    (fun _ => le_rfl) (by norm_num) hC3 hd1 (by rw [hg2]; norm_num) (fun _ => by norm_num)
    one_pos (fun _ => le_rfl) le_rfl hcoer hflow' hle
  set P := Graph.nrmL2 twoStateLam (perpL2 twoStateLam h) with hP
  have hrho : ∀ t : ℝ, rhoL (deriv (deriv F.g) 1) 1 1 * t / 2 = t := fun t => by
    rw [hg2, rhoL]; ring
  have hlim : Tendsto (fun t : ℝ => 2 * Real.exp (-(rhoL (deriv (deriv F.g) 1) 1 1 * t / 2)) * P)
      atTop (𝓝 0) := by
    simp only [hrho]
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 2).mul_const P
    simpa only [mul_zero, zero_mul] using this
  have hle0 : Graph.nrmL2 twoStateLam (fun x => h x - (cinf - 1)) ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨0, fun t ht => hdec t ht⟩)
  have hip : Graph.ipL2 twoStateLam (fun x => h x - (cinf - 1)) (fun x => h x - (cinf - 1)) ≤ 0 :=
    Real.sqrt_eq_zero'.1 (le_antisymm hle0 (Graph.nrmL2_nonneg _ _))
  simp only [Graph.ipL2, twoStateLam, Fin.sum_univ_two] at hip
  have e0 : h 0 = cinf - 1 := by nlinarith [sq_nonneg (h 0 - (cinf - 1)), sq_nonneg (h 1 - (cinf - 1))]
  have e1 : h 1 = cinf - 1 := by nlinarith [sq_nonneg (h 0 - (cinf - 1)), sq_nonneg (h 1 - (cinf - 1))]
  have hall : ∀ x, h x = cinf - 1 := by
    intro x
    fin_cases x
    · exact e0
    · exact e1
  intro y
  simp only [pushMass, hall, twoStateK, twoStateLam, Fin.sum_univ_two]
  ring

end RadiusCertified

/-! ## `rem:freezing` (iii): a freezing generator equal to `(x − 1)²` near `1` -/

section FreezingThree

variable (F : FreezingBands)

/-- `ζ := φ_{a,b} φ_{c,d}`, vanishing exactly on the closed bands. -/
noncomputable def zeta (t : ℝ) : ℝ := flatFactor F.a F.b t * flatFactor F.c F.d t

/-- `ξ := φ_{1−θ,1+θ}`, vanishing exactly on `[1−θ, 1+θ]`. -/
noncomputable def xi (θ t : ℝ) : ℝ := flatFactor (1 - θ) (1 + θ) t

/-- **The multiplier of `rem:freezing`*(iii)***: `m := 2ζ/(ζ+ξ)`. -/
noncomputable def mTheta (θ t : ℝ) : ℝ := 2 * zeta F t / (zeta F t + xi θ t)

/-- **The generator of `rem:freezing`*(iii)***: `g(x) := ∫₁ˣ m(t)(t−1) dt`. -/
noncomputable def gTheta (θ x : ℝ) : ℝ := ∫ t in (1:ℝ)..x, mTheta F θ t * (t - 1)

/-- The standing hypothesis `0 < θ < min(1 − b, c − 1)`. -/
structure ThetaOK (θ : ℝ) : Prop where
  pos : 0 < θ
  lt_b : θ < 1 - F.b
  lt_c : θ < F.c - 1

variable {F}

theorem zeta_nonneg (t : ℝ) : 0 ≤ zeta F t :=
  mul_nonneg (flatFactor_nonneg _ _ _) (flatFactor_nonneg _ _ _)

theorem xi_nonneg (θ t : ℝ) : 0 ≤ xi θ t := flatFactor_nonneg _ _ _

/-- **`ζ` vanishes exactly on `[a,b] ∪ [c,d]`.** -/
theorem zeta_eq_zero_iff {t : ℝ} : zeta F t = 0 ↔ t ∈ Icc F.a F.b ∪ Icc F.c F.d := by
  simp only [zeta, mul_eq_zero, flatFactor_eq_zero_iff, mem_union]

/-- **`ξ` vanishes exactly on `[1−θ, 1+θ]`.** -/
theorem xi_eq_zero_iff {θ t : ℝ} : xi θ t = 0 ↔ t ∈ Icc (1 - θ) (1 + θ) :=
  flatFactor_eq_zero_iff

/-- **The two zero sets are disjoint**, so `ζ + ξ > 0`. -/
theorem zeta_add_xi_pos {θ : ℝ} (hθ : ThetaOK F θ) (t : ℝ) : 0 < zeta F t + xi θ t := by
  rcases (add_nonneg (zeta_nonneg (F := F) t) (xi_nonneg θ t)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : zeta F t = 0 := by linarith [zeta_nonneg (F := F) t, xi_nonneg θ t]
    have hx : xi θ t = 0 := by linarith [zeta_nonneg (F := F) t, xi_nonneg θ t]
    obtain ⟨hx1, hx2⟩ := xi_eq_zero_iff.1 hx
    rcases zeta_eq_zero_iff.1 hz with ⟨-, h2⟩ | ⟨h1, -⟩
    · linarith [hθ.lt_b]
    · linarith [hθ.lt_c]

theorem contDiff_zeta : ContDiff ℝ ∞ (zeta F) :=
  (contDiff_flatFactor F.a F.b).mul (contDiff_flatFactor F.c F.d)

theorem contDiff_mTheta {θ : ℝ} (hθ : ThetaOK F θ) : ContDiff ℝ ∞ (mTheta F θ) :=
  (contDiff_const.mul contDiff_zeta).div (contDiff_zeta.add (contDiff_flatFactor _ _))
    fun t => (zeta_add_xi_pos hθ t).ne'

theorem continuous_mTheta {θ : ℝ} (hθ : ThetaOK F θ) : Continuous (mTheta F θ) :=
  (contDiff_mTheta hθ).continuous

theorem mTheta_nonneg {θ : ℝ} (hθ : ThetaOK F θ) (t : ℝ) : 0 ≤ mTheta F θ t :=
  div_nonneg (mul_nonneg zero_le_two (zeta_nonneg t)) (zeta_add_xi_pos hθ t).le

/-- **`m ≤ 2`.** -/
theorem mTheta_le_two {θ : ℝ} (hθ : ThetaOK F θ) (t : ℝ) : mTheta F θ t ≤ 2 := by
  rw [mTheta, div_le_iff₀ (zeta_add_xi_pos hθ t)]
  nlinarith [xi_nonneg θ t]

/-- **`m = 2` on `[1−θ, 1+θ]`.** -/
theorem mTheta_eq_two {θ : ℝ} (hθ : ThetaOK F θ) {t : ℝ} (ht : t ∈ Icc (1 - θ) (1 + θ)) :
    mTheta F θ t = 2 := by
  have hx : xi θ t = 0 := xi_eq_zero_iff.2 ht
  have hz : 0 < zeta F t := by
    have := zeta_add_xi_pos hθ t
    rwa [hx, add_zero] at this
  rw [mTheta, hx, add_zero, mul_div_assoc, div_self hz.ne', mul_one]

/-- **`m` vanishes exactly on `[a,b] ∪ [c,d]`.** -/
theorem mTheta_eq_zero_iff {θ : ℝ} (hθ : ThetaOK F θ) {t : ℝ} :
    mTheta F θ t = 0 ↔ t ∈ Icc F.a F.b ∪ Icc F.c F.d := by
  rw [mTheta, div_eq_zero_iff, ← zeta_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h (zeta_add_xi_pos hθ t).ne'
  · intro h; left; rw [h, mul_zero]

theorem mTheta_pos_of_mem_Ioo {θ : ℝ} (hθ : ThetaOK F θ) {t : ℝ} (h1 : F.b < t) (h2 : t < F.c) :
    0 < mTheta F θ t := by
  refine (mTheta_nonneg hθ t).lt_of_ne fun h => ?_
  rcases (mTheta_eq_zero_iff hθ).1 h.symm with ⟨-, h3⟩ | ⟨h3, -⟩
  · linarith
  · linarith

theorem continuous_integrandTheta {θ : ℝ} (hθ : ThetaOK F θ) :
    Continuous fun t => mTheta F θ t * (t - 1) :=
  (continuous_mTheta hθ).mul (continuous_id.sub continuous_const)

theorem gTheta_one (θ : ℝ) : gTheta F θ 1 = 0 := intervalIntegral.integral_same

theorem deriv_gTheta {θ : ℝ} (hθ : ThetaOK F θ) :
    deriv (gTheta F θ) = fun x => mTheta F θ x * (x - 1) := by
  funext x
  exact Continuous.deriv_integral _ (continuous_integrandTheta hθ) 1 x

theorem differentiable_gTheta {θ : ℝ} (hθ : ThetaOK F θ) : Differentiable ℝ (gTheta F θ) :=
  fun x => ((continuous_integrandTheta hθ).integral_hasStrictDerivAt 1 x).hasDerivAt.differentiableAt

theorem contDiff_gTheta {θ : ℝ} (hθ : ThetaOK F θ) : ContDiff ℝ ∞ (gTheta F θ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨differentiable_gTheta hθ, ?_⟩
  rw [deriv_gTheta hθ]
  exact (contDiff_mTheta hθ).mul (contDiff_id.sub contDiff_const)

/-- **`g' ≡ 0` on the bands.** -/
theorem deriv_gTheta_eq_zero {θ : ℝ} (hθ : ThetaOK F θ) {x : ℝ} (hx : x ∈ F.bands) :
    deriv (gTheta F θ) x = 0 := by
  rw [deriv_gTheta hθ]
  have hmem : x ∈ Icc F.a F.b ∪ Icc F.c F.d := by
    rcases hx with h | h
    · exact Or.inl (F.mem_Icc_of_mem_lower h)
    · exact Or.inr (F.mem_Icc_of_mem_upper h)
  simp only [(mTheta_eq_zero_iff hθ).2 hmem, zero_mul]

/-- **`g > 0` off `1`.** -/
theorem gTheta_pos {θ : ℝ} (hθ : ThetaOK F θ) {x : ℝ} (hx : x ≠ 1) : 0 < gTheta F θ x := by
  have hint := continuous_integrandTheta hθ
  rcases lt_or_gt_of_ne hx with h | h
  · have hmax : max x F.b < 1 := max_lt h F.b_lt_one
    set t0 : ℝ := (max x F.b + 1) / 2 with ht0
    have hlow : max x F.b < t0 := by rw [ht0]; linarith
    have hhigh : t0 < 1 := by rw [ht0]; linarith
    have hmem : t0 ∈ Icc x 1 :=
      mem_Icc.2 ⟨le_of_lt (lt_of_le_of_lt (le_max_left x F.b) hlow), hhigh.le⟩
    have hmpos : 0 < mTheta F θ t0 :=
      mTheta_pos_of_mem_Ioo hθ (lt_of_le_of_lt (le_max_right x F.b) hlow)
        (hhigh.trans F.one_lt_c)
    have key : (0:ℝ) < ∫ t in x..(1:ℝ), -(mTheta F θ t * (t - 1)) := by
      refine intervalIntegral.integral_pos h hint.neg.continuousOn ?_ ⟨t0, hmem, ?_⟩
      · intro t ht
        have h1 : t ≤ 1 := (mem_Ioc.1 ht).2
        nlinarith [mTheta_nonneg hθ t]
      · nlinarith
    rw [intervalIntegral.integral_neg] at key
    have hsym : gTheta F θ x = -∫ t in x..(1:ℝ), mTheta F θ t * (t - 1) :=
      intervalIntegral.integral_symm x 1
    rw [hsym]
    linarith
  · have hmin : 1 < min x F.c := lt_min h F.one_lt_c
    set t0 : ℝ := (1 + min x F.c) / 2 with ht0
    have hlow : 1 < t0 := by rw [ht0]; linarith
    have hhigh : t0 < min x F.c := by rw [ht0]; linarith
    have hmem : t0 ∈ Icc 1 x :=
      mem_Icc.2 ⟨hlow.le, le_of_lt (lt_of_lt_of_le hhigh (min_le_left x F.c))⟩
    have hmpos : 0 < mTheta F θ t0 :=
      mTheta_pos_of_mem_Ioo hθ (F.b_lt_one.trans hlow) (lt_of_lt_of_le hhigh (min_le_right x F.c))
    refine intervalIntegral.integral_pos h hint.continuousOn ?_ ⟨t0, hmem, ?_⟩
    · intro t ht
      have h1 : 1 ≤ t := (mem_Ioc.1 ht).1.le
      nlinarith [mTheta_nonneg hθ t]
    · nlinarith

/-- **`g''(1) = 2`.** -/
theorem deriv_deriv_gTheta_one {θ : ℝ} (hθ : ThetaOK F θ) : deriv (deriv (gTheta F θ)) 1 = 2 := by
  rw [deriv_gTheta hθ]
  have hm : HasDerivAt (mTheta F θ) (deriv (mTheta F θ) 1) 1 :=
    (((contDiff_mTheta hθ).differentiable (by simp)) 1).hasDerivAt
  have h : HasDerivAt (fun y : ℝ => mTheta F θ y * (y - 1))
      (deriv (mTheta F θ) 1 * (1 - 1) + mTheta F θ 1 * 1) 1 :=
    hm.mul ((hasDerivAt_id (1:ℝ)).sub_const 1)
  rw [h.deriv, mTheta_eq_two hθ ⟨by linarith [hθ.pos], by linarith [hθ.pos]⟩]
  ring

/-- **`g = (x − 1)²` on `[1−θ, 1+θ]`.** -/
theorem gTheta_eq_sq {θ : ℝ} (hθ : ThetaOK F θ) {x : ℝ} (hx : x ∈ Icc (1 - θ) (1 + θ)) :
    gTheta F θ x = (x - 1) ^ 2 := by
  have h1 : (1:ℝ) ∈ Icc (1 - θ) (1 + θ) := ⟨by linarith [hθ.pos], by linarith [hθ.pos]⟩
  have hcongr : (∫ t in (1:ℝ)..x, mTheta F θ t * (t - 1)) = ∫ t in (1:ℝ)..x, 2 * (t - 1) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    show mTheta F θ t * (t - 1) = 2 * (t - 1)
    rw [mTheta_eq_two hθ ((uIcc_subset_Icc h1 hx) ht)]
  rw [gTheta, hcongr, intervalIntegral.integral_const_mul, integral_sub_one]
  ring

/-- `|g(x)| ≤ (x − 1)²`, from `0 ≤ m ≤ 2`. -/
theorem abs_gTheta_le {θ : ℝ} (hθ : ThetaOK F θ) (x : ℝ) : |gTheta F θ x| ≤ (x - 1) ^ 2 := by
  have hint := continuous_integrandTheta hθ
  have hnn : 0 ≤ gTheta F θ x := by
    rcases eq_or_ne x 1 with h | h
    · rw [h, gTheta_one]
    · exact (gTheta_pos hθ h).le
  rw [abs_of_nonneg hnn]
  rcases le_total 1 x with h | h
  · have hmono : (∫ t in (1:ℝ)..x, mTheta F θ t * (t - 1)) ≤ ∫ t in (1:ℝ)..x, 2 * (t - 1) := by
      refine intervalIntegral.integral_mono_on h (hint.intervalIntegrable 1 x)
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable 1 x) ?_
      intro t ht
      have h1 : 1 ≤ t := (mem_Icc.1 ht).1
      nlinarith [mTheta_le_two hθ t]
    rw [intervalIntegral.integral_const_mul, integral_sub_one] at hmono
    calc gTheta F θ x = ∫ t in (1:ℝ)..x, mTheta F θ t * (t - 1) := rfl
      _ ≤ 2 * (((x - 1) ^ 2 - (1 - 1) ^ 2) / 2) := hmono
      _ = (x - 1) ^ 2 := by ring
  · have hmono : (∫ t in x..(1:ℝ), -(mTheta F θ t * (t - 1)))
        ≤ ∫ t in x..(1:ℝ), -(2 * (t - 1)) := by
      refine intervalIntegral.integral_mono_on h (hint.intervalIntegrable x 1).neg
        ((continuous_const.mul (continuous_id.sub continuous_const)).neg.intervalIntegrable x 1) ?_
      intro t ht
      have h1 : t ≤ 1 := (mem_Icc.1 ht).2
      nlinarith [mTheta_le_two hθ t]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, integral_sub_one] at hmono
    have hsym : gTheta F θ x = -∫ t in x..(1:ℝ), mTheta F θ t * (t - 1) :=
      intervalIntegral.integral_symm x 1
    rw [hsym]
    linarith

/-- **`rem:freezing`*(iii)*, the multiplier**: `m = 2ζ/(ζ+ξ)` is `C^∞` with values in `[0,2]`,
equals `2` on `[1−θ, 1+θ]`, and vanishes exactly on `[a,b] ∪ [c,d]`. -/
theorem freezing_three_multiplier {θ : ℝ} (hθ : ThetaOK F θ) :
    ContDiff ℝ ∞ (mTheta F θ) ∧ (∀ t, 0 ≤ mTheta F θ t ∧ mTheta F θ t ≤ 2)
      ∧ (∀ t ∈ Icc (1 - θ) (1 + θ), mTheta F θ t = 2)
      ∧ (∀ t, mTheta F θ t = 0 ↔ t ∈ Icc F.a F.b ∪ Icc F.c F.d) :=
  ⟨contDiff_mTheta hθ, fun t => ⟨mTheta_nonneg hθ t, mTheta_le_two hθ t⟩,
    fun _ ht => mTheta_eq_two hθ ht, fun _ => mTheta_eq_zero_iff hθ⟩

/-- **`rem:freezing`*(iii)*, the generator**: `g(x) := ∫₁ˣ m(t)(t−1) dt` is `C^∞` and admissible —
`g(1) = 0`, `g > 0` elsewhere, `g''(1) = 2`, `|g(x)| ≤ 2(1 + |x|²)` — with `g' ≡ 0` on the bands,
and it equals `(x − 1)²` on `[1−θ, 1+θ]`. -/
theorem freezing_three_generator {θ : ℝ} (hθ : ThetaOK F θ) :
    ContDiff ℝ ∞ (gTheta F θ) ∧ gTheta F θ 1 = 0 ∧ (∀ x ≠ (1:ℝ), 0 < gTheta F θ x)
      ∧ deriv (deriv (gTheta F θ)) 1 = 2
      ∧ (∀ x, |gTheta F θ x| ≤ 2 * (1 + |x| ^ 2))
      ∧ (∀ x ∈ F.bands, deriv (gTheta F θ) x = 0)
      ∧ (∀ x ∈ Icc (1 - θ) (1 + θ), gTheta F θ x = (x - 1) ^ 2) := by
  refine ⟨contDiff_gTheta hθ, gTheta_one θ, fun _ hx => gTheta_pos hθ hx,
    deriv_deriv_gTheta_one hθ, fun x => ?_, fun _ hx => deriv_gTheta_eq_zero hθ hx,
    fun _ hx => gTheta_eq_sq hθ hx⟩
  have h := abs_gTheta_le hθ x
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [sq_nonneg (x + 1)]

/-- **`rem:freezing`*(iii)*: item *(1)* of `prop:nonlinear_freezing` applies to it** — on a
finite state space a band-valued flow is critical for every training measure (`D ≡ 0`, and a
Fréchet derivative `0`), the set of such flows is open, and the loss is locally constant and
positive on it. -/
theorem freezing_three_item_one {θ : ℝ} (hθ : ThetaOK F θ) {V : Type*} [Fintype V] [Nonempty V]
    {K : V → V → ℝ} {lam nu u : V → ℝ} (hlam : ∀ x, 0 < lam x) (hnu : ∀ x, 0 < nu x)
    (hu : u ∈ frozen K lam F.bands) :
    (∀ w : V → ℝ, ∀ x, lossGradDensity K lam u w (deriv (gTheta F θ)) x = 0)
      ∧ (∀ nu' : V → ℝ,
          HasFDerivAt (fun u' => loss K lam nu' u' (gTheta F θ)) (0 : (V → ℝ) →L[ℝ] ℝ) u)
      ∧ IsOpen (frozen K lam F.bands)
      ∧ (∀ᶠ u' in 𝓝 u, loss K lam nu u' (gTheta F θ) = loss K lam nu u (gTheta F θ))
      ∧ 0 < loss K lam nu u (gTheta F θ) :=
  freezing_item_one_general F (fun x _ => (differentiable_gTheta hθ x).hasDerivAt)
    (fun _ hx => deriv_gTheta_eq_zero hθ hx)
    (fun _ hz => gTheta_pos hθ fun h1 => F.one_notMem_bands (h1 ▸ hz)) hlam hnu hu

/-- **`rem:freezing`*(iii)*: the freezing configurations are invisible to the linearization at
balance** — wherever every ratio lies in `[1−θ, 1+θ]`, the loss and the gradient density of this
freezing generator are those of `(x − 1)²`. -/
theorem freezing_three_invisible {θ : ℝ} (hθ : ThetaOK F θ) {V : Type*} [Fintype V]
    {K : V → V → ℝ} {lam nu u w : V → ℝ}
    (hr : ∀ x, ratio K lam u x ∈ Icc (1 - θ) (1 + θ)) :
    loss K lam nu u (gTheta F θ) = loss K lam nu u (fun z => (z - 1) ^ 2)
      ∧ lossGradDensity K lam u w (deriv (gTheta F θ))
          = lossGradDensity K lam u w (fun z => 2 * (z - 1)) := by
  have hd : ∀ x, deriv (gTheta F θ) (ratio K lam u x) = 2 * (ratio K lam u x - 1) := fun x => by
    rw [deriv_gTheta hθ]
    show mTheta F θ (ratio K lam u x) * (ratio K lam u x - 1) = _
    rw [mTheta_eq_two hθ (hr x)]
  refine ⟨Finset.sum_congr rfl fun x _ => by rw [gTheta_eq_sq hθ (hr x)], ?_⟩
  funext x
  simp only [lossGradDensity, gradDensity, funAct, hd]

/-- **`rem:freezing`*(iii)*, last clause: the generator of `prop:nonlinear_freezing` equals
`(x − 1)²` on no neighbourhood of `1`.** Near `1` its multiplier is `2e^{−1/(t−b)−1/(c−t)}/scale`,
and `1/(t−b) + 1/(c−t)` takes its value at `1` only at `t = 1` and `t = b + c − 1`. -/
theorem freezing_g_ne_sq_near_one (F : FreezingBands) :
    ¬ ∃ ε > 0, ∀ x ∈ Ioo (1 - ε) (1 + ε), F.g x = (x - 1) ^ 2 := by
  rintro ⟨ε, hε, hsq⟩
  -- on `(1, 1+ε)` the multiplier is `2`
  have hm2 : ∀ t ∈ Ioo (1:ℝ) (1 + ε), F.m t = 2 := by
    intro t ht
    have htmem : t ∈ Ioo (1 - ε) (1 + ε) := ⟨by linarith [ht.1], ht.2⟩
    have hev : F.g =ᶠ[𝓝 t] fun y => (y - 1) ^ 2 := by
      filter_upwards [Ioo_mem_nhds htmem.1 htmem.2] with y hy
      exact hsq y hy
    have hd : deriv F.g t = 2 * (t - 1) := by
      rw [hev.deriv_eq]
      have h := ((hasDerivAt_id' t).sub_const 1).fun_pow 2
      rw [h.deriv]
      norm_num
    rw [F.deriv_g] at hd
    have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
    exact mul_right_cancel₀ ht1 hd
  -- the exponent identity at a point `t ∈ (1, min(1+ε, c))`
  have hkey : ∀ t, 1 < t → t < 1 + ε → t < F.c →
      (t - F.b) * (F.c - t) = (1 - F.b) * (F.c - 1) := by
    intro t ht1 ht2 ht3
    have hb : F.b < t := F.b_lt_one.trans ht1
    have hglue : ∀ s, F.b < s → s < F.c →
        flatFactor F.a F.b s * flatFactor F.c F.d s
          = Real.exp (-((s - F.b)⁻¹ + (F.c - s)⁻¹)) := by
      intro s hs1 hs2
      have ha : F.a - s ≤ 0 := by linarith [F.a_lt_b]
      have hd : s - F.d ≤ 0 := by linarith [F.c_lt_d]
      have hp1 : ¬ (s - F.b ≤ 0) := by intro h; linarith
      have hp2 : ¬ (F.c - s ≤ 0) := by intro h; linarith
      simp only [flatFactor]
      rw [expNegInvGlue.zero_of_nonpos ha, expNegInvGlue.zero_of_nonpos hd, zero_add, add_zero]
      simp only [expNegInvGlue, if_neg hp1, if_neg hp2]
      rw [← Real.exp_add, neg_add]
    have hmt := hm2 t ⟨ht1, ht2⟩
    have hm1 := F.m_one
    simp only [FreezingBands.m, FreezingBands.scale] at hmt hm1
    rw [hglue t hb ht3] at hmt
    rw [hglue 1 F.b_lt_one F.one_lt_c] at hm1 hmt
    have hs : 0 < Real.exp (-((1 - F.b)⁻¹ + (F.c - 1)⁻¹)) := Real.exp_pos _
    have hne : (2:ℝ) / Real.exp (-((1 - F.b)⁻¹ + (F.c - 1)⁻¹)) ≠ 0 := div_ne_zero two_ne_zero hs.ne'
    have heq := mul_left_cancel₀ hne (hmt.trans hm1.symm)
    have hinv := neg_inj.1 (Real.exp_injective heq)
    have hA : 0 < t - F.b := by linarith
    have hB : 0 < F.c - t := by linarith
    have hA1 : 0 < 1 - F.b := by linarith [F.b_lt_one]
    have hC1 : 0 < F.c - 1 := by linarith [F.one_lt_c]
    have hL : 0 < F.c - F.b := by linarith
    have e1 : (t - F.b)⁻¹ + (F.c - t)⁻¹ = (F.c - F.b) / ((t - F.b) * (F.c - t)) := by
      field_simp; ring
    have e2 : (1 - F.b)⁻¹ + (F.c - 1)⁻¹ = (F.c - F.b) / ((1 - F.b) * (F.c - 1)) := by
      field_simp; ring
    rw [e1, e2, div_eq_div_iff (mul_pos hA hB).ne' (mul_pos hA1 hC1).ne'] at hinv
    exact (mul_left_cancel₀ hL.ne' hinv).symm
  -- two distinct points with the identity force them to coincide
  set e' : ℝ := min ε (F.c - 1) with he'
  have he'0 : 0 < e' := lt_min hε (by linarith [F.one_lt_c])
  have he'1 : e' ≤ ε := min_le_left _ _
  have he'2 : e' ≤ F.c - 1 := min_le_right _ _
  have hq : ∀ t, 1 < t → t < 1 + ε → t < F.c → t = F.b + F.c - 1 := by
    intro t ht1 ht2 ht3
    have h := hkey t ht1 ht2 ht3
    have hfac : (t - 1) * (F.b + F.c - 1 - t) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h0 | h0
    · linarith
    · linarith
  have h1 := hq (1 + e' / 2) (by linarith) (by linarith) (by linarith)
  have h2 := hq (1 + e' / 4) (by linarith) (by linarith) (by linarith)
  linarith

end FreezingThree

/-! ## `rem:freezing` (iv): pointers, certified -/

section FreezingFour

/-- **`rem:freezing`*(iv)*, first clause**: for a differentiable strictly unimodal generator,
every flow at which every directional derivative of `𝓛_{g,ν}` vanishes is balanced, for `ν` of
positive density (`prop:no_distant_equilibrium`*(1)*, through `theo:first_variation_full`). -/
theorem freezing_four_critical {V : Type*} [Fintype V] {K : V → V → ℝ} {lam nu u : V → ℝ}
    {g gd : ℝ → ℝ} (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hnu : ∀ x, 0 < nu x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hgd : StrictlyUnimodal gd)
    (hcrit : ∀ d : V → ℝ,
      HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g) 0 0) :
    Balanced K lam u :=
  balanced_of_hasDerivAt_zero hinv hK hlam hu hnu hg hgd hcrit

/-- **`rem:freezing`*(iv)*, second clause, the `(log x)²` half**: on the loop closure of a finite
path-connected marked graph, the `(log x)²` gradient flow from every `u₀ > 0` exists, is unique
among positive solutions, and converges to the balanced flow of its sphere
(`prop:no_distant_equilibrium`*(3)*, `FlowExistence.no_distant_equilibrium_three_of_init`). -/
theorem freezing_four_logSq_converges {V : Type*} [Fintype V] [DecidableEq V]
    {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G} {lam wf : V → ℝ} {wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ (∀ v : ℝ → V → ℝ, v 0 = u0 →
          IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t)
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam u0)
      ∧ Balanced B.phat lam (fun _ => Graph.nrmL2 lam u0) := by
  obtain ⟨u, h0, hflow, hpos', huniq, hconv, hbal, -⟩ :=
    no_distant_equilibrium_three_of_init hpc hpos hl hwmin hw hu0
  exact ⟨u, h0, hflow, hpos', huniq, hconv, hbal⟩

end FreezingFour

/-! ## Periodic chains: the mixing coefficients do not decay -/

section Periodic

variable {V : Type*}

/-- **`n`-step accessibility** for a kernel: `ReachIn K n x y` iff some path `x = x₀, …, xₙ = y`
has `K(xᵢ, xᵢ₊₁) ≠ 0` at every step. -/
def ReachIn (K : V → V → ℝ) : ℕ → V → V → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, ReachIn K n x z ∧ K z y ≠ 0

theorem ReachIn.append {K : V → V → ℝ} {m : ℕ} {x y : V} (hxy : ReachIn K m x y) :
    ∀ {n : ℕ} {z : V}, ReachIn K n y z → ReachIn K (m + n) x z
  | 0, z, h => by
    have h' : y = z := h
    rw [Nat.add_zero, ← h']; exact hxy
  | n + 1, z, h => by
    obtain ⟨w, hw, hwz⟩ := h
    exact ⟨w, ReachIn.append hxy hw, hwz⟩

/-- **Periodicity at a state**, read off its return times: `d ≥ 2` divides every `n` with a
return `x₀ ⤳ x₀` in `n` steps. With `d` the gcd of the return times this is the textbook
"`x₀` has period `≥ 2`". -/
def PeriodicAt (K : V → V → ℝ) (x₀ : V) (d : ℕ) : Prop :=
  2 ≤ d ∧ ∀ n, ReachIn K n x₀ x₀ → d ∣ n

/-- **Cyclic classes from a period**, for an irreducible kernel: the class of `y` is the length of
any path `x₀ ⤳ y`, modulo `d`; it is well defined because two such lengths differ by a multiple
of `d`, and every transition raises it by `1`. -/
theorem exists_cyclic_of_periodicAt {K : V → V → ℝ} (hirr : ∀ x y, ∃ n, ReachIn K n x y)
    {x₀ : V} {d : ℕ} (hper : PeriodicAt K x₀ d) :
    ∃ c : V → ZMod d, ∀ x y, K x y ≠ 0 → c y = c x + 1 := by
  classical
  choose len hlen using hirr x₀
  have hwd : ∀ {n : ℕ} {y : V}, ReachIn K n x₀ y → (n : ZMod d) = (len y : ZMod d) := by
    intro n y hn
    obtain ⟨k, hk⟩ := hirr y x₀
    have h1 := hper.2 _ (hn.append hk)
    have h2 := hper.2 _ ((hlen y).append hk)
    have e1 : ((n + k : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
    have e2 : ((len y + k : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
    push_cast at e1 e2
    linear_combination e1 - e2
  refine ⟨fun y => (len y : ZMod d), fun x y hxy => ?_⟩
  have hstep : ReachIn K (len x + 1) x₀ y := ⟨x, hlen x, hxy⟩
  have := hwd hstep
  push_cast at this
  exact this.symm

variable [Fintype V]

/-- The indicator of a cyclic class. -/
noncomputable def classInd {d : ℕ} (c : V → ZMod d) (i : ZMod d) : V → ℝ :=
  fun x => if c x = i then 1 else 0

variable {K : V → V → ℝ} {lam : V → ℝ}

/-- **The density action moves each cyclic class to the next**: `P 𝟙_{Cᵢ} = 𝟙_{Cᵢ₊₁}`. -/
theorem densAct_classInd (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x) {d : ℕ}
    {c : V → ZMod d} (hc : ∀ x y, K x y ≠ 0 → c y = c x + 1) (i : ZMod d) :
    Core.densAct lam K (classInd c i) = classInd c (i + 1) := by
  funext y
  rw [Core.densAct_apply]
  have hterm : ∀ x, lam x * K x y * classInd c i x = lam x * K x y * classInd c (i + 1) y := by
    intro x
    by_cases hk : K x y = 0
    · rw [hk, mul_zero, zero_mul, zero_mul]
    · have hcy := hc x y hk
      have hiff : (c x = i) ↔ (c y = i + 1) := by rw [hcy, add_left_inj]
      simp only [classInd, hiff]
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_mul, hinv.inv y,
    mul_div_cancel_left₀ _ (hlam y).ne']

theorem densOp_pow_classInd (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x) {d : ℕ}
    {c : V → ZMod d} (hc : ∀ x y, K x y ≠ 0 → c y = c x + 1) (i : ZMod d) (n : ℕ) :
    (densOp lam K ^ n) (wtL2 lam (classInd c i)) = wtL2 lam (classInd c (i + n)) := by
  induction n with
  | zero => rw [pow_zero, one_apply_eq_self, Nat.cast_zero, add_zero]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, densOp_wtL2 hlam, densAct_classInd hinv hlam hc,
      Nat.cast_succ, add_assoc]

theorem densOp_pow_mul_meanOp' (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x) (n : ℕ) :
    densOp lam K ^ n * meanOp lam = meanOp lam := by
  induction n with
  | zero => rw [pow_zero, one_mul]
  | succ n ih => rw [pow_succ, mul_assoc, densOp_mul_meanOp hinv hlam, ih]

/-- **A non-zero vector killed by `Π` and fixed by `Pⁿ` forces `β̂ₙ ≥ 1`.** -/
theorem one_le_beta_of_fixed' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P Pi : E →L[ℝ] E} {v : E} (hv : v ≠ 0) (hPi : Pi v = 0) {n : ℕ} (hfix : (P ^ n) v = v) :
    1 ≤ Core.Mixing.beta P Pi n := by
  have h := (P ^ n - Pi).le_opNorm v
  rw [sub_apply, hPi, sub_zero, hfix] at h
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have : 1 * ‖v‖ ≤ Core.Mixing.beta P Pi n * ‖v‖ := by
    rw [one_mul]; exact h
  exact le_of_mul_le_mul_right this hvpos

/-- **`β̂_{dk} ≥ 1` for every `k`** on a chain with `d ≥ 2` cyclic classes: the centred indicator
of one class is fixed by `P^d` and killed by `Π`. -/
theorem beta_mul_ge_one_of_cyclic (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) {d : ℕ} (hd : 2 ≤ d) {c : V → ZMod d}
    (hc : ∀ x y, K x y ≠ 0 → c y = c x + 1) (k : ℕ) :
    1 ≤ Core.Mixing.beta (densOp lam K) (meanOp lam) (d * k) := by
  classical
  have hne : Nonempty V := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at htot
    exact zero_ne_one htot
  obtain ⟨x₀⟩ := hne
  set i₀ := c x₀ with hi₀
  set a := wtL2 lam (classInd c i₀) with ha
  set v := a - meanOp lam a with hv
  have hidem : meanOp lam * meanOp lam = meanOp lam :=
    ContinuousLinearMap.ext fun u => meanOp_idem hlam htot u
  have hPi : meanOp lam v = 0 := by
    rw [hv, map_sub, ← mul_apply_eq_comp, hidem, sub_self]
  have hfix : (densOp lam K ^ d) v = v := by
    rw [hv, map_sub, ← mul_apply_eq_comp, densOp_pow_mul_meanOp' hinv hlam, ha,
      densOp_pow_classInd hinv hlam hc, ZMod.natCast_self, add_zero]
  -- `v ≠ 0`: the class indicator is not constant
  have hvne : v ≠ 0 := by
    intro h0
    have hfun : wtL2 lam (classInd c i₀) = wtL2 lam (fun _ => Graph.meanL2 lam (classInd c i₀)) := by
      rw [← meanOp_wtL2 hlam]
      exact sub_eq_zero.1 h0
    have hconst := congrFun (wtL2_injective hlam hfun)
    obtain ⟨y, hy⟩ : ∃ y, K x₀ y ≠ 0 := by
      by_contra hall
      have hz : ∀ y, K x₀ y = 0 := fun y => by_contra fun h => hall ⟨y, h⟩
      have := hK.row_sum x₀
      rw [Finset.sum_eq_zero fun y _ => hz y] at this
      exact zero_ne_one this
    have hcy := hc x₀ y hy
    have h1ne : (1 : ZMod d) ≠ 0 := by
      intro h1
      have : ((1 : ℕ) : ZMod d) = 0 := by exact_mod_cast h1
      have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 this
      have := Nat.le_of_dvd one_pos hdvd
      omega
    have hyx : c y ≠ i₀ := by
      rw [hcy, hi₀]
      intro h
      exact h1ne (by simpa using h)
    have e0 := hconst x₀
    have e1 := hconst y
    simp only [classInd, if_pos hi₀.symm, if_neg hyx] at e0 e1
    linarith
  exact one_le_beta_of_fixed' hvne hPi (GFNBounds.Graph.CycleRemarks.pow_mul_apply_eq_self hfix k)

/-- **Summable `L²` mixing fails on a chain with `d ≥ 2` cyclic classes**: `β̂_{dk} ≥ 1` for all
`k`, so `∑ₙ β̂ₙ = +∞` (as an extended real), the sequence is not summable, and
`Core.Mixing (P, Π)` — `lem:sigma_mixing`'s hypothesis — fails. -/
theorem mixing_fails_of_cyclic (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) {d : ℕ} (hd : 2 ≤ d) {c : V → ZMod d}
    (hc : ∀ x y, K x y ≠ 0 → c y = c x + 1) :
    (∀ k, 1 ≤ Core.Mixing.beta (densOp lam K) (meanOp lam) (d * k))
      ∧ ∑' n, ENNReal.ofReal (Core.Mixing.beta (densOp lam K) (meanOp lam) n) = ⊤
      ∧ ¬ Summable (Core.Mixing.beta (densOp lam K) (meanOp lam))
      ∧ ¬ Core.Mixing (densOp lam K) (meanOp lam) := by
  have hge := beta_mul_ge_one_of_cyclic hK hinv hlam htot hd hc
  have hd0 : 0 < d := by omega
  have hns := GFNBounds.Graph.CycleRemarks.not_summable_of_one_le hd0 hge
  exact ⟨hge, GFNBounds.Graph.CycleRemarks.tsum_ofReal_eq_top_of_one_le (Core.Mixing.beta_nonneg _ _) hd0 hge, hns,
    fun hmx => hns hmx.summable⟩

/-- **The same, from the period**: on an irreducible chain periodic at some state, summable
`L²` mixing fails. -/
theorem mixing_fails_of_periodicAt (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (hirr : ∀ x y, ∃ n, ReachIn K n x y)
    {x₀ : V} {d : ℕ} (hper : PeriodicAt K x₀ d) :
    (∀ k, 1 ≤ Core.Mixing.beta (densOp lam K) (meanOp lam) (d * k))
      ∧ ∑' n, ENNReal.ofReal (Core.Mixing.beta (densOp lam K) (meanOp lam) n) = ⊤
      ∧ ¬ Summable (Core.Mixing.beta (densOp lam K) (meanOp lam))
      ∧ ¬ Core.Mixing (densOp lam K) (meanOp lam) := by
  obtain ⟨c, hc⟩ := exists_cyclic_of_periodicAt hirr hper
  exact mixing_fails_of_cyclic hK hinv hlam htot hper.1 hc

end Periodic

/-! ## Periodicity on the loop closure of a marked graph, and the leveled graph -/

section GraphPeriodic

open Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : MarkedGraph V} {B : BackwardPolicy G}

theorem phat_isMarkov (B : BackwardPolicy G) : Core.IsMarkov B.phat :=
  ⟨B.phat_nonneg, B.phat_row_sum⟩

theorem phat_isInvariant {lam : V → ℝ} (hl : B.IsInvProb lam) : Core.IsInvariant lam B.phat :=
  ⟨hl.nonneg, hl.inv⟩

/-- Accessibility in the backward chain gives a path of some length. -/
theorem reachIn_of_breach {x y : V} (h : B.BReach x y) : ∃ n, ReachIn B.phat n x y := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, hn, hstep.ne'⟩

/-- **`rem:graphs_vs_L2`: summable mixing fails on every periodic loop closure.** On the loop
closure of a finite path-connected marked graph with a backward policy positive on its edges, if
the backward chain is periodic at some state — some `d ≥ 2` divides every return time there —
then `β̂_{dk} ≥ 1` for every `k`: the coefficients are bounded below along a subsequence,
`∑ₙ β̂ₙ = +∞`, and the summable-mixing hypothesis of `theo:universality_L2` at `p = 2`
(`Core.Mixing (P, Π)`) fails. -/
theorem graphs_vs_L2_periodic (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) {x₀ : V} {d : ℕ} (hper : PeriodicAt B.phat x₀ d) :
    (∀ k, 1 ≤ Core.Mixing.beta (densOp lam B.phat) (meanOp lam) (d * k))
      ∧ ∑' n, ENNReal.ofReal (Core.Mixing.beta (densOp lam B.phat) (meanOp lam) n) = ⊤
      ∧ ¬ Summable (Core.Mixing.beta (densOp lam B.phat) (meanOp lam))
      ∧ ¬ Core.Mixing (densOp lam B.phat) (meanOp lam) :=
  mixing_fails_of_periodicAt (phat_isMarkov B) (phat_isInvariant hl) (hl.pos hpc hpos) hl.total
    (fun x y => reachIn_of_breach (B.breach_all hpc hpos x y)) hper

variable (L : Leveled G)

omit [Fintype V] [DecidableEq V] in
/-- On a path-connected leveled graph every height is a natural number. -/
theorem leveled_exists_nat (hpc : G.PathConnected) (x : V) : ∃ n : ℕ, L.lvl x = n := by
  induction hpc.from_src x with
  | refl => exact ⟨0, by rw [L.lvl_src, Nat.cast_zero]⟩
  | tail _ hedge ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [L.lvl_edge hedge, hn, Nat.cast_succ]⟩

/-- The height as a natural number. -/
noncomputable def levNat (x : V) : ℕ := ⌊L.lvl x⌋₊

omit [Fintype V] [DecidableEq V] in
theorem levNat_eq (hpc : G.PathConnected) (x : V) : (levNat L x : ℝ) = L.lvl x := by
  obtain ⟨n, hn⟩ := leveled_exists_nat L hpc x
  rw [levNat, hn, Nat.floor_natCast]

omit [Fintype V] [DecidableEq V] in
/-- The sink is at height at least `1`: `s₀ ≠ s_f`. -/
theorem one_le_levNat_snk (hpc : G.PathConnected) : 1 ≤ levNat L G.snk := by
  have hr := hpc.from_src G.snk
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨z, hz, hzs⟩
  · exact absurd h G.src_ne_snk
  · have h1 : L.lvl z = 1 := by rw [L.lvl_edge hz, L.lvl_src, zero_add]
    have h2 := L.lvl_mono hzs
    have h3 := levNat_eq L hpc G.snk
    have : (1 : ℝ) ≤ levNat L G.snk := by rw [h3]; linarith
    exact_mod_cast this

/-- **The cyclic classes of a leveled loop closure**: `c(x) := −ℓ(x)` modulo `t_m + 1`, with
`t_m = ℓ(s_f)` — every backward step lowers the height by one, and the wrap `s₀ → s_f` raises it
by `t_m ≡ −1`. -/
theorem leveled_cyclic (hpc : G.PathConnected) (B : BackwardPolicy G) (x y : V) (hxy : B.phat x y ≠ 0) :
    (-(levNat L y : ZMod (levNat L G.snk + 1))) = -(levNat L x : ZMod (levNat L G.snk + 1)) + 1 := by
  by_cases hx : x = G.src
  · subst hx
    have hy : y = G.snk := by
      by_contra hne
      exact hxy (B.phat_src_of_ne hne)
    subst hy
    have h0 : levNat L G.src = 0 := by
      have := levNat_eq L hpc G.src
      rw [L.lvl_src] at this
      exact_mod_cast this
    rw [h0, Nat.cast_zero, neg_zero, zero_add]
    have hd : ((levNat L G.snk + 1 : ℕ) : ZMod (levNat L G.snk + 1)) = 0 := ZMod.natCast_self _
    push_cast at hd
    linear_combination -hd
  · rw [B.phat_of_ne_src hx] at hxy
    have hedge := B.supp hx hxy
    have hl := L.lvl_edge hedge
    have hn : levNat L x = levNat L y + 1 := by
      have e1 := levNat_eq L hpc x
      have e2 := levNat_eq L hpc y
      have : (levNat L x : ℝ) = levNat L y + 1 := by rw [e1, e2, hl]
      exact_mod_cast this
    rw [hn]
    push_cast
    ring

/-- **`prop:morozov_rate`, last assertion, and `rem:visit_ratio`'s witness: on a leveled graph the
loop-closed chain is periodic and the mixing sum is `+∞`.** With `t_m := ℓ(s_f)`, the classes
`−ℓ mod (t_m+1)` are cyclic for the backward chain, so `β̂_{(t_m+1)k} ≥ 1` for every `k`,
`∑ₙ β̂ₙ = +∞`, and summable mixing fails — while `B̂_σ ≤ (t_m+1)√((2+t_m)/min N)`
(`Morozov.Leveled.bsigma_le`). -/
theorem leveled_mixing_fails (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) :
    (∀ k, 1 ≤ Core.Mixing.beta (densOp lam B.phat) (meanOp lam) ((levNat L G.snk + 1) * k))
      ∧ ∑' n, ENNReal.ofReal (Core.Mixing.beta (densOp lam B.phat) (meanOp lam) n) = ⊤
      ∧ ¬ Summable (Core.Mixing.beta (densOp lam B.phat) (meanOp lam))
      ∧ ¬ Core.Mixing (densOp lam B.phat) (meanOp lam) :=
  mixing_fails_of_cyclic (phat_isMarkov B) (phat_isInvariant hl) (hl.pos hpc hpos) hl.total
    (by have := one_le_levNat_snk L hpc; omega) (leveled_cyclic L hpc B)

/-- **The leveled graph separates `B̂_σ` from `B̂`**: the coercivity of `prop:morozov_rate`*(2)*
holds with `B̂_σ ≤ (t_m+1)√((2+t_m)/min N)` finite, while the mixing sum `∑ₙ β̂ₙ` is `+∞`. -/
theorem leveled_bsigma_finite_mixing_infinite (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam g : V → ℝ} (hl : B.IsInvProb lam) (hg : B.IsGreen g) :
    (∀ h : V → ℝ, Graph.nrmL2 lam (fun x => h x - Graph.meanL2 lam h)
        ≤ sigmaStar G L.lvl * Real.sqrt ((2 + B.sigmaBar L.lvl) / minOver G (visits G g))
          * Graph.nrmL2 lam (fun x => h x - B.pdens lam h x))
      ∧ sigmaStar G L.lvl * Real.sqrt ((2 + B.sigmaBar L.lvl) / minOver G (visits G g))
          ≤ (L.lvl G.snk + 1) * Real.sqrt ((2 + L.lvl G.snk) / minOver G (visits G g))
      ∧ ∑' n, ENNReal.ofReal (Core.Mixing.beta (densOp lam B.phat) (meanOp lam) n) = ⊤ := by
  have hN : 0 < minOver G (visits G g) :=
    minOver_pos fun x => BackwardPolicy.IsGreen.visits_pos hpc hpos hl hg (L.isHitExp (B := B)) x
  exact ⟨BackwardPolicy.coercivity_morozov hpc hpos hl hg (L.isHitExp (B := B)),
    L.bsigma_le hpc hN, (leveled_mixing_fails L hpc hpos hl).2.1⟩

end GraphPeriodic

/-! ## `rem:visit_ratio` -/

section VisitRatio

open Graph

/-- **The coercivity constant bounds the mixing-sum operator**: if `‖v − Πv‖ ≤ C‖(1 − P)v‖` for
every `v` and `‖1 − Π‖ ≤ 1`, then under summable mixing `‖S‖ ≤ C`. The route is
`ΠS = 0` and `(1 − P)S = 1 − Π`: `‖Sv‖ = ‖Sv − ΠSv‖ ≤ C‖(1−P)Sv‖ = C‖(1−Π)v‖ ≤ C‖v‖`. -/
theorem norm_S_le_of_coercive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {P Pi : E →L[ℝ] E} (hmx : Core.Mixing P Pi) {C : ℝ} (hC : 0 ≤ C)
    (hco : ∀ v, ‖v - Pi v‖ ≤ C * ‖(1 - P) v‖) (hPi1 : ∀ v, ‖v - Pi v‖ ≤ ‖v‖) :
    ‖Core.Mixing.S P Pi‖ ≤ C := by
  have hPiS : Pi * Core.Mixing.S P Pi = 0 :=
    (GFNBounds.Doubling.resolvent_identities hmx.proj_idem hmx.proj_left hmx.proj_right
      hmx.tendsto_partialSum).2.2.1
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
  have h0 : Pi (Core.Mixing.S P Pi v) = 0 := by
    rw [← mul_apply_eq_comp, hPiS, zero_apply]
  calc ‖Core.Mixing.S P Pi v‖ = ‖Core.Mixing.S P Pi v - Pi (Core.Mixing.S P Pi v)‖ := by
        rw [h0, sub_zero]
    _ ≤ C * ‖(1 - P) (Core.Mixing.S P Pi v)‖ := hco _
    _ = C * ‖v - Pi v‖ := by rw [hmx.poisson_left_apply]
    _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_left (hPi1 v) hC

variable {V : Type*} [Fintype V] [DecidableEq V] {G : MarkedGraph V} {B : BackwardPolicy G}

/-- `prop:morozov_rate`*(2)* read on the bundled `L²(λ)`: `‖v − Πv‖ ≤ B̂_σ‖(1 − P)v‖`. -/
theorem coercivity_morozov_op (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam g u : V → ℝ} (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hu : B.IsHitExp u)
    (v : EuclideanSpace ℝ V) :
    ‖v - meanOp lam v‖
      ≤ sigmaStar G u * Real.sqrt ((2 + B.sigmaBar u) / minOver G (visits G g))
        * ‖(1 - densOp lam B.phat) v‖ := by
  have hlam : ∀ x, 0 < lam x := hl.pos hpc hpos
  have hnn : ∀ x, 0 ≤ lam x := hl.nonneg
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam v
  rw [sub_meanOp_wtL2 hlam, norm_wtL2 hnn, one_sub_densOp_wtL2 hlam, norm_neg, norm_wtL2 hnn]
  have hA : Aop B.phat lam a = fun x => -(a x - B.pdens lam a x) := by
    funext x
    rw [Aop_apply]
    show Core.densAct lam B.phat a x - a x = -(a x - B.pdens lam a x)
    rw [Core.densAct_apply, BackwardPolicy.pdens]
    ring
  rw [hA, nrmL2_neg]
  exact BackwardPolicy.coercivity_morozov hpc hpos hl hg hu a

/-- **`rem:visit_ratio`: `B̂_σ ≥ ‖S‖` wherever `S` is defined** — under summable mixing, the
operator `S = ∑ₙ(Pⁿ − Π)` of `lem:sigma_mixing` has operator norm at most the hitting-time
constant `B̂_σ = σ_*√((2+σ̄)/min N)` of `prop:morozov_rate`. -/
theorem visit_ratio_norm_S_le (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam g u : V → ℝ} (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hu : B.IsHitExp u)
    (hmx : Core.Mixing (densOp lam B.phat) (meanOp lam)) :
    ‖Core.Mixing.S (densOp lam B.phat) (meanOp lam)‖
      ≤ sigmaStar G u * Real.sqrt ((2 + B.sigmaBar u) / minOver G (visits G g)) := by
  have hlam : ∀ x, 0 < lam x := hl.pos hpc hpos
  have hnn : ∀ x, 0 ≤ lam x := hl.nonneg
  refine norm_S_le_of_coercive hmx
    (mul_nonneg (BackwardPolicy.sigmaStar_nonneg hu) (Real.sqrt_nonneg _))
    (coercivity_morozov_op hpc hpos hl hg hu) fun v => ?_
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam v
  rw [sub_meanOp_wtL2 hlam, norm_wtL2 hnn, norm_wtL2 hnn]
  exact nrmL2_perpL2_le hnn hl.total a

/-- **`rem:visit_ratio`, the displayed lower bound**: in the setting of
`theo:training_speed_full` — `g = (log x)²`, `ν = wλ` with `w ≥ w_min ≥ 0`, on the loop closure
of a finite path-connected marked graph — at any `μ = uλ ∼ λ`, with `u_max := max u`, the
contribution to the gradient mass of a set `U` of states on which `|r − 1| ≥ δ`,
`δ ∈ (0, 1/2]`, is
`∫_U |g'(r)(1−r)| (dν/dμ) dλ ≥ (w_min/u_max)(δ²/2) ∑_{x∈U} N(x)/(2+σ̄)`,
and it is at most the whole gradient mass `|∫ D dλ|`. -/
theorem visit_ratio_mass_lower (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam g σ u w : V → ℝ} {wmin δ : ℝ} (hl : B.IsInvProb lam) (hg : B.IsGreen g)
    (hσ : B.IsHitExp σ) (hu : ∀ x, 0 < u x) (hwmin0 : 0 ≤ wmin) (hw : ∀ x, wmin ≤ w x)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (U : Finset V)
    (hU : ∀ x ∈ U, δ ≤ |ratio B.phat lam u x - 1|) :
    wmin / maxOver G u * (δ ^ 2 / 2) * ∑ x ∈ U, visits G g x / (2 + B.sigmaBar σ)
        ≤ ∑ x ∈ U, lam x * (|logSqDeriv (ratio B.phat lam u x) * (1 - ratio B.phat lam u x)|
            * (w x / u x))
      ∧ ∑ x ∈ U, lam x * (|logSqDeriv (ratio B.phat lam u x) * (1 - ratio B.phat lam u x)|
            * (w x / u x))
          ≤ |gradMass B.phat lam u (fun x => w x / u x) logSqDeriv| := by
  have hlam : ∀ x, 0 < lam x := hl.pos hpc hpos
  have hinv : Invariant B.phat lam := invariant_of_isInvProb hl
  have hr : ∀ x, 0 < ratio B.phat lam u x := ratio_pos hinv B.phat_nonneg hlam hu
  have humax : 0 < maxOver G u := (hu G.src).trans_le (le_maxOver u G.src)
  have hwu : ∀ x, 0 ≤ w x / u x := fun x => div_nonneg (hwmin0.trans (hw x)) (hu x).le
  have hterm_nn : ∀ x, 0 ≤ lam x * (|logSqDeriv (ratio B.phat lam u x)
      * (1 - ratio B.phat lam u x)| * (w x / u x)) :=
    fun x => mul_nonneg (hlam x).le (mul_nonneg (abs_nonneg _) (hwu x))
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have hvis : visits G g x / (2 + B.sigmaBar σ) = lam x :=
      (BackwardPolicy.lam_eq_visits_div hpc hpos hl hg hσ x).symm
    rw [hvis]
    have h1 : δ ^ 2 / 2 ≤ |logSqDeriv (ratio B.phat lam u x) * (1 - ratio B.phat lam u x)| :=
      le_abs_logSqDeriv_mul_one_sub (hr x) hδ0 hδ1 (hU x hx)
    have h2 : wmin / maxOver G u ≤ w x / u x := by
      calc wmin / maxOver G u ≤ wmin / u x :=
            div_le_div_of_nonneg_left hwmin0 (hu x) (le_maxOver u x)
        _ ≤ w x / u x := div_le_div_of_nonneg_right (hw x) (hu x).le
    have h3 : 0 ≤ wmin / maxOver G u := div_nonneg hwmin0 humax.le
    have h4 : wmin / maxOver G u * (δ ^ 2 / 2)
        ≤ |logSqDeriv (ratio B.phat lam u x) * (1 - ratio B.phat lam u x)| * (w x / u x) := by
      rw [mul_comm]
      exact mul_le_mul h1 h2 h3 (abs_nonneg _)
    calc wmin / maxOver G u * (δ ^ 2 / 2) * lam x = lam x * (wmin / maxOver G u * (δ ^ 2 / 2)) :=
          by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (hlam x).le
  · have hid : gradMass B.phat lam u (fun x => w x / u x) logSqDeriv
        = ∑ x, lam x * (logSqDeriv (ratio B.phat lam u x) * (1 - ratio B.phat lam u x)
            * (w x / u x)) := by
      simp only [gradMass, lossGradDensity]
      exact integral_gradDensity_potential hinv logSqDeriv (ratio B.phat lam u) _
    have hneg : ∀ x, logSqDeriv (ratio B.phat lam u x) * (1 - ratio B.phat lam u x) ≤ 0 :=
      fun x => logSqDeriv_mul_one_sub_nonpos (hr x)
    have habs : |gradMass B.phat lam u (fun x => w x / u x) logSqDeriv|
        = ∑ x, lam x * (|logSqDeriv (ratio B.phat lam u x) * (1 - ratio B.phat lam u x)|
            * (w x / u x)) := by
      rw [hid, abs_of_nonpos (Finset.sum_nonpos fun x _ =>
        mul_nonpos_of_nonneg_of_nonpos (hlam x).le (mul_nonpos_of_nonpos_of_nonneg (hneg x)
          (hwu x))), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [abs_of_nonpos (hneg x)]
      ring
    rw [habs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      fun x _ _ => hterm_nn x

end VisitRatio

/-! ## Aperiodic chains: summable `L²` mixing, at a geometric rate -/

section Aperiodic

variable {V : Type*} [Fintype V] [DecidableEq V] {K : V → V → ℝ} {lam : V → ℝ}

/-- **The `n`-step kernel** `Kⁿ(x, y)`. -/
def kpow (K : V → V → ℝ) : ℕ → V → V → ℝ
  | 0, x, y => if x = y then 1 else 0
  | n + 1, x, y => ∑ z, kpow K n x z * K z y

theorem kpow_nonneg (hK : ∀ x y, 0 ≤ K x y) : ∀ n x y, 0 ≤ kpow K n x y
  | 0, x, y => by
    simp only [kpow]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  | n + 1, x, y => Finset.sum_nonneg fun z _ => mul_nonneg (kpow_nonneg hK n x z) (hK z y)

theorem kpow_row_sum (hK : Core.IsMarkov K) : ∀ n x, ∑ y, kpow K n x y = 1
  | 0, x => by simp only [kpow, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  | n + 1, x => by
    simp only [kpow]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hK.row_sum, mul_one]
    exact kpow_row_sum hK n x

theorem kpow_inv (hinv : Core.IsInvariant lam K) : ∀ n y, ∑ x, lam x * kpow K n x y = lam y
  | 0, y => by simp only [kpow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  | n + 1, y => by
    simp only [kpow, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h : ∀ z, ∑ x, lam x * (kpow K n x z * K z y) = lam z * K z y := fun z => by
      rw [← kpow_inv hinv n z, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [h]
    exact hinv.inv y

theorem kpow_pos_of_reachIn (hK : ∀ x y, 0 ≤ K x y) :
    ∀ {n : ℕ} {x y : V}, ReachIn K n x y → 0 < kpow K n x y
  | 0, x, y, h => by
    have h' : x = y := h
    simp only [kpow, if_pos h', zero_lt_one]
  | n + 1, x, y, h => by
    obtain ⟨z, hz, hzy⟩ := h
    exact Finset.sum_pos' (fun w _ => mul_nonneg (kpow_nonneg hK n x w) (hK w y))
      ⟨z, Finset.mem_univ z, mul_pos (kpow_pos_of_reachIn hK hz)
        (lt_of_le_of_ne (hK z y) (Ne.symm hzy))⟩

/-- `Pⁿ` on densities is `a ↦ (∑ₓ λ(x)Kⁿ(x,·)a(x))/λ`. -/
theorem densOp_pow_wtL2_kpow (hlam : ∀ x, 0 < lam x) (n : ℕ) (a : V → ℝ) :
    (densOp lam K ^ n) (wtL2 lam a)
      = wtL2 lam (fun y => (∑ x, lam x * kpow K n x y * a x) / lam y) := by
  induction n with
  | zero =>
    rw [pow_zero, one_apply_eq_self]
    congr 1
    funext y
    simp only [kpow, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [mul_div_cancel_left₀ _ (hlam y).ne']
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, densOp_wtL2 hlam]
    congr 1
    funext y
    rw [Core.densAct_apply]
    congr 1
    have h1 : ∀ z, lam z * K z y * ((∑ x, lam x * kpow K n x z * a x) / lam z)
        = ∑ x, lam x * (kpow K n x z * K z y) * a x := fun z => by
      rw [mul_comm (lam z), mul_assoc, mul_div_cancel₀ _ (hlam z).ne', Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [h1, kpow]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]

/-- **Aperiodicity plus irreducibility make some power of the kernel positive** (Schur's theorem
on numerical semigroups, `Nat.exists_mem_closure_of_ge`). -/
theorem exists_kpow_pos (hK : ∀ x y, 0 ≤ K x y) (hirr : ∀ x y, ∃ n, ReachIn K n x y) {x₀ : V}
    (hap : ¬ ∃ d, PeriodicAt K x₀ d) : ∃ N, 0 < N ∧ ∀ x y, 0 < kpow K N x y := by
  classical
  set S : Set ℕ := {n | ReachIn K n x₀ x₀} with hSdef
  let M : AddSubmonoid ℕ :=
    { carrier := S
      add_mem' := fun ha hb => ReachIn.append ha hb
      zero_mem' := rfl }
  have hclos : AddSubmonoid.closure S ≤ M := AddSubmonoid.closure_le.2 fun _ h => h
  have hgcd : Nat.setGcd S = 1 := by
    by_contra hne
    apply hap
    by_cases hz : Nat.setGcd S = 0
    · refine ⟨2, le_rfl, fun n hn => ?_⟩
      have h0 : n ∈ ({0} : Set ℕ) := Nat.setGcd_eq_zero_iff.1 hz hn
      rw [Set.mem_singleton_iff.1 h0]
      exact dvd_zero 2
    · exact ⟨Nat.setGcd S, by omega, fun n hn => Nat.setGcd_dvd_of_mem hn⟩
  obtain ⟨N₀, hN₀⟩ := Nat.exists_mem_closure_of_ge S
  have hS : ∀ m ≥ N₀, ReachIn K m x₀ x₀ := fun m hm =>
    hclos (hN₀ m hm (by rw [hgcd]; exact one_dvd m))
  choose a ha using fun x => hirr x x₀
  choose b hb using fun y => hirr x₀ y
  refine ⟨(∑ x, a x) + N₀ + (∑ y, b y) + 1, by omega, fun x y => ?_⟩
  have hax : a x ≤ ∑ z, a z := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  have hby : b y ≤ ∑ z, b z := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
  have hmid := hS ((∑ z, a z) + N₀ + (∑ z, b z) + 1 - a x - b y) (by omega)
  have hpath := ((ha x).append hmid).append (hb y)
  have heq : a x + ((∑ z, a z) + N₀ + (∑ z, b z) + 1 - a x - b y) + b y
      = (∑ z, a z) + N₀ + (∑ z, b z) + 1 := by omega
  rw [heq] at hpath
  exact kpow_pos_of_reachIn hK hpath

omit [DecidableEq V] in
/-- **The variance inequality**: a row-stochastic `R ≥ 0` with `λR = λ` and `R(y,x) ≥ δλ(x)`
contracts the `λ`-mean-zero functions in `L²(λ)` by `1 − δ`. -/
theorem variance_contract' {R : V → V → ℝ} {l h : V → ℝ} {δ : ℝ}
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

omit [DecidableEq V] in
theorem norm_wtL2_sq' (hnn : ∀ x, 0 ≤ lam x) (a : V → ℝ) :
    ‖wtL2 lam a‖ ^ 2 = Graph.ipL2 lam a a := by
  rw [norm_wtL2 hnn, Graph.sq_nrmL2 hnn]

omit [DecidableEq V] in
theorem sum_sq_sub_mean' {a : V → ℝ} (hlsum : ∑ x, lam x = 1) :
    ∑ x, lam x * (a x - ∑ z, lam z * a z) ^ 2 = ∑ x, lam x * a x ^ 2 - (∑ z, lam z * a z) ^ 2 := by
  set m := ∑ z, lam z * a z with hm
  have h : ∀ x, lam x * (a x - m) ^ 2 = lam x * a x ^ 2 - 2 * m * (lam x * a x) + m ^ 2 * lam x :=
    fun x => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hm, hlsum]
  ring

/-- **The `L²(λ)` Doeblin step**: if `Kᴺ(x, y) ≥ ε` everywhere then `‖Pᴺ − Π‖ ≤ √(1 − ε)`. -/
theorem norm_pow_sub_meanOp_le (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hfloor : ∀ x y, ε ≤ kpow K N x y) :
    ε ≤ 1 ∧ ‖densOp lam K ^ N - meanOp lam‖ ≤ Real.sqrt (1 - ε) := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hne : Nonempty V := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at htot
    exact zero_ne_one htot
  obtain ⟨y₀⟩ := hne
  set R : V → V → ℝ := fun y x => lam x * kpow K N x y / lam y with hR
  have hrow : ∀ y, ∑ x, R y x = 1 := fun y => by
    simp only [hR]
    rw [← Finset.sum_div, kpow_inv hinv N y, div_self (hlam y).ne']
  have hinvR : ∀ x, ∑ y, lam y * R y x = lam x := fun x => by
    simp only [hR]
    have e : ∀ y, lam y * (lam x * kpow K N x y / lam y) = lam x * kpow K N x y := fun y => by
      rw [mul_div_cancel₀ _ (hlam y).ne']
    simp only [e]
    rw [← Finset.mul_sum, kpow_row_sum hK N x, mul_one]
  have hlle : ∀ x, lam x ≤ 1 := fun x => by
    rw [← htot]
    exact Finset.single_le_sum (fun z _ => hnn z) (Finset.mem_univ x)
  have hmin : ∀ y x, ε * lam x ≤ R y x := fun y x => by
    simp only [hR]
    rw [le_div_iff₀ (hlam y)]
    have h1 : ε * lam x * lam y ≤ ε * lam x := by
      have := mul_le_mul_of_nonneg_left (hlle y) (mul_nonneg hε (hnn x))
      linarith
    have h2 : ε * lam x ≤ lam x * kpow K N x y := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hfloor x y) (hnn x)
    linarith
  have hε1 : ε ≤ 1 := by
    have h := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hmin y₀ x
    rw [← Finset.mul_sum, htot, mul_one, hrow y₀] at h
    exact h
  refine ⟨hε1, ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun w => ?_⟩
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam w
  set m0 := Graph.meanL2 lam a with hm0
  set h : V → ℝ := fun x => a x - m0 with hh
  have happ : (densOp lam K ^ N - meanOp lam) (wtL2 lam a)
      = wtL2 lam (fun y => ∑ x, R y x * h x) := by
    rw [sub_apply, densOp_pow_wtL2_kpow hlam, meanOp_wtL2 hlam, ← wtL2_sub]
    congr 1
    funext y
    simp only [hh, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hR]
    have hr1 := hrow y
    simp only [hR] at hr1
    rw [hr1, one_mul, hm0, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  have hvar := variance_contract' (R := R) (l := lam) (h := h) (δ := ε) hrow hinvR hnn htot hε
    hmin (by simp only [hh, hm0, Graph.meanL2, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, htot, one_mul, sub_self])
  have hhsq : ∑ x, lam x * h x ^ 2 ≤ ‖wtL2 lam a‖ ^ 2 := by
    rw [norm_wtL2_sq' hnn]
    have h1 := sum_sq_sub_mean' (a := a) htot
    simp only [hh, hm0, Graph.meanL2, Graph.ipL2]
    have e : ∀ x, lam x * (a x * a x) = lam x * a x ^ 2 := fun x => by ring
    simp only [e]
    nlinarith [sq_nonneg (∑ z, lam z * a z)]
  have hsq : ‖(densOp lam K ^ N - meanOp lam) (wtL2 lam a)‖ ^ 2
      ≤ (1 - ε) * ‖wtL2 lam a‖ ^ 2 := by
    rw [happ, norm_wtL2_sq' hnn]
    simp only [Graph.ipL2]
    have e : ∀ y, lam y * ((∑ x, R y x * h x) * (∑ x, R y x * h x))
        = lam y * (∑ x, R y x * h x) ^ 2 := fun y => by ring
    simp only [e]
    calc _ ≤ (1 - ε) * ∑ x, lam x * h x ^ 2 := hvar
      _ ≤ _ := mul_le_mul_of_nonneg_left hhsq (by linarith)
  have hle : ‖(densOp lam K ^ N - meanOp lam) (wtL2 lam a)‖
      ≤ Real.sqrt ((1 - ε) * ‖wtL2 lam a‖ ^ 2) :=
    Real.le_sqrt_of_sq_le hsq
  rwa [Real.sqrt_mul (by linarith), Real.sqrt_sq (norm_nonneg _)] at hle

omit [DecidableEq V] in
theorem meanOp_mul_densOp_pow' (hK : Core.IsMarkov K) (hlam : ∀ x, 0 < lam x) (n : ℕ) :
    meanOp lam * densOp lam K ^ n = meanOp lam := by
  induction n with
  | zero => rw [pow_zero, mul_one]
  | succ n ih => rw [pow_succ', ← mul_assoc, meanOp_mul_densOp hK hlam, ih]

omit [DecidableEq V] in
/-- `β̂_{n+N} ≤ ‖Pᴺ − Π‖ β̂ₙ`. -/
theorem beta_add_le (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (N n : ℕ) :
    Core.Mixing.beta (densOp lam K) (meanOp lam) (n + N)
      ≤ ‖densOp lam K ^ N - meanOp lam‖ * Core.Mixing.beta (densOp lam K) (meanOp lam) n := by
  have hidem : meanOp lam * meanOp lam = meanOp lam :=
    ContinuousLinearMap.ext fun u => meanOp_idem hlam htot u
  have hid : densOp lam K ^ (n + N) - meanOp lam
      = (densOp lam K ^ N - meanOp lam) * (densOp lam K ^ n - meanOp lam) := by
    rw [sub_mul, mul_sub, mul_sub, densOp_pow_mul_meanOp' hinv hlam,
      meanOp_mul_densOp_pow' hK hlam, hidem, add_comm n N, pow_add]
    abel
  unfold Core.Mixing.beta
  rw [hid]
  exact norm_mul_le _ _

omit [DecidableEq V] in
/-- `β̂ₙ ≤ 2`: `P` and `Π` are contractions of `L²(λ)`. -/
theorem beta_le_two (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (n : ℕ) :
    Core.Mixing.beta (densOp lam K) (meanOp lam) n ≤ 2 := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hP : ∀ w, ‖densOp lam K w‖ ≤ ‖w‖ := fun w => by
    obtain ⟨a, rfl⟩ := exists_wtL2 hlam w
    rw [densOp_wtL2 hlam, norm_wtL2 hnn, norm_wtL2 hnn]
    exact nrmL2_densAct_le hK hinv a
  have hPn : ∀ w, ‖(densOp lam K ^ n) w‖ ≤ ‖w‖ := by
    induction n with
    | zero => intro w; rw [pow_zero, one_apply_eq_self]
    | succ n ih => intro w; rw [pow_succ', mul_apply_eq_comp]; exact (hP _).trans (ih w)
  have hPi : ∀ w, ‖meanOp lam w‖ ≤ ‖w‖ := fun w => by
    obtain ⟨a, rfl⟩ := exists_wtL2 hlam w
    rw [meanOp_wtL2 hlam, norm_wtL2 hnn, norm_wtL2 hnn]
    have hc : Graph.nrmL2 lam (fun _ => Graph.meanL2 lam a) = |Graph.meanL2 lam a| := by
      rw [Graph.nrmL2]
      have : Graph.ipL2 lam (fun _ => Graph.meanL2 lam a) (fun _ => Graph.meanL2 lam a)
          = Graph.meanL2 lam a ^ 2 := by
        simp only [Graph.ipL2, ← Finset.sum_mul, htot]; ring
      rw [this, Real.sqrt_sq_eq_abs]
    rw [hc]
    exact abs_meanL2_le_nrmL2 hnn htot a
  unfold Core.Mixing.beta
  have h1 : ‖densOp lam K ^ n‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by rw [one_mul]; exact hPn w
  have h2 : ‖meanOp lam‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by rw [one_mul]; exact hPi w
  calc _ ≤ ‖densOp lam K ^ n‖ + ‖meanOp lam‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

/-- **Geometric decay of the mixing coefficients from a Doeblin floor**: if `Kᴺ ≥ ε > 0`
entrywise, then `β̂ₙ ≤ (2/r^{N−1}) rⁿ` with the explicit rate `r = 1 − ε/(2N) < 1`. -/
theorem beta_le_geometric_of_floor (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hfloor : ∀ x y, ε ≤ kpow K N x y) (n : ℕ) :
    Core.Mixing.beta (densOp lam K) (meanOp lam) n
      ≤ 2 / (1 - ε / (2 * N)) ^ (N - 1) * (1 - ε / (2 * N)) ^ n := by
  obtain ⟨hε1, hq⟩ := norm_pow_sub_meanOp_le hK hinv hlam htot hε.le hfloor
  set r : ℝ := 1 - ε / (2 * N) with hr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hεN : ε / (2 * N) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r ≤ 1 := by rw [hr]; have := div_nonneg hε.le (by positivity : (0:ℝ) ≤ 2 * N); linarith
  have hqr : ‖densOp lam K ^ N - meanOp lam‖ ≤ r ^ N := by
    refine hq.trans ?_
    have hs : Real.sqrt (1 - ε) ≤ 1 - ε / 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hb := one_add_mul_le_pow (a := -(ε / (2 * N))) (by linarith) N
    have : 1 - ε / 2 ≤ r ^ N := by
      have e : (N : ℝ) * -(ε / (2 * N)) = -(ε / 2) := by field_simp
      have e2 : (1 + -(ε / (2 * N))) = r := by rw [hr]; ring
      rw [e, e2] at hb
      linarith
    linarith
  have hblock : ∀ k j : ℕ, Core.Mixing.beta (densOp lam K) (meanOp lam) (N * k + j)
      ≤ 2 * (r ^ N) ^ k := by
    intro k j
    induction k with
    | zero => rw [mul_zero, zero_add, pow_zero, mul_one]; exact beta_le_two hK hinv hlam htot j
    | succ k ih =>
      have e : N * (k + 1) + j = (N * k + j) + N := by ring
      rw [e]
      calc Core.Mixing.beta (densOp lam K) (meanOp lam) (N * k + j + N)
          ≤ ‖densOp lam K ^ N - meanOp lam‖ * Core.Mixing.beta (densOp lam K) (meanOp lam)
              (N * k + j) := beta_add_le hK hinv hlam htot N _
        _ ≤ r ^ N * (2 * (r ^ N) ^ k) :=
            mul_le_mul hqr ih (Core.Mixing.beta_nonneg _ _ _) (pow_nonneg hr0.le _)
        _ = 2 * (r ^ N) ^ (k + 1) := by ring
  have hn := hblock (n / N) (n % N)
  rw [Nat.div_add_mod] at hn
  have hexp : r ^ (N * (n / N) + (N - 1)) ≤ r ^ n := by
    refine pow_le_pow_of_le_one hr0.le hr1 ?_
    have := Nat.lt_mul_div_succ n hN
    rw [Nat.mul_succ] at this
    omega
  have hrN : 0 < r ^ (N - 1) := pow_pos hr0 _
  calc Core.Mixing.beta (densOp lam K) (meanOp lam) n ≤ 2 * (r ^ N) ^ (n / N) := hn
    _ = 2 / r ^ (N - 1) * r ^ (N * (n / N) + (N - 1)) := by
        rw [pow_add, ← pow_mul]; field_simp
    _ ≤ 2 / r ^ (N - 1) * r ^ n := mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **`rem:graphs_vs_L2`: a finite irreducible aperiodic chain has summable `L²` mixing, at a
geometric rate.** For `K` Markov with an invariant probability `λ > 0`, irreducible, and aperiodic
at some state — no `d ≥ 2` divides all its return times — some `N ≥ 1` has `Kᴺ ≥ ε > 0` entrywise,
`β̂ₙ ≤ (2/r^{N−1}) rⁿ` with `r = 1 − ε/(2N) < 1`, and `Core.Mixing (P, Π)` holds. `N` comes from
Schur's theorem on numerical semigroups and is not effective. -/
theorem mixing_of_aperiodic (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (hirr : ∀ x y, ∃ n, ReachIn K n x y)
    {x₀ : V} (hap : ¬ ∃ d, PeriodicAt K x₀ d) :
    ∃ (N : ℕ) (ε : ℝ), 0 < N ∧ 0 < ε ∧ (∀ x y, ε ≤ kpow K N x y)
      ∧ (∀ n, Core.Mixing.beta (densOp lam K) (meanOp lam) n
          ≤ 2 / (1 - ε / (2 * N)) ^ (N - 1) * (1 - ε / (2 * N)) ^ n)
      ∧ 1 - ε / (2 * N) < 1
      ∧ Core.Mixing (densOp lam K) (meanOp lam) := by
  have hne : Nonempty V := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at htot
    exact zero_ne_one htot
  obtain ⟨N, hN, hpos⟩ := exists_kpow_pos hK.nonneg hirr hap
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image (Finset.univ : Finset (V × V))
    (fun p => kpow K N p.1 p.2) Finset.univ_nonempty
  set ε := kpow K N p.1 p.2 with hεdef
  have hε : 0 < ε := hpos p.1 p.2
  have hfloor : ∀ x y, ε ≤ kpow K N x y := fun x y => hp (x, y) (Finset.mem_univ _)
  have hgeo := beta_le_geometric_of_floor hK hinv hlam htot hN hε hfloor
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hεN : 0 < ε / (2 * N) := by positivity
  have hεN2 : ε / (2 * N) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 := (norm_pow_sub_meanOp_le hK hinv hlam htot hε.le hfloor).1
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hr0 : 0 ≤ 1 - ε / (2 * N) := by linarith
  have hr1 : 1 - ε / (2 * N) < 1 := by linarith
  refine ⟨N, ε, hN, hε, hfloor, hgeo, hr1, ?_⟩
  refine ⟨meanOp_mul_densOp hK hlam, densOp_mul_meanOp hinv hlam, ?_⟩
  exact Summable.of_nonneg_of_le (Core.Mixing.beta_nonneg _ _) hgeo
    ((summable_geometric_of_lt_one hr0 hr1).mul_left _)

omit [Fintype V] [DecidableEq V] in
/-- **Periodicity is the return-time gcd**: `x₀` is periodic in the sense of `PeriodicAt` for some
`d` if and only if the gcd of its return times, `Nat.setGcd {n | x₀ ⤳ x₀ in n steps}`, is not `1`.
So `¬ ∃ d, PeriodicAt K x₀ d` is aperiodicity in the textbook sense. -/
theorem periodicAt_iff_setGcd {x₀ : V} :
    (∃ d, PeriodicAt K x₀ d) ↔ Nat.setGcd {n | ReachIn K n x₀ x₀} ≠ 1 := by
  constructor
  · rintro ⟨d, hd, hdiv⟩ h1
    have := Nat.dvd_setGcd_iff (s := {n | ReachIn K n x₀ x₀}) (n := d) |>.2 fun m hm => hdiv m hm
    rw [h1] at this
    have := Nat.le_of_dvd one_pos this
    omega
  · intro hne
    by_cases hz : Nat.setGcd {n | ReachIn K n x₀ x₀} = 0
    · refine ⟨2, le_rfl, fun n hn => ?_⟩
      have h0 : n ∈ ({0} : Set ℕ) := Nat.setGcd_eq_zero_iff.1 hz hn
      rw [Set.mem_singleton_iff.1 h0]
      exact dvd_zero 2
    · exact ⟨Nat.setGcd {n | ReachIn K n x₀ x₀}, by omega, fun n hn => Nat.setGcd_dvd_of_mem hn⟩

end Aperiodic

/-! ## `rem:graphs_vs_L2` on the loop closure of a marked graph -/

section GraphsVsL2

open Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : MarkedGraph V} {B : BackwardPolicy G}

omit [Fintype V] [DecidableEq V] in
/-- Cyclic classes force every path length to be read off the classes: `c(y) = c(x) + n`. -/
theorem cyclic_reachIn {K : V → V → ℝ} {d : ℕ} {c : V → ZMod d}
    (hc : ∀ x y, K x y ≠ 0 → c y = c x + 1) :
    ∀ {n : ℕ} {x y : V}, ReachIn K n x y → c y = c x + n
  | 0, x, y, h => by
    have h' : x = y := h
    rw [h', Nat.cast_zero, add_zero]
  | n + 1, x, y, h => by
    obtain ⟨z, hz, hzy⟩ := h
    rw [hc z y hzy, cyclic_reachIn hc hz, Nat.cast_succ, add_assoc]

omit [Fintype V] [DecidableEq V] in
/-- **Cyclic classes make every state periodic**: with `d ≥ 2` cyclic classes, `d` divides every
return time. -/
theorem periodicAt_of_cyclic {K : V → V → ℝ} {d : ℕ} (hd : 2 ≤ d) {c : V → ZMod d}
    (hc : ∀ x y, K x y ≠ 0 → c y = c x + 1) (x₀ : V) : PeriodicAt K x₀ d := by
  refine ⟨hd, fun n hn => ?_⟩
  have h := cyclic_reachIn hc hn
  have h0 : ((n : ℕ) : ZMod d) = 0 := by
    have := congrArg (fun t => t - c x₀) h
    simpa only [sub_self, add_sub_cancel_left] using this.symm
  exact (ZMod.natCast_eq_zero_iff _ _).1 h0

/-- **`rem:graphs_vs_L2`: a finite irreducible aperiodic loop closure has summable `L²` mixing,
`B̂ ≥ 1`, and `B̂` is a coercivity constant.** -/
theorem graphs_vs_L2_aperiodic (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) {x₀ : V} (hap : ¬ ∃ d, PeriodicAt B.phat x₀ d) :
    Core.Mixing (densOp lam B.phat) (meanOp lam)
      ∧ 1 ≤ Core.Mixing.B (densOp lam B.phat) (meanOp lam)
      ∧ ∀ f : V → ℝ, Graph.nrmL2 lam (perpL2 lam f)
          ≤ Core.Mixing.B (densOp lam B.phat) (meanOp lam) * Graph.nrmL2 lam (Aop B.phat lam f) := by
  haveI : Nontrivial V := ⟨⟨G.src, G.snk, G.src_ne_snk⟩⟩
  have hlam := hl.pos hpc hpos
  obtain ⟨-, -, -, -, -, -, -, hmx⟩ := mixing_of_aperiodic (phat_isMarkov B) (phat_isInvariant hl)
    hlam hl.total (fun x y => reachIn_of_breach (B.breach_all hpc hpos x y)) hap
  exact ⟨hmx, one_le_B_densOp hlam hmx, mixing_coercivity_finite (phat_isInvariant hl) hlam hmx⟩

/-- **`rem:graphs_vs_L2`: on an aperiodic loop closure, `theo:db_stable_frozen_full` gives the
rate `g''(1)w_min/B̂²` of the linearized gradient descent toward the balanced ray** — `Πhₖ` is
conserved and `‖hₖ^⊥‖ ≤ (1 − εϱ)ᵏ‖h₀^⊥‖` with `ϱ = g''(1)w_min/B̂²`, `B̂ = ∑ₙ β̂ₙ`, for every step
`ε ≤ (4g''(1)‖w‖_∞)⁻¹`. -/
theorem graphs_vs_L2_rate (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) {x₀ : V} (hap : ¬ ∃ d, PeriodicAt B.phat x₀ d)
    {w : V → ℝ} {g2 wmin wsup eps : ℝ} {h : ℕ → V → ℝ}
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hwsup : ∀ x, w x ≤ wsup)
    (heps : 0 ≤ eps) (hepsL : eps * (4 * g2 * wsup) ≤ 1)
    (hstep : ∀ k x, h (k + 1) x = h k x - eps * linHess B.phat lam w g2 (h k) x) :
    (∀ k, Graph.meanL2 lam (h k) = Graph.meanL2 lam (h 0)) ∧
      ∀ k, Graph.nrmL2 lam (perpL2 lam (h k))
        ≤ (1 - eps * (g2 * wmin / Core.Mixing.B (densOp lam B.phat) (meanOp lam) ^ 2)) ^ k
          * Graph.nrmL2 lam (perpL2 lam (h 0)) := by
  obtain ⟨hmx, hB1, -⟩ := graphs_vs_L2_aperiodic hpc hpos hl hap
  have hws : wmin ≤ wsup := (hwmin G.src).trans (hwsup G.src)
  exact stable_frozen_discrete_mixing (phat_isMarkov B) (phat_isInvariant hl) (hl.pos hpc hpos)
    hl.total hg2 hwmin0 hwmin hwsup (hwmin0.trans hws) hmx (lt_of_lt_of_le one_pos hB1) heps hepsL
    (Graph.hrho_of_step hB1 hg2 hwmin0 hws heps hepsL) hstep

/-- **`rem:graphs_vs_L2`: `prop:morozov_rate` removes the aperiodicity**: the same contraction
holds on every loop closure, periodic or not, at `B̂_σ` in place of `B̂`
(`MorozovConsume.stable_frozen_discrete_sigma`). -/
theorem graphs_vs_L2_rate_sigma (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam gr uH : V → ℝ} (hl : B.IsInvProb lam) (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    {w : V → ℝ} {g2 wmin wsup eps : ℝ} {h : ℕ → V → ℝ}
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hwsup : ∀ x, w x ≤ wsup)
    (heps : 0 ≤ eps) (hepsL : eps * (4 * g2 * wsup) ≤ 1)
    (hstep : ∀ k x, h (k + 1) x = h k x - eps * linHess B.phat lam w g2 (h k) x) :
    (∀ k, Graph.meanL2 lam (h k) = Graph.meanL2 lam (h 0)) ∧
      ∀ k, Graph.nrmL2 lam (perpL2 lam (h k))
        ≤ (1 - eps * (g2 * wmin * minOver G (visits G gr)
              / (sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH)))) ^ k
          * Graph.nrmL2 lam (perpL2 lam (h 0)) :=
  Graph.stable_frozen_discrete_sigma hpc hpos hl hg hhit hg2 hwmin0 hwmin hwsup heps hepsL hstep

/-- **`rem:graphs_vs_L2`: the balanced locus is one-dimensional** — a positive density is balanced
if and only if it is constant, i.e. the flow lies on the ray `cλ`, `c > 0`. -/
theorem graphs_vs_L2_balanced_ray (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam : V → ℝ} (hl : B.IsInvProb lam) {u : V → ℝ} (hu : ∀ x, 0 < u x) :
    Balanced B.phat lam u ↔ ∃ c : ℝ, 0 < c ∧ u = fun _ => c := by
  constructor
  · intro hbal
    refine ⟨Graph.meanL2 lam u, ?_, funext fun x => const_of_balanced_graph hpc hpos hl hu hbal x⟩
    exact Finset.sum_pos (fun x _ => mul_pos (hl.pos hpc hpos x) (hu x)) ⟨G.src, Finset.mem_univ _⟩
  · rintro ⟨c, -, rfl⟩ y
    simp only [pushMass]
    rw [← hl.inv y, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- **`rem:graphs_vs_L2`: the total mass increases along the nonlinear gradient flow of a strictly
unimodal generator** (`prop:no_distant_equilibrium`*(2)*, `MassAscent.mass_monotone_flow`), on
every positive trajectory of the flow on the loop closure. -/
theorem graphs_vs_L2_mass_monotone (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ} (hl : B.IsInvProb lam)
    (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x) (hnu : ∀ x, 0 < nu x) (hg : StrictlyUnimodal gd)
    (hflow : IsGradientFlow B.phat lam nu gd u) :
    MonotoneOn (fun s : ℝ => Graph.meanL2 lam (u s)) (Ici 0) :=
  mass_monotone_flow (invariant_of_isInvProb hl) B.phat_nonneg (hl.pos hpc hpos) hu hnu hg hflow

end GraphsVsL2

/-! ## Witnesses: a directed path, whose loop closure is a directed cycle, and an aperiodic
triangle -/

section PathGraph

open Graph

/-- **The directed path** `0 → 1 → ⋯ → n+1` on `Fin (n+2)`, source `0`, sink `n+1`. -/
def pathGraph (n : ℕ) : MarkedGraph (Fin (n + 2)) where
  Edge i j := (j : ℕ) = i + 1
  src := 0
  snk := Fin.last (n + 1)
  src_ne_snk := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  no_edge_into_src := fun x h => by
    simp only [Fin.val_zero] at h
    omega
  no_edge_out_of_snk := fun y h => by
    have := y.isLt
    simp only [Fin.val_last] at h
    omega

/-- The only backward policy on the path: one step back. -/
noncomputable def pathPolicy (n : ℕ) : BackwardPolicy (pathGraph n) where
  pb s s' := if (s : ℕ) = s' + 1 then 1 else 0
  nonneg s s' := by
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  row_sum s hs := by
    have hs' : (s : ℕ) ≠ 0 := fun h => hs (Fin.ext (by simpa [pathGraph] using h))
    rw [Finset.sum_eq_single (⟨(s : ℕ) - 1, by omega⟩ : Fin (n + 2))]
    · rw [if_pos (by simp only; omega)]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by simp only; omega))
    · intro h
      exact absurd (Finset.mem_univ _) h
  supp s s' _ h := by
    by_contra hc
    exact h (if_neg hc)

theorem pathGraph_pathConnected (n : ℕ) : (pathGraph n).PathConnected := by
  have hfrom : ∀ k (hk : k < n + 2), (pathGraph n).Reach 0 ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      exact (ih (by omega)).tail (show ((⟨k + 1, hk⟩ : Fin (n + 2)) : ℕ) = k + 1 from rfl)
  have hto : ∀ d (hd : d ≤ n + 1),
      (pathGraph n).Reach ⟨n + 1 - d, by omega⟩ (Fin.last (n + 1)) := by
    intro d
    induction d with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ d ih =>
      intro hd
      refine Relation.ReflTransGen.head ?_ (ih (by omega))
      show n + 1 - d = n + 1 - (d + 1) + 1
      omega
  intro s
  refine ⟨hfrom s s.isLt, ?_⟩
  have h := hto (n + 1 - s) (by omega)
  have hs : (⟨n + 1 - (n + 1 - (s : ℕ)), by omega⟩ : Fin (n + 2)) = s := Fin.ext (by
    simp only; have := s.isLt; omega)
  rwa [hs] at h

theorem pathPolicy_positiveOnEdges (n : ℕ) : (pathPolicy n).PositiveOnEdges := by
  intro s s' h
  show 0 < (if (s : ℕ) = s' + 1 then (1 : ℝ) else 0)
  rw [if_pos (show (s : ℕ) = s' + 1 from h)]
  exact one_pos

/-- **The loop closure of a directed path is a directed cycle**: the backward chain moves
`y + 1 ↦ y` deterministically, indices modulo `n + 2`, the wrap `0 ↦ n+1` included. -/
theorem pathPolicy_phat (n : ℕ) (x y : Fin (n + 2)) :
    (pathPolicy n).phat x y = if x = y + 1 then 1 else 0 := by
  have hval : ((y + 1 : Fin (n + 2)) : ℕ) = if y = Fin.last (n + 1) then (0 : ℕ) else (y : ℕ) + 1 :=
    Fin.val_add_one y
  by_cases hx : x = 0
  · subst hx
    show (if (0 : Fin (n + 2)) = 0 then (if y = Fin.last (n + 1) then (1 : ℝ) else 0)
      else _) = _
    rw [if_pos rfl]
    by_cases hy : y = Fin.last (n + 1)
    · rw [if_pos hy, if_pos]
      rw [hy, Fin.last_add_one]
    · rw [if_neg hy, if_neg]
      intro h
      have := congrArg Fin.val h
      rw [hval, if_neg hy] at this
      simp only [Fin.val_zero] at this
      omega
  · have hx0 : (x : ℕ) ≠ 0 := fun h => hx (Fin.ext (by simpa using h))
    show (if x = 0 then _ else (if (x : ℕ) = y + 1 then (1 : ℝ) else 0)) = _
    rw [if_neg hx]
    have hiff : ((x : ℕ) = y + 1) ↔ x = y + 1 := by
      rw [Fin.ext_iff, hval]
      by_cases hy : y = Fin.last (n + 1)
      · rw [if_pos hy]
        have := x.isLt
        have hyv : (y : ℕ) = n + 1 := by rw [hy, Fin.val_last]
        constructor <;> intro h <;> omega
      · rw [if_neg hy]
    by_cases h : (x : ℕ) = y + 1
    · rw [if_pos h, if_pos (hiff.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

/-- The uniform invariant probability of the directed cycle. -/
theorem pathPolicy_invProb (n : ℕ) : (pathPolicy n).IsInvProb (fun _ => 1 / ((n : ℝ) + 2)) := by
  have hn : (0 : ℝ) < n + 2 := by positivity
  refine ⟨fun _ => by positivity, ?_, fun y => ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · simp only [pathPolicy_phat, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]

/-- The path is leveled by its index. -/
def pathLeveled (n : ℕ) : Leveled (pathGraph n) where
  lvl i := (i : ℕ)
  lvl_src := by simp only [pathGraph, Fin.val_zero, Nat.cast_zero]
  lvl_edge := fun {x y} h => by
    have h' : (y : ℕ) = x + 1 := h
    rw [h']
    push_cast
    ring

/-- **The witness of `rem:graphs_vs_L2` and `rem:visit_ratio`, inhabited**: on the directed path
with `n + 2` vertices, the loop closure is periodic at every state with period `n + 2`, the mixing
sum is `+∞`, and `B̂_σ ≤ (n+2)√((n+3)/min N)` is finite with the coercivity of
`prop:morozov_rate`*(2)*. -/
theorem path_witness (n : ℕ) :
    (∀ x₀, PeriodicAt (pathPolicy n).phat x₀ (n + 2))
      ∧ ∑' k, ENNReal.ofReal (Core.Mixing.beta (densOp (fun _ => 1 / ((n : ℝ) + 2))
          (pathPolicy n).phat) (meanOp (fun _ => 1 / ((n : ℝ) + 2))) k) = ⊤
      ∧ ¬ Core.Mixing (densOp (fun _ => 1 / ((n : ℝ) + 2)) (pathPolicy n).phat)
          (meanOp (fun _ => 1 / ((n : ℝ) + 2)))
      ∧ ∃ gr : Fin (n + 2) → ℝ, (pathPolicy n).IsGreen gr
          ∧ ∀ h : Fin (n + 2) → ℝ,
            Graph.nrmL2 (fun _ => 1 / ((n : ℝ) + 2)) (fun x => h x
                - Graph.meanL2 (fun _ => 1 / ((n : ℝ) + 2)) h)
              ≤ sigmaStar (pathGraph n) (pathLeveled n).lvl
                  * Real.sqrt ((2 + (pathPolicy n).sigmaBar (pathLeveled n).lvl)
                    / minOver (pathGraph n) (visits (pathGraph n) gr))
                * Graph.nrmL2 (fun _ => 1 / ((n : ℝ) + 2))
                    (fun x => h x - (pathPolicy n).pdens (fun _ => 1 / ((n : ℝ) + 2)) h x) := by
  have hpc := pathGraph_pathConnected n
  have hpos := pathPolicy_positiveOnEdges n
  have hl := pathPolicy_invProb n
  have hcyc := leveled_cyclic (pathLeveled n) hpc (pathPolicy n)
  have hsnk : levNat (pathLeveled n) (pathGraph n).snk + 1 = n + 2 := by
    have h := levNat_eq (pathLeveled n) hpc (pathGraph n).snk
    have h2 : (pathLeveled n).lvl (pathGraph n).snk = ((n + 1 : ℕ) : ℝ) := by
      show (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) : ℝ) = _
      rw [Fin.val_last]
    rw [h2] at h
    have := Nat.cast_injective h
    omega
  have hfail := leveled_mixing_fails (pathLeveled n) hpc hpos hl
  obtain ⟨gr, hgr⟩ := BackwardPolicy.exists_isGreen hpc hpos hl
  refine ⟨fun x₀ => ?_, hfail.2.1, hfail.2.2.2, gr, hgr,
    (leveled_bsigma_finite_mixing_infinite (pathLeveled n) hpc hpos hl hgr).1⟩
  have hp := periodicAt_of_cyclic (by have := one_le_levNat_snk (pathLeveled n) hpc; omega) hcyc x₀
  rw [hsnk] at hp
  exact hp

end PathGraph

section Triangle

open Graph

/-- **An aperiodic marked graph**: `s₀ → x → s_f` and `s₀ → s_f` on `Fin 3` (`s₀ = 0`, `x = 1`,
`s_f = 2`); its loop closure has returns to `s₀` of lengths `2` and `3`. -/
def triGraph : MarkedGraph (Fin 3) where
  Edge i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 2)
  src := 0
  snk := 2
  src_ne_snk := by decide
  no_edge_into_src := by decide
  no_edge_out_of_snk := by decide

/-- The triangle's backward policy: `π_←(x → s₀) = 1`, `π_←(s_f → x) = π_←(s_f → s₀) = 1/2`. -/
noncomputable def triPb (s s' : Fin 3) : ℝ :=
  if s = 1 ∧ s' = 0 then 1 else if s = 2 ∧ (s' = 0 ∨ s' = 1) then 1 / 2 else 0

noncomputable def triPolicy : BackwardPolicy triGraph where
  pb := triPb
  nonneg s s' := by unfold triPb; split_ifs <;> norm_num
  row_sum s hs := by
    fin_cases s
    · exact absurd rfl hs
    · simp +decide [triPb]
    · simp +decide [triPb, Fin.sum_univ_three]; norm_num
  supp s s' hs h := by
    fin_cases s <;> fin_cases s' <;> simp_all +decide [triPb, triGraph]

theorem triGraph_pathConnected : triGraph.PathConnected := by
  have e01 : triGraph.Edge 0 1 := Or.inl ⟨rfl, rfl⟩
  have e12 : triGraph.Edge 1 2 := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have e02 : triGraph.Edge 0 2 := Or.inr (Or.inr ⟨rfl, rfl⟩)
  intro s
  fin_cases s
  · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.single e02⟩
  · exact ⟨Relation.ReflTransGen.single e01, Relation.ReflTransGen.single e12⟩
  · exact ⟨Relation.ReflTransGen.single e02, Relation.ReflTransGen.refl⟩

theorem triPolicy_positiveOnEdges : triPolicy.PositiveOnEdges := by
  intro s s' h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp +decide [triPolicy, triPb]

/-- **The triangle's loop closure is aperiodic at `s₀`**: returns of lengths `2` and `3`. -/
theorem triPolicy_aperiodic : ¬ ∃ d, PeriodicAt triPolicy.phat 0 d := by
  rintro ⟨d, hd, hdiv⟩
  have h02 : triPolicy.phat 0 2 ≠ 0 := by
    simp +decide [BackwardPolicy.phat]
  have h20 : triPolicy.phat 2 0 ≠ 0 := by
    simp +decide [BackwardPolicy.phat, triPolicy, triPb, triGraph]
  have h21 : triPolicy.phat 2 1 ≠ 0 := by
    simp +decide [BackwardPolicy.phat, triPolicy, triPb, triGraph]
  have h10 : triPolicy.phat 1 0 ≠ 0 := by
    simp +decide [BackwardPolicy.phat, triPolicy, triPb, triGraph]
  have r1 : ReachIn triPolicy.phat 1 0 2 := ⟨0, rfl, h02⟩
  have r2 : ReachIn triPolicy.phat 2 0 0 := ⟨2, r1, h20⟩
  have r2' : ReachIn triPolicy.phat 2 0 1 := ⟨2, r1, h21⟩
  have r3 : ReachIn triPolicy.phat 3 0 0 := ⟨1, r2', h10⟩
  have d2 := hdiv 2 r2
  have d3 := hdiv 3 r3
  have d1 : d ∣ 1 := by simpa using (Nat.dvd_sub d3 d2)
  have := Nat.le_of_dvd one_pos d1
  omega

/-- **The aperiodic witness, inhabited**: on the triangle, for its invariant probability, summable
`L²` mixing holds, and `rem:visit_ratio`'s `‖S‖ ≤ B̂_σ` applies. -/
theorem triangle_witness :
    ∃ lam gr uH : Fin 3 → ℝ, triPolicy.IsInvProb lam ∧ triPolicy.IsGreen gr
      ∧ triPolicy.IsHitExp uH
      ∧ Core.Mixing (densOp lam triPolicy.phat) (meanOp lam)
      ∧ 1 ≤ Core.Mixing.B (densOp lam triPolicy.phat) (meanOp lam)
      ∧ ‖Core.Mixing.S (densOp lam triPolicy.phat) (meanOp lam)‖
          ≤ sigmaStar triGraph uH
            * Real.sqrt ((2 + triPolicy.sigmaBar uH) / minOver triGraph (visits triGraph gr)) := by
  obtain ⟨lam, hl⟩ := triPolicy.exists_invProb
  obtain ⟨gr, hg⟩ := BackwardPolicy.exists_isGreen triGraph_pathConnected
    triPolicy_positiveOnEdges hl
  obtain ⟨uH, hu⟩ := BackwardPolicy.exists_isHitExp (B := triPolicy) triGraph_pathConnected
    triPolicy_positiveOnEdges
  obtain ⟨hmx, hB1, -⟩ := graphs_vs_L2_aperiodic triGraph_pathConnected
    triPolicy_positiveOnEdges hl triPolicy_aperiodic
  exact ⟨lam, gr, uH, hl, hg, hu, hmx, hB1,
    visit_ratio_norm_S_le triGraph_pathConnected triPolicy_positiveOnEdges hl hg hu hmx⟩

end Triangle

/-! ## Inhabitation of the hypothesis bundles of `rem:freezing` -/

section Inhabitation

/-- `(x − 1)²` is admissible in the sense used by `rem:freezing`*(i)*: `g(1) = 0`, `g > 0` off `1`. -/
theorem sq_admissible :
    (fun x : ℝ => (x - 1) ^ 2) 1 = 0 ∧ ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < (fun x : ℝ => (x - 1) ^ 2) x :=
  ⟨by norm_num, fun x _ hx => by
    have : x - 1 ≠ 0 := sub_ne_zero.2 hx
    positivity⟩

/-- **The convex hypothesis bundle of `rem:freezing`*(i)* is inhabited** by `(x − 1)²`. -/
theorem sq_convexOn : ConvexOn ℝ (Ioi 0) fun x : ℝ => (x - 1) ^ 2 := by
  refine ⟨convex_Ioi 0, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg (x - y), mul_nonneg ha hb]

theorem sq_convex_small_deriv :
    (∀ x : ℝ, 0 < x → x < 1 → deriv (fun x : ℝ => (x - 1) ^ 2) x ≤ 0) ∧
      ∀ {x₀ ε : ℝ}, 0 < x₀ → x₀ < 1 → |deriv (fun x : ℝ => (x - 1) ^ 2) x₀| ≤ ε →
        ∀ x ∈ Icc x₀ 1, |deriv (fun x : ℝ => (x - 1) ^ 2) x| ≤ ε ∧ (x - 1) ^ 2 ≤ ε * (1 - x₀) :=
  convex_small_deriv sq_convexOn (fun _ _ => ((differentiableAt_id.sub_const 1).pow 2))
    sq_admissible.1 sq_admissible.2

/-- **The analytic hypothesis bundle of `rem:freezing`*(i)* is inhabited** by `(x − 1)²`. -/
theorem sq_analyticOnNhd : AnalyticOnNhd ℝ (fun x : ℝ => (x - 1) ^ 2) (Ioi 0) :=
  fun _ _ => (analyticAt_id.sub analyticAt_const).pow 2

theorem sq_no_flat (p q : ℝ) (hp : 0 < p) (hpq : p < q) :
    ¬ ∀ x ∈ Ioo p q, deriv (fun x : ℝ => (x - 1) ^ 2) x = 0 :=
  analytic_admissible_no_flat sq_analyticOnNhd sq_admissible.1 sq_admissible.2 hp hpq

/-- **`ThetaOK` is inhabited**: the bands `(5/8, 7/8)`, `(11/8, 13/8)` of
`prop:nonlinear_freezing`*(2)* with `θ = 1/16`. -/
theorem thetaOK_twoStateBands : ThetaOK twoStateBands (1 / 16) :=
  ⟨by norm_num, by norm_num [twoStateBands], by norm_num [twoStateBands]⟩

end Inhabitation

end GFNBounds.Balance.RemarksA
