import GFNBounds.Balance.TrainingSpeed
import GFNBounds.Balance.LocalConvergenceClauses
import GFNBounds.Balance.C3Wrappers
import GFNBounds.Balance.TrainingSpeedAssembled

/-!
# The discrete global phase: gradient descent converges from every positive initialization, with a step chosen from it

**`theo:training_speed_full`** — item *3* (gradient descent): statement `proofs.tex:1021–1033`,
proof `proofs.tex:1048–1090`. Items *1*–*2* are `GFNBounds/Balance/TrainingSpeed.lean`'s, assembled
from `u₀` alone in `TrainingSpeedAssembled.lean`; **the whole theorem** — preamble, items *1*–*3* —
is `training_speed_full_complete`, at the end of this file, which imports
`TrainingSpeedAssembled.lean` for it.
**`theo:training_speed`** — the body twin, `cv_divergence.tex:69–82`, whose discrete sentence this
file certifies through item *3*.
(The bold-backtick form of the label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> *3.* **gradient descent** — write `‖·‖ := ‖·‖_{L²(λ)}`, write `D(u)` for the density against `λ`
> of `∇^λ𝓛_{g,ν}(uλ)` when `u > 0`, and set `u_min := m₀(λ_min p_min e^{−M})^{#𝒱−1}`. There is an
> explicit `γ_* > 0` such that, for every step `0 < γ ≤ γ_*`, there is an explicit integer
> `k₀(γ)` and the gradient descent `u_{k+1} := u_k − γD(u_k)` is well defined and satisfies:
> *(a)* for every `k ≥ 0`, `u_k ≥ u_min` pointwise, `𝓛(u_{k+1}λ) ≤ 𝓛(u_kλ) − (γ/2)‖D(u_k)‖²`,
> `Πu_{k+1} ≥ Πu_k` and `‖u_{k+1}‖² = ‖u_k‖² + γ²‖D(u_k)‖² ≤ 2‖u₀‖²`;
> *(b)* for every `k ≥ 0`, `𝓛(u_kλ) ≤ (𝓛(μ₀)^{−1} + kγκ²/4)^{−1}`;
> *(c)* for every `k ≥ k₀(γ)`, `‖u_k/Πu_k − 1‖ ≤ ε₀`, with `ε₀` as in *2*, and
> `‖u_{k+1} − Πu_{k+1}‖ ≤ (1 − γϱ_σ/(4(Πu_{k₀(γ)})²))‖u_k − Πu_k‖`, where
> `m₀ ≤ Πu_{k₀(γ)} ≤ √2‖u₀‖`;
> *(d)* `Πu_k` increases to some `m_∞ ≤ √2‖u₀‖`, `m_∞λ` is balanced, and for every `k ≥ k₀(γ)`,
> `m_∞ − Πu_k ≤ ‖u_k − Πu_k‖²/Πu_{k₀(γ)}` and `‖u_k − m_∞‖ ≤ (9/8)‖u_k − Πu_k‖`.
> No step bound independent of the initialization exists: for every `γ > 0` and every `μ₀ ∼ λ`
> that is not balanced, `su₀ − γD(su₀)` takes a negative value for every small enough `s > 0`.

> (the theorem's header) … gradient descent with a step chosen from the initialization converges
> to a balanced flow as *3* states … `κ := w_min λ_min^{1/2}/(‖u₀‖‖w‖_{L^∞}M)`,
> `M := max(1, √(𝓛(μ₀)/(w_min λ_min)))`, `ϱ_σ = g''(1)w_min λ_min/σ_*²`; `ε₀` the radius of
> Theorem `theo:local_convergence_full` for `g = (log x)²` at `a = 1/2`, with `B̂_σ` in place of
> `B̂` and `C_∞ = λ_min^{−1/2}`; `p_min` the smallest positive transition probability of `π̂_←`.

> (proof, constants, `:1048–1058`) `θ := λ_min p_min e^{−M}`, `M' := M + ln 3`,
> `b₁ := 2M'e^{M'}`, `b₂ := 2(1+M')e^{2M'}`, `b₃ := (4‖w‖_{L^∞}/u_min²)(1+e^{M'})(b₂(1+e^{M'})+2b₁)`,
> `γ_* := min(1/b₃, (‖u₀‖²/2)𝓛(μ₀)^{−1}, γ₀m₀²)`, `δ₁ := ε₀m₀/(√2B̂_σ‖u₀‖)`,
> `k₀(γ) := ⌈16/(γκ²λ_min w_min δ₁²)⌉ = ⌈32‖u₀‖⁴‖w‖²_{L^∞}M²σ_*²/(γw_min³λ_min³ε₀²m₀²)⌉`.

> (body twin) Both phases hold for the gradient flow and for discrete gradient descent, the latter
> with a step size chosen from the initialization — no step size fixed in advance works from every
> initialization.

## The adversarial read first (lane order of work, step 1): no false step

Every inequality of the printed proof was re-derived before any Lean was written, and then again
by the Lean. **No counterexample; the descent lemma and the region invariance hold as printed.**

* **The region the iterates stay in cannot be jumped.** `𝒰_γ` is cut out by `𝓛(u) ≤ 𝓛(μ₀)` and
  `Πu ≥ m₀`, two quantities the step makes *monotone* (the descent inequality, `ΠD ≤ 0`), and the
  step bound `γ ≤ 1/b₃` is read from constants (`M`, `u_min`) fixed by `u₀` in advance. There is
  no barrier that a continuous trajectory crosses and a discrete one could overshoot: the positivity
  floor is *static* (`BoundaryBlowup.pos_of_loss_le`), not a continuation, and positivity of
  `u_{k+1}` comes from `u_{k+1} ≥ u_k/2` before the floor is invoked. This is unlike Theorem 10's
  discrete clause, whose repaired induction `local_convergence_gd` is consumed unchanged.
* **The relative step** `γ|D(u)| ≤ u/2`: `|P†ψ| ≤ max|ψ| ≤ 2M‖w‖e^M/u_min`, `|rψ| ≤ 2M‖w‖/u`, and
  `b₃u_min²/(4‖w‖) ≥ 2b₁(1+e^{M'}) ≥ M(e^M+1)` — all hold (`abs_lossGrad_le`, `rel_step_le`).
* **The segment** `u_s = u − sD`, `s ∈ [0,γ]`: `u/2 ≤ u_s ≤ 3u/2`, so `r_s ∈ [r/3, 3r] ⊂ [e^{−M'},e^{M'}]`
  by positivity of `P` — holds (`abs_logdiff_le`).
* **The second derivative.** The printed `f'' = ∫w(g''(r_s)χ_s² − 2g'(r_s)χ_s v/u_s)dλ` and
  `|f''| ≤ b₃‖D‖²` hold. The Lean computes `f''` by another route (below) and bounds it by
  `‖w‖(4+2M')(4/u_min²)(1+e^{2M})‖D‖² ≤ b₃‖D‖²` (`b3_bracket_ge`), so the **paper's `b₃`** is the
  step bound certified.
* **(b), (c), (d)**: `x|log x| ≤ 2M|x−1|` on `(0,e^M]`, the inverse recursion, `e^{δ/2}−1 ≤ δ`,
  `δ₁ ≤ ε₀ ≤ 1/32`, homogeneity `h_{j+1} = h_j − (γ/m²)D(1+h_j)` with `γ/m² ≤ γ₀`, `γ ≤ m²/(32‖w‖)`,
  `(32/31)⁴ ≤ 6/5`, `γϱ_σ/(4m²) ≤ 1/64`, and the constants `3/10`, `13/20`, `9/8` — all hold.
* **`k₀(γ)`'s two printed forms agree** exactly (`k0real_eq`).
* **The necessity sentence** holds as printed (`no_uniform_step`).

**Three proof-route differences, none a statement difference.** (1) `f''` is computed state by
state from `log r_s = log(Σ_xλ(x)u_s(x)K(x,·)) − log(λu_s)`, two logarithms of *lines* in `s`
(`hasDerivAt_sq_logdiff_deriv`), not through `g''(r_s)` and `r_s''`; the bound it yields is below
the paper's `b₃`. (2) The per-step Łojasiewicz bound `‖D(u_k)‖ ≥ (κ/√2)𝓛(u_k)` is
`Lojasiewicz.global_lojasiewicz_static` read at `u₀ := u_k`, rather than the paper's inline
`x|log x| ≤ 2M|x−1|` (which is that lemma's content). (3) *(d)*'s `m_∞² − (Πu_k)² ≤ 2γ𝓛(u_k) +
‖ξ_k‖²` is obtained by bounding every `Πu_j`, `j ≥ k`, through the non-increasing `‖u‖² + 2γ𝓛` and
taking the supremum, instead of summing `‖u_{i+1}‖² = ‖u_i‖² + γ²‖D(u_i)‖²` and passing to the
limit; it gives the same inequality without the limit `‖ξ_j‖ → 0`.

## What is proved

| | |
|---|---|
| `taylor_upper`, `hasDerivAt_sq_logdiff`, `hasDerivAt_sq_logdiff_deriv`, `sq_logdiff_deriv2_le` | the scalar calculus: one-sided Taylor, and the per-state loss term along a line with its two derivatives |
| `Mp`, `b1`, `b2`, **`b3`**, `b3_bracket_ge` | the step constants as the printed formulas, and the three lower bounds on `b₃`'s bracket the proof spends |
| `abs_lossGrad_le`, `rel_step_le` | **`γ|D(u)| ≤ u/2`** at `γ ≤ 1/b₃` |
| **`descent_step`** | **the descent lemma**: `u⁺ ≥ u/2` and `𝓛(u⁺) ≤ 𝓛(u) − (γ/2)‖D(u)‖²`, a static statement |
| `abs_log_ratio_le`, `meanL2_lossGrad_nonpos`, **`region_step`** | the positivity floor, `ΠD ≤ 0`, and one step inside the region: floor, positivity, descent, mass ascent, `‖u⁺‖² = ‖u‖² + γ²‖D‖²` |
| `traj_region`, **`traj_a`**, `traj_nrm_le` | the invariant region along the sequence, and **assertion *(a)*** |
| `inv_recursion`, **`traj_b`** | **assertion *(b)***, the discrete Łojasiewicz envelope at the printed `κ` |
| `delta1`, `kappa`, `k0real`, **`traj_entry`** | **the entry bound** at `k ≥ k₀(γ)`: `\|r(u_k) − 1\| ≤ δ₁`, `‖u_k − Πu_k‖ ≤ ε₀m₀`, `‖u_k/Πu_k − 1‖ ≤ ε₀` |
| **`Gamma3Val`**, `eps0At`, `gamma0At`, `Cinf_mul_eps0At_le`, `eps0At_le`, **`traj_c`** | `Γ₃ = 48 + 32 ln 2`, Theorem 10's `ε₀`, `γ₀` at it, `C_∞ε₀ ≤ 1/32`, and **assertion *(c)*'s contraction** through `LocalConvergence.local_convergence_gd` |
| `delta1_le`, `abs_log_le_of_close`, `loss_le_perp_sq`, `limit_arith`, `nrmL2_sub_const_le`, `past_bound`, **`traj_d`** | **assertion *(d)*** and *(c)*'s bounds on `Πu_{k₀}`, plus `‖u_k − m_∞‖ → 0` |
| **`gammaStar`**, `gammaStar_pos`, `le_gammaStar`, **`k0`**, **`k0real_eq`** | `γ_*` and `k₀(γ)` as printed, `γ_* > 0`, and the two forms of `k₀(γ)` equal |
| **`no_uniform_step`**, **`no_uniform_step_graph`** | **the necessity sentence** |
| **`training_speed_gd`** | **item *3*, assembled** on the loop closure of a finite path-connected marked graph, for every floor `p_min` |
| **`training_speed_gd_minPos`**, `minPos`, `minPos_pos`, `minPos_le`, `minPos_le_one` | **item *3* at the paper's `p_min`**, the smallest positive transition probability |
| `exists_descent_seq`, **`training_speed_gd_inhabited`**, **`cycle_training_speed_gd_nonvacuous`** | inhabitation (kb 0025): the sequence exists, `0 < γ ≤ γ_*` is satisfiable on every instance, and on `rem:cycle_no_stalemate`'s cycle from a non-balanced start |
| **`training_speed_gd_minPos_ennreal`** | *(b)* in `[0,∞]` with `𝓛(μ₀)^{−1} := +∞`, and balanced `↔ 𝓛(μ₀)^{−1} = ∞` |
| `Gamma3_logSq_eq_Gamma3Val`, `eps0At_Gamma3Val_eq`, `gamma0At_Gamma3Val_eq` | `Γ₃ = 48 + 32 ln 2` is `sup|g'''|`; `ε₀`, `γ₀` are `C3Wrappers.lean`'s |
| **`gammaStar_ofReal`** | **`γ_*` is the printed three-term minimum in `[0,∞]`** with `𝓛(μ₀)^{−1} := +∞`: `gammaStar`'s case split is exactly the convention |
| `gamma0W_logSq_eq_gamma0At`, `eps0W_logSq_eq_eps0At` | item *3*'s `γ₀`, `ε₀` are `TrainingSpeedAssembled`'s `gamma0W`, `eps0W` at `Γ₃ = sup|g'''|` — the `ε₀` of item *2* literally |
| **`training_speed_gd_exact`** | **item *3* with the paper's quantifiers**, from `u₀` alone: `γ_* > 0`; `γ_*` in `[0,∞]`; balanced `↔ 𝓛(μ₀)^{−1} = ∞`; for every `0 < γ ≤ γ_*` the sequence exists, and every such sequence is positive and satisfies *(a)*, *(b)* in `[0,∞]`, `𝓛(u_k) = 0` for all `k` at a balanced start, *(c)*, *(d)*; the necessity sentence for every non-balanced `μ₀`. No new dynamics: it calls `training_speed_gd_minPos` and `training_speed_gd_minPos_ennreal` |
| **`training_speed_full_complete`** | **`theo:training_speed_full` whole — the principal declaration of the label**: preamble and items *1*–*2* (`TrainingSpeedAssembled.training_speed_full_paper`, the flow constructed) and item *3* (`training_speed_gd_exact`) in one statement |
| `cycle_training_speed_complete_check` | inhabitation of `training_speed_full_complete` on the five-cycle from a non-balanced start |

## Hypothesis checklist — `theo:training_speed_full`*(3)*

| paper hypothesis | here |
|---|---|
| "in the setting above": the loop closure of a finite path-connected marked graph, backward policy positive on its edges, `λ` its invariant probability | ✓ `hpc`, `hpos`, `[Fintype V]`, `hl : B.IsInvProb lam`, kernel `B.phat`, exactly as `training_speed_full` |
| `σ_*` a maximal expected hitting time | ⚠ carried as `hhit : B.IsHitExp uH`, `Graph.Morozov`'s disclosed linear-system reading, as in `TrainingSpeed.lean` |
| `g = (log x)²` | ✓ `logSq`, `logSqDeriv` (the latter a definition `2 log x/x`, inherited) |
| `ν = wλ`, `w ≥ w_min > 0` | ✓ `fun z => lam z * wf z`, `hwmin`, `hw` |
| `‖w‖_{L^∞}` | ⚠ a parameter `wsup` with `hwsup : ∀ x, wf x ≤ wsup`, as throughout the layer; at `wsup := max wf` the constants are the paper's. ✓ **exactly** `Graph.maxOver G wf` in `training_speed_gd_exact` and `training_speed_full_complete` |
| `p_min` the smallest positive transition probability | ✓ `training_speed_gd_minPos` at `minPos B.phat`; `training_speed_gd` holds for every floor `0 < p_min ≤ 1` below the positive entries |
| `λ_min := min λ` | ✓ `Graph.minOver G lam` |
| `#𝒱` | ✓ `Fintype.card V` (in `BoundaryBlowup.uMin`) |
| `D(u)` the density of `∇^λ𝓛_{g,ν}(uλ)` | ⚠ `Flow.lossGrad`, a definition; its being the gradient is `theo:first_variation_full` (`FirstVariation.lean`), as in `TrainingSpeed.lean` |
| `μ₀ ∼ λ`, `u₀ = dμ₀/dλ` | ✓ `hu0 : ∀ x, 0 < uk 0 x` |
| `u_{k+1} := u_k − γD(u_k)` | ⚠ hypothesised of a given sequence, `hstep`; **inhabited** by `exists_descent_seq`. ✓ in `training_speed_gd_exact`: **no sequence hypothesised** — the sequence exists, and every sequence with `u_0 = u₀` and the recursion satisfies *(a)*–*(d)* |
| `0 < γ ≤ γ_*` | ✓ `hγ`, `hγs`, `γ_*` the printed formula (`gammaStar`); **satisfiable**, `gammaStar_pos`. ✓ in `training_speed_gd_exact` with the paper's quantifiers: `0 < γ_*` a conjunct, then `∀ γ, 0 < γ → γ ≤ γ_* → …` |
| `𝓛(μ₀)^{−1} := +∞` at a balanced start | ✓ in `γ_*` the middle entry `‖u₀‖²/(2𝓛(μ₀))` is `+∞` and dropped from the `min` when `𝓛(μ₀) = 0` (`gammaStar`'s `if`); *(b)* **as printed** in `training_speed_gd_minPos_ennreal`, read in `[0,∞]` where `0⁻¹ = ∞`, with `(𝓛(μ₀))⁻¹ = ∞ ↔` balanced — `global_phase_exact`'s reading of item *1*. The real display of `training_speed_gd_minPos` keeps `0⁻¹ = 0` and is the weaker form at a balanced start |
| `ε₀`, `γ₀` of `theo:local_convergence_full` at `a = 1/2`, `B̂_σ`, `C_∞ = λ_min^{−1/2}`, `Γ₃ = sup_{[1/2,3/2]}\|g'''\|` | ✓ `eps0At Gamma3Val …`, `gamma0At Gamma3Val …`, the printed formulas of `LocalConvergence.lean` at `Γ₃ = 48 + 32 ln 2`. ✓ that `48 + 32 ln 2` **is** `sup_{[1/2,3/2]}\|g'''\|`: `Gamma3_logSq_eq_Gamma3Val` (and `TrainingSpeedAssembled.Gamma3W_logSq`), with `eps0W_logSq_eq_eps0At`, `gamma0W_logSq_eq_gamma0At` identifying the radius and step cap with item *2*'s |
| `ϱ_σ = g''(1)w_min λ_min/σ_*²` | ✓ `rhoSigma 2 wmin λ_min σ_*`, from `rhoL` at `B̂_σ` by `rhoL_eq_rhoSigma` |
| "well defined" | ⚠ `lossGrad` is total in Lean; read as positivity of every iterate, `u_k ≥ u_min > 0` (*(a)* and `BoundaryBlowup.uMin_pos`) |
| "converges to a balanced flow" | ✓ `‖u_k − m_∞‖_{L²(λ)} → 0` and `Balanced B.phat lam (fun _ => m_∞)`; no measure-level statement |
| "Πu_k increases to some m_∞" | ✓ `Monotone` and `Tendsto … (nhds m_∞)` |
| "Every constant's dependence … runs through `σ_*`, `σ̄`, `N_min` alone, except that `u_min` and `γ_*` depend in addition on `p_min` and on `#𝒱`" | ⚠ not a separate conjunct; read off the explicit formulas. The graph and the backward policy enter every constant through `λ_min`, `B̂_σ` and `σ_*` only — `κ`, `M`, `ϱ_σ`, `k₀(γ)`, `ε₀`, `γ₀` are formulas (`kappa`, `ratioCap`, `rhoSigma`, `k0`, `eps0At`/`eps0W`, `gamma0At`/`gamma0W`) in `λ_min`, `B̂_σ`, `σ_*`, `w_min`, `‖w‖_{L^∞}`, `‖u₀‖`, `m₀`, `𝓛(μ₀)` — and `TrainingSpeed.minOver_lam_eq` gives `λ_min = N_min/(2+σ̄)`, `TrainingSpeed.BhatSigma_eq` gives `B̂_σ = σ_*/√λ_min`; so each is a function of `σ_*`, `σ̄`, `N_min`. `u_min` (`uMin`) takes in addition `p_min` (`minPos`) and `#𝒱` (`Fintype.card V`), and through `b₃` so does `γ_*` (`gammaStar`). Not stated as a congruence (kb 0028) |
| "No mixing, spectral-gap or aperiodicity hypothesis is used" | ✓ literally true of the signatures: the coercivity is `TrainingSpeed.hcoer_of_graph` |

## SCOPE (disclosed)

* **Finite state space**, as everywhere in `GFNBounds.Balance`; the paper's setting is finite.
* **`D` is `Flow.lossGrad`, a definition** — see the checklist; nothing here re-derives the first
  variation.
* **`‖w‖_{L^∞}` and `p_min` are parameters** (an upper bound, a floor) in `training_speed_gd` and
  `training_speed_gd_minPos` only; `training_speed_gd_minPos` pins `p_min` to the paper's value, and
  `training_speed_full_complete` pins both and hypothesises neither.
* **`Γ₃ = 48 + 32 ln 2` is identified with `sup|g'''|`**: `Gamma3_logSq_eq_Gamma3Val`,
  `gamma0W_logSq_eq_gamma0At`, `eps0W_logSq_eq_eps0At`. The Lean's Theorem 10 consumes a Taylor
  bound, which any `M₃ ≥ 24` supplies for `(log x)²` at `a = 1/2`; the paper's value is taken so
  that `ε₀` and `γ₀` are the paper's. (`TrainingSpeed.eps0Sq` is the same radius at `M₃ = 24`.)
* **The sequence and the flow are hypothesised in `training_speed_gd`/`_minPos` only** —
  `training_speed_full_complete` hypothesises neither — **and the sequence is shown to exist**
  (`exists_descent_seq`); the step bound is shown satisfiable (`training_speed_gd_inhabited`) and
  the whole hypothesis bundle inhabited from a non-balanced start on the five-vertex cycle
  (`cycle_training_speed_gd_nonvacuous`).
* **The balanced-start convention** — see the checklist row; *(b)* at `𝓛(μ₀) = 0` is
  `training_speed_gd_minPos_ennreal`, which carries the convention exactly, and `γ_*` at
  `𝓛(μ₀) = 0` is `gammaStar_ofReal`.
* **Item *3* with the paper's quantifiers, and the whole theorem** (`training_speed_gd_exact`,
  `training_speed_full_complete`, section `Complete`) add quantifier structure and nothing about the
  dynamics: every inequality is `training_speed_gd_minPos`'s or `training_speed_gd_minPos_ennreal`'s.
  `‖w‖_{L^∞}` is `Graph.maxOver G wf` exactly and `p_min` is `minPos`, so no parameter is left
  free. `D` stays `Flow.lossGrad`, and the flow of items *1*–*2* is `TrainingSpeedAssembled`'s,
  constructed, not hypothesised. The necessity clause picks one state `y` for all small `s`, which
  is slightly stronger than printed.
* **"Every constant's dependence runs through `σ_*`, `σ̄`, `N_min` alone"** is read off the formulas
  (checklist row), not stated as a separate conjunct.
* **`sorry`-free and axiom-clean**: `#print axioms` on `training_speed_gd`,
  `training_speed_gd_minPos`, `no_uniform_step_graph`, `descent_step`, `traj_a`, `traj_b`,
  `traj_c`, `traj_d`, `k0real_eq`, `training_speed_gd_inhabited` and
  `cycle_training_speed_gd_nonvacuous`, `training_speed_gd_minPos_ennreal`, `gammaStar_ofReal`,
  `training_speed_gd_exact`, `training_speed_full_complete` and
  `cycle_training_speed_complete_check` returns `[propext, Classical.choice, Quot.sound]`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance.DiscreteGlobal

open Finset GFNBounds.Balance

/-! ### Scalar calculus: a second-order Taylor bound, and the logarithm of a ratio of lines -/

/-- **Taylor's formula, one-sided**: `F(γ) ≤ F(0) + γF'(0) + Cγ²/2` when `F'' ≤ C` on `[0,γ]`. -/
theorem taylor_upper {F F' F'' : ℝ → ℝ} {γ C : ℝ} (hγ : 0 ≤ γ)
    (hF : ∀ s ∈ Set.Icc 0 γ, HasDerivAt F (F' s) s)
    (hF' : ∀ s ∈ Set.Icc 0 γ, HasDerivAt F' (F'' s) s)
    (hC : ∀ s ∈ Set.Icc 0 γ, F'' s ≤ C) :
    F γ ≤ F 0 + γ * F' 0 + C * γ ^ 2 / 2 := by
  have hA : ∀ s ∈ Set.Icc (0:ℝ) γ, F' s ≤ F' 0 + C * s := by
    intro s hs
    have hB : ∀ x : ℝ, HasDerivAt (fun s => F' 0 + C * s) C x := by
      intro x
      simpa using ((hasDerivAt_id x).const_mul C).const_add (F' 0)
    refine image_le_of_deriv_right_le_deriv_boundary (f := F') (f' := F'') (a := 0) (b := γ)
      (fun x hx => (hF' x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hF' x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (B := fun s => F' 0 + C * s) (B' := fun _ => C) (by simp)
      (fun x _ => (hB x).continuousAt.continuousWithinAt)
      (fun x _ => (hB x).hasDerivWithinAt) (fun x hx => hC x (Set.Ico_subset_Icc_self hx)) hs
  have hB : ∀ x : ℝ, HasDerivAt (fun s => F 0 + s * F' 0 + C * s ^ 2 / 2) (F' 0 + C * x) x := by
    intro x
    have h := (((hasDerivAt_id x).mul_const (F' 0)).const_add (F 0)).add
      (((hasDerivAt_pow 2 x).const_mul C).div_const 2)
    exact h.congr_deriv (by push_cast; ring)
  have := image_le_of_deriv_right_le_deriv_boundary (f := F) (f' := F') (a := 0) (b := γ)
      (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hF x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (B := fun s => F 0 + s * F' 0 + C * s ^ 2 / 2) (B' := fun s => F' 0 + C * s) (by simp)
      (fun x _ => (hB x).continuousAt.continuousWithinAt)
      (fun x _ => (hB x).hasDerivWithinAt) (fun x hx => hA x (Set.Ico_subset_Icc_self hx))
      ⟨hγ, le_rfl⟩
  simpa only [mul_comm γ] using this

/-- The line `t ↦ a − tb`. -/
theorem hasDerivAt_line (a b s : ℝ) : HasDerivAt (fun t => a - t * b) (-b) s := by
  simpa using ((hasDerivAt_id s).mul_const b).const_sub a

/-- `t ↦ b/(a − tb)` has derivative `(b/(a − sb))²`. -/
theorem hasDerivAt_div_line {a b s : ℝ} (h : a - s * b ≠ 0) :
    HasDerivAt (fun t => b / (a - t * b)) ((b / (a - s * b)) ^ 2) s := by
  have h1 := (hasDerivAt_const s b).div (hasDerivAt_line a b s) h
  exact h1.congr_deriv (by field_simp; ring)

/-- **`q(t) = (log(a − tb) − log(c − td))²`**, the per-state loss term along a line, and its
first derivative. -/
theorem hasDerivAt_sq_logdiff {a b c d s : ℝ} (ha : 0 < a - s * b) (hc : 0 < c - s * d) :
    HasDerivAt (fun t => (Real.log (a - t * b) - Real.log (c - t * d)) ^ 2)
      (2 * (Real.log (a - s * b) - Real.log (c - s * d)) * (d / (c - s * d) - b / (a - s * b)))
      s := by
  have h1 := (hasDerivAt_line a b s).log ha.ne'
  have h2 := (hasDerivAt_line c d s).log hc.ne'
  have h3 := (h1.sub h2).pow 2
  simp only [Pi.sub_apply] at h3
  exact h3.congr_deriv (by push_cast; ring)

/-- The second derivative of `q`. -/
theorem hasDerivAt_sq_logdiff_deriv {a b c d s : ℝ} (ha : 0 < a - s * b) (hc : 0 < c - s * d) :
    HasDerivAt
      (fun t => 2 * (Real.log (a - t * b) - Real.log (c - t * d))
        * (d / (c - t * d) - b / (a - t * b)))
      (2 * (d / (c - s * d) - b / (a - s * b)) ^ 2
        + 2 * (Real.log (a - s * b) - Real.log (c - s * d))
          * ((d / (c - s * d)) ^ 2 - (b / (a - s * b)) ^ 2)) s := by
  have h1 := (hasDerivAt_line a b s).log ha.ne'
  have h2 := (hasDerivAt_line c d s).log hc.ne'
  have h3 := ((h1.sub h2).const_mul 2).mul
    ((hasDerivAt_div_line hc.ne').sub (hasDerivAt_div_line ha.ne'))
  simp only [Pi.sub_apply] at h3
  refine h3.congr_deriv ?_
  have hA : a - s * b ≠ 0 := ha.ne'
  have hC : c - s * d ≠ 0 := hc.ne'
  rw [neg_div, neg_div]
  ring

/-- `q'' ≤ (4 + 2|ℓ|)(τ² + ρ²)`. -/
theorem sq_logdiff_deriv2_le (l τ ρ : ℝ) :
    2 * (τ - ρ) ^ 2 + 2 * l * (τ ^ 2 - ρ ^ 2) ≤ (4 + 2 * |l|) * (τ ^ 2 + ρ ^ 2) := by
  have h1 : 2 * (τ - ρ) ^ 2 ≤ 4 * (τ ^ 2 + ρ ^ 2) := by nlinarith [sq_nonneg (τ + ρ)]
  have h2 : 2 * l * (τ ^ 2 - ρ ^ 2) ≤ 2 * |l| * (τ ^ 2 + ρ ^ 2) := by
    rcases abs_cases l with ⟨hl, _⟩ | ⟨hl, _⟩ <;> rw [hl] <;>
      nlinarith [sq_nonneg τ, sq_nonneg ρ, abs_nonneg l]
  nlinarith

/-! ### The step-size constants of the descent lemma -/

/-- **`M' := M + ln 3`** (`proofs.tex:1048`). -/
noncomputable def Mp (M : ℝ) : ℝ := M + Real.log 3

/-- **`b₁ := 2M'e^{M'}`** (`proofs.tex:1048`), the bound on `|g'|` on `[e^{−M'}, e^{M'}]`. -/
noncomputable def b1 (M : ℝ) : ℝ := 2 * Mp M * Real.exp (Mp M)

/-- **`b₂ := 2(1+M')e^{2M'}`** (`proofs.tex:1048`), the bound on `|g''|` on `[e^{−M'}, e^{M'}]`. -/
noncomputable def b2 (M : ℝ) : ℝ := 2 * (1 + Mp M) * Real.exp (2 * Mp M)

/-- **`b₃ := (4‖w‖_{L^∞}/u_min²)(1+e^{M'})(b₂(1+e^{M'}) + 2b₁)`** (`proofs.tex:1050`). -/
noncomputable def b3 (W umin M : ℝ) : ℝ :=
  4 * W / umin ^ 2 * (1 + Real.exp (Mp M)) * (b2 M * (1 + Real.exp (Mp M)) + 2 * b1 M)

theorem exp_Mp (M : ℝ) : Real.exp (Mp M) = 3 * Real.exp M := by
  rw [Mp, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 3)]; ring

theorem exp_two_Mp (M : ℝ) : Real.exp (2 * Mp M) = 9 * Real.exp M ^ 2 := by
  rw [show 2 * Mp M = Mp M + Mp M by ring, Real.exp_add, exp_Mp]; ring

theorem Mp_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ Mp M := by
  have : 0 < Real.log 3 := Real.log_pos (by norm_num)
  simp only [Mp]; linarith

/-- The bracket of `b₃`, in `E = e^M`. -/
theorem b3_bracket_eq (M : ℝ) :
    (1 + Real.exp (Mp M)) * (b2 M * (1 + Real.exp (Mp M)) + 2 * b1 M)
      = (1 + 3 * Real.exp M) * (18 * (1 + Mp M) * Real.exp M ^ 2 * (1 + 3 * Real.exp M)
          + 12 * Mp M * Real.exp M) := by
  rw [b2, b1, exp_Mp, exp_two_Mp]; ring

/-- The three lower bounds on the bracket of `b₃` the proof spends: the relative step
(`M(e^M+1)`), the second derivative (`(4 + 2M')(1 + e^{2M})`, the form this file's `f''` bound
takes), and `8` (for `γ ≤ u_min²/(32‖w‖_{L^∞})`). -/
theorem b3_bracket_ge {M : ℝ} (hM : 0 ≤ M) :
    M * (Real.exp M + 1) ≤ (1 + Real.exp (Mp M)) * (b2 M * (1 + Real.exp (Mp M)) + 2 * b1 M)
      ∧ (4 + 2 * Mp M) * (1 + Real.exp M ^ 2)
          ≤ (1 + Real.exp (Mp M)) * (b2 M * (1 + Real.exp (Mp M)) + 2 * b1 M)
      ∧ 8 ≤ (1 + Real.exp (Mp M)) * (b2 M * (1 + Real.exp (Mp M)) + 2 * b1 M) := by
  rw [b3_bracket_eq]
  have hE : 1 ≤ Real.exp M := Real.one_le_exp hM
  have hMp : M ≤ Mp M := by
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    simp only [Mp]; linarith
  have hMp0 : 0 ≤ Mp M := Mp_nonneg hM
  set E := Real.exp M
  set m := Mp M
  have hE2 : 1 ≤ E ^ 2 := by nlinarith
  have hA : 0 ≤ 18 * (1 + m) * E ^ 2 * (1 + 3 * E) := by positivity
  have hB : 0 ≤ 12 * m * E := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h1 : M * (E + 1) ≤ m * (2 * E) := by nlinarith
    have h2 : m * (2 * E) ≤ (1 + 3 * E) * (12 * m * E) := by nlinarith
    nlinarith
  · have h1 : (4 + 2 * m) * (1 + E ^ 2) ≤ 18 * (1 + m) * (2 * E ^ 2) := by nlinarith
    have h2 : 18 * (1 + m) * (2 * E ^ 2) ≤ (1 + 3 * E) * (18 * (1 + m) * E ^ 2 * (1 + 3 * E)) := by
      have h3 : (2:ℝ) ≤ (1 + 3 * E) * (1 + 3 * E) := by nlinarith
      have h4 : 0 ≤ 18 * (1 + m) * E ^ 2 := by positivity
      nlinarith
    nlinarith
  · have h1 : (4:ℝ) ≤ 1 + 3 * E := by linarith
    have h2 : (18:ℝ) ≤ 18 * (1 + m) * E ^ 2 := by nlinarith
    nlinarith

/-! ### Algebra of a descent line `s ↦ u − sv` -/

section Line

variable {V : Type*} [Fintype V]

theorem pushMass_line (K : V → V → ℝ) (lam u v : V → ℝ) (s : ℝ) (y : V) :
    pushMass K lam (fun x => u x - s * v x) y = pushMass K lam u y - s * pushMass K lam v y := by
  simp only [pushMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem ratio_line (K : V → V → ℝ) (lam u v : V → ℝ) (s : ℝ) (y : V) :
    ratio K lam (fun x => u x - s * v x) y
      = (pushMass K lam u y - s * pushMass K lam v y) / (lam y * u y - s * (lam y * v y)) := by
  simp only [ratio, pushMass_line]
  congr 1; ring

theorem pushMass_eq_densAct {K : V → V → ℝ} {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    (v : V → ℝ) (y : V) : pushMass K lam v y = lam y * Core.densAct lam K v y := by
  rw [Core.densAct_apply, mul_div_cancel₀ _ (hlam y).ne']
  exact Finset.sum_congr rfl fun x _ => by ring

theorem logSq_div_eq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logSq (p / q) = (Real.log p - Real.log q) ^ 2 := by
  rw [logSq, Real.log_div hp.ne' hq.ne']

/-- `e^{−M} ≤ r ≤ e^M` from `|log r| ≤ M`. -/
theorem exp_neg_le_of_abs_log_le {r M : ℝ} (hr : 0 < r) (h : |Real.log r| ≤ M) :
    Real.exp (-M) ≤ r ∧ r ≤ Real.exp M := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor
  · calc Real.exp (-M) ≤ Real.exp (Real.log r) := Real.exp_le_exp.mpr h1
      _ = r := Real.exp_log hr
  · calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ ≤ Real.exp M := Real.exp_le_exp.mpr h2

end Line

/-! ### The relative step: `γ|D(u)| ≤ u/2` -/

section RelStep

variable {V : Type*} [Fintype V]

/-- **`|D(u)| ≤ 2M‖w‖_{L^∞}(e^M+1)u/u_min²`**: `|P†ψ| ≤ max|ψ| ≤
2M‖w‖e^M/u_min` and `|rψ| ≤ 2M‖w‖/u`, read against `u ≥ u_min` (`proofs.tex:1062`). -/
theorem abs_lossGrad_le {K : V → V → ℝ} {lam wf u : V → ℝ} {W M umin : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (hw0 : ∀ x, 0 ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu : ∀ x, 0 < u x) (humin0 : 0 < umin) (humin : ∀ x, umin ≤ u x) (hM0 : 0 ≤ M)
    (hlog : ∀ x, |Real.log (ratio K lam u x)| ≤ M) (x : V) :
    |lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x|
      ≤ 2 * M * W * (Real.exp M + 1) * u x / umin ^ 2 := by
  have hr : ∀ y, 0 < ratio K lam u y := ratio_pos hinv hKnn hlam hu
  have hW0 : 0 ≤ W := le_trans (hw0 x) (hW x)
  have hE0 : 0 < Real.exp M := Real.exp_pos M
  set φ : V → ℝ := fun y => logSqDeriv (ratio K lam u y) * (wf y / u y) with hφdef
  have hD : lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x
      = funAct K φ x - ratio K lam u x * φ x := by
    rw [lossGrad_of_weight hlam]; rfl
  have hwu : ∀ y, 0 ≤ wf y / u y ∧ wf y / u y ≤ W / umin := by
    intro y
    refine ⟨div_nonneg (hw0 y) (hu y).le, ?_⟩
    calc wf y / u y ≤ W / u y := div_le_div_of_nonneg_right (hW y) (hu y).le
      _ ≤ W / umin := div_le_div_of_nonneg_left hW0 humin0 (humin y)
  have hφ : ∀ y, |φ y| ≤ 2 * M * Real.exp M * (W / umin) := by
    intro y
    obtain ⟨hlo, -⟩ := exp_neg_le_of_abs_log_le (hr y) (hlog y)
    have hinvr : 1 / ratio K lam u y ≤ Real.exp M := by
      rw [div_le_iff₀ (hr y)]
      calc (1:ℝ) = Real.exp M * Real.exp (-M) := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp M * ratio K lam u y := mul_le_mul_of_nonneg_left hlo hE0.le
    have hg : |logSqDeriv (ratio K lam u y)| ≤ 2 * M * Real.exp M := by
      rw [logSqDeriv, abs_div, abs_mul, abs_of_pos (hr y)]
      rw [div_eq_mul_one_div]
      have h2 : |(2:ℝ)| * |Real.log (ratio K lam u y)| ≤ 2 * M := by
        rw [abs_two]; linarith [hlog y]
      calc |(2:ℝ)| * |Real.log (ratio K lam u y)| * (1 / ratio K lam u y)
          ≤ (2 * M) * Real.exp M :=
            mul_le_mul h2 hinvr (div_nonneg zero_le_one (hr y).le) (by linarith)
        _ = 2 * M * Real.exp M := by ring
    simp only [hφdef]
    rw [abs_mul, abs_of_nonneg (hwu y).1]
    exact mul_le_mul hg (hwu y).2 (hwu y).1 (mul_nonneg (by linarith) hE0.le)
  have hQ : |funAct K φ x| ≤ 2 * M * Real.exp M * (W / umin) := by
    simp only [funAct]
    calc |∑ y, K x y * φ y| ≤ ∑ y, |K x y * φ y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, K x y * |φ y| := Finset.sum_congr rfl fun y _ => by
          rw [abs_mul, abs_of_nonneg (hKnn x y)]
      _ ≤ ∑ y, K x y * (2 * M * Real.exp M * (W / umin)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hφ y) (hKnn x y)
      _ = 2 * M * Real.exp M * (W / umin) := by rw [← Finset.sum_mul, hrow x, one_mul]
  have hR : |ratio K lam u x * φ x| ≤ 2 * M * (W / u x) := by
    have heq : ratio K lam u x * φ x = 2 * Real.log (ratio K lam u x) * (wf x / u x) := by
      simp only [hφdef, logSqDeriv]
      field_simp [(hr x).ne']
    rw [heq, abs_mul, abs_mul, abs_two, abs_of_nonneg (hwu x).1]
    have hwux : wf x / u x ≤ W / u x := div_le_div_of_nonneg_right (hW x) (hu x).le
    have h2 : 2 * |Real.log (ratio K lam u x)| ≤ 2 * M := by linarith [hlog x]
    exact mul_le_mul h2 hwux (hwu x).1 (by linarith)
  rw [hD]
  have hux := hu x
  have humx := humin x
  have hsum : |funAct K φ x - ratio K lam u x * φ x|
      ≤ 2 * M * Real.exp M * (W / umin) + 2 * M * (W / u x) :=
    le_trans (abs_sub _ _) (add_le_add hQ hR)
  refine le_trans hsum ?_
  have k1 : W / umin ≤ W * u x / umin ^ 2 := by
    rw [div_le_div_iff₀ humin0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left humx (mul_nonneg hW0 humin0.le)]
  have k2 : W / u x ≤ W * u x / umin ^ 2 :=
    le_trans (div_le_div_of_nonneg_left hW0 humin0 humx) k1
  have e1 := mul_le_mul_of_nonneg_left k1 (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * M) hE0.le)
  have e2 := mul_le_mul_of_nonneg_left k2 (by linarith : (0:ℝ) ≤ 2 * M)
  calc 2 * M * Real.exp M * (W / umin) + 2 * M * (W / u x)
      ≤ 2 * M * Real.exp M * (W * u x / umin ^ 2) + 2 * M * (W * u x / umin ^ 2) :=
        add_le_add e1 e2
    _ = 2 * M * W * (Real.exp M + 1) * u x / umin ^ 2 := by ring

/-- **`γ|D(u)| ≤ u/2`** (`proofs.tex:1062`) at `γ ≤ 1/b₃`. -/
theorem rel_step_le {K : V → V → ℝ} {lam wf u : V → ℝ} {W M umin γ : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (hw0 : ∀ x, 0 ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu : ∀ x, 0 < u x) (humin0 : 0 < umin) (humin : ∀ x, umin ≤ u x) (hM0 : 0 ≤ M)
    (hlog : ∀ x, |Real.log (ratio K lam u x)| ≤ M) (hγ0 : 0 ≤ γ) (hγ : γ * b3 W umin M ≤ 1)
    (x : V) : γ * |lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x| ≤ u x / 2 := by
  have hW0 : 0 ≤ W := le_trans (hw0 x) (hW x)
  have hbr := (b3_bracket_ge hM0).1
  have hux := hu x
  have hb3 : 4 * W * (M * (Real.exp M + 1)) / umin ^ 2 ≤ b3 W umin M := by
    rw [b3, mul_assoc (4 * W / umin ^ 2), div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    exact mul_le_mul_of_nonneg_left hbr (by positivity)
  have h1 := mul_le_mul_of_nonneg_left
    (abs_lossGrad_le hKnn hrow hinv hlam hw0 hW hu humin0 humin hM0 hlog x) hγ0
  have h2 : γ * (4 * W * (M * (Real.exp M + 1)) / umin ^ 2) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hb3 hγ0) hγ
  have h3 : γ * (2 * M * W * (Real.exp M + 1) * u x / umin ^ 2)
      = γ * (4 * W * (M * (Real.exp M + 1)) / umin ^ 2) * (u x / 2) := by ring
  nlinarith

end RelStep

/-! ### The descent lemma -/

section Descent

variable {V : Type*} [Fintype V]

theorem pushMass_mono {K : V → V → ℝ} {lam v v' : V → ℝ} (hKnn : ∀ x y, 0 ≤ K x y)
    (hlam : ∀ x, 0 ≤ lam x) (h : ∀ x, v x ≤ v' x) (y : V) :
    pushMass K lam v y ≤ pushMass K lam v' y :=
  Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h x) (hlam x)) (hKnn x y)

theorem pushMass_smul (K : V → V → ℝ) (lam u : V → ℝ) (c : ℝ) (y : V) :
    pushMass K lam (fun x => c * u x) y = c * pushMass K lam u y := by
  simp only [pushMass, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `|log(a − sb) − log(c − sd)| ≤ |log(a/c)| + ln 3` when both lines stay within a factor two
of `a` and `c`: the ratio moves by at most a factor `3` along the segment (`proofs.tex:1062`). -/
theorem abs_logdiff_le {a a' c c' : ℝ} (ha : 0 < a) (hc : 0 < c)
    (ha1 : a / 2 ≤ a') (ha2 : a' ≤ 3 * a / 2) (hc1 : c / 2 ≤ c') (hc2 : c' ≤ 3 * c / 2) :
    |Real.log a' - Real.log c'| ≤ |Real.log (a / c)| + Real.log 3 := by
  have ha' : 0 < a' := lt_of_lt_of_le (by linarith) ha1
  have hc' : 0 < c' := lt_of_lt_of_le (by linarith) hc1
  have l1 : Real.log a' ≤ Real.log a + Real.log (3 / 2) := by
    rw [← Real.log_mul ha.ne' (by norm_num)]
    exact Real.log_le_log ha' (by linarith)
  have l2 : Real.log a - Real.log 2 ≤ Real.log a' := by
    rw [← Real.log_div ha.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have l3 : Real.log c' ≤ Real.log c + Real.log (3 / 2) := by
    rw [← Real.log_mul hc.ne' (by norm_num)]
    exact Real.log_le_log hc' (by linarith)
  have l4 : Real.log c - Real.log 2 ≤ Real.log c' := by
    rw [← Real.log_div hc.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have l5 : Real.log 3 = Real.log (3 / 2) + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l6 : Real.log (a / c) = Real.log a - Real.log c := Real.log_div ha.ne' hc.ne'
  rw [abs_le]
  have := abs_nonneg (Real.log (a / c))
  have := le_abs_self (Real.log (a / c))
  have := neg_abs_le (Real.log (a / c))
  constructor <;> linarith

/-- **`theo:training_speed_full`*(3)*, the descent lemma** (`proofs.tex:1062–1066`): on a positive density whose ratio is within
`e^{±M}` of `1` and which is at least `u_min`, one step `u⁺ = u − γD(u)` with `0 ≤ γ ≤ 1/b₃`
satisfies `u⁺ ≥ u/2` and `𝓛(u⁺) ≤ 𝓛(u) − (γ/2)‖D(u)‖²`.

The second derivative of `s ↦ 𝓛(u − sD)` is computed state by state through
`log r_s = log(μ_sT) − log(λu_s)`, two logarithms of lines, rather than through `g''(r_s)` and
`r_s''` as the paper does; the bound it gives, `‖w‖(4 + 2M')(4/u_min²)(1 + e^{2M})‖D‖²`, is at
most the paper's `b₃‖D‖²` (`b3_bracket_ge`), so the paper's `b₃` is the step bound used. -/
theorem descent_step {K : V → V → ℝ} {lam wf u : V → ℝ} {W M umin γ : ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (hw0 : ∀ x, 0 ≤ wf x) (hW : ∀ x, wf x ≤ W) (hW0 : 0 ≤ W)
    (hu : ∀ x, 0 < u x) (humin0 : 0 < umin) (humin : ∀ x, umin ≤ u x) (hM0 : 0 ≤ M)
    (hlog : ∀ x, |Real.log (ratio K lam u x)| ≤ M) (hγ0 : 0 ≤ γ) (hγ : γ * b3 W umin M ≤ 1) :
    (∀ x, u x / 2 ≤ u x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x)
      ∧ lossVal lam wf logSq
          (ratio K lam (fun x => u x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x))
        ≤ lossVal lam wf logSq (ratio K lam u)
          - γ / 2 * Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv u) ^ 2 := by
  classical
  have hKnn : ∀ x y, 0 ≤ K x y := hKM.nonneg
  have hrow : ∀ x, ∑ y, K x y = 1 := hKM.row_sum
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hr : ∀ y, 0 < ratio K lam u y := ratio_pos hinv hKnn hlam hu
  set D := lossGrad K lam (fun z => lam z * wf z) logSqDeriv u with hDdef
  set E := Real.exp M with hEdef
  have hE0 : 0 < E := Real.exp_pos M
  have hrel : ∀ x, γ * |D x| ≤ u x / 2 :=
    rel_step_le hKnn hrow hinv hlam hw0 hW hu humin0 humin hM0 hlog hγ0 hγ
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) γ, ∀ x, u x / 2 ≤ u x - s * D x ∧ u x - s * D x ≤ 3 * u x / 2 := by
    intro s hs x
    have h1 : |s * D x| ≤ u x / 2 := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact le_trans (mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)) (hrel x)
    obtain ⟨h2, h3⟩ := abs_le.mp h1
    constructor <;> linarith
  -- the four lines
  set a : V → ℝ := fun y => pushMass K lam u y with hadef
  set b : V → ℝ := fun y => pushMass K lam D y with hbdef
  set c : V → ℝ := fun y => lam y * u y with hcdef
  set d : V → ℝ := fun y => lam y * D y with hddef
  have hcpos : ∀ y, 0 < c y := fun y => mul_pos (hlam y) (hu y)
  have hra : ∀ y, a y = ratio K lam u y * c y := by
    intro y; simp only [hadef, hcdef, ratio]; rw [div_mul_cancel₀ _ (hcpos y).ne']
  have hapos : ∀ y, 0 < a y := fun y => by rw [hra y]; exact mul_pos (hr y) (hcpos y)
  have hlines : ∀ s ∈ Set.Icc (0:ℝ) γ, ∀ y,
      (a y / 2 ≤ a y - s * b y ∧ a y - s * b y ≤ 3 * a y / 2)
        ∧ (c y / 2 ≤ c y - s * d y ∧ c y - s * d y ≤ 3 * c y / 2) := by
    intro s hs y
    have hpl : a y - s * b y = pushMass K lam (fun x => u x - s * D x) y :=
      (pushMass_line K lam u D s y).symm
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hpl, show a y / 2 = pushMass K lam (fun x => (1/2) * u x) y by
        rw [pushMass_smul]; simp only [hadef]; ring]
      exact pushMass_mono hKnn hnn (fun x => by linarith [(hseg s hs x).1]) y
    · rw [hpl, show 3 * a y / 2 = pushMass K lam (fun x => (3/2) * u x) y by
        rw [pushMass_smul]; simp only [hadef]; ring]
      exact pushMass_mono hKnn hnn (fun x => by linarith [(hseg s hs x).2]) y
    · have := mul_le_mul_of_nonneg_left (hseg s hs y).1 (hnn y)
      simp only [hcdef, hddef]; nlinarith
    · have := mul_le_mul_of_nonneg_left (hseg s hs y).2 (hnn y)
      simp only [hcdef, hddef]; nlinarith
  have hApos : ∀ s ∈ Set.Icc (0:ℝ) γ, ∀ y, 0 < a y - s * b y := fun s hs y =>
    lt_of_lt_of_le (by linarith [hapos y]) (hlines s hs y).1.1
  have hCpos : ∀ s ∈ Set.Icc (0:ℝ) γ, ∀ y, 0 < c y - s * d y := fun s hs y =>
    lt_of_lt_of_le (by linarith [hcpos y]) (hlines s hs y).2.1
  -- the loss along the line, and its explicit form
  set Φ : ℝ → ℝ := fun s => ∑ y, lam y * (wf y *
    (Real.log (a y - s * b y) - Real.log (c y - s * d y)) ^ 2) with hΦdef
  set Φ1 : ℝ → ℝ := fun s => ∑ y, lam y * (wf y *
    (2 * (Real.log (a y - s * b y) - Real.log (c y - s * d y))
      * (d y / (c y - s * d y) - b y / (a y - s * b y)))) with hΦ1def
  set Φ2 : ℝ → ℝ := fun s => ∑ y, lam y * (wf y *
    (2 * (d y / (c y - s * d y) - b y / (a y - s * b y)) ^ 2
      + 2 * (Real.log (a y - s * b y) - Real.log (c y - s * d y))
        * ((d y / (c y - s * d y)) ^ 2 - (b y / (a y - s * b y)) ^ 2))) with hΦ2def
  have hΦ : ∀ s ∈ Set.Icc (0:ℝ) γ, HasDerivAt Φ (Φ1 s) s := by
    intro s hs
    exact HasDerivAt.fun_sum (u := Finset.univ) fun y _ =>
      ((hasDerivAt_sq_logdiff (hApos s hs y) (hCpos s hs y)).const_mul (wf y)).const_mul (lam y)
  have hΦ1 : ∀ s ∈ Set.Icc (0:ℝ) γ, HasDerivAt Φ1 (Φ2 s) s := by
    intro s hs
    exact HasDerivAt.fun_sum (u := Finset.univ) fun y _ =>
      ((hasDerivAt_sq_logdiff_deriv (hApos s hs y) (hCpos s hs y)).const_mul (wf y)).const_mul
        (lam y)
  -- the second-derivative bound
  set Cst : ℝ := W * (4 + 2 * Mp M) * (4 / umin ^ 2) * (1 + E ^ 2)
    * Graph.nrmL2 lam D ^ 2 with hCstdef
  have hΦ2 : ∀ s ∈ Set.Icc (0:ℝ) γ, Φ2 s ≤ Cst := by
    intro s hs
    have hterm : ∀ y, lam y * (wf y *
        (2 * (d y / (c y - s * d y) - b y / (a y - s * b y)) ^ 2
          + 2 * (Real.log (a y - s * b y) - Real.log (c y - s * d y))
            * ((d y / (c y - s * d y)) ^ 2 - (b y / (a y - s * b y)) ^ 2)))
        ≤ W * (4 + 2 * Mp M) * (4 / umin ^ 2)
          * (lam y * (D y * D y) + E ^ 2 * (lam y * (Core.densAct lam K D y
              * Core.densAct lam K D y))) := by
      intro y
      obtain ⟨⟨ha1, ha2⟩, ⟨hc1, hc2⟩⟩ := hlines s hs y
      have hl : |Real.log (a y - s * b y) - Real.log (c y - s * d y)| ≤ Mp M := by
        have := abs_logdiff_le (hapos y) (hcpos y) ha1 ha2 hc1 hc2
        have hlr : Real.log (a y / c y) = Real.log (ratio K lam u y) := by
          rw [hra y, mul_div_cancel_right₀ _ (hcpos y).ne']
        rw [hlr] at this
        simp only [Mp]; linarith [hlog y]
      set τ := d y / (c y - s * d y) with hτ
      set ρ := b y / (a y - s * b y) with hρ
      have hq := sq_logdiff_deriv2_le (Real.log (a y - s * b y) - Real.log (c y - s * d y)) τ ρ
      have hq' : 2 * (τ - ρ) ^ 2 + 2 * (Real.log (a y - s * b y) - Real.log (c y - s * d y))
            * (τ ^ 2 - ρ ^ 2) ≤ (4 + 2 * Mp M) * (τ ^ 2 + ρ ^ 2) :=
        le_trans hq (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      -- `τ = D/u_s`
      have hus : umin / 2 ≤ u y - s * D y := by linarith [(hseg s hs y).1, humin y]
      have hτeq : τ = D y / (u y - s * D y) := by
        simp only [hτ, hddef, hcdef]
        rw [show lam y * u y - s * (lam y * D y) = lam y * (u y - s * D y) by ring,
          mul_div_mul_left _ _ (hlam y).ne']
      have hτ2 : τ ^ 2 ≤ 4 / umin ^ 2 * (D y * D y) := by
        have hus0 : 0 < u y - s * D y := lt_of_lt_of_le (by linarith) hus
        have hq4 : 0 < umin ^ 2 / 4 := by positivity
        have hsq : umin ^ 2 / 4 ≤ (u y - s * D y) ^ 2 := by nlinarith
        rw [hτeq, div_pow]
        calc D y ^ 2 / (u y - s * D y) ^ 2 ≤ D y ^ 2 / (umin ^ 2 / 4) :=
              div_le_div_of_nonneg_left (sq_nonneg _) hq4 hsq
          _ = 4 / umin ^ 2 * (D y * D y) := by field_simp
      -- `ρ = (PD)/(Pu_s)`
      have hbP : b y = lam y * Core.densAct lam K D y := pushMass_eq_densAct hlam D y
      have halow : lam y * umin * Real.exp (-M) ≤ a y := by
        rw [hra y]
        obtain ⟨hlo, -⟩ := exp_neg_le_of_abs_log_le (hr y) (hlog y)
        have h1 : lam y * umin ≤ c y := mul_le_mul_of_nonneg_left (humin y) (hnn y)
        calc lam y * umin * Real.exp (-M) = Real.exp (-M) * (lam y * umin) := by ring
          _ ≤ ratio K lam u y * c y :=
            mul_le_mul hlo h1 (mul_nonneg (hnn y) humin0.le) (hr y).le
      have hρ2 : ρ ^ 2 ≤ 4 / umin ^ 2 * E ^ 2 * (Core.densAct lam K D y * Core.densAct lam K D y) := by
        have hAs : lam y * umin * Real.exp (-M) / 2 ≤ a y - s * b y := by linarith
        have hden : 0 < lam y * umin * Real.exp (-M) / 2 :=
          div_pos (mul_pos (mul_pos (hlam y) humin0) (Real.exp_pos _)) two_pos
        have hsq : (lam y * umin * Real.exp (-M) / 2) ^ 2 ≤ (a y - s * b y) ^ 2 :=
          pow_le_pow_left₀ hden.le hAs 2
        have hEE : E * Real.exp (-M) = 1 := by rw [hEdef, ← Real.exp_add]; simp
        rw [hρ, div_pow, div_le_iff₀ (lt_of_lt_of_le (by positivity) hsq)]
        calc b y ^ 2 = (E * Real.exp (-M)) ^ 2 * (lam y * Core.densAct lam K D y) ^ 2 := by
              rw [hEE, hbP]; ring
          _ = 4 / umin ^ 2 * E ^ 2 * (Core.densAct lam K D y * Core.densAct lam K D y)
                * (lam y * umin * Real.exp (-M) / 2) ^ 2 := by
              field_simp; ring
          _ ≤ 4 / umin ^ 2 * E ^ 2 * (Core.densAct lam K D y * Core.densAct lam K D y)
                * (a y - s * b y) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by
                have := mul_self_nonneg (Core.densAct lam K D y); positivity)
      have hbr : 2 * (τ - ρ) ^ 2 + 2 * (Real.log (a y - s * b y) - Real.log (c y - s * d y))
            * (τ ^ 2 - ρ ^ 2)
          ≤ (4 + 2 * Mp M) * (4 / umin ^ 2 * (D y * D y)
              + 4 / umin ^ 2 * E ^ 2 * (Core.densAct lam K D y * Core.densAct lam K D y)) :=
        le_trans hq' (mul_le_mul_of_nonneg_left (add_le_add hτ2 hρ2)
          (by linarith [Mp_nonneg hM0]))
      have hX : 0 ≤ (4 + 2 * Mp M) * (4 / umin ^ 2 * (D y * D y)
              + 4 / umin ^ 2 * E ^ 2 * (Core.densAct lam K D y * Core.densAct lam K D y)) := by
        have := Mp_nonneg hM0
        have := mul_self_nonneg (D y)
        have := mul_self_nonneg (Core.densAct lam K D y)
        positivity
      have hwq : wf y * (2 * (τ - ρ) ^ 2 + 2 * (Real.log (a y - s * b y) - Real.log (c y - s * d y))
            * (τ ^ 2 - ρ ^ 2))
          ≤ W * ((4 + 2 * Mp M) * (4 / umin ^ 2 * (D y * D y)
              + 4 / umin ^ 2 * E ^ 2 * (Core.densAct lam K D y * Core.densAct lam K D y))) :=
        le_trans (mul_le_mul_of_nonneg_left hbr (hw0 y)) (mul_le_mul_of_nonneg_right (hW y) hX)
      calc _ ≤ lam y * (W * ((4 + 2 * Mp M) * (4 / umin ^ 2 * (D y * D y)
              + 4 / umin ^ 2 * E ^ 2 * (Core.densAct lam K D y * Core.densAct lam K D y)))) :=
            mul_le_mul_of_nonneg_left hwq (hnn y)
        _ = _ := by ring
    have hPD : Graph.nrmL2 lam (Core.densAct lam K D) ^ 2 ≤ Graph.nrmL2 lam D ^ 2 :=
      pow_le_pow_left₀ (Graph.nrmL2_nonneg _ _) (Core.nrmL2_densAct_le hKM ⟨hnn, hinv⟩ D) 2
    calc Φ2 s ≤ ∑ y, W * (4 + 2 * Mp M) * (4 / umin ^ 2)
          * (lam y * (D y * D y) + E ^ 2 * (lam y * (Core.densAct lam K D y
              * Core.densAct lam K D y))) := Finset.sum_le_sum fun y _ => hterm y
      _ = W * (4 + 2 * Mp M) * (4 / umin ^ 2)
          * (Graph.nrmL2 lam D ^ 2 + E ^ 2 * Graph.nrmL2 lam (Core.densAct lam K D) ^ 2) := by
        rw [Graph.sq_nrmL2 hnn, Graph.sq_nrmL2 hnn]
        simp only [Graph.ipL2, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ Cst := by
        rw [hCstdef]
        have hc : 0 ≤ W * (4 + 2 * Mp M) * (4 / umin ^ 2) := by
          have := Mp_nonneg hM0; positivity
        have := mul_le_mul_of_nonneg_left hPD (sq_nonneg E)
        nlinarith
  -- Taylor, and the first derivative at `0`
  have hTaylor := taylor_upper hγ0 hΦ hΦ1 hΦ2
  have hfΦ : ∀ s : ℝ, (∀ y, 0 < a y - s * b y) → (∀ y, 0 < c y - s * d y) →
      lossVal lam wf logSq (ratio K lam (fun x => u x - s * D x)) = Φ s := by
    intro s hA hC
    simp only [lossVal, hΦdef]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ratio_line]
    exact congrArg (fun t => lam y * (wf y * t)) (logSq_div_eq (hA y) (hC y))
  have hderiv : HasDerivAt (fun s : ℝ => lossVal lam wf logSq (ratio K lam (fun x => u x - s * D x)))
      (-(Graph.nrmL2 lam D ^ 2)) 0 := by
    have h := hasDerivAt_loss_flow_line (nu := fun z => lam z * wf z) (g := logSq)
      (gd := logSqDeriv) hinv hKnn hlam hu (fun y hy => hasDerivAt_logSq hy)
    simpa only [loss_eq_lossVal] using h
  have hev : Φ =ᶠ[nhds 0] fun s : ℝ => lossVal lam wf logSq (ratio K lam (fun x => u x - s * D x)) := by
    have h1 : ∀ᶠ s in nhds (0:ℝ), ∀ y, 0 < a y - s * b y ∧ 0 < c y - s * d y := by
      rw [Filter.eventually_all]
      intro y
      have hA : ContinuousAt (fun s : ℝ => a y - s * b y) 0 := by fun_prop
      have hC : ContinuousAt (fun s : ℝ => c y - s * d y) 0 := by fun_prop
      exact (continuousAt_const.eventually_lt hA (by simpa using hapos y)).and
        (continuousAt_const.eventually_lt hC (by simpa using hcpos y))
    filter_upwards [h1] with s hs
    exact (hfΦ s (fun y => (hs y).1) (fun y => (hs y).2)).symm
  have hΦ0 : HasDerivAt Φ (-(Graph.nrmL2 lam D ^ 2)) 0 := hderiv.congr_of_eventuallyEq hev
  have hΦ10 : Φ1 0 = -(Graph.nrmL2 lam D ^ 2) := (hΦ 0 ⟨le_rfl, hγ0⟩).unique hΦ0
  have hmem0 : (0:ℝ) ∈ Set.Icc (0:ℝ) γ := ⟨le_rfl, hγ0⟩
  have hmemγ : γ ∈ Set.Icc (0:ℝ) γ := ⟨hγ0, le_rfl⟩
  have hf0 : lossVal lam wf logSq (ratio K lam (fun x => u x - 0 * D x))
      = lossVal lam wf logSq (ratio K lam u) := by
    congr 2; funext x; ring
  have hCb : Cst ≤ b3 W umin M * Graph.nrmL2 lam D ^ 2 := by
    rw [hCstdef, b3]
    have hbr := (b3_bracket_ge hM0).2.1
    have hD2 := sq_nonneg (Graph.nrmL2 lam D)
    have hc : 0 ≤ 4 * W / umin ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hbr hc
    calc W * (4 + 2 * Mp M) * (4 / umin ^ 2) * (1 + E ^ 2) * Graph.nrmL2 lam D ^ 2
        = 4 * W / umin ^ 2 * ((4 + 2 * Mp M) * (1 + Real.exp M ^ 2)) * Graph.nrmL2 lam D ^ 2 := by
          rw [hEdef]; ring
      _ ≤ 4 * W / umin ^ 2 * ((1 + Real.exp (Mp M)) * (b2 M * (1 + Real.exp (Mp M)) + 2 * b1 M))
          * Graph.nrmL2 lam D ^ 2 := mul_le_mul_of_nonneg_right this hD2
      _ = _ := by ring
  refine ⟨fun x => (hseg γ hmemγ x).1, ?_⟩
  rw [hfΦ γ (hApos γ hmemγ) (hCpos γ hmemγ), ← hf0, hfΦ 0 (hApos 0 hmem0) (hCpos 0 hmem0)]
  rw [hΦ10] at hTaylor
  have hD2 := sq_nonneg (Graph.nrmL2 lam D)
  have h1 : Cst * γ ^ 2 / 2 ≤ b3 W umin M * Graph.nrmL2 lam D ^ 2 * γ ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hCb (sq_nonneg γ); linarith
  have h2 : b3 W umin M * Graph.nrmL2 lam D ^ 2 * γ ^ 2 / 2 ≤ γ * Graph.nrmL2 lam D ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hγ (mul_nonneg hγ0 hD2)
    nlinarith
  nlinarith

end Descent

/-! ### The invariant region, and assertion *(a)* -/

section Region

variable {V : Type*} [Fintype V]

/-- **The positivity floor** (`proofs.tex:1061`): `𝓛(u) ≤ L₀` and `Πu ≥ m₀` give
`e^{−M} ≤ r(u) ≤ e^M`, i.e. `|log r(u)| ≤ M`, and `u ≥ u_min`. The second half is
`BoundaryBlowup.pos_of_loss_le`. -/
theorem abs_log_ratio_le {K : V → V → ℝ} {lam wf u : V → ℝ} {lamMin wmin L0 : ℝ}
    (hlam : ∀ x, 0 < lam x) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hL : lossVal lam wf logSq (ratio K lam u) ≤ L0) (x : V) :
    |Real.log (ratio K lam u x)| ≤ ratioCap lamMin wmin L0 := by
  have h := logSq_le_of_loss (r := ratio K lam u) (fun x => (hlam x).le) hlmin hlmin0 hwmin hw x
  have h2 : Real.log (ratio K lam u x) ^ 2 ≤ L0 / (wmin * lamMin) := by
    rw [le_div_iff₀ (mul_pos hwmin hlmin0)]
    simp only [logSq] at h
    nlinarith
  exact le_trans (Real.abs_le_sqrt h2) (le_max_right _ _)

/-- `ΠD(u) ≤ 0`, `prop:no_distant_equilibrium`*(1)*, read at `ν = wλ`. -/
theorem meanL2_lossGrad_nonpos {K : V → V → ℝ} {lam wf u : V → ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (hwpos : ∀ x, 0 < wf x) (hu : ∀ x, 0 < u x) :
    Graph.meanL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv u) ≤ 0 := by
  have h := (no_distant_equilibrium_one hinv hKnn hlam hu (w := fun x => wf x / u x)
    (fun x => div_pos (hwpos x) (hu x)) logSqDeriv_strictlyUnimodal).2.1
  rw [lossGrad_of_weight hlam]
  exact h

/-- **One step inside the region** (`proofs.tex:1060–1071`): a positive `u` with `𝓛(u) ≤ L₀`
and `Πu ≥ m₀` has `u ≥ u_min`, and one step at `0 ≤ γ ≤ 1/b₃` keeps positivity, descends by
`(γ/2)‖D‖²`, raises the mass, and adds exactly `γ²‖D‖²` to the squared norm. -/
theorem region_step {K : V → V → ℝ} {lam wf u : V → ℝ} {lamMin pmin wmin W L0 m0 γ : ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hW : ∀ x, wf x ≤ W) (hm0 : 0 < m0)
    (hγ0 : 0 ≤ γ)
    (hγb : γ * b3 W (uMin V lamMin pmin wmin L0 m0) (ratioCap lamMin wmin L0) ≤ 1)
    (hu : ∀ x, 0 < u x) (hL : lossVal lam wf logSq (ratio K lam u) ≤ L0)
    (hm : m0 ≤ Graph.meanL2 lam u) :
    (∀ x, uMin V lamMin pmin wmin L0 m0 ≤ u x)
      ∧ (∀ x, 0 < u x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x)
      ∧ lossVal lam wf logSq
          (ratio K lam (fun x => u x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x))
        ≤ lossVal lam wf logSq (ratio K lam u)
          - γ / 2 * Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv u) ^ 2
      ∧ Graph.meanL2 lam u
          ≤ Graph.meanL2 lam (fun x => u x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x)
      ∧ Graph.nrmL2 lam (fun x => u x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv u x) ^ 2
          = Graph.nrmL2 lam u ^ 2
            + γ ^ 2 * Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv u) ^ 2 := by
  haveI : Nonempty V := nonempty_of_total htot
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  have hW0 : 0 ≤ W := le_trans (hwpos x0).le (hW x0)
  have hfloor : ∀ x, uMin V lamMin pmin wmin L0 m0 ≤ u x := fun x =>
    pos_of_loss_le hinv hKM.nonneg hlam htot hu hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hL hm x
  have hlog := abs_log_ratio_le (K := K) hlam hlmin hlmin0 hwmin hw hL
  obtain ⟨hhalf, hdesc⟩ := descent_step hKM hinv hlam (fun x => (hwpos x).le) hW hW0 hu
    (uMin_pos hlmin0 hpmin0 hm0) hfloor (le_trans zero_le_one (one_le_ratioCap _ _ _)) hlog hγ0 hγb
  set D := lossGrad K lam (fun z => lam z * wf z) logSqDeriv u with hDdef
  refine ⟨hfloor, fun x => lt_of_lt_of_le (by linarith [hu x]) (hhalf x), hdesc, ?_, ?_⟩
  · rw [meanL2_sub_smul]
    have := meanL2_lossGrad_nonpos hKM.nonneg hinv hlam hwpos hu
    nlinarith
  · rw [sq_nrmL2_sub_smul hnn, ipL2_comm, ipL2_lossGrad_self _ _ hlam hu]
    ring

end Region

/-! ### The trajectory: assertions *(a)* and *(b)* -/

section Trajectory

variable {V : Type*} [Fintype V]

/-- **The region is invariant** (`proofs.tex:1067–1071`): every iterate is positive, has loss at most
`𝓛(μ₀)`, mass at least `m₀`, and `‖u_k‖² + 2γ𝓛(u_k) ≤ ‖u₀‖² + 2γ𝓛(μ₀)`. The region is fixed from
`u₀` in advance, and the step size `γ ≤ 1/b₃` is read off it, so no barrier can be jumped. -/
theorem traj_region {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin pmin wmin W γ : ℝ}
    {uk : ℕ → V → ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ0 : 0 ≤ γ)
    (hγb : γ * b3 W (uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))
      (Graph.meanL2 lam (uk 0))) (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))
      ≤ 1) :
    ∀ k, (∀ x, 0 < uk k x)
      ∧ lossVal lam wf logSq (ratio K lam (uk k)) ≤ lossVal lam wf logSq (ratio K lam (uk 0))
      ∧ Graph.meanL2 lam (uk 0) ≤ Graph.meanL2 lam (uk k)
      ∧ Graph.nrmL2 lam (uk k) ^ 2 + 2 * γ * lossVal lam wf logSq (ratio K lam (uk k))
          ≤ Graph.nrmL2 lam (uk 0) ^ 2 + 2 * γ * lossVal lam wf logSq (ratio K lam (uk 0)) := by
  have hm0 : 0 < Graph.meanL2 lam (uk 0) :=
    haveI := nonempty_of_total htot
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  intro k
  induction k with
  | zero => exact ⟨hu0, le_rfl, le_rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨hpos, hL, hm, hΦ⟩ := ih
    obtain ⟨-, hpos', hdesc, hmass, hnorm⟩ := region_step hKM hinv hlam htot hlmin hlmin0 hpmin0
      hpmin1 hcross hwmin hw hW hm0 hγ0 hγb hpos hL hm
    rw [hstep k]
    have hD2 := sq_nonneg (Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k)))
    refine ⟨hpos', by nlinarith, le_trans hm hmass, ?_⟩
    rw [hnorm]
    nlinarith

/-- **`theo:training_speed_full`, assertion *3(a)*** (`proofs.tex:1023`): for every `k`, `u_k ≥ u_min`, the loss descends by
`(γ/2)‖D(u_k)‖²`, the mass does not decrease, and `‖u_{k+1}‖² = ‖u_k‖² + γ²‖D(u_k)‖² ≤ 2‖u₀‖²`. -/
theorem traj_a {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin pmin wmin W γ : ℝ}
    {uk : ℕ → V → ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ0 : 0 ≤ γ)
    (hγb : γ * b3 W (uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))
      (Graph.meanL2 lam (uk 0))) (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))
      ≤ 1)
    (hγL : 2 * γ * lossVal lam wf logSq (ratio K lam (uk 0)) ≤ Graph.nrmL2 lam (uk 0) ^ 2) :
    ∀ k, (∀ x, uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))
          (Graph.meanL2 lam (uk 0)) ≤ uk k x)
      ∧ lossVal lam wf logSq (ratio K lam (uk (k + 1)))
          ≤ lossVal lam wf logSq (ratio K lam (uk k))
            - γ / 2 * Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2
      ∧ Graph.meanL2 lam (uk k) ≤ Graph.meanL2 lam (uk (k + 1))
      ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2
          = Graph.nrmL2 lam (uk k) ^ 2
            + γ ^ 2 * Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2
      ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2 ≤ 2 * Graph.nrmL2 lam (uk 0) ^ 2 := by
  have hm0 : 0 < Graph.meanL2 lam (uk 0) :=
    haveI := nonempty_of_total htot
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  have hreg := traj_region hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ0 hγb
  intro k
  obtain ⟨hpos, hL, hm, -⟩ := hreg k
  obtain ⟨hfloor, -, hdesc, hmass, hnorm⟩ := region_step hKM hinv hlam htot hlmin hlmin0 hpmin0
    hpmin1 hcross hwmin hw hW hm0 hγ0 hγb hpos hL hm
  obtain ⟨-, -, -, hΦ⟩ := hreg (k + 1)
  have hLnn : 0 ≤ lossVal lam wf logSq (ratio K lam (uk (k + 1))) :=
    lossVal_nonneg (fun x => (hlam x).le) (fun x => le_trans hwmin.le (hw x))
  rw [hstep k]
  refine ⟨hfloor, hdesc, hmass, hnorm, ?_⟩
  rw [hstep k] at hΦ hLnn
  nlinarith

/-- A real sequence with `L_{k+1} ≤ L_k − aL_k²` satisfies `L_k ≤ (L_0^{−1} + ka)^{−1}`
(`proofs.tex:1077`), with Lean's `0^{−1} = 0` standing in for the paper's `+∞` at a balanced
start. -/
theorem inv_recursion {L : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hL : ∀ k, 0 ≤ L k)
    (hrec : ∀ k, L (k + 1) ≤ L k - a * L k ^ 2) :
    ∀ k : ℕ, L k ≤ ((L 0)⁻¹ + k * a)⁻¹ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rcases eq_or_lt_of_le (hL (k + 1)) with h0 | hpos
    · rw [← h0]
      have : 0 ≤ (L 0)⁻¹ + ((k + 1 : ℕ) : ℝ) * a := by
        have := inv_nonneg.mpr (hL 0); positivity
      exact inv_nonneg.mpr this
    · have hk : 0 < L k := by nlinarith [hrec k, sq_nonneg (L k)]
      have h1 : 0 < 1 - a * L k := by
        by_contra hc
        push Not at hc
        nlinarith [hrec k]
      have hL0 : 0 < L 0 := by
        by_contra hc
        have hz : L 0 = 0 := le_antisymm (not_lt.mp hc) (hL 0)
        have hmono : ∀ j, L j ≤ L 0 := by
          intro j
          induction j with
          | zero => exact le_rfl
          | succ j ihj => nlinarith [hrec j, sq_nonneg (L j), ha]
        linarith [hmono k, hz]
      have hden : 0 < (L 0)⁻¹ + (k : ℝ) * a := by
        have := inv_pos.mpr hL0; positivity
      -- `1/L_k ≥ 1/L_0 + ka`
      have hinvk : (L 0)⁻¹ + (k : ℝ) * a ≤ (L k)⁻¹ := by
        have := inv_anti₀ hk ih
        rwa [inv_inv] at this
      -- `1/L_{k+1} ≥ 1/L_k + a`
      have hstep : (L k)⁻¹ + a ≤ (L (k + 1))⁻¹ := by
        have hle : L (k + 1) ≤ L k * (1 - a * L k) := by nlinarith [hrec k]
        rw [le_inv_comm₀ (by positivity) hpos]
        calc L (k + 1) ≤ L k * (1 - a * L k) := hle
          _ ≤ ((L k)⁻¹ + a)⁻¹ := by
            rw [le_inv_comm₀ (by positivity) (by positivity)]
            rw [show (L k * (1 - a * L k))⁻¹ = (L k)⁻¹ * (1 - a * L k)⁻¹ from mul_inv _ _]
            have hge : 1 + a * L k ≤ (1 - a * L k)⁻¹ := by
              rw [le_inv_comm₀ (by nlinarith) h1]
              rw [inv_eq_one_div, le_div_iff₀ (by nlinarith)]
              nlinarith [sq_nonneg (a * L k)]
            calc (L k)⁻¹ + a = (L k)⁻¹ * (1 + a * L k) := by field_simp
              _ ≤ (L k)⁻¹ * (1 - a * L k)⁻¹ :=
                mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr hk.le)
      have htot : (L 0)⁻¹ + ((k + 1 : ℕ) : ℝ) * a ≤ (L (k + 1))⁻¹ := by
        push_cast; linarith
      have := inv_anti₀ (by positivity) htot
      rwa [inv_inv] at this

/-- `‖u_k‖ ≤ √2‖u₀‖` and `0 < ‖u_k‖` along the descent. -/
theorem traj_nrm_le {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin pmin wmin W γ : ℝ}
    {uk : ℕ → V → ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ0 : 0 ≤ γ)
    (hγb : γ * b3 W (uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))
      (Graph.meanL2 lam (uk 0))) (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))
      ≤ 1)
    (hγL : 2 * γ * lossVal lam wf logSq (ratio K lam (uk 0)) ≤ Graph.nrmL2 lam (uk 0) ^ 2) :
    ∀ k, Graph.nrmL2 lam (uk k) ^ 2 ≤ 2 * Graph.nrmL2 lam (uk 0) ^ 2
      ∧ Graph.nrmL2 lam (uk k) ≤ Real.sqrt 2 * Graph.nrmL2 lam (uk 0)
      ∧ Graph.meanL2 lam (uk k) ≤ Graph.nrmL2 lam (uk k)
      ∧ 0 < Graph.meanL2 lam (uk k) := by
  have hreg := traj_region hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ0 hγb
  have ha := traj_a hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ0 hγb hγL
  have hm0 : 0 < Graph.meanL2 lam (uk 0) := by
    haveI := nonempty_of_total htot
    exact Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  intro k
  have hsq : Graph.nrmL2 lam (uk k) ^ 2 ≤ 2 * Graph.nrmL2 lam (uk 0) ^ 2 := by
    cases k with
    | zero => nlinarith [sq_nonneg (Graph.nrmL2 lam (uk 0))]
    | succ j => exact (ha j).2.2.2.2
  refine ⟨hsq, ?_, (mean_le_nrmL2_iff_const hlam htot (fun x => ((hreg k).1 x).le)).1,
    lt_of_lt_of_le hm0 (hreg k).2.2.1⟩
  have h2 : Real.sqrt 2 * Graph.nrmL2 lam (uk 0)
      = Real.sqrt (2 * Graph.nrmL2 lam (uk 0) ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (Graph.nrmL2_nonneg _ _)]
  rw [h2, ← Real.sqrt_sq (Graph.nrmL2_nonneg lam (uk k))]
  exact Real.sqrt_le_sqrt hsq

/-- **`theo:training_speed_full`, assertion *3(b)*, the discrete Łojasiewicz envelope** (`proofs.tex:1024`, proof `:1072–1077`):
`𝓛(u_k) ≤ (𝓛(μ₀)^{−1} + kγκ²/4)^{−1}` with the continuous phase's
`κ = w_min λ_min^{1/2}/(‖u₀‖‖w‖_{L^∞}M)`.

The per-step gradient lower bound `‖D(u_k)‖ ≥ (κ/√2)𝓛(u_k)` is
`Lojasiewicz.global_lojasiewicz_static` read at `u₀ := u_k` (so its sphere hypothesis is `rfl`),
with `M` computed from `𝓛(μ₀)`, and `‖u_k‖ ≤ √2‖u₀‖`. -/
theorem traj_b {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin pmin wmin W γ : ℝ}
    {uk : ℕ → V → ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ0 : 0 ≤ γ)
    (hγb : γ * b3 W (uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))
      (Graph.meanL2 lam (uk 0))) (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))
      ≤ 1)
    (hγL : 2 * γ * lossVal lam wf logSq (ratio K lam (uk 0)) ≤ Graph.nrmL2 lam (uk 0) ^ 2) :
    ∀ k : ℕ, lossVal lam wf logSq (ratio K lam (uk k))
      ≤ ((lossVal lam wf logSq (ratio K lam (uk 0)))⁻¹
          + k * γ * (wmin * Real.sqrt lamMin / (Graph.nrmL2 lam (uk 0) * W
              * ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))) ^ 2 / 4)⁻¹ := by
  have hreg := traj_region hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ0 hγb
  have ha := traj_a hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ0 hγb hγL
  have hnrm := traj_nrm_le hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ0 hγb hγL
  haveI := nonempty_of_total htot
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hWpos : 0 < W := lt_of_lt_of_le hwmin (le_trans (hw x0) (hW x0))
  set L0 := lossVal lam wf logSq (ratio K lam (uk 0)) with hL0def
  set U0 := Graph.nrmL2 lam (uk 0) with hU0def
  set M := ratioCap lamMin wmin L0 with hMdef
  have hMpos : 0 < M := ratioCap_pos _ _ _
  have hU0pos : 0 < U0 := lt_of_lt_of_le (hnrm 0).2.2.2 (hnrm 0).2.2.1
  set κ := wmin * Real.sqrt lamMin / (U0 * W * M) with hκdef
  have hc0 : 0 < wmin * Real.sqrt lamMin / (W * M) := by
    have := Real.sqrt_pos.mpr hlmin0; positivity
  have hloj : ∀ k, κ / Real.sqrt 2 * lossVal lam wf logSq (ratio K lam (uk k))
      ≤ Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k)) := by
    intro k
    obtain ⟨hpos, hL, -, -⟩ := hreg k
    have hnk : 0 < Graph.nrmL2 lam (uk k) := lt_of_lt_of_le (hnrm k).2.2.2 (hnrm k).2.2.1
    have hstat := global_lojasiewicz_static (u0 := uk k) hinv hKM.nonneg hlam htot hpos hlmin
      hlmin0 hwmin hw hW rfl hnk hL
    rw [← lossGrad_of_weight hlam] at hstat
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (lossVal_nonneg (fun x => (hlam x).le)
      (fun x => le_trans hwmin.le (hw x)))) hstat
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hkey : κ / Real.sqrt 2 = wmin * Real.sqrt lamMin / (W * M) / (Real.sqrt 2 * U0) := by
      rw [hκdef]; field_simp
    have hkey2 : wmin * Real.sqrt lamMin / (Graph.nrmL2 lam (uk k) * W
        * max 1 (Real.sqrt (L0 / (wmin * lamMin))))
        = wmin * Real.sqrt lamMin / (W * M) / Graph.nrmL2 lam (uk k) := by
      rw [hMdef, ratioCap]; field_simp
    rw [hkey, hkey2]
    exact div_le_div_of_nonneg_left hc0.le hnk (hnrm k).2.1
  refine fun k => le_trans (inv_recursion (L := fun k => lossVal lam wf logSq (ratio K lam (uk k)))
    (a := γ * κ ^ 2 / 4) (by positivity)
    (fun k => lossVal_nonneg (fun x => (hlam x).le) (fun x => le_trans hwmin.le (hw x)))
    (fun k => ?_) k) (le_of_eq ?_)
  · have hdesc := (ha k).2.1
    have hL := lossVal_nonneg (lam := lam) (wf := wf) (r := ratio K lam (uk k))
      (fun x => (hlam x).le) (fun x => le_trans hwmin.le (hw x))
    have h1 := hloj k
    have h2 : (κ / Real.sqrt 2 * lossVal lam wf logSq (ratio K lam (uk k))) ^ 2
        ≤ Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (κ / Real.sqrt 2 * lossVal lam wf logSq (ratio K lam (uk k))) ^ 2
        = κ ^ 2 / 2 * lossVal lam wf logSq (ratio K lam (uk k)) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
    show lossVal lam wf logSq (ratio K lam (uk (k + 1)))
      ≤ lossVal lam wf logSq (ratio K lam (uk k))
        - γ * κ ^ 2 / 4 * lossVal lam wf logSq (ratio K lam (uk k)) ^ 2
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ γ / 2)
    rw [h3] at h4
    nlinarith
  · ring

/-! ### Assertion *(c)*, first half: entry into the rescaled basin at `k₀(γ)` -/

/-- **`δ₁ := ε₀m₀/(√2 B̂_σ‖u₀‖)`** (`proofs.tex:1054`). -/
noncomputable def delta1 (eps0 m0 Bhat U0 : ℝ) : ℝ := eps0 * m0 / (Real.sqrt 2 * Bhat * U0)

/-- **`κ := w_min λ_min^{1/2}/(‖u₀‖‖w‖_{L^∞}M)`** (`proofs.tex:1010`). -/
noncomputable def kappa (wmin lamMin U0 W M : ℝ) : ℝ := wmin * Real.sqrt lamMin / (U0 * W * M)

/-- **The first form of `k₀(γ)`**, `16/(γκ²λ_min w_min δ₁²)` (`proofs.tex:1055`), before its
ceiling; `k0_closed_form` is the printed closed form. -/
noncomputable def k0real (γ κ lamMin wmin δ1 : ℝ) : ℝ := 16 / (γ * κ ^ 2 * lamMin * wmin * δ1 ^ 2)

theorem abs_exp_sub_one_le {y d : ℝ} (hy : |y| ≤ d / 2) (hd : d ≤ 1) :
    |Real.exp y - 1| ≤ d := by
  have h1 : |y| ≤ 1 := by linarith [abs_nonneg y]
  have h2 := Real.abs_exp_sub_one_sub_id_le h1
  have h3 : |Real.exp y - 1| ≤ |Real.exp y - 1 - y| + |y| := by
    calc |Real.exp y - 1| = |(Real.exp y - 1 - y) + y| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have h4 : y ^ 2 ≤ |y| := by
    rw [← sq_abs]; nlinarith [abs_nonneg y]
  linarith

/-- **`theo:training_speed_full`*(3)*, the entry bound** (`proofs.tex:1078`): for every `k ≥ k₀(γ)`, `|r(u_k) − 1| ≤ δ₁` at every
state, `‖u_k − Πu_k‖ ≤ ε₀m₀`, and `‖u_k/Πu_k − 1‖ ≤ ε₀`. Here `ε₀ ∈ (0, 1/32]` and the coercivity
constant `B̂ ≥ 1` are parameters; the theorem below instantiates them at the paper's. -/
theorem traj_entry {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin pmin wmin W γ Bhat eps0 : ℝ}
    {uk : ℕ → V → ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ : 0 < γ)
    (hγb : γ * b3 W (uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))
      (Graph.meanL2 lam (uk 0))) (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))
      ≤ 1)
    (hγL : 2 * γ * lossVal lam wf logSq (ratio K lam (uk 0)) ≤ Graph.nrmL2 lam (uk 0) ^ 2)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (heps0 : 0 < eps0) (heps1 : eps0 ≤ 1 / 32) :
    ∀ k : ℕ, ⌈k0real γ (kappa wmin lamMin (Graph.nrmL2 lam (uk 0)) W
        (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))) lamMin wmin
        (delta1 eps0 (Graph.meanL2 lam (uk 0)) Bhat (Graph.nrmL2 lam (uk 0)))⌉₊ ≤ k →
      (∀ x, |ratio K lam (uk k) x - 1|
          ≤ delta1 eps0 (Graph.meanL2 lam (uk 0)) Bhat (Graph.nrmL2 lam (uk 0)))
        ∧ Graph.nrmL2 lam (perpL2 lam (uk k)) ≤ eps0 * Graph.meanL2 lam (uk 0)
        ∧ Graph.nrmL2 lam (fun x => uk k x / Graph.meanL2 lam (uk k) - 1) ≤ eps0 := by
  have hreg := traj_region hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb
  have hb := traj_b hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb hγL
  have hnrm := traj_nrm_le hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb hγL
  haveI := nonempty_of_total htot
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hWpos : 0 < W := lt_of_lt_of_le hwmin (le_trans (hw x0) (hW x0))
  set L0 := lossVal lam wf logSq (ratio K lam (uk 0)) with hL0def
  set U0 := Graph.nrmL2 lam (uk 0) with hU0def
  set m0 := Graph.meanL2 lam (uk 0) with hm0def
  set M := ratioCap lamMin wmin L0 with hMdef
  have hMpos : 0 < M := ratioCap_pos _ _ _
  have hm0pos : 0 < m0 := (hnrm 0).2.2.2
  have hmU : m0 ≤ U0 := (hnrm 0).2.2.1
  have hU0pos : 0 < U0 := lt_of_lt_of_le hm0pos hmU
  set κ := kappa wmin lamMin U0 W M with hκdef
  have hκ : 0 < κ := by
    have := Real.sqrt_pos.mpr hlmin0; simp only [hκdef, kappa]; positivity
  set δ1 := delta1 eps0 m0 Bhat U0 with hδ1def
  have hs2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hδ1 : 0 < δ1 := by
    have : 0 < Real.sqrt 2 := by positivity
    simp only [hδ1def, delta1]; have := lt_of_lt_of_le zero_lt_one hB1; positivity
  have hδ1le : δ1 ≤ eps0 := by
    simp only [hδ1def, delta1]
    rw [div_le_iff₀ (by have := lt_of_lt_of_le zero_lt_one hB1; positivity)]
    have h1 : m0 ≤ Real.sqrt 2 * Bhat * U0 := by
      have : 1 ≤ Real.sqrt 2 * Bhat := by nlinarith
      nlinarith
    nlinarith
  intro k hk
  set k0r := k0real γ κ lamMin wmin δ1 with hk0r
  have hk0rpos : 0 < k0r := by simp only [hk0r, k0real]; positivity
  have hkreal : k0r ≤ (k : ℝ) := Nat.ceil_le.mp hk
  -- the loss is below `λ_min w_min δ₁²/4`
  have hLk : lossVal lam wf logSq (ratio K lam (uk k)) ≤ lamMin * wmin * δ1 ^ 2 / 4 := by
    refine le_trans (hb k) ?_
    have hbig : 4 / (lamMin * wmin * δ1 ^ 2) ≤ L0⁻¹ + k * γ * κ ^ 2 / 4 := by
      have hL0inv : 0 ≤ L0⁻¹ := inv_nonneg.mpr (lossVal_nonneg (fun x => (hlam x).le)
        (fun x => le_trans hwmin.le (hw x)))
      have h1 : k0r * γ * κ ^ 2 / 4 ≤ k * γ * κ ^ 2 / 4 := by
        have := mul_le_mul_of_nonneg_right hkreal (by positivity : (0:ℝ) ≤ γ * κ ^ 2 / 4)
        linarith
      have h2 : k0r * γ * κ ^ 2 / 4 = 4 / (lamMin * wmin * δ1 ^ 2) := by
        simp only [hk0r, k0real]; field_simp; ring
      linarith
    have := inv_anti₀ (by positivity) hbig
    calc (L0⁻¹ + k * γ * κ ^ 2 / 4)⁻¹ ≤ (4 / (lamMin * wmin * δ1 ^ 2))⁻¹ := this
      _ = lamMin * wmin * δ1 ^ 2 / 4 := by rw [inv_div]
  obtain ⟨hpos, -, hmk, -⟩ := hreg k
  have hratio : ∀ x, |ratio K lam (uk k) x - 1| ≤ δ1 := by
    intro x
    have h := logSq_le_of_loss (r := ratio K lam (uk k)) (fun x => (hlam x).le) hlmin hlmin0
      hwmin hw x
    have h2 : Real.log (ratio K lam (uk k) x) ^ 2 ≤ (δ1 / 2) ^ 2 := by
      simp only [logSq] at h
      have hlw : 0 < lamMin * wmin := mul_pos hlmin0 hwmin
      have : lamMin * wmin * Real.log (ratio K lam (uk k) x) ^ 2 ≤ lamMin * wmin * (δ1 / 2) ^ 2 := by
        nlinarith
      exact le_of_mul_le_mul_left this hlw
    have h3 : |Real.log (ratio K lam (uk k) x)| ≤ δ1 / 2 := by
      have := Real.abs_le_sqrt h2
      rwa [Real.sqrt_sq (by linarith)] at this
    have hr := ratio_pos hinv hKM.nonneg hlam hpos x
    rw [← Real.exp_log hr]
    exact abs_exp_sub_one_le h3 (by linarith)
  have hperp : Graph.nrmL2 lam (perpL2 lam (uk k)) ≤ eps0 * m0 := by
    have h1 := nrmL2_perpL2_le_of_ratio_close (fun x => (hlam x).le) (fun x => (hpos x).ne')
      hδ1.le (le_trans zero_le_one hB1) hcoer hratio
    refine le_trans h1 ?_
    have h2 : Bhat * δ1 * (Real.sqrt 2 * U0) = eps0 * m0 := by
      simp only [hδ1def, delta1]; field_simp
    rw [← h2]
    exact mul_le_mul_of_nonneg_left (hnrm k).2.1 (by have := le_trans zero_le_one hB1; positivity)
  refine ⟨hratio, hperp, ?_⟩
  have hmkpos : 0 < Graph.meanL2 lam (uk k) := lt_of_lt_of_le hm0pos hmk
  rw [dev_eq_smul_perpL2 hmkpos.ne' rfl, nrmL2_smul, abs_of_pos (inv_pos.mpr hmkpos)]
  rw [inv_mul_le_iff₀ hmkpos]
  calc Graph.nrmL2 lam (perpL2 lam (uk k)) ≤ eps0 * m0 := hperp
    _ ≤ Graph.meanL2 lam (uk k) * eps0 := by nlinarith
/-! ### Assertion *(c)*, second half: the handover to Theorem 10's discrete clause -/

/-- **`Γ₃ := sup_{[1/2,3/2]}|g'''| = 48 + 32 ln 2`** for `g = (log x)²`, attained at `x = 1/2`
(`g'''(x) = 2(2 ln x − 3)/x³`): the constant `theo:local_convergence_full` is read at in items
*2* and *3*. -/
noncomputable def Gamma3Val : ℝ := 48 + 32 * Real.log 2

theorem twentyfour_le_Gamma3Val : (24:ℝ) ≤ Gamma3Val := by
  have := Real.log_pos (by norm_num : (1:ℝ) < 2)
  simp only [Gamma3Val]; linarith

/-- **`ε₀` of `theo:local_convergence_full` for `g = (log x)²` at `a = 1/2`**, `g''(1) = 2`, with
third-derivative constant `M₃`, `‖w‖_{L^∞} = W`, coercivity constant `B̂` and `C_∞ = λ_min^{−1/2}`. -/
noncomputable def eps0At (M3 wmin W Bhat lamMin : ℝ) : ℝ :=
  eps0 (epsW (1/2) 2 wmin (Kexp 2 (1/2) M3 W) Bhat) (Cinf lamMin)
    (C7 (C6 (Cg 2 (1/2) M3) W) 2 wmin) (rhoL 2 wmin Bhat) (C6 (Cg 2 (1/2) M3) W)

/-- **`γ₀` of `theo:local_convergence_full`** at the same constants. -/
noncomputable def gamma0At (M3 wmin W Bhat : ℝ) : ℝ :=
  gamma0 2 wmin (Lgd 2 W (Kexp 2 (1/2) M3 W) (epsW (1/2) 2 wmin (Kexp 2 (1/2) M3 W) Bhat))

theorem eps0At_pos {M3 wmin W Bhat lamMin : ℝ} (hM3 : 0 ≤ M3) (hwmin : 0 < wmin) (hW : 0 < W)
    (hB : 0 < Bhat) (hlmin0 : 0 < lamMin) : 0 < eps0At M3 wmin W Bhat lamMin :=
  eps0_pos (epsW_pos (by norm_num) (by norm_num) hwmin
      (Kexp_pos (by norm_num) hM3 (by norm_num) hW) hB)
    (Cinf_pos hlmin0)
    (C7_nonneg (C6_pos (by norm_num) hM3 (by norm_num) hW).le (by positivity))
    (rhoL_pos (by positivity) hB) (C6_pos (by norm_num) hM3 (by norm_num) hW)

theorem gamma0At_pos {M3 wmin W Bhat : ℝ} (hM3 : 0 ≤ M3) (hwmin : 0 < wmin) (hW : 0 < W)
    (hB : 0 < Bhat) : 0 < gamma0At M3 wmin W Bhat :=
  gamma0_pos (by norm_num) hwmin (Lgd_pos (by norm_num) hW
    (Kexp_nonneg (by norm_num) hM3 (by norm_num) hW.le)
    (epsW_nonneg (by norm_num) (by norm_num) hwmin.le
      (Kexp_nonneg (by norm_num) hM3 (by norm_num) hW.le) hB.le))

/-- **`C_∞ε₀ ≤ 1/32`**, i.e. `ε₀ ≤ λ_min^{1/2}/32` (`proofs.tex:1048`), from `ε₀ ≤ a/(16C_∞)`. -/
theorem Cinf_mul_eps0At_le {M3 wmin W Bhat lamMin : ℝ} (hM3 : 0 ≤ M3) (hwmin : 0 < wmin)
    (hW : 0 < W) (hlmin0 : 0 < lamMin) :
    Cinf lamMin * eps0At M3 wmin W Bhat lamMin ≤ 1 / 32 := by
  have h := eps0_le_a_div (a := 1/2) (g2 := 2) (wmin := wmin) (Kex := Kexp 2 (1/2) M3 W)
    (Bhat := Bhat) (rho := rhoL 2 wmin Bhat) (c6 := C6 (Cg 2 (1/2) M3) W)
    (Ci := Cinf lamMin) (c7 := C7 (C6 (Cg 2 (1/2) M3) W) 2 wmin) (by norm_num)
    (Cinf_pos hlmin0) (C7_nonneg (C6_pos (by norm_num) hM3 (by norm_num) hW).le (by positivity))
  have hC := Cinf_pos hlmin0
  rw [eps0At]
  calc Cinf lamMin * _ ≤ Cinf lamMin * (1 / 2 / (16 * Cinf lamMin)) :=
        mul_le_mul_of_nonneg_left h hC.le
    _ = 1 / 32 := by field_simp; norm_num

theorem eps0At_le {lam : V → ℝ} {M3 wmin W Bhat lamMin : ℝ} (hM3 : 0 ≤ M3)
    (hwmin : 0 < wmin) (hW : 0 < W) (hB : 0 < Bhat) (hlmin0 : 0 < lamMin)
    (hlmin : ∀ x, lamMin ≤ lam x) (htot : ∑ x, lam x = 1) :
    eps0At M3 wmin W Bhat lamMin ≤ 1 / 32 := by
  have h1 := Cinf_mul_eps0At_le (Bhat := Bhat) hM3 hwmin hW hlmin0
  have h2 := one_le_Cinf hlmin0 hlmin htot
  have h3 := (eps0At_pos (Bhat := Bhat) hM3 hwmin hW hB hlmin0).le
  nlinarith

/-- The deviation of `u/m` from `1`, orthogonalised, is `m⁻¹` times that of `u`. -/
theorem perpL2_div_sub_one {lam u : V → ℝ} (htot : ∑ x, lam x = 1) {m : ℝ} (hm : m ≠ 0) :
    perpL2 lam (fun x => u x / m - 1) = fun x => m⁻¹ * perpL2 lam u x := by
  have hmean : Graph.meanL2 lam (fun x => u x / m - 1) = Graph.meanL2 lam u / m - 1 := by
    simp only [Graph.meanL2, mul_sub, mul_one, Finset.sum_sub_distrib, htot, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  funext x
  rw [perpL2_apply, perpL2_apply, hmean]
  field_simp
  ring

/-- **`theo:training_speed_full`, assertion *3(c)*'s contraction** (`proofs.tex:1079`): with `m := Πu_{k₀(γ)}` and
`h_j := u_{k₀+j}/m − 1`, homogeneity gives `h_{j+1} = h_j − (γ/m²)D(1 + h_j)`, the step `γ/m²` is
at most `γ₀`, `‖h_0‖ ≤ ε₀`, and `LocalConvergence.local_convergence_gd` gives the per-step
contraction; multiplying by `m` gives `‖u_{k+1} − Πu_{k+1}‖ ≤ (1 − γϱ/(4m²))‖u_k − Πu_k‖`.

`M₃` is any constant `≥ 24` (the Taylor bound `LogSqTaylor` supplies at `a = 1/2` then holds with
`M₃`); the theorem below takes the paper's `Γ₃ = 48 + 32 ln 2`. -/
theorem traj_c {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin pmin wmin W γ Bhat M3 : ℝ}
    {uk : ℕ → V → ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ : 0 < γ)
    (hγb : γ * b3 W (uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))
      (Graph.meanL2 lam (uk 0))) (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))
      ≤ 1)
    (hγL : 2 * γ * lossVal lam wf logSq (ratio K lam (uk 0)) ≤ Graph.nrmL2 lam (uk 0) ^ 2)
    (hγ0 : γ ≤ gamma0At M3 wmin W Bhat * Graph.meanL2 lam (uk 0) ^ 2)
    (hM3 : 24 ≤ M3) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f)) :
    ∀ k : ℕ, ⌈k0real γ (kappa wmin lamMin (Graph.nrmL2 lam (uk 0)) W
        (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))) lamMin wmin
        (delta1 (eps0At M3 wmin W Bhat lamMin) (Graph.meanL2 lam (uk 0)) Bhat
          (Graph.nrmL2 lam (uk 0)))⌉₊ ≤ k →
      Graph.nrmL2 lam (perpL2 lam (uk (k + 1)))
        ≤ (1 - γ * rhoL 2 wmin Bhat / (4 * Graph.meanL2 lam (uk ⌈k0real γ (kappa wmin lamMin
            (Graph.nrmL2 lam (uk 0)) W (ratioCap lamMin wmin
              (lossVal lam wf logSq (ratio K lam (uk 0))))) lamMin wmin
            (delta1 (eps0At M3 wmin W Bhat lamMin) (Graph.meanL2 lam (uk 0)) Bhat
              (Graph.nrmL2 lam (uk 0)))⌉₊) ^ 2))
          * Graph.nrmL2 lam (perpL2 lam (uk k)) := by
  haveI := nonempty_of_total htot
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hWpos : 0 < W := lt_of_lt_of_le hwmin (le_trans (hw x0) (hW x0))
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hB : 0 < Bhat := lt_of_lt_of_le zero_lt_one hB1
  have hM30 : 0 ≤ M3 := by linarith
  have he0 := eps0At_pos (Bhat := Bhat) hM30 hwmin hWpos hB hlmin0
  have he1 := eps0At_le (Bhat := Bhat) hM30 hwmin hWpos hB hlmin0 hlmin htot
  have hentry := traj_entry hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ hγb hγL hB1 hcoer he0 he1
  have hreg := traj_region hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb
  have ha := traj_a hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb hγL
  have hnrm := traj_nrm_le hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb hγL
  set k0 := ⌈k0real γ (kappa wmin lamMin (Graph.nrmL2 lam (uk 0)) W
        (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))) lamMin wmin
        (delta1 (eps0At M3 wmin W Bhat lamMin) (Graph.meanL2 lam (uk 0)) Bhat
          (Graph.nrmL2 lam (uk 0)))⌉₊ with hk0def
  set m := Graph.meanL2 lam (uk k0) with hmdef
  have hm0pos : 0 < Graph.meanL2 lam (uk 0) := (hnrm 0).2.2.2
  have hmm0 : Graph.meanL2 lam (uk 0) ≤ m := (hreg k0).2.2.1
  have hmpos : 0 < m := lt_of_lt_of_le hm0pos hmm0
  set hj : ℕ → V → ℝ := fun j x => uk (k0 + j) x / m - 1 with hjdef
  have hone : ∀ j, (fun z => 1 + hj j z) = fun z => m⁻¹ * uk (k0 + j) z := by
    intro j; funext z; simp only [hjdef]; field_simp; ring
  have hstep' : ∀ j : ℕ, hj (j + 1) = fun x =>
      hj j x - γ / m ^ 2 * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (fun z => 1 + hj j z) x := by
    intro j
    rw [hone j, lossGrad_smul (inv_ne_zero hmpos.ne')]
    funext x
    simp only [hjdef]
    rw [show k0 + (j + 1) = (k0 + j) + 1 by ring, hstep (k0 + j)]
    simp only [inv_inv]
    field_simp
    ring
  have hgam : γ / m ^ 2 ≤ gamma0At M3 wmin W Bhat := by
    rw [div_le_iff₀ (by positivity)]
    have hg0 := (gamma0At_pos (Bhat := Bhat) hM30 hwmin hWpos hB).le
    have : Graph.meanL2 lam (uk 0) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hm0pos.le hmm0 2
    nlinarith
  have hnorm0 : Graph.nrmL2 lam (hj 0) ≤ eps0At M3 wmin W Bhat lamMin := by
    have := (hentry k0 le_rfl).2.2
    simpa only [hjdef, add_zero] using this
  have hwabs : ∀ x, |wf x| ≤ W := fun x => by
    rw [abs_of_pos (lt_of_lt_of_le hwmin (hw x))]; exact hW x
  have hlc := local_convergence_gd (K := K) (lam := lam) (w := wf) (gd := logSqDeriv) (hk := hj)
    (g2 := 2) (a := 1/2) (M3 := M3) (wsup := W) (wmin := wmin) (Bhat := Bhat) (lamMin := lamMin)
    (gam := γ / m ^ 2) (hKM.toIsMarkovOn lam) ⟨hnn, hinv⟩ hlam htot hlmin0 hlmin (by norm_num)
    hM30 (by norm_num) hwabs hwmin hw hB1 hcoer
    (fun y hy => le_trans (logSqDeriv_taylor_half y hy)
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)))
    hstep' (by positivity) hgam hnorm0
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := hlc j
  have hperp : ∀ i, Graph.nrmL2 lam (perpL2 lam (hj i)) = m⁻¹ * Graph.nrmL2 lam (perpL2 lam (uk (k0 + i))) := by
    intro i
    simp only [hjdef]
    rw [perpL2_div_sub_one htot hmpos.ne', nrmL2_smul, abs_of_pos (inv_pos.mpr hmpos)]
  rw [hperp, hperp, show k0 + (j + 1) = k0 + j + 1 by ring] at h
  have hmi : 0 < m⁻¹ := inv_pos.mpr hmpos
  have h2 := mul_le_mul_of_nonneg_left h hmpos.le
  have heq1 : m * (m⁻¹ * Graph.nrmL2 lam (perpL2 lam (uk (k0 + j + 1))))
      = Graph.nrmL2 lam (perpL2 lam (uk (k0 + j + 1))) := by field_simp
  have heq2 : m * ((1 - γ / m ^ 2 * rhoL 2 wmin Bhat / 4) * (m⁻¹ * Graph.nrmL2 lam (perpL2 lam (uk (k0 + j)))))
      = (1 - γ * rhoL 2 wmin Bhat / (4 * m ^ 2)) * Graph.nrmL2 lam (perpL2 lam (uk (k0 + j))) := by
    field_simp
  rw [heq1, heq2] at h2
  exact h2

/-! ### Assertion *(d)*: the limit -/

theorem delta1_le {eps0 m0 Bhat U0 : ℝ} (heps0 : 0 ≤ eps0) (hm0 : 0 < m0) (hB1 : 1 ≤ Bhat)
    (hmU : m0 ≤ U0) : delta1 eps0 m0 Bhat U0 ≤ eps0 := by
  have hs2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hU0 : 0 < U0 := lt_of_lt_of_le hm0 hmU
  simp only [delta1]
  rw [div_le_iff₀ (by have := lt_of_lt_of_le zero_lt_one hB1; positivity)]
  have h1 : m0 ≤ Real.sqrt 2 * Bhat * U0 := by
    have : 1 ≤ Real.sqrt 2 * Bhat := by nlinarith
    nlinarith
  nlinarith

/-- `|log r| ≤ (32/31)|r − 1|` when `|r − 1| ≤ 1/32`. -/
theorem abs_log_le_of_close {r : ℝ} (h : |r - 1| ≤ 1 / 32) :
    |Real.log r| ≤ 32 / 31 * |r - 1| := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hr : 0 < r := by linarith
  rcases le_or_gt 1 r with hge | hlt
  · have hl0 : 0 ≤ Real.log r := Real.log_nonneg hge
    have hl1 := Real.log_le_sub_one_of_pos hr
    rw [abs_of_nonneg hl0, abs_of_nonneg (by linarith)]
    linarith
  · have hl0 : Real.log r < 0 := Real.log_neg hr hlt
    have hl1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
    rw [Real.log_inv] at hl1
    rw [abs_of_neg hl0, abs_of_neg (by linarith)]
    have : r⁻¹ - 1 ≤ 32 / 31 * (1 - r) := by
      rw [inv_eq_one_div, div_sub_one hr.ne', div_le_iff₀ hr]
      nlinarith
    linarith

/-- **`𝓛(u) ≤ (24/5)‖w‖_{L^∞}‖u − Πu‖²/m²`** near the balanced ray (`proofs.tex:1081`):
`r ≥ 31/32` gives `|log r| ≤ (32/31)|r − 1|`, `u ≥ 31m/32` gives `|r − 1| ≤ (32/31)|(P−I)ξ|/m`,
and `‖P − I‖ ≤ 2`, `(32/31)⁴ ≤ 6/5`. -/
theorem loss_le_perp_sq {K : V → V → ℝ} {lam wf u : V → ℝ} {W m : ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (hW : ∀ x, wf x ≤ W) (hW0 : 0 ≤ W) (hm : 0 < m)
    (hu : ∀ x, 31 / 32 * m ≤ u x) (hr : ∀ x, |ratio K lam u x - 1| ≤ 1 / 32) :
    lossVal lam wf logSq (ratio K lam u)
      ≤ 24 / 5 * W * Graph.nrmL2 lam (perpL2 lam u) ^ 2 / m ^ 2 := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hupos : ∀ x, 0 < u x := fun x => lt_of_lt_of_le (by positivity) (hu x)
  have hA : ∀ x, Aop K lam (perpL2 lam u) x = (ratio K lam u x - 1) * u x := by
    intro x
    rw [Aop_perpL2 ⟨hnn, hinv⟩ u (hlam x).ne']
    exact Aop_eq_ratio_sub_one_mul (hupos x).ne'
  have hpt : ∀ x, logSq (ratio K lam u x)
      ≤ (32 / 31) ^ 4 / m ^ 2 * (Aop K lam (perpL2 lam u) x * Aop K lam (perpL2 lam u) x) := by
    intro x
    have h1 := abs_log_le_of_close (hr x)
    have h2 : |ratio K lam u x - 1| ≤ 32 / 31 * |Aop K lam (perpL2 lam u) x| / m := by
      rw [hA x, abs_mul, abs_of_pos (hupos x), le_div_iff₀ hm]
      have := abs_nonneg (ratio K lam u x - 1)
      nlinarith [hu x]
    have h3 : |Real.log (ratio K lam u x)| ≤ (32 / 31) ^ 2 * |Aop K lam (perpL2 lam u) x| / m := by
      calc _ ≤ 32 / 31 * |ratio K lam u x - 1| := h1
        _ ≤ 32 / 31 * (32 / 31 * |Aop K lam (perpL2 lam u) x| / m) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = _ := by ring
    have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [sq_abs] at h4
    simp only [logSq]
    calc Real.log (ratio K lam u x) ^ 2 ≤ ((32 / 31) ^ 2 * |Aop K lam (perpL2 lam u) x| / m) ^ 2 := h4
      _ = _ := by rw [div_pow, mul_pow, sq_abs]; field_simp
  have hsum : lossVal lam wf logSq (ratio K lam u)
      ≤ W * ((32 / 31) ^ 4 / m ^ 2) * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2 := by
    rw [Graph.sq_nrmL2 hnn]
    simp only [lossVal, Graph.ipL2, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hAA := mul_self_nonneg (Aop K lam (perpL2 lam u) x)
    have h5 : wf x * logSq (ratio K lam u x)
        ≤ W * ((32 / 31) ^ 4 / m ^ 2 * (Aop K lam (perpL2 lam u) x * Aop K lam (perpL2 lam u) x)) :=
      mul_le_mul (hW x) (hpt x) (logSq_nonneg _) hW0
    calc lam x * (wf x * logSq (ratio K lam u x))
        ≤ lam x * (W * ((32 / 31) ^ 4 / m ^ 2
            * (Aop K lam (perpL2 lam u) x * Aop K lam (perpL2 lam u) x))) :=
          mul_le_mul_of_nonneg_left h5 (hnn x)
      _ = _ := by ring
  have hA2 : Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2 ≤ 4 * Graph.nrmL2 lam (perpL2 lam u) ^ 2 := by
    have := nrmL2_Aop_le_two hKM ⟨hnn, hinv⟩ (perpL2 lam u)
    have h0 := Graph.nrmL2_nonneg lam (Aop K lam (perpL2 lam u))
    nlinarith
  refine le_trans hsum ?_
  rw [show 24 / 5 * W * Graph.nrmL2 lam (perpL2 lam u) ^ 2 / m ^ 2
      = W * (1 / m ^ 2) * (24 / 5 * Graph.nrmL2 lam (perpL2 lam u) ^ 2) by ring]
  rw [show W * ((32 / 31) ^ 4 / m ^ 2) * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2
      = W * (1 / m ^ 2) * ((32 / 31) ^ 4 * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h6 : ((32:ℝ) / 31) ^ 4 ≤ 6 / 5 := by norm_num
  have h7 := sq_nonneg (Graph.nrmL2 lam (Aop K lam (perpL2 lam u)))
  nlinarith
/-- The real arithmetic closing *(d)* (`proofs.tex:1088`): from `0 < m ≤ Πu_k ≤ m_∞`,
`m_∞² ≤ (Πu_k)² + (13/10)‖ξ‖²` and `‖ξ‖ ≤ ε₀m` with `ε₀ ≤ 1/32`, the gap is at most `‖ξ‖²/m`
and `‖ξ‖ + (m_∞ − Πu_k) ≤ (9/8)‖ξ‖`. -/
theorem limit_arith {mk minf m ξ e0 : ℝ} (hm : 0 < m) (hmk : m ≤ mk) (hkinf : mk ≤ minf)
    (hsq : minf ^ 2 ≤ mk ^ 2 + 13 / 10 * ξ ^ 2) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ e0 * m)
    (he1 : e0 ≤ 1 / 32) :
    minf - mk ≤ ξ ^ 2 / m ∧ ξ + (minf - mk) ≤ 9 / 8 * ξ := by
  have hgap0 : 0 ≤ minf - mk := sub_nonneg.mpr hkinf
  have hgap : (minf - mk) * m ≤ 13 / 20 * ξ ^ 2 := by
    have h1 : (minf - mk) * (2 * m) ≤ (minf - mk) * (minf + mk) :=
      mul_le_mul_of_nonneg_left (by linarith) hgap0
    nlinarith only [h1, hsq]
  have hξ2 : 0 ≤ ξ ^ 2 := sq_nonneg ξ
  constructor
  · rw [le_div_iff₀ hm]; linarith only [hgap, hξ2]
  · have h1 : (minf - mk) * m ≤ 13 / 20 * (e0 * m) * ξ := by
      have : ξ ^ 2 ≤ (e0 * m) * ξ := by nlinarith only [hξ, hξ0]
      linarith only [hgap, this]
    have h2 : minf - mk ≤ 13 / 20 * e0 * ξ := by
      have : (minf - mk) * m ≤ (13 / 20 * e0 * ξ) * m := by linarith only [h1]
      exact le_of_mul_le_mul_right this hm
    have h3 : 13 / 20 * e0 * ξ ≤ 1 / 8 * ξ := by nlinarith only [he1, hξ0]
    linarith only [h2, h3]

/-- `‖u − c‖ ≤ ‖u − Πu‖ + |Πu − c|`. -/
theorem nrmL2_sub_const_le {lam u : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1)
    (c : ℝ) :
    Graph.nrmL2 lam (fun x => u x - c)
      ≤ Graph.nrmL2 lam (perpL2 lam u) + |Graph.meanL2 lam u - c| := by
  have hsplit : (fun x => u x - c)
      = fun x => perpL2 lam u x + (fun _ => Graph.meanL2 lam u - c) x := by
    funext x; rw [perpL2_apply]; ring
  rw [hsplit]
  refine le_trans (nrmL2_add_le hnn _ _) ?_
  rw [nrmL2_const htot]

/-- **The estimates of *(d)* at one `k ≥ k₀`** (`proofs.tex:1080–1088`), from the entry bound, the
monotone mass, the non-increasing `‖u‖² + 2γ𝓛` and `γ ≤ m²/(32‖w‖_{L^∞})`. -/
theorem past_bound {K : V → V → ℝ} {lam wf : V → ℝ} {uk : ℕ → V → ℝ}
    {lamMin W γ m e0 : ℝ} {k : ℕ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hW : ∀ x, wf x ≤ W) (hW0 : 0 < W) (hγ : 0 ≤ γ) (hmpos : 0 < m)
    (he1 : e0 ≤ 1 / 32) (hCe : Cinf lamMin * e0 ≤ 1 / 32)
    (hmono : Monotone fun j => Graph.meanL2 lam (uk j))
    (hbdd : BddAbove (Set.range fun j => Graph.meanL2 lam (uk j)))
    (hmk : m ≤ Graph.meanL2 lam (uk k))
    (hr32 : ∀ x, |ratio K lam (uk k) x - 1| ≤ 1 / 32)
    (hξm : Graph.nrmL2 lam (perpL2 lam (uk k)) ≤ e0 * m) (hγW : γ * (32 * W) ≤ m ^ 2)
    (hsq : ∀ j, k ≤ j → Graph.meanL2 lam (uk j) ^ 2
      ≤ Graph.meanL2 lam (uk k) ^ 2 + Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2
        + 2 * γ * lossVal lam wf logSq (ratio K lam (uk k))) :
    (⨆ j, Graph.meanL2 lam (uk j)) - Graph.meanL2 lam (uk k)
        ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2 / m
      ∧ Graph.nrmL2 lam (fun x => uk k x - ⨆ j, Graph.meanL2 lam (uk j))
        ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)) := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  set ξ := Graph.nrmL2 lam (perpL2 lam (uk k)) with hξdef
  set mk := Graph.meanL2 lam (uk k) with hmkdef
  set minf := ⨆ j, Graph.meanL2 lam (uk j) with hminfdef
  have hξ0 : 0 ≤ ξ := Graph.nrmL2_nonneg _ _
  have hu31 : ∀ x, 31 / 32 * m ≤ uk k x := by
    intro x
    have h1 := abs_le_Cinf_mul_nrmL2 hlmin0 hlmin (perpL2 lam (uk k)) x
    have h2 : Cinf lamMin * ξ ≤ m / 32 := by
      have h3 := mul_le_mul_of_nonneg_left hξm (Cinf_pos hlmin0).le
      have h4 : Cinf lamMin * (e0 * m) ≤ m / 32 := by
        have := mul_le_mul_of_nonneg_right hCe hmpos.le
        linarith only [this]
      linarith only [h3, h4]
    have h3 : perpL2 lam (uk k) x = uk k x - mk := perpL2_apply lam (uk k) x
    have := neg_abs_le (perpL2 lam (uk k) x)
    linarith only [h1, h2, h3, this, hmk]
  have hL := loss_le_perp_sq hKM hinv hlam hW hW0.le hmpos hu31 hr32
  have h2γL : 2 * γ * lossVal lam wf logSq (ratio K lam (uk k)) ≤ 3 / 10 * ξ ^ 2 := by
    have hmid : 2 * γ * (24 / 5 * W * ξ ^ 2 / m ^ 2) ≤ 3 / 10 * ξ ^ 2 := by
      rw [show 2 * γ * (24 / 5 * W * ξ ^ 2 / m ^ 2)
          = (γ * (32 * W)) * (3 / 10 * ξ ^ 2) / m ^ 2 by ring]
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hγW (by positivity : (0:ℝ) ≤ 3 / 10 * ξ ^ 2)
      linarith only [this]
    exact le_trans (mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) hγ)) hmid
  have hmkpos : 0 < mk := lt_of_lt_of_le hmpos hmk
  have hjS : ∀ j, Graph.meanL2 lam (uk j) ≤ Real.sqrt (mk ^ 2 + 13 / 10 * ξ ^ 2) := by
    intro j
    rcases le_total k j with hkj | hjk
    · have h6 : Graph.meanL2 lam (uk j) ^ 2 ≤ mk ^ 2 + 13 / 10 * ξ ^ 2 := by
        have := hsq j hkj
        linarith only [this, h2γL]
      exact le_trans (le_abs_self _) (Real.abs_le_sqrt h6)
    · refine le_trans (hmono hjk) (Real.le_sqrt_of_sq_le ?_)
      linarith only [sq_nonneg ξ]
  have hle_minf : mk ≤ minf := le_ciSup hbdd k
  have hminf2 : minf ^ 2 ≤ mk ^ 2 + 13 / 10 * ξ ^ 2 := by
    have h0 : 0 ≤ minf := le_trans hmkpos.le hle_minf
    have := pow_le_pow_left₀ h0 (ciSup_le hjS) 2
    rwa [Real.sq_sqrt (by positivity)] at this
  obtain ⟨hg1, hg2⟩ := limit_arith hmpos hmk hle_minf hminf2 hξ0 hξm he1
  refine ⟨hg1, le_trans (nrmL2_sub_const_le hnn htot minf) ?_⟩
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle_minf)]
  exact hg2

/-- **`theo:training_speed_full`, assertions *3(c)* (the bounds on `Πu_{k₀}`) and *3(d)*** (`proofs.tex:1029–1030`, proof
`:1079–1088`): `Πu_k` increases to some `m_∞ ≤ √2‖u₀‖`, `m_∞λ` is balanced, and for `k ≥ k₀(γ)`,
`m_∞ − Πu_k ≤ ‖u_k − Πu_k‖²/Πu_{k₀}` and `‖u_k − m_∞‖ ≤ (9/8)‖u_k − Πu_k‖`; moreover
`‖u_k − m_∞‖ → 0`, the convergence the item's header announces. -/
theorem traj_d {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin pmin wmin W γ Bhat M3 : ℝ}
    {uk : ℕ → V → ℝ}
    (hKM : Core.IsMarkov K) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hW : ∀ x, wf x ≤ W)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ : 0 < γ)
    (hγb : γ * b3 W (uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))
      (Graph.meanL2 lam (uk 0))) (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))
      ≤ 1)
    (hγL : 2 * γ * lossVal lam wf logSq (ratio K lam (uk 0)) ≤ Graph.nrmL2 lam (uk 0) ^ 2)
    (hγ0 : γ ≤ gamma0At M3 wmin W Bhat * Graph.meanL2 lam (uk 0) ^ 2)
    (hM3 : 24 ≤ M3) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f)) :
    Graph.meanL2 lam (uk 0) ≤ Graph.meanL2 lam (uk ⌈k0real γ (kappa wmin lamMin
        (Graph.nrmL2 lam (uk 0)) W (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))))
        lamMin wmin (delta1 (eps0At M3 wmin W Bhat lamMin) (Graph.meanL2 lam (uk 0)) Bhat
          (Graph.nrmL2 lam (uk 0)))⌉₊)
      ∧ Graph.meanL2 lam (uk ⌈k0real γ (kappa wmin lamMin
        (Graph.nrmL2 lam (uk 0)) W (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0)))))
        lamMin wmin (delta1 (eps0At M3 wmin W Bhat lamMin) (Graph.meanL2 lam (uk 0)) Bhat
          (Graph.nrmL2 lam (uk 0)))⌉₊) ≤ Real.sqrt 2 * Graph.nrmL2 lam (uk 0)
      ∧ Monotone (fun k => Graph.meanL2 lam (uk k))
      ∧ ∃ minf : ℝ, Filter.Tendsto (fun k => Graph.meanL2 lam (uk k)) Filter.atTop (nhds minf)
        ∧ minf ≤ Real.sqrt 2 * Graph.nrmL2 lam (uk 0)
        ∧ Balanced K lam (fun _ => minf)
        ∧ (∀ k : ℕ, ⌈k0real γ (kappa wmin lamMin (Graph.nrmL2 lam (uk 0)) W
              (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))) lamMin wmin
              (delta1 (eps0At M3 wmin W Bhat lamMin) (Graph.meanL2 lam (uk 0)) Bhat
                (Graph.nrmL2 lam (uk 0)))⌉₊ ≤ k →
            minf - Graph.meanL2 lam (uk k)
                ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2
                  / Graph.meanL2 lam (uk ⌈k0real γ (kappa wmin lamMin (Graph.nrmL2 lam (uk 0)) W
                    (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))) lamMin wmin
                    (delta1 (eps0At M3 wmin W Bhat lamMin) (Graph.meanL2 lam (uk 0)) Bhat
                      (Graph.nrmL2 lam (uk 0)))⌉₊)
              ∧ Graph.nrmL2 lam (fun x => uk k x - minf)
                ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)))
        ∧ Filter.Tendsto (fun k => Graph.nrmL2 lam (fun x => uk k x - minf)) Filter.atTop
            (nhds 0) := by
  haveI := nonempty_of_total htot
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hWpos : 0 < W := lt_of_lt_of_le hwmin (le_trans (hw x0) (hW x0))
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hB : 0 < Bhat := lt_of_lt_of_le zero_lt_one hB1
  have hM30 : 0 ≤ M3 := by linarith
  have he0 := eps0At_pos (Bhat := Bhat) hM30 hwmin hWpos hB hlmin0
  have he1 := eps0At_le (Bhat := Bhat) hM30 hwmin hWpos hB hlmin0 hlmin htot
  have hCe := Cinf_mul_eps0At_le (Bhat := Bhat) hM30 hwmin hWpos hlmin0
  have hentry := traj_entry hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ hγb hγL hB1 hcoer he0 he1
  have hreg := traj_region hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb
  have ha := traj_a hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb hγL
  have hnrm := traj_nrm_le hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ.le hγb hγL
  have hc := traj_c hKM hinv hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hW hu0
    hstep hγ hγb hγL hγ0 hM3 hB1 hcoer
  generalize hk0def : ⌈k0real γ (kappa wmin lamMin (Graph.nrmL2 lam (uk 0)) W
        (ratioCap lamMin wmin (lossVal lam wf logSq (ratio K lam (uk 0))))) lamMin wmin
        (delta1 (eps0At M3 wmin W Bhat lamMin) (Graph.meanL2 lam (uk 0)) Bhat
          (Graph.nrmL2 lam (uk 0)))⌉₊ = k0 at hentry hc ⊢
  generalize hL0def : lossVal lam wf logSq (ratio K lam (uk 0)) = L0 at hγb hγL
  generalize hm0def : Graph.meanL2 lam (uk 0) = m0 at hentry hγb hγ0 ⊢
  generalize he0def : eps0At M3 wmin W Bhat lamMin = e0 at he0 he1 hCe hentry
  have hm0pos : 0 < m0 := hm0def ▸ (hnrm 0).2.2.2
  have hmU : m0 ≤ Graph.nrmL2 lam (uk 0) := hm0def ▸ (hnrm 0).2.2.1
  have hmm0 : m0 ≤ Graph.meanL2 lam (uk k0) := hm0def ▸ (hreg k0).2.2.1
  set m := Graph.meanL2 lam (uk k0) with hmdef
  have hmpos : 0 < m := lt_of_lt_of_le hm0pos hmm0
  have hmono : Monotone (fun k => Graph.meanL2 lam (uk k)) :=
    monotone_nat_of_le_succ fun k => (ha k).2.2.1
  have hmass_le : ∀ k, Graph.meanL2 lam (uk k) ≤ Real.sqrt 2 * Graph.nrmL2 lam (uk 0) :=
    fun k => le_trans (hnrm k).2.2.1 (hnrm k).2.1
  -- `γ ≤ m²/(32‖w‖)`
  have humin_le : uMin V lamMin pmin wmin L0 m0 ≤ m0 := by
    have hlmin1 : lamMin ≤ 1 := le_trans (hlmin x0) (by
      rw [← htot]; exact Finset.single_le_sum (f := lam) (fun i _ => hnn i) (Finset.mem_univ x0))
    have hc1 := edgeDrop_le_one (wmin := wmin) (L0 := L0) hlmin1 hpmin0 hpmin1
    have hc0 := (edgeDrop_pos (wmin := wmin) (L0 := L0) hlmin0 hpmin0).le
    simp only [uMin]
    calc m0 * edgeDrop lamMin pmin wmin L0 ^ (Fintype.card V - 1) ≤ m0 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hc0 hc1) hm0pos.le
      _ = m0 := mul_one _
  have humin_pos : 0 < uMin V lamMin pmin wmin L0 m0 := uMin_pos hlmin0 hpmin0 hm0pos
  have hγW : γ * (32 * W) ≤ m ^ 2 := by
    have hbr := (b3_bracket_ge (ratioCap_pos lamMin wmin L0).le).2.2
    generalize humdef : uMin V lamMin pmin wmin L0 m0 = um at humin_le humin_pos hγb
    have hb3 : 32 * W / um ^ 2 ≤ b3 W um (ratioCap lamMin wmin L0) := by
      rw [b3, mul_assoc (4 * W / um ^ 2), div_mul_eq_mul_div]
      rw [div_le_div_iff_of_pos_right (by positivity)]
      have := mul_le_mul_of_nonneg_left hbr (by positivity : (0:ℝ) ≤ 4 * W)
      linarith only [this]
    have h1 : γ * (32 * W / um ^ 2) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hb3 hγ.le) hγb
    have h2 : γ * (32 * W) ≤ um ^ 2 := by
      rw [mul_div_assoc'] at h1
      rwa [div_le_one (by positivity)] at h1
    have h3 : um ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ humin_pos.le (le_trans humin_le hmm0) 2
    linarith only [h2, h3]
  -- the limit
  have hbdd : BddAbove (Set.range fun k => Graph.meanL2 lam (uk k)) :=
    ⟨Real.sqrt 2 * Graph.nrmL2 lam (uk 0), by rintro _ ⟨k, rfl⟩; exact hmass_le k⟩
  -- `‖u‖² + 2γ𝓛` is non-increasing
  have hΦ : ∀ i j, i ≤ j →
      Graph.nrmL2 lam (uk j) ^ 2 + 2 * γ * lossVal lam wf logSq (ratio K lam (uk j))
        ≤ Graph.nrmL2 lam (uk i) ^ 2 + 2 * γ * lossVal lam wf logSq (ratio K lam (uk i)) := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | step _ ih =>
      rename_i n _
      obtain ⟨-, hdesc, -, hnorm, -⟩ := ha n
      have h1 : 2 * γ * lossVal lam wf logSq (ratio K lam (uk (n + 1)))
          ≤ 2 * γ * (lossVal lam wf logSq (ratio K lam (uk n))
            - γ / 2 * Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk n)) ^ 2) :=
        mul_le_mul_of_nonneg_left hdesc (by positivity)
      linarith only [h1, hnorm, ih]
  have hpast : ∀ k, k0 ≤ k →
      (⨆ j, Graph.meanL2 lam (uk j)) - Graph.meanL2 lam (uk k)
          ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2 / m
        ∧ Graph.nrmL2 lam (fun x => uk k x - ⨆ j, Graph.meanL2 lam (uk j))
          ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)) := by
    intro k hk
    obtain ⟨hratio, hperp, -⟩ := hentry k hk
    have hr32 : ∀ x, |ratio K lam (uk k) x - 1| ≤ 1 / 32 := fun x =>
      le_trans (hratio x) (le_trans (delta1_le he0.le hm0pos hB1 hmU) he1)
    have hξm : Graph.nrmL2 lam (perpL2 lam (uk k)) ≤ e0 * m :=
      le_trans hperp (mul_le_mul_of_nonneg_left hmm0 he0.le)
    refine past_bound hKM hinv hlam htot hlmin hlmin0 hW hWpos hγ.le hmpos he1 hCe hmono hbdd
      (hmono hk) hr32 hξm hγW (fun j hkj => ?_)
    have h1 := hΦ k j hkj
    have h2 := nrmL2_sq_eq_mean_sq_add_perp hnn htot (uk j)
    have h3 := nrmL2_sq_eq_mean_sq_add_perp hnn htot (uk k)
    have h4 : 0 ≤ 2 * γ * lossVal lam wf logSq (ratio K lam (uk j)) :=
      mul_nonneg (by positivity) (lossVal_nonneg hnn (fun x => le_trans hwmin.le (hw x)))
    have h5 := sq_nonneg (Graph.nrmL2 lam (perpL2 lam (uk j)))
    linarith only [h1, h2, h3, h4, h5]
  -- geometric decay of `‖u_k − Πu_k‖` past `k₀`
  set c := γ * rhoL 2 wmin Bhat / (4 * m ^ 2) with hcdef
  have hc0 : 0 < c := by
    have := rhoL_pos (g2 := 2) (wmin := wmin) (by positivity) hB; positivity
  have hc1 : c ≤ 1 / 64 := by
    have hrho : rhoL 2 wmin Bhat ≤ 2 * W := by
      rw [rhoL, div_le_iff₀ (by positivity)]
      have hB2 : 1 ≤ Bhat ^ 2 := by nlinarith only [hB1]
      have hwW : wmin ≤ W := le_trans (hw x0) (hW x0)
      nlinarith only [hB2, hwW, hwmin]
    rw [hcdef, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hrho hγ.le
    linarith only [this, hγW]
  have hgeo : ∀ j, Graph.nrmL2 lam (perpL2 lam (uk (j + k0)))
      ≤ (1 - c) ^ j * Graph.nrmL2 lam (perpL2 lam (uk k0)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := hc (j + k0) (by omega)
      rw [show j + 1 + k0 = j + k0 + 1 by ring, pow_succ]
      calc Graph.nrmL2 lam (perpL2 lam (uk (j + k0 + 1)))
          ≤ (1 - c) * Graph.nrmL2 lam (perpL2 lam (uk (j + k0))) := h
        _ ≤ (1 - c) * ((1 - c) ^ j * Graph.nrmL2 lam (perpL2 lam (uk k0))) :=
            mul_le_mul_of_nonneg_left ih (by linarith only [hc1])
        _ = _ := by ring
  have hlim : Filter.Tendsto (fun k => Graph.nrmL2 lam (fun x => uk k x - ⨆ j, Graph.meanL2 lam (uk j)))
      Filter.atTop (nhds 0) := by
    rw [← Filter.tendsto_add_atTop_iff_nat k0]
    refine squeeze_zero (fun _ => Graph.nrmL2_nonneg _ _) (fun j => ?_) (g := fun j =>
      9 / 8 * ((1 - c) ^ j * Graph.nrmL2 lam (perpL2 lam (uk k0)))) ?_
    · exact le_trans (hpast (j + k0) (by omega)).2
        (mul_le_mul_of_nonneg_left (hgeo j) (by norm_num))
    · have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - c) (by linarith only [hc1])
        (by linarith only [hc0])
      simpa using (this.mul_const (Graph.nrmL2 lam (perpL2 lam (uk k0)))).const_mul (9 / 8)
  exact ⟨hmm0, hmass_le k0, hmono, ⨆ j, Graph.meanL2 lam (uk j), tendsto_atTop_ciSup hmono hbdd,
    ciSup_le hmass_le, balanced_const hinv _, hpast, hlim⟩


end Trajectory

/-! ### The step bound `γ_*`, the entry index `k₀(γ)`, and the necessity of an initialization-dependent step -/

section Constants

/-- **`theo:training_speed_full`*(3)*: `γ_* := min(1/b₃, (‖u₀‖²/2)𝓛(μ₀)^{−1}, γ₀m₀²)`** (`proofs.tex:1051`), with the paper's
convention `𝓛(μ₀)^{−1} := +∞` at a balanced start read as dropping the middle entry. -/
noncomputable def gammaStar (b3v U0 L0 γ0 m0 : ℝ) : ℝ :=
  if L0 = 0 then min (1 / b3v) (γ0 * m0 ^ 2)
  else min (min (1 / b3v) (U0 ^ 2 / 2 * L0⁻¹)) (γ0 * m0 ^ 2)

theorem gammaStar_pos {b3v U0 L0 γ0 m0 : ℝ} (hb : 0 < b3v) (hU0 : 0 < U0) (hL0 : 0 ≤ L0)
    (hγ0 : 0 < γ0) (hm0 : 0 < m0) : 0 < gammaStar b3v U0 L0 γ0 m0 := by
  unfold gammaStar
  split_ifs with h
  · exact lt_min (by positivity) (by positivity)
  · have : 0 < L0 := lt_of_le_of_ne hL0 (Ne.symm h)
    exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)

/-- What `0 ≤ γ ≤ γ_*` delivers: `γb₃ ≤ 1`, `2γ𝓛(μ₀) ≤ ‖u₀‖²` and `γ ≤ γ₀m₀²`. -/
theorem le_gammaStar {b3v U0 L0 γ0 m0 γ : ℝ} (hb : 0 < b3v) (hL0 : 0 ≤ L0)
    (h : γ ≤ gammaStar b3v U0 L0 γ0 m0) :
    γ * b3v ≤ 1 ∧ 2 * γ * L0 ≤ U0 ^ 2 ∧ γ ≤ γ0 * m0 ^ 2 := by
  unfold gammaStar at h
  split_ifs at h with hz
  · refine ⟨?_, ?_, le_trans h (min_le_right _ _)⟩
    · have := le_trans h (min_le_left _ _)
      rw [le_div_iff₀ hb] at this; linarith
    · rw [hz]; nlinarith [sq_nonneg U0]
  · have hL : 0 < L0 := lt_of_le_of_ne hL0 (Ne.symm hz)
    refine ⟨?_, ?_, le_trans h (min_le_right _ _)⟩
    · have := le_trans (le_trans h (min_le_left _ _)) (min_le_left _ _)
      rw [le_div_iff₀ hb] at this; linarith
    · have := le_trans (le_trans h (min_le_left _ _)) (min_le_right _ _)
      have h2 : U0 ^ 2 / 2 * L0⁻¹ = U0 ^ 2 / (2 * L0) := by field_simp
      rw [h2, le_div_iff₀ (by positivity)] at this
      linarith

/-- **`theo:training_speed_full`*(3)*: `k₀(γ) := ⌈32‖u₀‖⁴‖w‖²_{L^∞}M²σ_*²/(γw_min³λ_min³ε₀²m₀²)⌉`** (`proofs.tex:1056`), the printed
closed form. -/
noncomputable def k0 (γ U0 W M sigStar wmin lamMin e0 m0 : ℝ) : ℕ :=
  ⌈32 * U0 ^ 4 * W ^ 2 * M ^ 2 * sigStar ^ 2 / (γ * wmin ^ 3 * lamMin ^ 3 * e0 ^ 2 * m0 ^ 2)⌉₊

/-- **The two forms of `k₀(γ)` agree** (`proofs.tex:1056`, "the last equality by
`B̂_σ = σ_*λ_min^{−1/2}`"). -/
theorem k0real_eq {γ U0 W M sigStar wmin lamMin e0 m0 : ℝ} (hγ : 0 < γ) (hU0 : 0 < U0)
    (hW : 0 < W) (hM : 0 < M) (hsig : 0 < sigStar) (hwmin : 0 < wmin) (hlmin0 : 0 < lamMin)
    (he0 : 0 < e0) (hm0 : 0 < m0) :
    k0real γ (kappa wmin lamMin U0 W M) lamMin wmin
        (delta1 e0 m0 (sigStar / Real.sqrt lamMin) U0)
      = 32 * U0 ^ 4 * W ^ 2 * M ^ 2 * sigStar ^ 2
          / (γ * wmin ^ 3 * lamMin ^ 3 * e0 ^ 2 * m0 ^ 2) := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ lamMin = s ^ 2 :=
    ⟨Real.sqrt lamMin, Real.sqrt_pos.mpr hlmin0, (Real.sq_sqrt hlmin0.le).symm⟩
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := by positivity
  simp only [k0real, kappa, delta1, Real.sqrt_sq hs0.le]
  field_simp
  rw [h2]
  ring

end Constants

section Necessity

variable {V : Type*} [Fintype V]

/-- **`theo:training_speed_full`*(3)*, no step bound independent of the initialization exists** (`proofs.tex:1032`, proof
`:1090`): for every `γ > 0` and every positive non-balanced `u₀`, there is a state `y` at which
`su₀ − γD(su₀)` is negative for every small enough `s > 0`. -/
theorem no_uniform_step {K : V → V → ℝ} {lam wf u0 : V → ℝ} {γ : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x)
    (hwpos : ∀ x, 0 < wf x) (hu0 : ∀ x, 0 < u0 x) (hbal : ¬ Balanced K lam u0) (hγ : 0 < γ) :
    ∃ y : V, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s < s0 →
      s * u0 y - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (fun x => s * u0 x) y < 0 := by
  set D := lossGrad K lam (fun z => lam z * wf z) logSqDeriv u0 with hDdef
  have hmass := no_distant_equilibrium_one hinv hKnn hlam hu0 (w := fun x => wf x / u0 x)
    (fun x => div_pos (hwpos x) (hu0 x)) logSqDeriv_strictlyUnimodal
  have hneg : Graph.meanL2 lam D < 0 := by
    have h1 : Graph.meanL2 lam D = gradMass K lam u0 (fun x => wf x / u0 x) logSqDeriv := by
      rw [hDdef, lossGrad_of_weight hlam]; rfl
    rw [h1]
    exact lt_of_le_of_ne hmass.2.1 (fun h => hbal (hmass.2.2.mp h))
  have hexists : ∃ y, 0 < D y := by
    by_contra hc
    push Not at hc
    have horth : Graph.ipL2 lam D u0 = 0 := ipL2_lossGrad_self _ _ hlam hu0
    have hterm : ∀ x, lam x * (D x * u0 x) = 0 := by
      have hle : ∀ x ∈ Finset.univ, lam x * (D x * u0 x) ≤ 0 := fun x _ =>
        mul_nonpos_of_nonneg_of_nonpos (hlam x).le (mul_nonpos_of_nonpos_of_nonneg (hc x) (hu0 x).le)
      have := (Finset.sum_eq_zero_iff_of_nonpos hle).mp horth
      exact fun x => this x (Finset.mem_univ x)
    have hD0 : ∀ x, D x = 0 := by
      intro x
      have h := hterm x
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 (hlam x).ne'
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact h2
        · exact absurd h2 (hu0 x).ne'
    have : Graph.meanL2 lam D = 0 := by
      simp only [Graph.meanL2, hD0, mul_zero, Finset.sum_const_zero]
    linarith
  obtain ⟨y, hy⟩ := hexists
  refine ⟨y, Real.sqrt (γ * D y / u0 y), Real.sqrt_pos.mpr (by have := hu0 y; positivity),
    fun s hs hss => ?_⟩
  have hsm : lossGrad K lam (fun z => lam z * wf z) logSqDeriv (fun x => s * u0 x) y = s⁻¹ * D y := by
    rw [lossGrad_smul hs.ne']
  rw [hsm]
  have hs2 : s ^ 2 < γ * D y / u0 y := by
    have h0 : 0 ≤ γ * D y / u0 y := by have := hu0 y; positivity
    calc s ^ 2 < Real.sqrt (γ * D y / u0 y) ^ 2 := pow_lt_pow_left₀ hss hs.le (by norm_num)
      _ = _ := Real.sq_sqrt h0
  rw [lt_div_iff₀ (hu0 y)] at hs2
  have : s * u0 y - γ * (s⁻¹ * D y) = (s ^ 2 * u0 y - γ * D y) / s := by field_simp
  rw [this]
  exact div_neg_of_neg_of_pos (by linarith) hs

end Necessity


/-! ### The theorem: item *3* of `theo:training_speed_full` -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`theo:training_speed_full`, item *3*, gradient descent with a step chosen from the
initialization** (`proofs.tex:1021–1033`, proof `:1048–1090`).

On the loop closure of a finite path-connected marked graph with a backward policy positive on its
edges, `λ` its invariant probability, `g = (log x)²`, `ν = wλ` with `w_min ≤ w ≤ ‖w‖_{L^∞}`, and a
floor `p_min ∈ (0,1]` on the positive transition probabilities: from every positive `u₀`, for every
step `0 < γ ≤ γ_*`, the descent `u_{k+1} = u_k − γD(u_k)` satisfies *(a)*–*(d)*, with every constant
the printed formula — `u_min`, `b₃`, `γ_*`, `κ`, `k₀(γ)`, `ϱ_σ`, and `ε₀`, `γ₀` those of
`theo:local_convergence_full` at `a = 1/2`, `Γ₃ = 48 + 32 ln 2`, `B̂_σ`, `C_∞ = λ_min^{−1/2}`. -/
theorem training_speed_gd {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH wf : V → ℝ} {wmin wsup pmin γ : ℝ} {uk : ℕ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (hpmin : ∀ y z : V, 0 < B.phat y z → pmin ≤ B.phat y z)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ : 0 < γ)
    (hγs : γ ≤ gammaStar
      (b3 wsup (uMin V (Graph.minOver G lam) pmin wmin
          (lossVal lam wf logSq (ratio B.phat lam (uk 0))) (Graph.meanL2 lam (uk 0)))
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0)))))
      (Graph.nrmL2 lam (uk 0)) (lossVal lam wf logSq (ratio B.phat lam (uk 0)))
      (gamma0At Gamma3Val wmin wsup (BhatSigma G uH lam)) (Graph.meanL2 lam (uk 0))) :
    -- (a)
    (∀ k, (∀ x, uMin V (Graph.minOver G lam) pmin wmin
          (lossVal lam wf logSq (ratio B.phat lam (uk 0))) (Graph.meanL2 lam (uk 0)) ≤ uk k x)
      ∧ lossVal lam wf logSq (ratio B.phat lam (uk (k + 1)))
          ≤ lossVal lam wf logSq (ratio B.phat lam (uk k))
            - γ / 2 * Graph.nrmL2 lam
                (lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2
      ∧ Graph.meanL2 lam (uk k) ≤ Graph.meanL2 lam (uk (k + 1))
      ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2
          = Graph.nrmL2 lam (uk k) ^ 2
            + γ ^ 2 * Graph.nrmL2 lam
                (lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2
      ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2 ≤ 2 * Graph.nrmL2 lam (uk 0) ^ 2)
    -- (b)
    ∧ (∀ k : ℕ, lossVal lam wf logSq (ratio B.phat lam (uk k))
      ≤ ((lossVal lam wf logSq (ratio B.phat lam (uk 0)))⁻¹
          + k * γ * (wmin * Real.sqrt (Graph.minOver G lam) / (Graph.nrmL2 lam (uk 0) * wsup
              * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam (uk 0))
                  / (wmin * Graph.minOver G lam))))) ^ 2 / 4)⁻¹)
    -- (c)
    ∧ Graph.meanL2 lam (uk 0)
        ≤ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam (uk 0)) wsup
            (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
            (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
            (Graph.meanL2 lam (uk 0))))
    ∧ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam (uk 0)) wsup
            (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
            (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
            (Graph.meanL2 lam (uk 0))))
        ≤ Real.sqrt 2 * Graph.nrmL2 lam (uk 0)
    ∧ (∀ k : ℕ, k0 γ (Graph.nrmL2 lam (uk 0)) wsup
            (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
            (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
            (Graph.meanL2 lam (uk 0)) ≤ k →
        Graph.nrmL2 lam (fun x => uk k x / Graph.meanL2 lam (uk k) - 1)
            ≤ eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam)
          ∧ Graph.nrmL2 lam (perpL2 lam (uk (k + 1)))
            ≤ (1 - γ * rhoSigma 2 wmin (Graph.minOver G lam) (Graph.sigmaStar G uH)
                / (4 * Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam (uk 0)) wsup
                  (ratioCap (Graph.minOver G lam) wmin
                    (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
                  (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
                  (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
                  (Graph.meanL2 lam (uk 0)))) ^ 2))
              * Graph.nrmL2 lam (perpL2 lam (uk k)))
    -- (d)
    ∧ Monotone (fun k => Graph.meanL2 lam (uk k))
    ∧ ∃ minf : ℝ, Filter.Tendsto (fun k => Graph.meanL2 lam (uk k)) Filter.atTop (nhds minf)
        ∧ minf ≤ Real.sqrt 2 * Graph.nrmL2 lam (uk 0)
        ∧ Balanced B.phat lam (fun _ => minf)
        ∧ (∀ k : ℕ, k0 γ (Graph.nrmL2 lam (uk 0)) wsup
              (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
              (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
              (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
              (Graph.meanL2 lam (uk 0)) ≤ k →
            minf - Graph.meanL2 lam (uk k)
                ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2
                  / Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam (uk 0)) wsup
                    (ratioCap (Graph.minOver G lam) wmin
                      (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
                    (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
                    (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
                    (Graph.meanL2 lam (uk 0))))
              ∧ Graph.nrmL2 lam (fun x => uk k x - minf)
                ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)))
        ∧ Filter.Tendsto (fun k => Graph.nrmL2 lam (fun x => uk k x - minf)) Filter.atTop
            (nhds 0) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hp x).le
  have htot : ∑ x, lam x = 1 := hl.total
  have hinv : Invariant B.phat lam := hl.inv
  have hKM : Core.IsMarkov B.phat := ⟨B.phat_nonneg, B.phat_row_sum⟩
  have hlmin : ∀ x, Graph.minOver G lam ≤ lam x := fun x => Graph.minOver_le lam x
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hcross := crossingFloor_phat hpc hpos hpmin
  haveI := nonempty_of_total htot
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hWpos : 0 < wsup := lt_of_lt_of_le hwmin (le_trans (hw x0) (hwsup x0))
  have hB1 : 1 ≤ BhatSigma G uH lam := one_le_BhatSigma hpc hpos hl hhit
  have hcoer := hcoer_of_graph hpc hpos hl hhit
  have hm0 : 0 < Graph.meanL2 lam (uk 0) :=
    Finset.sum_pos (fun x _ => mul_pos (hp x) (hu0 x)) Finset.univ_nonempty
  have hL0 : 0 ≤ lossVal lam wf logSq (ratio B.phat lam (uk 0)) :=
    lossVal_nonneg hnn (fun x => le_trans hwmin.le (hw x))
  have hb3 : 0 < b3 wsup (uMin V (Graph.minOver G lam) pmin wmin
          (lossVal lam wf logSq (ratio B.phat lam (uk 0))) (Graph.meanL2 lam (uk 0)))
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0)))) := by
    have hum := uMin_pos (V := V) (wmin := wmin)
      (L0 := lossVal lam wf logSq (ratio B.phat lam (uk 0))) hlmin0 hpmin0 hm0
    have hbr := (b3_bracket_ge (ratioCap_pos (Graph.minOver G lam) wmin
      (lossVal lam wf logSq (ratio B.phat lam (uk 0)))).le).2.2
    rw [b3, mul_assoc]
    have : (0:ℝ) < (1 + Real.exp (Mp (ratioCap (Graph.minOver G lam) wmin
        (lossVal lam wf logSq (ratio B.phat lam (uk 0)))))) *
        (b2 (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
          * (1 + Real.exp (Mp (ratioCap (Graph.minOver G lam) wmin
            (lossVal lam wf logSq (ratio B.phat lam (uk 0)))))) + 2 * b1 (ratioCap
              (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))) := by
      linarith
    positivity
  obtain ⟨hγb, hγL, hγ0⟩ := le_gammaStar hb3 hL0 hγs
  have hk0eq : ⌈k0real γ (kappa wmin (Graph.minOver G lam) (Graph.nrmL2 lam (uk 0)) wsup
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0)))))
        (Graph.minOver G lam) wmin
        (delta1 (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
          (Graph.meanL2 lam (uk 0)) (BhatSigma G uH lam) (Graph.nrmL2 lam (uk 0)))⌉₊
      = k0 γ (Graph.nrmL2 lam (uk 0)) wsup
            (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
            (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
            (Graph.meanL2 lam (uk 0)) := by
    have hU0 : 0 < Graph.nrmL2 lam (uk 0) :=
      lt_of_lt_of_le hm0 (mean_le_nrmL2_iff_const hp htot (fun x => (hu0 x).le)).1
    have hsig : 0 < Graph.sigmaStar G uH := lt_of_lt_of_le zero_lt_one (one_le_sigmaStar hhit)
    rw [k0]
    congr 1
    exact k0real_eq hγ hU0 hWpos (ratioCap_pos _ _ _) hsig hwmin hlmin0
      (eps0At_pos (le_trans (by norm_num) twentyfour_le_Gamma3Val) hwmin hWpos
        (lt_of_lt_of_le zero_lt_one hB1) hlmin0) hm0
  have hrho : rhoL 2 wmin (BhatSigma G uH lam)
      = rhoSigma 2 wmin (Graph.minOver G lam) (Graph.sigmaStar G uH) :=
    rhoL_eq_rhoSigma hlmin0
  have hWpos' : 0 ≤ Gamma3Val := le_trans (by norm_num) twentyfour_le_Gamma3Val
  have ha := traj_a hKM hinv hp htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hwsup hu0
    hstep hγ.le hγb hγL
  have hb := traj_b hKM hinv hp htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hwsup hu0
    hstep hγ.le hγb hγL
  have hentry := traj_entry hKM hinv hp htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hwsup hu0
    hstep hγ hγb hγL hB1 hcoer
    (eps0At_pos hWpos' hwmin hWpos (lt_of_lt_of_le zero_lt_one hB1) hlmin0)
    (eps0At_le hWpos' hwmin hWpos (lt_of_lt_of_le zero_lt_one hB1) hlmin0 hlmin htot)
  have hc := traj_c hKM hinv hp htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hwsup hu0
    hstep hγ hγb hγL hγ0 twentyfour_le_Gamma3Val hB1 hcoer
  have hd := traj_d hKM hinv hp htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hwsup hu0
    hstep hγ hγb hγL hγ0 twentyfour_le_Gamma3Val hB1 hcoer
  rw [hk0eq] at hentry hc hd
  rw [hrho] at hc
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hd
  refine ⟨ha, fun k => ?_, hd1, hd2, fun k hk => ⟨(hentry k hk).2.2, hc k hk⟩, hd3, hd4⟩
  simpa only [kappa, ratioCap] using hb k

end Main


/-! ### The paper's `p_min`, the necessity sentence on the graph, and inhabitation -/

section Inhabit

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`p_min`, the smallest positive transition probability** of a kernel (`proofs.tex:1000`);
`1` if no entry is positive. -/
noncomputable def minPos (K : V → V → ℝ) : ℝ :=
  if h : (Finset.univ.filter fun p : V × V => 0 < K p.1 p.2).Nonempty then
    (Finset.univ.filter fun p : V × V => 0 < K p.1 p.2).inf' h fun p => K p.1 p.2
  else 1

omit [DecidableEq V] in
theorem minPos_pos (K : V → V → ℝ) : 0 < minPos K := by
  unfold minPos
  split_ifs with h
  · obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_inf' h (fun p : V × V => K p.1 p.2)
    rw [heq]
    exact (Finset.mem_filter.mp hp).2
  · exact one_pos

omit [DecidableEq V] in
theorem minPos_le {K : V → V → ℝ} {y z : V} (hyz : 0 < K y z) : minPos K ≤ K y z := by
  have hmem : (y, z) ∈ Finset.univ.filter fun p : V × V => 0 < K p.1 p.2 := by simp [hyz]
  unfold minPos
  rw [dif_pos ⟨(y, z), hmem⟩]
  exact Finset.inf'_le _ hmem

omit [DecidableEq V] in
/-- `p_min ≤ 1` for a Markov kernel on a non-empty state space. -/
theorem minPos_le_one {K : V → V → ℝ} (hK : Core.IsMarkov K) [Nonempty V] : minPos K ≤ 1 := by
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨z, -, hz⟩ : ∃ z ∈ Finset.univ, 0 < K x z := by
    by_contra hc
    push Not at hc
    have : ∑ y, K x y = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (hc y (Finset.mem_univ y)) (hK.nonneg x y)
    rw [hK.row_sum x] at this
    exact one_ne_zero this
  refine le_trans (minPos_le hz) ?_
  rw [← hK.row_sum x]
  exact Finset.single_le_sum (f := K x) (fun i _ => hK.nonneg x i) (Finset.mem_univ z)

/-- **`theo:training_speed_full`*(3)*, the necessity sentence on the paper's setting** (`proofs.tex:1032`): on the loop closure,
for every step `γ > 0` and every non-balanced positive `u₀`, `su₀ − γD(su₀)` leaves the positive
cone for every small enough `s > 0`; no step bound independent of the initialization exists. -/
theorem no_uniform_step_graph {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam wf u0 : V → ℝ} {wmin γ : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u0 x) (hbal : ¬ Balanced B.phat lam u0) (hγ : 0 < γ) :
    ∃ y : V, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s < s0 →
      s * u0 y - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv
        (fun x => s * u0 x) y < 0 :=
  no_uniform_step B.phat_nonneg hl.inv (fun x => hl.pos hpc hpos x)
    (fun x => lt_of_lt_of_le hwmin (hw x)) hu0 hbal hγ

omit [DecidableEq V] in
/-- **The descent sequence exists**: `hstep` is a recursion, and any `u₀` starts one. -/
theorem exists_descent_seq (K : V → V → ℝ) (lam wf u0 : V → ℝ) (γ : ℝ) :
    ∃ uk : ℕ → V → ℝ, uk 0 = u0 ∧ ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad K lam (fun z => lam z * wf z) logSqDeriv (uk k) x :=
  ⟨fun k => Nat.rec u0 (fun _ u x => u x - γ * lossGrad K lam (fun z => lam z * wf z)
      logSqDeriv u x) k, rfl, fun _ => rfl⟩

/-- **The hypotheses of `training_speed_gd` are inhabited** on every instance of its setting and
every positive initialization: `γ_* > 0`, and the descent at `γ = γ_*` is a sequence. -/
theorem training_speed_gd_inhabited {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH wf u0 : V → ℝ} {wmin wsup pmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hpmin0 : 0 < pmin) (hu0 : ∀ x, 0 < u0 x) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ gammaStar
      (b3 wsup (uMin V (Graph.minOver G lam) pmin wmin
          (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0))
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))))
      (Graph.nrmL2 lam u0) (lossVal lam wf logSq (ratio B.phat lam u0))
      (gamma0At Gamma3Val wmin wsup (BhatSigma G uH lam)) (Graph.meanL2 lam u0)
      ∧ ∃ uk : ℕ → V → ℝ, uk 0 = u0 ∧ ∀ k, uk (k + 1) = fun x =>
          uk k x - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k) x := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hp x).le
  haveI := nonempty_of_total hl.total
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hWpos : 0 < wsup := lt_of_lt_of_le hwmin (le_trans (hw x0) (hwsup x0))
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hm0 : 0 < Graph.meanL2 lam u0 :=
    Finset.sum_pos (fun x _ => mul_pos (hp x) (hu0 x)) Finset.univ_nonempty
  have hU0 : 0 < Graph.nrmL2 lam u0 :=
    lt_of_lt_of_le hm0 (mean_le_nrmL2_iff_const hp hl.total (fun x => (hu0 x).le)).1
  have hL0 : 0 ≤ lossVal lam wf logSq (ratio B.phat lam u0) :=
    lossVal_nonneg hnn (fun x => le_trans hwmin.le (hw x))
  have hum := uMin_pos (V := V) (wmin := wmin)
    (L0 := lossVal lam wf logSq (ratio B.phat lam u0)) hlmin0 hpmin0 hm0
  have hbr := (b3_bracket_ge (ratioCap_pos (Graph.minOver G lam) wmin
    (lossVal lam wf logSq (ratio B.phat lam u0))).le).2.2
  have hb3 : 0 < b3 wsup (uMin V (Graph.minOver G lam) pmin wmin
          (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0))
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) := by
    rw [b3, mul_assoc]
    have := lt_of_lt_of_le (by norm_num : (0:ℝ) < 8) hbr
    positivity
  have hB := lt_of_lt_of_le zero_lt_one (one_le_BhatSigma hpc hpos hl hhit)
  have hg := gammaStar_pos hb3 hU0 hL0
    (gamma0At_pos (le_trans (by norm_num) twentyfour_le_Gamma3Val) hwmin hWpos hB) hm0
  exact ⟨_, hg, le_rfl, exists_descent_seq _ _ _ _ _⟩

/-- **Non-vacuity on `rem:cycle_no_stalemate`'s five-vertex cycle** at `p = 1/2`, `w ≡ 1`, from the
over-inflated density `u₀ = uInfl 2`, which is **not** balanced (`r(s₀) = 2`): the setting's
predicates hold, and a step `0 < γ ≤ γ_*` and its descent sequence exist, so
`training_speed_gd` applies to a non-balanced start. -/
theorem cycle_training_speed_gd_nonvacuous :
    ¬ Balanced (Graph.CycleExample.pol (p := 1/2) (by norm_num) (by norm_num)).phat
        (Graph.CycleExample.lam (1/2)) (Graph.CycleExample.uInfl 2)
      ∧ ∃ γ : ℝ, 0 < γ ∧ γ ≤ gammaStar
        (b3 1 (uMin (Fin 5) (Graph.minOver Graph.CycleExample.cyc (Graph.CycleExample.lam (1/2)))
            (minPos (Graph.CycleExample.pol (p := 1/2) (by norm_num) (by norm_num)).phat) 1
            (lossVal (Graph.CycleExample.lam (1/2)) (fun _ => 1) logSq
              (ratio (Graph.CycleExample.pol (p := 1/2) (by norm_num) (by norm_num)).phat
                (Graph.CycleExample.lam (1/2)) (Graph.CycleExample.uInfl 2)))
            (Graph.meanL2 (Graph.CycleExample.lam (1/2)) (Graph.CycleExample.uInfl 2)))
          (ratioCap (Graph.minOver Graph.CycleExample.cyc (Graph.CycleExample.lam (1/2))) 1
            (lossVal (Graph.CycleExample.lam (1/2)) (fun _ => 1) logSq
              (ratio (Graph.CycleExample.pol (p := 1/2) (by norm_num) (by norm_num)).phat
                (Graph.CycleExample.lam (1/2)) (Graph.CycleExample.uInfl 2)))))
        (Graph.nrmL2 (Graph.CycleExample.lam (1/2)) (Graph.CycleExample.uInfl 2))
        (lossVal (Graph.CycleExample.lam (1/2)) (fun _ => 1) logSq
          (ratio (Graph.CycleExample.pol (p := 1/2) (by norm_num) (by norm_num)).phat
            (Graph.CycleExample.lam (1/2)) (Graph.CycleExample.uInfl 2)))
        (gamma0At Gamma3Val 1 1 (BhatSigma Graph.CycleExample.cyc (Graph.CycleExample.hitExp (1/2))
          (Graph.CycleExample.lam (1/2))))
        (Graph.meanL2 (Graph.CycleExample.lam (1/2)) (Graph.CycleExample.uInfl 2))
      ∧ ∃ uk : ℕ → Fin 5 → ℝ, uk 0 = Graph.CycleExample.uInfl 2 ∧ ∀ k, uk (k + 1) = fun x =>
          uk k x - γ * lossGrad (Graph.CycleExample.pol (p := 1/2) (by norm_num) (by norm_num)).phat
            (Graph.CycleExample.lam (1/2)) (fun z => Graph.CycleExample.lam (1/2) z * 1)
            logSqDeriv (uk k) x := by
  have hp0 : (0:ℝ) < 1/2 := by norm_num
  have hp1 : (1:ℝ)/2 < 1 := by norm_num
  refine ⟨fun hbal => ?_, training_speed_gd_inhabited (pmin :=
      minPos (Graph.CycleExample.pol hp0 hp1).phat)
    Graph.CycleExample.pathConnected (Graph.CycleExample.positiveOnEdges hp0 hp1)
    (Graph.CycleExample.isInvProb hp0 hp1) (Graph.CycleExample.isHitExp hp0 hp1)
    one_pos (fun _ => le_rfl) (fun _ => le_rfl) (minPos_pos _)
    (Graph.CycleExample.uInfl_pos (by norm_num))⟩
  have h := (ratio_eq_one_iff_balanced (K := (Graph.CycleExample.pol hp0 hp1).phat)
    (fun y => mul_pos (Graph.CycleExample.lam_pos hp1 y)
      (Graph.CycleExample.uInfl_pos (by norm_num) y))).mpr hbal 0
  rw [Graph.CycleExample.ratio_src hp0 hp1 (by norm_num)] at h
  norm_num at h

/-- **`theo:training_speed_full`, item *3*, at the paper's own `p_min`** — the smallest positive
transition probability of the loop-closed backward policy (`minPos`), which is the constant
`proofs.tex:1000` names: `training_speed_gd` with its floor hypotheses discharged by `minPos_pos`,
`minPos_le_one` and `minPos_le`. -/
theorem training_speed_gd_minPos {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH wf : V → ℝ} {wmin wsup γ : ℝ} {uk : ℕ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ : 0 < γ)
    (hγs : γ ≤ gammaStar
      (b3 wsup (uMin V (Graph.minOver G lam) (minPos B.phat) wmin
          (lossVal lam wf logSq (ratio B.phat lam (uk 0))) (Graph.meanL2 lam (uk 0)))
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0)))))
      (Graph.nrmL2 lam (uk 0)) (lossVal lam wf logSq (ratio B.phat lam (uk 0)))
      (gamma0At Gamma3Val wmin wsup (BhatSigma G uH lam)) (Graph.meanL2 lam (uk 0))) :
    -- (a)
    (∀ k, (∀ x, uMin V (Graph.minOver G lam) (minPos B.phat) wmin
          (lossVal lam wf logSq (ratio B.phat lam (uk 0))) (Graph.meanL2 lam (uk 0)) ≤ uk k x)
      ∧ lossVal lam wf logSq (ratio B.phat lam (uk (k + 1)))
          ≤ lossVal lam wf logSq (ratio B.phat lam (uk k))
            - γ / 2 * Graph.nrmL2 lam
                (lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2
      ∧ Graph.meanL2 lam (uk k) ≤ Graph.meanL2 lam (uk (k + 1))
      ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2
          = Graph.nrmL2 lam (uk k) ^ 2
            + γ ^ 2 * Graph.nrmL2 lam
                (lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2
      ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2 ≤ 2 * Graph.nrmL2 lam (uk 0) ^ 2)
    -- (b)
    ∧ (∀ k : ℕ, lossVal lam wf logSq (ratio B.phat lam (uk k))
      ≤ ((lossVal lam wf logSq (ratio B.phat lam (uk 0)))⁻¹
          + k * γ * (wmin * Real.sqrt (Graph.minOver G lam) / (Graph.nrmL2 lam (uk 0) * wsup
              * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam (uk 0))
                  / (wmin * Graph.minOver G lam))))) ^ 2 / 4)⁻¹)
    -- (c)
    ∧ Graph.meanL2 lam (uk 0)
        ≤ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam (uk 0)) wsup
            (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
            (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
            (Graph.meanL2 lam (uk 0))))
    ∧ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam (uk 0)) wsup
            (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
            (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
            (Graph.meanL2 lam (uk 0))))
        ≤ Real.sqrt 2 * Graph.nrmL2 lam (uk 0)
    ∧ (∀ k : ℕ, k0 γ (Graph.nrmL2 lam (uk 0)) wsup
            (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
            (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
            (Graph.meanL2 lam (uk 0)) ≤ k →
        Graph.nrmL2 lam (fun x => uk k x / Graph.meanL2 lam (uk k) - 1)
            ≤ eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam)
          ∧ Graph.nrmL2 lam (perpL2 lam (uk (k + 1)))
            ≤ (1 - γ * rhoSigma 2 wmin (Graph.minOver G lam) (Graph.sigmaStar G uH)
                / (4 * Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam (uk 0)) wsup
                  (ratioCap (Graph.minOver G lam) wmin
                    (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
                  (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
                  (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
                  (Graph.meanL2 lam (uk 0)))) ^ 2))
              * Graph.nrmL2 lam (perpL2 lam (uk k)))
    -- (d)
    ∧ Monotone (fun k => Graph.meanL2 lam (uk k))
    ∧ ∃ minf : ℝ, Filter.Tendsto (fun k => Graph.meanL2 lam (uk k)) Filter.atTop (nhds minf)
        ∧ minf ≤ Real.sqrt 2 * Graph.nrmL2 lam (uk 0)
        ∧ Balanced B.phat lam (fun _ => minf)
        ∧ (∀ k : ℕ, k0 γ (Graph.nrmL2 lam (uk 0)) wsup
              (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
              (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
              (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
              (Graph.meanL2 lam (uk 0)) ≤ k →
            minf - Graph.meanL2 lam (uk k)
                ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2
                  / Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam (uk 0)) wsup
                    (ratioCap (Graph.minOver G lam) wmin
                      (lossVal lam wf logSq (ratio B.phat lam (uk 0))))
                    (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
                    (eps0At Gamma3Val wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
                    (Graph.meanL2 lam (uk 0))))
              ∧ Graph.nrmL2 lam (fun x => uk k x - minf)
                ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)))
        ∧ Filter.Tendsto (fun k => Graph.nrmL2 lam (fun x => uk k x - minf)) Filter.atTop
            (nhds 0) :=
  haveI := nonempty_of_total hl.total
  training_speed_gd hpc hpos hl hhit hwmin hw hwsup (minPos_pos _)
    (minPos_le_one ⟨B.phat_nonneg, B.phat_row_sum⟩) (fun _ _ h => minPos_le h) hu0 hstep hγ hγs

/-- **`theo:training_speed_full`, assertion *3(b)*, as printed** (`proofs.tex:1024`), with the
convention `𝓛(μ₀)^{−1} := +∞` at a balanced start (`proofs.tex:1004`): the envelope read in
`[0,∞]`, where `0⁻¹ = ∞` and `∞⁻¹ = 0`, together with `(𝓛(μ₀))⁻¹ = ∞ ↔ μ₀` balanced. At a
balanced start it says `𝓛(u_kλ) = 0`, which *(a)* delivers (`𝓛` non-increasing from `0`);
otherwise it is `training_speed_gd_minPos`'s real display. This is `global_phase_exact`'s
reading of item *1*, carried to item *3*. -/
theorem training_speed_gd_minPos_ennreal {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH wf : V → ℝ} {wmin wsup γ : ℝ} {uk : ℕ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hu0 : ∀ x, 0 < uk 0 x)
    (hstep : ∀ k, uk (k + 1) = fun x =>
      uk k x - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
    (hγ : 0 < γ)
    (hγs : γ ≤ gammaStar
      (b3 wsup (uMin V (Graph.minOver G lam) (minPos B.phat) wmin
          (lossVal lam wf logSq (ratio B.phat lam (uk 0))) (Graph.meanL2 lam (uk 0)))
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam (uk 0)))))
      (Graph.nrmL2 lam (uk 0)) (lossVal lam wf logSq (ratio B.phat lam (uk 0)))
      (gamma0At Gamma3Val wmin wsup (BhatSigma G uH lam)) (Graph.meanL2 lam (uk 0))) :
    (∀ k : ℕ, ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (uk k)))
      ≤ ((ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (uk 0))))⁻¹
          + ENNReal.ofReal (k * γ * (wmin * Real.sqrt (Graph.minOver G lam)
              / (Graph.nrmL2 lam (uk 0) * wsup
                * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam (uk 0))
                    / (wmin * Graph.minOver G lam))))) ^ 2 / 4))⁻¹)
    ∧ (Balanced B.phat lam (uk 0)
        ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (uk 0))))⁻¹ = ⊤) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  have hLnn : ∀ k, 0 ≤ lossVal lam wf logSq (ratio B.phat lam (uk k)) := fun k =>
    lossVal_nonneg (fun x => (hp x).le) fun x => (hwpos x).le
  obtain ⟨ha, hb, -⟩ :=
    training_speed_gd_minPos hpc hpos hl hhit hwmin hw hwsup hu0 hstep hγ hγs
  have hanti : Antitone fun k => lossVal lam wf logSq (ratio B.phat lam (uk k)) :=
    antitone_nat_of_succ_le fun k => by
      have := (ha k).2.1
      have hsq : 0 ≤ γ / 2 * Graph.nrmL2 lam
          (lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2 :=
        mul_nonneg (div_nonneg hγ.le two_pos.le) (sq_nonneg _)
      linarith
  refine ⟨fun k => ?_, ?_⟩
  · have hc : 0 ≤ (k : ℝ) * γ * (wmin * Real.sqrt (Graph.minOver G lam)
          / (Graph.nrmL2 lam (uk 0) * wsup
            * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam (uk 0))
                / (wmin * Graph.minOver G lam))))) ^ 2 / 4 := by positivity
    rcases (hLnn 0).lt_or_eq with hpos0 | hzero
    · rw [← ENNReal.ofReal_inv_of_pos hpos0, ← ENNReal.ofReal_add (inv_pos.mpr hpos0).le hc,
        ← ENNReal.ofReal_inv_of_pos (add_pos_of_pos_of_nonneg (inv_pos.mpr hpos0) hc)]
      exact ENNReal.ofReal_le_ofReal (hb k)
    · have hLk : lossVal lam wf logSq (ratio B.phat lam (uk k)) ≤ 0 := by
        rw [hzero]; exact hanti (Nat.zero_le k)
      rw [ENNReal.ofReal_of_nonpos hLk]
      exact zero_le
  · rw [ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero,
      ← lossVal_eq_zero_iff_balanced hl.inv B.phat_nonneg hp hu0 hwpos]
    exact ⟨fun h => h.le, fun h => le_antisymm h (hLnn 0)⟩

end Inhabit


/-! ### Identification with `C3Wrappers.lean`'s constants

`Gamma3Val`, `eps0At` and `gamma0At` are the printed formulas at `Γ₃ = 48 + 32 ln 2`; that this
number **is** `sup_{[1/2,3/2]}|g'''|` for `g = (log x)²`, and that the radius and step cap are
Theorem 10's as `local_convergence_full_C3` computes them, is `C3Wrappers.lean`'s. -/

section Identify

/-- **`Γ₃ = sup_{[1/2,3/2]}|g'''|` for `g = (log x)²`** is `Gamma3Val` (`Gamma3_logSq`). -/
theorem Gamma3_logSq_eq_Gamma3Val :
    GFNBounds.Balance.Gamma3 GFNBounds.Balance.logSq (1/2) = Gamma3Val := by
  rw [GFNBounds.Balance.Gamma3_logSq]; rfl

/-- **The entry radius of item *3* is item *2*'s**, `eps0Gamma3`. -/
theorem eps0At_Gamma3Val_eq (wmin W Bhat lamMin : ℝ) :
    eps0At Gamma3Val wmin W Bhat lamMin = GFNBounds.Balance.eps0Gamma3 wmin W Bhat lamMin := rfl

/-- **The step cap `γ₀` of item *3* is Theorem 10's** for `g = (log x)²` at `a = 1/2`. -/
theorem gamma0At_Gamma3Val_eq (wmin W Bhat : ℝ) :
    gamma0At Gamma3Val wmin W Bhat
      = GFNBounds.Balance.gamma0C3 GFNBounds.Balance.logSq (1/2) wmin W Bhat := by
  simp only [gamma0At, GFNBounds.Balance.gamma0C3, GFNBounds.Balance.logSq_deriv2_one,
    GFNBounds.Balance.Gamma3_logSq, Gamma3Val]

end Identify


/-! ### Item *3* with the paper's quantifiers, and the whole theorem

`training_speed_gd_minPos` and `training_speed_gd_minPos_ennreal` take the sequence and the step as
hypotheses. The paper states item *3* from `u₀` alone — *there is an explicit `γ_* > 0` such that,
for every step `0 < γ ≤ γ_*`, … the gradient descent is well defined and satisfies (a)–(d)* — and
states the whole theorem as one statement with items *1*–*2*. This section adds that quantifier
structure and nothing about the dynamics: every inequality below is one of the two theorems above,
`γ_*` is shown to be the printed three-term minimum in `[0,∞]`, and `ε₀`, `γ₀` are identified with
item *2*'s (`TrainingSpeedAssembled.eps0W`, `gamma0W` at `Γ₃ = sup|g'''|`). -/

section Complete

variable {V : Type*} [Fintype V] [DecidableEq V]

open Filter Topology

/-- **`γ_* := min(1/b₃, (‖u₀‖²/2)𝓛(μ₀)^{−1}, γ₀m₀²)` with `𝓛(μ₀)^{−1} := +∞`, exactly**
(`proofs.tex:1051`, convention `:1004`): `gammaStar`'s case split (the middle entry dropped at
`𝓛(μ₀) = 0`) is the printed minimum read in `[0,∞]`, where `0⁻¹ = ∞` and `a · ∞ = ∞` for `a > 0`. -/
theorem gammaStar_ofReal {b3v U0 L0 γ0 m0 : ℝ} (hU0 : 0 < U0) (hL0 : 0 ≤ L0) :
    ENNReal.ofReal (gammaStar b3v U0 L0 γ0 m0)
      = min (min (ENNReal.ofReal (1 / b3v))
          (ENNReal.ofReal (U0 ^ 2 / 2) * (ENNReal.ofReal L0)⁻¹))
        (ENNReal.ofReal (γ0 * m0 ^ 2)) := by
  have hU : 0 < U0 ^ 2 / 2 := by positivity
  unfold gammaStar
  split_ifs with h
  · rw [h, ENNReal.ofReal_zero, ENNReal.inv_zero,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hU).ne', min_top_right, ENNReal.ofReal_min]
  · have hL : 0 < L0 := lt_of_le_of_ne hL0 (Ne.symm h)
    rw [ENNReal.ofReal_min, ENNReal.ofReal_min, ENNReal.ofReal_mul hU.le,
      ENNReal.ofReal_inv_of_pos hL]

/-- **Item *3*'s `γ₀` is Theorem 10's** for `g = (log x)²` at `a = 1/2`, with `Γ₃` the supremum of
`|g'''|` within the window (`TrainingSpeedAssembled.gamma0W`). -/
theorem gamma0W_logSq_eq_gamma0At (wmin W Bhat : ℝ) :
    gamma0W logSq (1/2) wmin W Bhat = gamma0At Gamma3Val wmin W Bhat := by
  simp only [gamma0W, gamma0At, logSq_deriv2_one, Gamma3W_logSq, Gamma3Val]

/-- **Item *3*'s `ε₀` is item *2*'s**, `TrainingSpeedAssembled.eps0W` at `g = (log x)²`,
`a = 1/2`. -/
theorem eps0W_logSq_eq_eps0At (wmin W Bhat lamMin : ℝ) :
    eps0W logSq (1/2) wmin W Bhat lamMin = eps0At Gamma3Val wmin W Bhat lamMin := by
  simp only [eps0W, eps0At, logSq_deriv2_one, Gamma3W_logSq, Gamma3Val]

/-- **`theo:training_speed_full`, item *3*, as printed** (`proofs.tex:1021–1033`, proof
`:1045–1090`), from `u₀` alone, with the paper's quantifiers: *there is an explicit `γ_* > 0` such
that for every step `0 < γ ≤ γ_*` … the gradient descent `u_{k+1} := u_k − γD(u_k)` is well defined
and satisfies (a)–(d)*, and the closing necessity sentence.

Every constant is the printed formula at the paper's own values: `‖w‖_{L^∞} = max w`
(`Graph.maxOver`), `λ_min = min λ`, `p_min` the smallest positive transition probability
(`minPos`), `M = ratioCap`, `u_min`, `b₃`, `γ_*`, `κ`, `k₀(γ)`, `ϱ_σ = g''(1)w_min λ_min/σ_*²`, and
`ε₀`, `γ₀` those of `theo:local_convergence_full` for `g = (log x)²` at `a = 1/2`, `B̂_σ`,
`C_∞ = λ_min^{−1/2}`, with `Γ₃ = sup |g'''|` (`eps0W`, `gamma0W`: the same `ε₀` as item *2*).

The convention `𝓛(μ₀)^{−1} := +∞` at a balanced start is honoured twice: `γ_*` is stated in `[0,∞]`
as the printed three-term minimum, and *(b)* is stated in `[0,∞]`; `μ₀` balanced `↔`
`𝓛(μ₀)^{−1} = ∞`, and at a balanced start `𝓛(u_k) = 0` for every `k`. The dynamics are
`training_speed_gd_minPos`'s and *(b)* is `training_speed_gd_minPos_ennreal`'s. -/
theorem training_speed_gd_exact {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH wf : V → ℝ} {wmin : ℝ} {u0 : V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hu0 : ∀ x, 0 < u0 x) :
    0 < (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos B.phat) wmin
        (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap
        (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))) (Graph.nrmL2 lam
        u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin (Graph.maxOver G
        wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
    ∧ ENNReal.ofReal (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos
        B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap
        (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))) (Graph.nrmL2 lam
        u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin (Graph.maxOver G
        wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
        = min (min (ENNReal.ofReal (1 / b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam)
            (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam
            u0)) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam
            u0)))))
            (ENNReal.ofReal (Graph.nrmL2 lam u0 ^ 2 / 2) * (ENNReal.ofReal (lossVal lam wf logSq
                (ratio B.phat lam u0)))⁻¹))
          (ENNReal.ofReal (gamma0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam) *
              Graph.meanL2 lam u0 ^ 2))
    ∧ (Balanced B.phat lam u0 ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ = ⊤)
    ∧ (∀ γ : ℝ, 0 < γ → γ ≤ (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam)
        (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0))
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))))
        (Graph.nrmL2 lam u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin
        (Graph.maxOver G wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0)) →
        (∃ uk : ℕ → V → ℝ, uk 0 = u0 ∧ ∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad B.phat lam
            (fun z => lam z * wf z) logSqDeriv (uk k) x)
        ∧ ∀ uk : ℕ → V → ℝ, uk 0 = u0 →
          (∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad B.phat lam (fun z => lam z * wf z)
              logSqDeriv (uk k) x) →
          -- well defined
          0 < uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat
              lam u0)) (Graph.meanL2 lam u0) ∧ (∀ k x, 0 < uk k x)
          -- (a)
          ∧ (∀ k, (∀ x, uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq
              (ratio B.phat lam u0)) (Graph.meanL2 lam u0) ≤ uk k x)
              ∧ (lossVal lam wf logSq (ratio B.phat lam (uk (k + 1)))) ≤ (lossVal lam wf logSq
                  (ratio B.phat lam (uk k))) - γ / 2 * Graph.nrmL2 lam (lossGrad B.phat lam (fun z
                  => lam z * wf z) logSqDeriv (uk k)) ^ 2
              ∧ Graph.meanL2 lam (uk k) ≤ Graph.meanL2 lam (uk (k + 1))
              ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2
                  = Graph.nrmL2 lam (uk k) ^ 2 + γ ^ 2 * Graph.nrmL2 lam (lossGrad B.phat lam (fun
                      z => lam z * wf z) logSqDeriv (uk k)) ^ 2
              ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2 ≤ 2 * Graph.nrmL2 lam u0 ^ 2)
          -- (b), in `[0,∞]`
          ∧ (∀ k : ℕ, ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (uk k)))
              ≤ ((ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ + ENNReal.ofReal
                  (k * γ * (wmin * Real.sqrt (Graph.minOver G lam) / (Graph.nrmL2 lam u0 *
                  (Graph.maxOver G wf) * max 1 (Real.sqrt ((lossVal lam wf logSq (ratio B.phat lam
                  u0)) / (wmin * (Graph.minOver G lam)))))) ^ 2 / 4))⁻¹)
          ∧ (Balanced B.phat lam u0 → ∀ k, (lossVal lam wf logSq (ratio B.phat lam (uk k))) = 0)
          -- (c)
          ∧ Graph.meanL2 lam u0 ≤ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G
              wf) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam
              u0))) (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
              (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam
              u0)))
          ∧ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap
              (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))
              (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
              (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam
              u0))) ≤ Real.sqrt 2 * Graph.nrmL2 lam u0
          ∧ (∀ k : ℕ, (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver G
              lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH) wmin
              (Graph.minOver G lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH
              lam) (Graph.minOver G lam)) (Graph.meanL2 lam u0)) ≤ k →
              Graph.nrmL2 lam (fun x => uk k x / Graph.meanL2 lam (uk k) - 1) ≤ eps0W logSq (1/2)
                  wmin (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)
              ∧ Graph.nrmL2 lam (perpL2 lam (uk (k + 1)))
                ≤ (1 - γ * rhoSigma (deriv (deriv logSq) 1) wmin (Graph.minOver G lam)
                    (Graph.sigmaStar G uH) / (4 * Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0)
                    (Graph.maxOver G wf) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq
                    (ratio B.phat lam u0))) (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
                    (eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
                    (Graph.minOver G lam)) (Graph.meanL2 lam u0))) ^ 2))
                  * Graph.nrmL2 lam (perpL2 lam (uk k)))
          -- (d)
          ∧ Monotone (fun k => Graph.meanL2 lam (uk k))
          ∧ ∃ minf : ℝ, Tendsto (fun k => Graph.meanL2 lam (uk k)) atTop (𝓝 minf)
              ∧ minf ≤ Real.sqrt 2 * Graph.nrmL2 lam u0
              ∧ Balanced B.phat lam (fun _ => minf)
              ∧ (∀ k : ℕ, (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver
                  G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH)
                  wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf)
                  (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam u0)) ≤ k →
                  minf - Graph.meanL2 lam (uk k)
                      ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2 / Graph.meanL2 lam (uk (k0 γ
                          (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver G lam)
                          wmin (lossVal lam wf logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH)
                          wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf)
                          (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam u0)))
                  ∧ Graph.nrmL2 lam (fun x => uk k x - minf)
                      ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)))
              ∧ Tendsto (fun k => Graph.nrmL2 lam (fun x => uk k x - minf)) atTop (𝓝 0))
    -- no step bound independent of the initialization
    ∧ (∀ γ : ℝ, 0 < γ → ∀ v0 : V → ℝ, (∀ x, 0 < v0 x) → ¬ Balanced B.phat lam v0 →
        ∃ y : V, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s < s0 →
          s * v0 y - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (fun x => s * v0 x)
              y < 0) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hp x).le
  haveI := nonempty_of_total hl.total
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hwsup : ∀ x, wf x ≤ Graph.maxOver G wf := fun x => Graph.le_maxOver wf x
  have hWpos : 0 < Graph.maxOver G wf := lt_of_lt_of_le hwmin (le_trans (hw x0) (hwsup x0))
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hm0 : 0 < Graph.meanL2 lam u0 :=
    Finset.sum_pos (fun x _ => mul_pos (hp x) (hu0 x)) Finset.univ_nonempty
  have hU0 : 0 < Graph.nrmL2 lam u0 :=
    lt_of_lt_of_le hm0 (mean_le_nrmL2_iff_const hp hl.total (fun x => (hu0 x).le)).1
  have hL0 : 0 ≤ lossVal lam wf logSq (ratio B.phat lam u0) :=
    lossVal_nonneg hnn (fun x => (hwpos x).le)
  have hum : 0 < uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq (ratio
      B.phat lam u0)) (Graph.meanL2 lam u0) := uMin_pos hlmin0 (minPos_pos _) hm0
  have hbr := (b3_bracket_ge (ratioCap_pos (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio
      B.phat lam u0))).le).2.2
  have hb3 : 0 < b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos B.phat) wmin
      (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap (Graph.minOver
      G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) := by
    rw [b3, mul_assoc]
    have := lt_of_lt_of_le (by norm_num : (0:ℝ) < 8) hbr
    positivity
  have hB := lt_of_lt_of_le zero_lt_one (one_le_BhatSigma hpc hpos hl hhit)
  rw [gamma0W_logSq_eq_gamma0At, eps0W_logSq_eq_eps0At, logSq_deriv2_one]
  have hGpos := gammaStar_pos hb3 hU0 hL0
    (gamma0At_pos (le_trans (by norm_num) twentyfour_le_Gamma3Val) hwmin hWpos hB) hm0
  -- the balanced-start iff is `training_speed_gd_minPos_ennreal`'s, read on the sequence at `γ_*`
  have hbal : Balanced B.phat lam u0 ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam
      u0)))⁻¹ = ⊤ := by
    obtain ⟨uk, h0, hrec⟩ := exists_descent_seq B.phat lam wf u0 (gammaStar (b3 (Graph.maxOver G
      wf) (uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat
      lam u0)) (Graph.meanL2 lam u0)) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq
      (ratio B.phat lam u0)))) (Graph.nrmL2 lam u0) (lossVal lam wf logSq (ratio B.phat lam u0))
      (gamma0At Gamma3Val wmin (Graph.maxOver G wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
    subst h0
    exact (training_speed_gd_minPos_ennreal hpc hpos hl hhit hwmin hw hwsup hu0 hrec hGpos
      le_rfl).2
  refine ⟨hGpos, gammaStar_ofReal hU0 hL0, hbal, fun γ hγ hγs => ⟨exists_descent_seq _ _ _ _ _,
    fun uk huk0 hstep => ?_⟩, fun γ hγ v0 hv0 hnb => no_uniform_step_graph hpc hpos hl hwmin hw
      hv0 hnb hγ⟩
  subst huk0
  obtain ⟨ha, -, hc1, hc2, hc3, hd1, hd2⟩ :=
    training_speed_gd_minPos hpc hpos hl hhit hwmin hw hwsup hu0 hstep hγ hγs
  obtain ⟨hb, hbal'⟩ :=
    training_speed_gd_minPos_ennreal hpc hpos hl hhit hwmin hw hwsup hu0 hstep hγ hγs
  have hbal0 : Balanced B.phat lam (uk 0) →
      ∀ k, lossVal lam wf logSq (ratio B.phat lam (uk k)) = 0 := by
    intro h k
    have hk := hb k
    rw [hbal'.mp h, top_add, ENNReal.inv_top, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero] at hk
    exact le_antisymm hk (lossVal_nonneg hnn fun x => (hwpos x).le)
  exact ⟨hum, fun k x => lt_of_lt_of_le hum ((ha k).1 x), ha, hb, hbal0, hc1, hc2, hc3, hd1, hd2⟩

/-- **`theo:training_speed_full`, the whole statement** (`proofs.tex:999–1035`): the preamble and
items *1*–*2* (`TrainingSpeedAssembled.training_speed_full_paper`, the flow constructed, no flow
hypothesis) and item *3* (`training_speed_gd_exact`), from the paper's hypotheses and `u₀` alone,
with `𝓛(μ₀)^{−1} := +∞` at a balanced start honoured in both the flow's and the descent's
displays, and `ε₀` literally the same constant in items *2* and *3*. The principal declaration of
the label. -/
theorem training_speed_full_complete {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam gr uH wf : V → ℝ} {wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ((∀ x, lam x = Graph.visits G gr x / (2 + B.sigmaBar uH))
        ∧ Graph.minOver G lam = Graph.minOver G (Graph.visits G gr) / (2 + B.sigmaBar uH)
        ∧ rhoSigma (deriv (deriv logSq) 1) wmin (Graph.minOver G lam) (Graph.sigmaStar G uH)
            = 2 * wmin * Graph.minOver G (Graph.visits G gr)
                / (Graph.sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH))
        ∧ ∃ u : ℝ → V → ℝ, u 0 = u0
          ∧ IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u
          ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
          ∧ (∀ v : ℝ → V → ℝ, v 0 = u0 →
              IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv v →
              (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t)
          ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam u0)
          ∧ Balanced B.phat lam (fun _ => Graph.nrmL2 lam u0)
          -- item 1
          ∧ (∀ t : ℝ, 0 ≤ t →
              HasDerivAt (fun s => lossVal lam wf logSq (ratio B.phat lam (u s)))
                (-(Graph.nrmL2 lam (lossGrad B.phat lam (fun x => lam x * wf x) logSqDeriv (u t))
                  ^ 2)) t
              ∧ (wmin * Real.sqrt (Graph.minOver G lam)
                  / (Graph.nrmL2 lam u0 * Graph.maxOver G wf
                      * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam u0)
                          / (wmin * Graph.minOver G lam))))) ^ 2
                  * lossVal lam wf logSq (ratio B.phat lam (u t)) ^ 2
                ≤ Graph.nrmL2 lam (lossGrad B.phat lam (fun x => lam x * wf x) logSqDeriv (u t))
                  ^ 2)
          ∧ (∀ t : ℝ, 0 ≤ t →
              ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (u t)))
                ≤ ((ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹
                    + ENNReal.ofReal ((wmin * Real.sqrt (Graph.minOver G lam)
                        / (Graph.nrmL2 lam u0 * Graph.maxOver G wf
                            * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam u0)
                                / (wmin * Graph.minOver G lam))))) ^ 2 * t))⁻¹)
          ∧ (Balanced B.phat lam u0
              ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ = ⊤)
          -- item 2
          ∧ ∃ t₁ ∈ Set.Icc (0:ℝ)
              (4 * lossVal lam wf logSq (ratio B.phat lam u0) * Graph.nrmL2 lam u0 ^ 6
                  * Graph.sigmaStar G uH ^ 4
                / (wmin ^ 2
                    * eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
                        (Graph.minOver G lam) ^ 4
                    * Graph.meanL2 lam u0 ^ 4 * Graph.minOver G lam ^ 5)),
              Graph.meanL2 lam u0 ≤ Graph.meanL2 lam (u t₁)
                ∧ Graph.meanL2 lam (u t₁) ≤ Graph.nrmL2 lam u0
                ∧ Graph.nrmL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)
                    ≤ eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
                        (Graph.minOver G lam)
                ∧ ∃ cinf : ℝ, Balanced B.phat lam (fun _ => cinf) ∧ ∀ t : ℝ, t₁ ≤ t →
                    Graph.nrmL2 lam (fun x => u t x / Graph.meanL2 lam (u t₁) - cinf)
                      ≤ 2 * Real.exp (-(rhoSigma (deriv (deriv logSq) 1) wmin (Graph.minOver G lam)
                              (Graph.sigmaStar G uH) * (t - t₁)
                            / (2 * Graph.meanL2 lam (u t₁) ^ 2)))
                        * Graph.nrmL2 lam
                            (perpL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)))
    ∧ (0 < (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos B.phat) wmin
        (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap
        (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))) (Graph.nrmL2 lam
        u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin (Graph.maxOver G
        wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
      ∧ ENNReal.ofReal (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos
          B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0))
          (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))))
          (Graph.nrmL2 lam u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2)
          wmin (Graph.maxOver G wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
          = min (min (ENNReal.ofReal (1 / b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam)
              (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam
              u0)) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam
              u0)))))
              (ENNReal.ofReal (Graph.nrmL2 lam u0 ^ 2 / 2) * (ENNReal.ofReal (lossVal lam wf logSq
                  (ratio B.phat lam u0)))⁻¹))
            (ENNReal.ofReal (gamma0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam) *
                Graph.meanL2 lam u0 ^ 2))
      ∧ (Balanced B.phat lam u0 ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ =
          ⊤)
      ∧ (∀ γ : ℝ, 0 < γ → γ ≤ (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam)
          (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0))
          (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))))
          (Graph.nrmL2 lam u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2)
          wmin (Graph.maxOver G wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0)) →
          (∃ uk : ℕ → V → ℝ, uk 0 = u0 ∧ ∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad B.phat
              lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
          ∧ ∀ uk : ℕ → V → ℝ, uk 0 = u0 →
            (∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad B.phat lam (fun z => lam z * wf z)
                logSqDeriv (uk k) x) →
            -- well defined
            0 < uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq (ratio
                B.phat lam u0)) (Graph.meanL2 lam u0) ∧ (∀ k x, 0 < uk k x)
            -- (a)
            ∧ (∀ k, (∀ x, uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq
                (ratio B.phat lam u0)) (Graph.meanL2 lam u0) ≤ uk k x)
                ∧ (lossVal lam wf logSq (ratio B.phat lam (uk (k + 1)))) ≤ (lossVal lam wf logSq
                    (ratio B.phat lam (uk k))) - γ / 2 * Graph.nrmL2 lam (lossGrad B.phat lam (fun
                    z => lam z * wf z) logSqDeriv (uk k)) ^ 2
                ∧ Graph.meanL2 lam (uk k) ≤ Graph.meanL2 lam (uk (k + 1))
                ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2
                    = Graph.nrmL2 lam (uk k) ^ 2 + γ ^ 2 * Graph.nrmL2 lam (lossGrad B.phat lam
                        (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2
                ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2 ≤ 2 * Graph.nrmL2 lam u0 ^ 2)
            -- (b), in `[0,∞]`
            ∧ (∀ k : ℕ, ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (uk k)))
                ≤ ((ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ + ENNReal.ofReal
                    (k * γ * (wmin * Real.sqrt (Graph.minOver G lam) / (Graph.nrmL2 lam u0 *
                    (Graph.maxOver G wf) * max 1 (Real.sqrt ((lossVal lam wf logSq (ratio B.phat
                    lam u0)) / (wmin * (Graph.minOver G lam)))))) ^ 2 / 4))⁻¹)
            ∧ (Balanced B.phat lam u0 → ∀ k, (lossVal lam wf logSq (ratio B.phat lam (uk k))) = 0)
            -- (c)
            ∧ Graph.meanL2 lam u0 ≤ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver
                G wf) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam
                u0))) (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
                (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam
                u0)))
            ∧ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap
                (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))
                (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
                (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam
                u0))) ≤ Real.sqrt 2 * Graph.nrmL2 lam u0
            ∧ (∀ k : ℕ, (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver G
                lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH) wmin
                (Graph.minOver G lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH
                lam) (Graph.minOver G lam)) (Graph.meanL2 lam u0)) ≤ k →
                Graph.nrmL2 lam (fun x => uk k x / Graph.meanL2 lam (uk k) - 1) ≤ eps0W logSq (1/2)
                    wmin (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)
                ∧ Graph.nrmL2 lam (perpL2 lam (uk (k + 1)))
                  ≤ (1 - γ * rhoSigma (deriv (deriv logSq) 1) wmin (Graph.minOver G lam)
                      (Graph.sigmaStar G uH) / (4 * Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0)
                      (Graph.maxOver G wf) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf
                      logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH) wmin (Graph.minOver G
                      lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
                      (Graph.minOver G lam)) (Graph.meanL2 lam u0))) ^ 2))
                    * Graph.nrmL2 lam (perpL2 lam (uk k)))
            -- (d)
            ∧ Monotone (fun k => Graph.meanL2 lam (uk k))
            ∧ ∃ minf : ℝ, Tendsto (fun k => Graph.meanL2 lam (uk k)) atTop (𝓝 minf)
                ∧ minf ≤ Real.sqrt 2 * Graph.nrmL2 lam u0
                ∧ Balanced B.phat lam (fun _ => minf)
                ∧ (∀ k : ℕ, (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap
                    (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))
                    (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
                    (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2
                    lam u0)) ≤ k →
                    minf - Graph.meanL2 lam (uk k)
                        ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2 / Graph.meanL2 lam (uk (k0 γ
                            (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver G
                            lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))
                            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2)
                            wmin (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam))
                            (Graph.meanL2 lam u0)))
                    ∧ Graph.nrmL2 lam (fun x => uk k x - minf)
                        ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)))
                ∧ Tendsto (fun k => Graph.nrmL2 lam (fun x => uk k x - minf)) atTop (𝓝 0))
      -- no step bound independent of the initialization
      ∧ (∀ γ : ℝ, 0 < γ → ∀ v0 : V → ℝ, (∀ x, 0 < v0 x) → ¬ Balanced B.phat lam v0 →
          ∃ y : V, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s < s0 →
            s * v0 y - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (fun x => s * v0
                x) y < 0)) :=
  ⟨training_speed_full_paper hpc hpos hl hg hhit hwmin hw hu0,
    training_speed_gd_exact hpc hpos hl hhit hwmin hw hu0⟩

open Graph.CycleExample in
/-- **Non-vacuity of `training_speed_full_complete`** (kb 0025) on the five-vertex cycle of
`rem:cycle_no_stalemate` at `p = 1/2`, `w ≡ 1`, from the over-inflated `uInfl 2`, which is **not**
balanced: the theorem applies with nothing hypothesised beyond the setting, `γ_* > 0`, and at
`γ = γ_*` the descent sequence exists and every iterate is positive. -/
theorem cycle_training_speed_complete_check :
    ¬ Balanced (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2)) (uInfl 2)
    ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ uk : ℕ → Fin 5 → ℝ, uk 0 = uInfl 2
        ∧ (∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad
            (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2))
            (fun z => lam (1 / 2) z * 1) logSqDeriv (uk k) x)
        ∧ ∀ k x, 0 < uk k x := by
  obtain ⟨-, hGS, -, -, hγ, -⟩ :=
    training_speed_full_complete (G := cyc) (B := pol (p := 1 / 2) (by norm_num) (by norm_num))
      (wf := fun _ => (1 : ℝ)) (wmin := 1) pathConnected (positiveOnEdges _ _) (isInvProb _ _)
      (isGreen _ _) (isHitExp _ _) one_pos (fun _ => le_rfl) (uInfl_pos (M := 2) (by norm_num))
  obtain ⟨⟨uk, h0, hrec⟩, hall⟩ := hγ _ hGS le_rfl
  obtain ⟨-, hpos, -⟩ := hall uk h0 hrec
  refine ⟨?_, _, hGS, uk, h0, hrec, hpos⟩
  rw [← ratio_eq_one_iff_balanced
    (fun y => mul_pos (lam_pos (p := 1 / 2) (by norm_num) y) (uInfl_pos (M := 2) (by norm_num) y))]
  intro h
  have h0' := h 0
  rw [ratio_src (by norm_num) (by norm_num) (by norm_num)] at h0'
  norm_num at h0'

end Complete

end GFNBounds.Balance.DiscreteGlobal
