import GFNBounds.Balance.C3Wrappers
import GFNBounds.Balance.FlowExistence

/-!
# Theorem 10 under `C³` on the closed window, with its flow constructed; items 1 and 2 of the training-speed theorem as printed, from `u₀` alone

**`theo:local_convergence_full`** — statement `proofs.tex:666–672`, proof `proofs.tex:674–727`;
the `C³` hypothesis read on the closed window, the existence and uniqueness of the flow, the DB
instance.
**`theo:training_speed_full`** — statement `proofs.tex:999–1035`, preamble and items 1–2 at
`proofs.tex:999–1020`, proof `proofs.tex:1037–1093`; **items 1 and 2 only**.

> (`theo:local_convergence_full`) In the setting of Theorem `theo:db_stable_frozen_full`, assume
> moreover that `g(1)=g'(1)=0`, that `g` is `C³` on `[1−a,1+a]` for some `a∈(0,1)`, and that the
> state space `𝒮` is finite, with `λ` a probability and `λ(x)>0` for every `x∈𝒮`; set
> `λ_min:=min_{x∈𝒮}λ(x)` and `C_∞:=λ_min^{−1/2}`, so that `C_∞≥1`. For the DB loss, `T=K₂` […]
> is taken on the set `E` of pairs `(s,s')∈𝒮²` with `π_←(s'→s)>0` […]. Then there are explicit
> `ε₀∈(0,a/(16C_∞)]` and `C≥1`, depending only on `g''(1)`, `sup_{[1−a,1+a]}|g'''|`, `a`,
> `w_min`, `‖w‖_{L^∞}`, `B̂` and `C_∞`, such that for every initialization `μ₀=(1+h₀)λ` with
> `‖h₀‖_{L²(λ)}≤ε₀`, the *nonlinear* gradient flow `μ̇_t=−∇^λ𝓛_{g,ν}(μ_t)` converges to a balanced
> flow `c_∞λ` with `|c_∞−1−Πh₀|≤C‖h₀−Πh₀‖²` and `‖h_t−(c_∞−1)‖_{L²(λ)} ≤ 2e^{−ϱt/2}‖h₀−Πh₀‖_{L²(λ)}`.
> There is moreover an explicit `γ₀>0`, depending only on the same quantities, such that for every
> such `h₀` and every step `0<γ≤γ₀` the gradient descent `h_{k+1}:=h_k−γD_k` […] is well defined and
> satisfies `‖h_{k+1}−Πh_{k+1}‖_{L²(λ)}≤(1−γϱ/4)‖h_k−Πh_k‖_{L²(λ)}` for every `k≥0`.

> (`theo:training_speed_full`, preamble, items 1–2) In the setting above, let `g=(log x)²` […], let
> `ν=wλ` with `w≥w_min>0` […]. Then the invariant measure of the backward chain is the visit ratio,
> `λ(x)=N(x)/(2+σ̄)`, so `λ_min=N_min/(2+σ̄)`, and, from *every* initialization `μ₀∼λ` — with
> `u₀:=dμ₀/dλ`, `m₀:=μ₀(𝒱)`, and `𝓛(μ₀)^{−1}:=+∞` if `μ₀` is balanced — the gradient flow of
> `𝓛_{g,ν}` converges to the balanced flow of its sphere in the two phases *1* and *2* […]:
> 1. *global phase* — the loss obeys a Łojasiewicz inequality `−𝓛̇≥κ²𝓛²`, hence decays at the
>    universal rate `𝓛(μ_t)≤(𝓛(μ₀)^{−1}+κ²t)^{−1}`,
>    `κ:=w_min λ_min^{1/2}/(‖u₀‖_{L²(λ)}‖w‖_{L^∞}M)`, with `M:=max(1,√(𝓛(μ₀)/(w_min λ_min)))`;
> 2. *local phase* — let `ε₀` be the radius of Theorem `theo:local_convergence_full` for
>    `g=(log x)²` at `a=1/2`, with `B̂_σ` in place of `B̂` and `C_∞=λ_min^{−1/2}`; at some time
>    `t₁≤T₀:=4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)`, the flow rescaled to unit mass enters the
>    neighbourhood of Theorem `theo:local_convergence_full`, and from `t₁` on the flow converges
>    exponentially at rate `ϱ_σ/(2m₁²)` — `m₁∈[m₀,‖u₀‖_{L²(λ)}]` the flow's mass at `t₁` […] —
>    where `ϱ_σ=g''(1)w_min λ_min/σ_*²=2w_min N_min/(σ_*²(2+σ̄))`.

## Why this file exists

The 2026-09-14 audits of `C3Wrappers.lean` left four gaps between the paper and the Lean. Each is
closed here, without touching the strict library.

1. **`C³` was read two-sided at the window ends.** `C3Wrappers` asks `ContDiffAt ℝ 3 g y` at every
   `y ∈ [1−a,1+a]`, i.e. `C³` on an open neighbourhood of the closed window. Here the hypothesis is
   `ContDiffOn ℝ 3 g [1−a,1+a]`, `Γ₃` is the sup of `|iteratedDerivWithin 3 g [1−a,1+a]|` over the
   window (one-sided at `1 ± a`), and the Taylor bound the library consumes is proved from it
   (`taylor_of_C3On`). **Route taken: the within-derivative version**, not an extension. The flow
   and the descent are driven by any `gd` that is a derivative of `g` within the window
   (`hgd : ∀ y ∈ [1−a,1+a], HasDerivWithinAt g (gd y) [1−a,1+a] y`); `deriv g` qualifies wherever
   `g` is two-sided differentiable on the window, and the within-derivative always does
   (`hasDerivWithinAt_derivWithin_of_C3On`). The two-sided reading is a special case with the same
   `Γ₃` and constants (`C3On_of_C3`, `constW_eq_constC3`); the widening is real (`kinkGen_C3On_not_C3`:
   `C³` on `[1/2,3/2]` from inside, not differentiable at `3/2`). Why `gd` and not `deriv g`: at an
   endpoint where `g` is only one-sidedly differentiable Mathlib's `deriv g` is `0`, and the Taylor
   bound at that endpoint fails for it; the flow never evaluates `g'` there (every ratio stays within
   `2a/3` of `1`), but the library's Taylor hypothesis is asked on the closed window.
2. **Existence of the flow in Theorem 10 was hypothesised.** `local_convergence_full_exists`
   constructs it for a general generator `C³` on the window: from `‖h₀‖ ≤ ε₀` a solution of the
   flow predicate exists, stays positive with every ratio within `2a/3` of `1`, is **unique among
   all solutions** from `μ₀` (not only among those staying in the window — every solution stays in
   it, `LocalConvergence.sup_global`), and converges as printed. The field **is** locally Lipschitz
   under `C³` on the window alone: on the box `[1−ε, 1+ε]^V` (`ε` Step 4's window,
   `ε ≤ min(a,1)/4`) the density is `≥ 3/4` and every ratio lies in `[1−2a/3, 1+2a/3]`, strictly
   inside the window, where `g'` agrees with the within-derivative, which is `C²`; so `D` is `C¹` on
   the box (`contDiffAt_lossGrad_local`, `contDiffAt_gd_of_C3On`) and Lipschitz there
   (`exists_lipschitzOnWith_lossGrad_box`). Route: `FlowExistence.lean`'s — clamp to the box, global
   Picard–Lindelöf (`exists_forall_hasDerivAt_of_lipschitzWith`), and a continuity bootstrap
   (`bootstrap_of_continuous`) whose step is `sup_bootstrap_step_on`, Step 4's inner estimate with
   the ODE asked on `[0,t]` only (the strict `sup_bootstrap_step` asks it on `[0,∞)`, which the
   clamped curve is not known to satisfy before the bootstrap closes).
3. **Item 1 omitted its differential inequality and misread a balanced start.**
   `global_phase_exact` states both conjuncts: `t ↦ 𝓛(μ_t)` has derivative `−‖∇𝓛(μ_t)‖²` and
   `κ²𝓛(μ_t)² ≤ ‖∇𝓛(μ_t)‖²` at every `t ≥ 0`; and the display is read in `ℝ≥0∞`, where `0⁻¹ = ∞` and
   `∞⁻¹ = 0`, which **is** the paper's convention `𝓛(μ₀)^{−1} := +∞` — with the equivalence
   `μ₀` balanced `↔ 𝓛(μ₀)^{−1} = ∞` proved. The real forms (balanced start: `𝓛 ≡ 0`; otherwise the
   real display) are conjuncts too.
4. **Assembly.** `training_speed_full_paper` states the preamble and items 1–2 from `u₀` alone: the
   flow exists, is unique among positive solutions and converges to the balanced flow of its sphere
   (`FlowExistence.no_distant_equilibrium_three_of_init`); `T₀` and `ϱ_σ` are the printed closed
   forms (`T0_eq`, `rhoSigma_eq_visits`); `c_∞λ` is stated balanced; `‖w‖_{L^∞}` and `λ_min` are the
   actual max and min, not bounds.

## What is proved

| | |
|---|---|
| `winC3`, `Gamma3W`, `bddAbove_abs_g3W`, `abs_g3W_le`, `Gamma3W_nonneg` | the window and `Γ₃ := sSup |g'''|` with `g'''` within the window |
| `abs_le_quadratic_of_deriv_Ico`, `hasDerivWithinAt_iteratedDerivWithin_winC3`, `abs_g2W_sub_le` | a fence with the derivative on `[0,b)` only; `|g''(t)−g''(1)| ≤ Γ₃|t−1|` within the window |
| **`taylor_of_C3On`**, `taylor_bundle_of_C3On`, `deriv_one_eq_of_C3On` | `|g'(y) − g''(1)(y−1)| ≤ (Γ₃/2)(y−1)²` on the closed window, for any derivative `gd` within it; `g'(1)`, `g''(1)` are the classical ones |
| **`C3On_of_C3`**, `hasDerivWithinAt_derivWithin_of_C3On`, **`Gamma3W_logSq`** | the two-sided reading is a special case with the same `Γ₃`; `gd` is always dischargeable; `Γ₃ = 48 + 32 log 2` for `(log x)²` |
| `eps0W`, `CW`, `gamma0W`, `constW_congr`, `constW_eq_constC3`, **`eps0W_logSq`**, **`constW_bounds`** | the constants at `Γ₃ = Gamma3W`; dependence as a congruence; equal to `C3Wrappers`' under the two-sided reading; item 2's `ε₀` is `eps0Gamma3`; `ε₀ ∈ (0, a/(16C_∞)]`, `C ≥ 1`, `γ₀ > 0` |
| **`local_convergence_full_C3On`**, **`local_convergence_gd_C3On`** | Theorem 10, flow clause for every solution, and descent clause, under `C³` on the window |
| `contDiffAt_lossGrad_local`, `contDiffAt_gd_of_C3On`, `pos_of_mem_box`, `abs_ratio_le_of_mem_box`, `exists_lipschitzOnWith_lossGrad_box` | the field is `C¹`, hence Lipschitz, on the box `[1−ε,1+ε]^V` |
| `hasDerivAt_mean_of_at`, `hasDerivAt_perp_sq_of_at`, **`sup_bootstrap_step_on`** | Steps 2–4 with the ODE asked on `[0,t]` only, by monotonicity of `‖h^⊥‖²` and `C₇‖h^⊥‖² ± m` |
| **`local_convergence_full_exists`** | Theorem 10's flow clause with **existence, positivity, the `2a/3` window, uniqueness** and convergence to a balanced `c_∞λ` |
| **`local_convergence_full_DB_exists`**, **`local_convergence_gd_DB_C3On`** | the same for the DB loss, `T = K₂` on `E`, `λ₂` |
| **`global_phase_exact`** | item 1: `−𝓛̇ = ‖∇𝓛‖² ≥ κ²𝓛²`, the display in `ℝ≥0∞`, balanced `↔ 𝓛(μ₀)⁻¹ = ∞`, and the real forms |
| **`training_speed_full_paper`** | the preamble and items 1–2 of `theo:training_speed_full`, from `u₀` alone |
| `logSq_C3On_bundle`, `kinkGen`, **`kinkGen_C3On_not_C3`**, **`twoState_exists_check`**, **`cycle_training_speed_paper_check`** | inhabitation (kb 0025), see SCOPE |

## Hypothesis checklist — `theo:local_convergence_full` (`local_convergence_full_C3On`, `local_convergence_full_exists`, `local_convergence_gd_C3On`)

The rows not listed are `LocalConvergence.lean`'s and `C3Wrappers.lean`'s checklists.

| paper hypothesis | here |
|---|---|
| `g` is `C³` on `[1−a,1+a]` | ✓ `hC3 : ContDiffOn ℝ 3 g (Icc (1−a) (1+a))`, `g : ℝ → ℝ`; one-sided at the ends |
| `g'` (the flow's and the descent's) | ✓ `gd` with `hgd : ∀ y ∈ [1−a,1+a], HasDerivWithinAt g (gd y) [1−a,1+a] y`; ⚠ outside the window `gd` is unconstrained (the paper's `g` is unconstrained there too) |
| `Γ₃ := sup_{[1−a,1+a]}|g'''|` | ✓ `Gamma3W g a := sSup (|iteratedDerivWithin 3 g [1−a,1+a]| '' [1−a,1+a])`, finite by `bddAbove_abs_g3W` |
| `g'(1) = 0`, `g''(1) > 0` | ✓ `hg1 : deriv g 1 = 0`, `hg2 : 0 < deriv (deriv g) 1` — the classical derivatives at the interior point `1`, equal to the within ones (`deriv_one_eq_of_C3On`) |
| `g(1) = 0`, `a < 1` | ✗ not carried, unused (a stronger theorem); for `a < 1` the printed window `min(a/4,ε₁)` is the library's (`epsW_eq_of_lt_one`) |
| "the nonlinear gradient flow … converges" | ✓ `local_convergence_full_exists`: `∃ h, h 0 = h₀ ∧ IsGradientFlow … gd (1+h) ∧ (positive, ratios within `2a/3`) ∧ (unique among all solutions from `μ₀`) ∧ ∃ c_∞, `c_∞λ` balanced ∧ the two bounds`; `local_convergence_full_C3On`: every solution converges |
| `λ_min`, `C_∞`, `‖w‖_{L^∞}` | ⚠ bounds `lamMin ≤ λ`, `|w| ≤ wsup`, as in `LocalConvergence.lean`; the theorem at the actual min and max is an instance |
| DB: `T = K₂` on `E`, `λ₂` | ✓ `local_convergence_full_DB_exists`, `local_convergence_gd_DB_C3On`, through `C3Wrappers`' `EdgeSet`, `edgeKernelE`, `edgeMeasureE` |

## Hypothesis checklist — `theo:training_speed_full`, preamble and items 1–2 (`training_speed_full_paper`)

| paper | here |
|---|---|
| finite path-connected marked graph, backward policy positive on the loop closure, `λ` its invariant probability | ✓ `hpc`, `hpos`, `hl` |
| `N(x)`, `σ̄`, `σ_*` | ✓ `gr` with `B.IsGreen gr`, `uH` with `B.IsHitExp uH`, as in `TrainingSpeed.lean` (both exist, `Morozov.exists_isGreen`, `exists_isHitExp`) |
| `g = (log x)²`, `ν = wλ`, `w ≥ w_min > 0` | ✓ `logSq`/`logSqDeriv`, `fun x => lam x * wf x`, `hwmin`, `hw` |
| "from every initialization `μ₀ ∼ λ`" | ✓ `hu0 : ∀ x, 0 < u₀ x`; **no flow hypothesis** |
| "the gradient flow … converges to the balanced flow of its sphere" | ✓ `∃ u, u 0 = u₀ ∧ IsGradientFlow … u ∧ u > 0 ∧ (unique among positive solutions) ∧ u → ‖u₀‖ ∧ ‖u₀‖·λ balanced` |
| `λ(x) = N(x)/(2+σ̄)`, `λ_min = N_min/(2+σ̄)` | ✓ first two conjuncts |
| `−𝓛̇ ≥ κ²𝓛²` | ✓ `HasDerivAt (t ↦ 𝓛(μ_t)) (−‖∇𝓛(μ_t)‖²) t ∧ κ²𝓛(μ_t)² ≤ ‖∇𝓛(μ_t)‖²`, `t ≥ 0` |
| `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1}+κ²t)^{−1}`, `𝓛(μ₀)^{−1} := +∞` at balance | ✓ in `ℝ≥0∞` via `ENNReal.ofReal`, plus `Balanced … u₀ ↔ (ofReal 𝓛(μ₀))⁻¹ = ⊤` |
| `κ`, `M`, `‖w‖_{L^∞}`, `λ_min` | ✓ printed; `‖w‖_{L^∞} = Graph.maxOver G wf`, `λ_min = Graph.minOver G lam` exactly |
| item 2's `ε₀` | ✓ `eps0W logSq (1/2) wmin ‖w‖_{L^∞} B̂_σ λ_min` (`= eps0Gamma3`, `eps0W_logSq`) |
| `t₁ ≤ T₀ = 4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)` | ✓ the closed form literally, `t₁ ∈ [0, T₀]` |
| entry, `m₁ ∈ [m₀,‖u₀‖]`, rate `ϱ_σ/(2m₁²)`, `c_∞λ` balanced | ✓ as `C3Wrappers.training_speed_full_Gamma3`, the rate `rhoSigma (deriv (deriv logSq) 1) …` |
| `ϱ_σ = g''(1)w_min λ_min/σ_*² = 2w_min N_min/(σ_*²(2+σ̄))` | ✓ `rhoSigma` is the first form by definition; the equality to the second is a conjunct |
| item 3 | ✗ not here (another lane, `DiscreteGlobal.lean`) |

## SCOPE (disclosed)

* **Finite state space**, as everywhere in `GFNBounds.Balance`; `g : ℝ → ℝ`.
* **`g'` is a derivative within the window, one-sided at `1 ± a`.** The flow predicate and the
  descent are driven by `gd`; outside `[1−a,1+a]` `gd` is arbitrary. Every solution from `‖h₀‖ ≤ ε₀` keeps its
  ratios within `2a/3` of `1` (`sup_global` with `abs_ratio_le_of_mem_box`), so `gd` is only ever
  evaluated in the open window, where it is `deriv g`; the choice outside is invisible to the
  solutions but part of the predicate.
* **Uniqueness in Theorem 10 is among all solutions of `IsGradientFlow` from `μ₀`** with the same
  `gd`; in `training_speed_full_paper` it is `FlowExistence`'s, among positive solutions. Both ask a
  two-sided derivative at `t = 0` (kb 0025's convention); the constructed curve has one.
* **Below `t = 0` the constructed curve is the clamped flow's**, not a gradient flow; the predicate
  asks nothing there.
* **Two constants are existential**: the Lipschitz constant of `D` on the box and its bound, from
  compactness. They serve only the qualitative existence and uniqueness clauses, which name no
  constant; `ε₀`, `C`, `γ₀` are explicit (kb 0007).
* **`λ_min`, `‖w‖_{L^∞}` are bounds in Theorem 10**, exact in `training_speed_full_paper`.
* **`g(1) = 0` and `a < 1` are not carried** by Theorem 10's restatements.
* **`B̂` stays a hypothesis** for both instances of Theorem 10, as printed (the DB coercivity
  constant `1 + C` of `lem:lift_coercivity` is not composed here).
* **`N`, `σ̄`, `σ_*` enter through `IsGreen`, `IsHitExp`**, as in `TrainingSpeed.lean`.
* **Item 3 of `theo:training_speed_full` is not here**; the assembly stops at items 1–2.
* **Inhabitation (kb 0025).** `logSq_C3On_bundle`: `(log x)²` at `a = 1/2` meets the `C³` bundle;
  `kinkGen_C3On_not_C3`: `(y−1)² + max(0, y−3/2)` meets it and is **not** differentiable at `3/2`, so
  the restatement strictly widens `C3Wrappers`'. `twoState_exists_check`: on the two-state chain,
  `(log x)²`, `a = 1/2`, `w ≡ 1`, `λ_min = 1/2`, `B̂ = 1`, from the **non-balanced** `h₀ = (ε₀/2, −ε₀/2)`,
  `local_convergence_full_exists` produces a solution of the flow predicate: the flow hypothesis of
  `local_convergence_full_C3On` is inhabited off balance. `cycle_training_speed_paper_check`:
  `training_speed_full_paper` applies on the five-vertex cycle at `p = 1/2`, `w ≡ 1`, from the
  non-balanced `uInfl 2`, and delivers the entry into the paper's neighbourhood.
* **`sorry`-free and axiom-clean.** `#print axioms` on `taylor_of_C3On`, `C3On_of_C3`,
  `Gamma3W_logSq`, `eps0W_logSq`, `local_convergence_full_C3On`, `constW_bounds`,
  `local_convergence_gd_C3On`, `sup_bootstrap_step_on`, `local_convergence_full_exists`,
  `local_convergence_full_DB_exists`, `local_convergence_gd_DB_C3On`, `global_phase_exact`,
  `training_speed_full_paper`, `kinkGen_C3On_not_C3`, `twoState_exists_check` and
  `cycle_training_speed_paper_check` returns `[propext, Classical.choice, Quot.sound]`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset Set Filter Topology
open scoped NNReal

/-! ### `C³` on the closed window, one-sided at its ends -/

section TaylorOn

/-- The closed window `[1 − a, 1 + a]`. -/
abbrev winC3 (a : ℝ) : Set ℝ := Icc (1 - a) (1 + a)

/-- **`Γ₃ := sup_{[1−a,1+a]} |g'''|`, with `g'''` the third derivative within the closed window**
(one-sided at `1 ± a`). -/
noncomputable def Gamma3W (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun y => |iteratedDerivWithin 3 g (winC3 a) y|) '' winC3 a)

theorem uniqueDiffOn_winC3 {a : ℝ} (ha : 0 < a) : UniqueDiffOn ℝ (winC3 a) :=
  uniqueDiffOn_Icc (by linarith)

theorem bddAbove_abs_g3W {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a)) :
    BddAbove ((fun y => |iteratedDerivWithin 3 g (winC3 a) y|) '' winC3 a) := by
  refine isCompact_Icc.bddAbove_image ?_
  exact (hC3.continuousOn_iteratedDerivWithin (m := 3) le_rfl (uniqueDiffOn_winC3 ha)).abs

theorem abs_g3W_le {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    {y : ℝ} (hy : y ∈ winC3 a) : |iteratedDerivWithin 3 g (winC3 a) y| ≤ Gamma3W g a :=
  le_csSup (bddAbove_abs_g3W ha hC3) ⟨y, hy, rfl⟩

theorem one_mem_winC3 {a : ℝ} (ha : 0 ≤ a) : (1 : ℝ) ∈ winC3 a := ⟨by linarith, by linarith⟩

theorem Gamma3W_nonneg {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a)) :
    0 ≤ Gamma3W g a :=
  le_trans (abs_nonneg _) (abs_g3W_le ha hC3 (one_mem_winC3 ha.le))

/-- A quadratic fence with the derivative asked on `[0,b)` only and continuity on `[0,b]`. -/
theorem abs_le_quadratic_of_deriv_Ico {e e' : ℝ → ℝ} {M b : ℝ} (hb : 0 ≤ b)
    (hc : ContinuousOn e (Icc 0 b)) (he : ∀ s ∈ Ico 0 b, HasDerivAt e (e' s) s) (h0 : e 0 = 0)
    (hbound : ∀ s ∈ Ico 0 b, |e' s| ≤ M * s) : |e b| ≤ M / 2 * b ^ 2 := by
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := b) (f := e)
    (f' := e') (B := fun s => M / 2 * s ^ 2) (B' := fun s => M * s) hc
    (fun s hs => (he s hs).hasDerivWithinAt)
    (by simp only [h0, norm_zero]; norm_num)
    (fun s => ((hasDerivAt_pow 2 s).const_mul (M / 2)).congr_deriv (by push_cast; ring))
    (fun s hs => by
      simp only [Real.norm_eq_abs]
      exact hbound s hs)
  have := key ⟨hb, le_rfl⟩
  simpa only [Real.norm_eq_abs] using this

/-- The first and second derivatives within the window, as within-derivatives on it. -/
theorem hasDerivWithinAt_iteratedDerivWithin_winC3 {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hC3 : ContDiffOn ℝ 3 g (winC3 a)) {m : ℕ} (hm : m < 3) {y : ℝ} (hy : y ∈ winC3 a) :
    HasDerivWithinAt (iteratedDerivWithin m g (winC3 a))
      (iteratedDerivWithin (m + 1) g (winC3 a) y) (winC3 a) y := by
  have hd := hC3.differentiableOn_iteratedDerivWithin (m := m) (by exact_mod_cast hm)
    (uniqueDiffOn_winC3 ha) y hy
  rw [iteratedDerivWithin_succ]
  exact hd.hasDerivWithinAt

theorem mem_nhds_winC3 {a y : ℝ} (hy : y ∈ Ioo (1 - a) (1 + a)) : winC3 a ∈ 𝓝 y :=
  Icc_mem_nhds hy.1 hy.2

/-- **`|g''(t) − g''(1)| ≤ Γ₃|t − 1|`** on the closed window, derivatives within it. -/
theorem abs_g2W_sub_le {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    {t : ℝ} (ht : t ∈ winC3 a) :
    |iteratedDerivWithin 2 g (winC3 a) t - iteratedDerivWithin 2 g (winC3 a) 1|
      ≤ Gamma3W g a * |t - 1| := by
  have := (convex_Icc (1 - a) (1 + a)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := iteratedDerivWithin 2 g (winC3 a)) (f' := iteratedDerivWithin 3 g (winC3 a))
    (C := Gamma3W g a)
    (fun x hx => hasDerivWithinAt_iteratedDerivWithin_winC3 ha hC3 (m := 2) (by norm_num) hx)
    (fun x hx => by simpa only [Real.norm_eq_abs] using abs_g3W_le ha hC3 hx)
    (one_mem_winC3 ha.le) ht
  simpa only [Real.norm_eq_abs] using this

/-- **`theo:local_convergence_full`, the `C³` hypothesis on the closed window read as the Taylor
bound Step 1 uses** (Taylor's formula in `theo:gd_diffusion_full`'s proof):
for any `g'` of `g` on `[1−a,1+a]` (one-sided at the ends) with `g'(1) = 0`,
`|g'(y) − g''(1)(y−1)| ≤ (Γ₃/2)(y−1)²` for `|y − 1| ≤ a`. -/
theorem taylor_of_C3On {g gd : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) (hg1 : gd 1 = 0) :
    ∀ y : ℝ, |y - 1| ≤ a →
      |gd y - iteratedDerivWithin 2 g (winC3 a) 1 * (y - 1)| ≤ Gamma3W g a / 2 * (y - 1) ^ 2 := by
  have hU := uniqueDiffOn_winC3 ha
  set d1 := iteratedDerivWithin 1 g (winC3 a) with hd1
  set d2 := iteratedDerivWithin 2 g (winC3 a) with hd2
  set g2 := d2 1 with hg2def
  have hgd_eq : ∀ y ∈ winC3 a, gd y = d1 y := by
    intro y hy
    rw [hd1, iteratedDerivWithin_one]
    exact ((hgd y hy).derivWithin (hU y hy)).symm
  have hcont : ContinuousOn d1 (winC3 a) :=
    hC3.continuousOn_iteratedDerivWithin (m := 1) (by norm_num) hU
  have hint : ∀ y ∈ Ioo (1 - a) (1 + a), HasDerivAt d1 (d2 y) y := fun y hy =>
    (hasDerivWithinAt_iteratedDerivWithin_winC3 ha hC3 (m := 1) (by norm_num)
      (Ioo_subset_Icc_self hy)).hasDerivAt (mem_nhds_winC3 hy)
  intro y hy
  have hyI : y ∈ winC3 a := ⟨by linarith [(abs_le.mp hy).1], by linarith [(abs_le.mp hy).2]⟩
  rw [hgd_eq y hyI]
  have hd1one : d1 1 = 0 := by rw [← hgd_eq 1 (one_mem_winC3 ha.le)]; exact hg1
  rcases le_total 1 y with h1y | hy1
  · have hb : 0 ≤ y - 1 := by linarith
    have hmem : ∀ s ∈ Icc (0:ℝ) (y - 1), 1 + s ∈ winC3 a := by
      intro s hs
      have := abs_le.mp hy
      exact ⟨by linarith [hs.1], by linarith [hs.2, this.2]⟩
    have key := abs_le_quadratic_of_deriv_Ico (e := fun s => d1 (1 + s) - g2 * s)
      (e' := fun s => d2 (1 + s) - g2) (M := Gamma3W g a) hb
      (by
        refine ContinuousOn.sub ?_ (continuousOn_const.mul continuousOn_id)
        exact hcont.comp (continuousOn_const.add continuousOn_id) (fun s hs => hmem s hs))
      (fun s hs => by
        have hs' : 1 + s ∈ Ioo (1 - a) (1 + a) := by
          have := abs_le.mp hy
          exact ⟨by linarith [hs.1], by linarith [hs.2, this.2]⟩
        have hd := hint (1 + s) hs'
        have hc : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
        have hcomp := hd.comp s hc
        have hlin : HasDerivAt (fun s : ℝ => g2 * s) g2 s := by
          simpa only [mul_one] using (hasDerivAt_id' s).const_mul g2
        simpa only [mul_one, Function.comp_def] using hcomp.fun_sub hlin)
      (by simp only [add_zero, mul_zero, sub_zero, hd1one])
      (fun s hs => by
        have h := abs_g2W_sub_le ha hC3 (hmem s (Ico_subset_Icc_self hs))
        have hs0 : |1 + s - 1| = s := by
          rw [show 1 + s - 1 = s by ring, abs_of_nonneg hs.1]
        rwa [hs0] at h)
    have hy' : 1 + (y - 1) = y := by ring
    simpa only [hy'] using key
  · have hb : 0 ≤ 1 - y := by linarith
    have hmem : ∀ s ∈ Icc (0:ℝ) (1 - y), 1 - s ∈ winC3 a := by
      intro s hs
      have := abs_le.mp hy
      exact ⟨by linarith [hs.2, this.1], by linarith [hs.1]⟩
    have key := abs_le_quadratic_of_deriv_Ico (e := fun s => d1 (1 - s) + g2 * s)
      (e' := fun s => -d2 (1 - s) + g2) (M := Gamma3W g a) hb
      (by
        refine ContinuousOn.add ?_ (continuousOn_const.mul continuousOn_id)
        exact hcont.comp (continuousOn_const.sub continuousOn_id) (fun s hs => hmem s hs))
      (fun s hs => by
        have hs' : 1 - s ∈ Ioo (1 - a) (1 + a) := by
          have := abs_le.mp hy
          exact ⟨by linarith [hs.2, this.1], by linarith [hs.1]⟩
        have hd := hint (1 - s) hs'
        have hc : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := (hasDerivAt_id' s).const_sub 1
        have hcomp := hd.comp s hc
        have hlin : HasDerivAt (fun s : ℝ => g2 * s) g2 s := by
          simpa only [mul_one] using (hasDerivAt_id' s).const_mul g2
        have hsum := hcomp.fun_add hlin
        refine hsum.congr_deriv ?_
        ring)
      (by simp only [sub_zero, mul_zero, add_zero, hd1one])
      (fun s hs => by
        have h := abs_g2W_sub_le ha hC3 (hmem s (Ico_subset_Icc_self hs))
        have hs0 : |1 - s - 1| = s := by
          rw [show 1 - s - 1 = -s by ring, abs_neg, abs_of_nonneg hs.1]
        rw [hs0] at h
        rw [show -d2 (1 - s) + g2 = -(d2 (1 - s) - g2) by ring, abs_neg]
        exact h)
    have hy' : 1 - (1 - y) = y := by ring
    have hsq : (1 - y) ^ 2 = (y - 1) ^ 2 := by ring
    have hlin : d1 y + g2 * (1 - y) = d1 y - g2 * (y - 1) := by ring
    simpa only [hy', hsq, hlin] using key

/-- At the interior point `1`, the derivatives within the window are the classical ones:
`g'(1) = gd 1` and `g''(1) = iteratedDerivWithin 2 g [1−a,1+a] 1`. -/
theorem deriv_one_eq_of_C3On {g gd : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) :
    deriv g 1 = gd 1 ∧ deriv (deriv g) 1 = iteratedDerivWithin 2 g (winC3 a) 1 := by
  have hU := uniqueDiffOn_winC3 ha
  have h1 : (1 : ℝ) ∈ Ioo (1 - a) (1 + a) := ⟨by linarith, by linarith⟩
  have hev : deriv g =ᶠ[𝓝 1] iteratedDerivWithin 1 g (winC3 a) := by
    filter_upwards [isOpen_Ioo.mem_nhds h1] with y hy
    rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds (mem_nhds_winC3 hy)]
  refine ⟨?_, ?_⟩
  · rw [← derivWithin_of_mem_nhds (mem_nhds_winC3 h1)]
    exact (hgd 1 (one_mem_winC3 ha.le)).derivWithin (hU 1 (one_mem_winC3 ha.le))
  · rw [hev.deriv_eq, ← derivWithin_of_mem_nhds (mem_nhds_winC3 h1), ← iteratedDerivWithin_succ]

/-- **`theo:local_convergence_full`, the two-sided reading of `C³` is a special case**: `C³` at
every point of the closed window gives
`C³` on it, `g' = deriv g` a derivative within it, and the same `Γ₃`. -/
theorem C3On_of_C3 {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y) :
    ContDiffOn ℝ 3 g (winC3 a)
      ∧ (∀ y ∈ winC3 a, HasDerivWithinAt g (deriv g y) (winC3 a) y)
      ∧ Gamma3W g a = Gamma3 g a := by
  refine ⟨fun y hy => (hC3 y hy).contDiffWithinAt, fun y hy =>
    ((hC3 y hy).differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt, ?_⟩
  simp only [Gamma3W, Gamma3]
  congr 1
  refine Set.image_congr fun y hy => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_winC3 ha) (hC3 y hy) hy,
    iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]

/-- **The derivative hypothesis is always dischargeable**: under `C³` on the window, the
within-derivative `derivWithin g [1−a,1+a]` is a derivative of `g` there, one-sided at the ends. -/
theorem hasDerivWithinAt_derivWithin_of_C3On {g : ℝ → ℝ} {a : ℝ}
    (hC3 : ContDiffOn ℝ 3 g (winC3 a)) :
    ∀ y ∈ winC3 a, HasDerivWithinAt g (derivWithin g (winC3 a) y) (winC3 a) y := fun y hy =>
  ((hC3.differentiableOn (by norm_num)) y hy).hasDerivWithinAt

/-- **`theo:training_speed_full` item 2, `Γ₃ = 48 + 32 log 2` for `g = (log x)²` at `a = 1/2`**,
in the within-window reading. -/
theorem Gamma3W_logSq : Gamma3W logSq (1/2) = 48 + 32 * Real.log 2 := by
  rw [(C3On_of_C3 (by norm_num) logSq_C3).2.2, Gamma3_logSq]

end TaylorOn

/-! ### Theorem 10 under `C³` on the closed window -/

section LocalConvergenceC3On

/-- `ε₀` of `theo:local_convergence_full` at `g''(1)` and `Γ₃ = Gamma3W g a`. -/
noncomputable def eps0W (g : ℝ → ℝ) (a wmin wsup Bhat lamMin : ℝ) : ℝ :=
  eps0 (epsW a (deriv (deriv g) 1) wmin (Kexp (deriv (deriv g) 1) a (Gamma3W g a) wsup) Bhat)
    (Cinf lamMin) (C7 (C6 (Cg (deriv (deriv g) 1) a (Gamma3W g a)) wsup) (deriv (deriv g) 1) wmin)
    (rhoL (deriv (deriv g) 1) wmin Bhat) (C6 (Cg (deriv (deriv g) 1) a (Gamma3W g a)) wsup)

/-- `C := max(1, C₇)` at `g''(1)`, `Γ₃ = Gamma3W g a`. -/
noncomputable def CW (g : ℝ → ℝ) (a wmin wsup : ℝ) : ℝ :=
  max 1 (C7 (C6 (Cg (deriv (deriv g) 1) a (Gamma3W g a)) wsup) (deriv (deriv g) 1) wmin)

/-- `γ₀` at `g''(1)`, `Γ₃ = Gamma3W g a`. -/
noncomputable def gamma0W (g : ℝ → ℝ) (a wmin wsup Bhat : ℝ) : ℝ :=
  gamma0 (deriv (deriv g) 1) wmin
    (Lgd (deriv (deriv g) 1) wsup (Kexp (deriv (deriv g) 1) a (Gamma3W g a) wsup)
      (epsW a (deriv (deriv g) 1) wmin (Kexp (deriv (deriv g) 1) a (Gamma3W g a) wsup) Bhat))

/-- **`theo:local_convergence_full`, "depending only on `g''(1)`, `sup_{[1−a,1+a]}|g'''|`, `a`,
`w_min`, `‖w‖_{L^∞}`, `B̂`, `C_∞`"**, as a congruence. -/
theorem constW_congr {g g' : ℝ → ℝ} {a : ℝ} (h2 : deriv (deriv g) 1 = deriv (deriv g') 1)
    (h3 : Gamma3W g a = Gamma3W g' a) (wmin wsup Bhat lamMin : ℝ) :
    eps0W g a wmin wsup Bhat lamMin = eps0W g' a wmin wsup Bhat lamMin
      ∧ CW g a wmin wsup = CW g' a wmin wsup
      ∧ gamma0W g a wmin wsup Bhat = gamma0W g' a wmin wsup Bhat := by
  simp only [eps0W, CW, gamma0W, h2, h3]
  exact ⟨trivial, trivial, trivial⟩

/-- Under the two-sided reading the constants are `C3Wrappers`'. -/
theorem constW_eq_constC3 {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y) (wmin wsup Bhat lamMin : ℝ) :
    eps0W g a wmin wsup Bhat lamMin = eps0C3 g a wmin wsup Bhat lamMin
      ∧ CW g a wmin wsup = CC3 g a wmin wsup
      ∧ gamma0W g a wmin wsup Bhat = gamma0C3 g a wmin wsup Bhat := by
  simp only [eps0W, CW, gamma0W, eps0C3, CC3, gamma0C3, (C3On_of_C3 ha hC3).2.2]
  exact ⟨trivial, trivial, trivial⟩

/-- **`theo:training_speed_full` item 2, `ε₀`**: Theorem 10's radius for `g = (log x)²` at `a = 1/2` is
`C3Wrappers.eps0Gamma3`. -/
theorem eps0W_logSq (wmin wsup Bhat lamMin : ℝ) :
    eps0W logSq (1/2) wmin wsup Bhat lamMin = eps0Gamma3 wmin wsup Bhat lamMin := by
  simp only [eps0W, eps0Gamma3, logSq_deriv2_one, Gamma3W_logSq]

variable {V : Type*} [Fintype V]

/-- The `C³`-on-the-window hypotheses, turned into the Taylor bound the library consumes, at `gd`
and at the classical `g''(1)`. -/
theorem taylor_bundle_of_C3On {g gd : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) (hg1 : deriv g 1 = 0) :
    ∀ y : ℝ, |y - 1| ≤ a →
      |gd y - deriv (deriv g) 1 * (y - 1)| ≤ Gamma3W g a / 2 * (y - 1) ^ 2 := by
  obtain ⟨h1, h2⟩ := deriv_one_eq_of_C3On ha hgd
  rw [h2]
  exact taylor_of_C3On ha hC3 hgd (by rw [← h1]; exact hg1)

/-- **`theo:local_convergence_full`, the flow clause, under `C³` on the closed window**: every
gradient flow driven by a derivative `gd` of `g` on `[1−a,1+a]` (one-sided at the ends), from
`‖h₀‖ ≤ ε₀`, converges to `c_∞λ` with the printed `C` and rate. -/
theorem local_convergence_full_C3On {K : V → V → ℝ} {lam w : V → ℝ} {g gd : ℝ → ℝ}
    {h : ℝ → V → ℝ} {a wsup wmin Bhat lamMin : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hnorm0 : Graph.nrmL2 lam (h 0) ≤ eps0W g a wmin wsup Bhat lamMin) :
    ∃ cinf : ℝ,
      |cinf - 1 - Graph.meanL2 lam (h 0)|
          ≤ CW g a wmin wsup * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (fun x => h t x - (cinf - 1))
            ≤ 2 * Real.exp (-(rhoL (deriv (deriv g) 1) wmin Bhat * t / 2))
                * Graph.nrmL2 lam (perpL2 lam (h 0)) :=
  local_convergence_full_C hK hinv hlam htot hlmin0 hlmin hg2 (Gamma3W_nonneg ha hC3) ha hwsup
    hwmin0 hwmin hB1 hcoer (taylor_bundle_of_C3On ha hC3 hgd hg1) hflow hnorm0

/-- **`theo:local_convergence_full`, the constants, under `C³` on the closed window**:
`ε₀ ∈ (0, a/(16C_∞)]`, `C ≥ 1`, `γ₀ > 0`. -/
theorem constW_bounds {lam w : V → ℝ} {g : ℝ → ℝ} {a wsup wmin Bhat lamMin : ℝ}
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a)) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hB1 : 1 ≤ Bhat) :
    eps0W g a wmin wsup Bhat lamMin ∈ Set.Ioc 0 (a / (16 * Cinf lamMin))
      ∧ 1 ≤ CW g a wmin wsup ∧ 0 < gamma0W g a wmin wsup Bhat :=
  ⟨eps0_mem_Ioc htot hlmin0 hg2 (Gamma3W_nonneg ha hC3) ha hwsup hwmin0 hwmin hB1,
    one_le_max_C7 _ _ _,
    gamma0_pos_of_weights htot hg2 (Gamma3W_nonneg ha hC3) ha.le hwsup hwmin0 hwmin
      (le_trans zero_le_one hB1)⟩

/-- **`theo:local_convergence_full`, the gradient-descent clause, under `C³` on the closed
window**: the descent driven by `gd` is well defined at every step and contracts by
`1 − γϱ/4`. -/
theorem local_convergence_gd_C3On {K : V → V → ℝ} {lam w : V → ℝ} {g gd : ℝ → ℝ}
    {hk : ℕ → V → ℝ} {a wsup wmin Bhat lamMin gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (hstep : ∀ k : ℕ, hk (k + 1) = fun x =>
      hk k x - gam * lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + hk k z) x)
    (hgam0 : 0 ≤ gam) (hgam : gam ≤ gamma0W g a wmin wsup Bhat)
    (hnorm0 : Graph.nrmL2 lam (hk 0) ≤ eps0W g a wmin wsup Bhat lamMin) :
    ∀ k : ℕ, ((∀ x : V, 0 < 1 + hk k x)
      ∧ (∀ x : V, |ratio K lam (fun z => 1 + hk k z) x - 1| ≤ 2 * a / 3)
      ∧ ∀ d : V → ℝ,
          HasDerivAt
            (fun t : ℝ => loss K lam (fun z => lam z * w z) (fun x => 1 + hk k x + t * d x) g)
            (Graph.ipL2 lam (lossGrad K lam (fun z => lam z * w z) gd
              fun z => 1 + hk k z) d) 0)
      ∧ Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))
          ≤ (1 - gam * rhoL (deriv (deriv g) 1) wmin Bhat / 4)
              * Graph.nrmL2 lam (perpL2 lam (hk k)) := by
  have hM3 := Gamma3W_nonneg ha hC3
  have htay := taylor_bundle_of_C3On ha hC3 hgd hg1
  have hg : ∀ y : ℝ, |y - 1| < a → HasDerivAt g (gd y) y := fun y hy => by
    have hy' : y ∈ Ioo (1 - a) (1 + a) :=
      ⟨by linarith [(abs_lt.mp hy).1], by linarith [(abs_lt.mp hy).2]⟩
    exact (hgd y (Ioo_subset_Icc_self hy')).hasDerivAt (mem_nhds_winC3 hy')
  intro k
  exact ⟨local_convergence_gd_welldefined hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha hwsup
      hwmin0 hwmin hB1 hcoer hg htay hstep hgam0 hgam hnorm0 k,
    local_convergence_gd hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha.le hwsup hwmin0 hwmin hB1
      hcoer htay hstep hgam0 hgam hnorm0 k⟩

end LocalConvergenceC3On

/-! ### Existence of the flow near `λ`, for a generator `C³` on the window only -/

section ExistenceNear

variable {V : Type*} [Fintype V]

/-- **`D(u)` is `C¹` in `u` at a positive `u` whose ratios all sit where `g'` is `C¹`**
(`FlowExistence.contDiffAt_lossGrad`, with `g'` asked `C¹` only at the values the ratio takes). -/
theorem contDiffAt_lossGrad_local {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : V → ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x)
    (hgd : ∀ y, ContDiffAt ℝ 1 gd (ratio K lam u y)) :
    ContDiffAt ℝ 1 (fun v : V → ℝ => lossGrad K lam nu gd v) u := by
  have hden : ∀ y, lam y * u y ≠ 0 := fun y => (mul_pos (hlam y) (hu y)).ne'
  have hr : ∀ y, ContDiffAt ℝ 1 (fun v : V → ℝ => ratio K lam v y) u :=
    fun y => contDiffAt_ratio y (hden y)
  have hphi : ∀ y, ContDiffAt ℝ 1
      (fun v : V → ℝ => gd (ratio K lam v y) * (nu y / (lam y * v y))) u := by
    intro y
    refine ContDiffAt.mul ?_ ?_
    · exact (hgd y).comp u (hr y)
    · exact contDiffAt_const.div (contDiff_const.mul (contDiff_apply ℝ ℝ y)).contDiffAt (hden y)
  refine contDiffAt_pi.2 fun x => ?_
  simp only [lossGrad, lossGradDensity, gradDensity, funAct]
  refine ContDiffAt.sub ?_ ((hr x).mul (hphi x))
  exact ContDiffAt.sum fun y _ => contDiffAt_const.mul (hphi y)

/-- **`g'` is `C¹` at every interior point of the window**: it agrees near such a point with the
within-derivative, which is `C²` on the closed window. -/
theorem contDiffAt_gd_of_C3On {g gd : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    {y : ℝ} (hy : y ∈ Ioo (1 - a) (1 + a)) : ContDiffAt ℝ 1 gd y := by
  have hU := uniqueDiffOn_winC3 ha
  have h2 : ContDiffAt ℝ 2 (derivWithin g (winC3 a)) y :=
    (hC3.derivWithin hU (m := 2) (by norm_num)).contDiffAt (mem_nhds_winC3 hy)
  refine (h2.of_le (by norm_num)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
  exact ((hgd z (Ioo_subset_Icc_self hz)).derivWithin (hU z (Ioo_subset_Icc_self hz))).symm

omit [Fintype V] in
/-- On the box `[1−e, 1+e]^V`, `e ≤ 1/4`, the density is positive. -/
theorem pos_of_mem_box {e : ℝ} (he : e ≤ 1 / 4) {v : V → ℝ}
    (hv : v ∈ densityBox V (1 - e) (1 + e)) (x : V) : 0 < v x := by
  have := ((mem_densityBox.1 hv) x).1
  linarith

/-- On the box `[1−e, 1+e]^V`, `e ≤ min(a,1)/4`, every ratio lies in `[1 − 2a/3, 1 + 2a/3]`. -/
theorem abs_ratio_le_of_mem_box {K : V → V → ℝ} {lam : V → ℝ} {a e : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (he0 : 0 ≤ e) (he : e ≤ min a 1 / 4) {v : V → ℝ}
    (hv : v ∈ densityBox V (1 - e) (1 + e)) (y : V) :
    |ratio K lam v y - 1| ≤ 2 * a / 3 := by
  have hh : ∀ x, |v x - 1| ≤ e := fun x => by
    obtain ⟨h1, h2⟩ := (mem_densityBox.1 hv) x
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hfun : (fun x => 1 + (v x - 1)) = v := by funext x; ring
  have := abs_ratio_sub_one_le_two_a_div_three (h := fun x => v x - 1) hKnn hinv hh he0 he
    (hlam y).ne'
  rwa [hfun] at this

/-- **`D` is Lipschitz on the box `[1−e, 1+e]^V`**, `e ≤ min(a,1)/4`, for `g` `C³` on the window. -/
theorem exists_lipschitzOnWith_lossGrad_box {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ}
    {a e : ℝ} (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (he0 : 0 ≤ e) (he : e ≤ min a 1 / 4) :
    ∃ L, LipschitzOnWith L (fun v : V → ℝ => lossGrad K lam nu gd v)
      (densityBox V (1 - e) (1 + e)) := by
  have he1 : e ≤ 1 / 4 := le_trans he (by have := min_le_right a 1; linarith)
  have hC : ContDiffOn ℝ 1 (fun v : V → ℝ => lossGrad K lam nu gd v)
      (densityBox V (1 - e) (1 + e)) := by
    intro v hv
    refine (contDiffAt_lossGrad_local hlam (pos_of_mem_box he1 hv) fun y => ?_).contDiffWithinAt
    have hr := abs_ratio_le_of_mem_box hKnn hinv hlam he0 he hv y
    exact contDiffAt_gd_of_C3On ha hC3 hgd
      ⟨by linarith [(abs_le.mp hr).1], by linarith [(abs_le.mp hr).2]⟩
  exact hC.exists_lipschitzOnWith one_ne_zero (convex_densityBox _ _) (isCompact_densityBox _ _)

/-- `ḣ = −D` at one time gives `ṁ = −ΠD` there. -/
theorem hasDerivAt_mean_of_at {lam : V → ℝ} {h : ℝ → V → ℝ} {Dv : V → ℝ} {t : ℝ}
    (hd : ∀ x, HasDerivAt (fun s : ℝ => h s x) (-Dv x) t) :
    HasDerivAt (fun s : ℝ => Graph.meanL2 lam (h s)) (-Graph.meanL2 lam Dv) t := by
  have hsum : HasDerivAt (fun s : ℝ => ∑ x, lam x * h s x) (∑ x, lam x * -Dv x) t :=
    HasDerivAt.fun_sum fun x _ => (hd x).const_mul (lam x)
  have hval : (∑ x, lam x * -Dv x) = -Graph.meanL2 lam Dv := by
    simp only [Graph.meanL2, mul_neg, Finset.sum_neg_distrib]
  rw [hval] at hsum
  exact hsum

/-- `ḣ = −D` at one time gives `d/dt‖h^⊥‖² = −2⟨h^⊥, D⟩` there (`LocalEnergy.hasDerivAt_perp_sq`
with the ODE asked at that time only). -/
theorem hasDerivAt_perp_sq_of_at {lam : V → ℝ} {h : ℝ → V → ℝ} {Dv : V → ℝ} {t : ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1)
    (hd : ∀ x, HasDerivAt (fun s : ℝ => h s x) (-Dv x) t) :
    HasDerivAt (fun s : ℝ => Graph.nrmL2 lam (perpL2 lam (h s)) ^ 2)
      (-(2 * Graph.ipL2 lam (perpL2 lam (h t)) Dv)) t := by
  set md : ℝ := Graph.meanL2 lam Dv with hmd
  have hdp : ∀ x : V, HasDerivAt (fun s : ℝ => perpL2 lam (h s) x) (-Dv x - -md) t := by
    intro x
    simp only [perpL2_apply]
    exact (hd x).sub (hasDerivAt_mean_of_at hd)
  have hsq : (fun s : ℝ => Graph.nrmL2 lam (perpL2 lam (h s)) ^ 2)
      = fun s : ℝ => ∑ x, lam x * (perpL2 lam (h s) x * perpL2 lam (h s) x) := by
    funext s
    rw [Graph.sq_nrmL2 hnn]
    rfl
  rw [hsq]
  have hsum : HasDerivAt (fun s : ℝ => ∑ x, lam x * (perpL2 lam (h s) x * perpL2 lam (h s) x))
      (∑ x, lam x * ((-Dv x - -md) * perpL2 lam (h t) x
        + perpL2 lam (h t) x * (-Dv x - -md))) t :=
    HasDerivAt.fun_sum fun x _ => HasDerivAt.const_mul (lam x) ((hdp x).fun_mul (hdp x))
  have hval : (∑ x, lam x * ((-Dv x - -md) * perpL2 lam (h t) x
        + perpL2 lam (h t) x * (-Dv x - -md)))
      = -(2 * Graph.ipL2 lam (perpL2 lam (h t)) Dv) := by
    have hexp : ∀ x : V, lam x * ((-Dv x - -md) * perpL2 lam (h t) x
        + perpL2 lam (h t) x * (-Dv x - -md))
        = 2 * md * (lam x * perpL2 lam (h t) x)
          - 2 * (lam x * (perpL2 lam (h t) x * Dv x)) := fun x => by ring
    rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h0 : (∑ x, lam x * perpL2 lam (h t) x) = 0 := meanL2_perpL2 htot (h t)
    rw [h0, mul_zero, zero_sub]
    rfl
  rwa [hval] at hsum

/-- **Step 4's inner estimate with the ODE asked on `[0,t]` only** (`LocalConvergence.sup_bootstrap_step`
on a curve that solves the gradient-flow ODE on `[0,t]` and nowhere else): on the window
`‖h_s‖_{L^∞} ≤ ε`, `s ∈ [0,t]`, `‖h_0‖ ≤ ε₀` gives `‖h_t‖_{L^∞} ≤ ε/2`.

Steps 2 and 3 are run without integrals: `‖h^⊥‖²` and `C₇‖h^⊥‖² ± m` have non-positive
derivative on the window (`d/dt‖h^⊥‖² ≤ −g''(1)w_min‖Ah^⊥‖²`, `|ṁ| ≤ C₆‖Ah^⊥‖²`,
`C₇g''(1)w_min = C₆`), so they are antitone there — the monotonicity form of the paper's Step 3. -/
theorem sup_bootstrap_step_on {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat lamMin t : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hnorm0 : Graph.nrmL2 lam (h 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) (Cinf lamMin)
          (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup))
    (ht0 : 0 ≤ t)
    (hode : ∀ s ∈ Set.Icc (0:ℝ) t, ∀ x, HasDerivAt (fun r : ℝ => h r x)
      (-lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h s z) x) s)
    (hwin : ∀ s ∈ Set.Icc (0:ℝ) t, ∀ x, |h s x| ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) :
    ∀ x, |h t x| ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat / 2 := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hwsup0 : 0 ≤ wsup := (wsup_pos hwmin0 (hwmin x0) (hwsup x0)).le
  have hB0 : 0 ≤ Bhat := le_trans zero_le_one hB1
  have hgw : 0 < g2 * wmin := mul_pos hg2 hwmin0
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2.le hM3 ha0 hwsup0
  have hew0 : 0 ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat :=
    epsW_nonneg ha0 hg2.le hwmin0.le hK0 hB0
  have hewA := epsW_le_window a g2 wmin (Kexp g2 a M3 wsup) Bhat
  have hewB := epsW_le_eps1 a g2 wmin (Kexp g2 a M3 wsup) Bhat
  set c6 := C6 (Cg g2 a M3) wsup with hc6def
  set c7 := C7 c6 g2 wmin with hc7def
  have hc60 : 0 ≤ c6 := by simp only [hc6def, C6, Cg]; positivity
  have hc70 : 0 ≤ c7 := by simp only [hc7def, C7]; positivity
  have hc76 : c7 * (g2 * wmin) = c6 := by
    simp only [hc7def, C7]; field_simp
  have hrho0 : 0 ≤ rhoL g2 wmin Bhat := rhoL_nonneg hg2.le hwmin0.le
  have hCi1 : 1 ≤ Cinf lamMin := one_le_Cinf hlmin0 hlmin htot
  have hCi0 : 0 < Cinf lamMin := Cinf_pos hlmin0
  -- the three functions and their derivatives on `[0,t]`
  set F : ℝ → ℝ := fun s => Graph.nrmL2 lam (perpL2 lam (h s)) ^ 2 with hFdef
  set m : ℝ → ℝ := fun s => Graph.meanL2 lam (h s) with hmdef
  set Dv : ℝ → V → ℝ := fun s => lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h s z)
    with hDvdef
  set E : ℝ → ℝ := fun s => Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2 with hEdef
  have hFd : ∀ s ∈ Set.Icc (0:ℝ) t,
      HasDerivAt F (-(2 * Graph.ipL2 lam (perpL2 lam (h s)) (Dv s))) s :=
    fun s hs => hasDerivAt_perp_sq_of_at hnn htot (hode s hs)
  have hmd : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivAt m (-Graph.meanL2 lam (Dv s)) s :=
    fun s hs => hasDerivAt_mean_of_at (hode s hs)
  have hen : ∀ s ∈ Set.Icc (0:ℝ) t, g2 * wmin / 2 * E s ≤ Graph.ipL2 lam (perpL2 lam (h s)) (Dv s) :=
    fun s hs => energy_lower hK hinv hlam hg2.le hM3 ha0 hwsup0 hwsup hwmin0.le hwmin hB0 hcoer
      htaylor (hwin s hs) hew0 hewA hewB
  have hdr : ∀ s ∈ Set.Icc (0:ℝ) t, |Graph.meanL2 lam (Dv s)| ≤ c6 * E s :=
    fun s hs => abs_deriv_mean_le hK.nonneg hinv hlam hg2.le hM3 ha0 hwsup0 hwsup htaylor
      (hwin s hs) hew0 hewA
  have hE0 : ∀ s, 0 ≤ E s := fun s => sq_nonneg _
  -- antitone on `[0,t]`
  have hanti : ∀ (G : ℝ → ℝ) (G' : ℝ → ℝ), (∀ s ∈ Set.Icc (0:ℝ) t, HasDerivAt G (G' s) s) →
      (∀ s ∈ Set.Icc (0:ℝ) t, G' s ≤ 0) → G t ≤ G 0 := by
    intro G G' hG hG'
    have hA : AntitoneOn G (Set.Icc 0 t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
        (fun s hs => (hG s hs).continuousAt.continuousWithinAt)
        (fun s hs => (hG s (interior_subset hs)).differentiableAt.differentiableWithinAt)
        fun s hs => ?_
      rw [(hG s (interior_subset hs)).deriv]
      exact hG' s (interior_subset hs)
    exact hA ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  have hFt : F t ≤ F 0 := hanti F _ hFd fun s hs => by
    have h1 := hen s hs
    have h2 := mul_nonneg hgw.le (hE0 s)
    linarith
  have hGp : c7 * F t + m t ≤ c7 * F 0 + m 0 :=
    hanti (fun s => c7 * F s + m s) _ (fun s hs => ((hFd s hs).const_mul c7).add (hmd s hs))
      fun s hs => by
        have h1 := mul_le_mul_of_nonneg_left (hen s hs) hc70
        have h2 := (abs_le.mp (hdr s hs)).1
        have h3 : c7 * (g2 * wmin / 2 * E s) = c6 * E s / 2 := by rw [← hc76]; ring
        linarith
  have hGm : c7 * F t - m t ≤ c7 * F 0 - m 0 :=
    hanti (fun s => c7 * F s - m s) _ (fun s hs => ((hFd s hs).const_mul c7).sub (hmd s hs))
      fun s hs => by
        have h1 := mul_le_mul_of_nonneg_left (hen s hs) hc70
        have h2 := (abs_le.mp (hdr s hs)).2
        have h3 : c7 * (g2 * wmin / 2 * E s) = c6 * E s / 2 := by rw [← hc76]; ring
        linarith
  have hFt0 : 0 ≤ F t := sq_nonneg _
  have hcF : 0 ≤ c7 * F t := mul_nonneg hc70 hFt0
  have hmt0 : |m t - m 0| ≤ c7 * F 0 := by
    rw [abs_le]; constructor <;> linarith
  -- the arithmetic of `sup_bootstrap_step`
  set eW := epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat with heWdef
  set Ci := Cinf lamMin with hCidef
  set e0 := eps0 eW Ci c7 (rhoL g2 wmin Bhat) c6 with he0def
  have he0A : e0 ≤ eW / (2 * Ci * (2 + c7)) := eps0_le_basin _ _ _ _ _
  have he01 : e0 ≤ 1 := eps0_le_one _ _ _ _ _
  have he00 : 0 ≤ e0 := eps0_nonneg hew0 hCi0 hc70 hrho0 hc60
  have hP0 : Graph.nrmL2 lam (perpL2 lam (h 0)) ≤ Graph.nrmL2 lam (h 0) :=
    nrmL2_perpL2_le hnn htot (h 0)
  have hm0 : |m 0| ≤ Graph.nrmL2 lam (h 0) := abs_meanL2_le_nrmL2 hnn htot (h 0)
  have hPe : Graph.nrmL2 lam (perpL2 lam (h 0)) ≤ e0 := le_trans hP0 hnorm0
  have hP0nn : 0 ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) := Graph.nrmL2_nonneg _ _
  have hsq0 : F 0 ≤ e0 := by
    have h1 : Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 ≤ e0 * 1 := by
      rw [sq]
      exact mul_le_mul hPe (le_trans hPe he01) hP0nn he00
    simpa only [hFdef, mul_one] using h1
  have hPt : Graph.nrmL2 lam (perpL2 lam (h t)) ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) :=
    (pow_le_pow_iff_left₀ (Graph.nrmL2_nonneg _ _) hP0nn two_ne_zero).1 hFt
  have hmt : |m t| ≤ e0 + c7 * e0 := by
    have h1 : |m t| - |m 0| ≤ |m t - m 0| := abs_sub_abs_le_abs_sub _ _
    have h2 : c7 * F 0 ≤ c7 * e0 := mul_le_mul_of_nonneg_left hsq0 hc70
    linarith
  intro x
  have hsplit := abs_le_Cinf_mean_add_perp hlmin0 hlmin htot (h t) x
  have hsum : |Graph.meanL2 lam (h t)| + Graph.nrmL2 lam (perpL2 lam (h t)) ≤ e0 * (2 + c7) := by
    have h1 : |Graph.meanL2 lam (h t)| = |m t| := rfl
    have h2 : e0 * (2 + c7) = (e0 + c7 * e0) + e0 := by ring
    rw [h1, h2]
    linarith
  have hpos : (0 : ℝ) < 2 * Ci * (2 + c7) := by positivity
  have hkey : e0 * (2 * Ci * (2 + c7)) ≤ eW := (le_div_iff₀ hpos).mp he0A
  have hfin : Ci * (e0 * (2 + c7)) = e0 * (2 * Ci * (2 + c7)) / 2 := by ring
  calc |h t x| ≤ Ci * (|Graph.meanL2 lam (h t)| + Graph.nrmL2 lam (perpL2 lam (h t))) := hsplit
    _ ≤ Ci * (e0 * (2 + c7)) := mul_le_mul_of_nonneg_left hsum hCi0.le
    _ ≤ eW / 2 := by rw [hfin]; linarith

/-- **`theo:local_convergence_full`, the flow clause with existence, under `C³` on the closed
window** (`proofs.tex:666–672`): from every `h₀` with `‖h₀‖_{L²(λ)} ≤ ε₀`, the nonlinear gradient
flow `μ̇ = −∇^λ𝓛_{g,ν}(μ)` from `μ₀ = (1+h₀)λ`, driven by a derivative `gd` of `g` on
`[1−a,1+a]`, **exists**; it stays positive with every ratio within `2a/3` of `1`; it is **unique**
among all solutions of the flow predicate from `μ₀`; and it converges to a balanced flow `c_∞λ`
with `|c_∞ − 1 − Πh₀| ≤ C‖h₀ − Πh₀‖²` and `‖h_t − (c_∞−1)‖ ≤ 2e^{−ϱt/2}‖h₀ − Πh₀‖`.

Existence is the route of `FlowExistence.lean`: the field clamped to the box `[1−ε, 1+ε]^V`
(`ε` Step 4's window) is globally Lipschitz and bounded, so a global solution exists; the box is
never left on `[0,∞)` by `sup_bootstrap_step_on`, so the clamp is inactive and the curve solves
the true ODE. Uniqueness: every solution from `μ₀` stays in the box (`LocalConvergence.sup_global`),
where the field is Lipschitz; Grönwall. -/
theorem local_convergence_full_exists {K : V → V → ℝ} {lam w : V → ℝ} {g gd : ℝ → ℝ}
    {a wsup wmin Bhat lamMin : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    {h0 : V → ℝ} (hnorm0 : Graph.nrmL2 lam h0 ≤ eps0W g a wmin wsup Bhat lamMin) :
    ∃ h : ℝ → V → ℝ, h 0 = h0
      ∧ IsGradientFlow K lam (fun z => lam z * w z) gd (fun s x => 1 + h s x)
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < 1 + h t x
          ∧ |ratio K lam (fun z => 1 + h t z) x - 1| ≤ 2 * a / 3)
      ∧ (∀ h' : ℝ → V → ℝ, h' 0 = h0 →
          IsGradientFlow K lam (fun z => lam z * w z) gd (fun s x => 1 + h' s x) →
          ∀ t : ℝ, 0 ≤ t → h' t = h t)
      ∧ ∃ cinf : ℝ, Balanced K lam (fun _ => cinf)
          ∧ |cinf - 1 - Graph.meanL2 lam h0|
              ≤ CW g a wmin wsup * Graph.nrmL2 lam (perpL2 lam h0) ^ 2
            ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (fun x => h t x - (cinf - 1))
                ≤ 2 * Real.exp (-(rhoL (deriv (deriv g) 1) wmin Bhat * t / 2))
                    * Graph.nrmL2 lam (perpL2 lam h0) := by
  classical
  obtain ⟨x0⟩ := nonempty_of_total htot
  set g2 := deriv (deriv g) 1 with hg2def
  set M3 := Gamma3W g a with hM3def
  have hM3 : 0 ≤ M3 := Gamma3W_nonneg ha hC3
  have htay := taylor_bundle_of_C3On ha hC3 hgd hg1
  set nu : V → ℝ := fun z => lam z * w z with hnudef
  have hwsupp : 0 < wsup := wsup_pos hwmin0 (hwmin x0) (hwsup x0)
  have hBpos : (0 : ℝ) < Bhat := lt_of_lt_of_le zero_lt_one hB1
  set e := epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat with hedef
  have he0 : 0 < e := epsW_pos ha hg2 hwmin0 (Kexp_pos hg2 hM3 ha.le hwsupp) hBpos
  have heA : e ≤ min a 1 / 4 := epsW_le_window a g2 wmin (Kexp g2 a M3 wsup) Bhat
  have he14 : e ≤ 1 / 4 := le_trans heA (by have := min_le_right a 1; linarith)
  have hnorm0' : Graph.nrmL2 lam h0
      ≤ eps0 e (Cinf lamMin) (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat)
          (C6 (Cg g2 a M3) wsup) := hnorm0
  -- the box and its Lipschitz field
  set lo := 1 - e with hlodef
  set hi := 1 + e with hhidef
  have hlohi : lo ≤ hi := by linarith
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_lossGrad_box (nu := nu) hK.nonneg hinv hlam ha hC3 hgd
    he0.le heA (V := V)
  set F : (V → ℝ) → (V → ℝ) := fun v => -lossGrad K lam nu gd (clampBox lo hi v) with hFdef
  have hFlip : LipschitzWith L F := by
    have h1 : LipschitzOnWith (L * 1) ((fun v => lossGrad K lam nu gd v) ∘ clampBox lo hi) univ :=
      hL.comp (lipschitzWith_clampBox lo hi).lipschitzOnWith (fun v _ => clampBox_mem hlohi v)
    rw [mul_one, lipschitzOnWith_univ] at h1
    refine LipschitzWith.of_dist_le_mul fun v v' => ?_
    rw [hFdef]
    simp only
    rw [dist_neg_neg]
    exact h1.dist_le_mul v v'
  obtain ⟨C, hC⟩ := (isCompact_densityBox (V := V) lo hi).exists_bound_of_continuousOn
    hL.continuousOn
  have hM : ∀ v, ‖F v‖ ≤ (⟨max C 0, le_max_right _ _⟩ : ℝ≥0) := by
    intro v
    rw [hFdef]
    simp only [norm_neg]
    exact (hC _ (clampBox_mem hlohi v)).trans (le_max_left _ _)
  obtain ⟨α, hα0, hα⟩ := exists_forall_hasDerivAt_of_lipschitzWith hFlip hM (fun x => 1 + h0 x)
  have hαx : ∀ t x, HasDerivAt (fun s => α s x) (F (α t) x) t :=
    fun t x => hasDerivAt_pi.1 (hα t) x
  have hcont : ∀ x, Continuous fun t => α t x :=
    fun x => continuous_iff_continuousAt.2 fun t => (hαx t x).continuousAt
  set h : ℝ → V → ℝ := fun s x => α s x - 1 with hhdef
  have hαh : ∀ s, (fun z => 1 + h s z) = α s := fun s => by funext z; simp only [hhdef]; ring
  have hode_box : ∀ s, α s ∈ densityBox V lo hi → ∀ x,
      HasDerivAt (fun r => h r x) (-lossGrad K lam nu gd (fun z => 1 + h s z) x) s := by
    intro s hs x
    have hd := (hαx s x).sub_const 1
    rw [hFdef] at hd
    simp only [Pi.neg_apply, clampBox_eq hs] at hd
    rw [hαh s]
    exact hd
  have hbox_of : ∀ s, (∀ x, |h s x| ≤ e) → α s ∈ densityBox V lo hi := by
    intro s hs
    refine mem_densityBox.2 fun x => ?_
    have := abs_le.mp (hs x)
    simp only [hhdef] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hh0 : h 0 = h0 := by funext x; simp only [hhdef, hα0]; ring
  -- the bootstrap: the clamp is never active on `[0,∞)`
  have hkey : ∀ t : ℝ, 0 ≤ t → ∀ x, |h t x| ≤ e / 2 := by
    refine bootstrap_of_continuous (h := h) he0 (fun x => (hcont x).sub continuous_const) ?_ ?_
    · intro x
      rw [hh0]
      have hc70 : 0 ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin := by
        simp only [C7, C6, Cg]; positivity
      have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by simp only [C6, Cg]; positivity
      have hrho0 : 0 ≤ rhoL g2 wmin Bhat := rhoL_nonneg hg2.le hwmin0.le
      have hCi0 : 0 < Cinf lamMin := Cinf_pos hlmin0
      set c7 := C7 (C6 (Cg g2 a M3) wsup) g2 wmin with hc7def
      set Ci := Cinf lamMin with hCidef
      set e0 := eps0 e Ci c7 (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup) with he0def
      have he00 : 0 ≤ e0 := eps0_nonneg he0.le hCi0 hc70 hrho0 hc60
      have hpos : (0 : ℝ) < 2 * Ci * (2 + c7) := by positivity
      have hk : e0 * (2 * Ci * (2 + c7)) ≤ e :=
        (le_div_iff₀ hpos).mp (eps0_le_basin e Ci c7 (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup))
      have h1 : |h0 x| ≤ Ci * Graph.nrmL2 lam h0 := abs_le_Cinf_mul_nrmL2 hlmin0 hlmin _ x
      have h2 : Ci * Graph.nrmL2 lam h0 ≤ Ci * e0 := mul_le_mul_of_nonneg_left hnorm0' hCi0.le
      have h3 : 0 ≤ Ci * e0 * c7 := by positivity
      have h4 : e0 * (2 * Ci * (2 + c7)) = 4 * (Ci * e0) + 2 * (Ci * e0 * c7) := by ring
      linarith
    · intro t ht hwin
      have hwin' : ∀ s ∈ Set.Icc (0:ℝ) t, ∀ x, |h s x| ≤ e := hwin
      have hnorm00 : Graph.nrmL2 lam (h 0) ≤ eps0 e (Cinf lamMin) (C7 (C6 (Cg g2 a M3) wsup) g2 wmin)
          (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup) := by rw [hh0]; exact hnorm0'
      exact sup_bootstrap_step_on hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha.le hwsup hwmin0 hwmin
        hB1 hcoer htay hnorm00 ht (fun s hs => hode_box s (hbox_of s (hwin' s hs))) hwin'
  have hbox : ∀ t : ℝ, 0 ≤ t → ∀ x, |h t x| ≤ e := fun t ht x => by
    linarith [hkey t ht x]
  have hflow : IsGradientFlow K lam nu gd (fun s x => 1 + h s x) := by
    intro t ht x
    have hd := hode_box t (hbox_of t (hbox t ht)) x
    have hd' := hd.const_add 1
    simpa only using hd'
  -- uniqueness
  have huniq : ∀ h' : ℝ → V → ℝ, h' 0 = h0 →
      IsGradientFlow K lam nu gd (fun s x => 1 + h' s x) → ∀ t : ℝ, 0 ≤ t → h' t = h t := by
    intro h' hh'0 hflow' T hT
    have hnorm0'' : Graph.nrmL2 lam (h' 0) ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat)
        (Cinf lamMin) (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat)
        (C6 (Cg g2 a M3) wsup) := by rw [hh'0]; exact hnorm0'
    have hsup' := sup_global hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha hwsup hwmin0 hwmin hB1
      hcoer htay hflow' hnorm0''
    have hin' : ∀ s, 0 ≤ s → (fun x => 1 + h' s x) ∈ densityBox V lo hi := by
      intro s hs
      refine mem_densityBox.2 fun x => ?_
      have := abs_le.mp (hsup' s hs x)
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hin : ∀ s, 0 ≤ s → (fun x => 1 + h s x) ∈ densityBox V lo hi := by
      intro s hs
      refine mem_densityBox.2 fun x => ?_
      have := abs_le.mp (hbox s hs x)
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hu' := (isGradientFlow_iff K lam nu gd _).1 hflow'
    have hu := (isGradientFlow_iff K lam nu gd _).1 hflow
    have hLn : LipschitzOnWith L (fun v : V → ℝ => fun x => -lossGrad K lam nu gd v x)
        (densityBox V lo hi) := by
      refine LipschitzOnWith.of_dist_le_mul fun v hv v' hv' => ?_
      show dist (-lossGrad K lam nu gd v) (-lossGrad K lam nu gd v') ≤ _
      rw [dist_neg_neg]
      exact hL.dist_le_mul v hv v' hv'
    have heq := ODE_solution_unique_of_mem_Icc_right
      (v := fun _ v => fun x => -lossGrad K lam nu gd v x)
      (s := fun _ => densityBox V lo hi) (K := L) (a := 0) (b := T)
      (fun _ _ => hLn)
      (fun s hs => (hu' s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hu' s hs.1).hasDerivWithinAt)
      (fun s hs => hin' s hs.1)
      (fun s hs => (hu s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hu s hs.1).hasDerivWithinAt)
      (fun s hs => hin s hs.1)
      (by funext x; simp only [hh'0, hh0])
    have := congrFun (heq ⟨hT, le_rfl⟩) 
    funext x
    have hx := this x
    simp only at hx
    linarith
  -- convergence
  have hnormh : Graph.nrmL2 lam (h 0) ≤ eps0W g a wmin wsup Bhat lamMin := by rw [hh0]; exact hnorm0
  obtain ⟨cinf, hc1, hc2⟩ := local_convergence_full_C3On hK hinv hlam htot hlmin0 hlmin ha hC3 hgd
    hg1 hg2 hwsup hwmin0 hwmin hB1 hcoer hflow hnormh
  refine ⟨h, hh0, hflow, fun t ht x => ⟨?_, ?_⟩, huniq, cinf,
    balanced_const (invariant_of_isInvariant hinv) cinf, ?_, fun t ht => ?_⟩
  · have := abs_le.mp (hbox t ht x); linarith [this.1]
  · have hr := abs_ratio_le_of_mem_box hK.nonneg hinv hlam he0.le heA (hbox_of t (hbox t ht)) x
    rwa [← hαh t] at hr
  · rw [← hh0]; exact hc1
  · rw [← hh0]; exact hc2 t ht

end ExistenceNear

/-! ### Item 1 of the training-speed theorem, both conjuncts, with `𝓛(μ₀)⁻¹ := +∞` at balance -/

section GlobalPhase

variable {V : Type*} [Fintype V]

/-- **`theo:training_speed_full`, item 1, as printed** (`proofs.tex:1005–1011`): along the
`(log x)²` gradient flow, at every `t ≥ 0`,

* `t ↦ 𝓛(μ_t)` is differentiable with `−(d/dt)𝓛(μ_t) = ‖∇𝓛(μ_t)‖²`, and `κ²𝓛(μ_t)² ≤ ‖∇𝓛(μ_t)‖²`
  — the Łojasiewicz inequality `−𝓛̇ ≥ κ²𝓛²`;
* `𝓛(μ_t) ≤ (𝓛(μ₀)⁻¹ + κ²t)⁻¹` read in `[0,∞]`, where `0⁻¹ = ∞` and `∞⁻¹ = 0` — the paper's
  convention `𝓛(μ₀)⁻¹ := +∞` exactly, and `(𝓛(μ₀))⁻¹ = ∞` holds iff `μ₀` is balanced;
* and, unfolded in `ℝ`: at a balanced start `𝓛(μ_t) = 0` for every `t ≥ 0`, otherwise the real
  display.

`κ = w_min λ_min^{1/2}/(‖u₀‖ ‖w‖_{L^∞} M)`, `M = max(1, √(𝓛(μ₀)/(w_min λ_min)))`, with
`λ_min`, `‖w‖_{L^∞}` read as the bounds `lamMin ≤ λ`, `w ≤ wsup`. -/
theorem global_phase_exact {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin wmin wsup : ℝ}
    {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    (∀ t : ℝ, 0 ≤ t →
        HasDerivAt (fun s => lossVal lam wf logSq (ratio K lam (u s)))
          (-(Graph.nrmL2 lam (lossGrad K lam (fun x => lam x * wf x) logSqDeriv (u t)) ^ 2)) t
        ∧ (wmin * Real.sqrt lamMin
            / (Graph.nrmL2 lam (u 0) * wsup
                * max 1 (Real.sqrt (lossVal lam wf logSq (ratio K lam (u 0))
                    / (wmin * lamMin))))) ^ 2
            * lossVal lam wf logSq (ratio K lam (u t)) ^ 2
          ≤ Graph.nrmL2 lam (lossGrad K lam (fun x => lam x * wf x) logSqDeriv (u t)) ^ 2)
      ∧ (∀ t : ℝ, 0 ≤ t →
          ENNReal.ofReal (lossVal lam wf logSq (ratio K lam (u t)))
            ≤ ((ENNReal.ofReal (lossVal lam wf logSq (ratio K lam (u 0))))⁻¹
                + ENNReal.ofReal ((wmin * Real.sqrt lamMin
                    / (Graph.nrmL2 lam (u 0) * wsup
                        * max 1 (Real.sqrt (lossVal lam wf logSq (ratio K lam (u 0))
                            / (wmin * lamMin))))) ^ 2 * t))⁻¹)
      ∧ (Balanced K lam (u 0)
          ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio K lam (u 0))))⁻¹ = ⊤)
      ∧ (lossVal lam wf logSq (ratio K lam (u 0)) = 0 →
          ∀ t : ℝ, 0 ≤ t → lossVal lam wf logSq (ratio K lam (u t)) = 0)
      ∧ (0 < lossVal lam wf logSq (ratio K lam (u 0)) →
          ∀ t : ℝ, 0 ≤ t →
            lossVal lam wf logSq (ratio K lam (u t))
              ≤ ((lossVal lam wf logSq (ratio K lam (u 0)))⁻¹
                  + (wmin * Real.sqrt lamMin
                      / (Graph.nrmL2 lam (u 0) * wsup
                          * max 1 (Real.sqrt (lossVal lam wf logSq (ratio K lam (u 0))
                              / (wmin * lamMin))))) ^ 2 * t)⁻¹) := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  set L : ℝ → ℝ := fun s => lossVal lam wf logSq (ratio K lam (u s)) with hLdef
  set κ : ℝ := wmin * Real.sqrt lamMin
      / (Graph.nrmL2 lam (u 0) * wsup
          * max 1 (Real.sqrt (L 0 / (wmin * lamMin)))) with hκdef
  have hL0nn : ∀ s, 0 ≤ L s := fun s => lossVal_nonneg hnn fun x => (hwpos x).le
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hm0 : 0 < Graph.meanL2 lam (u 0) :=
    Finset.sum_pos (fun i _ => mul_pos (hlam i) (hu 0 le_rfl i)) ⟨x0, Finset.mem_univ _⟩
  have hU0 : 0 < Graph.nrmL2 lam (u 0) :=
    lt_of_lt_of_le hm0 (mean_le_nrmL2_iff_const hlam htot (fun x => (hu 0 le_rfl x).le)).1
  have hanti := lossVal_antitone_flow hinv hK hlam hu hflow
  have hreal := global_lojasiewicz_flow' hinv hK hlam htot hu hlmin hlmin0 hwmin hw hwsup hU0
    hflow
  have hκt : ∀ t, 0 ≤ t → 0 ≤ κ ^ 2 * t := fun t ht => mul_nonneg (sq_nonneg _) ht
  refine ⟨fun t ht => ⟨?_, ?_⟩, fun t ht => ?_, ?_, fun h0 t ht => ?_, fun h0 t ht => hreal t ht⟩
  · have h := hasDerivAt_loss_flow (K := K) (lam := lam) (nu := fun x => lam x * wf x)
      (g := logSq) (gd := logSqDeriv) hinv hK hlam hu (fun _ hy => hasDerivAt_logSq hy) hflow t ht
    simpa only [loss_eq_lossVal] using h
  · rw [lossGrad_of_weight hlam]
    exact global_lojasiewicz_sq hinv hK hlam htot (hu t ht) hlmin hlmin0 hwmin hw hwsup
      (nrmL2_const_of_flow hlam hu hflow t ht) hU0
      (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht)
  · rcases (hL0nn 0).lt_or_eq with hpos | hzero
    · have hb := hreal t ht
      have hX : 0 < (L 0)⁻¹ + κ ^ 2 * t := by
        have := inv_pos.mpr hpos; linarith [hκt t ht]
      rw [← ENNReal.ofReal_inv_of_pos hpos,
        ← ENNReal.ofReal_add (inv_pos.mpr hpos).le (hκt t ht), ← ENNReal.ofReal_inv_of_pos hX]
      exact ENNReal.ofReal_le_ofReal hb
    · have hLt : L t ≤ 0 := by
        rw [hzero]
        exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
      rw [ENNReal.ofReal_of_nonpos hLt]
      exact zero_le
  · rw [ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero,
      ← lossVal_eq_zero_iff_balanced hinv hK hlam (hu 0 le_rfl) hwpos]
    exact ⟨fun h => h.le, fun h => le_antisymm h (hL0nn 0)⟩
  · refine le_antisymm ?_ (hL0nn t)
    have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simp only at this h0 ⊢
    linarith

end GlobalPhase

/-! ### `theo:training_speed_full`, items 1 and 2, from `u₀` alone -/

section Assembled

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`theo:training_speed_full`, the preamble and items 1 and 2, as printed** (`proofs.tex:999–1021`),
from the paper's hypotheses only — a finite path-connected marked graph, a backward policy positive
on the edges of its loop closure, `λ` its invariant probability, `g = (log x)²`, `ν = wλ` with
`w ≥ w_min > 0`, and an initialization `μ₀ = u₀λ ∼ λ`. No flow is hypothesised.

* the visit ratio `λ(x) = N(x)/(2+σ̄)`, `λ_min = N_min/(2+σ̄)`, and
  `ϱ_σ = g''(1)w_min λ_min/σ_*² = 2w_min N_min/(σ_*²(2+σ̄))`;
* the gradient flow from `u₀` **exists**, stays positive, is **unique** among positive solutions,
  and converges to the balanced flow of its sphere (the constant `‖u₀‖`);
* item 1: `−𝓛̇ = ‖∇𝓛‖² ≥ κ²𝓛²` at every `t ≥ 0`, and `𝓛(μ_t) ≤ (𝓛(μ₀)⁻¹ + κ²t)⁻¹` in `[0,∞]`,
  `𝓛(μ₀)⁻¹ = ∞` exactly when `μ₀` is balanced;
* item 2: with `ε₀` Theorem 10's radius for `(log x)²` at `a = 1/2`, `B̂_σ`, `C_∞ = λ_min^{−1/2}`
  (`eps0W logSq (1/2)`), there is `t₁ ≤ T₀ = 4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)` at which
  `m₁ ∈ [m₀, ‖u₀‖]` and the flow rescaled to unit mass is within `ε₀` of `1`, and from `t₁` on it
  converges to a balanced `c_∞λ` at rate `ϱ_σ/(2m₁²)`.

`‖w‖_{L^∞}` is `Graph.maxOver G wf` itself, not a bound. -/
theorem training_speed_full_paper {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam gr uH wf : V → ℝ} {wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    (∀ x, lam x = Graph.visits G gr x / (2 + B.sigmaBar uH))
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
                          (perpL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have htot : ∑ x, lam x = 1 := hl.total
  have hinv : Invariant B.phat lam := hl.inv
  have hKnn : ∀ x y, 0 ≤ B.phat x y := fun x y => B.phat_nonneg x y
  have hlmin : ∀ x, Graph.minOver G lam ≤ lam x := fun x => Graph.minOver_le lam x
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hwsup : ∀ x, wf x ≤ Graph.maxOver G wf := fun x => Graph.le_maxOver wf x
  have hwsupp : 0 < Graph.maxOver G wf := lt_of_lt_of_le (lt_of_lt_of_le hwmin (hw G.src))
    (hwsup G.src)
  obtain ⟨u, hu0', hflow, hupos, huniq, hconv, hbal, -⟩ :=
    no_distant_equilibrium_three_of_init hpc hpos hl hwmin hw hu0
  have hu0'' : ∀ x, 0 < u 0 x := fun x => by rw [hu0']; exact hu0 x
  obtain ⟨hI1, hI2, hI3, -, -⟩ :=
    global_phase_exact hinv hKnn hp htot hupos hlmin hlmin0 hwmin hw hwsup hflow
  obtain ⟨hvis, hmin, -, t₁, ht₁mem, hmono, hm1U, hrad, cinf, hcbal, hdecay⟩ :=
    training_speed_full_Gamma3 hpc hpos hl hg hhit hwmin hw hwsup hu0'' hflow
  rw [hu0'] at hI1 hI2 hI3 ht₁mem hmono hm1U
  have hm0 : 0 < Graph.meanL2 lam u0 :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (hu0 i)) ⟨G.src, Finset.mem_univ _⟩
  have hU0 : 0 < Graph.nrmL2 lam u0 :=
    lt_of_lt_of_le hm0 (mean_le_nrmL2_iff_const hp htot (fun x => (hu0 x).le)).1
  have hsig : 0 < Graph.sigmaStar G uH := lt_of_lt_of_le one_pos (one_le_sigmaStar hhit)
  have hB : 0 < BhatSigma G uH lam := BhatSigma_pos hpc hpos hl hhit
  have heps0 : 0 < eps0Gamma3 wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
      (Graph.minOver G lam) := eps0Gamma3_pos hlmin0 hwmin hwsupp hB
  have hT0 : T0 (lossVal lam wf logSq (ratio B.phat lam u0))
      (cDelta wmin (Graph.minOver G lam) (Graph.nrmL2 lam u0)
        (delta0 (eps0Gamma3 wmin (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam))
          (Graph.meanL2 lam u0) (BhatSigma G uH lam) (Graph.nrmL2 lam u0)))
      = 4 * lossVal lam wf logSq (ratio B.phat lam u0) * Graph.nrmL2 lam u0 ^ 6
          * Graph.sigmaStar G uH ^ 4
        / (wmin ^ 2
            * eps0Gamma3 wmin (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam) ^ 4
            * Graph.meanL2 lam u0 ^ 4 * Graph.minOver G lam ^ 5) := by
    rw [BhatSigma_eq]
    exact T0_eq hlmin0 hwmin hU0 (by rw [← BhatSigma_eq]; exact heps0) hm0 hsig
  rw [hT0] at ht₁mem
  simp only [eps0W_logSq, logSq_deriv2_one]
  refine ⟨hvis, hmin, rhoSigma_eq_visits hpc hpos hl hg hhit, u, hu0', hflow, hupos, huniq,
    hconv, hbal, hI1, hI2, hI3, t₁, ht₁mem, hmono, hm1U, hrad, cinf, hcbal, hdecay⟩

end Assembled

/-! ### The DB instance: `T = K₂` on the edge set `E`, under `C³` on the closed window -/

section EdgeInstanceC3On

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`theo:local_convergence_full` for the DB loss, flow clause with existence, under `C³` on the
closed window**: `local_convergence_full_exists` on `(E, K₂, λ₂)`, the kernel, invariance,
positivity and total mass of `λ₂` proved from the backward policy (`C3Wrappers`). -/
theorem local_convergence_full_DB_exists {pb : V → V → ℝ} {lam : V → ℝ} {w : EdgeSet pb → ℝ}
    {g gd : ℝ → ℝ} {a wsup wmin Bhat lamMin : ℝ}
    (hpb : Core.IsMarkovOn lam pb) (hinvpb : Core.IsInvariant lam pb) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin)
    (hlmin : ∀ e, lamMin ≤ edgeMeasureE pb lam e)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ e, |w e| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ e, wmin ≤ w e)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : EdgeSet pb → ℝ,
      Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) f)
        ≤ Bhat * Graph.nrmL2 (edgeMeasureE pb lam) (Aop (edgeKernelE pb) (edgeMeasureE pb lam) f))
    {h0 : EdgeSet pb → ℝ}
    (hnorm0 : Graph.nrmL2 (edgeMeasureE pb lam) h0 ≤ eps0W g a wmin wsup Bhat lamMin) :
    ∃ h : ℝ → EdgeSet pb → ℝ, h 0 = h0
      ∧ IsGradientFlow (edgeKernelE pb) (edgeMeasureE pb lam)
          (fun e => edgeMeasureE pb lam e * w e) gd (fun s e => 1 + h s e)
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ e, 0 < 1 + h t e
          ∧ |ratio (edgeKernelE pb) (edgeMeasureE pb lam) (fun z => 1 + h t z) e - 1| ≤ 2 * a / 3)
      ∧ (∀ h' : ℝ → EdgeSet pb → ℝ, h' 0 = h0 →
          IsGradientFlow (edgeKernelE pb) (edgeMeasureE pb lam)
            (fun e => edgeMeasureE pb lam e * w e) gd (fun s e => 1 + h' s e) →
          ∀ t : ℝ, 0 ≤ t → h' t = h t)
      ∧ ∃ cinf : ℝ, Balanced (edgeKernelE pb) (edgeMeasureE pb lam) (fun _ => cinf)
          ∧ |cinf - 1 - Graph.meanL2 (edgeMeasureE pb lam) h0|
              ≤ CW g a wmin wsup * Graph.nrmL2 (edgeMeasureE pb lam)
                  (perpL2 (edgeMeasureE pb lam) h0) ^ 2
            ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 (edgeMeasureE pb lam) (fun e => h t e - (cinf - 1))
                ≤ 2 * Real.exp (-(rhoL (deriv (deriv g) 1) wmin Bhat * t / 2))
                    * Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) h0) := by
  have hrow : ∀ x, ∑ y, pb x y = 1 := fun x => hpb.row_sum (hlam x).ne'
  exact local_convergence_full_exists (edgeKernelE_isMarkovOn hpb.nonneg hrow)
    (edgeMeasureE_isInvariant hpb.nonneg hinvpb.nonneg (invariant_of_isInvariant hinvpb))
    (edgeMeasureE_pos hlam) (edgeMeasureE_total hpb.nonneg hrow htot) hlmin0 hlmin ha hC3 hgd hg1
    hg2 hwsup hwmin0 hwmin hB1 hcoer hnorm0

/-- **`theo:local_convergence_full` for the DB loss, gradient-descent clause, under `C³` on the
closed window.** -/
theorem local_convergence_gd_DB_C3On {pb : V → V → ℝ} {lam : V → ℝ} {w : EdgeSet pb → ℝ}
    {g gd : ℝ → ℝ} {hk : ℕ → EdgeSet pb → ℝ} {a wsup wmin Bhat lamMin gam : ℝ}
    (hpb : Core.IsMarkovOn lam pb) (hinvpb : Core.IsInvariant lam pb) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin)
    (hlmin : ∀ e, lamMin ≤ edgeMeasureE pb lam e)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ e, |w e| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ e, wmin ≤ w e)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : EdgeSet pb → ℝ,
      Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) f)
        ≤ Bhat * Graph.nrmL2 (edgeMeasureE pb lam) (Aop (edgeKernelE pb) (edgeMeasureE pb lam) f))
    (hstep : ∀ k : ℕ, hk (k + 1) = fun e =>
      hk k e - gam * lossGrad (edgeKernelE pb) (edgeMeasureE pb lam)
        (fun z => edgeMeasureE pb lam z * w z) gd (fun z => 1 + hk k z) e)
    (hgam0 : 0 ≤ gam) (hgam : gam ≤ gamma0W g a wmin wsup Bhat)
    (hnorm0 : Graph.nrmL2 (edgeMeasureE pb lam) (hk 0) ≤ eps0W g a wmin wsup Bhat lamMin) :
    ∀ k : ℕ, ((∀ e, 0 < 1 + hk k e)
      ∧ (∀ e, |ratio (edgeKernelE pb) (edgeMeasureE pb lam) (fun z => 1 + hk k z) e - 1|
          ≤ 2 * a / 3)
      ∧ ∀ d : EdgeSet pb → ℝ,
          HasDerivAt
            (fun t : ℝ => loss (edgeKernelE pb) (edgeMeasureE pb lam)
              (fun z => edgeMeasureE pb lam z * w z) (fun e => 1 + hk k e + t * d e) g)
            (Graph.ipL2 (edgeMeasureE pb lam) (lossGrad (edgeKernelE pb) (edgeMeasureE pb lam)
              (fun z => edgeMeasureE pb lam z * w z) gd fun z => 1 + hk k z) d) 0)
      ∧ Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) (hk (k + 1)))
          ≤ (1 - gam * rhoL (deriv (deriv g) 1) wmin Bhat / 4)
              * Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) (hk k)) := by
  have hrow : ∀ x, ∑ y, pb x y = 1 := fun x => hpb.row_sum (hlam x).ne'
  exact local_convergence_gd_C3On (edgeKernelE_isMarkovOn hpb.nonneg hrow)
    (edgeMeasureE_isInvariant hpb.nonneg hinvpb.nonneg (invariant_of_isInvariant hinvpb))
    (edgeMeasureE_pos hlam) (edgeMeasureE_total hpb.nonneg hrow htot) hlmin0 hlmin ha hC3 hgd hg1
    hg2 hwsup hwmin0 hwmin hB1 hcoer hstep hgam0 hgam hnorm0

end EdgeInstanceC3On

/-! ### Inhabitation (kb 0025) -/

section Checks

/-- **The `C³`-on-the-window bundle is inhabited by `g = (log x)²`** at `a = 1/2`, `gd = 2 log x/x`. -/
theorem logSq_C3On_bundle :
    ContDiffOn ℝ 3 logSq (winC3 (1/2))
      ∧ (∀ y ∈ winC3 (1/2), HasDerivWithinAt logSq (logSqDeriv y) (winC3 (1/2)) y)
      ∧ deriv logSq 1 = 0 ∧ 0 < deriv (deriv logSq) 1 := by
  refine ⟨(C3On_of_C3 (by norm_num) logSq_C3).1, fun y hy => ?_, logSq_deriv_one,
    by rw [logSq_deriv2_one]; norm_num⟩
  have hy0 : 0 < y := by have := hy.1; norm_num at this; linarith
  exact (hasDerivAt_logSq hy0).hasDerivWithinAt

/-- A generator that is `C³` on `[1/2, 3/2]` only from inside: `(y−1)²` plus a kink at `3/2`. -/
noncomputable def kinkGen (y : ℝ) : ℝ := (y - 1) ^ 2 + max 0 (y - 3/2)

/-- **The widening is real**: `kinkGen` meets the `C³`-on-the-window bundle at `a = 1/2` with
`gd = 2(y−1)`, and is not differentiable at the endpoint `3/2`, so the two-sided reading of
`C3Wrappers` does not cover it. -/
theorem kinkGen_C3On_not_C3 :
    ContDiffOn ℝ 3 kinkGen (winC3 (1/2))
      ∧ (∀ y ∈ winC3 (1/2), HasDerivWithinAt kinkGen (2 * (y - 1)) (winC3 (1/2)) y)
      ∧ deriv kinkGen 1 = 0 ∧ 0 < deriv (deriv kinkGen) 1
      ∧ ¬ DifferentiableAt ℝ kinkGen (3/2) := by
  have heq : Set.EqOn kinkGen (fun y => (y - 1) ^ 2) (winC3 (1/2)) := by
    intro y hy
    have : y - 3/2 ≤ 0 := by have := hy.2; norm_num at this; linarith
    simp only [kinkGen, max_eq_left this, add_zero]
  have hpoly : ContDiff ℝ 3 (fun y : ℝ => (y - 1) ^ 2) := (contDiff_id.sub contDiff_const).pow 2
  have hdpoly : ∀ y : ℝ, HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (y - 1)) y := fun y => by
    simpa using ((hasDerivAt_id' y).sub_const 1).fun_pow 2
  have hnear : kinkGen =ᶠ[𝓝 1] fun y => (y - 1) ^ 2 := by
    filter_upwards [Iio_mem_nhds (by norm_num : (1:ℝ) < 3/2)] with y hy
    have : y - 3/2 ≤ 0 := by have := Set.mem_Iio.mp hy; linarith
    simp only [kinkGen, max_eq_left this, add_zero]
  have hd1 : deriv kinkGen =ᶠ[𝓝 1] fun y => 2 * (y - 1) := by
    filter_upwards [Iio_mem_nhds (by norm_num : (1:ℝ) < 3/2)] with y hy
    have hev : kinkGen =ᶠ[𝓝 y] fun y => (y - 1) ^ 2 := by
      filter_upwards [Iio_mem_nhds (Set.mem_Iio.mp hy)] with z hz
      have : z - 3/2 ≤ 0 := by have := Set.mem_Iio.mp hz; linarith
      simp only [kinkGen, max_eq_left this, add_zero]
    rw [hev.deriv_eq]
    exact (hdpoly y).deriv
  refine ⟨hpoly.contDiffOn.congr heq, fun y hy => ((hdpoly y).hasDerivWithinAt).congr
    (fun z hz => heq hz) (heq hy), ?_, ?_, ?_⟩
  · rw [hnear.deriv_eq, (hdpoly 1).deriv]; norm_num
  · have hlin : HasDerivAt (fun y : ℝ => 2 * (y - 1)) 2 1 := by
      simpa using ((hasDerivAt_id' (1:ℝ)).sub_const 1).const_mul 2
    rw [hd1.deriv_eq, hlin.deriv]; norm_num
  · intro hdiff
    have hpd : DifferentiableAt ℝ (fun y : ℝ => (y - 1) ^ 2) (3/2) := (hdpoly _).differentiableAt
    have hmax : DifferentiableAt ℝ (fun y : ℝ => max 0 (y - 3/2)) (3/2) := by
      have hfun : (fun y : ℝ => max 0 (y - 3/2)) = kinkGen - fun y => (y - 1) ^ 2 := by
        funext y; simp only [kinkGen, Pi.sub_apply]; ring
      rw [hfun]
      exact hdiff.sub hpd
    have habs : DifferentiableAt ℝ (fun z : ℝ => |z|) 0 := by
      have h2 : DifferentiableAt ℝ (fun z : ℝ => 2 * max 0 (z + 3/2 - 3/2) - (z + 3/2 - 3/2)) 0 := by
        have hc : DifferentiableAt ℝ (fun z : ℝ => z + 3/2) 0 :=
          differentiableAt_id.add (differentiableAt_const _)
        have hmax' : DifferentiableAt ℝ (fun y : ℝ => max 0 (y - 3/2)) ((fun z : ℝ => z + 3/2) 0) := by
          show DifferentiableAt ℝ _ (0 + 3/2)
          rw [zero_add]
          exact hmax
        have hm : DifferentiableAt ℝ (fun z : ℝ => max 0 (z + 3/2 - 3/2)) 0 :=
          DifferentiableAt.comp (g := fun y : ℝ => max 0 (y - 3/2)) (f := fun z : ℝ => z + 3/2)
            (0:ℝ) hmax' hc
        exact (hm.const_mul 2).sub (hc.sub (differentiableAt_const _))
      have hfun : (fun z : ℝ => 2 * max 0 (z + 3/2 - 3/2) - (z + 3/2 - 3/2)) = fun z => |z| := by
        funext z
        rw [show z + 3/2 - 3/2 = z by ring]
        rcases le_total 0 z with hz | hz
        · rw [max_eq_right hz, abs_of_nonneg hz]; ring
        · rw [max_eq_left hz, abs_of_nonpos hz]; ring
      rwa [hfun] at h2
    exact not_differentiableAt_abs_zero habs

/-- **The existence clause is inhabited off balance**: on the two-state chain, `g = (log x)²`,
`a = 1/2`, `w ≡ 1`, `λ_min = 1/2`, `B̂ = 1`, from `h₀ = (ε₀/2, −ε₀/2)` — a non-balanced start
inside the basin — `local_convergence_full_exists` produces a solution of the flow predicate. -/
theorem twoState_exists_check :
    ∃ h : ℝ → Fin 2 → ℝ,
      IsGradientFlow twoStateK twoStateLam (fun z => twoStateLam z * 1) logSqDeriv
          (fun s x => 1 + h s x)
        ∧ ¬ Balanced twoStateK twoStateLam (fun x => 1 + h 0 x) := by
  set ε := eps0W logSq (1/2) 1 1 1 (1/2) with hεdef
  have hlamU : ∀ x : Fin 2, (1:ℝ)/2 ≤ twoStateLam x := fun x => by norm_num [twoStateLam]
  have htotU : ∑ x, twoStateLam x = 1 := by norm_num [twoStateLam, Fin.sum_univ_two]
  obtain ⟨hC3, hgd, hg1, hg2⟩ := logSq_C3On_bundle
  have hεpos : 0 < ε :=
    (constW_bounds (lam := twoStateLam) (w := fun _ : Fin 2 => (1:ℝ)) htotU (by norm_num)
      (by norm_num) hC3 hg2 (fun _ => by norm_num) one_pos (fun _ => le_rfl) le_rfl).1.1
  set h0 : Fin 2 → ℝ := ![ε / 2, -(ε / 2)] with hh0def
  have hnorm : Graph.nrmL2 twoStateLam h0 ≤ ε := by
    have hval : Graph.nrmL2 twoStateLam h0 = Real.sqrt ((ε / 2) ^ 2) := by
      simp only [Graph.nrmL2, Graph.ipL2, Fin.sum_univ_two, twoStateLam, hh0def]
      congr 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [hval, Real.sqrt_sq (by positivity)]
    linarith
  obtain ⟨h, hh0, hflow, -, -, -⟩ := local_convergence_full_exists (K := twoStateK)
    (lam := twoStateLam) (w := fun _ => 1) (g := logSq) (gd := logSqDeriv) (a := 1/2) (wsup := 1)
    (wmin := 1) (Bhat := 1) (lamMin := 1/2)
    twoState_isMarkovOn twoState_isInvariant twoStateLam_pos htotU (by norm_num) hlamU
    (by norm_num) hC3 hgd hg1 hg2 (fun _ => by norm_num) one_pos (fun _ => le_rfl) le_rfl
    twoState_coercivity hnorm
  refine ⟨h, hflow, fun hbal => ?_⟩
  have h1 := hbal 0
  simp only [pushMass, Fin.sum_univ_two, twoStateK, twoStateLam, hh0, hh0def,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  nlinarith

open Graph.CycleExample in
/-- **`training_speed_full_paper` applies, with no flow hypothesised**, on the five-vertex cycle of
`rem:cycle_no_stalemate` at `p = 1/2`, `w ≡ 1`, from the over-inflated `uInfl 2`: a flow exists,
starts off balance, and enters the paper's neighbourhood at some `t₁ ≥ 0`. -/
theorem cycle_training_speed_paper_check :
    ∃ u : ℝ → Fin 5 → ℝ, u 0 = uInfl 2
      ∧ IsGradientFlow (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2))
          (fun x => lam (1 / 2) x * 1) logSqDeriv u
      ∧ ¬ Balanced (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2)) (u 0)
      ∧ ∃ t₁ : ℝ, 0 ≤ t₁
          ∧ Graph.nrmL2 (lam (1 / 2)) (fun x => u t₁ x / Graph.meanL2 (lam (1 / 2)) (u t₁) - 1)
              ≤ eps0W logSq (1/2) 1 (Graph.maxOver cyc fun _ => (1:ℝ))
                  (BhatSigma cyc (hitExp (1 / 2)) (lam (1 / 2)))
                  (Graph.minOver cyc (lam (1 / 2))) := by
  obtain ⟨-, -, -, u, hu0, hflow, -, -, -, -, -, -, -, t₁, ht₁, -, -, hrad, -⟩ :=
    training_speed_full_paper (G := cyc) (B := pol (p := 1 / 2) (by norm_num) (by norm_num))
      (wf := fun _ => (1 : ℝ)) (wmin := 1) pathConnected (positiveOnEdges _ _) (isInvProb _ _)
      (isGreen _ _) (isHitExp _ _) one_pos (fun _ => le_rfl) (uInfl_pos (M := 2) (by norm_num))
  refine ⟨u, hu0, hflow, ?_, t₁, ht₁.1, hrad⟩
  rw [hu0, ← ratio_eq_one_iff_balanced
    (fun y => mul_pos (lam_pos (p := 1 / 2) (by norm_num) y) (uInfl_pos (M := 2) (by norm_num) y))]
  intro h
  have h0 := h 0
  rw [ratio_src (by norm_num) (by norm_num) (by norm_num)] at h0
  norm_num at h0

end Checks

end GFNBounds.Balance
