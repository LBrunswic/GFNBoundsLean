import GFNBounds.Balance.LocalConvergenceClauses
import GFNBounds.Balance.TrainingSpeed
import GFNBounds.Balance.Lift

/-!
# Theorem 10 under its own `C³` hypothesis, for the DB loss on the edge set, and item 2 of the training-speed theorem at `Γ₃`

**`theo:local_convergence_full`** — statement `proofs.tex:666–672`, proof `proofs.tex:674–727`;
the `C³` hypothesis, the constants through `Γ₃`, and the DB instance.
**`theo:training_speed_full`** — statement `proofs.tex:999–1035`, item 2 at `proofs.tex:1013–1020`,
proof `proofs.tex:1037–1093`; **items 1 and 2 only**, at the paper's radius.
(The bold-backtick form of each label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (`theo:local_convergence_full`) In the setting of Theorem `theo:db_stable_frozen_full`, assume
> moreover that `g(1)=g'(1)=0`, that `g` is `C³` on `[1−a,1+a]` for some `a∈(0,1)`, and that the
> state space `𝒮` is finite, with `λ` a probability and `λ(x)>0` for every `x∈𝒮`; set
> `λ_min:=min_{x∈𝒮}λ(x)` and `C_∞:=λ_min^{−1/2}`, so that `C_∞≥1`. For the DB loss, `T=K₂`
> (Definition `def:edge_lift`) is taken on the set `E` of pairs `(s,s')∈𝒮²` with
> `π_←(s'→s)>0`, which is finite when `𝒮` is, which `K₂` maps into itself, and on which
> `λ₂(s,s')=π_←(s'→s)λ(s')>0` when `λ>0`; `E` plays the role of `𝒮` and the probability `λ₂`
> that of `λ` — in particular `λ_min:=min_{e∈E}λ₂(e)` and `C_∞:=λ_min^{−1/2}`. Then there are
> explicit `ε₀∈(0,a/(16C_∞)]` and `C≥1`, depending only on `g''(1)`, `sup_{[1−a,1+a]}|g'''|`,
> `a`, `w_min`, `‖w‖_{L^∞}`, `B̂` and `C_∞`, such that for every initialization `μ₀=(1+h₀)λ`
> with `‖h₀‖_{L²(λ)}≤ε₀`, the *nonlinear* gradient flow `μ̇_t=−∇^λ𝓛_{g,ν}(μ_t)` converges to a
> balanced flow `c_∞λ` with `|c_∞−1−Πh₀|≤C‖h₀−Πh₀‖²` and
> `‖h_t−(c_∞−1)‖_{L²(λ)} ≤ 2e^{−ϱt/2}‖h₀−Πh₀‖_{L²(λ)}`. There is moreover an explicit `γ₀>0`,
> depending only on the same quantities, such that for every such `h₀` and every step
> `0<γ≤γ₀` the gradient descent `h_{k+1}:=h_k−γD_k`, `D_k` the density against `λ` of
> `∇^λ𝓛_{g,ν}((1+h_k)λ)`, is well defined and satisfies
> `‖h_{k+1}−Πh_{k+1}‖_{L²(λ)}≤(1−γϱ/4)‖h_k−Πh_k‖_{L²(λ)}` for every `k≥0`.

> (proof, opening) set `Γ₃:=sup_{[1−a,1+a]}|g'''|`, `C_g:=g''(1)+aΓ₃/2` […] For the DB loss the
> same holds on `E` with `λ₂`, which is a probability, its second marginal being `λ`.

> (`theo:training_speed_full`, item 2) *local phase* — let `ε₀` be the radius of Theorem
> `theo:local_convergence_full` for `g=(log x)²` at `a=1/2`, with `B̂_σ` in place of `B̂` and
> `C_∞=λ_min^{−1/2}`; at some time `t₁ ≤ T₀ := 4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)`, the flow
> rescaled to unit mass enters the neighbourhood of Theorem `theo:local_convergence_full`, and
> from `t₁` on the flow converges exponentially at rate `ϱ_σ/(2m₁²)` — `m₁∈[m₀,‖u₀‖]` the
> flow's mass at `t₁` […] — where `ϱ_σ = g''(1)w_min λ_min/σ_*² = 2w_min N_min/(σ_*²(2+σ̄))`.

## Why this file exists

Three gaps the `paper-map.json` rows record (2026-09-14), each closed here without touching the
strict library.

1. **`C³`, not a Taylor bound.** `LocalConvergence.local_convergence_full` and its siblings take
   `htaylor : |gd y − g2(y−1)| ≤ (M₃/2)(y−1)²` for an opaque `gd` and a free `M₃`. The paper takes
   `g` `C³` with `Γ₃ := sup|g'''|`. `taylor_of_C3` derives `htaylor` from `C³` at `gd = g'`,
   `g2 = g''(1)`, `M₃ = Γ₃`, and the `_C3` theorems restate the theorem with the flow driven by
   `deriv g` and every constant a formula in `g''(1)` and `Γ₃`.
2. **The DB instance was never built.** `EdgeSet`, `edgeKernelE`, `edgeMeasureE` restrict
   `Lift.edgeKernel`, `Lift.edgeMeasure` to `E`; the three claims the statement makes about `E`
   and the probability claim of the proof are proved, and `local_convergence_full_DB`,
   `local_convergence_gd_DB` are the theorem on `(E, K₂, λ₂)`. `loss_edgeE_eq_db` identifies the
   balance loss of `K₂` on `E` with the DB loss, through `Lift.db_lift_ratio`.
3. **Item 2 was assembled at the wrong radius.** `TrainingSpeed.training_speed_full_of_init`
   takes `ε₀ = eps0Sq`, Theorem 10's radius at `M₃ = 24` — a constant for which the Taylor bound of
   `(log x)²` holds, but **not** `Γ₃`. The paper's `ε₀` is the radius at
   `Γ₃ = sup_{[1/2,3/2]}|g'''| = 48 + 32 log 2 ≈ 70.18` (`Gamma3_logSq`). The two statements are
   **incomparable**: at the larger radius `eps0Sq` the entry-time bound `T₀` is smaller (a
   stronger time claim) and the neighbourhood entered is larger (a weaker entry claim).
   `training_speed_full_Gamma3` states items 1 and 2 at the paper's radius.

## What is proved

| | |
|---|---|
| `Gamma3`, `bddAbove_abs_g3`, `abs_g3_le_Gamma3`, `Gamma3_nonneg` | `Γ₃ := sSup (|g'''| '' [1−a,1+a])`; the set is bounded (continuity on a compact) and `Γ₃` bounds `|g'''|` there |
| `abs_le_quadratic_of_deriv`, `hasDerivAt_deriv_of_C3`, `abs_g2_sub_le` | the two mean-value steps: `|g''(t)−g''(1)| ≤ Γ₃|t−1|`, then a quadratic fence |
| **`taylor_of_C3`** | **`htaylor` from `C³`**: `|g'(y)−g''(1)(y−1)| ≤ (Γ₃/2)(y−1)²` on `|y−1| ≤ a` |
| `eps0C3`, `CC3`, `gamma0C3`, `constC3_congr` | `ε₀`, `C := max(1,C₇)`, `γ₀` as printed formulas in `g''(1)`, `Γ₃`, `a`, `w_min`, `‖w‖_{L^∞}`, `B̂`, `C_∞`; "depending only on" as a congruence (kb 0028) |
| `epsW_eq_of_lt_one` | the library's window `min(min(a,1)/4, ε₁)` is the paper's `min(a/4, ε₁)` for `a < 1` |
| **`local_convergence_full_C3`** | the flow clause, `C³`, printed `C` |
| **`constC3_bounds`** | `ε₀ ∈ (0, a/(16C_∞)]`, `C ≥ 1`, `γ₀ > 0` |
| **`local_convergence_gd_C3`** | the descent clause: well defined at every step (three parts) and the `1 − γϱ/4` contraction |
| `EdgeSet`, `edgeKernelE`, `edgeMeasureE`, `sum_edgeSet_eq` | `E`, `K₂` and `λ₂` on `E` |
| **`edgeKernel_mem_edgeSet`**, `edgeKernel_eq_zero_of_not_mem` | "`K₂` maps `E` into itself" |
| **`edgeKernelE_isMarkovOn`**, **`edgeMeasureE_isInvariant`** | `K₂` is a Markov kernel on `E` and `λ₂` is invariant for it |
| **`edgeMeasureE_pos`**, **`edgeMeasureE_total`** | "`λ₂ > 0` when `λ > 0`" and "`λ₂` a probability" |
| **`local_convergence_full_DB`**, **`local_convergence_gd_DB`** | the theorem for the DB loss, `T = K₂` on `E`, `λ₂` in place of `λ` |
| `extE`, `ratio_edgeE_eq`, **`loss_edgeE_eq_db`** | the balance loss of `K₂` on `(E, λ₂)` is the DB loss of `(m₁μ, π_→^μ)` |
| `logSqDeriv2`, `logSqDeriv3`, `hasDerivAt_logSqDeriv`, `hasDerivAt_logSqDeriv2`, `deriv_logSq_eq`, `logSq_C3`, `logSq_deriv_one`, `logSq_deriv2_one` | `g = (log x)²` is `C³` near `[1/2,3/2]`, `g'(1) = 0`, `g''(1) = 2`, `g''' = (4 log x − 6)/x³` |
| **`Gamma3_logSq`** | `Γ₃ = 48 + 32 log 2` at `a = 1/2` |
| `logSqDeriv_taylor_Gamma3` | the Taylor bound of `logSqDeriv` at `M₃ = Γ₃`, **through `taylor_of_C3`** |
| `eps0Gamma3`, **`eps0Gamma3_eq`** | item 2's `ε₀`; it is `eps0C3 logSq (1/2)` |
| **`eps0_antitone_M3`**, `eps0Gamma3_le_eps0Sq` | the radius is antitone in `M₃`; the paper's radius is `≤` the strict library's `eps0Sq` |
| `eps0Gamma3_pos`, **`eps0Gamma3_le_sqrt`** | `0 < ε₀ ≤ λ_min^{1/2}/32` (`proofs.tex:1042`) |
| **`training_speed_full_Gamma3`** | items 1 and 2 of `theo:training_speed_full` at the paper's `ε₀`, from a positive initialization |
| `logSq_C3_bundle`, `isGradientFlow_one`, `pbU`, `lamU`, `sum_edgeSetU`, `pbU_markov`, `pbU_invariant`, **`coer_edgeU`**, **`local_convergence_full_DB_witness`** | inhabitation (kb 0025), see SCOPE |

## Hypothesis checklist — `theo:local_convergence_full` under `C³` (`local_convergence_full_C3`, `local_convergence_gd_C3`)

The rows not listed are `LocalConvergence.lean`'s checklist, verbatim.

| paper hypothesis | here |
|---|---|
| `g : ℝ₊* → ℝ` is `C³` on `[1−a,1+a]` | ⚠ **read two-sided**: `hC3 : ∀ y ∈ Icc (1−a) (1+a), ContDiffAt ℝ 3 g y`, i.e. `C³` on an open neighbourhood of the closed window, with `g : ℝ → ℝ`. A `g` that is `C³` only one-sidedly at `1 ± a` is not covered; see SCOPE |
| `Γ₃ := sup_{[1−a,1+a]}|g'''|` | ✓ `Gamma3 g a := sSup ((fun y => |deriv (deriv (deriv g)) y|) '' Icc (1−a) (1+a))`, finite by `bddAbove_abs_g3` |
| `g'(1) = 0` | ✓ `hg1 : deriv g 1 = 0` |
| `g''(1) > 0` | ✓ `hg2 : 0 < deriv (deriv g) 1`; `g2` is **`deriv (deriv g) 1`**, not a free parameter |
| `g(1) = 0` | ✗ **not carried**: unused by the proof (a stronger theorem) |
| `a ∈ (0,1)` | ⚠ `ha : 0 < a`; `a < 1` unused. The printed window `min(a/4, ε₁)` agrees with the library's `min(min(a,1)/4, ε₁)` for `a < 1` (`epsW_eq_of_lt_one`) |
| the flow `μ̇ = −∇^λ𝓛_{g,ν}(μ)`, driven by `g'` | ✓ `IsGradientFlow K lam (λw) (deriv g) (1 + h)` — the flow is driven by `deriv g` itself, not by an opaque `gd` |
| the descent `h_{k+1} = h_k − γD_k` | ✓ `hstep` with `lossGrad … (deriv g) …`; "`D_k` the density of the gradient" is the third conjunct, the derivative of `𝓛_{g,ν}` with `g` itself |
| `ε₀`, `C`, `γ₀` explicit, "depending only on `g''(1)`, `sup|g'''|`, `a`, `w_min`, `‖w‖_{L^∞}`, `B̂`, `C_∞`" | ✓ `eps0C3`, `CC3`, `gamma0C3` are the printed formulas with `g2 := g''(1)`, `M₃ := Γ₃`; `constC3_congr` is the dependence clause as a congruence; `‖w‖_{L^∞}` is read as an upper bound `wsup`, as in `LocalConvergence.lean` |
| `C ≥ 1` | ✓ `C := max(1, C₇)`, `constC3_bounds` |

## Hypothesis checklist — the DB instance (`local_convergence_full_DB`, `local_convergence_gd_DB`)

| paper hypothesis / claim | here |
|---|---|
| `π_←` a Markov kernel on the finite `𝒮` with invariant probability `λ > 0` | ✓ `hpb : Core.IsMarkovOn lam pb`, `hinvpb : Core.IsInvariant lam pb`, `hlam`, `htot` — the hypotheses `local_convergence_full` takes of `T` |
| `E := {(s,s') : π_←(s'→s) > 0}`, finite | ✓ `EdgeSet pb`, a subtype of `V × V`; `Fintype` by instance |
| "`K₂` maps `E` into itself" | ✓ **proved**, `edgeKernel_mem_edgeSet` |
| `K₂` on `E` is `T` | ✓ `edgeKernelE pb`, **proved** Markov on `E` (`edgeKernelE_isMarkovOn`) |
| "`λ₂(s,s') = π_←(s'→s)λ(s') > 0` when `λ > 0`" | ✓ **proved**, `edgeMeasureE_pos` |
| "`λ₂` is a probability, its second marginal being `λ`" | ✓ **proved**, `edgeMeasureE_total` |
| `λ₂` invariant for `K₂` (`lem:lift_wellposed`) | ✓ **proved on `E`**, `edgeMeasureE_isInvariant`, from `Lift.pushEdge_edgeMeasure` |
| `λ_min := min_E λ₂`, `C_∞ := λ_min^{−1/2}` | ⚠ a lower bound `lamMin` with `0 < lamMin ≤ λ₂`, as in `LocalConvergence.lean` |
| `B̂ ≥ 1` a coercivity constant of `K₂` on `L²(λ₂)` | ✓ `hB1`, `hcoer` on functions on `E`, as the paper takes it (the summable-mixing and `lem:lift_coercivity` routes to it are not used here) |
| "for the DB loss" | ✓ the balance loss of `K₂` on `(E, λ₂)`; `loss_edgeE_eq_db` shows it is the DB loss of `(m₁μ, π_→^μ)` at `μ = uλ₂` extended by `0` off `E` |
| `ν̂ = wλ₂` on `E`, `w ≥ w_min > 0` | ✓ `w : EdgeSet pb → ℝ`, `hwmin`, `hwsup` |

## Hypothesis checklist — `theo:training_speed_full` item 2 (`training_speed_full_Gamma3`)

Hypotheses verbatim `TrainingSpeed.training_speed_full_of_init`'s; that file's checklist applies.

| paper | here |
|---|---|
| `ε₀` the radius of Theorem 10 for `g = (log x)²` at `a = 1/2`, `B̂_σ`, `C_∞ = λ_min^{−1/2}` | ✓ `eps0Gamma3 wmin wsup (BhatSigma G uH lam) (minOver G lam)`, `= eps0C3 logSq (1/2) …` (`eps0Gamma3_eq`), `Γ₃ = 48 + 32 log 2` (`Gamma3_logSq`) |
| Theorem 10 invoked for `g = (log x)²` | ✓ at `M₃ = Γ₃`, its Taylor bound derived from `C³` (`logSqDeriv_taylor_Gamma3`) |
| `ε₀ ≤ λ_min^{1/2}/32 ≤ 1/2` (proof) | ✓ `eps0Gamma3_le_sqrt`; `≤ 1/2` through `eps0Gamma3_le_eps0Sq` and `eps0Sq_le_half` |
| `t₁ ≤ T₀`, entry into the `ε₀`-ball, `m₁ ∈ [m₀,‖u₀‖]`, rate `ϱ_σ/(2m₁²)` | ✓ as in `training_speed_full_of_init`, at the paper's `ε₀` |
| item 3 (gradient descent) | ✗ **not here** |

## SCOPE (disclosed)

* **Finite state space**, as everywhere in `GFNBounds.Balance`.
* **`C³` is read two-sided at the endpoints.** `ContDiffAt ℝ 3 g y` at every `y ∈ [1−a,1+a]` asks
  `g` to be `C³` on an open set containing the closed window. The paper's `g : ℝ₊* → ℝ` "`C³` on
  `[1−a,1+a]`" also admits a `g` whose third derivative exists only one-sidedly at `1 ± a`; that
  reading is not covered. The endpoints matter only through the closed Taylor window the library's
  `htaylor` asks, since the ratios stay within `2a/3` of `1`. For the paper's only instance,
  `(log x)²`, which is `C^∞` on `ℝ₊*`, the readings agree.
* **`g : ℝ → ℝ`, and `deriv g` is Mathlib's total derivative** (`0` where `g` is not
  differentiable). The flow and the descent are driven by `deriv g`; the theorem keeps the ratios in
  the window, where `deriv g` is the paper's `g'`.
* **`g''(1)` is `deriv (deriv g) 1` and `g'''` is `deriv (deriv (deriv g))`**, iterated total
  derivatives; under `hC3` they are the classical ones on the window (`hasDerivAt_deriv_of_C3`).
* **`B̂` stays a hypothesis** for both instances, as the paper's statement has it. For the DB
  instance, deriving it as `1 + C` from a coercivity constant `C` of `π_←` is
  `lem:lift_coercivity`, not built here.
* **Existence of the flow is hypothesised, not proved, for a general `C³` generator.** The descent
  exists by recursion (`local_convergence_gd_C3` shows every step well defined). For
  `g = (log x)²` and `g = (x−1)²` on a finite ergodic chain the flow exists and is unique by
  `FlowExistence.lean` (`existsUnique_flow_logSq_of_ergodic`, `existsUnique_flow_sq_of_ergodic`);
  for a general `C³` `g` the local existence near `λ` is not composed here.
* **Item 3 of `theo:training_speed_full` is not restated at `Γ₃`.** It is not formalized in the
  strict library either.
* **Inhabitation (kb 0025).** The `C³` bundle is inhabited by `g = (log x)²` at `a = 1/2`
  (`logSq_C3_bundle`). The DB bundle is inhabited **in full** on the uniform backward policy on two
  states (`local_convergence_full_DB_witness`): `K₂` on `E = 𝒮²`, `λ₂ ≡ 1/4`, `w ≡ 1`,
  `g = (log x)²`, `B̂ = 2` (`coer_edgeU`, the `1 + C` of `lem:lift_coercivity` at `C = 1`, proved by
  an explicit sum of squares), `λ_min = 1/4` and the balanced flow `h ≡ 0`
  (`isGradientFlow_one`). **The flow in the witness is the trivial one**; a non-balanced solution
  of the flow predicate is not exhibited here. `training_speed_full_Gamma3`'s hypotheses are
  `training_speed_full_of_init`'s, whose inhabitation is that file's (`cycle_training_speed_check`
  for the graph data; the flow again not exhibited).
* **`sorry`-free and axiom-clean.** `#print axioms` on `taylor_of_C3`,
  `local_convergence_full_C3`, `local_convergence_gd_C3`, `constC3_bounds`,
  `local_convergence_full_DB`, `local_convergence_gd_DB`, `loss_edgeE_eq_db`, `Gamma3_logSq`,
  `eps0_antitone_M3`, `training_speed_full_Gamma3` and `local_convergence_full_DB_witness`
  returns `[propext, Classical.choice, Quot.sound]`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset Set

/-! ### Taylor from `C³` -/

/-- **`theo:local_convergence_full`, `Γ₃ := sup_{[1−a,1+a]} |g'''|`** (`proofs.tex:675`), with
`g'''` the iterated derivative `deriv (deriv (deriv g))`. -/
noncomputable def Gamma3 (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun y => |deriv (deriv (deriv g)) y|) '' Icc (1 - a) (1 + a))

theorem bddAbove_abs_g3 {g : ℝ → ℝ} {a : ℝ}
    (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y) :
    BddAbove ((fun y => |deriv (deriv (deriv g)) y|) '' Icc (1 - a) (1 + a)) := by
  refine isCompact_Icc.bddAbove_image ?_
  intro y hy
  have h0 : ContDiffAt ℝ 0 (deriv (deriv (deriv g))) y :=
    (((hC3 y hy).derivWithin (m := 2) (by norm_num)).derivWithin (m := 1) (by norm_num)).derivWithin
      (m := 0) (by norm_num)
  exact (continuous_abs.continuousAt.comp h0.continuousAt).continuousWithinAt

theorem abs_g3_le_Gamma3 {g : ℝ → ℝ} {a : ℝ}
    (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y) {y : ℝ} (hy : y ∈ Icc (1 - a) (1 + a)) :
    |deriv (deriv (deriv g)) y| ≤ Gamma3 g a :=
  le_csSup (bddAbove_abs_g3 hC3) ⟨y, hy, rfl⟩

theorem Gamma3_nonneg {g : ℝ → ℝ} {a : ℝ} (ha0 : 0 ≤ a)
    (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y) : 0 ≤ Gamma3 g a :=
  le_trans (abs_nonneg _) (abs_g3_le_Gamma3 hC3 (y := 1) ⟨by linarith, by linarith⟩)

/-- A quadratic fence. -/
theorem abs_le_quadratic_of_deriv {e e' : ℝ → ℝ} {M b : ℝ} (hb : 0 ≤ b)
    (he : ∀ s ∈ Icc 0 b, HasDerivAt e (e' s) s) (h0 : e 0 = 0)
    (hbound : ∀ s ∈ Icc 0 b, |e' s| ≤ M * s) : |e b| ≤ M / 2 * b ^ 2 := by
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := b) (f := e)
    (f' := e') (B := fun s => M / 2 * s ^ 2) (B' := fun s => M * s)
    (fun s hs => (he s hs).continuousAt.continuousWithinAt)
    (fun s hs => (he s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp only [h0, norm_zero]; norm_num)
    (fun s => ((hasDerivAt_pow 2 s).const_mul (M / 2)).congr_deriv (by push_cast; ring))
    (fun s hs => by
      simp only [Real.norm_eq_abs]
      exact hbound s (Ico_subset_Icc_self hs))
  have := key ⟨hb, le_rfl⟩
  simpa only [Real.norm_eq_abs] using this

/-- The two derivatives the Taylor argument differentiates, at every point of the window. -/
theorem hasDerivAt_deriv_of_C3 {g : ℝ → ℝ} {a : ℝ}
    (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y) {y : ℝ} (hy : y ∈ Icc (1 - a) (1 + a)) :
    HasDerivAt g (deriv g y) y ∧ HasDerivAt (deriv g) (deriv (deriv g) y) y
      ∧ HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) y) y := by
  have h3 := hC3 y hy
  have h2 : ContDiffAt ℝ 2 (deriv g) y := h3.derivWithin (m := 2) (by norm_num)
  have h1 : ContDiffAt ℝ 1 (deriv (deriv g)) y := h2.derivWithin (m := 1) (by norm_num)
  exact ⟨(h3.differentiableAt (by norm_num)).hasDerivAt,
    (h2.differentiableAt (by norm_num)).hasDerivAt,
    (h1.differentiableAt (by norm_num)).hasDerivAt⟩

/-- **`|g''(t) − g''(1)| ≤ Γ₃|t − 1|`** on the window, by the mean value theorem. -/
theorem abs_g2_sub_le {g : ℝ → ℝ} {a : ℝ} (ha0 : 0 ≤ a)
    (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y) {t : ℝ} (ht : t ∈ Icc (1 - a) (1 + a)) :
    |deriv (deriv g) t - deriv (deriv g) 1| ≤ Gamma3 g a * |t - 1| := by
  have h1mem : (1 : ℝ) ∈ Icc (1 - a) (1 + a) := ⟨by linarith, by linarith⟩
  have := (convex_Icc (1 - a) (1 + a)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := deriv (deriv g)) (f' := deriv (deriv (deriv g))) (C := Gamma3 g a)
    (fun x hx => (hasDerivAt_deriv_of_C3 hC3 hx).2.2.hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using abs_g3_le_Gamma3 hC3 hx) h1mem ht
  simpa only [Real.norm_eq_abs] using this

/-- **`theo:local_convergence_full`, the `C³` hypothesis read as the Taylor bound it is used
through** (Taylor's formula in `theo:gd_diffusion_full`'s proof, `proofs.tex:616–626`, which Step 1
of the proof invokes): `|g'(y) − g''(1)(y−1)| ≤ (Γ₃/2)(y−1)²` for `|y − 1| ≤ a`, given
`g'(1) = 0` — the library's `htaylor` at `gd = g'`, `g2 = g''(1)`, `M3 = Γ₃`. -/
theorem taylor_of_C3 {g : ℝ → ℝ} {a : ℝ}
    (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y) (hg1 : deriv g 1 = 0) :
    ∀ y : ℝ, |y - 1| ≤ a →
      |deriv g y - deriv (deriv g) 1 * (y - 1)| ≤ Gamma3 g a / 2 * (y - 1) ^ 2 := by
  intro y hy
  have ha0 : 0 ≤ a := le_trans (abs_nonneg _) hy
  set g2 := deriv (deriv g) 1 with hg2def
  rcases le_total 1 y with h1y | hy1
  · -- `y ≥ 1`: fence `s ↦ g'(1+s) − g''(1)s` on `[0, y−1]`
    have hb : 0 ≤ y - 1 := by linarith
    have hmem : ∀ s ∈ Icc (0:ℝ) (y - 1), 1 + s ∈ Icc (1 - a) (1 + a) := by
      intro s hs
      have := abs_le.mp hy
      exact ⟨by linarith [hs.1], by linarith [hs.2, this.2]⟩
    have key := abs_le_quadratic_of_deriv (e := fun s => deriv g (1 + s) - g2 * s)
      (e' := fun s => deriv (deriv g) (1 + s) - g2) (M := Gamma3 g a) hb
      (fun s hs => by
        have hd := (hasDerivAt_deriv_of_C3 hC3 (hmem s hs)).2.1
        have hc : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
        have hcomp := hd.comp s hc
        have hlin : HasDerivAt (fun s : ℝ => g2 * s) g2 s := by
          simpa only [mul_one] using (hasDerivAt_id' s).const_mul g2
        simpa only [mul_one, Function.comp_def] using hcomp.fun_sub hlin)
      (by simp only [add_zero, mul_zero, sub_zero, hg1])
      (fun s hs => by
        have h := abs_g2_sub_le ha0 hC3 (hmem s hs)
        have hs0 : |1 + s - 1| = s := by
          rw [show 1 + s - 1 = s by ring, abs_of_nonneg hs.1]
        rwa [hs0] at h)
    have hy' : 1 + (y - 1) = y := by ring
    simpa only [hy'] using key
  · -- `y ≤ 1`: fence `s ↦ g'(1−s) + g''(1)s` on `[0, 1−y]`
    have hb : 0 ≤ 1 - y := by linarith
    have hmem : ∀ s ∈ Icc (0:ℝ) (1 - y), 1 - s ∈ Icc (1 - a) (1 + a) := by
      intro s hs
      have := abs_le.mp hy
      exact ⟨by linarith [hs.2, this.1], by linarith [hs.1]⟩
    have key := abs_le_quadratic_of_deriv (e := fun s => deriv g (1 - s) + g2 * s)
      (e' := fun s => -deriv (deriv g) (1 - s) + g2) (M := Gamma3 g a) hb
      (fun s hs => by
        have hd := (hasDerivAt_deriv_of_C3 hC3 (hmem s hs)).2.1
        have hc : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
          exact (hasDerivAt_id' s).const_sub 1
        have hcomp := hd.comp s hc
        have hlin : HasDerivAt (fun s : ℝ => g2 * s) g2 s := by
          simpa only [mul_one] using (hasDerivAt_id' s).const_mul g2
        have hsum := hcomp.fun_add hlin
        refine hsum.congr_deriv ?_
        ring)
      (by simp only [sub_zero, mul_zero, add_zero, hg1])
      (fun s hs => by
        have h := abs_g2_sub_le ha0 hC3 (hmem s hs)
        have hs0 : |1 - s - 1| = s := by
          rw [show 1 - s - 1 = -s by ring, abs_neg, abs_of_nonneg hs.1]
        rw [hs0] at h
        rw [show -deriv (deriv g) (1 - s) + g2 = -(deriv (deriv g) (1 - s) - g2) by ring, abs_neg]
        exact h)
    have hy' : 1 - (1 - y) = y := by ring
    have hsq : (1 - y) ^ 2 = (y - 1) ^ 2 := by ring
    have hlin : deriv g y + g2 * (1 - y) = deriv g y - g2 * (y - 1) := by ring
    simpa only [hy', hsq, hlin] using key

/-! ### The constants of Theorem 10 read through `g''(1)` and `Γ₃` -/

/-- `ε₀` of `theo:local_convergence_full` at `g''(1)`, `Γ₃ = Gamma3 g a`. -/
noncomputable def eps0C3 (g : ℝ → ℝ) (a wmin wsup Bhat lamMin : ℝ) : ℝ :=
  eps0 (epsW a (deriv (deriv g) 1) wmin (Kexp (deriv (deriv g) 1) a (Gamma3 g a) wsup) Bhat)
    (Cinf lamMin) (C7 (C6 (Cg (deriv (deriv g) 1) a (Gamma3 g a)) wsup) (deriv (deriv g) 1) wmin)
    (rhoL (deriv (deriv g) 1) wmin Bhat) (C6 (Cg (deriv (deriv g) 1) a (Gamma3 g a)) wsup)

/-- `C := max(1, C₇)` at `g''(1)`, `Γ₃`. -/
noncomputable def CC3 (g : ℝ → ℝ) (a wmin wsup : ℝ) : ℝ :=
  max 1 (C7 (C6 (Cg (deriv (deriv g) 1) a (Gamma3 g a)) wsup) (deriv (deriv g) 1) wmin)

/-- `γ₀` at `g''(1)`, `Γ₃`. -/
noncomputable def gamma0C3 (g : ℝ → ℝ) (a wmin wsup Bhat : ℝ) : ℝ :=
  gamma0 (deriv (deriv g) 1) wmin
    (Lgd (deriv (deriv g) 1) wsup (Kexp (deriv (deriv g) 1) a (Gamma3 g a) wsup)
      (epsW a (deriv (deriv g) 1) wmin (Kexp (deriv (deriv g) 1) a (Gamma3 g a) wsup) Bhat))

/-- **"depending only on `g''(1)`, `Γ₃`, `a`, `w_min`, `‖w‖_{L^∞}`, `B̂`, `C_∞`"**, as a
congruence: two generators with the same `g''(1)` and `Γ₃` have the same `ε₀`, `C`, `γ₀`. -/
theorem constC3_congr {g g' : ℝ → ℝ} {a : ℝ} (h2 : deriv (deriv g) 1 = deriv (deriv g') 1)
    (h3 : Gamma3 g a = Gamma3 g' a) (wmin wsup Bhat lamMin : ℝ) :
    eps0C3 g a wmin wsup Bhat lamMin = eps0C3 g' a wmin wsup Bhat lamMin
      ∧ CC3 g a wmin wsup = CC3 g' a wmin wsup
      ∧ gamma0C3 g a wmin wsup Bhat = gamma0C3 g' a wmin wsup Bhat := by
  simp only [eps0C3, CC3, gamma0C3, h2, h3]
  exact ⟨trivial, trivial, trivial⟩

/-- **Step 4's `ε := min(a/4, ε₁)`** as printed, for `a < 1`: the library's
`min(min(a,1)/4, ε₁)` is the same number. -/
theorem epsW_eq_of_lt_one {a g2 wmin Kex Bhat : ℝ} (ha1 : a < 1) :
    epsW a g2 wmin Kex Bhat = min (a / 4) (eps1 g2 wmin Kex Bhat) := by
  simp only [epsW, min_eq_left ha1.le]

section LocalConvergenceC3

variable {V : Type*} [Fintype V]

/-- **`theo:local_convergence_full`, the flow clause, under the paper's `C³` hypothesis**:
`g` is `C³` at every point of `[1−a,1+a]`, `g'(1) = 0 < g''(1)`, the flow is driven by `g'`, and
every constant is the printed formula in `g''(1)` and `Γ₃ = sup_{[1−a,1+a]}|g'''|`. -/
theorem local_convergence_full_C3 {K : V → V → ℝ} {lam w : V → ℝ} {g : ℝ → ℝ}
    {h : ℝ → V → ℝ} {a wsup wmin Bhat lamMin : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (ha : 0 < a) (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) (deriv g) fun s x => 1 + h s x)
    (hnorm0 : Graph.nrmL2 lam (h 0) ≤ eps0C3 g a wmin wsup Bhat lamMin) :
    ∃ cinf : ℝ,
      |cinf - 1 - Graph.meanL2 lam (h 0)|
          ≤ CC3 g a wmin wsup * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (fun x => h t x - (cinf - 1))
            ≤ 2 * Real.exp (-(rhoL (deriv (deriv g) 1) wmin Bhat * t / 2))
                * Graph.nrmL2 lam (perpL2 lam (h 0)) :=
  local_convergence_full_C hK hinv hlam htot hlmin0 hlmin hg2 (Gamma3_nonneg ha.le hC3) ha hwsup
    hwmin0 hwmin hB1 hcoer (taylor_of_C3 hC3 hg1) hflow hnorm0

/-- **`theo:local_convergence_full`, the constants**: `ε₀ ∈ (0, a/(16C_∞)]`, `C ≥ 1` and `γ₀ > 0`
at the constants of `local_convergence_full_C3`. -/
theorem constC3_bounds {lam w : V → ℝ} {g : ℝ → ℝ} {a wsup wmin Bhat lamMin : ℝ}
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin)
    (ha : 0 < a) (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y)
    (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hB1 : 1 ≤ Bhat) :
    eps0C3 g a wmin wsup Bhat lamMin ∈ Set.Ioc 0 (a / (16 * Cinf lamMin))
      ∧ 1 ≤ CC3 g a wmin wsup ∧ 0 < gamma0C3 g a wmin wsup Bhat :=
  ⟨eps0_mem_Ioc htot hlmin0 hg2 (Gamma3_nonneg ha.le hC3) ha hwsup hwmin0 hwmin hB1,
    one_le_max_C7 _ _ _,
    gamma0_pos_of_weights htot hg2 (Gamma3_nonneg ha.le hC3) ha.le hwsup hwmin0 hwmin
      (le_trans zero_le_one hB1)⟩

/-- **`theo:local_convergence_full`, the gradient-descent clause, under the paper's `C³`
hypothesis**: for `0 ≤ γ ≤ γ₀` and `‖h₀‖ ≤ ε₀`, the descent driven by `g'` is well defined at
every step — `1 + h_k > 0`, `|r_k − 1| ≤ 2a/3`, and `D_k` is the derivative of `𝓛_{g,ν}` in every
direction — and `‖h^⊥_{k+1}‖ ≤ (1 − γϱ/4)‖h^⊥_k‖`. -/
theorem local_convergence_gd_C3 {K : V → V → ℝ} {lam w : V → ℝ} {g : ℝ → ℝ}
    {hk : ℕ → V → ℝ} {a wsup wmin Bhat lamMin gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (ha : 0 < a) (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (hstep : ∀ k : ℕ, hk (k + 1) = fun x =>
      hk k x - gam * lossGrad K lam (fun z => lam z * w z) (deriv g) (fun z => 1 + hk k z) x)
    (hgam0 : 0 ≤ gam) (hgam : gam ≤ gamma0C3 g a wmin wsup Bhat)
    (hnorm0 : Graph.nrmL2 lam (hk 0) ≤ eps0C3 g a wmin wsup Bhat lamMin) :
    ∀ k : ℕ, ((∀ x : V, 0 < 1 + hk k x)
      ∧ (∀ x : V, |ratio K lam (fun z => 1 + hk k z) x - 1| ≤ 2 * a / 3)
      ∧ ∀ d : V → ℝ,
          HasDerivAt
            (fun t : ℝ => loss K lam (fun z => lam z * w z) (fun x => 1 + hk k x + t * d x) g)
            (Graph.ipL2 lam (lossGrad K lam (fun z => lam z * w z) (deriv g)
              fun z => 1 + hk k z) d) 0)
      ∧ Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))
          ≤ (1 - gam * rhoL (deriv (deriv g) 1) wmin Bhat / 4)
              * Graph.nrmL2 lam (perpL2 lam (hk k)) := by
  have hM3 := Gamma3_nonneg ha.le hC3
  have htay := taylor_of_C3 hC3 hg1
  have hg : ∀ y : ℝ, |y - 1| < a → HasDerivAt g (deriv g y) y := fun y hy =>
    (hasDerivAt_deriv_of_C3 hC3 (y := y)
      ⟨by linarith [(abs_lt.mp hy).1], by linarith [(abs_lt.mp hy).2]⟩).1
  intro k
  exact ⟨local_convergence_gd_welldefined hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha hwsup
      hwmin0 hwmin hB1 hcoer hg htay hstep hgam0 hgam hnorm0 k,
    local_convergence_gd hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha.le hwsup hwmin0 hwmin hB1
      hcoer htay hstep hgam0 hgam hnorm0 k⟩

end LocalConvergenceC3

/-! ### The DB instance: `T = K₂` on the edge set `E`, with `λ₂` -/

section EdgeInstance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The edge set `E := {(s,s') ∈ 𝒮² : π_←(s' → s) > 0}`** (`proofs.tex:667`), as a subtype of
`V × V`; it is a `Fintype` because `V` is. `pb x y` is `π_←(x → y)`, as in `Lift.lean`. -/
abbrev EdgeSet (pb : V → V → ℝ) : Type _ := {p : V × V // 0 < pb p.2 p.1}

/-- **`K₂` restricted to `E`**: `K₂(e → e') = [e'.2 = e.1] · π_←(e.1 → e'.1)`, `Lift.edgeKernel`
read at the two edges. -/
def edgeKernelE (pb : V → V → ℝ) (e e' : EdgeSet pb) : ℝ :=
  edgeKernel pb e.1.1 e.1.2 e'.1.1 e'.1.2

/-- **`λ₂` restricted to `E`**: `λ₂(s,s') = π_←(s' → s) λ(s')`, `Lift.edgeMeasure` at the edge. -/
def edgeMeasureE (pb : V → V → ℝ) (lam : V → ℝ) (e : EdgeSet pb) : ℝ :=
  edgeMeasure pb lam e.1.1 e.1.2

omit [DecidableEq V] in
/-- A sum over `E` of a function vanishing off `E` is the sum over `𝒮²`. -/
theorem sum_edgeSet_eq {pb : V → V → ℝ} (f : V × V → ℝ)
    (hf : ∀ p : V × V, ¬ 0 < pb p.2 p.1 → f p = 0) :
    ∑ e : EdgeSet pb, f e.1 = ∑ p : V × V, f p := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun p : V × V => 0 < pb p.2 p.1) f]
  have h0 : ∑ i : {x : V × V // ¬ 0 < pb x.2 x.1}, f i = 0 :=
    Finset.sum_eq_zero fun i _ => hf i.1 i.2
  rw [h0, add_zero]

omit [Fintype V] in
/-- **`theo:local_convergence_full`, DB instance: "`K₂` maps `E` into itself"** (`proofs.tex:667`): from any pair, `K₂` charges only pairs of
`E`. -/
theorem edgeKernel_mem_edgeSet {pb : V → V → ℝ} {s s' z w : V}
    (hpos : 0 < edgeKernel pb s s' z w) : 0 < pb w z := by
  unfold edgeKernel at hpos
  split at hpos
  · rename_i hws
    rw [hws]
    exact hpos
  · exact absurd hpos (lt_irrefl 0)

omit [Fintype V] in
/-- The same, as vanishing: off `E` the kernel is `0` (`π_← ≥ 0`). -/
theorem edgeKernel_eq_zero_of_not_mem {pb : V → V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y) {s s' z w : V}
    (hzw : ¬ 0 < pb w z) : edgeKernel pb s s' z w = 0 := by
  rcases (edgeKernel_nonneg hnn s s' z w).lt_or_eq with hlt | heq
  · exact absurd (edgeKernel_mem_edgeSet hlt) hzw
  · exact heq.symm

omit [Fintype V] [DecidableEq V] in
/-- Off `E` the edge measure is `0`. -/
theorem edgeMeasure_eq_zero_of_not_mem {pb : V → V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (lam : V → ℝ) {s s' : V} (hss : ¬ 0 < pb s' s) : edgeMeasure pb lam s s' = 0 := by
  have h0 : pb s' s = 0 := le_antisymm (not_lt.mp hss) (hnn s' s)
  simp only [edgeMeasure, h0, zero_mul]

/-- **`theo:local_convergence_full`, DB instance: `K₂` is a Markov kernel on `E`**: non-negative, and every row sums to `1` over `E`. -/
theorem edgeKernelE_isMarkovOn {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) :
    Core.IsMarkovOn (edgeMeasureE pb lam) (edgeKernelE pb) := by
  refine ⟨fun e e' => edgeKernel_nonneg hnn _ _ _ _, fun e _ => ?_⟩
  have h := sum_edgeSet_eq (pb := pb) (fun p : V × V => edgeKernel pb e.1.1 e.1.2 p.1 p.2)
    (fun p hp => edgeKernel_eq_zero_of_not_mem hnn hp)
  simp only [edgeKernelE]
  rw [h, Fintype.sum_prod_type]
  exact edgeKernel_total hrow _ _

omit [Fintype V] [DecidableEq V] in
/-- **`theo:local_convergence_full`, DB instance: `λ₂ > 0` on `E` when `λ > 0`** (`proofs.tex:667`). -/
theorem edgeMeasureE_pos {pb : V → V → ℝ} {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    (e : EdgeSet pb) : 0 < edgeMeasureE pb lam e :=
  mul_pos e.2 (hlam e.1.2)

omit [DecidableEq V] in
/-- **`theo:local_convergence_full`, DB instance: `λ₂` is a probability on `E`** (`proofs.tex:675`: "its second marginal being `λ`"). -/
theorem edgeMeasureE_total {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) (htot : ∑ x, lam x = 1) :
    ∑ e : EdgeSet pb, edgeMeasureE pb lam e = 1 := by
  have h := sum_edgeSet_eq (pb := pb) (fun p : V × V => edgeMeasure pb lam p.1 p.2)
    (fun p hp => edgeMeasure_eq_zero_of_not_mem hnn lam hp)
  simp only [edgeMeasureE]
  rw [h, Fintype.sum_prod_type]
  exact edgeMeasure_total hrow htot

/-- **`theo:local_convergence_full`, DB instance: `λ₂` is `K₂`-invariant on `E`**: `Lift.pushEdge_edgeMeasure`, with both sums restricted to
`E`, where `λ₂` and `K₂` live. -/
theorem edgeMeasureE_isInvariant {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hlam : ∀ x, 0 ≤ lam x) (hinv : Invariant pb lam) :
    Core.IsInvariant (edgeMeasureE pb lam) (edgeKernelE pb) := by
  refine ⟨fun e => edgeMeasure_nonneg hnn hlam _ _, fun e' => ?_⟩
  have h := sum_edgeSet_eq (pb := pb)
    (fun p : V × V => edgeMeasure pb lam p.1 p.2 * edgeKernel pb p.1 p.2 e'.1.1 e'.1.2)
    (fun p hp => by rw [edgeMeasure_eq_zero_of_not_mem hnn lam hp, zero_mul])
  simp only [edgeMeasureE, edgeKernelE]
  rw [h, Fintype.sum_prod_type]
  have hpush := congrFun (congrFun (pushEdge_edgeMeasure hinv) e'.1.1) e'.1.2
  simpa only [pushEdge] using hpush

/-- **`theo:local_convergence_full` for the DB loss** (`proofs.tex:667`): `T = K₂` on the finite
edge set `E`, `λ₂` in the role of `λ`, `λ_min := min_E λ₂` (read as a lower bound `lamMin`),
`C_∞ = λ_min^{−1/2}`, and a coercivity constant `B̂ ≥ 1` of `K₂` on `L²(λ₂)` as hypothesis. The
kernel, the invariance of `λ₂`, its positivity and its total mass are **proved** from the backward
policy; the `C³` hypothesis is the paper's. Flow clause. -/
theorem local_convergence_full_DB {pb : V → V → ℝ} {lam : V → ℝ} {w : EdgeSet pb → ℝ}
    {g : ℝ → ℝ} {h : ℝ → EdgeSet pb → ℝ} {a wsup wmin Bhat lamMin : ℝ}
    (hpb : Core.IsMarkovOn lam pb) (hinvpb : Core.IsInvariant lam pb) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin)
    (hlmin : ∀ e, lamMin ≤ edgeMeasureE pb lam e)
    (ha : 0 < a) (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ e, |w e| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ e, wmin ≤ w e)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : EdgeSet pb → ℝ,
      Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) f)
        ≤ Bhat * Graph.nrmL2 (edgeMeasureE pb lam) (Aop (edgeKernelE pb) (edgeMeasureE pb lam) f))
    (hflow : IsGradientFlow (edgeKernelE pb) (edgeMeasureE pb lam)
      (fun e => edgeMeasureE pb lam e * w e) (deriv g) fun s e => 1 + h s e)
    (hnorm0 : Graph.nrmL2 (edgeMeasureE pb lam) (h 0) ≤ eps0C3 g a wmin wsup Bhat lamMin) :
    ∃ cinf : ℝ,
      |cinf - 1 - Graph.meanL2 (edgeMeasureE pb lam) (h 0)|
          ≤ CC3 g a wmin wsup
              * Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) (h 0)) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 (edgeMeasureE pb lam) (fun e => h t e - (cinf - 1))
            ≤ 2 * Real.exp (-(rhoL (deriv (deriv g) 1) wmin Bhat * t / 2))
                * Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) (h 0)) := by
  have hrow : ∀ x, ∑ y, pb x y = 1 := fun x => hpb.row_sum (hlam x).ne'
  exact local_convergence_full_C3 (edgeKernelE_isMarkovOn hpb.nonneg hrow)
    (edgeMeasureE_isInvariant hpb.nonneg hinvpb.nonneg (invariant_of_isInvariant hinvpb))
    (edgeMeasureE_pos hlam) (edgeMeasureE_total hpb.nonneg hrow htot) hlmin0 hlmin ha hC3 hg1
    hg2 hwsup hwmin0 hwmin hB1 hcoer hflow hnorm0

/-- **`theo:local_convergence_full` for the DB loss, the gradient-descent clause**, on `E` with
`λ₂`, as `local_convergence_full_DB`. -/
theorem local_convergence_gd_DB {pb : V → V → ℝ} {lam : V → ℝ} {w : EdgeSet pb → ℝ}
    {g : ℝ → ℝ} {hk : ℕ → EdgeSet pb → ℝ} {a wsup wmin Bhat lamMin gam : ℝ}
    (hpb : Core.IsMarkovOn lam pb) (hinvpb : Core.IsInvariant lam pb) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin)
    (hlmin : ∀ e, lamMin ≤ edgeMeasureE pb lam e)
    (ha : 0 < a) (hC3 : ∀ y ∈ Icc (1 - a) (1 + a), ContDiffAt ℝ 3 g y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwsup : ∀ e, |w e| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ e, wmin ≤ w e)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : EdgeSet pb → ℝ,
      Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) f)
        ≤ Bhat * Graph.nrmL2 (edgeMeasureE pb lam) (Aop (edgeKernelE pb) (edgeMeasureE pb lam) f))
    (hstep : ∀ k : ℕ, hk (k + 1) = fun e =>
      hk k e - gam * lossGrad (edgeKernelE pb) (edgeMeasureE pb lam)
        (fun z => edgeMeasureE pb lam z * w z) (deriv g) (fun z => 1 + hk k z) e)
    (hgam0 : 0 ≤ gam) (hgam : gam ≤ gamma0C3 g a wmin wsup Bhat)
    (hnorm0 : Graph.nrmL2 (edgeMeasureE pb lam) (hk 0) ≤ eps0C3 g a wmin wsup Bhat lamMin) :
    ∀ k : ℕ, ((∀ e, 0 < 1 + hk k e)
      ∧ (∀ e, |ratio (edgeKernelE pb) (edgeMeasureE pb lam) (fun z => 1 + hk k z) e - 1|
          ≤ 2 * a / 3)
      ∧ ∀ d : EdgeSet pb → ℝ,
          HasDerivAt
            (fun t : ℝ => loss (edgeKernelE pb) (edgeMeasureE pb lam)
              (fun z => edgeMeasureE pb lam z * w z) (fun e => 1 + hk k e + t * d e) g)
            (Graph.ipL2 (edgeMeasureE pb lam) (lossGrad (edgeKernelE pb) (edgeMeasureE pb lam)
              (fun z => edgeMeasureE pb lam z * w z) (deriv g) fun z => 1 + hk k z) d) 0)
      ∧ Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) (hk (k + 1)))
          ≤ (1 - gam * rhoL (deriv (deriv g) 1) wmin Bhat / 4)
              * Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) (hk k)) := by
  have hrow : ∀ x, ∑ y, pb x y = 1 := fun x => hpb.row_sum (hlam x).ne'
  exact local_convergence_gd_C3 (edgeKernelE_isMarkovOn hpb.nonneg hrow)
    (edgeMeasureE_isInvariant hpb.nonneg hinvpb.nonneg (invariant_of_isInvariant hinvpb))
    (edgeMeasureE_pos hlam) (edgeMeasureE_total hpb.nonneg hrow htot) hlmin0 hlmin ha hC3 hg1
    hg2 hwsup hwmin0 hwmin hB1 hcoer hstep hgam0 hgam hnorm0

end EdgeInstance

/-! ### `Γ₃` for `g = (log x)²`, and `theo:training_speed_full` item 2 at the paper's radius -/

/-- `g''(x) = 2(1 − log x)/x²` for `g = (log x)²`. -/
noncomputable def logSqDeriv2 (x : ℝ) : ℝ := 2 * (1 - Real.log x) / x ^ 2

/-- `g'''(x) = (4 log x − 6)/x³` for `g = (log x)²`. -/
noncomputable def logSqDeriv3 (x : ℝ) : ℝ := (4 * Real.log x - 6) / x ^ 3

theorem hasDerivAt_logSqDeriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt logSqDeriv (logSqDeriv2 y) y := by
  have hn : HasDerivAt (fun x => 2 * Real.log x) (2 * y⁻¹) y :=
    (Real.hasDerivAt_log hy.ne').const_mul 2
  have hq := hn.div (hasDerivAt_id y) hy.ne'
  have hfun : ((fun x => 2 * Real.log x) / id) = logSqDeriv := by
    funext x; simp only [Pi.div_apply, logSqDeriv, id]
  rw [hfun] at hq
  refine hq.congr_deriv ?_
  simp only [logSqDeriv2, id]
  field_simp

theorem hasDerivAt_logSqDeriv2 {y : ℝ} (hy : 0 < y) :
    HasDerivAt logSqDeriv2 (logSqDeriv3 y) y := by
  have hn : HasDerivAt (fun x => 2 * (1 - Real.log x)) (2 * (0 - y⁻¹)) y :=
    ((hasDerivAt_const y (1:ℝ)).sub (Real.hasDerivAt_log hy.ne')).const_mul 2
  have hd : HasDerivAt (fun x : ℝ => x ^ 2) ((2:ℕ) * y ^ (2 - 1)) y := hasDerivAt_pow 2 y
  have hq := hn.div hd (pow_ne_zero 2 hy.ne')
  have hfun : ((fun x => 2 * (1 - Real.log x)) / fun x : ℝ => x ^ 2) = logSqDeriv2 := by
    funext x; simp only [Pi.div_apply, logSqDeriv2]
  rw [hfun] at hq
  refine hq.congr_deriv ?_
  simp only [logSqDeriv3]
  field_simp
  ring

/-- On `(0, ∞)`, the three derivatives of `logSq` are `logSqDeriv`, `logSqDeriv2`, `logSqDeriv3`. -/
theorem deriv_logSq_eq {y : ℝ} (hy : 0 < y) :
    deriv logSq y = logSqDeriv y ∧ deriv (deriv logSq) y = logSqDeriv2 y
      ∧ deriv (deriv (deriv logSq)) y = logSqDeriv3 y := by
  have e1 : deriv logSq =ᶠ[nhds y] logSqDeriv :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hy))
      fun z hz => (hasDerivAt_logSq hz).deriv
  have e2 : deriv (deriv logSq) =ᶠ[nhds y] logSqDeriv2 :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hy)) fun z hz => by
      have e1z : deriv logSq =ᶠ[nhds z] logSqDeriv :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz)
          fun u hu => (hasDerivAt_logSq hu).deriv
      rw [e1z.deriv_eq]
      exact (hasDerivAt_logSqDeriv hz).deriv
  refine ⟨(hasDerivAt_logSq hy).deriv, ?_, ?_⟩
  · rw [e1.deriv_eq]; exact (hasDerivAt_logSqDeriv hy).deriv
  · rw [e2.deriv_eq]; exact (hasDerivAt_logSqDeriv2 hy).deriv

/-- `g = (log x)²` is `C³` (indeed `C^∞`) at every point of `[1/2, 3/2]`. -/
theorem logSq_C3 : ∀ y ∈ Icc (1 - (1/2 : ℝ)) (1 + 1/2), ContDiffAt ℝ 3 logSq y := by
  intro y hy
  have hy0 : y ≠ 0 := by have := hy.1; norm_num at this; linarith
  have hfun : logSq = fun x => Real.log x ^ 2 := rfl
  rw [hfun]
  exact (Real.contDiffAt_log.2 hy0).pow 2

theorem logSq_deriv_one : deriv logSq 1 = 0 := by
  rw [(deriv_logSq_eq one_pos).1]
  simp only [logSqDeriv, Real.log_one, mul_zero, zero_div]

theorem logSq_deriv2_one : deriv (deriv logSq) 1 = 2 := by
  rw [(deriv_logSq_eq one_pos).2.1]
  simp only [logSqDeriv2, Real.log_one, sub_zero, mul_one, one_pow, div_one]

/-- **`theo:training_speed_full` item 2, `Γ₃ = sup_{[1/2,3/2]} |g'''| = 48 + 32 log 2`** for
`g = (log x)²` (`proofs.tex:1013`, the
radius of item 2): `|g'''(x)| = (6 − 4 log x)/x³` is largest at `x = 1/2`. -/
theorem Gamma3_logSq : Gamma3 logSq (1/2) = 48 + 32 * Real.log 2 := by
  have hbound : ∀ y ∈ Icc (1 - (1/2 : ℝ)) (1 + 1/2),
      |deriv (deriv (deriv logSq)) y| ≤ 48 + 32 * Real.log 2 := by
    intro y hy
    have hy1 : (1/2 : ℝ) ≤ y := by have := hy.1; norm_num at this; linarith
    have hy2 : y ≤ 3/2 := by have := hy.2; norm_num at this; linarith
    have hy0 : 0 < y := by linarith
    rw [(deriv_logSq_eq hy0).2.2]
    have hlogup : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
    have hloglow : -Real.log 2 ≤ Real.log y := by
      have := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hy1
      rwa [one_div, Real.log_inv] at this
    have hnum : 0 ≤ 6 - 4 * Real.log y := by linarith
    have hy3 : 0 < y ^ 3 := by positivity
    have hinv3 : 1 / y ^ 3 ≤ 8 := by
      rw [div_le_iff₀ hy3]
      have : (1/2 : ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy1 3
      nlinarith
    rw [logSqDeriv3, abs_div, abs_of_pos hy3, abs_of_nonpos (by linarith)]
    have hstep : -(4 * Real.log y - 6) / y ^ 3 = (6 - 4 * Real.log y) * (1 / y ^ 3) := by ring
    rw [hstep]
    calc (6 - 4 * Real.log y) * (1 / y ^ 3) ≤ (6 + 4 * Real.log 2) * 8 := by
          apply mul_le_mul (by linarith) hinv3 (by positivity)
          have := Real.log_pos (by norm_num : (1:ℝ) < 2)
          linarith
      _ = 48 + 32 * Real.log 2 := by ring
  have hmem : (1/2 : ℝ) ∈ Icc (1 - (1/2 : ℝ)) (1 + 1/2) := ⟨by norm_num, by norm_num⟩
  have hattain : |deriv (deriv (deriv logSq)) (1/2)| = 48 + 32 * Real.log 2 := by
    rw [(deriv_logSq_eq (by norm_num : (0:ℝ) < 1/2)).2.2, logSqDeriv3, one_div, Real.log_inv]
    have hl := Real.log_pos (by norm_num : (1:ℝ) < 2)
    rw [abs_of_nonpos (by
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
    field_simp
    ring
  refine IsGreatest.csSup_eq ⟨⟨1/2, hmem, hattain⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hbound y hy

/-- **`htaylor` for `logSqDeriv` at `a = 1/2`, `g''(1) = 2`, `M₃ = Γ₃ = 48 + 32 log 2`**, derived
from `C³` through `taylor_of_C3`, not from the elementary `LogSqTaylor` bound. -/
theorem logSqDeriv_taylor_Gamma3 (y : ℝ) (hy : |y - 1| ≤ 1/2) :
    |logSqDeriv y - 2 * (y - 1)| ≤ (48 + 32 * Real.log 2) / 2 * (y - 1) ^ 2 := by
  have h := taylor_of_C3 logSq_C3 logSq_deriv_one y hy
  have hy0 : 0 < y := by linarith [(abs_le.mp hy).1]
  rwa [(deriv_logSq_eq hy0).1, logSq_deriv2_one, Gamma3_logSq] at h

/-- **`ε₀` of `theo:training_speed_full` item 2** (`proofs.tex:1013`): Theorem 10's radius for
`g = (log x)²` at `a = 1/2`, `g''(1) = 2`, `Γ₃ = 48 + 32 log 2`. -/
noncomputable def eps0Gamma3 (wmin wsup Bhat lamMin : ℝ) : ℝ :=
  eps0 (epsW (1/2) 2 wmin (Kexp 2 (1/2) (48 + 32 * Real.log 2) wsup) Bhat) (Cinf lamMin)
    (C7 (C6 (Cg 2 (1/2) (48 + 32 * Real.log 2)) wsup) 2 wmin) (rhoL 2 wmin Bhat)
    (C6 (Cg 2 (1/2) (48 + 32 * Real.log 2)) wsup)

/-- `eps0Gamma3` **is** `eps0C3 logSq (1/2)`: item 2's radius is Theorem 10's radius as
`local_convergence_full_C3` computes it from `g = (log x)²`. -/
theorem eps0Gamma3_eq (wmin wsup Bhat lamMin : ℝ) :
    eps0Gamma3 wmin wsup Bhat lamMin = eps0C3 logSq (1/2) wmin wsup Bhat lamMin := by
  simp only [eps0Gamma3, eps0C3, logSq_deriv2_one, Gamma3_logSq]

/-- **The radius is antitone in `M₃`.** -/
theorem eps0_antitone_M3 {g2 a wmin wsup Bhat Ci M M' : ℝ} (hg2 : 0 < g2) (ha : 0 < a)
    (hwmin : 0 < wmin) (hwsup : 0 < wsup) (hB : 0 < Bhat) (hCi : 0 < Ci) (hM : 0 ≤ M)
    (hMM : M ≤ M') :
    eps0 (epsW a g2 wmin (Kexp g2 a M' wsup) Bhat) Ci (C7 (C6 (Cg g2 a M') wsup) g2 wmin)
        (rhoL g2 wmin Bhat) (C6 (Cg g2 a M') wsup)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M wsup) Bhat) Ci (C7 (C6 (Cg g2 a M) wsup) g2 wmin)
        (rhoL g2 wmin Bhat) (C6 (Cg g2 a M) wsup) := by
  have hM' : 0 ≤ M' := le_trans hM hMM
  have hK : 0 < Kexp g2 a M wsup := Kexp_pos hg2 hM ha.le hwsup
  have hKK : Kexp g2 a M wsup ≤ Kexp g2 a M' wsup := by
    simp only [Kexp, C4, C5, Cg]
    have : a * M ≤ a * M' := mul_le_mul_of_nonneg_left hMM ha.le
    nlinarith [mul_le_mul_of_nonneg_left hMM hwsup.le, mul_le_mul_of_nonneg_left this hwsup.le]
  have he1 : eps1 g2 wmin (Kexp g2 a M' wsup) Bhat ≤ eps1 g2 wmin (Kexp g2 a M wsup) Bhat := by
    simp only [eps1]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) hB.le
  have hW : epsW a g2 wmin (Kexp g2 a M' wsup) Bhat ≤ epsW a g2 wmin (Kexp g2 a M wsup) Bhat :=
    min_le_min le_rfl he1
  have hW0 : 0 ≤ epsW a g2 wmin (Kexp g2 a M' wsup) Bhat :=
    epsW_nonneg ha.le hg2.le hwmin.le (Kexp_pos hg2 hM' ha.le hwsup).le hB.le
  have hC6 : C6 (Cg g2 a M) wsup ≤ C6 (Cg g2 a M') wsup := by
    simp only [C6, Cg]
    have : a * M ≤ a * M' := mul_le_mul_of_nonneg_left hMM ha.le
    nlinarith
  have hC6pos : 0 < C6 (Cg g2 a M) wsup := C6_pos hg2 hM ha.le hwsup
  have hC7 : C7 (C6 (Cg g2 a M) wsup) g2 wmin ≤ C7 (C6 (Cg g2 a M') wsup) g2 wmin :=
    div_le_div_of_nonneg_right hC6 (by positivity)
  have hC70 : 0 ≤ C7 (C6 (Cg g2 a M) wsup) g2 wmin := C7_nonneg hC6pos.le (by positivity)
  have hrho : 0 < rhoL g2 wmin Bhat := rhoL_pos (mul_pos hg2 hwmin) hB
  simp only [eps0]
  refine min_le_min (min_le_min ?_ ?_) le_rfl
  · calc epsW a g2 wmin (Kexp g2 a M' wsup) Bhat / (2 * Ci * (2 + C7 (C6 (Cg g2 a M') wsup) g2 wmin))
        ≤ epsW a g2 wmin (Kexp g2 a M' wsup) Bhat
            / (2 * Ci * (2 + C7 (C6 (Cg g2 a M) wsup) g2 wmin)) :=
          div_le_div_of_nonneg_left hW0 (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ ≤ epsW a g2 wmin (Kexp g2 a M wsup) Bhat
            / (2 * Ci * (2 + C7 (C6 (Cg g2 a M) wsup) g2 wmin)) :=
          div_le_div_of_nonneg_right hW (by positivity)
  · exact div_le_div_of_nonneg_left hrho.le (by positivity) (by linarith)

/-- **Item 2's radius is at most the one the strict library assembles at `M₃ = 24`**:
`24 ≤ 48 + 32 log 2`. So the paper's neighbourhood is contained in the Lean's, and
`T₀` at the paper's radius is at least `T₀` at the Lean's. -/
theorem eps0Gamma3_le_eps0Sq {wmin wsup Bhat lamMin : ℝ} (hwmin : 0 < wmin) (hwsup : 0 < wsup)
    (hB : 0 < Bhat) (hlmin0 : 0 < lamMin) :
    eps0Gamma3 wmin wsup Bhat lamMin ≤ eps0Sq wmin wsup Bhat lamMin := by
  have hl := Real.log_pos (by norm_num : (1:ℝ) < 2)
  exact eps0_antitone_M3 (by norm_num) (by norm_num) hwmin hwsup hB (Cinf_pos hlmin0)
    (by norm_num) (by linarith)

theorem eps0Gamma3_pos {lamMin wmin wsup Bhat : ℝ} (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hwsup : 0 < wsup) (hB : 0 < Bhat) :
    0 < eps0Gamma3 wmin wsup Bhat lamMin := by
  have hl := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hG : (0:ℝ) ≤ 48 + 32 * Real.log 2 := by linarith
  exact eps0_pos (epsW_pos (by norm_num) (by norm_num) hwmin
      (Kexp_pos (by norm_num) hG (by norm_num) hwsup) hB)
    (Cinf_pos hlmin0)
    (C7_nonneg (C6_pos (by norm_num) hG (by norm_num) hwsup).le (by positivity))
    (rhoL_pos (by linarith) hB) (C6_pos (by norm_num) hG (by norm_num) hwsup)

/-- **`ε₀ ≤ λ_min^{1/2}/32`** (`proofs.tex:1042`, `:1048`): `ε₀ ≤ a/(16C_∞)` at `a = 1/2`,
`C_∞ = λ_min^{−1/2}`. -/
theorem eps0Gamma3_le_sqrt {lamMin wmin wsup Bhat : ℝ} (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hwsup : 0 < wsup) :
    eps0Gamma3 wmin wsup Bhat lamMin ≤ Real.sqrt lamMin / 32 := by
  have hl := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hG : (0:ℝ) ≤ 48 + 32 * Real.log 2 := by linarith
  have hs : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
  have h := eps0_le_a_div (a := 1/2) (g2 := 2) (wmin := wmin)
    (Kex := Kexp 2 (1/2) (48 + 32 * Real.log 2) wsup) (Bhat := Bhat) (rho := rhoL 2 wmin Bhat)
    (c6 := C6 (Cg 2 (1/2) (48 + 32 * Real.log 2)) wsup)
    (c7 := C7 (C6 (Cg 2 (1/2) (48 + 32 * Real.log 2)) wsup) 2 wmin) (by norm_num)
    (Cinf_pos hlmin0)
    (C7_nonneg (C6_pos (by norm_num) hG (by norm_num) hwsup).le (by positivity))
  have hval : (1/2 : ℝ) / (16 * Cinf lamMin) = Real.sqrt lamMin / 32 := by
    simp only [Cinf]
    field_simp
    ring
  simpa only [eps0Gamma3, hval] using h

section TrainingSpeedGamma3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`theo:training_speed_full`, items 1 and 2, at the paper's radius** (`proofs.tex:999–1035`):
`TrainingSpeed.training_speed_full_of_init` with `ε₀` Theorem 10's radius at
`Γ₃ = sup_{[1/2,3/2]}|g'''| = 48 + 32 log 2` (`eps0Gamma3`, which is `eps0C3 logSq (1/2)` by
`eps0Gamma3_eq`), in place of the radius at `M₃ = 24`. The proof is `training_speed_full`'s,
with Theorem 10 applied at `M₃ = Γ₃` through `logSqDeriv_taylor_Gamma3`, and positivity of the
trajectory discharged as in `training_speed_full_of_init`. -/
theorem training_speed_full_Gamma3 {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
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
              (delta0 (eps0Gamma3 wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam))
                (Graph.meanL2 lam (u 0)) (BhatSigma G uH lam) (Graph.nrmL2 lam (u 0))))),
          Graph.meanL2 lam (u 0) ≤ Graph.meanL2 lam (u t₁)
            ∧ Graph.meanL2 lam (u t₁) ≤ Graph.nrmL2 lam (u 0)
            ∧ Graph.nrmL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)
                ≤ eps0Gamma3 wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam)
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
  obtain ⟨pmin, hpmin0, hpmin1, hpmin⟩ := exists_edgeFloor B.phat
  have hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x :=
    flow_pos_graph (lamMin := Graph.minOver G lam) hpc hpos hl hlmin hlmin0 hpmin0 hpmin1 hpmin
      hwmin hw hu0 hflow
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
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hG : (0:ℝ) ≤ 48 + 32 * Real.log 2 := by linarith
  have heps0 : 0 < eps0Gamma3 wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam) :=
    eps0Gamma3_pos hlmin0 hwmin hwsupp hB
  have heps1 : eps0Gamma3 wmin wsup (BhatSigma G uH lam) (Graph.minOver G lam) ≤ 1/2 :=
    le_trans (eps0Gamma3_le_eps0Sq hwmin hwsupp hB hlmin0)
      (eps0Sq_le_half hlmin0 hlmin htot hwmin hwsupp)
  refine ⟨Graph.BackwardPolicy.lam_eq_visits_div hpc hpos hl hg hhit,
    minOver_lam_eq hpc hpos hl hg hhit,
    global_lojasiewicz_flow' hinv hKnn hp htot hu hlmin hlmin0 hwmin hw hwsup hU0 hflow, ?_⟩
  obtain ⟨t₁, ht₁mem, -, hmono, hm1U, hm1pos, hflow1, -, hrad⟩ :=
    entry_and_rescale hpc hpos hl hhit hu hwmin hw heps0 heps1 hflow
  refine ⟨t₁, ht₁mem, hmono, hm1U, hrad, ?_⟩
  set m₁ : ℝ := Graph.meanL2 lam (u t₁) with hm₁def
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
      (g2 := 2) (a := 1/2) (M3 := 48 + 32 * Real.log 2) (wsup := wsup) (wmin := wmin)
      (Bhat := BhatSigma G uH lam) (lamMin := Graph.minOver G lam)
      ⟨hKnn, fun {x} _ => B.phat_row_sum x⟩ ⟨hnn, hl.inv⟩ hp htot hlmin0 hlmin
      (by norm_num) hG (by norm_num) hwabs hwmin hw hB1
      (hcoer_of_graph hpc hpos hl hhit) (fun y hy => logSqDeriv_taylor_Gamma3 y hy) hflow2
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

end TrainingSpeedGamma3

/-! ### The balance loss of `K₂` on `E` is the DB loss (`prop:db_lift`) -/

section EdgeLoss

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge flow `μ = uλ₂` of a density `u` on `E`, as a measure on `𝒮²`, `0` off `E`. -/
noncomputable def extE (pb : V → V → ℝ) (lam : V → ℝ) (u : EdgeSet pb → ℝ) : V → V → ℝ :=
  fun s s' => if h : 0 < pb s' s then edgeMeasure pb lam s s' * u ⟨(s, s'), h⟩ else 0

omit [Fintype V] [DecidableEq V] in
theorem extE_apply (pb : V → V → ℝ) (lam : V → ℝ) (u : EdgeSet pb → ℝ) (e : EdgeSet pb) :
    extE pb lam u e.1.1 e.1.2 = edgeMeasureE pb lam e * u e := by
  simp only [extE, dif_pos e.2, edgeMeasureE]

/-- **The ratio of `K₂` on `E` is the lifted ratio `d(μK₂)/dμ` on `𝒮²`**, at `μ = uλ₂`. -/
theorem ratio_edgeE_eq {pb : V → V → ℝ} {lam : V → ℝ}
    (u : EdgeSet pb → ℝ) (e : EdgeSet pb) :
    ratio (edgeKernelE pb) (edgeMeasureE pb lam) u e
      = pushEdge pb (extE pb lam u) e.1.1 e.1.2 / extE pb lam u e.1.1 e.1.2 := by
  have hnum : pushMass (edgeKernelE pb) (edgeMeasureE pb lam) u e
      = pushEdge pb (extE pb lam u) e.1.1 e.1.2 := by
    have h := sum_edgeSet_eq (pb := pb)
      (fun p : V × V => extE pb lam u p.1 p.2 * edgeKernel pb p.1 p.2 e.1.1 e.1.2)
      (fun p hp => by simp only [extE, dif_neg hp, zero_mul])
    simp only [pushMass, pushEdge]
    refine (Finset.sum_congr rfl fun x _ => ?_).trans (h.trans (Fintype.sum_prod_type'
      (fun s s' => extE pb lam u s s' * edgeKernel pb s s' e.1.1 e.1.2)))
    rw [extE_apply]
    rfl
  simp only [ratio]
  rw [hnum, extE_apply]

/-- **`theo:local_convergence_full`, DB instance: the loss is the DB loss** (`prop:db_lift` on
`E`): the balance loss of `K₂` on `(E, λ₂)` at `μ = uλ₂`, for any
generator `g` and training weights `ν̂`, is the detailed-balance loss of `(F, π_→^μ)`,
`F = m₁μ`, `π_→^μ` the disintegration — `Lift.db_lift_ratio`, read on `E`. -/
theorem loss_edgeE_eq_db {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hlam : ∀ x, 0 ≤ lam x) {u : EdgeSet pb → ℝ} (hu : ∀ e, 0 ≤ u e)
    (nu : EdgeSet pb → ℝ) (g : ℝ → ℝ) :
    loss (edgeKernelE pb) (edgeMeasureE pb lam) nu u g
      = ∑ e : EdgeSet pb, nu e * g (marg₁ (extE pb lam u) e.1.2 * pb e.1.2 e.1.1
          / (marg₁ (extE pb lam u) e.1.1 * disint (extE pb lam u) e.1.1 e.1.2)) := by
  have hmu : ∀ s s', 0 ≤ extE pb lam u s s' := by
    intro s s'
    simp only [extE]
    split
    · exact mul_nonneg (edgeMeasure_nonneg hnn hlam s s') (hu _)
    · exact le_rfl
  simp only [loss]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [ratio_edgeE_eq, db_lift_ratio hmu]

end EdgeLoss

/-! ### Inhabitation -/

/-- **The `C³` bundle is inhabited by the paper's generator**: `g = (log x)²` at `a = 1/2`. -/
theorem logSq_C3_bundle :
    (∀ y ∈ Icc (1 - (1/2 : ℝ)) (1 + 1/2), ContDiffAt ℝ 3 logSq y)
      ∧ deriv logSq 1 = 0 ∧ 0 < deriv (deriv logSq) 1 :=
  ⟨logSq_C3, logSq_deriv_one, by rw [logSq_deriv2_one]; norm_num⟩

/-- A balanced start is a gradient flow: at `u ≡ 1` the ratio is `1` and `g'(1) = 0`. -/
theorem isGradientFlow_one {V : Type*} [Fintype V] {K : V → V → ℝ} {lam nu : V → ℝ}
    {gd : ℝ → ℝ} (hinv : Invariant K lam) (hlam : ∀ x, 0 < lam x) (hgd : gd 1 = 0) :
    IsGradientFlow K lam nu gd (fun _ _ => 1) := by
  intro t _ x
  have hr : ∀ y, ratio K lam (fun _ => (1:ℝ)) y = 1 :=
    (ratio_eq_one_iff_balanced (fun y => by simpa only [mul_one] using hlam y)).2 (balanced_const hinv 1)
  have h0 : lossGrad K lam nu gd (fun _ => 1) x = 0 := by
    simp only [lossGrad, lossGradDensity, gradDensity, funAct, hr, hgd, zero_mul, mul_zero,
      Finset.sum_const_zero, sub_zero]
  rw [h0, neg_zero]
  exact hasDerivAt_const t (1:ℝ)

section DBWitness

/-- The uniform backward policy on two states. -/
noncomputable def pbU : Fin 2 → Fin 2 → ℝ := fun _ _ => 1/2

/-- Its invariant probability. -/
noncomputable def lamU : Fin 2 → ℝ := fun _ => 1/2

theorem pbU_pos (p : Fin 2 × Fin 2) : 0 < pbU p.2 p.1 := by norm_num [pbU]

theorem sum_edgeSetU (F : EdgeSet pbU → ℝ) :
    ∑ e, F e = F ⟨(0, 0), pbU_pos _⟩ + F ⟨(0, 1), pbU_pos _⟩ + F ⟨(1, 0), pbU_pos _⟩
      + F ⟨(1, 1), pbU_pos _⟩ := by
  rw [← (Equiv.subtypeUnivEquiv pbU_pos).symm.sum_comp, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Equiv.subtypeUnivEquiv_symm_apply]
  ring

theorem pbU_markov : Core.IsMarkovOn lamU pbU :=
  ⟨fun _ _ => by norm_num [pbU], fun _ _ => by simp only [pbU, Fin.sum_univ_two]; norm_num⟩

theorem pbU_invariant : Core.IsInvariant lamU pbU :=
  ⟨fun _ => by norm_num [lamU], fun _ => by simp only [lamU, pbU, Fin.sum_univ_two]; norm_num⟩

/-- **The coercivity hypothesis of the DB instance is inhabited**: for the uniform policy on two
states, `B̂ = 2` is a coercivity constant of `K₂` on `(E, λ₂)` — the value `1 + C`
`lem:lift_coercivity` gives from `C = 1`. -/
theorem coer_edgeU (f : EdgeSet pbU → ℝ) :
    Graph.nrmL2 (edgeMeasureE pbU lamU) (perpL2 (edgeMeasureE pbU lamU) f)
      ≤ 2 * Graph.nrmL2 (edgeMeasureE pbU lamU) (Aop (edgeKernelE pbU) (edgeMeasureE pbU lamU) f) := by
  set a := f ⟨(0, 0), pbU_pos _⟩
  set b := f ⟨(0, 1), pbU_pos _⟩
  set c := f ⟨(1, 0), pbU_pos _⟩
  set d := f ⟨(1, 1), pbU_pos _⟩
  have hlam2 : ∀ e, edgeMeasureE pbU lamU e = 1/4 := fun e => by
    simp only [edgeMeasureE, edgeMeasure, pbU, lamU]; norm_num
  have hmean : Graph.meanL2 (edgeMeasureE pbU lamU) f = (a + b + c + d) / 4 := by
    simp only [Graph.meanL2, hlam2]
    rw [sum_edgeSetU]
    ring
  have hK : ∀ e e' : EdgeSet pbU, edgeKernelE pbU e e' = if e'.1.2 = e.1.1 then 1/2 else 0 :=
    fun e e' => by simp only [edgeKernelE, edgeKernel, pbU]
  have hdens : ∀ e' : EdgeSet pbU, Core.densAct (edgeMeasureE pbU lamU) (edgeKernelE pbU) f e'
      = (f ⟨(e'.1.2, 0), pbU_pos _⟩ + f ⟨(e'.1.2, 1), pbU_pos _⟩) / 2 := by
    intro e'
    simp only [Core.densAct, hlam2, hK]
    rw [sum_edgeSetU]
    rcases e' with ⟨⟨z, w⟩, hzw⟩
    fin_cases w <;>
      simp only [one_div, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.isValue, ↓reduceIte,
        zero_ne_one, one_ne_zero, mul_zero, zero_mul, add_zero, zero_add, div_inv_eq_mul] <;> ring
  have hS1 : Graph.ipL2 (edgeMeasureE pbU lamU) (perpL2 (edgeMeasureE pbU lamU) f)
      (perpL2 (edgeMeasureE pbU lamU) f)
      = ((a - (a+b+c+d)/4)^2 + (b - (a+b+c+d)/4)^2 + (c - (a+b+c+d)/4)^2
          + (d - (a+b+c+d)/4)^2) / 4 := by
    simp only [Graph.ipL2, perpL2, hmean, hlam2]
    rw [sum_edgeSetU]
    ring
  have hS2 : Graph.ipL2 (edgeMeasureE pbU lamU) (Aop (edgeKernelE pbU) (edgeMeasureE pbU lamU) f)
      (Aop (edgeKernelE pbU) (edgeMeasureE pbU lamU) f)
      = (((a+b)/2 - a)^2 + ((c+d)/2 - b)^2 + ((a+b)/2 - c)^2 + ((c+d)/2 - d)^2) / 4 := by
    simp only [Graph.ipL2, Aop, hdens, hlam2]
    rw [sum_edgeSetU]
    ring
  simp only [Graph.nrmL2]
  rw [hS1, hS2]
  have h4 : (2:ℝ) = Real.sqrt 4 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (21 * (b - a) - 15 * (c - a) - 7 * (d - a)),
    sq_nonneg (18 * (c - a) - 7 * (d - a)), sq_nonneg (d - a)]

/-- **The DB bundle, all hypotheses at once, on the two-state uniform policy**: `local_convergence_full_DB`
applies with `g = (log x)²`, `a = 1/2`, `w ≡ 1`, `λ_min = 1/4`, `B̂ = 2`, and the balanced flow
`h ≡ 0`. The flow is the trivial one; a non-trivial flow is not exhibited here. -/
theorem local_convergence_full_DB_witness :
    ∃ cinf : ℝ,
      |cinf - 1 - Graph.meanL2 (edgeMeasureE pbU lamU) (fun _ => 0)|
          ≤ CC3 logSq (1/2) 1 1
              * Graph.nrmL2 (edgeMeasureE pbU lamU) (perpL2 (edgeMeasureE pbU lamU) fun _ => 0) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 (edgeMeasureE pbU lamU) (fun _ => 0 - (cinf - 1))
            ≤ 2 * Real.exp (-(rhoL (deriv (deriv logSq) 1) 1 2 * t / 2))
                * Graph.nrmL2 (edgeMeasureE pbU lamU) (perpL2 (edgeMeasureE pbU lamU) fun _ => 0) := by
  have hlam2 : ∀ e, edgeMeasureE pbU lamU e = 1/4 := fun e => by
    simp only [edgeMeasureE, edgeMeasure, pbU, lamU]; norm_num
  have hpos : ∀ e, 0 < edgeMeasureE pbU lamU e := fun e => by rw [hlam2]; norm_num
  have hinvE := edgeMeasureE_isInvariant pbU_markov.nonneg pbU_invariant.nonneg
    (invariant_of_isInvariant pbU_invariant)
  have hflow0 : IsGradientFlow (edgeKernelE pbU) (edgeMeasureE pbU lamU)
      (fun e => edgeMeasureE pbU lamU e * (fun _ => (1:ℝ)) e) (deriv logSq)
      (fun _ _ => 1) := isGradientFlow_one (invariant_of_isInvariant hinvE) hpos logSq_deriv_one
  have hflow : IsGradientFlow (edgeKernelE pbU) (edgeMeasureE pbU lamU)
      (fun e => edgeMeasureE pbU lamU e * (fun _ => (1:ℝ)) e) (deriv logSq)
      (fun s e => 1 + (fun _ _ => (0:ℝ)) s e) := by
    simpa only [add_zero] using hflow0
  have hB : ∀ e : EdgeSet pbU, (1:ℝ)/4 ≤ edgeMeasureE pbU lamU e := fun e => by rw [hlam2]
  have hnorm0 : Graph.nrmL2 (edgeMeasureE pbU lamU) (fun _ => (0:ℝ))
      ≤ eps0C3 logSq (1/2) 1 1 2 (1/4) := by
    have hz : Graph.nrmL2 (edgeMeasureE pbU lamU) (fun _ => (0:ℝ)) = 0 := by
      simp only [Graph.nrmL2, Graph.ipL2, mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
    rw [hz]
    exact (constC3_bounds (lam := lamU) (w := fun _ : Fin 2 => (1:ℝ))
      (by simp only [lamU, Fin.sum_univ_two]; norm_num) (by norm_num) (by norm_num) logSq_C3
      logSq_C3_bundle.2.2 (fun _ => by norm_num) one_pos (fun _ => le_rfl) (by norm_num)).1.1.le
  exact local_convergence_full_DB (w := fun _ => 1) (h := fun _ _ => 0) pbU_markov pbU_invariant
    (fun _ => by norm_num [lamU]) (by simp only [lamU, Fin.sum_univ_two]; norm_num)
    (by norm_num) hB (by norm_num) logSq_C3 logSq_deriv_one logSq_C3_bundle.2.2
    (fun _ => by norm_num) one_pos (fun _ => le_rfl) (by norm_num) coer_edgeU hflow hnorm0

end DBWitness

end GFNBounds.Balance
