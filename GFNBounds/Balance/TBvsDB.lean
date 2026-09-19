import GFNBounds.Balance.TBHessian
import GFNBounds.Doubling.PhaseRecurrence
import GFNBounds.Doubling.MainPackaging
import GFNBounds.Doubling.OperatorFiniteSum
import GFNBounds.Doubling.StatExists

/-!
# TB against DB under a frozen backward policy: the step cap, the Fejér modes, the doubling graph

**`rem:tb_vs_db`** — `proofs.tex`, the remark after `prop:tb_hessian` (rewritten 2026-09-14; the
label is the anchor, kb `0036`).

> Proposition `prop:tb_hessian` compares TB and DB under the same frozen backward policy and the
> stationary window measure. Heuristically, one trajectory performs `ℓ` detailed-balance updates at
> once; what is proved is one-sided, `0 ⪯ H_TB ⪯ ℓ(1+2B̂′)H_DB`, so a step cap derived from the norm
> of `H_DB` remains sufficient for TB once divided by `ℓ(1+2B̂′)`, and no TB rate is claimed. On an
> eigenfunction of `Q` with eigenvalue `e^{iθ}` the Rayleigh quotient of `Θ_ℓ` is the Fejér kernel
> `∑_{|m|<ℓ}(1 − |m|/ℓ)e^{imθ}`: it vanishes at `θ = π` for `ℓ` even, equals `1/ℓ` there for `ℓ`
> odd, and tends to `ℓ` as `θ → 0`. On the counter-example graph with the damping
> `π_←(j → 2j) = c/(j+1)`, the condition of morozov2025revisiting and summable mixing fail on
> different sets: backward trajectories have infinite expected length exactly for `1 ≤ c < 2`,
> whereas the state-space mixing sum `B̂` is `+∞` at every `c` for which the loop-closed chain is
> positive recurrent (Theorem `theo:doubling_unbounded`). At `c = 1/4`, where `σ̄ = j̄/(1−c) = 6`
> for a target row of mean `j̄ = 9/2` (Proposition `prop:doubling_length`), the rate of Theorem
> `theo:db_stable_frozen_full` on the truncation at an even `K ≥ K₀` satisfies
> `ϱ_K ≤ g''(1)w_min/(c₈²K) → 0`, with `c₈` and `K₀` the constants of Theorem
> `theo:doubling_main`(5): in the flow-matching instance at every coercivity constant
> `eq:coercivity` of the truncation, `B̂_K = ‖S‖ ≥ c₈√K` being the smallest of them, and the
> mixing sum `∑_n β̂_n` of the truncated state chain, when finite, being one of them
> (Lemma `lem:sigma_mixing`) and at least `B̂_K` (Lemma `lem:doubling_operator`(3)); in the
> detailed-balance instance at the constant `1 + B̂_K` that Lemma `lem:lift_coercivity` supplies.
> Summable `L²`-mixing, which supplies the coercivity hypothesis of these rates, is exactly the
> hypothesis of Theorem `theo:universality_L2` at `p = 2`: heuristically, […] and the
> expected-backward-length condition of morozov2025revisiting is the `L¹` shadow of `B̂ < ∞`.
> Proposition `prop:morozov_rate` replaces `B̂` by the hitting-time constant `B̂_σ` in […].

## What is proved

| | |
|---|---|
| `TBHessian.stepCap` (in `TBHessian.lean`) | **the step cap**: `⟨h,H_DB h⟩ ≤ L‖h‖²` for all `h` gives `⟨h,H_TB h⟩ ≤ ℓ(1+2B̂′)L‖h‖²` |
| `fejer`, **`rayleigh_fejer`** | **the Fejér clause**: on `Q(f+ig) = e^{iθ}(f+ig)`, `⟨f,Θ_ℓf⟩ + ⟨g,Θ_ℓg⟩ = F_ℓ(θ)(‖f‖²+‖g‖²)` |
| **`fejer_pi_even`**, **`fejer_pi_odd`**, **`tendsto_fejer`** | `F_ℓ(π) = 0` for `ℓ` even, `1/ℓ` for `ℓ` odd; `F_ℓ(θ) → ℓ` as `θ → 0` |
| **`sbar_bdd_iff`** | **"infinite expected length exactly for `1 ≤ c < 2`"**: at `s = 1` the truncated expected backward lengths `σ̄⁽ⁿ⁾` are bounded iff `c < 1` |
| **`bhat_infinite_of_posRec`** | **"`B̂ = +∞` at every `c` at which the chain is positive recurrent"** (`s = 1`): positive recurrence forces `c < 1`, an invariant probability exists, and at every one no bounded `S` solves `S(Id − P⋆) = Id − Π` and `∑β̂_n` diverges |
| `CoercConst`, **`isLeast_bhatK`** | **"`B̂_K = ‖S‖` being the smallest"** coercivity constant of the truncation, `eq:coercivity` for the density action `P` (`S` is built on `P⋆ = P†`; the adjoint argument is proved) |
| **`truncation_rate`** | **the truncation clause** at every `0 < c < 1` (`c = 1/4` included): `c₈ > 0`, `K₀ ≥ d` of `theo:doubling_main`(5); a truncation exists at every even `K ≥ K₀`; `c₈√K ≤ B̂_K`; `B̂_K` least coercivity constant; every real bound `B` of the partial sums of `∑β̂_n` has `B̂_K ≤ B` and is a coercivity constant; `g''(1)w_min/C² ≤ g''(1)w_min/(c₈²K)` at every coercivity constant `C` and at `C = 1 + B̂_K`; and `g''(1)w_min/(c₈²K) → 0` |
| **`sigmaBar_six`**, `exists_setting_six` | **`σ̄ = 6` at `c = 1/4`, `j̄ = 9/2`**, and such a `Setting` exists (row uniform on `{1,…,8}`) |

## SCOPE (disclosed)

* **Heuristic and recall sentences are not formalized**: "Heuristically, one trajectory performs
  `ℓ` detailed-balance updates at once", "heuristically, the same ergodicity property …", "the `L¹`
  shadow of `B̂ < ∞`" are marked heuristic by the paper; "is exactly the hypothesis of
  `theo:universality_L2` at `p = 2`" and the closing sentence on `prop:morozov_rate` recall those
  rows' own statements (both closed) and add nothing to certify here.
* **The Fejér kernel is carried in its real form** `1 + 2∑_{m=1}^{ℓ−1}(1 − m/ℓ)cos(mθ)`, which is
  `∑_{|m|<ℓ}(1 − |m|/ℓ)e^{imθ}` with the terms `±m` paired; the complex sum itself is not written.
  A complex eigenfunction `u = f + ig` of `Q` with eigenvalue `e^{iθ}` is carried by its real
  coordinates (`Qf = cos θ f − sin θ g`, `Qg = sin θ f + cos θ g`), and its Rayleigh quotient
  `⟨u,Θ_ℓu⟩_ℂ/‖u‖²_ℂ` by `(⟨f,Θ_ℓf⟩ + ⟨g,Θ_ℓg⟩)/(‖f‖² + ‖g‖²)` — equal because `Θ_ℓ` is real and
  self-adjoint. No complexified `L²` is built.
* **"Infinite expected length"** is `¬ BddAbove (range σ̄⁽ⁿ⁾)` (PhaseRecurrence's convention: `⨆` of
  an unbounded real family is a junk value); **`c < 2`** is the standing range, which a `Setting`
  with `ε = ε_{c,1}` forces (`ε(1) = c/2 < 1`) and `exists_family_setting` inhabits.
* **`B̂ = +∞`** is the convention of `def:doubling_setting`: no bounded `S` with
  `S(Id − P⋆) = Id − Π` (`main_unbounded_two`); `∑β̂_n = +∞` is its `¬ Summable` clause.
* **The rate `ϱ = g''(1)w_min/C²`** of `theo:db_stable_frozen_full` enters as its formula, with
  `g''(1)w_min` a non-negative real `g2w`; the theorem that the linearized descent contracts at that
  rate is that row's own certificate (`WeightedL2.stable_frozen_discrete_mixing`), not repeated.
* **The detailed-balance instance is certified at the constant `1 + B̂_K`, not its supply.** That
  `1 + B̂_K` is a coercivity constant of `K₂` on the truncation's edge lift is
  `lem:lift_coercivity`, which is closed on a `Fintype` with finite-sum norms
  (`LiftFinite.lift_coercivity_finite`); the truncation lives in `Lp ℝ 2 L.mu` over `St`, and **no
  bridge from `Stat S (some K)`'s `L²` to a `Fintype` chain exists in the library**, so that
  instantiation is open. What is certified is the rate bound at `C = 1 + B̂_K`.
* **Odd `K`** (kb `0027`): `truncation_rate`'s per-`L` clauses quantify over `Stat S (some K)`, which
  is empty at odd `K`; the non-vacuous case is even `K`, inhabited by its `Nonempty` clause.
* **The `sorry` list is empty and this file adds nothing to it.**

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `prop:tb_hessian`'s setting (step cap, Fejér) | ✓ as in `TBHessian.lean` |
| an eigenfunction of `Q` with eigenvalue `e^{iθ}` | ✓ `hf`, `hg` (real coordinates, see SCOPE) |
| `ℓ` even / odd, `ℓ ≥ 1` | ✓ `2n` with `1 ≤ n`, `2n+1`; `1 ≤ ℓ` |
| the counter-example graph, damping `c/(j+1)` | ✓ `Setting` with `ε = epsCS c 1` (`s = 1`), `0 < c` |
| "positive recurrent" | ✓ `IsPositiveRecurrent S none` (RecurrenceClass, ruling R8) |
| `c = 1/4`, `j̄ = 9/2` | ✓ `sigmaBar_six`; `truncation_rate` at every `0 < c < 1` |
| even `K ≥ K₀`, `c₈`, `K₀` of `theo:doubling_main`(5) | ✓ `Decay.c8Of`, `Decay.K0Of` (`main_truncation_explicit`) |
| coercivity constant `eq:coercivity` | ✓ `CoercConst`: `C ≥ 0` and `‖f − Πf‖ ≤ C‖(I − P)f‖`, `P = densL2` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance.TBHessian

open Finset

/-! ### The Fejér kernel on the eigenmodes of `Q` -/

section Fejer

/-- **`rem:tb_vs_db`, the Fejér kernel** `∑_{|m|<ℓ}(1 − |m|/ℓ)e^{imθ} = 1 + 2∑_{m=1}^{ℓ−1}(1 − m/ℓ) cos(mθ)`, in
its real form (the terms `±m` paired). -/
noncomputable def fejer (ℓ : ℕ) (θ : ℝ) : ℝ :=
  1 + 2 * ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ) * Real.cos (m * θ)

/-- `∑_{m<k} (−1)^m` is `0` at even `k` and `1` at odd `k`. -/
theorem sum_neg_one_pow (n : ℕ) :
    ∑ m ∈ range (2 * n), (-1 : ℝ) ^ m = 0 ∧ ∑ m ∈ range (2 * n + 1), (-1 : ℝ) ^ m = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      have hA : ∑ m ∈ range (2 * (n + 1)), (-1 : ℝ) ^ m = 0 := by
        rw [h1, Finset.sum_range_succ, ih.2, pow_succ, pow_mul, neg_one_sq, one_pow]; norm_num
      refine ⟨hA, ?_⟩
      rw [Finset.sum_range_succ, hA, pow_mul, neg_one_sq, one_pow]; norm_num

/-- `T(ℓ) := ∑_{m<ℓ}(ℓ − m)(−1)^m` is `n` at `ℓ = 2n` and `n + 1` at `ℓ = 2n + 1`. -/
theorem alt_weighted (n : ℕ) :
    ∑ m ∈ range (2 * n), ((2 * n : ℕ) - (m : ℝ)) * (-1) ^ m = n ∧
      ∑ m ∈ range (2 * n + 1), ((2 * n + 1 : ℕ) - (m : ℝ)) * (-1) ^ m = n + 1 := by
  have step : ∀ k : ℕ, ∑ m ∈ range (k + 1), ((k + 1 : ℕ) - (m : ℝ)) * (-1) ^ m
      = ∑ m ∈ range k, ((k : ℕ) - (m : ℝ)) * (-1) ^ m + ∑ m ∈ range (k + 1), (-1 : ℝ) ^ m := by
    intro k
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun m => (-1 : ℝ) ^ m), ← add_assoc,
      ← Finset.sum_add_distrib]
    push_cast
    congr 1
    · exact Finset.sum_congr rfl fun m _ => by ring
    · ring
  induction n with
  | zero => simp
  | succ n ih =>
      have e1 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      have hA := (sum_neg_one_pow (n + 1))
      rw [e1] at hA
      refine ⟨?_, ?_⟩
      · rw [e1, step, ih.2, hA.1]; push_cast; ring
      · rw [step, e1, step, ih.2, hA.1, hA.2]; push_cast; ring

/-- **`rem:tb_vs_db`, the Fejér kernel at `θ = π`**: `0` for `ℓ` even, `1/ℓ` for `ℓ` odd (`ℓ ≥ 1`). -/
theorem fejer_pi_even (n : ℕ) (hn : 1 ≤ n) : fejer (2 * n) Real.pi = 0 := by
  have hT := (alt_weighted n).1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsplit : ∑ m ∈ range (2 * n), ((2 * n : ℕ) - (m : ℝ)) * (-1) ^ m
      = (2 * n : ℕ) + ∑ m ∈ Finset.Ico 1 (2 * n), ((2 * n : ℕ) - (m : ℝ)) * (-1) ^ m := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]; simp
  unfold fejer
  have hc : ∀ m ∈ Finset.Ico 1 (2 * n), (1 - (m : ℝ) / (2 * n : ℕ)) * Real.cos (m * Real.pi)
      = (((2 * n : ℕ) : ℝ) - m) * (-1) ^ m / (2 * n : ℕ) := by
    intro m _
    rw [Real.cos_nat_mul_pi]; push_cast; field_simp
  rw [Finset.sum_congr rfl hc, ← Finset.sum_div]
  have hs : ∑ m ∈ Finset.Ico 1 (2 * n), (((2 * n : ℕ) : ℝ) - m) * (-1) ^ m = -n := by
    rw [hT] at hsplit; push_cast at hsplit ⊢; linarith
  rw [hs]; push_cast; field_simp; ring

/-- **`rem:tb_vs_db`, the Fejér kernel at `θ = π`, `ℓ` odd**: `F_ℓ(π) = 1/ℓ`. -/
theorem fejer_pi_odd (n : ℕ) : fejer (2 * n + 1) Real.pi = 1 / (2 * n + 1 : ℕ) := by
  have hT := (alt_weighted n).2
  have hsplit : ∑ m ∈ range (2 * n + 1), ((2 * n + 1 : ℕ) - (m : ℝ)) * (-1) ^ m
      = (2 * n + 1 : ℕ) + ∑ m ∈ Finset.Ico 1 (2 * n + 1), ((2 * n + 1 : ℕ) - (m : ℝ)) * (-1) ^ m := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]; simp
  unfold fejer
  have hc : ∀ m ∈ Finset.Ico 1 (2 * n + 1),
      (1 - (m : ℝ) / (2 * n + 1 : ℕ)) * Real.cos (m * Real.pi)
      = (((2 * n + 1 : ℕ) : ℝ) - m) * (-1) ^ m / (2 * n + 1 : ℕ) := by
    intro m _
    rw [Real.cos_nat_mul_pi]
    have : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl hc, ← Finset.sum_div]
  have hs : ∑ m ∈ Finset.Ico 1 (2 * n + 1), (((2 * n + 1 : ℕ) : ℝ) - m) * (-1) ^ m = -n := by
    rw [hT] at hsplit; push_cast at hsplit ⊢; linarith
  rw [hs]
  have : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at this ⊢
  field_simp
  ring

/-- **`fejer ℓ 0 = ℓ`**, the Cesàro weights summed (`cesaro_sum`). -/
theorem fejer_zero {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : fejer ℓ 0 = ℓ := by
  simp only [fejer, mul_zero, Real.cos_zero, mul_one]
  exact cesaro_sum hℓ

theorem continuous_fejer (ℓ : ℕ) : Continuous (fejer ℓ) := by
  unfold fejer
  fun_prop

open Filter Topology in
/-- **`rem:tb_vs_db`, "tends to `ℓ` as `θ → 0`"**. -/
theorem tendsto_fejer {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : Tendsto (fejer ℓ) (𝓝 0) (𝓝 (ℓ : ℝ)) := by
  have := (continuous_fejer ℓ).tendsto 0
  rwa [fejer_zero hℓ] at this

end Fejer

section Eigen

variable {V : Type*} [Fintype V] [DecidableEq V] {pb : V → V → ℝ} {lam : V → ℝ}

theorem funAct_lin {α : Type*} [Fintype α] (K : α → α → ℝ) (a b : ℝ) (f g : α → ℝ) :
    funAct K (fun e => a * f e + b * g e) = fun e => a * funAct K f e + b * funAct K g e := by
  funext e
  simp only [funAct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun x _ => by ring

/-- On `Q(f + ig) = e^{iθ}(f + ig)`, `Q^m(f + ig) = e^{imθ}(f + ig)`, in real coordinates. -/
theorem Q_iterate_rot (θ : ℝ) {f g : EdgeSet pb → ℝ}
    (hf : funAct (edgeKernelE pb) f = fun e => Real.cos θ * f e - Real.sin θ * g e)
    (hg : funAct (edgeKernelE pb) g = fun e => Real.sin θ * f e + Real.cos θ * g e) :
    ∀ m : ℕ, (funAct (edgeKernelE pb))^[m] f = (fun e => Real.cos (m * θ) * f e - Real.sin (m * θ) * g e)
      ∧ (funAct (edgeKernelE pb))^[m] g = (fun e => Real.sin (m * θ) * f e + Real.cos (m * θ) * g e)
  | 0 => by
      refine ⟨funext fun e => ?_, funext fun e => ?_⟩ <;> simp
  | m + 1 => by
      obtain ⟨ih1, ih2⟩ := Q_iterate_rot θ hf hg m
      have e1 : (fun e => Real.cos (m * θ) * f e - Real.sin (m * θ) * g e)
          = fun e => Real.cos (m * θ) * f e + (-Real.sin (m * θ)) * g e := by
        funext e; ring
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply', ih1, e1, funAct_lin, hf, hg]
        funext e
        push_cast
        rw [add_mul, one_mul, Real.cos_add, Real.sin_add]
        ring
      · rw [Function.iterate_succ_apply', ih2, funAct_lin, hf, hg]
        funext e
        push_cast
        rw [add_mul, one_mul, Real.cos_add, Real.sin_add]
        ring

/-- **`rem:tb_vs_db`, the Fejér clause**: on an eigenfunction `u = f + ig` of `Q` with eigenvalue
`e^{iθ}` — written in real coordinates, `Qf = cos θ f − sin θ g`, `Qg = sin θ f + cos θ g` — the
Rayleigh quotient of `Θ_ℓ` is the Fejér kernel:
`⟨u, Θ_ℓ u⟩_ℂ = ⟨f, Θ_ℓ f⟩ + ⟨g, Θ_ℓ g⟩ = F_ℓ(θ)(‖f‖² + ‖g‖²) = F_ℓ(θ)‖u‖²_ℂ`. -/
theorem rayleigh_fejer (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x)
    (hinv : Invariant pb lam) (ℓ : ℕ) (θ : ℝ) {f g : EdgeSet pb → ℝ}
    (hf : funAct (edgeKernelE pb) f = fun e => Real.cos θ * f e - Real.sin θ * g e)
    (hg : funAct (edgeKernelE pb) g = fun e => Real.sin θ * f e + Real.cos θ * g e) :
    Graph.ipL2 (edgeMeasureE pb lam) f (Theta pb lam ℓ f)
        + Graph.ipL2 (edgeMeasureE pb lam) g (Theta pb lam ℓ g)
      = fejer ℓ θ * (Graph.ipL2 (edgeMeasureE pb lam) f f
        + Graph.ipL2 (edgeMeasureE pb lam) g g) := by
  have hQ : ∀ m : ℕ, Graph.ipL2 (edgeMeasureE pb lam) f ((funAct (edgeKernelE pb))^[m] f)
      + Graph.ipL2 (edgeMeasureE pb lam) g ((funAct (edgeKernelE pb))^[m] g)
      = Real.cos (m * θ) * (Graph.ipL2 (edgeMeasureE pb lam) f f
        + Graph.ipL2 (edgeMeasureE pb lam) g g) := by
    intro m
    obtain ⟨h1, h2⟩ := Q_iterate_rot θ hf hg m
    rw [h1, h2]
    simp only [Graph.ipL2, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [ip_Theta, ip_Theta]
  simp only [ip_P_self hnn hlam hinv]
  have hsum : ∀ m ∈ Finset.Ico 1 ℓ,
      (1 - (m : ℝ) / ℓ) * (Graph.ipL2 (edgeMeasureE pb lam) f ((funAct (edgeKernelE pb))^[m] f)
          + Graph.ipL2 (edgeMeasureE pb lam) f ((funAct (edgeKernelE pb))^[m] f))
        + (1 - (m : ℝ) / ℓ) * (Graph.ipL2 (edgeMeasureE pb lam) g ((funAct (edgeKernelE pb))^[m] g)
          + Graph.ipL2 (edgeMeasureE pb lam) g ((funAct (edgeKernelE pb))^[m] g))
      = 2 * ((1 - (m : ℝ) / ℓ) * Real.cos (m * θ)) * (Graph.ipL2 (edgeMeasureE pb lam) f f
        + Graph.ipL2 (edgeMeasureE pb lam) g g) := by
    intro m _
    linear_combination (2 * (1 - (m : ℝ) / ℓ)) * hQ m
  have : Graph.ipL2 (edgeMeasureE pb lam) f f
        + ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ)
          * (Graph.ipL2 (edgeMeasureE pb lam) f ((funAct (edgeKernelE pb))^[m] f)
            + Graph.ipL2 (edgeMeasureE pb lam) f ((funAct (edgeKernelE pb))^[m] f))
      + (Graph.ipL2 (edgeMeasureE pb lam) g g
        + ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ)
          * (Graph.ipL2 (edgeMeasureE pb lam) g ((funAct (edgeKernelE pb))^[m] g)
            + Graph.ipL2 (edgeMeasureE pb lam) g ((funAct (edgeKernelE pb))^[m] g)))
      = (Graph.ipL2 (edgeMeasureE pb lam) f f + Graph.ipL2 (edgeMeasureE pb lam) g g)
        + ∑ m ∈ Finset.Ico 1 ℓ, 2 * ((1 - (m : ℝ) / ℓ) * Real.cos (m * θ))
          * (Graph.ipL2 (edgeMeasureE pb lam) f f + Graph.ipL2 (edgeMeasureE pb lam) g g) := by
    rw [← Finset.sum_congr rfl hsum, Finset.sum_add_distrib]; ring
  rw [this, ← Finset.sum_mul, ← Finset.mul_sum, fejer]
  ring

end Eigen

end GFNBounds.Balance.TBHessian

/-! ### The counter-example graph: where the two conditions fail -/

namespace GFNBounds.Doubling.TBvsDB

open Real MeasureTheory Filter

variable {S : Setting}

/-- **`rem:tb_vs_db`: "backward trajectories have infinite expected length exactly for
`1 ≤ c < 2`"**. At `s = 1` the truncated expectations `σ̄⁽ⁿ⁾` of the backward length are bounded
exactly when `c < 1`; `c < 2` is the standing range, carried by the `Setting`. -/
theorem sbar_bdd_iff {c : ℝ} (hc : 0 < c) (heps : ∀ j, S.eps j = epsCS c 1 j) :
    BddAbove (Set.range (sbar S none)) ↔ c < 1 := by
  have heps' : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1) :=
    fun j _ => by rw [heps j, epsCS_one_apply]
  constructor
  · intro hb
    by_contra hc1
    push Not at hc1
    obtain ⟨B, hB⟩ := hb
    obtain ⟨k, hk, hrk⟩ : ∃ k ∈ Finset.Icc 1 S.d, 0 < S.row k := by
      by_contra hne
      push Not at hne
      have : ∑ j ∈ Finset.Icc 1 S.d, S.row j ≤ 0 := Finset.sum_nonpos hne
      rw [S.row_sum] at this; linarith
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    apply hitLad_unbdd hc1 heps' hk1
    refine ⟨B / S.row k, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [le_div_iff₀ hrk]
    have hle : S.row k * hitLad S n k ≤ sbar S none n := by
      unfold sbar
      exact Finset.single_le_sum (f := fun j => S.row j * hitExp S none n (.lad j))
        (fun j _ => mul_nonneg (S.row_nonneg j) (hitExp_nonneg n _)) hk
    have := hB ⟨n, rfl⟩
    linarith
  · intro hc1
    exact ⟨S.jbar / (1 - c), by rintro _ ⟨n, rfl⟩; exact main_sigmaBar_le hc hc1 heps n⟩

/-- **`rem:tb_vs_db`: "the state-space mixing sum `B̂` is `+∞` at every `c` for which the
loop-closed chain is positive recurrent"** (at `s = 1`): positive recurrence forces `c < 1`, an
invariant probability exists there, and at every one of them no bounded `S` solves
`S(Id − P⋆) = Id − Π` (`B̂ = +∞` by the convention of `def:doubling_setting`) and `∑ β̂_n` diverges
(`theo:doubling_unbounded`, via `main_unbounded_two`). -/
theorem bhat_infinite_of_posRec {c : ℝ} (hc : 0 < c) (heps : ∀ j, S.eps j = epsCS c 1 j)
    (hpr : IsPositiveRecurrent S none) :
    c < 1 ∧ Nonempty (Stat S none) ∧ ∀ L : Stat S none,
      (¬ ∃ Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
        Sop * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2) ∧
      ¬ Summable (L.betaHat (rowOnChain_none S)) := by
  have hc1 : c < 1 := by
    by_contra h
    push Not at h
    have hph := (prop_doubling_phase hc heps).2.2.2 rfl
    exact hph.2.1 h |>.2 (.lad 0) (hpr (.lad 0) trivial)
  refine ⟨hc1, exists_stat_of_family hc hc1 S (funext heps), fun L => ?_⟩
  obtain ⟨h1, -, h3⟩ := main_unbounded_two hc zero_le_one heps L
  exact ⟨h1, h3⟩

/-- `‖g − Πg‖ ≤ ‖g‖`: `Π` is an orthogonal projection. -/
theorem norm_sub_piL2_le {cap : Option ℕ} (L : Stat S cap) (g : Lp ℝ 2 L.mu) :
    ‖g - L.piL2 g‖ ≤ ‖g‖ := by
  have horth : inner ℝ (g - L.piL2 g) (L.piL2 g) = 0 := by
    rw [Stat.piL2_apply, inner_sub_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right, L.inner_oneLp_self, real_inner_comm]
    ring
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [sub_add_cancel] at h
  have h0 : 0 ≤ ‖L.piL2 g‖ * ‖L.piL2 g‖ := mul_self_nonneg _
  have := mul_self_le_mul_self_iff (norm_nonneg (g - L.piL2 g)) (norm_nonneg g) |>.mpr
  nlinarith [norm_nonneg (g - L.piL2 g), norm_nonneg g]

/-- `(AB)† = B†A†`: Mathlib's `ContinuousLinearMap.adjoint_comp`, read through `* = ∘L`. -/
theorem adjoint_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A B : E →L[ℝ] E) :
    ContinuousLinearMap.adjoint (A * B) = ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint A :=
  ContinuousLinearMap.adjoint_comp A B

/-- `1† = 1`: Mathlib's `ContinuousLinearMap.adjoint_id`, read through `1 = id`. -/
theorem adjoint_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    ContinuousLinearMap.adjoint (1 : E →L[ℝ] E) = 1 :=
  ContinuousLinearMap.adjoint_id

/-- The coercivity constants of the truncation, `eq:coercivity` for the density action `P`. -/
def CoercConst {K : ℕ} (L : Stat S (some K)) (hdK : S.d ≤ K) : Set ℝ :=
  {C | 0 ≤ C ∧ ∀ f : Lp ℝ 2 L.mu,
    ‖f - L.piL2 f‖ ≤ C * ‖(1 - L.densL2 (rowOnChain_some hdK)) f‖}

/-- **`rem:tb_vs_db`, `B̂_K = ‖S‖` is the smallest coercivity constant of the truncation** (
"`B̂_K = ‖S‖ ≥ c₈√K` being the smallest of them"). `S` is built on `P⋆ = P†`; its adjoint solves
the same equations for `P`, and taking adjoints is an isometry. -/
theorem isLeast_bhatK {K : ℕ} (L : Stat S (some K)) (hdK : S.d ≤ K) :
    IsLeast (CoercConst L hdK) (L.bhatK hdK) := by
  obtain ⟨h1, h2, h3, h4⟩ := L.diffOpK_resolvent hdK
  set T := ContinuousLinearMap.adjoint (L.diffOpK hdK)
  have hPs : ContinuousLinearMap.adjoint (1 - L.pstarL2 (rowOnChain_some hdK))
      = 1 - L.densL2 (rowOnChain_some hdK) := by
    rw [map_sub, adjoint_one, L.adjoint_pstarL2]
  have hPi : ContinuousLinearMap.adjoint (1 - L.piL2) = 1 - L.piL2 := by
    rw [map_sub, adjoint_one, L.adjoint_piL2]
  -- `T(1 − P) = 1 − Π`, `(1 − P)T = 1 − Π`, `ΠT = 0`
  have hT1 : T * (1 - L.densL2 (rowOnChain_some hdK)) = 1 - L.piL2 := by
    have := congrArg ContinuousLinearMap.adjoint h1
    rwa [adjoint_mul, hPs, hPi] at this
  have hT2 : (1 - L.densL2 (rowOnChain_some hdK)) * T = 1 - L.piL2 := by
    have := congrArg ContinuousLinearMap.adjoint h2
    rwa [adjoint_mul, hPs, hPi] at this
  have hT3 : L.piL2 * T = 0 := by
    have := congrArg ContinuousLinearMap.adjoint h4
    rwa [adjoint_mul, L.adjoint_piL2, map_zero] at this
  have hnT : ‖T‖ = L.bhatK hdK := ContinuousLinearMap.adjoint.norm_map _
  refine ⟨⟨norm_nonneg _, fun f => ?_⟩, fun C hC => ?_⟩
  · have hf : f - L.piL2 f = T ((1 - L.densL2 (rowOnChain_some hdK)) f) := by
      have := congrArg (fun A => A f) hT1
      simpa using this.symm
    rw [hf, ← hnT]
    exact T.le_opNorm _
  · rw [← hnT]
    refine ContinuousLinearMap.opNorm_le_bound _ hC.1 fun g => ?_
    have hPiT : L.piL2 (T g) = 0 := by
      have := congrArg (fun A => A g) hT3; simpa using this
    have hA : (1 - L.densL2 (rowOnChain_some hdK)) (T g) = g - L.piL2 g := by
      have := congrArg (fun A => A g) hT2; simpa using this
    have := hC.2 (T g)
    rw [hPiT, sub_zero, hA] at this
    exact this.trans (mul_le_mul_of_nonneg_left (norm_sub_piL2_le L g) hC.1)

/-- A constant above a coercivity constant is one. -/
theorem coercConst_mono {K : ℕ} (L : Stat S (some K)) (hdK : S.d ≤ K) {C C' : ℝ}
    (hC : C ∈ CoercConst L hdK) (hCC : C ≤ C') : C' ∈ CoercConst L hdK :=
  ⟨hC.1.trans hCC, fun f => (hC.2 f).trans
    (mul_le_mul_of_nonneg_right hCC (norm_nonneg _))⟩

/-- **`rem:tb_vs_db`, the truncation clause.** At `s = 1`, `0 < c < 1`, with `c₈` and `K₀` the
constants of `theo:doubling_main`(5): on the truncation at every `K ≥ K₀` and every invariant
probability `λ^K`, `B̂_K ≥ c₈√K`, `B̂_K` is the smallest coercivity constant, the mixing sum
`∑ β̂_n`, when finite, is one of them and at least `B̂_K`, and the rate
`ϱ = g''(1)w_min/C²` of `theo:db_stable_frozen_full` satisfies `ϱ ≤ g''(1)w_min/(c₈²K)` at every
coercivity constant `C` (flow-matching instance) and at `C = 1 + B̂_K` (detailed-balance
instance). -/
theorem truncation_rate {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (heps : ∀ j, S.eps j = epsCS c 1 j) :
    let c₈ := (Decay.ofC hc0 hc1).c8Of S.d S.jbar
    let K₀ := (Decay.ofC hc0 hc1).K0Of S.d
    0 < c₈ ∧ S.d ≤ K₀ ∧
    (∀ g2w : ℝ, Tendsto (fun K : ℕ => g2w / (c₈ ^ 2 * K)) atTop (nhds 0)) ∧
    (∀ K : ℕ, K₀ ≤ K → Even K → Nonempty (Stat S (some K))) ∧
    ∀ K : ℕ, K₀ ≤ K → ∀ (hdK : S.d ≤ K) (L : Stat S (some K)),
      c₈ * Real.sqrt K ≤ L.bhatK hdK ∧
      IsLeast (CoercConst L hdK) (L.bhatK hdK) ∧
      (∀ B : ℝ, (∀ N, ∑ n ∈ Finset.range N, L.betaHat (rowOnChain_some hdK) n ≤ B) →
        L.bhatK hdK ≤ B ∧ B ∈ CoercConst L hdK) ∧
      ∀ g2w : ℝ, 0 ≤ g2w →
        (∀ C ∈ CoercConst L hdK, g2w / C ^ 2 ≤ g2w / (c₈ ^ 2 * K)) ∧
        g2w / (1 + L.bhatK hdK) ^ 2 ≤ g2w / (c₈ ^ 2 * K) := by
  intro c₈ K₀
  obtain ⟨hex, hK0, hc8, hbound⟩ := main_truncation_explicit hc0 hc1 heps
  refine ⟨hc8, hK0, fun g2w => ?_, fun K hK hev => (hex K hev (hK0.trans hK)).2.2.1,
    fun K hK hdK L => ?_⟩
  · have h := tendsto_const_div_atTop_nhds_zero_nat (g2w / c₈ ^ 2)
    refine h.congr fun K => ?_
    rw [div_div]
  have hb := hbound K hK hdK L
  have hleast := isLeast_bhatK L hdK
  have hKpos : (0 : ℝ) < K := by
    have := S.d_pos; exact_mod_cast (show 0 < K by omega)
  have hlow : 0 < c₈ * Real.sqrt K := mul_pos hc8 (Real.sqrt_pos.mpr hKpos)
  have hsq : c₈ ^ 2 * K = (c₈ * Real.sqrt K) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hKpos.le]
  have hrate : ∀ g2w : ℝ, 0 ≤ g2w → ∀ C, c₈ * Real.sqrt K ≤ C →
      g2w / C ^ 2 ≤ g2w / (c₈ ^ 2 * K) := by
    intro g2w hg C hC
    rw [hsq]
    exact div_le_div_of_nonneg_left hg (by positivity)
      (pow_le_pow_left₀ hlow.le hC 2)
  refine ⟨hb, hleast, fun B hB => ?_, fun g2w hg => ⟨fun C hC => ?_, ?_⟩⟩
  · have hle : L.bhatK hdK ≤ B := L.inverse_sub_piL2_le_sum_betaHat hdK hB
    exact ⟨hle, coercConst_mono L hdK hleast.1 hle⟩
  · exact hrate g2w hg C (hb.trans (hleast.2 hC))
  · exact hrate g2w hg _ (hb.trans (by linarith))

/-- **`rem:tb_vs_db`: `σ̄ = j̄/(1 − c) = 6` at `c = 1/4` and `j̄ = 9/2`.** -/
theorem sigmaBar_six (heps : ∀ j, S.eps j = epsCS (1 / 4) 1 j) (hj : S.jbar = 9 / 2) :
    ⨆ n, sbar S none n = 6 := by
  rw [main_sigmaBar_eq (by norm_num) (by norm_num) heps, hj]
  norm_num

/-- The row uniform on `{1, …, 8}`, of mean `9/2`. -/
noncomputable def row8 : ℕ → ℝ := fun j => if 1 ≤ j ∧ j ≤ 8 then 1 / 8 else 0

/-- **`rem:tb_vs_db`, inhabitation**: a `Setting` with `ε = ε_{1/4,1}` and a target row of mean `9/2` exists, so
`sigmaBar_six` is not vacuous. -/
theorem exists_setting_six :
    ∃ S : Setting, (∀ j, S.eps j = epsCS (1 / 4) 1 j) ∧ S.jbar = 9 / 2 := by
  refine ⟨Setting.ofFamily (1 / 4) 1 (by norm_num) zero_le_one (by norm_num) 8 (by norm_num) row8
    (fun j => by unfold row8; split_ifs <;> norm_num)
    (fun j hj => by unfold row8 at hj; split_ifs at hj with h; exacts [h, absurd rfl hj])
    (by simp [row8, Finset.sum_Icc_succ_top]; norm_num), fun j => rfl, ?_⟩
  simp [Setting.jbar, Setting.ofFamily, row8, Finset.sum_Icc_succ_top]
  norm_num

end GFNBounds.Doubling.TBvsDB
