import GFNBounds.Core.Sampling
import GFNBounds.Core.StableBound

/-!
# The quantitative sampling theorem (negative control), on a finite state space

**`theo:negative_control`** — `proofs.tex`, the theorem quoted from `\cite{brunswicEGF}` just
after `theo:sampling_theorem`. Line numbers drift (kb `0036`); the label is the anchor.

> Let `(π⋆_→, f⋆_out)` be a generative flow and let `F_init` and `F_term` initial and terminal
> distributions. Assume that `F_init ≠ 0`, and consider the sample `s_τ` of the generative flow
> Markov chain from `F_init` to `F̂_term` then:
> `TV(s_τ ‖ F̂_term / F̂_term(𝒮)) ≤ δF_init(𝒮) / F̂_term(𝒮)`, with `TV` the total variation.

with, from the paragraph preceding it,

> `F̂_term = F_term + δF_term`, `F̂_init = F_init + δF_init`,
> `δF_term = (F_init + F⋆_in − F⋆_out − F_term)⁺`, `δF_init = (F_init + F⋆_in − F⋆_out − F_term)⁻`,
> `F⋆_in := F⋆_out π⋆_→`.

The paper proves nothing; the ruling of 2026-09-13 (iii) puts the theorem in scope, to be
formalized from its source and not assumed. The source is `brunswicEGF`
(`/home/maxbrain/Dropbox/ErgodicGFN Camera ready/main.tex`, `theo:negative_control` in §4 and its
proof as `theo:negative_control_appendix` in the appendix). **The source's statement is the
paper's, word for word**, so there is no discrepancy to record. The proof below is the source's:

1. `(π⋆, F⋆_out)` is flow-matching from `F̂_init` to `F̂_term` (`matched_flowMatching`), because
   `δF_term − δF_init` is the defect itself.
2. The sampler's kernel depends on `F_term` and not on `F_init`, so the three chains from
   `F_init`, `δF_init` and `F̂_init` to `F̂_term` share it, and the law is linear in the initial
   mass: `F̂_init(𝒮)·law_{F̂} = F_init(𝒮)·law_F + δF_init(𝒮)·law_δ` at every time (`mixture`).
3. The sampling theorem (`Sampling.FlowData.sampling_theorem`) applied to the matched flow gives
   `s_τ(F̂_init) ∼ F̂_term`; hence `F̂_term/F̂_term(𝒮) = α·s_τ + (1 − α)·μ` with
   `α = F_init(𝒮)/F̂_term(𝒮)` and `μ` a probability, and `TV(s_τ ‖ α s_τ + (1−α) μ) ≤ 1 − α`.

The source leaves implicit that `s_τ` exists, i.e. that the chain from `F_init` stops almost
surely although it is **not** flow-matching; step 2 delivers it (clause 2 of `negative_control`),
since the chain from `F_init` is dominated by the one from `F̂_init`.

## What is proved

| | |
|---|---|
| `defect`, `dInit`, `dTerm`, `hatInit`, `hatTerm` | `D := F_init + F⋆_out P⋆ − F⋆_out − F_term`, `δF_init = D⁻`, `δF_term = D⁺`, `F̂_init`, `F̂_term` |
| `sampler F` | the chain "from `F_init` to `F̂_term`", as a `Sampling.FlowData` |
| `matched_flowMatching` | `(π⋆, F⋆_out)` is flow-matching from `F̂_init` to `F̂_term` |
| `mixture` | the law is linear in the initial mass, time by time |
| **`negative_control`** | the theorem: `s_τ` exists, stops a.s., `F̂_term(𝒮) = F_init(𝒮) + δF_init(𝒮)`, and the TV bound |
| `inference`, `eDens` | the downstream instance: inference at `F_term = κ̂ := E⁺`, `E := F_init + F⋆_in − F⋆_out`, with `E`'s density `e` against a background measure `ν` |
| **`negative_control_hNC`** | the instance in exactly the form of the hypotheses `hNC` of `Core.tv_le_two_fmL1`, `Core.stable_bound` and `Core.il_tv_bound`, plus Step 0's `∫ e dν = F_init(𝒮)` (their `hz`/`he1`) |
| `tv_le_two_fmL1_finite` | Step 2 of `theo:RL_CV_bound_full` with `hNC` and `htri` both discharged, on a finite space |
| `Tight.bound_attained` | the bound is attained: `TV = δF_init(𝒮)/F̂_term(𝒮) = 1/2` on a two-state flow |

## Hypothesis checklist

| paper | here |
|---|---|
| `(π⋆_→, f⋆_out)` a generative flow | ✓ `P⋆` stochastic, `F⋆_out ≥ 0` (`Sampling.FlowData.IsGenFlow`) |
| `F_init`, `F_term` initial and terminal distributions | ✓ non-negative (`IsGenFlow`); **no** flow matching assumed, which is the point |
| `F_init ≠ 0` | ✓ `hinit` |
| `F̂_term`, `δF_init` as defined before the theorem | ✓ `hatTerm`, `dInit`, as positive and negative parts of the pointwise defect |
| "the sample `s_τ` of the chain from `F_init` to `F̂_term`" | ✓ `sampler F`, the sampler of `Sampling` with `F_term := F̂_term`; its law is the limit `p` of `P(τ ≤ n, s_τ = ·)` |
| `TV` | ✓ ½-convention of `app:notation`, written out as `(1/2) ∑ |·|` (it is `Graph.CycleDivergence.tvFin`, and `Core.tvD` against counting measure) |
| a Polish state space | ⚠ **narrowed to a finite `V`**; see SCOPE |

## SCOPE (disclosed)

* **Finite state space only**, inheriting `Core/Sampling.lean`'s narrowing: measures are functions
  `V → ℝ` (masses of atoms) and the kernel a stochastic matrix. The general form is
  `Core/SamplingGeneralBounds.lean` (`MFlow.negative_control_general`), with `δF_init`,
  `δF_term` the Jordan parts of the signed defect. The argument (steps 1–3) is linear and
  transfers unchanged; this file is its finite-state counterpart, proved independently.
* **The sampler is modelled by its time-`n` marginals**, as in `Core/Sampling.lean`; "`s_τ` has
  law `p`" is delivered as `P(τ ≤ n, s_τ = y) → p y` with `∑ p = 1` and `P(τ > n) → 0`.
* **`negative_control_hNC` asks every atom of `ν` to be charged** (`hν : ∀ x, 0 < ν.real {x}`), so
  that `e = E/ν` and the sampler's density `p/ν` are defined everywhere. On a finite space this is
  "`ν_B` has full support", which the paper's background measure has on every instance it treats;
  on a `ν_B`-null atom the densities the downstream theorems carry are undefined anyway.
* **Downstream wiring is not done here.** `negative_control_hNC` produces the hypothesis `hNC` of
  `Core.stable_bound`/`Core.il_tv_bound` for the finite instance, and `tv_le_two_fmL1_finite`
  shows it composes (with `htri` from `Core.tvD_triangle`). On the general measurable space `hNC`
  is discharged by `Core/SamplingGeneralBounds.lean` (`inference_negative_control`, used by
  `stable_bound_general` and `il_first_bullet_general`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core.NegativeControl

open Finset Filter Topology MeasureTheory
open GFNBounds.Core.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The virtual initial and terminal flows -/

/-- The flow-matching defect `D := F_init + F⋆_out P⋆ − F⋆_out − F_term`. -/
noncomputable def defect (F : FlowData V) (y : V) : ℝ :=
  F.finit y + ∑ x, F.fout x * F.P x y - F.fout y - F.fterm y

/-- The initial error `δF_init := D⁻`. -/
noncomputable def dInit (F : FlowData V) (y : V) : ℝ := max (-defect F y) 0

/-- The terminal error `δF_term := D⁺`. -/
noncomputable def dTerm (F : FlowData V) (y : V) : ℝ := max (defect F y) 0

/-- The virtual initial flow `F̂_init := F_init + δF_init`. -/
noncomputable def hatInit (F : FlowData V) (y : V) : ℝ := F.finit y + dInit F y

/-- The virtual terminal flow `F̂_term := F_term + δF_term`. -/
noncomputable def hatTerm (F : FlowData V) (y : V) : ℝ := F.fterm y + dTerm F y

/-- The generative flow Markov chain **from `F_init` to `F̂_term`**: the theorem's sampler. -/
noncomputable def sampler (F : FlowData V) : FlowData V :=
  { finit := F.finit, fterm := hatTerm F, fout := F.fout, P := F.P }

/-- The same flow, from `F̂_init` to `F̂_term`: flow-matching (`matched_flowMatching`). -/
noncomputable def matched (F : FlowData V) : FlowData V :=
  { finit := hatInit F, fterm := hatTerm F, fout := F.fout, P := F.P }

/-- The same flow, from `δF_init` to `F̂_term`. -/
noncomputable def errFlow (F : FlowData V) : FlowData V :=
  { finit := dInit F, fterm := hatTerm F, fout := F.fout, P := F.P }

omit [DecidableEq V] in
theorem dInit_nonneg (F : FlowData V) (y : V) : 0 ≤ dInit F y := le_max_right _ _

omit [DecidableEq V] in
theorem dTerm_nonneg (F : FlowData V) (y : V) : 0 ≤ dTerm F y := le_max_right _ _

omit [DecidableEq V] in
theorem defect_eq (F : FlowData V) (y : V) : defect F y = dTerm F y - dInit F y := by
  unfold dTerm dInit
  rcases le_total 0 (defect F y) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

omit [DecidableEq V] in
/-- **Step 1.** `(π⋆, F⋆_out)` is flow-matching from `F̂_init` to `F̂_term`. -/
theorem matched_flowMatching (F : FlowData V) : (matched F).FlowMatching := by
  intro y
  show hatInit F y + ∑ x, F.fout x * F.P x y = hatTerm F y + F.fout y
  have h := defect_eq F y
  unfold defect at h
  unfold hatInit hatTerm
  linarith

omit [DecidableEq V] in
theorem sampler_isGenFlow {F : FlowData V} (hF : F.IsGenFlow) : (sampler F).IsGenFlow where
  finit_nonneg := hF.finit_nonneg
  fterm_nonneg x := add_nonneg (hF.fterm_nonneg x) (dTerm_nonneg F x)
  fout_nonneg := hF.fout_nonneg
  P_nonneg := hF.P_nonneg
  P_row := hF.P_row

omit [DecidableEq V] in
theorem matched_isGenFlow {F : FlowData V} (hF : F.IsGenFlow) : (matched F).IsGenFlow where
  finit_nonneg x := add_nonneg (hF.finit_nonneg x) (dInit_nonneg F x)
  fterm_nonneg x := add_nonneg (hF.fterm_nonneg x) (dTerm_nonneg F x)
  fout_nonneg := hF.fout_nonneg
  P_nonneg := hF.P_nonneg
  P_row := hF.P_row

omit [DecidableEq V] in
theorem errFlow_isGenFlow {F : FlowData V} (hF : F.IsGenFlow) : (errFlow F).IsGenFlow where
  finit_nonneg := dInit_nonneg F
  fterm_nonneg x := add_nonneg (hF.fterm_nonneg x) (dTerm_nonneg F x)
  fout_nonneg := hF.fout_nonneg
  P_nonneg := hF.P_nonneg
  P_row := hF.P_row

omit [DecidableEq V] in
theorem sum_mul_div_sum (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (y : V) :
    (∑ x, f x) * (f y / ∑ x, f x) = f y := by
  rcases (Finset.sum_nonneg fun x _ => hf x).eq_or_lt with h | h
  · have : f y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hf x)).mp h.symm y (Finset.mem_univ y)
    rw [this, zero_div, mul_zero]
  · field_simp

/-! ## Step 2: the law is linear in the initial mass -/

/-- **Step 2.** The three chains share their kernel, and at every time
`F̂_init(𝒮)·law_{F̂} = F_init(𝒮)·law_F + δF_init(𝒮)·law_δ`. -/
theorem mixture {F : FlowData V} (hF : F.IsGenFlow) :
    ∀ (n : ℕ) (z : V × Bool), (∑ x, hatInit F x) * (matched F).law n z
      = (∑ x, F.finit x) * (sampler F).law n z + (∑ x, dInit F x) * (errFlow F).law n z
  | 0, (y, false) => by
    rw [FlowData.law_zero_false, FlowData.law_zero_false, FlowData.law_zero_false]
    show (∑ x, hatInit F x) * (hatInit F y / ∑ x, hatInit F x)
      = (∑ x, F.finit x) * (F.finit y / ∑ x, F.finit x)
        + (∑ x, dInit F x) * (dInit F y / ∑ x, dInit F x)
    rw [sum_mul_div_sum (hatInit F) (fun x => add_nonneg (hF.finit_nonneg x) (dInit_nonneg F x)),
      sum_mul_div_sum F.finit hF.finit_nonneg, sum_mul_div_sum (dInit F) (dInit_nonneg F)]
    rfl
  | 0, (y, true) => by
    simp only [FlowData.law_zero_true, mul_zero, add_zero]
  | n + 1, z => by
    have hK1 : (sampler F).K = (matched F).K := rfl
    have hK2 : (errFlow F).K = (matched F).K := rfl
    rw [FlowData.law_succ, FlowData.law_succ, FlowData.law_succ, hK1, hK2, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have ih := mixture hF n w
    linear_combination (matched F).K w z * ih

/-! ## Generic facts about the sampler's stopped mass -/

omit [DecidableEq V] in
theorem law_true_mono {G : FlowData V} [DecidableEq V] (hG : G.IsGenFlow) (y : V) :
    Monotone fun n => G.law n (y, true) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [FlowData.law_succ_true]
  have := mul_nonneg (FlowData.law_nonneg hG n (y, false)) (FlowData.stop_nonneg hG y)
  linarith

theorem sum_law_true_le_one {G : FlowData V} (hG : G.IsGenFlow) (hZ : 0 < ∑ x, G.finit x)
    (n : ℕ) : ∑ y, G.law n (y, true) ≤ 1 := by
  rw [FlowData.stopped_sum hG hZ n]
  have : 0 ≤ G.tailProb n :=
    Finset.sum_nonneg fun y _ => FlowData.law_nonneg hG n (y, false)
  linarith

theorem law_true_le_one {G : FlowData V} (hG : G.IsGenFlow) (hZ : 0 < ∑ x, G.finit x)
    (n : ℕ) (y : V) : G.law n (y, true) ≤ 1 :=
  (Finset.single_le_sum (f := fun y => G.law n (y, true))
    (fun y _ => FlowData.law_nonneg hG n (y, true)) (Finset.mem_univ y)).trans
    (sum_law_true_le_one hG hZ n)

/-- The mass stopped by time `n`, scaled by the initial mass, never exceeds the initial mass —
including when that mass is `0`. -/
theorem scaled_sum_law_true_le {G : FlowData V} (hG : G.IsGenFlow) (n : ℕ) :
    ∑ y, (∑ x, G.finit x) * G.law n (y, true) ≤ ∑ x, G.finit x := by
  rw [← Finset.mul_sum]
  rcases (Finset.sum_nonneg fun x _ => hG.finit_nonneg x).eq_or_lt with h | h
  · rw [← h, zero_mul]
  · exact mul_le_of_le_one_right h.le (sum_law_true_le_one hG h n)

omit [DecidableEq V] in
theorem sum_pos_of_ne_zero {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) (h : f ≠ 0) : 0 < ∑ x, f x := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
    by_contra hc
    exact h (funext fun x => not_not.mp (not_exists.mp hc x))
  exact Finset.sum_pos' (fun i _ => hf i)
    ⟨x₀, Finset.mem_univ _, (hf x₀).lt_of_ne (Ne.symm hx₀)⟩

/-! ## The theorem -/

/-- **`theo:negative_control`, finite state space.** Let `(P⋆, F⋆_out)` be a generative flow and
`F_init, F_term ≥ 0` with `F_init ≠ 0`, flow matching **not** assumed. The sampler from `F_init`
to `F̂_term` (`sampler F`):

1. has a limit law `p` of `s_τ`: `P(τ ≤ n, s_τ = y) → p y`;
2. stops almost surely: `P(τ > n) → 0`, and `∑ p = 1`;
3. `F̂_term(𝒮) = F_init(𝒮) + δF_init(𝒮)` (the source's `F̂_term(𝒮) ≥ F_init(𝒮) > 0`);
4. `TV(s_τ ‖ F̂_term/F̂_term(𝒮)) ≤ δF_init(𝒮)/F̂_term(𝒮)`, `TV` with the ½-convention. -/
theorem negative_control {F : FlowData V} (hF : F.IsGenFlow) (hinit : F.finit ≠ 0) :
    ∃ p : V → ℝ,
      (∀ y, Tendsto (fun n => (sampler F).law n (y, true)) atTop (𝓝 (p y))) ∧
      Tendsto (sampler F).tailProb atTop (𝓝 0) ∧
      ∑ y, p y = 1 ∧
      ∑ y, hatTerm F y = ∑ y, F.finit y + ∑ y, dInit F y ∧
      (1 / 2) * ∑ y, |p y - hatTerm F y / ∑ x, hatTerm F x|
        ≤ (∑ y, dInit F y) / ∑ y, hatTerm F y := by
  set Z : ℝ := ∑ x, F.finit x with hZdef
  set Zd : ℝ := ∑ x, dInit F x with hZddef
  set T : ℝ := ∑ x, hatTerm F x with hTdef
  have hS := sampler_isGenFlow hF
  have hM := matched_isGenFlow hF
  have hD := errFlow_isGenFlow hF
  have hZ : 0 < Z := sum_pos_of_ne_zero hF.finit_nonneg hinit
  have hZd0 : 0 ≤ Zd := Finset.sum_nonneg fun x _ => dInit_nonneg F x
  have hZ' : ∑ x, hatInit F x = Z + Zd := Finset.sum_add_distrib
  -- Step 1 and the mass identity of the sampling theorem
  have hmass : ∑ x, hatInit F x = T := FlowData.mass_eq hM (matched_flowMatching F)
  have hTZ : T = Z + Zd := hmass.symm.trans hZ'
  have hT : 0 < T := by rw [hTZ]; linarith
  have hterm : (matched F).fterm ≠ 0 := by
    intro h
    have : T = 0 := by
      rw [hTdef]
      exact Finset.sum_eq_zero fun x _ => congrFun h x
    linarith
  obtain ⟨-, -, -, -, -, hlim⟩ :=
    FlowData.sampling_theorem hM hterm (matched_flowMatching F)
  have hlimM : ∀ y, Tendsto (fun n => (matched F).law n (y, true)) atTop
      (𝓝 (hatTerm F y / T)) := hlim
  -- the limit law of the sampler, by monotonicity
  have hZS : 0 < ∑ x, (sampler F).finit x := hZ
  let p : V → ℝ := fun y => ⨆ n, (sampler F).law n (y, true)
  have hp : ∀ y, Tendsto (fun n => (sampler F).law n (y, true)) atTop (𝓝 (p y)) := fun y =>
    tendsto_atTop_ciSup (law_true_mono hS y)
      ⟨1, by rintro _ ⟨n, rfl⟩; exact law_true_le_one hS hZS n y⟩
  -- the error chain's scaled limit
  let q : V → ℝ := fun y => hatTerm F y - Z * p y
  have hq : ∀ y, Tendsto (fun n => Zd * (errFlow F).law n (y, true)) atTop (𝓝 (q y)) := by
    intro y
    have h1 := ((hlimM y).const_mul T).sub ((hp y).const_mul Z)
    have h2 : T * (hatTerm F y / T) - Z * p y = q y := by
      simp only [q]; field_simp
    rw [h2] at h1
    refine h1.congr fun n => ?_
    have := mixture hF n (y, true)
    rw [hmass] at this
    linarith
  have hq0 : ∀ y, 0 ≤ q y := fun y =>
    ge_of_tendsto' (hq y) fun n => mul_nonneg hZd0 (FlowData.law_nonneg hD n (y, true))
  have hsumq : ∑ y, q y ≤ Zd :=
    le_of_tendsto' (tendsto_finsetSum Finset.univ fun y _ => hq y)
      fun n => scaled_sum_law_true_le hD n
  have hsump : ∑ y, p y ≤ 1 :=
    le_of_tendsto' (tendsto_finsetSum Finset.univ fun y _ => hp y)
      fun n => sum_law_true_le_one hS hZS n
  have hq_sum : ∑ y, q y = T - Z * ∑ y, p y := by
    simp only [q, Finset.sum_sub_distrib, ← Finset.mul_sum, hTdef]
  have hp1 : ∑ y, p y = 1 := by
    refine le_antisymm hsump ?_
    have : Z * 1 ≤ Z * ∑ y, p y := by nlinarith
    exact le_of_mul_le_mul_left this hZ
  have hq_sum' : ∑ y, q y = Zd := by rw [hq_sum, hp1, hTZ]; ring
  have hp0 : ∀ y, 0 ≤ p y := fun y =>
    ge_of_tendsto' (hp y) fun n => FlowData.law_nonneg hS n (y, true)
  refine ⟨p, hp, ?_, hp1, hTZ, ?_⟩
  · -- almost-sure stopping
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_finsetSum Finset.univ fun y _ => hp y)
    rw [hp1, sub_self] at h
    exact h.congr fun n => by rw [FlowData.stopped_sum hS hZS n]; ring
  · -- Step 3: the mixture bound
    have hpt : ∀ y, |p y - hatTerm F y / T| ≤ (Zd * p y + q y) / T := by
      intro y
      have e1 : p y - hatTerm F y / T = (Zd * p y - q y) / T := by
        simp only [q]; field_simp; rw [hTZ]; ring
      rw [e1, abs_div, abs_of_pos hT]
      refine div_le_div_of_nonneg_right ?_ hT.le
      have := mul_nonneg hZd0 (hp0 y)
      exact abs_le.mpr ⟨by linarith [hq0 y], by linarith [hq0 y]⟩
    have hsum : ∑ y, |p y - hatTerm F y / T| ≤ 2 * Zd / T := by
      refine (Finset.sum_le_sum fun y _ => hpt y).trans (le_of_eq ?_)
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq_sum']
      ring
    calc (1 / 2) * ∑ y, |p y - hatTerm F y / T| ≤ (1 / 2) * (2 * Zd / T) := by
          gcongr
      _ = Zd / T := by ring

/-! ## The instance the downstream rows consume: inference at `κ̂ := E⁺` -/

/-- `E := F_init + F⋆_in − F⋆_out`, `F⋆_in = F⋆_out P⋆` (`proofs.tex`, `theo:RL_CV_bound_full`,
`theo:IL_CV_bound`). -/
noncomputable def emass (F : FlowData V) (y : V) : ℝ :=
  F.finit y + ∑ x, F.fout x * F.P x y - F.fout y

/-- Inference at `F_term = κ̂ := E⁺`, the sampler of `theo:RL_CV_bound_full` and
`theo:IL_CV_bound`. `F.fterm` is ignored. -/
noncomputable def inference (F : FlowData V) : FlowData V :=
  { finit := F.finit, fterm := fun y => max (emass F y) 0, fout := F.fout, P := F.P }

omit [DecidableEq V] in
theorem inference_dInit (F : FlowData V) (y : V) :
    dInit (inference F) y = max (-emass F y) 0 := by
  unfold dInit defect
  show max (-(F.finit y + ∑ x, F.fout x * F.P x y - F.fout y - max (emass F y) 0)) 0 = _
  have : F.finit y + ∑ x, F.fout x * F.P x y - F.fout y = emass F y := rfl
  rw [this]
  rcases le_total 0 (emass F y) with h | h
  · rw [max_eq_left h, sub_self, neg_zero, max_self, max_eq_right (by linarith)]
  · rw [max_eq_right h, sub_zero]

omit [DecidableEq V] in
theorem inference_hatTerm (F : FlowData V) (y : V) :
    hatTerm (inference F) y = max (emass F y) 0 := by
  unfold hatTerm dTerm defect
  show max (emass F y) 0 + max (F.finit y + ∑ x, F.fout x * F.P x y - F.fout y
    - max (emass F y) 0) 0 = _
  have : F.finit y + ∑ x, F.fout x * F.P x y - F.fout y = emass F y := rfl
  rw [this]
  rcases le_total 0 (emass F y) with h | h
  · rw [max_eq_left h, sub_self, max_self, add_zero]
  · rw [max_eq_right h, sub_zero, max_eq_right h, zero_add]

omit [DecidableEq V] in
/-- The sampler from `F_init` to `F̂_term` **is** inference at `κ̂`: `F̂_term = E⁺`. -/
theorem sampler_inference (F : FlowData V) : sampler (inference F) = inference F := by
  have h : hatTerm (inference F) = fun y => max (emass F y) 0 :=
    funext (inference_hatTerm F)
  simp only [sampler, h]
  rfl

omit [DecidableEq V] in
/-- Step 0 of `theo:RL_CV_bound_full`: `E(𝒮) = F_init(𝒮)`, `P⋆` being stochastic. -/
theorem sum_emass (F : FlowData V) (hP : ∀ x, ∑ y, F.P x y = 1) :
    ∑ y, emass F y = ∑ y, F.finit y := by
  unfold emass
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_comm]
  simp only [← Finset.mul_sum, hP, mul_one]
  ring

section Measure

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The density `e = dE/dν` of `E` against a background measure `ν` charging every atom. -/
noncomputable def eDens (ν : Measure V) (F : FlowData V) (x : V) : ℝ := emass F x / ν.real {x}

omit [DecidableEq V] in
theorem mul_max_div {w : ℝ} (hw : 0 < w) (b : ℝ) : w * max (b / w) 0 = max b 0 := by
  rw [mul_max_of_nonneg _ _ hw.le, mul_div_cancel₀ _ hw.ne', mul_zero]

omit [DecidableEq V] in
theorem integral_posPart_eDens (ν : Measure V) [IsFiniteMeasure ν] (hν : ∀ x, 0 < ν.real {x})
    (F : FlowData V) : ∫ x, max (eDens ν F x) 0 ∂ν = ∑ x, max (emass F x) 0 := by
  rw [integral_fintype Integrable.of_finite]
  exact Finset.sum_congr rfl fun x _ => by rw [smul_eq_mul, eDens, mul_max_div (hν x)]

omit [DecidableEq V] in
theorem integral_negPart_eDens (ν : Measure V) [IsFiniteMeasure ν] (hν : ∀ x, 0 < ν.real {x})
    (F : FlowData V) : ∫ x, max (-eDens ν F x) 0 ∂ν = ∑ x, max (-emass F x) 0 := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_eq_mul, eDens, ← neg_div, mul_max_div (hν x)]

omit [DecidableEq V] in
theorem integral_eDens (ν : Measure V) [IsFiniteMeasure ν] (hν : ∀ x, 0 < ν.real {x})
    (F : FlowData V) : ∫ x, eDens ν F x ∂ν = ∑ x, emass F x := by
  rw [integral_fintype Integrable.of_finite]
  exact Finset.sum_congr rfl fun x _ => by
    rw [smul_eq_mul, eDens, mul_div_cancel₀ _ (hν x).ne']

omit [DecidableEq V] in
theorem tvD_count_form (ν : Measure V) [IsFiniteMeasure ν] (hν : ∀ x, 0 < ν.real {x})
    (F : FlowData V) (p : V → ℝ) (c : ℝ) :
    Core.tvD ν (fun y => p y / ν.real {y}) (fun x => max (eDens ν F x) 0 / c)
      = (1 / 2) * ∑ y, |p y - max (emass F y) 0 / c| := by
  unfold Core.tvD
  rw [integral_fintype Integrable.of_finite]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  have hw := hν y
  simp only [smul_eq_mul, eDens]
  have hm : max (emass F y / ν.real {y}) 0 = max (emass F y) 0 / ν.real {y} := by
    rw [← max_div_div_right hw.le, zero_div]
  rw [hm]
  have : p y / ν.real {y} - max (emass F y) 0 / ν.real {y} / c
      = (p y - max (emass F y) 0 / c) / ν.real {y} := by
    field_simp
  rw [this, abs_div, abs_of_pos hw, mul_div_cancel₀ _ hw.ne']

/-- **`theo:negative_control` in the form the downstream rows consume.** On a finite space with a
background measure `ν` charging every atom, a generative flow `(P⋆, F⋆_out)` and `F_init ≠ 0`,
put `E := F_init + F⋆_in − F⋆_out`, `e := dE/dν` and infer at `F_term = κ̂ := E⁺`. Then the
sampler's `s_τ` has a law `p` (clauses 1–2) with `ν`-density `p/ν`, Step 0 holds (clause 3, the
hypothesis `hz`/`he1` of `Core.stable_bound`/`Core.il_tv_bound`), `κ̂(𝒮) > 0` (clause 4), and

  `tvD ν (p/ν) (e⁺/ẑ) ≤ (∫ e⁻ dν)/ẑ`, `ẑ := ∫ e⁺ dν`,

which is **exactly** the hypothesis `hNC` of `Core.tv_le_two_fmL1`, `Core.stable_bound` (with
`zhat := ẑ`) and, with `δ := ∫ e⁻ dν`, of `Core.il_tv_bound`, at `tvNC := tvD ν (p/ν) (e⁺/ẑ)`. -/
theorem negative_control_hNC (ν : Measure V) [IsFiniteMeasure ν] (hν : ∀ x, 0 < ν.real {x})
    (F : FlowData V) (hfi : ∀ x, 0 ≤ F.finit x) (hfo : ∀ x, 0 ≤ F.fout x)
    (hP0 : ∀ x y, 0 ≤ F.P x y) (hP1 : ∀ x, ∑ y, F.P x y = 1) (hinit : F.finit ≠ 0) :
    ∃ p : V → ℝ,
      (∀ y, Tendsto (fun n => (inference F).law n (y, true)) atTop (𝓝 (p y))) ∧
      ∑ y, p y = 1 ∧
      ∫ x, eDens ν F x ∂ν = ∑ x, F.finit x ∧
      0 < ∫ x, max (eDens ν F x) 0 ∂ν ∧
      Core.tvD ν (fun y => p y / ν.real {y})
          (fun x => max (eDens ν F x) 0 / ∫ x, max (eDens ν F x) 0 ∂ν)
        ≤ (∫ x, max (-eDens ν F x) 0 ∂ν) / ∫ x, max (eDens ν F x) 0 ∂ν := by
  have hI : (inference F).IsGenFlow :=
    { finit_nonneg := hfi, fterm_nonneg := fun _ => le_max_right _ _, fout_nonneg := hfo,
      P_nonneg := hP0, P_row := hP1 }
  obtain ⟨p, hp, -, hp1, hmass, htv⟩ := negative_control hI hinit
  have hT : ∑ y, hatTerm (inference F) y = ∑ y, max (emass F y) 0 :=
    Finset.sum_congr rfl fun y _ => inference_hatTerm F y
  have hdI : ∑ y, dInit (inference F) y = ∑ y, max (-emass F y) 0 :=
    Finset.sum_congr rfl fun y _ => inference_dInit F y
  have hZ : 0 < ∑ x, F.finit x := sum_pos_of_ne_zero hfi hinit
  refine ⟨p, ?_, hp1, ?_, ?_, ?_⟩
  · rw [← sampler_inference F]; exact hp
  · rw [integral_eDens ν hν, sum_emass F hP1]
  · rw [integral_posPart_eDens ν hν, ← hT, hmass]
    have : 0 ≤ ∑ y, dInit (inference F) y := Finset.sum_nonneg fun y _ => dInit_nonneg _ y
    change 0 < ∑ x, F.finit x + _
    linarith
  · rw [integral_posPart_eDens ν hν, integral_negPart_eDens ν hν, tvD_count_form ν hν,
      ← hT, ← hdI]
    have hpt : ∀ y, max (emass F y) 0 = hatTerm (inference F) y := fun y =>
      (inference_hatTerm F y).symm
    simp only [hpt]
    exact htv

/-- **Step 2 of `theo:RL_CV_bound_full` with nothing left external**, on a finite space: the
sampler inferring at `κ̂ = E⁺` satisfies `TV(s_τ ‖ κ/t) ≤ 2‖e − k‖_{L¹(ν)}/t`. `hNC` is
`negative_control_hNC` and `htri` is `Core.tvD_triangle`; everything else is
`Core.tv_le_two_fmL1` as it stands. -/
theorem tv_le_two_fmL1_finite (ν : Measure V) [IsFiniteMeasure ν] (hν : ∀ x, 0 < ν.real {x})
    (F : FlowData V) (hfi : ∀ x, 0 ≤ F.finit x) (hfo : ∀ x, 0 ≤ F.fout x)
    (hP0 : ∀ x y, 0 ≤ F.P x y) (hP1 : ∀ x, ∑ y, F.P x y = 1) (hinit : F.finit ≠ 0)
    {k : V → ℝ} (hk0 : ∀ x, 0 ≤ k x) (ht0 : 0 < ∫ x, k x ∂ν) :
    ∃ p : V → ℝ,
      (∀ y, Tendsto (fun n => (inference F).law n (y, true)) atTop (𝓝 (p y))) ∧
      ∑ y, p y = 1 ∧
      Core.tvD ν (fun y => p y / ν.real {y}) (fun x => k x / ∫ x, k x ∂ν)
        ≤ 2 * (∫ x, |eDens ν F x - k x| ∂ν) / ∫ x, k x ∂ν := by
  obtain ⟨p, hp, hp1, hz, hzh0, hNC⟩ := negative_control_hNC ν hν F hfi hfo hP0 hP1 hinit
  refine ⟨p, hp, hp1, ?_⟩
  have hz0 : 0 < ∫ x, eDens ν F x ∂ν := by rw [hz]; exact sum_pos_of_ne_zero hfi hinit
  exact Core.tv_le_two_fmL1 Integrable.of_finite Integrable.of_finite
    (Filter.Eventually.of_forall hk0) rfl rfl rfl hz0 ht0 hNC
    (Core.tvD_triangle Integrable.of_finite Integrable.of_finite)

end Measure

/-! ## The bound is attained -/

namespace Tight

/-- Two states, no outflow: `F_init = δ_true`, `F_term = δ_false`. The defect is
`δ_true − δ_false`, so `δF_init = δ_false`, `F̂_term = δ_true + δ_false`; the sampler stops at once
in `true`, and `TV(δ_true ‖ ½(δ_true + δ_false)) = ½ = δF_init(𝒮)/F̂_term(𝒮)`. -/
noncomputable def flow : FlowData Bool where
  finit := fun b => if b then 1 else 0
  fterm := fun b => if b then 0 else 1
  fout := fun _ => 0
  P := fun x y => if x = y then 1 else 0

theorem isGenFlow : flow.IsGenFlow where
  finit_nonneg b := by cases b <;> norm_num [flow]
  fterm_nonneg b := by cases b <;> norm_num [flow]
  fout_nonneg _ := le_rfl
  P_nonneg x y := by cases x <;> cases y <;> norm_num [flow]
  P_row x := by cases x <;> simp [flow]

theorem finit_ne : flow.finit ≠ 0 := fun h => by
  have := congrFun h true
  norm_num [flow] at this

theorem hatTerm_eq (b : Bool) : hatTerm flow b = 1 := by
  cases b <;> norm_num [hatTerm, dTerm, defect, flow]

theorem dInit_eq (b : Bool) : dInit flow b = if b then 0 else 1 := by
  cases b <;> norm_num [dInit, defect, flow]

theorem law_succ_false (n : ℕ) (y : Bool) : (sampler flow).law (n + 1) (y, false) = 0 := by
  rw [FlowData.law_succ_false]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [FlowData.cont, sampler, flow]

theorem law_true (n : ℕ) (y : Bool) :
    (sampler flow).law (n + 1) (y, true) = if y then 1 else 0 := by
  induction n with
  | zero =>
    rw [FlowData.law_succ_true, FlowData.law_zero_true, FlowData.law_zero_false]
    cases y <;> simp [FlowData.stop, FlowData.cont, sampler, flow]
  | succ n ih =>
    rw [FlowData.law_succ_true, ih, law_succ_false, zero_mul, add_zero]

/-- **The bound of `theo:negative_control` is attained**: on `flow` the hypotheses hold,
`δF_init(𝒮)/F̂_term(𝒮) = 1/2`, and the TV of the theorem's conclusion equals it. -/
theorem bound_attained :
    ∃ p : Bool → ℝ,
      (∀ y, Tendsto (fun n => (sampler flow).law n (y, true)) atTop (𝓝 (p y))) ∧
      (∑ y, dInit flow y) / (∑ y, hatTerm flow y) = 1 / 2 ∧
      (1 / 2) * ∑ y, |p y - hatTerm flow y / ∑ x, hatTerm flow x| = 1 / 2 := by
  obtain ⟨p, hp, -⟩ := negative_control isGenFlow finit_ne
  have hpv : ∀ y, p y = if y then 1 else 0 := fun y =>
    tendsto_nhds_unique (hp y) (tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact law_true m y)
  refine ⟨p, hp, ?_, ?_⟩
  · simp [dInit_eq, hatTerm_eq]
  · simp [hpv, hatTerm_eq]; norm_num

end Tight

end GFNBounds.Core.NegativeControl
