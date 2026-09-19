import Mathlib

/-!
# The sampling theorem for generative flows, on a measurable space

**`theo:sampling_theorem`** — `proofs.tex`, the theorem cited from `bengio2021flow,
brunswic2024theory` just before `theo:negative_control`. Line numbers drift (kb `0036`); the
label is the anchor.

> Let `F_init`, and `F_term` be unnormalized distributions with `F_term ≠ 0` and let
> `(π⋆_→, F⋆_out)` be a generative flow. If the flow-matching constraint
> `F_init + F⋆_out π⋆_→ = F_term + F⋆_out` is satisfied then `F_init(𝒮) = F_term(𝒮)` and:
> `𝔼(τ) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1`, `s_τ ∼ F_term`.

The sampler, from `brunswic2024theory` and the body of the paper:

> it induces a Markov chain `(s_t)_{t ≥ 1}` defined by `s_1 ∼ F_init` and `s_{t+1} = π⋆_→(s_t)`.
> Define the sampling time `τ ∈ ℕ_{≥1}` […] by `P(τ ≥ 1) = 1` and
> `P(τ = t | τ ≥ t) = dF_term/d(F_term + F⋆_out)(s_t)`. […] sampling `s_τ`.

and `app:notation` reads `x ∼ μ` for an unnormalized `μ` as "the law of `x` is `μ/μ(𝒮)`".

`Core/Sampling.lean` proves the theorem on a finite state space, by an independent finite proof. This file
proves it **on an arbitrary measurable space**, with finite measures `F_init, F_term, F⋆_out`, a
Markov kernel `π⋆` and flow matching as an equality of measures. The proof is the finite one,
which is linear and monotone and carries over unchanged: **the occupation measure of the sampler
is dominated by every non-negative super-solution of `μ = μ₀ + (cont · μ) π⋆`, and
`(F_term + F⋆_out)/F_init(𝒮)` is one.**

## The sampler

* `cont := min(dF⋆_out/dG, 1)`, `stop := 1 − cont`, `G := F_term + F⋆_out`; `G`-a.e. `stop` is
  the paper's `dF_term/dG` (`stop_ae_eq`) and the cap is inactive (`cont_ae_eq`).
* `step μ := (cont · μ) π⋆`; `occ μ₀ n` the unstopped mass at time `n`
  (`occ μ₀ 0 = μ₀`, `occ μ₀ (n+1) = step (occ μ₀ n)`); `stopped μ₀ n := ∑_{k<n} stop · occ μ₀ k`;
  `occupation μ₀ := ∑_n occ μ₀ n`; `termLaw μ₀ := stop · occupation μ₀`.
* **The chain.** `chainKernel` is a Markov kernel on `𝒮 × Bool` — from `(x, false)` to
  `(x, true)` with probability `stop x` and to `(y, false)`, `y ∼ π⋆(x)`, with probability
  `cont x`; `(x, true)` absorbing — and `chainLaw μ₀ n` is the law of `X_n` by Chapman–Kolmogorov.
  `chainLaw_eq` identifies it: `X_n ∼ occ μ₀ n ⊗ δ_false + stopped μ₀ n ⊗ δ_true`, so
  `P(τ > n, s_{n+1} ∈ A) = occ μ₀ n A` (`occ_eq_chainLaw`) and
  `P(τ ≤ n, s_τ ∈ A) = stopped μ₀ n A` (`stopped_eq_chainLaw`).
* The theorem's sampler starts from `init := F_init/F_init(𝒮)`: `tailProb n := P(τ > n)`,
  `expectedTau := ∑_{n ≥ 0} P(τ > n) ∈ [0, ∞]`, `stoppedLaw n := P(τ ≤ n, s_τ ∈ ·)`, and
  `sampleLaw := termLaw init`, its setwise limit (`stopped_tendsto`), the law of `s_τ` on `{τ < ∞}`.

## The proof

1. Flow matching at `𝒮`, `π⋆` Markov: `F_init(𝒮) = F_term(𝒮)` (`mass_eq`).
2. `cont · G = F⋆_out` and `stop · G = F_term` (`withDensity_cont`, `withDensity_stop`), so flow
   matching reads `F_init + step G = G` (`finit_add_step_G`); scaled, `init + step (G/Z) = G/Z`.
3. **Domination** (`partial_le`, `occupation_le`): if `μ₀ + step H ≤ H` then every partial sum of
   `occ μ₀` is `≤ H`, by induction. Hence `𝔼(τ) = occupation(𝒮) ≤ G(𝒮)/Z = F⋆_out(𝒮)/F_init(𝒮) + 1`
   (`expectedTau_le`), and `P(τ > n) → 0`.
4. On masses, `Q(𝒮) = μ₀(𝒮) + ∫ cont dQ` (`occupation_univ`), so a finite occupation stops all
   its mass: `termLaw μ₀ (𝒮) = μ₀(𝒮)` (`termLaw_univ`). With `termLaw init ≤ stop · G/Z = F_term/Z`
   (`termLaw_mono`) and equal total mass `1`, the two measures are equal (`eq_of_le_of_univ`):
   **`s_τ ∼ F_term`** as an equality of measures (`sampleLaw_eq`). The finite file's invariant-gap
   argument is replaced by this mass comparison, which needs no subtraction of measures.

Linearity in the initial mass (`occ_add`, `occupation_smul`, `termLaw_add`, `termLaw_smul`) and the
unnormalised form (`termLaw_eq_fterm`) are what `theo:negative_control` consumes
(`SamplingGeneralBounds.lean`).

## What is proved

| | |
|---|---|
| `MFlow`, `FlowMatching` | the data `(F_init, F_term, F⋆_out, π⋆)` on a measurable space, and `equ:FM_const` as measures |
| `cont`, `stop`, `cont_ae_eq`, `stop_ae_eq` | the stopping rule, `G`-a.e. the paper's `dF_term/d(F_term + F⋆_out)` |
| `chainKernel` (a Markov kernel), `chainLaw`, **`chainLaw_eq`**, `occ_eq_chainLaw`, `stopped_eq_chainLaw` | the sampler as a Markov chain on `𝒮 × Bool` and its time-`n` marginals |
| `partial_le`, `occupation_le`, `occupation_univ`, `termLaw_univ`, `termLaw_mono` | the domination argument |
| `mass_eq` | `F_init(𝒮) = F_term(𝒮)` |
| `expectedTau_le`, `tailProb_tendsto_zero`, `sampleLaw_eq`, `stoppedLaw_tendsto` | the clauses |
| **`sampling_theorem`** | the theorem, all clauses |
| `stopped_add_occ` | `P(τ ≤ n) + P(τ > n) = 1` at every time |
| `Resample.inhabited` | the hypotheses are met on every probability space by a flow with non-zero outflow |

## Hypothesis checklist

| paper | here |
|---|---|
| `F_init`, `F_term` unnormalized distributions | ✓ finite measures `[IsFiniteMeasure]` on any `MeasurableSpace α` |
| `F_term ≠ 0` | ✓ `hterm` |
| `(π⋆_→, F⋆_out)` a generative flow | ✓ `π⋆` a Markov kernel (`[IsMarkovKernel F.P]`), `F⋆_out` a finite measure. The paper's generative flow has `F⋆_out = f⋆_out ν_B` with `f⋆_out ∈ L¹(ν_B)`: any such is a finite measure, so this is the paper's hypothesis with the background measure forgotten (the theorem never uses it) |
| flow matching `F_init + F⋆_out π⋆_→ = F_term + F⋆_out` | ✓ `FlowMatching`, an equality of measures |
| `F_init(𝒮) = F_term(𝒮)` | ✓ clause 1 |
| `𝔼(τ) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1` | ✓ clause 2, in `[0, ∞]` |
| `s_τ ∼ F_term` | ✓ clauses 3–4: `P(τ > n) → 0`, `P(τ ≤ n) → 1`, the law of `s_τ` **equals** `F_term/F_term(𝒮)`, and `P(τ ≤ n, s_τ ∈ A) → F_term(A)/F_term(𝒮)` for every measurable `A` |
| a Polish state space (`app:notation`) | ⚠ weakened: any measurable space; Polish is used nowhere |

## SCOPE (disclosed)

* **The sampler is modelled by its time-`n` marginals, not by a path-space measure**, as in
  `Core/Sampling.lean`. `chainLaw` is the Chapman–Kolmogorov recursion of the explicit Markov
  kernel `chainKernel` on `𝒮 × Bool`, i.e. the law of `X_n` for the chain `Kernel.traj` would
  build; no trajectory measure is constructed. It loses nothing: by absorption `{τ > n}` and
  `{τ ≤ n, s_τ ∈ A}` are events of `X_n` alone, and `𝔼(τ)` is the tail sum `∑_{n ≥ 0} P(τ > n)`,
  its value for a time valued in `ℕ≥1 ∪ {∞}`.
* **"`s_τ ∼ F_term`"** is delivered as the equality `sampleLaw = F_term/F_term(𝒮)`, where
  `sampleLaw` is the setwise limit of `P(τ ≤ n, s_τ ∈ ·)` (`stopped_tendsto`), i.e.
  `P(τ < ∞, s_τ ∈ ·)`; together with `P(τ ≤ n) → 1` it is the law of `s_τ`.
* **The stopping probability off the support of `G = F_term + F⋆_out`.** The paper's `dF_term/dG`
  is defined `G`-a.e. only; here `stop = 1 − min(dF⋆_out/dG, 1)` with Mathlib's `rnDeriv`. The
  sampler never charges a `G`-null set (`occupation_le`: its occupation is `≤ G/Z`), so any other
  version gives the same marginals.
* **The bound is not an equality** and nothing here claims it; `Core/Sampling.lean`'s
  `Parked.strict` is the counterexample.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core.SamplingGeneral

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- The data of `theo:sampling_theorem` on a measurable space: initial and terminal flows
`F_init`, `F_term`, the star outflow `F⋆_out` (measures) and the star forward policy `π⋆`
(a kernel). -/
structure MFlow (α : Type*) [MeasurableSpace α] where
  finit : Measure α
  fterm : Measure α
  fout : Measure α
  P : Kernel α α

namespace MFlow

variable (F : MFlow α)

/-- `G := F_term + F⋆_out`, the measure the stopping rule is a density against. -/
noncomputable def G : Measure α := F.fterm + F.fout

/-- The probability of moving on from `x`: `dF⋆_out/d(F_term + F⋆_out)(x)`, capped at `1` (it is
at most `1` `G`-a.e. anyway, `cont_ae_eq`). -/
noncomputable def cont (x : α) : ℝ≥0∞ := min (F.fout.rnDeriv F.G x) 1

/-- The probability of stopping at `x`, `1 − cont(x)`; `G`-a.e. it is the paper's
`dF_term/d(F_term + F⋆_out)(x)` (`stop_ae_eq`). -/
noncomputable def stop (x : α) : ℝ≥0∞ := 1 - F.cont x

theorem measurable_cont : Measurable F.cont :=
  (Measure.measurable_rnDeriv _ _).min measurable_const

theorem measurable_stop : Measurable F.stop :=
  measurable_const.sub F.measurable_cont

theorem cont_le_one (x : α) : F.cont x ≤ 1 := min_le_right _ _

theorem cont_add_stop (x : α) : F.cont x + F.stop x = 1 :=
  add_tsub_cancel_of_le (F.cont_le_one x)

/-- One step of the unstopped sampler: keep the continuing part of a sub-probability `μ` and
move it by `π⋆`, `μ ↦ (cont · μ) π⋆`. -/
noncomputable def step (μ : Measure α) : Measure α := (μ.withDensity F.cont).bind F.P

/-- The unstopped marginals from an initial measure `μ₀`: `occ μ₀ n (A)` is the mass that has not
stopped by time `n` and stands in `A` (the paper's `P(τ > n, s_{n+1} ∈ A)` when `μ₀` is the
normalised `F_init`). -/
noncomputable def occ (μ₀ : Measure α) : ℕ → Measure α
  | 0 => μ₀
  | n + 1 => F.step (occ μ₀ n)

/-- The mass stopped by time `n`, with its location: `P(τ ≤ n, s_τ ∈ A)`. -/
noncomputable def stopped (μ₀ : Measure α) (n : ℕ) : Measure α :=
  ∑ k ∈ Finset.range n, (F.occ μ₀ k).withDensity F.stop

/-- The total occupation measure `Q = ∑_n occ μ₀ n`. -/
noncomputable def occupation (μ₀ : Measure α) : Measure α := Measure.sum (F.occ μ₀)

/-- The law of the stopped state, `stop · Q`. -/
noncomputable def termLaw (μ₀ : Measure α) : Measure α := (F.occupation μ₀).withDensity F.stop

theorem step_apply (μ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    F.step μ s = ∫⁻ x, F.cont x * F.P x s ∂μ := by
  rw [step, Measure.bind_apply hs (F.P.aemeasurable),
    lintegral_withDensity_eq_lintegral_mul _ F.measurable_cont (F.P.measurable_coe hs)]
  rfl

theorem step_mono {μ μ' : Measure α} (h : μ ≤ μ') : F.step μ ≤ F.step μ' := by
  rw [Measure.le_iff]
  intro s hs
  rw [F.step_apply μ hs, F.step_apply μ' hs]
  exact lintegral_mono' h le_rfl

theorem step_smul (c : ℝ≥0∞) (μ : Measure α) : F.step (c • μ) = c • F.step μ := by
  rw [step, withDensity_smul_measure, Measure.bind_smul, step]

theorem occ_zero (μ₀ : Measure α) : F.occ μ₀ 0 = μ₀ := rfl

theorem occ_succ (μ₀ : Measure α) (n : ℕ) : F.occ μ₀ (n + 1) = F.step (F.occ μ₀ n) := rfl

/-- **Domination by any super-solution.** If `μ₀ + (cont · H) π⋆ ≤ H`, every partial sum of the
unstopped marginals is at most `H`. -/
theorem partial_le {μ₀ H : Measure α} (hH : μ₀ + F.step H ≤ H) :
    ∀ N : ℕ, ∑ k ∈ Finset.range N, F.occ μ₀ k ≤ H
  | 0 => by simp only [Finset.range_zero, Finset.sum_empty]; exact Measure.zero_le _
  | N + 1 => by
    have ih := partial_le hH N
    rw [Measure.le_iff] at hH ⊢
    intro s hs
    rw [Finset.sum_range_succ', Measure.add_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [occ_succ, occ_zero, F.step_apply _ hs]
    rw [← lintegral_finsetSum_measure]
    calc ∫⁻ x, F.cont x * F.P x s ∂(∑ k ∈ Finset.range N, F.occ μ₀ k) + μ₀ s
        ≤ ∫⁻ x, F.cont x * F.P x s ∂H + μ₀ s := by gcongr
      _ = (μ₀ + F.step H) s := by rw [Measure.add_apply, F.step_apply H hs, add_comm]
      _ ≤ H s := hH s hs

theorem occupation_apply (μ₀ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    F.occupation μ₀ s = ∑' n, F.occ μ₀ n s := Measure.sum_apply _ hs

/-- The occupation measure is dominated by any super-solution. -/
theorem occupation_le {μ₀ H : Measure α} (hH : μ₀ + F.step H ≤ H) : F.occupation μ₀ ≤ H := by
  rw [Measure.le_iff]
  intro s hs
  rw [F.occupation_apply μ₀ hs]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have h := F.partial_le hH N
  rw [Measure.le_iff] at h
  have := h s hs
  rwa [Measure.coe_finsetSum, Finset.sum_apply] at this

/-- The occupation recursion read on total masses: `Q(𝒮) = μ₀(𝒮) + ∫ cont dQ`, `π⋆` Markov. -/
theorem occupation_univ [IsMarkovKernel F.P] (μ₀ : Measure α) :
    F.occupation μ₀ Set.univ = μ₀ Set.univ + ∫⁻ x, F.cont x ∂(F.occupation μ₀) := by
  rw [F.occupation_apply μ₀ MeasurableSet.univ, occupation, lintegral_sum_measure,
    tsum_eq_zero_add' ENNReal.summable]
  congr 1
  refine tsum_congr fun n => ?_
  rw [occ_succ, F.step_apply _ MeasurableSet.univ]
  simp only [measure_univ, mul_one]

theorem lintegral_cont_add_stop (μ : Measure α) :
    ∫⁻ x, F.cont x ∂μ + ∫⁻ x, F.stop x ∂μ = μ Set.univ := by
  rw [← lintegral_add_left F.measurable_cont]
  simp only [F.cont_add_stop, lintegral_one]

theorem termLaw_apply (μ₀ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    F.termLaw μ₀ s = ∫⁻ x in s, F.stop x ∂(F.occupation μ₀) :=
  withDensity_apply _ hs

/-- **Termination, on masses**: if the occupation is finite, the stopped mass is the initial
mass. -/
theorem termLaw_univ [IsMarkovKernel F.P] (μ₀ : Measure α)
    (hQ : F.occupation μ₀ Set.univ ≠ ∞) : F.termLaw μ₀ Set.univ = μ₀ Set.univ := by
  rw [F.termLaw_apply μ₀ MeasurableSet.univ, Measure.restrict_univ]
  have h1 := F.occupation_univ μ₀
  have h2 := F.lintegral_cont_add_stop (F.occupation μ₀)
  have hc : ∫⁻ x, F.cont x ∂(F.occupation μ₀) ≠ ∞ := by
    refine ne_top_of_le_ne_top hQ ?_
    rw [← h2]; exact le_self_add
  rw [← h2, add_comm] at h1
  exact (ENNReal.add_left_inj hc).1 h1

theorem termLaw_mono {μ₀ : Measure α} {H : Measure α} (hH : μ₀ + F.step H ≤ H) :
    F.termLaw μ₀ ≤ H.withDensity F.stop := by
  rw [Measure.le_iff]
  intro s hs
  rw [F.termLaw_apply μ₀ hs, withDensity_apply _ hs]
  exact lintegral_mono' (Measure.restrict_mono le_rfl (F.occupation_le hH)) le_rfl

theorem stopped_apply (μ₀ : Measure α) (n : ℕ) {s : Set α} (hs : MeasurableSet s) :
    F.stopped μ₀ n s = ∑ k ∈ Finset.range n, ∫⁻ x in s, F.stop x ∂(F.occ μ₀ k) := by
  rw [stopped, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => withDensity_apply _ hs

/-- `P(τ ≤ n, s_τ ∈ A) → (stop · Q)(A)`, setwise. -/
theorem stopped_tendsto (μ₀ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun n => F.stopped μ₀ n s) atTop (𝓝 (F.termLaw μ₀ s)) := by
  have : F.termLaw μ₀ s = ∑' k, ∫⁻ x in s, F.stop x ∂(F.occ μ₀ k) := by
    rw [termLaw, occupation, withDensity_sum, Measure.sum_apply _ hs]
    exact tsum_congr fun k => withDensity_apply _ hs
  rw [this]
  simp only [F.stopped_apply μ₀ _ hs]
  exact ENNReal.tendsto_nat_tsum _

/-- `P(τ ≤ n) + P(τ > n) = μ₀(𝒮)` at every time. -/
theorem stopped_add_occ [IsMarkovKernel F.P] (μ₀ : Measure α) :
    ∀ n, F.stopped μ₀ n Set.univ + F.occ μ₀ n Set.univ = μ₀ Set.univ
  | 0 => by simp [stopped, occ_zero]
  | n + 1 => by
    rw [← stopped_add_occ μ₀ n, F.stopped_apply μ₀ _ MeasurableSet.univ,
      F.stopped_apply μ₀ _ MeasurableSet.univ, Finset.sum_range_succ, occ_succ,
      F.step_apply _ MeasurableSet.univ]
    simp only [measure_univ, mul_one, Measure.restrict_univ]
    rw [add_assoc, add_comm (∫⁻ x, F.stop x ∂_), F.lintegral_cont_add_stop]

/-- Two measures, one below the other, with the same finite total mass, are equal. Mathlib's
`MeasureTheory.Measure.eq_of_le_of_measure_univ_eq`, which asks finiteness of the smaller measure;
here it follows from that of the larger. -/
theorem eq_of_le_of_univ {μ ν : Measure α} [IsFiniteMeasure ν] (h : μ ≤ ν)
    (hu : μ Set.univ = ν Set.univ) : μ = ν := by
  haveI := isFiniteMeasure_of_le ν h
  exact Measure.eq_of_le_of_measure_univ_eq h hu

/-! ### Flow matching -/

/-- The flow-matching constraint `equ:FM_const`, `F_init + F⋆_out π⋆ = F_term + F⋆_out`, as an
equality of measures. -/
def FlowMatching : Prop := F.finit + F.fout.bind F.P = F.fterm + F.fout

section FM

variable [IsFiniteMeasure F.fterm] [IsFiniteMeasure F.fout]

instance : IsFiniteMeasure F.G := by unfold G; infer_instance

omit [IsFiniteMeasure F.fterm] [IsFiniteMeasure F.fout] in
theorem fout_ac_G : F.fout ≪ F.G :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)

omit [IsFiniteMeasure F.fterm] [IsFiniteMeasure F.fout] in
theorem fterm_ac_G : F.fterm ≪ F.G :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)

/-- `dF_term/dG + dF⋆_out/dG = 1`, `G`-a.e. -/
theorem rnDeriv_sum_ae :
    ∀ᵐ x ∂F.G, F.fterm.rnDeriv F.G x + F.fout.rnDeriv F.G x = 1 := by
  have h1 := Measure.rnDeriv_add F.fterm F.fout F.G
  have h2 := Measure.rnDeriv_self F.G
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← Pi.add_apply, ← hx1]
  exact hx2

/-- `cont = dF⋆_out/d(F_term + F⋆_out)`, `G`-a.e.: the cap at `1` is never active. -/
theorem cont_ae_eq : F.cont =ᵐ[F.G] F.fout.rnDeriv F.G := by
  filter_upwards [F.rnDeriv_sum_ae] with x hx
  refine min_eq_left ?_
  rw [← hx]; exact le_add_self

/-- `stop = dF_term/d(F_term + F⋆_out)`, `G`-a.e.: the paper's stopping probability. -/
theorem stop_ae_eq : F.stop =ᵐ[F.G] F.fterm.rnDeriv F.G := by
  filter_upwards [F.rnDeriv_sum_ae, F.cont_ae_eq,
    Measure.rnDeriv_lt_top F.fout F.G] with x hx hc hlt
  rw [stop, hc]
  exact ENNReal.sub_eq_of_eq_add hlt.ne hx.symm

theorem withDensity_cont : F.G.withDensity F.cont = F.fout := by
  rw [withDensity_congr_ae F.cont_ae_eq, Measure.withDensity_rnDeriv_eq _ _ F.fout_ac_G]

theorem withDensity_stop : F.G.withDensity F.stop = F.fterm := by
  rw [withDensity_congr_ae F.stop_ae_eq, Measure.withDensity_rnDeriv_eq _ _ F.fterm_ac_G]

/-- Flow matching read through the stopping rule: `F_init + (cont · G) π⋆ = G`. -/
theorem finit_add_step_G (hFM : F.FlowMatching) : F.finit + F.step F.G = F.G := by
  rw [step, withDensity_cont]; exact hFM

omit [IsFiniteMeasure F.fterm] in
/-- **Mass conservation**: flow matching forces `F_init(𝒮) = F_term(𝒮)`. -/
theorem mass_eq [IsMarkovKernel F.P] (hFM : F.FlowMatching) :
    F.finit Set.univ = F.fterm Set.univ := by
  have h := congrArg (fun μ : Measure α => μ Set.univ) hFM
  simp only [Measure.add_apply] at h
  rw [Measure.bind_apply MeasurableSet.univ F.P.aemeasurable] at h
  simp only [measure_univ, lintegral_one] at h
  exact (ENNReal.add_left_inj (measure_ne_top F.fout Set.univ)).1 h

end FM

/-! ### The sampler as a Markov chain on `𝒮 × Bool`

The flag records whether the sampler has stopped. From `(x, false)` the chain moves to
`(x, true)` with probability `stop(x)` and to `(y, false)`, `y ∼ π⋆(x)`, with probability
`cont(x)`; `(x, true)` is absorbing. `chainLaw n` is the law of `X_n` by Chapman–Kolmogorov, and
`chainLaw_eq` identifies it with the marginals above: `{τ > n} = 𝒮 × {false}` at time `n`, and
`{τ ≤ n, s_τ ∈ A} = A × {true}`. -/

/-- `x ↦ (x, false)`. -/
def inF (x : α) : α × Bool := (x, false)

/-- `x ↦ (x, true)`. -/
def inT (x : α) : α × Bool := (x, true)

omit [MeasurableSpace α] in
theorem inF_def (x : α) : inF x = (x, false) := rfl

theorem measurable_inF : Measurable (inF : α → α × Bool) :=
  measurable_id.prodMk measurable_const

theorem measurable_inT : Measurable (inT : α → α × Bool) :=
  measurable_id.prodMk measurable_const

/-- The sampler's transition law from `z = (x, b)`. -/
noncomputable def kernelFun (z : α × Bool) : Measure (α × Bool) :=
  if z.2 then Measure.dirac (inT z.1)
  else F.stop z.1 • Measure.dirac (inT z.1) + F.cont z.1 • (F.P z.1).map inF

theorem kernelFun_apply (z : α × Bool) {s : Set (α × Bool)} (hs : MeasurableSet s) :
    F.kernelFun z s = if z.2 then (inT ⁻¹' s).indicator 1 z.1
      else F.stop z.1 * (inT ⁻¹' s).indicator 1 z.1 + F.cont z.1 * F.P z.1 (inF ⁻¹' s) := by
  unfold kernelFun
  split_ifs
  · rw [Measure.dirac_apply' _ hs]; rfl
  · rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
      Measure.map_apply measurable_inF hs, smul_eq_mul, smul_eq_mul]
    rfl

theorem measurable_kernelFun : Measurable F.kernelFun := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [F.kernelFun_apply _ hs]
  have hi : Measurable fun z : α × Bool => (inT ⁻¹' s).indicator (1 : α → ℝ≥0∞) z.1 :=
    (measurable_one.indicator (measurable_inT hs)).comp measurable_fst
  refine Measurable.ite ?_ hi ?_
  · exact measurable_snd (measurableSet_singleton true)
  · exact ((F.measurable_stop.comp measurable_fst).mul hi).add
      ((F.measurable_cont.comp measurable_fst).mul
        ((F.P.measurable_coe (measurable_inF hs)).comp measurable_fst))

/-- The sampler's kernel on `𝒮 × Bool`. -/
noncomputable def chainKernel : Kernel (α × Bool) (α × Bool) :=
  ⟨F.kernelFun, F.measurable_kernelFun⟩

theorem chainKernel_apply (z : α × Bool) : F.chainKernel z = F.kernelFun z := rfl

instance [IsMarkovKernel F.P] : IsMarkovKernel F.chainKernel := by
  refine ⟨fun z => ⟨?_⟩⟩
  rw [chainKernel_apply, F.kernelFun_apply z MeasurableSet.univ]
  simp only [Set.preimage_univ, Set.indicator_univ, Pi.one_apply, measure_univ, mul_one]
  split_ifs
  · rfl
  · rw [add_comm]; exact F.cont_add_stop z.1

/-- The law of the chain at time `n`, from `(s₁, false)`, `s₁ ∼ μ₀`. -/
noncomputable def chainLaw (μ₀ : Measure α) : ℕ → Measure (α × Bool)
  | 0 => μ₀.map inF
  | n + 1 => (chainLaw μ₀ n).bind F.chainKernel

/-- One Chapman–Kolmogorov step on a law split by the flag. -/
theorem bind_split (A B : Measure α) :
    (A.map inF + B.map inT).bind F.chainKernel
      = (F.step A).map inF + (B + A.withDensity F.stop).map inT := by
  ext s hs
  have hK : Measurable fun z => F.chainKernel z s := F.chainKernel.measurable_coe hs
  have hF' := measurable_inF hs
  have hT' := measurable_inT hs
  rw [Measure.bind_apply hs F.chainKernel.aemeasurable, lintegral_add_measure,
    lintegral_map hK measurable_inF, lintegral_map hK measurable_inT, Measure.add_apply,
    Measure.map_apply measurable_inF hs, Measure.map_apply measurable_inT hs, Measure.add_apply,
    F.step_apply A hF', withDensity_apply _ hT']
  simp only [chainKernel_apply, F.kernelFun_apply _ hs, inF, inT, Bool.false_eq_true,
    if_false, if_true]
  have h1 : ∀ x, F.stop x * (inT ⁻¹' s).indicator 1 x = (inT ⁻¹' s).indicator F.stop x := by
    intro x
    by_cases hx : x ∈ inT ⁻¹' s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  simp only [h1]
  rw [lintegral_add_left ((F.measurable_stop).indicator hT'), lintegral_indicator hT',
    lintegral_indicator_one hT']
  ring

/-- **The chain's law is the split of the marginals**: `X_n` has law
`occ μ₀ n ⊗ δ_false + stopped μ₀ n ⊗ δ_true`. -/
theorem chainLaw_eq (μ₀ : Measure α) :
    ∀ n, F.chainLaw μ₀ n = (F.occ μ₀ n).map inF + (F.stopped μ₀ n).map inT
  | 0 => by simp [chainLaw, occ_zero, stopped]
  | n + 1 => by
    rw [chainLaw, chainLaw_eq μ₀ n, bind_split, occ_succ]
    simp only [stopped, Finset.sum_range_succ]

/-- `P(τ > n) = P(X_n ∈ 𝒮 × {false})`. -/
theorem occ_eq_chainLaw (μ₀ : Measure α) (n : ℕ) {s : Set α} (hs : MeasurableSet s) :
    F.occ μ₀ n s = F.chainLaw μ₀ n (s ×ˢ {false}) := by
  have hm : MeasurableSet (s ×ˢ ({false} : Set Bool)) := hs.prod (measurableSet_singleton _)
  rw [F.chainLaw_eq μ₀ n, Measure.add_apply, Measure.map_apply measurable_inF hm,
    Measure.map_apply measurable_inT hm]
  have e1 : inF ⁻¹' (s ×ˢ ({false} : Set Bool)) = s := by ext x; simp [inF]
  have e2 : inT ⁻¹' (s ×ˢ ({false} : Set Bool)) = ∅ := by ext x; simp [inT]
  rw [e1, e2, measure_empty, add_zero]

/-- `P(τ ≤ n, s_τ ∈ A) = P(X_n ∈ A × {true})`. -/
theorem stopped_eq_chainLaw (μ₀ : Measure α) (n : ℕ) {s : Set α} (hs : MeasurableSet s) :
    F.stopped μ₀ n s = F.chainLaw μ₀ n (s ×ˢ {true}) := by
  have hm : MeasurableSet (s ×ˢ ({true} : Set Bool)) := hs.prod (measurableSet_singleton _)
  rw [F.chainLaw_eq μ₀ n, Measure.add_apply, Measure.map_apply measurable_inF hm,
    Measure.map_apply measurable_inT hm]
  have e1 : inF ⁻¹' (s ×ˢ ({true} : Set Bool)) = ∅ := by ext x; simp [inF]
  have e2 : inT ⁻¹' (s ×ˢ ({true} : Set Bool)) = s := by ext x; simp [inT]
  rw [e1, e2, measure_empty, zero_add]

/-! ### Linearity in the initial mass -/

/-- Duplicate of `Core.bind_add_measure`, kept so this file imports Mathlib only. -/
theorem bind_add_measure (μ μ' : Measure α) (κ : Kernel α α) :
    (μ + μ').bind κ = μ.bind κ + μ'.bind κ := by
  ext s hs
  rw [Measure.add_apply, Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable,
    Measure.bind_apply hs κ.aemeasurable, lintegral_add_measure]

theorem step_add (μ μ' : Measure α) : F.step (μ + μ') = F.step μ + F.step μ' := by
  rw [step, withDensity_add_measure, bind_add_measure, step, step]

theorem occ_add (μ μ' : Measure α) : ∀ n, F.occ (μ + μ') n = F.occ μ n + F.occ μ' n
  | 0 => rfl
  | n + 1 => by rw [occ_succ, occ_add μ μ' n, step_add, occ_succ, occ_succ]

theorem occ_smul (c : ℝ≥0∞) (μ : Measure α) : ∀ n, F.occ (c • μ) n = c • F.occ μ n
  | 0 => rfl
  | n + 1 => by rw [occ_succ, occ_smul c μ n, step_smul, occ_succ]

theorem occupation_add (μ μ' : Measure α) :
    F.occupation (μ + μ') = F.occupation μ + F.occupation μ' := by
  ext s hs
  rw [Measure.add_apply, F.occupation_apply _ hs, F.occupation_apply _ hs,
    F.occupation_apply _ hs, ← ENNReal.tsum_add]
  exact tsum_congr fun n => by rw [occ_add, Measure.add_apply]

theorem occupation_smul (c : ℝ≥0∞) (μ : Measure α) :
    F.occupation (c • μ) = c • F.occupation μ := by
  ext s hs
  rw [Measure.smul_apply, F.occupation_apply _ hs, F.occupation_apply _ hs, smul_eq_mul,
    ← ENNReal.tsum_mul_left]
  exact tsum_congr fun n => by rw [occ_smul, Measure.smul_apply, smul_eq_mul]

theorem termLaw_add (μ μ' : Measure α) : F.termLaw (μ + μ') = F.termLaw μ + F.termLaw μ' := by
  rw [termLaw, occupation_add, withDensity_add_measure, termLaw, termLaw]

theorem termLaw_smul (c : ℝ≥0∞) (μ : Measure α) : F.termLaw (c • μ) = c • F.termLaw μ := by
  rw [termLaw, occupation_smul, withDensity_smul_measure, termLaw]

/-- **The unnormalised sampling theorem**: an initial measure `μ₀` flow-matching to `F_term`
(`μ₀ + (cont · G) π⋆ = G`) is carried by the sampler exactly onto `F_term`. -/
theorem termLaw_eq_fterm [IsFiniteMeasure F.fterm] [IsFiniteMeasure F.fout] [IsMarkovKernel F.P]
    {μ₀ : Measure α} (h : μ₀ + F.step F.G = F.G) : F.termLaw μ₀ = F.fterm := by
  have hle : F.termLaw μ₀ ≤ F.fterm := by
    have := F.termLaw_mono (le_of_eq h); rwa [withDensity_stop] at this
  refine eq_of_le_of_univ hle ?_
  have hQ : F.occupation μ₀ Set.univ ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top F.G Set.univ)
      (Measure.le_iff.1 (F.occupation_le (le_of_eq h)) _ MeasurableSet.univ)
  rw [F.termLaw_univ μ₀ hQ]
  have h1 := congrArg (fun μ : Measure α => μ Set.univ) h
  simp only [Measure.add_apply, step, withDensity_cont] at h1
  rw [Measure.bind_apply MeasurableSet.univ F.P.aemeasurable] at h1
  simp only [measure_univ, lintegral_one, G, Measure.add_apply] at h1
  exact (ENNReal.add_left_inj (measure_ne_top F.fout Set.univ)).1 h1

/-! ### The sampler of `theo:sampling_theorem` -/

/-- The sampler's initial law, `s₁ ∼ F_init`, i.e. `F_init/F_init(𝒮)` (`app:notation`). -/
noncomputable def init : Measure α := (F.finit Set.univ)⁻¹ • F.finit

/-- `P(τ > n)`: the mass not yet stopped at time `n` (`P(τ > 0) = 1`, the paper's `τ ≥ 1`). -/
noncomputable def tailProb (n : ℕ) : ℝ≥0∞ := F.occ F.init n Set.univ

/-- `𝔼(τ) = ∑_{n ≥ 0} P(τ > n)`, in `[0, ∞]`. -/
noncomputable def expectedTau : ℝ≥0∞ := ∑' n, F.tailProb n

/-- `P(τ ≤ n, s_τ ∈ ·)`. -/
noncomputable def stoppedLaw (n : ℕ) : Measure α := F.stopped F.init n

/-- The law of `s_τ` on `{τ < ∞}`, the setwise limit of `stoppedLaw` (`stopped_tendsto`). -/
noncomputable def sampleLaw : Measure α := F.termLaw F.init

theorem expectedTau_eq : F.expectedTau = F.occupation F.init Set.univ :=
  (F.occupation_apply _ MeasurableSet.univ).symm

/-- A finite `𝔼(τ)` forces termination: `P(τ > n) → 0`. -/
theorem tailProb_tendsto_zero_of_ne_top (h : F.expectedTau ≠ ∞) :
    Tendsto F.tailProb atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top h

section Theorem

variable [IsFiniteMeasure F.finit] [IsFiniteMeasure F.fterm] [IsFiniteMeasure F.fout]
  [IsMarkovKernel F.P]

omit [IsFiniteMeasure F.finit] [IsMarkovKernel F.P] in
/-- The normalised flow-matching identity: `init + (cont · G/Z) π⋆ = G/Z`. -/
theorem init_add_step (hFM : F.FlowMatching) :
    F.init + F.step ((F.finit Set.univ)⁻¹ • F.G) = (F.finit Set.univ)⁻¹ • F.G := by
  rw [step_smul, init, ← smul_add, F.finit_add_step_G hFM]

omit [IsFiniteMeasure F.finit] [IsFiniteMeasure F.fterm] in
theorem finit_univ_ne_zero (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) :
    F.finit Set.univ ≠ 0 := by
  rw [F.mass_eq hFM]
  exact fun h => hterm (Measure.measure_univ_eq_zero.1 h)

/-- **`𝔼(τ) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1`.** -/
theorem expectedTau_le (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) :
    F.expectedTau ≤ F.fout Set.univ / F.finit Set.univ + 1 := by
  have hZ := F.finit_univ_ne_zero hterm hFM
  have hZt : F.finit Set.univ ≠ ∞ := measure_ne_top _ _
  rw [expectedTau_eq]
  refine (Measure.le_iff.1 (F.occupation_le (le_of_eq (F.init_add_step hFM)))
    Set.univ MeasurableSet.univ).trans (le_of_eq ?_)
  rw [Measure.smul_apply, smul_eq_mul, G, Measure.add_apply, ← F.mass_eq hFM, mul_add,
    ENNReal.inv_mul_cancel hZ hZt, div_eq_mul_inv, mul_comm, add_comm]

theorem expectedTau_ne_top (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) :
    F.expectedTau ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (measure_ne_top _ _)
    (F.finit_univ_ne_zero hterm hFM), ENNReal.one_ne_top⟩) (F.expectedTau_le hterm hFM)

/-- **Termination**: `P(τ > n) → 0`. -/
theorem tailProb_tendsto_zero (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) :
    Tendsto F.tailProb atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top (F.expectedTau_ne_top hterm hFM)

omit [IsFiniteMeasure F.fterm] in
theorem init_univ (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) : F.init Set.univ = 1 := by
  rw [init, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (F.finit_univ_ne_zero hterm hFM) (measure_ne_top _ _)

/-- **`s_τ ∼ F_term`**: the law of the stopped state is `F_term/F_term(𝒮)`, as measures. -/
theorem sampleLaw_eq (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) :
    F.sampleLaw = (F.fterm Set.univ)⁻¹ • F.fterm := by
  have hZ := F.finit_univ_ne_zero hterm hFM
  have hmass := F.mass_eq hFM
  have hZ' : F.fterm Set.univ ≠ 0 := hmass ▸ hZ
  haveI : IsFiniteMeasure ((F.fterm Set.univ)⁻¹ • F.fterm) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hZ'))
          (measure_lt_top _ _)⟩
  have hle : F.sampleLaw ≤ (F.fterm Set.univ)⁻¹ • F.fterm := by
    have h := F.termLaw_mono (le_of_eq (F.init_add_step hFM))
    rwa [withDensity_smul_measure, withDensity_stop, hmass] at h
  refine eq_of_le_of_univ hle ?_
  have hQ : F.occupation F.init Set.univ ≠ ∞ := by
    rw [← expectedTau_eq]; exact F.expectedTau_ne_top hterm hFM
  rw [sampleLaw, F.termLaw_univ _ hQ, F.init_univ hterm hFM, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel hZ' (measure_ne_top _ _)]

/-- `P(τ ≤ n, s_τ ∈ A) → F_term(A)/F_term(𝒮)` for every measurable `A`. -/
theorem stoppedLaw_tendsto (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) {s : Set α}
    (hs : MeasurableSet s) :
    Tendsto (fun n => F.stoppedLaw n s) atTop (𝓝 (F.fterm s / F.fterm Set.univ)) := by
  have h := F.stopped_tendsto F.init hs
  rw [← sampleLaw, F.sampleLaw_eq hterm hFM, Measure.smul_apply, smul_eq_mul, mul_comm,
    ← div_eq_mul_inv] at h
  exact h

/-- **`theo:sampling_theorem`, on a measurable space.** Let `F_init, F_term, F⋆_out` be finite
measures with `F_term ≠ 0` and `π⋆` a Markov kernel. If `F_init + F⋆_out π⋆ = F_term + F⋆_out`,
then

1. `F_init(𝒮) = F_term(𝒮)`;
2. `𝔼(τ) = ∑_{n ≥ 0} P(τ > n) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1`;
3. the sampler terminates: `P(τ > n) → 0`, and `P(τ ≤ n) → 1`;
4. `s_τ ∼ F_term`: the law of the stopped state is `F_term/F_term(𝒮)`, and
   `P(τ ≤ n, s_τ ∈ A) → F_term(A)/F_term(𝒮)` for every measurable `A`. -/
theorem sampling_theorem (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) :
    F.finit Set.univ = F.fterm Set.univ ∧
    F.expectedTau ≤ F.fout Set.univ / F.finit Set.univ + 1 ∧
    Tendsto F.tailProb atTop (𝓝 0) ∧
    Tendsto (fun n => F.stoppedLaw n Set.univ) atTop (𝓝 1) ∧
    F.sampleLaw = (F.fterm Set.univ)⁻¹ • F.fterm ∧
    ∀ s, MeasurableSet s →
      Tendsto (fun n => F.stoppedLaw n s) atTop (𝓝 (F.fterm s / F.fterm Set.univ)) := by
  have hZ' : F.fterm Set.univ ≠ 0 := fun h => hterm (Measure.measure_univ_eq_zero.1 h)
  refine ⟨F.mass_eq hFM, F.expectedTau_le hterm hFM, F.tailProb_tendsto_zero hterm hFM, ?_,
    F.sampleLaw_eq hterm hFM, fun s hs => F.stoppedLaw_tendsto hterm hFM hs⟩
  have h := F.stoppedLaw_tendsto hterm hFM MeasurableSet.univ
  rwa [ENNReal.div_self hZ' (measure_ne_top _ _)] at h

end Theorem

end MFlow

/-! ### Inhabitation (kb `0025`) -/

namespace Resample

variable (μ : Measure α) [IsProbabilityMeasure μ] (c : NNReal)

/-- On any probability space: `F_init = F_term = μ`, outflow `c μ`, and the i.i.d. resampling
policy `π⋆(x) = μ`. -/
noncomputable def flow : MFlow α where
  finit := μ
  fterm := μ
  fout := c • μ
  P := Kernel.const α μ

theorem flowMatching : (flow μ c).FlowMatching := by
  unfold MFlow.FlowMatching flow
  dsimp only
  rw [Measure.bind_smul]
  have : μ.bind (Kernel.const α μ) = μ := by
    change μ.bind (fun _ => μ) = μ
    rw [Measure.bind_const, measure_univ, one_smul]
  rw [this]

theorem fterm_ne_zero : (flow μ c).fterm ≠ 0 := IsProbabilityMeasure.ne_zero μ

instance : IsFiniteMeasure (flow μ c).finit := by unfold flow; infer_instance
instance : IsFiniteMeasure (flow μ c).fterm := by unfold flow; infer_instance
instance : IsFiniteMeasure (flow μ c).fout := by unfold flow; infer_instance
instance : IsMarkovKernel (flow μ c).P := by unfold flow; infer_instance

/-- **`sampling_theorem` is inhabited on every probability space**, by a flow with non-zero
outflow when `c ≠ 0`. -/
theorem inhabited :
    (flow μ c).finit Set.univ = (flow μ c).fterm Set.univ ∧
    (flow μ c).expectedTau ≤ (flow μ c).fout Set.univ / (flow μ c).finit Set.univ + 1 ∧
    Tendsto (flow μ c).tailProb atTop (𝓝 0) ∧
    Tendsto (fun n => (flow μ c).stoppedLaw n Set.univ) atTop (𝓝 1) ∧
    (flow μ c).sampleLaw = ((flow μ c).fterm Set.univ)⁻¹ • (flow μ c).fterm ∧
    ∀ s, MeasurableSet s → Tendsto (fun n => (flow μ c).stoppedLaw n s) atTop
      (𝓝 ((flow μ c).fterm s / (flow μ c).fterm Set.univ)) :=
  (flow μ c).sampling_theorem (fterm_ne_zero μ c) (flowMatching μ c)

end Resample

end GFNBounds.Core.SamplingGeneral
