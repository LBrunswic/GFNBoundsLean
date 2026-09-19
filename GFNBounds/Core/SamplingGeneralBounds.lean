import GFNBounds.Core.SamplingGeneral
import GFNBounds.Core.RLBound
import GFNBounds.Core.ILBoundFull

/-!
# Negative control, and the TV bounds of the two convergence theorems, on a measurable space

**`theo:negative_control`** — `proofs.tex`, the theorem quoted from `\cite{brunswicEGF}` just
after `theo:sampling_theorem`.

> Let `(π⋆_→, f⋆_out)` be a generative flow and let `F_init` and `F_term` initial and terminal
> distributions. Assume that `F_init ≠ 0`, and consider the sample `s_τ` of the generative flow
> Markov chain from `F_init` to `F̂_term` then:
> `TV(s_τ ‖ F̂_term / F̂_term(𝒮)) ≤ δF_init(𝒮) / F̂_term(𝒮)`, with `TV` the total variation.

with `δF_term = (F_init + F⋆_in − F⋆_out − F_term)⁺`, `δF_init = (…)⁻`, `F̂_term = F_term + δF_term`.

**`theo:RL_CV_bound_full`**, item (1), first display (`equ:stable_bound`):
> `TV(s_τ ‖ κ/t) ≤ C 𝓛`, `(π⋆, f⋆_out)` … using `F_term = κ̂ := E⁺` during inference, where
> `E := F_init + F⋆_← − F⋆_out`.

**`theo:IL_CV_bound`**, first bullet:
> `𝓛^q_{KL-wFM}(π⋆, f⋆_out) ≥ 𝓗` and
> `TV(s_τ ‖ κ) ≤ (1/√2)√(𝓛^q_{KL-wFM} − 𝓗) + min(1, ‖dν_B/dν_T‖_{L^{q*}(ν_T)}(𝓛^q_{KL-wFM} − 𝓗))`,
> with `F_term = κ̂ := (F_init + F⋆_← − F⋆_out)⁺` during inference.

Line numbers drift (kb `0036`); the labels are the anchors.

`Core/RLBound.lean` (`stable_bound_kernel`) and `Core/ILBoundFull.lean` (`il_first_bullet`)
prove the two TV clauses on a general measurable space with two external inputs carried as
hypotheses on reals: `hNC` (`theo:negative_control`) and `htri` (the triangle inequality for the
abstract sampler `s_τ`). Both were discharged on a finite state space only
(`Core/NegativeControl.lean`), because the sampler had not been built on a general space. This
file builds on `SamplingGeneral.lean`'s sampler and **discharges both on the general space**.

## The proof of `theo:negative_control` (the source's, now on measures)

1. `(π⋆, F⋆_out)` is flow-matching from `F̂_init = F_init + δF_init` to `F̂_term`
   (`hat_matched`): `D = D⁺ − D⁻` by the Jordan decomposition, compared as signed measures.
2. The chains from `F_init` and `δF_init` to `F̂_term` share one kernel, and the law of the stopped
   state is additive in the initial measure (`SamplingGeneral.termLaw_add`); the unnormalised
   sampling theorem on the matched flow gives `a + b = F̂_term`, `a := termLaw F_init`,
   `b := termLaw δF_init` (`termLaw_split`). Both chains have finite occupation, dominated by `G`
   (`finit_super`, `delta_super`), so the chain from `F_init` stops a.s. — the fact the source
   leaves implicit — and `a(𝒮) = F_init(𝒮)`, `b(𝒮) = δF_init(𝒮)`.
3. `s_τ ∼ a/a(𝒮)`, and against any σ-finite `ρ`,
   `½∫|a'/Z − (a' + b')/K| ≤ ½[(1/Z − 1/K)Z + B/K] = B/K` with `K = Z + B` (`tvD_mixture_le`).

## The inference sampler

`infFlow ν θ f_init` is the sampler of `theo:RL_CV_bound_full` and `theo:IL_CV_bound`:
from `F_init = f_init ν_B` to `κ̂ = E⁺ = e⁺ ν_B`, `e = RLBound.eFn` (`= ILBoundFull.eFlow`,
`eFn_eq_eFlow`), with `δF_init = E⁻` (`infDelta`) and `δF_term = 0`. `infFlow_matched` is step 1
for it on densities; `inference_negative_control` gives termination, a probability law of `s_τ`
`≪ ν_B` with an integrable density `samplerDens`, and `hNC`; `htri_inference` gives `htri` by
`Core.tvD_triangle`.

## What is proved

| | |
|---|---|
| `tvD_mixture_le` | the mixture estimate, against any σ-finite `ρ` |
| `MFlow.termLaw_split`, `MFlow.negative_control_tv` | negative control for any `δ` with `F_init + δ` flow-matching to `F_term` |
| `MFlow.defect`, `dInit`, `dTerm`, `hatTerm`, `hat`, `hat_matched` | the paper's `D`, `δF_init = D⁻`, `δF_term = D⁺`, `F̂_term`, the sampler from `F_init` to `F̂_term`, step 1 |
| **`MFlow.negative_control_general`** | **`theo:negative_control` on a measurable space**, all clauses |
| `infFlow`, `infDelta`, `infFlow_matched`, `samplerDens` | the inference sampler of the two convergence theorems |
| **`inference_negative_control`** | `hNC` discharged, the law of `s_τ` a probability `≪ ν_B` |
| `htri_inference` | `htri` discharged |
| `stable_bound_general_hNC`, **`stable_bound_general`** | `theo:RL_CV_bound_full` item (1), both displays, general space: with `hNC` named (ruling (vii)), and with nothing external |
| `le_essSup_rnDeriv_smul`, `essSup_rnDeriv_eq_eLpNorm_top`, `stable_bound_general_essSup` | the paper's constant: `M = ‖dν_B/dν_T‖_{L^∞(ν_T)}` is admissible in `hdom`, and item (1) at that `M` |
| `il_first_bullet_general_hNC`, **`il_first_bullet_general`** | `theo:IL_CV_bound` first bullet, general space: with `hNC` named, and with nothing external |
| `Resample.stable_bound_general_inhabited`, `Resample.lossFinite`, `Resample.il_first_bullet_general_inhabited` | inhabitation on every probability space, outflow `c ≥ 0`, with the IL TV clause live (`ilLoss ≠ ⊤`) |

## Hypothesis checklist

| paper | here |
|---|---|
| NC: `(π⋆, f⋆_out)` a generative flow, `F_init`, `F_term` distributions, `F_init ≠ 0` | ✓ Markov kernel, finite measures, `hinit`; no flow matching assumed |
| NC: `δF_init`, `δF_term`, `F̂_term` | ✓ Jordan decomposition of the signed defect `D` |
| NC: `TV` | ✓ `Core.tvD` (½-convention of `app:notation`) between the `ρ`-densities, for **every** σ-finite `ρ`, in particular a common dominating one |
| RL/IL: `(𝒮, ν_B)` Polish, `ν_B` finite | ⚠ weakened: any measurable space; `ν_B` finite (RL) / σ-finite (IL), as in the files these extend |
| RL/IL: `F_init ≪ ν_B` a non-zero initial flow / a probability | ✓ `f_init` integrable, **`0 ≤ᵐ f_init`** (a measure has a non-negative density; the parent theorems did not need it, the sampler does), `0 < ∫ f_init` (RL) / `∫ f_init = 1` (IL) |
| RL/IL: `F⋆_← ≪ ν_B` | ✓ RL: `ν_B π⋆ ≪ ν_B` (`hac`), weaker than app:stable's standing ν_B-invariance of π⋆; IL: `InflowAC`, the paper's hypothesis |
| RL/IL: inference at `κ̂ = E⁺`, sampler `s_τ` | ✓ `infFlow`, the sampler of `theo:sampling_theorem` from `F_init` to `κ̂`; `TV(s_τ ‖ ·)` is `tvD ν_B (samplerDens) (·)`, `samplerDens` the `ν_B`-density of `s_τ`'s law, which is shown to be a probability `≪ ν_B` |
| RL/IL: `theo:negative_control` in the proof | ✓ discharged (`inference_negative_control`); also carried as the named hypothesis `hNC` in the `_hNC` forms (ruling (vii)) |
| everything else | as in `stable_bound_kernel` / `il_first_bullet`, whose checklists apply unchanged |

## SCOPE (disclosed)

* **The sampler is modelled by its time-`n` marginals**, as in `SamplingGeneral.lean` (whose
  `chainKernel` is the Markov chain they are the marginals of); "the law of `s_τ`" is `sampleLaw`,
  the setwise limit of `P(τ ≤ n, s_τ ∈ ·)`, and termination is `P(τ > n) → 0`.
* **TV is read between `ρ`-densities.** `negative_control_general` holds for every σ-finite `ρ`;
  the paper's `TV` is its value at any `ρ` dominating both laws. The RL/IL corollaries read it
  against `ν_B`, which dominates both `s_τ`'s law (`inference_negative_control`) and the target.
* **`0 ≤ᵐ f_init` is added to the RL/IL corollaries**: the paper's `F_init` is a measure, and the
  sampler needs one; `stable_bound_kernel`/`il_first_bullet` did not need it because they never
  built the sampler. It is a hypothesis of the paper, not an addition to it.
* **No `sorry`.**

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core.SamplingGeneral

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ### Total variation against a mixture -/

/-- **The mixture estimate of the negative-control proof.** If `a, b` are finite measures
dominated by `ρ` and `a ≠ 0`, the ½-TV between `a/a(𝒮)` and `(a + b)/(a + b)(𝒮)` is at most
`b(𝒮)/(a + b)(𝒮)`. -/
theorem tvD_mixture_le {ρ : Measure α} [SigmaFinite ρ] (a b : Measure α) [IsFiniteMeasure a]
    [IsFiniteMeasure b] (hZ : 0 < a.real Set.univ) :
    GFNBounds.Core.tvD ρ (fun x => (a.rnDeriv ρ x).toReal / a.real Set.univ)
        (fun x => ((a + b).rnDeriv ρ x).toReal / (a + b).real Set.univ)
      ≤ b.real Set.univ / (a + b).real Set.univ := by
  set Z := a.real Set.univ
  set B := b.real Set.univ
  set K := (a + b).real Set.univ
  have hK : K = Z + B := by
    simp only [K, Z, B, measureReal_def, Measure.add_apply]
    exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  have hB0 : 0 ≤ B := measureReal_nonneg
  have hK0 : 0 < K := by rw [hK]; linarith
  have hZK : Z ≤ K := by rw [hK]; linarith
  have hsum : ∀ᵐ x ∂ρ, ((a + b).rnDeriv ρ x).toReal
      = (a.rnDeriv ρ x).toReal + (b.rnDeriv ρ x).toReal := by
    filter_upwards [Measure.rnDeriv_add a b ρ, Measure.rnDeriv_lt_top a ρ,
      Measure.rnDeriv_lt_top b ρ] with x hx ha hb
    rw [hx, Pi.add_apply, ENNReal.toReal_add ha.ne hb.ne]
  have hia : Integrable (fun x => (a.rnDeriv ρ x).toReal) ρ := Measure.integrable_toReal_rnDeriv
  have hib : Integrable (fun x => (b.rnDeriv ρ x).toReal) ρ := Measure.integrable_toReal_rnDeriv
  have hInt_a : ∫ x, (a.rnDeriv ρ x).toReal ∂ρ ≤ Z := by
    have := Measure.integral_toReal_rnDeriv' (μ := a) (ν := ρ)
    rw [this]; linarith [measureReal_nonneg (μ := a.singularPart ρ) (s := Set.univ)]
  have hInt_b : ∫ x, (b.rnDeriv ρ x).toReal ∂ρ ≤ B := by
    have := Measure.integral_toReal_rnDeriv' (μ := b) (ν := ρ)
    rw [this]; linarith [measureReal_nonneg (μ := b.singularPart ρ) (s := Set.univ)]
  have hZne : Z ≠ 0 := hZ.ne'
  have hKne : K ≠ 0 := hK0.ne'
  have hc : 0 ≤ 1 / Z - 1 / K := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hZ hZK
  have hpt : ∀ᵐ x ∂ρ, |(a.rnDeriv ρ x).toReal / Z - ((a + b).rnDeriv ρ x).toReal / K|
      ≤ (1 / Z - 1 / K) * (a.rnDeriv ρ x).toReal + 1 / K * (b.rnDeriv ρ x).toReal := by
    filter_upwards [hsum] with x hx
    rw [hx]
    have hpa : 0 ≤ (a.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
    have hpb : 0 ≤ (b.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
    have e : (a.rnDeriv ρ x).toReal / Z - ((a.rnDeriv ρ x).toReal + (b.rnDeriv ρ x).toReal) / K
        = (1 / Z - 1 / K) * (a.rnDeriv ρ x).toReal - 1 / K * (b.rnDeriv ρ x).toReal := by
      field_simp
      ring
    rw [e]
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (mul_nonneg hc hpa), abs_of_nonneg (mul_nonneg (by positivity) hpb)]
  have hint : Integrable (fun x => (1 / Z - 1 / K) * (a.rnDeriv ρ x).toReal
      + 1 / K * (b.rnDeriv ρ x).toReal) ρ := (hia.const_mul _).add (hib.const_mul _)
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
    hint hpt
  rw [integral_add (hia.const_mul _) (hib.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  unfold GFNBounds.Core.tvD
  have h1 : (1 / Z - 1 / K) * ∫ x, (a.rnDeriv ρ x).toReal ∂ρ ≤ (1 / Z - 1 / K) * Z :=
    mul_le_mul_of_nonneg_left hInt_a hc
  have h2 : 1 / K * ∫ x, (b.rnDeriv ρ x).toReal ∂ρ ≤ 1 / K * B :=
    mul_le_mul_of_nonneg_left hInt_b (by positivity)
  have h3 : (1 / Z - 1 / K) * Z + 1 / K * B = 2 * (B / K) := by
    rw [hK]; field_simp; ring
  linarith

theorem tvD_congr_left {ρ : Measure α} {f f' g : α → ℝ} (h : f =ᵐ[ρ] f') :
    GFNBounds.Core.tvD ρ f g = GFNBounds.Core.tvD ρ f' g := by
  unfold GFNBounds.Core.tvD
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-! ### `theo:negative_control` on a measurable space -/

namespace MFlow

theorem sampleLaw_eq_smul (F : MFlow α) :
    F.sampleLaw = (F.finit Set.univ)⁻¹ • F.termLaw F.finit := by
  rw [sampleLaw, init, termLaw_smul]

variable (F : MFlow α) [IsFiniteMeasure F.fterm] [IsFiniteMeasure F.fout]

section Matched

variable {δ : Measure α}
  (hmatch : F.finit + δ + F.fout.bind F.P = F.fterm + F.fout)

include hmatch

theorem matched_step : (F.finit + δ) + F.step F.G = F.G := by
  rw [step, withDensity_cont]; exact hmatch

theorem finit_super : F.finit + F.step F.G ≤ F.G := by
  calc F.finit + F.step F.G ≤ (F.finit + δ) + F.step F.G :=
        add_le_add_left (Measure.le_add_right le_rfl) _
    _ = F.G := F.matched_step hmatch

theorem delta_super : δ + F.step F.G ≤ F.G := by
  calc δ + F.step F.G ≤ (F.finit + δ) + F.step F.G :=
        add_le_add_left (Measure.le_add_left le_rfl) _
    _ = F.G := F.matched_step hmatch

/-- **Step 2 of the source's proof**: the chains from `F_init` and from `δF_init` share the
kernel, and their stopped laws add up to `F̂_term`. -/
theorem termLaw_split [IsMarkovKernel F.P] : F.termLaw F.finit + F.termLaw δ = F.fterm := by
  rw [← termLaw_add]; exact F.termLaw_eq_fterm (F.matched_step hmatch)

theorem occupation_finit_ne_top : F.occupation F.finit Set.univ ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top F.G Set.univ)
    (Measure.le_iff.1 (F.occupation_le (F.finit_super hmatch)) _ MeasurableSet.univ)

theorem occupation_delta_ne_top : F.occupation δ Set.univ ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top F.G Set.univ)
    (Measure.le_iff.1 (F.occupation_le (F.delta_super hmatch)) _ MeasurableSet.univ)

/-- `F̂_term(𝒮) = F_init(𝒮) + δF_init(𝒮)`. -/
theorem fterm_univ_eq [IsMarkovKernel F.P] : F.fterm Set.univ = F.finit Set.univ + δ Set.univ := by
  rw [← F.termLaw_split hmatch, Measure.add_apply, F.termLaw_univ _ (F.occupation_finit_ne_top hmatch),
    F.termLaw_univ _ (F.occupation_delta_ne_top hmatch)]

/-- The sampler from `F_init` to `F̂_term` stops almost surely: `𝔼(τ) < ∞`. -/
theorem expectedTau_ne_top_matched (hinit : F.finit ≠ 0) : F.expectedTau ≠ ∞ := by
  have hZ : F.finit Set.univ ≠ 0 := fun h => hinit (Measure.measure_univ_eq_zero.1 h)
  rw [expectedTau_eq, init, occupation_smul, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ) (F.occupation_finit_ne_top hmatch)

theorem sampleLaw_univ_matched [IsFiniteMeasure F.finit] [IsMarkovKernel F.P] (hinit : F.finit ≠ 0) : F.sampleLaw Set.univ = 1 := by
  have hZ : F.finit Set.univ ≠ 0 := fun h => hinit (Measure.measure_univ_eq_zero.1 h)
  rw [F.sampleLaw_eq_smul, Measure.smul_apply, smul_eq_mul,
    F.termLaw_univ _ (F.occupation_finit_ne_top hmatch)]
  exact ENNReal.inv_mul_cancel hZ (measure_ne_top _ _)

theorem isFiniteMeasure_termLaw_finit [IsMarkovKernel F.P] : IsFiniteMeasure (F.termLaw F.finit) :=
  isFiniteMeasure_of_le F.fterm (by
    rw [← F.termLaw_split hmatch]; exact Measure.le_add_right le_rfl)

theorem isFiniteMeasure_termLaw_delta [IsMarkovKernel F.P] : IsFiniteMeasure (F.termLaw δ) :=
  isFiniteMeasure_of_le F.fterm (by
    rw [← F.termLaw_split hmatch]; exact Measure.le_add_left le_rfl)

theorem sampleLaw_le [IsMarkovKernel F.P] :
    F.sampleLaw ≤ (F.finit Set.univ)⁻¹ • F.fterm := by
  rw [F.sampleLaw_eq_smul, ← F.termLaw_split hmatch, smul_add]
  exact Measure.le_add_right le_rfl

/-- **`theo:negative_control` on a measurable space**, TV read against any σ-finite `ρ`:
`TV(s_τ ‖ F̂_term/F̂_term(𝒮)) ≤ δF_init(𝒮)/F̂_term(𝒮)`, for the sampler from `F_init` to
`F̂_term`, whenever `(π⋆, F⋆_out)` is flow-matching from `F_init + δF_init` to `F̂_term`. -/
theorem negative_control_tv [IsFiniteMeasure F.finit] [IsMarkovKernel F.P] (hinit : F.finit ≠ 0) (ρ : Measure α) [SigmaFinite ρ] :
    GFNBounds.Core.tvD ρ (fun x => (F.sampleLaw.rnDeriv ρ x).toReal)
        (fun x => (F.fterm.rnDeriv ρ x).toReal / F.fterm.real Set.univ)
      ≤ δ.real Set.univ / F.fterm.real Set.univ := by
  haveI := F.isFiniteMeasure_termLaw_finit hmatch
  haveI := F.isFiniteMeasure_termLaw_delta hmatch
  have hZ : F.finit Set.univ ≠ 0 := fun h => hinit (Measure.measure_univ_eq_zero.1 h)
  have ha : F.termLaw F.finit Set.univ = F.finit Set.univ :=
    F.termLaw_univ _ (F.occupation_finit_ne_top hmatch)
  have hb : F.termLaw δ Set.univ = δ Set.univ :=
    F.termLaw_univ _ (F.occupation_delta_ne_top hmatch)
  have hZr : 0 < (F.termLaw F.finit).real Set.univ := by
    rw [measureReal_def, ha]
    exact ENNReal.toReal_pos hZ (measure_ne_top _ _)
  have hdens : (fun x => (F.sampleLaw.rnDeriv ρ x).toReal)
      =ᵐ[ρ] fun x => ((F.termLaw F.finit).rnDeriv ρ x).toReal
        / (F.termLaw F.finit).real Set.univ := by
    rw [F.sampleLaw_eq_smul]
    filter_upwards [Measure.rnDeriv_smul_left_of_ne_top (F.termLaw F.finit) ρ
      (ENNReal.inv_ne_top.2 hZ)] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def,
      ha, div_eq_mul_inv, mul_comm]
  rw [tvD_congr_left hdens]
  have h := tvD_mixture_le (ρ := ρ) (F.termLaw F.finit) (F.termLaw δ) hZr
  rw [F.termLaw_split hmatch] at h
  have hbr : (F.termLaw δ).real Set.univ = δ.real Set.univ := by rw [measureReal_def, hb]; rfl
  rwa [hbr] at h

end Matched

end MFlow

/-! ### The paper's `δF_init`, `δF_term`, `F̂_term`: the Jordan decomposition of the defect -/

namespace MFlow

section Jordan

variable (F : MFlow α) [IsFiniteMeasure F.finit] [IsFiniteMeasure F.fterm]
  [IsFiniteMeasure F.fout] [IsMarkovKernel F.P]

instance isFiniteMeasure_bind : IsFiniteMeasure (F.fout.bind F.P) :=
  ⟨by rw [Measure.bind_apply MeasurableSet.univ F.P.aemeasurable]
      simp only [measure_univ, lintegral_one]
      exact measure_lt_top _ _⟩

/-- The flow-matching defect `D := F_init + F⋆_in − F⋆_out − F_term`, `F⋆_in = F⋆_out π⋆`, as a
signed measure. -/
noncomputable def defect : SignedMeasure α :=
  (F.finit + F.fout.bind F.P).toSignedMeasure - (F.fterm + F.fout).toSignedMeasure

/-- `δF_term := D⁺`, the positive part of the Jordan decomposition. -/
noncomputable def dTerm : Measure α := F.defect.toJordanDecomposition.posPart

/-- `δF_init := D⁻`, the negative part. -/
noncomputable def dInit : Measure α := F.defect.toJordanDecomposition.negPart

/-- `F̂_term := F_term + δF_term`. -/
noncomputable def hatTerm : Measure α := F.fterm + F.dTerm

/-- The sampler "from `F_init` to `F̂_term`" of `theo:negative_control`. -/
noncomputable def hat : MFlow α := { F with fterm := F.hatTerm }

instance : IsFiniteMeasure F.dTerm := by unfold dTerm; infer_instance
instance : IsFiniteMeasure F.dInit := by unfold dInit; infer_instance
instance : IsFiniteMeasure F.hatTerm := by unfold hatTerm; infer_instance
instance : IsFiniteMeasure F.hat.finit := by unfold hat; dsimp only; infer_instance
instance : IsFiniteMeasure F.hat.fterm := by unfold hat; dsimp only; infer_instance
instance : IsFiniteMeasure F.hat.fout := by unfold hat; dsimp only; infer_instance
instance : IsMarkovKernel F.hat.P := by unfold hat; dsimp only; infer_instance

/-- **Step 1**: `(π⋆, F⋆_out)` is flow-matching from `F̂_init = F_init + δF_init` to `F̂_term`. -/
theorem hat_matched :
    F.hat.finit + F.dInit + F.hat.fout.bind F.hat.P = F.hat.fterm + F.hat.fout := by
  have hj := F.defect.toSignedMeasure_toJordanDecomposition
  rw [JordanDecomposition.toSignedMeasure] at hj
  change F.dTerm.toSignedMeasure - F.dInit.toSignedMeasure = F.defect at hj
  have h2 : (F.finit + F.fout.bind F.P + F.dInit).toSignedMeasure
      = (F.fterm + F.fout + F.dTerm).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add (F.fterm + F.fout)]
    have : F.defect = (F.finit + F.fout.bind F.P).toSignedMeasure
        - (F.fterm + F.fout).toSignedMeasure := rfl
    rw [this] at hj
    have h3 : F.dTerm.toSignedMeasure - F.dInit.toSignedMeasure
        + (F.fterm + F.fout).toSignedMeasure + F.dInit.toSignedMeasure
        = (F.finit + F.fout.bind F.P).toSignedMeasure - (F.fterm + F.fout).toSignedMeasure
        + (F.fterm + F.fout).toSignedMeasure + F.dInit.toSignedMeasure := by rw [hj]
    rw [Measure.toSignedMeasure_add F.fterm F.fout] at h3 ⊢
    calc (F.finit + F.fout.bind F.P).toSignedMeasure + F.dInit.toSignedMeasure
        = (F.finit + F.fout.bind F.P).toSignedMeasure
          - (F.fterm.toSignedMeasure + F.fout.toSignedMeasure)
          + (F.fterm.toSignedMeasure + F.fout.toSignedMeasure) + F.dInit.toSignedMeasure := by
          abel
      _ = F.dTerm.toSignedMeasure - F.dInit.toSignedMeasure
          + (F.fterm.toSignedMeasure + F.fout.toSignedMeasure) + F.dInit.toSignedMeasure :=
          h3.symm
      _ = F.fterm.toSignedMeasure + F.fout.toSignedMeasure + F.dTerm.toSignedMeasure := by
          abel
  rw [Measure.toSignedMeasure_eq_toSignedMeasure_iff] at h2
  change F.finit + F.dInit + F.fout.bind F.P = F.hatTerm + F.fout
  rw [hatTerm, add_right_comm, h2, add_right_comm]

/-- **`theo:negative_control` on a measurable space.** Let `(π⋆, F⋆_out)` be a generative flow
(a Markov kernel and a finite measure) and `F_init, F_term` finite measures with `F_init ≠ 0`;
flow matching is not assumed. The sampler from `F_init` to `F̂_term`

1. stops almost surely, `P(τ > n) → 0`, and `s_τ` has a probability law;
2. `F̂_term(𝒮) = F_init(𝒮) + δF_init(𝒮)`;
3. `TV(s_τ ‖ F̂_term/F̂_term(𝒮)) ≤ δF_init(𝒮)/F̂_term(𝒮)`, TV with the ½-convention read against
   any σ-finite `ρ` (a common dominating measure of `app:notation`, e.g. `s_τ`'s law plus
   `F̂_term`). -/
theorem negative_control_general (hinit : F.finit ≠ 0) (ρ : Measure α) [SigmaFinite ρ] :
    Tendsto F.hat.tailProb atTop (𝓝 0) ∧
    F.hat.sampleLaw Set.univ = 1 ∧
    F.hatTerm Set.univ = F.finit Set.univ + F.dInit Set.univ ∧
    GFNBounds.Core.tvD ρ (fun x => (F.hat.sampleLaw.rnDeriv ρ x).toReal)
        (fun x => (F.hatTerm.rnDeriv ρ x).toReal / F.hatTerm.real Set.univ)
      ≤ F.dInit.real Set.univ / F.hatTerm.real Set.univ := by
  have hm := F.hat_matched
  have hinit' : F.hat.finit ≠ 0 := hinit
  exact ⟨F.hat.tailProb_tendsto_zero_of_ne_top (F.hat.expectedTau_ne_top_matched hm hinit'),
    F.hat.sampleLaw_univ_matched hm hinit', F.hat.fterm_univ_eq hm,
    F.hat.negative_control_tv hm hinit' ρ⟩

end Jordan

end MFlow

/-! ### The inference sampler of `theo:RL_CV_bound_full` and `theo:IL_CV_bound`

The flow is carried by densities against `ν_B`, as in `Core/RLBound.lean` and
`Core/ILBoundFull.lean`: `F_init = f_init ν_B`, `F⋆_out = f⋆_out ν_B`, and
`E = F_init + F⋆_← − F⋆_out` has density `e = RLBound.eFn`. Inference runs the sampler of
`theo:sampling_theorem` from `F_init` to `κ̂ := E⁺`. -/

section Inference

open GFNBounds.Core.Family GFNBounds.Core.RLBound GFNBounds.Core.ILBoundFull

variable {ν : Measure α} {θ : Kernel α α × (α → ℝ)} {f_init : α → ℝ}

/-- The inference sampler: from `F_init = f_init ν_B` to `κ̂ = E⁺ = e⁺ ν_B`, with the flow's
outflow `F⋆_out = f⋆_out ν_B` and policy `π⋆`. -/
noncomputable def infFlow (ν : Measure α) (θ : Kernel α α × (α → ℝ)) (f_init : α → ℝ) :
    MFlow α where
  finit := ν.withDensity fun x => ENNReal.ofReal (f_init x)
  fterm := ν.withDensity fun x => ENNReal.ofReal (max (eFn ν θ f_init x) 0)
  fout := ν.withDensity fun x => ENNReal.ofReal (θ.2 x)
  P := θ.1

/-- The initial error `δF_init = E⁻ = e⁻ ν_B` of the inference flow (its terminal error
`δF_term = (E − κ̂)⁺` is `0`). -/
noncomputable def infDelta (ν : Measure α) (θ : Kernel α α × (α → ℝ)) (f_init : α → ℝ) :
    Measure α :=
  ν.withDensity fun x => ENNReal.ofReal (max (-eFn ν θ f_init x) 0)

theorem eFn_eq_eFlow : eFn ν θ f_init = eFlow ν θ f_init := by
  funext x; simp only [eFn, eFlow, defectFn, sub_zero]

theorem withDensity_add_ae {f g : α → ℝ≥0∞} (hf : AEMeasurable f ν) :
    ν.withDensity f + ν.withDensity g = ν.withDensity (f + g) := by
  ext s hs
  rw [Measure.add_apply, withDensity_apply _ hs, withDensity_apply _ hs, withDensity_apply _ hs,
    Pi.add_def, lintegral_add_left' hf.restrict]

theorem measureReal_withDensity_ofReal {f : α → ℝ} (hf : Integrable f ν) (hf0 : 0 ≤ᵐ[ν] f) :
    (ν.withDensity fun x => ENNReal.ofReal (f x)).real Set.univ = ∫ x, f x ∂ν := by
  rw [measureReal_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    integral_eq_lintegral_of_nonneg_ae hf0 hf.1]

section Hyp

variable [SigmaFinite ν] (hθ : IsGenerativeFlow ν θ) (hin : InflowAC ν θ)
  (hfi : Integrable f_init ν) (hfi0 : 0 ≤ᵐ[ν] f_init)

include hθ hin hfi

theorem integrable_eFn' : Integrable (eFn ν θ f_init) ν := by
  rw [eFn_eq_eFlow]; exact (eFlow_integral hθ hin hfi).1

theorem infFlow_finite :
    IsFiniteMeasure (infFlow ν θ f_init).finit ∧ IsFiniteMeasure (infFlow ν θ f_init).fterm ∧
    IsFiniteMeasure (infFlow ν θ f_init).fout ∧ IsMarkovKernel (infFlow ν θ f_init).P ∧
    IsFiniteMeasure (infDelta ν θ f_init) :=
  ⟨isFiniteMeasure_withDensity_ofReal hfi.2,
    isFiniteMeasure_withDensity_ofReal ((integrable_eFn' hθ hin hfi).pos_part).2,
    isFiniteMeasure_withDensity_ofReal hθ.integrable.2, hθ.markov,
    isFiniteMeasure_withDensity_ofReal ((integrable_eFn' hθ hin hfi).neg.pos_part).2⟩

include hfi0 in
/-- **Step 1 of the negative-control proof, for the inference flow**: `(π⋆, F⋆_out)` is
flow-matching from `F_init + E⁻` to `κ̂ = E⁺`. -/
theorem infFlow_matched :
    (infFlow ν θ f_init).finit + infDelta ν θ f_init
        + (infFlow ν θ f_init).fout.bind (infFlow ν θ f_init).P
      = (infFlow ν θ f_init).fterm + (infFlow ν θ f_init).fout := by
  haveI := hθ.markov
  have hlt : ∫⁻ x, ENNReal.ofReal (θ.2 x) ∂ν ≠ ⊤ := lintegral_ofReal_ne_top hθ.integrable
  haveI := isFiniteMeasure_bind_withDensity θ.1 ν hlt
  have he := integrable_eFn' hθ hin hfi
  simp only [infFlow, infDelta]
  -- `F⋆_←` has density `ofReal (densityAction …)`
  have hbd : (ν.withDensity fun x => ENNReal.ofReal (θ.2 x)).bind ⇑θ.1
      = ν.withDensity (bindDensity θ.1 ν fun y => ENNReal.ofReal (θ.2 y)) :=
    (Measure.withDensity_rnDeriv_eq _ _ hin).symm
  have hz : (fun y => ENNReal.ofReal (-θ.2 y)) = 0 := by
    funext y; exact ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 (hθ.nonneg y))
  have hneg : bindDensity θ.1 ν (fun y => ENNReal.ofReal (-θ.2 y)) =ᵐ[ν] 0 := by
    rw [hz]; exact bindDensity_zero θ.1 ν
  have hfin : ∀ᵐ x ∂ν, bindDensity θ.1 ν (fun y => ENNReal.ofReal (θ.2 y)) x < ⊤ :=
    Measure.rnDeriv_lt_top _ _
  have hm1 : AEMeasurable ((fun y => ENNReal.ofReal (f_init y))
      + fun x => ENNReal.ofReal (max (-eFn ν θ f_init x) 0)) ν :=
    (aemeasurable_ofReal hfi).add (aemeasurable_ofReal (he.neg.pos_part))
  rw [hbd, withDensity_add_ae (aemeasurable_ofReal hfi), withDensity_add_ae hm1,
    withDensity_add_ae (aemeasurable_ofReal he.pos_part)]
  refine withDensity_congr_ae ?_
  filter_upwards [hneg, hfin, hfi0] with x hx hxf hx0
  simp only [Pi.add_apply]
  set b := bindDensity θ.1 ν (fun y => ENNReal.ofReal (θ.2 y)) x with hb
  have hdA : densityAction θ.1 ν θ.2 x = b.toReal := by
    simp only [densityAction, hx, Pi.zero_apply, ENNReal.toReal_zero, sub_zero, hb]
  have hbeq : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hxf.ne).symm
  have hθ0 := hθ.nonneg x
  have hb0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have heq : eFn ν θ f_init x = f_init x + b.toReal - θ.2 x := by
    simp only [eFn, hdA]
  rw [hbeq, ← ENNReal.ofReal_add hx0 (le_max_right _ _),
    ← ENNReal.ofReal_add (add_nonneg hx0 (le_max_right _ _)) hb0,
    ← ENNReal.ofReal_add (le_max_right _ _) hθ0]
  congr 1
  rw [heq]
  rcases le_total (f_init x + b.toReal - θ.2 x) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

end Hyp

theorem tvD_congr_right {ρ : Measure α} {f g g' : α → ℝ} (h : g =ᵐ[ρ] g') :
    GFNBounds.Core.tvD ρ f g = GFNBounds.Core.tvD ρ f g' := by
  unfold GFNBounds.Core.tvD
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The density of the law of the inference sampler's output `s_τ` against `ν_B`. -/
noncomputable def samplerDens (ν : Measure α) (θ : Kernel α α × (α → ℝ)) (f_init : α → ℝ) :
    α → ℝ :=
  fun x => ((infFlow ν θ f_init).sampleLaw.rnDeriv ν x).toReal

section Hyp2

variable [SigmaFinite ν] (hθ : IsGenerativeFlow ν θ) (hin : InflowAC ν θ)
  (hfi : Integrable f_init ν) (hfi0 : 0 ≤ᵐ[ν] f_init) (hz0 : 0 < ∫ x, f_init x ∂ν)

include hθ hin hfi hfi0 hz0

/-- **`theo:negative_control` for the inference sampler, on a general measurable space.** The
sampler from `F_init` to `κ̂ = E⁺` stops almost surely (`P(τ > n) → 0`), its output `s_τ` has a
probability law `≪ ν_B` with an integrable density `p`, and
`TV(s_τ ‖ κ̂/κ̂(𝒮)) ≤ δF_init(𝒮)/κ̂(𝒮)` with `δF_init = E⁻` — the hypothesis `hNC` of
`RLBound.stable_bound_kernel` and `ILBoundFull.il_first_bullet`, discharged. -/
theorem inference_negative_control :
    Tendsto (infFlow ν θ f_init).tailProb atTop (𝓝 0) ∧
    (infFlow ν θ f_init).sampleLaw Set.univ = 1 ∧
    (infFlow ν θ f_init).sampleLaw ≪ ν ∧
    Integrable (samplerDens ν θ f_init) ν ∧
    GFNBounds.Core.tvD ν (samplerDens ν θ f_init)
        (fun x => max (eFn ν θ f_init x) 0 / ∫ x, max (eFn ν θ f_init x) 0 ∂ν)
      ≤ (∫ x, max (-eFn ν θ f_init x) 0 ∂ν) / ∫ x, max (eFn ν θ f_init x) 0 ∂ν := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := infFlow_finite hθ hin hfi
  have hmatch := infFlow_matched hθ hin hfi hfi0
  have he := integrable_eFn' hθ hin hfi
  set F := infFlow ν θ f_init with hFdef
  have hinit : F.finit ≠ 0 := by
    intro h
    have : F.finit.real Set.univ = ∫ x, f_init x ∂ν :=
      measureReal_withDensity_ofReal hfi hfi0
    rw [h] at this
    simp only [measureReal_zero, Pi.zero_apply] at this
    linarith
  have hsl1 := F.sampleLaw_univ_matched hmatch hinit
  haveI : IsFiniteMeasure F.sampleLaw := ⟨by rw [hsl1]; exact ENNReal.one_lt_top⟩
  have hac : F.sampleLaw ≪ ν := by
    refine (Measure.absolutelyContinuous_of_le (F.sampleLaw_le hmatch)).trans ?_
    exact (Measure.smul_absolutelyContinuous).trans (withDensity_absolutelyContinuous _ _)
  refine ⟨F.tailProb_tendsto_zero_of_ne_top (F.expectedTau_ne_top_matched hmatch hinit), hsl1,
    hac, Measure.integrable_toReal_rnDeriv, ?_⟩
  have hNC := F.negative_control_tv hmatch hinit ν
  have hterm : F.fterm.real Set.univ = ∫ x, max (eFn ν θ f_init x) 0 ∂ν :=
    measureReal_withDensity_ofReal he.pos_part (Filter.Eventually.of_forall fun _ =>
      le_max_right _ _)
  have hdelta : (infDelta ν θ f_init).real Set.univ = ∫ x, max (-eFn ν θ f_init x) 0 ∂ν :=
    measureReal_withDensity_ofReal he.neg.pos_part (Filter.Eventually.of_forall fun _ =>
      le_max_right _ _)
  rw [hterm, hdelta] at hNC
  have hd : (fun x => (F.fterm.rnDeriv ν x).toReal / ∫ x, max (eFn ν θ f_init x) 0 ∂ν)
      =ᵐ[ν] fun x => max (eFn ν θ f_init x) 0 / ∫ x, max (eFn ν θ f_init x) 0 ∂ν := by
    have hft : F.fterm = ν.withDensity fun y => ENNReal.ofReal (max (eFn ν θ f_init y) 0) := rfl
    rw [hft]
    filter_upwards [Measure.rnDeriv_withDensity₀ ν (aemeasurable_ofReal he.pos_part)] with x hx
    rw [hx, ENNReal.toReal_ofReal (le_max_right _ _)]
  rw [tvD_congr_right hd] at hNC
  exact hNC

end Hyp2

/-! ### `theo:RL_CV_bound_full`, item (1), on a general measurable space -/

section RL

variable [IsFiniteMeasure ν] {νT : Measure α} {M : ℝ≥0} {q : ℝ≥0∞} {k : α → ℝ}

/-- The triangle inequality `htri` for the inference sampler: its law has a `ν_B`-density. -/
theorem htri_inference (hθ : IsGenerativeFlow ν θ) (hin : InflowAC ν θ)
    (hfi : Integrable f_init ν) (hfi0 : 0 ≤ᵐ[ν] f_init) (hz0 : 0 < ∫ x, f_init x ∂ν)
    (hk : Integrable k ν) (t zhat : ℝ) :
    GFNBounds.Core.tvD ν (samplerDens ν θ f_init) (fun x => k x / t)
      ≤ GFNBounds.Core.tvD ν (samplerDens ν θ f_init)
          (fun x => max (eFn ν θ f_init x) 0 / zhat)
        + GFNBounds.Core.tvD ν (fun x => max (eFn ν θ f_init x) 0 / zhat) (fun x => k x / t) := by
  have hp := (inference_negative_control hθ hin hfi hfi0 hz0).2.2.2.1
  have he := (integrable_eFn' hθ hin hfi).pos_part.div_const zhat
  exact GFNBounds.Core.tvD_triangle (hp.sub he) (he.sub (hk.div_const t))

/-- **`equ:stable_bound` on a general measurable space, `theo:negative_control` as a named
hypothesis** (ruling (vii)): `htri` is discharged, the sampler being the inference sampler of
`theo:sampling_theorem` from `F_init` to `κ̂ = E⁺`, whose output law has the `ν_B`-density
`samplerDens`. -/
theorem stable_bound_general_hNC {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT) (hq : 1 ≤ q)
    (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν) (hi : Integrable f_init ν)
    (hi0 : 0 ≤ᵐ[ν] f_init) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k)
    (hmem : MemLp (defectFn ν θ f_init k) q νT)
    (hz0 : 0 < ∫ x, f_init x ∂ν) (ht0 : 0 < ∫ x, k x ∂ν)
    (hNC : GFNBounds.Core.tvD ν (samplerDens ν θ f_init)
        (fun x => max (eFn ν θ f_init x) 0 / ∫ x, max (eFn ν θ f_init x) 0 ∂ν)
      ≤ (∫ x, max (-eFn ν θ f_init x) 0 ∂ν) / ∫ x, max (eFn ν θ f_init x) 0 ∂ν) :
    GFNBounds.Core.tvD ν (samplerDens ν θ f_init) (fun x => k x / ∫ x, k x ∂ν)
      ≤ GFNBounds.Core.stableConst ν M q.toReal (∫ x, k x ∂ν)
        * (eLpNorm (defectFn ν θ f_init k) q νT).toReal :=
  stable_bound_kernel hdom hq hθ hac hi hk hk0 hmem hz0 ht0 hNC
    (htri_inference hθ (inflowAC_of_bind_ac hac) hi hi0 hz0 hk _ _)

/-- **`theo:RL_CV_bound_full`, item (1), both displays, on a general measurable space, with
nothing external**: `hNC` by `inference_negative_control`, `htri` by `htri_inference`, `hz` by
`RLBound.integral_eFn`. The inference sampler from `F_init` to `κ̂ = E⁺` stops almost surely,
its output `s_τ` has a probability law `≪ ν_B` with density `samplerDens`, and at every
`q ∈ [1, ∞]`

  `TV(s_τ ‖ κ/t) ≤ C 𝓛`,  `|F_init(𝒮) − κ(𝒮)| ≤ C₀ 𝓛`. -/
theorem stable_bound_general {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT) (hq : 1 ≤ q)
    (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν) (hi : Integrable f_init ν)
    (hi0 : 0 ≤ᵐ[ν] f_init) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k)
    (hmem : MemLp (defectFn ν θ f_init k) q νT)
    (hz0 : 0 < ∫ x, f_init x ∂ν) (ht0 : 0 < ∫ x, k x ∂ν) :
    Tendsto (infFlow ν θ f_init).tailProb atTop (𝓝 0) ∧
    (infFlow ν θ f_init).sampleLaw Set.univ = 1 ∧
    (infFlow ν θ f_init).sampleLaw ≪ ν ∧
    GFNBounds.Core.tvD ν (samplerDens ν θ f_init) (fun x => k x / ∫ x, k x ∂ν)
      ≤ GFNBounds.Core.stableConst ν M q.toReal (∫ x, k x ∂ν)
        * (eLpNorm (defectFn ν θ f_init k) q νT).toReal ∧
    |(∫ x, f_init x ∂ν) - ∫ x, k x ∂ν|
      ≤ GFNBounds.Core.holderConst ν M q.toReal * (eLpNorm (defectFn ν θ f_init k) q νT).toReal := by
  have hin := inflowAC_of_bind_ac hac
  obtain ⟨h1, h2, h3, -, hNC⟩ := inference_negative_control hθ hin hi hi0 hz0
  exact ⟨h1, h2, h3, stable_bound_general_hNC hdom hq hθ hac hi hi0 hk hk0 hmem hz0 ht0 hNC,
    mass_floor_kernel hdom hq hθ hac hi hk hmem⟩

/-- **The paper's constant is admissible.** If `ν_B ≪ ν_T` (both σ-finite), then
`ν_B ≤ ‖dν_B/dν_T‖_{L^∞(ν_T)} • ν_T`, the norm being the essential supremum of the
Radon–Nikodym derivative (`essSup_rnDeriv_eq_eLpNorm_top`). So `M = ‖dν_B/dν_T‖_∞`, the least
admissible `M`, is an instance of `hdom` whenever it is finite. -/
theorem le_essSup_rnDeriv_smul {ν νT : Measure α} [SigmaFinite ν] [SigmaFinite νT]
    (hνT : ν ≪ νT) : ν ≤ essSup (ν.rnDeriv νT) νT • νT :=
  calc ν = νT.withDensity (ν.rnDeriv νT) := (Measure.withDensity_rnDeriv_eq ν νT hνT).symm
    _ ≤ νT.withDensity (fun _ => essSup (ν.rnDeriv νT) νT) := withDensity_mono ae_le_essSup
    _ = essSup (ν.rnDeriv νT) νT • νT := withDensity_const _

/-- The essential supremum of `dν_B/dν_T` is its `L^∞(ν_T)` norm. -/
theorem essSup_rnDeriv_eq_eLpNorm_top (ν νT : Measure α) :
    essSup (ν.rnDeriv νT) νT = eLpNorm (ν.rnDeriv νT) ⊤ νT := by
  rw [eLpNorm_exponent_top, eLpNormEssSup]; simp only [enorm_eq_self]

/-- **`theo:RL_CV_bound_full`, item (1), at the paper's constant**: `stable_bound_general`
instantiated at `M = ‖dν_B/dν_T‖_{L^∞(ν_T)}`, which is admissible by `le_essSup_rnDeriv_smul`
whenever `ν_B ≪ ν_T` and the norm is finite (the paper's hypothesis `dν_B/dν_T ∈ L^∞(ν_T)`). -/
theorem stable_bound_general_essSup [SigmaFinite νT] (hνT : ν ≪ νT)
    (hM : essSup (ν.rnDeriv νT) νT ≠ ∞) (hq : 1 ≤ q)
    (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν) (hi : Integrable f_init ν)
    (hi0 : 0 ≤ᵐ[ν] f_init) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k)
    (hmem : MemLp (defectFn ν θ f_init k) q νT)
    (hz0 : 0 < ∫ x, f_init x ∂ν) (ht0 : 0 < ∫ x, k x ∂ν) :
    Tendsto (infFlow ν θ f_init).tailProb atTop (𝓝 0) ∧
    (infFlow ν θ f_init).sampleLaw Set.univ = 1 ∧
    (infFlow ν θ f_init).sampleLaw ≪ ν ∧
    GFNBounds.Core.tvD ν (samplerDens ν θ f_init) (fun x => k x / ∫ x, k x ∂ν)
      ≤ GFNBounds.Core.stableConst ν (essSup (ν.rnDeriv νT) νT).toNNReal q.toReal
          (∫ x, k x ∂ν)
        * (eLpNorm (defectFn ν θ f_init k) q νT).toReal ∧
    |(∫ x, f_init x ∂ν) - ∫ x, k x ∂ν|
      ≤ GFNBounds.Core.holderConst ν (essSup (ν.rnDeriv νT) νT).toNNReal q.toReal
        * (eLpNorm (defectFn ν θ f_init k) q νT).toReal := by
  have hdom : ν ≤ (((essSup (ν.rnDeriv νT) νT).toNNReal : ℝ≥0) : ℝ≥0∞) • νT := by
    rw [ENNReal.coe_toNNReal hM]; exact le_essSup_rnDeriv_smul hνT
  exact stable_bound_general hdom hq hθ hac hi hi0 hk hk0 hmem hz0 ht0

end RL

/-! ### `theo:IL_CV_bound`, first bullet, on a general measurable space -/

section IL

variable {νT : Measure α} {k : α → ℝ}

/-- **The first bullet of `theo:IL_CV_bound` on a general measurable space, `theo:negative_control`
as a named hypothesis** (ruling (vii)): `htri` discharged for the inference sampler. -/
theorem il_first_bullet_general_hNC [SigmaFinite ν] [SigmaFinite νT] {q qstar : ℝ≥0∞}
    [ENNReal.HolderConjugate qstar q] (hνT : ν ≪ νT)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT) {b : ℝ}
    (hb : 1 + rnNorm ν νT qstar ≤ b)
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (hfi : Integrable f_init ν) (hfi1 : ∫ x, f_init x ∂ν = 1) (hfi0 : 0 ≤ᵐ[ν] f_init)
    (hθ : IsGenerativeFlow ν θ) (hin : InflowAC ν θ)
    (hNC : GFNBounds.Core.tvD ν (samplerDens ν θ f_init)
        (fun x => max (eFlow ν θ f_init x) 0 / ∫ x, max (eFlow ν θ f_init x) 0 ∂ν)
      ≤ (∫ x, max (-eFlow ν θ f_init x) 0 ∂ν) / ∫ x, max (eFlow ν θ f_init x) 0 ∂ν) :
    ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) ≤ ilLoss ν νT q b k (eFlow ν θ f_init) ∧
    (ilLoss ν νT q b k (eFlow ν θ f_init) ≠ ⊤ →
      GFNBounds.Core.tvD ν (samplerDens ν θ f_init) k
        ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLossE ν νT q b k (eFlow ν θ f_init)
              - GFNBounds.Core.selfEntropy ν k)
          + min 1 (rnNorm ν νT qstar * (wklfmLossE ν νT q b k (eFlow ν θ f_init)
              - GFNBounds.Core.selfEntropy ν k))) := by
  have hz0 : 0 < ∫ x, f_init x ∂ν := by rw [hfi1]; exact one_pos
  obtain ⟨h1, h2⟩ := il_first_bullet (q := q) hνT hr hb hk hk1 hk0 hklog hfi hfi1 hθ hin
  refine ⟨h1, fun hne => h2 _ _ hne hNC ?_⟩
  have hp := (inference_negative_control hθ hin hfi hfi0 hz0).2.2.2.1
  have he := (integrable_eFn' hθ hin hfi).pos_part.div_const
    (∫ x, max (eFlow ν θ f_init x) 0 ∂ν)
  rw [eFn_eq_eFlow] at he
  rw [GFNBounds.Core.tvD_comm ν k]
  exact GFNBounds.Core.tvD_triangle (hp.sub he) (he.sub hk)

/-- **`theo:IL_CV_bound`, first bullet, on a general measurable space, with nothing external**:
`𝓛^q ≥ 𝓗`, and where the loss is finite
`TV(s_τ ‖ κ) ≤ (1/√2)√(𝓛 − 𝓗) + min(1, ‖dν_B/dν_T‖_{L^{q*}(ν_T)}(𝓛 − 𝓗))`, with `s_τ` the
output of the inference sampler from `F_init` to `κ̂ = E⁺`, which stops almost surely and whose
law is a probability `≪ ν_B` with density `samplerDens`. -/
theorem il_first_bullet_general [SigmaFinite ν] [SigmaFinite νT] {q qstar : ℝ≥0∞}
    [ENNReal.HolderConjugate qstar q] (hνT : ν ≪ νT)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT) {b : ℝ}
    (hb : 1 + rnNorm ν νT qstar ≤ b)
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (hfi : Integrable f_init ν) (hfi1 : ∫ x, f_init x ∂ν = 1) (hfi0 : 0 ≤ᵐ[ν] f_init)
    (hθ : IsGenerativeFlow ν θ) (hin : InflowAC ν θ) :
    Tendsto (infFlow ν θ f_init).tailProb atTop (𝓝 0) ∧
    (infFlow ν θ f_init).sampleLaw Set.univ = 1 ∧
    (infFlow ν θ f_init).sampleLaw ≪ ν ∧
    ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) ≤ ilLoss ν νT q b k (eFlow ν θ f_init) ∧
    (ilLoss ν νT q b k (eFlow ν θ f_init) ≠ ⊤ →
      GFNBounds.Core.tvD ν (samplerDens ν θ f_init) k
        ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLossE ν νT q b k (eFlow ν θ f_init)
              - GFNBounds.Core.selfEntropy ν k)
          + min 1 (rnNorm ν νT qstar * (wklfmLossE ν νT q b k (eFlow ν θ f_init)
              - GFNBounds.Core.selfEntropy ν k))) := by
  have hz0 : 0 < ∫ x, f_init x ∂ν := by rw [hfi1]; exact one_pos
  obtain ⟨h1, h2, h3, -, hNC⟩ := inference_negative_control hθ hin hfi hfi0 hz0
  rw [eFn_eq_eFlow] at hNC
  exact ⟨h1, h2, h3, il_first_bullet_general_hNC (q := q) hνT hr hb hk hk1 hk0 hklog hfi hfi1 hfi0 hθ hin
    hNC⟩

end IL

end Inference

/-! ### Inhabitation (kb `0025`, `0027`): the i.i.d. resampling flow on any probability space -/

namespace Resample

open GFNBounds.Core.Family GFNBounds.Core.RLBound GFNBounds.Core.ILBoundFull

variable (ν : Measure α) [IsProbabilityMeasure ν] (c : ℝ)

/-- The flow `(π⋆, f⋆_out) = (x ↦ ν, c)`. -/
noncomputable def theta : Kernel α α × (α → ℝ) := (Kernel.const α ν, fun _ => c)

theorem isGenerativeFlow (hc : 0 ≤ c) : IsGenerativeFlow ν (theta ν c) where
  markov := by unfold theta; infer_instance
  nonneg _ := hc
  integrable := integrable_const c

theorem bind_ac : ν.bind ⇑(theta ν c).1 ≪ ν := by
  unfold theta; rw [bind_const_kernel]

/-- With `F_init = 1`, `E = F_init + F⋆_← − F⋆_out = 1` a.e. -/
theorem eFn_ae : eFn ν (theta ν c) (fun _ => 1) =ᵐ[ν] fun _ => 1 := by
  filter_upwards [densityAction_const_kernel (ν := ν) (integrable_const c)] with x hx
  simp only [eFn, theta] at hx ⊢
  rw [hx, integral_const, probReal_univ, one_smul]
  ring

/-- **`stable_bound_general` is inhabited**, on every probability space and for every outflow
level `c ≥ 0`: `F_init = κ = ν`, the resampling policy, `ν_T = ν`. -/
theorem stable_bound_general_inhabited (hc : 0 ≤ c) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    Tendsto (infFlow ν (theta ν c) fun _ => 1).tailProb atTop (𝓝 0) ∧
    (infFlow ν (theta ν c) fun _ => 1).sampleLaw Set.univ = 1 ∧
    (infFlow ν (theta ν c) fun _ => 1).sampleLaw ≪ ν ∧
    GFNBounds.Core.tvD ν (samplerDens ν (theta ν c) fun _ => 1) (fun _ => 1 / ∫ _, (1 : ℝ) ∂ν)
      ≤ GFNBounds.Core.stableConst ν 1 q.toReal (∫ _, (1 : ℝ) ∂ν)
        * (eLpNorm (defectFn ν (theta ν c) (fun _ => 1) fun _ => 1) q ν).toReal ∧
    |(∫ _, (1 : ℝ) ∂ν) - ∫ _, (1 : ℝ) ∂ν|
      ≤ GFNBounds.Core.holderConst ν 1 q.toReal
        * (eLpNorm (defectFn ν (theta ν c) (fun _ => 1) fun _ => 1) q ν).toReal := by
  have hmem : MemLp (defectFn ν (theta ν c) (fun _ => 1) fun _ => 1) q ν := by
    refine (memLp_const (0 : ℝ)).ae_eq ?_
    filter_upwards [eFn_ae ν c] with x hx
    rw [defectFn_eq_eFn_sub, hx]; ring
  have h1 : (0 : ℝ) < ∫ _, (1 : ℝ) ∂ν := by simp
  exact stable_bound_general (M := 1) (by simp) hq (isGenerativeFlow ν c hc) (bind_ac ν c)
    (integrable_const _) (Filter.Eventually.of_forall fun _ => zero_le_one) (integrable_const _)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hmem h1 h1

/-- The resampling flow has finite KL-weak-FM loss (`LossFinite`), so the TV clause of
`il_first_bullet_general` is not vacuous on it. -/
theorem lossFinite {q : ℝ≥0∞} :
    LossFinite ν ν q (fun _ => 1) (eFlow ν (theta ν c) fun _ => 1) := by
  have he : eFlow ν (theta ν c) (fun _ => 1) =ᵐ[ν] fun _ => 1 := by
    rw [← eFn_eq_eFlow]; exact eFn_ae ν c
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [he] with x hx h
    rw [hx] at h; norm_num at h
  · refine (integrable_const (0 : ℝ)).congr ?_
    filter_upwards [he] with x hx
    rw [hx]; simp
  · refine (memLp_const (0 : ℝ)).ae_eq ?_
    filter_upwards [he] with x hx
    rw [hx]; norm_num

/-- **`il_first_bullet_general` is inhabited, with its TV clause live**: on every probability
space, `F_init = κ = ν`, the resampling policy with outflow `c ≥ 0`, `ν_T = ν`, `q = 1`. -/
theorem il_first_bullet_general_inhabited (hc : 0 ≤ c) :
    ilLoss ν ν 1 (1 + rnNorm ν ν ⊤) (fun _ => 1) (eFlow ν (theta ν c) fun _ => 1) ≠ ⊤ ∧
    GFNBounds.Core.tvD ν (samplerDens ν (theta ν c) fun _ => 1) (fun _ => 1)
      ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLossE ν ν 1 (1 + rnNorm ν ν ⊤) (fun _ => 1)
            (eFlow ν (theta ν c) fun _ => 1) - GFNBounds.Core.selfEntropy ν fun _ => 1)
        + min 1 (rnNorm ν ν ⊤ * (wklfmLossE ν ν 1 (1 + rnNorm ν ν ⊤) (fun _ => 1)
            (eFlow ν (theta ν c) fun _ => 1) - GFNBounds.Core.selfEntropy ν fun _ => 1)) := by
  have hne : ilLoss ν ν 1 (1 + rnNorm ν ν ⊤) (fun _ => 1) (eFlow ν (theta ν c) fun _ => 1)
      ≠ ⊤ := by
    rw [ilLoss_of_finite (lossFinite ν c)]; exact EReal.coe_ne_top _
  have hr : MemLp (fun x => (ν.rnDeriv ν x).toReal) ⊤ ν := by
    refine (memLp_const (1 : ℝ)).ae_eq ?_
    filter_upwards [Measure.rnDeriv_self ν] with x hx
    rw [hx]; simp
  have h := il_first_bullet_general (q := 1) (qstar := ⊤) (ν := ν) (νT := ν)
    (Measure.AbsolutelyContinuous.refl ν) hr le_rfl (integrable_const _) (by simp)
    (Filter.Eventually.of_forall fun _ => zero_le_one) (by simp) (integrable_const _) (by simp)
    (Filter.Eventually.of_forall fun _ => zero_le_one) (isGenerativeFlow ν c hc)
    (inflowAC_of_bind_ac (bind_ac ν c))
  exact ⟨hne, h.2.2.2.2 hne⟩

end Resample

end GFNBounds.Core.SamplingGeneral
