import GFNBounds.Balance.FreezingGeneral2
import GFNBounds.Core.FirstVariationGeneral
import GFNBounds.Balance.RemarksA

/-!
# The freezing and dichotomy group with `D` read as the gradient

**`prop:nonlinear_freezing`** — `proofs.tex`, the proposition carrying that label;
**`prop:no_distant_equilibrium`** — `proofs.tex`, the proposition carrying that label;
**`theo:global_dichotomy_full`** — `proofs.tex`, the theorem carrying that label;
**`theo:global_dichotomy`** — `cv_divergence.tex`, its body twin;
**`rem:freezing`** — `proofs.tex`, the remark carrying that label.
(Line numbers drift, kb 0036; the labels are the anchors.)

`GFNBounds/Balance/FreezingGeneral2.lean` proves the general-space items of these statements with
`D = Tφ − rφ` (`gradDensityG`) read as a **definition**, "critical" read as `D = 0`, and the
first variation entering only as the named, uninhabited hypothesis `FirstVariationFull`. The
general first variation is now proved (`GFNBounds/Core/FirstVariationGeneral.lean`,
theo:first_variation_full, closed in A). This file composes the two: `D` **is** the `λ`-density
of `∇^λ_μ𝓛_{g,ν}`, "critical" is read in the derivative sense of the paper, and the named
hypothesis is discharged.

> (`prop:nonlinear_freezing`*(1)*) for every `g̃ : ℝ₊* → ℝ` continuously differentiable with
> locally Lipschitz derivative, positive on `U⁻ ∪ U⁺` and with `g̃' ≡ 0` there, `g` included, and
> every ergodic `(𝒮̂, λ, T)`, every `μ` whose ratio `r = d(μT)/dμ` takes values in `U⁻ ∪ U⁺`
> `λ`-almost everywhere is a critical point of `𝓛_{g̃,ν}` for *every* training measure `ν`; […]

> (`prop:nonlinear_freezing`*(3)*) […] then on the set of flows `μ = (1+h)λ` with
> `‖h‖_{L^∞(λ)} ≤ 1/2` whose ratio takes values in `U⁻ ∪ U⁺` `λ`-almost everywhere, the gradient
> `∇^λ𝓛_{g̃,ν}` has norm at most `C'ε` in `𝓜²(λ)`, so a trajectory of the gradient flow moves a
> distance `η` in `𝓜²(λ)` in a time at least `η/(C'ε)` while it remains in that set.

> (`prop:no_distant_equilibrium`*(1)*) For any `ν` with `dν/dμ > 0` `μ`-a.e., the total mass of
> `∇^λ𝓛_{g,ν}(μ)` is `∫ g'(r)(1−r)(dν/dμ) dλ ≤ 0`, with equality if and only if `μ` is balanced.
> Every critical point of `𝓛_{g,ν}` is therefore balanced […]
> *(2)* For fixed `ν = wλ` the loss is scale-invariant, so the gradient flow preserves
> `‖u_t‖_{L²(λ)}`, while by *(1)* the total mass `μ_t(𝒮̂)` strictly increases off balance:
> training is a monotone ascent of the mass on a sphere of `𝓜²(λ)`, whose unique maximizer
> (Cauchy–Schwarz) is the balanced flow. […]

> (`theo:global_dichotomy_full`) *(1)* If `g` is strictly unimodal […] then the total mass of
> `∇^λ𝓛_{g,ν}` equals `∫ g'(r)(1−r)(dν/dμ) dλ ≤ 0`, with equality only at balance: *every critical
> point of `𝓛_{g,ν}` is balanced*, for every training measure with positive density, on every
> graph, cycles included. […] *(2)* If instead `g'` vanishes on bands on either side of `1`, then
> every flow with band-valued ratios is a critical point of `𝓛_{g,ν}` for *every* `ν`; […]

> (`rem:freezing`*(iv)*) For every admissible differentiable strictly unimodal generator, every
> critical point of `𝓛_{g,ν}` is balanced when `ν` has positive density […]
> *(ii)* Every admissible generator `C³` on `[1,1+δ]` with `g''(1)=2` and `g'≡0` on
> `[1+δ,1+2δ]` […] whence `sup_{[1,1+δ]}|g'''| ≥ 4/δ` […]

## The reading

| paper | here |
|---|---|
| a direction admissible in theo:first_variation_full: `δ ≪ μ`, `‖dδ/dμ‖_{L^∞(μ)} < 1`, `d(δT)/dμ ∈ L^∞(μ)` | `AdmissibleDir T μ u`, `u = dδ/dμ`; `μ + sδ` is `FirstVariation.perturb μ u s` (`perturb_toSignedMeasure`) |
| `D` is the `λ`-density of `∇^λ_μ𝓛_{g,ν}` (theo:first_variation_full at `ν_G = λ`) | `IsGradDensity T lam ν μ g D`: `D ∈ L²(λ)` and `d/ds|₀𝓛(μ+sδ) = ⟨D, dδ/dλ⟩_{L²(λ)}` along every admissible `δ` |
| `μ` is a critical point of `𝓛_{g,ν}` | `IsCriticalG T ν μ g`: every admissible directional derivative exists and is `0` |
| the gradient flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` | `IsGradientFlowPaper`: `u̇_t = −D_t` in `L²(λ)` for `t ≥ 0` (two-sided derivative at `0`, the convention of `IsGradientFlow` since 2026-09-14; a paper flow with only a right derivative at `0` becomes one by extending it linearly to `t < 0`, not formalized), `D_t` **a** gradient density of `μ_t` (no formula) |

## What is proved

| paper | here |
|---|---|
| `D = Tφ − rφ` is the gradient density, and the only one | `gradDensityG_isGradDensity`, `isGradDensity_unique` (through `hasDerivAt_loss_gradDens`, `representative_unique`) |
| critical ⟺ `D = 0` (no constant direction, no lower bound on `dμ/dλ`) | `isCriticalG_iff` |
| no_distant *(1)*: every gradient density has mass `∫g'(r)(1−r)(dν/dμ)dλ ≤ 0`, `= 0` iff balanced; critical ⟹ balanced | `no_distant_equilibrium_one_bridge` |
| no_distant *(2)*, static: scale invariance, `⟨D, u⟩ = 0` for every gradient density, Cauchy–Schwarz maximizer | `no_distant_equilibrium_two_bridge` (standard Borel: the reversal is `Core.General.reversal`) |
| no_distant *(2)*, flow: for the paper's flow | `no_distant_equilibrium_two_flow_bridge`, via `isGradientFlowPaper_iff` |
| freezing *(1)*: band-valued ⟹ critical for every `ν` | `nonlinear_freezing_one_critical` (any Markov `T`, every finite `ν ≪ μ`); with the gradient: `nonlinear_freezing_one_bridge` |
| freezing *(3)*: the gradient exists on the set, every density of it has norm `≤ C'ε`; the paper's flow moves `≤ C'ετ` | `nonlinear_freezing_three_bridge` (`setting_pertG` derives the first-variation hypotheses from the set) |
| dichotomy *(1)* first sentence, *(2)* first clause | `global_dichotomy_full_bridge` |
| body twin; rem *(i)*, *(iv)* critical-point sentence | `freezing_remark_four_bridge` |
| `FirstVariationFull` (the named hypothesis of `FreezingGeneral2`) | **discharged**: `firstVariationFull_of_setting` on the admissible cone `AdmL`; `isCriticalAlong_iff`; `balanced_of_isCriticalAlong_bridge` needs no constant direction |
| rem *(ii)*: `C³` on `[1,1+δ]` ⟹ `sup|g'''| ≥ 4/δ` | `third_deriv_sSup_of_C3`: `C³` read with `g₃` continuous on the closed interval, so the supremum is finite by compactness and `RemarksA.third_deriv_sSup`'s `BddAbove` is discharged |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the hypotheses under which `∇^λ𝓛_{g,ν}(μ)` exists (theo:first_variation_full: `μ ∼ λ`, `dμ/dλ ∈ L²(λ)`, `r` essentially in `[ρ₀, ρ₁] ⊂ (0,∞)`, `ν` finite, `dν/dμ ∈ L^∞(μ)`, `g ∈ C¹`) | ⚠ presupposed: the paper prints `g` only differentiable (no_distant preamble, dichotomy *(1)*, rem *(iv)*); `g'` continuous enters because `∇^λ𝓛` is defined only by theo:first_variation_full. `FirstVariationSetting` + `[IsFiniteMeasure ν]` + `hgd : ∀ y > 0, HasDerivAt g (gd y) y` (`gd` continuous on `ℝ₊*` is in the bundle). **Not printed** in no_distant *(1)* / dichotomy *(1)*: the statements speak of "the total mass of `∇^λ𝓛_{g,ν}(μ)`", which exists under these; see SCOPE |
| `g'` locally Lipschitz | ⚠ **weakened**: neither carried nor used (the derivative clauses of theo:first_variation_full need `C¹` only) |
| `(𝒮̂, λ, T)` ergodic | ⚠ **weakened** to invariance (`IsInvariant T lam`) everywhere except the maximizer clause, which carries `ErgodicG`; `nonlinear_freezing_one_critical` needs no invariant measure at all |
| `𝒮̂` Polish | ✓ `no_distant_equilibrium_two_bridge` carries `[StandardBorelSpace S] [Nonempty S]` and builds the reversal; `no_distant_equilibrium_two_flow_bridge` takes a λ-reversal as the hypothesis `IsReversalPair lam T R`, supplied on a standard Borel space by `IsInvariant.isReversalPair_reversal`; everything else holds on any measurable space |
| "every training measure `ν`" (freezing *(1)*, dichotomy *(2)*) | ✓ read as every finite `ν ≪ μ` (`ν ≪ μ ∼ λ`, so that `𝓛_{g̃,ν} = ∫ g̃(r) dν` depends on `r` only through its `μ`-class); `dν/dμ ∈ L^∞` is not needed |
| `g̃` positive on the bands (freezing *(1)*) | used only by the finite-space half (`FreezingGeneral.lean`); criticality does not use it |
| freezing *(3)*: `λ` probability, `ν = wλ`, `w ∈ L^∞`, `w ≥ 0`, `‖h‖_∞ ≤ ½`, `|g̃'| ≤ ε` on the bands | ✓ carried; `w`, `h` measurable |
| dichotomy *(2)*: `g'` vanishes on bands (no regularity printed) | ⚠ presupposed: `g` differentiable on `ℝ₊*` with `g'` continuous there, the hypothesis of prop:nonlinear_freezing *(1)*, which the proof cites |
| `C³` on `[1, 1+δ]` (rem *(ii)*) | ✓ `g → g₁ → g₂ → g₃` derivatives within the interval, `g₃` continuous there; ⚠ presupposed: `g` differentiable at `1` (`hd0`), which the remark's own `g'(1) = 0` needs; `C³` on `[1,1+δ]` gives only a right derivative there |

Inhabited off balance (kb 0025, 0027), on `Bool` with the resampling kernel:
`bool_critical_unbalanced` (a critical point that is not balanced, gradient `0`),
`bool_not_critical` (for `(x−1)²` the gradient exists and the unbalanced flow is not critical),
`bool_paper_flow` (the constant curve at a frozen flow is an `IsGradientFlowPaper`), and
`bool_unimodal_flow` — a **non-constant** `IsGradientFlowPaper` of `(x−1)²` from the unbalanced
`(3/2, 1/2)·π`, meeting the first-variation hypotheses at every `t ≥ 0`, with strictly increasing
mass at `t = 0` (the finite solution `twoState_flow_exists_check_sq` transported to `L²(π)` by
`boolLp`).

## SCOPE (disclosed)

* **The first-variation hypotheses are carried by no_distant *(1)* and dichotomy *(1)*, and by no_distant *(2)*'s flow half at every `t ≥ 0` (`hset` of `no_distant_equilibrium_two_flow_bridge`), which do
  not print them.** "The total mass of `∇^λ𝓛_{g,ν}(μ)`" presupposes that the gradient exists,
  and theo:first_variation_full gives it under `r` essentially bounded away from `0` and `∞`,
  `dν/dμ ∈ L^∞(μ)`, `g ∈ C¹`; outside those the gradient is not defined and the sentence has no
  content. The Lean carries them (`FirstVariationSetting`), as the paper's proof uses them
  ("the gradient density is `D = P†φ − rφ`").
* **The gradient flow on a general space is hypothesised, as in the paper** (existence is claimed
  only on finite state spaces, closed in `Balance/FlowExistence.lean`). `IsGradientFlowPaper` asks
  `u̇_t = −D_t` in `L²(λ)` for `t ≥ 0` (two-sided derivative at `0`, the convention of `IsGradientFlow` since 2026-09-14; a paper flow with only a right derivative at `0` becomes one by extending it linearly to `t < 0`, not formalized). Its predicate is now
  inhabited off balance by a non-constant solution with a strictly unimodal generator
  (`bool_unimodal_flow`).
* **The finite-space half of freezing *(1)*** (open set, locally constant, positive loss) and
  items *(2)*, the last assertion, and no_distant *(3)* stay where they are proved
  (`FreezingGeneral.lean`, `Freezing.lean`, `WeightedL2Norm.lean`, `FreezingGeneral2.lean`,
  `GlobalConvergenceFinite.lean`); nothing here restates them.
* **`rem:freezing`'s "admissible"** stays narrowed as in `RemarksA.lean` (`g(1) = 0`, `g > 0` off
  `1`); fewer conditions on the generator make those statements stronger, not weaker.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GFNBounds.Balance.General.Bridge

open GFNBounds.Core.General (IsInvariant IsReversalPair)

variable {S : Type*} [MeasurableSpace S]

/-! ### The two libraries name the same objects -/

theorem ratioG_eq_ratio (T : Kernel S S) (μ : Measure S) :
    ratioG T μ = Core.General.FirstVariation.ratio T μ := rfl

theorem gradDensityG_eq_gradDens (T : Kernel S S) (μ ν : Measure S) (gd : ℝ → ℝ) :
    gradDensityG T μ ν gd = Core.General.FirstVariation.gradDens T gd ν μ := rfl

theorem lossG_eq_loss (T : Kernel S S) (ν : Measure S) (g : ℝ → ℝ) (μ : Measure S) :
    lossG T ν g μ = Core.General.FirstVariation.loss T g ν μ := rfl

/-! ### The paper's notions -/

/-- **A direction admissible in `theo:first_variation_full`**, given by its density `u = dδ/dμ`:
`δ ≪ μ` with `‖dδ/dμ‖_{L^∞(μ)} < 1` and `d(δT)/dμ ∈ L^∞(μ)` (the last is automatic when `r` is
essentially bounded: `Core.General.FirstVariation.abs_dirPush_le`, `|d(δT)/dμ| ≤ ‖u‖_∞·r`;
`admissibleDir_of_abs_le` packages the case `|u| ≤ ½`). The flow `μ + sδ` is `Core.General.FirstVariation.perturb μ u s`. -/
def AdmissibleDir (T : Kernel S S) (μ : Measure S) (u : S → ℝ) : Prop :=
  Measurable u ∧ eLpNorm u ⊤ μ < 1 ∧ MemLp (Core.General.FirstVariation.dirPush T μ u) ⊤ μ

/-- **`D` is the `λ`-density of `∇^λ_μ𝓛_{g,ν}`**: `D ∈ L²(λ)` and, along every admissible
direction `δ = uμ`, `d/ds|₀ 𝓛_{g,ν}(μ + sδ) = ⟨D, dδ/dλ⟩_{L²(λ)}`, `dδ/dλ = u·dμ/dλ`
(`theo:first_variation_full` at `ν_G = λ`). -/
def IsGradDensity (T : Kernel S S) (lam ν μ : Measure S) (g : ℝ → ℝ) (D : S → ℝ) : Prop :=
  MemLp D 2 lam ∧ ∀ u : S → ℝ, AdmissibleDir T μ u →
    HasDerivAt (fun s => Core.General.FirstVariation.loss T g ν (Core.General.FirstVariation.perturb μ u s))
      (∫ x, D x * (u x * (μ.rnDeriv lam x).toReal) ∂lam) 0

/-- **`μ` is a critical point of `𝓛_{g,ν}`**: the derivative of `s ↦ 𝓛_{g,ν}(μ + sδ)` at `0`
exists and vanishes along every admissible direction. -/
def IsCriticalG (T : Kernel S S) (ν μ : Measure S) (g : ℝ → ℝ) : Prop :=
  ∀ u : S → ℝ, AdmissibleDir T μ u → HasDerivAt (fun s => Core.General.FirstVariation.loss T g ν (Core.General.FirstVariation.perturb μ u s)) 0 0

section Admissible

variable {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S}

omit [IsMarkovKernel T] in
theorem ae_abs_le_one_of_admissible {u : S → ℝ} (hu : AdmissibleDir T μ u) :
    ∀ᵐ x ∂μ, |u x| ≤ 1 := by
  have h := hu.2.1
  rw [eLpNorm_exponent_top] at h
  filter_upwards [ae_le_eLpNormEssSup (f := u) (μ := μ)] with x hx
  have h1 : ‖u x‖ₑ < 1 := lt_of_le_of_lt hx h
  rw [Real.enorm_eq_ofReal_abs] at h1
  exact (ENNReal.ofReal_lt_one.1 h1).le

/-- The directions `|dδ/dμ| ≤ ½` are admissible when `r ≤ b`: `‖·‖_∞ ≤ ½ < 1`, and
`|d(δT)/dμ| ≤ ½·r ≤ b/2`. -/
theorem admissibleDir_of_abs_le [IsFiniteMeasure μ] {b : ℝ}
    (hrb : ∀ᵐ x ∂μ, Core.General.FirstVariation.ratio T μ x ≤ b) {u : S → ℝ}
    (hu : Measurable u) (hub : ∀ᵐ x ∂μ, |u x| ≤ 1 / 2) : AdmissibleDir T μ u := by
  refine ⟨hu, ?_, ?_⟩
  · rw [eLpNorm_exponent_top]
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (C := 1 / 2) ?_) ?_
    · filter_upwards [hub] with x hx; rwa [Real.norm_eq_abs]
    · exact ENNReal.ofReal_lt_one.2 (by norm_num)
  · refine MemLp.of_bound (Core.General.FirstVariation.measurable_dirPush u).aestronglyMeasurable
      (1 / 2 * b) ?_
    filter_upwards [Core.General.FirstVariation.abs_dirPush_le (T := T) hu (by norm_num) hub, hrb]
      with x h1 h2
    rw [Real.norm_eq_abs]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))

end Admissible

/-! ### `D = Tφ − rφ` is the `λ`-gradient, and critical means `D = 0` -/

section Gradient

variable {T : Kernel S S} [IsMarkovKernel T] {lam μ ν : Measure S} [IsFiniteMeasure lam]
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g gd : ℝ → ℝ}

omit [IsMarkovKernel T] [IsFiniteMeasure lam] [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem ratio_Icc_of_setting (h : FirstVariationSetting T lam μ ν gd) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ᵐ x ∂μ, a ≤ Core.General.FirstVariation.ratio T μ x ∧
      Core.General.FirstVariation.ratio T μ x ≤ b := by
  obtain ⟨ρ₀, ρ₁, hρ₀, hr⟩ := h.ratio_bdd
  exact ⟨ρ₀, max ρ₀ ρ₁, hρ₀, le_max_left _ _, by
    filter_upwards [hr] with x hx using ⟨hx.1, hx.2.trans (le_max_right _ _)⟩⟩

/-- **`theo:first_variation_full` at `ν_G = λ`, read for `D = Tφ − rφ`**: under the
first-variation hypotheses (`FirstVariationSetting`, and `g` differentiable on `ℝ₊*` with
derivative `gd`), `gradDensityG` **is** the `λ`-density of `∇^λ_μ𝓛_{g,ν}`. -/
theorem gradDensityG_isGradDensity (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) :
    IsGradDensity T lam ν μ g (gradDensityG T μ ν gd) := by
  obtain ⟨a, b, ha, hab, hr⟩ := ratio_Icc_of_setting h
  obtain ⟨W, hW⟩ := h.dens_bdd
  have hW' : ∀ᵐ x ∂μ, |(ν.rnDeriv μ x).toReal| ≤ W := by
    filter_upwards [hW] with x hx; rwa [abs_of_nonneg ENNReal.toReal_nonneg]
  have hac : T ∘ₘ μ ≪ μ := comp_absolutelyContinuous_self hinv h.ac h.ac'
  refine ⟨(hinv.memLp_funAct one_le_two (h.memLp_pot hinv 2)).sub (h.memLp_rpot hinv 2),
    fun u hu => ?_⟩
  have key := Core.General.FirstVariation.hasDerivAt_loss_gradDens (T := T) h.nu_ac hW' hac ha
    hab hr hgd h.gd_cont hu.1 zero_le_one (ae_abs_le_one_of_admissible hu)
  convert key using 1
  rw [← integral_rnDeriv_smul h.ac]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, gradDensityG_eq_gradDens]
  ring

/-- **The `λ`-gradient density is unique** (`representative_unique` at `ν_G = λ`): any `L²(λ)`
function representing the derivative along the admissible directions is `gradDensityG`,
`λ`-a.e. -/
theorem isGradDensity_unique (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd)
    (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) {D : S → ℝ}
    (hD : IsGradDensity T lam ν μ g D) : D =ᵐ[lam] gradDensityG T μ ν gd := by
  have hG := gradDensityG_isGradDensity hinv h hgd
  obtain ⟨a, b, -, -, hr⟩ := ratio_Icc_of_setting h
  have hrb : ∀ᵐ x ∂μ, Core.General.FirstVariation.ratio T μ x ≤ b := by
    filter_upwards [hr] with x hx using hx.2
  refine Core.General.FirstVariation.representative_unique h.ac h.ac' hD.1 hG.1
    (fun u hu hub => ?_)
  have hA := admissibleDir_of_abs_le (T := T) hrb hu hub
  exact (hD.2 u hA).unique (hG.2 u hA)

/-- **Critical ⟺ `D = 0`**: `μ` is a critical point of `𝓛_{g,ν}` in the derivative sense (every
admissible directional derivative vanishes) iff `D = Tφ − rφ = 0` `λ`-a.e. No constant direction,
and no lower bound on `dμ/dλ`, is asked. -/
theorem isCriticalG_iff (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd)
    (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) :
    IsCriticalG T ν μ g ↔ gradDensityG T μ ν gd =ᵐ[lam] 0 := by
  constructor
  · intro hc
    have h0 : IsGradDensity T lam ν μ g (fun _ => 0) :=
      ⟨memLp_const 0, fun u hu => by simpa using hc u hu⟩
    exact (isGradDensity_unique hinv h hgd h0).symm
  · intro hD u hu
    have := (gradDensityG_isGradDensity hinv h hgd).2 u hu
    rwa [integral_eq_zero_of_ae (by filter_upwards [hD] with x hx; simp [hx])] at this

end Gradient

/-! ### The rows, with `D` read as the gradient and "critical" in the derivative sense -/

section Rows

variable {T : Kernel S S} [IsMarkovKernel T] {lam μ ν : Measure S} [IsFiniteMeasure lam]
  [IsFiniteMeasure μ] {g gd : ℝ → ℝ}

/-- **`prop:no_distant_equilibrium`*(1)*, with the gradient**: under the hypotheses of
`theo:first_variation_full` at `μ` (with `ν_G = λ`), `g` differentiable on `ℝ₊*` with derivative
`gd` strictly unimodal, and `dν/dμ > 0` `μ`-a.e.: `∇^λ_μ𝓛_{g,ν}` exists (its density is
`D = Tφ − rφ`); **every** `λ`-density `D'` of it has total mass
`∫ D' dλ = ∫ g'(r)(1 − r)(dν/dμ) dλ ≤ 0`, vanishing iff `μ` is balanced; and every critical point of
`𝓛_{g,ν}` (all admissible directional derivatives zero) is balanced. -/
theorem no_distant_equilibrium_one_bridge [IsFiniteMeasure ν] (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y)
    (hg : StrictlyUnimodal gd) (hν : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal) :
    IsGradDensity T lam ν μ g (gradDensityG T μ ν gd)
      ∧ (∀ D : S → ℝ, IsGradDensity T lam ν μ g D →
          ∫ x, D x ∂lam
              = ∫ x, gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal ∂lam
            ∧ ∫ x, D x ∂lam ≤ 0
            ∧ (∫ x, D x ∂lam = 0 ↔ BalancedG T μ))
      ∧ (IsCriticalG T ν μ g → BalancedG T μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := no_distant_equilibrium_one_general hinv h hg hν
  refine ⟨gradDensityG_isGradDensity hinv h hgd, fun D hD => ?_, fun hc => ?_⟩
  · have e : ∫ x, D x ∂lam = ∫ x, gradDensityG T μ ν gd x ∂lam :=
      integral_congr_ae (isGradDensity_unique hinv h hgd hD)
    rw [e]
    exact ⟨h1, h2, h3⟩
  · exact h4 ((isCriticalG_iff hinv h hgd).1 hc)

omit [IsFiniteMeasure lam] in
/-- **`prop:nonlinear_freezing`*(1)*, criticality in the derivative sense**: for every `g̃`
differentiable on `ℝ₊*` with derivative `g̃'` continuous there and `g̃' ≡ 0` on the bands, and every
Markov kernel `T`, a finite `μ ≪ λ` whose ratio is band-valued `λ`-a.e. is a critical point of
`𝓛_{g̃,ν}` — every admissible directional derivative exists and vanishes — for **every** finite
training measure `ν ≪ μ`. Neither invariance, ergodicity, `dν/dμ ∈ L^∞` nor positivity of `g̃` on
the bands is used. -/
theorem nonlinear_freezing_one_critical (F : FreezingBands)
    (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) (hgc : ContinuousOn gd (Set.Ioi 0))
    (hgd0 : ∀ z ∈ F.bands, gd z = 0) (hml : μ ≪ lam)
    (hband : ∀ᵐ x ∂lam, ratioG T μ x ∈ F.bands) (ν : Measure S) [IsFiniteMeasure ν]
    (hνμ : ν ≪ μ) : IsCriticalG T ν μ g := by
  have hbandμ : ∀ᵐ x ∂μ, ratioG T μ x ∈ F.bands := hml.ae_le hband
  have had : F.a ≤ F.d :=
    (F.a_lt_b.trans (F.b_lt_one.trans (F.one_lt_c.trans F.c_lt_d))).le
  have hr : ∀ᵐ x ∂μ, F.a ≤ Core.General.FirstVariation.ratio T μ x ∧
      Core.General.FirstVariation.ratio T μ x ≤ F.d := by
    filter_upwards [hbandμ] with x hx
    rcases hx with hx | hx
    · exact ⟨hx.1.le, (hx.2.trans (F.b_lt_one.trans (F.one_lt_c.trans F.c_lt_d))).le⟩
    · exact ⟨(F.a_lt_b.trans (F.b_lt_one.trans (F.one_lt_c.trans hx.1))).le, hx.2.le⟩
  intro u hu
  have key := Core.General.FirstVariation.hasDerivAt_loss_perturb (T := T) hνμ hu.1 F.a_pos had
    zero_le_one (ae_abs_le_one_of_admissible hu) hr hgd hgc
  have h0 : ∫ x, gd (Core.General.FirstVariation.ratio T μ x) *
      (Core.General.FirstVariation.dirPush T μ u x -
        Core.General.FirstVariation.ratio T μ x * u x) ∂ν = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hνμ.ae_le hbandμ] with x hx
    have : gd (Core.General.FirstVariation.ratio T μ x) = 0 := hgd0 _ hx
    simp [this]
  rwa [h0] at key

/-- **`prop:nonlinear_freezing`*(1)*, with the gradient**: in addition, under the first-variation
hypotheses at `μ` the `λ`-gradient of `𝓛_{g̃,ν}` exists and its density is `0`, for every `ν`
meeting them. -/
theorem nonlinear_freezing_one_bridge (F : FreezingBands) (hinv : IsInvariant T lam)
    (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) (hgc : ContinuousOn gd (Set.Ioi 0))
    (hgd0 : ∀ z ∈ F.bands, gd z = 0) (hml : μ ≪ lam)
    (hband : ∀ᵐ x ∂lam, ratioG T μ x ∈ F.bands) :
    (∀ (ν : Measure S) [IsFiniteMeasure ν], ν ≪ μ → IsCriticalG T ν μ g)
      ∧ (∀ ν : Measure S, gradDensityG T μ ν gd =ᵐ[lam] 0)
      ∧ (∀ (ν : Measure S) [IsFiniteMeasure ν], FirstVariationSetting T lam μ ν gd →
          IsGradDensity T lam ν μ g (fun _ => 0)) := by
  refine ⟨fun ν _ hνμ => nonlinear_freezing_one_critical F hgd hgc hgd0 hml hband ν hνμ,
    fun ν => gradDensityG_eq_zero_of_band hinv hband hgd0 ν, fun ν _ h => ?_⟩
  have hG := gradDensityG_isGradDensity hinv h hgd
  have hz := gradDensityG_eq_zero_of_band hinv hband hgd0 ν
  refine ⟨memLp_const 0, fun u hu => ?_⟩
  have := hG.2 u hu
  rwa [integral_congr_ae (by filter_upwards [hz] with x hx; simp [hx] :
    (fun x => gradDensityG T μ ν gd x * (u x * (μ.rnDeriv lam x).toReal)) =ᵐ[lam]
      fun x => (fun _ => (0 : ℝ)) x * (u x * (μ.rnDeriv lam x).toReal))] at this

/-- **`theo:global_dichotomy_full`, the general halves, with the gradient**: *(1)* for a
strictly unimodal `g` every gradient density has mass `∫ g'(r)(1 − r)(dν/dμ) dλ ≤ 0`, zero only
at balance, and every critical point of `𝓛_{g,ν}` is balanced, for every training measure with
positive density meeting the first-variation hypotheses; *(2)* if `g'` vanishes on bands on
either side of `1`, every flow with band-valued ratios is a critical point of `𝓛_{g,ν}` for
every finite `ν ≪ μ`. -/
theorem global_dichotomy_full_bridge (hinv : IsInvariant T lam) (hml : μ ≪ lam) :
    (∀ (ν : Measure S) [IsFiniteMeasure ν] (g gd : ℝ → ℝ),
        FirstVariationSetting T lam μ ν gd → (∀ y, 0 < y → HasDerivAt g (gd y) y) →
        StrictlyUnimodal gd → (∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal) →
        (∀ D : S → ℝ, IsGradDensity T lam ν μ g D →
            ∫ x, D x ∂lam
                = ∫ x, gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal ∂lam
              ∧ ∫ x, D x ∂lam ≤ 0 ∧ (∫ x, D x ∂lam = 0 ↔ BalancedG T μ))
          ∧ (IsCriticalG T ν μ g → BalancedG T μ))
      ∧ (∀ (F : FreezingBands) (g gd : ℝ → ℝ), (∀ y, 0 < y → HasDerivAt g (gd y) y) →
        ContinuousOn gd (Set.Ioi 0) → (∀ z ∈ F.bands, gd z = 0) →
        (∀ᵐ x ∂lam, ratioG T μ x ∈ F.bands) →
        ∀ (ν : Measure S) [IsFiniteMeasure ν], ν ≪ μ → IsCriticalG T ν μ g) :=
  ⟨fun _ _ _ _ h hgd hg hν =>
      let H := no_distant_equilibrium_one_bridge hinv h hgd hg hν
      ⟨H.2.1, H.2.2⟩,
    fun F _ _ hgd hgc hgd0 hband ν _ hνμ =>
      nonlinear_freezing_one_critical F hgd hgc hgd0 hml hband ν hνμ⟩

/-- **`theo:global_dichotomy`** (body) **and `rem:freezing`*(i)*, *(iv)*, the critical-point
sentence**: for an admissible differentiable strictly unimodal generator, every critical point of
`𝓛_{g,ν}` — in the derivative sense — is balanced when `ν` has positive density. -/
theorem freezing_remark_four_bridge [IsFiniteMeasure ν] (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y)
    (hg : StrictlyUnimodal gd) (hν : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal)
    (hc : IsCriticalG T ν μ g) : BalancedG T μ :=
  (no_distant_equilibrium_one_bridge hinv h hgd hg hν).2.2 hc

end Rows

/-! ### The gradient flow of the paper -/

section Flow

variable {T : Kernel S S} [IsMarkovKernel T] {lam ν : Measure S} [IsFiniteMeasure lam]
  {g gd : ℝ → ℝ}

/-- **The gradient flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` of the paper**, for `t ≥ 0`: the
`λ`-densities `u_t` of `μ_t` form a curve in `L²(λ)` whose derivative is minus **a** `λ`-density
of the gradient (`IsGradDensity`, the first-variation reading, not a formula). -/
def IsGradientFlowPaper (T : Kernel S S) (lam ν : Measure S) (g : ℝ → ℝ) (μ : ℝ → Measure S)
    (u : ℝ → Lp ℝ 2 lam) : Prop :=
  ∀ t, 0 ≤ t → (u t : S → ℝ) =ᵐ[lam] (fun x => ((μ t).rnDeriv lam x).toReal) ∧
    ∃ D : Lp ℝ 2 lam, IsGradDensity T lam ν (μ t) g D ∧ HasDerivAt u (-D) t

omit [IsMarkovKernel T] [IsFiniteMeasure lam] in
/-- A gradient density can be replaced by any `λ`-a.e. equal `L²` function. -/
theorem IsGradDensity.congr {μ : Measure S} {D D' : S → ℝ} (hD : IsGradDensity T lam ν μ g D)
    (hD' : MemLp D' 2 lam) (he : D =ᵐ[lam] D') : IsGradDensity T lam ν μ g D' := by
  refine ⟨hD', fun u hu => ?_⟩
  have := hD.2 u hu
  rwa [integral_congr_ae (by filter_upwards [he] with x hx; rw [hx] :
    (fun x => D x * (u x * (μ.rnDeriv lam x).toReal)) =ᵐ[lam]
      fun x => D' x * (u x * (μ.rnDeriv lam x).toReal))] at this

/-- **The paper's flow is `IsGradientFlowG`**, and conversely, wherever the first-variation
hypotheses hold along the curve: the two predicates differ only in naming the derivative's
density by the formula `D = Tφ − rφ` or by the first variation, and those agree
(`isGradDensity_unique`). -/
theorem isGradientFlowPaper_iff [IsFiniteMeasure ν] (hinv : IsInvariant T lam)
    (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) {μ : ℝ → Measure S} {u : ℝ → Lp ℝ 2 lam}
    (hfin : ∀ t, IsFiniteMeasure (μ t))
    (hset : ∀ t, 0 ≤ t → FirstVariationSetting T lam (μ t) ν gd) :
    IsGradientFlowPaper T lam ν g μ u ↔ IsGradientFlowG T lam ν gd μ u := by
  constructor
  · intro hflow t ht
    haveI := hfin t
    obtain ⟨hdens, D, hD, hder⟩ := hflow t ht
    exact ⟨hdens, D, isGradDensity_unique hinv (hset t ht) hgd hD, hder⟩
  · intro hflow t ht
    haveI := hfin t
    obtain ⟨hdens, D, hD, hder⟩ := hflow t ht
    exact ⟨hdens, D, (gradDensityG_isGradDensity hinv (hset t ht) hgd).congr (Lp.memLp D)
      hD.symm, hder⟩

/-- **`prop:no_distant_equilibrium`*(2)*, the flow, for the paper's flow**: along a gradient
flow in `𝓜²(λ)` at fixed `ν`, meeting the first-variation hypotheses at every time,
`‖u_t‖_{L²(λ)}` is constant, the mass is non-decreasing on `[0, ∞)`, and its derivative is
positive at every time off balance. -/
theorem no_distant_equilibrium_two_flow_bridge [IsFiniteMeasure ν] {R : Kernel S S}
    [IsMarkovKernel R] (hR : IsReversalPair lam T R) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y)
    (hg : StrictlyUnimodal gd) {μ : ℝ → Measure S} {u : ℝ → Lp ℝ 2 lam}
    (hflow : IsGradientFlowPaper T lam ν g μ u) (hfin : ∀ t, IsFiniteMeasure (μ t))
    (hset : ∀ t, 0 ≤ t → FirstVariationSetting T lam (μ t) ν gd) :
    (∀ t, 0 ≤ t → ‖u t‖ = ‖u 0‖)
      ∧ MonotoneOn (fun s => ∫ x, u s x ∂lam) (Set.Ici 0)
      ∧ ∀ t, 0 ≤ t → (∀ᵐ x ∂(μ t), 0 < (ν.rnDeriv (μ t) x).toReal) → ¬ BalancedG T (μ t) →
          HasDerivAt (fun s => ∫ x, u s x ∂lam) (-∫ x, gradDensityG T (μ t) ν gd x ∂lam) t
            ∧ 0 < -∫ x, gradDensityG T (μ t) ν gd x ∂lam :=
  no_distant_equilibrium_two_flow hR hg
    ((isGradientFlowPaper_iff hR.symm.isInvariant hgd hfin hset).1 hflow) hfin hset

/-- **`prop:no_distant_equilibrium`*(2)*, static half, with the gradient** (on a standard Borel
space, where the `λ`-reversal exists): the loss is scale-invariant; every `λ`-density `D` of
`∇^λ𝓛_{g,ν}(μ)` is orthogonal to the radial direction, `⟨D, u⟩_{L²(λ)} = 0`; and under
ergodicity the mass is at most `√λ(𝒮)‖u‖`, with equality iff `μ` is balanced. -/
theorem no_distant_equilibrium_two_bridge [StandardBorelSpace S] [Nonempty S]
    {μ : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) :
    (∀ c : ℝ≥0∞, c ≠ 0 → c ≠ ∞ → lossG T ν g (c • μ) = lossG T ν g μ)
      ∧ (∀ D : S → ℝ, IsGradDensity T lam ν μ g D →
          ∫ x, D x * (μ.rnDeriv lam x).toReal ∂lam = 0)
      ∧ (ErgodicG T lam → lam ≠ 0 →
          ∫ x, (μ.rnDeriv lam x).toReal ∂lam
              ≤ Real.sqrt (lam.real Set.univ * ∫ x, (μ.rnDeriv lam x).toReal ^ 2 ∂lam)
            ∧ (∫ x, (μ.rnDeriv lam x).toReal ∂lam
                = Real.sqrt (lam.real Set.univ * ∫ x, (μ.rnDeriv lam x).toReal ^ 2 ∂lam)
                  ↔ BalancedG T μ)) := by
  obtain ⟨h1, h2, h3⟩ := no_distant_equilibrium_two_general (g := g)
    hinv.isReversalPair_reversal h
  refine ⟨h1, fun D hD => ?_, h3⟩
  rw [← h2]
  refine integral_congr_ae ?_
  filter_upwards [isGradDensity_unique hinv h hgd hD] with x hx
  rw [hx]

end Flow

/-! ### `prop:nonlinear_freezing`*(3)*, with the gradient -/

section FreezingThree

variable {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsProbabilityMeasure lam]
  {g gd : ℝ → ℝ}

omit [IsProbabilityMeasure lam] in
theorem isFiniteMeasure_pertG_ae [IsFiniteMeasure lam] {h : S → ℝ} (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ 1 / 2) : IsFiniteMeasure (pertG lam h) := by
  refine isFiniteMeasure_withDensity_ofReal (Integrable.of_bound (by fun_prop) (3 / 2) ?_).2
  filter_upwards [hh] with x hx
  rw [Real.norm_eq_abs, abs_le]
  have := abs_le.1 hx
  constructor <;> linarith

omit [IsProbabilityMeasure lam] in
theorem isFiniteMeasure_wtG_ae [IsFiniteMeasure lam] {w : S → ℝ} {W : ℝ} (hwm : Measurable w)
    (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwW : ∀ᵐ x ∂lam, w x ≤ W) : IsFiniteMeasure (wtG lam w) := by
  refine isFiniteMeasure_withDensity_ofReal (Integrable.of_bound hwm.aestronglyMeasurable W ?_).2
  filter_upwards [hw0, hwW] with x h0 h1
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

omit [IsMarkovKernel T] [IsProbabilityMeasure lam] in
/-- **The first-variation hypotheses hold on the set of item *(3)***: `μ = (1 + h)λ` with
`|h| ≤ ½` and band-valued ratio, `ν = wλ` with `0 ≤ w ≤ W`, `g̃'` continuous on `ℝ₊*` (the
proof's "`μ ∼ λ` and `dν/dμ = w/(1 + h) ∈ L^∞(μ)`, and `r` takes its values in `(a, d)`"). -/
theorem setting_pertG [IsFiniteMeasure lam] (F : FreezingBands) {w h : S → ℝ} {W : ℝ}
    (hwm : Measurable w) (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwW : ∀ᵐ x ∂lam, w x ≤ W)
    (hhm : Measurable h) (hh : ∀ᵐ x ∂lam, |h x| ≤ 1 / 2)
    (hband : ∀ᵐ x ∂lam, ratioG T (pertG lam h) x ∈ F.bands)
    (hgc : ContinuousOn gd (Set.Ioi 0)) :
    FirstVariationSetting T lam (pertG lam h) (wtG lam w) gd := by
  have hne : ∀ᵐ x ∂lam, ENNReal.ofReal (1 + h x) ≠ 0 := by
    filter_upwards [hh] with x hx
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := (abs_le.1 hx).1; linarith
  have hac : pertG lam h ≪ lam := withDensity_absolutelyContinuous _ _
  have hac' : lam ≪ pertG lam h := withDensity_absolutelyContinuous' (by fun_prop) hne
  refine ⟨hac, hac', ?_, (withDensity_absolutelyContinuous _ _).trans hac',
    ⟨F.a, F.d, F.a_pos, hac.ae_le ?_⟩, ⟨2 * W, hac.ae_le ?_⟩, hgc⟩
  · refine MemLp.of_bound (Measure.measurable_rnDeriv _ _).ennreal_toReal.aestronglyMeasurable
      (3 / 2) ?_
    filter_upwards [Measure.rnDeriv_withDensity lam
      (show Measurable fun x => ENNReal.ofReal (1 + h x) by fun_prop), hh] with x hx hhx
    have h1 := abs_le.1 hhx
    change ‖((lam.withDensity fun x => ENNReal.ofReal (1 + h x)).rnDeriv lam x).toReal‖ ≤ 3 / 2
    rw [hx, Real.norm_eq_abs, ENNReal.toReal_ofReal (by linarith), abs_le]
    constructor <;> linarith
  · filter_upwards [hband] with x hx
    rcases hx with hx | hx
    · exact ⟨hx.1.le, (hx.2.trans (F.b_lt_one.trans (F.one_lt_c.trans F.c_lt_d))).le⟩
    · exact ⟨(F.a_lt_b.trans (F.b_lt_one.trans (F.one_lt_c.trans hx.1))).le, hx.2.le⟩
  · filter_upwards [toReal_rnDeriv_wt_pert hwm hw0 hhm hh, hh, hw0, hwW] with x hx hhx hwx hWx
    have h1h : 1 / 2 ≤ 1 + h x := by have := (abs_le.1 hhx).1; linarith
    have hq0 : 0 ≤ ((wtG lam w).rnDeriv (pertG lam h) x).toReal := ENNReal.toReal_nonneg
    nlinarith

/-- **`prop:nonlinear_freezing`*(3)* with the gradient read by the first variation**: on the set
of flows `μ = (1 + h)λ`, `‖h‖_{L^∞(λ)} ≤ ½`, with band-valued ratio, `∇^λ𝓛_{g̃,ν}(μ)` exists —
its `λ`-density is `D = Tφ − rφ` — and **every** `λ`-density of it has `L²(λ)`-norm at most
`C'ε`, `C' = 2(1 + d)‖w‖_{L^∞(λ)}`; and a trajectory of the paper's gradient flow
(`IsGradientFlowPaper`) moves at most `C'ετ` in `𝓜²(λ)` during a time `τ` it spends in the set,
so moving a distance `η` there takes a time `τ ≥ η/(C'ε)`. -/
theorem nonlinear_freezing_three_bridge (F : FreezingBands) (hinv : IsInvariant T lam) {ε : ℝ}
    (hε : 0 < ε) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) (hgc : ContinuousOn gd (Set.Ioi 0))
    (hgdε : ∀ z ∈ F.bands, |gd z| ≤ ε) {w : S → ℝ} (hwm : Measurable w)
    (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwinf : eLpNorm w ⊤ lam ≠ ⊤) :
    (∀ h : S → ℝ, Measurable h → (∀ᵐ x ∂lam, |h x| ≤ 1 / 2) →
        (∀ᵐ x ∂lam, ratioG T (pertG lam h) x ∈ F.bands) →
        IsGradDensity T lam (wtG lam w) (pertG lam h) g
            (gradDensityG T (pertG lam h) (wtG lam w) gd)
          ∧ ∀ D : S → ℝ, IsGradDensity T lam (wtG lam w) (pertG lam h) g D →
            eLpNorm D 2 lam ≤ ENNReal.ofReal (2 * (1 + F.d) * (eLpNorm w ⊤ lam).toReal * ε))
      ∧ ∀ (μ : ℝ → Measure S) (u : ℝ → Lp ℝ 2 lam),
        IsGradientFlowPaper T lam (wtG lam w) g μ u → ∀ τ : ℝ, 0 ≤ τ →
        (∀ t ∈ Set.Icc 0 τ, ∃ h : S → ℝ, Measurable h ∧ (∀ᵐ x ∂lam, |h x| ≤ 1 / 2) ∧
          μ t = pertG lam h ∧ ∀ᵐ x ∂lam, ratioG T (μ t) x ∈ F.bands) →
        ∀ η : ℝ, η ≤ ‖u τ - u 0‖ →
          η ≤ 2 * (1 + F.d) * (eLpNorm w ⊤ lam).toReal * ε * τ := by
  classical
  have hwW := ae_le_linfty hwinf
  set W := (eLpNorm w ⊤ lam).toReal
  haveI := isFiniteMeasure_wtG_ae hwm hw0 hwW
  have hC : 0 ≤ 2 * (1 + F.d) * W * ε := by
    have : 0 < F.d := (zero_lt_one.trans F.one_lt_c).trans F.c_lt_d
    have : 0 ≤ W := ENNReal.toReal_nonneg
    positivity
  -- the gradient and the bound on every one of its densities
  have hstatic : ∀ h : S → ℝ, Measurable h → (∀ᵐ x ∂lam, |h x| ≤ 1 / 2) →
      (∀ᵐ x ∂lam, ratioG T (pertG lam h) x ∈ F.bands) →
      IsGradDensity T lam (wtG lam w) (pertG lam h) g
          (gradDensityG T (pertG lam h) (wtG lam w) gd)
        ∧ ∀ D : S → ℝ, IsGradDensity T lam (wtG lam w) (pertG lam h) g D →
          eLpNorm D 2 lam ≤ ENNReal.ofReal (2 * (1 + F.d) * W * ε) := by
    intro h hhm hh hband
    haveI := isFiniteMeasure_pertG_ae hhm hh
    have hset := setting_pertG (T := T) F hwm hw0 hwW hhm hh hband hgc
    refine ⟨gradDensityG_isGradDensity hinv hset hgd, fun D hD => ?_⟩
    rw [eLpNorm_congr_ae (isGradDensity_unique hinv hset hgd hD)]
    exact freezing_three_eLpNorm_le F hinv hε.le hgdε hwm hw0 hwW hhm hh hband
  refine ⟨hstatic, fun μ u hflow τ hτ hin η hη => hη.trans ?_⟩
  let f' : ℝ → Lp ℝ 2 lam := fun t => if ht : 0 ≤ t then -(hflow t ht).2.choose else 0
  have hder : ∀ t ∈ Set.Icc 0 τ, HasDerivWithinAt u (f' t) (Set.Icc 0 τ) t := by
    intro t ht
    have := (hflow t ht.1).2.choose_spec.2
    simp only [f', dif_pos ht.1]
    exact this.hasDerivWithinAt
  have hbd : ∀ t ∈ Set.Ico 0 τ, ‖f' t‖ ≤ 2 * (1 + F.d) * W * ε := by
    intro t ht
    obtain ⟨h, hhm, hh, hμt, hband⟩ := hin t (Set.Ico_subset_Icc_self ht)
    have hD := (hflow t ht.1).2.choose_spec.1
    simp only [f', dif_pos ht.1, norm_neg]
    generalize (hflow t ht.1).2.choose = D at hD ⊢
    rw [hμt] at hD hband
    rw [Lp.norm_def]
    exact ENNReal.toReal_le_of_le_ofReal hC ((hstatic h hhm hh hband).2 _ hD)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hder hbd τ ⟨hτ, le_rfl⟩
  simpa using this

end FreezingThree

/-! ### `FirstVariationFull` is inhabited: the named hypothesis of `FreezingGeneral2` discharged -/

section NamedHypothesis

variable {T : Kernel S S} [IsMarkovKernel T] {lam μ ν : Measure S} [IsFiniteMeasure lam]
  [IsFiniteMeasure μ] {g gd : ℝ → ℝ}

/-- **The admissible directions in `λ`-coordinates**: `δ = eλ` with `|e| ≤ C·dμ/dλ`, i.e.
`dδ/dμ = e/(dμ/dλ)` essentially bounded — the cone spanned by the paper's class
(`‖dδ/dμ‖_{L^∞(μ)} < 1`). It contains the constant directions only when `dμ/dλ` is essentially
bounded below. -/
def AdmL (lam μ : Measure S) : Set (S → ℝ) :=
  {e | Measurable e ∧ ∃ C : ℝ, ∀ᵐ x ∂lam, |e x| ≤ C * (μ.rnDeriv lam x).toReal}

omit [IsMarkovKernel T] in
/-- `λ`-coordinates and `μ`-coordinates describe the same line: `(u + se)λ = (1 + s·w)μ` when
`w·u = e`, `u = dμ/dλ`. -/
theorem lineG_eq_perturb (hμl : μ ≪ lam) {e w : S → ℝ} (hwm : Measurable w)
    (hwe : ∀ᵐ x ∂lam, w x * (μ.rnDeriv lam x).toReal = e x) (s : ℝ) :
    lineG lam (fun x => (μ.rnDeriv lam x).toReal) e s
      = Core.General.FirstVariation.perturb μ w s := by
  have hμ : lam.withDensity (μ.rnDeriv lam) = μ := Measure.withDensity_rnDeriv_eq μ lam hμl
  unfold lineG Core.General.FirstVariation.perturb
  conv_rhs => rw [← hμ]
  rw [← withDensity_mul _ (Measure.measurable_rnDeriv _ _)
    (by fun_prop : Measurable fun x => ENNReal.ofReal (1 + s * w x))]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ lam, hwe] with x htop hx
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_toReal htop.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ← hx]
  congr 1
  ring

/-- **`FirstVariationFull` holds**, on the admissible cone `AdmL`, with density `D = Tφ − rφ`,
under the first-variation hypotheses: the named hypothesis that `nonlinear_freezing_one_general`
and `balanced_of_isCriticalAlong` consume is discharged. -/
theorem firstVariationFull_of_setting [IsFiniteMeasure ν] (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) :
    FirstVariationFull T lam ν g μ (AdmL lam μ) (gradDensityG T μ ν gd) := by
  rintro e ⟨hem, C, hC⟩
  have hum : Measurable fun x => (μ.rnDeriv lam x).toReal :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  set w : S → ℝ := fun x => e x / (μ.rnDeriv lam x).toReal with hw
  have hwm : Measurable w := hem.div hum
  have hupos : ∀ᵐ x ∂lam, 0 < (μ.rnDeriv lam x).toReal := by
    filter_upwards [h.ac'.ae_le (Measure.rnDeriv_pos h.ac), Measure.rnDeriv_lt_top μ lam]
      with x h1 h2
    exact ENNReal.toReal_pos h1.ne' h2.ne
  have hwe : ∀ᵐ x ∂lam, w x * (μ.rnDeriv lam x).toReal = e x := by
    filter_upwards [hupos] with x hx
    simp only [hw]
    exact div_mul_cancel₀ _ hx.ne'
  have hwb : ∀ᵐ x ∂μ, |w x| ≤ max C 0 := h.ac.ae_le (by
    filter_upwards [hC, hupos] with x h1 h2
    simp only [hw]
    rw [abs_div, abs_of_pos h2, div_le_iff₀ h2]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h2.le))
  obtain ⟨a, b, ha, hab, hr⟩ := ratio_Icc_of_setting h
  obtain ⟨W, hW⟩ := h.dens_bdd
  have hW' : ∀ᵐ x ∂μ, |(ν.rnDeriv μ x).toReal| ≤ W := by
    filter_upwards [hW] with x hx; rwa [abs_of_nonneg ENNReal.toReal_nonneg]
  have hac : T ∘ₘ μ ≪ μ := comp_absolutelyContinuous_self hinv h.ac h.ac'
  have key := Core.General.FirstVariation.hasDerivAt_loss_gradDens (T := T) h.nu_ac hW' hac ha
    hab hr hgd h.gd_cont hwm (le_max_right C 0) hwb
  have heq : (fun s => lossG T ν g (lineG lam (fun x => (μ.rnDeriv lam x).toReal) e s))
      = fun s => Core.General.FirstVariation.loss T g ν
          (Core.General.FirstVariation.perturb μ w s) := by
    funext s
    rw [lossG_eq_loss, lineG_eq_perturb h.ac hwm hwe s]
  rw [heq]
  convert key using 1
  rw [← integral_rnDeriv_smul h.ac]
  refine integral_congr_ae ?_
  filter_upwards [hwe] with x hx
  simp only [smul_eq_mul, gradDensityG_eq_gradDens]
  rw [← hx]
  ring

/-- **Criticality along `AdmL` is criticality**: in `λ`-coordinates (`IsCriticalAlong`, on the
admissible cone) and in `μ`-coordinates (`IsCriticalG`) the notions agree, both being `D = 0`. -/
theorem isCriticalAlong_iff [IsFiniteMeasure ν] (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y) :
    IsCriticalAlong T lam ν g μ (AdmL lam μ) ↔ IsCriticalG T ν μ g := by
  have hFV := firstVariationFull_of_setting hinv h hgd
  constructor
  · intro hc u hu
    have hum : Measurable fun x => (μ.rnDeriv lam x).toReal :=
      (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have hmem : (fun x => u x * (μ.rnDeriv lam x).toReal) ∈ AdmL lam μ := by
      refine ⟨hu.1.mul hum, 1, ?_⟩
      filter_upwards [h.ac'.ae_le (ae_abs_le_one_of_admissible hu)] with x hx
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_right hx ENNReal.toReal_nonneg
    have := hc _ hmem
    rwa [show (fun s => lossG T ν g (lineG lam (fun x => (μ.rnDeriv lam x).toReal)
        (fun x => u x * (μ.rnDeriv lam x).toReal) s))
        = fun s => Core.General.FirstVariation.loss T g ν
            (Core.General.FirstVariation.perturb μ u s) from
      funext fun s => by
        rw [lossG_eq_loss, lineG_eq_perturb h.ac hu.1
          (Filter.Eventually.of_forall fun _ => rfl) s]] at this
  · intro hc
    exact isCriticalAlong_of_ae_zero hFV ((isCriticalG_iff hinv h hgd).1 hc)

/-- **`balanced_of_isCriticalAlong` without the constant direction**: a critical point of
`𝓛_{g,ν}` along the admissible cone is balanced, for strictly unimodal `g` and `dν/dμ > 0` —
no lower bound on `dμ/dλ` is asked. -/
theorem balanced_of_isCriticalAlong_bridge [IsFiniteMeasure ν] (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hgd : ∀ y, 0 < y → HasDerivAt g (gd y) y)
    (hg : StrictlyUnimodal gd) (hν : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal)
    (hc : IsCriticalAlong T lam ν g μ (AdmL lam μ)) : BalancedG T μ :=
  freezing_remark_four_bridge hinv h hgd hg hν ((isCriticalAlong_iff hinv h hgd).1 hc)

end NamedHypothesis

/-! ### The new predicates are inhabited, off balance (kb 0025, 0027) -/

section Witness

theorem hasDerivAt_twoStateBands_g :
    ∀ y, 0 < y → HasDerivAt twoStateBands.g (deriv twoStateBands.g y) y :=
  fun y _ => (twoStateBands.differentiable_g y).hasDerivAt

theorem continuousOn_deriv_twoStateBands_g :
    ContinuousOn (deriv twoStateBands.g) (Set.Ioi 0) :=
  (twoStateBands.contDiff_g.continuous_deriv (by norm_num)).continuousOn

/-- **A critical point that is not balanced** (`prop:nonlinear_freezing`*(1)*–*(2)*, in the
derivative sense): on the two-state chain (`Bool`, uniform `π`, `T = const π`), the flow
`μ = (1 + h)π`, `h = (3/10, −3/10)`, is a critical point of `𝓛_{g,ν}` for the constructed
generator `g` of item *(2)*'s bands and every finite `ν ≪ μ`; its gradient exists and is `0`; and
`μ` is not balanced. -/
theorem bool_critical_unbalanced :
    (∀ (ν : Measure Bool) [IsFiniteMeasure ν], ν ≪ pertG boolUnif boolH →
        IsCriticalG (Kernel.const Bool boolUnif) ν (pertG boolUnif boolH) twoStateBands.g)
      ∧ IsGradDensity (Kernel.const Bool boolUnif) boolUnif boolUnif (pertG boolUnif boolH)
          twoStateBands.g (fun _ => 0)
      ∧ ¬ BalancedG (Kernel.const Bool boolUnif) (pertG boolUnif boolH) := by
  haveI := isFiniteMeasure_pertG (π := boolUnif) (measurable_of_countable boolH) boolH_abs
  obtain ⟨-, hset, -, hband, hnb⟩ := bool_witness continuousOn_deriv_twoStateBands_g
  have H := nonlinear_freezing_one_bridge twoStateBands (Core.General.isInvariant_const boolUnif)
    hasDerivAt_twoStateBands_g continuousOn_deriv_twoStateBands_g
    (fun _ hz => twoStateBands.deriv_g_eq_zero_of_mem_bands' hz) hset.ac
    (Filter.Eventually.of_forall hband)
  exact ⟨H.1, H.2.2 boolUnif hset, hnb⟩

/-- **`prop:no_distant_equilibrium`*(1)* with the gradient is not vacuous**: on the same
unbalanced flow, for the strictly unimodal `g = (x − 1)²` and `ν = π`, the gradient exists
(density `D = Tφ − rφ`) and `μ` is **not** a critical point. -/
theorem bool_not_critical :
    IsGradDensity (Kernel.const Bool boolUnif) boolUnif boolUnif (pertG boolUnif boolH)
        (fun x => (x - 1) ^ 2)
        (gradDensityG (Kernel.const Bool boolUnif) (pertG boolUnif boolH) boolUnif
          (fun z => 2 * (z - 1)))
      ∧ ¬ IsCriticalG (Kernel.const Bool boolUnif) boolUnif (pertG boolUnif boolH)
          (fun x => (x - 1) ^ 2) := by
  haveI := isFiniteMeasure_pertG (π := boolUnif) (measurable_of_countable boolH) boolH_abs
  obtain ⟨-, hset, -, -, hnb⟩ := bool_witness (gd := fun z => 2 * (z - 1)) (by fun_prop)
  have hgd : ∀ y : ℝ, 0 < y → HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (y - 1)) y := by
    intro y _
    have h1 := (hasDerivAt_pow 2 (y - 1)).comp y ((hasDerivAt_id' y).sub_const 1)
    have h2 : (2 : ℝ) * (y - 1) = ((2 : ℕ) : ℝ) * (y - 1) ^ (2 - 1) * 1 := by norm_num
    rw [h2]
    exact h1
  have H := no_distant_equilibrium_one_bridge (Core.General.isInvariant_const boolUnif) hset hgd
    strictlyUnimodal_sqDeriv (toReal_rnDeriv_pos_of_ac hset.ac)
  exact ⟨H.1, fun hc => hnb (H.2.2 hc)⟩

/-- **The paper's gradient-flow predicate is inhabited off balance**: the constant curve at the
frozen, unbalanced Bool flow is an `IsGradientFlowPaper` of `𝓛_{g,π}` for the constructed
generator. -/
theorem bool_paper_flow :
    ∃ u : Lp ℝ 2 boolUnif,
      IsGradientFlowPaper (Kernel.const Bool boolUnif) boolUnif boolUnif twoStateBands.g
        (fun _ => pertG boolUnif boolH) (fun _ => u)
      ∧ ¬ BalancedG (Kernel.const Bool boolUnif) (pertG boolUnif boolH) := by
  haveI := isFiniteMeasure_pertG (π := boolUnif) (measurable_of_countable boolH) boolH_abs
  obtain ⟨-, hset, -, -, -⟩ := bool_witness continuousOn_deriv_twoStateBands_g
  obtain ⟨u, hu, hnb⟩ := bool_frozen_flow boolUnif
  exact ⟨u, (isGradientFlowPaper_iff (Core.General.isInvariant_const boolUnif)
    hasDerivAt_twoStateBands_g (fun _ => inferInstance) (fun _ _ => hset)).2 hu, hnb⟩

end Witness

/-! ### `rem:freezing`*(ii)*: `C³` makes the supremum finite -/

section ThirdDeriv

open Set in
/-- **`rem:freezing`*(ii)*, `C³` read with a continuous third derivative**: for a generator `C³` on
`[1, 1 + δ]` (derivative chain `g → g₁ → g₂ → g₃` within the interval, `g₃` continuous there),
`sup_{[1,1+δ]} |g₃| ≥ 4/δ`. The supremum is attained and finite by compactness, so
`RemarksA.third_deriv_sSup`'s boundedness hypothesis is discharged rather than assumed.
⚠ presupposed: `g` differentiable at `1` (`hd0`), which the remark's own `g'(1) = 0` needs; `C³` on
`[1,1+δ]` gives only a right derivative there. -/
theorem third_deriv_sSup_of_C3 {g g1 g2 g3 : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hg1 : g 1 = 0) (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x)
    (hd0 : HasDerivAt g (g1 1) 1)
    (hd1 : ∀ x ∈ Icc 1 (1 + δ), HasDerivWithinAt g1 (g2 x) (Icc 1 (1 + δ)) x)
    (hd2 : ∀ x ∈ Icc 1 (1 + δ), HasDerivWithinAt g2 (g3 x) (Icc 1 (1 + δ)) x)
    (hc3 : ContinuousOn g3 (Icc 1 (1 + δ)))
    (hflat : ∀ x ∈ Icc (1 + δ) (1 + 2 * δ), g1 x = 0) (h2 : g2 1 = 2) :
    4 / δ ≤ sSup ((fun x => |g3 x|) '' Icc 1 (1 + δ)) :=
  RemarksA.third_deriv_sSup hδ hg1 hgpos hd0 hd1 hd2 hflat h2
    (isCompact_Icc.image_of_continuousOn (continuous_abs.comp_continuousOn hc3)).bddAbove

end ThirdDeriv

/-! ### A non-constant gradient flow with a strictly unimodal generator, on a general space

The finite library proves that on the two-state chain the gradient flow of `(x − 1)²` exists from
the unbalanced `u₀ = (3/2, 1/2)` (`twoState_flow_exists_check_sq`). Read on `Bool` with the
uniform `π` and the resampling kernel, it is an `IsGradientFlowG` — hence, by
`isGradientFlowPaper_iff`, an `IsGradientFlowPaper` — meeting the first-variation hypotheses at
every time: the flow half of `prop:no_distant_equilibrium`*(2)* is not vacuous off balance. -/

section BoolFlow

/-- `true ↦ 0`, `false ↦ 1`. -/
def boolIdx (b : Bool) : Fin 2 := if b then 0 else 1

/-- The flow of `π`-density `f` on `Bool`. -/
noncomputable def boolFlow (f : Bool → ℝ) : Measure Bool :=
  boolUnif.withDensity fun b => ENNReal.ofReal (f b)

instance boolFlow.isFinite (f : Bool → ℝ) : IsFiniteMeasure (boolFlow f) :=
  isFiniteMeasure_withDensity_ofReal
    (memLp_one_iff_integrable.1 (MemLp.of_discrete (f := f) (p := 1) (μ := boolUnif))).2

theorem integral_boolUnif (φ : Bool → ℝ) : ∫ b, φ b ∂boolUnif = (φ true + φ false) / 2 := by
  have hI : ∀ μ : Measure Bool, IsFiniteMeasure μ → Integrable φ μ := fun μ _ =>
    memLp_one_iff_integrable.1 (MemLp.of_discrete (f := φ) (p := 1) (μ := μ))
  have hf : ∀ b : Bool, IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • Measure.dirac b) := fun b =>
    (Measure.dirac b).smul_finite (by norm_num)
  rw [boolUnif, integral_add_measure (hI _ (hf true)) (hI _ (hf false)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem boolUnif_ne_zero (b : Bool) : boolUnif {b} ≠ 0 := by
  rw [boolUnif_singleton]; norm_num

theorem ae_bool_iff {p : Bool → Prop} : (∀ᵐ b ∂boolUnif, p b) ↔ ∀ b, p b :=
  ⟨fun h b => ae_iff_of_countable.1 h b (boolUnif_ne_zero b),
    fun h => Filter.Eventually.of_forall h⟩

theorem toReal_rnDeriv_boolFlow {f : Bool → ℝ} (hf : ∀ b, 0 < f b) (b : Bool) :
    ((boolFlow f).rnDeriv boolUnif b).toReal = f b := by
  have h := Measure.rnDeriv_withDensity boolUnif
    (show Measurable fun b => ENNReal.ofReal (f b) from measurable_of_countable _)
  have := ae_bool_iff.1 h b
  change ((boolUnif.withDensity fun b => ENNReal.ofReal (f b)).rnDeriv boolUnif b).toReal = f b
  rw [this, ENNReal.toReal_ofReal (hf b).le]

theorem toReal_rnDeriv_unif_boolFlow {f : Bool → ℝ} (hf : ∀ b, 0 < f b) (b : Bool) :
    (boolUnif.rnDeriv (boolFlow f) b).toReal = 1 / f b := by
  have h1 := Measure.rnDeriv_withDensity_right boolUnif boolUnif
    (f := fun b => ENNReal.ofReal (f b)) (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun b => by simp [hf b])
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  have h2 := ae_bool_iff.1 (h1.and (Measure.rnDeriv_self boolUnif)) b
  change (boolUnif.rnDeriv (boolUnif.withDensity fun b => ENNReal.ofReal (f b)) b).toReal = _
  have e2 : boolUnif.rnDeriv boolUnif b = 1 := h2.2
  rw [h2.1]
  dsimp only
  rw [e2, mul_one, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hf b).le, one_div]

theorem boolFlow_univ_toReal {f : Bool → ℝ} (hf : ∀ b, 0 < f b) :
    ((boolFlow f) Set.univ).toReal = (f true + f false) / 2 := by
  have hI : Integrable f boolUnif :=
    memLp_one_iff_integrable.1 (MemLp.of_discrete (f := f) (p := 1) (μ := boolUnif))
  rw [boolFlow, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun b => (hf b).le),
    ENNReal.toReal_ofReal (integral_nonneg fun b => (hf b).le), integral_boolUnif]

theorem ratioG_boolFlow {f : Bool → ℝ} (hf : ∀ b, 0 < f b) (b : Bool) :
    ratioG (Kernel.const Bool boolUnif) (boolFlow f) b = ((f true + f false) / 2) / f b := by
  set c := (boolFlow f) Set.univ
  have hct : c ≠ ∞ := measure_ne_top _ _
  haveI := boolUnif.smul_finite hct
  have h1 := Measure.rnDeriv_withDensity_right (c • boolUnif) boolUnif
    (f := fun x => ENNReal.ofReal (f x)) (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun x => by simp [hf x])
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  have h2 : (c • boolUnif).rnDeriv boolUnif =ᵐ[boolUnif] c • boolUnif.rnDeriv boolUnif :=
    Measure.rnDeriv_smul_left_of_ne_top' _ _ hct
  have h := ae_bool_iff.1 ((h1.and h2).and (Measure.rnDeriv_self boolUnif)) b
  simp only [ratioG, Measure.const_comp]
  change ((c • boolUnif).rnDeriv (boolUnif.withDensity fun x => ENNReal.ofReal (f x)) b).toReal
    = _
  have e1 : (c • boolUnif).rnDeriv boolUnif b = c * boolUnif.rnDeriv boolUnif b := h.1.2
  have e2 : boolUnif.rnDeriv boolUnif b = 1 := h.2
  rw [h.1.1]
  dsimp only
  rw [e1, e2, mul_one, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (hf b).le, boolFlow_univ_toReal hf]
  ring

/-- `D = Tφ − rφ` on `Bool`, for `ν = π`: `φ = g'(r)/f`, `Tφ` the mean of `φ`. -/
theorem gradDensityG_boolFlow {f : Bool → ℝ} (hf : ∀ b, 0 < f b) (gd : ℝ → ℝ) (b : Bool) :
    gradDensityG (Kernel.const Bool boolUnif) (boolFlow f) boolUnif gd b
      = ((gd (((f true + f false) / 2) / f true) * (1 / f true)
          + gd (((f true + f false) / 2) / f false) * (1 / f false)) / 2)
        - ((f true + f false) / 2) / f b * (gd (((f true + f false) / 2) / f b) * (1 / f b)) := by
  have hpot : ∀ x, potG (Kernel.const Bool boolUnif) (boolFlow f) boolUnif gd x
      = gd (((f true + f false) / 2) / f x) * (1 / f x) := fun x => by
    rw [potG, ratioG_boolFlow hf, toReal_rnDeriv_unif_boolFlow hf]
  simp only [gradDensityG, Core.General.funAct, Kernel.const_apply, hpot, integral_boolUnif,
    ratioG_boolFlow hf]

/-- **The first-variation hypotheses at every positive flow on `Bool`** (`ν = π`). -/
theorem setting_boolFlow {f : Bool → ℝ} (hf : ∀ b, 0 < f b) {gd : ℝ → ℝ}
    (hgd : ContinuousOn gd (Set.Ioi 0)) :
    FirstVariationSetting (Kernel.const Bool boolUnif) boolUnif (boolFlow f) boolUnif gd := by
  have hne : ∀ᵐ b ∂boolUnif, ENNReal.ofReal (f b) ≠ 0 :=
    Filter.Eventually.of_forall fun b => by simp [hf b]
  have hac : boolFlow f ≪ boolUnif := withDensity_absolutelyContinuous _ _
  have hac' : boolUnif ≪ boolFlow f :=
    withDensity_absolutelyContinuous' (measurable_of_countable _).aemeasurable hne
  have hr : ∀ b, 0 < ratioG (Kernel.const Bool boolUnif) (boolFlow f) b := fun b => by
    rw [ratioG_boolFlow hf]
    have := hf true; have := hf false; have := hf b
    positivity
  refine ⟨hac, hac', MemLp.of_discrete, hac',
    ⟨min (ratioG (Kernel.const Bool boolUnif) (boolFlow f) true)
        (ratioG (Kernel.const Bool boolUnif) (boolFlow f) false),
      max (ratioG (Kernel.const Bool boolUnif) (boolFlow f) true)
        (ratioG (Kernel.const Bool boolUnif) (boolFlow f) false),
      lt_min (hr true) (hr false), Filter.Eventually.of_forall fun b => ?_⟩,
    ⟨max (1 / f true) (1 / f false), Filter.Eventually.of_forall fun b => ?_⟩, hgd⟩
  · cases b
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · rw [toReal_rnDeriv_unif_boolFlow hf]
    cases b
    · exact le_max_right _ _
    · exact le_max_left _ _

/-- `L²(π)` on `Bool` as the image of `ℝ²`: `v ↦ v ∘ boolIdx`. -/
noncomputable def boolLp : (Fin 2 → ℝ) →L[ℝ] Lp ℝ 2 boolUnif :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (MemLp.of_discrete (f := fun b => v (boolIdx b)) (p := 2)
        (μ := boolUnif)).toLp _
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coe_boolLp (v : Fin 2 → ℝ) : (boolLp v : Bool → ℝ) =ᵐ[boolUnif] fun b => v (boolIdx b) :=
  MemLp.coeFn_toLp (MemLp.of_discrete (f := fun b => v (boolIdx b)) (p := 2) (μ := boolUnif))

/-- The finite gradient density on the two-state chain, `ν = λ = (½, ½)`, is the same formula. -/
theorem lossGrad_twoState {U : Fin 2 → ℝ} (hU : ∀ i, 0 < U i) (gd : ℝ → ℝ) (i : Fin 2) :
    lossGrad twoStateK twoStateLam (fun x => twoStateLam x * 1) gd U i
      = ((gd (((U 0 + U 1) / 2) / U 0) * (1 / U 0)
          + gd (((U 0 + U 1) / 2) / U 1) * (1 / U 1)) / 2)
        - ((U 0 + U 1) / 2) / U i * (gd (((U 0 + U 1) / 2) / U i) * (1 / U i)) := by
  have hr : ∀ j, ratio twoStateK twoStateLam U j = ((U 0 + U 1) / 2) / U j := fun j => by
    have := hU j
    simp only [ratio, pushMass, twoStateK, twoStateLam, Fin.sum_univ_two]
    field_simp
  have hw : ∀ j, twoStateLam j * 1 / (twoStateLam j * U j) = 1 / U j := fun j => by
    have := hU j
    simp only [twoStateLam]
    field_simp
  simp only [lossGrad, lossGradDensity, gradDensity, funAct, hr, hw, twoStateK,
    Fin.sum_univ_two]
  ring

/-- **The paper's gradient flow, with the strictly unimodal `g = (x − 1)²`, exists off balance on
a general space**: on `Bool` with the resampling kernel and `ν = π`, a curve of flows `μ_t` from
the unbalanced `μ₀ = (3/2, 1/2)·π` is an `IsGradientFlowPaper` of `𝓛_{g,π}`, meets the
first-variation hypotheses at every `t ≥ 0`, and its mass strictly increases at `t = 0` — so
`no_distant_equilibrium_two_flow_bridge` applies to it with a non-trivial conclusion. -/
theorem bool_unimodal_flow :
    ∃ (μ : ℝ → Measure Bool) (u : ℝ → Lp ℝ 2 boolUnif),
      IsGradientFlowPaper (Kernel.const Bool boolUnif) boolUnif boolUnif
          (fun x => (x - 1) ^ 2) μ u
        ∧ IsGradientFlowG (Kernel.const Bool boolUnif) boolUnif boolUnif
          (fun z => 2 * (z - 1)) μ u
        ∧ (∀ t, IsFiniteMeasure (μ t))
        ∧ (∀ t, 0 ≤ t → FirstVariationSetting (Kernel.const Bool boolUnif) boolUnif (μ t)
            boolUnif (fun z => 2 * (z - 1)))
        ∧ ¬ BalancedG (Kernel.const Bool boolUnif) (μ 0)
        ∧ 0 < -∫ x, gradDensityG (Kernel.const Bool boolUnif) (μ 0) boolUnif
            (fun z => 2 * (z - 1)) x ∂boolUnif := by
  obtain ⟨U, hU0, hflow, hpos, -⟩ := twoState_flow_exists_check_sq
  set μ : ℝ → Measure Bool := fun t => boolFlow fun b => U t (boolIdx b) with hμ
  set u : ℝ → Lp ℝ 2 boolUnif := fun t => boolLp (U t) with hu
  have hposb : ∀ t, 0 ≤ t → ∀ b, 0 < U t (boolIdx b) := fun t ht b => hpos t ht _
  have hgc : ContinuousOn (fun z : ℝ => 2 * (z - 1)) (Set.Ioi 0) := by fun_prop
  have hset : ∀ t, 0 ≤ t → FirstVariationSetting (Kernel.const Bool boolUnif) boolUnif (μ t)
      boolUnif (fun z => 2 * (z - 1)) := fun t ht => setting_boolFlow (hposb t ht) hgc
  have hfin : ∀ t, IsFiniteMeasure (μ t) := fun t => boolFlow.isFinite _
  have hsqd : ∀ y : ℝ, 0 < y → HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (y - 1)) y := by
    intro y _
    have h1 := (hasDerivAt_pow 2 (y - 1)).comp y ((hasDerivAt_id' y).sub_const 1)
    have h2 : (2 : ℝ) * (y - 1) = ((2 : ℕ) : ℝ) * (y - 1) ^ (2 - 1) * 1 := by norm_num
    rw [h2]
    exact h1
  have hG : IsGradientFlowG (Kernel.const Bool boolUnif) boolUnif boolUnif
      (fun z => 2 * (z - 1)) μ u := by
    intro t ht
    have hd : HasDerivAt U
        (fun i => -lossGrad twoStateK twoStateLam (fun x => twoStateLam x * 1)
          (fun x => 2 * (x - 1)) (U t) i) t :=
      hasDerivAt_pi.2 fun i => hflow t ht i
    refine ⟨?_, boolLp (fun i => lossGrad twoStateK twoStateLam (fun x => twoStateLam x * 1)
      (fun x => 2 * (x - 1)) (U t) i), ?_, ?_⟩
    · filter_upwards [coe_boolLp (U t)] with b hb
      rw [hb]
      exact (toReal_rnDeriv_boolFlow (hposb t ht) b).symm
    · filter_upwards [coe_boolLp (fun i => lossGrad twoStateK twoStateLam
        (fun x => twoStateLam x * 1) (fun x => 2 * (x - 1)) (U t) i)] with b hb
      rw [hb, lossGrad_twoState (hpos t ht), gradDensityG_boolFlow (hposb t ht)]
      cases b <;> simp [boolIdx]
    · have := boolLp.hasFDerivAt.comp_hasDerivAt t hd
      rw [show (fun i => -lossGrad twoStateK twoStateLam (fun x => twoStateLam x * 1)
          (fun x => 2 * (x - 1)) (U t) i)
          = -(fun i => lossGrad twoStateK twoStateLam (fun x => twoStateLam x * 1)
            (fun x => 2 * (x - 1)) (U t) i) from rfl, map_neg] at this
      exact this
  have hP := (isGradientFlowPaper_iff (Core.General.isInvariant_const boolUnif) hsqd hfin
    hset).2 hG
  have hnb : ¬ BalancedG (Kernel.const Bool boolUnif) (μ 0) := by
    intro hb
    have h0 := hset 0 le_rfl
    have h1 := (ratioG_eq_one_iff (Core.General.isInvariant_const boolUnif) h0.ac h0.ac').2 hb
    have h2 := ae_bool_iff.1 (h0.ac'.ae_le h1) true
    simp only [hμ] at h2
    rw [ratioG_boolFlow (hposb 0 le_rfl)] at h2
    simp only [boolIdx, hU0, blowupU] at h2
    norm_num at h2
  have hR : IsReversalPair boolUnif (Kernel.const Bool boolUnif) (Kernel.const Bool boolUnif) := by
    unfold IsReversalPair
    rw [Measure.compProd_const, Measure.prod_swap]
  have hν : ∀ᵐ x ∂(μ 0), 0 < (boolUnif.rnDeriv (μ 0) x).toReal :=
    toReal_rnDeriv_pos_of_ac (hset 0 le_rfl).ac
  have H := no_distant_equilibrium_two_flow_bridge hR hsqd strictlyUnimodal_sqDeriv hP hfin hset
  exact ⟨μ, u, hP, hG, hfin, hset, hnb, (H.2.2 0 le_rfl hν hnb).2⟩

end BoolFlow

end GFNBounds.Balance.General.Bridge
