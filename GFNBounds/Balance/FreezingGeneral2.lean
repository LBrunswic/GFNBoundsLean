import GFNBounds.Core.AdjointGeneral
import GFNBounds.Balance.FreezingGeneral
import GFNBounds.Balance.Flow
import GFNBounds.Balance.WeightedL2Norm

/-!
# Freezing, the mass identity and the dichotomy on a general ergodic system

**`prop:nonlinear_freezing`** — statement `proofs.tex:840–852`, proof `:854–868`;
**`prop:no_distant_equilibrium`** — statement `proofs.tex:874–885`, proof `:887–908`;
**`theo:global_dichotomy_full`** — statement `proofs.tex:914–920`, proof `:922–924`; its body twin
**`theo:global_dichotomy`** — `cv_divergence.tex:221–231`; and the critical-point sentences of
**`rem:freezing`** — `proofs.tex:870–872`. (Line numbers advisory, kb 0036; the labels are the
anchors.)

This file lifts the general-space items of those statements from the finite library
(`Balance/MassIdentity.lean`, `Balance/Freezing.lean`, `Balance/FreezingGeneral.lean`,
`Balance/MassAscent.lean`, `Balance/Flow.lean`) onto the general measure layer of
`GFNBounds/Core/AdjointGeneral.lean`: `(𝒮̂, λ, T)` is a measurable space, a finite `λ` and a Markov
kernel `T` leaving it invariant; `μ, ν` are measures; `r = d(μT)/dμ` is `ratioG`;
`φ = g'(r)·dν/dμ` is `potG`; and the `λ`-density of `∇^λ𝓛_{g,ν}(μ)` is
`D = Tφ − rφ` (`gradDensityG`, `T` acting on functions — the paper's `P†`, `lem:adjoint`*(3)*).

> (`prop:nonlinear_freezing`*(1)*) for every `g̃ : ℝ₊* → ℝ` continuously differentiable with
> locally Lipschitz derivative, positive on `U⁻ ∪ U⁺` and with `g̃' ≡ 0` there, `g` included, and
> every ergodic `(𝒮̂, λ, T)`, every `μ` whose ratio `r = d(μT)/dμ` takes values in `U⁻ ∪ U⁺`
> `λ`-almost everywhere is a critical point of `𝓛_{g̃,ν}` for *every* training measure `ν`; on a
> finite state space the set of such `μ` is open, and `𝓛_{g̃,ν}` is locally constant on it, and
> positive when `ν ≠ 0`;

> (`prop:nonlinear_freezing`*(3)*) let `ε > 0`, let `g̃ : ℝ₊* → ℝ` be continuously differentiable
> with locally Lipschitz derivative and `|g̃'| ≤ ε` on `U⁻ ∪ U⁺`, let `(𝒮̂, λ, T)` be ergodic with `λ`
> a probability, let `ν = wλ` with `w ∈ L^∞(λ)` non-negative, and set `C' := 2(1+d)‖w‖_{L^∞(λ)}`;
> then on the set of flows `μ = (1+h)λ` with `‖h‖_{L^∞(λ)} ≤ 1/2` whose ratio takes values in
> `U⁻ ∪ U⁺` `λ`-almost everywhere, the gradient `∇^λ𝓛_{g̃,ν}` has norm at most `C'ε` in `𝓜²(λ)`,
> so a trajectory of the gradient flow moves a distance `η` in `𝓜²(λ)` in a time at least
> `η/(C'ε)` while it remains in that set.

> (`prop:nonlinear_freezing`, last sentence) In particular, no bound on the time the gradient
> flow takes to bring the loss below a given positive level, finite and depending only on that
> level, on `g''(1)`, on the mixing coefficients and on `w`, holds for every admissible generator.

> (`prop:no_distant_equilibrium`) Let `g` be admissible and differentiable with
> `sign g'(x) = sign(x−1)` for `x ≠ 1` (*strictly unimodal*), let `(𝒮̂, λ, T)` be ergodic, and
> write `u := dμ/dλ` and `r := d(μT)/dμ`. *(1) Mass identity.* For any `ν` with `dν/dμ > 0`
> `μ`-a.e., the total mass of `∇^λ𝓛_{g,ν}(μ)` is `∫ g'(r)(1−r)(dν/dμ) dλ ≤ 0`, with equality if and
> only if `μ` is balanced. Every critical point of `𝓛_{g,ν}` is therefore balanced […]
> *(2) The inflation is the algorithm.* For fixed `ν = wλ` the loss is scale-invariant, so the
> gradient flow preserves `‖u_t‖_{L²(λ)}`, while by *(1)* the total mass `μ_t(𝒮̂)` strictly
> increases off balance: training is a monotone ascent of the mass on a sphere of `𝓜²(λ)`, whose
> unique maximizer (Cauchy–Schwarz) is the balanced flow. […]

> (`theo:global_dichotomy_full`) *(1)* If `g` is strictly unimodal […] then the total mass of
> `∇^λ𝓛_{g,ν}` equals `∫ g'(r)(1−r)(dν/dμ) dλ ≤ 0`, with equality only at balance: *every critical
> point of `𝓛_{g,ν}` is balanced*, for every training measure with positive density, on every graph,
> cycles included. […] *(2)* If instead `g'` vanishes on bands on either side of `1`, then every
> flow with band-valued ratios is a critical point of `𝓛_{g,ν}` for *every* `ν`; […]

> (`rem:freezing`*(iv)*) For every admissible differentiable strictly unimodal generator, every
> critical point of `𝓛_{g,ν}` is balanced when `ν` has positive density
> (Proposition `prop:no_distant_equilibrium`*(1)*); […]

## What is proved

| paper | here |
|---|---|
| `r > 0` (the proof's "`g'(r)(1−r) < 0` wherever `r ≠ 1`" needs it) | `ratioG_pos` — **derived** from `μ ∼ λ` and invariance (`λ ≪ μT`), not hypothesised |
| `r = 1` a.e. ⟺ `μT = μ` | `ratioG_eq_one_iff` |
| no_distant *(1)*: `∫D dλ = ∫g'(r)(1−r)(dν/dμ)dλ` | `integral_gradDensityG` (from `∫Tφ dλ = ∫φ dλ`, `integral_funAct_eq`) |
| no_distant *(1)*: `≤ 0`, `= 0` iff balanced, critical ⟹ balanced | `mass_nonpos`, `mass_eq_zero_iff`, `balanced_of_criticalG`; bundled `no_distant_equilibrium_one_general` |
| no_distant *(1)*, criticality as vanishing directional derivatives | `balanced_of_isCriticalAlong` — conditional on `FirstVariationFull` (see SCOPE) |
| no_distant *(2)*: loss scale-invariant | `ratioG_smul`, `lossG_smul` |
| no_distant *(2)*: gradient ⟂ radial direction, `⟨D, u⟩ = 0` | `integral_gradDensityG_mul_dens` (through `lem:adjoint`*(3)*, a `λ`-reversal `R` of `T`) |
| no_distant *(2)*: Cauchy–Schwarz, unique maximizer is the balanced flow | `sq_integral_le_integral_sq`, `balancedG_iff_const`, `mass_le_nrm_and_eq_iff_balanced` |
| no_distant *(2)*: the flow preserves `‖u_t‖`, the mass increases, strictly off balance | `norm_const_of_flow`, `mass_monotoneOn_of_flow`, `mass_hasDerivAt_of_flow`; bundled `no_distant_equilibrium_two_flow` (static half `no_distant_equilibrium_two_general`) |
| freezing *(1)*, general: band-valued `r` ⟹ `D = 0` for every `ν`, critical | `gradDensityG_eq_zero_of_band`; bundled `nonlinear_freezing_one_general` |
| freezing *(3)*: `|D| ≤ C'ε`, `‖∇^λ𝓛‖_{𝓜²(λ)} ≤ C'ε` | `freezing_three_ae_bound`, `freezing_three_eLpNorm_le`, with `dν/dμ = w/(1+h)` (`toReal_rnDeriv_wt_pert`) |
| freezing *(3)*: a trajectory moves `≤ C'ετ`; distance `η` needs time `≥ η/(C'ε)` | `freezing_three_flow`; as printed, `C' = 2(1+d)‖w‖_∞`: `nonlinear_freezing_three_general` |
| freezing, the last assertion | `freezing_last_instance` (the constant flow at `μ*` is a gradient flow, positive constant loss), `freezing_no_time_bound` (the negation, for every candidate bound) |
| dichotomy *(1)* first sentence, *(2)* first clause, general | `global_dichotomy_full_general` |
| rem:freezing *(i)*, *(iv)*: critical ⟹ balanced, general | `no_distant_equilibrium_one_general`, `balanced_of_isCriticalAlong` |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮̂, λ, T)` ergodic | ⚠ **weakened** to invariance (`IsInvariant T lam`) wherever ergodicity is unused — everywhere except the unique-maximizer clause of *(2)*, which carries `ErgodicG` (invariance + every finite `T`-fixed `μ ≪ λ` is a multiple of `λ`, `universality.tex`'s definition at `ν_B = λ`, restricted to finite `μ`: a weaker hypothesis). Inhabited: `ergodicG_const` |
| `λ` finite, non-zero; a probability in freezing *(3)* | ✓ `[IsFiniteMeasure lam]`, `lam ≠ 0` where used; `[IsProbabilityMeasure lam]` in freezing *(3)* |
| `T` Markov | ✓ `[IsMarkovKernel T]` |
| `𝒮̂` a (Polish) measurable space | ✓ any measurable space: only the unique-maximizer and radial clauses use a reversal, taken as a hypothesis `IsReversalPair lam T R` (it exists on a standard Borel space, `Core.General.IsInvariant.isReversalPair_reversal`) |
| the hypotheses of `theo:first_variation_full` under which `∇^λ𝓛_{g,ν}(μ)` exists (`μ ∼ λ`, `dμ/dλ ∈ L²`, `ν ≪ μ`, `dν/dμ ∈ L^∞(μ)`, `r` essentially in `[ρ₀, ρ₁] ⊂ (0,∞)`, `g` continuously differentiable with locally Lipschitz derivative) | ⚠ **weakened**: `FirstVariationSetting` (`μT ≪ μ` derived; `g ∈ C¹` read as `g'` continuous on `ℝ₊*`, the only use; local Lipschitz of `g'` neither carried nor used). Inhabited off balance: `bool_witness` |
| `g` strictly unimodal | ✓ `StrictlyUnimodal gd` (`Balance.MassIdentity`, on `g'`) |
| `dν/dμ > 0` `μ`-a.e. | ✓ `hν` |
| `g̃` `C¹`, loc. Lipschitz `g̃'`, `g̃' ≡ 0`/`> 0` on the bands | ⚠ **weakened**: only `g̃' = 0` on the bands is used for `D = 0`; the rest is for the dynamics / first variation, not consumed |
| freezing *(3)*: `w ∈ L^∞`, `w ≥ 0`, `‖h‖_∞ ≤ 1/2`, `|g̃'| ≤ ε` on the bands | ✓ carried; `w`, `h` measurable (implicit in the paper) |
| the gradient flow | `IsGradientFlowG`: a curve `u : ℝ → L²(λ)` of densities of `μ_t`, `u̇ = −D(μ_t)` for `t ≥ 0` (kb 0025). Inhabited off balance: `bool_frozen_flow` |

## SCOPE (disclosed)

* **`D` is the gradient density by `theo:first_variation_full`, which is another lane's (general
  form not yet in the library).** Here `D = Tφ − rφ` is a definition, exactly as in the finite
  files before the finite first variation landed. *Critical* is read as `D = 0` `λ`-a.e. (the
  paper's "at a critical point `D = 0`"). The derivative reading is supplied conditionally:
  `FirstVariationFull T lam ν g μ Adm D` is the first variation's conclusion (directional
  derivatives along `μ + sδ`, `δ = eλ`, `e ∈ Adm`, equal to `⟨D, e⟩_{L²(λ)}`), taken as a
  **named hypothesis** with `Adm` abstract so the other lane's admissible class can be substituted;
  `isCriticalAlong_of_ae_zero` and `balanced_of_isCriticalAlong` consume it.
  `balanced_of_isCriticalAlong` also asks a non-zero constant direction `cλ ∈ Adm`, which is
  admissible in the paper's class iff `dλ/dμ ∈ L^∞(μ)`, i.e. `u` is essentially bounded below.
* **The gradient flow in `𝓜²(λ)` is hypothesised, never constructed**, as the paper does on a
  general space (existence is claimed only for finite state spaces, item *(3)*, closed in
  `Balance/GlobalConvergenceFinite.lean`). The flow theorems ask the first-variation setting at
  every time. `IsGradientFlowG` is witnessed off balance only by a constant curve at a frozen
  flow (`bool_frozen_flow`); no non-constant solution, and none with a strictly unimodal
  generator, is exhibited, so `no_distant_equilibrium_two_flow` is not shown non-vacuous off
  balance (kb 0025). Likewise `FirstVariationFull` with a non-empty `Adm` is inhabited nowhere:
  every theorem consuming it is conditional on a hypothesis no instance of this file discharges.
* **Freezing *(1)*'s finite-space half** (open set, locally constant, positive loss) stays in
  `Balance/FreezingGeneral.lean`; this file gives the general-space criticality.
* **Freezing *(3)* is proved on a general space**, with `D = Tφ − rφ` as defined here; that `D`
  is the density of `∇^λ𝓛_{g̃,ν}`, and that `IsGradientFlowG` is the paper's gradient flow, rests
  on the general `theo:first_variation_full`, as for every item of this file (first SCOPE
  bullet). Under that reading the finite residue recorded in the map is superseded by the general
  statement; no separate `Fintype` restatement is given.
* **The last assertion** is proved on the paper's own instance (`Fin 2`, the finite library's
  `IsGradientFlow`), as a negation quantified over every candidate bound
  `Tb(level, g''(1), (β̂ₙ), ν)`, within `C^∞` admissible generators with `g''(1) = 2`.
* **Strengthened, proved**: Cauchy–Schwarz and the unique maximizer are stated for every finite
  `λ ≠ 0` (`∫u ≤ √λ(𝒮)·‖u‖`), the paper's `∫u ≤ ‖u‖` being the probability case.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GFNBounds.Balance.General

open GFNBounds.Core.General (IsInvariant IsReversalPair)

variable {S : Type*} [MeasurableSpace S]

/-- `r = d(μT)/dμ`. -/
noncomputable def ratioG (T : Kernel S S) (μ : Measure S) : S → ℝ :=
  fun x => ((T ∘ₘ μ).rnDeriv μ x).toReal

/-- `φ = g'(r)·dν/dμ`. -/
noncomputable def potG (T : Kernel S S) (μ ν : Measure S) (gd : ℝ → ℝ) : S → ℝ :=
  fun x => gd (ratioG T μ x) * (ν.rnDeriv μ x).toReal

/-- `D = Tφ − rφ`. -/
noncomputable def gradDensityG (T : Kernel S S) (μ ν : Measure S) (gd : ℝ → ℝ) : S → ℝ :=
  fun x => Core.General.funAct T (potG T μ ν gd) x - ratioG T μ x * potG T μ ν gd x

/-- `μT = μ`. -/
def BalancedG (T : Kernel S S) (μ : Measure S) : Prop := T ∘ₘ μ = μ

section Basic

variable {T : Kernel S S} {lam μ : Measure S}

theorem measurable_ratioG (T : Kernel S S) (μ : Measure S) : Measurable (ratioG T μ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- `λ ≪ μT` when `λ ≪ μ` and `λ` is `T`-invariant. -/
theorem absolutelyContinuous_comp (hinv : IsInvariant T lam) (hlm : lam ≪ μ) :
    lam ≪ T ∘ₘ μ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.bind_apply hs T.aemeasurable] at hs0
  have h1 : ∀ᵐ y ∂μ, T y s = 0 :=
    (lintegral_eq_zero_iff (T.measurable_coe hs)).1 hs0
  have h2 : ∀ᵐ y ∂lam, T y s = 0 := hlm.ae_le h1
  rw [← hinv, Measure.bind_apply hs T.aemeasurable]
  exact lintegral_eq_zero_of_ae_eq_zero h2

/-- `μT ≪ μ` when `μ ∼ λ` and `λ` is `T`-invariant. -/
theorem comp_absolutelyContinuous_self (hinv : IsInvariant T lam) (hml : μ ≪ lam)
    (hlm : lam ≪ μ) : T ∘ₘ μ ≪ μ :=
  (hinv.comp_absolutelyContinuous hml).trans hlm

/-- **`r > 0`, `μ`-a.e., derived**: `μ ≪ λ ≪ μT`. -/
theorem ratioG_pos [IsMarkovKernel T] [IsFiniteMeasure μ] (hinv : IsInvariant T lam) (hml : μ ≪ lam)
    (hlm : lam ≪ μ) : ∀ᵐ x ∂μ, 0 < ratioG T μ x := by
  have hac : μ ≪ T ∘ₘ μ := hml.trans (absolutelyContinuous_comp hinv hlm)
  filter_upwards [Measure.rnDeriv_pos' hac, Measure.rnDeriv_lt_top (T ∘ₘ μ) μ] with x h0 htop
  exact ENNReal.toReal_pos h0.ne' htop.ne

/-- **`r = 1` `μ`-a.e. iff `μ` is balanced.** -/
theorem ratioG_eq_one_iff [IsMarkovKernel T] [IsFiniteMeasure μ] (hinv : IsInvariant T lam) (hml : μ ≪ lam)
    (hlm : lam ≪ μ) : (∀ᵐ x ∂μ, ratioG T μ x = 1) ↔ BalancedG T μ := by
  have hac := comp_absolutelyContinuous_self hinv hml hlm
  rw [BalancedG, ← Measure.rnDeriv_eq_one_iff_eq hac]
  constructor
  · intro h
    filter_upwards [h, Measure.rnDeriv_lt_top (T ∘ₘ μ) μ] with x hx htop
    rw [ratioG, ENNReal.toReal_eq_one_iff] at hx
    exact hx
  · intro h
    filter_upwards [h] with x hx
    rw [ratioG, hx]; rfl

end Basic


section Setting

/-- **The hypotheses of `theo:first_variation_full` at `μ`**, with `ν_G = λ`: `μ ∼ λ`,
`dμ/dλ ∈ L²(λ)`, `ν ≪ μ` with `dν/dμ ∈ L^∞(μ)`, `r` essentially bounded away from `0` and `∞`,
`g'` continuous on `ℝ₊*` (the paper's `C¹`; the locally Lipschitz derivative is not carried). `μT ≪ μ` is derived (`comp_absolutelyContinuous_self`),
not asked. -/
structure FirstVariationSetting (T : Kernel S S) (lam μ ν : Measure S) (gd : ℝ → ℝ) : Prop where
  ac : μ ≪ lam
  ac' : lam ≪ μ
  memL2 : MemLp (fun x => (μ.rnDeriv lam x).toReal) 2 lam
  nu_ac : ν ≪ μ
  ratio_bdd : ∃ ρ₀ ρ₁ : ℝ, 0 < ρ₀ ∧ ∀ᵐ x ∂μ, ratioG T μ x ∈ Set.Icc ρ₀ ρ₁
  dens_bdd : ∃ W : ℝ, ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal ≤ W
  gd_cont : ContinuousOn gd (Set.Ioi 0)

variable {T : Kernel S S} {lam μ ν : Measure S} {gd : ℝ → ℝ}

/-- `g' ∘ r` is `λ`-a.e. strongly measurable when `g'` is continuous on `ℝ₊*` and `r > 0` a.e. -/
theorem aestronglyMeasurable_gd_comp (hgd : ContinuousOn gd (Set.Ioi 0))
    (hr : ∀ᵐ x ∂lam, 0 < ratioG T μ x) :
    AEStronglyMeasurable (fun x => gd (ratioG T μ x)) lam := by
  classical
  have hm : Measurable ((Set.Ioi (0 : ℝ)).piecewise gd (fun _ => 0)) :=
    hgd.measurable_piecewise continuousOn_const measurableSet_Ioi
  refine ⟨fun x => (Set.Ioi (0 : ℝ)).piecewise gd (fun _ => 0) (ratioG T μ x),
    (hm.comp (measurable_ratioG T μ)).stronglyMeasurable, ?_⟩
  filter_upwards [hr] with x hx
  simp [Set.piecewise, Set.mem_Ioi.2 hx]

theorem FirstVariationSetting.ratio_pos_lam [IsMarkovKernel T] [IsFiniteMeasure μ]
    (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd) :
    ∀ᵐ x ∂lam, 0 < ratioG T μ x :=
  h.ac'.ae_le (ratioG_pos hinv h.ac h.ac')

/-- Under the first-variation setting, `φ = g'(r)dν/dμ` and `rφ` are bounded `λ`-a.e. -/
theorem FirstVariationSetting.bound (h : FirstVariationSetting T lam μ ν gd) :
    ∃ C : ℝ, ∀ᵐ x ∂lam, ‖potG T μ ν gd x‖ ≤ C ∧ ‖ratioG T μ x * potG T μ ν gd x‖ ≤ C := by
  obtain ⟨ρ₀, ρ₁, hρ₀, hr⟩ := h.ratio_bdd
  obtain ⟨W, hW⟩ := h.dens_bdd
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := ρ₀) (b := ρ₁)).exists_bound_of_continuousOn
    (h.gd_cont.mono fun z hz => lt_of_lt_of_le hρ₀ hz.1)
  refine ⟨max 0 M * max 0 W * max 1 ρ₁, ?_⟩
  filter_upwards [h.ac'.ae_le hr, h.ac'.ae_le hW] with x hx hWx
  have hg : ‖gd (ratioG T μ x)‖ ≤ max 0 M := (hM _ hx).trans (le_max_right _ _)
  have hw : ‖(ν.rnDeriv μ x).toReal‖ ≤ max 0 W := by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hWx.trans (le_max_right _ _)
  have hφ : ‖potG T μ ν gd x‖ ≤ max 0 M * max 0 W := by
    simp only [potG, norm_mul]
    exact mul_le_mul hg hw (norm_nonneg _) (le_max_left _ _)
  have hr0 : 0 ≤ ratioG T μ x := hρ₀.le.trans hx.1
  have hA : 0 ≤ max 0 M * max 0 W := mul_nonneg (le_max_left _ _) (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · calc ‖potG T μ ν gd x‖ ≤ max 0 M * max 0 W := hφ
      _ = max 0 M * max 0 W * 1 := (mul_one _).symm
      _ ≤ max 0 M * max 0 W * max 1 ρ₁ := mul_le_mul_of_nonneg_left (le_max_left _ _) hA
  · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hr0, mul_comm]
    exact mul_le_mul hφ (hx.2.trans (le_max_right _ _)) hr0 hA

theorem FirstVariationSetting.aestronglyMeasurable_pot [IsMarkovKernel T] [IsFiniteMeasure μ]
    (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd) :
    AEStronglyMeasurable (potG T μ ν gd) lam :=
  (aestronglyMeasurable_gd_comp h.gd_cont (h.ratio_pos_lam hinv)).mul
    (Measure.measurable_rnDeriv ν μ).ennreal_toReal.aestronglyMeasurable

theorem FirstVariationSetting.memLp_pot [IsMarkovKernel T] [IsFiniteMeasure μ]
    [IsFiniteMeasure lam] (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd)
    (p : ℝ≥0∞) : MemLp (potG T μ ν gd) p lam := by
  obtain ⟨C, hC⟩ := h.bound
  exact MemLp.of_bound (h.aestronglyMeasurable_pot hinv) C (hC.mono fun _ hx => hx.1)

theorem FirstVariationSetting.memLp_rpot [IsMarkovKernel T] [IsFiniteMeasure μ]
    [IsFiniteMeasure lam] (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd)
    (p : ℝ≥0∞) : MemLp (fun x => ratioG T μ x * potG T μ ν gd x) p lam := by
  obtain ⟨C, hC⟩ := h.bound
  exact MemLp.of_bound ((measurable_ratioG T μ).aestronglyMeasurable.mul
    (h.aestronglyMeasurable_pot hinv)) C (hC.mono fun _ hx => hx.2)

theorem FirstVariationSetting.integrable_pot [IsMarkovKernel T] [IsFiniteMeasure μ]
    [IsFiniteMeasure lam] (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd) :
    Integrable (potG T μ ν gd) lam :=
  memLp_one_iff_integrable.1 (h.memLp_pot hinv 1)

theorem FirstVariationSetting.integrable_rpot [IsMarkovKernel T] [IsFiniteMeasure μ]
    [IsFiniteMeasure lam] (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd) :
    Integrable (fun x => ratioG T μ x * potG T μ ν gd x) lam :=
  memLp_one_iff_integrable.1 (h.memLp_rpot hinv 1)

end Setting

section Mass

variable {T : Kernel S S} [IsMarkovKernel T] {lam μ ν : Measure S} {gd : ℝ → ℝ}

/-- `∫ Tφ dλ = ∫ φ dλ` for `φ ∈ L¹(λ)`, `λ` being `T`-invariant (`P1 = 1`, read on the adjoint). -/
theorem integral_funAct_eq [SFinite lam] (hinv : IsInvariant T lam) {φ : S → ℝ}
    (hφ : Integrable φ lam) :
    ∫ x, Core.General.funAct T φ x ∂lam = ∫ x, φ x ∂lam := by
  have hmp := hinv.measurePreserving_snd_compProd
  have hI : Integrable (fun z : S × S => φ z.2) (lam ⊗ₘ T) := memLp_one_iff_integrable.1 ((memLp_one_iff_integrable.2 hφ).comp_measurePreserving hmp)
  calc ∫ x, Core.General.funAct T φ x ∂lam = ∫ z, φ z.2 ∂(lam ⊗ₘ T) :=
        (Measure.integral_compProd hI).symm
    _ = ∫ y, φ y ∂(Measure.map Prod.snd (lam ⊗ₘ T)) :=
        (integral_map measurable_snd.aemeasurable (by rw [hmp.map_eq]; exact hφ.1)).symm
    _ = ∫ y, φ y ∂lam := by rw [hmp.map_eq]

/-- **`prop:no_distant_equilibrium`*(1)*, the identity**: `∫ D dλ = ∫ g'(r)(1 − r)(dν/dμ) dλ`. -/
theorem integral_gradDensityG [SFinite lam] (hinv : IsInvariant T lam)
    (hφ : Integrable (potG T μ ν gd) lam)
    (hrφ : Integrable (fun x => ratioG T μ x * potG T μ ν gd x) lam) :
    ∫ x, gradDensityG T μ ν gd x ∂lam
      = ∫ x, gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal ∂lam := by
  have hT : Integrable (Core.General.funAct T (potG T μ ν gd)) lam :=
    memLp_one_iff_integrable.1 (hinv.memLp_funAct le_rfl (memLp_one_iff_integrable.2 hφ))
  have h1 : ∫ x, gradDensityG T μ ν gd x ∂lam
      = ∫ x, potG T μ ν gd x ∂lam - ∫ x, ratioG T μ x * potG T μ ν gd x ∂lam := by
    simp only [gradDensityG]
    rw [integral_sub hT hrφ, integral_funAct_eq hinv hφ]
  rw [h1, ← integral_sub hφ hrφ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [potG]
  ring

/-- The integrand `g'(r)(1 − r)(dν/dμ)` is `≤ 0` wherever `r > 0`, for strictly unimodal `g`. -/
theorem integrand_nonpos (hg : StrictlyUnimodal gd) {r w : ℝ} (hr : 0 < r) (hw : 0 ≤ w) :
    gd r * (1 - r) * w ≤ 0 := by
  rcases eq_or_ne r 1 with h | h
  · rw [h]; simp
  · have := hg r hr h
    have h2 : gd r * (1 - r) ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg h2 hw

/-- **`prop:no_distant_equilibrium`*(1)*, the sign**: `∫ g'(r)(1 − r)(dν/dμ) dλ ≤ 0`. -/
theorem mass_nonpos [IsFiniteMeasure μ] (hinv : IsInvariant T lam) (hml : μ ≪ lam)
    (hlm : lam ≪ μ) (hg : StrictlyUnimodal gd) :
    ∫ x, gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal ∂lam ≤ 0 := by
  refine integral_nonpos_of_ae ?_
  filter_upwards [hlm.ae_le (ratioG_pos hinv hml hlm)] with x hx
  exact integrand_nonpos hg hx ENNReal.toReal_nonneg

/-- **`prop:no_distant_equilibrium`*(1)*, the equality case**: for `dν/dμ > 0` `μ`-a.e., the
mass vanishes iff `μ` is balanced. -/
theorem mass_eq_zero_iff [SFinite lam] [IsFiniteMeasure μ] (hinv : IsInvariant T lam)
    (hml : μ ≪ lam) (hlm : lam ≪ μ) (hg : StrictlyUnimodal gd)
    (hφ : Integrable (potG T μ ν gd) lam)
    (hrφ : Integrable (fun x => ratioG T μ x * potG T μ ν gd x) lam)
    (hν : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal) :
    ∫ x, gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal ∂lam = 0
      ↔ BalancedG T μ := by
  rw [← ratioG_eq_one_iff hinv hml hlm]
  have hint : Integrable
      (fun x => gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal) lam := by
    refine (hφ.sub hrφ).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [potG, Pi.sub_apply]; ring
  have hr := hlm.ae_le (ratioG_pos hinv hml hlm)
  constructor
  · intro h0
    have hneg : ∫ x, -(gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal) ∂lam
        = 0 := by rw [integral_neg, h0, neg_zero]
    have hnn : 0 ≤ᵐ[lam] fun x =>
        -(gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal) := by
      filter_upwards [hr] with x hx
      exact neg_nonneg.2 (integrand_nonpos hg hx ENNReal.toReal_nonneg)
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint.neg).1 hneg
    refine hml.ae_le ?_
    filter_upwards [hz, hr, hlm.ae_le hν] with x hx hrx hνx
    simp only [Pi.zero_apply, neg_eq_zero] at hx
    by_contra hne
    have h1 := hg _ hrx hne
    have h2 : gd (ratioG T μ x) * (1 - ratioG T μ x) = 0 := by
      rcases mul_eq_zero.1 hx with h | h
      · exact h
      · exact absurd h hνx.ne'
    nlinarith
  · intro h1
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hlm.ae_le h1] with x hx
    simp [hx]

/-- **`prop:no_distant_equilibrium`*(1)*, critical ⟹ balanced**: `D = 0` `λ`-a.e. forces balance. -/
theorem balanced_of_criticalG [SFinite lam] [IsFiniteMeasure μ] (hinv : IsInvariant T lam)
    (hml : μ ≪ lam) (hlm : lam ≪ μ) (hg : StrictlyUnimodal gd)
    (hφ : Integrable (potG T μ ν gd) lam)
    (hrφ : Integrable (fun x => ratioG T μ x * potG T μ ν gd x) lam)
    (hν : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal)
    (hD : gradDensityG T μ ν gd =ᵐ[lam] 0) : BalancedG T μ := by
  refine (mass_eq_zero_iff hinv hml hlm hg hφ hrφ hν).1 ?_
  rw [← integral_gradDensityG hinv hφ hrφ, integral_congr_ae hD]
  simp

end Mass

section Freezing

variable {T : Kernel S S} {lam μ : Measure S} {gd : ℝ → ℝ}

/-- **`prop:nonlinear_freezing`*(1)*, general**: if `r` takes its values `λ`-a.e. in a set on
which `g̃'` vanishes, then `φ = 0` and `D = Tφ − rφ = 0` `λ`-a.e., for **every** `ν`. -/
theorem gradDensityG_eq_zero_of_band (hinv : IsInvariant T lam) {U : Set ℝ}
    (hband : ∀ᵐ x ∂lam, ratioG T μ x ∈ U) (hgd0 : ∀ z ∈ U, gd z = 0) (ν : Measure S) :
    gradDensityG T μ ν gd =ᵐ[lam] 0 := by
  have hφ : potG T μ ν gd =ᵐ[lam] fun _ => 0 := by
    filter_upwards [hband] with x hx
    simp [potG, hgd0 _ hx]
  filter_upwards [hφ, hinv.funAct_congr hφ] with x hx hTx
  have hT0 : Core.General.funAct T (fun _ => (0 : ℝ)) x = 0 := by
    simp [Core.General.funAct]
  simp only [gradDensityG, Pi.zero_apply, hTx, hT0, hx, mul_zero, sub_zero]

end Freezing

section Criticality

/-- **The loss `𝓛_{g,ν}(μ) = ∫ g(r) dν`** at a fixed training measure `ν`. -/
noncomputable def lossG (T : Kernel S S) (ν : Measure S) (g : ℝ → ℝ) (μ : Measure S) : ℝ :=
  ∫ x, g (ratioG T μ x) ∂ν

/-- The line `s ↦ μ + sδ` through `μ = uλ` in the direction `δ = eλ`, as the flow of `λ`-density
`u + se` (clipped at `0`, which the admissible directions never reach). -/
noncomputable def lineG (lam : Measure S) (u e : S → ℝ) (s : ℝ) : Measure S :=
  lam.withDensity fun x => ENNReal.ofReal (u x + s * e x)

/-- **The conclusion of `theo:first_variation_full` at `μ`, with `ν_G = λ`**, on a class `Adm` of
admissible directions given by their `λ`-densities: along every `δ = eλ`, `e ∈ Adm`, the derivative
of `s ↦ 𝓛_{g,ν}(μ + sδ)` at `0` is `⟨D, e⟩_{L²(λ)}`. This is a *hypothesis* here — the general
first variation is another lane's (see the module SCOPE); `Adm` is left abstract so that it can be
instantiated with that lane's admissible class. -/
def FirstVariationFull (T : Kernel S S) (lam ν : Measure S) (g : ℝ → ℝ) (μ : Measure S)
    (Adm : Set (S → ℝ)) (D : S → ℝ) : Prop :=
  ∀ e ∈ Adm, HasDerivAt (fun s => lossG T ν g (lineG lam (fun x => (μ.rnDeriv lam x).toReal) e s))
    (∫ x, D x * e x ∂lam) 0

/-- **Critical along `Adm`**: every admissible directional derivative vanishes. -/
def IsCriticalAlong (T : Kernel S S) (lam ν : Measure S) (g : ℝ → ℝ) (μ : Measure S)
    (Adm : Set (S → ℝ)) : Prop :=
  ∀ e ∈ Adm, HasDerivAt (fun s => lossG T ν g (lineG lam (fun x => (μ.rnDeriv lam x).toReal) e s))
    0 0

variable {T : Kernel S S} {lam μ ν : Measure S} {g : ℝ → ℝ} {Adm : Set (S → ℝ)} {D : S → ℝ}

/-- A vanishing gradient density makes `μ` critical along every admissible direction. -/
theorem isCriticalAlong_of_ae_zero (hFV : FirstVariationFull T lam ν g μ Adm D)
    (hD : D =ᵐ[lam] 0) : IsCriticalAlong T lam ν g μ Adm := by
  intro e he
  have h := hFV e he
  have h0 : ∫ x, D x * e x ∂lam = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hD] with x hx
    simp [hx]
  rwa [h0] at h

/-- At a critical point, the gradient density is orthogonal to every admissible direction. -/
theorem integral_mul_eq_zero_of_critical (hFV : FirstVariationFull T lam ν g μ Adm D)
    (hc : IsCriticalAlong T lam ν g μ Adm) {e : S → ℝ} (he : e ∈ Adm) :
    ∫ x, D x * e x ∂lam = 0 :=
  (hFV e he).unique (hc e he)

end Criticality

section Sphere

variable {T R : Kernel S S} [IsMarkovKernel T] {lam μ ν : Measure S} {gd g : ℝ → ℝ}

/-- `d(μT)/dλ = r·u`, `λ`-a.e., for `μ ∼ λ`. -/
theorem toReal_rnDeriv_comp_eq [IsFiniteMeasure lam] [IsFiniteMeasure μ]
    (hinv : IsInvariant T lam) (hml : μ ≪ lam) (hlm : lam ≪ μ) :
    (fun x => ((T ∘ₘ μ).rnDeriv lam x).toReal)
      =ᵐ[lam] fun x => ratioG T μ x * (μ.rnDeriv lam x).toReal := by
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := lam)
    (comp_absolutelyContinuous_self hinv hml hlm)] with x hx
  rw [← hx, Pi.mul_apply, ENNReal.toReal_mul]
  rfl

/-- **`prop:no_distant_equilibrium`*(2)*, the radial orthogonality** `⟨D, u⟩_{L²(λ)} = 0`
(`proofs.tex`, proof of *(2)*): the gradient is orthogonal to the radial direction. Through
`lem:adjoint`*(3)*: `∫ (Tφ)u dλ = ∫ φ·T^λu dλ` and `T^λu = d(μT)/dλ = ru`. -/
theorem integral_gradDensityG_mul_dens [IsMarkovKernel R] [IsFiniteMeasure lam]
    [IsFiniteMeasure μ] (hR : IsReversalPair lam T R) (hml : μ ≪ lam) (hlm : lam ≪ μ)
    (hφ : MemLp (potG T μ ν gd) 2 lam)
    (hrφ : MemLp (fun x => ratioG T μ x * potG T μ ν gd x) 2 lam)
    (hu : MemLp (fun x => (μ.rnDeriv lam x).toReal) 2 lam) :
    ∫ x, gradDensityG T μ ν gd x * (μ.rnDeriv lam x).toReal ∂lam = 0 := by
  have hinv : IsInvariant T lam := hR.symm.isInvariant
  set u : S → ℝ := fun x => (μ.rnDeriv lam x).toReal with hu_def
  set φ := potG T μ ν gd with hφ_def
  have hadj : ∫ x, φ x * Core.General.funAct R u x ∂lam
      = ∫ x, Core.General.funAct T φ x * u x ∂lam := hR.integral_mul_funAct hφ hu
  have hRu : Core.General.funAct R u =ᵐ[lam] fun x => ratioG T μ x * u x :=
    (hR.toReal_rnDeriv_comp hml).symm.trans (toReal_rnDeriv_comp_eq hinv hml hlm)
  have hTφ : MemLp (Core.General.funAct T φ) 2 lam := hinv.memLp_funAct one_le_two hφ
  have hI1 : Integrable (fun x => Core.General.funAct T φ x * u x) lam :=
    hTφ.integrable_mul hu
  have hI2 : Integrable (fun x => ratioG T μ x * φ x * u x) lam := hrφ.integrable_mul hu
  have hsplit : ∫ x, gradDensityG T μ ν gd x * u x ∂lam
      = ∫ x, Core.General.funAct T φ x * u x ∂lam - ∫ x, ratioG T μ x * φ x * u x ∂lam := by
    rw [← integral_sub hI1 hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [gradDensityG, hφ_def]; ring
  rw [hsplit, ← hadj, sub_eq_zero]
  refine integral_congr_ae ?_
  filter_upwards [hRu] with x hx
  rw [hx]; ring

/-- **`prop:no_distant_equilibrium`*(2)*, scale invariance of the ratio**: `r(cμ) = r(μ)`,
`μ`-a.e., for `0 < c < ∞`. -/
theorem ratioG_smul [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    ratioG T (c • μ) =ᵐ[μ] ratioG T μ := by
  haveI := μ.smul_finite hct
  have h1 : (c • (T ∘ₘ μ)).rnDeriv (c • μ) =ᵐ[c • μ] c • (T ∘ₘ μ).rnDeriv (c • μ) :=
    Measure.rnDeriv_smul_left_of_ne_top' _ _ hct
  have h2 : (T ∘ₘ μ).rnDeriv (c • μ) =ᵐ[μ] c⁻¹ • (T ∘ₘ μ).rnDeriv μ :=
    Measure.rnDeriv_smul_right_of_ne_top' _ _ hc0 hct
  have hac : μ ≪ c • μ := Measure.absolutelyContinuous_smul hc0
  filter_upwards [hac.ae_le h1, h2] with x hx1 hx2
  simp only [ratioG, Measure.comp_smul]
  rw [hx1, Pi.smul_apply, hx2, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hc0 hct, one_mul]

/-- **`prop:no_distant_equilibrium`*(2)*, scale invariance of the loss** at fixed `ν ≪ μ`:
`𝓛_{g,ν}(cμ) = 𝓛_{g,ν}(μ)`. -/
theorem lossG_smul [IsFiniteMeasure μ] (hνμ : ν ≪ μ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    lossG T ν g (c • μ) = lossG T ν g μ := by
  refine integral_congr_ae ?_
  filter_upwards [hνμ.ae_le (ratioG_smul (T := T) hc0 hct)] with x hx
  rw [hx]

/-- **Cauchy–Schwarz against `1` on a finite measure, with its equality case**: for `u ∈ L²(λ)`
and `L = λ(𝒮)`, `(∫u)² ≤ L ∫u²`, and equality holds iff `u` is `λ`-a.e. the constant `∫u / L`. -/
theorem sq_integral_le_integral_sq [IsFiniteMeasure lam] (hlam : lam ≠ 0) {u : S → ℝ}
    (hu : MemLp u 2 lam) :
    (∫ x, u x ∂lam) ^ 2 ≤ lam.real Set.univ * ∫ x, u x ^ 2 ∂lam
      ∧ ((∫ x, u x ∂lam) ^ 2 = lam.real Set.univ * ∫ x, u x ^ 2 ∂lam
          ↔ u =ᵐ[lam] fun _ => (∫ x, u x ∂lam) / lam.real Set.univ) := by
  set m := ∫ x, u x ∂lam
  set L := lam.real Set.univ with hL
  have hL0 : 0 < L := by
    rw [hL, measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hlam) (measure_ne_top _ _)
  set k := m / L
  have hI : Integrable u lam := hu.integrable one_le_two
  have hI2 : Integrable (fun x => u x ^ 2) lam := hu.integrable_sq
  have hid : ∫ x, (u x - k) ^ 2 ∂lam = ∫ x, u x ^ 2 ∂lam - m ^ 2 / L := by
    have hexp : (fun x => (u x - k) ^ 2) = fun x => (u x ^ 2 - 2 * k * u x) + k ^ 2 := by
      funext x; ring
    rw [hexp, integral_add (f := fun x => u x ^ 2 - 2 * k * u x) (g := fun _ => k ^ 2)
      (hI2.sub (hI.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => u x ^ 2) (g := fun x => 2 * k * u x) hI2 (hI.const_mul _),
      integral_const_mul, integral_const, smul_eq_mul]
    simp only [k]
    field_simp
    ring
  have hnn : 0 ≤ ∫ x, (u x - k) ^ 2 ∂lam := integral_nonneg fun x => sq_nonneg _
  have hkey : m ^ 2 ≤ L * ∫ x, u x ^ 2 ∂lam := by
    have : m ^ 2 / L ≤ ∫ x, u x ^ 2 ∂lam := by linarith
    rwa [div_le_iff₀ hL0, mul_comm] at this
  refine ⟨hkey, ?_⟩
  have hI3 : Integrable (fun x => (u x - k) ^ 2) lam := by
    have := (hu.sub (memLp_const k)).integrable_sq
    simpa using this
  constructor
  · intro h
    have h0 : ∫ x, (u x - k) ^ 2 ∂lam = 0 := by
      rw [hid, h]; field_simp; ring
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (u x - k)) hI3).1 h0
    filter_upwards [hz] with x hx
    simp only [Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero] at hx
    exact hx
  · intro h
    have h0 : ∫ x, (u x - k) ^ 2 ∂lam = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [h] with x hx
      simp [hx, k]
    rw [hid, sub_eq_zero, eq_div_iff hL0.ne'] at h0
    rw [← h0, mul_comm]

/-- **Ergodicity** of `(𝒮̂, λ, T)`: `λ` is `T`-invariant and the only finite `μ ≪ λ` that `T`
fixes are the multiples of `λ` (`universality.tex`, the definition of `ν_B`-ergodic, at
`ν_B = λ`). -/
def ErgodicG (T : Kernel S S) (lam : Measure S) : Prop :=
  IsInvariant T lam ∧ ∀ μ : Measure S, IsFiniteMeasure μ → μ ≪ lam → T ∘ₘ μ = μ →
    ∃ c : ℝ≥0∞, μ = c • lam

/-- The identity kernel is not ergodic in general; the constant kernel is: every probability `π`
is ergodic for resampling from `π` (a witness that `ErgodicG` is inhabited). -/
theorem ergodicG_const (π : Measure S) [IsProbabilityMeasure π] :
    ErgodicG (Kernel.const S π) π := by
  refine ⟨Core.General.isInvariant_const π, fun μ _ _ hfix => ⟨μ Set.univ, ?_⟩⟩
  rw [Measure.const_comp] at hfix; exact hfix.symm

omit [IsMarkovKernel T] in
/-- **Under ergodicity, balanced ⟺ constant density.** -/
theorem balancedG_iff_const [IsFiniteMeasure lam] [IsFiniteMeasure μ] (hT : ErgodicG T lam)
    (hml : μ ≪ lam) :
    BalancedG T μ ↔ ∃ k : ℝ, (fun x => (μ.rnDeriv lam x).toReal) =ᵐ[lam] fun _ => k := by
  constructor
  · intro hb
    obtain ⟨c, hc⟩ := hT.2 μ inferInstance hml hb
    rcases eq_or_ne lam 0 with h0 | h0
    · subst h0
      exact ⟨0, by simp [Filter.EventuallyEq]⟩
    have hct : c ≠ ∞ := by
      intro h
      have := measure_ne_top μ Set.univ
      rw [hc, h, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul] at this
      · exact this rfl
      · simpa using h0
    refine ⟨c.toReal, ?_⟩
    have h1 : (c • lam).rnDeriv lam =ᵐ[lam] c • lam.rnDeriv lam :=
      Measure.rnDeriv_smul_left_of_ne_top' _ _ hct
    filter_upwards [h1, Measure.rnDeriv_self lam] with x hx hself
    rw [hc, hx, Pi.smul_apply, hself, smul_eq_mul, mul_one]
  · rintro ⟨k, hk⟩
    have hμ : μ = ENNReal.ofReal k • lam := by
      rw [← Measure.withDensity_rnDeriv_eq μ lam hml, ← withDensity_const]
      refine withDensity_congr_ae ?_
      filter_upwards [hk, Measure.rnDeriv_lt_top μ lam] with x hx htop
      rw [← hx, ENNReal.ofReal_toReal htop.ne]
    rw [BalancedG, hμ, Measure.comp_smul, hT.1]

omit [IsMarkovKernel T] in
/-- **`prop:no_distant_equilibrium`*(2)*, the unique maximizer**: the mass `∫u dλ` of a flow is at
most `√λ(𝒮) ‖u‖_{L²(λ)}` (`‖u‖_{L²(λ)}` when `λ` is a probability), with equality iff the flow is
balanced — under ergodicity, the balanced flow is the unique maximizer of the mass on its sphere. -/
theorem mass_le_nrm_and_eq_iff_balanced [IsFiniteMeasure lam] [IsFiniteMeasure μ]
    (hT : ErgodicG T lam) (hlam : lam ≠ 0) (hml : μ ≪ lam)
    (hu : MemLp (fun x => (μ.rnDeriv lam x).toReal) 2 lam) :
    ∫ x, (μ.rnDeriv lam x).toReal ∂lam
        ≤ Real.sqrt (lam.real Set.univ * ∫ x, (μ.rnDeriv lam x).toReal ^ 2 ∂lam)
      ∧ (∫ x, (μ.rnDeriv lam x).toReal ∂lam
          = Real.sqrt (lam.real Set.univ * ∫ x, (μ.rnDeriv lam x).toReal ^ 2 ∂lam)
            ↔ BalancedG T μ) := by
  obtain ⟨hle, hiff⟩ := sq_integral_le_integral_sq hlam hu
  set m := ∫ x, (μ.rnDeriv lam x).toReal ∂lam with hm
  set L := lam.real Set.univ with hL
  have hm0 : 0 ≤ m := integral_nonneg fun _ => ENNReal.toReal_nonneg
  have hQ0 : 0 ≤ L * ∫ x, (μ.rnDeriv lam x).toReal ^ 2 ∂lam :=
    mul_nonneg measureReal_nonneg (integral_nonneg fun _ => sq_nonneg _)
  refine ⟨Real.le_sqrt_of_sq_le hle, ?_⟩
  rw [balancedG_iff_const hT hml]
  constructor
  · intro h
    refine ⟨m / L, hiff.1 ?_⟩
    rw [h, Real.sq_sqrt hQ0]
  · rintro ⟨k, hk⟩
    have hkm : m = k * L := by
      rw [hm, integral_congr_ae hk, integral_const, smul_eq_mul, mul_comm]
    have hL0 : L ≠ 0 := by
      rw [hL, measureReal_def]
      exact (ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hlam) (measure_ne_top _ _)).ne'
    have hsq : m ^ 2 = L * ∫ x, (μ.rnDeriv lam x).toReal ^ 2 ∂lam :=
      hiff.2 (hk.trans (by rw [hkm, mul_div_cancel_right₀ _ hL0]))
    rw [← hsq, Real.sqrt_sq hm0]

end Sphere

section Flow

variable {T : Kernel S S} {lam : Measure S} [IsFiniteMeasure lam]
  {ν : Measure S} {gd : ℝ → ℝ}

/-- **The gradient flow `μ̇_t = −∇^λ 𝓛_{g,ν}(μ_t)` in `𝓜²(λ)`**, for `t ≥ 0`: a curve of flows
`μ_t` whose `λ`-densities form a curve `u : ℝ → L²(λ)` with derivative `−D(μ_t)`. Existence is not
claimed (the paper claims it only on finite state spaces, `prop:no_distant_equilibrium`*(3)*). -/
def IsGradientFlowG (T : Kernel S S) (lam ν : Measure S) (gd : ℝ → ℝ) (μ : ℝ → Measure S)
    (u : ℝ → Lp ℝ 2 lam) : Prop :=
  ∀ t, 0 ≤ t → (u t : S → ℝ) =ᵐ[lam] (fun x => ((μ t).rnDeriv lam x).toReal) ∧
    ∃ D : Lp ℝ 2 lam, (D : S → ℝ) =ᵐ[lam] gradDensityG T (μ t) ν gd ∧ HasDerivAt u (-D) t

omit [IsFiniteMeasure lam] in
theorem inner_Lp_eq (f g : Lp ℝ 2 lam) : inner ℝ f g = ∫ x, f x * g x ∂lam := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

omit [IsFiniteMeasure lam] in
/-- **`prop:no_distant_equilibrium`*(2)*: the gradient flow preserves `‖u_t‖_{L²(λ)}`**, given
the radial orthogonality `⟨D(μ_t), u_t⟩ = 0` at every time (`integral_gradDensityG_mul_dens`). -/
theorem norm_const_of_flow {μ : ℝ → Measure S} {u : ℝ → Lp ℝ 2 lam}
    (hflow : IsGradientFlowG T lam ν gd μ u)
    (hrad : ∀ t, 0 ≤ t →
      ∫ x, gradDensityG T (μ t) ν gd x * ((μ t).rnDeriv lam x).toReal ∂lam = 0)
    {t : ℝ} (ht : 0 ≤ t) : ‖u t‖ = ‖u 0‖ := by
  have hd : ∀ s ∈ Set.Ici (0 : ℝ), HasDerivAt (fun s => ‖u s‖ ^ 2) 0 s := by
    intro s hs
    obtain ⟨hdens, D, hD, hder⟩ := hflow s hs
    have h := hder.norm_sq
    have hi : inner ℝ (u s) (-D) = 0 := by
      rw [inner_neg_right, inner_Lp_eq, neg_eq_zero, ← hrad s hs]
      refine integral_congr_ae ?_
      filter_upwards [hdens, hD] with x h1 h2
      rw [h1, h2, mul_comm]
    rwa [hi, mul_zero] at h
  have := eq_of_hasDerivAt_zero_on (convex_Ici 0) hd (Set.self_mem_Ici) ht ht
  have h2 : ‖u t‖ ^ 2 = ‖u 0‖ ^ 2 := this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- The constant `1` in `L²(λ)`. -/
noncomputable def oneLp (lam : Measure S) [IsFiniteMeasure lam] : Lp ℝ 2 lam :=
  (memLp_const (1 : ℝ)).toLp _

theorem inner_oneLp (f : Lp ℝ 2 lam) : inner ℝ (oneLp lam) f = ∫ x, f x ∂lam := by
  rw [inner_Lp_eq]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℝ) (μ := lam) (p := 2))] with x hx
  simp only [oneLp] at *
  rw [hx, one_mul]

/-- **`prop:no_distant_equilibrium`*(2)*: the mass `∫u_t dλ` is non-decreasing along the flow**,
its derivative being `−∫D(μ_t) dλ ≥ 0`, and **strictly increasing off balance**: the derivative is
positive at every time where `μ_t` is not balanced. -/
theorem mass_hasDerivAt_of_flow {μ : ℝ → Measure S} {u : ℝ → Lp ℝ 2 lam}
    (hflow : IsGradientFlowG T lam ν gd μ u) {t : ℝ} (ht : 0 ≤ t) :
    ∃ D : Lp ℝ 2 lam, (D : S → ℝ) =ᵐ[lam] gradDensityG T (μ t) ν gd ∧
      HasDerivAt (fun s => ∫ x, u s x ∂lam) (-∫ x, gradDensityG T (μ t) ν gd x ∂lam) t := by
  obtain ⟨-, D, hD, hder⟩ := hflow t ht
  refine ⟨D, hD, ?_⟩
  have h := (hasDerivAt_const t (oneLp lam)).inner ℝ hder
  simp only [inner_zero_left, add_zero, inner_neg_right, inner_oneLp] at h
  rwa [integral_congr_ae hD] at h

/-- **`prop:no_distant_equilibrium`*(2)*, the mass ascent**: the mass is non-decreasing along the
flow on `[0, ∞)`. -/
theorem mass_monotoneOn_of_flow {μ : ℝ → Measure S} {u : ℝ → Lp ℝ 2 lam}
    (hflow : IsGradientFlowG T lam ν gd μ u)
    (hmass : ∀ t, 0 ≤ t → ∫ x, gradDensityG T (μ t) ν gd x ∂lam ≤ 0) :
    MonotoneOn (fun s => ∫ x, u s x ∂lam) (Set.Ici 0) := by
  have hd : ∀ s ∈ Set.Ici (0 : ℝ), HasDerivAt (fun s => ∫ x, u s x ∂lam)
      (-∫ x, gradDensityG T (μ s) ν gd x ∂lam) s := fun s hs =>
    (mass_hasDerivAt_of_flow hflow hs).choose_spec.2
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => ?_)
  rw [(hd s (interior_subset hs)).deriv]
  exact neg_nonneg.2 (hmass s (interior_subset hs))

end Flow

section FreezingThree

variable {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsProbabilityMeasure lam]
  {gd : ℝ → ℝ}

/-- The flow `(1 + h)λ`. -/
noncomputable def pertG (lam : Measure S) (h : S → ℝ) : Measure S :=
  lam.withDensity fun x => ENNReal.ofReal (1 + h x)

/-- The training measure `wλ`. -/
noncomputable def wtG (lam : Measure S) (w : S → ℝ) : Measure S :=
  lam.withDensity fun x => ENNReal.ofReal (w x)

instance pertG.sigmaFinite [SigmaFinite lam] (h : S → ℝ) : SigmaFinite (pertG lam h) :=
  SigmaFinite.withDensity_ofReal fun x => 1 + h x

instance wtG.sigmaFinite [SigmaFinite lam] (w : S → ℝ) : SigmaFinite (wtG lam w) :=
  SigmaFinite.withDensity_ofReal w

omit [IsProbabilityMeasure lam] in
/-- `dν/dμ = w/(1 + h)` for `ν = wλ`, `μ = (1 + h)λ`, `|h| ≤ 1/2`, `w ≥ 0`. -/
theorem toReal_rnDeriv_wt_pert [SigmaFinite lam] {w h : S → ℝ} (hwm : Measurable w)
    (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hhm : Measurable h) (hh : ∀ᵐ x ∂lam, |h x| ≤ 1 / 2) :
    ∀ᵐ x ∂lam, ((wtG lam w).rnDeriv (pertG lam h) x).toReal * (1 + h x) = w x := by
  have hne : ∀ᵐ x ∂lam, ENNReal.ofReal (1 + h x) ≠ 0 := by
    filter_upwards [hh] with x hx
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := (abs_le.1 hx).1; linarith
  have hlm : lam ≪ pertG lam h :=
    withDensity_absolutelyContinuous' (by fun_prop) hne
  have hνμ : wtG lam w ≪ pertG lam h := (withDensity_absolutelyContinuous _ _).trans hlm
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := lam) hνμ,
    Measure.rnDeriv_withDensity lam (show Measurable fun x => ENNReal.ofReal (1 + h x) by fun_prop),
    Measure.rnDeriv_withDensity lam (show Measurable fun x => ENNReal.ofReal (w x) by fun_prop),
    hh, hw0] with x hx h1 h2 hhx hwx
  simp only [Pi.mul_apply, pertG, wtG] at hx
  rw [h1, h2] at hx
  have h1h : 0 ≤ 1 + h x := by have := (abs_le.1 hhx).1; linarith
  have := congrArg ENNReal.toReal hx
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1h, ENNReal.toReal_ofReal hwx] at this

/-- **`prop:nonlinear_freezing`*(3)*, the pointwise bound**: on the set of flows `μ = (1 + h)λ`,
`‖h‖_∞ ≤ 1/2`, with band-valued ratio, `|D| ≤ 2(1 + d)Wε` `λ`-a.e., for `ν = wλ`, `0 ≤ w ≤ W`,
and `|g̃'| ≤ ε` on the bands. -/
theorem freezing_three_ae_bound (F : FreezingBands) (hinv : IsInvariant T lam) {ε W : ℝ}
    (hε : 0 ≤ ε) (hgd : ∀ z ∈ F.bands, |gd z| ≤ ε) {w h : S → ℝ} (hwm : Measurable w)
    (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwW : ∀ᵐ x ∂lam, w x ≤ W) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ 1 / 2)
    (hband : ∀ᵐ x ∂lam, ratioG T (pertG lam h) x ∈ F.bands) :
    ∀ᵐ x ∂lam, |gradDensityG T (pertG lam h) (wtG lam w) gd x| ≤ 2 * (1 + F.d) * W * ε := by
  set μ := pertG lam h
  set ν := wtG lam w
  have hW : 0 ≤ W := by
    obtain ⟨x, hx1, hx2⟩ := (hw0.and hwW).exists
    linarith
  have hq : ∀ᵐ x ∂lam, (ν.rnDeriv μ x).toReal ≤ 2 * W := by
    filter_upwards [toReal_rnDeriv_wt_pert hwm hw0 hhm hh, hh, hw0, hwW] with x hx hhx hwx hWx
    have h1h : 1 / 2 ≤ 1 + h x := by have := (abs_le.1 hhx).1; linarith
    have hq0 : 0 ≤ (ν.rnDeriv μ x).toReal := ENNReal.toReal_nonneg
    nlinarith
  have hφ : ∀ᵐ x ∂lam, |potG T μ ν gd x| ≤ 2 * W * ε := by
    filter_upwards [hq, hband] with x hqx hbx
    rw [potG, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    have := hgd _ hbx
    calc |gd (ratioG T μ x)| * (ν.rnDeriv μ x).toReal ≤ ε * (2 * W) :=
          mul_le_mul this hqx ENNReal.toReal_nonneg hε
      _ = 2 * W * ε := by ring
  have hTφ : ∀ᵐ x ∂lam, |Core.General.funAct T (potG T μ ν gd) x| ≤ 2 * W * ε := by
    filter_upwards [hinv.ae_ae hφ] with x hx
    have := norm_integral_le_of_norm_le_const (μ := T x) (f := potG T μ ν gd)
      (C := 2 * W * ε) (hx.mono fun y hy => by rwa [Real.norm_eq_abs])
    simpa [Core.General.funAct, Real.norm_eq_abs] using this
  have hr : ∀ᵐ x ∂lam, 0 < ratioG T μ x ∧ ratioG T μ x < F.d := by
    filter_upwards [hband] with x hx
    refine ⟨F.pos_of_mem_bands hx, ?_⟩
    rcases hx with h1 | h1
    · exact h1.2.trans (F.b_lt_one.trans (F.one_lt_c.trans F.c_lt_d))
    · exact h1.2
  filter_upwards [hφ, hTφ, hr] with x hφx hTx hrx
  simp only [gradDensityG]
  have hrφ : |ratioG T μ x * potG T μ ν gd x| ≤ F.d * (2 * W * ε) := by
    rw [abs_mul, abs_of_pos hrx.1]
    exact mul_le_mul hrx.2.le hφx (abs_nonneg _) (hrx.1.trans hrx.2).le
  calc |Core.General.funAct T (potG T μ ν gd) x - ratioG T μ x * potG T μ ν gd x|
      ≤ |Core.General.funAct T (potG T μ ν gd) x| + |ratioG T μ x * potG T μ ν gd x| :=
        abs_sub _ _
    _ ≤ 2 * W * ε + F.d * (2 * W * ε) := add_le_add hTx hrφ
    _ = 2 * (1 + F.d) * W * ε := by ring

/-- **`prop:nonlinear_freezing`*(3)*, the gradient bound**: `‖∇^λ𝓛_{g̃,ν}‖_{𝓜²(λ)} ≤ C'ε` with
`C' = 2(1 + d)W` on the frozen set near `λ`, for any `W ≥ w` (the paper's `W = ‖w‖_∞`:
`nonlinear_freezing_three_general`). -/
theorem freezing_three_eLpNorm_le (F : FreezingBands) (hinv : IsInvariant T lam) {ε W : ℝ}
    (hε : 0 ≤ ε) (hgd : ∀ z ∈ F.bands, |gd z| ≤ ε) {w h : S → ℝ} (hwm : Measurable w)
    (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwW : ∀ᵐ x ∂lam, w x ≤ W) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ 1 / 2)
    (hband : ∀ᵐ x ∂lam, ratioG T (pertG lam h) x ∈ F.bands) :
    eLpNorm (gradDensityG T (pertG lam h) (wtG lam w) gd) 2 lam
      ≤ ENNReal.ofReal (2 * (1 + F.d) * W * ε) := by
  have hb : ∀ᵐ x ∂lam, ‖gradDensityG T (pertG lam h) (wtG lam w) gd x‖
      ≤ 2 * (1 + F.d) * W * ε := by
    filter_upwards [freezing_three_ae_bound F hinv hε hgd hwm hw0 hwW hhm hh hband] with x hx
    rwa [Real.norm_eq_abs]
  have := eLpNorm_le_of_ae_bound (p := 2) (μ := lam) hb
  simpa [measure_univ] using this

omit [IsMarkovKernel T] in
theorem nonneg_of_ae_le {w : S → ℝ} {W : ℝ} (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x)
    (hwW : ∀ᵐ x ∂lam, w x ≤ W) : 0 ≤ W := by
  obtain ⟨x, hx1, hx2⟩ := (hw0.and hwW).exists
  linarith

/-- **`prop:nonlinear_freezing`*(3)*, the trajectory**: while a gradient flow of `𝓛_{g̃,ν}` stays in
the frozen set near `λ` on `[0, τ]`, it moves at most `C'ετ` in `𝓜²(λ)`: moving a distance `η`
within the set takes a time `τ` with `η ≤ C'ετ`, i.e. at least `η/(C'ε)`. -/
theorem freezing_three_flow (F : FreezingBands) (hinv : IsInvariant T lam) {ε W : ℝ}
    (hε : 0 ≤ ε) (hgd : ∀ z ∈ F.bands, |gd z| ≤ ε) {w : S → ℝ} (hwm : Measurable w)
    (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwW : ∀ᵐ x ∂lam, w x ≤ W) {μ : ℝ → Measure S}
    {u : ℝ → Lp ℝ 2 lam} (hflow : IsGradientFlowG T lam (wtG lam w) gd μ u) {τ : ℝ}
    (hτ : 0 ≤ τ)
    (hin : ∀ t ∈ Set.Icc 0 τ, ∃ h : S → ℝ, Measurable h ∧ (∀ᵐ x ∂lam, |h x| ≤ 1 / 2) ∧
      μ t = pertG lam h ∧ ∀ᵐ x ∂lam, ratioG T (μ t) x ∈ F.bands) :
    ‖u τ - u 0‖ ≤ 2 * (1 + F.d) * W * ε * τ := by
  classical
  have hW := nonneg_of_ae_le hw0 hwW
  have hC : 0 ≤ 2 * (1 + F.d) * W * ε := by
    have : 0 < F.d := (zero_lt_one.trans F.one_lt_c).trans F.c_lt_d
    positivity
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
    rw [Lp.norm_def, eLpNorm_congr_ae hD, hμt]
    rw [hμt] at hband
    exact ENNReal.toReal_le_of_le_ofReal hC
      (freezing_three_eLpNorm_le F hinv hε hgd hwm hw0 hwW hhm hh hband)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hder hbd τ ⟨hτ, le_rfl⟩
  simpa using this

omit [IsMarkovKernel T] [IsProbabilityMeasure lam] in
/-- `w ≤ ‖w‖_{L^∞(λ)}` `λ`-a.e. for `w ∈ L^∞(λ)`. -/
theorem ae_le_linfty {w : S → ℝ} (hwinf : eLpNorm w ⊤ lam ≠ ⊤) :
    ∀ᵐ x ∂lam, w x ≤ (eLpNorm w ⊤ lam).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (f := w) (μ := lam)] with x hx
  rw [eLpNorm_exponent_top]
  calc w x ≤ ‖w x‖ := Real.le_norm_self _
    _ = (‖w x‖ₑ).toReal := (toReal_enorm _).symm
    _ ≤ (eLpNormEssSup w lam).toReal :=
        ENNReal.toReal_mono (by rwa [← eLpNorm_exponent_top]) hx

/-- **`prop:nonlinear_freezing`*(3)* as printed**: `C' = 2(1 + d)‖w‖_{L^∞(λ)}`; on the set of flows
`μ = (1 + h)λ`, `‖h‖_{L^∞(λ)} ≤ 1/2`, whose ratio is band-valued `λ`-a.e., the gradient has norm at
most `C'ε` in `𝓜²(λ)`, and a gradient flow moves at most `C'ετ` in `𝓜²(λ)` during a time `τ` spent
in that set — so moving a distance `η` takes a time `τ ≥ η/(C'ε)`, i.e. `η ≤ C'ετ`. -/
theorem nonlinear_freezing_three_general (F : FreezingBands) (hinv : IsInvariant T lam) {ε : ℝ}
    (hε : 0 < ε) (hgd : ∀ z ∈ F.bands, |gd z| ≤ ε) {w : S → ℝ} (hwm : Measurable w)
    (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwinf : eLpNorm w ⊤ lam ≠ ⊤) :
    (∀ h : S → ℝ, Measurable h → (∀ᵐ x ∂lam, |h x| ≤ 1 / 2) →
        (∀ᵐ x ∂lam, ratioG T (pertG lam h) x ∈ F.bands) →
        eLpNorm (gradDensityG T (pertG lam h) (wtG lam w) gd) 2 lam
          ≤ ENNReal.ofReal (2 * (1 + F.d) * (eLpNorm w ⊤ lam).toReal * ε))
      ∧ ∀ (μ : ℝ → Measure S) (u : ℝ → Lp ℝ 2 lam),
        IsGradientFlowG T lam (wtG lam w) gd μ u → ∀ τ : ℝ, 0 ≤ τ →
        (∀ t ∈ Set.Icc 0 τ, ∃ h : S → ℝ, Measurable h ∧ (∀ᵐ x ∂lam, |h x| ≤ 1 / 2) ∧
          μ t = pertG lam h ∧ ∀ᵐ x ∂lam, ratioG T (μ t) x ∈ F.bands) →
        ∀ η : ℝ, η ≤ ‖u τ - u 0‖ →
          η ≤ 2 * (1 + F.d) * (eLpNorm w ⊤ lam).toReal * ε * τ := by
  have hwW := ae_le_linfty hwinf
  refine ⟨fun h hhm hh hband =>
    freezing_three_eLpNorm_le F hinv hε.le hgd hwm hw0 hwW hhm hh hband,
    fun μ u hflow τ hτ hin η hη => hη.trans
      (freezing_three_flow F hinv hε.le hgd hwm hw0 hwW hflow hτ hin)⟩

end FreezingThree

section Statements

variable {T R : Kernel S S} [IsMarkovKernel T] {lam μ ν : Measure S} [IsFiniteMeasure lam]
  [IsFiniteMeasure μ] {gd g : ℝ → ℝ}

/-- **`prop:no_distant_equilibrium`*(1)* on a general space**: under the hypotheses of
`theo:first_variation_full` at `μ` (`h`), for strictly unimodal `g` and `dν/dμ > 0` `μ`-a.e., the
total mass of `∇^λ𝓛_{g,ν}(μ)` — whose `λ`-density is `D = Tφ − rφ` — equals
`∫ g'(r)(1 − r)(dν/dμ) dλ`, is `≤ 0`, and vanishes iff `μ` is balanced; every critical point
(`D = 0` `λ`-a.e.) is balanced. -/
theorem no_distant_equilibrium_one_general (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hg : StrictlyUnimodal gd)
    (hν : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal) :
    ∫ x, gradDensityG T μ ν gd x ∂lam
        = ∫ x, gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal ∂lam
      ∧ ∫ x, gradDensityG T μ ν gd x ∂lam ≤ 0
      ∧ (∫ x, gradDensityG T μ ν gd x ∂lam = 0 ↔ BalancedG T μ)
      ∧ (gradDensityG T μ ν gd =ᵐ[lam] 0 → BalancedG T μ) := by
  have hφ := h.integrable_pot hinv
  have hrφ := h.integrable_rpot hinv
  have hid := integral_gradDensityG hinv hφ hrφ
  refine ⟨hid, hid ▸ mass_nonpos hinv h.ac h.ac' hg, ?_,
    balanced_of_criticalG hinv h.ac h.ac' hg hφ hrφ hν⟩
  rw [hid]
  exact mass_eq_zero_iff hinv h.ac h.ac' hg hφ hrφ hν

/-- **`prop:no_distant_equilibrium`*(1)*, criticality in the derivative sense**: if the first
variation holds at `μ` with density `D` along an admissible class containing a non-zero constant
direction `δ = cλ`, then a critical point of `𝓛_{g,ν}` along that class is balanced. -/
theorem balanced_of_isCriticalAlong (hinv : IsInvariant T lam)
    (h : FirstVariationSetting T lam μ ν gd) (hg : StrictlyUnimodal gd)
    (hν : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal) {Adm : Set (S → ℝ)}
    (hFV : FirstVariationFull T lam ν g μ Adm (gradDensityG T μ ν gd))
    (hc : IsCriticalAlong T lam ν g μ Adm) {c : ℝ} (hc0 : c ≠ 0)
    (hcA : (fun _ => c) ∈ Adm) : BalancedG T μ := by
  have h0 := integral_mul_eq_zero_of_critical hFV hc hcA
  rw [integral_mul_const, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact (no_distant_equilibrium_one_general hinv h hg hν).2.2.1.1 h0
  · exact absurd h0 hc0

/-- **`prop:no_distant_equilibrium`*(2)* on a general space, static half**: the loss is
scale-invariant; the gradient is orthogonal to the radial direction, `⟨D, u⟩_{L²(λ)} = 0`
(through a `λ`-reversal `R` of `T`, `lem:adjoint`); and, `T` ergodic and `λ ≠ 0`, the mass
`∫u dλ` is at most `√λ(𝒮)‖u‖_{L²(λ)}` (`‖u‖_{L²(λ)}` when `λ` is a probability, the paper's
convention) with equality iff `μ` is balanced. -/
theorem no_distant_equilibrium_two_general [IsMarkovKernel R] (hR : IsReversalPair lam T R)
    (h : FirstVariationSetting T lam μ ν gd) :
    (∀ c : ℝ≥0∞, c ≠ 0 → c ≠ ∞ → lossG T ν g (c • μ) = lossG T ν g μ)
      ∧ ∫ x, gradDensityG T μ ν gd x * (μ.rnDeriv lam x).toReal ∂lam = 0
      ∧ (ErgodicG T lam → lam ≠ 0 →
          ∫ x, (μ.rnDeriv lam x).toReal ∂lam
              ≤ Real.sqrt (lam.real Set.univ * ∫ x, (μ.rnDeriv lam x).toReal ^ 2 ∂lam)
            ∧ (∫ x, (μ.rnDeriv lam x).toReal ∂lam
                = Real.sqrt (lam.real Set.univ * ∫ x, (μ.rnDeriv lam x).toReal ^ 2 ∂lam)
                  ↔ BalancedG T μ)) := by
  have hinv : IsInvariant T lam := hR.symm.isInvariant
  refine ⟨fun c hc0 hct => lossG_smul h.nu_ac hc0 hct,
    integral_gradDensityG_mul_dens hR h.ac h.ac' (h.memLp_pot hinv 2) (h.memLp_rpot hinv 2)
      h.memL2, fun hT hlam => mass_le_nrm_and_eq_iff_balanced hT hlam h.ac h.memL2⟩

omit [IsFiniteMeasure μ] in
/-- **`prop:no_distant_equilibrium`*(2)* on a general space, the flow**: along a gradient flow in
`𝓜²(λ)` at fixed `ν`, satisfying the first-variation hypotheses at every time, `‖u_t‖_{L²(λ)}` is
constant, the mass `∫u_t dλ` is non-decreasing on `[0, ∞)`, and its derivative is positive at every
time where `μ_t` is off balance. -/
theorem no_distant_equilibrium_two_flow [IsMarkovKernel R] (hR : IsReversalPair lam T R)
    (hg : StrictlyUnimodal gd) {μ : ℝ → Measure S} {u : ℝ → Lp ℝ 2 lam}
    (hflow : IsGradientFlowG T lam ν gd μ u) (hfin : ∀ t, IsFiniteMeasure (μ t))
    (hset : ∀ t, 0 ≤ t → FirstVariationSetting T lam (μ t) ν gd) :
    (∀ t, 0 ≤ t → ‖u t‖ = ‖u 0‖)
      ∧ MonotoneOn (fun s => ∫ x, u s x ∂lam) (Set.Ici 0)
      ∧ ∀ t, 0 ≤ t → (∀ᵐ x ∂(μ t), 0 < (ν.rnDeriv (μ t) x).toReal) → ¬ BalancedG T (μ t) →
          HasDerivAt (fun s => ∫ x, u s x ∂lam) (-∫ x, gradDensityG T (μ t) ν gd x ∂lam) t
            ∧ 0 < -∫ x, gradDensityG T (μ t) ν gd x ∂lam := by
  have hinv : IsInvariant T lam := hR.symm.isInvariant
  have hrad : ∀ t, 0 ≤ t →
      ∫ x, gradDensityG T (μ t) ν gd x * ((μ t).rnDeriv lam x).toReal ∂lam = 0 := by
    intro t ht
    haveI := hfin t
    have h := hset t ht
    exact integral_gradDensityG_mul_dens hR h.ac h.ac' (h.memLp_pot hinv 2)
      (h.memLp_rpot hinv 2) h.memL2
  have hmass : ∀ t, 0 ≤ t → ∫ x, gradDensityG T (μ t) ν gd x ∂lam ≤ 0 := by
    intro t ht
    haveI := hfin t
    have h := hset t ht
    rw [integral_gradDensityG hinv (h.integrable_pot hinv) (h.integrable_rpot hinv)]
    exact mass_nonpos hinv h.ac h.ac' hg
  refine ⟨fun t ht => norm_const_of_flow hflow hrad ht, mass_monotoneOn_of_flow hflow hmass,
    fun t ht hν hnb => ⟨(mass_hasDerivAt_of_flow hflow ht).choose_spec.2, ?_⟩⟩
  haveI := hfin t
  have h := hset t ht
  have hne : ∫ x, gradDensityG T (μ t) ν gd x ∂lam ≠ 0 := fun h0 =>
    hnb ((no_distant_equilibrium_one_general hinv h hg hν).2.2.1.1 h0)
  exact neg_pos.2 (lt_of_le_of_ne (hmass t ht) hne)

omit [IsMarkovKernel T] [IsFiniteMeasure lam] [IsFiniteMeasure μ] in
/-- **`prop:nonlinear_freezing`*(1)* on a general space**: for every `g̃` with `g̃' ≡ 0` on the bands
and every ergodic (in fact every invariant) `(𝒮̂, λ, T)`, every `μ` whose ratio is band-valued
`λ`-a.e. has vanishing gradient density `D` for **every** training measure `ν`; and wherever the
first variation holds with density `D` (`theo:first_variation_full`, a hypothesis here), `μ` is a
critical point of `𝓛_{g̃,ν}` along every admissible direction. `g` and `gd` are linked by no
hypothesis here: the link `g' = gd` is supplied only through `FirstVariationFull`, so the second
conjunct is meaningful exactly when that hypothesis is instantiated with `gd = deriv g`. -/
theorem nonlinear_freezing_one_general (F : FreezingBands) (hinv : IsInvariant T lam)
    (hgd0 : ∀ z ∈ F.bands, gd z = 0) (hband : ∀ᵐ x ∂lam, ratioG T μ x ∈ F.bands) :
    (∀ ν : Measure S, gradDensityG T μ ν gd =ᵐ[lam] 0)
      ∧ ∀ (ν : Measure S) (Adm : Set (S → ℝ)),
          FirstVariationFull T lam ν g μ Adm (gradDensityG T μ ν gd) →
          IsCriticalAlong T lam ν g μ Adm :=
  ⟨fun ν => gradDensityG_eq_zero_of_band hinv hband hgd0 ν, fun ν _ hFV =>
    isCriticalAlong_of_ae_zero hFV (gradDensityG_eq_zero_of_band hinv hband hgd0 ν)⟩

/-- **`theo:global_dichotomy_full`, the general halves**: item *(1)*'s first sentence (the mass
identity, its sign, equality only at balance, every critical point balanced) and item *(2)*'s
first clause (band-valued flows have vanishing gradient density for every `ν`). -/
theorem global_dichotomy_full_general (hinv : IsInvariant T lam) :
    (∀ (ν : Measure S) (gd : ℝ → ℝ), IsFiniteMeasure ν → FirstVariationSetting T lam μ ν gd →
        StrictlyUnimodal gd → (∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal) →
        ∫ x, gradDensityG T μ ν gd x ∂lam
            = ∫ x, gd (ratioG T μ x) * (1 - ratioG T μ x) * (ν.rnDeriv μ x).toReal ∂lam
          ∧ ∫ x, gradDensityG T μ ν gd x ∂lam ≤ 0
          ∧ (∫ x, gradDensityG T μ ν gd x ∂lam = 0 ↔ BalancedG T μ)
          ∧ (gradDensityG T μ ν gd =ᵐ[lam] 0 → BalancedG T μ))
      ∧ (∀ (F : FreezingBands) (gd : ℝ → ℝ), (∀ z ∈ F.bands, gd z = 0) →
        (∀ᵐ x ∂lam, ratioG T μ x ∈ F.bands) →
        ∀ ν : Measure S, gradDensityG T μ ν gd =ᵐ[lam] 0) :=
  ⟨fun _ _ _ h hg hν => no_distant_equilibrium_one_general hinv h hg hν,
    fun _ _ hgd0 hband ν => gradDensityG_eq_zero_of_band hinv hband hgd0 ν⟩

/-- **`theo:global_dichotomy`** (body) **and `rem:freezing`*(iv)*, the critical-point sentence on a
general space**: `global_dichotomy_full_general`'s item *(1)*, read for a critical point. -/
theorem freezing_remark_four_general (hinv : IsInvariant T lam) (h : FirstVariationSetting T lam μ ν gd) (hg : StrictlyUnimodal gd)
    (hν : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal) (hD : gradDensityG T μ ν gd =ᵐ[lam] 0) :
    BalancedG T μ :=
  (no_distant_equilibrium_one_general hinv h hg hν).2.2.2 hD

end Statements

section Witness

/-! ### The hypotheses are inhabited, off balance (kb 0025, 0027)

On every probability space `(S, π)`, the resampling kernel `T = const π` is ergodic
(`ergodicG_const`), and every flow `μ = (1 + h)π` with `|h| ≤ 1/2` satisfies the first-variation
hypotheses, with `r = μ(S)/(1 + h)` explicitly. On `Bool` with the uniform `π` this is the two-state
chain of `prop:nonlinear_freezing`*(2)*, and `h = (3/10, −3/10)` is band-valued, off balance, and in
the set of item *(3)*. -/

variable (π : Measure S) [IsProbabilityMeasure π]

variable {π}

theorem isFiniteMeasure_pertG {h : S → ℝ} (hhm : Measurable h) (hh : ∀ x, |h x| ≤ 1 / 2) :
    IsFiniteMeasure (pertG π h) := by
  refine isFiniteMeasure_withDensity_ofReal (Integrable.of_bound (by fun_prop) (3 / 2)
    (Filter.Eventually.of_forall fun x => ?_)).2
  rw [Real.norm_eq_abs]
  have := abs_le.1 (hh x)
  rw [abs_le]; constructor <;> linarith

theorem rnDeriv_pertG {h : S → ℝ} (hhm : Measurable h) :
    (pertG π h).rnDeriv π =ᵐ[π] fun x => ENNReal.ofReal (1 + h x) :=
  Measure.rnDeriv_withDensity π (by fun_prop)

theorem ratioG_const_pertG {h : S → ℝ} (hhm : Measurable h) (hh : ∀ x, |h x| ≤ 1 / 2) :
    ratioG (Kernel.const S π) (pertG π h)
      =ᵐ[π] fun x => ((pertG π h) Set.univ).toReal / (1 + h x) := by
  haveI := isFiniteMeasure_pertG (π := π) hhm hh
  set c := (pertG π h) Set.univ
  have hct : c ≠ ∞ := measure_ne_top _ _
  haveI := π.smul_finite hct
  have hpos : ∀ x, 0 < 1 + h x := fun x => by have := (abs_le.1 (hh x)).1; linarith
  have h1 := Measure.rnDeriv_withDensity_right (c • π) π
    (f := fun x => ENNReal.ofReal (1 + h x)) (by fun_prop)
    (Filter.Eventually.of_forall fun x => by simp [hpos x])
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_ne_top)
  have h2 : (c • π).rnDeriv π =ᵐ[π] c • π.rnDeriv π :=
    Measure.rnDeriv_smul_left_of_ne_top' _ _ hct
  filter_upwards [h1, h2, Measure.rnDeriv_self π] with x hx1 hx2 hx3
  simp only [ratioG, Measure.const_comp]
  change ((c • π).rnDeriv (π.withDensity fun x => ENNReal.ofReal (1 + h x)) x).toReal = _
  rw [hx1, hx2, Pi.smul_apply, hx3, smul_eq_mul, mul_one, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (hpos x).le, div_eq_inv_mul]

theorem measure_univ_pertG_toReal {h : S → ℝ} (hhm : Measurable h) (hh : ∀ x, |h x| ≤ 1 / 2) :
    ((pertG π h) Set.univ).toReal = 1 + ∫ x, h x ∂π := by
  have hI : Integrable h π := Integrable.of_bound hhm.aestronglyMeasurable (1 / 2)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hh x)
  have hpos : ∀ x, 0 ≤ 1 + h x := fun x => by have := (abs_le.1 (hh x)).1; linarith
  have hI1 : Integrable (fun x => 1 + h x) π := (integrable_const 1).add hI
  rw [pertG, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI1 (Filter.Eventually.of_forall hpos),
    ENNReal.toReal_ofReal (integral_nonneg hpos), integral_add (integrable_const 1) hI]
  simp

/-- **The first-variation hypotheses are inhabited on every probability space**: for
`T = const π`, `μ = (1 + h)π`, `|h| ≤ 1/2`, `ν = π` and any `g'` continuous on `ℝ₊*`. -/
theorem firstVariationSetting_const_pertG {gd : ℝ → ℝ} (hgd : ContinuousOn gd (Set.Ioi 0))
    {h : S → ℝ} (hhm : Measurable h) (hh : ∀ x, |h x| ≤ 1 / 2) :
    FirstVariationSetting (Kernel.const S π) π (pertG π h) π gd := by
  have hpos : ∀ x, 1 / 2 ≤ 1 + h x := fun x => by have := (abs_le.1 (hh x)).1; linarith
  have hle : ∀ x, 1 + h x ≤ 3 / 2 := fun x => by have := (abs_le.1 (hh x)).2; linarith
  have hne : ∀ᵐ x ∂π, ENNReal.ofReal (1 + h x) ≠ 0 :=
    Filter.Eventually.of_forall fun x => by simp; linarith [hpos x]
  have hac : pertG π h ≪ π := withDensity_absolutelyContinuous _ _
  have hac' : π ≪ pertG π h := withDensity_absolutelyContinuous' (by fun_prop) hne
  have hm := measure_univ_pertG_toReal (π := π) hhm hh
  have hint : |∫ x, h x ∂π| ≤ 1 / 2 := by
    have := norm_integral_le_of_norm_le_const (μ := π) (f := h) (C := 1 / 2)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hh x)
    simpa [Real.norm_eq_abs] using this
  refine ⟨hac, hac', ?_, hac', ⟨1 / 3, 3, by norm_num, ?_⟩, ⟨2, ?_⟩, hgd⟩
  · refine MemLp.of_bound (Measure.measurable_rnDeriv _ _).ennreal_toReal.aestronglyMeasurable
      (3 / 2) ?_
    filter_upwards [rnDeriv_pertG hhm] with x hx
    rw [hx, Real.norm_eq_abs, ENNReal.toReal_ofReal (by linarith [hpos x]),
      abs_of_nonneg (by linarith [hpos x])]
    exact hle x
  · refine hac.ae_le ?_
    filter_upwards [ratioG_const_pertG hhm hh] with x hx
    rw [hx, hm]
    have h1 := (abs_le.1 hint)
    constructor
    · rw [le_div_iff₀ (by linarith [hpos x])]; nlinarith [hle x]
    · rw [div_le_iff₀ (by linarith [hpos x])]; nlinarith [hpos x]
  · refine hac.ae_le ?_
    have h1 := Measure.rnDeriv_withDensity_right π π
      (f := fun x => ENNReal.ofReal (1 + h x)) (by fun_prop) hne
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_ne_top)
    filter_upwards [h1, Measure.rnDeriv_self π] with x hx hself
    change (π.rnDeriv (π.withDensity fun x => ENNReal.ofReal (1 + h x)) x).toReal ≤ 2
    rw [hx, hself, mul_one, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith [hpos x])]
    rw [inv_le_comm₀ (by linarith [hpos x]) (by norm_num)]
    linarith [hpos x]

end Witness

section BoolWitness

/-- The uniform probability on `Bool`: the two-state chain of `prop:nonlinear_freezing`*(2)*, with
`T = const boolUnif` being `T(i → j) = 1/2`. -/
noncomputable def boolUnif : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac true + (2 : ℝ≥0∞)⁻¹ • Measure.dirac false

instance : IsProbabilityMeasure boolUnif := by
  constructor
  simp only [boolUnif, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

theorem boolUnif_singleton (b : Bool) : boolUnif {b} = 2⁻¹ := by
  cases b <;> simp [boolUnif, Measure.add_apply, Measure.smul_apply]

/-- `h = (3/10, −3/10)`: `μ = (1 + h)π` has ratio `(10/13, 10/7) ∈ U⁻ × U⁺` for item *(2)*'s bands. -/
noncomputable def boolH : Bool → ℝ := fun b => if b then 3 / 10 else -(3 / 10)

theorem boolH_abs (b : Bool) : |boolH b| ≤ 1 / 2 := by
  cases b <;> norm_num [boolH, abs_of_nonneg, abs_of_nonpos]

theorem integral_boolH : ∫ b, boolH b ∂boolUnif = 0 := by
  have hI : ∀ μ : Measure Bool, IsFiniteMeasure μ → Integrable boolH μ := fun μ _ =>
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (1 / 2)
      (Filter.Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact boolH_abs b)
  have hf : ∀ b : Bool, IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • Measure.dirac b) := fun b =>
    (Measure.dirac b).smul_finite (by norm_num)
  rw [boolUnif, integral_add_measure (hI _ (hf true)) (hI _ (hf false)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  norm_num [boolH]

theorem ratioG_boolH :
    ∀ b, ratioG (Kernel.const Bool boolUnif) (pertG boolUnif boolH) b = 1 / (1 + boolH b) := by
  have h := ratioG_const_pertG (π := boolUnif) (measurable_of_countable boolH) boolH_abs
  rw [measure_univ_pertG_toReal (measurable_of_countable boolH) boolH_abs, integral_boolH,
    add_zero] at h
  have h' := ae_iff_of_countable.1 h
  exact fun b => h' b (by rw [boolUnif_singleton]; norm_num)

/-- **A non-trivial witness for the static hypotheses of this file (ErgodicG,
FirstVariationSetting, band-valued ratio, off balance); FirstVariationFull and a non-constant
IsGradientFlowG are not witnessed (SCOPE)**: on the two-state chain
(`Bool`, uniform `π`, `T = const π`), `T` is ergodic; the flow `μ = (1 + h)π`, `h = (3/10, −3/10)`,
satisfies the first-variation hypotheses for every `g'` continuous on `ℝ₊*`; its ratio
`(10/13, 10/7)` lies in the bands `(5/8, 7/8) ∪ (11/8, 13/8)` of item *(2)*; and it is **not**
balanced. -/
theorem bool_witness {gd : ℝ → ℝ} (hgd : ContinuousOn gd (Set.Ioi 0)) :
    ErgodicG (Kernel.const Bool boolUnif) boolUnif
      ∧ FirstVariationSetting (Kernel.const Bool boolUnif) boolUnif (pertG boolUnif boolH)
          boolUnif gd
      ∧ (∀ b, |boolH b| ≤ 1 / 2)
      ∧ (∀ b, ratioG (Kernel.const Bool boolUnif) (pertG boolUnif boolH) b
          ∈ twoStateBands.bands)
      ∧ ¬ BalancedG (Kernel.const Bool boolUnif) (pertG boolUnif boolH) := by
  have hset := firstVariationSetting_const_pertG (π := boolUnif) hgd
    (measurable_of_countable boolH) boolH_abs
  refine ⟨ergodicG_const boolUnif, hset, boolH_abs, fun b => ?_, fun hb => ?_⟩
  · rw [ratioG_boolH]
    cases b
    · right; norm_num [boolH, twoStateBands, FreezingBands.upper]
    · left; norm_num [boolH, twoStateBands, FreezingBands.lower]
  · haveI := isFiniteMeasure_pertG (π := boolUnif) (measurable_of_countable boolH) boolH_abs
    have h1 := (ratioG_eq_one_iff (Core.General.isInvariant_const boolUnif) hset.ac
      hset.ac').2 hb
    have h2 := ae_iff_of_countable.1 (hset.ac'.ae_le h1)
    have := h2 true (by rw [boolUnif_singleton]; norm_num)
    rw [ratioG_boolH] at this
    norm_num [boolH] at this

/-- `dν/dμ > 0` `μ`-a.e. whenever `μ ≪ ν`. -/
theorem toReal_rnDeriv_pos_of_ac {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ ≪ ν) : ∀ᵐ x ∂μ, 0 < (ν.rnDeriv μ x).toReal := by
  filter_upwards [Measure.rnDeriv_pos' h, Measure.rnDeriv_lt_top ν μ] with x h0 htop
  exact ENNReal.toReal_pos h0.ne' htop.ne

/-- **`prop:no_distant_equilibrium`*(1)* is not vacuous**: on the Bool witness, for the strictly
unimodal `g' = 2(x − 1)` (`g = (x − 1)²`) and `ν = π`, the gradient mass is strictly negative. -/
theorem bool_mass_neg :
    ∫ x, gradDensityG (Kernel.const Bool boolUnif) (pertG boolUnif boolH) boolUnif
      (fun z => 2 * (z - 1)) x ∂boolUnif < 0 := by
  haveI := isFiniteMeasure_pertG (π := boolUnif) (measurable_of_countable boolH) boolH_abs
  obtain ⟨-, hset, -, -, hnb⟩ := bool_witness (gd := fun z => 2 * (z - 1))
    (by fun_prop)
  have h := no_distant_equilibrium_one_general (Core.General.isInvariant_const boolUnif) hset
    strictlyUnimodal_sqDeriv (toReal_rnDeriv_pos_of_ac hset.ac)
  exact lt_of_le_of_ne h.2.1 fun h0 => hnb (h.2.2.1.1 h0)

/-- **The general gradient-flow predicate is inhabited off balance**: on the Bool witness the
constant curve at the frozen, unbalanced flow `(1 + h)π` is a gradient flow of `𝓛_{g,ν}` for the
constructed generator `g` of item *(2)*'s bands, for every `ν`. -/
theorem bool_frozen_flow (ν : Measure Bool) :
    ∃ u : Lp ℝ 2 boolUnif,
      IsGradientFlowG (Kernel.const Bool boolUnif) boolUnif ν (deriv twoStateBands.g)
        (fun _ => pertG boolUnif boolH) (fun _ => u)
      ∧ ¬ BalancedG (Kernel.const Bool boolUnif) (pertG boolUnif boolH) := by
  obtain ⟨-, hset, -, hband, hnb⟩ := bool_witness (gd := deriv twoStateBands.g)
    (twoStateBands.contDiff_g.continuous_deriv (by norm_num)).continuousOn
  refine ⟨hset.memL2.toLp _, fun t _ => ⟨hset.memL2.coeFn_toLp, 0, ?_, ?_⟩, hnb⟩
  · refine (Lp.coeFn_zero _ _ _).trans ?_
    exact (gradDensityG_eq_zero_of_band (Core.General.isInvariant_const boolUnif)
      (Filter.Eventually.of_forall hband)
      (fun _ hz => twoStateBands.deriv_g_eq_zero_of_mem_bands' hz) ν).symm
  · rw [neg_zero]
    exact hasDerivAt_const t _

end BoolWitness

section Closing

/-- **`prop:nonlinear_freezing`, the last assertion's instance** (the proof's "*The last
assertion*"): on the two-state chain of item *(2)*, for every `ν ≥ 0`, `ν ≠ 0`, the constant curve
at `μ* = (1, 1/2)` (density `u = (2, 1)`) **is** a gradient flow of `𝓛_{g,ν}` for the constructed
generator `g`, and its loss is the positive constant `𝓛_{g,ν}(μ*)` at every time. -/
theorem freezing_last_instance (nu : Fin 2 → ℝ) (hnu0 : ∀ x, 0 ≤ nu x) (hnu : ∃ x, 0 < nu x) :
    IsGradientFlow twoStateK twoStateLam nu (deriv twoStateBands.g) (fun _ => twoStateU)
      ∧ 0 < loss twoStateK twoStateLam nu twoStateU twoStateBands.g
      ∧ ∀ t : ℝ, loss twoStateK twoStateLam nu ((fun _ => twoStateU) t) twoStateBands.g
          = loss twoStateK twoStateLam nu twoStateU twoStateBands.g := by
  refine ⟨fun t _ x => ?_, loss_pos_of_nonneg twoStateBands
    (fun _ hz => twoStateBands.g_pos fun h1 => twoStateBands.one_notMem_bands (h1 ▸ hz))
    hnu0 hnu twoState_mem_frozen.2, fun _ => rfl⟩
  have hz : lossGrad twoStateK twoStateLam nu (deriv twoStateBands.g) twoStateU x = 0 :=
    freezing_critical twoState_mem_frozen.2
      (fun _ hz => twoStateBands.deriv_g_eq_zero_of_mem_bands' hz) x
  rw [hz, neg_zero]
  exact hasDerivAt_const t _

/-- **`prop:nonlinear_freezing`, the last assertion**: *no bound on the time the gradient flow
takes to bring the loss below a given positive level, finite and depending only on that level, on
`g''(1)`, on the mixing coefficients and on `w`, holds for every admissible generator.*

Stated as the paper's negation, and in a strong form: for every candidate bound `Tb(level, g''(1),
(β̂ₙ), ν)`, the claim fails already on the two-state chain of item *(2)*, already within the
`C^∞` admissible generators with `g''(1) = 2`, and already for flows started at a positive
density. `ν` stands for the training measure `ν = wλ` (so `w = 2ν` here, `λ ≡ 1/2`). -/
theorem freezing_no_time_bound
    (Tb : ℝ → ℝ → (ℕ → ℝ) → (Fin 2 → ℝ) → ℝ) :
    ¬ (∀ g : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → g 1 = 0 → (∀ x ≠ (1 : ℝ), 0 < g x) →
        deriv (deriv g) 1 = 2 → (∃ C : ℝ, ∀ x, |g x| ≤ C * (1 + |x| ^ 2)) →
        ∀ nu : Fin 2 → ℝ, (∀ x, 0 ≤ nu x) → (∃ x, 0 < nu x) →
        ∀ u : ℝ → Fin 2 → ℝ, IsGradientFlow twoStateK twoStateLam nu (deriv g) u →
        (∀ x, 0 < u 0 x) → ∀ ℓ : ℝ, 0 < ℓ →
        ∃ t, 0 ≤ t ∧ t ≤ Tb ℓ (deriv (deriv g) 1)
            (Core.Mixing.beta (densOp twoStateLam twoStateK) (meanOp twoStateLam)) nu ∧
          loss twoStateK twoStateLam nu (u t) g < ℓ) := by
  intro H
  set F := twoStateBands
  obtain ⟨hC, h1, hpos, h2, hgrow, -⟩ := F.admissible
  set nu : Fin 2 → ℝ := fun _ => 1
  have hnu0 : ∀ x, 0 ≤ nu x := fun _ => zero_le_one
  have hnu : ∃ x, 0 < nu x := ⟨0, one_pos⟩
  obtain ⟨hflow, hL, hconst⟩ := freezing_last_instance nu hnu0 hnu
  obtain ⟨t, -, -, hlt⟩ := H F.g hC h1 hpos h2 ⟨F.bound, hgrow⟩ nu hnu0 hnu _ hflow
    twoStateU_pos _ (half_pos hL)
  rw [hconst t] at hlt
  linarith

end Closing

end GFNBounds.Balance.General
