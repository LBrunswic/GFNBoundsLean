import GFNBounds.Core.Flow

/-!
# The density action of a Markov kernel, and the two conditions `Core.Flow` assumes

**`theo:universality_L2_full`** — statement `proofs.tex:65–74`, proof `proofs.tex:76–115`
(Theorem 15 of the ICLR build) — together with the paragraph of the main text that says what
`P⋆` *is* (`universality.tex:22–29`):

> `π⋆` is *`ν_B`-ergodic* if `ν_B π⋆ = ν_B` and the only `μ ≪ ν_B` it fixes are the multiples of
> `ν_B`. Invariance makes the density action `P⋆ f := d((f ν_B) π⋆)/dν_B` well defined on
> `L¹(ν_B)`, and boundedness of `‖π⋆‖_{L^p(ν_B)}` says exactly that it restricts to a bounded
> operator of `L^p(ν_B)` — automatic for `p = 1`, a genuine hypothesis beyond.

`GFNBounds.Core.Flow` proves weak `L^p`-universality from two conditions on a *hypothesised*
bounded operator `P` on `L^p(ν)`,

    hone : P 𝟏 = 𝟏
    hint : ∀ f, ∫ (P f) dν = ∫ f dν

and its own SCOPE names the missing storey: `P` is not built from a kernel there. This file is
that storey. It **constructs** `P⋆` from a Markov kernel `π⋆` and an invariant finite measure
`ν`, proves the well-definedness the main text asserts, and discharges `hone` and `hint` — so
that the only hypothesis left between a Markov kernel and weak `L^p`-universality is the paper's
own boundedness requirement on the parameterization, plus summable mixing.

## What is proved

| | |
|---|---|
| `bind_absolutelyContinuous_bind` | `μ ≪ ν → μ π⋆ ≪ ν π⋆`, for any kernel |
| `bind_withDensity_absolutelyContinuous` | `(f ν) π⋆ ≪ ν`, **from invariance alone** — this is the main text's "invariance makes the density action well defined" |
| `bindDensity` | `T f := d((f ν) π⋆)/dν` for `f : 𝒮 → [0,∞]`, the density action on non-negative densities |
| `lintegral_bindDensity` | `∫ T f dν = ∫ f dν`: stochasticity, not invariance |
| `bindDensity_one` | `T 𝟏 = 𝟏` a.e.: invariance |
| `bindDensity_add`, `bindDensity_smul` | `T` is a.e. additive and positively homogeneous |
| `densityAction` | `P⋆ f := (T f⁺).toReal − (T f⁻).toReal`, the density action on signed densities |
| `integral_densityAction` | **`hint`**, in the paper's own terms: `∫ P⋆ f dν = ∫ f dν` for integrable `f` |
| `densityAction_one` | **`hone`**: `P⋆ 𝟏 = 𝟏` a.e. |
| `densityActionCLM` | `P⋆` as a `ContinuousLinearMap` on `L^p(ν)`, under `IsBoundedDensityAction` |
| `weaklyUniversal_of_kernel` | the payoff: weak `L^p`-universality from `π⋆` Markov, `ν π⋆ = ν`, `‖π⋆‖_{L^p} ≤ C`, summable mixing, `p ≠ ∞` |

## The one thing absolute continuity needs, and it is not new

`(f ν) π⋆ ≪ ν` is **proved**, not hypothesised. It factors through two steps, neither of which
asks anything of `f`:

* `f ν ≪ ν` always (`MeasureTheory.withDensity_absolutelyContinuous`);
* `μ ≪ ν ⇒ μ π⋆ ≪ ν π⋆` for every kernel — if `∫ π⋆(x, A) dν = 0` then `π⋆(·, A) = 0` `ν`-a.e.,
  hence `μ`-a.e., hence `∫ π⋆(x, A) dμ = 0`. Mathlib has no such lemma; it is proved here as
  `bind_absolutelyContinuous_bind`.

Composing them gives `(f ν) π⋆ ≪ ν π⋆`, and **invariance** `ν π⋆ = ν` closes it. So the paper's
sentence "invariance makes the density action well defined on `L¹(ν_B)`" is exactly right, and
nothing beyond `ν π⋆ = ν` is assumed. No extra domination hypothesis appears anywhere below.

## SCOPE (disclosed)

**Boundedness on `L^p` is assumed, because the paper assumes it.** `IsBoundedDensityAction κ ν p C`
says that `P⋆` maps `L^p(ν)` into `L^p(ν)` with `‖P⋆ f‖_p ≤ C ‖f‖_p`. This is
`theo:universality_L2_full`'s hypothesis "`π⋆` a Markov kernel on `𝒮` with finite
`L^p(ν_B) → L^p(ν_B)` operator norm", which the main text is explicit is *not* a theorem: "a
genuine requirement on the parameterization" (`universality.tex:6–9, 27–29`), "the definitions
above do not guarantee that `‖π⋆‖_{L^p(ν_B)}` is finite" (`proofs.tex:36`). It is not proved here
and is not provable: it is false for some Markov kernels.

**The `p = 1` case is not carried.** The main text says boundedness is "automatic for `p = 1`",
and `lintegral_bindDensity` is most of that proof — `‖P⋆ f‖_1 ≤ ‖f‖_1` follows from
`T f⁺ + T f⁻` dominating `T |f|`. It is not assembled: nothing downstream uses it, `p = 1`
being covered by `IsBoundedDensityAction κ ν 1 1` at the cost of stating it.

**Ergodicity is not used, and `Π` is the mean projection.** As in `Core.Flow`: `meanProj` is the
mean projection by construction, `eq_meanProj_of_invariant` there shows the summability
hypothesis already forces every `P⋆`-invariant density to be constant, and no separate
ergodicity hypothesis is carried. Nothing here changes that reading.

**Summable mixing is assumed, exactly as the paper assumes it**, and now against the operator
this file constructs rather than against a hypothesised one.

**Polish is not used.** Any `MeasurableSpace α` with a finite measure serves; the appendix's
Polish hypothesis is not consumed by the proof.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` a measured Polish space, `ν_B` finite | ⚠ weakened: any `MeasurableSpace α` with `[IsFiniteMeasure ν]` |
| `π⋆` a Markov kernel on `𝒮` | ✓ `κ : Kernel α α` with `[IsMarkovKernel κ]` — **the primitive**, no longer an operator |
| `ν_B π⋆ = ν_B` | ✓ `hinv : ν.bind ⇑κ = ν`, a hypothesis on the kernel |
| `P⋆ f = d((f ν_B) π⋆)/dν_B` well defined on `L¹(ν_B)` | ✓ **constructed** as `densityAction`, its absolute continuity **proved** from `hinv` |
| `π⋆` has finite `L^p(ν_B) → L^p(ν_B)` operator norm | ⚠ **assumed**, as `IsBoundedDensityAction κ ν p C`; the paper calls it a requirement on the parameterization, not a theorem |
| `Π` the mean projection (`proofs.tex:22`) | ✓ `meanProj` of `Core.Flow` |
| `Π P⋆ = P⋆ Π = Π` | ✓ **derived** in `Core.Flow` from `hone`/`hint`, which are **derived here** from the kernel |
| `π⋆` ergodic | ⚠ not assumed and not used; see SCOPE and `Core.Flow.eq_meanProj_of_invariant` |
| summable `L^p`-mixing coefficients | ⚠ **assumed**, as in the paper |
| `p < +∞` | ✓ carried, as `hp : p ≠ ⊤`; `1 ≤ p` as `[Fact (1 ≤ p)]` |
| conclusion: `Θ = {π⋆} × L^p_+(ν_B)` weakly `L^p`-universal | ✓ `weaklyUniversal_of_kernel` |
| conclusion: strong universality at `p = +∞` | ✗ not carried — as in `Core.UniversalityLp` and `Core.Flow` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

/-! ## Pushing a measure through a kernel preserves domination -/

/-- **A kernel push preserves domination**: `μ ≪ ν` implies `μ π⋆ ≪ ν π⋆`.

Mathlib has no lemma of this shape at `v4.31.0`, and it is the whole of what makes the density
action well defined. Nothing is asked of the kernel beyond measurability. -/
theorem bind_absolutelyContinuous_bind (κ : Kernel α α) {μ ν : Measure α} (h : μ ≪ ν) :
    μ.bind ⇑κ ≪ ν.bind ⇑κ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  have hm : Measurable fun x => κ x s := κ.measurable_coe hs
  rw [Measure.bind_apply hs (κ.aemeasurable (μ := ν)), lintegral_eq_zero_iff hm] at hs0
  rw [Measure.bind_apply hs (κ.aemeasurable (μ := μ)), lintegral_eq_zero_iff hm]
  exact h.ae_le hs0

/-- `bind` is additive in the measure: `(μ₁ + μ₂) π⋆ = μ₁ π⋆ + μ₂ π⋆`. -/
theorem bind_add_measure (κ : Kernel α α) (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).bind ⇑κ = μ₁.bind ⇑κ + μ₂.bind ⇑κ := by
  ext s hs
  rw [Measure.bind_apply hs (κ.aemeasurable (μ := μ₁ + μ₂)), Measure.add_apply,
    Measure.bind_apply hs (κ.aemeasurable (μ := μ₁)),
    Measure.bind_apply hs (κ.aemeasurable (μ := μ₂)), lintegral_add_measure]

/-- **`(f ν) π⋆ ≪ ν`, from invariance alone.** This is the main text's "invariance makes the
density action `P⋆ f := d((f ν_B) π⋆)/dν_B` well defined on `L¹(ν_B)`"
(`universality.tex:26–27`), and it is a theorem, not a hypothesis. -/
theorem bind_withDensity_absolutelyContinuous (κ : Kernel α α) {ν : Measure α}
    (hinv : ν.bind ⇑κ = ν) (f : α → ℝ≥0∞) : (ν.withDensity f).bind ⇑κ ≪ ν := by
  have h := bind_absolutelyContinuous_bind κ (withDensity_absolutelyContinuous ν f)
  rwa [hinv] at h

/-- **The mass of `(f ν) π⋆` is the mass of `f ν`** — stochasticity of the kernel, and not
invariance of the measure. -/
theorem bind_withDensity_univ (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α) (f : α → ℝ≥0∞) :
    ((ν.withDensity f).bind ⇑κ) Set.univ = ∫⁻ x, f x ∂ν := by
  rw [Measure.bind_apply MeasurableSet.univ (κ.aemeasurable (μ := ν.withDensity f))]
  simp only [measure_univ]
  rw [lintegral_one, withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]

/-- `(f ν) π⋆` is a finite measure as soon as `f` has finite `ν`-integral. -/
theorem isFiniteMeasure_bind_withDensity (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂ν ≠ ⊤) : IsFiniteMeasure ((ν.withDensity f).bind ⇑κ) :=
  ⟨by rw [bind_withDensity_univ κ ν f]; exact hf.lt_top⟩

/-! ## The density action on non-negative densities -/

/-- **The density action `T f := d((f ν) π⋆)/dν`** of the main text (`universality.tex:26–27`),
on non-negative densities. It is well defined — that is, `ν.withDensity (T f) = (f ν) π⋆` —
whenever `ν` is `π⋆`-invariant and `f` has finite integral; that is `withDensity_bindDensity`. -/
noncomputable def bindDensity (κ : Kernel α α) (ν : Measure α) (f : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  ((ν.withDensity f).bind ⇑κ).rnDeriv ν

/-- `T` depends on `f` only through its `ν`-a.e. class, and the dependence is by *equality* of
functions, not merely a.e. equality: `ν.withDensity` already forgets the null sets. This is what
makes `T` descend to `L^p(ν)` without a quotient argument. -/
theorem bindDensity_congr (κ : Kernel α α) (ν : Measure α) {f g : α → ℝ≥0∞} (h : f =ᵐ[ν] g) :
    bindDensity κ ν f = bindDensity κ ν g := by
  rw [bindDensity, bindDensity, withDensity_congr_ae h]

/-- `T f` is measurable, with no hypothesis on `f`: a Radon–Nikodym derivative always is. -/
theorem measurable_bindDensity (κ : Kernel α α) (ν : Measure α) (f : α → ℝ≥0∞) :
    Measurable (bindDensity κ ν f) :=
  Measure.measurable_rnDeriv _ _

/-- **`T f` is a genuine density for `(f ν) π⋆`.** This is the well-definedness assertion of
`universality.tex:26–27`, and it consumes invariance (through absolute continuity) and finite
mass (through the Lebesgue decomposition). -/
theorem withDensity_bindDensity (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) (f : α → ℝ≥0∞) :
    ν.withDensity (bindDensity κ ν f) = (ν.withDensity f).bind ⇑κ :=
  Measure.withDensity_rnDeriv_eq _ _ (bind_withDensity_absolutelyContinuous κ hinv f)

/-- **`∫ T f dν = ∫ f dν`** — the non-negative half of `hint`. It is stochasticity of `π⋆` that
is used here, each fibre `π⋆(x)` being a probability measure; invariance enters only through the
absolute continuity that makes `T f` a density at all. -/
theorem lintegral_bindDensity (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) (f : α → ℝ≥0∞) :
    ∫⁻ x, bindDensity κ ν f x ∂ν = ∫⁻ x, f x ∂ν := by
  calc ∫⁻ x, bindDensity κ ν f x ∂ν
      = (ν.withDensity (bindDensity κ ν f)) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = ((ν.withDensity f).bind ⇑κ) Set.univ := by rw [withDensity_bindDensity κ hinv f]
    _ = ∫⁻ x, f x ∂ν := bind_withDensity_univ κ ν f

/-- **`T 𝟏 = 𝟏`** — the non-negative half of `hone`, and pure invariance: `𝟏 ν = ν`, so
`(𝟏 ν) π⋆ = ν π⋆ = ν` and `dν/dν = 𝟏`. -/
theorem bindDensity_one (κ : Kernel α α) {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) : bindDensity κ ν 1 =ᵐ[ν] 1 := by
  rw [bindDensity, withDensity_one, hinv]
  exact Measure.rnDeriv_self ν

/-- `T 0 = 0`: the zero density pushes to the zero measure. -/
theorem bindDensity_zero (κ : Kernel α α) (ν : Measure α) : bindDensity κ ν 0 =ᵐ[ν] 0 := by
  rw [bindDensity, withDensity_zero, Measure.bind_zero_left]
  exact Measure.rnDeriv_zero ν

/-- **`T` is additive**, `ν`-a.e., on densities of finite integral. -/
theorem bindDensity_add (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hfi : ∫⁻ x, f x ∂ν ≠ ⊤)
    (hgi : ∫⁻ x, g x ∂ν ≠ ⊤) :
    bindDensity κ ν (f + g) =ᵐ[ν] bindDensity κ ν f + bindDensity κ ν g := by
  have hwd : ν.withDensity (f + g) = ν.withDensity f + ν.withDensity g := by
    have h1 : ν.withDensity (f + g) = ν.withDensity (hf.mk f + g) :=
      withDensity_congr_ae (hf.ae_eq_mk.add (Filter.EventuallyEq.refl _ g))
    have h2 : ν.withDensity (hf.mk f) = ν.withDensity f :=
      withDensity_congr_ae hf.ae_eq_mk.symm
    rw [h1, withDensity_add_left hf.measurable_mk g, h2]
  have hsplit : (ν.withDensity (f + g)).bind ⇑κ
      = (ν.withDensity f).bind ⇑κ + (ν.withDensity g).bind ⇑κ := by
    rw [hwd, bind_add_measure]
  haveI := isFiniteMeasure_bind_withDensity κ ν hfi
  haveI := isFiniteMeasure_bind_withDensity κ ν hgi
  rw [bindDensity, hsplit]
  exact Measure.rnDeriv_add _ _ _

/-- **`T` is positively homogeneous**, `ν`-a.e., for a finite scalar. -/
theorem bindDensity_smul (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    (hfi : ∫⁻ x, f x ∂ν ≠ ⊤) :
    bindDensity κ ν (c • f) =ᵐ[ν] c • bindDensity κ ν f := by
  have hwd : ν.withDensity (c • f) = c • ν.withDensity f := by
    have h1 : ν.withDensity (c • f) = ν.withDensity (c • hf.mk f) :=
      withDensity_congr_ae (hf.ae_eq_mk.fun_comp (c • ·))
    have h2 : ν.withDensity (hf.mk f) = ν.withDensity f :=
      withDensity_congr_ae hf.ae_eq_mk.symm
    rw [h1, withDensity_smul c hf.measurable_mk, h2]
  have hsplit : (ν.withDensity (c • f)).bind ⇑κ = c • ((ν.withDensity f).bind ⇑κ) := by
    rw [hwd, Measure.bind_smul]
  haveI := isFiniteMeasure_bind_withDensity κ ν hfi
  rw [bindDensity, hsplit]
  exact Measure.rnDeriv_smul_left_of_ne_top _ _ hc

/-! ## The density action on signed densities -/

/-- **The density action `P⋆ f := d((f ν) π⋆)/dν` on signed densities.** A signed density is
split into its positive and negative parts, each pushed by `T = bindDensity`, and the two
densities subtracted. Nothing here supposes `f` integrable or even measurable — the statements
that need it say so. -/
noncomputable def densityAction (κ : Kernel α α) (ν : Measure α) (f : α → ℝ) : α → ℝ :=
  fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal
    - (bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x).toReal

/-- `P⋆` depends on `f` only through its `ν`-a.e. class, and by *equality* of functions. This is
what lets it descend to `L^p(ν)`. -/
theorem densityAction_congr (κ : Kernel α α) (ν : Measure α) {f g : α → ℝ} (h : f =ᵐ[ν] g) :
    densityAction κ ν f = densityAction κ ν g := by
  have h1 : (fun y => ENNReal.ofReal (f y)) =ᵐ[ν] fun y => ENNReal.ofReal (g y) := by
    filter_upwards [h] with x hx; rw [hx]
  have h2 : (fun y => ENNReal.ofReal (-f y)) =ᵐ[ν] fun y => ENNReal.ofReal (-g y) := by
    filter_upwards [h] with x hx; rw [hx]
  have e1 := bindDensity_congr κ ν h1
  have e2 := bindDensity_congr κ ν h2
  funext x
  simp only [densityAction, e1, e2]

/-- `P⋆ f` is measurable, with no hypothesis on `f`. -/
theorem measurable_densityAction (κ : Kernel α α) (ν : Measure α) (f : α → ℝ) :
    Measurable (densityAction κ ν f) :=
  ((measurable_bindDensity κ ν _).ennreal_toReal).sub
    ((measurable_bindDensity κ ν _).ennreal_toReal)

/-- The positive part of an integrable function has finite `ν`-integral. -/
theorem lintegral_ofReal_ne_top {ν : Measure α} {f : α → ℝ} (hf : Integrable f ν) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≠ ⊤ := by
  refine ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_mono fun x => ?_)
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- `T f⁺` has finite `ν`-integral, hence is a.e. finite. -/
theorem bindDensity_ofReal_lt_top (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∀ᵐ x ∂ν, bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x < ⊤ :=
  ae_lt_top (measurable_bindDensity κ ν _)
    (by rw [lintegral_bindDensity κ hinv]; exact lintegral_ofReal_ne_top hf)

/-- `(T f⁺).toReal` is `ν`-integrable, with `∫ (T f⁺).toReal dν = ∫ f⁺ dν`. -/
theorem integrable_toReal_bindDensity (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    Integrable (fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (measurable_bindDensity κ ν _).aemeasurable
    (by rw [lintegral_bindDensity κ hinv]; exact lintegral_ofReal_ne_top hf)

theorem integral_toReal_bindDensity (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∫ x, (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal ∂ν
      = (∫⁻ x, ENNReal.ofReal (f x) ∂ν).toReal := by
  rw [integral_toReal (measurable_bindDensity κ ν _).aemeasurable
      (bindDensity_ofReal_lt_top κ hinv hf), lintegral_bindDensity κ hinv]

/-- **`hint`, in the paper's own terms**: `∫ P⋆ f dν = ∫ f dν` for every `ν`-integrable `f`.

Stochasticity of `π⋆` is what is used — each fibre `π⋆(x)` is a probability measure, so the push
`(f ν) π⋆` has the mass of `f ν`. Invariance enters only through the absolute continuity that
makes `P⋆ f` a density. -/
theorem integral_densityAction (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∫ x, densityAction κ ν f x ∂ν = ∫ x, f x ∂ν := by
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  simp only [densityAction]
  rw [integral_sub (integrable_toReal_bindDensity κ hinv hf)
      (integrable_toReal_bindDensity κ hinv hfn),
    integral_toReal_bindDensity κ hinv hf, integral_toReal_bindDensity κ hinv hfn]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm

/-- **`hone`**: `P⋆ 𝟏 = 𝟏` a.e. This is pure invariance — `𝟏 ν = ν`, so `(𝟏 ν) π⋆ = ν` and its
`ν`-density is `𝟏`; the negative part is the zero density and contributes nothing. -/
theorem densityAction_one (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) : densityAction κ ν 1 =ᵐ[ν] 1 := by
  have h1 : (fun y : α => ENNReal.ofReal ((1 : α → ℝ) y)) = 1 := by
    funext y; simp
  have h0 : (fun y : α => ENNReal.ofReal (-(1 : α → ℝ) y)) = 0 := by
    funext y; simp
  filter_upwards [bindDensity_one κ (ν := ν) hinv, bindDensity_zero κ ν] with x hx1 hx0
  simp only [densityAction, h1, h0]
  rw [hx1, hx0]
  simp

/-! ## Linearity -/

/-- The real identity behind additivity of `P⋆`: `(u+v)⁺ + u⁻ + v⁻ = (u+v)⁻ + u⁺ + v⁺`. -/
theorem max_add_aux (u v : ℝ) :
    max (u + v) 0 + max (-u) 0 + max (-v) 0 = max (-(u + v)) 0 + max u 0 + max v 0 := by
  have h : ∀ x : ℝ, max x 0 - max (-x) 0 = x := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ (0 : ℝ))]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith : (0 : ℝ) ≤ -x)]; ring
  have h1 := h (u + v)
  have h2 := h u
  have h3 := h v
  linarith

/-- The same identity in `ℝ≥0∞`, which is where `T` consumes it. -/
theorem ofReal_add_aux (u v : ℝ) :
    ENNReal.ofReal (u + v) + ENNReal.ofReal (-u) + ENNReal.ofReal (-v)
      = ENNReal.ofReal (-(u + v)) + ENNReal.ofReal u + ENNReal.ofReal v := by
  have e : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx]
    · rw [max_eq_right hx, ENNReal.ofReal_of_nonpos hx, ENNReal.ofReal_zero]
  rw [e (u + v), e (-u), e (-v), e (-(u + v)), e u, e v,
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _), max_add_aux u v]

/-- `∫ (u + v) dν` is finite when both summands are. -/
theorem lintegral_add_ne_top {ν : Measure α} {u v : α → ℝ≥0∞} (hu : AEMeasurable u ν)
    (hun : ∫⁻ x, u x ∂ν ≠ ⊤) (hvn : ∫⁻ x, v x ∂ν ≠ ⊤) : ∫⁻ x, (u + v) x ∂ν ≠ ⊤ := by
  simp only [Pi.add_apply]
  rw [lintegral_add_left' hu]
  exact ENNReal.add_ne_top.2 ⟨hun, hvn⟩

/-- `T` on a sum of three densities of finite integral. -/
theorem bindDensity_add₃ (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    {u v w : α → ℝ≥0∞} (hu : AEMeasurable u ν) (hv : AEMeasurable v ν)
    (hun : ∫⁻ x, u x ∂ν ≠ ⊤) (hvn : ∫⁻ x, v x ∂ν ≠ ⊤) (hwn : ∫⁻ x, w x ∂ν ≠ ⊤) :
    bindDensity κ ν (u + v + w)
      =ᵐ[ν] bindDensity κ ν u + bindDensity κ ν v + bindDensity κ ν w := by
  have h1 : bindDensity κ ν (u + v + w) =ᵐ[ν] bindDensity κ ν (u + v) + bindDensity κ ν w :=
    bindDensity_add κ (hu.add hv) (lintegral_add_ne_top hu hun hvn) hwn
  have h2 : bindDensity κ ν (u + v) =ᵐ[ν] bindDensity κ ν u + bindDensity κ ν v :=
    bindDensity_add κ hu hun hvn
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Pi.add_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]

/-- The positive part of an integrable function is `ν`-a.e. measurable as an `ℝ≥0∞` density. -/
theorem aemeasurable_ofReal {ν : Measure α} {f : α → ℝ} (hf : Integrable f ν) :
    AEMeasurable (fun y => ENNReal.ofReal (f y)) ν :=
  ENNReal.measurable_ofReal.comp_aemeasurable hf.aestronglyMeasurable.aemeasurable

/-- **`P⋆` is additive**, `ν`-a.e., on `ν`-integrable densities.

The proof is the pointwise identity `(u+v)⁺ + u⁻ + v⁻ = (u+v)⁻ + u⁺ + v⁺` of `ofReal_add_aux`,
pushed through `T` — which is additive by `bindDensity_add` — and read back in `ℝ` where every
term is finite. Subtraction in `ℝ≥0∞` is never performed. -/
theorem densityAction_add (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) {f g : α → ℝ} (hf : Integrable f ν) (hg : Integrable g ν) :
    densityAction κ ν (fun x => f x + g x)
      =ᵐ[ν] fun x => densityAction κ ν f x + densityAction κ ν g x := by
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  have hgn : Integrable (fun x => -g x) ν := hg.neg
  have hs : Integrable (fun x => f x + g x) ν := hf.add hg
  have hsn : Integrable (fun x => -(f x + g x)) ν := hs.neg
  have hfun : (fun y => ENNReal.ofReal (f y + g y)) + (fun y => ENNReal.ofReal (-f y))
        + (fun y => ENNReal.ofReal (-g y))
      = (fun y => ENNReal.ofReal (-(f y + g y))) + (fun y => ENNReal.ofReal (f y))
        + (fun y => ENNReal.ofReal (g y)) := by
    funext y
    simpa only [Pi.add_apply] using ofReal_add_aux (f y) (g y)
  have hL := bindDensity_add₃ κ (aemeasurable_ofReal hs) (aemeasurable_ofReal hfn)
    (lintegral_ofReal_ne_top hs) (lintegral_ofReal_ne_top hfn) (lintegral_ofReal_ne_top hgn)
  have hR := bindDensity_add₃ κ (aemeasurable_ofReal hsn) (aemeasurable_ofReal hf)
    (lintegral_ofReal_ne_top hsn) (lintegral_ofReal_ne_top hf) (lintegral_ofReal_ne_top hg)
  rw [hfun] at hL
  filter_upwards [hL, hR, bindDensity_ofReal_lt_top κ hinv hf,
    bindDensity_ofReal_lt_top κ hinv hfn, bindDensity_ofReal_lt_top κ hinv hg,
    bindDensity_ofReal_lt_top κ hinv hgn, bindDensity_ofReal_lt_top κ hinv hs,
    bindDensity_ofReal_lt_top κ hinv hsn] with x hxL hxR hA hB hC hD hE hK
  simp only [Pi.add_apply] at hxL hxR
  have hkey : bindDensity κ ν (fun y => ENNReal.ofReal (f y + g y)) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (-g y)) x
      = bindDensity κ ν (fun y => ENNReal.ofReal (-(f y + g y))) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (g y)) x := by
    rw [← hxL, ← hxR]
  have hreal := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hE.ne, hB.ne⟩) hD.ne,
    ENNReal.toReal_add hE.ne hB.ne,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hK.ne, hA.ne⟩) hC.ne,
    ENNReal.toReal_add hK.ne hA.ne] at hreal
  simp only [densityAction]
  linarith

/-- `P⋆(-f) = -P⋆ f`, by definition: negation swaps the positive and negative parts. -/
theorem densityAction_neg (κ : Kernel α α) (ν : Measure α) (f : α → ℝ) :
    densityAction κ ν (fun x => -f x) = fun x => -densityAction κ ν f x := by
  funext x
  simp only [densityAction, neg_neg]
  ring

/-- `P⋆` is homogeneous under a non-negative scalar. -/
theorem densityAction_smul_nonneg (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] {r : ℝ} (hr : 0 ≤ r) {f : α → ℝ} (hf : Integrable f ν) :
    densityAction κ ν (fun x => r * f x) =ᵐ[ν] fun x => r * densityAction κ ν f x := by
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  have e1 : (fun y => ENNReal.ofReal (r * f y))
      = ENNReal.ofReal r • fun y => ENNReal.ofReal (f y) := by
    funext y; simp [ENNReal.ofReal_mul hr, smul_eq_mul]
  have e2 : (fun y => ENNReal.ofReal (-(r * f y)))
      = ENNReal.ofReal r • fun y => ENNReal.ofReal (-f y) := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hr]
    ring_nf
  have hA := bindDensity_smul κ (c := ENNReal.ofReal r) ENNReal.ofReal_ne_top
    (aemeasurable_ofReal hf) (lintegral_ofReal_ne_top hf)
  have hB := bindDensity_smul κ (c := ENNReal.ofReal r) ENNReal.ofReal_ne_top
    (aemeasurable_ofReal hfn) (lintegral_ofReal_ne_top hfn)
  filter_upwards [hA, hB] with x hxA hxB
  simp only [densityAction, e1, e2]
  rw [hxA, hxB]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]
  ring

/-- **`P⋆` is homogeneous**, `ν`-a.e., under every real scalar. -/
theorem densityAction_smul (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (r : ℝ) {f : α → ℝ} (hf : Integrable f ν) :
    densityAction κ ν (fun x => r * f x) =ᵐ[ν] fun x => r * densityAction κ ν f x := by
  rcases le_total 0 r with hr | hr
  · exact densityAction_smul_nonneg κ hr hf
  · have hrn : (0 : ℝ) ≤ -r := by linarith
    have e : (fun x => r * f x) = fun x => -((-r) * f x) := by funext x; ring
    have h := densityAction_smul_nonneg κ hrn hf
    rw [e, densityAction_neg]
    filter_upwards [h] with x hx
    rw [hx]
    ring

/-! ## `P⋆` as a bounded operator on `L^p(ν)`, and the universality payoff -/

/-- **The paper's boundedness hypothesis on the parameterization**, and the only hypothesis of
`theo:universality_L2_full` that this file assumes rather than derives.

`theo:universality_L2_full` asks for "a Markov kernel on `𝒮` with finite
`L^p(ν_B) → L^p(ν_B)` operator norm", and the main text is explicit that this is a requirement on
the parameterization and not a theorem: "boundedness of `‖π⋆‖_{L^p(ν_B)}` […] is not automatic"
(`universality.tex:6–9`), "the definitions above do not guarantee that `‖π⋆‖_{L^p(ν_B)}` is
finite" (`proofs.tex:36`). The two fields are the two halves of "`P⋆` is a bounded operator of
`L^p(ν_B)`": that it maps `L^p` into `L^p`, and that it does so with a bound. `C` is the operator
norm bound, carried explicitly rather than as `∃ C`. -/
structure IsBoundedDensityAction (κ : Kernel α α) (ν : Measure α) (p : ℝ≥0∞) (C : ℝ) : Prop where
  /-- The bound is non-negative. -/
  nonneg : 0 ≤ C
  /-- `P⋆` maps `L^p(ν)` into `L^p(ν)`. -/
  memLp : ∀ f : α → ℝ, MemLp f p ν → MemLp (densityAction κ ν f) p ν
  /-- `‖P⋆ f‖_{L^p(ν)} ≤ C ‖f‖_{L^p(ν)}`. -/
  eLpNorm_le : ∀ f : α → ℝ, MemLp f p ν →
    eLpNorm (densityAction κ ν f) p ν ≤ ENNReal.ofReal C * eLpNorm f p ν

/-- `P⋆` as a linear map on `L^p(ν)`. Linearity is `densityAction_add` and `densityAction_smul`
read on the `L^p` quotient, which is where the two a.e. identities become equalities. -/
noncomputable def densityActionLM (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) : Lp ℝ p ν →ₗ[ℝ] Lp ℝ p ν where
  toFun F := (hb.memLp _ (Lp.memLp F)).toLp _
  map_add' F G := by
    have hae : densityAction κ ν ⇑(F + G)
        =ᵐ[ν] densityAction κ ν ⇑F + densityAction κ ν ⇑G := by
      have h1 : densityAction κ ν ⇑(F + G)
          = densityAction κ ν fun x => (F : α → ℝ) x + (G : α → ℝ) x := by
        refine densityAction_congr κ ν ?_
        filter_upwards [Lp.coeFn_add F G] with x hx
        simpa using hx
      rw [h1]
      filter_upwards [densityAction_add κ hinv (integrable_of_Lp F) (integrable_of_Lp G)]
        with x hx
      simpa using hx
    rw [← MemLp.toLp_add (hb.memLp _ (Lp.memLp F)) (hb.memLp _ (Lp.memLp G))]
    exact MemLp.toLp_congr _ _ hae
  map_smul' c F := by
    have hae : densityAction κ ν ⇑(c • F) =ᵐ[ν] c • densityAction κ ν ⇑F := by
      have h1 : densityAction κ ν ⇑(c • F)
          = densityAction κ ν fun x => c * (F : α → ℝ) x := by
        refine densityAction_congr κ ν ?_
        filter_upwards [Lp.coeFn_smul c F] with x hx
        simpa using hx
      rw [h1]
      filter_upwards [densityAction_smul κ c (integrable_of_Lp F)] with x hx
      simpa using hx
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (hb.memLp _ (Lp.memLp F))]
    exact MemLp.toLp_congr _ _ hae

/-- **`P⋆` as a `ContinuousLinearMap` on `L^p(ν)`**, with the paper's own operator-norm bound `C`
as the continuity constant. -/
noncomputable def densityActionCLM (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) : Lp ℝ p ν →L[ℝ] Lp ℝ p ν :=
  (densityActionLM κ ν p hinv hb).mkContinuous C fun F => by
    have h := hb.eLpNorm_le _ (Lp.memLp F)
    have hne : ENNReal.ofReal C * eLpNorm (⇑F) p ν ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)
    calc ‖(densityActionLM κ ν p hinv hb) F‖
        = (eLpNorm (densityAction κ ν ⇑F) p ν).toReal :=
          Lp.norm_toLp _ (hb.memLp _ (Lp.memLp F))
      _ ≤ (ENNReal.ofReal C * eLpNorm (⇑F) p ν).toReal := ENNReal.toReal_mono hne h
      _ = C * ‖F‖ := by
          simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.nonneg, Lp.norm_def]

/-- `‖P⋆‖_{L^p→L^p} ≤ C`: the paper's constant bounds the operator norm, as rule 3 asks. -/
theorem norm_densityActionCLM_le (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) : ‖densityActionCLM κ ν p hinv hb‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hb.nonneg _

/-- The `L^p` operator applied to `F` is represented by `P⋆` applied to any representative. -/
theorem coeFn_densityActionCLM (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) (F : Lp ℝ p ν) :
    ⇑(densityActionCLM κ ν p hinv hb F) =ᵐ[ν] densityAction κ ν ⇑F :=
  MemLp.coeFn_toLp (hb.memLp _ (Lp.memLp F))

/-- **`hone` on `L^p(ν)`**: `P⋆ 𝟏 = 𝟏`, the paper's `(Id − P⋆) 𝟏 = 0` (`proofs.tex:100`). -/
theorem densityActionCLM_constOne (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) :
    densityActionCLM κ ν p hinv hb (constOne ν p) = constOne ν p := by
  have h1 : densityAction κ ν ⇑(constOne ν p) =ᵐ[ν] fun _ : α => (1 : ℝ) := by
    rw [densityAction_congr κ ν (coeFn_constOne (ν := ν) (p := p))]
    exact densityAction_one κ hinv
  exact MemLp.toLp_congr (hb.memLp _ (Lp.memLp (constOne ν p))) (memLp_const (1 : ℝ)) h1

/-- **`hint` on `L^p(ν)`**: `∫ P⋆ f dν = ∫ f dν`. -/
theorem integral_densityActionCLM (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) (F : Lp ℝ p ν) :
    ∫ x, (densityActionCLM κ ν p hinv hb F) x ∂ν = ∫ x, F x ∂ν := by
  rw [integral_congr_ae (coeFn_densityActionCLM κ ν p hinv hb F)]
  exact integral_densityAction κ hinv (integrable_of_Lp F)

/-- **`theo:universality_L2_full`'s weak half, from the paper's own hypotheses about the kernel.**

`π⋆` is a Markov kernel, `ν` is finite and `π⋆`-invariant, `P⋆` is bounded on `L^p(ν)` with
constant `C` — the paper's requirement on the parameterization — and the mixing coefficients
`β_n = ‖P⋆^n − Π‖` are summable. Then `Θ = {π⋆} × L^p_+(ν)` is weakly `L^p`-universal for
`p < ∞`, with `Π` the mean projection of `proofs.tex:22`.

No operator is hypothesised: `P⋆` is built from `π⋆` here, `Π P⋆ = P⋆ Π = Π` is derived in
`Core.Flow` from `hone` and `hint`, and those two are theorems above. What remains assumed is
what the paper assumes — boundedness and summable mixing. -/
theorem weaklyUniversal_of_kernel (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν p hinv hb) ^ n - meanProj ν p‖)
    (hp : p ≠ ⊤) :
    WeaklyUniversal (densityActionCLM κ ν p hinv hb) (meanProj ν p) :=
  weaklyUniversal_of_massPreserving (densityActionCLM_constOne κ ν p hinv hb)
    (integral_densityActionCLM κ ν p hinv hb) hsum hp

/-- **The same, at one admissible pair**: two densities in `L^p(ν)` of equal total mass are
joined to arbitrary accuracy by a non-negative outflow against the kernel `π⋆`. -/
theorem weaklyUniversalAt_of_kernel (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν p hinv hb) ^ n - meanProj ν p‖)
    (hp : p ≠ ⊤) {f_init f_term : Lp ℝ p ν}
    (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    WeaklyUniversalAt (densityActionCLM κ ν p hinv hb) (f_term - f_init) :=
  weaklyUniversal_of_kernel κ ν p hinv hb hsum hp _ (meanProj_sub_eq_zero hmass)

end GFNBounds.Core
