import GFNBounds.Core.SigmaMixing
import GFNBounds.Core.AdjointGeneral
import GFNBounds.Doubling.OperatorFiniteSum

/-!
# The diffusion operator of a Markov kernel on a measurable space

**`lem:doubling_operator`** — `app_doubling.tex`, statement and proof under the label (line
citations drift, kb `0036`; the label is the anchor).

> Let `T` be a Markov kernel on a measurable space carrying an invariant probability `λ`, let `P`
> be its density action `Pu := d((uλ)T)/dλ` and `P⋆` its function action
> `(P⋆v)(x) := ∫ v dT(x, ·)`, let `Π` be the `λ`-mean projection, let `β̂ₙ := ‖Pⁿ − Π‖_{L²(λ)}`
> and, whenever `Id − P⋆ + Π` is invertible on `L²(λ)`, put `S := (Id − P⋆ + Π)^{-1} − Π` and
> `B̂ := ‖S‖_{L²(λ)}`. Then:
> *(1)* `P⋆` is a contraction of `L^p(λ)` for every `p ∈ [1, +∞]` and is the `L²(λ)`-adjoint of
> `P`, so that `‖P⋆ⁿ − Π‖_{L²(λ)} = β̂ₙ` for every `n ≥ 0`;
> *(2)* if moreover the chain is finite and irreducible then `P⋆` fixes only the constant
> functions, the operator `Id − P⋆ + Π` is invertible, and
> `S(Id − P⋆) = (Id − P⋆)S = Id − Π`, `ΠS = SΠ = 0` (`eq:doubling_resolvent`);
> *(3)* if `U := Σ_{n≥0}(P⋆ⁿ − Π)` converges in operator norm on `L²(λ)`, then `Id − P⋆ + Π` is
> invertible with inverse `Π + U`, the operator `S` equals `U` and satisfies
> `eq:doubling_resolvent`, and `B̂ ≤ Σ_{n≥0} β̂ₙ`; in particular, on a finite irreducible chain
> `B̂ ≤ Σ_{n≥0} β̂ₙ`, the inequality being vacuous when its right side is `+∞`.

The library certified this lemma only on the doubling graph (`Doubling/Operator*.lean`,
`AdjointL2.lean`, `LpContraction.lean`), with the abstract Banach-space algebra of items (2)–(3)
in `Operator.lean`, `OperatorFinite.lean`, `OperatorFiniteSum.lean`. This file states and proves
it **for the paper's general kernel**, reusing that algebra verbatim and the general layer of
`Core/Kernel.lean` (the density action on signed densities), `Core/SigmaMixing.lean`
(`densityActionL2`, `‖P‖ ≤ 1` from invariance alone) and `Core/AdjointGeneral.lean` (the
function action and its per-fibre Jensen contraction).

## What the paper claims and this file delivers

| paper | here |
|---|---|
| `P`, `Pu = d((uλ)T)/dλ` on `L²(λ)` | `Core.densityActionL2 T λ hinv` (inherited from `Core.Kernel`, `Core.SigmaMixing`) |
| `P⋆`, `(P⋆v)(x) = ∫ v dT(x)` | `funActLp T λ p hinv`, with `coeFn_funActLp : P⋆F =ᵐ funAct T F` |
| `Π`, `β̂ₙ`, `S`, `B̂` | `Core.meanProj λ 2`; `betaHat` (on `P`, as the paper defines it); `Ring.inverse (1 − P⋆ + Π) − Π`; its norm |
| *(1)* contraction of `L^p(λ)`, `p ∈ [1, ∞]` | `norm_funActLp_le` (every `p` with `Fact (1 ≤ p)`, `∞` included) |
| *(1)* `P⋆ = P*` | `inner_densityActionL2_left`, `adjoint_densityActionL2`, `adjoint_funActL2` |
| *(1)* `‖P⋆ⁿ − Π‖ = β̂ₙ` | `norm_funActL2_pow_sub` (via `adjoint_meanProj`: `Π` self-adjoint) |
| *(2)* `P⋆` fixes only constants | `eq_smul_constOne_of_fixed` (maximum principle `funAct_fixed_const`) |
| *(2)* `λ` positive at every state (the proof's first sentence) | `measure_singleton_ne_zero` |
| *(2)* `L²(λ)` finite-dimensional, `Id − P⋆ + Π` invertible, `eq:doubling_resolvent` | `finiteDimensional_Lp`, `doubling_operator_item2` |
| *(3)* inverse `Π + U`, `S = U`, `eq:doubling_resolvent`, `B̂ ≤ Σβ̂ₙ` | `doubling_operator_item3` |
| *(3)* "in particular" on a finite irreducible chain | `doubling_operator_item3_finite` |
| the whole lemma | `lem_doubling_operator` |
| hypotheses inhabited | `doubling_operator_witness` (the two-state chain) |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `T` a Markov kernel on a measurable space | ✓ `T : Kernel α α`, `[IsMarkovKernel T]`, `α` any measurable space — no standard Borel structure, no countability |
| `λ` an invariant probability | ✓ `[IsProbabilityMeasure lam]`, `hinv : lam.bind T = lam` in `lem_doubling_operator`; the component theorems ask only `[IsFiniteMeasure lam]` (and `[NeZero lam]` where `Π² = Π` is used) |
| "the chain is finite" | ✓ `Finite α` with `MeasurableSingletonClass α` — a finite state space whose states are events, which is what "finite chain" means for a kernel |
| "irreducible" | ✓ `KernelIrreducible T`: every `y` reachable from every `x` along transitions with `T(a, {b}) ≠ 0` (`Relation.ReflTransGen`), i.e. `P(X_n = y ∣ X_0 = x) > 0` for some `n ≥ 0` |
| `S` defined "whenever `Id − P⋆ + Π` is invertible" | ✓ `Ring.inverse`; every clause about `S` is stated together with `IsUnit (1 − P⋆ + Π)` |
| the series converges in operator norm | ✓ `hconv : Tendsto (partialSum P⋆ Π) atTop (𝓝 U)` |
| `B̂ ≤ Σβ̂ₙ`, vacuous at `+∞` | ✓ twice: at every real bound of the partial sums, and in `ℝ≥0∞` as `ofReal B̂ ≤ Σ' ofReal β̂ₙ` (`ofReal_le_tsum_of_forall_bdd`), which is the extended-real inequality itself |

## SCOPE (disclosed)

* **The adjointness is proved by density of indicators, not by Riesz.** The paper identifies
  `Pu` through the Riesz representation of `v ↦ ∫ v d((uλ)T)`. Here `P` is already a bounded
  operator (`Core.SigmaMixing.isBoundedDensityAction_two`), so it suffices to check
  `⟪P𝟏_B, 𝟏_A⟫ = ∫_B T(x, A) λ(dx) = ⟪𝟏_B, P⋆𝟏_A⟫` (`inner_densityActionL2_indicator`, from
  `Core.SigmaMixing.lintegral_bindDensity_mul`) and extend by `MeasureTheory.Lp.induction` in each
  variable, both sides being continuous and additive. No disintegration and no `λ`-reversal is
  used, so no standard Borel hypothesis enters.
* **Item (2)'s "fixes only the constants" is proved by the maximum principle**, not by the
  strict-convexity equality case of Jensen the paper uses (via `lem:doubling_fixed_points`). Same
  statement, different route; the paper's route needs the positivity of `λ` too, and that is
  proved here (`measure_singleton_ne_zero`), not assumed.
* **Uniqueness of the invariant probability on a finite irreducible chain is not proved and not
  used**: the paper invokes it to identify `λ`, but the argument needs only that `λ` is *an*
  invariant probability, which is the hypothesis, and that it charges every state, which is
  derived.
* **`P` on signed densities** is `Core.Kernel.densityAction`, `(Tf⁺) − (Tf⁻)`; that modelling
  choice is `Core/Kernel.lean`'s and is inherited.
* **`sorry`-free; no new axiom.** Nothing here is behind obstruction 2 of kb `0006`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling.General

open MeasureTheory ProbabilityTheory Filter GFNBounds.Core
open scoped ENNReal Topology InnerProductSpace

variable {α : Type*} [MeasurableSpace α]

section FunAct

variable (T : Kernel α α) {lam : Measure α}

/-- The invariance hypothesis in `Core.Kernel`'s form is `Core.General.IsInvariant`. -/
theorem isInvariant_of_bind (hinv : lam.bind ⇑T = lam) : General.IsInvariant T lam := hinv

/-- An integrable function is integrable against `T(x, ·)` for `λ`-a.e. `x`. -/
theorem ae_integrable_fibre (hinv : lam.bind ⇑T = lam) {u : α → ℝ} (hu : Integrable u lam) :
    ∀ᵐ x ∂lam, Integrable u (T x) := by
  have hu' : Integrable u (T ∘ₘ lam) := by
    show Integrable u (lam.bind ⇑T); rw [hinv]; exact hu
  exact ((Measure.integrable_comp_iff hu'.1).1 hu').1

/-- The function action is additive on integrable functions, `λ`-a.e. -/
theorem funAct_add_ae (hinv : lam.bind ⇑T = lam) {u v : α → ℝ} (hu : Integrable u lam)
    (hv : Integrable v lam) :
    General.funAct T (u + v) =ᵐ[lam] General.funAct T u + General.funAct T v := by
  filter_upwards [ae_integrable_fibre T hinv hu, ae_integrable_fibre T hinv hv] with x hux hvx
  simp only [General.funAct, _root_.Pi.add_apply]
  exact integral_add hux hvx

/-- The function action is homogeneous, everywhere. -/
theorem funAct_smul (c : ℝ) (u : α → ℝ) :
    General.funAct T (c • u) = c • General.funAct T u := by
  funext x
  simp only [General.funAct, _root_.Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

end FunAct

/-! ## `P⋆` on `L^p(λ)`, `1 ≤ p ≤ ∞` -/

section FunActLp

variable (T : Kernel α α) [IsMarkovKernel T] (lam : Measure α) [IsFiniteMeasure lam]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- `P⋆` as a linear map on `L^p(λ)`. -/
noncomputable def funActLM (hinv : lam.bind ⇑T = lam) : Lp ℝ p lam →ₗ[ℝ] Lp ℝ p lam where
  toFun F := ((isInvariant_of_bind T hinv).memLp_funAct Fact.out (Lp.memLp F)).toLp _
  map_add' F G := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    have h1 : General.funAct T ⇑(F + G) =ᵐ[lam] General.funAct T (⇑F + ⇑G) :=
      (isInvariant_of_bind T hinv).funAct_congr (Lp.coeFn_add F G)
    exact h1.trans (funAct_add_ae T hinv (integrable_of_Lp F) (integrable_of_Lp G))
  map_smul' c F := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    have h1 : General.funAct T ⇑(c • F) =ᵐ[lam] General.funAct T (c • ⇑F) :=
      (isInvariant_of_bind T hinv).funAct_congr (Lp.coeFn_smul c F)
    rw [funAct_smul] at h1
    exact h1

/-- **`lem:doubling_operator`, the function action `P⋆`**: `P⋆v(x) = ∫ v dT(x)` on `L^p(λ)`,
for every `1 ≤ p ≤ ∞`, as a bounded operator of norm at most `1`. -/
noncomputable def funActLp (hinv : lam.bind ⇑T = lam) : Lp ℝ p lam →L[ℝ] Lp ℝ p lam :=
  (funActLM T lam p hinv).mkContinuous 1 fun F => by
    have h := (isInvariant_of_bind T hinv).eLpNorm_funAct_le (Lp.aestronglyMeasurable F)
      (Fact.out : (1 : ℝ≥0∞) ≤ p)
    rw [one_mul]
    show ‖((isInvariant_of_bind T hinv).memLp_funAct Fact.out (Lp.memLp F)).toLp _‖ ≤ ‖F‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top F) h

/-- **`lem:doubling_operator`(1), the contraction**: `‖P⋆‖_{L^p(λ) → L^p(λ)} ≤ 1` for every
`p ∈ [1, +∞]`. -/
theorem norm_funActLp_le (hinv : lam.bind ⇑T = lam) : ‖funActLp T lam p hinv‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem coeFn_funActLp (hinv : lam.bind ⇑T = lam) (F : Lp ℝ p lam) :
    ⇑(funActLp T lam p hinv F) =ᵐ[lam] General.funAct T ⇑F :=
  MemLp.coeFn_toLp ((isInvariant_of_bind T hinv).memLp_funAct Fact.out (Lp.memLp F))

/-- `P⋆ 𝟏 = 𝟏`. -/
theorem funActLp_constOne (hinv : lam.bind ⇑T = lam) :
    funActLp T lam p hinv (constOne lam p) = constOne lam p := by
  refine Lp.ext ?_
  filter_upwards [coeFn_funActLp T lam p hinv (constOne lam p),
    (isInvariant_of_bind T hinv).funAct_congr (coeFn_constOne (ν := lam) (p := p)),
    coeFn_constOne (ν := lam) (p := p)] with x h1 h2 h3
  rw [h1, h2, h3, General.funAct_one]

end FunActLp

/-! ## `P⋆ = P*` on `L²(λ)` -/

section Adjoint

variable (T : Kernel α α) [IsMarkovKernel T] (lam : Measure α) [IsFiniteMeasure lam]

omit [MeasurableSpace α] in
/-- `c • 𝟏_A = c • (1 • 𝟏_A)`, as classes. -/
theorem indicatorConstLp_eq_smul {m : MeasurableSpace α} {μ : Measure α} {A : Set α}
    (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (c : ℝ) :
    indicatorConstLp 2 hA hμA c = c • indicatorConstLp 2 hA hμA (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c),
    Lp.coeFn_smul c (indicatorConstLp 2 hA hμA (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := (1 : ℝ))] with x h1 h2 h3
  rw [h1, h2, _root_.Pi.smul_apply, h3]
  by_cases hx : x ∈ A <;> simp [hx]

omit [IsMarkovKernel T] [IsFiniteMeasure lam] in
/-- The density action of an indicator: `P𝟏_B = (T𝟏_B).toReal`, `λ`-a.e. -/
theorem densityAction_indicator {B : Set α} :
    densityAction T lam (B.indicator fun _ => (1 : ℝ))
      =ᵐ[lam] fun x => (bindDensity T lam (B.indicator 1) x).toReal := by
  have h1 : (fun y => ENNReal.ofReal (B.indicator (fun _ => (1 : ℝ)) y)) = B.indicator 1 := by
    funext y; by_cases hy : y ∈ B <;> simp [hy]
  have h2 : (fun y => ENNReal.ofReal (-B.indicator (fun _ => (1 : ℝ)) y)) = 0 := by
    funext y; by_cases hy : y ∈ B <;> simp [hy]
  filter_upwards [bindDensity_zero T lam] with x hx
  simp only [densityAction, h1, h2, hx, _root_.Pi.zero_apply, ENNReal.toReal_zero, sub_zero]

/-- `∫_A P𝟏_B dλ = ∫_B T(x, A) λ(dx)`, in `ℝ≥0∞`. -/
theorem setLIntegral_bindDensity_indicator (hinv : lam.bind ⇑T = lam) {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, bindDensity T lam (B.indicator 1) x ∂lam = ∫⁻ x in B, T x A ∂lam := by
  have hAm : Measurable (A.indicator (1 : α → ℝ≥0∞)) := measurable_one.indicator hA
  have key := lintegral_bindDensity_mul T hinv
    ((measurable_one.indicator hB).aemeasurable (μ := lam)) hAm
  calc ∫⁻ x in A, bindDensity T lam (B.indicator 1) x ∂lam
      = ∫⁻ x, bindDensity T lam (B.indicator 1) x * A.indicator 1 x ∂lam := by
        rw [← lintegral_indicator hA]; congr 1; funext x
        by_cases hx : x ∈ A <;> simp [hx]
    _ = ∫⁻ x, B.indicator 1 x * ∫⁻ y, A.indicator 1 y ∂T x ∂lam := key
    _ = ∫⁻ x in B, T x A ∂lam := by
        rw [← lintegral_indicator hB]; congr 1; funext x
        rw [lintegral_indicator_one hA]
        by_cases hx : x ∈ B <;> simp [hx]

/-- **The adjointness on indicators**: `⟪P𝟏_B, 𝟏_A⟫ = ⟪𝟏_B, P⋆𝟏_A⟫ = ∫_B T(x, A) λ(dx)`. -/
theorem inner_densityActionL2_indicator (hinv : lam.bind ⇑T = lam) {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ⟪densityActionL2 T lam hinv (indicatorConstLp 2 hB (measure_ne_top lam B) (1 : ℝ)),
        indicatorConstLp 2 hA (measure_ne_top lam A) (1 : ℝ)⟫_ℝ
      = ⟪indicatorConstLp 2 hB (measure_ne_top lam B) (1 : ℝ),
          funActLp T lam 2 hinv (indicatorConstLp 2 hA (measure_ne_top lam A) (1 : ℝ))⟫_ℝ := by
  rw [real_inner_comm, L2.inner_indicatorConstLp_one, L2.inner_indicatorConstLp_one]
  have hfinB : ∫⁻ x, B.indicator (1 : α → ℝ≥0∞) x ∂lam ≠ ⊤ := by
    rw [lintegral_indicator_one hB]; exact measure_ne_top lam B
  -- left side
  have hL : ∫ x in A, (densityActionL2 T lam hinv
        (indicatorConstLp 2 hB (measure_ne_top lam B) (1 : ℝ))) x ∂lam
      = (∫⁻ x in B, T x A ∂lam).toReal := by
    have hae : ⇑(densityActionL2 T lam hinv
          (indicatorConstLp 2 hB (measure_ne_top lam B) (1 : ℝ)))
        =ᵐ[lam] fun x => (bindDensity T lam (B.indicator 1) x).toReal := by
      refine (coeFn_densityActionCLM T lam 2 hinv _ _).trans ?_
      rw [densityAction_congr T lam indicatorConstLp_coeFn]
      exact densityAction_indicator T lam
    rw [setIntegral_congr_ae₀ hA.nullMeasurableSet (hae.mono fun x hx _ => hx),
      integral_toReal (measurable_bindDensity T lam _).aemeasurable, 
      setLIntegral_bindDensity_indicator T lam hinv hA hB]
    refine ae_lt_top (measurable_bindDensity T lam _) ?_
    refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral A _)
    rw [lintegral_bindDensity T hinv]; exact hfinB
  -- right side
  have hR : ∫ x in B, (funActLp T lam 2 hinv
        (indicatorConstLp 2 hA (measure_ne_top lam A) (1 : ℝ))) x ∂lam
      = (∫⁻ x in B, T x A ∂lam).toReal := by
    have hae : ⇑(funActLp T lam 2 hinv (indicatorConstLp 2 hA (measure_ne_top lam A) (1 : ℝ)))
        =ᵐ[lam] fun x => (T x A).toReal := by
      refine (coeFn_funActLp T lam 2 hinv _).trans ?_
      refine ((isInvariant_of_bind T hinv).funAct_congr (indicatorConstLp_coeFn (p := 2)
        (hs := hA) (hμs := measure_ne_top lam A) (c := (1 : ℝ)))).mono fun x hx => ?_
      rw [hx, General.funAct]
      exact integral_indicator_one hA
    rw [setIntegral_congr_ae₀ hB.nullMeasurableSet (hae.mono fun x hx _ => hx),
      integral_toReal (T.measurable_coe hA).aemeasurable
        (Eventually.of_forall fun x => measure_lt_top (T x) A)]
  rw [hL, hR]

/-- The adjointness against a fixed indicator `𝟏_A`, for every `u ∈ L²(λ)`: induction over
`L²(λ)` from indicators, the two sides being continuous and additive in `u`. -/
theorem inner_densityActionL2_indicator_right (hinv : lam.bind ⇑T = lam) {A : Set α}
    (hA : MeasurableSet A) (u : Lp ℝ 2 lam) :
    ⟪densityActionL2 T lam hinv u, indicatorConstLp 2 hA (measure_ne_top lam A) (1 : ℝ)⟫_ℝ
      = ⟪u, funActLp T lam 2 hinv (indicatorConstLp 2 hA (measure_ne_top lam A) (1 : ℝ))⟫_ℝ := by
  induction u using Lp.induction (p := 2) (hp_ne_top := ENNReal.ofNat_ne_top) with
  | indicatorConst c hB hμB =>
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul hB, map_smul,
        real_inner_smul_left, real_inner_smul_left]
      congr 1
      exact inner_densityActionL2_indicator T lam hinv hA hB
  | add _ _ _ hf hg =>
      rw [map_add, inner_add_left, inner_add_left, hf, hg]
  | isClosed =>
      exact isClosed_eq ((densityActionL2 T lam hinv).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)

/-- **`lem:doubling_operator`(1), the adjointness**: `⟪Pu, v⟫_λ = ⟪u, P⋆v⟫_λ` for all
`u, v ∈ L²(λ)`. -/
theorem inner_densityActionL2_left (hinv : lam.bind ⇑T = lam) (u v : Lp ℝ 2 lam) :
    ⟪densityActionL2 T lam hinv u, v⟫_ℝ = ⟪u, funActLp T lam 2 hinv v⟫_ℝ := by
  induction v using Lp.induction (p := 2) (hp_ne_top := ENNReal.ofNat_ne_top) with
  | indicatorConst c hA hμA =>
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul hA, map_smul,
        real_inner_smul_right, real_inner_smul_right]
      congr 1
      exact inner_densityActionL2_indicator_right T lam hinv hA u
  | add _ _ _ hf hg =>
      rw [map_add, inner_add_right, inner_add_right, hf, hg]
  | isClosed =>
      exact isClosed_eq (continuous_const.inner continuous_id)
        (continuous_const.inner (funActLp T lam 2 hinv).continuous)

/-- `P = (P⋆)*`. -/
theorem adjoint_funActL2 (hinv : lam.bind ⇑T = lam) :
    ContinuousLinearMap.adjoint (funActLp T lam 2 hinv) = densityActionL2 T lam hinv :=
  ((ContinuousLinearMap.eq_adjoint_iff (densityActionL2 T lam hinv)
    (funActLp T lam 2 hinv)).mpr (inner_densityActionL2_left T lam hinv)).symm

/-- **`lem:doubling_operator`(1), `P⋆ = P*`**: the function action is the `L²(λ)`-adjoint of
the density action. -/
theorem adjoint_densityActionL2 (hinv : lam.bind ⇑T = lam) :
    ContinuousLinearMap.adjoint (densityActionL2 T lam hinv) = funActLp T lam 2 hinv := by
  rw [← adjoint_funActL2 T lam hinv, ContinuousLinearMap.adjoint_adjoint]

end Adjoint

/-! ## `Π`, and `‖P⋆ⁿ − Π‖ = β̂ₙ` -/

section MeanProj

variable (T : Kernel α α) [IsMarkovKernel T] (lam : Measure α) [IsFiniteMeasure lam]

/-- **`Π` is self-adjoint on `L²(λ)`**: `⟪Πu, v⟫ = (∫u)(∫v)/λ(𝒮) = ⟪u, Πv⟫`. -/
theorem adjoint_meanProj : ContinuousLinearMap.adjoint (meanProj lam 2) = meanProj lam 2 := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (meanProj lam 2) (meanProj lam 2)).mpr
    fun u v => ?_).symm
  rw [meanProj_apply, meanProj_apply, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm, inner_constOne_two, inner_constOne_two]
  ring

/-- `Π P = Π`: the density action preserves `λ`-integrals. -/
theorem meanProj_mul_densityActionL2 (hinv : lam.bind ⇑T = lam) :
    meanProj lam 2 * densityActionL2 T lam hinv = meanProj lam 2 :=
  meanProj_comp_left (integral_densityActionCLM T lam 2 hinv _)

/-- `P Π = Π`: invariance, `P𝟏 = 𝟏`. -/
theorem densityActionL2_mul_meanProj (hinv : lam.bind ⇑T = lam) :
    densityActionL2 T lam hinv * meanProj lam 2 = meanProj lam 2 :=
  comp_meanProj (densityActionCLM_constOne T lam 2 hinv _)

/-- `P⋆ Π = Π`: a Markov kernel fixes the constants. -/
theorem funActL2_mul_meanProj (hinv : lam.bind ⇑T = lam) :
    funActLp T lam 2 hinv * meanProj lam 2 = meanProj lam 2 :=
  comp_meanProj (funActLp_constOne T lam 2 hinv)

/-- `Π P⋆ = Π`, the adjoint of `P Π = Π`. -/
theorem meanProj_mul_funActL2 (hinv : lam.bind ⇑T = lam) :
    meanProj lam 2 * funActLp T lam 2 hinv = meanProj lam 2 := by
  have h := congrArg ContinuousLinearMap.adjoint (densityActionL2_mul_meanProj T lam hinv)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    adjoint_meanProj, adjoint_densityActionL2] at h
  exact h

/-- `Π² = Π`, for `λ ≠ 0`. -/
theorem meanProj_mul_self [NeZero lam] : meanProj lam 2 * meanProj lam 2 = meanProj lam 2 :=
  meanProj_idem (Measure.measure_univ_ne_zero.2 (NeZero.ne lam))

/-- **`β̂ₙ := ‖Pⁿ − Π‖_{L²(λ)}`**, on the density action as the paper defines it. -/
noncomputable def betaHat (hinv : lam.bind ⇑T = lam) (n : ℕ) : ℝ :=
  ‖densityActionL2 T lam hinv ^ n - meanProj lam 2‖

/-- `P⋆ⁿ − Π = (Pⁿ − Π)*`. -/
theorem adjoint_densityActionL2_pow_sub (hinv : lam.bind ⇑T = lam) (n : ℕ) :
    ContinuousLinearMap.adjoint (densityActionL2 T lam hinv ^ n - meanProj lam 2)
      = funActLp T lam 2 hinv ^ n - meanProj lam 2 := by
  rw [map_sub, adjoint_meanProj, ← ContinuousLinearMap.star_eq_adjoint, star_pow,
    ContinuousLinearMap.star_eq_adjoint, adjoint_densityActionL2]

/-- **`lem:doubling_operator`(1), last clause**: `‖P⋆ⁿ − Π‖_{L²(λ)} = β̂ₙ` for every `n ≥ 0`. -/
theorem norm_funActL2_pow_sub (hinv : lam.bind ⇑T = lam) (n : ℕ) :
    ‖funActLp T lam 2 hinv ^ n - meanProj lam 2‖ = betaHat T lam hinv n := by
  rw [betaHat, ← adjoint_densityActionL2_pow_sub T lam hinv n]
  exact ContinuousLinearMap.adjoint.norm_map _

end MeanProj

/-! ## Item (3): a norm-convergent series inverts `Id − P⋆ + Π` -/

section Abstract

/-- An upper bound valid at every real bound of the partial sums is an upper bound by the
extended-real sum: the paper's "`B̂ ≤ Σβ̂ₙ`, vacuous when the right side is `+∞`". -/
theorem ofReal_le_tsum_of_forall_bdd {x : ℝ} {β : ℕ → ℝ} (hβ : ∀ n, 0 ≤ β n)
    (h : ∀ B : ℝ, (∀ N : ℕ, ∑ n ∈ Finset.range N, β n ≤ B) → x ≤ B) :
    ENNReal.ofReal x ≤ ∑' n, ENNReal.ofReal (β n) := by
  set s := ∑' n, ENNReal.ofReal (β n)
  rcases eq_or_ne s ⊤ with hs | hs
  · rw [hs]; exact le_top
  have hB : ∀ N : ℕ, ∑ n ∈ Finset.range N, β n ≤ s.toReal := by
    intro N
    have h1 : ∑ n ∈ Finset.range N, β n
        = (∑ n ∈ Finset.range N, ENNReal.ofReal (β n)).toReal := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => hβ n,
        ENNReal.toReal_ofReal (Finset.sum_nonneg fun n _ => hβ n)]
    rw [h1]
    exact ENNReal.toReal_mono hs (ENNReal.sum_le_tsum _)
  calc ENNReal.ofReal x ≤ ENNReal.ofReal s.toReal := ENNReal.ofReal_le_ofReal (h _ hB)
    _ = s := ENNReal.ofReal_toReal hs

end Abstract

section Item3

variable (T : Kernel α α) [IsMarkovKernel T] (lam : Measure α) [IsFiniteMeasure lam] [NeZero lam]

/-- **`lem:doubling_operator`(3), for a Markov kernel on a measurable space.** If
`U := Σ_{n≥0}(P⋆ⁿ − Π)` converges in operator norm on `L²(λ)`, then `Id − P⋆ + Π` is invertible
with inverse `Π + U`, the diffusion operator `S := (Id − P⋆ + Π)^{-1} − Π` equals `U` and
satisfies `eq:doubling_resolvent`, and `B̂ := ‖S‖ ≤ Σ_{n≥0} β̂ₙ` — stated at every real bound of
the partial sums (vacuous exactly when the sum is `+∞`) and, equivalently, in `ℝ≥0∞`. -/
theorem doubling_operator_item3 (hinv : lam.bind ⇑T = lam) {U : Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 lam}
    (hconv : Tendsto (partialSum (funActLp T lam 2 hinv) (meanProj lam 2)) atTop (𝓝 U)) :
    IsUnit (1 - funActLp T lam 2 hinv + meanProj lam 2)
    ∧ Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) = meanProj lam 2 + U
    ∧ Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2 = U
    ∧ ((1 - funActLp T lam 2 hinv) * U = 1 - meanProj lam 2
      ∧ U * (1 - funActLp T lam 2 hinv) = 1 - meanProj lam 2
      ∧ meanProj lam 2 * U = 0 ∧ U * meanProj lam 2 = 0)
    ∧ (∀ B : ℝ, (∀ N : ℕ, ∑ n ∈ Finset.range N, betaHat T lam hinv n ≤ B) →
        ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖ ≤ B)
    ∧ ENNReal.ofReal
        ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖
        ≤ ∑' n, ENNReal.ofReal (betaHat T lam hinv n) := by
  have hPi2 := meanProj_mul_self lam
  have hPiP := meanProj_mul_funActL2 T lam hinv
  have hPPi := funActL2_mul_meanProj T lam hinv
  obtain ⟨h1, h2⟩ := resolvent_inverse hPi2 hPiP hPPi hconv
  have hunit : IsUnit (1 - funActLp T lam 2 hinv + meanProj lam 2) := ⟨⟨_, _, h1, h2⟩, rfl⟩
  have hinvEq : Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) = meanProj lam 2 + U := by
    have := Ring.inverse_unit (⟨_, _, h1, h2⟩ : (Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 lam)ˣ)
    exact this
  have hSU : Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2 = U := by
    rw [hinvEq, add_sub_cancel_left]
  have hbd : ∀ B : ℝ, (∀ N : ℕ, ∑ n ∈ Finset.range N, betaHat T lam hinv n ≤ B) →
      ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖ ≤ B := by
    intro B hB
    rw [hSU]
    refine resolvent_norm_le hconv fun N => ?_
    rw [Finset.sum_congr rfl fun n _ => norm_funActL2_pow_sub T lam hinv n]
    exact hB N
  refine ⟨hunit, hinvEq, hSU, resolvent_identities hPi2 hPiP hPPi hconv, hbd,
    ofReal_le_tsum_of_forall_bdd (fun n => norm_nonneg _) hbd⟩

end Item3

/-! ## Item (2): a finite irreducible chain -/

section Finite

/-- **Irreducibility** of a Markov kernel on a (finite) state space: every state reaches every
state along transitions of positive probability, `P(X_n = y | X_0 = x) > 0` for some `n ≥ 0`. -/
def KernelIrreducible (T : Kernel α α) : Prop :=
  ∀ x y : α, Relation.ReflTransGen (fun a b => T a {b} ≠ 0) x y

variable [MeasurableSingletonClass α] (T : Kernel α α) {lam : Measure α}

/-- One step of invariance: `λ{y} ≥ λ{x} T(x, {y})`. -/
theorem measure_singleton_mul_le (hinv : lam.bind ⇑T = lam) (x y : α) :
    lam {x} * T x {y} ≤ lam {y} := by
  calc lam {x} * T x {y} = ∫⁻ z in {x}, T z {y} ∂lam := by
        rw [lintegral_singleton, mul_comm]
    _ ≤ ∫⁻ z, T z {y} ∂lam := setLIntegral_le_lintegral _ _
    _ = lam.bind ⇑T {y} :=
        (Measure.bind_apply (measurableSet_singleton y) T.aemeasurable).symm
    _ = lam {y} := by rw [hinv]

/-- **An invariant measure of an irreducible chain charges every state as soon as it charges one**
(the paper's `λ(y) ≥ λ(x) P(X_n = y | X_0 = x) > 0`). -/
theorem measure_singleton_ne_zero [Finite α] [NeZero lam] (hinv : lam.bind ⇑T = lam)
    (hirr : KernelIrreducible T) (y : α) : lam {y} ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, lam {x} ≠ 0 := by
    by_contra h
    push Not at h
    have : lam (⋃ x, {x}) = 0 := measure_iUnion_null h
    rw [Set.iUnion_singleton_eq_range, Set.range_id'] at this
    exact NeZero.ne lam (Measure.measure_univ_eq_zero.1 this)
  induction hirr x y with
  | refl => exact hx
  | @tail b c _ hbc ih =>
      intro h0
      have := measure_singleton_mul_le T hinv b c
      rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at this
      rcases this with h | h
      · exact ih h
      · exact hbc h

omit [MeasurableSingletonClass α] in
/-- On a space whose points are all charged, `λ`-a.e. equality is equality. -/
theorem eq_of_ae_eq (hpos : ∀ x, lam {x} ≠ 0) {f g : α → ℝ} (h : f =ᵐ[lam] g) (x : α) :
    f x = g x := by
  by_contra hx
  exact hpos x (measure_mono_null (Set.singleton_subset_iff.2 hx) (ae_iff.1 h))

/-- **The maximum principle**: on a finite irreducible chain a function fixed by `P⋆` is
constant. -/
theorem funAct_fixed_const [Finite α] [IsMarkovKernel T] (hirr : KernelIrreducible T) {f : α → ℝ}
    (hf : ∀ x, General.funAct T f x = f x) (x y : α) : f y = f x := by
  haveI : Nonempty α := ⟨x⟩
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max f
  have hstep : ∀ a b, f a = f x₀ → T a {b} ≠ 0 → f b = f x₀ := by
    intro a b ha hab
    have hint : Integrable (fun z => f x₀ - f z) (T a) := Integrable.of_finite
    have h0 : ∫ z, (f x₀ - f z) ∂(T a) = 0 := by
      rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const, probReal_univ,
        one_smul]
      have := hf a
      rw [General.funAct] at this
      rw [this, ha, sub_self]
    have hae := (integral_eq_zero_iff_of_nonneg (fun z => sub_nonneg.2 (hx₀ z)) hint).1 h0
    have hb : f x₀ - f b = 0 := by
      by_contra hb
      exact hab (measure_mono_null (Set.singleton_subset_iff.2 hb) (ae_iff.1 hae))
    linarith
  have hall : ∀ z, f z = f x₀ := by
    intro z
    induction hirr x₀ z with
    | refl => rfl
    | tail _ hbc ih => exact hstep _ _ ih hbc
  rw [hall x, hall y]

section Lp

variable [IsMarkovKernel T] [IsFiniteMeasure lam]

/-- Evaluation at the states, as a linear map out of `L²(λ)`: linear because every state is
charged, so a.e. identities hold pointwise. -/
noncomputable def evalLp (hpos : ∀ x, lam {x} ≠ 0) : Lp ℝ 2 lam →ₗ[ℝ] (α → ℝ) where
  toFun F := ⇑F
  map_add' F G := funext (eq_of_ae_eq hpos (Lp.coeFn_add F G))
  map_smul' c F := funext (eq_of_ae_eq hpos (Lp.coeFn_smul c F))

omit [MeasurableSingletonClass α] [IsFiniteMeasure lam] in
theorem evalLp_injective (hpos : ∀ x, lam {x} ≠ 0) : Function.Injective (evalLp (lam := lam) hpos) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  refine Lp.ext ?_
  refine (Filter.EventuallyEq.of_eq (hF : (⇑F : α → ℝ) = 0)).trans ?_
  exact (Lp.coeFn_zero ℝ 2 lam).symm

omit [MeasurableSingletonClass α] [IsFiniteMeasure lam] [IsMarkovKernel T] in
/-- **`L²(λ)` is finite-dimensional** on a finite state space all of whose states are charged. -/
theorem finiteDimensional_Lp [Finite α] (hpos : ∀ x, lam {x} ≠ 0) :
    FiniteDimensional ℝ (Lp ℝ 2 lam) :=
  FiniteDimensional.of_injective (evalLp hpos) (evalLp_injective hpos)

/-- **`lem:doubling_operator`(2), `P⋆` fixes only the constants** in `L²(λ)`, on a finite irreducible chain whose invariant
measure charges every state. -/
theorem eq_smul_constOne_of_fixed [Finite α] (hinv : lam.bind ⇑T = lam) (hirr : KernelIrreducible T)
    (hpos : ∀ x, lam {x} ≠ 0) {F : Lp ℝ 2 lam} (hF : funActLp T lam 2 hinv F = F) :
    ∃ c : ℝ, F = c • constOne lam 2 := by
  have hfix : ∀ x, General.funAct T ⇑F x = ⇑F x := by
    intro x
    refine eq_of_ae_eq hpos ?_ x
    exact (coeFn_funActLp T lam 2 hinv F).symm.trans (by rw [hF])
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · refine ⟨0, Lp.ext ?_⟩
    exact Filter.Eventually.of_forall fun x => (hα.false x).elim
  refine ⟨F x₀, Lp.ext ?_⟩
  filter_upwards [Lp.coeFn_smul (F x₀) (constOne lam 2), coeFn_constOne (ν := lam) (p := 2)]
    with x h1 h2
  rw [h1, _root_.Pi.smul_apply, h2, smul_eq_mul, mul_one]
  exact funAct_fixed_const T hirr hfix x₀ x

/-- `hker`: `P⋆F = F` forces `ΠF = F`. -/
theorem meanProj_fixed_of_fixed [Finite α] [NeZero lam] (hinv : lam.bind ⇑T = lam)
    (hirr : KernelIrreducible T) {F : Lp ℝ 2 lam} (hF : funActLp T lam 2 hinv F = F) :
    meanProj lam 2 F = F := by
  obtain ⟨c, rfl⟩ := eq_smul_constOne_of_fixed T hinv hirr
    (measure_singleton_ne_zero T hinv hirr) hF
  rw [map_smul, meanProj_constOne (Measure.measure_univ_ne_zero.2 (NeZero.ne lam))]

end Lp

end Finite

/-! ## Item (2), and the finite case of item (3) -/

section FiniteItems

variable [MeasurableSingletonClass α] [Finite α] (T : Kernel α α) [IsMarkovKernel T]
  (lam : Measure α) [IsProbabilityMeasure lam]

/-- **`lem:doubling_operator`(2), for a Markov kernel on a finite state space.** If the chain is
irreducible and `λ` is an invariant probability, then `λ` charges every state, `P⋆` fixes only the
constant functions of `L²(λ)`, `Id − P⋆ + Π` is invertible, and
`S := (Id − P⋆ + Π)^{-1} − Π` satisfies `eq:doubling_resolvent`. -/
theorem doubling_operator_item2 (hinv : lam.bind ⇑T = lam) (hirr : KernelIrreducible T) :
    (∀ x, lam {x} ≠ 0)
    ∧ (∀ F : Lp ℝ 2 lam, funActLp T lam 2 hinv F = F → ∃ c : ℝ, F = c • constOne lam 2)
    ∧ IsUnit (1 - funActLp T lam 2 hinv + meanProj lam 2)
    ∧ (1 - funActLp T lam 2 hinv)
          * (Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2)
        = 1 - meanProj lam 2
    ∧ (Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2)
          * (1 - funActLp T lam 2 hinv)
        = 1 - meanProj lam 2
    ∧ meanProj lam 2
          * (Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2) = 0
    ∧ (Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2)
          * meanProj lam 2 = 0 := by
  have hpos := measure_singleton_ne_zero T hinv hirr
  haveI := finiteDimensional_Lp (lam := lam) hpos
  have hPi2 := meanProj_mul_self lam
  have hPiP := meanProj_mul_funActL2 T lam hinv
  have hPPi := funActL2_mul_meanProj T lam hinv
  obtain ⟨R, hMR, hRM⟩ := exists_inverse hPi2 hPiP fun F hF => meanProj_fixed_of_fixed T hinv hirr hF
  have hunit : IsUnit (1 - funActLp T lam 2 hinv + meanProj lam 2) := ⟨⟨_, R, hMR, hRM⟩, rfl⟩
  obtain ⟨e1, e2, e3, e4⟩ := resolvent_identities_of_inverse hPi2 hPiP hPPi
    (Ring.mul_inverse_cancel _ hunit) (Ring.inverse_mul_cancel _ hunit)
  exact ⟨hpos, fun F hF => eq_smul_constOne_of_fixed T hinv hirr hpos hF, hunit, e1, e2, e3, e4⟩

/-- **`lem:doubling_operator`(3), "in particular"**: on a finite irreducible chain
`B̂ = ‖(Id − P⋆ + Π)^{-1} − Π‖ ≤ Σ_{n≥0} β̂ₙ`, at every real bound of the partial sums (vacuous
exactly when the sum is `+∞`) and in `ℝ≥0∞`; and when `Σβ̂ₙ < +∞`, `S = U = Σ'(P⋆ⁿ − Π)`. -/
theorem doubling_operator_item3_finite (hinv : lam.bind ⇑T = lam) (hirr : KernelIrreducible T) :
    (∀ B : ℝ, (∀ N : ℕ, ∑ n ∈ Finset.range N, betaHat T lam hinv n ≤ B) →
        ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖ ≤ B)
    ∧ ENNReal.ofReal
        ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖
        ≤ ∑' n, ENNReal.ofReal (betaHat T lam hinv n)
    ∧ (Summable (betaHat T lam hinv) →
        Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2
          = ∑' n : ℕ, (funActLp T lam 2 hinv ^ n - meanProj lam 2)
        ∧ ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖
          ≤ ∑' n, betaHat T lam hinv n) := by
  obtain ⟨-, -, hunit, -⟩ := doubling_operator_item2 T lam hinv hirr
  have hPi2 := meanProj_mul_self lam
  have hPiP := meanProj_mul_funActL2 T lam hinv
  have hPPi := funActL2_mul_meanProj T lam hinv
  have hRM := Ring.inverse_mul_cancel _ hunit
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖funActLp T lam 2 hinv ^ n - meanProj lam 2‖
      = ∑ n ∈ Finset.range N, betaHat T lam hinv n :=
    fun N => Finset.sum_congr rfl fun n _ => norm_funActL2_pow_sub T lam hinv n
  have hbd : ∀ B : ℝ, (∀ N : ℕ, ∑ n ∈ Finset.range N, betaHat T lam hinv n ≤ B) →
      ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖ ≤ B :=
    fun B hB => (resolvent_eq_tsum_of_bdd hPi2 hPiP hPPi hRM
      fun N => (hsum N).trans_le (hB N)).2
  refine ⟨hbd, ofReal_le_tsum_of_forall_bdd (fun n => norm_nonneg _) hbd, fun hs => ?_⟩
  exact resolvent_eq_tsum_of_bdd hPi2 hPiP hPPi hRM fun N =>
    (hsum N).trans_le (hs.sum_le_tsum _ fun n _ => norm_nonneg _)

end FiniteItems

/-! ## The lemma -/

section Lemma

variable (T : Kernel α α) [IsMarkovKernel T] (lam : Measure α) [IsProbabilityMeasure lam]

/-- **`lem:doubling_operator`(1), for a Markov kernel on a measurable space.** `P⋆` is the
function action `v ↦ ∫ v dT(x)` on every `L^p(λ)`, a contraction there for every `p ∈ [1, +∞]`;
on `L²(λ)` it is the adjoint of the density action `P`; and `‖P⋆ⁿ − Π‖_{L²(λ)} = β̂ₙ` for every
`n ≥ 0`. -/
theorem doubling_operator_item1 (hinv : lam.bind ⇑T = lam) :
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], (∀ F : Lp ℝ p lam,
        ⇑(funActLp T lam p hinv F) =ᵐ[lam] General.funAct T ⇑F)
      ∧ ‖funActLp T lam p hinv‖ ≤ 1)
    ∧ ContinuousLinearMap.adjoint (densityActionL2 T lam hinv) = funActLp T lam 2 hinv
    ∧ ContinuousLinearMap.adjoint (funActLp T lam 2 hinv) = densityActionL2 T lam hinv
    ∧ ∀ n : ℕ, ‖funActLp T lam 2 hinv ^ n - meanProj lam 2‖ = betaHat T lam hinv n :=
  ⟨fun p _ => ⟨coeFn_funActLp T lam p hinv, norm_funActLp_le T lam p hinv⟩,
    adjoint_densityActionL2 T lam hinv, adjoint_funActL2 T lam hinv,
    norm_funActL2_pow_sub T lam hinv⟩

/-- **`lem:doubling_operator`, whole**, for a Markov kernel `T` on a measurable space with an
invariant probability `λ`: items (1) and (3) on the measurable space itself, and item (2) with the
"in particular" of item (3) under the lemma's "if moreover the chain is finite and irreducible",
rendered as a finite state space with measurable points and `KernelIrreducible T`. -/
theorem lem_doubling_operator (hinv : lam.bind ⇑T = lam) :
    -- (1)
    ((∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], (∀ F : Lp ℝ p lam,
        ⇑(funActLp T lam p hinv F) =ᵐ[lam] General.funAct T ⇑F)
      ∧ ‖funActLp T lam p hinv‖ ≤ 1)
    ∧ ContinuousLinearMap.adjoint (densityActionL2 T lam hinv) = funActLp T lam 2 hinv
    ∧ ContinuousLinearMap.adjoint (funActLp T lam 2 hinv) = densityActionL2 T lam hinv
    ∧ ∀ n : ℕ, ‖funActLp T lam 2 hinv ^ n - meanProj lam 2‖ = betaHat T lam hinv n)
    -- (2), and the "in particular" of (3)
    ∧ (Finite α → MeasurableSingletonClass α → KernelIrreducible T →
      (∀ F : Lp ℝ 2 lam, funActLp T lam 2 hinv F = F → ∃ c : ℝ, F = c • constOne lam 2)
      ∧ IsUnit (1 - funActLp T lam 2 hinv + meanProj lam 2)
      ∧ (1 - funActLp T lam 2 hinv)
            * (Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2)
          = 1 - meanProj lam 2
      ∧ (Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2)
            * (1 - funActLp T lam 2 hinv)
          = 1 - meanProj lam 2
      ∧ meanProj lam 2
            * (Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2) = 0
      ∧ (Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2)
            * meanProj lam 2 = 0
      ∧ ENNReal.ofReal
          ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖
          ≤ ∑' n, ENNReal.ofReal (betaHat T lam hinv n))
    -- (3)
    ∧ ∀ U : Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 lam,
      Tendsto (partialSum (funActLp T lam 2 hinv) (meanProj lam 2)) atTop (𝓝 U) →
      IsUnit (1 - funActLp T lam 2 hinv + meanProj lam 2)
      ∧ Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) = meanProj lam 2 + U
      ∧ Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2 = U
      ∧ ((1 - funActLp T lam 2 hinv) * U = 1 - meanProj lam 2
        ∧ U * (1 - funActLp T lam 2 hinv) = 1 - meanProj lam 2
        ∧ meanProj lam 2 * U = 0 ∧ U * meanProj lam 2 = 0)
      ∧ ENNReal.ofReal
          ‖Ring.inverse (1 - funActLp T lam 2 hinv + meanProj lam 2) - meanProj lam 2‖
          ≤ ∑' n, ENNReal.ofReal (betaHat T lam hinv n) := by
  refine ⟨doubling_operator_item1 T lam hinv, fun hfin hms hirr => ?_, fun U hconv => ?_⟩
  · obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := doubling_operator_item2 T lam hinv hirr
    exact ⟨h1, h2, h3, h4, h5, h6, (doubling_operator_item3_finite T lam hinv hirr).2.1⟩
  · obtain ⟨h1, h2, h3, h4, -, h6⟩ := doubling_operator_item3 T lam hinv hconv
    exact ⟨h1, h2, h3, h4, h6⟩

end Lemma

/-! ## Inhabitation -/

/-- **`lem:doubling_operator`, the hypotheses are inhabited, non-vacuously** (kb `0025`, `0027`): the paper's two-state
chain `T(i → j) = 1/2`, `λ` uniform on `Bool`, is a finite irreducible chain with an invariant
probability; its mixing coefficients are summable, the series `Σ(P⋆ⁿ − Π)` converges in operator
norm (so item (3)'s hypothesis holds), and item (2) applies. -/
theorem doubling_operator_witness :
    KernelIrreducible (Kernel.const Bool boolUniform)
    ∧ Summable (betaHat (Kernel.const Bool boolUniform) boolUniform Family.bind_const_kernel)
    ∧ Tendsto (partialSum (funActLp (Kernel.const Bool boolUniform) boolUniform 2
          Family.bind_const_kernel) (meanProj boolUniform 2)) atTop
        (𝓝 (∑' n : ℕ, (funActLp (Kernel.const Bool boolUniform) boolUniform 2
          Family.bind_const_kernel ^ n - meanProj boolUniform 2)))
    ∧ IsUnit (1 - funActLp (Kernel.const Bool boolUniform) boolUniform 2
          Family.bind_const_kernel + meanProj boolUniform 2) := by
  have hirr : KernelIrreducible (Kernel.const Bool boolUniform) := fun a b =>
    Relation.ReflTransGen.single (by
      rw [Kernel.const_apply]; exact (boolUniform_singleton_pos b).ne')
  have hs : Summable (betaHat (Kernel.const Bool boolUniform) boolUniform
      Family.bind_const_kernel) := Family.summable_const_kernel
  have hs' : Summable fun n : ℕ => ‖funActLp (Kernel.const Bool boolUniform) boolUniform 2
      Family.bind_const_kernel ^ n - meanProj boolUniform 2‖ := by
    simp only [norm_funActL2_pow_sub]; exact hs
  exact ⟨hirr, hs, (Summable.of_norm hs').hasSum.tendsto_sum_nat,
    (doubling_operator_item2 _ _ Family.bind_const_kernel hirr).2.2.1⟩

end GFNBounds.Doubling.General
