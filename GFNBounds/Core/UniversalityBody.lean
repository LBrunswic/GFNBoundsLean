import GFNBounds.Core.UniversalityKernelBound

/-!
# `L²` universality for an EGF policy, through the change-of-variables bound

**`theo:universality_L2_body`** — statement `proofs.tex:119–124`, proof `proofs.tex:126–144`
(draft commit `3194054`; line citations drift, `kb/entries/0036`).

> Under the same hypotheses as in Theorem `theo:universality_L2_full`, if in addition `𝒮` is a
> differential manifold, if `ν_B` is finite and comes from a differential volume form and if
> `π⋆` is the policy of an EGF then
>
>   `inf_{f_out⋆ ∈ L²(ν_B)} [‖δf_init‖_{L²(ν_B)} + ‖δf_term‖_{L²(ν_B)}] = 0`.

The proof (`proofs.tex:126–144`) continues Step 2 of `theo:universality_L2_full`, with `m` the
mixture size, `α^i ≤ 1` the mixture weights, `Φ_i` the diffeomorphisms and `ψ := (Sθ − η)⁺`:

> `½ (‖δF_init‖ + ‖δF_term‖) ≤ ‖(ψ ν_B) π⋆‖ + ‖ψ‖
>   ≤ ∑ᵢ ‖α^i‖_∞ ‖Φ_i#(ψ ν_B)‖ + ‖ψ‖ ≤ (1 + ∑ᵢ ‖|JΦ_i⁻¹|^{1/2}‖_∞) ‖ψ‖`
>
> Where we used the manifold `L^p` bound for change of variable one may find in Stern 2010
> Theorem 1. The constant in the right-hand side only depends on `π⋆`, also we have
> `‖ψ‖ → 0` as `η → +∞`, we may thus conclude that `‖δF_init‖ + ‖δF_term‖ → 0`.

Author's ruling (vii), 2026-09-14: the row closes through `theo:universality_L2_full` at
`p = 2`, the Stern 2010 bound entering as a disclosed named hypothesis.

## What is proved

| | |
|---|---|
| `IsEGFPolicy` | "`π⋆` is the policy of an EGF": `π⋆(x) = ∑ᵢ wᵢ(x) δ_{Φᵢ(x)}`, measurable maps, measurable weights `≥ 0` summing to `1` |
| `egfKernel`, `isEGFPolicy_egfKernel`, `IsEGFPolicy.isMarkovKernel` | such a kernel exists for every such data, and is Markov |
| `IsEGFPolicy.bind_withDensity` | the push of `f ν` is `∑ᵢ Φᵢ#((wᵢ f) ν)` |
| `SternBound` | **the named hypothesis** (Stern 2010, Thm 3 / Cor 4 at `p = q = 2` on densities; the paper cites Thm 1, which is the function bound): `Ψ#ν ≪ ν` and `‖d(Ψ#(g ν))/dν‖_{L²(ν)} ≤ c ‖g‖_{L²(ν)}` |
| `sternBound_of_rnDeriv_le` | **the named hypothesis, proved** on any finite measure space from a bounded Jacobian: `d(Ψ#ν)/dν ≤ c²` a.e. gives `SternBound ν Ψ c` |
| `IsEGFPolicy.eLpNorm_bindDensity_le`, `IsEGFPolicy.norm_densityActionCLM_le` | the second and third displays: `‖(ψ ν) π⋆‖ ≤ (∑ᵢ cᵢ) ‖ψ‖` for `ψ ≥ 0` |
| `universality_L2_body_display` | the whole display, at `f_out^η` and `ψ_η` of `theo:universality_L2_full`, every `η` |
| `tendsto_residuals_L2_body` | the last display: `‖δf_init‖ + ‖δf_term‖ → 0` |
| `weaklyUniversalAt_L2_body` | the conclusion in the library's `ε`-form |
| **`universality_L2_body`** | **the conclusion as printed**: the infimum over non-negative `f_out ∈ L²(ν)` is `0` |
| `iInf_residuals_eq_zero` | the `ε`-form gives the printed infimum |
| `IsEGFPolicy.isBoundedDensityAction`, `universality_L2_body_of_stern` | the finite-operator-norm hypothesis is implied by the others; the theorem without it |
| `universality_L2_body_of_full` | **finding**: the printed conclusion needs none of the added hypotheses |
| `IsEGFPolicy.one_le_sum_stern` | **finding**: the Stern route's constant `1 + ∑ᵢ cᵢ` is at least `2` |
| `coinMeasure`, `coinKernel`, `sternBound_coinMaps`, `summable_of_resampling`, `universality_L2_body_coin` | **inhabitation** of the whole bundle, and the theorem applied there |

## SCOPE (disclosed)

**No manifold, no volume form.** `𝒮` is any measurable space and `ν_B` any finite measure; the
differential structure is not modelled. It enters the paper's proof at exactly one place, the
change of variables, and enters here through `SternBound`. Everything else in the proof is
measure theory and is certified.

**The Stern bound is a named hypothesis, and is also proved in measure form.** `SternBound ν Ψ c`
states the inequality the proof takes from Stern 2010 — Theorem 3 / Corollary 4 at `p = q = 2`, the
density form `‖φ_*(uμ)‖₂ ≤ ‖J_φ^{−1/2}‖_∞‖uμ‖₂`, whose constant is the paper's; the paper cites
Theorem 1, which is the function bound with a different constant — with a finite constant
`c : ℝ≥0`, which is Corollary 4's own bounded-reciprocal-Jacobian hypothesis. `sternBound_of_rnDeriv_le` proves it on any finite measure space from
`Ψ` measurable, `Ψ#ν ≪ ν` and `d(Ψ#ν)/dν ≤ c²` a.e. (Cauchy–Schwarz against a truncation of the
push density). **What is not formalized** is the manifold fact that links the two: for a
diffeomorphism `Φ` of a manifold with volume form `ν`, `d(Φ#ν)/dν = |JΦ⁻¹|`, so that the paper's
constant `‖|JΦᵢ⁻¹|^{1/2}‖_∞` is a `c` with `d(Φᵢ#ν)/dν ≤ c²`. That identification is the whole
of the modelling. On the witness the named hypothesis is discharged by `sternBound_of_rnDeriv_le`,
so nothing external is assumed there.

**Diffeomorphisms are measurable maps.** Bijectivity and smoothness of `Φᵢ` are not used; they
enter only through `SternBound` (`Φᵢ#ν ≪ ν` and the bound). The field `map_ac` is not consumed by
the display — `bindDensity` is a Radon–Nikodym derivative and the display holds for it
regardless — but without it `SternBound` would be satisfiable by a singular map (a constant map on
an atomless `ν`, with `c = 0`), and it would no longer be the change-of-variables inequality.

**The constant is finite.** The paper's `‖|JΦᵢ⁻¹|^{1/2}‖_∞` may be `+∞` on a non-compact manifold
of finite volume, and the printed proof is then empty; here `cᵢ : ℝ≥0`. The *statement* does not
need it: `universality_L2_body_of_full` certifies the printed conclusion with no Stern constant at
all.

**`p = 2`.** The paper says "the same hypotheses as in Theorem `theo:universality_L2_full`", whose
exponent is a free `p`. Readings at `p ∈ (2,∞]` are meaningful
(on a finite measure `L^p ⊂ L²`, and the printed proof goes through) and are **not stated here**;
readings at `p < 2` can fail (a pair with `θ ∉ L²` forces an infimum `+∞` when `P⋆` is bounded on
`L²`). Ruling (vii) selects `p = 2`. The statement does not say it.

**The pair.** The statement does not name `F_init`, `F_term`; they are those of the "more precisely"
paragraph of `theo:universality_L2_full`. As in `Core/UniversalityKernelBound.lean`: two elements
of `L²(ν)` of equal integral, non-negativity not used.

**Ergodicity** is `hinv : ν.bind κ = ν` plus summable mixing against the mean projection, exactly
as in `Core/Kernel.lean`; the uniqueness half is absorbed by the summability.

**The infimum** ranges over non-negative `f_out ∈ L²(ν)` — the family of `theo:universality_L2_full`,
whose outflows are `ℝ₊`-valued (`proofs.tex:16`). The printed `inf_{f_out⋆ ∈ L²(ν_B)}` over signed
outflows is then `0` as well, the residual sum being non-negative.

**The middle display is taken with the weight inside the push.** The paper bounds
`‖Φᵢ#(αⁱψ ν)‖ ≤ ‖αⁱ‖_∞ ‖Φᵢ#(ψ ν)‖`; here the Stern bound is applied to `wᵢψ` and then
`‖wᵢψ‖ ≤ ‖ψ‖`. The two routes give the same final constant `1 + ∑ᵢ cᵢ`; the paper's middle term is
not stated.

**Redundancies in the bundle** (`kb/entries/0033`): `[IsMarkovKernel κ]` follows from
`IsEGFPolicy` (`IsEGFPolicy.isMarkovKernel`) and is carried because `densityActionCLM` needs the
instance; `SternBound.measurable` repeats `IsEGFPolicy.measurable_map`; and `hb`, the finite
operator norm of `theo:universality_L2_full`, follows from `IsEGFPolicy` and `SternBound`
(`IsEGFPolicy.isBoundedDensityAction`, constant `∑ᵢ cᵢ`) — carried in `universality_L2_body`
because the paper carries it, dropped in `universality_L2_body_of_stern`.

## Findings on the paper

1. **The added hypotheses buy nothing for the statement.** Its conclusion is weak
   `L²`-universality, which `theo:universality_L2_full` at `p = 2` already gives
   (`universality_L2_body_of_full`, with no manifold, no EGF, no Stern bound). The proof's only
   addition is the constant `1 + ∑ᵢ ‖|JΦᵢ⁻¹|^{1/2}‖_∞`, which the statement does not carry.
2. **The constant is not an improvement.** Under the invariance the theorem assumes, `P⋆ 𝟏 = 𝟏`
   forces `∑ᵢ cᵢ ≥ 1` (`IsEGFPolicy.one_le_sum_stern`), so `1 + ∑ᵢ cᵢ ≥ 2`; while for any
   `ν`-invariant Markov kernel `‖P⋆‖_{L²(ν)} ≤ 1` (Jensen and invariance — the paper's own
   `lem:adjoint`(3), `proofs.tex:417`; in this library `Core/Adjoint.lean` has it on finite types only), so the
   operator-norm constant `1 + ‖P⋆‖` of `theo:universality_L2_full` is at most `2`.
3. "The `L²` strengthening" (`proofs.tex:4`, `:117`) is a restriction: same conclusion at
   `p = 2`, more hypotheses. The exponent `p = 2` is not stated, and the "control of the two
   residuals separately" (`:117`) is a control of their sum.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` a measured Polish space, `ν_B` finite | ⚠ weakened: `MeasurableSpace α`, `[IsFiniteMeasure ν]`; Polish not consumed |
| `𝒮` a differential manifold, `ν_B` from a volume form | ✗ not modelled — enters only through `SternBound`; see SCOPE |
| `π⋆` a Markov kernel | ✓ `[IsMarkovKernel κ]` (redundant with `IsEGFPolicy`) |
| finite `L²(ν_B) → L²(ν_B)` operator norm | ✓ `hb : IsBoundedDensityAction κ ν 2 C`; derived in `universality_L2_body_of_stern` |
| `π⋆` ergodic (`ν_B π⋆ = ν_B`, uniqueness) | ⚠ `hinv`; uniqueness absorbed by `hsum`, as in `Core/Kernel.lean` |
| summable `L²`-mixing | ✓ `hsum`, against `meanProj ν 2` |
| exponent of `theo:universality_L2_full` | ⚠ read at `p = 2` (ruling (vii)); not stated in the paper |
| `F_init, F_term` with densities in `L²(ν_B)` | ⚠ weakened: `f_init f_term : Lp ℝ 2 ν`, equal integrals `hmass`, sign not used |
| `π⋆` the policy of an EGF: `m` maps `Φᵢ`, weights `αⁱ ≤ 1` | ✓ `IsEGFPolicy κ Φ w`, `Φ : Fin m → α → α`, `wᵢ ≥ 0`, `∑ᵢ wᵢ = 1` (hence `wᵢ ≤ 1`, `IsEGFPolicy.weight_le_one`) |
| `Φᵢ` diffeomorphisms | ⚠ weakened to measurable maps; diffeomorphism enters through `SternBound` |
| the group generated by the `Φᵢ` topologically ergodic (source definition of an EGF, ICML camera-ready `main.tex:216–222`) | ⚠ **dropped** (the Lean is more general); ergodicity of `π⋆` enters through `hinv`, `hsum` |
| Stern 2010 (cited as Thm 1; the density bound is Thm 3 / Cor 4 at `p = q = 2`) with constant `‖|JΦᵢ⁻¹|^{1/2}‖_∞` | ⚠ **named hypothesis** `SternBound ν (Φ i) (c i)`, `cᵢ : ℝ≥0` finite; proved from `d(Φᵢ#ν)/dν ≤ cᵢ²` by `sternBound_of_rnDeriv_le` |
| conclusion: `inf_{f_out} (‖δf_init‖ + ‖δf_term‖) = 0` | ✓ `universality_L2_body` (infimum over `f_out ≥ 0`), and `universality_L2_body_of_full` without the EGF hypotheses |
| proof, display 1: `½ (‖δF_init‖ + ‖δF_term‖) ≤ ‖(ψν)π⋆‖ + ‖ψ‖` | ✓ `universality_L2_body_display`, first conjunct |
| proof, display 2: `≤ ∑ᵢ ‖αⁱ‖_∞ ‖Φᵢ#(ψν)‖ + ‖ψ‖` | ⚠ not stated; replaced by `∑ᵢ ‖Φᵢ#(wᵢψ ν)‖`, see SCOPE |
| proof, display 3: `≤ (1 + ∑ᵢ cᵢ) ‖ψ‖` | ✓ second conjunct |
| proof: `‖δF_init‖ + ‖δF_term‖ → 0` | ✓ `tendsto_residuals_L2_body` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core.EGF

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {α : Type*} [MeasurableSpace α]

/-- **"`π⋆` is the policy of an EGF"** (`proofs.tex:120`, `:127`): a finite mixture of pushforwards
by measurable maps `Φᵢ`, with measurable state-dependent weights `wᵢ ≥ 0` summing to `1`,
`π⋆(x) = ∑ᵢ wᵢ(x) δ_{Φᵢ(x)}`. -/
structure IsEGFPolicy (κ : Kernel α α) {m : ℕ} (Φ : Fin m → α → α) (w : Fin m → α → ℝ) :
    Prop where
  measurable_map : ∀ i, Measurable (Φ i)
  measurable_weight : ∀ i, Measurable (w i)
  weight_nonneg : ∀ i x, 0 ≤ w i x
  weight_sum : ∀ x, ∑ i, w i x = 1
  apply_eq : ∀ x, κ x = ∑ i, ENNReal.ofReal (w i x) • Measure.dirac (Φ i x)

/-- The kernel `x ↦ ∑ᵢ wᵢ(x) δ_{Φᵢ(x)}`, for measurable maps and weights. -/
noncomputable def egfKernel {m : ℕ} (Φ : Fin m → α → α) (w : Fin m → α → ℝ)
    (hΦ : ∀ i, Measurable (Φ i)) (hw : ∀ i, Measurable (w i)) : Kernel α α where
  toFun x := ∑ i, ENNReal.ofReal (w i x) • Measure.dirac (Φ i x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hs, smul_eq_mul]
    exact Finset.measurable_sum _ fun i _ =>
      (ENNReal.measurable_ofReal.comp (hw i)).mul
        ((measurable_const.indicator hs).comp (hΦ i))


/-- Every admissible choice of maps and weights is the policy of an EGF. -/
theorem isEGFPolicy_egfKernel {m : ℕ} (Φ : Fin m → α → α) (w : Fin m → α → ℝ)
    (hΦ : ∀ i, Measurable (Φ i)) (hw : ∀ i, Measurable (w i)) (hnn : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x, ∑ i, w i x = 1) : IsEGFPolicy (egfKernel Φ w hΦ hw) Φ w where
  measurable_map := hΦ
  measurable_weight := hw
  weight_nonneg := hnn
  weight_sum := hsum
  apply_eq _ := rfl

variable {κ : Kernel α α} {m : ℕ} {Φ : Fin m → α → α} {w : Fin m → α → ℝ}

/-- An EGF policy is a Markov kernel: its weights sum to `1`. -/
theorem IsEGFPolicy.isMarkovKernel (h : IsEGFPolicy κ Φ w) : IsMarkovKernel κ := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [h.apply_eq x, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h.weight_nonneg i x), h.weight_sum x,
    ENNReal.ofReal_one]

/-- `π⋆(x, s) = ∑ᵢ wᵢ(x) 𝟙_s(Φᵢ x)`. -/
theorem IsEGFPolicy.apply_set (h : IsEGFPolicy κ Φ w) (x : α) {s : Set α}
    (hs : MeasurableSet s) :
    κ x s = ∑ i, ENNReal.ofReal (w i x) * s.indicator 1 (Φ i x) := by
  rw [h.apply_eq x, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]

/-- **The push of a density by an EGF policy is the mixture of pushforwards**:
`(f ν) π⋆ = ∑ᵢ Φᵢ#((wᵢ f) ν)`. -/
theorem IsEGFPolicy.bind_withDensity (h : IsEGFPolicy κ Φ w) (ν : Measure α)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).bind ⇑κ
      = ∑ i, (ν.withDensity fun x => ENNReal.ofReal (w i x) * f x).map (Φ i) := by
  ext s hs
  rw [Measure.bind_apply hs κ.measurable.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hf (κ.measurable_coe hs), Measure.finsetSum_apply]
  simp only [Pi.mul_apply, h.apply_set _ hs, Finset.mul_sum]
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Measurable fun a => f a * (ENNReal.ofReal (w i a) * s.indicator 1 (Φ i a)) :=
    fun i _ => hf.mul ((ENNReal.measurable_ofReal.comp (h.measurable_weight i)).mul
      ((measurable_const.indicator hs).comp (h.measurable_map i)))
  rw [lintegral_finsetSum _ hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (h.measurable_map i) hs,
    withDensity_apply _ (h.measurable_map i hs), ← lintegral_indicator (h.measurable_map i hs)]
  refine lintegral_congr fun x => ?_
  by_cases hx : Φ i x ∈ s
  · have hx' : x ∈ Φ i ⁻¹' s := hx
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Pi.one_apply, mul_one]
    ring
  · have hx' : x ∉ Φ i ⁻¹' s := hx
    simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]


/-- The mixture weights are at most `1` — the paper's `αⁱ ≤ 1` (`proofs.tex:127`). -/
theorem IsEGFPolicy.weight_le_one (h : IsEGFPolicy κ Φ w) (i : Fin m) (x : α) : w i x ≤ 1 := by
  have hle := Finset.single_le_sum (fun j _ => h.weight_nonneg j x) (Finset.mem_univ i)
  rwa [h.weight_sum x] at hle

/-! ## The change-of-variables bound, as a named hypothesis -/

/-- **The change-of-variables bound of Stern 2010, Theorem 3 / Corollary 4 at `p = q = 2`, on
densities** (the paper cites Theorem 1) — the
named hypothesis of `theo:universality_L2_body` (ruling (vii)). `Ψ` is measurable, pushes `ν` to
an absolutely continuous measure, and pushes an `L²(ν)` density to one of norm at most `c` times
as large: `‖d(Ψ#(g ν))/dν‖_{L²(ν)} ≤ c ‖g‖_{L²(ν)}`. On a manifold with volume form `ν` and a
diffeomorphism `Ψ`, the paper's constant is `c = ‖|JΨ⁻¹|^{1/2}‖_∞`; `sternBound_of_rnDeriv_le`
proves the bound from `d(Ψ#ν)/dν ≤ c²`. -/
structure SternBound (ν : Measure α) (Ψ : α → α) (c : ℝ≥0) : Prop where
  measurable : Measurable Ψ
  map_ac : ν.map Ψ ≪ ν
  bound : ∀ g : α → ℝ≥0∞, Measurable g → eLpNorm g 2 ν ≠ ⊤ →
    eLpNorm (((ν.withDensity g).map Ψ).rnDeriv ν) 2 ν ≤ c * eLpNorm g 2 ν

/-! ## Stern's change-of-variables bound at `p = 2`, from a bounded Jacobian -/

section SternProof

variable {ν : Measure α}

/-- On a finite measure, an `L²` function has finite integral. -/
theorem lintegral_ne_top_of_eLpNorm_two [IsFiniteMeasure ν] {g : α → ℝ≥0∞}
    (hg : AEMeasurable g ν) (h2 : eLpNorm g 2 ν ≠ ⊤) : ∫⁻ x, g x ∂ν ≠ ⊤ := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
    hg.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  simp only [enorm_eq_self] at h
  refine ne_top_of_le_ne_top ?_ h
  exact ENNReal.mul_ne_top h2 (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top ν _))

/-- The `L²` seminorm of a non-negative function, as a Lebesgue integral. -/
theorem eLpNorm_two_eq_rpow (f : α → ℝ≥0∞) :
    eLpNorm f 2 ν = (∫⁻ x, f x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [enorm_eq_self, ENNReal.toReal_ofNat]

/-- The square of the `L²` seminorm of a non-negative function. -/
theorem eLpNorm_two_sq (f : α → ℝ≥0∞) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ x, f x ^ (2 : ℝ) ∂ν := by
  rw [eLpNorm_two_eq_rpow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy–Schwarz for non-negative functions, in `eLpNorm` form. -/
theorem lintegral_mul_le_eLpNorm_two {f g : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    (hg : AEMeasurable g ν) : ∫⁻ x, f x * g x ∂ν ≤ eLpNorm f 2 ν * eLpNorm g 2 ν := by
  rw [eLpNorm_two_eq_rpow, eLpNorm_two_eq_rpow]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf hg

/-- Against a density bounded by `c²`, the `L²` norm grows by at most `c`. -/
theorem eLpNorm_two_withDensity_le {J : α → ℝ≥0∞} (hJ : Measurable J) {c : ℝ≥0}
    (hJc : ∀ᵐ x ∂ν, J x ≤ (c : ℝ≥0∞) ^ 2) {h : α → ℝ≥0∞} (hh : Measurable h) :
    eLpNorm h 2 (ν.withDensity J) ≤ c * eLpNorm h 2 ν := by
  have hI : ∫⁻ x, h x ^ (2 : ℝ) ∂(ν.withDensity J)
      ≤ (c : ℝ≥0∞) ^ 2 * ∫⁻ x, h x ^ (2 : ℝ) ∂ν := by
    rw [lintegral_withDensity_eq_lintegral_mul ν hJ (hh.pow_const _), ← lintegral_const_mul _
      (hh.pow_const _)]
    refine lintegral_mono_ae ?_
    filter_upwards [hJc] with x hx
    simp only [Pi.mul_apply]
    gcongr
  rw [eLpNorm_two_eq_rpow, eLpNorm_two_eq_rpow]
  calc (∫⁻ x, h x ^ (2 : ℝ) ∂(ν.withDensity J)) ^ (1 / 2 : ℝ)
      ≤ ((c : ℝ≥0∞) ^ 2 * ∫⁻ x, h x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by gcongr
    _ = (c : ℝ≥0∞) * (∫⁻ x, h x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

/-- **Stern's change-of-variables bound at `p = 2`, on a finite measure space.** If `Ψ` is
measurable, `ν ∘ Ψ⁻¹ ≪ ν`, and the Jacobian `d(Ψ#ν)/dν` of `Ψ⁻¹` is at most `c²` a.e., then
`‖d(Ψ#(g ν))/dν‖_{L²(ν)} ≤ c ‖g‖_{L²(ν)}`. -/
theorem sternBound_of_rnDeriv_le [IsFiniteMeasure ν] {Ψ : α → α} (hΨ : Measurable Ψ)
    (hac : ν.map Ψ ≪ ν) {c : ℝ≥0} (hJ : ∀ᵐ x ∂ν, (ν.map Ψ).rnDeriv ν x ≤ (c : ℝ≥0∞) ^ 2) :
    SternBound ν Ψ c where
  measurable := hΨ
  map_ac := hac
  bound g hg hg2 := by
    set μ := (ν.withDensity g).map Ψ with hμdef
    set ρ := μ.rnDeriv ν with hρdef
    haveI : IsFiniteMeasure (ν.withDensity g) :=
      isFiniteMeasure_withDensity (lintegral_ne_top_of_eLpNorm_two hg.aemeasurable hg2)
    haveI : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
    have hμac : μ ≪ ν := ((withDensity_absolutelyContinuous ν g).map hΨ).trans hac
    have hρm : Measurable ρ := Measure.measurable_rnDeriv _ _
    have hμ : ν.withDensity ρ = μ := Measure.withDensity_rnDeriv_eq μ ν hμac
    have hνΨ : ν.withDensity ((ν.map Ψ).rnDeriv ν) = ν.map Ψ :=
      Measure.withDensity_rnDeriv_eq _ ν hac
    -- The key estimate for a finite-norm minorant `h ≤ ρ`.
    have key : ∀ h : α → ℝ≥0∞, Measurable h → (∀ x, h x ≤ ρ x) →
        eLpNorm h 2 ν ^ 2 ≤ eLpNorm g 2 ν * ((c : ℝ≥0∞) * eLpNorm h 2 ν) := by
      intro h hh hle
      rw [eLpNorm_two_sq]
      calc ∫⁻ x, h x ^ (2 : ℝ) ∂ν ≤ ∫⁻ x, (ρ * h) x ∂ν := by
            refine lintegral_mono fun x => ?_
            rw [ENNReal.rpow_two, sq, Pi.mul_apply]
            gcongr
            exact hle x
        _ = ∫⁻ x, h x ∂μ := by rw [← lintegral_withDensity_eq_lintegral_mul ν hρm hh, hμ]
        _ = ∫⁻ x, h (Ψ x) ∂(ν.withDensity g) := lintegral_map hh hΨ
        _ = ∫⁻ x, g x * h (Ψ x) ∂ν :=
            lintegral_withDensity_eq_lintegral_mul ν hg (hh.comp hΨ)
        _ ≤ eLpNorm g 2 ν * eLpNorm (h ∘ Ψ) 2 ν :=
            lintegral_mul_le_eLpNorm_two hg.aemeasurable (hh.comp hΨ).aemeasurable
        _ = eLpNorm g 2 ν * eLpNorm h 2 (ν.map Ψ) := by
            rw [eLpNorm_map_measure hh.aestronglyMeasurable hΨ.aemeasurable]
        _ ≤ eLpNorm g 2 ν * ((c : ℝ≥0∞) * eLpNorm h 2 ν) := by
            gcongr
            rw [← hνΨ]
            exact eLpNorm_two_withDensity_le (Measure.measurable_rnDeriv _ _) hJ hh
    -- Truncate `ρ` at level `n`; each truncation has finite norm, so `key` cancels.
    set h : ℕ → α → ℝ≥0∞ := fun n x => min (ρ x) n with hhdef
    have hhm : ∀ n, Measurable (h n) := fun n => hρm.min measurable_const
    have hfin : ∀ n, eLpNorm (h n) 2 ν ≠ ⊤ := by
      intro n
      rw [eLpNorm_two_eq_rpow]
      refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_top_of_le_ne_top ?_
        (lintegral_mono fun x => ENNReal.rpow_le_rpow (min_le_right (ρ x) (n : ℝ≥0∞))
          (by norm_num : (0 : ℝ) ≤ 2)))
      rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.natCast_ne_top n)) (measure_ne_top ν _)
    have hn : ∀ n, eLpNorm (h n) 2 ν ≤ (c : ℝ≥0∞) * eLpNorm g 2 ν := by
      intro n
      have hk := key (h n) (hhm n) fun x => min_le_left _ _
      rcases eq_or_ne (eLpNorm (h n) 2 ν) 0 with h0 | h0
      · rw [h0]
        exact zero_le
      · have hk' : eLpNorm (h n) 2 ν * eLpNorm (h n) 2 ν
            ≤ ((c : ℝ≥0∞) * eLpNorm g 2 ν) * eLpNorm (h n) 2 ν := by
          calc eLpNorm (h n) 2 ν * eLpNorm (h n) 2 ν = eLpNorm (h n) 2 ν ^ 2 := (sq _).symm
            _ ≤ eLpNorm g 2 ν * ((c : ℝ≥0∞) * eLpNorm (h n) 2 ν) := hk
            _ = ((c : ℝ≥0∞) * eLpNorm g 2 ν) * eLpNorm (h n) 2 ν := by ring
        exact (ENNReal.mul_le_mul_iff_left h0 (hfin n)).1 hk'
    -- Monotone convergence.
    have hlim : ∫⁻ x, ρ x ^ (2 : ℝ) ∂ν ≤ ⨆ n, ∫⁻ x, h n x ^ (2 : ℝ) ∂ν := by
      rw [← lintegral_iSup (fun n => (hhm n).pow_const _) fun a b hab x => by
        simp only [hhdef]
        gcongr]
      refine lintegral_mono_ae ?_
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      obtain ⟨n, hnx⟩ := ENNReal.exists_nat_gt hx.ne
      refine le_iSup_of_le n (le_of_eq ?_)
      simp only [hhdef]
      rw [min_eq_left (hnx.le : ρ x ≤ n)]
    have hsq : ∫⁻ x, ρ x ^ (2 : ℝ) ∂ν ≤ ((c : ℝ≥0∞) * eLpNorm g 2 ν) ^ 2 := by
      refine hlim.trans (iSup_le fun n => ?_)
      rw [← eLpNorm_two_sq]
      gcongr
      exact hn n
    rw [eLpNorm_two_eq_rpow]
    calc (∫⁻ x, ρ x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)
        ≤ (((c : ℝ≥0∞) * eLpNorm g 2 ν) ^ 2) ^ (1 / 2 : ℝ) := by gcongr
      _ = (c : ℝ≥0∞) * eLpNorm g 2 ν := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num

end SternProof

/-! ## The density action of an EGF policy is bounded by the Stern constants -/

/-- The Radon–Nikodym derivative of a finite sum of finite measures is the sum of theirs, a.e. -/
theorem rnDeriv_finsetSum {ι : Type*} (s : Finset ι) (μ : ι → Measure α)
    [∀ i, IsFiniteMeasure (μ i)] (ν : Measure α) [SigmaFinite ν] :
    (∑ i ∈ s, μ i).rnDeriv ν =ᵐ[ν] ∑ i ∈ s, (μ i).rnDeriv ν := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Measure.rnDeriv_zero ν
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      filter_upwards [Measure.rnDeriv_add (μ a) (∑ i ∈ s, μ i) ν, ih] with x h1 h2
      rw [h1, Pi.add_apply, Pi.add_apply, h2]

/-- **The Stern route, on non-negative densities** (`proofs.tex:135–136`): for an EGF policy whose
maps satisfy the Stern bound, `‖d((f ν) π⋆)/dν‖_{L²(ν)} ≤ (∑ᵢ cᵢ) ‖f‖_{L²(ν)}`. The triangle
inequality over the mixture, then the Stern bound on each `wᵢ f`, then `wᵢ ≤ 1`. -/
theorem IsEGFPolicy.eLpNorm_bindDensity_le {ν : Measure α} [IsFiniteMeasure ν]
    (h : IsEGFPolicy κ Φ w) {c : Fin m → ℝ≥0} (hS : ∀ i, SternBound ν (Φ i) (c i))
    {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hf2 : eLpNorm f 2 ν ≠ ⊤) :
    eLpNorm (bindDensity κ ν f) 2 ν ≤ (∑ i, (c i : ℝ≥0∞)) * eLpNorm f 2 ν := by
  -- Reduce to a measurable representative: `T` and the norm only see the a.e. class.
  rw [bindDensity_congr κ ν hf.ae_eq_mk, eLpNorm_congr_ae hf.ae_eq_mk]
  rw [eLpNorm_congr_ae hf.ae_eq_mk] at hf2
  set f' := hf.mk f
  have hf' : Measurable f' := hf.measurable_mk
  set g : Fin m → α → ℝ≥0∞ := fun i x => ENNReal.ofReal (w i x) * f' x with hg
  have hgm : ∀ i, Measurable (g i) := fun i =>
    (ENNReal.measurable_ofReal.comp (h.measurable_weight i)).mul hf'
  have hgle : ∀ i, eLpNorm (g i) 2 ν ≤ eLpNorm f' 2 ν := fun i =>
    eLpNorm_mono_enorm fun x => by
      simp only [enorm_eq_self, hg]
      calc ENNReal.ofReal (w i x) * f' x ≤ 1 * f' x := by
            gcongr
            exact ENNReal.ofReal_le_one.2 (h.weight_le_one i x)
        _ = f' x := one_mul _
  have hg2 : ∀ i, eLpNorm (g i) 2 ν ≠ ⊤ := fun i => ne_top_of_le_ne_top hf2 (hgle i)
  haveI : ∀ i, IsFiniteMeasure ((ν.withDensity (g i)).map (Φ i)) := fun i => by
    haveI := isFiniteMeasure_withDensity
      (lintegral_ne_top_of_eLpNorm_two (hgm i).aemeasurable (hg2 i))
    exact Measure.isFiniteMeasure_map _ _
  have hbind : bindDensity κ ν f'
      =ᵐ[ν] ∑ i, ((ν.withDensity (g i)).map (Φ i)).rnDeriv ν := by
    rw [bindDensity, h.bind_withDensity ν hf']
    exact rnDeriv_finsetSum _ _ ν
  rw [eLpNorm_congr_ae hbind]
  calc eLpNorm (∑ i, ((ν.withDensity (g i)).map (Φ i)).rnDeriv ν) 2 ν
      ≤ ∑ i, eLpNorm (((ν.withDensity (g i)).map (Φ i)).rnDeriv ν) 2 ν :=
        eLpNorm_sum_le (fun i _ => (Measure.measurable_rnDeriv _ _).aestronglyMeasurable)
          (by norm_num)
    _ ≤ ∑ i, (c i : ℝ≥0∞) * eLpNorm f' 2 ν := Finset.sum_le_sum fun i _ =>
        ((hS i).bound (g i) (hgm i) (hg2 i)).trans (by gcongr; exact hgle i)
    _ = (∑ i, (c i : ℝ≥0∞)) * eLpNorm f' 2 ν := (Finset.sum_mul _ _ _).symm


/-- On a non-negative `L²` element the signed density action is the non-negative one. -/
theorem densityAction_ae_eq_of_nonneg (κ : Kernel α α) {ν : Measure α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[ν] f) :
    densityAction κ ν f
      =ᵐ[ν] fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal := by
  have hneg : (fun y => ENNReal.ofReal (-f y)) =ᵐ[ν] 0 := by
    filter_upwards [hf] with y hy
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero, Left.neg_nonpos_iff]
    exact hy
  filter_upwards [bindDensity_zero κ ν] with x hx
  simp only [densityAction, bindDensity_congr κ ν hneg, hx, Pi.zero_apply, ENNReal.toReal_zero,
    sub_zero]

/-- **The Stern route on `L²(ν)`**: for a non-negative `ψ ∈ L²(ν)` the density action of an EGF
policy satisfies `‖(ψ ν) π⋆‖_{L²(ν)} ≤ (∑ᵢ cᵢ) ‖ψ‖_{L²(ν)}`. -/
theorem IsEGFPolicy.norm_densityActionCLM_le {ν : Measure α} [IsFiniteMeasure ν]
    [IsMarkovKernel κ] {C : ℝ} (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν 2 C)
    (h : IsEGFPolicy κ Φ w) {c : Fin m → ℝ≥0} (hS : ∀ i, SternBound ν (Φ i) (c i))
    {ψ : Lp ℝ 2 ν} (hψ : 0 ≤ ψ) :
    ‖densityActionCLM κ ν 2 hinv hb ψ‖ ≤ (∑ i, (c i : ℝ)) * ‖ψ‖ := by
  have hψae : 0 ≤ᵐ[ν] ⇑ψ := (Lp.coeFn_nonneg ψ).2 hψ
  have hrep : ⇑(densityActionCLM κ ν 2 hinv hb ψ)
      =ᵐ[ν] fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (ψ y)) x).toReal :=
    (coeFn_densityActionCLM κ ν 2 hinv hb ψ).trans (densityAction_ae_eq_of_nonneg κ hψae)
  have hofReal : eLpNorm (fun y => ENNReal.ofReal (ψ y)) 2 ν ≤ eLpNorm (⇑ψ) 2 ν :=
    eLpNorm_mono_enorm fun y => by
      rw [enorm_eq_self, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hfin : eLpNorm (fun y => ENNReal.ofReal (ψ y)) 2 ν ≠ ⊤ :=
    ne_top_of_le_ne_top (Lp.eLpNorm_ne_top ψ) hofReal
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (ψ y)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable (Lp.aestronglyMeasurable ψ).aemeasurable
  have hbound := h.eLpNorm_bindDensity_le hS hmeas hfin
  have htoReal : eLpNorm (fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (ψ y)) x).toReal)
      2 ν ≤ eLpNorm (bindDensity κ ν (fun y => ENNReal.ofReal (ψ y))) 2 ν :=
    eLpNorm_mono_enorm fun x => by
      rw [enorm_eq_self, Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
  have hsum_coe : (∑ i, (c i : ℝ≥0∞)) = ENNReal.ofReal (∑ i, (c i : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (c i).coe_nonneg)]
    simp only [ENNReal.ofReal_coe_nnreal]
  have hne : ENNReal.ofReal (∑ i, (c i : ℝ)) * eLpNorm (⇑ψ) 2 ν ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top ψ)
  rw [Lp.norm_def, eLpNorm_congr_ae hrep, Lp.norm_def]
  calc (eLpNorm (fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (ψ y)) x).toReal) 2 ν).toReal
      ≤ (ENNReal.ofReal (∑ i, (c i : ℝ)) * eLpNorm (⇑ψ) 2 ν).toReal := by
        refine ENNReal.toReal_mono hne ?_
        calc _ ≤ _ := htoReal
          _ ≤ _ := hbound
          _ ≤ _ := by rw [hsum_coe]; gcongr
    _ = (∑ i, (c i : ℝ)) * (eLpNorm (⇑ψ) 2 ν).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
          (Finset.sum_nonneg fun i _ => (c i).coe_nonneg)]


/-- **The Stern bound supplies the operator-norm hypothesis.** For an EGF policy whose maps satisfy
the Stern bound, `P⋆` is bounded on `L²(ν)` with constant `∑ᵢ cᵢ`:
the hypothesis "finite `L²(ν) → L²(ν)` operator norm" that `theo:universality_L2_body` inherits
from `theo:universality_L2_full` is implied by its other hypotheses. -/
theorem IsEGFPolicy.isBoundedDensityAction {ν : Measure α} [IsFiniteMeasure ν] [IsMarkovKernel κ]
    (h : IsEGFPolicy κ Φ w) {c : Fin m → ℝ≥0}
    (hS : ∀ i, SternBound ν (Φ i) (c i)) :
    IsBoundedDensityAction κ ν 2 (∑ i, (c i : ℝ)) := by
  have hsum_coe : (∑ i, (c i : ℝ≥0∞)) = ENNReal.ofReal (∑ i, (c i : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (c i).coe_nonneg)]
    simp only [ENNReal.ofReal_coe_nnreal]
  -- The bound, for every `f ∈ L²(ν)`.
  have key : ∀ f : α → ℝ, MemLp f 2 ν →
      eLpNorm (densityAction κ ν f) 2 ν ≤ ENNReal.ofReal (∑ i, (c i : ℝ)) * eLpNorm f 2 ν := by
    intro f hf
    have hfm : AEMeasurable f ν := hf.aestronglyMeasurable.aemeasurable
    set fp : α → ℝ≥0∞ := fun y => ENNReal.ofReal (f y)
    set fn : α → ℝ≥0∞ := fun y => ENNReal.ofReal (-f y)
    have hfpm : AEMeasurable fp ν := ENNReal.measurable_ofReal.comp_aemeasurable hfm
    have hfnm : AEMeasurable fn ν := ENNReal.measurable_ofReal.comp_aemeasurable hfm.neg
    have hint : Integrable f ν := hf.integrable (by norm_num)
    have hadd : bindDensity κ ν (fp + fn) =ᵐ[ν] bindDensity κ ν fp + bindDensity κ ν fn :=
      bindDensity_add κ hfpm (lintegral_ofReal_ne_top hint) (lintegral_ofReal_ne_top hint.neg)
    -- `fp + fn = ‖f‖ₑ`, whose `L²` norm is that of `f`.
    have habs : fp + fn = fun y => ‖f y‖ₑ := by
      funext y
      simp only [fp, fn, Pi.add_apply, Real.enorm_eq_ofReal_abs]
      rcases le_total 0 (f y) with hy | hy
      · rw [ENNReal.ofReal_of_nonpos (by linarith : -f y ≤ 0), add_zero, abs_of_nonneg hy]
      · rw [ENNReal.ofReal_of_nonpos hy, zero_add, abs_of_nonpos hy]
    have hnorm_abs : eLpNorm (fp + fn) 2 ν = eLpNorm f 2 ν := by
      rw [habs]
      exact eLpNorm_enorm f
    have hpoint : ∀ᵐ x ∂ν, ‖densityAction κ ν f x‖ₑ ≤ ‖bindDensity κ ν (fp + fn) x‖ₑ := by
      filter_upwards [hadd] with x hx
      rw [hx, enorm_eq_self, Pi.add_apply, Real.enorm_eq_ofReal_abs]
      simp only [densityAction]
      calc ENNReal.ofReal |(bindDensity κ ν fp x).toReal - (bindDensity κ ν fn x).toReal|
          ≤ ENNReal.ofReal ((bindDensity κ ν fp x).toReal + (bindDensity κ ν fn x).toReal) := by
            refine ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨?_, ?_⟩) <;>
              linarith [ENNReal.toReal_nonneg (a := bindDensity κ ν fp x),
                ENNReal.toReal_nonneg (a := bindDensity κ ν fn x)]
        _ ≤ ENNReal.ofReal (bindDensity κ ν fp x).toReal
              + ENNReal.ofReal (bindDensity κ ν fn x).toReal := ENNReal.ofReal_add_le
        _ ≤ bindDensity κ ν fp x + bindDensity κ ν fn x := by
            gcongr <;> exact ENNReal.ofReal_toReal_le
    have hfin : eLpNorm (fp + fn) 2 ν ≠ ⊤ := by rw [hnorm_abs]; exact hf.eLpNorm_ne_top
    calc eLpNorm (densityAction κ ν f) 2 ν ≤ eLpNorm (bindDensity κ ν (fp + fn)) 2 ν :=
          eLpNorm_mono_enorm_ae hpoint
      _ ≤ (∑ i, (c i : ℝ≥0∞)) * eLpNorm (fp + fn) 2 ν :=
          h.eLpNorm_bindDensity_le hS (hfpm.add hfnm) hfin
      _ = ENNReal.ofReal (∑ i, (c i : ℝ)) * eLpNorm f 2 ν := by rw [hsum_coe, hnorm_abs]
  refine ⟨Finset.sum_nonneg fun i _ => (c i).coe_nonneg, fun f hf => ?_, key⟩
  refine ⟨(measurable_densityAction κ ν f).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (key f hf) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

/-- **The Stern constant is at least `1`.** Under invariance `P⋆ 𝟏 = 𝟏`, so the Stern route's
constant `1 + ∑ᵢ cᵢ` is at least `2`, for every non-zero `ν`. -/
theorem IsEGFPolicy.one_le_sum_stern {ν : Measure α} [IsFiniteMeasure ν] [IsMarkovKernel κ]
    (hν : ν ≠ 0) {C : ℝ} (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν 2 C)
    (h : IsEGFPolicy κ Φ w) {c : Fin m → ℝ≥0} (hS : ∀ i, SternBound ν (Φ i) (c i)) :
    1 ≤ ∑ i, (c i : ℝ) := by
  have hone : (0 : Lp ℝ 2 ν) ≤ constOne ν 2 := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [coeFn_constOne (ν := ν) (p := 2)] with x hx
    rw [hx]
    exact zero_le_one
  have hle := h.norm_densityActionCLM_le hinv hb hS hone
  rw [densityActionCLM_constOne κ ν 2 hinv hb] at hle
  have hpos : 0 < ‖constOne ν 2‖ := by
    refine norm_pos_iff.2 fun h0 => hν ?_
    have hint := integral_constOne (ν := ν) (p := 2)
    have hz : ∫ x, (0 : Lp ℝ 2 ν) x ∂ν = 0 := by
      rw [integral_congr_ae (Lp.coeFn_zero ℝ 2 ν)]
      exact integral_zero _ _
    rw [h0, hz] at hint
    have : ν Set.univ = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 hint.symm with h1 | h1
      · exact h1
      · exact absurd h1 (measure_ne_top ν _)
    exact Measure.measure_univ_eq_zero.1 this
  nlinarith

/-! ## `theo:universality_L2_body` -/

section Body

variable {ν : Measure α} [IsFiniteMeasure ν] [IsMarkovKernel κ] {C : ℝ}

omit [IsFiniteMeasure ν] in
/-- The infimum of `theo:universality_L2_body`, over the non-negative outflows of `L²(ν)`, read off
the `ε`-form of `WeaklyUniversalAt`: the residual sum is non-negative, so the infimum is `0`
exactly when it is approached. -/
theorem iInf_residuals_eq_zero {P : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} {θ : Lp ℝ 2 ν}
    (h : WeaklyUniversalAt P θ) :
    ⨅ fout : {f : Lp ℝ 2 ν // 0 ≤ f}, (‖resInit P θ fout.1‖ + ‖resTerm P θ fout.1‖) = 0 := by
  have hbdd : BddBelow (Set.range fun fout : {f : Lp ℝ 2 ν // 0 ≤ f} =>
      ‖resInit P θ fout.1‖ + ‖resTerm P θ fout.1‖) :=
    ⟨0, fun _ ⟨_, hy⟩ => hy ▸ by positivity⟩
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) ?_
  · obtain ⟨fout, hnn, hlt⟩ := h ε hε
    rw [zero_add]
    exact (ciInf_le hbdd ⟨fout, hnn⟩).trans_lt hlt
  · haveI : Nonempty {f : Lp ℝ 2 ν // 0 ≤ f} := ⟨⟨0, le_rfl⟩⟩
    exact le_ciInf fun _ => by positivity

/-- **The displays of the proof of `theo:universality_L2_body`** (`proofs.tex:133–137`), at the
lifted outflow `f_out^η` and the truncation `ψ_η` of `theo:universality_L2_full`, for every `η`:

  `½ (‖δf_init‖ + ‖δf_term‖) ≤ ‖(ψ_η ν) π⋆‖ + ‖ψ_η‖ ≤ (1 + ∑ᵢ cᵢ) ‖ψ_η‖`,

with `cᵢ` the Stern constant of the `i`-th map. -/
theorem universality_L2_body_display (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν 2 C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν 2 hinv hb) ^ n - meanProj ν 2‖)
    (hEGF : IsEGFPolicy κ Φ w) {c : Fin m → ℝ≥0} (hS : ∀ i, SternBound ν (Φ i) (c i))
    {f_init f_term : Lp ℝ 2 ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) (η : ℝ) :
    (1 / 2 : ℝ) * (‖resInit (densityActionCLM κ ν 2 hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
            (f_term - f_init) η)‖
        + ‖resTerm (densityActionCLM κ ν 2 hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
            (f_term - f_init) η)‖)
      ≤ ‖densityActionCLM κ ν 2 hinv hb
            (truncation (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
              (f_term - f_init) η)‖
        + ‖truncation (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
              (f_term - f_init) η‖
      ∧ ‖densityActionCLM κ ν 2 hinv hb
            (truncation (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
              (f_term - f_init) η)‖
        + ‖truncation (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
              (f_term - f_init) η‖
      ≤ (1 + ∑ i, (c i : ℝ))
        * ‖truncation (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
              (f_term - f_init) η‖ := by
  set P := densityActionCLM κ ν 2 hinv hb with hP
  set θ := f_term - f_init with hθdef
  have hone := densityActionCLM_constOne κ ν 2 hinv hb
  have hmix := mixing_of_massPreserving hone (integral_densityActionCLM κ ν 2 hinv hb) hsum
  have hθ : meanProj ν 2 θ = 0 := meanProj_sub_eq_zero hmass
  refine ⟨?_, ?_⟩
  · have h2 := residuals_le_two_norm_defect P θ
      (liftedOutflow P (meanProj ν 2) (constOne ν 2) θ η)
    rw [defect_eq_truncation hmix hone hθ η] at h2
    have h3 := norm_sub_le (P (truncation P (meanProj ν 2) (constOne ν 2) θ η))
      (truncation P (meanProj ν 2) (constOne ν 2) θ η)
    linarith
  · have h4 := hEGF.norm_densityActionCLM_le hinv hb hS
      (truncation_nonneg P (meanProj ν 2) (constOne ν 2) θ η)
    linarith

/-- **The last display of the proof of `theo:universality_L2_body`** (`proofs.tex:139–141`): the
two residuals of `f_out^η` vanish together as `η → +∞`, by the Stern constant and
`‖ψ_η‖ → 0`. -/
theorem tendsto_residuals_L2_body (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν 2 C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν 2 hinv hb) ^ n - meanProj ν 2‖)
    (hEGF : IsEGFPolicy κ Φ w) {c : Fin m → ℝ≥0} (hS : ∀ i, SternBound ν (Φ i) (c i))
    {f_init f_term : Lp ℝ 2 ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    Tendsto (fun η : ℝ =>
      ‖resInit (densityActionCLM κ ν 2 hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
            (f_term - f_init) η)‖
        + ‖resTerm (densityActionCLM κ ν 2 hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2) (constOne ν 2)
            (f_term - f_init) η)‖) atTop (𝓝 0) := by
  have hlim := (tendsto_truncation_norm_all (densityActionCLM κ ν 2 hinv hb) (meanProj ν 2)
    (f_term - f_init)).const_mul (2 * (1 + ∑ i, (c i : ℝ)))
  rw [mul_zero] at hlim
  refine squeeze_zero (fun _ => by positivity) (fun η => ?_) hlim
  obtain ⟨h1, h2⟩ := universality_L2_body_display hinv hb hsum hEGF hS hmass η
  linarith

/-- **`theo:universality_L2_body`** (`proofs.tex:119–125`), in the `ε`-form of the library: for
every `ε > 0` some non-negative outflow `f_out ∈ L²(ν)` brings `‖δf_init‖ + ‖δf_term‖` below `ε`.
The witness is `f_out^η` for `η` large, and the proof runs through the Stern constant. -/
theorem weaklyUniversalAt_L2_body (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν 2 C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν 2 hinv hb) ^ n - meanProj ν 2‖)
    (hEGF : IsEGFPolicy κ Φ w) {c : Fin m → ℝ≥0} (hS : ∀ i, SternBound ν (Φ i) (c i))
    {f_init f_term : Lp ℝ 2 ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    WeaklyUniversalAt (densityActionCLM κ ν 2 hinv hb) (f_term - f_init) := by
  intro ε hε
  obtain ⟨η, hη⟩ :=
    ((tendsto_residuals_L2_body hinv hb hsum hEGF hS hmass).eventually_lt_const hε).exists
  exact ⟨_, liftedOutflow_nonneg _ _ _ _ _, hη⟩

/-- **`theo:universality_L2_body`** (`proofs.tex:119–125`), as printed:

  `inf_{f_out ∈ L²(ν), f_out ≥ 0} (‖δf_init‖_{L²(ν)} + ‖δf_term‖_{L²(ν)}) = 0`

for an EGF policy `π⋆ = ∑ᵢ wᵢ δ_{Φᵢ}` whose maps satisfy the Stern bound, under the hypotheses of
`theo:universality_L2_full` at `p = 2`. -/
theorem universality_L2_body (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν 2 C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν 2 hinv hb) ^ n - meanProj ν 2‖)
    (hEGF : IsEGFPolicy κ Φ w) {c : Fin m → ℝ≥0} (hS : ∀ i, SternBound ν (Φ i) (c i))
    {f_init f_term : Lp ℝ 2 ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    ⨅ fout : {f : Lp ℝ 2 ν // 0 ≤ f},
      (‖resInit (densityActionCLM κ ν 2 hinv hb) (f_term - f_init) fout.1‖
        + ‖resTerm (densityActionCLM κ ν 2 hinv hb) (f_term - f_init) fout.1‖) = 0 :=
  iInf_residuals_eq_zero (weaklyUniversalAt_L2_body hinv hb hsum hEGF hS hmass)

/-- **`theo:universality_L2_body` without its own hypotheses.** The printed conclusion follows from
`theo:universality_L2_full` at `p = 2` alone — no EGF structure, no Stern bound: the manifold, the
volume form and the EGF enter the proof only through the constant, which the statement does not
carry. -/
theorem universality_L2_body_of_full (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν 2 C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν 2 hinv hb) ^ n - meanProj ν 2‖)
    {f_init f_term : Lp ℝ 2 ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    ⨅ fout : {f : Lp ℝ 2 ν // 0 ≤ f},
      (‖resInit (densityActionCLM κ ν 2 hinv hb) (f_term - f_init) fout.1‖
        + ‖resTerm (densityActionCLM κ ν 2 hinv hb) (f_term - f_init) fout.1‖) = 0 :=
  iInf_residuals_eq_zero (weaklyUniversalAt_of_kernel κ ν 2 hinv hb hsum (by norm_num) hmass)

/-- **`theo:universality_L2_body` with its operator-norm hypothesis discharged.** The bound
`‖P⋆‖_{L²(ν)} ≤ ∑ᵢ cᵢ` is supplied by the Stern bound (`IsEGFPolicy.isBoundedDensityAction`), so
the theorem holds with invariance, summable mixing, the EGF structure and the Stern bound only. -/
theorem universality_L2_body_of_stern (hinv : ν.bind ⇑κ = ν) (hEGF : IsEGFPolicy κ Φ w)
    {c : Fin m → ℝ≥0} (hS : ∀ i, SternBound ν (Φ i) (c i))
    (hsum : Summable fun n : ℕ =>
      ‖(densityActionCLM κ ν 2 hinv (hEGF.isBoundedDensityAction hS)) ^ n - meanProj ν 2‖)
    {f_init f_term : Lp ℝ 2 ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    ⨅ fout : {f : Lp ℝ 2 ν // 0 ≤ f},
      (‖resInit (densityActionCLM κ ν 2 hinv (hEGF.isBoundedDensityAction hS)) (f_term - f_init)
          fout.1‖
        + ‖resTerm (densityActionCLM κ ν 2 hinv (hEGF.isBoundedDensityAction hS))
          (f_term - f_init) fout.1‖) = 0 :=
  universality_L2_body hinv (hEGF.isBoundedDensityAction hS) hsum hEGF hS hmass

end Body


/-! ## Inhabitation -/

section Resampling

variable {ν : Measure α} [IsProbabilityMeasure ν]

/-- A policy that resamples from `ν` whatever the state leaves `ν` invariant. -/
theorem bind_of_resampling {κ : Kernel α α} (hκ : ⇑κ = fun _ => ν) : ν.bind ⇑κ = ν := by
  rw [hκ, Measure.bind_const, measure_univ, one_smul]

/-- The resampling policy pushes `g ν` to `(∫ g dν) ν`. -/
theorem bindDensity_of_resampling {κ : Kernel α α} (hκ : ⇑κ = fun _ => ν) {g : α → ℝ≥0∞}
    (hg : ∫⁻ x, g x ∂ν ≠ ⊤) : bindDensity κ ν g =ᵐ[ν] fun _ => ∫⁻ x, g x ∂ν := by
  have hpush : (ν.withDensity g).bind ⇑κ = (∫⁻ x, g x ∂ν) • ν := by
    rw [hκ, Measure.bind_const, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [bindDensity, hpush]
  filter_upwards [Measure.rnDeriv_smul_left_of_ne_top ν ν hg, Measure.rnDeriv_self ν]
    with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, mul_one]

/-- The density action of the resampling policy is the mean. -/
theorem densityAction_of_resampling {κ : Kernel α α} (hκ : ⇑κ = fun _ => ν) {f : α → ℝ}
    (hf : Integrable f ν) : densityAction κ ν f =ᵐ[ν] fun _ => ∫ x, f x ∂ν := by
  filter_upwards [bindDensity_of_resampling hκ (lintegral_ofReal_ne_top hf),
    bindDensity_of_resampling hκ (g := fun y => ENNReal.ofReal (-f y))
      (lintegral_ofReal_ne_top hf.neg)] with x h1 h2
  simp only [densityAction]
  rw [h1, h2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm

/-- The resampling policy is bounded on `L²(ν)` with constant `1`. -/
theorem isBoundedDensityAction_of_resampling {κ : Kernel α α} (hκ : ⇑κ = fun _ => ν) :
    IsBoundedDensityAction κ ν 2 1 where
  nonneg := zero_le_one
  memLp f hf := (memLp_const (∫ x, f x ∂ν)).ae_eq
    (densityAction_of_resampling hκ (hf.integrable (by norm_num))).symm
  eLpNorm_le f hf := by
    have hint := hf.integrable (by norm_num)
    rw [eLpNorm_congr_ae (densityAction_of_resampling hκ hint), ENNReal.ofReal_one, one_mul]
    have hb : ∀ᵐ _x ∂ν, ‖∫ x, f x ∂ν‖ ≤ ∫ x, ‖f x‖ ∂ν :=
      Eventually.of_forall fun _ => norm_integral_le_integral_norm f
    refine (eLpNorm_le_of_ae_bound hb).trans ?_
    rw [measure_univ, ENNReal.one_rpow, one_mul,
      ofReal_integral_norm_eq_lintegral_enorm hint, ← eLpNorm_one_eq_lintegral_enorm]
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hint.1
    rwa [measure_univ, ENNReal.one_rpow, mul_one] at h

/-- On `L²(ν)` the density action of the resampling policy is the mean projection. -/
theorem densityActionCLM_of_resampling {κ : Kernel α α} [IsMarkovKernel κ]
    (hκ : ⇑κ = fun _ => ν) :
    densityActionCLM κ ν 2 (bind_of_resampling hκ) (isBoundedDensityAction_of_resampling hκ)
      = meanProj ν 2 := by
  ext1 F
  refine Lp.ext ?_
  have h1 := coeFn_densityActionCLM κ ν 2 (bind_of_resampling hκ)
    (isBoundedDensityAction_of_resampling hκ) F
  refine (h1.trans (densityAction_of_resampling hκ ((Lp.memLp F).integrable
    (by norm_num)))).trans ?_
  rw [meanProj_apply, measure_univ, ENNReal.toReal_one, div_one]
  filter_upwards [Lp.coeFn_smul (∫ x, F x ∂ν) (constOne ν 2),
    coeFn_constOne (ν := ν) (p := 2)] with x e1 e2
  rw [e1, Pi.smul_apply, e2, smul_eq_mul, mul_one]

/-- The mixing coefficients of a resampling policy vanish from `n = 1` on. -/
theorem summable_of_resampling {κ : Kernel α α} [IsMarkovKernel κ] (hκ : ⇑κ = fun _ => ν) :
    Summable fun n : ℕ => ‖(densityActionCLM κ ν 2 (bind_of_resampling hκ)
        (isBoundedDensityAction_of_resampling hκ)) ^ n - meanProj ν 2‖ := by
  rw [densityActionCLM_of_resampling hκ]
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  have hn0 : n ≠ 0 := fun h => hn (Finset.mem_singleton.2 h)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hidem : ∀ k : ℕ, (meanProj ν 2) ^ (k + 1) = meanProj ν 2 := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one]
    | succ k ih =>
        rw [pow_succ, ih]
        exact meanProj_idem (by rw [measure_univ]; exact one_ne_zero)
  rw [hidem k, sub_self, norm_zero]

/-- A measure-preserving map satisfies the Stern bound with constant `1`. -/
theorem sternBound_of_map_eq {Ψ : α → α} (hΨ : Measurable Ψ) (hmap : ν.map Ψ = ν) :
    SternBound ν Ψ 1 := by
  refine sternBound_of_rnDeriv_le hΨ (by rw [hmap]) ?_
  filter_upwards [Measure.rnDeriv_self ν] with x hx
  rw [hmap, hx, ENNReal.coe_one, one_pow]

end Resampling

/-! ### The witness: the two-point space, the identity and the swap, with equal weights -/

/-- The uniform probability on `Bool`. -/
noncomputable def coinMeasure : Measure Bool :=
  ENNReal.ofReal (1 / 2) • (Measure.dirac true + Measure.dirac false)

/-- The witness measure is a probability. -/
instance isProbabilityMeasure_coinMeasure : IsProbabilityMeasure coinMeasure := by
  refine ⟨?_⟩
  simp only [coinMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- The two maps of the witness: the identity and the swap. -/
def coinMaps : Fin 2 → Bool → Bool := ![id, not]

/-- Equal mixture weights. -/
noncomputable def coinWeights : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

/-- Every map out of `Bool` is measurable. -/
theorem measurable_coinMaps (i : Fin 2) : Measurable (coinMaps i) := measurable_of_countable _

/-- Constant weights are measurable. -/
theorem measurable_coinWeights (i : Fin 2) : Measurable (coinWeights i) := measurable_const

/-- The EGF policy `π⋆(x) = ½ δ_x + ½ δ_{¬x}`. -/
noncomputable def coinKernel : Kernel Bool Bool :=
  egfKernel coinMaps coinWeights measurable_coinMaps measurable_coinWeights

/-- The witness kernel is the policy of an EGF. -/
theorem isEGFPolicy_coinKernel : IsEGFPolicy coinKernel coinMaps coinWeights :=
  isEGFPolicy_egfKernel _ _ _ _ (fun _ _ => by norm_num [coinWeights])
    (fun _ => by simp only [coinWeights, Fin.sum_univ_two]; norm_num)

/-- The witness kernel is Markov. -/
instance isMarkovKernel_coinKernel : IsMarkovKernel coinKernel := isEGFPolicy_coinKernel.isMarkovKernel

/-- The witness policy resamples from the uniform probability: `½ δ_x + ½ δ_{¬x} = ν`. -/
theorem coe_coinKernel : ⇑coinKernel = fun _ => coinMeasure := by
  funext x
  rw [isEGFPolicy_coinKernel.apply_eq x, Fin.sum_univ_two]
  cases x
  · simp only [coinMaps, coinWeights, coinMeasure, Matrix.cons_val_zero, Matrix.cons_val_one,
      id, Bool.not_false, smul_add]
    rw [add_comm]
  · simp only [coinMaps, coinWeights, coinMeasure, Matrix.cons_val_zero, Matrix.cons_val_one,
      id, Bool.not_true, smul_add]

/-- The swap preserves the uniform probability. -/
theorem map_not_coinMeasure : coinMeasure.map not = coinMeasure := by
  have hnot : Measurable not := measurable_of_countable _
  rw [coinMeasure, Measure.map_smul, Measure.map_add _ _ hnot, Measure.map_dirac' hnot,
    Measure.map_dirac' hnot, Bool.not_true, Bool.not_false, add_comm]

/-- Both maps of the witness preserve the uniform probability. -/
theorem map_coinMaps (i : Fin 2) : coinMeasure.map (coinMaps i) = coinMeasure := by
  fin_cases i
  · exact Measure.map_id
  · exact map_not_coinMeasure

/-- Both maps of the witness satisfy the Stern bound with constant `1`. -/
theorem sternBound_coinMaps (i : Fin 2) : SternBound coinMeasure (coinMaps i) 1 :=
  sternBound_of_map_eq (measurable_coinMaps i) (map_coinMaps i)

/-- **Inhabitation of the whole hypothesis bundle of `universality_L2_body`**, and its conclusion
at the witness: the uniform probability on `Bool`, the EGF policy `½ δ_x + ½ δ_{¬x}` (a mixture of
two measure-preserving bijections, not the identity kernel), invariance, the `L²` bound, summable
mixing, and the Stern bound with `cᵢ = 1`. -/
theorem universality_L2_body_coin {f_init f_term : Lp ℝ 2 coinMeasure}
    (hmass : ∫ x, f_init x ∂coinMeasure = ∫ x, f_term x ∂coinMeasure) :
    ⨅ fout : {f : Lp ℝ 2 coinMeasure // 0 ≤ f},
      (‖resInit (densityActionCLM coinKernel coinMeasure 2 (bind_of_resampling coe_coinKernel)
            (isBoundedDensityAction_of_resampling coe_coinKernel)) (f_term - f_init) fout.1‖
        + ‖resTerm (densityActionCLM coinKernel coinMeasure 2 (bind_of_resampling coe_coinKernel)
            (isBoundedDensityAction_of_resampling coe_coinKernel)) (f_term - f_init) fout.1‖)
      = 0 :=
  universality_L2_body (bind_of_resampling coe_coinKernel)
    (isBoundedDensityAction_of_resampling coe_coinKernel) (summable_of_resampling coe_coinKernel)
    isEGFPolicy_coinKernel sternBound_coinMaps hmass

end GFNBounds.Core.EGF
