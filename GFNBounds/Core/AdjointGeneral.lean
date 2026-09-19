import Mathlib.Probability.Kernel.Posterior
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import GFNBounds.Core.Adjoint

/-!
# The `λ`-reversal of a Markov kernel on a standard Borel space, and its `L²(λ)` adjointness

**`lem:adjoint`** — statement `proofs.tex:412–420`, proof `proofs.tex:422–455` (line numbers
advisory, kb 0036; the label is the anchor).

> Let `𝒮` be Polish, let `ν_B ∈ 𝓜⁺(𝒮)`, let `T` be a Markov kernel on `𝒮`, and let
> `λ ∈ 𝓜⁺(𝒮, ν_B)` be non-zero, finite and `T`-invariant. Then:
> *(1)* the measure `T ⊗ λ` on `𝒮²` disintegrates over its first marginal — which is `λT = λ` —
> into a `λ`-almost everywhere unique Markov kernel `T^λ`, the *`λ`-reversal* of `T`,
> characterized by `λ ⊗ T^λ = T ⊗ λ`;
> *(2)* `λ` is `T^λ`-invariant and `T^λ ⊗ λ = λ ⊗ T`, so that `T` is in turn the `λ`-reversal of
> `T^λ`: reversal is an involution, `λ`-almost everywhere, on the Markov kernels leaving `λ`
> invariant;
> *(3)* the density actions `μ ↦ μT` and `μ ↦ μT^λ` are mutually adjoint contractions of
> `𝓜²(λ)`, each of operator norm `1`: `⟪μT ∣ ν⟫_λ = ⟪μ ∣ νT^λ⟫_λ` for all `μ, ν ∈ 𝓜²(λ)`; under
> `μ ↦ dμ/dλ` the density action of each of `T` and `T^λ` on `𝓜²(λ)` is the function action of
> the other on `L²(λ)`;
> *(4)* when `T = π_←` is a backward policy […] its reversal, written `π_→^λ := π_←^λ`, is the
> forward policy that the *balanced* flow of inflow `λ` pairs with `π_←`, and
> `(π_→^λ)^λ = π_←` […]. On a finite marked graph with `λ > 0` everywhere,
> `π_→^λ(s → s') = λ(s')π̂_←(s' → s)/λ(s)` […].

This file is the **general** form. `GFNBounds/Core/Adjoint.lean` is the finite one (every item
over a `Fintype`, with the graph half of item (4)); `IsInvariant.toReal_reversal_singleton` below
shows the general reversal *is* that finite one on a discrete space.

Conventions. Mathlib's `λ ⊗ₘ A` is the paper's `λ ⊗ A`, `(λ ⊗ A)(dx dy) = λ(dx)A(x → dy)`; the
paper's `A ⊗ λ`, `(A ⊗ λ)(dx dy) = A(y → dx)λ(dy)`, is `(λ ⊗ₘ A).map Prod.swap` — the flip image,
as the paper's proof says. The density action `μ ↦ μA` is `A ∘ₘ μ` (`Measure.bind`); the function
action `u ↦ Au` is `funAct A u x = ∫ u dA(x)`.

## What the paper claims and this file delivers

| paper | here |
|---|---|
| *(1)* `T^λ` exists, is Markov | `reversal` (Mathlib's `ProbabilityTheory.posterior`, a `condKernel`), its `IsMarkovKernel` instance |
| *(1)* `λ ⊗ T^λ = T ⊗ λ` | `IsInvariant.isReversalPair_reversal` |
| *(1)* `T^λ` is `λ`-a.e. unique | `IsInvariant.ae_eq_reversal` (among all *finite* kernels, not only Markov ones) |
| *(2)* `λ` is `T^λ`-invariant | `IsInvariant.isInvariant_reversal` |
| *(2)* `T^λ ⊗ λ = λ ⊗ T`, `eq:reversal_flip` | `IsInvariant.isReversalPair_reversal_symm`, from `IsReversalPair.symm` |
| *(2)* `(T^λ)^λ = T`, `λ`-a.e. | `IsInvariant.reversal_reversal` |
| *(3)* `μT ≪ λ` for `μ ≪ λ` (the proof's first step) | `IsInvariant.comp_absolutelyContinuous` |
| *(3)* `⟪μT ∣ ν⟫_λ = ⟪μ ∣ νT^λ⟫_λ` on `𝓜²(λ)` | `IsReversalPair.ipM_comp` |
| *(3)* density action of `T` is the function action of `T^λ` under `μ ↦ dμ/dλ`, and conversely | `IsInvariant.rnDeriv_comp`, `IsInvariant.rnDeriv_reversal_comp`; everywhere-form `IsReversalPair.comp_withDensity`; real form `IsReversalPair.toReal_rnDeriv_comp` |
| *(3)* both are contractions of `𝓜²(λ)` | `IsReversalPair.inM2_comp`, `IsReversalPair.nrmM_comp_le` (every `L^p` density norm, `1 ≤ p ≤ ∞`) |
| *(3)* each of operator norm `1` | `IsReversalPair.isLeast_opNorm_comp` (density action), `IsInvariant.isLeast_opNorm_funAct` (function action, every `p`) |
| *(3)* `eq:reversal_contraction`, the Jensen step | `IsInvariant.eLpNorm_funAct_le` — every `L^p`, `1 ≤ p ≤ ∞`, Jensen per fibre (`lintegral_rpow_le`) |
| *(3)* the `L²(λ)` adjointness of the function actions, `∫ v · T^λu dλ = ∫ Tv · u dλ` | `IsInvariant.integral_mul_funAct_reversal`; for a Hölder pair `(p, q)` `IsReversalPair.integral_mul_funAct` — **signed** `u, v` |
| *(1)*–*(3)* in one statement | `adjoint_general` |
| *(4)*, general half: `π_→^λ := π_←^λ` is the unique kernel with the balance constraint `λ ⊗ π_→ = π_← ⊗ λ`, and `(π_→^λ)^λ = π_←` | items *(1)*–*(2)* at `T = π̂_←`: the paper's own proof of *(4)* reads the balance constraint as the characterizing identity, which is `IsReversalPair lam π̂_← π_→` here |
| *(4)*, finite half: `π_→^λ(s → s') = λ(s')π̂_←(s' → s)/λ(s)` | `IsInvariant.reversal_singleton` (general object, atoms, `λ{s} ≠ 0`), `IsInvariant.toReal_reversal_singleton` (equal to `GFNBounds.Core.reversal`); the support and wrap-edge clauses are `GFNBounds.Core.reversal_hatEdge`, `reversal_snk_src` |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒮` Polish | ✓ carried, weakened in the safe direction: `[StandardBorelSpace S]`, which every Polish space with its Borel σ-algebra is (instance `PolishSpace` + `BorelSpace` → `StandardBorelSpace`) |
| — | `[Nonempty S]`, needed by `posterior`'s definition. **Not an added hypothesis**: `λ ≠ 0` forces `𝒮 ≠ ∅`, so on an empty `𝒮` the paper's statement is vacuous (kb 0027) |
| `ν_B ∈ 𝓜⁺(𝒮)`, `λ ∈ 𝓜⁺(𝒮, ν_B)` | ✓ not needed: no statement involves `ν_B`; every finite `λ` is covered, in particular every one dominated by some `ν_B` |
| `T` a Markov kernel | ✓ carried (`[IsMarkovKernel T]`; Mathlib kernels are measurable by definition) |
| `λ` finite | ✓ carried (`[IsFiniteMeasure lam]`) |
| `λ` non-zero | ✓ carried where used — the operator-norm-`1` clauses (`hlam : lam ≠ 0`); items *(1)*–*(2)*, the adjointness and the contractions hold without it |
| `λ` `T`-invariant | ✓ carried (`IsInvariant T lam : T ∘ₘ lam = lam`) |
| `𝓜²(λ)`: non-negative measures with square-integrable `λ`-density | ✓ `InM2`: finite, `≪ λ`, `(dμ/dλ).toReal ∈ L²(λ)`; `inM2_withDensity_ofReal` and `InM2.eq_withDensity_ofReal` show it is exactly `{uλ : 0 ≤ u ∈ L²(λ)}` (u measurable; an a.e.-measurable u enters through its `mk` representative), and `InM2.of_sigmaFinite` that finiteness is implied for σ-finite `μ` |
| `λ ≠ 0` witnesses are inhabited | `isInvariant_id`, `isInvariant_const`: the hypotheses are not vacuous (kb 0025) |

## SCOPE (disclosed)

* **"Operator norm `1`" is `IsLeast`, not `‖·‖`.** `𝓜²(λ)` is a cone, not a normed space, so
  no continuous-linear-map object is formed; `1` is shown to be the least `c` with
  `‖μA‖ ≤ c‖μ‖` on `𝓜²(λ)` (and `‖Au‖_p ≤ c‖u‖_p` on `L^p(λ)`), attained at `λ` (resp. `1`).
* **The adjoint's uniqueness** ("`μ ↦ μT^λ` is the only map satisfying this identity",
  `proofs.tex`, proof of (3)) is the Riesz step and is not formalized as such; what is proved is
  uniqueness of the *reversal* (`IsInvariant.ae_eq_reversal`), from which it follows.
* **Item (4)'s "balanced flow" is not a Lean object in the general setting**: the general half of
  (4) is certified as items (1)–(2) at `T = π̂_←`, reading the balance constraint of the pair
  `(λ, π_→)` as `λ ⊗ π_→ = π̂_← ⊗ λ`, as the paper's proof of (4) does. The finite-graph half is
  `GFNBounds/Core/Adjoint.lean` (and `theo:universality_graphs`(2) for the balanced-flow reading).
* **Strengthened, proved**: the function-action contraction and operator norm hold on every
  `L^p(λ)`, `1 ≤ p ≤ ∞` (the paper states `p = 2`), the adjointness for every Hölder pair and for
  **signed** `u, v` (which is what `theo:first_variation_full`'s proof applies (3) to), and the
  uniqueness among all finite kernels. None of this outruns the paper's *statement* — each is
  proved here, and each specializes to the paper's clause.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GFNBounds.Core.General

variable {S : Type*} [MeasurableSpace S]

/-- `λ` is `T`-invariant: `λT = λ`. -/
def IsInvariant (T : Kernel S S) (lam : Measure S) : Prop := T ∘ₘ lam = lam

/-- The function action `Af(x) = ∫ f(y) A(x → dy)` (`proofs.tex`, proof of `lem:adjoint`(3)). -/
noncomputable def funAct (A : Kernel S S) (u : S → ℝ) : S → ℝ := fun x => ∫ y, u y ∂(A x)

/-- Every finite measure is invariant for the identity kernel: the hypotheses are inhabited. -/
theorem isInvariant_id (lam : Measure S) : IsInvariant Kernel.id lam := Measure.id_comp

/-- A probability `π` is invariant for the kernel resampling from `π`, a non-trivial instance. -/
theorem isInvariant_const (π : Measure S) [IsProbabilityMeasure π] :
    IsInvariant (Kernel.const S π) π := by
  unfold IsInvariant
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp

/-- A `λ`-null set is `A x`-null for `λ`-a.e. `x`, when `λ` is `A`-invariant. -/
theorem IsInvariant.ae_ae {A : Kernel S S} {lam : Measure S} (h : IsInvariant A lam)
    {p : S → Prop} (hp : ∀ᵐ y ∂lam, p y) : ∀ᵐ x ∂lam, ∀ᵐ y ∂(A x), p y := by
  have hp' : ∀ᵐ y ∂(A ∘ₘ lam), p y := by rw [h]; exact hp
  exact Measure.ae_ae_of_ae_comp hp'

/-- Jensen for `x ↦ x^p` in `ℝ≥0∞` against a probability measure. -/
theorem lintegral_rpow_le {ν : Measure S} [IsProbabilityMeasure ν] {f : S → ℝ≥0∞}
    (hf : AEMeasurable f ν) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ y, f y ∂ν) ^ p ≤ ∫⁻ y, f y ^ p ∂ν := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have h1 : eLpNorm f 1 ν ≤ eLpNorm f (ENNReal.ofReal p) ν :=
    eLpNorm_le_eLpNorm_of_exponent_le (by simpa using ENNReal.ofReal_le_ofReal hp)
      hf.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le] at h1
  simp only [enorm_eq_self] at h1
  calc (∫⁻ y, f y ∂ν) ^ p ≤ ((∫⁻ y, f y ^ p ∂ν) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h1 hp0.le
    _ = ∫⁻ y, f y ^ p ∂ν := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]

/-- The `L^p` contraction in `ℝ≥0∞`: Jensen per fibre, then invariance. -/
theorem IsInvariant.lintegral_rpow_lintegral_le {A : Kernel S S} [IsMarkovKernel A]
    {lam : Measure S} (h : IsInvariant A lam) {f : S → ℝ≥0∞} (hf : AEMeasurable f lam)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (∫⁻ y, f y ∂(A x)) ^ p ∂lam ≤ ∫⁻ y, f y ^ p ∂lam := by
  set g := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  have hfg : ∀ᵐ x ∂lam, ∫⁻ y, f y ∂(A x) = ∫⁻ y, g y ∂(A x) := by
    filter_upwards [h.ae_ae hf.ae_eq_mk] with x hx using lintegral_congr_ae hx
  calc ∫⁻ x, (∫⁻ y, f y ∂(A x)) ^ p ∂lam = ∫⁻ x, (∫⁻ y, g y ∂(A x)) ^ p ∂lam :=
        lintegral_congr_ae (by filter_upwards [hfg] with x hx; rw [hx])
    _ ≤ ∫⁻ x, ∫⁻ y, g y ^ p ∂(A x) ∂lam :=
        lintegral_mono fun x => lintegral_rpow_le hg.aemeasurable hp
    _ = ∫⁻ y, g y ^ p ∂(A ∘ₘ lam) :=
        (Measure.lintegral_bind (A.aemeasurable) (hg.pow_const p).aemeasurable).symm
    _ = ∫⁻ y, f y ^ p ∂lam := by
        rw [h]; exact lintegral_congr_ae (by
          filter_upwards [hf.ae_eq_mk] with y hy; rw [hy])

/-- `‖Au(x)‖ ≤ ∫⁻ ‖u‖ dA(x)`, the pointwise step. -/
theorem enorm_funAct_le (A : Kernel S S) (u : S → ℝ) (x : S) :
    ‖funAct A u x‖ₑ ≤ ∫⁻ y, ‖u y‖ₑ ∂(A x) :=
  enorm_integral_le_lintegral_enorm _

/-- The function action of `A` respects `λ`-a.e. equality when `λ` is `A`-invariant. -/
theorem IsInvariant.funAct_congr {A : Kernel S S} {lam : Measure S} (h : IsInvariant A lam)
    {u v : S → ℝ} (huv : u =ᵐ[lam] v) : funAct A u =ᵐ[lam] funAct A v := by
  filter_upwards [h.ae_ae huv] with x hx using integral_congr_ae hx

/-- The function action of `A` maps `λ`-a.e. strongly measurable functions to such. -/
theorem IsInvariant.aestronglyMeasurable_funAct {A : Kernel S S} {lam : Measure S}
    (h : IsInvariant A lam) {u : S → ℝ} (hu : AEStronglyMeasurable u lam) :
    AEStronglyMeasurable (funAct A u) lam :=
  ⟨funAct A (hu.mk u), hu.stronglyMeasurable_mk.integral_kernel, h.funAct_congr hu.ae_eq_mk⟩

/-- **`lem:adjoint`(3), `eq:reversal_contraction`: the function action is a contraction of every
`L^p(λ)`, `1 ≤ p ≤ ∞`** — the paper's
`eq:reversal_contraction` (stated there at `p = 2`), by Jensen per fibre and invariance. -/
theorem IsInvariant.eLpNorm_funAct_le {A : Kernel S S} [IsMarkovKernel A] {lam : Measure S}
    (h : IsInvariant A lam) {u : S → ℝ} (hu : AEStronglyMeasurable u lam) {p : ℝ≥0∞}
    (hp : 1 ≤ p) : eLpNorm (funAct A u) p lam ≤ eLpNorm u p lam := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  by_cases hpt : p = ⊤
  · subst hpt
    simp only [eLpNorm_exponent_top]
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [h.ae_ae (ae_le_eLpNormEssSup (f := u) (μ := lam))] with x hx
    calc ‖funAct A u x‖ₑ ≤ ∫⁻ y, ‖u y‖ₑ ∂(A x) := enorm_funAct_le A u x
      _ ≤ ∫⁻ _, eLpNormEssSup u lam ∂(A x) := lintegral_mono_ae hx
      _ = eLpNormEssSup u lam := by simp
  · have hpr : 1 ≤ p.toReal := by
      have := ENNReal.toReal_mono hpt hp; simpa using this
    have hpr0 : 0 < p.toReal := lt_of_lt_of_le one_pos hpr
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
    gcongr ?_ ^ _
    calc ∫⁻ x, ‖funAct A u x‖ₑ ^ p.toReal ∂lam
        ≤ ∫⁻ x, (∫⁻ y, ‖u y‖ₑ ∂(A x)) ^ p.toReal ∂lam :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (enorm_funAct_le A u x) hpr0.le
      _ ≤ ∫⁻ y, ‖u y‖ₑ ^ p.toReal ∂lam :=
          h.lintegral_rpow_lintegral_le hu.enorm hpr

/-- The function action maps `L^p(λ)` into itself. -/
theorem IsInvariant.memLp_funAct {A : Kernel S S} [IsMarkovKernel A] {lam : Measure S}
    (h : IsInvariant A lam) {u : S → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : MemLp u p lam) :
    MemLp (funAct A u) p lam :=
  ⟨h.aestronglyMeasurable_funAct hu.1, lt_of_le_of_lt (h.eLpNorm_funAct_le hu.1 hp) hu.2⟩

/-- A Markov kernel fixes the constants. -/
theorem funAct_one (A : Kernel S S) [IsMarkovKernel A] : funAct A (fun _ => 1) = fun _ => 1 := by
  funext x; simp [funAct]

/-- **`lem:adjoint`(3), operator norm exactly `1`** of the function action on `L^p(λ)`, `1 ≤ p ≤ ∞`: `1` is the least `c` with
`‖Au‖_p ≤ c‖u‖_p` for every `u ∈ L^p(λ)`, attained at the constant `1` (which is `dλ/dλ`). -/
theorem IsInvariant.isLeast_opNorm_funAct {A : Kernel S S} [IsMarkovKernel A] {lam : Measure S}
    [IsFiniteMeasure lam] (h : IsInvariant A lam) (hlam : lam ≠ 0) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    IsLeast {c : ℝ≥0∞ | ∀ u : S → ℝ, MemLp u p lam →
      eLpNorm (funAct A u) p lam ≤ c * eLpNorm u p lam} 1 := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  refine ⟨fun u hu => by simpa using h.eLpNorm_funAct_le hu.1 hp, fun c hc => ?_⟩
  have h1 := hc (fun _ => 1) (memLp_const 1)
  rw [funAct_one] at h1
  have ha0 : eLpNorm (fun _ : S => (1 : ℝ)) p lam ≠ 0 := by
    rw [eLpNorm_const _ hp0 hlam]
    simp [hlam]
  have hat : eLpNorm (fun _ : S => (1 : ℝ)) p lam ≠ ⊤ := (memLp_const 1).2.ne
  calc (1 : ℝ≥0∞) = eLpNorm (fun _ : S => (1 : ℝ)) p lam / eLpNorm (fun _ : S => (1 : ℝ)) p lam :=
        (ENNReal.div_self ha0 hat).symm
    _ ≤ c * eLpNorm (fun _ : S => (1 : ℝ)) p lam / eLpNorm (fun _ : S => (1 : ℝ)) p lam := by
        gcongr
    _ = c := ENNReal.mul_div_cancel_right ha0 hat

/-- `B` is a `λ`-reversal of `A`: `λ ⊗ B = A ⊗ λ`, where the paper's
`(A ⊗ λ)(dx dy) = A(y → dx) λ(dy)` is the flip image of `λ ⊗ A`. -/
def IsReversalPair (lam : Measure S) (A B : Kernel S S) : Prop :=
  lam ⊗ₘ B = (lam ⊗ₘ A).map Prod.swap

/-- The relation is symmetric: this is the flip identity `eq:reversal_flip`. -/
theorem IsReversalPair.symm {lam : Measure S} {A B : Kernel S S} (h : IsReversalPair lam A B) :
    IsReversalPair lam B A := by
  unfold IsReversalPair at *
  rw [h, Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id]

/-- A reversal leaves `λ` invariant: `λB` is the second marginal of `λ ⊗ B = A ⊗ λ`, which is
`λ` (the first marginal of `λ ⊗ A`). -/
theorem IsReversalPair.isInvariant {lam : Measure S} [SFinite lam] {A B : Kernel S S}
    [IsMarkovKernel A] [IsMarkovKernel B] (h : IsReversalPair lam A B) : IsInvariant B lam := by
  unfold IsInvariant
  rw [← Measure.snd_compProd lam B, h, Measure.snd_map_swap, Measure.fst_compProd]

section Reversal

variable [StandardBorelSpace S] [Nonempty S]

/-- **`lem:adjoint`(1), the `λ`-reversal** `T^λ`: the disintegration of `T ⊗ λ = fl_*(λ ⊗ T)` over its first
marginal, which is Mathlib's Bayesian posterior `T†λ` (`ProbabilityTheory.posterior`, defined as
`((λ ⊗ₘ T).map Prod.swap).condKernel`). -/
noncomputable def reversal (T : Kernel S S) (lam : Measure S) [IsFiniteMeasure lam]
    [IsMarkovKernel T] : Kernel S S :=
  T†lam

instance (T : Kernel S S) (lam : Measure S) [IsFiniteMeasure lam] [IsMarkovKernel T] :
    IsMarkovKernel (reversal T lam) := by
  unfold reversal; infer_instance

theorem posterior_congr_measure {T : Kernel S S} [IsMarkovKernel T] {μ ν : Measure S}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ = ν) : T†μ = T†ν := by
  subst h; rfl

variable {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsFiniteMeasure lam]

/-- **`lem:adjoint`(1), existence and the characterizing identity**: `λ ⊗ T^λ = T ⊗ λ`. -/
theorem IsInvariant.isReversalPair_reversal (h : IsInvariant T lam) :
    IsReversalPair lam T (reversal T lam) := by
  have := compProd_posterior_eq_map_swap (κ := T) (μ := lam)
  unfold IsInvariant at h
  unfold IsReversalPair reversal
  rw [h] at this
  exact this

/-- **`lem:adjoint`(1), `λ`-a.e. uniqueness**: every finite kernel `η` with `λ ⊗ η = T ⊗ λ` agrees with
`T^λ` `λ`-almost everywhere. -/
theorem IsInvariant.ae_eq_reversal (h : IsInvariant T lam) {η : Kernel S S} [IsFiniteKernel η]
    (hη : IsReversalPair lam T η) : η =ᵐ[lam] reversal T lam := by
  unfold IsInvariant at h
  have := ae_eq_posterior_of_compProd_eq (κ := T) (μ := lam) (η := η) (by rw [h]; exact hη)
  rw [h] at this
  exact this

/-- **`lem:adjoint`(2)**: `λ` is `T^λ`-invariant. -/
theorem IsInvariant.isInvariant_reversal (h : IsInvariant T lam) :
    IsInvariant (reversal T lam) lam :=
  IsReversalPair.isInvariant (A := T) h.isReversalPair_reversal

/-- **`lem:adjoint`(2)**: the flip identity `T^λ ⊗ λ = λ ⊗ T`, i.e. `T` is a `λ`-reversal of `T^λ`. -/
theorem IsInvariant.isReversalPair_reversal_symm (h : IsInvariant T lam) :
    IsReversalPair lam (reversal T lam) T :=
  h.isReversalPair_reversal.symm

/-- **`lem:adjoint`(2)**: reversal is a `λ`-a.e. involution, `(T^λ)^λ = T` `λ`-a.e. -/
theorem IsInvariant.reversal_reversal (h : IsInvariant T lam) :
    reversal (reversal T lam) lam =ᵐ[lam] T := by
  have := h.isInvariant_reversal.ae_eq_reversal h.isReversalPair_reversal_symm
  filter_upwards [this] with x hx using hx.symm

end Reversal

section DensityAction

variable {lam : Measure S} {A B : Kernel S S}

/-- **`lem:adjoint`(3), first step**: `μ ≪ λ ⟹ μA ≪ λ` when `λ` is `A`-invariant (`proofs.tex`, the
opening of the proof of (3)). -/
theorem IsInvariant.comp_absolutelyContinuous (h : IsInvariant A lam) {μ : Measure S}
    (hμ : μ ≪ lam) : A ∘ₘ μ ≪ lam := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  have h1 : ∀ᵐ y ∂lam, y ∉ s := measure_eq_zero_iff_ae_notMem.1 hs0
  have h2 : ∀ᵐ x ∂lam, A x s = 0 := by
    filter_upwards [h.ae_ae h1] with x hx
    exact measure_eq_zero_iff_ae_notMem.2 hx
  rw [Measure.bind_apply hs A.aemeasurable]
  exact lintegral_eq_zero_of_ae_eq_zero (hμ.ae_le h2)

/-- The lintegral identity behind item (3): `∫⁻ f(y) A(y → s) λ(dy) = ∫⁻_s (Bf) dλ` for a
`λ`-reversal pair `(A, B)`, `f ≥ 0` measurable. -/
theorem IsReversalPair.lintegral_mul_apply [SFinite lam] [IsMarkovKernel A] [IsMarkovKernel B]
    (h : IsReversalPair lam A B) {f : S → ℝ≥0∞} (hf : Measurable f) {s : Set S}
    (hs : MeasurableSet s) :
    ∫⁻ y, f y * A y s ∂lam = ∫⁻ x in s, ∫⁻ y, f y ∂(B x) ∂lam := by
  have hg : Measurable fun p : S × S => f p.1 * s.indicator 1 p.2 :=
    (hf.comp measurable_fst).mul ((measurable_const.indicator hs).comp measurable_snd)
  have hg' : Measurable fun q : S × S => f q.2 * s.indicator 1 q.1 :=
    (hf.comp measurable_snd).mul ((measurable_const.indicator hs).comp measurable_fst)
  calc ∫⁻ y, f y * A y s ∂lam
      = ∫⁻ p, f p.1 * s.indicator 1 p.2 ∂(lam ⊗ₘ A) := by
        rw [Measure.lintegral_compProd hg]
        refine lintegral_congr fun y => ?_
        dsimp only
        rw [lintegral_const_mul (f y) ((show Measurable (1 : S → ℝ≥0∞) from measurable_one).indicator hs)]
        congr 1
        exact (lintegral_indicator_one hs).symm
    _ = ∫⁻ q, f q.2 * s.indicator 1 q.1 ∂((lam ⊗ₘ A).map Prod.swap) := by
        rw [lintegral_map hg' measurable_swap]; rfl
    _ = ∫⁻ q, f q.2 * s.indicator 1 q.1 ∂(lam ⊗ₘ B) := by rw [h]
    _ = ∫⁻ x, s.indicator 1 x * ∫⁻ y, f y ∂(B x) ∂lam := by
        rw [Measure.lintegral_compProd hg']
        refine lintegral_congr fun x => ?_
        dsimp only
        by_cases hx : x ∈ s <;> simp [hx]
    _ = ∫⁻ x in s, ∫⁻ y, f y ∂(B x) ∂lam := by
        rw [← lintegral_indicator hs]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ s <;> simp [hx]

/-- **`lem:adjoint`(3), the density-action identity** `(fλ)A = (Bf)λ` for a `λ`-reversal pair: the
density action of `A` is, on densities, the function action of `B` — `d((fλ)A)/dλ = Bf`
*everywhere*, for every measurable `f ≥ 0`, with no integrability hypothesis. -/
theorem IsReversalPair.comp_withDensity [SFinite lam] [IsMarkovKernel A] [IsMarkovKernel B]
    (h : IsReversalPair lam A B) {f : S → ℝ≥0∞} (hf : Measurable f) :
    A ∘ₘ (lam.withDensity f) = lam.withDensity (fun x => ∫⁻ y, f y ∂(B x)) := by
  ext s hs
  rw [Measure.bind_apply hs A.aemeasurable, withDensity_apply _ hs,
    lintegral_withDensity_eq_lintegral_mul lam hf (A.measurable_coe hs)]
  exact h.lintegral_mul_apply hf hs

/-- **`lem:adjoint`(3), `d(μA)/dλ = B(dμ/dλ)`** for every σ-finite `μ ≪ λ`, `λ`-a.e. -/
theorem IsReversalPair.rnDeriv_comp [SigmaFinite lam] [IsMarkovKernel A] [IsMarkovKernel B]
    (h : IsReversalPair lam A B) {μ : Measure S} [SigmaFinite μ] (hμ : μ ≪ lam) :
    (A ∘ₘ μ).rnDeriv lam =ᵐ[lam] fun x => ∫⁻ y, μ.rnDeriv lam y ∂(B x) := by
  have hμ' : A ∘ₘ μ = lam.withDensity (fun x => ∫⁻ y, μ.rnDeriv lam y ∂(B x)) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ lam hμ]
    exact h.comp_withDensity (Measure.measurable_rnDeriv μ lam)
  rw [hμ']
  exact Measure.rnDeriv_withDensity lam (Measure.measurable_rnDeriv μ lam).lintegral_kernel

/-- The same identity read in `ℝ`: `(d(μA)/dλ).toReal = B((dμ/dλ).toReal)` `λ`-a.e. -/
theorem IsReversalPair.toReal_rnDeriv_comp [SigmaFinite lam] [IsMarkovKernel A]
    [IsMarkovKernel B] (h : IsReversalPair lam A B) {μ : Measure S} [SigmaFinite μ]
    (hμ : μ ≪ lam) :
    (fun x => ((A ∘ₘ μ).rnDeriv lam x).toReal) =ᵐ[lam]
      funAct B (fun y => (μ.rnDeriv lam y).toReal) := by
  have hB : IsInvariant B lam := h.isInvariant
  filter_upwards [h.rnDeriv_comp hμ, hB.ae_ae (Measure.rnDeriv_lt_top μ lam)] with x hx hlt
  rw [hx, funAct, integral_toReal (Measure.measurable_rnDeriv μ lam).aemeasurable hlt]

end DensityAction

section Adjoint

variable {lam : Measure S} [SFinite lam] {A B : Kernel S S} [IsMarkovKernel A] [IsMarkovKernel B]

theorem measurePreserving_fst_compProd (K : Kernel S S) [IsMarkovKernel K] :
    MeasurePreserving Prod.fst (lam ⊗ₘ K) lam :=
  ⟨measurable_fst, Measure.fst_compProd lam K⟩

theorem IsInvariant.measurePreserving_snd_compProd {K : Kernel S S} [IsMarkovKernel K]
    (h : IsInvariant K lam) : MeasurePreserving Prod.snd (lam ⊗ₘ K) lam :=
  ⟨measurable_snd, (Measure.snd_compProd lam K).trans h⟩

omit [SFinite lam] [IsMarkovKernel A] [IsMarkovKernel B] in
/-- A reversal pair makes the flip measure-preserving `λ ⊗ A → λ ⊗ B`. -/
theorem IsReversalPair.measurePreserving_swap (h : IsReversalPair lam A B) :
    MeasurePreserving Prod.swap (lam ⊗ₘ A) (lam ⊗ₘ B) :=
  ⟨measurable_swap, (show lam ⊗ₘ B = _ from h).symm⟩

/-- `(x, y) ↦ v(x) u(y)` is integrable on `λ ⊗ K` for `v ∈ L^p(λ)`, `u ∈ L^q(λ)`,
`1/p + 1/q = 1`, `λ` being `K`-invariant (Hölder, the paper's Cauchy–Schwarz/Fubini step). -/
theorem IsInvariant.integrable_mul_compProd {K : Kernel S S} [IsMarkovKernel K]
    (hK : IsInvariant K lam) {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1] {u v : S → ℝ}
    (hv : MemLp v p lam) (hu : MemLp u q lam) :
    Integrable (fun z : S × S => v z.1 * u z.2) (lam ⊗ₘ K) :=
  (hv.comp_measurePreserving (measurePreserving_fst_compProd K)).integrable_mul
    (hu.comp_measurePreserving hK.measurePreserving_snd_compProd)

/-- **`lem:adjoint`(3), `L^p`–`L^q` adjointness of the function actions** of a `λ`-reversal pair:
`∫ v · Bu dλ = ∫ Av · u dλ` for `v ∈ L^p(λ)`, `u ∈ L^q(λ)`, `1/p + 1/q = 1` (the paper states
`p = q = 2`). -/
theorem IsReversalPair.integral_mul_funAct (h : IsReversalPair lam A B) {p q : ℝ≥0∞}
    [ENNReal.HolderTriple p q 1] {u v : S → ℝ} (hv : MemLp v p lam) (hu : MemLp u q lam) :
    ∫ x, v x * funAct B u x ∂lam = ∫ x, funAct A v x * u x ∂lam := by
  have hA : IsInvariant A lam := h.symm.isInvariant
  have hB : IsInvariant B lam := h.isInvariant
  have hIB := hB.integrable_mul_compProd hv hu
  have hIA := hA.integrable_mul_compProd (p := q) (q := p) hu hv
  calc ∫ x, v x * funAct B u x ∂lam = ∫ x, ∫ y, v x * u y ∂(B x) ∂lam := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [funAct, integral_const_mul]
    _ = ∫ z, v z.1 * u z.2 ∂(lam ⊗ₘ B) := (Measure.integral_compProd hIB).symm
    _ = ∫ z, v z.2 * u z.1 ∂(lam ⊗ₘ A) :=
        (h.measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
          (fun z : S × S => v z.1 * u z.2)).symm
    _ = ∫ z, u z.1 * v z.2 ∂(lam ⊗ₘ A) := by simp only [mul_comm]
    _ = ∫ x, ∫ y, u x * v y ∂(A x) ∂lam := Measure.integral_compProd hIA
    _ = ∫ x, funAct A v x * u x ∂lam := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [funAct, integral_const_mul, mul_comm]

end Adjoint

section MeasureLevel

/-- `𝓜²(λ)`: the non-negative measures with a square-integrable density against `λ`
(`proofs.tex`, the conventions paragraph opening Appendix A). Finiteness is carried as a field
and is load-bearing: for finite `λ` it follows from the other two only when `μ` is σ-finite
(`InM2.of_sigmaFinite`); for `λ ≠ 0`, `μ = ∞ • λ` is `≪ λ` with `(dμ/dλ).toReal =ᵐ 0 ∈ L²`
and is not finite. -/
def InM2 (lam μ : Measure S) : Prop :=
  IsFiniteMeasure μ ∧ μ ≪ lam ∧ MemLp (fun x => (μ.rnDeriv lam x).toReal) 2 lam

/-- The inner product of `𝓜²(λ)`: `⟪μ ∣ ν⟫_λ = ∫ (dμ/dλ)(dν/dλ) dλ`. -/
noncomputable def ipM (lam μ ν : Measure S) : ℝ :=
  ∫ x, (μ.rnDeriv lam x).toReal * (ν.rnDeriv lam x).toReal ∂lam

/-- The `L^p(λ)` seminorm of the `λ`-density; at `p = 2` the norm of `𝓜²(λ)`. -/
noncomputable def nrmM (p : ℝ≥0∞) (lam μ : Measure S) : ℝ≥0∞ :=
  eLpNorm (fun x => (μ.rnDeriv lam x).toReal) p lam

variable {lam : Measure S} [IsFiniteMeasure lam] {A B : Kernel S S} [IsMarkovKernel A]
  [IsMarkovKernel B]

/-- For finite `λ`, a σ-finite `μ ≪ λ` with square-integrable density is finite. -/
theorem InM2.of_sigmaFinite {μ : Measure S} [SigmaFinite μ] (hμ : μ ≪ lam)
    (h2 : MemLp (fun x => (μ.rnDeriv lam x).toReal) 2 lam) : InM2 lam μ := by
  refine ⟨⟨?_⟩, hμ, h2⟩
  have hint : Integrable (fun x => (μ.rnDeriv lam x).toReal) lam :=
    h2.integrable (by norm_num)
  have := Measure.setLIntegral_rnDeriv hμ (s := Set.univ)
  rw [Measure.restrict_univ] at this
  rw [← this]
  have h' : ∫⁻ x, μ.rnDeriv lam x ∂lam = ∫⁻ x, ENNReal.ofReal (μ.rnDeriv lam x).toReal ∂lam :=
    lintegral_congr_ae (by
      filter_upwards [Measure.rnDeriv_lt_top μ lam] with x hx
      rw [ENNReal.ofReal_toReal hx.ne])
  rw [h']
  exact hint.lintegral_lt_top

/-- `𝓜²(λ)` is exactly the set of measures `uλ`, `u ≥ 0` in `L²(λ)` — the "if" half. -/
theorem inM2_withDensity_ofReal {u : S → ℝ} (hu : Measurable u) (hu0 : 0 ≤ᵐ[lam] u)
    (h2 : MemLp u 2 lam) : InM2 lam (lam.withDensity fun x => ENNReal.ofReal (u x)) := by
  refine InM2.of_sigmaFinite (withDensity_absolutelyContinuous _ _) ?_
  refine h2.ae_eq ?_
  filter_upwards [Measure.rnDeriv_withDensity lam hu.ennreal_ofReal, hu0] with x hx hx0
  rw [hx, ENNReal.toReal_ofReal hx0]

/-- … and the "only if" half: every `μ ∈ 𝓜²(λ)` is `uλ` with `u = (dμ/dλ).toReal ≥ 0` in
`L²(λ)`. -/
theorem InM2.eq_withDensity_ofReal {μ : Measure S} (hμ : InM2 lam μ) :
    μ = lam.withDensity fun x => ENNReal.ofReal (μ.rnDeriv lam x).toReal := by
  obtain ⟨hfin, hac, -⟩ := hμ
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ lam hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ lam] with x hx
  rw [ENNReal.ofReal_toReal hx.ne]

/-- **`lem:adjoint`(3)**: the density action of a `λ`-reversal pair's `A` maps `𝓜²(λ)` into
itself. -/
theorem IsReversalPair.inM2_comp (h : IsReversalPair lam A B) {μ : Measure S}
    (hμ : InM2 lam μ) : InM2 lam (A ∘ₘ μ) := by
  obtain ⟨hfin, hac, h2⟩ := hμ
  have hA : IsInvariant A lam := h.symm.isInvariant
  have hB : IsInvariant B lam := h.isInvariant
  refine ⟨inferInstance, hA.comp_absolutelyContinuous hac, ?_⟩
  exact (hB.memLp_funAct (by norm_num) h2).ae_eq (h.toReal_rnDeriv_comp hac).symm

/-- **`lem:adjoint`(3)**: the density action is a contraction of `𝓜²(λ)`, in every `L^p(λ)`
density norm, `1 ≤ p ≤ ∞`. -/
theorem IsReversalPair.nrmM_comp_le (h : IsReversalPair lam A B) {μ : Measure S}
    [SigmaFinite μ] (hac : μ ≪ lam) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    nrmM p lam (A ∘ₘ μ) ≤ nrmM p lam μ := by
  have hB : IsInvariant B lam := h.isInvariant
  unfold nrmM
  rw [eLpNorm_congr_ae (h.toReal_rnDeriv_comp hac)]
  exact hB.eLpNorm_funAct_le
    (Measure.measurable_rnDeriv μ lam).ennreal_toReal.aestronglyMeasurable hp

/-- **`lem:adjoint`(3), the adjointness** `⟪μA ∣ ν⟫_λ = ⟪μ ∣ νB⟫_λ` on `𝓜²(λ)`, for a `λ`-reversal
pair `(A, B)`. -/
theorem IsReversalPair.ipM_comp (h : IsReversalPair lam A B) {μ ν : Measure S}
    (hμ : InM2 lam μ) (hν : InM2 lam ν) :
    ipM lam (A ∘ₘ μ) ν = ipM lam μ (B ∘ₘ ν) := by
  obtain ⟨hμf, hμac, hμ2⟩ := hμ
  obtain ⟨hνf, hνac, hν2⟩ := hν
  unfold ipM
  set u := fun x => (μ.rnDeriv lam x).toReal
  set v := fun x => (ν.rnDeriv lam x).toReal
  have e1 := h.toReal_rnDeriv_comp hμac
  have e2 := h.symm.toReal_rnDeriv_comp hνac
  calc ∫ x, ((A ∘ₘ μ).rnDeriv lam x).toReal * v x ∂lam
      = ∫ x, v x * funAct B u x ∂lam := by
        refine integral_congr_ae ?_
        filter_upwards [e1] with x hx
        rw [hx, mul_comm]
    _ = ∫ x, funAct A v x * u x ∂lam := h.integral_mul_funAct (p := 2) (q := 2) hν2 hμ2
    _ = ∫ x, u x * ((B ∘ₘ ν).rnDeriv lam x).toReal ∂lam := by
        refine integral_congr_ae ?_
        filter_upwards [e2] with x hx
        rw [hx, mul_comm]

/-- **`lem:adjoint`(3), operator norm exactly `1`** of the density action on `𝓜²(λ)`: `1` is the least
`c` with `‖μA‖ ≤ c‖μ‖` on `𝓜²(λ)`, attained at `λ` itself. -/
theorem IsReversalPair.isLeast_opNorm_comp (h : IsReversalPair lam A B) (hlam : lam ≠ 0) :
    IsLeast {c : ℝ≥0∞ | ∀ μ : Measure S, InM2 lam μ →
      nrmM 2 lam (A ∘ₘ μ) ≤ c * nrmM 2 lam μ} 1 := by
  have hA : IsInvariant A lam := h.symm.isInvariant
  refine ⟨fun μ hμ => ?_, fun c hc => ?_⟩
  · obtain ⟨hfin, hac, -⟩ := hμ
    simpa using h.nrmM_comp_le hac (le_refl _ |>.trans' (by norm_num) : (1 : ℝ≥0∞) ≤ 2)
  · have hlamM : InM2 lam lam := by
      refine InM2.of_sigmaFinite (Measure.AbsolutelyContinuous.refl lam) ?_
      exact (memLp_const (1 : ℝ)).ae_eq (by
        filter_upwards [Measure.rnDeriv_self lam] with x hx
        simp [hx])
    have h1 := hc lam hlamM
    unfold IsInvariant at hA
    rw [hA] at h1
    have hn : nrmM 2 lam lam = eLpNorm (fun _ : S => (1 : ℝ)) 2 lam := by
      unfold nrmM
      exact eLpNorm_congr_ae (by
        filter_upwards [Measure.rnDeriv_self lam] with x hx
        simp [hx])
    rw [hn] at h1
    have ha0 : eLpNorm (fun _ : S => (1 : ℝ)) 2 lam ≠ 0 := by
      rw [eLpNorm_const _ (by norm_num) hlam]
      simp [hlam]
    have hat : eLpNorm (fun _ : S => (1 : ℝ)) 2 lam ≠ ⊤ := (memLp_const 1).2.ne
    calc (1 : ℝ≥0∞) = eLpNorm (fun _ : S => (1 : ℝ)) 2 lam / eLpNorm (fun _ : S => (1 : ℝ)) 2 lam :=
          (ENNReal.div_self ha0 hat).symm
      _ ≤ c * eLpNorm (fun _ : S => (1 : ℝ)) 2 lam / eLpNorm (fun _ : S => (1 : ℝ)) 2 lam := by
          gcongr
      _ = c := ENNReal.mul_div_cancel_right ha0 hat

end MeasureLevel

section Lemma

variable [StandardBorelSpace S] [Nonempty S] {T : Kernel S S} [IsMarkovKernel T]
  {lam : Measure S} [IsFiniteMeasure lam]

/-- **`lem:adjoint`(3)**: `d(μT)/dλ = T^λ(dμ/dλ)`, `λ`-a.e., for every σ-finite `μ ≪ λ`. -/
theorem IsInvariant.rnDeriv_comp (h : IsInvariant T lam) {μ : Measure S} [SigmaFinite μ]
    (hμ : μ ≪ lam) :
    (T ∘ₘ μ).rnDeriv lam =ᵐ[lam] fun x => ∫⁻ y, μ.rnDeriv lam y ∂(reversal T lam x) :=
  h.isReversalPair_reversal.rnDeriv_comp hμ

/-- **`lem:adjoint`(3)**: `d(μT^λ)/dλ = T(dμ/dλ)`, `λ`-a.e., for every σ-finite `μ ≪ λ`. -/
theorem IsInvariant.rnDeriv_reversal_comp (h : IsInvariant T lam) {μ : Measure S}
    [SigmaFinite μ] (hμ : μ ≪ lam) :
    (reversal T lam ∘ₘ μ).rnDeriv lam =ᵐ[lam] fun x => ∫⁻ y, μ.rnDeriv lam y ∂(T x) :=
  h.isReversalPair_reversal.symm.rnDeriv_comp hμ

/-- **`lem:adjoint`(3)**, function form: `∫ v · T^λ u dλ = ∫ Tv · u dλ` on `L²(λ)`. -/
theorem IsInvariant.integral_mul_funAct_reversal (h : IsInvariant T lam) {u v : S → ℝ}
    (hv : MemLp v 2 lam) (hu : MemLp u 2 lam) :
    ∫ x, v x * funAct (reversal T lam) u x ∂lam = ∫ x, funAct T v x * u x ∂lam :=
  h.isReversalPair_reversal.integral_mul_funAct hv hu

/-- **`lem:adjoint` on a standard Borel space**, items (1)–(3) in one statement. -/
theorem adjoint_general (h : IsInvariant T lam) (hlam : lam ≠ 0) :
    -- (1) the characterizing identity `λ ⊗ T^λ = T ⊗ λ`, and λ-a.e. uniqueness
    IsReversalPair lam T (reversal T lam) ∧
    (∀ η : Kernel S S, IsFiniteKernel η → IsReversalPair lam T η →
      η =ᵐ[lam] reversal T lam) ∧
    -- (2) invariance, the flip identity, the λ-a.e. involution
    IsInvariant (reversal T lam) lam ∧ IsReversalPair lam (reversal T lam) T ∧
    reversal (reversal T lam) lam =ᵐ[lam] T ∧
    -- (3) adjointness on `𝓜²(λ)`, stability of `𝓜²(λ)`, the density/function action identity,
    -- the contractions and the operator norm `1`
    (∀ μ ν : Measure S, InM2 lam μ → InM2 lam ν →
      ipM lam (T ∘ₘ μ) ν = ipM lam μ (reversal T lam ∘ₘ ν)) ∧
    (∀ μ : Measure S, InM2 lam μ → InM2 lam (T ∘ₘ μ) ∧ InM2 lam (reversal T lam ∘ₘ μ)) ∧
    (∀ μ : Measure S, InM2 lam μ →
      (T ∘ₘ μ).rnDeriv lam =ᵐ[lam] (fun x => ∫⁻ y, μ.rnDeriv lam y ∂(reversal T lam x)) ∧
      (reversal T lam ∘ₘ μ).rnDeriv lam =ᵐ[lam] (fun x => ∫⁻ y, μ.rnDeriv lam y ∂(T x))) ∧
    IsLeast {c : ℝ≥0∞ | ∀ μ : Measure S, InM2 lam μ →
      nrmM 2 lam (T ∘ₘ μ) ≤ c * nrmM 2 lam μ} 1 ∧
    IsLeast {c : ℝ≥0∞ | ∀ μ : Measure S, InM2 lam μ →
      nrmM 2 lam (reversal T lam ∘ₘ μ) ≤ c * nrmM 2 lam μ} 1 := by
  have hp := h.isReversalPair_reversal
  refine ⟨hp, fun η _ hη => h.ae_eq_reversal hη, h.isInvariant_reversal, hp.symm,
    h.reversal_reversal, fun μ ν hμ hν => hp.ipM_comp hμ hν,
    fun μ hμ => ⟨hp.inM2_comp hμ, hp.symm.inM2_comp hμ⟩, fun μ hμ => ?_,
    hp.isLeast_opNorm_comp hlam, hp.symm.isLeast_opNorm_comp hlam⟩
  obtain ⟨hfin, hac, -⟩ := hμ
  exact ⟨h.rnDeriv_comp hac, h.rnDeriv_reversal_comp hac⟩

end Lemma

section Finite

/-! ### The finite instance: the general reversal is the entrywise division

On a finite (or countable) discrete space, the characterizing identity read at `{x} × {y}` gives
`λ{x} T^λ(x → {y}) = λ{y} T(y → {x})`, i.e. item (4)'s formula
`T^λ(x → y) = λ(y) T(y → x)/λ(x)` wherever `λ{x} ≠ 0`. -/

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [StandardBorelSpace V]
  [Nonempty V] {T : Kernel V V} [IsMarkovKernel T] {lam : Measure V} [IsFiniteMeasure lam]

/-- The characterizing identity read on atoms. -/
theorem IsInvariant.reversal_singleton_mul (h : IsInvariant T lam) (x y : V) :
    lam {x} * reversal T lam x {y} = lam {y} * T y {x} := by
  have hp : (lam ⊗ₘ reversal T lam) ({x} ×ˢ {y}) = ((lam ⊗ₘ T).map Prod.swap) ({x} ×ˢ {y}) := by
    rw [h.isReversalPair_reversal]
  rw [Measure.compProd_apply_prod (measurableSet_singleton x) (measurableSet_singleton y),
    Measure.map_apply measurable_swap
      ((measurableSet_singleton x).prod (measurableSet_singleton y)),
    Set.preimage_swap_prod,
    Measure.compProd_apply_prod (measurableSet_singleton y) (measurableSet_singleton x),
    Measure.restrict_singleton, Measure.restrict_singleton] at hp
  simpa [lintegral_smul_measure, mul_comm] using hp

/-- **`lem:adjoint`(4)'s entrywise formula for the general reversal**: where `λ{x} ≠ 0`,
`T^λ(x → {y}) = λ{y} T(y → {x}) / λ{x}`. -/
theorem IsInvariant.reversal_singleton (h : IsInvariant T lam) {x : V} (hx : lam {x} ≠ 0)
    (y : V) : reversal T lam x {y} = lam {y} * T y {x} / lam {x} := by
  rw [← h.reversal_singleton_mul x y, mul_comm, ENNReal.mul_div_cancel_right hx
    (measure_ne_top lam _)]

/-- **`lem:adjoint`(4), bridge to the finite library** (`GFNBounds/Core/Adjoint.lean`): read through real masses
`λ(v) := λ{v}` and the matrix `T(a → b) := T(a → {b})`, the general reversal is the finite one,
`GFNBounds.Core.reversal`, at every `λ`-charged `x`. -/
theorem IsInvariant.toReal_reversal_singleton (h : IsInvariant T lam) {x : V}
    (hx : lam {x} ≠ 0) (y : V) :
    (reversal T lam x {y}).toReal =
      GFNBounds.Core.reversal (fun v => (lam {v}).toReal) (fun a b => (T a {b}).toReal) x y := by
  rw [h.reversal_singleton hx, GFNBounds.Core.reversal_apply, ENNReal.toReal_div,
    ENNReal.toReal_mul]

end Finite

end GFNBounds.Core.General
