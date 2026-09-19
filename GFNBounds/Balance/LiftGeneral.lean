import GFNBounds.Core.Kernel
import Mathlib.Probability.Kernel.Posterior

/-!
# The edge lift on a general measurable space: `K₂`, `λ₂`, and the duality `λ₂ ⊗ K₂* = K₂ ⊗ λ₂`

**`def:edge_lift`** — `proofs.tex`, the `definition` carrying that label (`:514–520` when written).
**`lem:lift_wellposed`** — statement `proofs.tex:522–524`, proof `:526–532` when written.
(Line numbers drift, kb `0036`; the label is the anchor.)

> (`def:edge_lift`) Let `π_←` be a backward policy on `(𝒮, λ)` with `λ` `π_←`-invariant. The
> *edge lift* of `π_←` is the Markov kernel `K₂` on `𝒮²` given by `K₂ : (s,s') ↦ (π_←(s), s)`,
> i.e. the current edge is shifted one `π_←`-step backward along the trajectory. The *edge
> measure* is `λ₂(ds ds') := π_←(s' → ds) λ(ds')`.

> (`lem:lift_wellposed`) `λ₂` is `K₂`-invariant, `K₂` is a contraction of `𝓜²(λ₂)`, and the
> `𝓜²(λ₂)`-dual of `K₂` is the edge lift `(s,s') ↦ (s', π_→^λ(s'))` of the dual forward policy
> `π_→^λ = π_←^λ`.

`GFNBounds/Balance/Lift.lean` proves both on a `Fintype`. This file is the general form the
paper states, on a measurable space `𝒮`, built on Mathlib's kernels: `K₂` is the product kernel
`(π_← ∘ pr₁) ×ₖ δ_{pr₁}`, `λ₂` is `(λ ⊗ₘ π_←).map swap`, and the dual forward policy is
Mathlib's posterior `π_←†λ` — the disintegration of `π_← ⊗ λ` over its first marginal
`λπ_← = λ`, which is how `lem:adjoint`*(1)* defines the `λ`-reversal.

## Conventions

The paper's `(λ ⊗ A)(dx dy) = λ(dx)A(x → dy)` is Mathlib's `λ ⊗ₘ A`; its
`(A ⊗ λ)(dx dy) = A(y → dx)λ(dy)` is `(λ ⊗ₘ A).map Prod.swap`. So `λ₂ = π_← ⊗ λ`, and
`IsReversal A R ρ := ρ ⊗ₘ R = (ρ ⊗ₘ A).map Prod.swap` is the paper's `ρ ⊗ R = A ⊗ ρ` verbatim.
The measure action `μ ↦ μK` is `μ.bind K` (`= K ∘ₘ μ`), as in `GFNBounds.Core.Kernel`. The
`𝓜²(ρ)` pairing `⟪μ ∣ ν⟫_ρ = ∫ (dμ/dρ)(dν/dρ) dρ` is carried by `Measure.rnDeriv`.

## The one idea that avoids disintegration in the contraction

The paper argues the contraction through the forward conditional `π_→^λ` ("the map
`dμ/dλ₂ ↦ d(m₁μ)/dλ` is the conditional expectation given the first coordinate"). Here it is
`lintegral_rnDeriv_map_sq_le`, for **any** measurable map `φ` and finite `μ ≪ ρ`:
`∫ (d(φ_*μ)/d(φ_*ρ))² d(φ_*ρ) ≤ ∫ (dμ/dρ)² dρ`, proved by testing the truncation `w ∧ n` of the
image density against `w` itself and applying Cauchy–Schwarz — no conditional kernel, no
standard-Borel hypothesis. With `φ = pr₁`, `eq:muK2_density` (`rnDeriv_bind_edgeLift`) and "both
marginals of `λ₂` equal `λ`" it is the contraction. Only the *dual* needs the reversal.

## What is proved

| | |
|---|---|
| `edgeLift`, `edgeLift_apply`, the `IsMarkovKernel` instance | **`def:edge_lift`**: `K₂(s,s') = π_←(s → ·) ⊗ δ_s`, a Markov kernel on `𝒮²` |
| `edgeMeasure`, `lintegral_edgeMeasure` | **`def:edge_lift`**: `λ₂(ds ds') = π_←(s' → ds)λ(ds')` |
| `edgeLift_apply_singleton` | agreement with the finite form: `K₂((s,s') → {(z,w)}) = [w = s]·π_←(s → {z})` |
| `fst_edgeMeasure`, `snd_edgeMeasure` | the marginals: `m₁λ₂ = λπ_←` (`= λ` under invariance), `m₂λ₂ = λ` |
| `bind_edgeLift` | `μK₂ = π_← ⊗ (m₁μ)` for every s-finite `μ` — the first display of the proof |
| `rnDeriv_bind_edgeLift`, `bind_edgeLift_eq_withDensity` | **`eq:muK2_density`**: `d(μK₂)/dλ₂ (s,s') = d(m₁μ)/dλ (s')` `λ₂`-a.e., for finite `μ ≪ λ₂` |
| `edgeMeasure_invariant` | **invariance**: `λ₂K₂ = λ₂` |
| `bind_edgeLift_absolutelyContinuous`, `edgeLift_contraction` | **contraction**: `μK₂ ≪ λ₂` and `‖μK₂‖²_{𝓜²(λ₂)} ≤ ‖μ‖²_{𝓜²(λ₂)}` |
| `edgeLiftDual`, `edgeLift_duality` | **the dual**: for every `λ`-reversal `R` of `π_←`, `K₂* = (s,s') ↦ (s', R(s'))` satisfies `λ₂ ⊗ K₂* = K₂ ⊗ λ₂` |
| `edgeLift_reversal_unique` | … and is the `λ₂`-a.e. unique kernel doing so (countably generated `𝒮`) |
| `edgeMeasure_invariant_dual` | `λ₂K₂* = λ₂` |
| `edgeLift_adjoint`, `edgeLift_adjoint_real` | **adjointness**: `⟪μK₂ ∣ ν⟫_{λ₂} = ⟪μ ∣ νK₂*⟫_{λ₂}`, in `ℝ≥0∞` and in the real pairing |
| `lift_wellposed` | **`lem:lift_wellposed` whole**, on a standard Borel `𝒮`, with `π_→^λ := π_←†λ` constructed |
| `IsReversal`, `.bind_eq`, `.bind_eq_left`, `.flip`, `.ae_eq`, `isReversal_posterior`, `adjoint_of_isReversal` | the general-space `λ`-reversal facts the dual consumes (see SCOPE) |
| `lintegral_rnDeriv_map_sq_le` | conditional Jensen for image densities, by Cauchy–Schwarz |
| `isFiniteMeasure_withDensity_of_sq` | an `𝓜²(ρ)` measure over a finite `ρ` is finite: the `IsFiniteMeasure μ` binders are implied by membership |
| `isReversal_const` | non-vacuity on every measurable space: `x ↦ ρ` is `ρ`-invariant and self-reversing |

## SCOPE (disclosed)

* **The state space.** Everything except the *construction* of `π_→^λ` and the *uniqueness* of
  the dual holds on an arbitrary measurable space, with the reversal `R` of `π_←` taken as a
  hypothesis `IsReversal T R lam` — the paper's characterizing identity, not an extra assumption
  about `R`. Existence of `R` (`isReversal_posterior`) needs `[StandardBorelSpace 𝒮] [Nonempty 𝒮]`,
  and uniqueness needs `[MeasurableSpace.CountablyGenerated 𝒮]`; the paper's `𝒮` is Polish
  (`lem:adjoint`), which with its Borel σ-algebra gives both (the empty space being the one
  Polish space the `Nonempty` binder excludes, where every measure is `0` and the lemma is empty).
  `lift_wellposed` assembles the lemma on a standard Borel `𝒮`.
* **`λ` finite** (`[IsFiniteMeasure lam]`), as the paper's conventions fix for every invariant
  measure (`proofs.tex`, "Four measures": "assumed to exist, non-zero and finite"). Non-zero is
  never used.
* **`𝓜²(λ₂)` is read as the paper defines it**: the *non-negative* measures dominated by `λ₂`
  with square-integrable density (`proofs.tex`, "Four measures"). The results quantify over finite
  `μ ≪ λ₂` — every `𝓜²(λ₂)` measure is one, by `isFiniteMeasure_withDensity_of_sq` — and the
  norm is stated squared, as `∫⁻ (dμ/dλ₂)² dλ₂ : ℝ≥0∞`; `edgeLift_contraction` holds whether or
  not that norm is finite, and in particular maps `𝓜²(λ₂)` into itself. No signed-measure or
  `Lp`-quotient form is stated.
* **"The `𝓜²(λ₂)`-dual" is delivered as the paper's proof delivers it**: `K₂*` is the
  `λ₂`-reversal of `K₂` (`edgeLift_duality`, with a.e. uniqueness `edgeLift_reversal_unique`, the
  paper's appeal to `lem:adjoint`*(1)*), and its density action satisfies the adjoint identity
  (`edgeLift_adjoint`, the paper's appeal to `lem:adjoint`*(3)*). The Riesz step "the only map
  satisfying this identity is the adjoint" is not formalized, as in `GFNBounds/Core/Adjoint.lean`.
* **`lem:adjoint` itself is not certified here.** The general-space reversal facts this file
  needs (`IsReversal.*`, `isReversal_posterior`, `adjoint_of_isReversal`) are proved locally,
  in the paper's form, because the general `lem:adjoint` layer is not in the library at this
  commit (`GFNBounds/Core/Adjoint.lean` is finite). They cover `lem:adjoint`*(1)*, *(2)* and
  the adjoint identity of *(3)* for non-negative measures; the contraction and "operator norm 1"
  of *(3)* and item *(4)* are not attempted. Whether they are merged with a general `lem:adjoint`
  file is the master's call.
* **The window lift `K_ℓ`, `ℓ ≥ 3`, is absent — as it is from the paper since 2026-09-14.**

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒮` a measurable space (Polish in `lem:adjoint`) | ✓ any `MeasurableSpace S` for `def:edge_lift`, invariance, contraction, duality given `R`, adjointness; `StandardBorelSpace` + `Nonempty` for constructing `π_→^λ`; `CountablyGenerated` for uniqueness. Polish ⇒ all three |
| `π_←` a backward policy = a Markov kernel on `𝒮` | ✓ `T : Kernel S S`, `[IsMarkovKernel T]` |
| `λ` `π_←`-invariant | ✓ `hinv : lam.bind T = lam`; `bind_edgeLift`, `snd_edgeMeasure` and `edgeLift_duality` do not need it (the last gets it from `IsReversal`, `IsReversal.bind_eq_left`) |
| `λ` finite, non-zero | ⚠ finite carried; non-zero unused |
| `K₂ : (s,s') ↦ (π_←(s), s)` | ✓ `edgeLift`, defined, proved Markov |
| `λ₂(ds ds') = π_←(s' → ds)λ(ds')` | ✓ `edgeMeasure` |
| `μ ∈ 𝓜²(λ₂)` | ✓ as the paper defines `𝓜²` (non-negative); carried as `[IsFiniteMeasure μ]`, `μ ≪ λ₂` — implied by membership (`isFiniteMeasure_withDensity_of_sq`) |
| `π_→^λ = π_←^λ` the dual forward policy | ✓ **constructed** as `T†lam` (standard Borel) with `λ ⊗ π_→^λ = π_← ⊗ λ` proved; in the general results any `R` with that identity |
| `K₂^*(s,s') := (s', π_→^λ(s'))` | ✓ `edgeLiftDual R`, `(s,s') ↦ δ_{s'} ⊗ R(s')` |
| conclusion: `λ₂ ⊗ K₂^* = K₂ ⊗ λ₂` | ✓ `edgeLift_duality`, in the paper's orientation (`Lift.lean`'s `edgeKernel_dual` states the equivalent flipped identity `λ₂ ⊗ K₂ = K₂* ⊗ λ₂`; `IsReversal.flip` converts between the two) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance.LiftGeneral

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- **`def:edge_lift`, the kernel**: the edge lift `K₂ : (s,s') ↦ (π_←(s), s)`, i.e. the law
`π_←(s → ·) ⊗ δ_s` on `𝒮²` — the current edge shifted one `π_←`-step backward. -/
noncomputable def edgeLift (T : Kernel S S) [IsSFiniteKernel T] : Kernel (S × S) (S × S) :=
  (T.comap Prod.fst measurable_fst) ×ₖ Kernel.deterministic Prod.fst measurable_fst

instance (T : Kernel S S) [IsMarkovKernel T] : IsMarkovKernel (edgeLift T) := by
  unfold edgeLift; infer_instance

/-- **`def:edge_lift`, "the Markov kernel `K₂` on `𝒮²`"**: `K₂` is Markov when `π_←` is. -/
theorem edgeLift_isMarkovKernel (T : Kernel S S) [IsMarkovKernel T] :
    IsMarkovKernel (edgeLift T) := inferInstance

theorem edgeLift_apply (T : Kernel S S) [IsSFiniteKernel T] (x : S × S) :
    edgeLift T x = (T x.1).map (fun z => (z, x.1)) := by
  rw [edgeLift, Kernel.prod_apply, Kernel.comap_apply, Kernel.deterministic_apply,
    Measure.prod_dirac]

/-- **`def:edge_lift`, the edge measure**: `λ₂(ds ds') := π_←(s' → ds) λ(ds')`, i.e. the law of
the backward pair `(s, s')` with `s' ∼ λ` and `s ∼ π_←(s' → ·)`. -/
noncomputable def edgeMeasure (T : Kernel S S) (lam : Measure S) : Measure (S × S) :=
  (lam ⊗ₘ T).map Prod.swap

theorem lintegral_edgeLift (T : Kernel S S) [IsSFiniteKernel T] (x : S × S)
    {f : S × S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(edgeLift T x) = ∫⁻ z, f (z, x.1) ∂(T x.1) := by
  rw [edgeLift_apply, lintegral_map hf (by fun_prop)]

theorem lintegral_edgeMeasure (T : Kernel S S) [IsSFiniteKernel T] (lam : Measure S) [SFinite lam]
    {f : S × S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(edgeMeasure T lam) = ∫⁻ s', ∫⁻ s, f (s, s') ∂(T s') ∂lam := by
  rw [edgeMeasure, lintegral_map hf measurable_swap]
  exact Measure.lintegral_compProd (f := fun p => f p.swap) (hf.comp measurable_swap)

/-- **`lem:lift_wellposed`, the push identity of its proof**: `μK₂(ds ds') = π_←(s' → ds)(m₁μ)(ds')`, i.e. the push of
any s-finite `μ` on `𝒮²` through `K₂` is the edge measure of its first marginal. -/
theorem bind_edgeLift (T : Kernel S S) [IsSFiniteKernel T] (μ : Measure (S × S)) [SFinite μ] :
    μ.bind (edgeLift T) = edgeMeasure T μ.fst := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hg : Measurable fun s => ∫⁻ z, f (z, s) ∂(T s) :=
    Measurable.lintegral_kernel_prod_right' (κ := T) (f := fun p => f (p.2, p.1))
      (hf.comp measurable_swap)
  rw [Measure.lintegral_bind (edgeLift T).aemeasurable hf.aemeasurable,
    lintegral_edgeMeasure T _ hf, Measure.fst, lintegral_map hg measurable_fst]
  exact lintegral_congr fun x => lintegral_edgeLift T x hf

/-- The first marginal of `λ₂` is `λπ_←`. -/
theorem fst_edgeMeasure (T : Kernel S S) [IsSFiniteKernel T] (lam : Measure S) [SFinite lam] :
    (edgeMeasure T lam).fst = lam.bind T := by
  rw [edgeMeasure, Measure.fst_map_swap, Measure.snd_compProd]

/-- The second marginal of `λ₂` is `λ`, by row-stochasticity alone. -/
theorem snd_edgeMeasure (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [SFinite lam] :
    (edgeMeasure T lam).snd = lam := by
  rw [edgeMeasure, Measure.snd_map_swap, Measure.fst_compProd]

instance (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam] :
    IsFiniteMeasure (edgeMeasure T lam) := by
  unfold edgeMeasure; infer_instance

/-- **`lem:lift_wellposed`, invariance**: `λ₂ K₂ = λ₂` when `λπ_← = λ`. -/
theorem edgeMeasure_invariant (T : Kernel S S) [IsSFiniteKernel T] (lam : Measure S) [SFinite lam]
    (hinv : lam.bind T = lam) :
    (edgeMeasure T lam).bind (edgeLift T) = edgeMeasure T lam := by
  have : SFinite (edgeMeasure T lam) := by unfold edgeMeasure; infer_instance
  rw [bind_edgeLift, fst_edgeMeasure, hinv]

/-- Weighting `λ` by a density `w` weights `λ₂` by `w` read at the second coordinate. -/
theorem edgeMeasure_withDensity (T : Kernel S S) [IsSFiniteKernel T] (lam : Measure S)
    [SFinite lam] {w : S → ℝ≥0∞} (hw : Measurable w) :
    edgeMeasure T (lam.withDensity w) = (edgeMeasure T lam).withDensity (fun p => w p.2) := by
  have : SFinite (lam.withDensity w) := inferInstance
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hg : Measurable fun s => ∫⁻ z, f (z, s) ∂(T s) :=
    Measurable.lintegral_kernel_prod_right' (κ := T) (f := fun p => f (p.2, p.1))
      (hf.comp measurable_swap)
  rw [lintegral_edgeMeasure T _ hf, lintegral_withDensity_eq_lintegral_mul _ hw hg,
    lintegral_withDensity_eq_lintegral_mul _ (f := fun p : S × S => w p.2)
      (hw.comp measurable_snd) hf,
    lintegral_edgeMeasure T _ (f := (fun p : S × S => w p.2) * f)
      ((hw.comp measurable_snd).mul hf)]
  refine lintegral_congr fun s' => ?_
  simp only [Pi.mul_apply]
  rw [lintegral_const_mul _ (f := fun z => f (z, s'))
    (hf.comp (measurable_id.prodMk measurable_const))]

/-! ### Pushing forward is an `L²` contraction on densities -/

/-- From `A ≤ √B·√A` with `A < ∞`, `A ≤ B`. -/
theorem le_of_le_sqrt_mul_sqrt {A B : ℝ≥0∞} (hA : A ≠ ∞)
    (h : A ≤ B ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) : A ≤ B := by
  set a := A ^ (1 / 2 : ℝ) with ha
  set b := B ^ (1 / 2 : ℝ) with hb
  have hsqA : a * a = A := by
    rw [ha, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  have hsqB : b * b = B := by
    rw [hb, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  by_cases h0 : a = 0
  · rw [← hsqA, h0, zero_mul]; exact zero_le
  have htop : a ≠ ∞ := by
    rw [ha]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA
  have hab : a ≤ b := by
    rw [← hsqA] at h
    exact (ENNReal.mul_le_mul_iff_left h0 htop).1 h
  rw [← hsqA, ← hsqB]; exact mul_le_mul' hab hab

/-- **Conditional Jensen, by Cauchy–Schwarz.** For finite `μ ≪ ρ` and a measurable `φ`, the
density of the image `φ_*μ` against `φ_*ρ` has `L²(φ_*ρ)` norm at most that of `dμ/dρ` in
`L²(ρ)`. No disintegration is used: the truncation `w ⊓ n` is tested against `w` itself. -/
theorem lintegral_rnDeriv_map_sq_le {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (ρ μ : Measure X) [IsFiniteMeasure ρ] [IsFiniteMeasure μ] (hμ : μ ≪ ρ) {φ : X → Z}
    (hφ : Measurable φ) :
    ∫⁻ z, ((μ.map φ).rnDeriv (ρ.map φ) z) ^ 2 ∂(ρ.map φ) ≤ ∫⁻ x, (μ.rnDeriv ρ x) ^ 2 ∂ρ := by
  set w := (μ.map φ).rnDeriv (ρ.map φ) with hw_def
  set u := μ.rnDeriv ρ with hu_def
  have hw : Measurable w := Measure.measurable_rnDeriv _ _
  have hu : Measurable u := Measure.measurable_rnDeriv _ _
  have hac : μ.map φ ≪ ρ.map φ := hμ.map hφ
  -- the truncations
  have key : ∀ n : ℕ, ∫⁻ z, (w z ⊓ (n : ℝ≥0∞)) ^ 2 ∂(ρ.map φ) ≤ ∫⁻ x, u x ^ 2 ∂ρ := by
    intro n
    set g : Z → ℝ≥0∞ := fun z => w z ⊓ (n : ℝ≥0∞) with hg_def
    have hg : Measurable g := hw.inf measurable_const
    set A := ∫⁻ z, g z ^ 2 ∂(ρ.map φ) with hA_def
    have hAfin : A ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _z, ((n : ℝ≥0∞)) ^ 2 ∂(ρ.map φ)) ?_ ?_
      · rw [lintegral_const]
        exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
      · exact lintegral_mono fun z => pow_le_pow_left' inf_le_right 2
    have h1 : A ≤ ∫⁻ z, w z * g z ∂(ρ.map φ) := by
      refine lintegral_mono fun z => ?_
      rw [sq]; exact mul_le_mul_left (inf_le_left : g z ≤ w z) (g z)
    have h2 : ∫⁻ z, w z * g z ∂(ρ.map φ) = ∫⁻ x, u x * g (φ x) ∂ρ := by
      rw [lintegral_rnDeriv_mul hac hg.aemeasurable, lintegral_map hg hφ]
      exact (lintegral_rnDeriv_mul hμ (f := fun x => g (φ x)) (hg.comp hφ).aemeasurable).symm
    have h3 : ∫⁻ x, u x * g (φ x) ∂ρ ≤
        (∫⁻ x, u x ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ) * (∫⁻ x, g (φ x) ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two hu.aemeasurable
        (hg.comp hφ).aemeasurable
    have h4 : ∫⁻ x, g (φ x) ^ (2 : ℝ) ∂ρ = A := by
      rw [hA_def, lintegral_map (hg.pow_const 2) hφ]
      simp only [ENNReal.rpow_two]
    have h5 : ∫⁻ x, u x ^ (2 : ℝ) ∂ρ = ∫⁻ x, u x ^ 2 ∂ρ := by
      simp only [ENNReal.rpow_two]
    rw [h4, h5] at h3
    exact le_of_le_sqrt_mul_sqrt hAfin (h1.trans (h2.le.trans h3))
  have hlim : ∀ z, w z ^ 2 = ⨆ n : ℕ, (w z ⊓ (n : ℝ≥0∞)) ^ 2 := by
    intro z
    have h1 : ⨆ n : ℕ, w z ⊓ (n : ℝ≥0∞) = w z := by
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    conv_lhs => rw [← h1]
    exact ENNReal.iSup_pow _ 2
  calc ∫⁻ z, w z ^ 2 ∂(ρ.map φ)
      = ∫⁻ z, ⨆ n : ℕ, (w z ⊓ (n : ℝ≥0∞)) ^ 2 ∂(ρ.map φ) := lintegral_congr fun z => hlim z
    _ = ⨆ n : ℕ, ∫⁻ z, (w z ⊓ (n : ℝ≥0∞)) ^ 2 ∂(ρ.map φ) := by
        refine lintegral_iSup (fun n => (hw.inf measurable_const).pow_const 2) ?_
        intro a b hab z
        exact pow_le_pow_left' (inf_le_inf_left _ (by exact_mod_cast hab)) 2
    _ ≤ ∫⁻ x, u x ^ 2 ∂ρ := iSup_le key

/-! ### The density of `μK₂`, and the contraction -/

section Density

variable (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam]

/-- `m₁μ ≪ λ` for every `μ ≪ λ₂`, the first marginal of `λ₂` being `λπ_← = λ`. -/
theorem fst_absolutelyContinuous (hinv : lam.bind T = lam) {μ : Measure (S × S)}
    (hμ : μ ≪ edgeMeasure T lam) : μ.fst ≪ lam := by
  have h := hμ.map (measurable_fst (α := S) (β := S))
  rwa [← Measure.fst, ← Measure.fst, fst_edgeMeasure, hinv] at h

/-- **`lem:lift_wellposed`, `eq:muK2_density` as a measure identity**: `μK₂ = (d(m₁μ)/dλ)(s') · λ₂`. -/
theorem bind_edgeLift_eq_withDensity (hinv : lam.bind T = lam) (μ : Measure (S × S))
    [IsFiniteMeasure μ] (hμ : μ ≪ edgeMeasure T lam) :
    μ.bind (edgeLift T) =
      (edgeMeasure T lam).withDensity (fun p => μ.fst.rnDeriv lam p.2) := by
  rw [bind_edgeLift, ← edgeMeasure_withDensity T lam (Measure.measurable_rnDeriv _ _),
    Measure.withDensity_rnDeriv_eq _ _ (fst_absolutelyContinuous T lam hinv hμ)]

/-- `μK₂ ≪ λ₂`: `K₂` maps `𝓜(λ₂)` into itself. -/
theorem bind_edgeLift_absolutelyContinuous (hinv : lam.bind T = lam) (μ : Measure (S × S))
    [IsFiniteMeasure μ] (hμ : μ ≪ edgeMeasure T lam) :
    μ.bind (edgeLift T) ≪ edgeMeasure T lam := by
  rw [bind_edgeLift_eq_withDensity T lam hinv μ hμ]
  exact withDensity_absolutelyContinuous _ _

/-- **`lem:lift_wellposed`, `eq:muK2_density` verbatim**: `d(μK₂)/dλ₂ (s,s') = d(m₁μ)/dλ (s')`, `λ₂`-a.e. -/
theorem rnDeriv_bind_edgeLift (hinv : lam.bind T = lam) (μ : Measure (S × S))
    [IsFiniteMeasure μ] (hμ : μ ≪ edgeMeasure T lam) :
    (μ.bind (edgeLift T)).rnDeriv (edgeMeasure T lam)
      =ᵐ[edgeMeasure T lam] fun p => μ.fst.rnDeriv lam p.2 := by
  rw [bind_edgeLift_eq_withDensity T lam hinv μ hμ]
  exact Measure.rnDeriv_withDensity _ ((Measure.measurable_rnDeriv _ _).comp measurable_snd)

/-- **`lem:lift_wellposed`, contraction**: `‖μK₂‖_{𝓜²(λ₂)} ≤ ‖μ‖_{𝓜²(λ₂)}`, in squared
`ℝ≥0∞` form (so that it also says: `μ ∈ 𝓜²(λ₂) ⇒ μK₂ ∈ 𝓜²(λ₂)`). -/
theorem edgeLift_contraction (hinv : lam.bind T = lam) (μ : Measure (S × S))
    [IsFiniteMeasure μ] (hμ : μ ≪ edgeMeasure T lam) :
    ∫⁻ p, ((μ.bind (edgeLift T)).rnDeriv (edgeMeasure T lam) p) ^ 2 ∂(edgeMeasure T lam)
      ≤ ∫⁻ p, (μ.rnDeriv (edgeMeasure T lam) p) ^ 2 ∂(edgeMeasure T lam) := by
  have hw : Measurable fun s => (μ.fst.rnDeriv lam s) ^ 2 :=
    (Measure.measurable_rnDeriv _ _).pow_const 2
  calc ∫⁻ p, ((μ.bind (edgeLift T)).rnDeriv (edgeMeasure T lam) p) ^ 2 ∂(edgeMeasure T lam)
      = ∫⁻ p, (μ.fst.rnDeriv lam p.2) ^ 2 ∂(edgeMeasure T lam) := by
        refine lintegral_congr_ae ?_
        filter_upwards [rnDeriv_bind_edgeLift T lam hinv μ hμ] with p hp
        rw [hp]
    _ = ∫⁻ s, (μ.fst.rnDeriv lam s) ^ 2 ∂lam := by
        have h := lintegral_map hw (measurable_snd (α := S) (β := S)) (μ := edgeMeasure T lam)
        rw [← Measure.snd, snd_edgeMeasure] at h
        exact h.symm
    _ = ∫⁻ s, (μ.fst.rnDeriv (edgeMeasure T lam).fst s) ^ 2 ∂(edgeMeasure T lam).fst := by
        rw [fst_edgeMeasure, hinv]
    _ ≤ ∫⁻ p, (μ.rnDeriv (edgeMeasure T lam) p) ^ 2 ∂(edgeMeasure T lam) :=
        lintegral_rnDeriv_map_sq_le _ _ hμ measurable_fst

end Density

/-! ### The `λ`-reversal, abstractly and on a standard Borel space -/

section Reversal

variable {X : Type*} [MeasurableSpace X]

/-- `R` is a `ρ`-reversal of `A`: `ρ ⊗ R = A ⊗ ρ` in the paper's notation, i.e.
`ρ(dx)R(x → dy) = A(y → dx)ρ(dy)` — `lem:adjoint`*(1)*'s characterizing identity. -/
def IsReversal (A R : Kernel X X) (ρ : Measure X) : Prop :=
  ρ ⊗ₘ R = (ρ ⊗ₘ A).map Prod.swap

/-- A reversal leaves `ρ` invariant (`lem:adjoint`*(2)*, first half). -/
theorem IsReversal.bind_eq {A R : Kernel X X} [IsMarkovKernel A] [IsMarkovKernel R]
    {ρ : Measure X} [SFinite ρ] (h : IsReversal A R ρ) : ρ.bind R = ρ := by
  have := congrArg Measure.snd h
  rwa [Measure.snd_compProd, Measure.snd_map_swap, Measure.fst_compProd] at this

/-- A Markov kernel with a Markov reversal leaves `ρ` invariant. -/
theorem IsReversal.bind_eq_left {A R : Kernel X X} [IsMarkovKernel A] [IsMarkovKernel R]
    {ρ : Measure X} [SFinite ρ] (h : IsReversal A R ρ) : ρ.bind A = ρ := by
  have := congrArg Measure.fst h
  rwa [Measure.fst_compProd, Measure.fst_map_swap, Measure.snd_compProd, eq_comm] at this

/-- Reversal is symmetric (`lem:adjoint`*(2)*, `eq:reversal_flip`): if `R` reverses `A` then
`A` reverses `R`. -/
theorem IsReversal.flip {A R : Kernel X X} {ρ : Measure X} (h : IsReversal A R ρ) :
    IsReversal R A ρ := by
  unfold IsReversal at *
  rw [h, Measure.map_map measurable_swap measurable_swap]
  simp [Function.comp_def, Prod.swap_swap, Measure.map_id']

/-- `λ`-a.e. uniqueness of the reversal (`lem:adjoint`*(1)*), on a countably generated space. -/
theorem IsReversal.ae_eq [MeasurableSpace.CountablyGenerated X] {A R R' : Kernel X X}
    [IsFiniteKernel R] [IsFiniteKernel R'] {ρ : Measure X} [IsFiniteMeasure ρ]
    (h : IsReversal A R ρ) (h' : IsReversal A R' ρ) : R =ᵐ[ρ] R' :=
  Kernel.ae_eq_of_compProd_eq (Eq.trans h (Eq.symm h'))

/-- **Existence of the `λ`-reversal** on a standard Borel space (`lem:adjoint`*(1)*): Mathlib's
posterior `A†ρ` — the disintegration of `(ρ ⊗ A).map swap` over its first marginal
`ρA = ρ` — is a Markov kernel reversing `A`. -/
theorem isReversal_posterior [StandardBorelSpace X] [Nonempty X] (A : Kernel X X)
    [IsMarkovKernel A] (ρ : Measure X) [IsFiniteMeasure ρ] (hinv : ρ.bind A = ρ) :
    IsReversal A (A†ρ) ρ := by
  have h := compProd_posterior_eq_map_swap (κ := A) (μ := ρ)
  rwa [show A ∘ₘ ρ = ρ from hinv] at h

/-- The density/density pairing of `μA` against `ν`, as an integral against `ρ ⊗ A`. -/
theorem lintegral_rnDeriv_bind_mul (A : Kernel X X) [IsMarkovKernel A] (ρ : Measure X)
    [IsFiniteMeasure ρ] (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ ≪ ρ)
    (hAμ : μ.bind A ≪ ρ) {v : X → ℝ≥0∞} (hv : Measurable v) :
    ∫⁻ x, (μ.bind A).rnDeriv ρ x * v x ∂ρ
      = ∫⁻ p, μ.rnDeriv ρ p.1 * v p.2 ∂(ρ ⊗ₘ A) := by
  have hu : Measurable (μ.rnDeriv ρ) := Measure.measurable_rnDeriv _ _
  have hAv : Measurable fun x => ∫⁻ y, v y ∂(A x) := hv.lintegral_kernel
  rw [lintegral_rnDeriv_mul hAμ hv.aemeasurable,
    Measure.lintegral_bind A.aemeasurable hv.aemeasurable,
    ← lintegral_rnDeriv_mul hμ hAv.aemeasurable,
    Measure.lintegral_compProd (f := fun p : X × X => μ.rnDeriv ρ p.1 * v p.2)
      ((hu.comp measurable_fst).mul (hv.comp measurable_snd))]
  exact lintegral_congr fun x => (lintegral_const_mul _ hv).symm

/-- **`lem:adjoint`*(3)*, adjointness, on a general measurable space.** If `R` is a
`ρ`-reversal of `A` and `ρA = ρ`, then for all finite `μ, ν ≪ ρ`
`⟪μA ∣ ν⟫_ρ = ⟪μ ∣ νR⟫_ρ`, the pairing `⟪μ ∣ ν⟫_ρ = ∫ (dμ/dρ)(dν/dρ) dρ` taken in `ℝ≥0∞`
(so with no integrability hypothesis at all; on `𝓜²(ρ)` both sides are finite). -/
theorem adjoint_of_isReversal (A R : Kernel X X) [IsMarkovKernel A] [IsMarkovKernel R]
    (ρ : Measure X) [IsFiniteMeasure ρ] (hrev : IsReversal A R ρ)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≪ ρ) (hν : ν ≪ ρ) :
    ∫⁻ x, (μ.bind A).rnDeriv ρ x * ν.rnDeriv ρ x ∂ρ
      = ∫⁻ x, μ.rnDeriv ρ x * (ν.bind R).rnDeriv ρ x ∂ρ := by
  have hAμ : μ.bind A ≪ ρ := by
    have := GFNBounds.Core.bind_absolutelyContinuous_bind A hμ
    rwa [hrev.bind_eq_left] at this
  have hRν : ν.bind R ≪ ρ := by
    have := GFNBounds.Core.bind_absolutelyContinuous_bind R hν
    rwa [hrev.bind_eq] at this
  have hu : Measurable (μ.rnDeriv ρ) := Measure.measurable_rnDeriv _ _
  have hv : Measurable (ν.rnDeriv ρ) := Measure.measurable_rnDeriv _ _
  rw [lintegral_rnDeriv_bind_mul A ρ μ hμ hAμ hv]
  simp_rw [mul_comm (μ.rnDeriv ρ _)]
  rw [lintegral_rnDeriv_bind_mul R ρ ν hν hRν hu, hrev,
    lintegral_map (f := fun p : X × X => ν.rnDeriv ρ p.1 * μ.rnDeriv ρ p.2)
      ((hv.comp measurable_fst).mul (hu.comp measurable_snd)) measurable_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, mul_comm]

end Reversal

/-! ### The dual edge lift and the duality `λ₂ ⊗ K₂* = K₂ ⊗ λ₂` -/

/-- The dual edge lift `K₂* : (s,s') ↦ (s', R(s'))` of a kernel `R` (the paper takes
`R = π_→^λ = π_←^λ`). -/
noncomputable def edgeLiftDual (R : Kernel S S) [IsSFiniteKernel R] : Kernel (S × S) (S × S) :=
  Kernel.deterministic Prod.snd measurable_snd ×ₖ R.comap Prod.snd measurable_snd

instance (R : Kernel S S) [IsMarkovKernel R] : IsMarkovKernel (edgeLiftDual R) := by
  unfold edgeLiftDual; infer_instance

theorem edgeLiftDual_apply (R : Kernel S S) [IsSFiniteKernel R] (x : S × S) :
    edgeLiftDual R x = (R x.2).map (Prod.mk x.2) := by
  rw [edgeLiftDual, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply,
    Measure.dirac_prod]

theorem lintegral_edgeLiftDual (R : Kernel S S) [IsSFiniteKernel R] (x : S × S)
    {f : S × S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(edgeLiftDual R x) = ∫⁻ t, f (x.2, t) ∂(R x.2) := by
  rw [edgeLiftDual_apply, lintegral_map hf (by fun_prop)]

/-- **`lem:lift_wellposed`, duality**: if `R` is a `λ`-reversal of `π_←` (`λ ⊗ R = π_← ⊗ λ`),
then `K₂* = (s,s') ↦ (s', R(s'))` is a `λ₂`-reversal of `K₂`: `λ₂ ⊗ K₂* = K₂ ⊗ λ₂`. Both sides are
the law of three consecutive states of the stationary backward chain. -/
theorem edgeLift_duality (T R : Kernel S S) [IsMarkovKernel T] [IsMarkovKernel R]
    (lam : Measure S) [IsFiniteMeasure lam] (hR : IsReversal T R lam) :
    IsReversal (edgeLift T) (edgeLiftDual R) (edgeMeasure T lam) := by
  unfold IsReversal
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  -- measurability of the two inner integrals, read off their kernel forms
  have hL : Measurable fun p : S × S => ∫⁻ t, f (p, (p.2, t)) ∂(R p.2) := by
    have e : (fun p : S × S => ∫⁻ t, f (p, (p.2, t)) ∂(R p.2))
        = fun p => ∫⁻ y, f (p, y) ∂(edgeLiftDual R p) :=
      funext fun p => (lintegral_edgeLiftDual R p (hf.comp measurable_prodMk_left)).symm
    rw [e]; exact Measurable.lintegral_kernel_prod_right' (κ := edgeLiftDual R) hf
  have hRm : Measurable fun p : S × S => ∫⁻ c, f ((c, p.1), p) ∂(T p.1) := by
    have e : (fun p : S × S => ∫⁻ c, f ((c, p.1), p) ∂(T p.1))
        = fun p => ∫⁻ y, f (Prod.swap (p, y)) ∂(edgeLift T p) :=
      funext fun p => (lintegral_edgeLift T p
        ((hf.comp measurable_swap).comp measurable_prodMk_left)).symm
    rw [e]
    exact Measurable.lintegral_kernel_prod_right' (κ := edgeLift T)
      (f := fun q => f (Prod.swap q)) (hf.comp measurable_swap)
  rw [Measure.lintegral_compProd hf, lintegral_map hf measurable_swap,
    Measure.lintegral_compProd (f := fun q => f (Prod.swap q)) (hf.comp measurable_swap)]
  have e1 : ∀ p : S × S, ∫⁻ y, f (p, y) ∂(edgeLiftDual R p) = ∫⁻ t, f (p, (p.2, t)) ∂(R p.2) :=
    fun p => lintegral_edgeLiftDual R p (hf.comp measurable_prodMk_left)
  have e2 : ∀ p : S × S, ∫⁻ y, f (Prod.swap (p, y)) ∂(edgeLift T p)
      = ∫⁻ c, f ((c, p.1), p) ∂(T p.1) :=
    fun p => lintegral_edgeLift T p ((hf.comp measurable_swap).comp measurable_prodMk_left)
  simp_rw [e1, e2]
  rw [lintegral_edgeMeasure T lam hL, show edgeMeasure T lam = lam ⊗ₘ R from Eq.symm hR,
    Measure.lintegral_compProd hRm]
  refine lintegral_congr fun a => ?_
  simp only
  refine (lintegral_lintegral_swap ?_).symm
  exact (hf.comp ((measurable_snd.prodMk (measurable_const (a := a))).prodMk
    ((measurable_const (a := a)).prodMk measurable_fst))).aemeasurable

/-- `λ₂` is `K₂*`-invariant. -/
theorem edgeMeasure_invariant_dual (T R : Kernel S S) [IsMarkovKernel T] [IsMarkovKernel R]
    (lam : Measure S) [IsFiniteMeasure lam] (hR : IsReversal T R lam) :
    (edgeMeasure T lam).bind (edgeLiftDual R) = edgeMeasure T lam :=
  (edgeLift_duality T R lam hR).bind_eq

/-- **`lem:lift_wellposed`, adjointness**: the density action of `K₂*` is the
`𝓜²(λ₂)`-adjoint of that of `K₂`: `⟪μK₂ ∣ ν⟫_{λ₂} = ⟪μ ∣ νK₂*⟫_{λ₂}`. -/
theorem edgeLift_adjoint (T R : Kernel S S) [IsMarkovKernel T] [IsMarkovKernel R]
    (lam : Measure S) [IsFiniteMeasure lam] (hR : IsReversal T R lam)
    (μ ν : Measure (S × S)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ edgeMeasure T lam) (hν : ν ≪ edgeMeasure T lam) :
    ∫⁻ p, (μ.bind (edgeLift T)).rnDeriv (edgeMeasure T lam) p
        * ν.rnDeriv (edgeMeasure T lam) p ∂(edgeMeasure T lam)
      = ∫⁻ p, μ.rnDeriv (edgeMeasure T lam) p
        * (ν.bind (edgeLiftDual R)).rnDeriv (edgeMeasure T lam) p ∂(edgeMeasure T lam) :=
  adjoint_of_isReversal _ _ _ (edgeLift_duality T R lam hR) μ ν hμ hν

/-- **`lem:lift_wellposed`, uniqueness of the dual** (`lem:adjoint`*(1)* applied to `K₂` and
`λ₂`, as the paper's proof does): on a countably generated `𝒮`, every `λ₂`-reversal of `K₂` agrees with `K₂*` `λ₂`-a.e.,
so "the `𝓜²(λ₂)`-dual of `K₂`" is well defined and is the edge lift of the reversal. -/
theorem edgeLift_reversal_unique [MeasurableSpace.CountablyGenerated S] (T R : Kernel S S)
    [IsMarkovKernel T] [IsMarkovKernel R] (lam : Measure S) [IsFiniteMeasure lam]
    (hR : IsReversal T R lam) (Q : Kernel (S × S) (S × S)) [IsFiniteKernel Q]
    (hQ : IsReversal (edgeLift T) Q (edgeMeasure T lam)) :
    Q =ᵐ[edgeMeasure T lam] edgeLiftDual R :=
  IsReversal.ae_eq hQ (edgeLift_duality T R lam hR)

/-! ### `𝓜²` bookkeeping and the real inner product -/

/-- A measure with square-integrable density against a finite measure is finite
(Cauchy–Schwarz against `1`): the `IsFiniteMeasure` hypotheses above are implied by
membership of `𝓜²`. -/
theorem isFiniteMeasure_withDensity_of_sq {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    [IsFiniteMeasure ρ] {u : X → ℝ≥0∞} (hu : Measurable u) (h2 : ∫⁻ x, u x ^ 2 ∂ρ ≠ ∞) :
    IsFiniteMeasure (ρ.withDensity u) := by
  refine isFiniteMeasure_withDensity ?_
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two
    hu.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  refine ne_top_of_le_ne_top ?_ h
  refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))
  simpa only [ENNReal.rpow_two] using h2

/-- For `ℝ≥0∞`-valued functions finite a.e., the real integral of the product of their real
parts is the real part of the `ℝ≥0∞` integral of their product — whatever the integrability. -/
theorem integral_toReal_mul_toReal {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hf' : ∀ᵐ x ∂ρ, f x < ∞)
    (hg' : ∀ᵐ x ∂ρ, g x < ∞) :
    ∫ x, (f x).toReal * (g x).toReal ∂ρ = (∫⁻ x, f x * g x ∂ρ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x =>
      mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    ((hf.ennreal_toReal.mul hg.ennreal_toReal).aestronglyMeasurable)]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hf', hg'] with x hfx hgx
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfx.ne,
    ENNReal.ofReal_toReal hgx.ne]

/-- **`lem:lift_wellposed`, adjointness in the paper's real inner product**
`⟪μ ∣ ν⟫_{λ₂} = ∫ (dμ/dλ₂)(dν/dλ₂) dλ₂`: `⟪μK₂ ∣ ν⟫_{λ₂} = ⟪μ ∣ νK₂*⟫_{λ₂}`. -/
theorem edgeLift_adjoint_real (T R : Kernel S S) [IsMarkovKernel T] [IsMarkovKernel R]
    (lam : Measure S) [IsFiniteMeasure lam] (hR : IsReversal T R lam)
    (μ ν : Measure (S × S)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ edgeMeasure T lam) (hν : ν ≪ edgeMeasure T lam) :
    ∫ p, ((μ.bind (edgeLift T)).rnDeriv (edgeMeasure T lam) p).toReal
        * (ν.rnDeriv (edgeMeasure T lam) p).toReal ∂(edgeMeasure T lam)
      = ∫ p, (μ.rnDeriv (edgeMeasure T lam) p).toReal
        * ((ν.bind (edgeLiftDual R)).rnDeriv (edgeMeasure T lam) p).toReal
          ∂(edgeMeasure T lam) := by
  have : IsFiniteMeasure (μ.bind (edgeLift T)) := by
    rw [show μ.bind (edgeLift T) = edgeLift T ∘ₘ μ from rfl]; infer_instance
  have : IsFiniteMeasure (ν.bind (edgeLiftDual R)) := by
    rw [show ν.bind (edgeLiftDual R) = edgeLiftDual R ∘ₘ ν from rfl]; infer_instance
  rw [integral_toReal_mul_toReal _ (Measure.measurable_rnDeriv _ _)
      (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _) (Measure.rnDeriv_lt_top _ _),
    integral_toReal_mul_toReal _ (Measure.measurable_rnDeriv _ _)
      (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _) (Measure.rnDeriv_lt_top _ _),
    edgeLift_adjoint T R lam hR μ ν hμ hν]

/-! ### Agreement with the finite form, and non-vacuity -/

/-- On singletons `K₂((s,s') → {(z,w)}) = [w = s]·π_←(s → {z})` — `GFNBounds.Balance.edgeKernel`
of the finite form, read on a space with measurable singletons. -/
theorem edgeLift_apply_singleton [MeasurableSingletonClass S] [DecidableEq S] (T : Kernel S S)
    [IsSFiniteKernel T] (x : S × S) (z w : S) :
    edgeLift T x {(z, w)} = if w = x.1 then T x.1 {z} else 0 := by
  rw [edgeLift_apply, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  split_ifs with h
  · subst h
    congr 1
    ext y; simp
  · convert measure_empty (μ := T x.1)
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
      Set.mem_empty_iff_false, iff_false, not_and]
    exact fun _ hw => h hw.symm

/-- **Non-vacuity** on any measurable space: for every probability `ρ`, the resampling kernel
`x ↦ ρ` leaves `ρ` invariant and is its own `ρ`-reversal, so every hypothesis of the results
above is met (and `λ₂ = ρ ⊗ ρ ≠ 0`). -/
theorem isReversal_const {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ] :
    IsReversal (Kernel.const X ρ) (Kernel.const X ρ) ρ ∧ ρ.bind (Kernel.const X ρ) = ρ := by
  refine ⟨?_, ?_⟩
  · unfold IsReversal
    rw [Measure.compProd_const, Measure.prod_swap]
  · rw [show ρ.bind (Kernel.const X ρ) = Kernel.const X ρ ∘ₘ ρ from rfl, Measure.const_comp,
      measure_univ, one_smul]

/-! ### `lem:lift_wellposed` in one statement, on a standard Borel space -/

/-- **`lem:lift_wellposed`** on a standard Borel space (the paper's Polish `𝒮` is one), with the
dual forward policy `π_→^λ = π_←^λ` constructed as the disintegration of `π_← ⊗ λ` over its first
marginal (`T†λ`, Mathlib's posterior):
*(i)* `λ₂` is `K₂`-invariant;
*(ii)* `K₂` maps `𝓜(λ₂)` into itself and contracts the `𝓜²(λ₂)` norm;
*(iii)* `K₂* = (s,s') ↦ (s', π_→^λ(s'))` satisfies `λ₂ ⊗ K₂* = K₂ ⊗ λ₂`, and is the
`λ₂`-a.e. unique kernel doing so — the `λ₂`-reversal of `K₂`;
*(iv)* its density action is the `𝓜²(λ₂)`-adjoint of that of `K₂`. -/
theorem lift_wellposed [StandardBorelSpace S] [Nonempty S] (T : Kernel S S) [IsMarkovKernel T]
    (lam : Measure S) [IsFiniteMeasure lam] (hinv : lam.bind T = lam) :
    (edgeMeasure T lam).bind (edgeLift T) = edgeMeasure T lam ∧
    (∀ (μ : Measure (S × S)) [IsFiniteMeasure μ], μ ≪ edgeMeasure T lam →
      μ.bind (edgeLift T) ≪ edgeMeasure T lam ∧
      ∫⁻ p, ((μ.bind (edgeLift T)).rnDeriv (edgeMeasure T lam) p) ^ 2 ∂(edgeMeasure T lam)
        ≤ ∫⁻ p, (μ.rnDeriv (edgeMeasure T lam) p) ^ 2 ∂(edgeMeasure T lam)) ∧
    IsReversal (edgeLift T) (edgeLiftDual (T†lam)) (edgeMeasure T lam) ∧
    (∀ (Q : Kernel (S × S) (S × S)) [IsFiniteKernel Q],
      IsReversal (edgeLift T) Q (edgeMeasure T lam) →
        Q =ᵐ[edgeMeasure T lam] edgeLiftDual (T†lam)) ∧
    (∀ (μ ν : Measure (S × S)) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      μ ≪ edgeMeasure T lam → ν ≪ edgeMeasure T lam →
      ∫ p, ((μ.bind (edgeLift T)).rnDeriv (edgeMeasure T lam) p).toReal
          * (ν.rnDeriv (edgeMeasure T lam) p).toReal ∂(edgeMeasure T lam)
        = ∫ p, (μ.rnDeriv (edgeMeasure T lam) p).toReal
          * ((ν.bind (edgeLiftDual (T†lam))).rnDeriv (edgeMeasure T lam) p).toReal
            ∂(edgeMeasure T lam)) := by
  have hR := isReversal_posterior T lam hinv
  refine ⟨edgeMeasure_invariant T lam hinv, fun μ _ hμ => ⟨?_, ?_⟩,
    edgeLift_duality T _ lam hR, fun Q _ hQ => edgeLift_reversal_unique T _ lam hR Q hQ,
    fun μ ν _ _ hμ hν => edgeLift_adjoint_real T _ lam hR μ ν hμ hν⟩
  · exact bind_edgeLift_absolutelyContinuous T lam hinv μ hμ
  · exact edgeLift_contraction T lam hinv μ hμ

end GFNBounds.Balance.LiftGeneral
