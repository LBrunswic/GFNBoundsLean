import GFNBounds.Core.AdjointGeneral
import GFNBounds.Balance.GradientFormulas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# The first variation of the `g`-divergence balance loss on a general measurable space

**`theo:first_variation_full`** — `proofs.tex`, the `theorem` carrying that label (`:457–463`
when written), proof `:465–493`.
**`theo:first_variation`** — its body twin, `cv_divergence.tex` (`:122–128` when written).
**`cor:gradient_formulas`** — `proofs.tex` (`:495–508` when written), proof `:510–512`.
(Line numbers drift, kb `0036`; the label is the anchor.)

> (`theo:first_variation_full`) Under the hypotheses of Lemma `lem:adjoint`, let
> `μ ∈ 𝓜⁺(𝒮, ν_B)` with `μ ∼ λ`, `dμ/dλ ∈ L²(λ)`, `μT ≪ μ`, and let `r := d(μT)/dμ` be
> essentially bounded away from `0` and `∞`. For any finite measure `ν` with
> `dν/dμ ∈ L^∞(μ)`, define the associated `g`-divergence balance loss
> `𝓛_{g,ν}(μ) := ∫_𝒮 g(r) dν`. Then, for any `g : ℝ_+^* → ℝ` continuously differentiable with
> locally Lipschitz derivative, and any finite `ν_G ∈ 𝓜⁺(𝒮, ν_B)` with `ν_G ∼ λ`, the
> derivative of `𝓛_{g,ν}` — taken along directions `δ ≪ μ` with `‖dδ/dμ‖_{L^∞(μ)} < 1` and
> `d(δT)/dμ ∈ L^∞(μ)` — is represented by
> `∇^{ν_G}_μ 𝓛_{g,ν} = (dν_G/dλ)·(T^λ − r)[g'(r)(dν/dμ)λ]`.

> (`theo:first_variation`) For a continuously differentiable generator, the `g`-divergence
> balance loss of an arbitrary Markov kernel is differentiable at every flow whose balance ratio
> is bounded away from `0` and `∞`, and — as soon as the kernel admits a non-zero finite
> invariant measure equivalent to that flow — its gradient is the reversal of the kernel, minus
> the ratio, applied to `g'` of that ratio.

> (`cor:gradient_formulas`) Under the assumptions of Theorem `theo:first_variation_full` with
> `T = π_←` and `μ = F_←`: `∇^λ_{F_←} 𝓛_{g,F_←} = (π_→^λ − r)[g'(r)λ]`. For `g(x) = (x−1)²`,
> `∇^λ_{F_←} 𝓛_{g,F_←} = 2(π_→^λ − r)[(r−1)λ] = 2(π_→^λ(rλ) − λ − r²λ + rλ)`. The case
> `g(x) = |x−1|` is analogous when `r` is moreover essentially bounded away from `1`, with `g'(r)`
> replaced by `sign(r−1)` […].

`GFNBounds/Balance/FirstVariation.lean` and `GFNBounds/Balance/GradientFormulas.lean` prove these
on a `Fintype`. This file is the general form, on a measurable space, built on
`GFNBounds/Core/AdjointGeneral.lean` (the `λ`-reversal `T^λ` as Mathlib's posterior, the function
and density actions).

## Conventions

A flow is a `Measure S`; the density action `μ ↦ μT` is `T ∘ₘ μ`; `r := d(μT)/dμ` is
`ratio T μ = ((T ∘ₘ μ).rnDeriv μ ·).toReal`; the loss is `loss T g ν μ = ∫ g(r) dν`, literally
the paper's `𝓛_{g,ν}(μ)`. A direction `δ ≪ μ` is carried by its density `u = dδ/dμ` (measurable,
essentially bounded); `perturb μ u s := μ.withDensity (1 + s·u)` **is** `μ + s·δ`
(`perturb_toSignedMeasure`: as signed measures, `= μ + s • μ.withDensityᵥ u`). The paper's
`v := d(δT)/dμ` is `dirPush T μ u = d((u⁺μ)T)/dμ − d((u⁻μ)T)/dμ`, i.e. `δT` read through the
Jordan decomposition `δ = u⁺μ − u⁻μ`. `ψ := g'(r)·dν/dμ` is `psi`, and the gradient's density
`Tψ − rψ` is `gradDens` (`T` acting on functions, `funAct`, as in `lem:adjoint`(3)). The signed
measure `(T^λ − r)[ψλ]` is read setwise (clause (1) below), which needs no instance on the two
halves `(ψ^±λ)T^λ`.

## How the proof differs from the paper's, and what that buys

The paper routes the first variation through `λ`: it writes `⟨ψλ ∣ δT⟩_λ` and moves `T` across
with `lem:adjoint`(3). Here the whole computation is done in `μ`-coordinates, and `λ` enters only
to *name* the result:

* **the perturbed ratio** `r(μ + sδ) = (r + s·v)/(1 + s·u)` (`ratio_perturb`, the paper's own
  display) comes from linearity of `φ ↦ d((φμ)T)/dμ` (`pushDens_add4`, `pushDens_smul`), which is
  additivity of `bind` plus `rnDeriv_add` — no reversal;
* **the adjoint step** `∫ ψ · d(δT)/dμ dμ = ∫ Tψ · dδ/dμ dμ` (`integral_mul_dirPush`) is
  `κ ∘ₘ m = (m ⊗ₘ κ).snd` and Fubini — again no reversal, only `μT ≪ μ`;
* **differentiation under the integral** (`hasDerivAt_integral_quot`) needs `g` only `C¹`;
  the paper's local Lipschitz bound on `g'` is what makes the remainder *uniformly* second order,
  and that uniform statement is proved separately with an explicit constant
  (`loss_remainder_le`).

Consequences, each proved rather than asserted: the paper's `dμ/dλ ∈ L²(λ)` is never used;
`μT ≪ μ` follows from `μ ∼ λ` and invariance (`IsInvariant.comp_absolutelyContinuous`); the
admissibility requirement `d(δT)/dμ ∈ L^∞(μ)` is automatic, `|d(δT)/dμ| ≤ ‖dδ/dμ‖_∞·r`
(`abs_dirPush_le`); and the differentiability clause of the body twin holds with no invariant
measure at all (`hasDerivAt_loss_perturb`).

## What is proved

| | |
|---|---|
| `ratio_perturb`, `perturb_toSignedMeasure` | `r(μ+sδ) = (r+s·v)/(1+s·u)` `μ`-a.e. for `|s|·‖u‖_∞ < 1`; `perturb` is `μ + sδ` |
| `abs_dirPush_le` | `|d(δT)/dμ| ≤ ‖u‖_∞·r`: the `L^∞` admissibility of `δT` is automatic |
| `hasDerivAt_loss_perturb` | **differentiability, no invariant measure**: `d/ds|₀ 𝓛(μ+sδ) = ∫ g'(r)(v − r·u) dν` for `g ∈ C¹(ℝ₊*)` |
| `integral_mul_dirPush` | the adjoint step `∫ ψ d(δT) = ∫ Tψ dδ` |
| `hasDerivAt_loss_gradDens` | `d/ds|₀ 𝓛(μ+sδ) = ∫ (Tψ − rψ)·(dδ/dμ) dμ` |
| `loss_remainder_le` | **the uniform remainder**, explicit: `|𝓛(μ+δ) − 𝓛(μ) − ⟨G∣δ⟩| ≤ ν(𝒮)(16Kb² + 4Mb)c²` for `‖dδ/dμ‖_∞ ≤ c`, `c ≤ ½`, `bc ≤ a/2` |
| `reversal_comp_signed`, `phi_density` | **`lem:adjoint`(3) for the signed `ψλ`**: `(T^λ − r)[ψλ]` has `λ`-density `Tψ − rψ` |
| `withDensityᵥ_rnDeriv_mul` | `ϖ·Φ` has `ν_G`-density `dΦ/dλ`, `ϖ = dν_G/dλ`: the preconditioner moves the inner product, not the density |
| `representative_unique` | the `L²(ν_G)` representative is unique (pairing against the directions `‖dδ/dμ‖_∞ ≤ ½`) |
| `first_variation_general` | **`theo:first_variation_full`** in five clauses, without the unused hypotheses |
| `theo_first_variation_full` | the same with **the paper's hypotheses verbatim**, plus clause (6) the uniform remainder and (7) existence of its constants |
| `theo_first_variation` | **the body twin**, clause by clause |
| `cor_gradient_formulas` | **`cor:gradient_formulas`, first display**, with uniqueness |
| `cor_gradient_formulas_sq` | the `(x−1)²` display: density `2(π_← r − 1 − r² + r)`, and the pieces `π_→^λλ = λ`, `π_→^λ(rλ) = (π_← r)λ` |
| `cor_gradient_formulas_abs` | the `|x−1|` case under `|r − 1| ≥ a' > 0` a.e., `g'` replaced by `sign(r − 1)` |
| `theo_first_variation_full_hypotheses_inhabited` | non-vacuity (kb `0025`, `0027`): `T = const π`, `λ = μ = ν = π`, `a = b = 1` meets every measure hypothesis (`g`, `ν_G := π` trivially); a balanced base point |

## Hypothesis checklist (`theo:first_variation_full`)

| paper hypothesis | here |
|---|---|
| `lem:adjoint`: `𝒮` Polish | ✓ weakened in the safe direction to `[StandardBorelSpace S] [Nonempty S]`, as in `AdjointGeneral.lean` (`Nonempty` is implied by `λ ≠ 0`, kb `0027`); only clause (1), which names `T^λ`, uses it — the derivative clauses (`hasDerivAt_loss_perturb`, `hasDerivAt_loss_gradDens`, `loss_remainder_le`) hold on any measurable space |
| `lem:adjoint`: `T` Markov, `λ` finite, `T`-invariant | ✓ carried (`[IsMarkovKernel T]`, `[IsFiniteMeasure lam]`, `IsInvariant T lam`) |
| `lem:adjoint`: `λ` non-zero | ✓ carried in `theo_first_variation_full` (`_hlam0`), unused: every clause holds without it |
| `ν_B`, `μ ∈ 𝓜⁺(𝒮, ν_B)`, `ν_G ∈ 𝓜⁺(𝒮, ν_B)` | ✓ `ν_B` dropped: no clause involves it (as in `lem:adjoint`'s row); `μ` enters as a finite measure (`InM2 lam μ` in the verbatim form, which carries finiteness) |
| `μ ∼ λ` | ✓ carried (`μ ≪ λ`, `λ ≪ μ`) |
| `dμ/dλ ∈ L²(λ)` | ✓ carried in `theo_first_variation_full` (inside `InM2`), **unused**: the proof never needs it; the case where it fails is inhabited, e.g. `T = Kernel.id` (`r ≡ 1`), `μ = uλ` with `u ∈ L¹(λ) \ L²(λ)` |
| `μT ≪ μ` | ✓ carried in `theo_first_variation_full` (`_hac`), **unused**: implied by `μ ∼ λ` and invariance |
| `r` essentially bounded away from `0` and `∞` | ✓ carried as `a ≤ r ≤ b` `μ`-a.e., `0 < a` (the explicit form of "bounded away") |
| `ν` finite, `dν/dμ ∈ L^∞(μ)` | ✓ carried (`[IsFiniteMeasure ν]`, `ν ≪ μ` — which `dν/dμ` presupposes —, `MemLp (dν/dμ) ⊤ μ`) |
| `g : ℝ₊* → ℝ` continuously differentiable | ✓ carried as `g, g' : ℝ → ℝ` with `HasDerivAt g (g' y) y` for `y > 0` and `g'` continuous on `(0, ∞)`; values of `g` on `(−∞, 0]` are never read (`r > 0`) |
| `g'` locally Lipschitz | ✓ carried in `theo_first_variation_full` and used **only** by clause (6), the uniform remainder; clauses (1)–(5) need `C¹` only |
| `ν_G` finite, `ν_G ∼ λ` | ✓ carried |
| directions `δ ≪ μ`, `‖dδ/dμ‖_∞ < 1`, `d(δT)/dμ ∈ L^∞(μ)` | ✓ clause (4) holds for **every** essentially bounded `dδ/dμ` (each is a multiple of an admissible one, and the derivative is along the line), `d(δT)/dμ ∈ L^∞` being automatic; clause (5) (uniqueness) hypothesises the pairing only on `‖dδ/dμ‖_∞ ≤ ½`, inside the paper's class; clause (6) on `‖dδ/dμ‖_∞ ≤ c` with `c ≤ ½`, `bc ≤ a/2` |

## SCOPE (disclosed)

* **What "the derivative is represented by `∇`" means here.** Two readings, both proved:
  *along lines* (clause (4)) — for each admissible `δ`, `s ↦ 𝓛(μ + sδ)` is differentiable at
  `0` with derivative `⟨G ∣ δ⟩_{ν_G} = ∫ (dG/dν_G)(dδ/dν_G) dν_G`; and *uniformly on the
  admissible class* (clause (6)) — `|𝓛(μ+δ) − 𝓛(μ) − ⟨G ∣ δ⟩_{ν_G}| ≤ ν(𝒮)(16Kb² + 4Mb)‖dδ/dμ‖²_∞`
  on the ball `‖dδ/dμ‖_∞ ≤ min(½, a/(2b))`, `K` a Lipschitz constant of `g'` on `[a/3, 3b]` and
  `M` a bound of `|g'|` on `[a, b]` (clause (7): such `K`, `M` exist). This is the paper's "the
  remainder is second order in `(u, v)`, uniformly", with `‖v‖_∞ ≤ b‖u‖_∞` absorbed. No
  continuous-linear-functional object on `𝓜(𝒮)` is formed: the admissible directions form a cone
  inside a space the library does not topologize, as in `AdjointGeneral.lean`'s `IsLeast`
  reading of an operator norm.
* **`G` is named, not constructed as an operator image.** Clause (1) states that the signed
  measure `(T^λ − r)[ψλ] = (ψ⁺λ)T^λ − (ψ⁻λ)T^λ − rψλ` has `λ`-density `h := Tψ − rψ`, setwise;
  clause (2) that `ϖ·(hλ) = h·ν_G` as signed measures (`withDensityᵥ`), `ϖ = dν_G/dλ`; clause (3)
  that `h ∈ L²(ν_G)`. Together: `G := (dν_G/dλ)·(T^λ − r)[ψλ]` has `ν_G`-density `h ∈ L²(ν_G)`,
  which is what "represented in `⟨·∣·⟩_{ν_G}`" consumes.
* **`ψ` need not be measurable.** `g'` is only continuous on `(0, ∞)`, so `g' ∘ r` is measurable
  only up to a `μ`-null set; every clause is stated for the paper's `ψ` and `Tψ` as written, the
  proof passing through a measurable version (`exists_psi_version`).
* **Strengthened, proved** (none outruns the statement; each specializes to the paper's clause):
  the directions of clause (4) are all essentially bounded ones; the `L²(λ)` and `μT ≪ μ`
  hypotheses are unused; clauses (1)–(5) need `g ∈ C¹` only; uniqueness of the representative
  (clause (5)) is added — the paper says "represented by", uniqueness is the reason the
  representative is *the* gradient.
* **`cor:gradient_formulas`** is stated at the paper's specialisation `ν = μ = F_←`, `ν_G = λ`
  (`ϖ = 1`), for an arbitrary Markov `π_←` with finite invariant `λ ∼ F_←` — the graph structure
  of a backward policy is not used. The `|x−1|` case carries the paper's repaired hypothesis
  `|r − 1| ≥ a' > 0` a.e.; it is proved directly (`g = |·−1|` is continuous and differentiable off
  `1`), not through the paper's smoothing `g̃`, which the argument does not need.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace GFNBounds.Core.General.FirstVariation

variable {S : Type*} [MeasurableSpace S]

/-! ### The objects -/

/-- The balance ratio `r(μ) := d(μT)/dμ`, read in `ℝ`. -/
noncomputable def ratio (T : Kernel S S) (μ : Measure S) : S → ℝ :=
  fun x => ((T ∘ₘ μ).rnDeriv μ x).toReal

/-- The `g`-divergence balance loss `𝓛_{g,ν}(μ) := ∫ g(d(μT)/dμ) dν`. -/
noncomputable def loss (T : Kernel S S) (g : ℝ → ℝ) (ν μ : Measure S) : ℝ :=
  ∫ x, g (ratio T μ x) ∂ν

/-- The perturbed flow `μ + sδ` for the direction `δ := uμ`, i.e. the measure of density
`1 + s·u` against `μ` (a positive measure as soon as `|s·u| ≤ 1`). -/
noncomputable def perturb (μ : Measure S) (u : S → ℝ) (s : ℝ) : Measure S :=
  μ.withDensity fun x => ENNReal.ofReal (1 + s * u x)

/-- The pushed measure `(φ⁺μ)T` of a density `φ` against `μ` (negative values are clipped). -/
noncomputable def push (T : Kernel S S) (μ : Measure S) (φ : S → ℝ) : Measure S :=
  T ∘ₘ μ.withDensity fun y => ENNReal.ofReal (φ y)

/-- `d((φ⁺μ)T)/dμ`, read in `ℝ`. -/
noncomputable def pushDens (T : Kernel S S) (μ : Measure S) (φ : S → ℝ) : S → ℝ :=
  fun x => ((push T μ φ).rnDeriv μ x).toReal

/-- The paper's `v := d(δT)/dμ` for `δ = uμ = u⁺μ − u⁻μ`: `δT = (u⁺μ)T − (u⁻μ)T`. -/
noncomputable def dirPush (T : Kernel S S) (μ : Measure S) (u : S → ℝ) : S → ℝ :=
  fun x => pushDens T μ u x - pushDens T μ (fun y => -u y) x

/-! ### Linearity of the density action relative to `μ` -/

section Algebra

variable {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem push_isFinite {φ : S → ℝ} (hφ : Integrable φ μ) : IsFiniteMeasure (push T μ φ) := by
  haveI := isFiniteMeasure_withDensity_ofReal hφ.2
  unfold push; infer_instance

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem push_one : push T μ (fun _ => 1) = T ∘ₘ μ := by
  unfold push
  simp only [ENNReal.ofReal_one]
  rw [show (fun _ : S => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem pushDens_one : pushDens T μ (fun _ => 1) = ratio T μ := by
  unfold pushDens ratio; rw [push_one]

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem push_zero : push T μ (fun _ => 0) = 0 := by
  unfold push
  simp only [ENNReal.ofReal_zero]
  rw [show (fun _ : S => (0 : ℝ≥0∞)) = 0 from rfl, withDensity_zero]
  ext s hs; simp

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem pushDens_zero : pushDens T μ (fun _ => 0) =ᵐ[μ] 0 := by
  unfold pushDens; rw [push_zero]
  filter_upwards [Measure.rnDeriv_zero μ] with x hx
  simp [hx]

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem push_congr {φ ψ : S → ℝ}
    (h : ∀ᵐ x ∂μ, ENNReal.ofReal (φ x) = ENNReal.ofReal (ψ x)) : push T μ φ = push T μ ψ := by
  unfold push; rw [withDensity_congr_ae h]

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem push_add {φ ψ : S → ℝ} (hφ : Measurable φ) :
    push T μ φ + push T μ ψ = T ∘ₘ μ.withDensity
      (fun y => ENNReal.ofReal (φ y) + ENNReal.ofReal (ψ y)) := by
  unfold push
  rw [← Measure.comp_add]
  congr 1
  exact (withDensity_add_left hφ.ennreal_ofReal _).symm

/-- **Additivity of `d((φμ)T)/dμ`**: `φ₁⁺ + φ₂⁺ = φ₃⁺ + φ₄⁺` a.e. forces the same identity on the
pushed densities, `μ`-a.e. -/
theorem pushDens_add4 {φ₁ φ₂ φ₃ φ₄ : S → ℝ} (h₁ : Measurable φ₁) (h₃ : Measurable φ₃)
    (i₁ : Integrable φ₁ μ) (i₂ : Integrable φ₂ μ) (i₃ : Integrable φ₃ μ) (i₄ : Integrable φ₄ μ)
    (hsum : ∀ᵐ x ∂μ, ENNReal.ofReal (φ₁ x) + ENNReal.ofReal (φ₂ x) =
      ENNReal.ofReal (φ₃ x) + ENNReal.ofReal (φ₄ x)) :
    (fun x => pushDens T μ φ₁ x + pushDens T μ φ₂ x) =ᵐ[μ]
      fun x => pushDens T μ φ₃ x + pushDens T μ φ₄ x := by
  haveI := push_isFinite (T := T) i₁
  haveI := push_isFinite (T := T) i₂
  haveI := push_isFinite (T := T) i₃
  haveI := push_isFinite (T := T) i₄
  have hm : push T μ φ₁ + push T μ φ₂ = push T μ φ₃ + push T μ φ₄ := by
    rw [push_add h₁, push_add h₃, withDensity_congr_ae hsum]
  have e1 := Measure.rnDeriv_add (push T μ φ₁) (push T μ φ₂) μ
  have e2 := Measure.rnDeriv_add (push T μ φ₃) (push T μ φ₄) μ
  rw [hm] at e1
  filter_upwards [e1, e2, Measure.rnDeriv_lt_top (push T μ φ₁) μ,
    Measure.rnDeriv_lt_top (push T μ φ₂) μ, Measure.rnDeriv_lt_top (push T μ φ₃) μ,
    Measure.rnDeriv_lt_top (push T μ φ₄) μ] with x hx1 hx2 l1 l2 l3 l4
  simp only [Pi.add_apply] at hx1 hx2
  unfold pushDens
  rw [← ENNReal.toReal_add l1.ne l2.ne, ← ENNReal.toReal_add l3.ne l4.ne, ← hx1, ← hx2]

/-- **Homogeneity of `d((φμ)T)/dμ`** under a non-negative scalar. -/
theorem pushDens_smul {φ : S → ℝ} {c : ℝ} (hc : 0 ≤ c) (hφ : Measurable φ)
    (i : Integrable φ μ) :
    pushDens T μ (fun y => c * φ y) =ᵐ[μ] fun x => c * pushDens T μ φ x := by
  haveI := push_isFinite (T := T) i
  have hm : push T μ (fun y => c * φ y) = (Real.toNNReal c : ℝ≥0∞) • push T μ φ := by
    unfold push
    rw [← Measure.comp_smul]
    congr 1
    rw [← withDensity_smul _ hφ.ennreal_ofReal]
    congr 1
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_mul hc]; rfl
  have e := Measure.rnDeriv_smul_left (push T μ φ) μ (Real.toNNReal c)
  unfold pushDens
  rw [hm]
  have hsm : ((Real.toNNReal c : ℝ≥0∞) • push T μ φ) = (Real.toNNReal c) • push T μ φ := rfl
  rw [hsm]
  filter_upwards [e] with x hx
  rw [hx, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    Real.coe_toNNReal _ hc]

/-- The pointwise identity behind `pushDens_one_add`: `(1+x)⁺ + (−x)⁺ = 1 + x⁺` when `1+x ≥ 0`. -/
theorem ofReal_one_add_split {x : ℝ} (hx : 0 ≤ 1 + x) :
    ENNReal.ofReal (1 + x) + ENNReal.ofReal (-x) = ENNReal.ofReal 1 + ENNReal.ofReal x := by
  rcases le_total 0 x with h | h
  · rw [ENNReal.ofReal_of_nonpos (show -x ≤ 0 by linarith), add_zero,
      ENNReal.ofReal_add zero_le_one h]
  · rw [ENNReal.ofReal_of_nonpos h, add_zero, ← ENNReal.ofReal_add hx (by linarith)]
    congr 1; ring

end Algebra

/-! ### The perturbed ratio `r(μ + sδ) = (r + s·v)/(1 + s·u)` -/

section Perturb

variable {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S} [IsFiniteMeasure μ]

theorem integrable_of_abs_le {φ : S → ℝ} (hφ : Measurable φ) {K : ℝ}
    (hK : ∀ᵐ x ∂μ, |φ x| ≤ K) : Integrable φ μ :=
  Integrable.of_bound hφ.aestronglyMeasurable K (by simpa [Real.norm_eq_abs] using hK)

/-- `d((1 + s·u)μ T)/dμ = r + s·v`, `μ`-a.e., as soon as `|s|·C ≤ 1`. -/
theorem pushDens_one_add {u : S → ℝ} (hu : Measurable u) {C : ℝ} (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    {s : ℝ} (hs : |s| * C ≤ 1) :
    pushDens T μ (fun y => 1 + s * u y) =ᵐ[μ]
      fun x => ratio T μ x + s * dirPush T μ u x := by
  have iu : Integrable u μ := integrable_of_abs_le hu hub
  have iu' : Integrable (fun y => -u y) μ := iu.neg
  have isu : Integrable (fun y => s * u y) μ := iu.const_mul s
  have isu' : Integrable (fun y => -(s * u y)) μ := isu.neg
  have i1 : Integrable (fun _ : S => (1 : ℝ)) μ := integrable_const 1
  have i1su : Integrable (fun y => 1 + s * u y) μ := i1.add isu
  have hadd := pushDens_add4 (T := T) (φ₁ := fun y => 1 + s * u y) (φ₂ := fun y => -(s * u y))
    (φ₃ := fun _ => 1) (φ₄ := fun y => s * u y) (measurable_const.add (hu.const_mul s))
    measurable_const i1su isu' i1 isu (by
      filter_upwards [hub] with x hx
      refine ofReal_one_add_split ?_
      have : |s * u x| ≤ 1 := by
        rw [abs_mul]
        calc |s| * |u x| ≤ |s| * C := mul_le_mul_of_nonneg_left hx (abs_nonneg s)
          _ ≤ 1 := hs
      linarith [neg_abs_le (s * u x)])
  rw [pushDens_one] at hadd
  rcases le_total 0 s with h0 | h0
  · have e1 := pushDens_smul (T := T) h0 hu iu
    have e2 := pushDens_smul (T := T) h0 hu.neg iu'
    have e2' : pushDens T μ (fun y => -(s * u y)) = pushDens T μ (fun y => s * -u y) := by
      congr 1; funext y; ring
    rw [e2'] at hadd
    filter_upwards [hadd, e1, e2] with x hx h1 h2
    unfold dirPush
    rw [h1, h2] at hx
    linarith
  · have hs' : 0 ≤ -s := by linarith
    have e1 := pushDens_smul (T := T) hs' hu.neg iu'
    have e2 := pushDens_smul (T := T) hs' hu iu
    have e1' : pushDens T μ (fun y => s * u y) = pushDens T μ (fun y => -s * -u y) := by
      congr 1; funext y; ring
    have e2' : pushDens T μ (fun y => -(s * u y)) = pushDens T μ (fun y => -s * u y) := by
      congr 1; funext y; ring
    rw [e1', e2'] at hadd
    filter_upwards [hadd, e1, e2] with x hx h1 h2
    unfold dirPush
    rw [h1, h2] at hx
    linarith

theorem perturb_isFinite {u : S → ℝ} (hu : Measurable u) {C : ℝ} (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    (s : ℝ) : IsFiniteMeasure (perturb μ u s) := by
  have i : Integrable (fun y => 1 + s * u y) μ :=
    (integrable_const 1).add ((integrable_of_abs_le hu hub).const_mul s)
  exact isFiniteMeasure_withDensity_ofReal i.2

/-- **`perturb` is the paper's `μ + sδ`**: as signed measures, `μ ⊕ (1 + s·u)` is
`μ + s·δ` with `δ := uμ` (`withDensityᵥ`), as soon as `|s|·‖u‖_∞ ≤ 1`. -/
theorem perturb_toSignedMeasure {u : S → ℝ} (hu : Measurable u) {C : ℝ}
    (hub : ∀ᵐ x ∂μ, |u x| ≤ C) {s : ℝ} (hs : |s| * C ≤ 1) :
    @MeasureTheory.Measure.toSignedMeasure S _ (perturb μ u s) (perturb_isFinite hu hub s) =
      μ.toSignedMeasure + s • μ.withDensityᵥ u := by
  have iu : Integrable u μ := integrable_of_abs_le hu hub
  have i1 : Integrable (fun x => 1 + s * u x) μ := (integrable_const 1).add (iu.const_mul s)
  have hnn : ∀ᵐ x ∂μ, 0 ≤ 1 + s * u x := by
    filter_upwards [hub] with x hx
    have : |s * u x| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hx (abs_nonneg s)).trans hs
    linarith [neg_abs_le (s * u x)]
  haveI := perturb_isFinite hu hub s
  ext t ht
  rw [VectorMeasure.add_apply, VectorMeasure.smul_apply,
    Measure.toSignedMeasure_apply_measurable ht, Measure.toSignedMeasure_apply_measurable ht, withDensityᵥ_apply iu ht, measureReal_def,
    measureReal_def, perturb, withDensity_apply _ ht,
    ← ofReal_integral_eq_lintegral_ofReal i1.integrableOn (ae_restrict_of_ae hnn),
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae hnn)),
    integral_add (integrable_const 1).integrableOn (iu.const_mul s).integrableOn,
    integral_const_mul, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, smul_eq_mul]

/-- **The paper's display `r(x, μ+δ) = (r+v)/(1+u)`** (`proofs.tex`, proof of
`theo:first_variation_full`), along the line `s ↦ μ + s·δ`: for `|s|·C < 1`,
`d((μ+sδ)T)/d(μ+sδ) = (r + s·v)/(1 + s·u)`, `μ`-a.e. -/
theorem ratio_perturb {u : S → ℝ} (hu : Measurable u) {C : ℝ} (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    {s : ℝ} (hs : |s| * C < 1) :
    ratio T (perturb μ u s) =ᵐ[μ]
      fun x => (ratio T μ x + s * dirPush T μ u x) / (1 + s * u x) := by
  haveI := perturb_isFinite hu hub s
  have hpos : ∀ᵐ x ∂μ, 0 < 1 + s * u x := by
    filter_upwards [hub] with x hx
    have : |s * u x| < 1 := by
      rw [abs_mul]
      calc |s| * |u x| ≤ |s| * C := mul_le_mul_of_nonneg_left hx (abs_nonneg s)
        _ < 1 := hs
    linarith [neg_abs_le (s * u x)]
  have hf : Measurable fun x => ENNReal.ofReal (1 + s * u x) :=
    (measurable_const.add (hu.const_mul s)).ennreal_ofReal
  have e := Measure.rnDeriv_withDensity_right (T ∘ₘ perturb μ u s) μ hf.aemeasurable
    (by filter_upwards [hpos] with x hx; exact (ENNReal.ofReal_pos.2 hx).ne')
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_ne_top)
  have e2 := pushDens_one_add (T := T) hu hub hs.le
  filter_upwards [e, e2, hpos] with x hx hx2 hp
  unfold ratio
  have hpush : T ∘ₘ perturb μ u s = push T μ (fun y => 1 + s * u y) := rfl
  unfold perturb at hx ⊢
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le]
  unfold perturb at hpush
  rw [hpush]
  change (1 + s * u x)⁻¹ * pushDens T μ (fun y => 1 + s * u y) x = _
  rw [hx2, div_eq_inv_mul]
  rfl

/-- `d(δT)/dμ` is dominated by the ratio: `|v| ≤ C·r` `μ`-a.e. when `|u| ≤ C`. In particular
the paper's admissibility requirement `d(δT)/dμ ∈ L^∞(μ)` is automatic once `r` is essentially
bounded. -/
theorem abs_dirPush_le {u : S → ℝ} (hu : Measurable u) {C : ℝ} (hC : 0 ≤ C)
    (hub : ∀ᵐ x ∂μ, |u x| ≤ C) :
    ∀ᵐ x ∂μ, |dirPush T μ u x| ≤ C * ratio T μ x := by
  have iu : Integrable u μ := integrable_of_abs_le hu hub
  have iabs : Integrable (fun y => |u y|) μ := iu.abs
  have i0 : Integrable (fun _ : S => (0 : ℝ)) μ := integrable_const 0
  have iC : Integrable (fun y => C - |u y|) μ := (integrable_const C).sub iabs
  have i1 : Integrable (fun _ : S => (1 : ℝ)) μ := integrable_const 1
  have a1 := pushDens_add4 (T := T) (φ₁ := u) (φ₂ := fun y => -u y) (φ₃ := fun y => |u y|)
    (φ₄ := fun _ => 0) hu hu.abs iu iu.neg iabs i0 (Filter.Eventually.of_forall fun x => by
      rcases le_total 0 (u x) with h | h
      · rw [ENNReal.ofReal_of_nonpos (show -u x ≤ 0 by linarith), abs_of_nonneg h]; simp
      · rw [ENNReal.ofReal_of_nonpos h, abs_of_nonpos h]; simp)
  have a2 := pushDens_add4 (T := T) (φ₁ := fun y => |u y|) (φ₂ := fun y => C - |u y|)
    (φ₃ := fun _ => C * 1) (φ₄ := fun _ => 0) hu.abs measurable_const iabs iC
    ((integrable_const C).congr (by simp)) i0 (by
      filter_upwards [hub] with x hx
      rw [← ENNReal.ofReal_add (abs_nonneg _) (by linarith)]
      simp)
  have a3 := pushDens_smul (T := T) (φ := fun _ => (1 : ℝ)) hC measurable_const i1
  rw [pushDens_one] at a3
  filter_upwards [a1, a2, a3, pushDens_zero (T := T) (μ := μ)] with x h1 h2 h3 h0
  simp only [Pi.zero_apply] at h0
  rw [h0] at h1 h2
  rw [h3] at h2
  have p1 : 0 ≤ pushDens T μ u x := ENNReal.toReal_nonneg
  have p2 : 0 ≤ pushDens T μ (fun y => -u y) x := ENNReal.toReal_nonneg
  have p3 : 0 ≤ pushDens T μ (fun y => C - |u y|) x := ENNReal.toReal_nonneg
  unfold dirPush
  rw [abs_le]
  constructor <;> linarith

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem ratio_nonneg (x : S) : 0 ≤ ratio T μ x := ENNReal.toReal_nonneg

end Perturb

/-! ### Differentiation under the integral -/

section Calculus

/-- Pointwise bounds on the line `s ↦ (r + s·v)/(1 + s·u)` for `|s|·C ≤ ½`. -/
theorem quot_bounds {r v u s C : ℝ} (hr : 0 ≤ r) (hu : |u| ≤ C) (hv : |v| ≤ C * r)
    (hs : |s| * C ≤ 1 / 2) :
    1 / 2 ≤ 1 + s * u ∧ |(r + s * v) / (1 + s * u) - r| ≤ 4 * (|s| * C * r) ∧
      |v - r * u| ≤ 2 * C * r := by
  have hsu : |s * u| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |s| * |u| ≤ |s| * C := mul_le_mul_of_nonneg_left hu (abs_nonneg s)
      _ ≤ 1 / 2 := hs
  have h1 : 1 / 2 ≤ 1 + s * u := by linarith [neg_abs_le (s * u)]
  have hvru : |v - r * u| ≤ 2 * C * r := by
    calc |v - r * u| ≤ |v| + |r * u| := abs_sub _ _
      _ = |v| + r * |u| := by rw [abs_mul, abs_of_nonneg hr]
      _ ≤ C * r + r * C := by gcongr
      _ = 2 * C * r := by ring
  refine ⟨h1, ?_, hvru⟩
  have hpos : 0 < 1 + s * u := by linarith
  have e : (r + s * v) / (1 + s * u) - r = s * (v - r * u) / (1 + s * u) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hpos, abs_mul, div_le_iff₀ hpos]
  calc |s| * |v - r * u| ≤ |s| * (2 * C * r) := mul_le_mul_of_nonneg_left hvru (abs_nonneg s)
    _ = 4 * (|s| * C * r) * (1 / 2) := by ring
    _ ≤ 4 * (|s| * C * r) * (1 + s * u) := by
        have : 0 ≤ 4 * (|s| * C * r) := by
          have := abs_nonneg s
          have hC : 0 ≤ C := le_trans (abs_nonneg u) hu
          positivity
        exact mul_le_mul_of_nonneg_left h1 this

/-- **Differentiation under the integral along the line**: with `r ∈ [0, b]`, `|u| ≤ C`,
`|v| ≤ C·r` a.e., and `g` differentiable with derivative `g'` bounded by `M` on an
`η`-neighbourhood of the (essential) values of `r`,
`d/ds|₀ ∫ g((r + s·v)/(1 + s·u)) dν = ∫ g'(r)·(v − r·u) dν`. -/
theorem hasDerivAt_integral_quot {ν : Measure S} [IsFiniteMeasure ν] {r v u : S → ℝ}
    (hr_m : AEStronglyMeasurable r ν) (hv_m : AEStronglyMeasurable v ν)
    (hu_m : AEStronglyMeasurable u ν) {b C η M : ℝ} (hb : 0 ≤ b) (hC : 0 ≤ C) (hη : 0 < η)
    (hr : ∀ᵐ x ∂ν, 0 ≤ r x ∧ r x ≤ b) (hub : ∀ᵐ x ∂ν, |u x| ≤ C)
    (hv : ∀ᵐ x ∂ν, |v x| ≤ C * r x)
    {g g' : ℝ → ℝ} (hgc : Continuous g) (hg'm : Measurable g')
    (hgd : ∀ᵐ x ∂ν, ∀ y, |y - r x| ≤ η → HasDerivAt g (g' y) y)
    (hg'b : ∀ᵐ x ∂ν, ∀ y, |y - r x| ≤ η → |g' y| ≤ M) :
    HasDerivAt (fun s => ∫ x, g ((r x + s * v x) / (1 + s * u x)) ∂ν)
      (∫ x, g' (r x) * (v x - r x * u x) ∂ν) 0 := by
  set ε : ℝ := min (1 / (2 * (C + 1))) (η / (4 * (C + 1) * (b + 1))) with hε
  have hε0 : 0 < ε := by
    rw [hε]; apply lt_min <;> positivity
  have hsε : ∀ s ∈ Metric.ball (0 : ℝ) ε, |s| * C ≤ 1 / 2 ∧ 4 * (|s| * C * b) ≤ η := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    have h1 : |s| < 1 / (2 * (C + 1)) := lt_of_lt_of_le hs (min_le_left _ _)
    have h2 : |s| < η / (4 * (C + 1) * (b + 1)) := lt_of_lt_of_le hs (min_le_right _ _)
    have hs0 := abs_nonneg s
    constructor
    · rw [lt_div_iff₀ (by positivity)] at h1
      nlinarith
    · rw [lt_div_iff₀ (by positivity)] at h2
      nlinarith [mul_nonneg hs0 hC, mul_nonneg (mul_nonneg hs0 hC) hb]
  set F : ℝ → S → ℝ := fun s x => g ((r x + s * v x) / (1 + s * u x)) with hF
  set F' : ℝ → S → ℝ := fun s x =>
    g' ((r x + s * v x) / (1 + s * u x)) * ((v x - r x * u x) / (1 + s * u x) ^ 2) with hF'
  have hq_m : ∀ s : ℝ, AEStronglyMeasurable (fun x => (r x + s * v x) / (1 + s * u x)) ν :=
    fun s => ((hr_m.aemeasurable.add (hv_m.aemeasurable.const_mul s)).div
      (aemeasurable_const.add (hu_m.aemeasurable.const_mul s))).aestronglyMeasurable
  -- the bound on `g` over `[0, b]`
  obtain ⟨Kg, hKg⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    hgc.continuousOn
  have hF_int : Integrable (F 0) ν := by
    refine Integrable.of_bound (hgc.comp_aestronglyMeasurable (hq_m 0)) Kg ?_
    filter_upwards [hr] with x hx
    simp only [hF, zero_mul, add_zero]
    rw [div_one]
    exact hKg (r x) ⟨hx.1, hx.2⟩
  have hF'_meas : AEStronglyMeasurable (F' 0) ν := by
    refine ((hg'm.comp_aemeasurable (hq_m 0).aemeasurable).aestronglyMeasurable).mul ?_
    exact ((hv_m.aemeasurable.sub (hr_m.aemeasurable.mul hu_m.aemeasurable)).div
      ((aemeasurable_const.add (hu_m.aemeasurable.const_mul 0)).pow_const 2)).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F')
    (x₀ := 0) (bound := fun _ => M * (2 * C * b) * 4) (Metric.ball_mem_nhds 0 hε0)
    (Filter.Eventually.of_forall fun s => hgc.comp_aestronglyMeasurable (hq_m s)) hF_int
    hF'_meas ?_ (integrable_const _) ?_
  · have hval : ∫ x, F' 0 x ∂ν = ∫ x, g' (r x) * (v x - r x * u x) ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [hF']
    rw [← hval]
    exact key.2
  · filter_upwards [hr, hub, hv, hg'b] with x hx hux hvx hgx
    intro s hs
    obtain ⟨hs1, hs2⟩ := hsε s hs
    obtain ⟨b1, b2, b3⟩ := quot_bounds hx.1 hux hvx hs1
    have hq : |(r x + s * v x) / (1 + s * u x) - r x| ≤ η := by
      refine b2.trans (le_trans ?_ hs2)
      have := abs_nonneg s
      have : |s| * C * r x ≤ |s| * C * b :=
        mul_le_mul_of_nonneg_left hx.2 (mul_nonneg (abs_nonneg s) hC)
      linarith
    have hM := hgx _ hq
    have hden : 1 / 4 ≤ (1 + s * u x) ^ 2 := by nlinarith
    have hden0 : 0 < (1 + s * u x) ^ 2 := by positivity
    simp only [hF', Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hden0]
    have hvb : |v x - r x * u x| ≤ 2 * C * b := b3.trans (by nlinarith [hx.2])
    have hfrac : |v x - r x * u x| / (1 + s * u x) ^ 2 ≤ 2 * C * b * 4 := by
      rw [div_le_iff₀ hden0]; nlinarith [abs_nonneg (v x - r x * u x)]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
    calc |g' ((r x + s * v x) / (1 + s * u x))| * (|v x - r x * u x| / (1 + s * u x) ^ 2)
        ≤ M * (2 * C * b * 4) :=
          mul_le_mul hM hfrac (div_nonneg (abs_nonneg _) hden0.le) hM0
      _ = M * (2 * C * b) * 4 := by ring
  · filter_upwards [hr, hub, hv, hgd] with x hx hux hvx hgx
    intro s hs
    obtain ⟨hs1, hs2⟩ := hsε s hs
    obtain ⟨b1, b2, -⟩ := quot_bounds hx.1 hux hvx hs1
    have hq : |(r x + s * v x) / (1 + s * u x) - r x| ≤ η := by
      refine b2.trans (le_trans ?_ hs2)
      have : |s| * C * r x ≤ |s| * C * b :=
        mul_le_mul_of_nonneg_left hx.2 (mul_nonneg (abs_nonneg s) hC)
      linarith
    have hne : 1 + s * u x ≠ 0 := by linarith
    have hc : HasDerivAt (fun y : ℝ => r x + y * v x) (1 * v x) s :=
      ((hasDerivAt_id' s).mul_const (v x)).const_add (r x)
    have hd : HasDerivAt (fun y : ℝ => 1 + y * u x) (1 * u x) s :=
      ((hasDerivAt_id' s).mul_const (u x)).const_add 1
    have hquot := hc.div hd hne
    have hcomp := (hgx _ hq).comp s hquot
    refine hcomp.congr_deriv ?_
    simp only [hF']
    congr 1
    field_simp
    ring

end Calculus

/-! ### The loss along an admissible line -/

section LossLine

variable {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S} [IsFiniteMeasure μ]
  {ν : Measure S} [IsFiniteMeasure ν]

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem measurable_ratio : Measurable (ratio T μ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem measurable_pushDens (φ : S → ℝ) : Measurable (pushDens T μ φ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
theorem measurable_dirPush (u : S → ℝ) : Measurable (dirPush T μ u) :=
  (measurable_pushDens u).sub (measurable_pushDens _)

omit [IsFiniteMeasure ν] in
/-- For `|s|·C < 1`, the loss at `μ + sδ` is the integral of `g` along the explicit quotient. -/
theorem loss_perturb_eq (hν : ν ≪ μ) {u : S → ℝ} (hu : Measurable u) {C : ℝ}
    (hub : ∀ᵐ x ∂μ, |u x| ≤ C) (g : ℝ → ℝ) {s : ℝ} (hs : |s| * C < 1) :
    loss T g ν (perturb μ u s) =
      ∫ x, g ((ratio T μ x + s * dirPush T μ u x) / (1 + s * u x)) ∂ν := by
  unfold loss
  refine integral_congr_ae ?_
  filter_upwards [hν.ae_le (ratio_perturb (T := T) hu hub hs)] with x hx
  rw [hx]

theorem eventually_abs_mul_lt' (C : ℝ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ s in 𝓝 (0 : ℝ), |s| * C < K := by
  have h : Tendsto (fun s : ℝ => |s| * C) (𝓝 0) (𝓝 (|0| * C)) :=
    (continuous_abs.mul continuous_const).tendsto 0
  exact h.eventually (gt_mem_nhds (by simpa using hK))

theorem eventually_abs_mul_lt (C : ℝ) : ∀ᶠ s in 𝓝 (0 : ℝ), |s| * C < 1 :=
  eventually_abs_mul_lt' C one_pos

/-- **The derivative along the line, general `g`-form**: for a continuous `g` whose derivative
`g'` is measurable and bounded near the essential values of `r`,
`d/ds|₀ 𝓛_{g,ν}(μ + sδ) = ∫ g'(r)·(v − r·u) dν`, with `v = d(δT)/dμ`. No invariant measure is
used. -/
theorem hasDerivAt_loss_perturb_of_continuous (hν : ν ≪ μ) {u : S → ℝ} (hu : Measurable u)
    {b C η M : ℝ} (hb : 0 ≤ b) (hC : 0 ≤ C) (hη : 0 < η) (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    (hrb : ∀ᵐ x ∂μ, ratio T μ x ≤ b)
    {g g' : ℝ → ℝ} (hgc : Continuous g) (hg'm : Measurable g')
    (hgd : ∀ᵐ x ∂μ, ∀ y, |y - ratio T μ x| ≤ η → HasDerivAt g (g' y) y)
    (hg'b : ∀ᵐ x ∂μ, ∀ y, |y - ratio T μ x| ≤ η → |g' y| ≤ M) :
    HasDerivAt (fun s => loss T g ν (perturb μ u s))
      (∫ x, g' (ratio T μ x) * (dirPush T μ u x - ratio T μ x * u x) ∂ν) 0 := by
  have key := hasDerivAt_integral_quot (ν := ν) (r := ratio T μ) (v := dirPush T μ u) (u := u)
    measurable_ratio.aestronglyMeasurable (measurable_dirPush u).aestronglyMeasurable
    hu.aestronglyMeasurable hb hC hη
    (hν.ae_le (by filter_upwards [hrb] with x hx using ⟨ratio_nonneg x, hx⟩))
    (hν.ae_le hub) (hν.ae_le (abs_dirPush_le hu hC hub)) hgc hg'm (hν.ae_le hgd)
    (hν.ae_le hg'b)
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [eventually_abs_mul_lt C] with s hs
  exact loss_perturb_eq hν hu hub g hs

end LossLine

/-! ### The paper's generator class: `g` differentiable on `ℝ₊*` with continuous derivative -/

section PaperG

variable {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S} [IsFiniteMeasure μ]
  {ν : Measure S} [IsFiniteMeasure ν]

/-- Clamp to `[c, d]`. -/
def clamp (c d y : ℝ) : ℝ := max c (min y d)

theorem continuous_clamp (c d : ℝ) : Continuous (clamp c d) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp_mem {c d : ℝ} (h : c ≤ d) (y : ℝ) : clamp c d y ∈ Set.Icc c d :=
  ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

theorem clamp_of_mem {c d y : ℝ} (h : y ∈ Set.Icc c d) : clamp c d y = y := by
  unfold clamp; rw [min_eq_left h.2, max_eq_right h.1]

/-- For `s` near `0`, the ratio of `μ + sδ` stays `a/4`-close to `r`, `μ`-a.e. -/
theorem eventually_ratio_perturb_near {u : S → ℝ} (hu : Measurable u) {a b C : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hub : ∀ᵐ x ∂μ, |u x| ≤ C) (hrb : ∀ᵐ x ∂μ, ratio T μ x ≤ b) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᵐ x ∂μ, |ratio T (perturb μ u s) x - ratio T μ x| ≤ a / 4 := by
  filter_upwards [eventually_abs_mul_lt' C (show (0 : ℝ) < 1 / 2 by norm_num),
    eventually_abs_mul_lt' (4 * C * b) (show 0 < a / 4 by positivity)] with s hs1 hs2
  filter_upwards [ratio_perturb (T := T) hu hub (hs1.trans (by norm_num)),
    abs_dirPush_le (T := T) hu hC hub, hub, hrb] with x hx hv hux hrx
  rw [hx]
  have hb := (quot_bounds (ratio_nonneg x) hux hv hs1.le).2.1
  refine hb.trans ?_
  have : |s| * C * ratio T μ x ≤ |s| * C * b :=
    mul_le_mul_of_nonneg_left hrx (mul_nonneg (abs_nonneg s) hC)
  nlinarith

/-- **The derivative along the line, for the paper's generators** (`g : ℝ₊* → ℝ` differentiable
with continuous derivative; the paper's local Lipschitz bound on `g'` is not needed): if `r` is
essentially valued in `[a, b] ⊂ (0, ∞)`, then
`d/ds|₀ 𝓛_{g,ν}(μ + sδ) = ∫ g'(r)·(v − r·u) dν`. -/
theorem hasDerivAt_loss_perturb (hν : ν ≪ μ) {u : S → ℝ} (hu : Measurable u) {a b C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hC : 0 ≤ C) (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    (hr : ∀ᵐ x ∂μ, a ≤ ratio T μ x ∧ ratio T μ x ≤ b)
    {g g' : ℝ → ℝ} (hgd : ∀ y, 0 < y → HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Set.Ioi 0)) :
    HasDerivAt (fun s => loss T g ν (perturb μ u s))
      (∫ x, g' (ratio T μ x) * (dirPush T μ u x - ratio T μ x * u x) ∂ν) 0 := by
  set c := a / 2 with hc
  set d := b + a / 2 with hd
  have hcd : c ≤ d := by rw [hc, hd]; linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hIcc : Set.Icc c d ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le hc0 hy.1
  have hgcont : ContinuousOn g (Set.Icc c d) := fun y hy =>
    (hgd y (hIcc hy)).continuousAt.continuousWithinAt
  set g₁ : ℝ → ℝ := fun y => g (clamp c d y) with hg₁
  set g₁' : ℝ → ℝ := fun y => g' (clamp c d y) with hg₁'
  have hg₁c : Continuous g₁ := hgcont.comp_continuous (continuous_clamp c d) (clamp_mem hcd)
  have hg₁'c : Continuous g₁' :=
    (hg'c.mono hIcc).comp_continuous (continuous_clamp c d) (clamp_mem hcd)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := c) (b := d)).exists_bound_of_continuousOn
    (hg'c.mono hIcc)
  have hnear : ∀ x, a ≤ ratio T μ x ∧ ratio T μ x ≤ b → ∀ y, |y - ratio T μ x| ≤ a / 4 →
      y ∈ Set.Ioo c d := by
    intro x hx y hy
    rw [abs_le] at hy
    constructor <;> [rw [hc]; rw [hd]] <;> linarith [hx.1, hx.2]
  have hgd₁ : ∀ᵐ x ∂μ, ∀ y, |y - ratio T μ x| ≤ a / 4 → HasDerivAt g₁ (g₁' y) y := by
    filter_upwards [hr] with x hx y hy
    have hyI := hnear x hx y hy
    have hev : g₁ =ᶠ[𝓝 y] g := by
      filter_upwards [isOpen_Ioo.mem_nhds hyI] with z hz
      simp only [hg₁, clamp_of_mem (Set.Ioo_subset_Icc_self hz)]
    have : g₁' y = g' y := by simp only [hg₁', clamp_of_mem (Set.Ioo_subset_Icc_self hyI)]
    rw [this]
    exact (hgd y (lt_trans hc0 hyI.1)).congr_of_eventuallyEq hev
  have hg'b₁ : ∀ᵐ x ∂μ, ∀ y, |y - ratio T μ x| ≤ a / 4 → |g₁' y| ≤ M :=
    Filter.Eventually.of_forall fun x y _ => by
      simpa [Real.norm_eq_abs] using hM _ (clamp_mem hcd y)
  have key := hasDerivAt_loss_perturb_of_continuous (T := T) (b := b) hν hu (by linarith) hC
    (show 0 < a / 4 by positivity) hub (by filter_upwards [hr] with x hx using hx.2) hg₁c
    hg₁'c.measurable hgd₁ hg'b₁
  have hval : ∫ x, g₁' (ratio T μ x) * (dirPush T μ u x - ratio T μ x * u x) ∂ν =
      ∫ x, g' (ratio T μ x) * (dirPush T μ u x - ratio T μ x * u x) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hν.ae_le hr] with x hx
    have : ratio T μ x ∈ Set.Icc c d := by
      constructor <;> [rw [hc]; rw [hd]] <;> linarith [hx.1, hx.2]
    simp only [hg₁', clamp_of_mem this]
  rw [hval] at key
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ratio_perturb_near (T := T) hu ha hC hub
    (by filter_upwards [hr] with x hx using hx.2)] with s hs
  unfold loss
  refine integral_congr_ae ?_
  filter_upwards [hν.ae_le hs, hν.ae_le hr] with x hx hrx
  have : ratio T (perturb μ u s) x ∈ Set.Icc c d := by
    rw [abs_le] at hx
    constructor <;> [rw [hc]; rw [hd]] <;> linarith [hrx.1, hrx.2]
  simp only [hg₁, clamp_of_mem this]

end PaperG

/-! ### The adjoint step: `∫ ψ d(δT) = ∫ Tψ dδ` -/

section AdjointStep

variable {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- An `L^∞(μ)` function has an a.e. bound. -/
theorem exists_ae_abs_le_of_memLp_top {f : S → ℝ} (hf : MemLp f ⊤ μ) :
    ∃ K, ∀ᵐ x ∂μ, |f x| ≤ K := by
  refine ⟨(eLpNorm f ⊤ μ).toReal, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [Real.enorm_eq_ofReal_abs] at hx
  rw [eLpNorm_exponent_top]
  have hfin : eLpNormEssSup f μ ≠ ⊤ := by
    have := hf.2; rw [eLpNorm_exponent_top] at this; exact this.ne
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hx

omit [IsFiniteMeasure μ] in
/-- The function action of a Markov kernel on an a.e.-bounded function is a.e.-bounded, when
`μT ≪ μ`. -/
theorem ae_abs_funAct_le (hac : T ∘ₘ μ ≪ μ) {ψ : S → ℝ} {L : ℝ} (hψb : ∀ᵐ x ∂μ, |ψ x| ≤ L) :
    ∀ᵐ x ∂μ, |funAct T ψ x| ≤ L := by
  have h1 : ∀ᵐ y ∂(T ∘ₘ μ), |ψ y| ≤ L := hac.ae_le hψb
  filter_upwards [Measure.ae_ae_of_ae_comp h1] with x hx
  have := norm_integral_le_of_norm_le_const (μ := T x) (f := ψ) (C := L)
    (by simpa [Real.norm_eq_abs] using hx)
  simpa [Real.norm_eq_abs, funAct] using this

omit [IsMarkovKernel T] [IsFiniteMeasure μ] in
/-- `ψ =ᵐ[μ] ψ'` gives `Tψ =ᵐ[μ] Tψ'` when `μT ≪ μ`, with no measurability of `ψ`. -/
theorem funAct_congr_of_ac (hac : T ∘ₘ μ ≪ μ) {ψ ψ' : S → ℝ} (h : ψ =ᵐ[μ] ψ') :
    funAct T ψ =ᵐ[μ] funAct T ψ' := by
  have h1 : ∀ᵐ y ∂(T ∘ₘ μ), ψ y = ψ' y := hac.ae_le h
  filter_upwards [Measure.ae_ae_of_ae_comp h1] with x hx
  exact integral_congr_ae hx

/-- **The adjoint step for one half of a direction**: `∫ ψ · d((φ⁺μ)T)/dμ dμ = ∫ φ⁺ · Tψ dμ`. -/
theorem integral_mul_pushDens {φ : S → ℝ} (hφ : Measurable φ) {K : ℝ}
    (hφb : ∀ᵐ x ∂μ, |φ x| ≤ K) (hac : T ∘ₘ μ ≪ μ) {ψ : S → ℝ} (hψ : Measurable ψ) {L : ℝ}
    (hψb : ∀ᵐ x ∂μ, |ψ x| ≤ L) :
    ∫ x, ψ x * pushDens T μ φ x ∂μ = ∫ x, max (φ x) 0 * funAct T ψ x ∂μ := by
  have iφ : Integrable φ μ := integrable_of_abs_le hφ hφb
  haveI := push_isFinite (T := T) iφ
  haveI := isFiniteMeasure_withDensity_ofReal iφ.2
  set m := μ.withDensity fun y => ENNReal.ofReal (φ y) with hm
  have hξ : push T μ φ ≪ μ :=
    ((withDensity_absolutelyContinuous μ _).comp_right T).trans hac
  have hψξ : Integrable ψ (push T μ φ) :=
    Integrable.of_bound hψ.aestronglyMeasurable L
      (by filter_upwards [hξ.ae_le hψb] with x hx; simpa [Real.norm_eq_abs] using hx)
  have hpush : push T μ φ = (m ⊗ₘ T).map Prod.snd := by
    rw [← Measure.snd, Measure.snd_compProd]; rfl
  have hint2 : Integrable (fun z : S × S => ψ z.2) (m ⊗ₘ T) := by
    have := hψξ
    rw [hpush] at this
    exact (integrable_map_measure hψ.aestronglyMeasurable measurable_snd.aemeasurable).1 this
  calc ∫ x, ψ x * pushDens T μ φ x ∂μ
      = ∫ x, ((push T μ φ).rnDeriv μ x).toReal • ψ x ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [pushDens, smul_eq_mul, mul_comm]
    _ = ∫ x, ψ x ∂(push T μ φ) := integral_rnDeriv_smul hξ
    _ = ∫ z, ψ z.2 ∂(m ⊗ₘ T) := by
        rw [hpush, integral_map measurable_snd.aemeasurable hψ.aestronglyMeasurable]
    _ = ∫ x, funAct T ψ x ∂m := Measure.integral_compProd hint2
    _ = ∫ x, (ENNReal.ofReal (φ x)).toReal • funAct T ψ x ∂μ :=
        integral_withDensity_eq_integral_toReal_smul hφ.ennreal_ofReal
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = ∫ x, max (φ x) 0 * funAct T ψ x ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [ENNReal.toReal_ofReal', smul_eq_mul]

/-- **The adjoint step of the paper's proof** (`⟨ψλ ∣ δT⟩ = ⟨(ψλ)T^λ ∣ δ⟩`, here read with no
invariant measure): `∫ ψ · d(δT)/dμ dμ = ∫ Tψ · dδ/dμ dμ`, for `ψ` bounded and `δ = uμ`. -/
theorem integral_mul_dirPush {u : S → ℝ} (hu : Measurable u) {C : ℝ}
    (hub : ∀ᵐ x ∂μ, |u x| ≤ C) (hac : T ∘ₘ μ ≪ μ) {ψ : S → ℝ} (hψ : Measurable ψ) {L : ℝ}
    (hψb : ∀ᵐ x ∂μ, |ψ x| ≤ L) :
    ∫ x, ψ x * dirPush T μ u x ∂μ = ∫ x, funAct T ψ x * u x ∂μ := by
  have hub' : ∀ᵐ x ∂μ, |(-u x)| ≤ C := by filter_upwards [hub] with x hx; rwa [abs_neg]
  have iu : Integrable u μ := integrable_of_abs_le hu hub
  haveI := push_isFinite (T := T) iu
  haveI := push_isFinite (T := T) iu.neg
  have iP1 : Integrable (fun x => ψ x * pushDens T μ u x) μ :=
    (Measure.integrable_toReal_rnDeriv).bdd_mul hψ.aestronglyMeasurable
      (by simpa [Real.norm_eq_abs] using hψb)
  have iP2 : Integrable (fun x => ψ x * pushDens T μ (fun y => -u y) x) μ :=
    (Measure.integrable_toReal_rnDeriv).bdd_mul hψ.aestronglyMeasurable
      (by simpa [Real.norm_eq_abs] using hψb)
  have hTm : AEStronglyMeasurable (funAct T ψ) μ :=
    hψ.stronglyMeasurable.integral_kernel.aestronglyMeasurable
  have hTb := ae_abs_funAct_le hac hψb
  have iT1 : Integrable (fun x => max (u x) 0 * funAct T ψ x) μ :=
    (integrable_of_abs_le (hu.max measurable_const) (K := C) (by
      filter_upwards [hub] with x hx
      rw [abs_le] at hx ⊢; constructor
      · linarith [le_max_right (u x) 0, abs_nonneg (u x), neg_abs_le (u x)]
      · exact max_le hx.2 (by linarith [hx.1, hx.2]))).mul_bdd hTm
      (by simpa [Real.norm_eq_abs] using hTb)
  have iT2 : Integrable (fun x => max (-u x) 0 * funAct T ψ x) μ :=
    (integrable_of_abs_le (hu.neg.max measurable_const) (K := C) (by
      filter_upwards [hub] with x hx
      rw [abs_le] at hx ⊢; constructor
      · linarith [le_max_right (-u x) 0, abs_nonneg (u x), neg_abs_le (u x)]
      · exact max_le (by linarith [hx.1]) (by linarith [hx.1, hx.2]))).mul_bdd hTm
      (by simpa [Real.norm_eq_abs] using hTb)
  have e1 := integral_mul_pushDens (T := T) hu hub hac hψ hψb
  have e2 := integral_mul_pushDens (T := T) hu.neg hub' hac hψ hψb
  calc ∫ x, ψ x * dirPush T μ u x ∂μ
      = ∫ x, (ψ x * pushDens T μ u x - ψ x * pushDens T μ (fun y => -u y) x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [dirPush, mul_sub]
    _ = ∫ x, ψ x * pushDens T μ u x ∂μ - ∫ x, ψ x * pushDens T μ (fun y => -u y) x ∂μ :=
        integral_sub iP1 iP2
    _ = ∫ x, max (u x) 0 * funAct T ψ x ∂μ - ∫ x, max (-u x) 0 * funAct T ψ x ∂μ := by
        rw [e1, e2]
    _ = ∫ x, (max (u x) 0 * funAct T ψ x - max (-u x) 0 * funAct T ψ x) ∂μ :=
        (integral_sub iT1 iT2).symm
    _ = ∫ x, funAct T ψ x * u x ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rcases le_total 0 (u x) with h | h
        · rw [max_eq_left h, max_eq_right (by linarith)]; ring
        · rw [max_eq_right h, max_eq_left (by linarith)]; ring

end AdjointStep

/-! ### The first variation, represented -/

section Represent

variable {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S} [IsFiniteMeasure μ]
  {ν : Measure S} [IsFiniteMeasure ν]

/-- The paper's `ψ := g'(r)·dν/dμ`. -/
noncomputable def psi (T : Kernel S S) (g' : ℝ → ℝ) (ν μ : Measure S) : S → ℝ :=
  fun x => g' (ratio T μ x) * (ν.rnDeriv μ x).toReal

/-- The density `Tψ − rψ` of the gradient: against `λ` it is the density of
`(T^λ − r)[ψλ]` (`lem:adjoint`(3)), and against `ν_G` that of `(dν_G/dλ)·(T^λ − r)[ψλ]`. -/
noncomputable def gradDens (T : Kernel S S) (g' : ℝ → ℝ) (ν μ : Measure S) : S → ℝ :=
  fun x => funAct T (psi T g' ν μ) x - ratio T μ x * psi T g' ν μ x

/-- **The value of the first variation**: for any measurable, a.e.-bounded version `ψ₁` of
`ψ = g'(r)·dν/dμ`, `∫ g'(r)·(v − r·u) dν = ∫ (Tψ − rψ)·u dμ`. This is the paper's computation
`δ𝓛 = ∫ g'(r)[d(δT)/dμ − r dδ/dμ] dν = ⟨[ψλ](T^λ − r) ∣ δ⟩`, read in `μ`-coordinates. -/
theorem integral_deriv_eq_gradDens (hν : ν ≪ μ) (hac : T ∘ₘ μ ≪ μ) {b : ℝ}
    (hrb : ∀ᵐ x ∂μ, ratio T μ x ≤ b) {u : S → ℝ} (hu : Measurable u) {C : ℝ} (hC : 0 ≤ C)
    (hub : ∀ᵐ x ∂μ, |u x| ≤ C) {g' : ℝ → ℝ} {ψ₁ : S → ℝ} (hψ₁m : Measurable ψ₁) {K : ℝ}
    (hψ₁b : ∀ᵐ x ∂μ, |ψ₁ x| ≤ K) (hψe : psi T g' ν μ =ᵐ[μ] ψ₁) :
    ∫ x, g' (ratio T μ x) * (dirPush T μ u x - ratio T μ x * u x) ∂ν =
      ∫ x, gradDens T g' ν μ x * u x ∂μ := by
  have hTe := funAct_congr_of_ac hac hψe
  have hvb := abs_dirPush_le (T := T) hu hC hub
  have hTb := ae_abs_funAct_le hac hψ₁b
  have hTm : AEStronglyMeasurable (funAct T ψ₁) μ :=
    hψ₁m.stronglyMeasurable.integral_kernel.aestronglyMeasurable
  have i1 : Integrable (fun x => ψ₁ x * dirPush T μ u x) μ :=
    Integrable.of_bound (hψ₁m.mul (measurable_dirPush u)).aestronglyMeasurable
      (K * (C * b)) (by
        filter_upwards [hψ₁b, hvb, hrb] with x h1 h2 h3
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hC)) (abs_nonneg _)
          ((abs_nonneg _).trans h1))
  have i2 : Integrable (fun x => ratio T μ x * ψ₁ x * u x) μ :=
    Integrable.of_bound ((measurable_ratio.mul hψ₁m).mul hu).aestronglyMeasurable
      (b * K * C) (by
        filter_upwards [hψ₁b, hub, hrb] with x h1 h2 h3
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (ratio_nonneg x)]
        have hK : 0 ≤ K := (abs_nonneg _).trans h1
        have hb : 0 ≤ b := (ratio_nonneg x).trans h3
        exact mul_le_mul (mul_le_mul h3 h1 (abs_nonneg _) hb) h2 (abs_nonneg _)
          (mul_nonneg hb hK))
  have i3 : Integrable (fun x => funAct T ψ₁ x * u x) μ :=
    Integrable.of_bound (hTm.mul hu.aestronglyMeasurable) (K * C) (by
      filter_upwards [hTb, hub] with x h1 h2
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
  calc ∫ x, g' (ratio T μ x) * (dirPush T μ u x - ratio T μ x * u x) ∂ν
      = ∫ x, (ν.rnDeriv μ x).toReal •
          (g' (ratio T μ x) * (dirPush T μ u x - ratio T μ x * u x)) ∂μ :=
        (integral_rnDeriv_smul hν).symm
    _ = ∫ x, (ψ₁ x * dirPush T μ u x - ratio T μ x * ψ₁ x * u x) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hψe] with x hx
        simp only [psi] at hx
        rw [smul_eq_mul, ← hx]
        ring
    _ = ∫ x, ψ₁ x * dirPush T μ u x ∂μ - ∫ x, ratio T μ x * ψ₁ x * u x ∂μ :=
        integral_sub i1 i2
    _ = ∫ x, funAct T ψ₁ x * u x ∂μ - ∫ x, ratio T μ x * ψ₁ x * u x ∂μ := by
        rw [integral_mul_dirPush (T := T) hu hub hac hψ₁m hψ₁b]
    _ = ∫ x, (funAct T ψ₁ x * u x - ratio T μ x * ψ₁ x * u x) ∂μ := (integral_sub i3 i2).symm
    _ = ∫ x, gradDens T g' ν μ x * u x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hψe, hTe] with x h1 h2
        simp only [gradDens]
        rw [h1, h2]
        ring

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- `ψ = g'(r)·dν/dμ` has a measurable, `μ`-a.e. bounded version; so does `Tψ − rψ`. -/
theorem exists_psi_version (hac : T ∘ₘ μ ≪ μ) {W : ℝ}
    (hw : ∀ᵐ x ∂μ, |(ν.rnDeriv μ x).toReal| ≤ W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ᵐ x ∂μ, a ≤ ratio T μ x ∧ ratio T μ x ≤ b) {g' : ℝ → ℝ}
    (hg'c : ContinuousOn g' (Set.Ioi 0)) :
    ∃ ψ₁ : S → ℝ, ∃ K : ℝ, Measurable ψ₁ ∧ (∀ᵐ x ∂μ, |ψ₁ x| ≤ K) ∧
      psi T g' ν μ =ᵐ[μ] ψ₁ ∧
      gradDens T g' ν μ =ᵐ[μ] (fun x => funAct T ψ₁ x - ratio T μ x * ψ₁ x) ∧
      Measurable (fun x => funAct T ψ₁ x - ratio T μ x * ψ₁ x) ∧
      (∀ᵐ x ∂μ, |funAct T ψ₁ x - ratio T μ x * ψ₁ x| ≤ K + b * K) := by
  have hIcc : Set.Icc a b ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le ha hy.1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hg'c.mono hIcc)
  have hgc : Continuous fun y => g' (clamp a b y) :=
    (hg'c.mono hIcc).comp_continuous (continuous_clamp a b) (clamp_mem hab)
  set ψ₁ : S → ℝ := fun x => g' (clamp a b (ratio T μ x)) * (ν.rnDeriv μ x).toReal with hψ₁
  have hψ₁m : Measurable ψ₁ :=
    (hgc.measurable.comp measurable_ratio).mul (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hψ₁b : ∀ᵐ x ∂μ, |ψ₁ x| ≤ M * W := by
    filter_upwards [hw] with x hx
    rw [hψ₁, abs_mul]
    have h1 := hM _ (clamp_mem hab (ratio T μ x))
    rw [Real.norm_eq_abs] at h1
    exact mul_le_mul h1 hx (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hψe : psi T g' ν μ =ᵐ[μ] ψ₁ := by
    filter_upwards [hr] with x hx
    simp only [psi, hψ₁, clamp_of_mem (⟨hx.1, hx.2⟩ : ratio T μ x ∈ Set.Icc a b)]
  have hTe := funAct_congr_of_ac hac hψe
  refine ⟨ψ₁, M * W, hψ₁m, hψ₁b, hψe, ?_, ?_, ?_⟩
  · filter_upwards [hψe, hTe] with x h1 h2
    simp only [gradDens]; rw [h1, h2]
  · exact hψ₁m.stronglyMeasurable.integral_kernel.measurable.sub
      (measurable_ratio.mul hψ₁m)
  · filter_upwards [ae_abs_funAct_le hac hψ₁b, hψ₁b, hr] with x h1 h2 h3
    calc |funAct T ψ₁ x - ratio T μ x * ψ₁ x| ≤ |funAct T ψ₁ x| + |ratio T μ x * ψ₁ x| :=
          abs_sub _ _
      _ ≤ M * W + b * (M * W) := by
          rw [abs_mul, abs_of_nonneg (ratio_nonneg x)]
          exact add_le_add h1 (mul_le_mul h3.2 h2 (abs_nonneg _) (by linarith [h3.1]))

/-- **The first variation, in `μ`-coordinates** (no invariant measure used):
`d/ds|₀ 𝓛_{g,ν}(μ + sδ) = ∫ (Tψ − rψ)·u dμ` for every admissible `δ = uμ`. -/
theorem hasDerivAt_loss_gradDens (hν : ν ≪ μ) {W : ℝ}
    (hw : ∀ᵐ x ∂μ, |(ν.rnDeriv μ x).toReal| ≤ W) (hac : T ∘ₘ μ ≪ μ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : ∀ᵐ x ∂μ, a ≤ ratio T μ x ∧ ratio T μ x ≤ b)
    {g g' : ℝ → ℝ} (hgd : ∀ y, 0 < y → HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Set.Ioi 0))
    {u : S → ℝ} (hu : Measurable u) {C : ℝ} (hC : 0 ≤ C) (hub : ∀ᵐ x ∂μ, |u x| ≤ C) :
    HasDerivAt (fun s => loss T g ν (perturb μ u s))
      (∫ x, gradDens T g' ν μ x * u x ∂μ) 0 := by
  have key := hasDerivAt_loss_perturb (T := T) hν hu ha hab hC hub hr hgd hg'c
  obtain ⟨ψ₁, K, hψ₁m, hψ₁b, hψe, -⟩ := exists_psi_version (T := T) hac hw ha hab hr hg'c
  rw [integral_deriv_eq_gradDens hν hac (by filter_upwards [hr] with x hx using hx.2) hu hC
    hub hψ₁m hψ₁b hψe] at key
  exact key


/-- First-order Taylor with a Lipschitz derivative: on `[c, d]`,
`|g(y) − g(x) − g'(x)(y − x)| ≤ K·(y − x)²`. -/
theorem abs_taylor_le_of_lipschitz {g g' : ℝ → ℝ} {c d : ℝ}
    (hgd : ∀ y ∈ Set.Icc c d, HasDerivAt g (g' y) y) {K : NNReal}
    (hK : LipschitzOnWith K g' (Set.Icc c d)) {x y : ℝ} (hx : x ∈ Set.Icc c d)
    (hy : y ∈ Set.Icc c d) : |g y - g x - g' x * (y - x)| ≤ K * (y - x) ^ 2 := by
  have hcont : ∀ p q : ℝ, p ∈ Set.Icc c d → q ∈ Set.Icc c d → ContinuousOn g (Set.Icc p q) :=
    fun p q hp hq z hz => (hgd z ⟨le_trans hp.1 hz.1, le_trans hz.2 hq.2⟩).continuousAt.continuousWithinAt
  have hderiv : ∀ p q : ℝ, p ∈ Set.Icc c d → q ∈ Set.Icc c d →
      ∀ z ∈ Set.Ioo p q, HasDerivAt g (g' z) z :=
    fun p q hp hq z hz => hgd z ⟨le_trans hp.1 hz.1.le, le_trans hz.2.le hq.2⟩
  have hlip := hK.dist_le_mul
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' hxy (hcont x y hx hy)
      (hderiv x y hx hy)
    have hξI : ξ ∈ Set.Icc c d := ⟨le_trans hx.1 hξ.1.le, le_trans hξ.2.le hy.2⟩
    have hne : y - x ≠ 0 := by linarith
    have e : g y - g x - g' x * (y - x) = (g' ξ - g' x) * (y - x) := by
      rw [sub_mul, hξe, div_mul_cancel₀ _ hne]
    rw [e, abs_mul]
    have h1 := hlip ξ hξI x hx
    rw [Real.dist_eq, Real.dist_eq] at h1
    have h2 : |ξ - x| ≤ |y - x| := by
      rw [abs_of_pos (by linarith [hξ.1]), abs_of_pos (by linarith)]; linarith [hξ.2]
    calc |g' ξ - g' x| * |y - x| ≤ (K * |ξ - x|) * |y - x| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ (K * |y - x|) * |y - x| := by gcongr
      _ = K * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  · subst hxy; simp
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' hxy (hcont y x hy hx)
      (hderiv y x hy hx)
    have hξI : ξ ∈ Set.Icc c d := ⟨le_trans hy.1 hξ.1.le, le_trans hξ.2.le hx.2⟩
    have hne : x - y ≠ 0 := by linarith
    have e : g y - g x - g' x * (y - x) = (g' ξ - g' x) * (y - x) := by
      have : g y - g x = g' ξ * (y - x) := by
        rw [hξe, show y - x = -(x - y) by ring, mul_neg, div_mul_cancel₀ _ hne]; ring
      rw [this]; ring
    rw [e, abs_mul]
    have h1 := hlip ξ hξI x hx
    rw [Real.dist_eq, Real.dist_eq] at h1
    have h2 : |ξ - x| ≤ |y - x| := by
      rw [abs_of_neg (by linarith [hξ.2]), abs_of_neg (by linarith)]; linarith [hξ.1]
    calc |g' ξ - g' x| * |y - x| ≤ (K * |ξ - x|) * |y - x| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ (K * |y - x|) * |y - x| := by gcongr
      _ = K * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **The uniform second-order remainder** (`proofs.tex`, proof of `theo:first_variation_full`:
"the remainder is second order in `(u, v)`, uniformly"), with an explicit constant: for every
direction `δ = uμ` with `‖u‖_∞ ≤ c`, `c ≤ ½`, `b·c ≤ a/2`,
`|𝓛(μ + δ) − 𝓛(μ) − ∫ (Tψ − rψ)·u dμ| ≤ ν(𝒮)·(16·K·b² + 4·M·b)·c²`,
`K` a Lipschitz constant of `g'` on `[a/3, 3b]` and `M` a bound of `|g'|` on `[a, b]`. So the
first variation is a derivative *uniformly* over the admissible class, not only along lines. -/
theorem loss_remainder_le (hν : ν ≪ μ) (hac : T ∘ₘ μ ≪ μ) {W : ℝ}
    (hw : ∀ᵐ x ∂μ, |(ν.rnDeriv μ x).toReal| ≤ W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ᵐ x ∂μ, a ≤ ratio T μ x ∧ ratio T μ x ≤ b) {g g' : ℝ → ℝ}
    (hgd : ∀ y, 0 < y → HasDerivAt g (g' y) y) (hg'c : ContinuousOn g' (Set.Ioi 0))
    {K : NNReal} (hK : LipschitzOnWith K g' (Set.Icc (a / 3) (3 * b))) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc a b, |g' y| ≤ M) {u : S → ℝ} (hu : Measurable u) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) (hcb : b * c ≤ a / 2) (hub : ∀ᵐ x ∂μ, |u x| ≤ c) :
    |loss T g ν (perturb μ u 1) - loss T g ν μ - ∫ x, gradDens T g' ν μ x * u x ∂μ| ≤
      ν.real Set.univ * (16 * K * b ^ 2 + 4 * M * b) * c ^ 2 := by
  obtain ⟨ψ₁, K₁, hψ₁m, hψ₁b, hψe, -⟩ := exists_psi_version (T := T) hac hw ha hab hr hg'c
  have hrb : ∀ᵐ x ∂μ, ratio T μ x ≤ b := by filter_upwards [hr] with x hx using hx.2
  rw [← integral_deriv_eq_gradDens hν hac hrb hu hc0 hub hψ₁m hψ₁b hψe,
    loss_perturb_eq hν hu hub g (by rw [abs_one, one_mul]; linarith)]
  unfold loss
  set r := ratio T μ with hrdef
  set v := dirPush T μ u with hvdef
  have hvb := abs_dirPush_le (T := T) hu hc0 hub
  have hrm : Measurable r := measurable_ratio
  have hvm : Measurable v := measurable_dirPush u
  have hb0 : 0 ≤ b := by linarith
  -- the range `[a/3, 3b]`
  set I := Set.Icc (a / 3) (3 * b) with hI
  have hIpos : I ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le (by positivity) hy.1
  have hgI : ∀ y ∈ I, HasDerivAt g (g' y) y := fun y hy => hgd y (hIpos hy)
  have hrI : ∀ x, a ≤ r x ∧ r x ≤ b → r x ∈ I := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hqI : ∀ x, a ≤ r x ∧ r x ≤ b → |u x| ≤ c → |v x| ≤ c * r x →
      (r x + 1 * v x) / (1 + 1 * u x) ∈ I := by
    intro x hx hux hvx
    rw [abs_le] at hux hvx
    have h1 : 1 / 2 ≤ 1 + 1 * u x := by linarith
    have hvx' : c * r x ≤ b * c := by nlinarith [hx.2]
    constructor
    · rw [le_div_iff₀ (by linarith)]; nlinarith
    · rw [div_le_iff₀ (by linarith)]; nlinarith
  -- pointwise bound
  have hpt : ∀ᵐ x ∂ν, |g ((r x + 1 * v x) / (1 + 1 * u x)) - g (r x) -
      g' (r x) * (v x - r x * u x)| ≤ (16 * K * b ^ 2 + 4 * M * b) * c ^ 2 := by
    filter_upwards [hν.ae_le hr, hν.ae_le hub, hν.ae_le hvb] with x hx hux hvx
    set q := (r x + 1 * v x) / (1 + 1 * u x) with hq
    have hpos : 0 < 1 + 1 * u x := by rw [abs_le] at hux; linarith
    have hne1 : (1 : ℝ) + u x ≠ 0 := by rw [abs_le] at hux; linarith
    have hT := abs_taylor_le_of_lipschitz hgI hK (hrI x hx) (hqI x hx hux hvx)
    have hvru : |v x - r x * u x| ≤ 2 * b * c := by
      calc |v x - r x * u x| ≤ |v x| + |r x * u x| := abs_sub _ _
        _ ≤ c * r x + r x * c := by
            rw [abs_mul, abs_of_nonneg (ratio_nonneg x)]
            exact add_le_add hvx (mul_le_mul_of_nonneg_left hux (ratio_nonneg x))
        _ ≤ 2 * b * c := by nlinarith [hx.2]
    have hqr : q - r x = (v x - r x * u x) / (1 + 1 * u x) := by
      rw [hq]; simp only [one_mul]; field_simp; ring
    have hdiv : |q - r x| ≤ 4 * b * c := by
      rw [hqr, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have : 1 / 2 ≤ 1 + 1 * u x := by rw [abs_le] at hux; linarith
      nlinarith [abs_nonneg (v x - r x * u x)]
    have hΔ : |q - r x - (v x - r x * u x)| ≤ 4 * b * c ^ 2 := by
      have e : q - r x - (v x - r x * u x) = -(u x) * (q - r x) := by
        rw [hqr]; simp only [one_mul]; field_simp; ring
      rw [e, abs_mul, abs_neg]
      calc |u x| * |q - r x| ≤ c * (4 * b * c) :=
            mul_le_mul hux hdiv (abs_nonneg _) hc0
        _ = 4 * b * c ^ 2 := by ring
    have hMr := hM (r x) ⟨hx.1, hx.2⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hMr
    have hK0 : (0 : ℝ) ≤ K := K.2
    have e2 : g q - g (r x) - g' (r x) * (v x - r x * u x) =
        (g q - g (r x) - g' (r x) * (q - r x)) + g' (r x) * (q - r x - (v x - r x * u x)) := by
      ring
    rw [e2]
    calc |(g q - g (r x) - g' (r x) * (q - r x)) + g' (r x) * (q - r x - (v x - r x * u x))|
        ≤ |g q - g (r x) - g' (r x) * (q - r x)| +
            |g' (r x) * (q - r x - (v x - r x * u x))| := abs_add_le _ _
      _ ≤ K * (q - r x) ^ 2 + M * (4 * b * c ^ 2) := by
          rw [abs_mul]; exact add_le_add hT (mul_le_mul hMr hΔ (abs_nonneg _) hM0)
      _ ≤ K * (4 * b * c) ^ 2 + M * (4 * b * c ^ 2) := by
          have : (q - r x) ^ 2 ≤ (4 * b * c) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdiv 2
          exact add_le_add_left (mul_le_mul_of_nonneg_left this hK0) _
      _ = (16 * K * b ^ 2 + 4 * M * b) * c ^ 2 := by ring
  -- integrability, through continuous stand-ins
  have hgIc : ContinuousOn g I := fun y hy => (hgI y hy).continuousAt.continuousWithinAt
  have h3b : a / 3 ≤ 3 * b := by linarith
  have hg₁ : Continuous fun y => g (clamp (a / 3) (3 * b) y) :=
    hgIc.comp_continuous (continuous_clamp _ _) (clamp_mem h3b)
  obtain ⟨Kg, hKg⟩ := (isCompact_Icc (a := a / 3) (b := 3 * b)).exists_bound_of_continuousOn hgIc
  have hq_m : AEStronglyMeasurable (fun x => (r x + 1 * v x) / (1 + 1 * u x)) ν :=
    ((hrm.add (hvm.const_mul 1)).div
      (measurable_const.add (hu.const_mul 1))).aestronglyMeasurable
  have i1 : Integrable (fun x => g ((r x + 1 * v x) / (1 + 1 * u x))) ν := by
    refine Integrable.of_bound ((hg₁.comp_aestronglyMeasurable hq_m).congr ?_) Kg ?_
    · filter_upwards [hν.ae_le hr, hν.ae_le hub, hν.ae_le hvb] with x hx hux hvx
      exact congrArg g (clamp_of_mem (hqI x hx hux hvx))
    · filter_upwards [hν.ae_le hr, hν.ae_le hub, hν.ae_le hvb] with x hx hux hvx
      exact hKg _ (hqI x hx hux hvx)
  have i2 : Integrable (fun x => g (r x)) ν := by
    refine Integrable.of_bound ((hg₁.comp_aestronglyMeasurable
      hrm.aestronglyMeasurable).congr ?_) Kg ?_
    · filter_upwards [hν.ae_le hr] with x hx
      exact congrArg g (clamp_of_mem (hrI x hx))
    · filter_upwards [hν.ae_le hr] with x hx
      exact hKg _ (hrI x hx)
  have i3 : Integrable (fun x => g' (r x) * (v x - r x * u x)) ν := by
    have hIcc : Set.Icc a b ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le ha hy.1
    have hg'₁ : Continuous fun y => g' (clamp a b y) :=
      (hg'c.mono hIcc).comp_continuous (continuous_clamp a b) (clamp_mem hab)
    refine Integrable.of_bound (((hg'₁.measurable.comp hrm).mul
      (hvm.sub (hrm.mul hu))).aestronglyMeasurable.congr ?_)
      (M * (2 * b * c)) ?_
    · filter_upwards [hν.ae_le hr] with x hx
      simp only [Function.comp, clamp_of_mem (⟨hx.1, hx.2⟩ : r x ∈ Set.Icc a b)]
    · filter_upwards [hν.ae_le hr, hν.ae_le hub, hν.ae_le hvb] with x hx hux hvx
      rw [Real.norm_eq_abs, abs_mul]
      have hvru : |v x - r x * u x| ≤ 2 * b * c := by
        calc |v x - r x * u x| ≤ |v x| + |r x * u x| := abs_sub _ _
          _ ≤ c * r x + r x * c := by
              rw [abs_mul, abs_of_nonneg (ratio_nonneg x)]
              exact add_le_add hvx (mul_le_mul_of_nonneg_left hux (ratio_nonneg x))
          _ ≤ 2 * b * c := by nlinarith [hx.2]
      have hMr := hM (r x) ⟨hx.1, hx.2⟩
      exact mul_le_mul hMr hvru (abs_nonneg _) ((abs_nonneg _).trans hMr)
  have i12 : Integrable (fun x => g ((r x + 1 * v x) / (1 + 1 * u x)) - g (r x)) ν :=
    i1.sub i2
  rw [← integral_sub i1 i2, ← integral_sub i12 i3]
  have := norm_integral_le_of_norm_le_const (μ := ν) (by
    filter_upwards [hpt] with x hx; exact (Real.norm_eq_abs _).le.trans hx)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  ring

end Represent

/-! ### Naming the gradient: `(T^λ − r)[ψλ]` and the preconditioner `ν_G` -/

section Naming

variable [StandardBorelSpace S] [Nonempty S] {T : Kernel S S} [IsMarkovKernel T]
  {lam : Measure S} [IsFiniteMeasure lam]

/-- The mass the density action of `T^λ` gives a set, for `fλ`, `f ≥ 0`: `∫_s (∫⁻ f dT(x)) dλ`
(`lem:adjoint`(3), density action of `T^λ` is the function action of `T`). -/
theorem reversal_comp_withDensity_real (h : IsInvariant T lam) {f : S → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∀ᵐ x ∂lam, ∫⁻ y, f y ∂(T x) < ∞) {s : Set S}
    (hs : MeasurableSet s) :
    (reversal T lam ∘ₘ lam.withDensity f).real s = ∫ x in s, (∫⁻ y, f y ∂(T x)).toReal ∂lam := by
  rw [h.isReversalPair_reversal_symm.comp_withDensity hf, measureReal_def,
    withDensity_apply _ hs, integral_toReal hf.lintegral_kernel.aemeasurable
      (ae_restrict_of_ae hfin)]

/-- **The signed density action of `T^λ`**: for a bounded measurable `ψ`,
`(ψ⁺λ)T^λ − (ψ⁻λ)T^λ` has density `Tψ` against `λ` — setwise, so that no instance on the
two measures is needed. This is `lem:adjoint`(3) for the signed measure `ψλ`, which is what the
paper's `(T^λ − r)[ψλ]` applies it to. -/
theorem reversal_comp_signed (h : IsInvariant T lam) {ψ : S → ℝ} (hψ : Measurable ψ) {L : ℝ}
    (hψb : ∀ᵐ x ∂lam, |ψ x| ≤ L) {s : Set S} (hs : MeasurableSet s) :
    (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (ψ y)).real s -
      (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (-ψ y)).real s =
      ∫ x in s, funAct T ψ x ∂lam := by
  have hT : ∀ᵐ x ∂lam, ∀ᵐ y ∂(T x), |ψ y| ≤ L := h.ae_ae hψb
  have hint : ∀ᵐ x ∂lam, Integrable ψ (T x) := by
    filter_upwards [hT] with x hx
    exact Integrable.of_bound hψ.aestronglyMeasurable L (by simpa [Real.norm_eq_abs] using hx)
  have hfin : ∀ φ : S → ℝ, (∀ᵐ x ∂lam, Integrable φ (T x)) →
      ∀ᵐ x ∂lam, ∫⁻ y, ENNReal.ofReal (φ y) ∂(T x) < ∞ := fun φ hφ => by
    filter_upwards [hφ] with x hx
    exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm φ) hx.2
  have hint' : ∀ᵐ x ∂lam, Integrable (fun y => -ψ y) (T x) := by
    filter_upwards [hint] with x hx using hx.neg
  rw [reversal_comp_withDensity_real h hψ.ennreal_ofReal (hfin ψ hint) hs,
    reversal_comp_withDensity_real h hψ.neg.ennreal_ofReal (hfin _ hint') hs]
  have hbd : ∀ φ : S → ℝ, Measurable φ → (∀ᵐ x ∂lam, ∀ᵐ y ∂(T x), |φ y| ≤ L) →
      Integrable (fun x => (∫⁻ y, ENNReal.ofReal (φ y) ∂(T x)).toReal) (lam.restrict s) :=
    fun φ hφ hφb => by
      refine Integrable.of_bound
        (hφ.ennreal_ofReal.lintegral_kernel.ennreal_toReal.aestronglyMeasurable) L ?_
      refine ae_restrict_of_ae ?_
      filter_upwards [hφb] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      have hL : 0 ≤ L ∨ ∀ᵐ y ∂(T x), False := by
        by_cases hL : 0 ≤ L
        · exact Or.inl hL
        · right; filter_upwards [hx] with y hy; exact hL ((abs_nonneg _).trans hy)
      rcases hL with hL | hL
      · have : ∫⁻ y, ENNReal.ofReal (φ y) ∂(T x) ≤ ∫⁻ _, ENNReal.ofReal L ∂(T x) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hx] with y hy
          exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hy)
        rw [lintegral_const, measure_univ, mul_one] at this
        exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top this)
          ENNReal.ofReal_ne_top).2 this |>.trans (by rw [ENNReal.toReal_ofReal hL])
      · exfalso
        have := measure_univ (μ := T x)
        rw [ae_iff] at hL
        simp at hL
  rw [← integral_sub (hbd ψ hψ hT) (hbd (fun y => -ψ y) hψ.neg (by
    filter_upwards [hT] with x hx; filter_upwards [hx] with y hy; rwa [abs_neg]))]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hint] with x hx
  rw [funAct, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hx]

omit [StandardBorelSpace S] [Nonempty S] [IsMarkovKernel T] in
/-- **The preconditioner moves the inner product, not the density**: with `ϖ := dν_G/dλ`,
the signed measure `ϖ·(hλ)` has density `h` against `ν_G`, i.e. `dG/dν_G = dΦ/dλ`. -/
theorem withDensityᵥ_rnDeriv_mul {nuG : Measure S} [IsFiniteMeasure nuG] (hG : nuG ≪ lam)
    {h : S → ℝ} (hh : AEStronglyMeasurable h lam) {K : ℝ} (hhb : ∀ᵐ x ∂lam, |h x| ≤ K) :
    lam.withDensityᵥ (fun x => (nuG.rnDeriv lam x).toReal * h x) = nuG.withDensityᵥ h := by
  have hI : Integrable (fun x => (nuG.rnDeriv lam x).toReal * h x) lam :=
    (Measure.integrable_toReal_rnDeriv).mul_bdd hh (by simpa [Real.norm_eq_abs] using hhb)
  have hI' : Integrable h nuG :=
    Integrable.of_bound (hh.mono_ac hG) K
      (by filter_upwards [hG.ae_le hhb] with x hx; simpa [Real.norm_eq_abs] using hx)
  ext s hs
  rw [withDensityᵥ_apply hI hs, withDensityᵥ_apply hI' hs, ← integral_indicator hs,
    ← integral_indicator hs, ← integral_rnDeriv_smul hG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s <;> simp [hx, Set.indicator]

end Naming

/-! ### Uniqueness of the representative -/

section Unique

/-- **The representative is unique in `L²(ν_G)`**: two `L²(ν_G)` functions whose pairings with
every admissible direction (`|dδ/dμ| ≤ ½`) agree are `ν_G`-a.e. equal, when `μ ∼ ν_G`. -/
theorem representative_unique {μ nuG : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure nuG]
    (hμG : μ ≪ nuG) (hGμ : nuG ≪ μ) {h h' : S → ℝ} (hh : MemLp h 2 nuG)
    (hh' : MemLp h' 2 nuG)
    (heq : ∀ u : S → ℝ, Measurable u → (∀ᵐ x ∂μ, |u x| ≤ 1 / 2) →
      ∫ x, h x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG =
        ∫ x, h' x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG) :
    h =ᵐ[nuG] h' := by
  set m : S → ℝ := fun x => (μ.rnDeriv nuG x).toReal with hm
  have hmm : Measurable m := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hmpos : ∀ᵐ x ∂nuG, 0 < m x := by
    filter_upwards [hGμ.ae_le (Measure.rnDeriv_pos hμG), Measure.rnDeriv_lt_top μ nuG]
      with x h1 h2
    exact ENNReal.toReal_pos h1.ne' h2.ne
  have hk := hh.1.sub hh'.1
  set k₁ := hk.mk (fun x => h x - h' x) with hk₁
  have hk₁m : Measurable k₁ := hk.stronglyMeasurable_mk.measurable
  have hkk : (fun x => h x - h' x) =ᵐ[nuG] k₁ := hk.ae_eq_mk
  have hI : Integrable h nuG := hh.integrable (by norm_num)
  have hI' : Integrable h' nuG := hh'.integrable (by norm_num)
  have step : ∀ n : ℕ, ∀ᵐ x ∂nuG, m x ≤ n → k₁ x = 0 := by
    intro n
    set u : S → ℝ := fun x => if m x ≤ n then k₁ x / (2 * (1 + |k₁ x|)) else 0 with hu
    have hum : Measurable u :=
      Measurable.ite (measurableSet_le hmm measurable_const)
        (hk₁m.div (measurable_const.mul (measurable_const.add hk₁m.abs))) measurable_const
    have hub : ∀ x, |u x| ≤ 1 / 2 := by
      intro x
      simp only [hu]
      split_ifs
      · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (1 + |k₁ x|)),
          div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg (k₁ x)]
      · simp
    have hum' : ∀ x, |u x * m x| ≤ 1 / 2 * n := by
      intro x
      simp only [hu]
      split_ifs with hx
      · rw [abs_mul]
        have h1 := hub x
        simp only [hu, if_pos hx] at h1
        exact mul_le_mul h1 (by rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact hx)
          (abs_nonneg _) (by norm_num)
      · simp
    have hbdd : AEStronglyMeasurable (fun x => u x * m x) nuG :=
      (hum.mul hmm).aestronglyMeasurable
    have i1 : Integrable (fun x => h x * (u x * m x)) nuG :=
      hI.mul_bdd hbdd (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hum' x)
    have i2 : Integrable (fun x => h' x * (u x * m x)) nuG :=
      hI'.mul_bdd hbdd (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hum' x)
    have e := heq u hum (Filter.Eventually.of_forall hub)
    have hzero : ∫ x, (h x * (u x * m x) - h' x * (u x * m x)) ∂nuG = 0 := by
      rw [integral_sub i1 i2, e, sub_self]
    have hnn : 0 ≤ᵐ[nuG] fun x => h x * (u x * m x) - h' x * (u x * m x) := by
      filter_upwards [hkk, hmpos] with x hx hmx
      simp only [Pi.zero_apply, hu]
      split_ifs
      · have : h x * (k₁ x / (2 * (1 + |k₁ x|)) * m x) - h' x * (k₁ x / (2 * (1 + |k₁ x|)) * m x)
            = k₁ x * k₁ x / (2 * (1 + |k₁ x|)) * m x := by rw [← hx]; ring
        rw [this]
        have := mul_self_nonneg (k₁ x)
        positivity
      · simp
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (i1.sub i2)).1 hzero
    filter_upwards [hae, hkk, hmpos] with x hx hkx hmx hxn
    simp only [Pi.zero_apply, hu, if_pos hxn] at hx
    have : k₁ x * k₁ x / (2 * (1 + |k₁ x|)) * m x = 0 := by
      rw [← hx, ← hkx]; ring
    have hd : (0 : ℝ) < 2 * (1 + |k₁ x|) := by positivity
    rcases mul_eq_zero.1 this with h0 | h0
    · rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact mul_self_eq_zero.1 h0
      · exact absurd h0 hd.ne'
    · exact absurd h0 hmx.ne'
  have hall := ae_all_iff.2 step
  filter_upwards [hall, hkk] with x hx hkx
  obtain ⟨n, hn⟩ := exists_nat_ge (m x)
  have := hx n hn
  rw [this] at hkx
  linarith

end Unique

/-! ### `theo:first_variation_full` -/

section Theorem

variable {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S} [IsFiniteMeasure μ]
  {ν : Measure S} [IsFiniteMeasure ν]

omit [IsFiniteMeasure μ] in
/-- **`(T^λ − r)[ψλ]` has density `Tψ − rψ` against `λ`**, setwise, for any `ψ` with a
measurable, `μ`-a.e. bounded version (`μ ∼ λ`, `λ` `T`-invariant). -/
theorem phi_density [StandardBorelSpace S] [Nonempty S] {lam : Measure S} [IsFiniteMeasure lam]
    (hinv : IsInvariant T lam) (hlμ : lam ≪ μ) (hac : T ∘ₘ μ ≪ μ) {b : ℝ}
    (hrb : ∀ᵐ x ∂μ, ratio T μ x ≤ b) {ψ ψ₁ : S → ℝ} (hψ₁m : Measurable ψ₁) {K : ℝ}
    (hψ₁b : ∀ᵐ x ∂μ, |ψ₁ x| ≤ K) (hψe : ψ =ᵐ[μ] ψ₁) {s : Set S} (hs : MeasurableSet s) :
    (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (ψ y)).real s -
        (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (-ψ y)).real s -
        ∫ x in s, ratio T μ x * ψ x ∂lam =
      ∫ x in s, (funAct T ψ x - ratio T μ x * ψ x) ∂lam := by
  have hψl : ψ =ᵐ[lam] ψ₁ := hlμ.ae_le hψe
  have hψ₁bl : ∀ᵐ x ∂lam, |ψ₁ x| ≤ K := hlμ.ae_le hψ₁b
  have hTl : funAct T ψ =ᵐ[lam] funAct T ψ₁ := hlμ.ae_le (funAct_congr_of_ac hac hψe)
  have hwd1 : (lam.withDensity fun y => ENNReal.ofReal (ψ y)) =
      lam.withDensity fun y => ENNReal.ofReal (ψ₁ y) :=
    withDensity_congr_ae (by filter_upwards [hψl] with x hx; rw [hx])
  have hwd2 : (lam.withDensity fun y => ENNReal.ofReal (-ψ y)) =
      lam.withDensity fun y => ENNReal.ofReal (-ψ₁ y) :=
    withDensity_congr_ae (by filter_upwards [hψl] with x hx; rw [hx])
  rw [hwd1, hwd2, reversal_comp_signed hinv hψ₁m hψ₁bl hs]
  have hrb' : ∀ᵐ x ∂lam, |ratio T μ x * ψ₁ x| ≤ b * K := by
    filter_upwards [hlμ.ae_le hrb, hψ₁bl] with x h1 h2
    rw [abs_mul, abs_of_nonneg (ratio_nonneg x)]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((ratio_nonneg x).trans h1)
  have i1 : Integrable (funAct T ψ₁) (lam.restrict s) :=
    Integrable.of_bound hψ₁m.stronglyMeasurable.integral_kernel.aestronglyMeasurable K
      (ae_restrict_of_ae (by
        filter_upwards [hlμ.ae_le (ae_abs_funAct_le hac hψ₁b)] with x hx
        rwa [Real.norm_eq_abs]))
  have i2 : Integrable (fun x => ratio T μ x * ψ₁ x) (lam.restrict s) :=
    Integrable.of_bound (measurable_ratio.mul hψ₁m).aestronglyMeasurable (b * K)
      (ae_restrict_of_ae (by filter_upwards [hrb'] with x hx; rwa [Real.norm_eq_abs]))
  have e3 : ∫ x in s, ratio T μ x * ψ x ∂lam = ∫ x in s, ratio T μ x * ψ₁ x ∂lam :=
    integral_congr_ae (ae_restrict_of_ae (by filter_upwards [hψl] with x hx; rw [hx]))
  rw [e3, ← integral_sub i1 i2]
  exact integral_congr_ae (ae_restrict_of_ae (by
    filter_upwards [hψl, hTl] with x h1 h2; rw [h1, h2]))

/-- **`theo:first_variation_full`, on a standard Borel space.** Under the hypotheses of
`lem:adjoint` (`T` Markov, `λ` finite and `T`-invariant), let `μ ∼ λ` be finite with `μT ≪ μ`
and `r := d(μT)/dμ` essentially valued in `[a, b] ⊂ (0, ∞)`; let `ν ≪ μ` be finite with
`dν/dμ ∈ L^∞(μ)`; let `g` be differentiable on `ℝ₊*` with continuous derivative `g'`; let `ν_G`
be finite with `ν_G ∼ λ`. Write `ψ := g'(r)·dν/dμ`, `h := Tψ − rψ`, `ϖ := dν_G/dλ`. Then

1. `Φ := (T^λ − r)[ψλ]` has density `h` against `λ` (setwise, `T^λ` the `λ`-reversal);
2. `G := ϖ·Φ` has density `h` against `ν_G`;
3. `G ∈ 𝓜²(ν_G)`: `h ∈ L²(ν_G)`;
4. `G` represents the derivative: for every direction `δ = uμ` with `u` essentially bounded,
   `d/ds|₀ 𝓛_{g,ν}(μ + sδ) = ∫ (dG/dν_G)(dδ/dν_G) dν_G`;
5. and it is the only `L²(ν_G)` function doing so on the directions with `‖dδ/dμ‖_∞ ≤ ½`.

The paper's hypothesis `dμ/dλ ∈ L²(λ)` is not used (see `theo_first_variation_full` for the
statement carrying it). -/
theorem first_variation_general [StandardBorelSpace S] [Nonempty S] {lam : Measure S}
    [IsFiniteMeasure lam] (hinv : IsInvariant T lam) (hμl : μ ≪ lam) (hlμ : lam ≪ μ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ᵐ x ∂μ, a ≤ ratio T μ x ∧ ratio T μ x ≤ b) (hνμ : ν ≪ μ)
    (hw : MemLp (fun x => (ν.rnDeriv μ x).toReal) ⊤ μ) {g g' : ℝ → ℝ}
    (hgd : ∀ y, 0 < y → HasDerivAt g (g' y) y) (hg'c : ContinuousOn g' (Set.Ioi 0))
    {nuG : Measure S} [IsFiniteMeasure nuG] (hGl : nuG ≪ lam) (hlG : lam ≪ nuG) :
    -- (1) `Φ = (T^λ − r)[ψλ]` has `λ`-density `h = Tψ − rψ`
    (∀ s : Set S, MeasurableSet s →
      (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (psi T g' ν μ y)).real s -
        (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (-psi T g' ν μ y)).real s -
        ∫ x in s, ratio T μ x * psi T g' ν μ x ∂lam =
      ∫ x in s, gradDens T g' ν μ x ∂lam) ∧
    -- (2) `G = (dν_G/dλ)·Φ` has `ν_G`-density `h`
    lam.withDensityᵥ (fun x => (nuG.rnDeriv lam x).toReal * gradDens T g' ν μ x) =
      nuG.withDensityᵥ (gradDens T g' ν μ) ∧
    -- (3) `G ∈ 𝓜²(ν_G)`
    MemLp (gradDens T g' ν μ) 2 nuG ∧
    -- (4) `G` represents the derivative in `⟨·∣·⟩_{ν_G}`
    (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂μ, |u x| ≤ C) →
      HasDerivAt (fun s => loss T g ν (perturb μ u s))
        (∫ x, gradDens T g' ν μ x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG) 0) ∧
    -- (5) uniquely
    (∀ h' : S → ℝ, MemLp h' 2 nuG →
      (∀ u : S → ℝ, Measurable u → (∀ᵐ x ∂μ, |u x| ≤ 1 / 2) →
        HasDerivAt (fun s => loss T g ν (perturb μ u s))
          (∫ x, h' x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG) 0) →
      h' =ᵐ[nuG] gradDens T g' ν μ) := by
  have hac : T ∘ₘ μ ≪ μ := (hinv.comp_absolutelyContinuous hμl).trans hlμ
  obtain ⟨W, hW⟩ := exists_ae_abs_le_of_memLp_top hw
  obtain ⟨ψ₁, K, hψ₁m, hψ₁b, hψe, hhe, hh₁m, hh₁b⟩ :=
    exists_psi_version (T := T) hac hW ha hab hr hg'c
  have hμG : μ ≪ nuG := hμl.trans hlG
  have hGμ : nuG ≪ μ := hGl.trans hlμ
  set h := gradDens T g' ν μ with hdef
  set h₁ : S → ℝ := fun x => funAct T ψ₁ x - ratio T μ x * ψ₁ x with hh₁
  -- derivative in `μ`-coordinates, then read against `ν_G`
  have hder : ∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂μ, |u x| ≤ C) →
      HasDerivAt (fun s => loss T g ν (perturb μ u s))
        (∫ x, h x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG) 0 := by
    intro u hu C hub
    have hub' : ∀ᵐ x ∂μ, |u x| ≤ max C 0 := by
      filter_upwards [hub] with x hx using hx.trans (le_max_left _ _)
    have key := hasDerivAt_loss_gradDens (T := T) hνμ hW hac ha hab hr hgd hg'c hu
      (le_max_right C 0) hub'
    convert key using 1
    rw [← integral_rnDeriv_smul hμG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]; ring
  have hhl : h =ᵐ[lam] h₁ := hlμ.ae_le hhe
  have hhG : h =ᵐ[nuG] h₁ := hGμ.ae_le hhe
  have hhbμ : ∀ᵐ x ∂μ, |h x| ≤ K + b * K := by
    filter_upwards [hhe, hh₁b] with x h1 h2; rw [h1]; exact h2
  have hhL2 : MemLp h 2 nuG :=
    MemLp.of_bound (hh₁m.aestronglyMeasurable.congr hhG.symm) (K + b * K)
      (by filter_upwards [hGμ.ae_le hhbμ] with x hx; rwa [Real.norm_eq_abs])
  refine ⟨?_, ?_, hhL2, hder, ?_⟩
  · -- (1)
    exact fun s hs => phi_density hinv hlμ hac (by filter_upwards [hr] with x hx using hx.2)
      hψ₁m hψ₁b hψe hs
  · -- (2)
    exact withDensityᵥ_rnDeriv_mul hGl
      (hh₁m.aestronglyMeasurable.congr hhl.symm) (hlμ.ae_le hhbμ)
  · -- (5)
    intro h' hh' hrep
    refine representative_unique hμG hGμ hh' hhL2 (fun u hu hub => ?_)
    exact (hrep u hu hub).unique (hder u hu (1 / 2) hub)

/-- **`theo:first_variation_full` with the paper's hypotheses verbatim.** Everything
`first_variation_general` does not use is carried and unused: `λ ≠ 0`, the square-integrability
`dμ/dλ ∈ L²(λ)` (inside `InM2`, which also carries `μ ≪ λ` and finiteness), `μT ≪ μ` (implied by
`μ ∼ λ` and invariance), and the local Lipschitz bound on `g'`. -/
theorem theo_first_variation_full [StandardBorelSpace S] [Nonempty S] {lam : Measure S}
    [IsFiniteMeasure lam] (_hlam0 : lam ≠ 0) (hinv : IsInvariant T lam) {μ : Measure S}
    (hμ2 : InM2 lam μ) (hlμ : lam ≪ μ) (_hac : T ∘ₘ μ ≪ μ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hr : ∀ᵐ x ∂μ, a ≤ ratio T μ x ∧ ratio T μ x ≤ b) {ν : Measure S}
    [IsFiniteMeasure ν] (hνμ : ν ≪ μ) (hw : MemLp (fun x => (ν.rnDeriv μ x).toReal) ⊤ μ)
    {g g' : ℝ → ℝ} (hgd : ∀ y, 0 < y → HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Set.Ioi 0)) (hg'L : LocallyLipschitzOn (Set.Ioi 0) g')
    {nuG : Measure S} [IsFiniteMeasure nuG] (hGl : nuG ≪ lam) (hlG : lam ≪ nuG) :
    (∀ s : Set S, MeasurableSet s →
      (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (psi T g' ν μ y)).real s -
        (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (-psi T g' ν μ y)).real s -
        ∫ x in s, ratio T μ x * psi T g' ν μ x ∂lam =
      ∫ x in s, gradDens T g' ν μ x ∂lam) ∧
    lam.withDensityᵥ (fun x => (nuG.rnDeriv lam x).toReal * gradDens T g' ν μ x) =
      nuG.withDensityᵥ (gradDens T g' ν μ) ∧
    MemLp (gradDens T g' ν μ) 2 nuG ∧
    (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂μ, |u x| ≤ C) →
      HasDerivAt (fun s => loss T g ν (perturb μ u s))
        (∫ x, gradDens T g' ν μ x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG) 0) ∧
    (∀ h' : S → ℝ, MemLp h' 2 nuG →
      (∀ u : S → ℝ, Measurable u → (∀ᵐ x ∂μ, |u x| ≤ 1 / 2) →
        HasDerivAt (fun s => loss T g ν (perturb μ u s))
          (∫ x, h' x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG) 0) →
      h' =ᵐ[nuG] gradDens T g' ν μ) ∧
    -- (6) the derivative is uniform over the admissible class, explicit second-order remainder
    (∀ K : NNReal, LipschitzOnWith K g' (Set.Icc (a / 3) (3 * b)) →
      ∀ M : ℝ, (∀ y ∈ Set.Icc a b, |g' y| ≤ M) →
      ∀ u : S → ℝ, Measurable u → ∀ c : ℝ, 0 ≤ c → c ≤ 1 / 2 → b * c ≤ a / 2 →
      (∀ᵐ x ∂μ, |u x| ≤ c) →
      |loss T g ν (perturb μ u 1) - loss T g ν μ -
          ∫ x, gradDens T g' ν μ x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG| ≤
        ν.real Set.univ * (16 * K * b ^ 2 + 4 * M * b) * c ^ 2) ∧
    -- (7) such constants exist (local Lipschitz ⟹ Lipschitz on the compact `[a/3, 3b]`)
    (∃ K : NNReal, LipschitzOnWith K g' (Set.Icc (a / 3) (3 * b))) ∧
      (∃ M : ℝ, ∀ y ∈ Set.Icc a b, |g' y| ≤ M) := by
  haveI : IsFiniteMeasure μ := hμ2.1
  have hμl := hμ2.2.1
  have hac : T ∘ₘ μ ≪ μ := (hinv.comp_absolutelyContinuous hμl).trans hlμ
  obtain ⟨c1, c2, c3, c4, c5⟩ :=
    first_variation_general hinv hμl hlμ ha hab hr hνμ hw hgd hg'c hGl hlG
  obtain ⟨W, hW⟩ := exists_ae_abs_le_of_memLp_top hw
  have hIpos : Set.Icc (a / 3) (3 * b) ⊆ Set.Ioi 0 :=
    fun y hy => lt_of_lt_of_le (by positivity) hy.1
  refine ⟨c1, c2, c3, c4, c5, fun K hK M hM u hu c hc0 hc hcb hub => ?_,
    (hg'L.mono hIpos).exists_lipschitzOnWith_of_compact isCompact_Icc, ?_⟩
  · have e : ∫ x, gradDens T g' ν μ x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG =
        ∫ x, gradDens T g' ν μ x * u x ∂μ := by
      rw [← integral_rnDeriv_smul (hμl.trans hlG)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]; ring
    rw [e]
    exact loss_remainder_le hνμ hac hW ha hab hr hgd hg'c hK hM hu hc0 hc hcb hub
  · obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      (hg'c.mono fun y hy => lt_of_lt_of_le ha hy.1)
    exact ⟨M, fun y hy => by simpa [Real.norm_eq_abs] using hM y hy⟩

end Theorem

/-- **`theo:first_variation` (body, `cv_divergence.tex`)**, read clause by clause. *(i)* "For a
continuously differentiable generator, the `g`-divergence balance loss of an arbitrary Markov
kernel is differentiable at every flow whose balance ratio is bounded away from `0` and `∞`" —
no invariant measure, no standard Borel hypothesis: the derivative along every bounded direction
exists and is `∫ g'(r)(v − r·u) dν`. *(ii)* "as soon as the kernel admits a non-zero finite
invariant measure equivalent to that flow — its gradient is the reversal of the kernel, minus the
ratio, applied to `g'` of that ratio": clauses (1) and (4) of `first_variation_general`, which
needs neither `dμ/dλ ∈ L²(λ)` nor `μT ≪ μ`. -/
theorem theo_first_variation {T : Kernel S S} [IsMarkovKernel T] {μ : Measure S}
    [IsFiniteMeasure μ] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ᵐ x ∂μ, a ≤ ratio T μ x ∧ ratio T μ x ≤ b) {ν : Measure S} [IsFiniteMeasure ν]
    (hνμ : ν ≪ μ) (hw : MemLp (fun x => (ν.rnDeriv μ x).toReal) ⊤ μ) {g g' : ℝ → ℝ}
    (hgd : ∀ y, 0 < y → HasDerivAt g (g' y) y) (hg'c : ContinuousOn g' (Set.Ioi 0)) :
    (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂μ, |u x| ≤ C) →
      HasDerivAt (fun s => loss T g ν (perturb μ u s))
        (∫ x, g' (ratio T μ x) * (dirPush T μ u x - ratio T μ x * u x) ∂ν) 0) ∧
    (∀ [StandardBorelSpace S] [Nonempty S] (lam : Measure S) [IsFiniteMeasure lam],
      lam ≠ 0 → IsInvariant T lam → μ ≪ lam → lam ≪ μ →
      ∀ (nuG : Measure S) [IsFiniteMeasure nuG], nuG ≪ lam → lam ≪ nuG →
      (∀ s : Set S, MeasurableSet s →
        (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (psi T g' ν μ y)).real s -
          (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (-psi T g' ν μ y)).real s -
          ∫ x in s, ratio T μ x * psi T g' ν μ x ∂lam =
        ∫ x in s, gradDens T g' ν μ x ∂lam) ∧
      (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂μ, |u x| ≤ C) →
        HasDerivAt (fun s => loss T g ν (perturb μ u s))
          (∫ x, gradDens T g' ν μ x * (u x * (μ.rnDeriv nuG x).toReal) ∂nuG) 0)) := by
  refine ⟨fun u hu C hub => ?_, fun lam _ _hlam0 hinv hμl hlμ nuG _ hGl hlG => ?_⟩
  · have hub' : ∀ᵐ x ∂μ, |u x| ≤ max C 0 := by
      filter_upwards [hub] with x hx using hx.trans (le_max_left _ _)
    exact hasDerivAt_loss_perturb hνμ hu ha hab (le_max_right C 0) hub' hr hgd hg'c
  · obtain ⟨c1, -, -, c4, -⟩ :=
      first_variation_general hinv hμl hlμ ha hab hr hνμ hw hgd hg'c hGl hlG
    exact ⟨c1, c4⟩

/-! ### `cor:gradient_formulas` -/

section Corollary

variable [StandardBorelSpace S] [Nonempty S] {pb : Kernel S S} [IsMarkovKernel pb]
  {lam : Measure S} [IsFiniteMeasure lam] {F : Measure S} [IsFiniteMeasure F]

theorem measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

theorem abs_real_sign_le (y : ℝ) : |Real.sign y| ≤ 1 := by
  rcases Real.sign_apply_eq y with h | h | h <;> rw [h] <;> simp

omit [StandardBorelSpace S] [Nonempty S] [IsFiniteMeasure lam] in
theorem memLp_top_rnDeriv_self : MemLp (fun x => (F.rnDeriv F x).toReal) ⊤ F :=
  (memLp_const (1 : ℝ)).ae_eq (by
    filter_upwards [Measure.rnDeriv_self F] with x hx; simp [hx])

omit [StandardBorelSpace S] [Nonempty S] [IsMarkovKernel pb] [IsFiniteMeasure lam] in
theorem psi_self_ae (g' : ℝ → ℝ) :
    psi pb g' F F =ᵐ[F] fun x => g' (ratio pb F x) := by
  filter_upwards [Measure.rnDeriv_self F] with x hx
  simp [psi, hx]

omit [StandardBorelSpace S] [Nonempty S] [IsMarkovKernel pb] [IsFiniteMeasure lam] in
theorem gradDens_self_ae (hac : pb ∘ₘ F ≪ F) (g' : ℝ → ℝ) :
    gradDens pb g' F F =ᵐ[F] fun x =>
      funAct pb (fun y => g' (ratio pb F y)) x - ratio pb F x * g' (ratio pb F x) := by
  filter_upwards [psi_self_ae (pb := pb) g', funAct_congr_of_ac hac (psi_self_ae (pb := pb) g')]
    with x h1 h2
  simp only [gradDens]; rw [h1, h2]

/-- **`cor:gradient_formulas`, first display**: with `T = π_←`, `μ = ν = F_←`, `ν_G = λ`,
`∇^λ_{F} 𝓛_{g,F} = (π_→^λ − r)[g'(r)λ]`, `π_→^λ = π_←^λ` the reversal: (1) that signed measure
has `λ`-density `π_←[g'(r)] − r·g'(r)`; (2) this density represents the derivative in
`L²(λ)` along every admissible direction; (3) uniquely. -/
theorem cor_gradient_formulas (hinv : IsInvariant pb lam) (hFl : F ≪ lam) (hlF : lam ≪ F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ᵐ x ∂F, a ≤ ratio pb F x ∧ ratio pb F x ≤ b) {g g' : ℝ → ℝ}
    (hgd : ∀ y, 0 < y → HasDerivAt g (g' y) y) (hg'c : ContinuousOn g' (Set.Ioi 0)) :
    (∀ s : Set S, MeasurableSet s →
      (reversal pb lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (g' (ratio pb F y))).real s -
        (reversal pb lam ∘ₘ
          lam.withDensity fun y => ENNReal.ofReal (-g' (ratio pb F y))).real s -
        ∫ x in s, ratio pb F x * g' (ratio pb F x) ∂lam =
      ∫ x in s, (funAct pb (fun y => g' (ratio pb F y)) x -
        ratio pb F x * g' (ratio pb F x)) ∂lam) ∧
    (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂F, |u x| ≤ C) →
      HasDerivAt (fun s => loss pb g F (perturb F u s))
        (∫ x, (funAct pb (fun y => g' (ratio pb F y)) x - ratio pb F x * g' (ratio pb F x)) *
          (u x * (F.rnDeriv lam x).toReal) ∂lam) 0) ∧
    (∀ h' : S → ℝ, MemLp h' 2 lam →
      (∀ u : S → ℝ, Measurable u → (∀ᵐ x ∂F, |u x| ≤ 1 / 2) →
        HasDerivAt (fun s => loss pb g F (perturb F u s))
          (∫ x, h' x * (u x * (F.rnDeriv lam x).toReal) ∂lam) 0) →
      h' =ᵐ[lam] fun x => funAct pb (fun y => g' (ratio pb F y)) x -
        ratio pb F x * g' (ratio pb F x)) := by
  have hac : pb ∘ₘ F ≪ F := (hinv.comp_absolutelyContinuous hFl).trans hlF
  obtain ⟨-, -, -, h4, h5⟩ := first_variation_general hinv hFl hlF ha hab hr
    (Measure.AbsolutelyContinuous.refl F) memLp_top_rnDeriv_self hgd hg'c
    (Measure.AbsolutelyContinuous.refl lam) (Measure.AbsolutelyContinuous.refl lam)
  have hgl := hlF.ae_le (gradDens_self_ae hac g')
  obtain ⟨W, hW⟩ := exists_ae_abs_le_of_memLp_top (memLp_top_rnDeriv_self (F := F))
  obtain ⟨ψ₁, K, hψ₁m, hψ₁b, hψe, -⟩ := exists_psi_version (T := pb) hac hW ha hab hr hg'c
  refine ⟨fun s hs => ?_, fun u hu C hub => ?_, fun h' hh' hrep => ?_⟩
  · exact phi_density hinv hlF hac (by filter_upwards [hr] with x hx using hx.2) hψ₁m hψ₁b
      ((psi_self_ae g').symm.trans hψe) hs
  · have := h4 u hu C hub
    convert this using 1
    refine integral_congr_ae ?_
    filter_upwards [hgl] with x hx
    rw [hx]
  · exact (h5 h' hh' hrep).trans hgl

omit [StandardBorelSpace S] [Nonempty S] [IsFiniteMeasure lam] [IsFiniteMeasure F] in
/-- `π_←[2(r − 1)] = 2(π_← r − 1)`, `F`-a.e.: `r` is bounded, `π_←` Markov. -/
theorem funAct_two_mul_sub (hac : pb ∘ₘ F ≪ F) {b : ℝ} (hrb : ∀ᵐ x ∂F, ratio pb F x ≤ b) :
    funAct pb (fun y => 2 * (ratio pb F y - 1)) =ᵐ[F]
      fun x => 2 * (funAct pb (ratio pb F) x - 1) := by
  have h1 : ∀ᵐ y ∂(pb ∘ₘ F), ratio pb F y ≤ b := hac.ae_le hrb
  filter_upwards [Measure.ae_ae_of_ae_comp h1] with x hx
  have hi : Integrable (ratio pb F) (pb x) :=
    Integrable.of_bound measurable_ratio.aestronglyMeasurable b (by
      filter_upwards [hx] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (ratio_nonneg y)]; exact hy)
  simp only [funAct]
  rw [integral_const_mul, integral_sub hi (integrable_const 1)]
  simp

/-- **`cor:gradient_formulas`, `g(x) = (x−1)²`**: the gradient
`2(π_→^λ − r)[(r − 1)λ] = 2(π_→^λ(rλ) − λ − r²λ + rλ)` — (1) the pieces of the measure form:
`π_→^λ λ = λ`, and `π_→^λ(rλ)` has `λ`-density `π_← r`; (2) the density
`2(π_← r − 1 − r² + r)` represents the derivative in `L²(λ)`. -/
theorem cor_gradient_formulas_sq (hinv : IsInvariant pb lam) (hFl : F ≪ lam) (hlF : lam ≪ F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ᵐ x ∂F, a ≤ ratio pb F x ∧ ratio pb F x ≤ b) :
    (reversal pb lam ∘ₘ lam = lam ∧
      ∀ s : Set S, MeasurableSet s →
        (reversal pb lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (ratio pb F y)).real s =
          ∫ x in s, funAct pb (ratio pb F) x ∂lam) ∧
    (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂F, |u x| ≤ C) →
      HasDerivAt (fun s => loss pb (fun y => (y - 1) ^ 2) F (perturb F u s))
        (∫ x, 2 * (funAct pb (ratio pb F) x - 1 - ratio pb F x ^ 2 + ratio pb F x) *
          (u x * (F.rnDeriv lam x).toReal) ∂lam) 0) := by
  have hac : pb ∘ₘ F ≪ F := (hinv.comp_absolutelyContinuous hFl).trans hlF
  have hrb : ∀ᵐ x ∂F, ratio pb F x ≤ b := by filter_upwards [hr] with x hx using hx.2
  have hgd : ∀ y, 0 < y → HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (y - 1)) y := by
    intro y _
    have h := (hasDerivAt_pow 2 (y - 1)).comp y ((hasDerivAt_id y).sub_const 1)
    exact h.congr_deriv (by simp)
  have hg'c : ContinuousOn (fun y : ℝ => 2 * (y - 1)) (Set.Ioi 0) := by fun_prop
  obtain ⟨-, h2, -⟩ := cor_gradient_formulas hinv hFl hlF ha hab hr hgd hg'c
  refine ⟨⟨(hinv.isInvariant_reversal : _), fun s hs => ?_⟩, fun u hu C hub => ?_⟩
  · have hrbl : ∀ᵐ x ∂lam, |ratio pb F x| ≤ b := by
      filter_upwards [hlF.ae_le hrb] with x hx
      rwa [abs_of_nonneg (ratio_nonneg x)]
    have := reversal_comp_signed hinv measurable_ratio hrbl hs
    have h0 : (lam.withDensity fun y => ENNReal.ofReal (-ratio pb F y)) = 0 := by
      have : (fun y => ENNReal.ofReal (-ratio pb F y)) = 0 := by
        funext y; simp [ENNReal.ofReal_of_nonpos (neg_nonpos.2 (ratio_nonneg y))]
      rw [this, withDensity_zero]
    rw [h0] at this
    simpa using this
  · have := h2 u hu C hub
    convert this using 1
    refine integral_congr_ae ?_
    filter_upwards [hlF.ae_le (funAct_two_mul_sub hac hrb)] with x hx
    rw [hx]; ring

/-- **`cor:gradient_formulas`, `g(x) = |x−1|`**, on a flow whose ratio is essentially bounded away
from `1` (`|r − 1| ≥ a'` a.e., `a' > 0` — the hypothesis the paper added on 2026-09-13):
`g'(r)` is replaced by `sign(r − 1)` and the first display holds unchanged. -/
theorem cor_gradient_formulas_abs (hinv : IsInvariant pb lam) (hFl : F ≪ lam) (hlF : lam ≪ F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ᵐ x ∂F, a ≤ ratio pb F x ∧ ratio pb F x ≤ b) {a' : ℝ} (ha' : 0 < a')
    (hr1 : ∀ᵐ x ∂F, a' ≤ |ratio pb F x - 1|) :
    (∀ s : Set S, MeasurableSet s →
      (reversal pb lam ∘ₘ
          lam.withDensity fun y => ENNReal.ofReal (Real.sign (ratio pb F y - 1))).real s -
        (reversal pb lam ∘ₘ
          lam.withDensity fun y => ENNReal.ofReal (-Real.sign (ratio pb F y - 1))).real s -
        ∫ x in s, ratio pb F x * Real.sign (ratio pb F x - 1) ∂lam =
      ∫ x in s, (funAct pb (fun y => Real.sign (ratio pb F y - 1)) x -
        ratio pb F x * Real.sign (ratio pb F x - 1)) ∂lam) ∧
    (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂F, |u x| ≤ C) →
      HasDerivAt (fun s => loss pb (fun y => |y - 1|) F (perturb F u s))
        (∫ x, (funAct pb (fun y => Real.sign (ratio pb F y - 1)) x -
          ratio pb F x * Real.sign (ratio pb F x - 1)) *
          (u x * (F.rnDeriv lam x).toReal) ∂lam) 0) := by
  have hac : pb ∘ₘ F ≪ F := (hinv.comp_absolutelyContinuous hFl).trans hlF
  have hrb : ∀ᵐ x ∂F, ratio pb F x ≤ b := by filter_upwards [hr] with x hx using hx.2
  set φ : S → ℝ := fun y => Real.sign (ratio pb F y - 1) with hφ
  have hφm : Measurable φ := measurable_real_sign.comp (measurable_ratio.sub measurable_const)
  have hφb : ∀ᵐ x ∂F, |φ x| ≤ 1 := Filter.Eventually.of_forall fun x => abs_real_sign_le _
  have hψe : psi pb (fun y => Real.sign (y - 1)) F F =ᵐ[F] φ := psi_self_ae _
  refine ⟨fun s hs => phi_density hinv hlF hac hrb hφm hφb (Filter.EventuallyEq.refl _ _) hs,
    fun u hu C hub => ?_⟩
  have hub' : ∀ᵐ x ∂F, |u x| ≤ max C 0 := by
    filter_upwards [hub] with x hx using hx.trans (le_max_left _ _)
  have key := hasDerivAt_loss_perturb_of_continuous (T := pb) (ν := F) (b := b)
    (η := a' / 2) (M := 1) (g := fun y => |y - 1|) (g' := fun y => Real.sign (y - 1))
    (Measure.AbsolutelyContinuous.refl F) hu (by linarith) (le_max_right C 0)
    (by positivity) hub' hrb (by fun_prop)
    (measurable_real_sign.comp (measurable_id.sub measurable_const))
    (by
      filter_upwards [hr1] with x hx y hy
      refine GFNBounds.Balance.hasDerivAt_abs_sub_one ?_
      intro h1
      rw [h1] at hy
      rw [abs_sub_comm] at hy
      linarith)
    (Filter.Eventually.of_forall fun x y _ => abs_real_sign_le _)
  rw [integral_deriv_eq_gradDens (T := pb) (Measure.AbsolutelyContinuous.refl F) hac hrb hu
    (le_max_right C 0) hub' hφm hφb hψe, ← integral_rnDeriv_smul (hFl)] at key
  convert key using 1
  refine integral_congr_ae ?_
  filter_upwards [hlF.ae_le (gradDens_self_ae hac (fun y => Real.sign (y - 1)))] with x hx
  rw [smul_eq_mul, hx]
  ring

end Corollary

/-! ### The hypotheses are inhabited (kb 0025, 0027) -/

section Inhabited

/-- **Non-vacuity**: for any probability `π` on a standard Borel space, the resampling kernel
`T := const π` with `λ = μ = ν = π` meets every measure hypothesis of
`theo_first_variation_full` with `a = b = 1`; the remaining ones (`g`, e.g. `(x−1)²`, and
`ν_G := π`) are independent of the measures and trivially met. The conclusion is then a statement about the
unbalanced flows `μ + sδ`, `s ≠ 0`, so it is not empty. -/
theorem theo_first_variation_full_hypotheses_inhabited [StandardBorelSpace S] [Nonempty S] (π : Measure S) [IsProbabilityMeasure π] :
    π ≠ 0 ∧ IsInvariant (Kernel.const S π) π ∧ InM2 π π ∧ π ≪ π ∧
      Kernel.const S π ∘ₘ π ≪ π ∧
      (∀ᵐ x ∂π, (1 : ℝ) ≤ ratio (Kernel.const S π) π x ∧ ratio (Kernel.const S π) π x ≤ 1) ∧
      MemLp (fun x => (π.rnDeriv π x).toReal) ⊤ π := by
  have hinv := isInvariant_const π
  have hr : ∀ᵐ x ∂π, ratio (Kernel.const S π) π x = 1 := by
    unfold ratio
    rw [show Kernel.const S π ∘ₘ π = π from hinv]
    filter_upwards [Measure.rnDeriv_self π] with x hx
    simp [hx]
  have hm : MemLp (fun x => (π.rnDeriv π x).toReal) ⊤ π :=
    (memLp_const (1 : ℝ)).ae_eq (by
      filter_upwards [Measure.rnDeriv_self π] with x hx; simp [hx])
  refine ⟨IsProbabilityMeasure.ne_zero π, hinv, ?_, Measure.AbsolutelyContinuous.refl π, ?_, ?_,
    hm⟩
  · refine InM2.of_sigmaFinite (Measure.AbsolutelyContinuous.refl π) ?_
    exact (memLp_const (1 : ℝ)).ae_eq (by
      filter_upwards [Measure.rnDeriv_self π] with x hx; simp [hx])
  · rw [show Kernel.const S π ∘ₘ π = π from hinv]
  · filter_upwards [hr] with x hx; rw [hx]; simp

end Inhabited

end GFNBounds.Core.General.FirstVariation
