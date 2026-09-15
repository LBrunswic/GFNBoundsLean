import GFNBounds.Core.MixingBase
import GFNBounds.Core.FamilyUniversality
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

set_option maxHeartbeats 1000000

/-!
# Mixing controls coercivity, for the density action of a Markov kernel on `L²(λ)`

**`lem:sigma_mixing`** — statement `proofs.tex:628–634`, proof `proofs.tex:636–638` (draft
commit `3194054`; line citations drift, `kb/entries/0036` — the label is the anchor).

> Let `T` be a Markov kernel on a Polish space `𝒮` leaving a non-zero finite measure `λ`
> invariant, `P` its density action `h ↦ d((hλ)T)/dλ` on `L²(λ)`, `Π` the `λ`-mean projection
> `h ↦ λ(𝒮)⁻¹ ∫ h dλ`, and `β̂_n := ‖Pⁿ − Π‖_{L²(λ)}`. Assume `B̂ := ∑_{n≥0} β̂_n < +∞`
> (summable `L²`-mixing). Then `S := ∑_{n≥0}(Pⁿ − Π)` converges in operator norm,
> `S(I−P) = I − Π`, and consequently
> `∀ h ∈ L²(λ), ‖h − Πh‖_{L²(λ)} ≤ B̂ ‖(I−P)h‖_{L²(λ)}`.
> If moreover `λ` is not a multiple of a Dirac mass — in particular if `𝒮` is finite with
> `#𝒮 ≥ 2` and `λ > 0` everywhere — then `β̂₀ = 1` and `B̂ ≥ 1`.

> (proof, last sentence) If `λ` is not a multiple of a Dirac mass, then, `λ` being a finite
> measure on the Polish space `𝒮`, it charges a Borel set `X` with `0 < λ(X) < λ(𝒮)`, so
> `𝟏_X − Π𝟏_X ≠ 0`; hence `I − Π` is a non-zero orthogonal projection, `β̂₀ = ‖I − Π‖ = 1`, and
> `B̂ ≥ β̂₀ = 1`.

## What this file assembles

The operator half of the lemma was closed on an abstract Banach space in `Core/Mixing.lean`
(`Mixing.tendsto_partialSum`, `Mixing.poisson_right`, `Mixing.coercivity`); the two intertwining
identities `ΠP = PΠ = Π` were derived from `P𝟏 = 𝟏` and mass preservation in `Core/Flow.lean`;
and the density action of a Markov kernel was built in `Core/Kernel.lean`, but as a bounded
operator only **under the extra hypothesis** `IsBoundedDensityAction κ ν p C`. The new clause
`β̂₀ = 1` was proved only on a finite weighted `L²` (`Balance/WeightedL2Norm.lean`). This file
removes both gaps at the lemma's own generality:

| | |
|---|---|
| `lintegral_bindDensity_mul` | duality: `∫ (Tf)·h dλ = ∫∫ f(x) h(y) T(x,dy) λ(dx)` |
| `two_mul_lintegral_bindDensity_mul_le` | `2∫(Tf)·h ≤ ∫f² + ∫h²`, by `2ab ≤ a² + b²` under `λ ⊗ T` |
| `lintegral_bindDensity_sq_le`, `eLpNorm_bindDensity_two_le` | **`‖Tf‖₂ ≤ ‖f‖₂`** for `f ≥ 0`, by truncating `Tf` at `n` and monotone convergence |
| `enorm_densityAction_le` | `|Pf| ≤ T|f|` a.e. |
| `isBoundedDensityAction_two` | **`IsBoundedDensityAction κ λ 2 1` is a theorem**, from invariance alone |
| `densityActionL2`, `norm_densityActionL2_le` | the paper's `P` on `L²(λ)`, with `‖P‖ ≤ 1` |
| `norm_sub_meanProj_le`, `norm_one_sub_meanProj_le` | `‖I − Π‖ ≤ 1`: Pythagoras, `Π` being orthogonal |
| `meanProj_indicator_ne`, `norm_one_sub_meanProj_eq_one` | **`‖I − Π‖ = 1`** once `λ` charges `X` with `0 < λ(X) < λ(𝒮)` |
| `exists_measurableSet_of_ne_smul_dirac` | on a standard Borel space, `λ ≠ c·δ_x` for all `c, x` gives such an `X` |
| `ne_smul_dirac_of_two_pos`, `exists_measurableSet_of_two_pos` | two points of positive mass: not a multiple of a Dirac, and such an `X` |
| `sigma_mixing` | the first sentence: `S` converges in operator norm, `S(I−P) = I−Π`, the coercivity |
| `sigma_mixing_beta_zero_of_set`, `sigma_mixing_one_le_B_of_set` | `β̂₀ = 1`, `B̂ ≥ 1`, from the set `X` |
| **`lem_sigma_mixing`** | **the whole lemma**, on a standard Borel space |
| `lem_sigma_mixing_polish` | the same with the paper's literal "Polish space" |
| `sigma_mixing_finite` | the "in particular" parenthesis |
| `sigma_mixing_witness` | inhabitation: the paper's own two-state chain, `B̂ = 1` |

## The route to `‖P‖ ≤ 1`, and why it is not the paper's

The paper gets `‖P‖ ≤ 1` from `eq:reversal_contraction` (`proofs.tex:435`), i.e. through the
`λ`-reversal `T^λ` of `lem:adjoint`, whose existence is a disintegration theorem — obstruction 2
of `kb/entries/0006`. **This file does not use the reversal.** It proves the same bound from the
duality identity and `2ab ≤ a² + b²` integrated against `λ ⊗ T`: with `g := min(Tf, n)`,
`2∫g² ≤ 2∫(Tf)g ≤ ∫f² + ∫g²`, and `∫g² ≤ n²λ(𝒮) < ∞` lets `∫g²` be cancelled. The first
marginal of `λ ⊗ T` is `λ` because `T` is Markov, the second is `λT = λ` by invariance; nothing
else is used. So the bound is certified at the lemma's generality with no disintegration, and
`lem:adjoint` stays where it is (finite state spaces, `Core/Adjoint.lean`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒮` Polish | ✓ `[StandardBorelSpace α]` in `lem_sigma_mixing`, the measurable content of "Polish with its Borel σ-algebra"; `lem_sigma_mixing_polish` takes `[TopologicalSpace α] [PolishSpace α] [BorelSpace α]` literally. **Load-bearing only in the Dirac clause** (`exists_measurableSet_of_ne_smul_dirac`, through Mathlib's `IsZeroOneMeasure.exists_eq_dirac`); the first sentence holds on any measurable space (`sigma_mixing`) |
| `T` a Markov kernel on `𝒮` | ✓ `κ : Kernel α α`, `[IsMarkovKernel κ]` |
| `λ` finite | ✓ `[IsFiniteMeasure ν]` |
| `λ` non-zero | ✓ `[NeZero ν]` in `lem_sigma_mixing`; consumed only by the Dirac clause. Necessary there: on an empty type `ν = 0` is not a multiple of any Dirac mass, and `β̂₀ = 0` |
| `λ` `T`-invariant | ✓ `hinv : ν.bind ⇑κ = ν` |
| `P` the density action on `L²(λ)` | ✓ `densityActionL2`, the `Core.Kernel` construction at `p = 2`; **its boundedness is proved** (`isBoundedDensityAction_two`), not carried |
| `Π` the `λ`-mean projection | ✓ `meanProj ν 2` of `Core.Flow` |
| `ΠP = PΠ = Π` (used in the proof) | ✓ derived (`Core.Flow.mixing_of_massPreserving` from `Core.Kernel`'s `hone`/`hint`) |
| `β̂_n = ‖Pⁿ − Π‖_{L²(λ)}` | ✓ `Mixing.beta (densityActionL2 κ ν hinv) (meanProj ν 2) n`, the operator norm on `Lp ℝ 2 ν` |
| `B̂ < +∞` | ✓ `hsum : Summable fun n => ‖Pⁿ − Π‖`; `B̂` is `Mixing.B`, the `tsum` |
| conclusion: `S` converges in operator norm | ✓ `Tendsto (partialSum P Π) atTop (𝓝 (Mixing.S P Π))` in `Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν` |
| conclusion: `S(I−P) = I − Π` | ✓ |
| conclusion: `‖h − Πh‖ ≤ B̂ ‖(I−P)h‖` for all `h ∈ L²(λ)` | ✓ |
| `λ` not a multiple of a Dirac mass | ✓ `∀ (c : ℝ≥0∞) (x : α), ν ≠ c • Measure.dirac x` |
| conclusion: `β̂₀ = 1`, `B̂ ≥ 1` | ✓ |
| in particular: `𝒮` finite, `#𝒮 ≥ 2`, `λ > 0` everywhere | ✓ `sigma_mixing_finite`: `[Finite α] [MeasurableSingletonClass α] [Nontrivial α]`, `∀ x, 0 < ν {x}`; it concludes both that `ν` is not a multiple of a Dirac mass and `β̂₀ = 1`, `B̂ ≥ 1` |

## SCOPE (disclosed)

* **`p = 2` only.** `isBoundedDensityAction_two` is the `L²` contraction the lemma needs. The
  analogous `IsBoundedDensityAction κ ν p 1` for other `p` (which `Core/Kernel.lean`'s SCOPE
  records as true under invariance and unproved) is not attempted; `p = 1` would follow from
  `enorm_densityAction_le` and `lintegral_bindDensity` in a few lines.
* **"Polish" is read as `StandardBorelSpace`** in the main statement; the literal topological
  reading is `lem_sigma_mixing_polish`, a one-line corollary. Nothing topological is used.
* **The Dirac clause is stated as an implication inside the conclusion** of `lem_sigma_mixing`
  (`(∀ c x, ν ≠ c • dirac x) → β̂₀ = 1 ∧ 1 ≤ B̂`), which is the paper's "if moreover". The
  standalone set form (`sigma_mixing_beta_zero_of_set`) needs neither standard Borel nor `ν ≠ 0`.
* **`β̂₀ = 1` does not need summability**, and `sigma_mixing_beta_zero_of_set` does not assume it;
  `B̂ ≥ 1` does, because a non-summable `tsum` is `0` in Lean. The paper states both under
  summable mixing, so nothing is lost.
* **In the finite clause, `[Finite α]` is carried as the paper states it and is not consumed**:
  two distinct points of positive mass suffice (`sigma_mixing_two_states`), which is weaker. No
  standard Borel structure is needed there.
* **The density action on signed densities** is `Core.Kernel.densityAction`,
  `(T f⁺) − (T f⁻)`; that modelling choice is `Core/Kernel.lean`'s and is inherited, not re-made.
* **The witness is the paper's own two-state chain** (`prop:nonlinear_freezing`(2):
  `T(i→j) = 1/2`, `λ = (1/2, 1/2)`), realised as the constant kernel `Kernel.const Bool λ` with
  `λ` the uniform law on `Bool`; the density-action computation is reused from
  `Core/FamilyUniversality.lean` (`densityActionCLM_const_kernel`, `summable_const_kernel`). There
  `P = Π`, so the witness shows the bundle inhabited and `B̂ ≥ 1` sharp, not a chain with `P ≠ Π`.
* **`sorry`-free**; no new axiom.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

/-! ## `‖P‖ ≤ 1` on `L²(λ)`, from invariance and no reversal -/

/-- `2ab ≤ a² + b²` in `ℝ≥0∞` — including at `∞`, where both sides are `∞` unless a factor on
the left vanishes. -/
theorem two_mul_le_sq_add_sq_ennreal (a b : ℝ≥0∞) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · rcases eq_or_ne b 0 with rfl | hb
    · simp
    · simp [ENNReal.top_pow two_ne_zero]
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [ENNReal.top_pow two_ne_zero]
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast two_mul_le_add_sq a b

/-- **Duality for the density action**: `∫ (Tf)·h dλ = ∫ f(x) (∫ h dT(x)) dλ(x)`, for a
non-negative density `f` and a measurable test function `h`. It is `(Tf)λ = (fλ)T`
(`withDensity_bindDensity`) integrated against `h`. -/
theorem lintegral_bindDensity_mul (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    {h : α → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, bindDensity κ ν f x * h x ∂ν = ∫⁻ x, f x * ∫⁻ y, h y ∂κ x ∂ν := by
  have h1 : ∫⁻ x, h x ∂(ν.withDensity (bindDensity κ ν f))
      = ∫⁻ x, bindDensity κ ν f x * h x ∂ν :=
    lintegral_withDensity_eq_lintegral_mul ν (measurable_bindDensity κ ν f) hh
  rw [← h1, withDensity_bindDensity κ hinv f,
    Measure.lintegral_bind (κ.aemeasurable) hh.aemeasurable]
  exact lintegral_withDensity_eq_lintegral_mul₀ hf (hh.lintegral_kernel.aemeasurable)

/-- `2 ∫ (Tf)·h dλ ≤ ∫ f² dλ + ∫ h² dλ`: `2f(x)h(y) ≤ f(x)² + h(y)²` integrated against
`λ(dx) T(x,dy)`, whose first marginal is `λ` (`T` Markov) and second `λT = λ` (invariance). -/
theorem two_mul_lintegral_bindDensity_mul_le (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    {h : α → ℝ≥0∞} (hh : Measurable h) :
    2 * ∫⁻ x, bindDensity κ ν f x * h x ∂ν ≤ ∫⁻ x, f x ^ 2 ∂ν + ∫⁻ x, h x ^ 2 ∂ν := by
  have hh2 : Measurable fun y => h y ^ 2 := hh.pow_const 2
  rw [lintegral_bindDensity_mul κ hinv hf hh, ← lintegral_const_mul' 2 _ (by norm_num)]
  calc ∫⁻ x, 2 * (f x * ∫⁻ y, h y ∂κ x) ∂ν
      = ∫⁻ x, ∫⁻ y, 2 * f x * h y ∂κ x ∂ν := by
        congr 1; funext x; rw [lintegral_const_mul _ hh, mul_assoc]
    _ ≤ ∫⁻ x, ∫⁻ y, (f x ^ 2 + h y ^ 2) ∂κ x ∂ν := by
        gcongr with x y; exact two_mul_le_sq_add_sq_ennreal _ _
    _ = ∫⁻ x, (f x ^ 2 + ∫⁻ y, h y ^ 2 ∂κ x) ∂ν := by
        congr 1; funext x
        rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ x, f x ^ 2 ∂ν + ∫⁻ x, ∫⁻ y, h y ^ 2 ∂κ x ∂ν :=
        lintegral_add_right' _ hh2.lintegral_kernel.aemeasurable
    _ = ∫⁻ x, f x ^ 2 ∂ν + ∫⁻ x, h x ^ 2 ∂ν := by
        rw [← Measure.lintegral_bind κ.aemeasurable hh2.aemeasurable, hinv]

/-- **`∫ (Tf)² dλ ≤ ∫ f² dλ`** for every non-negative density `f`, with no integrability
assumed. The truncations `min(Tf, n)` have finite square integral, which is what lets the
duality bound be cancelled; monotone convergence removes the truncation. -/
theorem lintegral_bindDensity_sq_le (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) :
    ∫⁻ x, bindDensity κ ν f x ^ 2 ∂ν ≤ ∫⁻ x, f x ^ 2 ∂ν := by
  have hg : Measurable (bindDensity κ ν f) := measurable_bindDensity κ ν f
  set t : ℕ → α → ℝ≥0∞ := fun n x => min (bindDensity κ ν f x) n with ht_def
  have ht : ∀ n, Measurable (t n) := fun n => hg.min measurable_const
  have hbound : ∀ n, ∫⁻ x, t n x ^ 2 ∂ν ≤ ∫⁻ x, f x ^ 2 ∂ν := by
    intro n
    have hfin : ∫⁻ x, t n x ^ 2 ∂ν ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (n : ℝ≥0∞) ^ 2 ∂ν) ?_ (lintegral_mono fun x => ?_)
      · rw [lintegral_const]
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n))
          (measure_ne_top _ _)
      · gcongr
        exact min_le_right _ _
    have hsq : ∫⁻ x, t n x ^ 2 ∂ν ≤ ∫⁻ x, bindDensity κ ν f x * t n x ∂ν := by
      refine lintegral_mono fun x => ?_
      rw [sq]
      gcongr
      exact min_le_left _ _
    have h2 := two_mul_lintegral_bindDensity_mul_le κ hinv hf (ht n)
    have hsum : ∫⁻ x, t n x ^ 2 ∂ν + ∫⁻ x, t n x ^ 2 ∂ν
        ≤ ∫⁻ x, f x ^ 2 ∂ν + ∫⁻ x, t n x ^ 2 ∂ν := by
      rw [← two_mul]
      exact (mul_le_mul_right hsq 2).trans h2
    exact ENNReal.le_of_add_le_add_right hfin hsum
  have hsup : ∀ x, bindDensity κ ν f x ^ 2 = ⨆ n : ℕ, t n x ^ 2 := by
    intro x
    rw [← ENNReal.iSup_pow]
    congr 1
    simp only [ht_def]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hmono : Monotone fun n x => t n x ^ 2 := by
    intro n m hnm x
    simp only [ht_def]
    gcongr
  calc ∫⁻ x, bindDensity κ ν f x ^ 2 ∂ν = ∫⁻ x, ⨆ n : ℕ, t n x ^ 2 ∂ν := by
        congr 1; funext x; exact hsup x
    _ = ⨆ n : ℕ, ∫⁻ x, t n x ^ 2 ∂ν := lintegral_iSup (fun n => (ht n).pow_const 2) hmono
    _ ≤ ∫⁻ x, f x ^ 2 ∂ν := iSup_le hbound

/-- `‖Tf‖_{L²(λ)} ≤ ‖f‖_{L²(λ)}` for a non-negative density, in `eLpNorm` form. -/
theorem eLpNorm_bindDensity_two_le (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) :
    eLpNorm (bindDensity κ ν f) 2 ν ≤ eLpNorm f 2 ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_bindDensity_sq_le κ hinv hf) (by norm_num)

/-- `r⁺ + r⁻ = |r|`, in `ℝ≥0∞`. -/
theorem ofReal_add_ofReal_neg (r : ℝ) : ENNReal.ofReal r + ENNReal.ofReal (-r) = ‖r‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 r with hr | hr
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -r ≤ 0), add_zero, abs_of_nonneg hr]
  · rw [ENNReal.ofReal_of_nonpos hr, zero_add, abs_of_nonpos hr]

/-- `|P f| ≤ T |f|`, `λ`-a.e., for an integrable signed density: `|Tf⁺ − Tf⁻| ≤ Tf⁺ + Tf⁻`, and
`T` is additive. -/
theorem enorm_densityAction_le (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∀ᵐ x ∂ν, ‖densityAction κ ν f x‖ₑ ≤ bindDensity κ ν (fun y => ‖f y‖ₑ) x := by
  have hsplit : (fun y => ‖f y‖ₑ)
      = (fun y => ENNReal.ofReal (f y)) + (fun y => ENNReal.ofReal (-f y)) := by
    funext y
    simp only [_root_.Pi.add_apply, ofReal_add_ofReal_neg]
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  have hadd := bindDensity_add κ (ν := ν) (aemeasurable_ofReal hf) (lintegral_ofReal_ne_top hf)
    (lintegral_ofReal_ne_top hfn)
  filter_upwards [hadd, bindDensity_ofReal_lt_top κ hinv hf,
    bindDensity_ofReal_lt_top κ hinv hfn] with x hx hA hB
  rw [hsplit, hx]
  simp only [_root_.Pi.add_apply, densityAction]
  rw [Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal |(bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal
        - (bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x).toReal|
      ≤ ENNReal.ofReal ((bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal
        + (bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x).toReal) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := ENNReal.toReal_nonneg (a := bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x)
        have h2 := ENNReal.toReal_nonneg (a := bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x)
        refine abs_sub_le_iff.2 ⟨?_, ?_⟩ <;> linarith
    _ = bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hA.ne, ENNReal.ofReal_toReal hB.ne]

/-- **The density action of a Markov kernel is a contraction of `L²(λ)`** whenever `λ` is finite
and invariant: `IsBoundedDensityAction κ λ 2 1`. This is the `‖P‖ ≤ 1` that `lem:sigma_mixing`
presupposes in calling `P` an operator on `L²(λ)` (the paper's `eq:reversal_contraction`), and it
discharges the hypothesis `Core.Kernel` carries at `p = 2`. -/
theorem isBoundedDensityAction_two (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) : IsBoundedDensityAction κ ν 2 1 := by
  have key : ∀ f : α → ℝ, MemLp f 2 ν → eLpNorm (densityAction κ ν f) 2 ν ≤ eLpNorm f 2 ν := by
    intro f hf
    have hint : Integrable f ν := hf.integrable (by norm_num)
    calc eLpNorm (densityAction κ ν f) 2 ν
        ≤ eLpNorm (bindDensity κ ν (fun y => ‖f y‖ₑ)) 2 ν := by
          refine eLpNorm_mono_enorm_ae ?_
          simpa only [enorm_eq_self] using enorm_densityAction_le κ hinv hint
      _ ≤ eLpNorm (fun y => ‖f y‖ₑ) 2 ν :=
          eLpNorm_bindDensity_two_le κ hinv hf.aestronglyMeasurable.enorm
      _ = eLpNorm f 2 ν := eLpNorm_enorm f
  refine ⟨zero_le_one, fun f hf => ⟨(measurable_densityAction κ ν f).aestronglyMeasurable,
    lt_of_le_of_lt (key f hf) hf.eLpNorm_lt_top⟩, fun f hf => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  exact key f hf

/-! ## `‖I − Π‖ = 1` on `L²(λ)` -/

section MeanProj

variable {ν : Measure α} [IsFiniteMeasure ν]

/-- `⟪u, 𝟏⟫_{L²(λ)} = ∫ u dλ`. -/
theorem inner_constOne_two (u : Lp ℝ 2 ν) :
    inner ℝ u (constOne ν 2) = ∫ x, u x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_constOne (ν := ν) (p := 2)] with x hx
  rw [hx]
  simp

/-- **`Π` is an orthogonal projection**, read as `‖h − Πh‖ ≤ ‖h‖`: `h − Πh` has mean zero, hence
is orthogonal to the constant `Πh`, and Pythagoras concludes. -/
theorem norm_sub_meanProj_le (f : Lp ℝ 2 ν) : ‖f - meanProj ν 2 f‖ ≤ ‖f‖ := by
  set c : ℝ := (∫ x, f x ∂ν) / (ν Set.univ).toReal with hc
  have hm : meanProj ν 2 f = c • constOne ν 2 := meanProj_apply f
  have hint : ∫ x, (f - meanProj ν 2 f) x ∂ν = 0 := by
    have h1 := map_sub (integralCLM ν 2) f (meanProj ν 2 f)
    have h2 := map_smul (integralCLM ν 2) c (constOne ν 2)
    simp only [integralCLM_apply] at h1 h2
    rw [h1, hm, h2, integral_constOne, smul_eq_mul]
    rcases eq_or_ne (ν Set.univ).toReal 0 with h0 | h0
    · have hfz : ∫ x, f x ∂ν = 0 := by
        have hν : ν = 0 := by
          rw [ENNReal.toReal_eq_zero_iff] at h0
          rcases h0 with h0 | h0
          · exact Measure.measure_univ_eq_zero.1 h0
          · exact absurd h0 (measure_ne_top ν Set.univ)
        subst hν
        simp
      rw [h0, mul_zero, hfz, sub_zero]
    · rw [hc, div_mul_cancel₀ _ h0, sub_self]
  have horth : inner ℝ (f - meanProj ν 2 f) (meanProj ν 2 f) = 0 := by
    rw [show inner ℝ (f - meanProj ν 2 f) (meanProj ν 2 f)
        = c * inner ℝ (f - meanProj ν 2 f) (constOne ν 2) by rw [← inner_smul_right, ← hm],
      inner_constOne_two, hint, mul_zero]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (f - meanProj ν 2 f) (meanProj ν 2 f) horth
  rw [sub_add_cancel] at hpyth
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2
    (by rw [hpyth]; linarith [mul_self_nonneg ‖meanProj ν 2 f‖])

/-- `‖I − Π‖ ≤ 1` on `L²(λ)`, for every finite `λ`. -/
theorem norm_one_sub_meanProj_le :
    ‖(1 : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) - meanProj ν 2‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  rw [one_mul]
  exact norm_sub_meanProj_le f

/-- **`𝟏_X − Π𝟏_X ≠ 0`** — the paper's "`𝟏_X` is not `λ`-a.e. constant" — for a measurable `X`
with `0 < λ(X) < λ(𝒮)`. If `𝟏_X = r` a.e., then `r = 1` on the non-null `X`, and
`r = λ(X)/λ(𝒮) = 1` contradicts `λ(X) < λ(𝒮)`. -/
theorem meanProj_indicator_ne {X : Set α} (hX : MeasurableSet X) (hX0 : 0 < ν X)
    (hX1 : ν X < ν Set.univ) :
    meanProj ν 2 (indicatorConstLp 2 hX (measure_ne_top ν X) (1 : ℝ))
      ≠ indicatorConstLp 2 hX (measure_ne_top ν X) (1 : ℝ) := by
  intro heq
  set r : ℝ := (∫ x, (indicatorConstLp 2 hX (measure_ne_top ν X) (1 : ℝ)) x ∂ν)
    / (ν Set.univ).toReal with hr
  have hae : ∀ᵐ x ∂ν, X.indicator (fun _ => (1 : ℝ)) x = r := by
    have h1 := indicatorConstLp_coeFn (p := 2) (hs := hX) (hμs := measure_ne_top ν X)
      (c := (1 : ℝ))
    have h2 : ⇑(meanProj ν 2 (indicatorConstLp 2 hX (measure_ne_top ν X) (1 : ℝ)))
        =ᵐ[ν] fun _ => r := by
      rw [meanProj_apply]
      filter_upwards [Lp.coeFn_smul r (constOne ν 2), coeFn_constOne (ν := ν) (p := 2)]
        with x hx hx1
      rw [hx, _root_.Pi.smul_apply, hx1, smul_eq_mul, mul_one]
    rw [heq] at h2
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← hx1, hx2]
  have hr1 : r = 1 := by
    by_contra hne
    have hsub : X ⊆ {x | ¬ X.indicator (fun _ => (1 : ℝ)) x = r} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Set.indicator_of_mem hx]
      exact fun h => hne h.symm
    have hnull : ν {x | ¬ X.indicator (fun _ => (1 : ℝ)) x = r} = 0 := ae_iff.1 hae
    exact absurd (measure_mono_null hsub hnull) hX0.ne'
  have hint : ∫ x, (indicatorConstLp 2 hX (measure_ne_top ν X) (1 : ℝ)) x ∂ν = ν.real X := by
    rw [integral_indicatorConstLp, smul_eq_mul, mul_one]
  have huniv : (ν Set.univ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(hX0.trans hX1).ne', measure_ne_top ν Set.univ⟩
  rw [hr, hint, div_eq_one_iff_eq huniv, measureReal_def,
    ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν X) (measure_ne_top ν Set.univ)] at hr1
  exact hX1.ne hr1

/-- **`‖I − Π‖_{L²(λ)} = 1`** as soon as `λ` charges a measurable `X` with
`0 < λ(X) < λ(𝒮)`: `≤ 1` by orthogonality, `≥ 1` because `I − Π` is a non-zero idempotent
(`Mixing.one_le_norm_one_sub_proj`). -/
theorem norm_one_sub_meanProj_eq_one {X : Set α} (hX : MeasurableSet X) (hX0 : 0 < ν X)
    (hX1 : ν X < ν Set.univ) :
    ‖(1 : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) - meanProj ν 2‖ = 1 := by
  have hν : ν Set.univ ≠ 0 := (hX0.trans hX1).ne'
  refine le_antisymm norm_one_sub_meanProj_le
    (Mixing.one_le_norm_one_sub_proj (meanProj_idem hν) ?_)
  exact Mixing.one_sub_ne_zero_iff.2 ⟨_, meanProj_indicator_ne hX hX0 hX1⟩

end MeanProj

/-! ## Not a multiple of a Dirac mass -/

section Dirac

/-- **The paper's Polish step**: a non-zero finite measure on a standard Borel space that is not a
multiple of a Dirac mass charges a measurable `X` with `0 < λ(X) < λ(𝒮)`. Otherwise
`λ(𝒮)⁻¹ λ` is a zero-one measure, hence a Dirac mass (`IsZeroOneMeasure.exists_eq_dirac`).
Standard Borel is what that step consumes: on `ℝ` with the countable–cocountable σ-algebra the
countable–cocountable measure is zero-one and not a Dirac mass. -/
theorem exists_measurableSet_of_ne_smul_dirac [StandardBorelSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] [NeZero ν] (h : ∀ (c : ℝ≥0∞) (x : α), ν ≠ c • Measure.dirac x) :
    ∃ X, MeasurableSet X ∧ 0 < ν X ∧ ν X < ν Set.univ := by
  by_contra hne
  push Not at hne
  have hu0 : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.2 (NeZero.ne ν)
  have hut : ν Set.univ ≠ ⊤ := measure_ne_top ν Set.univ
  set μ : Measure α := (ν Set.univ)⁻¹ • ν with hμ
  haveI : IsZeroOneMeasure μ := by
    refine ⟨fun s hs => ?_⟩
    simp only [hμ, Measure.smul_apply, smul_eq_mul]
    rcases eq_or_ne (ν s) 0 with h0 | h0
    · left; rw [h0, mul_zero]
    · right
      have hle : ν s ≤ ν Set.univ := measure_mono (Set.subset_univ s)
      have hge : ν Set.univ ≤ ν s := hne s hs (pos_iff_ne_zero.2 h0)
      rw [le_antisymm hle hge, ENNReal.inv_mul_cancel hu0 hut]
  haveI : NeZero μ := by
    refine ⟨fun h0 => ?_⟩
    have := congrArg (fun m : Measure α => m Set.univ) h0
    simp only [hμ, Measure.smul_apply, smul_eq_mul, Measure.coe_zero, _root_.Pi.zero_apply,
      ENNReal.inv_mul_cancel hu0 hut] at this
    exact one_ne_zero this
  obtain ⟨x₀, hx₀⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := μ)
  refine h (ν Set.univ) x₀ ?_
  rw [← hx₀, hμ, smul_smul, ENNReal.mul_inv_cancel hu0 hut, one_smul]

/-- Two distinct points of positive mass: `λ` is not a multiple of a Dirac mass. -/
theorem ne_smul_dirac_of_two_pos [MeasurableSingletonClass α] {ν : Measure α} {x y : α}
    (hxy : x ≠ y) (hx : 0 < ν {x}) (hy : 0 < ν {y}) :
    ∀ (c : ℝ≥0∞) (z : α), ν ≠ c • Measure.dirac z := by
  intro c z hν
  have key : ∀ w, w ≠ z → ν {w} = 0 := by
    intro w hw
    have hz : z ∉ ({w} : Set α) := fun h => hw (Set.mem_singleton_iff.1 h).symm
    rw [hν, Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton w),
      Set.indicator_of_notMem hz, smul_zero]
  by_cases hxz : x = z
  · exact hy.ne' (key y fun h => hxy (hxz.trans h.symm))
  · exact hx.ne' (key x hxz)

/-- Two distinct points of positive mass: `X := {x}` has `0 < λ(X) < λ(𝒮)`. -/
theorem exists_measurableSet_of_two_pos [MeasurableSingletonClass α] {ν : Measure α}
    [IsFiniteMeasure ν] {x y : α} (hxy : x ≠ y) (hx : 0 < ν {x}) (hy : 0 < ν {y}) :
    ∃ X, MeasurableSet X ∧ 0 < ν X ∧ ν X < ν Set.univ := by
  refine ⟨{x}, measurableSet_singleton x, hx, ?_⟩
  have hdisj : Disjoint ({x} : Set α) {y} := Set.disjoint_singleton.2 hxy
  calc ν {x} < ν {x} + ν {y} := ENNReal.lt_add_right (measure_ne_top ν _) hy.ne'
    _ = ν ({x} ∪ {y}) := (measure_union hdisj (measurableSet_singleton y)).symm
    _ ≤ ν Set.univ := measure_mono (Set.subset_univ _)

end Dirac

/-! ## The lemma -/

section Assembled

/-- **The paper's `P` of `lem:sigma_mixing`**: the density action `h ↦ d((hλ)T)/dλ` of a Markov
kernel on `L²(λ)`, a bounded operator by `isBoundedDensityAction_two` rather than by
hypothesis. -/
noncomputable def densityActionL2 (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  densityActionCLM κ ν 2 hinv (isBoundedDensityAction_two κ hinv)

variable (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α) [IsFiniteMeasure ν]

/-- `‖P‖_{L²(λ) → L²(λ)} ≤ 1`. -/
theorem norm_densityActionL2_le (hinv : ν.bind ⇑κ = ν) : ‖densityActionL2 κ ν hinv‖ ≤ 1 :=
  norm_densityActionCLM_le κ ν 2 hinv _

/-- The `Mixing` bundle at `(P, Π)`, with only summability assumed: `ΠP = PΠ = Π` is derived. -/
theorem mixing_densityActionL2 (hinv : ν.bind ⇑κ = ν)
    (hsum : Summable fun n : ℕ => ‖densityActionL2 κ ν hinv ^ n - meanProj ν 2‖) :
    Mixing (densityActionL2 κ ν hinv) (meanProj ν 2) :=
  mixing_of_massPreserving (densityActionCLM_constOne κ ν 2 hinv _)
    (integral_densityActionCLM κ ν 2 hinv _) hsum

/-- **`lem:sigma_mixing`, first sentence**, at the kernel level: for `T` Markov and `λ` finite
and invariant, summable `L²`-mixing makes `S = ∑(Pⁿ − Π)` converge in operator norm, with
`S(I−P) = I − Π` and `‖h − Πh‖ ≤ B̂ ‖(I−P)h‖`. No Polish structure and no `λ ≠ 0` is used. -/
theorem sigma_mixing (hinv : ν.bind ⇑κ = ν)
    (hsum : Summable fun n : ℕ => ‖densityActionL2 κ ν hinv ^ n - meanProj ν 2‖) :
    Tendsto (GFNBounds.Doubling.partialSum (densityActionL2 κ ν hinv) (meanProj ν 2)) atTop
        (𝓝 (Mixing.S (densityActionL2 κ ν hinv) (meanProj ν 2))) ∧
      Mixing.S (densityActionL2 κ ν hinv) (meanProj ν 2) * (1 - densityActionL2 κ ν hinv)
        = 1 - meanProj ν 2 ∧
      ∀ h : Lp ℝ 2 ν, ‖h - meanProj ν 2 h‖
        ≤ Mixing.B (densityActionL2 κ ν hinv) (meanProj ν 2)
          * ‖(1 - densityActionL2 κ ν hinv) h‖ :=
  let hm := mixing_densityActionL2 κ ν hinv hsum
  ⟨hm.tendsto_partialSum, hm.poisson_right, hm.coercivity⟩

/-- **`lem:sigma_mixing`, `β̂₀ = 1`**, from a measurable `X` with `0 < λ(X) < λ(𝒮)`. -/
theorem sigma_mixing_beta_zero_of_set (hinv : ν.bind ⇑κ = ν) {X : Set α}
    (hX : MeasurableSet X) (hX0 : 0 < ν X) (hX1 : ν X < ν Set.univ) :
    Mixing.beta (densityActionL2 κ ν hinv) (meanProj ν 2) 0 = 1 := by
  rw [Mixing.beta_zero, norm_one_sub_meanProj_eq_one hX hX0 hX1]

/-- **`lem:sigma_mixing`, `B̂ ≥ 1`**, from summability and the same `X`: `B̂ ≥ β̂₀ = 1`. -/
theorem sigma_mixing_one_le_B_of_set (hinv : ν.bind ⇑κ = ν)
    (hsum : Summable fun n : ℕ => ‖densityActionL2 κ ν hinv ^ n - meanProj ν 2‖) {X : Set α}
    (hX : MeasurableSet X) (hX0 : 0 < ν X) (hX1 : ν X < ν Set.univ) :
    1 ≤ Mixing.B (densityActionL2 κ ν hinv) (meanProj ν 2) := by
  rw [← sigma_mixing_beta_zero_of_set κ ν hinv hX hX0 hX1]
  exact (mixing_densityActionL2 κ ν hinv hsum).summable_beta.le_tsum 0
    fun n _ => Mixing.beta_nonneg _ _ n

/-- **`lem:sigma_mixing`, whole.** `T` a Markov kernel on a standard Borel space leaving a
non-zero finite `λ` invariant, `P` its density action on `L²(λ)`, `Π` the `λ`-mean projection,
`B̂ = ∑‖Pⁿ − Π‖ < ∞`: then `S` converges in operator norm, `S(I−P) = I − Π`,
`‖h − Πh‖ ≤ B̂ ‖(I−P)h‖` for every `h ∈ L²(λ)`; and if moreover `λ` is not a multiple of a
Dirac mass, `β̂₀ = 1` and `B̂ ≥ 1`. -/
theorem lem_sigma_mixing [StandardBorelSpace α] [NeZero ν] (hinv : ν.bind ⇑κ = ν)
    (hsum : Summable fun n : ℕ => ‖densityActionL2 κ ν hinv ^ n - meanProj ν 2‖) :
    (Tendsto (GFNBounds.Doubling.partialSum (densityActionL2 κ ν hinv) (meanProj ν 2)) atTop
        (𝓝 (Mixing.S (densityActionL2 κ ν hinv) (meanProj ν 2))) ∧
      Mixing.S (densityActionL2 κ ν hinv) (meanProj ν 2) * (1 - densityActionL2 κ ν hinv)
        = 1 - meanProj ν 2 ∧
      ∀ h : Lp ℝ 2 ν, ‖h - meanProj ν 2 h‖
        ≤ Mixing.B (densityActionL2 κ ν hinv) (meanProj ν 2)
          * ‖(1 - densityActionL2 κ ν hinv) h‖) ∧
    ((∀ (c : ℝ≥0∞) (x : α), ν ≠ c • Measure.dirac x) →
      Mixing.beta (densityActionL2 κ ν hinv) (meanProj ν 2) 0 = 1 ∧
        1 ≤ Mixing.B (densityActionL2 κ ν hinv) (meanProj ν 2)) := by
  refine ⟨sigma_mixing κ ν hinv hsum, fun hd => ?_⟩
  obtain ⟨X, hX, hX0, hX1⟩ := exists_measurableSet_of_ne_smul_dirac hd
  exact ⟨sigma_mixing_beta_zero_of_set κ ν hinv hX hX0 hX1,
    sigma_mixing_one_le_B_of_set κ ν hinv hsum hX hX0 hX1⟩

/-- **`lem:sigma_mixing`, whole, on a Polish space with its Borel σ-algebra** — the paper's
literal hypothesis; `lem_sigma_mixing` through `standardBorel_of_polish`. -/
theorem lem_sigma_mixing_polish [TopologicalSpace α] [PolishSpace α] [BorelSpace α] [NeZero ν]
    (hinv : ν.bind ⇑κ = ν)
    (hsum : Summable fun n : ℕ => ‖densityActionL2 κ ν hinv ^ n - meanProj ν 2‖) :
    (Tendsto (GFNBounds.Doubling.partialSum (densityActionL2 κ ν hinv) (meanProj ν 2)) atTop
        (𝓝 (Mixing.S (densityActionL2 κ ν hinv) (meanProj ν 2))) ∧
      Mixing.S (densityActionL2 κ ν hinv) (meanProj ν 2) * (1 - densityActionL2 κ ν hinv)
        = 1 - meanProj ν 2 ∧
      ∀ h : Lp ℝ 2 ν, ‖h - meanProj ν 2 h‖
        ≤ Mixing.B (densityActionL2 κ ν hinv) (meanProj ν 2)
          * ‖(1 - densityActionL2 κ ν hinv) h‖) ∧
    ((∀ (c : ℝ≥0∞) (x : α), ν ≠ c • Measure.dirac x) →
      Mixing.beta (densityActionL2 κ ν hinv) (meanProj ν 2) 0 = 1 ∧
        1 ≤ Mixing.B (densityActionL2 κ ν hinv) (meanProj ν 2)) :=
  lem_sigma_mixing κ ν hinv hsum

/-- The "in particular" of `lem:sigma_mixing`, in the weaker form its proof uses: two distinct
points of positive mass make `λ` not a multiple of a Dirac mass, and give `β̂₀ = 1`, `B̂ ≥ 1`. -/
theorem sigma_mixing_two_states [MeasurableSingletonClass α] (hinv : ν.bind ⇑κ = ν)
    (hsum : Summable fun n : ℕ => ‖densityActionL2 κ ν hinv ^ n - meanProj ν 2‖)
    {x y : α} (hxy : x ≠ y) (hx : 0 < ν {x}) (hy : 0 < ν {y}) :
    (∀ (c : ℝ≥0∞) (z : α), ν ≠ c • Measure.dirac z) ∧
      Mixing.beta (densityActionL2 κ ν hinv) (meanProj ν 2) 0 = 1 ∧
        1 ≤ Mixing.B (densityActionL2 κ ν hinv) (meanProj ν 2) := by
  obtain ⟨X, hX, hX0, hX1⟩ := exists_measurableSet_of_two_pos hxy hx hy
  exact ⟨ne_smul_dirac_of_two_pos hxy hx hy, sigma_mixing_beta_zero_of_set κ ν hinv hX hX0 hX1,
    sigma_mixing_one_le_B_of_set κ ν hinv hsum hX hX0 hX1⟩

/-- **`lem:sigma_mixing`, "in particular if `𝒮` is finite with `#𝒮 ≥ 2` and `λ > 0`
everywhere"**: then `λ` is not a multiple of a Dirac mass, `β̂₀ = 1` and `B̂ ≥ 1`. `[Finite α]`
is the paper's and is not consumed (`sigma_mixing_two_states`). -/
theorem sigma_mixing_finite [Finite α] [MeasurableSingletonClass α] [Nontrivial α]
    (hpos : ∀ x, 0 < ν {x}) (hinv : ν.bind ⇑κ = ν)
    (hsum : Summable fun n : ℕ => ‖densityActionL2 κ ν hinv ^ n - meanProj ν 2‖) :
    (∀ (c : ℝ≥0∞) (z : α), ν ≠ c • Measure.dirac z) ∧
      Mixing.beta (densityActionL2 κ ν hinv) (meanProj ν 2) 0 = 1 ∧
        1 ≤ Mixing.B (densityActionL2 κ ν hinv) (meanProj ν 2) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  exact sigma_mixing_two_states κ ν hinv hsum hxy (hpos x) (hpos y)

end Assembled

/-! ## Inhabitation: the paper's two-state chain -/

section Witness

/-- The uniform law `λ = (1/2, 1/2)` on the two-point space. -/
noncomputable def boolUniform : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure boolUniform := by
  unfold boolUniform
  infer_instance

theorem boolUniform_singleton_pos (b : Bool) : 0 < boolUniform {b} := by
  rw [boolUniform, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.uniformOfFintype_apply]
  exact ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)

/-- **Inhabitation of `lem_sigma_mixing`'s whole hypothesis bundle** (`kb/entries/0025`), on the
two-state chain `T(i → j) = 1/2`, `λ = (1/2, 1/2)` of `prop:nonlinear_freezing`(2), realised as
`Kernel.const Bool λ` on the standard Borel space `Bool`: `λ` is invariant, non-zero and not a
multiple of a Dirac mass, the mixing coefficients are summable, the lemma applies, and `B̂ = 1`
exactly — so `B̂ ≥ 1` is sharp. -/
theorem sigma_mixing_witness :
    boolUniform.bind ⇑(Kernel.const Bool boolUniform) = boolUniform ∧
    (∀ (c : ℝ≥0∞) (x : Bool), boolUniform ≠ c • Measure.dirac x) ∧
    Summable (fun n : ℕ => ‖densityActionL2 (Kernel.const Bool boolUniform) boolUniform
      Family.bind_const_kernel ^ n - meanProj boolUniform 2‖) ∧
    Mixing.beta (densityActionL2 (Kernel.const Bool boolUniform) boolUniform
      Family.bind_const_kernel) (meanProj boolUniform 2) 0 = 1 ∧
    Mixing.B (densityActionL2 (Kernel.const Bool boolUniform) boolUniform
      Family.bind_const_kernel) (meanProj boolUniform 2) = 1 := by
  have hne : (true : Bool) ≠ false := by decide
  have hnd := ne_smul_dirac_of_two_pos hne (boolUniform_singleton_pos true)
    (boolUniform_singleton_pos false)
  have hsum : Summable (fun n : ℕ => ‖densityActionL2 (Kernel.const Bool boolUniform)
      boolUniform Family.bind_const_kernel ^ n - meanProj boolUniform 2‖) :=
    Family.summable_const_kernel
  have hlem := (lem_sigma_mixing (Kernel.const Bool boolUniform) boolUniform
    Family.bind_const_kernel hsum).2 hnd
  have hP : densityActionL2 (Kernel.const Bool boolUniform) boolUniform Family.bind_const_kernel
      = meanProj boolUniform 2 := Family.densityActionCLM_const_kernel
  have hν : boolUniform Set.univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  refine ⟨Family.bind_const_kernel, hnd, hsum, hlem.1, ?_⟩
  rw [hP, Mixing.B_of_idem (meanProj_idem hν), ← Mixing.beta_zero, ← hP]
  exact hlem.1

end Witness

end GFNBounds.Core
