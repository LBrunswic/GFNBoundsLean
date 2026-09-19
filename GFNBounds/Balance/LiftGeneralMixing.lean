import GFNBounds.Balance.LiftGeneral
import GFNBounds.Core.SigmaMixing
import GFNBounds.Core.FamilyUniversality
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# `prop:db_lift`, `lem:lift_mixing`, `lem:lift_coercivity` on a general measurable space

**`prop:db_lift`**, **`lem:lift_mixing`**, **`lem:lift_coercivity`** — `proofs.tex`, the
proposition and the two lemmas carrying those labels (`:534–545`, `:560–570`, `:572–587` when
written; line numbers drift, kb `0036`, the label is the anchor). Built on the general edge lift
of `GFNBounds/Balance/LiftGeneral.lean` (`edgeLift`, `edgeMeasure`, `eq:muK2_density` as
`rnDeriv_bind_edgeLift`) and on the `L²` density action of `GFNBounds/Core/SigmaMixing.lean`
(`densityActionL2`, bounded by invariance alone) with the mean projection `meanProj` of
`GFNBounds/Core/Flow.lean`. The finite forms are `Balance/Lift.lean` (`db_lift_loss`,
`db_lift_iff`) and `Balance/LiftFinite.lean` (`lift_mixing_dens`, `lift_coercivity_finite`).

> (`prop:db_lift`) Let `μ ∈ 𝓜²(λ₂)` be an edge flow, let `F := m₁μ` and let `π_→^μ` be the
> disintegration `μ = F ⊗ π_→^μ`. Then for any `g` and any training distribution `ν̂` on `𝒮²`,
> `∫ g(d(μK₂)/dμ) dν̂ = ∫ g( F(ds')π_←(s'→ds) / F(ds)π_→^μ(s→ds') ) dν̂`, the `g`-divergence
> detailed-balance loss with frozen backward policy […]. In particular `μK₂ = μ` if and only if
> `(F, π_→^μ)` satisfies detailed balance with respect to `π_←`.

> (`lem:lift_mixing`) In the setting of Definition `def:edge_lift`, let
> `β_n := ‖π_←ⁿ − Π‖_{L²(λ)}` and `β̂_n := ‖K₂ⁿ − Π₂‖_{L²(λ₂)}` be the `L²`-mixing coefficients
> of the density actions of `π_←` and of its edge lift `K₂` […]. Then `β̂_n = β_{n−1}` for every
> `n ≥ 1`.

> (`lem:lift_coercivity`) In the setting of Definition `def:edge_lift`, let `P` and `P₂` be the
> density actions `φ ↦ d((φλ)π_←)/dλ` of `π_←` on `L²(λ)` and `h ↦ d((hλ₂)K₂)/dλ₂` of `K₂` on
> `L²(λ₂)`, and let `Π` and `Π₂` be the mean projections against `λ` and `λ₂`. If `C ≥ 0`
> satisfies `‖φ − Πφ‖ ≤ C‖(I − P)φ‖` for every `φ ∈ L²(λ)`, then
> `‖h − Π₂h‖ ≤ (1 + C)‖(I − P₂)h‖` for every `h ∈ L²(λ₂)`.

## The one idea: three operators, and no reversal

Both lemmas are proved on **density actions**, the paper's objects, through three bounded
operators between `L²(λ)` and `L²(λ₂)`:

* `E φ := φ ∘ pr₂` (`liftSnd`) and `D φ := φ ∘ pr₁` (`liftFst`), linear isometries because both
  marginals of `λ₂` are `λ` (Mathlib's `Lp.compMeasurePreservingₗᵢ`);
* `M := E† P₂` (`edgeMarg`), which is the paper's `h ↦ k_h`, the `λ`-density of the first
  marginal of `hλ₂`: `E M = P₂` is `eq:muK2_density` on `L²` (`liftSnd_edgeMarg`).

The identities `P₂ E = E P` (`densityActionL2_edge_liftSnd`), `P₂ D = E`, hence `M E = P`,
`M D = 1` (`edgeMarg_liftSnd`, `edgeMarg_liftFst`), `Π₂ = E Π M` (`meanProj_edge`) and
`‖M‖ ≤ 1` give `P₂^{n+1} − Π₂ = E (Pⁿ − Π) M`, from which `β̂_{n+1} ≤ β_n` (`E` isometric,
`‖M‖ ≤ 1`) and `β_n ≤ β̂_{n+1}` (test `Dφ`, the paper's `f(z,s') = φ(s')` read on the density
side). The paper's proof passes to function actions and uses `π_→^λ`; neither is needed here, so
**no standard Borel hypothesis and no disintegration** enter the two lemmas. `P₂h ∈ range E` is
read off `rnDeriv_bind_edgeLift` applied to `h⁺λ₂` and `h⁻λ₂` (`densityAction_edge_exists`).

## What is proved

| | |
|---|---|
| `DetailedBalance` | `F ⊗ π_→ = π_← ⊗ F`, i.e. `F(ds)π_→(s→ds') = F(ds')π_←(s'→ds)` (= `IsReversal T π_→ F`) |
| `db_lift_ratio_eq`, `db_lift_loss_eq` | **`prop:db_lift`, the loss identity**: `d(μK₂)/dμ = d(π_← ⊗ F)/d(F ⊗ π_→^μ)` as functions, for every disintegration `π_→^μ`, so the losses agree for every `g`, `ν̂` |
| `bind_edgeLift_eq_self_iff` | **`prop:db_lift`, "in particular"**: `μK₂ = μ ↔ DetailedBalance π_← F π_→^μ` |
| `rnDeriv_bind_eq_one_iff` | the proof's last sentence: `d(μK)/dμ = 1` `μ`-a.e. iff `μK = μ`, any Markov `K`, finite `μ` |
| `db_lift_ratio_ae` | the proof's route: `d(μK₂)/dμ = (dF/dλ)(s') / (dμ/dλ₂)(s,s')`, `μ`-a.e., for `μ ≪ λ₂` |
| `db_lift` | **`prop:db_lift` assembled** on a standard Borel `𝒮`, `π_→^μ := μ.condKernel` |
| `densityAction_edge_snd`, `densityAction_edge_fst`, `densityAction_edge_exists` | `P₂(φ∘pr₂) = (Pφ)∘pr₂`, `P₂(φ∘pr₁) = φ∘pr₂`, `P₂h = k_h∘pr₂` pointwise a.e. |
| `liftSnd`, `liftFst`, `edgeMarg` and their identities | the three operators above |
| `lift_mixing_succ`, `lift_mixing_general` | **`lem:lift_mixing`**: `β̂_{n+1} = β_n`, i.e. `β̂_n = β_{n−1}` for `n ≥ 1` |
| `lift_coercivity_general` | **`lem:lift_coercivity`** |
| `lift_mixing_summable_iff`, `lift_mixing_B`, `lift_beta_zero_le_one`, `lift_mixing_B_eq_one_add`, `lift_coercivity_of_mixing` | the remark after `lem:lift_coercivity`: `C = B` lifts to `1 + B`, and `B̂₂ = β̂₀ + B`, `= 1 + B` when `λ` charges a measurable `X` with `0 < λ(X) < λ(𝒮)` (on a Polish `𝒮`: `λ` not a multiple of a Dirac mass) |
| `lift_hypotheses_inhabited`, `lift_coercivity_const` | non-vacuity (kb `0025`, `0027`): the resampling kernel `x ↦ ρ` meets every hypothesis, `C = 1` |

## SCOPE (disclosed)

* **State space.** `lem:lift_mixing` and `lem:lift_coercivity` hold on **any measurable space**
  (the paper's `𝒮` is Polish). `prop:db_lift`'s identities hold on any measurable space for any
  kernel `π_→^μ` with `μ = F ⊗ π_→^μ` (`[μ.IsCondKernel pf]`); its *existence* is Mathlib's
  `Measure.condKernel`, which needs `[StandardBorelSpace 𝒮] [Nonempty 𝒮]` — Polish with its Borel
  σ-algebra is standard Borel, and on the empty space every measure is `0`.
* **`prop:db_lift` is stated for every finite `μ` on `𝒮²`**, not only `μ ∈ 𝓜²(λ₂)`: the loss
  identity is an equality of Radon–Nikodym derivatives of equal measures (`μK₂ = π_← ⊗ F` by
  `bind_edgeLift`, `μ = F ⊗ π_→^μ` by disintegration) and uses neither `λ` nor its invariance.
  Stronger than the statement, in the safe direction. `g : ℝ≥0∞ → ℝ` is any function (the
  paper's `g : ℝ₊* → ℝ` extended arbitrarily at `0, ∞`); the integral is Bochner's, and since the
  two integrands are the same function the identity holds whatever `ν̂` and integrability. The
  parenthetical on orientation (`g(1/x)`, symmetric `g`) is commentary and is not formalized.
* **`β_n`, `β̂_n` are Mathlib operator norms** `‖Pⁿ − Π‖`, `‖P₂ⁿ − Π₂‖` on `Lp ℝ 2`, with `Pⁿ`
  the `n`-th power of the density action — the reading `lem:sigma_mixing`'s row uses
  (`Mixing.beta`). The paper's `π_←ⁿ` is the `n`-step kernel, whose density action is `Pⁿ`; that
  identification is not formalized. The density action on signed densities is
  `Core.Kernel.densityAction`, `(T f⁺) − (T f⁻)` — the modelling of `Core/Kernel.lean`, inherited.
* **`λ` finite** (`[IsFiniteMeasure lam]`) and invariant (`hinv : lam.bind T = lam`), as the
  paper's conventions fix; "non-zero" is never used.
* **No normalisation**: `λ` need not be a probability (the finite forms of `LiftFinite.lean`
  assumed mass `1`; the general `Π = λ(𝒮)⁻¹∫ · dλ` removes that restriction).
* **The remark's "`1 + C` is also the value of the edge-lifted mixing sum"** holds when `λ`
  charges some `X` with `0 < λ(X) < λ(𝒮)` (`lift_mixing_B_eq_one_add`); in general
  `B̂₂ = β̂₀ + B` with `β̂₀ = ‖I − Π₂‖ ≤ 1` (`lift_mixing_B`). When `λ` is a multiple of a Dirac
  mass `L²(λ₂)` has dimension at most one, `β̂₀ = 0` and the sentence fails (not formalized: noted as a
  finding on the remark, which is not a labelled statement).
* **`sorry`-free**; no new axiom.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `π_←` a backward policy = Markov kernel on `𝒮` | ✓ `T : Kernel S S`, `[IsMarkovKernel T]` |
| `λ` `π_←`-invariant, finite, non-zero | ✓ `hinv`, `[IsFiniteMeasure lam]`; non-zero unused |
| `𝒮` Polish | ✓ weakened: any measurable space; standard Borel only to construct `π_→^μ` |
| `μ ∈ 𝓜²(λ₂)` an edge flow (`prop:db_lift`) | ✓ weakened: any finite `μ` (`db_lift_ratio_ae` uses `μ ≪ λ₂`) |
| `π_→^μ` the disintegration `μ = F ⊗ π_→^μ` | ✓ any `pf` with `μ.IsCondKernel pf`; `μ.condKernel` in `db_lift` |
| `g`, `ν̂` arbitrary | ✓ `g : ℝ≥0∞ → ℝ`, `nu : Measure (S × S)` arbitrary |
| `P`, `P₂` density actions on `L²` | ✓ `Core.densityActionL2 T lam hinv`, `… (edgeLift T) (edgeMeasure T lam) _` |
| `Π`, `Π₂` mean projections | ✓ `Core.meanProj lam 2`, `Core.meanProj (edgeMeasure T lam) 2` |
| `C ≥ 0` with `‖φ − Πφ‖ ≤ C‖(I−P)φ‖` | ✓ `hC`, `hcoer`; inhabited (`lift_coercivity_const`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance.LiftGeneral

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-! ### `prop:db_lift` -/

/-- **Detailed balance of `(F, π_→)` with respect to `π_←`**: `F(ds)π_→(s → ds') =
F(ds')π_←(s' → ds)` as measures on `𝒮²`, i.e. `F ⊗ π_→ = π_← ⊗ F` in the paper's notation. -/
def DetailedBalance (T : Kernel S S) (F : Measure S) (pf : Kernel S S) : Prop :=
  F ⊗ₘ pf = (F ⊗ₘ T).map Prod.swap

theorem detailedBalance_iff_isReversal (T : Kernel S S) (F : Measure S) (pf : Kernel S S) :
    DetailedBalance T F pf ↔ IsReversal T pf F := Iff.rfl

section DB

variable (T : Kernel S S) [IsMarkovKernel T] (μ : Measure (S × S)) [IsFiniteMeasure μ]
  (pf : Kernel S S) [μ.IsCondKernel pf]

/-- **`prop:db_lift`, the ratio**: `d(μK₂)/dμ = d(π_← ⊗ F)/d(F ⊗ π_→^μ)`, as functions:
`μK₂ = π_← ⊗ m₁μ` (`bind_edgeLift`) and `μ = m₁μ ⊗ π_→^μ` (disintegration). -/
theorem db_lift_ratio_eq :
    (μ.bind (edgeLift T)).rnDeriv μ = (edgeMeasure T μ.fst).rnDeriv (μ.fst ⊗ₘ pf) := by
  rw [bind_edgeLift, Measure.disintegrate μ pf]

/-- **`prop:db_lift`, the loss identity**, for every `g` and every training distribution `ν̂`. -/
theorem db_lift_loss_eq (g : ℝ≥0∞ → ℝ) (nu : Measure (S × S)) :
    ∫ p, g ((μ.bind (edgeLift T)).rnDeriv μ p) ∂nu
      = ∫ p, g ((edgeMeasure T μ.fst).rnDeriv (μ.fst ⊗ₘ pf) p) ∂nu := by
  rw [db_lift_ratio_eq T μ pf]

/-- **`prop:db_lift`, "in particular"**: `μK₂ = μ` iff `(F, π_→^μ)` is in detailed balance
with respect to `π_←`. -/
theorem bind_edgeLift_eq_self_iff :
    μ.bind (edgeLift T) = μ ↔ DetailedBalance T μ.fst pf := by
  rw [bind_edgeLift, DetailedBalance, Measure.disintegrate μ pf, edgeMeasure, eq_comm]

end DB

/-- **The ratio vanishes to `1` exactly at a fixed point**: for a Markov kernel `K` and a finite
`μ`, `d(μK)/dμ = 1` `μ`-a.e. if and only if `μK = μ`. The `⇐` is `rnDeriv_self`; for `⇒` the
Lebesgue decomposition gives `μK = (μK)_⊥ + μ`, and equal masses kill the singular part. -/
theorem rnDeriv_bind_eq_one_iff {X : Type*} [MeasurableSpace X] (K : Kernel X X)
    [IsMarkovKernel K] (μ : Measure X) [IsFiniteMeasure μ] :
    (μ.bind K).rnDeriv μ =ᵐ[μ] 1 ↔ μ.bind K = μ := by
  constructor
  · intro h
    have hfin : IsFiniteMeasure (μ.bind K) := by
      rw [show μ.bind K = K ∘ₘ μ from rfl]; infer_instance
    have hdec := Measure.singularPart_add_rnDeriv (μ.bind K) μ
    rw [withDensity_congr_ae h, withDensity_one] at hdec
    have huniv : (μ.bind K) Set.univ = μ Set.univ := by
      rw [Measure.bind_apply MeasurableSet.univ K.aemeasurable]
      simp
    have hs : (μ.bind K).singularPart μ Set.univ = 0 := by
      have h2 := congrArg (fun m : Measure X => m Set.univ) hdec
      simp only [Measure.coe_add, Pi.add_apply] at h2
      rw [huniv] at h2
      have hne : μ Set.univ ≠ ⊤ := measure_ne_top _ _
      exact (ENNReal.add_left_inj hne).1 (h2.trans (zero_add _).symm)
    rw [Measure.measure_univ_eq_zero] at hs
    rw [hs, zero_add] at hdec
    exact hdec.symm
  · intro h
    rw [h]
    exact Measure.rnDeriv_self μ

section DBDensity

variable (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam]

/-- **`prop:db_lift`, the proof's route through `λ`-densities**: for `μ ≪ λ₂` finite and `λ`
invariant, `d(μK₂)/dμ (s,s') = (dF/dλ)(s') / (dμ/dλ₂)(s,s')`, `μ`-a.e., with `F = m₁μ`
(`eq:muK2_density` divided by `dμ/dλ₂`). -/
theorem db_lift_ratio_ae (hinv : lam.bind T = lam) (μ : Measure (S × S)) [IsFiniteMeasure μ]
    (hμ : μ ≪ edgeMeasure T lam) :
    (μ.bind (edgeLift T)).rnDeriv μ
      =ᵐ[μ] fun p => μ.fst.rnDeriv lam p.2 / μ.rnDeriv (edgeMeasure T lam) p := by
  have hfin : IsFiniteMeasure (μ.bind (edgeLift T)) := by
    rw [show μ.bind (edgeLift T) = edgeLift T ∘ₘ μ from rfl]; infer_instance
  have h1 := Measure.rnDeriv_eq_div (μ := μ.bind (edgeLift T)) (ν := μ)
    (bind_edgeLift_absolutelyContinuous T lam hinv μ hμ) hμ
  have h2 := hμ.ae_le (rnDeriv_bind_edgeLift T lam hinv μ hμ)
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp1, hp2]

end DBDensity

/-! ### The density actions of `π_←` and `K₂` on `L²`, and the three operators relating them -/

section L2

open GFNBounds.Core

/-- The first marginal of `(f ∘ pr₁)·ρ` is `f·(m₁ρ)`. -/
theorem fst_withDensity_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure (X × Y)) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (ρ.withDensity (fun p => f p.1)).fst = ρ.fst.withDensity f := by
  ext s hs
  rw [Measure.fst_apply hs, withDensity_apply _ (measurable_fst hs), withDensity_apply _ hs,
    Measure.fst, setLIntegral_map hs hf measurable_fst]

variable (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam]

/-- `pr₂ : (𝒮², λ₂) → (𝒮, λ)` is measure-preserving: the second marginal of `λ₂` is `λ`. -/
theorem measurePreserving_snd_edge : MeasurePreserving Prod.snd (edgeMeasure T lam) lam :=
  ⟨measurable_snd, snd_edgeMeasure T lam⟩

/-- `pr₁ : (𝒮², λ₂) → (𝒮, λ)` is measure-preserving under invariance: `m₁λ₂ = λπ_← = λ`. -/
theorem measurePreserving_fst_edge (hinv : lam.bind T = lam) :
    MeasurePreserving Prod.fst (edgeMeasure T lam) lam :=
  ⟨measurable_fst, (fst_edgeMeasure T lam).trans hinv⟩

theorem edgeMeasure_univ : edgeMeasure T lam Set.univ = lam Set.univ := by
  rw [← Measure.snd_univ, snd_edgeMeasure]

/-- An a.e. identity on `(𝒮, λ)` read through `pr₂` on `(𝒮², λ₂)`. -/
theorem ae_comp_snd {u v : S → ℝ} (h : u =ᵐ[lam] v) :
    (fun p : S × S => u p.2) =ᵐ[edgeMeasure T lam] fun p => v p.2 := by
  have h' : u =ᵐ[(edgeMeasure T lam).map Prod.snd] v := by
    show u =ᵐ[(edgeMeasure T lam).snd] v
    rw [snd_edgeMeasure]; exact h
  exact ae_eq_comp measurable_snd.aemeasurable h'

variable (hinv : lam.bind T = lam)
include hinv

/-- `K₂` pushes a density read at the second coordinate to the `π_←`-push read there:
`T₂(f ∘ pr₂) = (T f) ∘ pr₂`, `λ₂`-a.e., for the non-negative density actions `T, T₂`. -/
theorem bindDensity_edge_snd {f : S → ℝ≥0∞} (hf : Measurable f) :
    bindDensity (edgeLift T) (edgeMeasure T lam) (fun p => f p.2)
      =ᵐ[edgeMeasure T lam] fun p => bindDensity T lam f p.2 := by
  have hg : Measurable (bindDensity T lam f) := measurable_bindDensity T lam f
  have hsf : SFinite (edgeMeasure T (lam.withDensity f)) := by
    unfold edgeMeasure; infer_instance
  have e : ((edgeMeasure T lam).withDensity (fun p => f p.2)).bind (edgeLift T)
      = (edgeMeasure T lam).withDensity (fun p => bindDensity T lam f p.2) := by
    rw [← edgeMeasure_withDensity T lam hf, bind_edgeLift, fst_edgeMeasure,
      ← withDensity_bindDensity T hinv f, edgeMeasure_withDensity T lam hg]
  rw [bindDensity, e]
  exact Measure.rnDeriv_withDensity _ (hg.comp measurable_snd)

/-- `K₂` moves a density read at the first coordinate to the second: `T₂(f ∘ pr₁) = f ∘ pr₂`. -/
theorem bindDensity_edge_fst {f : S → ℝ≥0∞} (hf : Measurable f) :
    bindDensity (edgeLift T) (edgeMeasure T lam) (fun p => f p.1)
      =ᵐ[edgeMeasure T lam] fun p => f p.2 := by
  have e : ((edgeMeasure T lam).withDensity (fun p => f p.1)).bind (edgeLift T)
      = (edgeMeasure T lam).withDensity (fun p => f p.2) := by
    rw [bind_edgeLift, fst_withDensity_fst _ hf, fst_edgeMeasure, hinv,
      edgeMeasure_withDensity T lam hf]
  rw [bindDensity, e]
  exact Measure.rnDeriv_withDensity _ (hf.comp measurable_snd)

/-- `eq:muK2_density` for a density: `T₂ f (s,s') = d(m₁(fλ₂))/dλ (s')`, `λ₂`-a.e. -/
theorem bindDensity_edge {f : S × S → ℝ≥0∞} (hfi : ∫⁻ p, f p ∂(edgeMeasure T lam) ≠ ∞) :
    bindDensity (edgeLift T) (edgeMeasure T lam) f
      =ᵐ[edgeMeasure T lam] fun p => ((edgeMeasure T lam).withDensity f).fst.rnDeriv lam p.2 := by
  haveI : IsFiniteMeasure ((edgeMeasure T lam).withDensity f) := isFiniteMeasure_withDensity hfi
  exact rnDeriv_bind_edgeLift T lam hinv _ (withDensity_absolutelyContinuous _ _)

/-- The signed form of `bindDensity_edge_snd`: `P₂(φ ∘ pr₂) = (Pφ) ∘ pr₂`. -/
theorem densityAction_edge_snd {φ : S → ℝ} (hφ : Measurable φ) :
    densityAction (edgeLift T) (edgeMeasure T lam) (fun p => φ p.2)
      =ᵐ[edgeMeasure T lam] fun p => densityAction T lam φ p.2 := by
  have a := bindDensity_edge_snd T lam hinv (f := fun s => ENNReal.ofReal (φ s))
    (ENNReal.measurable_ofReal.comp hφ)
  have b := bindDensity_edge_snd T lam hinv (f := fun s => ENNReal.ofReal (-φ s))
    (ENNReal.measurable_ofReal.comp hφ.neg)
  filter_upwards [a, b] with p ha hb
  simp only [densityAction]
  rw [ha, hb]

/-- The signed form of `bindDensity_edge_fst`: `P₂(φ ∘ pr₁) = φ ∘ pr₂`. -/
theorem densityAction_edge_fst {φ : S → ℝ} (hφ : Measurable φ) :
    densityAction (edgeLift T) (edgeMeasure T lam) (fun p => φ p.1)
      =ᵐ[edgeMeasure T lam] fun p => φ p.2 := by
  have a := bindDensity_edge_fst T lam hinv (f := fun s => ENNReal.ofReal (φ s))
    (ENNReal.measurable_ofReal.comp hφ)
  have b := bindDensity_edge_fst T lam hinv (f := fun s => ENNReal.ofReal (-φ s))
    (ENNReal.measurable_ofReal.comp hφ.neg)
  filter_upwards [a, b] with p ha hb
  simp only [densityAction]
  rw [ha, hb, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', max_zero_sub_eq_self]

/-- **`P₂` factors through the first marginal**: for every `h ∈ L²(λ₂)` there is `φ ∈ L²(λ)`
(the density of `m₁(hλ₂)` against `λ`) with `P₂h = φ ∘ pr₂`, `λ₂`-a.e. -/
theorem densityAction_edge_exists (h : S × S → ℝ) (hh : MemLp h 2 (edgeMeasure T lam)) :
    ∃ φ : S → ℝ, Measurable φ ∧ densityAction (edgeLift T) (edgeMeasure T lam) h
      =ᵐ[edgeMeasure T lam] fun p => φ p.2 := by
  have hint : Integrable h (edgeMeasure T lam) := hh.integrable (by norm_num)
  refine ⟨fun s => (((edgeMeasure T lam).withDensity (fun p => ENNReal.ofReal (h p))).fst.rnDeriv
      lam s).toReal - (((edgeMeasure T lam).withDensity
        (fun p => ENNReal.ofReal (-h p))).fst.rnDeriv lam s).toReal, ?_, ?_⟩
  · exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
      (Measure.measurable_rnDeriv _ _).ennreal_toReal
  · have a := bindDensity_edge T lam hinv (lintegral_ofReal_ne_top hint)
    have b := bindDensity_edge T lam hinv (f := fun p => ENNReal.ofReal (-h p))
      (lintegral_ofReal_ne_top hint.neg)
    filter_upwards [a, b] with p ha hb
    simp only [densityAction]
    rw [ha, hb]

end L2

section Ops

open GFNBounds.Core

variable (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam]

/-- `E φ := φ ∘ pr₂`, a linear isometry `L²(λ) → L²(λ₂)` (the second marginal of `λ₂` is `λ`). -/
noncomputable def liftSnd : Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 (edgeMeasure T lam) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.snd
    (measurePreserving_snd_edge T lam)).toContinuousLinearMap

theorem coeFn_liftSnd (φ : Lp ℝ 2 lam) :
    ⇑(liftSnd T lam φ) =ᵐ[edgeMeasure T lam] fun p => φ p.2 :=
  Lp.coeFn_compMeasurePreserving φ _

theorem norm_liftSnd (φ : Lp ℝ 2 lam) : ‖liftSnd T lam φ‖ = ‖φ‖ :=
  Lp.norm_compMeasurePreserving φ _

theorem adjoint_liftSnd_comp :
    (ContinuousLinearMap.adjoint (liftSnd T lam)).comp (liftSnd T lam) = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (norm_liftSnd T lam)

theorem adjoint_liftSnd_apply (φ : Lp ℝ 2 lam) :
    ContinuousLinearMap.adjoint (liftSnd T lam) (liftSnd T lam φ) = φ := by
  have h := congrArg (fun A : Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 lam => A φ) (adjoint_liftSnd_comp T lam)
  simpa using h

theorem norm_adjoint_liftSnd_le :
    ‖ContinuousLinearMap.adjoint (liftSnd T lam)‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
  rw [norm_liftSnd, one_mul]

theorem liftSnd_constOne :
    liftSnd T lam (constOne lam 2) = constOne (edgeMeasure T lam) 2 := by
  apply Lp.ext
  refine (coeFn_liftSnd T lam _).trans ?_
  refine (ae_comp_snd T lam (coeFn_constOne (ν := lam) (p := 2))).trans ?_
  exact (coeFn_constOne (ν := edgeMeasure T lam) (p := 2)).symm

variable (hinv : lam.bind T = lam)

/-- `D φ := φ ∘ pr₁`, a linear isometry `L²(λ) → L²(λ₂)` under invariance. -/
noncomputable def liftFst : Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 (edgeMeasure T lam) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
    (measurePreserving_fst_edge T lam hinv)).toContinuousLinearMap

theorem coeFn_liftFst (φ : Lp ℝ 2 lam) :
    ⇑(liftFst T lam hinv φ) =ᵐ[edgeMeasure T lam] fun p => φ p.1 :=
  Lp.coeFn_compMeasurePreserving φ _

theorem norm_liftFst (φ : Lp ℝ 2 lam) : ‖liftFst T lam hinv φ‖ = ‖φ‖ :=
  Lp.norm_compMeasurePreserving φ _

/-- `M := E† P₂ : L²(λ₂) → L²(λ)`, which is `h ↦ d(m₁(hλ₂))/dλ` (`liftSnd_edgeMarg`): the
paper's `k_h`, the density of the first marginal of `hλ₂`. -/
noncomputable def edgeMarg : Lp ℝ 2 (edgeMeasure T lam) →L[ℝ] Lp ℝ 2 lam :=
  (ContinuousLinearMap.adjoint (liftSnd T lam)).comp
    (densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv))

/-- **`P₂ E = E P`**: `P₂(φ ∘ pr₂) = (Pφ) ∘ pr₂` on `L²`. -/
theorem densityActionL2_edge_liftSnd (φ : Lp ℝ 2 lam) :
    densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv)
        (liftSnd T lam φ)
      = liftSnd T lam (densityActionL2 T lam hinv φ) := by
  have hφ : Measurable (φ : S → ℝ) := (Lp.stronglyMeasurable φ).measurable
  apply Lp.ext
  have h1 := coeFn_densityActionCLM (edgeLift T) (edgeMeasure T lam) 2
    (edgeMeasure_invariant T lam hinv)
    (isBoundedDensityAction_two (edgeLift T) (edgeMeasure_invariant T lam hinv)) (liftSnd T lam φ)
  rw [densityAction_congr _ _ (coeFn_liftSnd T lam φ)] at h1
  have h2 := coeFn_densityActionCLM T lam 2 hinv (isBoundedDensityAction_two T hinv) φ
  refine h1.trans ((densityAction_edge_snd T lam hinv hφ).trans ?_)
  refine (ae_comp_snd T lam h2.symm).trans ?_
  exact (coeFn_liftSnd T lam _).symm

/-- **`P₂ D = E`**: `P₂(φ ∘ pr₁) = φ ∘ pr₂` on `L²`. -/
theorem densityActionL2_edge_liftFst (φ : Lp ℝ 2 lam) :
    densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv)
        (liftFst T lam hinv φ)
      = liftSnd T lam φ := by
  have hφ : Measurable (φ : S → ℝ) := (Lp.stronglyMeasurable φ).measurable
  apply Lp.ext
  have h1 := coeFn_densityActionCLM (edgeLift T) (edgeMeasure T lam) 2
    (edgeMeasure_invariant T lam hinv)
    (isBoundedDensityAction_two (edgeLift T) (edgeMeasure_invariant T lam hinv))
    (liftFst T lam hinv φ)
  rw [densityAction_congr _ _ (coeFn_liftFst T lam hinv φ)] at h1
  exact h1.trans ((densityAction_edge_fst T lam hinv hφ).trans (coeFn_liftSnd T lam φ).symm)

/-- **`E M = P₂`**: `P₂h = k_h ∘ pr₂` with `k_h = Mh` — `eq:muK2_density` on `L²(λ₂)`. -/
theorem liftSnd_edgeMarg (h : Lp ℝ 2 (edgeMeasure T lam)) :
    liftSnd T lam (edgeMarg T lam hinv h)
      = densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv) h := by
  obtain ⟨φ, hφm, hae⟩ := densityAction_edge_exists T lam hinv h (Lp.memLp h)
  have h1 := coeFn_densityActionCLM (edgeLift T) (edgeMeasure T lam) 2
    (edgeMeasure_invariant T lam hinv)
    (isBoundedDensityAction_two (edgeLift T) (edgeMeasure_invariant T lam hinv)) h
  have hm2 : MemLp (fun p => φ p.2) 2 (edgeMeasure T lam) :=
    (Lp.memLp _).ae_eq (h1.trans hae)
  have hmem : MemLp φ 2 lam := by
    have := (memLp_map_measure_iff hφm.aestronglyMeasurable measurable_snd.aemeasurable).2 hm2
    rwa [show (edgeMeasure T lam).map Prod.snd = lam from snd_edgeMeasure T lam] at this
  have hE : densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv) h
      = liftSnd T lam (hmem.toLp φ) := by
    apply Lp.ext
    refine (h1.trans hae).trans ?_
    refine (ae_comp_snd T lam (MemLp.coeFn_toLp hmem).symm).trans ?_
    exact (coeFn_liftSnd T lam _).symm
  show liftSnd T lam (ContinuousLinearMap.adjoint (liftSnd T lam)
    (densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv) h)) = _
  rw [hE, adjoint_liftSnd_apply]

/-- **`M E = P`**: `k_{φ∘pr₂} = Pφ`. -/
theorem edgeMarg_liftSnd (φ : Lp ℝ 2 lam) :
    edgeMarg T lam hinv (liftSnd T lam φ) = densityActionL2 T lam hinv φ := by
  show ContinuousLinearMap.adjoint (liftSnd T lam)
    (densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv)
      (liftSnd T lam φ)) = _
  rw [densityActionL2_edge_liftSnd, adjoint_liftSnd_apply]

/-- **`M D = 1`**: `k_{φ∘pr₁} = φ`. -/
theorem edgeMarg_liftFst (φ : Lp ℝ 2 lam) :
    edgeMarg T lam hinv (liftFst T lam hinv φ) = φ := by
  show ContinuousLinearMap.adjoint (liftSnd T lam)
    (densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv)
      (liftFst T lam hinv φ)) = _
  rw [densityActionL2_edge_liftFst, adjoint_liftSnd_apply]

/-- **`‖M‖ ≤ 1`**: Jensen for the first-marginal density. -/
theorem norm_edgeMarg_apply_le (h : Lp ℝ 2 (edgeMeasure T lam)) :
    ‖edgeMarg T lam hinv h‖ ≤ ‖h‖ := by
  show ‖ContinuousLinearMap.adjoint (liftSnd T lam)
    (densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv) h)‖ ≤ _
  refine ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_adjoint_liftSnd_le T lam))).trans ?_
  refine ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_densityActionL2_le _ _ _)))

/-- `∫ M h dλ = ∫ h dλ₂`: the first marginal of `hλ₂` has the mass of `hλ₂`. -/
theorem integral_edgeMarg (h : Lp ℝ 2 (edgeMeasure T lam)) :
    ∫ s, edgeMarg T lam hinv h s ∂lam = ∫ p, h p ∂(edgeMeasure T lam) := by
  rw [← inner_constOne_two]
  show inner ℝ (ContinuousLinearMap.adjoint (liftSnd T lam)
    (densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv) h))
      (constOne lam 2) = _
  rw [ContinuousLinearMap.adjoint_inner_left, liftSnd_constOne, inner_constOne_two]
  exact integral_densityActionCLM _ _ 2 _ _ h

/-- **`Π₂ = E Π M`**: the `λ₂`-mean of `h` is the `λ`-mean of `k_h`, read as a constant. -/
theorem meanProj_edge (h : Lp ℝ 2 (edgeMeasure T lam)) :
    meanProj (edgeMeasure T lam) 2 h
      = liftSnd T lam (meanProj lam 2 (edgeMarg T lam hinv h)) := by
  rw [meanProj_apply, meanProj_apply, map_smul, liftSnd_constOne, integral_edgeMarg,
    edgeMeasure_univ]

/-- `P₂^{n+1} = E Pⁿ M`. -/
theorem densityActionL2_edge_pow_succ_apply (n : ℕ) (h : Lp ℝ 2 (edgeMeasure T lam)) :
    (densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv) ^ (n + 1))
        h
      = liftSnd T lam ((densityActionL2 T lam hinv ^ n) (edgeMarg T lam hinv h)) := by
  induction n generalizing h with
  | zero => simp [liftSnd_edgeMarg]
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, ← liftSnd_edgeMarg T lam hinv h,
      edgeMarg_liftSnd, pow_succ, mul_apply_eq_comp]

/-- `(P₂^{n+1} − Π₂) = E (Pⁿ − Π) M`. -/
theorem edge_deviation_apply (n : ℕ) (h : Lp ℝ 2 (edgeMeasure T lam)) :
    (densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv) ^ (n + 1)
        - meanProj (edgeMeasure T lam) 2) h
      = liftSnd T lam ((densityActionL2 T lam hinv ^ n - meanProj lam 2)
          (edgeMarg T lam hinv h)) := by
  rw [sub_apply, sub_apply, map_sub,
    densityActionL2_edge_pow_succ_apply, meanProj_edge]

/-- **`lem:lift_mixing`**, in the form `β̂_{n+1} = β_n` for every `n ≥ 0`: the `L²(λ₂)`
mixing coefficients of the density action of the edge lift `K₂` are those of `π_←`, shifted by
one. `β_n = ‖Pⁿ − Π‖_{L²(λ)}` and `β̂_n = ‖P₂ⁿ − Π₂‖_{L²(λ₂)}` are Mathlib operator norms, `P`,
`P₂` the density actions `φ ↦ d((φλ)π_←)/dλ`, `h ↦ d((hλ₂)K₂)/dλ₂` (`Core.densityActionL2`),
`Π`, `Π₂` the mean projections (`Core.meanProj`). -/
theorem lift_mixing_succ (n : ℕ) :
    Mixing.beta (densityActionL2 (edgeLift T) (edgeMeasure T lam)
        (edgeMeasure_invariant T lam hinv)) (meanProj (edgeMeasure T lam) 2) (n + 1)
      = Mixing.beta (densityActionL2 T lam hinv) (meanProj lam 2) n := by
  unfold Mixing.beta
  set X := densityActionL2 T lam hinv ^ n - meanProj lam 2 with hX
  set Y := densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv)
      ^ (n + 1) - meanProj (edgeMeasure T lam) 2 with hY
  refine le_antisymm ?_ ?_
  · -- `β̂_{n+1} ≤ β_n`: `E` is an isometry and `‖M‖ ≤ 1`
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h => ?_
    rw [hY, edge_deviation_apply, norm_liftSnd]
    exact (X.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_edgeMarg_apply_le T lam hinv h) (norm_nonneg _))
  · -- `β_n ≤ β̂_{n+1}`: test `h = φ ∘ pr₁`, for which `M h = φ` and `‖h‖ = ‖φ‖`
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun φ => ?_
    have e : X φ = X (edgeMarg T lam hinv (liftFst T lam hinv φ)) := by
      rw [edgeMarg_liftFst]
    rw [e, ← norm_liftSnd T lam, ← edge_deviation_apply, ← hY, ← norm_liftFst T lam hinv φ]
    exact Y.le_opNorm _

/-- **`lem:lift_mixing`, verbatim**: `β̂_n = β_{n−1}` for every `n ≥ 1`. -/
theorem lift_mixing_general {n : ℕ} (hn : 1 ≤ n) :
    Mixing.beta (densityActionL2 (edgeLift T) (edgeMeasure T lam)
        (edgeMeasure_invariant T lam hinv)) (meanProj (edgeMeasure T lam) 2) n
      = Mixing.beta (densityActionL2 T lam hinv) (meanProj lam 2) (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa using lift_mixing_succ T lam hinv m

/-- **`lem:lift_coercivity`**: if `‖φ − Πφ‖ ≤ C‖(I − P)φ‖` on `L²(λ)`, then
`‖h − Π₂h‖ ≤ (1 + C)‖(I − P₂)h‖` on `L²(λ₂)`. The paper's proof, on the three operators
`E = · ∘ pr₂`, `M = k_·` and `P`: `v := (I − P₂)h = h − E k_h`, `k_v = (I − P)k_h`,
`h − Π₂h = v + E(k_h − Πk_h)`. -/
theorem lift_coercivity_general {C : ℝ} (hC : 0 ≤ C)
    (hcoer : ∀ φ : Lp ℝ 2 lam,
      ‖φ - meanProj lam 2 φ‖ ≤ C * ‖(1 - densityActionL2 T lam hinv) φ‖)
    (h : Lp ℝ 2 (edgeMeasure T lam)) :
    ‖h - meanProj (edgeMeasure T lam) 2 h‖
      ≤ (1 + C) * ‖(1 - densityActionL2 (edgeLift T) (edgeMeasure T lam)
          (edgeMeasure_invariant T lam hinv)) h‖ := by
  set P := densityActionL2 T lam hinv
  set P₂ := densityActionL2 (edgeLift T) (edgeMeasure T lam) (edgeMeasure_invariant T lam hinv)
  set E := liftSnd T lam
  set M := edgeMarg T lam hinv
  set k := M h
  set v := (1 - P₂) h with hv
  have hv' : v = h - E k := by
    rw [hv, sub_apply, one_apply_eq_self, liftSnd_edgeMarg]
  have hkv : M v = (1 - P) k := by
    rw [hv', map_sub, edgeMarg_liftSnd, sub_apply,
      one_apply_eq_self]
  have hsplit : h - meanProj (edgeMeasure T lam) 2 h = v + E (k - meanProj lam 2 k) := by
    rw [meanProj_edge T lam hinv h, hv', map_sub]
    abel
  rw [hsplit]
  calc ‖v + E (k - meanProj lam 2 k)‖ ≤ ‖v‖ + ‖E (k - meanProj lam 2 k)‖ := norm_add_le _ _
    _ = ‖v‖ + ‖k - meanProj lam 2 k‖ := by rw [norm_liftSnd]
    _ ≤ ‖v‖ + C * ‖(1 - P) k‖ := by gcongr; exact hcoer k
    _ = ‖v‖ + C * ‖M v‖ := by rw [hkv]
    _ ≤ ‖v‖ + C * ‖v‖ := by gcongr; exact norm_edgeMarg_apply_le T lam hinv v
    _ = (1 + C) * ‖v‖ := by ring

/-- **The remark after `lem:lift_coercivity`, the mixing half**: the edge-lifted mixing sum is
summable exactly when `π_←`'s is, and then `B̂₂ = β̂₀ + B`, with `β̂₀ = ‖I − Π₂‖ ≤ 1`. -/
theorem lift_mixing_summable_iff :
    Summable (Mixing.beta (densityActionL2 (edgeLift T) (edgeMeasure T lam)
        (edgeMeasure_invariant T lam hinv)) (meanProj (edgeMeasure T lam) 2))
      ↔ Summable (Mixing.beta (densityActionL2 T lam hinv) (meanProj lam 2)) := by
  rw [← summable_nat_add_iff 1]
  simp only [lift_mixing_succ T lam hinv]

theorem lift_mixing_B
    (hsum : Summable (Mixing.beta (densityActionL2 T lam hinv) (meanProj lam 2))) :
    Mixing.B (densityActionL2 (edgeLift T) (edgeMeasure T lam)
        (edgeMeasure_invariant T lam hinv)) (meanProj (edgeMeasure T lam) 2)
      = Mixing.beta (densityActionL2 (edgeLift T) (edgeMeasure T lam)
          (edgeMeasure_invariant T lam hinv)) (meanProj (edgeMeasure T lam) 2) 0
        + Mixing.B (densityActionL2 T lam hinv) (meanProj lam 2) := by
  unfold Mixing.B
  rw [((lift_mixing_summable_iff T lam hinv).2 hsum).tsum_eq_zero_add]
  simp only [lift_mixing_succ T lam hinv]

theorem lift_beta_zero_le_one :
    Mixing.beta (densityActionL2 (edgeLift T) (edgeMeasure T lam)
        (edgeMeasure_invariant T lam hinv)) (meanProj (edgeMeasure T lam) 2) 0 ≤ 1 := by
  rw [Mixing.beta_zero]; exact norm_one_sub_meanProj_le

/-- **The remark after `lem:lift_coercivity`, "which is also the value of the edge-lifted
mixing sum"**: `B̂₂ = 1 + B` as soon as `λ` charges a measurable `X` with `0 < λ(X) < λ(𝒮)`
(then `λ₂` charges `𝒮 × X` the same way and `β̂₀ = 1`). Without such an `X` (on a Polish `𝒮`:
`λ` a multiple of a Dirac mass) `L²(λ₂)` has dimension at most one, `β̂₀ = 0` and the sentence
fails (not formalized); `lift_mixing_B` is the general form. -/
theorem lift_mixing_B_eq_one_add
    (hsum : Summable (Mixing.beta (densityActionL2 T lam hinv) (meanProj lam 2)))
    {X : Set S} (hX : MeasurableSet X) (hX0 : 0 < lam X) (hX1 : lam X < lam Set.univ) :
    Mixing.B (densityActionL2 (edgeLift T) (edgeMeasure T lam)
        (edgeMeasure_invariant T lam hinv)) (meanProj (edgeMeasure T lam) 2)
      = 1 + Mixing.B (densityActionL2 T lam hinv) (meanProj lam 2) := by
  have hpre : edgeMeasure T lam (Prod.snd ⁻¹' X) = lam X :=
    (measurePreserving_snd_edge T lam).measure_preimage hX.nullMeasurableSet
  rw [lift_mixing_B T lam hinv hsum,
    sigma_mixing_beta_zero_of_set (edgeLift T) (edgeMeasure T lam)
      (edgeMeasure_invariant T lam hinv) (measurable_snd hX) (by rwa [hpre])
      (by rwa [hpre, edgeMeasure_univ])]

/-- **The remark after `lem:lift_coercivity`, the coercivity half**: under summable mixing of
`π_←`, the constant `C = B = ∑ β_n` of `lem:sigma_mixing` lifts to `1 + B` for `K₂`. -/
theorem lift_coercivity_of_mixing
    (hsum : Summable (Mixing.beta (densityActionL2 T lam hinv) (meanProj lam 2)))
    (h : Lp ℝ 2 (edgeMeasure T lam)) :
    ‖h - meanProj (edgeMeasure T lam) 2 h‖
      ≤ (1 + Mixing.B (densityActionL2 T lam hinv) (meanProj lam 2))
        * ‖(1 - densityActionL2 (edgeLift T) (edgeMeasure T lam)
          (edgeMeasure_invariant T lam hinv)) h‖ :=
  lift_coercivity_general T lam hinv (Mixing.B_nonneg _ _)
    (sigma_mixing T lam hinv hsum).2.2 h

end Ops

/-! ### The three statements, assembled -/

/-- **`prop:db_lift`** on a standard Borel `𝒮`, for every finite edge flow `μ` on `𝒮²`, with
`F := m₁μ` and `π_→^μ := μ.condKernel` the disintegration `μ = F ⊗ π_→^μ`:
*(i)* the lifted ratio `d(μK₂)/dμ` **is** the detailed-balance ratio
`F(ds')π_←(s'→ds) / F(ds)π_→^μ(s→ds')` (as functions, not only a.e.), so the two losses agree for
every `g` and every training distribution `ν̂`;
*(ii)* `μK₂ = μ` iff `(F, π_→^μ)` is in detailed balance with respect to `π_←`;
*(iii)* the ratio is `1` `μ`-a.e. iff `μK₂ = μ` (the proof's last sentence). -/
theorem db_lift [StandardBorelSpace S] [Nonempty S] (T : Kernel S S) [IsMarkovKernel T]
    (μ : Measure (S × S)) [IsFiniteMeasure μ] :
    μ.fst ⊗ₘ μ.condKernel = μ ∧
    (μ.bind (edgeLift T)).rnDeriv μ
      = (edgeMeasure T μ.fst).rnDeriv (μ.fst ⊗ₘ μ.condKernel) ∧
    (∀ (g : ℝ≥0∞ → ℝ) (nu : Measure (S × S)),
      ∫ p, g ((μ.bind (edgeLift T)).rnDeriv μ p) ∂nu
        = ∫ p, g ((edgeMeasure T μ.fst).rnDeriv (μ.fst ⊗ₘ μ.condKernel) p) ∂nu) ∧
    (μ.bind (edgeLift T) = μ ↔ DetailedBalance T μ.fst μ.condKernel) ∧
    ((μ.bind (edgeLift T)).rnDeriv μ =ᵐ[μ] 1 ↔ μ.bind (edgeLift T) = μ) :=
  ⟨Measure.disintegrate μ μ.condKernel, db_lift_ratio_eq T μ _, db_lift_loss_eq T μ _,
    bind_edgeLift_eq_self_iff T μ _, rnDeriv_bind_eq_one_iff _ μ⟩

/-- **Non-vacuity** (kb `0025`, `0027`): the hypotheses of the `L²` statements — `π_←` Markov,
`λ` finite and `π_←`-invariant — are met on every measurable space by the resampling kernel
`x ↦ ρ` and any probability `ρ`, so `lift_mixing_general` and `lift_coercivity_general` are not
vacuous. -/
theorem lift_hypotheses_inhabited (ρ : Measure S) [IsProbabilityMeasure ρ] :
    ρ.bind (Kernel.const S ρ) = ρ :=
  (isReversal_const ρ).2

/-- **Non-vacuity of `lem:lift_coercivity`'s hypothesis**: for the resampling kernel `x ↦ ρ`
the density action is `Π` (`Core.Family.densityActionCLM_const_kernel`), so the hypothesis holds
with `C = 1` and `lift_coercivity_general` gives the edge-lift bound with `1 + C = 2` — the
general-space twin of `Balance.lift_coercivity_twoState`. -/
theorem lift_coercivity_const (ρ : Measure S) [IsProbabilityMeasure ρ] :
    (∀ φ : Lp ℝ 2 ρ, ‖φ - GFNBounds.Core.meanProj ρ 2 φ‖
      ≤ 1 * ‖(1 - GFNBounds.Core.densityActionL2 (Kernel.const S ρ) ρ
          (lift_hypotheses_inhabited ρ)) φ‖) ∧
    ∀ h : Lp ℝ 2 (edgeMeasure (Kernel.const S ρ) ρ),
      ‖h - GFNBounds.Core.meanProj (edgeMeasure (Kernel.const S ρ) ρ) 2 h‖
        ≤ (1 + 1) * ‖(1 - GFNBounds.Core.densityActionL2 (edgeLift (Kernel.const S ρ))
            (edgeMeasure (Kernel.const S ρ) ρ)
            (edgeMeasure_invariant _ ρ (lift_hypotheses_inhabited ρ))) h‖ := by
  have hP : GFNBounds.Core.densityActionL2 (Kernel.const S ρ) ρ (lift_hypotheses_inhabited ρ)
      = GFNBounds.Core.meanProj ρ 2 :=
    GFNBounds.Core.Family.densityActionCLM_const_kernel
  have hc : ∀ φ : Lp ℝ 2 ρ, ‖φ - GFNBounds.Core.meanProj ρ 2 φ‖
      ≤ 1 * ‖(1 - GFNBounds.Core.densityActionL2 (Kernel.const S ρ) ρ
          (lift_hypotheses_inhabited ρ)) φ‖ := by
    intro φ
    rw [hP, one_mul, sub_apply, one_apply_eq_self]
  exact ⟨hc, lift_coercivity_general _ ρ _ zero_le_one hc⟩

end GFNBounds.Balance.LiftGeneral
