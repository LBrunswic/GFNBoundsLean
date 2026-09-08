import GFNBounds.Core.UniversalityLp

/-!
# The mean projection, and the two identities `Core.Mixing` assumes

**`theo:universality_L2_full`** — statement `proofs.tex:65–74`, proof `proofs.tex:76–115`
(Theorem 15 of the ICLR build), Steps 1 (`:87–98`) and 2 (`:100`) — together with the notation
paragraph `proofs.tex:22` that says what `Π` *is*:

> `Π` denotes the mean projection onto the invariant functions of the kernel in play,
> `f ↦ (∫ f dρ / ρ(𝒮)) 𝟏` against that kernel's invariant measure `ρ`.

> *Step 1.* Using `Π P⋆ = P⋆ Π = Π`, its partial sums telescope […]. Now `F_init` and `F_term`
> are both probability distributions, so `∫ θ dν_B = 0`, that is `Π θ = 0` (`proofs.tex:87, 95`).

> *Step 2: a `0`-flow restores non-negativity.* […] Invariance supplies the missing freedom:
> `ν_B π⋆ = ν_B` gives `(Id − P⋆) 𝟏 = 0` — the constants are `0`-flows […] — and `𝟏 ∈ L^p(ν_B)`
> because `ν_B` is finite (`proofs.tex:100`).

`Core.Mixing`, `Core.Universality` and `Core.UniversalityLp` prove weak `L^p`-universality for
`p ≠ ∞` from three hypotheses that the paper does not hypothesize but *derives*:

    Mixing P Pi   (that is, `Pi * P = Pi`, `P * Pi = Pi`, and summability)
    P 𝟏 = 𝟏
    Pi θ = 0

`Core/Mixing.lean`'s docstring names the missing layer `Core.Flow` and records that it does not
exist. This file is that layer, less one storey: it **constructs** `Π` as the mean projection of
`proofs.tex:22` and **derives** the two intertwining identities and `Π θ = 0` from two conditions
on `P` that are properties of a Markov kernel and of an invariant measure —

* `hint : ∀ f, ∫ (P f) dν = ∫ f dν`, mass preservation. For `P⋆ f = d((f ν_B) π⋆)/dν_B` this is
  `(f ν_B) π⋆ (𝒮) = f ν_B (𝒮)`, which holds because each `π⋆(x)` is a *probability* measure —
  it is stochasticity of the kernel, not invariance of the measure;
* `hone : P 𝟏 = 𝟏`, the paper's `(Id − P⋆) 𝟏 = 0`, which is `ν_B π⋆ = ν_B`: it is invariance,
  and it is the hypothesis `Core.Universality` already carries under the same name.

What remains missing is the storey below: `P` is a hypothesised bounded operator here, not the
density action of a kernel. See SCOPE.

## What is proved

| | |
|---|---|
| `integralCLM` | `f ↦ ∫ f dν` as a `ContinuousLinearMap` on `L^p(ν)`, `ν` finite |
| `meanProj` | `Π f = (∫ f dν / ν(𝒮)) • 𝟏`, the projection of `proofs.tex:22`, as a `ContinuousLinearMap` |
| `meanProj_comp_left` / `comp_meanProj` | `Π P = Π` from `hint`; `P Π = Π` from `hone` — `Mixing.proj_left` / `Mixing.proj_right` |
| `meanProj_sub_eq_zero` | `Π (f_term − f_init) = 0` for equal masses |
| `mixing_of_massPreserving` | the `Mixing P (meanProj ν p)` bundle, from `hone`, `hint` and summability |
| `weaklyUniversal_of_massPreserving` | the payoff, on `hone`/`hint`/summability instead of on a bare `Mixing` |
| `eq_meanProj_of_invariant` | the converse guard: under summable mixing *against the mean projection*, every `P`-invariant density is constant |

## The constant, explicitly

`integralCLM` is built with the bound `|∫ f dν| ≤ ν(𝒮)^{1 − 1/p} ‖f‖_{L^p(ν)}`, which is Hölder
against `𝟏`: the constant is `‖𝟏‖_{L^{p*}(ν)} = ν(𝒮)^{1/p*}`, and it is sharp, attained at
`f = 𝟏`. At `p = ∞` the exponent reads `1 − 1/0 = 1` under `ENNReal.toReal ∞ = 0`, giving
`|∫ f| ≤ ν(𝒮) ‖f‖_∞`, which is again right.

## SCOPE (disclosed)

**The kernel-to-operator passage is still missing, and `hone`/`hint` are its consequences, not
its replacement.** Constructing `P⋆ f := d((f ν) π⋆)/dν` from a Markov kernel `π⋆` — showing the
image measure is `ν`-dominated, that the Radon–Nikodym derivative is linear in `f`, and that it
is bounded on `L^p(ν)` — is a further layer, and this file does not attempt it. `P` here is a
hypothesised bounded operator on `L^p(ν)`, and `hone`, `hint` are hypotheses about it. What the
file removes from `Core.Mixing`'s debt is the *upper* half: given those two, `Π P = P Π = Π` is
no longer assumed. This is `CLAUDE.md`'s obstruction 2 and it is not closed.

**`Π` is the mean projection by definition, and the paper's `Π` only when `P` is ergodic.** The
paper's `Π` is the projection onto the invariant densities; it *equals* the mean projection
because `π⋆` is ergodic, so that the only invariant densities are the multiples of `𝟏`. Nothing
below proves that `meanProj` projects onto `ker (Id − P)`, and for a non-ergodic `P` it does not:
the mean projection is then still a legitimate `Pi` for the `Mixing` bundle — the identities
`Π P = P Π = Π` hold from `hint` and `hone` alone — but it is not the paper's `Π`, and
`Mixing P (meanProj ν p)` is then *unsatisfiable* rather than weaker, its summability half
already failing. The ergodicity content has not been deleted; it has moved into summability, and
`eq_meanProj_of_invariant` is where that is made precise: if `n ↦ ‖P^n − Π‖` is summable with
`Π` the mean projection, then every `P`-invariant element of `L^p(ν)` is a.e. constant. So the
bundle assembled here is honest — no `P` carrying a non-constant invariant density satisfies
it — but the burden
sits on the summability hypothesis, which this file supplies no criterion for.

**Nothing is claimed about when summable mixing holds.** `mixing_of_massPreserving` takes it as a
hypothesis, exactly as `Core.Mixing` does. The paper hypothesizes it too
(`theo:universality_L2_full`: "ergodic with summable `L^p`-mixing coefficients"), so no fidelity
is lost here; but the derivation this file performs is of the *two identities* only.

**`ν(𝒮) ≠ 0` is an explicit hypothesis, not an instance.** It is carried as `hν : ν Set.univ ≠ 0`
on the two statements that need it — idempotence of `Π` and `Π 𝟏 = 𝟏`. It is deliberately *not*
a `[NeZero (ν Set.univ)]` instance argument on `meanProj`: the definition is meaningful without
it (`ν = 0` makes `L^p(ν)` trivial and `Π = 0 = Id`), and the two intertwining identities,
`Π θ = 0`, and the universality payoff are all proved without it.

**Equal mass is read off the integrals, not off the measures.** `meanProj_sub_eq_zero` takes
`∫ f_init dν = ∫ f_term dν`, which is what the paper's "both are probability distributions"
delivers and all that Step 1 consumes. That `F_init`, `F_term` are non-negative is not used and
not required.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` a measured Polish space, `ν_B` finite | ⚠ weakened: any `MeasurableSpace α` with `[IsFiniteMeasure ν]`; Polish is not used |
| `π⋆` a Markov kernel with finite `L^p(ν_B) → L^p(ν_B)` operator norm | ⚠ weakened: a bounded operator `P` on `Lp ℝ p ν`; the kernel is not the primitive |
| `π⋆` stochastic, hence the density action preserves mass | ⚠ **assumed** as `hint : ∀ f, ∫ (P f) dν = ∫ f dν` |
| `ν_B π⋆ = ν_B`, hence `(Id − P⋆) 𝟏 = 0` | ⚠ **assumed** as `hone : P 𝟏 = 𝟏` |
| `Π` the mean projection onto the invariant densities (`proofs.tex:22`) | ✓ **constructed** as `meanProj`, `f ↦ (∫ f dν / ν(𝒮)) • 𝟏` |
| `Π P⋆ = P⋆ Π = Π` | ✓ **derived** from `hint` and `hone` — no longer assumed |
| `Π θ = 0` from equal total mass | ✓ **derived**, from `∫ f_init dν = ∫ f_term dν` |
| `π⋆` ergodic | ⚠ not assumed and not used; its role is discussed in SCOPE, and `eq_meanProj_of_invariant` shows summable mixing against `meanProj` already forces it |
| summable `L^p`-mixing coefficients `β_n = ‖P^n − Π‖` | ⚠ **assumed**, now with `Π` pinned to the paper's mean projection rather than to an arbitrary `Pi` |
| `p < +∞` | ✓ carried, as `hp : p ≠ ⊤`; `1 ≤ p` as `[Fact (1 ≤ p)]` |
| conclusion: `Θ = {π⋆} × L^p_+(ν_B)` weakly `L^p`-universal | ✓ `weaklyUniversal_of_massPreserving` |
| conclusion: strong universality at `p = +∞` | ✗ not carried — as in `Core.UniversalityLp` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open MeasureTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ## The mean functional `f ↦ ∫ f dν` -/

/-- An element of `L^p(ν)` is `ν`-integrable: `ν` is finite and `1 ≤ p`, so `L^p(ν) ⊆ L^1(ν)`.
This is what lets the appendix write `∫ θ dν_B` for `θ ∈ L^p(ν_B)` at all. -/
theorem integrable_of_Lp (f : Lp ℝ p ν) : Integrable (⇑f) ν :=
  (Lp.memLp f).integrable (Fact.out : (1 : ℝ≥0∞) ≤ p)

/-- The mean functional `f ↦ ∫ f dν`, as a linear map on `L^p(ν)`. -/
noncomputable def integralLM (ν : Measure α) (p : ℝ≥0∞) [IsFiniteMeasure ν] [Fact (1 ≤ p)] :
    Lp ℝ p ν →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂ν
  map_add' f g := by
    have h := integral_congr_ae (Lp.coeFn_add f g)
    simp only [_root_.Pi.add_apply] at h
    rw [h]
    exact integral_add (integrable_of_Lp f) (integrable_of_Lp g)
  map_smul' c f := by
    have h := integral_congr_ae (Lp.coeFn_smul c f)
    simp only [_root_.Pi.smul_apply, smul_eq_mul] at h
    rw [h, integral_const_mul]
    simp

/-- **Hölder against `𝟏`**: `|∫ f dν| ≤ ν(𝒮)^{1 − 1/p} ‖f‖_{L^p(ν)}`.

The constant is `‖𝟏‖_{L^{p*}(ν)}`, and it is what makes the mean functional continuous. At
`p = ∞` the exponent is `1` and the bound reads `|∫ f| ≤ ν(𝒮) ‖f‖_∞`. -/
theorem norm_integral_le_holder (f : Lp ℝ p ν) :
    ‖∫ x, f x ∂ν‖ ≤ (ν Set.univ).toReal ^ (1 - 1 / p.toReal) * ‖f‖ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmeas : AEStronglyMeasurable (⇑f) ν := Lp.aestronglyMeasurable f
  -- The exponent `1 − 1/p` is non-negative for every `p ∈ [1, ∞]`.
  have hexp : 0 ≤ 1 - 1 / p.toReal := by
    rcases eq_or_ne p ⊤ with rfl | hpt
    · simp
    · have h1 : (1 : ℝ) ≤ p.toReal := by
        simpa using ENNReal.toReal_mono hpt hp1
      rw [sub_nonneg, div_le_one (lt_of_lt_of_le zero_lt_one h1)]
      exact h1
  -- `|∫ f| ≤ ∫ |f| = ‖f‖₁`.
  have h1 : ‖∫ x, f x ∂ν‖ ≤ ∫ x, ‖f x‖ ∂ν := norm_integral_le_integral_norm _
  have h2 : ∫ x, ‖f x‖ ∂ν = (eLpNorm (⇑f) 1 ν).toReal := by
    rw [integral_norm_eq_lintegral_enorm hmeas, eLpNorm_one_eq_lintegral_enorm]
  -- `‖f‖₁ ≤ ‖f‖_p ν(𝒮)^{1 − 1/p}`, in `ℝ≥0∞`.
  have h3 : eLpNorm (⇑f) 1 ν ≤ eLpNorm (⇑f) p ν * ν Set.univ ^ (1 - 1 / p.toReal) := by
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (f := ⇑f) hp1 hmeas
    simpa using this
  have hne : eLpNorm (⇑f) p ν * ν Set.univ ^ (1 - 1 / p.toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top ν Set.univ))
  have h4 : (eLpNorm (⇑f) 1 ν).toReal
      ≤ (ν Set.univ).toReal ^ (1 - 1 / p.toReal) * ‖f‖ := by
    refine (ENNReal.toReal_mono hne h3).trans_eq ?_
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Lp.norm_def, mul_comm]
  exact h1.trans (h2.trans_le h4)

/-- The mean functional `f ↦ ∫ f dν` as a **continuous** linear map on `L^p(ν)`, with the
explicit operator-norm bound `ν(𝒮)^{1 − 1/p}` of `norm_integral_le_holder`. -/
noncomputable def integralCLM (ν : Measure α) (p : ℝ≥0∞) [IsFiniteMeasure ν] [Fact (1 ≤ p)] :
    Lp ℝ p ν →L[ℝ] ℝ :=
  (integralLM ν p).mkContinuous ((ν Set.univ).toReal ^ (1 - 1 / p.toReal))
    norm_integral_le_holder

@[simp]
theorem integralCLM_apply (f : Lp ℝ p ν) : integralCLM ν p f = ∫ x, f x ∂ν := rfl

/-- `‖∫ · dν‖ ≤ ν(𝒮)^{1 − 1/p}`: the constant of `norm_integral_le_holder` bounds the operator
norm, which is rule 3's explicit formula rather than a bare existential. -/
theorem norm_integralCLM_le :
    ‖integralCLM ν p‖ ≤ (ν Set.univ).toReal ^ (1 - 1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg ENNReal.toReal_nonneg _) _

omit [Fact (1 ≤ p)] in
/-- `∫ 𝟏 dν = ν(𝒮)`. -/
theorem integral_constOne : ∫ x, (constOne ν p) x ∂ν = (ν Set.univ).toReal := by
  rw [integral_congr_ae (coeFn_constOne (ν := ν) (p := p))]
  simp [measureReal_def]

/-! ## The mean projection `Π` -/

/-- **The mean projection of `proofs.tex:22`**, `Π f = (∫ f dν / ν(𝒮)) • 𝟏`, as a continuous
linear map on `L^p(ν)`.

This is the `Pi` that `Core.Mixing`, `Core.Universality` and `Core.UniversalityLp` carry as a
hypothesis. It is the paper's `Π` — the projection onto the *invariant* densities — exactly when
the policy is ergodic; see this file's SCOPE. -/
noncomputable def meanProj (ν : Measure α) (p : ℝ≥0∞) [IsFiniteMeasure ν] [Fact (1 ≤ p)] :
    Lp ℝ p ν →L[ℝ] Lp ℝ p ν :=
  ((ν Set.univ).toReal⁻¹ • integralCLM ν p).smulRight (constOne ν p)

theorem meanProj_apply (f : Lp ℝ p ν) :
    meanProj ν p f = ((∫ x, f x ∂ν) / (ν Set.univ).toReal) • constOne ν p := by
  simp [meanProj, div_eq_inv_mul]

/-- `Π 𝟏 = 𝟏`: the constants are fixed by the mean projection. -/
theorem meanProj_constOne (hν : ν Set.univ ≠ 0) :
    meanProj ν p (constOne ν p) = constOne ν p := by
  rw [meanProj_apply, integral_constOne,
    div_self (ENNReal.toReal_ne_zero.2 ⟨hν, measure_ne_top ν Set.univ⟩), one_smul]

/-- `Π` is idempotent — it is a projection. `Core.Mixing` does not assume this (it derives
`Pi * Pi = Pi` from summability); here it is immediate from `∫ 𝟏 dν = ν(𝒮)`. -/
theorem meanProj_idem (hν : ν Set.univ ≠ 0) :
    meanProj ν p * meanProj ν p = meanProj ν p := by
  refine ContinuousLinearMap.ext fun f => ?_
  show meanProj ν p (meanProj ν p f) = meanProj ν p f
  rw [meanProj_apply f, map_smul, meanProj_constOne hν, ← meanProj_apply]

/-! ## The two intertwining identities, and `Π θ = 0` -/

variable {P : Lp ℝ p ν →L[ℝ] Lp ℝ p ν}

/-- **`Mixing.proj_left`, derived**: `Π P = Π`, from mass preservation alone.

The paper's `Π P⋆ = Π` (`proofs.tex:87`): the density action of a Markov kernel preserves
`ν_B`-integrals, so it does not move the mean, and the mean is all `Π` reads. -/
theorem meanProj_comp_left (hint : ∀ f : Lp ℝ p ν, ∫ x, (P f) x ∂ν = ∫ x, f x ∂ν) :
    meanProj ν p * P = meanProj ν p := by
  refine ContinuousLinearMap.ext fun f => ?_
  show meanProj ν p (P f) = meanProj ν p f
  rw [meanProj_apply, meanProj_apply, hint f]

/-- **`Mixing.proj_right`, derived**: `P Π = Π`, from `P 𝟏 = 𝟏` and linearity.

The paper's `P⋆ Π = Π` (`proofs.tex:87`): `Π` lands in the constants, and invariance of `ν_B`
fixes the constants — "the constants are `0`-flows" (`proofs.tex:100`). -/
theorem comp_meanProj (hone : P (constOne ν p) = constOne ν p) :
    P * meanProj ν p = meanProj ν p := by
  refine ContinuousLinearMap.ext fun f => ?_
  show P (meanProj ν p f) = meanProj ν p f
  rw [meanProj_apply, map_smul, hone]

/-- **`Π θ = 0` for a pair of equal total mass** — the paper's "`F_init` and `F_term` are both
probability distributions, so `∫ θ dν_B = 0`, that is `Π θ = 0`" (`proofs.tex:95`).

Only the equality of the two integrals is used; non-negativity of the densities is not. -/
theorem meanProj_sub_eq_zero {f_init f_term : Lp ℝ p ν}
    (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    meanProj ν p (f_term - f_init) = 0 := by
  have h : ∫ x, (f_term - f_init) x ∂ν = 0 := by
    have := map_sub (integralCLM ν p) f_term f_init
    simp only [integralCLM_apply] at this
    rw [this, hmass, sub_self]
  rw [meanProj_apply, h, zero_div, zero_smul]

/-! ## Assembly: the universality payoff on `hone` and `hint` -/

/-- **The `Mixing` bundle, with only its summability half assumed.** `Core.Mixing` hypothesizes
`Pi * P = Pi` and `P * Pi = Pi`; here they are the two theorems above, and `Pi` is pinned to the
paper's mean projection rather than left arbitrary. What remains a hypothesis is the summability
of `β_n = ‖P^n − Π‖`, which the paper hypothesizes too. -/
theorem mixing_of_massPreserving (hone : P (constOne ν p) = constOne ν p)
    (hint : ∀ f : Lp ℝ p ν, ∫ x, (P f) x ∂ν = ∫ x, f x ∂ν)
    (hsum : Summable fun n : ℕ => ‖P ^ n - meanProj ν p‖) :
    Mixing P (meanProj ν p) where
  proj_left := meanProj_comp_left hint
  proj_right := comp_meanProj hone
  summable := hsum

/-- **`theo:universality_L2_full` at `p < ∞`, on the paper's own hypotheses about `P`.**

This is `Core.UniversalityLp.weaklyUniversal_Lp` with `Mixing P Pi` replaced by what the paper
derives it from: `P` fixes the constants (`ν_B π⋆ = ν_B`), `P` preserves `ν_B`-integrals
(`π⋆` is a Markov kernel), and the mixing coefficients against the mean projection are summable.
`Π` is no longer a hypothesis at all — it is `meanProj`.

What is still assumed, and is the whole of the remaining debt: that `P` is a bounded operator on
`L^p(ν)` with those two properties, rather than the density action of a Markov kernel `π⋆`
constructed from it. See SCOPE. -/
theorem weaklyUniversal_of_massPreserving (hone : P (constOne ν p) = constOne ν p)
    (hint : ∀ f : Lp ℝ p ν, ∫ x, (P f) x ∂ν = ∫ x, f x ∂ν)
    (hsum : Summable fun n : ℕ => ‖P ^ n - meanProj ν p‖) (hp : p ≠ ⊤) :
    WeaklyUniversal P (meanProj ν p) :=
  weaklyUniversal_Lp (mixing_of_massPreserving hone hint hsum) hone hp

/-- **The same, at one admissible pair**, in the paper's own terms: two densities in `L^p(ν)` of
equal total mass are joined to arbitrary accuracy by a non-negative outflow. -/
theorem weaklyUniversalAt_of_equalMass (hone : P (constOne ν p) = constOne ν p)
    (hint : ∀ f : Lp ℝ p ν, ∫ x, (P f) x ∂ν = ∫ x, f x ∂ν)
    (hsum : Summable fun n : ℕ => ‖P ^ n - meanProj ν p‖) (hp : p ≠ ⊤)
    {f_init f_term : Lp ℝ p ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    WeaklyUniversalAt P (f_term - f_init) :=
  weaklyUniversal_of_massPreserving hone hint hsum hp _ (meanProj_sub_eq_zero hmass)

/-- **Summable mixing against the mean projection is an ergodicity hypothesis.**

The paper's `Π` is the projection onto the invariant densities and coincides with the mean
projection because `π⋆` is ergodic. `meanProj` is the mean projection by construction, so nothing
above proves it projects onto `ker (Id − P)` — but nothing above needs to: as soon as
`n ↦ ‖P^n − Π‖` is summable with `Π` the *mean* projection, every `P`-invariant element of
`L^p(ν)` is its own mean, hence a multiple of `𝟏`. The ergodicity has moved into the summability
hypothesis rather than disappeared, which is what this file's SCOPE records. -/
theorem eq_meanProj_of_invariant (h : Mixing P (meanProj ν p)) {g : Lp ℝ p ν} (hg : P g = g) :
    g = ((∫ x, g x ∂ν) / (ν Set.univ).toReal) • constOne ν p := by
  have hpow : ∀ n : ℕ, (P ^ n) g = g := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        hg, ih]
  have hle : ∀ n : ℕ, ‖g - meanProj ν p g‖ ≤ ‖P ^ n - meanProj ν p‖ * ‖g‖ := by
    intro n
    have := (P ^ n - meanProj ν p).le_opNorm g
    rwa [sub_apply, hpow n] at this
  have hzero : Tendsto (fun n : ℕ => ‖P ^ n - meanProj ν p‖ * ‖g‖) atTop (𝓝 0) := by
    simpa using h.summable.tendsto_atTop_zero.mul_const ‖g‖
  have : ‖g - meanProj ν p g‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hzero hle
  have hg0 : g - meanProj ν p g = 0 := by
    simpa using le_antisymm this (norm_nonneg _)
  rw [← meanProj_apply, ← sub_eq_zero]
  exact hg0

end GFNBounds.Core
