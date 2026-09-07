import GFNBounds.Doubling.Adjoint
import GFNBounds.Doubling.Unsolvable

/-!
# `P⋆ = P*` on `L²(λ)`, and `‖P⋆ⁿ − Π‖ = β̂ₙ`

**`lem:doubling_operator`(1), the adjoint clause and its corollary** — `app_doubling.tex:166–262`.

> let `P` be its density action `Pu := d((uλ)T)/dλ` and `P⋆` its function action
> `(P⋆v)(x) := ∫v dT(x,·)`, let `Π` be the `λ`-mean projection, let `β̂ₙ := ‖Pⁿ − Π‖_{L²(λ)}` […]
> Then: *(1)* `P⋆` is a contraction of `L^p(λ)` for every `p ∈ [1,+∞]` **and is the `L²(λ)`-adjoint
> of `P`, so that `‖P⋆ⁿ − Π‖_{L²(λ)} = β̂ₙ` for every `n ≥ 0`**.

The paper's last two sentences of *(1)*:

> […] the display reads `⟨Pu,v⟩_λ = ⟨u,P⋆v⟩_λ`, that is `P⋆ = P*`. Since `λ` is a probability,
> `Π` is self-adjoint, so `P⋆ⁿ − Π = (Pⁿ − Π)*` and the two operators have the same norm.

## What was missing, and what this file supplies

`Adjoint.lean` proved the adjoint identity on the **plain-real layer**, at the paper's own
hypothesis pair `u, v ∈ L²(λ)`:

  `Stat.tsum_dens_mul_sq : ∑' y, λ y · (Pu)(y) · v(y) = ∑' x, λ x · u(x) · (P⋆v)(x)`,

and `LpLayer.lean` built `P⋆` as a `ContinuousLinearMap` of `Lp ℝ 2 μ`. Neither file claimed the
identification with `ContinuousLinearMap.adjoint`, both disclosing in SCOPE that the
Bochner-integral half of the dictionary was not built. That half is the first section here:

  `Stat.inner_eq_tsum : ⟪F, G⟫_ℝ = ∑' x, λ x · F x · G x`,

from `MeasureTheory.L2.inner_def`, `MeasureTheory.L2.integrable_inner` and
`MeasureTheory.integral_countable` — `μ` charging `{x}` by exactly `λ x`. With it:

* `Stat.densL2` is the density action as a bounded operator of `L²(μ)` of norm at most `1`, built
  exactly as `Stat.pstarL2` was, on `Stat.eLpNorm_dens_le` and a new `Stat.dens_congr_onChain`;
* `Stat.adjoint_pstarL2 : ContinuousLinearMap.adjoint (pstarL2) = densL2`, and its mirror
  `Stat.adjoint_densL2`, by `ContinuousLinearMap.eq_adjoint_iff` against `tsum_dens_mul_sq`;
* `Stat.piL2` is the `λ`-mean projection `F ↦ ⟪1,F⟫·1`, self-adjoint because `λ` is a probability,
  idempotent, and intertwining both actions (`Π P⋆ = P⋆ Π = Π` and `Π P = P Π = Π`, the last two
  read off the adjoint);
* `Stat.betaHat n := ‖Pⁿ − Π‖` and
  `Stat.norm_pstar_pow_sub_pi : ‖P⋆ⁿ − Π‖ = β̂ₙ` for every `n`, which is the trailing clause.

## SCOPE (disclosed)

* **`RowOnChain` is carried**, as everywhere in this layer, by both operators. It is `d ≤ K` on the
  truncation and vacuous on the loop closure (`rowOnChain_none`); it is a hypothesis of the
  *construction* — without it `P⋆` at the sink reads the target row off the chain, where a.e.
  equality says nothing — and not of the mathematics. It is on the face of every statement.
* **The mean projection is `F ↦ ⟪1,F⟫·1`, not an `orthogonalProjection`.** The two agree, `‖1‖ = 1`
  making `ℝ·1` a line through a unit vector, but nothing below needs that identification and it is
  not proved.
* **This settles the adjoint clause of item (1) and no more.** Item (1)'s contraction clause is
  `Stat.eLpNorm_pstar_le_of_memLp` (`LpContraction.lean`), item (2) is `OperatorFinite.lean`
  *modulo* a finite-dimensionality instance on `Lp ℝ 2 μ` that is **still not built**, and item (3)
  is `Operator.lean`. In particular `B̂_K < +∞` of `lem:doubling_truncation_irreducible` Step 4 is
  **not** closed here: the intertwining hypotheses `Pi * P = Pi`, `P * Pi = Pi`, `Pi * Pi = Pi` and
  the kernel hypothesis `hker` that `OperatorFinite.exists_resolvent` consumes are all supplied
  below, and `FiniteDimensional ℝ (Lp ℝ 2 μ)` at `cap = some K` is the one remaining gap.
* **`β̂ₙ` is defined from `P`, as in the paper**, and the theorem is that `P⋆` gives the same
  number. Defining it from `P⋆` and proving the mirror would be the same content read backwards.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `T` Markov with invariant probability `λ` | ✓ carried (`Stat`) |
| `λ` a probability, so `Π` is self-adjoint | ✓ carried (`Stat.total`, via `Stat.norm_oneLp`) |
| `u, v ∈ L²(λ)` in the adjoint identity | ✓ carried (`Lp.memLp`) |
| `Π` the `λ`-mean projection | ✓ carried (`Stat.piL2`, with `Stat.inner_oneLp`) |
| `β̂ₙ = ‖Pⁿ − Π‖_{L²(λ)}` | ✓ carried (`Stat.betaHat`) |
| — | ⚠ **added**: `RowOnChain S cap` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology Real
open scoped ENNReal NNReal InnerProductSpace

variable {S : Setting} {cap : Option ℕ}

namespace Stat

variable (L : Stat S cap)

/-! ## 1. The inner product of `L²(μ)` is the `λ`-weighted sum -/

/-- **The Bochner half of the `LpLayer` dictionary.** `⟪F,G⟫_{L²(μ)} = ∑' x, λ(x)F(x)G(x)`.

`L2.integrable_inner` makes the pointwise product integrable, `integral_countable` turns the
integral into a sum over the countable `St`, and `Stat.mu_singleton` evaluates the weight. -/
theorem inner_eq_tsum (F G : Lp ℝ 2 L.mu) : ⟪F, G⟫_ℝ = ∑' x, L.lam x * F x * G x := by
  rw [L2.inner_def, integral_countable (L2.integrable_inner F G)]
  refine tsum_congr fun x => ?_
  rw [measureReal_def, L.mu_singleton, ENNReal.toReal_ofReal (L.nonneg x), smul_eq_mul,
    Real.inner_apply]
  ring

/-- The same, read against any representatives: off the chain `λ` vanishes, so a.e. equality of
the integrands suffices term by term. -/
theorem inner_eq_tsum_of_ae {F G : Lp ℝ 2 L.mu} {f g : St → ℝ}
    (hF : ⇑F =ᵐ[L.mu] f) (hG : ⇑G =ᵐ[L.mu] g) :
    ⟪F, G⟫_ℝ = ∑' x, L.lam x * f x * g x := by
  rw [L.inner_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : OnChain cap x
  · rw [L.ae_iff_eq.mp hF x hx, L.ae_iff_eq.mp hG x hx]
  · rw [L.vanish hx, zero_mul, zero_mul, zero_mul, zero_mul]

/-! ## 2. The density action is linear and descends to `λ`-classes -/

theorem dens_add (u v : St → ℝ) : L.dens (u + v) = L.dens u + L.dens v := by
  funext y
  rcases y with k | _
  · simp only [Pi.add_apply, L.dens_lad]; ring
  · simp only [Pi.add_apply, L.dens_sink]

theorem dens_smul (c : ℝ) (u : St → ℝ) : L.dens (c • u) = c • L.dens u := by
  funext y
  rcases y with k | _
  · simp only [Pi.smul_apply, smul_eq_mul, L.dens_lad]; ring
  · simp only [Pi.smul_apply, smul_eq_mul, L.dens_sink]

/-- **`P` descends to `λ`-classes**, and unlike `P⋆` it needs no hypothesis to do so: each of its
three weights carries the factor `λ` of the state it reads (`Stat.w1`, `Stat.w2`, `Stat.w3`), so a
state off the chain is read with weight zero. -/
theorem dens_congr_onChain {u v : St → ℝ} (h : ∀ x, OnChain cap x → u x = v x) (y : St) :
    L.dens u y = L.dens v y := by
  rcases y with k | _
  · rw [L.dens_lad, L.dens_lad]
    have h1 : L.w1 k * u (.lad (k + 1)) = L.w1 k * v (.lad (k + 1)) := by
      by_cases hc : OnChain cap (St.lad (k + 1))
      · rw [h _ hc]
      · rw [w1, L.vanish hc, zero_mul, zero_div, zero_mul, zero_mul]
    have h2 : L.w2 k * u (.lad (k / 2)) = L.w2 k * v (.lad (k / 2)) := by
      by_cases hc : OnChain cap (St.lad (k / 2))
      · rw [h _ hc]
      · have hw : L.w2 k = 0 := by
          rw [w2]
          by_cases hd : 1 ≤ k ∧ 2 ∣ k
          · rw [if_pos hd, L.vanish hc, zero_mul, zero_div]
          · rw [if_neg hd, zero_div]
        rw [hw, zero_mul, zero_mul]
    rw [h1, h2, h _ (onChain_sink cap)]
  · rw [L.dens_sink, L.dens_sink, h _ (onChain_src cap)]

/-! ## 3. `P` as a bounded operator of `L²(μ)` -/

/-- `P` acting on `L²(μ)`, as a map of the space into itself. -/
noncomputable def densLp (hrow : RowOnChain S cap) (F : Lp ℝ 2 L.mu) : Lp ℝ 2 L.mu :=
  MemLp.toLp _ (L.memLp_dens hrow one_le_two (by norm_num) (Lp.memLp F))

theorem coeFn_densLp (hrow : RowOnChain S cap) (F : Lp ℝ 2 L.mu) :
    ⇑(L.densLp hrow F) =ᵐ[L.mu] L.dens ⇑F := MemLp.coeFn_toLp _

theorem norm_densLp_le (hrow : RowOnChain S cap) (F : Lp ℝ 2 L.mu) :
    ‖L.densLp hrow F‖ ≤ ‖F‖ := by
  rw [densLp, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp F).eLpNorm_ne_top
    (L.eLpNorm_dens_le hrow one_le_two (by norm_num) (Lp.memLp F))

theorem densLp_add (hrow : RowOnChain S cap) (F G : Lp ℝ 2 L.mu) :
    L.densLp hrow (F + G) = L.densLp hrow F + L.densLp hrow G := by
  refine Lp.ext ?_
  have hcong : L.dens ⇑(F + G) = L.dens (⇑F + ⇑G) :=
    funext fun _ => L.dens_congr_onChain (L.ae_iff_eq.mp (Lp.coeFn_add F G)) _
  filter_upwards [L.coeFn_densLp hrow (F + G), Lp.coeFn_add (L.densLp hrow F) (L.densLp hrow G),
    L.coeFn_densLp hrow F, L.coeFn_densLp hrow G] with x h1 h2 h3 h4
  rw [h1, hcong, L.dens_add, h2]
  simp [h3, h4]

theorem densLp_smul (hrow : RowOnChain S cap) (c : ℝ) (F : Lp ℝ 2 L.mu) :
    L.densLp hrow (c • F) = c • L.densLp hrow F := by
  refine Lp.ext ?_
  have hcong : L.dens ⇑(c • F) = L.dens (c • ⇑F) :=
    funext fun _ => L.dens_congr_onChain (L.ae_iff_eq.mp (Lp.coeFn_smul c F)) _
  filter_upwards [L.coeFn_densLp hrow (c • F), Lp.coeFn_smul c (L.densLp hrow F),
    L.coeFn_densLp hrow F] with x h1 h2 h3
  rw [h1, hcong, L.dens_smul, h2]
  simp [h3]

/-- **`P` as a bounded linear operator on `L²(μ)`**, of norm at most `1` — the mirror of
`Stat.pstarL2`, and the operator the paper's `β̂ₙ` is measured on. -/
noncomputable def densL2 (hrow : RowOnChain S cap) : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu :=
  LinearMap.mkContinuous
    { toFun := L.densLp hrow
      map_add' := L.densLp_add hrow
      map_smul' := fun c F => L.densLp_smul hrow c F } 1
    fun F => by simpa using L.norm_densLp_le hrow F

@[simp] theorem densL2_apply (hrow : RowOnChain S cap) (F : Lp ℝ 2 L.mu) :
    L.densL2 hrow F = L.densLp hrow F := rfl

theorem coeFn_densL2 (hrow : RowOnChain S cap) (F : Lp ℝ 2 L.mu) :
    ⇑(L.densL2 hrow F) =ᵐ[L.mu] L.dens ⇑F := L.coeFn_densLp hrow F

/-- `‖P‖ ≤ 1` on `L²(μ)`. -/
theorem norm_densL2_le (hrow : RowOnChain S cap) : ‖L.densL2 hrow‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## 4. `P⋆ = P*` -/

/-- **`⟪PU, V⟫ = ⟪U, P⋆V⟫` on `L²(μ)`** — `Stat.tsum_dens_mul_sq` read through the inner
product. -/
theorem inner_densL2_left (hrow : RowOnChain S cap) (U V : Lp ℝ 2 L.mu) :
    ⟪L.densL2 hrow U, V⟫_ℝ = ⟪U, L.pstarL2 hrow V⟫_ℝ := by
  rw [L.inner_eq_tsum_of_ae (L.coeFn_densL2 hrow U) (Filter.EventuallyEq.refl _ _),
    L.inner_eq_tsum_of_ae (Filter.EventuallyEq.refl _ ⇑U) (L.coeFn_pstarL2 hrow V)]
  exact L.tsum_dens_mul_sq hrow (L.memLp_two_iff.mp (Lp.memLp U))
    (L.memLp_two_iff.mp (Lp.memLp V))

/-- **The adjoint clause of `lem:doubling_operator`(1).** The density action is the `L²(λ)`-adjoint
of the function action. -/
theorem adjoint_pstarL2 (hrow : RowOnChain S cap) :
    ContinuousLinearMap.adjoint (L.pstarL2 hrow) = L.densL2 hrow :=
  ((ContinuousLinearMap.eq_adjoint_iff (L.densL2 hrow) (L.pstarL2 hrow)).mpr
    (L.inner_densL2_left hrow)).symm

/-- The same identity read the other way: `P* = P⋆`. -/
theorem adjoint_densL2 (hrow : RowOnChain S cap) :
    ContinuousLinearMap.adjoint (L.densL2 hrow) = L.pstarL2 hrow := by
  rw [← L.adjoint_pstarL2 hrow, ContinuousLinearMap.adjoint_adjoint]

/-! ## 5. The mean projection -/

/-- **`Π`, the `λ`-mean projection** of `L²(μ)`: `ΠF = (∫F dλ)·1`. -/
noncomputable def piL2 : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu :=
  (innerSL ℝ L.oneLp).smulRight L.oneLp

@[simp] theorem piL2_apply (F : Lp ℝ 2 L.mu) : L.piL2 F = ⟪L.oneLp, F⟫_ℝ • L.oneLp := rfl

/-- `⟪1,1⟫ = 1`: `λ` is a probability. -/
theorem inner_oneLp_self : ⟪L.oneLp, L.oneLp⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, L.norm_oneLp, one_pow]

/-- **`Π` is idempotent.** -/
theorem piL2_mul_piL2 : L.piL2 * L.piL2 = L.piL2 := by
  refine ContinuousLinearMap.ext fun F => ?_
  show L.piL2 (L.piL2 F) = L.piL2 F
  rw [piL2_apply, piL2_apply, real_inner_smul_right, L.inner_oneLp_self, mul_one]

/-- **`Π` is self-adjoint**, `λ` being a probability. -/
theorem adjoint_piL2 : ContinuousLinearMap.adjoint L.piL2 = L.piL2 := by
  refine ((ContinuousLinearMap.eq_adjoint_iff L.piL2 L.piL2).mpr fun U V => ?_).symm
  rw [piL2_apply, piL2_apply, real_inner_smul_left, real_inner_smul_right, real_inner_comm]
  ring

/-- `Π P⋆ = Π`: the function action preserves the `λ`-mean. -/
theorem piL2_mul_pstarL2 (hrow : RowOnChain S cap) : L.piL2 * L.pstarL2 hrow = L.piL2 := by
  refine ContinuousLinearMap.ext fun F => ?_
  show L.piL2 (L.pstarL2 hrow F) = L.piL2 F
  rw [piL2_apply, piL2_apply, pstarL2_apply, L.inner_oneLp_pstarLp]

/-- `P⋆ Π = Π`: the function action fixes the constants. -/
theorem pstarL2_mul_piL2 (hrow : RowOnChain S cap) : L.pstarL2 hrow * L.piL2 = L.piL2 := by
  refine ContinuousLinearMap.ext fun F => ?_
  show L.pstarL2 hrow (L.piL2 F) = L.piL2 F
  rw [piL2_apply, map_smul, pstarL2_apply, L.pstarLp_oneLp hrow]

/-- `Π P = Π`, read off the adjoint of `P Π = Π`. -/
theorem piL2_mul_densL2 (hrow : RowOnChain S cap) : L.piL2 * L.densL2 hrow = L.piL2 := by
  have h := congrArg ContinuousLinearMap.adjoint (L.pstarL2_mul_piL2 hrow)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, L.adjoint_piL2,
    L.adjoint_pstarL2 hrow] at h
  exact h

/-- `P Π = Π`, read off the adjoint of `Π P⋆ = Π`. -/
theorem densL2_mul_piL2 (hrow : RowOnChain S cap) : L.densL2 hrow * L.piL2 = L.piL2 := by
  have h := congrArg ContinuousLinearMap.adjoint (L.piL2_mul_pstarL2 hrow)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, L.adjoint_piL2,
    L.adjoint_pstarL2 hrow] at h
  exact h

/-! ## 6. `β̂ₙ`, and the trailing clause -/

/-- **`β̂ₙ := ‖Pⁿ − Π‖_{L²(λ)}`** — the mixing coefficient of `def:doubling_setting`, defined on
the density action as the paper defines it. -/
noncomputable def betaHat (hrow : RowOnChain S cap) (n : ℕ) : ℝ :=
  ‖(L.densL2 hrow) ^ n - L.piL2‖

/-- `P⋆ⁿ − Π` is the adjoint of `Pⁿ − Π`. -/
theorem adjoint_densL2_pow_sub_piL2 (hrow : RowOnChain S cap) (n : ℕ) :
    ContinuousLinearMap.adjoint ((L.densL2 hrow) ^ n - L.piL2)
      = (L.pstarL2 hrow) ^ n - L.piL2 := by
  rw [map_sub, L.adjoint_piL2, ← ContinuousLinearMap.star_eq_adjoint, star_pow,
    ContinuousLinearMap.star_eq_adjoint, L.adjoint_densL2 hrow]

/-- **`‖P⋆ⁿ − Π‖_{L²(λ)} = β̂ₙ` for every `n ≥ 0`** — the trailing clause of
`lem:doubling_operator`(1). `Π` is self-adjoint because `λ` is a probability, so `P⋆ⁿ − Π` is the
adjoint of `Pⁿ − Π`, and taking adjoints is an isometry. -/
theorem norm_pstarL2_pow_sub_piL2 (hrow : RowOnChain S cap) (n : ℕ) :
    ‖(L.pstarL2 hrow) ^ n - L.piL2‖ = L.betaHat hrow n := by
  rw [betaHat, ← L.adjoint_densL2_pow_sub_piL2 hrow n]
  exact ContinuousLinearMap.adjoint.norm_map _

end Stat

end GFNBounds.Doubling
