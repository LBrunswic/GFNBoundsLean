import GFNBounds.Core.Universality

/-!
# The truncation vanishes on `L^p(ν)` for `p < ∞`, and weak universality follows

**`theo:universality_L2_full`** — `proofs.tex:65–115` (Theorem 15 of the ICLR build),
**Step 3**, `proofs.tex:114`:

> *Step 3: the truncation vanishes.* Let `p < +∞`. Then `0 ≤ ψ_η ≤ (Sθ)⁺` with
> `(Sθ)⁺ ∈ L^p(ν_B)`, and `ψ_η → 0` pointwise as `η → +∞`; dominated convergence gives
> `‖ψ_η‖_{L^p(ν_B)} → 0`, so `Θ` is weakly `L^p`-universal.

`Core.Universality` proved everything the step is *applied* to — the defect identity
`equ:defect_is_truncation`, the quantitative bound `equ:universality_quantitative`, and
`weaklyUniversalAt_of_tendsto`, which carries `‖ψ_η‖ → 0` as a hypothesis. This file discharges
that hypothesis on the concrete space, which is where it lives: it is the one step of the proof
that is not lattice algebra.

What is proved here:

* `tendsto_truncation_norm` — `‖ψ_η‖_{L^p(ν)} → 0` as `η → +∞`, for `ν` finite and `p ≠ ∞`,
  for **every** bounded `P`, `Pi` and every `θ`. No mixing hypothesis is needed: `Sθ` is an
  element of `L^p(ν)` whatever it is, and the statement is about the truncation of a fixed
  `L^p` function, not about the flow.
* `weaklyUniversalAt_Lp` — the payoff, unconditional for `p ≠ ∞`: under summable mixing,
  `P 𝟏 = 𝟏` and `Π θ = 0`, the family `Θ = {P} × L^p_+(ν)` is weakly `L^p`-universal.

The constant `𝟏 ∈ L^p(ν)` is `constOne`, which exists because `ν` is finite — the appendix's
"`𝟏 ∈ L^p(ν_B)` because `ν_B` is finite" (`proofs.tex:100`, Step 2).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` a measured Polish space, `ν_B` finite | ⚠ weakened: any `MeasurableSpace α` with `[IsFiniteMeasure ν]`. Polish is not used by Step 3 |
| `π⋆` a Markov kernel with finite `L^p(ν_B) → L^p(ν_B)` operator norm | ⚠ weakened: a bounded operator `P` on `Lp ℝ p ν`, as in `Core.Mixing` — the kernel is not the primitive |
| `π⋆` ergodic on `(𝒮, ν_B)` | ⚠ weakened: replaced by its three consequences, assumed directly — `Mixing P Pi` (`Π P = P Π = Π`), `P 𝟏 = 𝟏`, `Π θ = 0` |
| summable `L^p`-mixing coefficients | ✓ carried, as `Mixing.summable` |
| `F_init, F_term ≪ ν_B` probability distributions with densities in `L^p(ν_B)` | ⚠ weakened: `θ : Lp ℝ p ν` arbitrary with `Π θ = 0`, which is all the proof uses |
| `p < +∞` | ✓ carried, as `hp : p ≠ ⊤`; `1 ≤ p` as `[Fact (1 ≤ p)]` |
| conclusion: `Θ = {π⋆} × L^p_+(ν_B)` weakly `L^p`-universal | ✓ carried, as `WeaklyUniversalAt P θ` of `Core.Universality` |
| conclusion: `Θ` strongly universal at `p = +∞` | ✗ not carried — see SCOPE |

## The analytic step, and what carries it

`ψ_η` has the a.e. representative `x ↦ max (Sθ x - η, 0)` (`coeFn_truncation`). Dominated
convergence is applied to the `ℝ≥0∞`-integrals `∫⁻ ‖ψ_η x‖ₑ ^ p.toReal dν` through
`MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence'` along the filter
`atTop : Filter ℝ` itself — `ℝ` is archimedean, so that filter is countably generated
(`atTop_isCountablyGenerated_of_archimedean`) and the sequential detour through
`η = (n : ℕ)`, with its antitonicity argument, is unnecessary. The dominating function is
`x ↦ ‖Sθ x‖ₑ ^ p.toReal`, whose integral is finite because `Sθ ∈ L^p(ν)`; the `η`-limit is
pointwise and in fact eventually exact, since `max (Sθ x - η, 0) = 0` once `η > Sθ x`.

## SCOPE (disclosed)

* **`p = ∞` is not covered, and the paper does not cover it this way either.** Step 3's second
  half handles `p = +∞` by a different argument — `ψ_η = 0` outright for `η ≥ ‖Sθ‖_∞`, giving
  *strong* universality. That half is already
  `GFNBounds.Core.stronglyUniversalAt_of_le` in `Core.Universality`, stated as the order
  hypothesis `Sθ ≤ η • 𝟏` it consumes; instantiating it at `L^∞(ν)` would need
  `Sθ ≤ ‖Sθ‖_∞ • 𝟏` in the `Lp` order, which is not proved here.
* **`tendsto_truncation_norm` is stated more generally than the paper's step**, not less: it
  drops `Mixing P Pi`, `P 𝟏 = 𝟏` and `Π θ = 0`, none of which Step 3 uses. `weaklyUniversalAt_Lp`
  restores all three, since the steps it composes with do use them.
* **The hypotheses of `weaklyUniversalAt_Lp` are those of `Core.Universality`, not of the paper's
  theorem statement.** The paper hypothesizes a Markov kernel `π⋆`, ergodic on `(𝒮, ν_B)`, with
  finite `L^p → L^p` operator norm and summable mixing coefficients, and *derives*
  `Π P⋆ = P⋆ Π = Π`, `P⋆ 𝟏 = 𝟏` and `Π θ = 0` from ergodicity, invariance of `ν_B` and
  `∫θ dν_B = 0`. Those three derivations are `Core.Flow`'s business and are not done anywhere in
  this library yet; here they are hypotheses. Nothing is claimed about when they hold.
* `θ` is an arbitrary element of `L^p(ν)`, not required to be a difference of two probability
  densities. `Π θ = 0` is the only consequence of that the proof uses, and it is assumed
  directly.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open MeasureTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The constant `𝟏` of `L^p(ν)`. It is an element of `L^p` because `ν` is finite, which is
the appendix's own reason (`proofs.tex:100`); on `L^p(ν_B)` it is the `𝟏` whose `0`-flow
property `(Id - P⋆) 𝟏 = 0` supplies the freedom in Step 2. -/
noncomputable def constOne (ν : Measure α) (p : ℝ≥0∞) [IsFiniteMeasure ν] : Lp ℝ p ν :=
  (memLp_const (1 : ℝ)).toLp fun _ => (1 : ℝ)

omit [Fact (1 ≤ p)] in
theorem coeFn_constOne : ⇑(constOne ν p) =ᵐ[ν] fun _ => (1 : ℝ) :=
  MemLp.coeFn_toLp _

/-- The pointwise form of the truncation `ψ_η = (η • 𝟏 - Sθ)⁻`: its a.e. representative is
`x ↦ max (Sθ x - η, 0)`, which is the appendix's `(Sθ - η)⁺`. -/
theorem coeFn_truncation (P Pi : Lp ℝ p ν →L[ℝ] Lp ℝ p ν) (θ : Lp ℝ p ν) (η : ℝ) :
    ⇑(truncation P Pi (constOne ν p) θ η)
      =ᵐ[ν] fun x => max (Mixing.S P Pi θ x - η) 0 := by
  have hsmul : ⇑(η • constOne ν p) =ᵐ[ν] fun _ => η := by
    filter_upwards [Lp.coeFn_smul η (constOne ν p), coeFn_constOne (ν := ν) (p := p)]
      with x hx h1
    rw [hx, _root_.Pi.smul_apply, h1, smul_eq_mul, mul_one]
  have hsub : ⇑(η • constOne ν p - Mixing.S P Pi θ)
      =ᵐ[ν] fun x => η - Mixing.S P Pi θ x := by
    filter_upwards [Lp.coeFn_sub (η • constOne ν p) (Mixing.S P Pi θ), hsmul] with x hx hs
    rw [hx, _root_.Pi.sub_apply, hs]
  have hdef : truncation P Pi (constOne ν p) θ η
      = (-(η • constOne ν p - Mixing.S P Pi θ)) ⊔ 0 := rfl
  filter_upwards [Lp.coeFn_sup (-(η • constOne ν p - Mixing.S P Pi θ)) (0 : Lp ℝ p ν),
    Lp.coeFn_neg (η • constOne ν p - Mixing.S P Pi θ), Lp.coeFn_zero ℝ p ν, hsub]
    with x hsup hneg hzero hx
  show (truncation P Pi (constOne ν p) θ η) x = _
  rw [hdef, hsup, _root_.Pi.sup_apply, hneg, hzero, _root_.Pi.neg_apply,
    _root_.Pi.zero_apply, hx, neg_sub]

/-- **Step 3 of `theo:universality_L2_full`, `p < +∞`**: the truncation vanishes in `L^p(ν)`.

`0 ≤ ψ_η ≤ (Sθ)⁺ ∈ L^p(ν)` and `ψ_η → 0` pointwise as `η → +∞`, so dominated convergence gives
`‖ψ_η‖_{L^p(ν)} → 0`. No hypothesis on `P`, `Pi` or `θ` is used: the statement is about the
truncation of the fixed `L^p` element `Sθ`. -/
theorem tendsto_truncation_norm (hp : p ≠ ⊤) (P Pi : Lp ℝ p ν →L[ℝ] Lp ℝ p ν)
    (θ : Lp ℝ p ν) :
    Tendsto (fun η : ℝ => ‖truncation P Pi (constOne ν p) θ η‖) atTop (𝓝 0) := by
  set g : Lp ℝ p ν := Mixing.S P Pi θ
  set r : ℝ := p.toReal
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hrpos : 0 < r := ENNReal.toReal_pos hp0 hp
  -- The a.e. representative of `ψ_η`, and the integrand it produces.
  set F : ℝ → α → ℝ≥0∞ := fun η x => ‖max (g x - η) 0‖ₑ ^ r with hF
  have hgm : AEMeasurable (⇑g) ν := (Lp.aestronglyMeasurable g).aemeasurable
  have hFmeas : ∀ η : ℝ, AEMeasurable (F η) ν := by
    intro η
    exact (ENNReal.continuous_rpow_const.measurable).comp_aemeasurable
      ((hgm.sub_const η).max aemeasurable_const).enorm
  -- Each `‖ψ_η‖` is the `p`-seminorm of `F η`'s base function.
  have hnorm : ∀ η : ℝ, ‖truncation P Pi (constOne ν p) θ η‖
      = (eLpNorm (fun x => max (g x - η) 0) p ν).toReal := by
    intro η
    rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_truncation P Pi θ η)]
  -- Dominated convergence for the `ℝ≥0∞`-integrals, along `atTop : Filter ℝ`.
  have hbound_fin : ∫⁻ x, ‖g x‖ₑ ^ r ∂ν ≠ ⊤ := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hrpos, ← eLpNorm_eq_eLpNorm' hp0 hp]
    exact (ENNReal.rpow_lt_top_of_nonneg hrpos.le (Lp.eLpNorm_ne_top g)).ne
  have hlint : Tendsto (fun η : ℝ => ∫⁻ x, F η x ∂ν) atTop (𝓝 0) := by
    have hzero : ∫⁻ _ : α, (0 : ℝ≥0∞) ∂ν = 0 := lintegral_zero
    rw [← hzero]
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun x => ‖g x‖ₑ ^ r)
      (Eventually.of_forall hFmeas) ?_ hbound_fin ?_
    · -- `0 ≤ max (g x - η) 0 ≤ |g x|` once `η ≥ 0`, so the enorms compare.
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with η hη
      filter_upwards with x
      refine ENNReal.rpow_le_rpow ?_ hrpos.le
      rw [enorm_le_iff_norm_le, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self (g x)]) (abs_nonneg _)
    · -- Pointwise: `max (g x - η) 0 = 0` once `η > g x`, so the integrand is eventually `0`.
      filter_upwards with x
      refine Tendsto.congr' ?_ (tendsto_const_nhds (α := ℝ) (x := (0 : ℝ≥0∞)))
      filter_upwards [eventually_ge_atTop (g x)] with η hη
      rw [hF]
      simp [max_eq_right (by linarith : g x - η ≤ 0), ENNReal.zero_rpow_of_pos hrpos]
  -- `eLpNorm = (∫⁻ …) ^ (1/r)`, and `x ↦ x ^ (1/r)` is continuous with `0 ^ (1/r) = 0`.
  have heL : Tendsto (fun η : ℝ => eLpNorm (fun x => max (g x - η) 0) p ν) atTop (𝓝 0) := by
    have hcont : Tendsto (fun t : ℝ≥0∞ => t ^ (1 / r)) (𝓝 0) (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := 1 / r)).tendsto (0 : ℝ≥0∞)
      rwa [ENNReal.zero_rpow_of_pos (by positivity)] at this
    have := hcont.comp hlint
    refine this.congr fun η => ?_
    rw [Function.comp_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  -- Back to the real norm.
  have := (ENNReal.tendsto_toReal (by simp)).comp heL
  simpa [Function.comp_def, hnorm] using this

/-- **`theo:universality_L2_full`, its conclusion at `p < +∞`**: the family
`Θ = {P} × L^p_+(ν)` is weakly `L^p`-universal.

Steps 1 and 2 are `Core.Mixing` and `Core.Universality`; Step 3 is
`tendsto_truncation_norm` above, and this is their composition. The hypotheses are the two the
construction consumes — `P` fixes the constants and `Π θ = 0` — together with summable
mixing. -/
theorem weaklyUniversalAt_Lp {P Pi : Lp ℝ p ν →L[ℝ] Lp ℝ p ν} {θ : Lp ℝ p ν}
    (h : Mixing P Pi) (hone : P (constOne ν p) = constOne ν p) (hθ : Pi θ = 0)
    (hp : p ≠ ⊤) : WeaklyUniversalAt P θ :=
  weaklyUniversalAt_of_tendsto h hone hθ (tendsto_truncation_norm hp P Pi θ)

/-- **`theo:universality_L2_full`, weak half, with `def:universality`'s quantifier closed**:
for `p ≠ ∞`, under summable mixing and with `P` fixing the constants, the family
`Θ = {P} × L^p_+(ν)` is weakly `L^p`-universal — every pair of equal total mass is reachable,
each by its own outflow.

This is the paper's conclusion for `p < ∞`. What it still assumes rather than derives is
`Mixing P Pi` and `P 𝟏 = 𝟏`; see this file's SCOPE. -/
theorem weaklyUniversal_Lp {P Pi : Lp ℝ p ν →L[ℝ] Lp ℝ p ν}
    (h : Mixing P Pi) (hone : P (constOne ν p) = constOne ν p) (hp : p ≠ ⊤) :
    WeaklyUniversal P Pi :=
  fun _θ hθ => weaklyUniversalAt_Lp h hone hθ hp

end GFNBounds.Core
