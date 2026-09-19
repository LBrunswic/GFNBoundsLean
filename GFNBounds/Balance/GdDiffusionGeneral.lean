import GFNBounds.Core.FirstVariationGeneral
import GFNBounds.Balance.TrainingSpeedAssembled
import GFNBounds.Balance.LiftGeneralMixing

/-!
# Gradient descent as backward diffusion, and the DB gradient, on a standard Borel space

**`theo:gd_diffusion_full`** — `proofs.tex`, the `theorem` carrying that label (`:591–614` when
written), proof `:616–626`.
**`theo:gd_diffusion`** — its body twin, `cv_divergence.tex` (`:147–153` when written).
**`cor:db_gradient`** — `proofs.tex` (`:547–554` when written), proof `:556–558`.
(Line numbers drift, kb `0036`; the label is the anchor.)

> (`theo:gd_diffusion_full`) Under the hypotheses of Lemma `lem:adjoint`, let `T` be ergodic;
> write `P` for the density action `h ↦ d((hλ)T)/dλ` of `T` on `L²(λ)`, `P†` for its adjoint,
> `A := P − I`, and `M_w` for the multiplication by a non-negative `w ∈ L^∞(λ)`, and let
> `ν := wλ`. Let `a ∈ (0,1)` and let `g : ℝ₊* → ℝ` be `C³` on `[1−a,1+a]` with
> `g(1) = g'(1) = 0 < g''(1)`; set `Γ₃ := sup_{[1−a,1+a]}|g'''|`, `C_g := g''(1) + aΓ₃/2`,
> `C₄ := ‖w‖_{L^∞}(4g''(1) + 3Γ₃)`, `C₅ := (16/3)C_g‖w‖_{L^∞}`, `K := 2C₄ + C₅`. Then for every
> `ε ∈ (0, a/4]` and every `h ∈ L^∞(λ)` with `‖h‖_{L^∞(λ)} ≤ ε`, the ratio `r := d(μT)/dμ` of
> `μ := (1+h)λ` is `r = (1+Ph)/(1+h)` and satisfies, `λ`-almost everywhere,
> `|r−1| ≤ (4/3)|Ah|`, `|r−1| ≤ 2a/3`, `|g'(r)| ≤ C_g|r−1|` (`eq:gd_ratio_bounds`);
> `𝓛_{g,ν}` has at `μ` a gradient `∇^λ𝓛_{g,ν}(μ)` in the sense of Theorem
> `theo:first_variation_full`, with density `P†ψ − rψ` against `λ`, where `ψ := g'(r)w/(1+h)`;
> and (`eq:linearized_flow`) `∇^λ𝓛_{g,ν}(μ) = g''(1)(P† − I)[w(P − I)h]λ + err(h)`,
> `‖err(h)‖_{𝓜²(λ)} ≤ Kε‖(P−I)h‖_{L²(λ)} ≤ 2Kε‖h‖_{L²(λ)}`. The linearization of the gradient
> flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` at `λ` is therefore `ḣ = −g''(1)A†M_wAh`. In particular for
> `w ≡ 1` and `T` reversible with respect to `λ`, `ḣ = −g''(1)(I−P)²h`: training is the *square*
> of the backward-policy heat flow `ḣ = −(I−P)h`, and each eigenmode `Pφ = βφ` of the backward
> policy decays at rate `g''(1)(1−β)²`.

> (`theo:gd_diffusion`) Near the balanced flow, and for any generator of class `C³` near `1` with
> non-degenerate curvature there, the gradient field of a balance loss linearizes to the backward
> policy's diffusion applied twice, so that training relaxes the current flow guess by diffusing
> it through the frozen backward policy — and for the FM loss with a reversible policy and uniform
> training weight (`w ≡ 1`) it is exactly the square of that policy's heat flow, each of its
> eigenmodes decaying at `g''(1)(1−β)²`. (Setting of the subsection: `(𝒮', λ', T)` is either
> `(𝒮, λ, π_←)` for the FM loss or its edge lift `(𝒮², λ₂, K₂)` for the DB loss.)

> (`cor:db_gradient`) Under the hypotheses of Theorem `theo:first_variation_full` applied on
> `(𝒮², λ₂, K₂)`, the DB loss with frozen backward policy satisfies, with `r̂ := d(μK₂)/dμ`,
> `∇^{λ₂}_μ 𝓛_{DB,g,ν̂} = (K₂^{λ₂} − r̂)[g'(r̂)(dν̂/dμ)λ₂]` where `K₂^{λ₂}` is the forward edge
> kernel of Lemma `lem:lift_wellposed`.

`GFNBounds/Balance/Expansion.lean` and `GFNBounds/Balance/GradientFormulas.lean` prove finite forms of these
on a `Fintype` (the finite forms; `Expansion.lean` is the one `theo:local_convergence_full`
consumes). This file is the general form, on a standard Borel space, built on
`GFNBounds/Core/FirstVariationGeneral.lean` (the first variation, closed in A),
`GFNBounds/Core/AdjointGeneral.lean` (the reversal `T^λ`, the function/density actions, the
contraction) and `GFNBounds/Balance/LiftGeneral.lean` (`K₂`, `λ₂`, the duality); the `C³`
convention and `Γ₃` are `GFNBounds/Balance/TrainingSpeedAssembled.lean`'s (`winC3`, `Gamma3W`,
`taylor_bundle_of_C3On`), the constants `Cg`, `C4`, `C5`, `Kexp` are `Expansion.lean`'s.

## Conventions

`P` is `Pd T lam = funAct (reversal T lam)`, the function action of the `λ`-reversal, which *is*
the density action `h ↦ d((hλ)T)/dλ` (`Pd_eq_densityAction`, against the library's signed
`Core.densityAction`); `P†` is the function action of `T` (`Pd_adjoint`); `A = Aop`, `A† = Adag`,
`H = linHess T lam w g''(1)`, `I − P = IminusP`. `μ = (1+h)λ` is `flowOf lam h`, `ν = wλ` is
`wMeas lam w`, the ratio, loss and perturbed flow `μ + sδ` are `FirstVariationGeneral`'s `ratio`,
`loss`, `perturb`. `g'` is any derivative `gd` of `g` within the window (one-sided at `1 ± a`),
as in `TrainingSpeedAssembled.lean`; `ψ = psiP`, `D = P†ψ − rψ = gradD`. The DB loss is
`dbLoss pb g ν̂ μ = ∫ g(d(π_← ⊗ F)/dμ) dν̂`, `F = m₁μ`: its denominator `F ⊗ π_→^μ` is `μ` itself
(`dbLoss_eq_condKernel` restores the paper's form for every disintegration).

## How the proof goes (the paper's, step for step)

The scalar core (`abs_r_sub_one_le_*`, `sq_r_sub_one_le`, `psi_expansion`, `r_sub_one_mul_psi_le`)
is the paper's bullets 1, 3, 4 read at one point; `ratio_flowOf` is bullet 1's `r = (1+Ph)/(1+h)`
(`lem:adjoint`(3) plus the Radon–Nikodym chain rule); bullet 2 is `gd_gradient`: the paper's
extension `g̃` (`gext`, affine outside the window with slope `g'(1∓a)`) is `C¹` on `ℝ`
(`hasDerivAt_gext`, `continuous_gext'`), `first_variation_general` applies to it, and the two
losses agree near `s = 0` along every bounded direction (`loss_eventually_eq_gext`); bullet 5 is
`gd_expansion`, with `‖A†‖ ≤ 2` from the `L²` contraction (`IsInvariant.eLpNorm_funAct_le`).
Bullet 6 is split into its three claims: `linearization_unique` (with `gradD_zero`, `linHess_const_mul`),
`linHess_reversible`, and `linHess_eigen`/`eigenmode_decay`.

## What is proved

| | |
|---|---|
| `ratio_flowOf` | `r = (1+Ph)/(1+h)` `λ`-a.e. |
| `gd_ratio_bounds` | **`eq:gd_ratio_bounds`**, `λ`-a.e. |
| `gd_gradient` | the gradient at `μ`: `(T^λ − r)[ψλ]` has `λ`-density `D` (setwise), `D ∈ L²(λ)`, `D` represents the derivative along every essentially bounded direction, uniquely in `L²(λ)` |
| `gd_expansion` | **`eq:linearized_flow`**: `‖D − g''(1)A†M_wAh‖_{L²} ≤ Kε‖Ah‖_{L²}` and `‖Ah‖ ≤ 2‖h‖`, for any `gd` with the Taylor bound, `K = Kexp g''(1) a Γ₃ W` |
| `gradD_zero`, `linHess_const_mul`, `linearization_unique` | the flow sentence: `D(0) = 0`, `H` linear, and `H` is the **unique** homogeneous `H'` with `‖D(h) − H'h‖_{L²} ≤ c(δ)‖h‖_{L²}` on `‖h‖_{L^∞} ≤ δ`, `c(δ) → 0` |
| `linHess_reversible` | `w ≡ 1`, `λ ⊗ T = T ⊗ λ`: `H = g''(1)(I−P)²` `λ`-a.e. |
| `linHess_eigen`, `eigenmode_decay` | `Pφ = βφ` ⟹ `Hφ = g''(1)(1−β)²φ`, and `e^{−g''(1)(1−β)²t}φ` solves `ḣ = −Hh` |
| **`theo_gd_diffusion_full`** | the theorem with the paper's hypotheses, `W = ‖w‖_{L^∞}`, `Γ₃ = Gamma3W` |
| **`theo_gd_diffusion_DB`** | the body twin's DB half: the same on `(𝒮², λ₂, K₂)`, for `dbLoss` |
| `dbLoss_eq_loss`, `dbLoss_eq_condKernel`, `reversal_edgeLift_ae` | `prop:db_lift` as a loss identity; `K₂^{λ₂} = (s,s') ↦ (s', π_→^λ(s'))` `λ₂`-a.e. |
| **`cor_db_gradient`** | **`cor:db_gradient`** with the paper's hypotheses, `K₂^{λ₂}` the forward edge kernel |
| `Pd_eq_densityAction`, `Pd_adjoint` | `P` is the density action of the paper, `P†` its `L²(λ)` adjoint |
| `gd_diffusion_hypotheses_inhabited` | non-vacuity (kb `0025`, `0027`), the reversible hypothesis included |
| `cor_db_gradient_hypotheses_inhabited` | non-vacuity of `cor_db_gradient` (kb `0025`, `0027`): the edge lift of the resampling kernel `x ↦ π`, `μ = ν̂ = λ₂`, `r̂ = 1`, `g = (x−1)²` |

## Hypothesis checklist (`theo:gd_diffusion_full`, `theo_gd_diffusion_full`)

| paper hypothesis | here |
|---|---|
| `lem:adjoint`: `𝒮` Polish, `ν_B`, `λ ∈ 𝓜⁺(𝒮, ν_B)` | ✓ weakened in the safe direction to `[StandardBorelSpace S] [Nonempty S]` as in `AdjointGeneral.lean`; `ν_B` dropped (no clause involves it) |
| `T` Markov, `λ` non-zero, finite, `T`-invariant | ✓ carried; `λ ≠ 0` carried and unused |
| `T` ergodic | ⚠ **weakened**: not carried — used nowhere in the proof (the paper's proof never invokes it) |
| `w ≥ 0`, `w ∈ L^∞(λ)`, `ν = wλ` | ✓ `hw0` (a.e.), `hwinf : MemLp w ⊤ lam`, `ν = wMeas lam w`; `w` measurable (a representative) |
| `a ∈ (0,1)` | ✓ `ha`, `ha1` |
| `g : ℝ₊* → ℝ` `C³` on `[1−a,1+a]` | ✓ `ContDiffOn ℝ 3 g (winC3 a)` (one-sided at `1 ± a`, the library's A-reading of `theo:local_convergence_full`), `g'` any derivative `gd` within the window (`derivWithin g (winC3 a)` always qualifies, `hasDerivWithinAt_derivWithin_of_C3On`); values of `g` off the window never matter |
| `g(1) = g'(1) = 0 < g''(1)` | ✓ `_hg1` (carried, unused), `hg'1 : deriv g 1 = 0`, `hg2 : 0 < deriv (deriv g) 1` — the classical derivatives at the interior point `1` |
| `Γ₃`, `C_g`, `C₄`, `C₅`, `K` | ✓ `Gamma3W g a` (sup of `|iteratedDerivWithin 3 g [1−a,1+a]|`), `Cg`, `C4`, `C5`, `Kexp` at `‖w‖_{L^∞} = (eLpNorm w ⊤ lam).toReal` — the printed formulas |
| `ε ∈ (0, a/4]`, `h ∈ L^∞(λ)`, `‖h‖_{L^∞} ≤ ε` | ✓ `0 < eps`, `eps ≤ a/4`, `h` measurable (a representative of the class; `μ` depends only on the class), `∀ᵐ x ∂λ, |h x| ≤ ε` |

## SCOPE (disclosed)

* **"Has a gradient in the sense of `theo:first_variation_full`"** is certified as that
  theorem's statement reads — the derivative along every admissible direction (here every
  essentially bounded one) is represented by `D` in `⟨·∣·⟩_λ` — plus uniqueness in `L²(λ)` and the
  setwise identification of the signed measure `(T^λ − r)[ψλ]`. The uniform second-order
  remainder that `theo_first_variation_full` adds as its clause (6) is **not** restated for `g`
  (it holds for `g̃`, and `g = g̃` on the window; transporting it needs a ball on which every
  perturbed ratio stays in the window, which the paper does not state).
* **`err(h)` and `‖·‖_{𝓜²(λ)}`** are delivered at the density level: `err(h) = Eλ` with
  `E = D − Hh`, `‖Eλ‖_{𝓜²(λ)} := ‖E‖_{L²(λ)}` (`eLpNorm E 2 lam`, in `ℝ≥0∞`), the decomposition
  `∇ = (Hh)λ + Eλ` being `D = Hh + E`.
* **The flow sentence** "the linearization of the gradient flow at `λ` is `ḣ = −Hh`" is certified
  as a statement about the field `h ↦ −D(h)` of the flow read on `μ = (1+h)λ` (the paper's own
  reading, "along `μ_t = (1+h_t)λ` the flow reads `ḣ_t = −D`"): `D(0) = 0`, `D(h) − Hh` is
  `O(‖h‖_{L^∞}‖h‖_{L²})` (`gd_expansion`), and `H` is the only homogeneous map with an `o(‖h‖)`
  remainder (`linearization_unique`). No flow of measures is constructed here.
* **Eigenmode decay** is certified by the paper's own witness: `e^{−g''(1)(1−β)²t}φ` solves
  `ḣ = −g''(1)(I−P)²h`, pointwise in `t`, `λ`-a.e. in the state (`eigenmode_decay`); uniqueness
  of solutions of the linear ODE is not claimed by the paper and not proved.
* **`cor:db_gradient`** carries `theo_first_variation_full`'s hypotheses verbatim on
  `(𝒮², λ₂, K₂)`, `ν_G = λ₂`; `λ₂ ≠ 0` is derived from `λ ≠ 0`, invariance of `λ₂` from that of
  `λ` (`edgeMeasure_invariant`). The general statement subsumes the finite residue recorded on
  `GradientFormulas.lean` (`λ₂ > 0` at every pair): `μ ∼ λ₂` is a measure-level hypothesis, so a
  sparse edge set is covered with no subtype.
* **The body twin** is certified as `theo_gd_diffusion_full` for the FM loss (`T = π_←`) and
  `theo_gd_diffusion_DB` for the DB loss (`T = K₂`, the loss identified with `dbLoss` by
  `prop:db_lift`); the reversible sentence is the FM one, `theo_gd_diffusion_full`(6).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GFNBounds.Balance.GdDiffusionGeneral

open GFNBounds.Core.General GFNBounds.Core.General.FirstVariation

/-! ### The scalar core of the proof -/

section Scalar

/-- `3/4 ≤ 1 + t` for `|t| ≤ ε ≤ 1/4`. -/
theorem three_quarters_le {t eps : ℝ} (ht : |t| ≤ eps) (heps : eps ≤ 1 / 4) : 3 / 4 ≤ 1 + t := by
  have := (abs_le.mp ht).1; linarith

/-- `r − 1 = Ah/(1+h)` for `r = (1+Ph)/(1+h)`, `Ah = Ph − h`. -/
theorem ratio_sub_one {hx Px : ℝ} (hd : 1 + hx ≠ 0) :
    (1 + Px) / (1 + hx) - 1 = (Px - hx) / (1 + hx) := by
  field_simp; ring

variable {hx Px eps a : ℝ}

/-- `|Ah| ≤ 2ε`. -/
theorem abs_A_le (hh : |hx| ≤ eps) (hP : |Px| ≤ eps) : |Px - hx| ≤ 2 * eps := by
  have := abs_sub Px hx; linarith

/-- **`|r − 1| ≤ (4/3)|Ah|`**. -/
theorem abs_r_sub_one_le_four_thirds (hh : |hx| ≤ eps) (heps : eps ≤ 1 / 4) :
    |(1 + Px) / (1 + hx) - 1| ≤ 4 / 3 * |Px - hx| := by
  have hd := three_quarters_le hh heps
  have hdpos : (0 : ℝ) < 1 + hx := by linarith
  rw [ratio_sub_one hdpos.ne', abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  nlinarith [abs_nonneg (Px - hx)]

/-- **`|r − 1| ≤ 8ε/3`**. -/
theorem abs_r_sub_one_le_eight_thirds (hh : |hx| ≤ eps) (hP : |Px| ≤ eps)
    (heps : eps ≤ 1 / 4) : |(1 + Px) / (1 + hx) - 1| ≤ 8 * eps / 3 := by
  have hd := three_quarters_le hh heps
  have hdpos : (0 : ℝ) < 1 + hx := by linarith
  have hA := abs_A_le hh hP
  have hlow : 1 - eps ≤ 1 + hx := by linarith [(abs_le.mp hh).1]
  have heps0 : 0 ≤ eps := (abs_nonneg _).trans hh
  rw [ratio_sub_one hdpos.ne', abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  nlinarith

/-- **`|r − 1| ≤ 2a/3`** for `ε ≤ a/4`, `a < 1`. -/
theorem abs_r_sub_one_le_two_a_div_three (hh : |hx| ≤ eps) (hP : |Px| ≤ eps)
    (heps : eps ≤ a / 4) (ha1 : a < 1) : |(1 + Px) / (1 + hx) - 1| ≤ 2 * a / 3 := by
  have h14 : eps ≤ 1 / 4 := by linarith
  have := abs_r_sub_one_le_eight_thirds hh hP h14
  linarith

/-- **`(r − 1)² ≤ 4ε|Ah|`**. -/
theorem sq_r_sub_one_le (hh : |hx| ≤ eps) (hP : |Px| ≤ eps) (heps : eps ≤ 1 / 4) :
    ((1 + Px) / (1 + hx) - 1) ^ 2 ≤ 4 * eps * |Px - hx| := by
  have hb1 := abs_r_sub_one_le_eight_thirds hh hP heps
  have hb2 := abs_r_sub_one_le_four_thirds (Px := Px) hh heps
  have heps0 : 0 ≤ eps := (abs_nonneg _).trans hh
  set q := (1 + Px) / (1 + hx) - 1
  have hsq : q ^ 2 = |q| * |q| := by rw [abs_mul_abs_self]; ring
  rw [hsq]
  have hA : (0 : ℝ) ≤ |Px - hx| := abs_nonneg _
  calc |q| * |q| ≤ (8 * eps / 3) * (4 / 3 * |Px - hx|) :=
        mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
    _ ≤ 4 * eps * |Px - hx| := by nlinarith

variable {w W g2 M3 : ℝ} {gd : ℝ → ℝ}

/-- **`ψ = g''(1) w Ah + e`, `|e| ≤ C₄ε|Ah|`**, pointwise, with `ψ = g'(r)·w/(1+h)`. -/
theorem psi_expansion (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (hw : |w| ≤ W)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : |hx| ≤ eps) (hP : |Px| ≤ eps) (heps : eps ≤ a / 4) (ha1 : a < 1) :
    |gd ((1 + Px) / (1 + hx)) * (w / (1 + hx)) - g2 * (w * (Px - hx))|
      ≤ C4 W g2 M3 * eps * |Px - hx| := by
  have heps4 : eps ≤ 1 / 4 := by linarith
  have heps0 : 0 ≤ eps := (abs_nonneg _).trans hh
  have hden := three_quarters_le hh heps4
  have hdpos : (0 : ℝ) < 1 + hx := by linarith
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hw
  set r : ℝ := (1 + Px) / (1 + hx) with hrdef
  set Ay : ℝ := Px - hx with hAdef
  have hA0 : (0 : ℝ) ≤ |Ay| := abs_nonneg _
  have hr1 : r - 1 = Ay / (1 + hx) := ratio_sub_one hdpos.ne'
  have e1 : (r - 1) * (w / (1 + hx)) = w * Ay * (1 / (1 + hx) ^ 2) := by
    rw [hr1]; field_simp
  have hmain : gd r * (w / (1 + hx)) - g2 * (w * Ay)
      = (gd r - g2 * (r - 1)) * (w / (1 + hx))
        + g2 * (w * Ay * (1 / (1 + hx) ^ 2 - 1)) := by
    linear_combination g2 * e1
  have hra : |r - 1| ≤ a := by
    have := abs_r_sub_one_le_two_a_div_three hh hP heps ha1
    have ha0 : 0 ≤ a := by linarith
    linarith
  have htay : |gd r - g2 * (r - 1)| ≤ M3 / 2 * (4 * eps * |Ay|) := by
    refine le_trans (htaylor r hra) ?_
    have := sq_r_sub_one_le hh hP heps4
    nlinarith
  have hfrac : |w / (1 + hx)| ≤ W * (4 / 3) := by
    rw [abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
    nlinarith [abs_nonneg w]
  have hb1 : |(gd r - g2 * (r - 1)) * (w / (1 + hx))|
      ≤ (M3 / 2 * (4 * eps * |Ay|)) * (W * (4 / 3)) := by
    rw [abs_mul]
    exact mul_le_mul htay hfrac (abs_nonneg _) (by positivity)
  have hb2 : |g2 * (w * Ay * (1 / (1 + hx) ^ 2 - 1))| ≤ g2 * (W * (|Ay| * (4 * eps))) := by
    rw [abs_mul, abs_of_nonneg hg2, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ hg2
    have hX : |1 / (1 + hx) ^ 2 - 1| ≤ 4 * eps := abs_inv_sq_sub_one_le hh heps4
    have t1 : |w| * |Ay| ≤ W * |Ay| := mul_le_mul_of_nonneg_right hw (abs_nonneg Ay)
    calc |w| * |Ay| * |1 / (1 + hx) ^ 2 - 1|
        ≤ W * |Ay| * (4 * eps) :=
          mul_le_mul t1 hX (abs_nonneg _) (mul_nonneg hW0 (abs_nonneg Ay))
      _ = W * (|Ay| * (4 * eps)) := by ring
  rw [hmain]
  refine le_trans (abs_add_le _ _) ?_
  have hkey : (0 : ℝ) ≤ M3 * W * eps * |Ay| := by positivity
  simp only [C4]
  nlinarith [hb1, hb2, hkey]

/-- **`|(r − 1)ψ| ≤ C₅ε|Ah|`**, pointwise. -/
theorem r_sub_one_mul_psi_le (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (hw : |w| ≤ W)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : |hx| ≤ eps) (hP : |Px| ≤ eps) (heps : eps ≤ a / 4) (ha1 : a < 1) :
    |((1 + Px) / (1 + hx) - 1) * (gd ((1 + Px) / (1 + hx)) * (w / (1 + hx)))|
      ≤ C5 g2 a M3 W * eps * |Px - hx| := by
  have heps4 : eps ≤ 1 / 4 := by linarith
  have heps0 : 0 ≤ eps := (abs_nonneg _).trans hh
  have hden := three_quarters_le hh heps4
  have hdpos : (0 : ℝ) < 1 + hx := by linarith
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hw
  have ha0 : 0 ≤ a := by linarith
  set r : ℝ := (1 + Px) / (1 + hx) with hrdef
  set Ay : ℝ := Px - hx with hAdef
  have hA0 : (0 : ℝ) ≤ |Ay| := abs_nonneg _
  have hra : |r - 1| ≤ a := by
    have := abs_r_sub_one_le_two_a_div_three hh hP heps ha1
    linarith
  have hCg0 : 0 ≤ Cg g2 a M3 := by simp only [Cg]; positivity
  have hgd : |gd r| ≤ Cg g2 a M3 * |r - 1| := abs_gd_le_Cg hg2 hM3 htaylor hra
  have hfrac : |w / (1 + hx)| ≤ W * (4 / 3) := by
    rw [abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
    nlinarith [abs_nonneg w]
  have hsq : (r - 1) ^ 2 ≤ 4 * eps * |Ay| := sq_r_sub_one_le hh hP heps4
  have hstep : |r - 1| * (|gd r| * |w / (1 + hx)|)
      ≤ |r - 1| * (Cg g2 a M3 * |r - 1| * (W * (4 / 3))) := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul hgd hfrac (abs_nonneg _) (by positivity)
  have habs : |r - 1| * |r - 1| = (r - 1) ^ 2 := by rw [abs_mul_abs_self]; ring
  rw [abs_mul, abs_mul]
  refine le_trans hstep ?_
  simp only [C5]
  nlinarith [hsq, hCg0, hW0, habs, mul_nonneg hCg0 hW0]

end Scalar

/-! ### The paper's extension `g̃` of a generator that is `C³` on the window only -/

section Extension

/-- **The paper's `g̃`** (proof of `theo:gd_diffusion_full`, second bullet): equal to `g` on
`[1−a, 1+a]`, and affine with slope `g'(1∓a)` to either side, `g'` a derivative of `g` within the
window (one-sided at `1 ± a`). -/
noncomputable def gext (g gd : ℝ → ℝ) (a : ℝ) (y : ℝ) : ℝ :=
  if y < 1 - a then g (1 - a) + gd (1 - a) * (y - (1 - a))
  else if 1 + a < y then g (1 + a) + gd (1 + a) * (y - (1 + a)) else g y

/-- The derivative of `g̃`: `g'` on the window, constant to either side. -/
noncomputable def gext' (gd : ℝ → ℝ) (a : ℝ) (y : ℝ) : ℝ := gd (clamp (1 - a) (1 + a) y)

variable {g gd : ℝ → ℝ} {a : ℝ}

theorem gext_of_mem {y : ℝ} (hy : y ∈ Icc (1 - a) (1 + a)) : gext g gd a y = g y := by
  unfold gext
  rw [if_neg (not_lt.mpr hy.1), if_neg (not_lt.mpr hy.2)]

theorem gext'_of_mem {y : ℝ} (hy : y ∈ Icc (1 - a) (1 + a)) : gext' gd a y = gd y := by
  unfold gext'; rw [clamp_of_mem hy]

/-- A derivative of `g` within the window is continuous on it (`C³` on the window). -/
theorem continuousOn_gd (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) :
    ContinuousOn gd (winC3 a) :=
  (hC3.continuousOn_derivWithin (uniqueDiffOn_winC3 ha) (by norm_num)).congr fun y hy =>
    ((hgd y hy).derivWithin (uniqueDiffOn_winC3 ha y hy)).symm

theorem continuous_gext' (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) :
    Continuous (gext' gd a) :=
  (continuousOn_gd ha hC3 hgd).comp_continuous (continuous_clamp _ _) (clamp_mem (by linarith))

/-- **`g̃` is differentiable everywhere, with derivative `gext'`** (continuous,
`continuous_gext'`) — what `first_variation_general` asks of a generator. -/
theorem hasDerivAt_gext (ha : 0 < a)
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) (y : ℝ) :
    HasDerivAt (gext g gd a) (gext' gd a y) y := by
  have hcd : 1 - a < 1 + a := by linarith
  set c := 1 - a with hc
  set d := 1 + a with hd
  have hL : ∀ z : ℝ, HasDerivAt (fun y => g c + gd c * (y - c)) (gd c) z := fun z => by
    simpa using ((hasDerivAt_id z).sub_const c).const_mul (gd c) |>.const_add (g c)
  have hR : ∀ z : ℝ, HasDerivAt (fun y => g d + gd d * (y - d)) (gd d) z := fun z => by
    simpa using ((hasDerivAt_id z).sub_const d).const_mul (gd d) |>.const_add (g d)
  have hcmem : c ∈ Icc c d := ⟨le_rfl, hcd.le⟩
  have hdmem : d ∈ Icc c d := ⟨hcd.le, le_rfl⟩
  have e_lo : ∀ z, z ≤ c → gext g gd a z = g c + gd c * (z - c) := by
    intro z hz
    rcases hz.lt_or_eq with hz | hz
    · unfold gext; rw [if_pos hz]
    · subst hz; rw [gext_of_mem hcmem]; ring
  have e_hi : ∀ z, d ≤ z → gext g gd a z = g d + gd d * (z - d) := by
    intro z hz
    rcases hz.lt_or_eq with hz | hz
    · unfold gext; rw [if_neg (by linarith), if_pos hz]
    · subst hz; rw [gext_of_mem hdmem]; ring
  rcases lt_or_ge y c with hyc | hcy
  · -- left of the window
    have hcl : clamp c d y = c := by
      unfold clamp; rw [min_eq_left (by linarith), max_eq_left hyc.le]
    rw [show gext' gd a y = gd c by unfold gext'; rw [hcl]]
    refine (hL y).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hyc] with z hz using e_lo z (le_of_lt hz)
  rcases lt_or_ge d y with hdy | hyd
  · -- right of the window
    have hcl : clamp c d y = d := by
      unfold clamp; rw [min_eq_right hdy.le, max_eq_right hcd.le]
    rw [show gext' gd a y = gd d by unfold gext'; rw [hcl]]
    refine (hR y).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hdy] with z hz using e_hi z (le_of_lt hz)
  have hy : y ∈ Icc c d := ⟨hcy, hyd⟩
  rw [gext'_of_mem hy]
  rcases hcy.lt_or_eq with hcy' | hcy'
  · rcases hyd.lt_or_eq with hyd' | hyd'
    · -- interior
      refine ((hgd y hy).hasDerivAt (mem_nhds_winC3 ⟨hcy', hyd'⟩)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hcy' hyd'] with z hz using
        gext_of_mem ⟨hz.1.le, hz.2.le⟩
    · -- `y = 1 + a`
      subst hyd'
      have h1 : HasDerivWithinAt (gext g gd a) (gd d) (Iic d) d := by
        refine ((hgd d hdmem).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hcd)).congr_of_eventuallyEq
          ?_ (gext_of_mem hdmem)
        filter_upwards [Icc_mem_nhdsLE hcd] with z hz using gext_of_mem hz
      have h2 : HasDerivWithinAt (gext g gd a) (gd d) (Ici d) d :=
        (hR d).hasDerivWithinAt.congr (fun z hz => e_hi z hz) (e_hi d le_rfl)
      have := h1.union h2
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · -- `y = 1 − a`
    subst hcy'
    have h1 : HasDerivWithinAt (gext g gd a) (gd c) (Ici c) c := by
      refine ((hgd c hcmem).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hcd)).congr_of_eventuallyEq
        ?_ (gext_of_mem hcmem)
      filter_upwards [Icc_mem_nhdsGE hcd] with z hz using gext_of_mem hz
    have h2 : HasDerivWithinAt (gext g gd a) (gd c) (Iic c) c :=
      (hL c).hasDerivWithinAt.congr (fun z hz => e_lo z hz) (e_lo c le_rfl)
    have := h2.union h1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- `g̃'` still satisfies the Taylor bound of `g'`, the two agreeing on the window. -/
theorem taylor_gext' {g2 M3 : ℝ}
    (htay : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2) :
    ∀ y : ℝ, |y - 1| ≤ a → |gext' gd a y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2 := by
  intro y hy
  have := abs_le.mp hy
  rw [gext'_of_mem ⟨by linarith, by linarith⟩]
  exact htay y hy

end Extension

/-! ### The objects of `theo:gd_diffusion_full` on a standard Borel space -/

section Objects

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]

/-- **`P`, the density action of `T` on `L²(λ)`**, `h ↦ d((hλ)T)/dλ` — by `lem:adjoint`(3) the
function action of the `λ`-reversal `T^λ` (`IsInvariant.toReal_rnDeriv_comp`). -/
noncomputable def Pd (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam]
    (f : S → ℝ) : S → ℝ :=
  Core.General.funAct (reversal T lam) f

/-- `A := P − I`. -/
noncomputable def Aop (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam]
    (h : S → ℝ) : S → ℝ :=
  fun x => Pd T lam h x - h x

/-- `A† = P† − I`, `P†` the function action of `T` (`lem:adjoint`(3)). -/
noncomputable def Adag (T : Kernel S S) (f : S → ℝ) : S → ℝ := fun x => Core.General.funAct T f x - f x

/-- **`H := g''(1) A† M_w A`**, the linearization of the gradient field. -/
noncomputable def linHess (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S)
    [IsFiniteMeasure lam] (w : S → ℝ) (g2 : ℝ) (h : S → ℝ) : S → ℝ :=
  fun x => g2 * Adag T (fun y => w y * Aop T lam h y) x

end Objects

section MeasureObjects

variable {S : Type*} [MeasurableSpace S]

/-- The flow `μ := (1+h)λ`. -/
noncomputable def flowOf (lam : Measure S) (h : S → ℝ) : Measure S :=
  lam.withDensity fun x => ENNReal.ofReal (1 + h x)

/-- The training measure `ν := wλ`. -/
noncomputable def wMeas (lam : Measure S) (w : S → ℝ) : Measure S :=
  lam.withDensity fun x => ENNReal.ofReal (w x)

/-- **The paper's `ψ := g'(r)·w/(1+h)`**, `r` the ratio of `μ = (1+h)λ`, `gd` standing for `g'`. -/
noncomputable def psiP (T : Kernel S S) (lam : Measure S) (gd : ℝ → ℝ) (w h : S → ℝ) : S → ℝ :=
  fun x => gd (FirstVariation.ratio T (flowOf lam h) x) * (w x / (1 + h x))

/-- **The paper's gradient density `D := P†ψ − rψ`** against `λ`. -/
noncomputable def gradD (T : Kernel S S) (lam : Measure S) (gd : ℝ → ℝ) (w h : S → ℝ) :
    S → ℝ :=
  fun x => Core.General.funAct T (psiP T lam gd w h) x -
    FirstVariation.ratio T (flowOf lam h) x * psiP T lam gd w h x

variable {lam : Measure S} [IsFiniteMeasure lam] {h : S → ℝ} {eps : ℝ}

theorem flowOf_isFinite (hhm : Measurable h) (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) :
    IsFiniteMeasure (flowOf lam h) := by
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact (Integrable.of_bound (measurable_const.add hhm).aestronglyMeasurable (1 + eps)
    (by filter_upwards [hh] with x hx
        rw [Real.norm_eq_abs]
        calc |1 + h x| ≤ |1| + |h x| := abs_add_le _ _
          _ ≤ 1 + eps := by rw [abs_one]; linarith)).2

theorem wMeas_isFinite {w : S → ℝ} (hwm : Measurable w) {W : ℝ}
    (hwb : ∀ᵐ x ∂lam, |w x| ≤ W) : IsFiniteMeasure (wMeas lam w) :=
  isFiniteMeasure_withDensity_ofReal
    (Integrable.of_bound hwm.aestronglyMeasurable W (by simpa [Real.norm_eq_abs] using hwb)).2

omit [IsFiniteMeasure lam] in
theorem flowOf_ac : flowOf lam h ≪ lam := withDensity_absolutelyContinuous _ _

omit [IsFiniteMeasure lam] in
theorem ac_flowOf (hhm : Measurable h) (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (heps : eps ≤ 1 / 4) :
    lam ≪ flowOf lam h := by
  refine withDensity_absolutelyContinuous' (measurable_const.add hhm).ennreal_ofReal.aemeasurable ?_
  filter_upwards [hh] with x hx
  have := three_quarters_le hx heps
  exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'

theorem toReal_rnDeriv_flowOf (hhm : Measurable h) (hh : ∀ᵐ x ∂lam, |h x| ≤ eps)
    (heps : eps ≤ 1 / 4) :
    (fun x => ((flowOf lam h).rnDeriv lam x).toReal) =ᵐ[lam] fun x => 1 + h x := by
  filter_upwards [Measure.rnDeriv_withDensity lam (measurable_const.add hhm).ennreal_ofReal, hh]
    with x hx hhx
  rw [flowOf] at *
  rw [hx, ENNReal.toReal_ofReal (by linarith [three_quarters_le hhx heps])]

end MeasureObjects

section Ratio

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsFiniteMeasure lam]
  {h : S → ℝ} {eps : ℝ}

/-- `|Ph| ≤ ε` `λ`-a.e. when `|h| ≤ ε` `λ`-a.e.: `P` averages against `T^λ(x → ·)`. -/
theorem abs_Pd_le (hinv : IsInvariant T lam) (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) :
    ∀ᵐ x ∂lam, |Pd T lam h x| ≤ eps := by
  filter_upwards [hinv.isInvariant_reversal.ae_ae hh] with x hx
  have := norm_integral_le_of_norm_le_const (μ := reversal T lam x) (f := h) (C := eps)
    (by simpa [Real.norm_eq_abs] using hx)
  simpa [Pd, Core.General.funAct, Real.norm_eq_abs] using this

/-- **`P` is the density action `h ↦ d((hλ)T)/dλ`** of the paper, on signed integrable densities:
`Pd T lam f` agrees `λ`-a.e. with the library's signed density action
`GFNBounds.Core.densityAction T lam f = d((f⁺λ)T)/dλ − d((f⁻λ)T)/dλ` (`lem:adjoint`(3)). -/
theorem Pd_eq_densityAction (hinv : IsInvariant T lam) {f : S → ℝ} (hf : Measurable f)
    (hfi : Integrable f lam) : Pd T lam f =ᵐ[lam] GFNBounds.Core.densityAction T lam f := by
  have hrev := hinv.isReversalPair_reversal
  have hR := hinv.isInvariant_reversal
  have part : ∀ φ : S → ℝ, Measurable φ → Integrable φ lam →
      (fun x => (GFNBounds.Core.bindDensity T lam (fun y => ENNReal.ofReal (φ y)) x).toReal)
        =ᵐ[lam] Core.General.funAct (reversal T lam) (fun y => max (φ y) 0) := by
    intro φ hφ hφi
    haveI := isFiniteMeasure_withDensity_ofReal (μ := lam) hφi.2
    have e1 := hrev.toReal_rnDeriv_comp (μ := lam.withDensity fun y => ENNReal.ofReal (φ y))
      (withDensity_absolutelyContinuous _ _)
    have e2 : (fun y => ((lam.withDensity fun y => ENNReal.ofReal (φ y)).rnDeriv lam y).toReal)
        =ᵐ[lam] fun y => max (φ y) 0 := by
      filter_upwards [Measure.rnDeriv_withDensity lam hφ.ennreal_ofReal] with y hy
      rw [hy, ENNReal.toReal_ofReal']
    filter_upwards [e1, hR.funAct_congr e2] with x h1 h2
    rw [← h2, ← h1]
    rfl
  have hint : ∀ᵐ x ∂lam, Integrable f (reversal T lam x) := by
    have hm : Measurable fun x => ∫⁻ y, ‖f y‖ₑ ∂(reversal T lam x) :=
      hf.enorm.lintegral_kernel
    have hfin : ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(reversal T lam x) ∂lam ≠ ⊤ := by
      rw [← Measure.lintegral_bind (reversal T lam).aemeasurable hf.enorm.aemeasurable]
      rw [show lam.bind (reversal T lam) = reversal T lam ∘ₘ lam from rfl, hR]
      exact hfi.2.ne
    filter_upwards [ae_lt_top hm hfin] with x hx
    exact ⟨hf.aestronglyMeasurable, hx⟩
  filter_upwards [part f hf hfi, part (fun y => -f y) hf.neg hfi.neg, hint] with x h1 h2 hx
  simp only [GFNBounds.Core.densityAction]
  rw [h1, h2]
  simp only [Pd, Core.General.funAct]
  rw [← integral_sub hx.pos_part hx.neg_part]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rcases le_total 0 (f y) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- **`P†` is the `L²(λ)`-adjoint of `P`** (`lem:adjoint`(3)): `⟪v ∣ Pu⟫_λ = ⟪P†v ∣ u⟫_λ` with
`P† = ` the function action of `T` (`Core.General.funAct T`), which is how `Adag` reads it. -/
theorem Pd_adjoint (hinv : IsInvariant T lam) {u v : S → ℝ} (hv : MemLp v 2 lam)
    (hu : MemLp u 2 lam) :
    ∫ x, v x * Pd T lam u x ∂lam = ∫ x, Core.General.funAct T v x * u x ∂lam :=
  hinv.integral_mul_funAct_reversal hv hu

/-- `P(1 + h) = 1 + Ph` `λ`-a.e. -/
theorem Pd_one_add (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) :
    ∀ᵐ x ∂lam, Pd T lam (fun y => 1 + h y) x = 1 + Pd T lam h x := by
  filter_upwards [hinv.isInvariant_reversal.ae_ae hh] with x hx
  have hi : Integrable h (reversal T lam x) :=
    Integrable.of_bound hhm.aestronglyMeasurable eps (by simpa [Real.norm_eq_abs] using hx)
  simp only [Pd, Core.General.funAct]
  rw [integral_add (integrable_const 1) hi]
  simp

/-- **`theo:gd_diffusion_full`: the ratio of `μ = (1+h)λ` is `r = (1+Ph)/(1+h)`**, `λ`-a.e.
(first bullet of the proof). -/
theorem ratio_flowOf (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (heps : eps ≤ 1 / 4) :
    FirstVariation.ratio T (flowOf lam h) =ᵐ[lam] fun x => (1 + Pd T lam h x) / (1 + h x) := by
  haveI := flowOf_isFinite (lam := lam) hhm hh
  have hμl : flowOf lam h ≪ lam := flowOf_ac
  have hlμ : lam ≪ flowOf lam h := ac_flowOf hhm hh heps
  have hTμ : T ∘ₘ flowOf lam h ≪ lam := hinv.comp_absolutelyContinuous hμl
  have e1 := Measure.rnDeriv_eq_div (μ := T ∘ₘ flowOf lam h) (ν := flowOf lam h) (ξ := lam)
    hTμ hμl
  have e2 := hinv.isReversalPair_reversal.toReal_rnDeriv_comp hμl
  have e3 := hinv.isInvariant_reversal.funAct_congr (toReal_rnDeriv_flowOf hhm hh heps)
  filter_upwards [hlμ.ae_le e1, e2, e3, Pd_one_add hinv hhm hh,
    toReal_rnDeriv_flowOf hhm hh heps] with x h1 h2 h3 h4 h5
  simp only [FirstVariation.ratio]
  rw [h1, ENNReal.toReal_div, h2, h3, h5]
  exact congrArg (· / (1 + h x)) h4

omit [StandardBorelSpace S] [Nonempty S] in
/-- **`dν/dμ = w/(1+h)`**, `λ`-a.e., for `ν = wλ`, `w ≥ 0`. -/
theorem toReal_rnDeriv_wMeas {w : S → ℝ} (hwm : Measurable w) (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x)
    {W : ℝ} (hwb : ∀ᵐ x ∂lam, |w x| ≤ W)
    (hhm : Measurable h) (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (heps : eps ≤ 1 / 4) :
    (fun x => ((wMeas lam w).rnDeriv (flowOf lam h) x).toReal) =ᵐ[lam]
      fun x => w x / (1 + h x) := by
  haveI := wMeas_isFinite (lam := lam) hwm hwb
  haveI := flowOf_isFinite (lam := lam) hhm hh
  have hμl : flowOf lam h ≪ lam := flowOf_ac
  have hlμ : lam ≪ flowOf lam h := ac_flowOf hhm hh heps
  have hνl : wMeas lam w ≪ lam := withDensity_absolutelyContinuous _ _
  have e1 := Measure.rnDeriv_eq_div (μ := wMeas lam w) (ν := flowOf lam h) (ξ := lam) hνl hμl
  filter_upwards [hlμ.ae_le e1, Measure.rnDeriv_withDensity lam hwm.ennreal_ofReal, hw0,
    toReal_rnDeriv_flowOf hhm hh heps] with x h1 h2 h3 h5
  rw [h1, ENNReal.toReal_div, h5]
  simp only [wMeas] at h2 ⊢
  rw [h2, ENNReal.toReal_ofReal h3]

end Ratio

/-! ### The ratio bounds and the gradient at `μ = (1+h)λ` -/

section Gradient

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsFiniteMeasure lam]
  {h w : S → ℝ} {eps a W : ℝ} {g gd : ℝ → ℝ}

/-- The pointwise data at a.e. `x`: `|h| ≤ ε`, `|Ph| ≤ ε`, `r = (1+Ph)/(1+h)`. -/
theorem ae_data (hinv : IsInvariant T lam) (hhm : Measurable h) (hh : ∀ᵐ x ∂lam, |h x| ≤ eps)
    (heps : eps ≤ 1 / 4) :
    ∀ᵐ x ∂lam, |h x| ≤ eps ∧ |Pd T lam h x| ≤ eps ∧
      FirstVariation.ratio T (flowOf lam h) x = (1 + Pd T lam h x) / (1 + h x) := by
  filter_upwards [hh, abs_Pd_le hinv hh, ratio_flowOf hinv hhm hh heps] with x h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **`eq:gd_ratio_bounds`**: `|r−1| ≤ (4/3)|Ah|`, `|r−1| ≤ 2a/3`, `|g'(r)| ≤ C_g|r−1|`, `λ`-a.e. -/
theorem gd_ratio_bounds (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (ha : 0 < a) (ha1 : a < 1) (heps : eps ≤ a / 4)
    (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) (hg'1 : deriv g 1 = 0)
    (hg2 : 0 ≤ deriv (deriv g) 1) :
    ∀ᵐ x ∂lam,
      |FirstVariation.ratio T (flowOf lam h) x - 1| ≤ 4 / 3 * |Aop T lam h x| ∧
      |FirstVariation.ratio T (flowOf lam h) x - 1| ≤ 2 * a / 3 ∧
      |gd (FirstVariation.ratio T (flowOf lam h) x)| ≤
        Cg (deriv (deriv g) 1) a (Gamma3W g a) * |FirstVariation.ratio T (flowOf lam h) x - 1| := by
  have heps4 : eps ≤ 1 / 4 := by linarith
  filter_upwards [ae_data hinv hhm hh heps4] with x ⟨h1, h2, h3⟩
  rw [h3]
  refine ⟨abs_r_sub_one_le_four_thirds h1 heps4, abs_r_sub_one_le_two_a_div_three h1 h2 heps ha1,
    ?_⟩
  have hr := abs_r_sub_one_le_two_a_div_three h1 h2 heps ha1
  exact abs_gd_le_Cg hg2 (Gamma3W_nonneg ha hC3) (taylor_bundle_of_C3On ha hC3 hgd hg'1)
    (by linarith)

/-- The ratio lies in `[1 − 2a/3, 1 + 2a/3]`, `μ`-a.e. -/
theorem ratio_window (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (ha1 : a < 1) (heps : eps ≤ a / 4) :
    ∀ᵐ x ∂(flowOf lam h), 1 - 2 * a / 3 ≤ FirstVariation.ratio T (flowOf lam h) x ∧
      FirstVariation.ratio T (flowOf lam h) x ≤ 1 + 2 * a / 3 := by
  have heps4 : eps ≤ 1 / 4 := by linarith
  refine flowOf_ac.ae_le ?_
  filter_upwards [ae_data hinv hhm hh heps4] with x ⟨h1, h2, h3⟩
  have := abs_le.mp (abs_r_sub_one_le_two_a_div_three h1 h2 heps ha1)
  rw [h3]
  constructor <;> linarith [this.1, this.2]

/-- `ψ` of `theo_first_variation_full` at `(g̃, ν = wλ, μ = (1+h)λ)` is the paper's
`g'(r)·w/(1+h)`, `λ`-a.e. -/
theorem psi_eq_psiP (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (ha1 : a < 1) (heps : eps ≤ a / 4)
    (hwm : Measurable w) (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwb : ∀ᵐ x ∂lam, |w x| ≤ W) :
    FirstVariation.psi T (gext' gd a) (wMeas lam w) (flowOf lam h) =ᵐ[lam]
      psiP T lam gd w h := by
  have heps4 : eps ≤ 1 / 4 := by linarith
  filter_upwards [ae_data hinv hhm hh heps4, toReal_rnDeriv_wMeas hwm hw0 hwb hhm hh heps4]
    with x ⟨h1, h2, h3⟩ h4
  have := abs_le.mp (abs_r_sub_one_le_two_a_div_three h1 h2 heps ha1)
  have hmem : FirstVariation.ratio T (flowOf lam h) x ∈ Icc (1 - a) (1 + a) := by
    rw [h3]; constructor <;> linarith [this.1, this.2]
  simp only [FirstVariation.psi, psiP]
  rw [gext'_of_mem hmem, h4]

/-- … and hence the gradient density `Tψ − rψ` is the paper's `D`, `λ`-a.e. -/
theorem gradDens_eq_gradD (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (ha1 : a < 1) (heps : eps ≤ a / 4)
    (hwm : Measurable w) (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwb : ∀ᵐ x ∂lam, |w x| ≤ W) :
    FirstVariation.gradDens T (gext' gd a) (wMeas lam w) (flowOf lam h) =ᵐ[lam]
      gradD T lam gd w h := by
  have hp := psi_eq_psiP (gd := gd) hinv hhm hh ha1 heps hwm hw0 hwb
  filter_upwards [hp, hinv.funAct_congr hp] with x h1 h2
  simp only [FirstVariation.gradDens, gradD]
  rw [h1, h2]

/-- Near `s = 0` the loss of `g` and of `g̃` agree along every bounded direction: the ratio of
`μ + sδ` stays in the window, where `g̃ = g`. -/
theorem loss_eventually_eq_gext (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (ha : 0 < a) (ha1 : a < 1) (heps : eps ≤ a / 4)
    (ν : Measure S) (hν : ν ≪ flowOf lam h) {u : S → ℝ} (hu : Measurable u) {C : ℝ}
    (hC : 0 ≤ C) (hub : ∀ᵐ x ∂(flowOf lam h), |u x| ≤ C) :
    ∀ᶠ s in 𝓝 (0 : ℝ), FirstVariation.loss T g ν (FirstVariation.perturb (flowOf lam h) u s) =
      FirstVariation.loss T (gext g gd a) ν (FirstVariation.perturb (flowOf lam h) u s) := by
  have heps4 : eps ≤ 1 / 4 := by linarith
  haveI := flowOf_isFinite (lam := lam) hhm hh
  have hw := ratio_window (T := T) hinv hhm hh ha1 heps
  filter_upwards [eventually_ratio_perturb_near (T := T) hu ha hC hub
    (by filter_upwards [hw] with x hx using hx.2)] with s hs
  unfold FirstVariation.loss
  refine integral_congr_ae ?_
  filter_upwards [hν.ae_le hs, hν.ae_le hw] with x hx hrx
  rw [abs_le] at hx
  rw [gext_of_mem ⟨by linarith [hrx.1, hx.1], by linarith [hrx.2, hx.2]⟩]

/-- **`theo:gd_diffusion_full`, the gradient clause**: `𝓛_{g,ν}` has at `μ = (1+h)λ` a gradient in
the sense of `theo_first_variation_full` (with `ν_G = λ`), of density `D = P†ψ − rψ` against `λ`,
`ψ = g'(r)·w/(1+h)`. Four clauses: (1) the signed measure `(T^λ − r)[ψλ]` has `λ`-density `D`,
setwise; (2) `D ∈ L²(λ)`; (3) `D` represents the derivative along every essentially bounded
direction `δ = uμ`, `⟨Dλ ∣ δ⟩_λ = ∫ D·(dδ/dλ) dλ`, `dδ/dλ = u(1+h)`; (4) uniquely in `L²(λ)`.
The hypotheses of `first_variation_general` are discharged for `g̃` inside the proof
(`ratio_window`: the ratio lies in `[1 − 2a/3, 1 + 2a/3]`). -/
theorem gd_gradient (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (ha : 0 < a) (ha1 : a < 1) (heps : eps ≤ a / 4)
    (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (hwm : Measurable w) (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwb : ∀ᵐ x ∂lam, |w x| ≤ W) :
    (∀ s : Set S, MeasurableSet s →
      (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (psiP T lam gd w h y)).real s -
        (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (-psiP T lam gd w h y)).real s -
        ∫ x in s, FirstVariation.ratio T (flowOf lam h) x * psiP T lam gd w h x ∂lam =
      ∫ x in s, gradD T lam gd w h x ∂lam) ∧
    MemLp (gradD T lam gd w h) 2 lam ∧
    (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂lam, |u x| ≤ C) →
      HasDerivAt (fun s => FirstVariation.loss T g (wMeas lam w)
          (FirstVariation.perturb (flowOf lam h) u s))
        (∫ x, gradD T lam gd w h x * (u x * (1 + h x)) ∂lam) 0) ∧
    (∀ D' : S → ℝ, MemLp D' 2 lam →
      (∀ u : S → ℝ, Measurable u → (∀ᵐ x ∂lam, |u x| ≤ 1 / 2) →
        HasDerivAt (fun s => FirstVariation.loss T g (wMeas lam w)
            (FirstVariation.perturb (flowOf lam h) u s))
          (∫ x, D' x * (u x * (1 + h x)) ∂lam) 0) →
      D' =ᵐ[lam] gradD T lam gd w h) := by
  have heps4 : eps ≤ 1 / 4 := by linarith
  haveI := flowOf_isFinite (lam := lam) hhm hh
  haveI := wMeas_isFinite (lam := lam) hwm hwb
  set μ := flowOf lam h with hμdef
  set ν := wMeas lam w with hνdef
  have hμl : μ ≪ lam := flowOf_ac
  have hlμ : lam ≪ μ := ac_flowOf hhm hh heps4
  have hνμ : ν ≪ μ := (withDensity_absolutelyContinuous _ _).trans hlμ
  have hwin := ratio_window (T := T) hinv hhm hh ha1 heps
  have hwnu : MemLp (fun x => (ν.rnDeriv μ x).toReal) ⊤ μ := by
    refine MemLp.of_bound (Measure.measurable_rnDeriv _ _).ennreal_toReal.aestronglyMeasurable
      (W * (4 / 3)) (hμl.ae_le ?_)
    filter_upwards [toReal_rnDeriv_wMeas hwm hw0 hwb hhm hh heps4, hwb, hh] with x h1 h2 h3
    rw [h1, Real.norm_eq_abs]
    have hd := three_quarters_le h3 heps4
    have hdp : (0 : ℝ) < 1 + h x := by linarith
    rw [abs_div, abs_of_pos hdp, div_le_iff₀ hdp]
    nlinarith [abs_nonneg (w x)]
  have ha' : 0 < 1 - 2 * a / 3 := by linarith
  have hab : 1 - 2 * a / 3 ≤ 1 + 2 * a / 3 := by linarith
  obtain ⟨c1, -, c3, c4, c5⟩ := first_variation_general (T := T) (ν := ν) hinv hμl hlμ ha' hab
    hwin hνμ hwnu (fun y _ => hasDerivAt_gext ha hgd y)
    (continuous_gext' ha hC3 hgd).continuousOn (nuG := lam) (Measure.AbsolutelyContinuous.refl _)
    (Measure.AbsolutelyContinuous.refl _)
  have hG := gradDens_eq_gradD (gd := gd) (T := T) hinv hhm hh ha1 heps hwm hw0 hwb
  have hP := psi_eq_psiP (gd := gd) (T := T) hinv hhm hh ha1 heps hwm hw0 hwb
  have hrn := toReal_rnDeriv_flowOf (lam := lam) hhm hh heps4
  have hval : ∀ D' : S → ℝ, ∀ u : S → ℝ,
      ∫ x, D' x * (u x * (μ.rnDeriv lam x).toReal) ∂lam = ∫ x, D' x * (u x * (1 + h x)) ∂lam :=
    fun D' u => integral_congr_ae (by filter_upwards [hrn] with x hx; rw [hx])
  refine ⟨fun s hs => ?_, c3.ae_eq hG, fun u hu C hub => ?_, fun D' hD' hrep => ?_⟩
  · have e1 : (lam.withDensity fun y => ENNReal.ofReal (psiP T lam gd w h y)) =
        lam.withDensity fun y => ENNReal.ofReal
          (FirstVariation.psi T (gext' gd a) ν μ y) :=
      withDensity_congr_ae (by filter_upwards [hP] with x hx; rw [hx])
    have e2 : (lam.withDensity fun y => ENNReal.ofReal (-psiP T lam gd w h y)) =
        lam.withDensity fun y => ENNReal.ofReal
          (-FirstVariation.psi T (gext' gd a) ν μ y) :=
      withDensity_congr_ae (by filter_upwards [hP] with x hx; rw [hx])
    have e3 : ∫ x in s, FirstVariation.ratio T μ x * psiP T lam gd w h x ∂lam =
        ∫ x in s, FirstVariation.ratio T μ x * FirstVariation.psi T (gext' gd a) ν μ x ∂lam :=
      integral_congr_ae (ae_restrict_of_ae (by filter_upwards [hP] with x hx; rw [hx]))
    have e4 : ∫ x in s, gradD T lam gd w h x ∂lam =
        ∫ x in s, FirstVariation.gradDens T (gext' gd a) ν μ x ∂lam :=
      integral_congr_ae (ae_restrict_of_ae (by filter_upwards [hG] with x hx; rw [hx]))
    rw [e1, e2, e3, e4]
    exact c1 s hs
  · have hub' : ∀ᵐ x ∂μ, |u x| ≤ max C 0 :=
      hμl.ae_le (by filter_upwards [hub] with x hx using hx.trans (le_max_left _ _))
    have key := c4 u hu (max C 0) hub'
    rw [hval] at key
    have hv : ∫ x, FirstVariation.gradDens T (gext' gd a) ν μ x * (u x * (1 + h x)) ∂lam =
        ∫ x, gradD T lam gd w h x * (u x * (1 + h x)) ∂lam :=
      integral_congr_ae (by filter_upwards [hG] with x hx; rw [hx])
    rw [hv] at key
    refine key.congr_of_eventuallyEq ?_
    exact loss_eventually_eq_gext (gd := gd) hinv hhm hh ha ha1 heps ν hνμ hu (le_max_right C 0) hub'
  · have := c5 D' hD' (fun u hu hub => ?_)
    · filter_upwards [this, hG] with x h1 h2; rw [h1, h2]
    · have hubl : ∀ᵐ x ∂lam, |u x| ≤ 1 / 2 := hlμ.ae_le hub
      have key := hrep u hu hubl
      rw [← hval] at key
      refine key.congr_of_eventuallyEq ?_
      filter_upwards [loss_eventually_eq_gext (g := g) (gd := gd) hinv hhm hh ha ha1 heps ν hνμ hu
        (by norm_num) hub] with s hs
      exact hs.symm

end Gradient

/-! ### `eq:linearized_flow`: the expansion of the gradient density -/

section Expansion

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsFiniteMeasure lam]
  {h w : S → ℝ} {eps a W : ℝ} {gd : ℝ → ℝ}

omit [StandardBorelSpace S] [Nonempty S] [IsFiniteMeasure lam] in
/-- A bounded measurable function stays bounded under the function action of `T`, `λ`-a.e.,
and is integrable against `T(x → ·)` for `λ`-a.e. `x`. -/
theorem ae_funAct_bound (hinv : IsInvariant T lam) {f : S → ℝ} (hf : Measurable f) {L : ℝ}
    (hfb : ∀ᵐ x ∂lam, |f x| ≤ L) :
    ∀ᵐ x ∂lam, Integrable f (T x) ∧ |Core.General.funAct T f x| ≤ L := by
  filter_upwards [hinv.ae_ae hfb] with x hx
  refine ⟨Integrable.of_bound hf.aestronglyMeasurable L (by simpa [Real.norm_eq_abs] using hx), ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := T x) (f := f) (C := L)
    (by simpa [Real.norm_eq_abs] using hx)
  simpa [Real.norm_eq_abs, Core.General.funAct] using this

theorem measurable_Pd (f : S → ℝ) (hf : Measurable f) : Measurable (Pd T lam f) :=
  hf.stronglyMeasurable.integral_kernel.measurable

theorem measurable_Aop (hhm : Measurable h) : Measurable (Aop T lam h) :=
  (measurable_Pd h hhm).sub hhm

omit [StandardBorelSpace S] [Nonempty S] [IsMarkovKernel T] [IsFiniteMeasure lam] in
theorem measurable_psiP (hgdm : Measurable gd) (hhm : Measurable h) (hwm : Measurable w) :
    Measurable (psiP T lam gd w h) :=
  (hgdm.comp measurable_ratio).mul (hwm.div (measurable_const.add hhm))

/-- The pointwise data of the expansion: at `λ`-a.e. `x`, `ψ(x)` and `r(x)` are the scalar
expressions of `psi_expansion`, and `|w| ≤ W`. -/
theorem ae_data_psi (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (heps4 : eps ≤ 1 / 4) (hwb : ∀ᵐ x ∂lam, |w x| ≤ W) :
    ∀ᵐ x ∂lam, |h x| ≤ eps ∧ |Pd T lam h x| ≤ eps ∧ |w x| ≤ W ∧
      FirstVariation.ratio T (flowOf lam h) x = (1 + Pd T lam h x) / (1 + h x) ∧
      psiP T lam gd w h x =
        gd ((1 + Pd T lam h x) / (1 + h x)) * (w x / (1 + h x)) := by
  filter_upwards [ae_data hinv hhm hh heps4, hwb] with x ⟨h1, h2, h3⟩ h4
  exact ⟨h1, h2, h4, h3, by simp only [psiP]; rw [h3]⟩

/-- **`eq:linearized_flow`**, in `L²(λ)`: with `E := D − g''(1)A†M_wAh`,
`‖E‖_{L²(λ)} ≤ Kε‖(P−I)h‖_{L²(λ)}` and `‖(P−I)h‖_{L²(λ)} ≤ 2‖h‖_{L²(λ)}`, `K = 2C₄ + C₅` the
paper's constant at `Γ₃ = sup_{[1−a,1+a]}|g'''|` and `W ≥ ‖w‖_{L^∞}`. -/
theorem gd_expansion (hinv : IsInvariant T lam) (hhm : Measurable h)
    (hh : ∀ᵐ x ∂lam, |h x| ≤ eps) (ha1 : a < 1) (heps0 : 0 ≤ eps) (heps : eps ≤ a / 4)
    (hgdm : Measurable gd) {g2 M3 : ℝ} (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3)
    (htay : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hwm : Measurable w) (hwb : ∀ᵐ x ∂lam, |w x| ≤ W) (hW0 : 0 ≤ W) :
    eLpNorm (fun x => gradD T lam gd w h x - linHess T lam w g2 h x) 2 lam ≤
        ENNReal.ofReal (Kexp g2 a M3 W * eps) * eLpNorm (Aop T lam h) 2 lam ∧
    eLpNorm (Aop T lam h) 2 lam ≤ 2 * eLpNorm h 2 lam := by
  have heps4 : eps ≤ 1 / 4 := by linarith
  have ha0 : 0 ≤ a := by linarith
  set ψ := psiP T lam gd w h with hψ
  set Ah := Aop T lam h with hAh
  set e : S → ℝ := fun y => ψ y - g2 * (w y * Ah y) with he
  set r := FirstVariation.ratio T (flowOf lam h)
  have hψm : Measurable ψ := measurable_psiP hgdm hhm hwm
  have hAm : Measurable Ah := measurable_Aop hhm
  have hem : Measurable e := hψm.sub (measurable_const.mul (hwm.mul hAm))
  have hrm : Measurable r := measurable_ratio
  have hdata := ae_data_psi (gd := gd) hinv hhm hh heps4 hwb
  -- pointwise bounds
  have hbe : ∀ᵐ x ∂lam, |e x| ≤ C4 W g2 M3 * eps * |Ah x| := by
    filter_upwards [hdata] with x ⟨h1, h2, h3, _, h5⟩
    simp only [he, hψ, hAh, Aop]
    rw [h5]
    exact psi_expansion (hg2) hM3 h3 htay h1 h2 heps ha1
  have hbr : ∀ᵐ x ∂lam, |(r x - 1) * ψ x| ≤ C5 g2 a M3 W * eps * |Ah x| := by
    filter_upwards [hdata] with x ⟨h1, h2, h3, h4, h5⟩
    simp only [hψ, hAh, Aop]
    rw [h5, show r x = _ from h4]
    exact r_sub_one_mul_psi_le hg2 hM3 h3 htay h1 h2 heps ha1
  -- bounds making `ψ` and `w·Ah` integrable along `T`
  have hψb : ∀ᵐ x ∂lam, |ψ x| ≤ Cg g2 a M3 * 1 * (W * (4 / 3)) := by
    filter_upwards [hdata] with x ⟨h1, h2, h3, _, h5⟩
    rw [hψ, h5, abs_mul]
    have hr := abs_r_sub_one_le_two_a_div_three h1 h2 heps ha1
    have hgd := abs_gd_le_Cg hg2 hM3 htay (y := (1 + Pd T lam h x) / (1 + h x)) (by linarith)
    have hd := three_quarters_le h1 heps4
    have hdp : (0 : ℝ) < 1 + h x := by linarith
    have hfrac : |w x / (1 + h x)| ≤ W * (4 / 3) := by
      rw [abs_div, abs_of_pos hdp, div_le_iff₀ hdp]
      nlinarith [abs_nonneg (w x)]
    have hCg : 0 ≤ Cg g2 a M3 := by simp only [Cg]; positivity
    have hr1 : |(1 + Pd T lam h x) / (1 + h x) - 1| ≤ 1 := by linarith
    exact mul_le_mul (hgd.trans (mul_le_mul_of_nonneg_left hr1 hCg)) hfrac (abs_nonneg _)
      (by positivity)
  have hwAb : ∀ᵐ x ∂lam, |w x * Ah x| ≤ W * (2 * eps) := by
    filter_upwards [hdata] with x ⟨h1, h2, h3, _, _⟩
    rw [abs_mul]
    exact mul_le_mul h3 (abs_A_le h1 h2) (abs_nonneg _) hW0
  have hTψ := ae_funAct_bound hinv hψm hψb
  have hTw := ae_funAct_bound hinv (hwm.mul hAm) hwAb
  -- the identity `D − Hh = A†e − (r−1)ψ`
  have hsplit : (fun x => gradD T lam gd w h x - linHess T lam w g2 h x) =ᵐ[lam]
      fun x => Adag T e x - (r x - 1) * ψ x := by
    filter_upwards [hTψ, hTw] with x ⟨i1, _⟩ ⟨i2, _⟩
    have hlin : Core.General.funAct T e x =
        Core.General.funAct T ψ x - g2 * Core.General.funAct T (fun y => w y * Ah y) x := by
      simp only [Core.General.funAct, he]
      rw [integral_sub i1 (i2.const_mul g2), integral_const_mul]
    simp only [gradD, linHess, Adag, hlin]
    ring
  -- the three `L²` bounds
  have hE1 : eLpNorm e 2 lam ≤ ENNReal.ofReal (C4 W g2 M3 * eps) * eLpNorm Ah 2 lam :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by
      filter_upwards [hbe] with x hx
      simpa [Real.norm_eq_abs, mul_assoc] using hx) 2
  have hE2 : eLpNorm (fun x => (r x - 1) * ψ x) 2 lam ≤
      ENNReal.ofReal (C5 g2 a M3 W * eps) * eLpNorm Ah 2 lam :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by
      filter_upwards [hbr] with x hx
      simpa [Real.norm_eq_abs, mul_assoc] using hx) 2
  have hAdag : eLpNorm (Adag T e) 2 lam ≤ 2 * eLpNorm e 2 lam := by
    have h1 := eLpNorm_sub_le (p := 2) (μ := lam)
      (f := Core.General.funAct T e) (g := e)
      (hem.stronglyMeasurable.integral_kernel.aestronglyMeasurable) hem.aestronglyMeasurable
      (by norm_num)
    have h2 := hinv.eLpNorm_funAct_le hem.aestronglyMeasurable (p := 2) (by norm_num)
    calc eLpNorm (Adag T e) 2 lam = eLpNorm (Core.General.funAct T e - e) 2 lam := rfl
      _ ≤ eLpNorm (Core.General.funAct T e) 2 lam + eLpNorm e 2 lam := h1
      _ ≤ eLpNorm e 2 lam + eLpNorm e 2 lam := by gcongr
      _ = 2 * eLpNorm e 2 lam := by rw [two_mul]
  have hC40 : 0 ≤ C4 W g2 M3 * eps := by simp only [C4]; positivity
  have hC50 : 0 ≤ C5 g2 a M3 W * eps := by simp only [C5, Cg]; positivity
  refine ⟨?_, ?_⟩
  · rw [eLpNorm_congr_ae hsplit]
    have h1 := eLpNorm_sub_le (p := 2) (μ := lam) (f := Adag T e)
      (g := fun x => (r x - 1) * ψ x)
      ((hem.stronglyMeasurable.integral_kernel.measurable.sub hem).aestronglyMeasurable)
      (((hrm.sub measurable_const).mul hψm).aestronglyMeasurable) (by norm_num)
    calc eLpNorm (fun x => Adag T e x - (r x - 1) * ψ x) 2 lam
        ≤ eLpNorm (Adag T e) 2 lam + eLpNorm (fun x => (r x - 1) * ψ x) 2 lam := h1
      _ ≤ 2 * (ENNReal.ofReal (C4 W g2 M3 * eps) * eLpNorm Ah 2 lam) +
            ENNReal.ofReal (C5 g2 a M3 W * eps) * eLpNorm Ah 2 lam := by
          gcongr
          exact hAdag.trans (by gcongr)
      _ = ENNReal.ofReal (Kexp g2 a M3 W * eps) * eLpNorm Ah 2 lam := by
          rw [← mul_assoc, ← add_mul]
          congr 1
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) hC50]
          congr 1
          simp only [Kexp]; ring
  · have hPm := measurable_Pd (T := T) (lam := lam) h hhm
    have h1 := eLpNorm_sub_le (p := 2) (μ := lam) (f := Pd T lam h) (g := h)
      hPm.aestronglyMeasurable hhm.aestronglyMeasurable (by norm_num)
    have h2 := hinv.isInvariant_reversal.eLpNorm_funAct_le hhm.aestronglyMeasurable (p := 2)
      (by norm_num)
    calc eLpNorm Ah 2 lam = eLpNorm (Pd T lam h - h) 2 lam := rfl
      _ ≤ eLpNorm (Pd T lam h) 2 lam + eLpNorm h 2 lam := h1
      _ ≤ eLpNorm h 2 lam + eLpNorm h 2 lam := by gcongr; exact h2
      _ = 2 * eLpNorm h 2 lam := by rw [two_mul]

end Expansion

/-! ### The linearization: `H` is linear, it is the only linear part of `D`, and the reversible case -/

section Linearization

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsFiniteMeasure lam]

/-- `I − P`. -/
noncomputable def IminusP (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S)
    [IsFiniteMeasure lam] (f : S → ℝ) : S → ℝ :=
  fun x => f x - Pd T lam f x

omit [StandardBorelSpace S] [Nonempty S] [IsMarkovKernel T] [IsFiniteMeasure lam] in
theorem funAct_const_mul (A : Kernel S S) (c : ℝ) (f : S → ℝ) :
    Core.General.funAct A (fun y => c * f y) = fun x => c * Core.General.funAct A f x := by
  funext x; simp only [Core.General.funAct, integral_const_mul]

theorem Aop_const_mul (c : ℝ) (f : S → ℝ) :
    Aop T lam (fun y => c * f y) = fun x => c * Aop T lam f x := by
  funext x
  simp only [Aop, Pd, funAct_const_mul]
  ring

/-- **`H` is linear** (homogeneity, exactly and not only a.e.). -/
theorem linHess_const_mul (w : S → ℝ) (g2 c : ℝ) (f : S → ℝ) :
    linHess T lam w g2 (fun y => c * f y) = fun x => c * linHess T lam w g2 f x := by
  funext x
  have e : (fun y => w y * Aop T lam (fun y => c * f y) y) =
      fun y => c * (w y * Aop T lam f y) := by
    funext y; rw [Aop_const_mul]; ring
  show g2 * (Core.General.funAct T (fun y => w y * Aop T lam (fun y => c * f y) y) x
      - w x * Aop T lam (fun y => c * f y) x) =
    c * (g2 * (Core.General.funAct T (fun y => w y * Aop T lam f y) x - w x * Aop T lam f x))
  rw [e, funAct_const_mul, Aop_const_mul]
  ring

/-- For `T` reversible with respect to `λ` (`λ ⊗ T = T ⊗ λ`), `P` and the function action of `T`
agree `λ`-a.e.: the uniqueness in `lem:adjoint`(1) gives `T^λ = T`. -/
theorem Pd_eq_funAct_of_reversible (hrev : IsReversalPair lam T T) :
    ∀ᵐ x ∂lam, ∀ f : S → ℝ, Pd T lam f x = Core.General.funAct T f x := by
  have hinv : IsInvariant T lam := hrev.isInvariant
  filter_upwards [hinv.ae_eq_reversal hrev] with x hx f
  simp only [Pd, Core.General.funAct, hx]

/-- **`theo:gd_diffusion_full`, the "in particular"**: for `w ≡ 1` and `T` reversible,
`H = g''(1)(I − P)²`, `λ`-a.e. -/
theorem linHess_reversible (hrev : IsReversalPair lam T T) (g2 : ℝ) (f : S → ℝ) :
    linHess T lam (fun _ => 1) g2 f =ᵐ[lam]
      fun x => g2 * IminusP T lam (IminusP T lam f) x := by
  filter_upwards [Pd_eq_funAct_of_reversible hrev] with x hx
  have e : IminusP T lam f = fun y => -Aop T lam f y := by
    funext y; simp only [IminusP, Aop]; ring
  have hneg : Core.General.funAct T (fun y => -Aop T lam f y) x =
      -Core.General.funAct T (Aop T lam f) x := by
    simp only [Core.General.funAct, integral_neg]
  simp only [linHess, Adag, one_mul]
  rw [show IminusP T lam (IminusP T lam f) x
      = IminusP T lam f x - Pd T lam (IminusP T lam f) x from rfl, hx, e, hneg]
  ring

/-- **`theo:gd_diffusion_full`: each eigenmode `Pφ = βφ` is an eigenmode of `H`** (`w ≡ 1`,
`T` reversible), with
eigenvalue `g''(1)(1 − β)²`, `λ`-a.e. -/
theorem linHess_eigen (hrev : IsReversalPair lam T T) (g2 β : ℝ) {φ : S → ℝ}
    (heig : Pd T lam φ =ᵐ[lam] fun x => β * φ x) :
    linHess T lam (fun _ => 1) g2 φ =ᵐ[lam] fun x => g2 * (1 - β) ^ 2 * φ x := by
  have hinv : IsInvariant T lam := hrev.isInvariant
  have hA : Aop T lam φ =ᵐ[lam] fun x => (β - 1) * φ x := by
    filter_upwards [heig] with x hx
    simp only [Aop, hx]; ring
  have hA' : (fun y => (1 : ℝ) * Aop T lam φ y) =ᵐ[lam] fun x => (β - 1) * φ x := by
    filter_upwards [hA] with x hx; rw [hx, one_mul]
  filter_upwards [hinv.funAct_congr hA', hA, Pd_eq_funAct_of_reversible hrev, heig]
    with x h1 h2 h3 h4
  simp only [linHess, Adag]
  rw [h1, funAct_const_mul]
  beta_reduce
  rw [← h3 φ, h4, h2, one_mul]
  ring

/-- **`theo:gd_diffusion_full`: each eigenmode decays at rate `g''(1)(1 − β)²`**: `h_t := e^{−g''(1)(1−β)²t}φ` solves the
linearized flow `ḣ = −Hh` (`w ≡ 1`), pointwise in `t` and `λ`-a.e. in the state. -/
theorem eigenmode_decay (hrev : IsReversalPair lam T T) (g2 β : ℝ) {φ : S → ℝ}
    (heig : Pd T lam φ =ᵐ[lam] fun x => β * φ x) (t : ℝ) :
    ∀ᵐ x ∂lam, HasDerivAt (fun t => Real.exp (-(g2 * (1 - β) ^ 2) * t) * φ x)
      (-linHess T lam (fun _ => 1) g2
        (fun y => Real.exp (-(g2 * (1 - β) ^ 2) * t) * φ y) x) t := by
  filter_upwards [linHess_eigen hrev g2 β heig] with x hx
  rw [linHess_const_mul]
  beta_reduce
  rw [hx]
  have hd : HasDerivAt (fun t => -(g2 * (1 - β) ^ 2) * t) (-(g2 * (1 - β) ^ 2)) t := by
    simpa using (hasDerivAt_id t).const_mul (-(g2 * (1 - β) ^ 2))
  have := ((Real.hasDerivAt_exp _).comp t hd).mul_const (φ x)
  refine this.congr_deriv ?_
  ring

end Linearization

/-! ### "The linearization of the gradient flow at `λ` is `ḣ = −g''(1)A†M_wAh`" -/

section Linearized

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsFiniteMeasure lam]
  {w : S → ℝ} {a W : ℝ} {gd : ℝ → ℝ}

omit [StandardBorelSpace S] [Nonempty S] [IsMarkovKernel T] [IsFiniteMeasure lam] in
theorem measurable_gradD (hgdm : Measurable gd) {h : S → ℝ} (hhm : Measurable h)
    (hwm : Measurable w) : Measurable (gradD T lam gd w h) :=
  (measurable_psiP hgdm hhm hwm).stronglyMeasurable.integral_kernel.measurable.sub
    (measurable_ratio.mul (measurable_psiP hgdm hhm hwm))

theorem measurable_linHess {h : S → ℝ} (hhm : Measurable h) (hwm : Measurable w) (g2 : ℝ) :
    Measurable (linHess T lam w g2 h) := by
  have hf : Measurable fun y => w y * Aop T lam h y := hwm.mul (measurable_Aop hhm)
  exact measurable_const.mul (hf.stronglyMeasurable.integral_kernel.measurable.sub hf)

/-- **`theo:gd_diffusion_full`, the flow sentence: the balanced flow is a zero of the field**:
`D(0) = 0`, `λ`-a.e. -/
theorem gradD_zero (hinv : IsInvariant T lam) (ha : 0 < a) (ha1 : a < 1)
    (hgdm : Measurable gd) {g2 M3 : ℝ} (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3)
    (htay : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hwm : Measurable w) (hwb : ∀ᵐ x ∂lam, |w x| ≤ W) (hW0 : 0 ≤ W) :
    gradD T lam gd w (fun _ => 0) =ᵐ[lam] fun _ => 0 := by
  have hA : Aop T lam (fun _ : S => (0 : ℝ)) = fun _ => 0 := by
    funext x; simp [Aop, Pd, Core.General.funAct]
  have hH : linHess T lam w g2 (fun _ : S => (0 : ℝ)) = fun _ => 0 := by
    funext x; simp [linHess, Adag, hA, Core.General.funAct]
  obtain ⟨h1, -⟩ := gd_expansion (T := T) (gd := gd) hinv measurable_const
    (Filter.Eventually.of_forall fun _ => by simp : ∀ᵐ x ∂lam, |(fun _ : S => (0 : ℝ)) x| ≤ 0)
    ha1 le_rfl (by linarith) hgdm hg2 hM3 htay hwm hwb hW0
  rw [hH, hA] at h1
  have hz : eLpNorm (gradD T lam gd w (fun _ => 0)) 2 lam = 0 := by
    simpa using h1
  exact (eLpNorm_eq_zero_iff (measurable_gradD hgdm measurable_const hwm).aestronglyMeasurable
    two_ne_zero).1 hz

/-- **`theo:gd_diffusion_full`, the flow sentence: the part of the field linear in `h` is `−H`,
uniquely.** `D(h) − Hh = o(‖h‖_{L²(λ)})` as
`‖h‖_{L^∞(λ)} → 0` (`gd_expansion`, with the explicit rate `2K‖h‖_{L^∞}`), and `H` is linear
(`linHess_const_mul`). Conversely, any map `H'` that is homogeneous and satisfies
`‖D(h) − H'h‖_{L²(λ)} ≤ c(δ)‖h‖_{L²(λ)}` whenever `‖h‖_{L^∞(λ)} ≤ δ`, for some `c(δ) → 0`, agrees
with `H` on every bounded measurable `f`, `λ`-a.e. So `ḣ = −Hh` is *the* linearization at `λ`
of the flow `ḣ = −D(h)`, which is the gradient flow `μ̇ = −∇^λ𝓛(μ)` read on `μ = (1+h)λ`. -/
theorem linearization_unique (hinv : IsInvariant T lam) (ha : 0 < a) (ha1 : a < 1)
    (hgdm : Measurable gd) {g2 M3 : ℝ} (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3)
    (htay : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hwm : Measurable w) (hwb : ∀ᵐ x ∂lam, |w x| ≤ W) (hW0 : 0 ≤ W)
    (H' : (S → ℝ) → S → ℝ)
    (hH'lin : ∀ f : S → ℝ, ∀ c : ℝ, H' (fun y => c * f y) =ᵐ[lam] fun x => c * H' f x)
    (hH'm : ∀ f : S → ℝ, Measurable f → AEStronglyMeasurable (H' f) lam)
    {c : ℝ → ℝ} (hc : Tendsto c (𝓝[>] 0) (𝓝 0))
    (hH' : ∀ f : S → ℝ, Measurable f → ∀ δ : ℝ, 0 < δ → δ ≤ a / 4 →
      (∀ᵐ x ∂lam, |f x| ≤ δ) →
      eLpNorm (fun x => gradD T lam gd w f x - H' f x) 2 lam ≤
        ENNReal.ofReal (c δ) * eLpNorm f 2 lam)
    {f : S → ℝ} (hf : Measurable f) {L : ℝ} (hL : 0 < L) (hfb : ∀ᵐ x ∂lam, |f x| ≤ L) :
    H' f =ᵐ[lam] linHess T lam w g2 f := by
  set K := Kexp g2 a M3 W
  set F : S → ℝ := fun x => H' f x - linHess T lam w g2 f x with hF
  have hFm : AEStronglyMeasurable F lam :=
    (hH'm f hf).sub (measurable_linHess hf hwm g2).aestronglyMeasurable
  have hN : eLpNorm f 2 lam ≠ ⊤ :=
    (MemLp.of_bound hf.aestronglyMeasurable L (by simpa [Real.norm_eq_abs] using hfb)).2.ne
  -- the bound at scale `t`
  have key : ∀ t : ℝ, 0 < t → t * L ≤ a / 4 →
      eLpNorm F 2 lam ≤ (ENNReal.ofReal (2 * K * (t * L)) + ENNReal.ofReal (c (t * L))) *
        eLpNorm f 2 lam := by
    intro t ht htL
    set ft : S → ℝ := fun y => t * f y with hft
    have hftm : Measurable ft := measurable_const.mul hf
    have hftb : ∀ᵐ x ∂lam, |ft x| ≤ t * L := by
      filter_upwards [hfb] with x hx
      rw [hft, abs_mul, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left hx ht.le
    obtain ⟨e1, e2⟩ := gd_expansion (T := T) (gd := gd) hinv hftm hftb ha1
      (by positivity) htL hgdm hg2 hM3 htay hwm hwb hW0
    have e3 := hH' ft hftm (t * L) (by positivity) htL hftb
    have hnft : eLpNorm ft 2 lam = ENNReal.ofReal t * eLpNorm f 2 lam := by
      have : ft = t • f := rfl
      rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos ht]
    have hK0 : 0 ≤ K := by
      simp only [K, Kexp, C4, C5, Cg]
      have := ha.le
      positivity
    -- `t·F = (D − H'ft) … ` rearranged
    have hid : (fun x => t * F x) =ᵐ[lam]
        fun x => (gradD T lam gd w ft x - linHess T lam w g2 ft x) -
          (gradD T lam gd w ft x - H' ft x) := by
      filter_upwards [hH'lin f t] with x hx
      rw [hft, hx, linHess_const_mul]
      simp only [hF]
      ring
    have hDm := measurable_gradD (T := T) (lam := lam) hgdm hftm hwm
    have hsub := eLpNorm_sub_le (p := 2) (μ := lam)
      (f := fun x => gradD T lam gd w ft x - linHess T lam w g2 ft x)
      (g := fun x => gradD T lam gd w ft x - H' ft x)
      ((hDm.sub (measurable_linHess hftm hwm g2)).aestronglyMeasurable)
      (hDm.aestronglyMeasurable.sub (hH'm ft hftm)) (by norm_num)
    have htF : eLpNorm (fun x => t * F x) 2 lam = ENNReal.ofReal t * eLpNorm F 2 lam := by
      have : (fun x => t * F x) = t • F := rfl
      rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos ht]
    have hmain : ENNReal.ofReal t * eLpNorm F 2 lam ≤ ENNReal.ofReal t *
        ((ENNReal.ofReal (2 * K * (t * L)) + ENNReal.ofReal (c (t * L))) * eLpNorm f 2 lam) := by
      rw [← htF, eLpNorm_congr_ae hid]
      refine hsub.trans ?_
      calc eLpNorm (fun x => gradD T lam gd w ft x - linHess T lam w g2 ft x) 2 lam +
            eLpNorm (fun x => gradD T lam gd w ft x - H' ft x) 2 lam
          ≤ ENNReal.ofReal (K * (t * L)) * (2 * eLpNorm ft 2 lam) +
              ENNReal.ofReal (c (t * L)) * eLpNorm ft 2 lam := by
            gcongr
            exact e1.trans (by gcongr)
        _ = ENNReal.ofReal t *
            ((ENNReal.ofReal (2 * K * (t * L)) + ENNReal.ofReal (c (t * L))) *
              eLpNorm f 2 lam) := by
            rw [hnft, show (2 * K * (t * L)) = 2 * (K * (t * L)) by ring,
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            simp only [ENNReal.ofReal_ofNat]
            ring
    exact (ENNReal.mul_le_mul_iff_right (by simpa using ht) ENNReal.ofReal_ne_top).1 hmain
  -- let `t → 0⁺`
  have htL : Tendsto (fun t : ℝ => t * L) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_mul_const L).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact mul_pos ht hL
  have hlim : Tendsto (fun t : ℝ =>
      (ENNReal.ofReal (2 * K * (t * L)) + ENNReal.ofReal (c (t * L))) * eLpNorm f 2 lam)
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 2 * K * (t * L)) (𝓝[>] 0) (𝓝 0) := by
      have := (((continuous_const_mul (2 * K)).comp (continuous_mul_const L)).tendsto
        (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun t : ℝ => c (t * L)) (𝓝[>] 0) (𝓝 0) :=
      hc.comp htL
    have h3 := ENNReal.Tendsto.mul_const
      ((ENNReal.tendsto_ofReal h1).add (ENNReal.tendsto_ofReal h2)) (Or.inr hN)
    simpa using h3
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), eLpNorm F 2 lam ≤
      (ENNReal.ofReal (2 * K * (t * L)) + ENNReal.ofReal (c (t * L))) * eLpNorm f 2 lam := by
    have hpos : (0 : ℝ) < a / 4 / L := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos] with t ht
    refine key t ht.1 ?_
    have := ht.2
    rw [lt_div_iff₀ hL] at this
    exact this.le
  have hz : eLpNorm F 2 lam = 0 := le_zero_iff.1 (ge_of_tendsto hlim hev)
  have := (eLpNorm_eq_zero_iff hFm two_ne_zero).1 hz
  filter_upwards [this] with x hx
  simp only [hF, Pi.zero_apply] at hx
  linarith

end Linearized

/-! ### `theo:gd_diffusion_full`, assembled with the paper's hypotheses -/

section Paper

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S} [IsFiniteMeasure lam]

omit [StandardBorelSpace S] [Nonempty S] [IsFiniteMeasure lam] in
/-- `|w| ≤ ‖w‖_{L^∞(λ)}` `λ`-a.e. -/
theorem ae_abs_le_eLpNorm_top {w : S → ℝ} (hw : MemLp w ⊤ lam) :
    ∀ᵐ x ∂lam, |w x| ≤ (eLpNorm w ⊤ lam).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (f := w) (μ := lam)] with x hx
  rw [Real.enorm_eq_ofReal_abs] at hx
  rw [eLpNorm_exponent_top]
  have hfin : eLpNormEssSup w lam ≠ ⊤ := by
    have := hw.2; rw [eLpNorm_exponent_top] at this; exact this.ne
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hx

/-- On `‖f‖_{L^∞} ≤ a/4` the field only reads `g'` inside the window, so `D` is unchanged when
`g'` is replaced by its clamped (continuous, measurable) version `g̃'`. -/
theorem gradD_eq_gext' (hinv : IsInvariant T lam) {gd : ℝ → ℝ} {a δ : ℝ} (ha1 : a < 1)
    (hδ : δ ≤ a / 4) (w : S → ℝ) {f : S → ℝ} (hfm : Measurable f)
    (hf : ∀ᵐ x ∂lam, |f x| ≤ δ) :
    gradD T lam gd w f =ᵐ[lam] gradD T lam (gext' gd a) w f := by
  have hδ4 : δ ≤ 1 / 4 := by linarith
  have hp : psiP T lam gd w f =ᵐ[lam] psiP T lam (gext' gd a) w f := by
    filter_upwards [ae_data hinv hfm hf hδ4] with x ⟨h1, h2, h3⟩
    have := abs_le.mp (abs_r_sub_one_le_two_a_div_three h1 h2 hδ ha1)
    have hmem : FirstVariation.ratio T (flowOf lam f) x ∈ Icc (1 - a) (1 + a) := by
      rw [h3]; constructor <;> linarith [this.1, this.2]
    simp only [psiP]
    rw [gext'_of_mem hmem]
  filter_upwards [hp, hinv.funAct_congr hp] with x h1 h2
  simp only [gradD]
  rw [h1, h2]

/-- **`theo:gd_diffusion_full`, on a standard Borel space, with the paper's hypotheses.**
`T` Markov with `λ` non-zero, finite, `T`-invariant (`lem:adjoint`); `w ≥ 0` in `L^∞(λ)`,
`ν = wλ`; `a ∈ (0,1)`, `g` `C³` on `[1−a, 1+a]` (`ContDiffOn`, one-sided at `1 ± a`) with
`g'(1) = 0 < g''(1)` and `g(1) = 0`, `g'` (`gd`) its derivative within the window;
`Γ₃ = sup_{[1−a,1+a]}|g'''|` (`Gamma3W`) and `‖w‖_{L^∞}` enter `K = 2C₄ + C₅` (`Kexp`). For every
`ε ∈ (0, a/4]` and every (measurable representative of) `h` with `‖h‖_{L^∞(λ)} ≤ ε`, writing
`μ = (1+h)λ`, `r = d(μT)/dμ`, `ψ = g'(r)w/(1+h)`, `D = P†ψ − rψ`, `H = g''(1)A†M_wA`:

1. `r = (1+Ph)/(1+h)` `λ`-a.e.;
2. `eq:gd_ratio_bounds`, `λ`-a.e.;
3. the gradient clause of `gd_gradient` (the density `D`, `L²`, representation, uniqueness);
4. `eq:linearized_flow`: `‖D − Hh‖ ≤ Kε‖(P−I)h‖ ≤ 2Kε‖h‖`;

and, for the flow sentence and the "in particular":

5. `D(0) = 0` and `H` is the unique homogeneous `H'` with `‖D(h) − H'h‖ ≤ c(δ)‖h‖` on
   `‖h‖_{L^∞} ≤ δ`, `c(δ) → 0` (`linearization_unique`);
6. for `T` reversible (`λ ⊗ T = T ⊗ λ`) and `w ≡ 1`: `H = g''(1)(I − P)²`, every eigenmode
   `Pφ = βφ` has `Hφ = g''(1)(1−β)²φ`, and `e^{−g''(1)(1−β)²t}φ` solves `ḣ = −Hh`. -/
theorem theo_gd_diffusion_full (_hlam0 : lam ≠ 0) (hinv : IsInvariant T lam)
    {w : S → ℝ} (hwm : Measurable w) (hw0 : ∀ᵐ x ∂lam, 0 ≤ w x) (hwinf : MemLp w ⊤ lam)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {g gd : ℝ → ℝ}
    (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) (_hg1 : g 1 = 0)
    (hg'1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1) :
    (∀ eps : ℝ, 0 < eps → eps ≤ a / 4 → ∀ h : S → ℝ, Measurable h →
      (∀ᵐ x ∂lam, |h x| ≤ eps) →
      -- (1) the ratio
      FirstVariation.ratio T (flowOf lam h) =ᵐ[lam] (fun x => (1 + Pd T lam h x) / (1 + h x)) ∧
      -- (2) `eq:gd_ratio_bounds`
      (∀ᵐ x ∂lam,
        |FirstVariation.ratio T (flowOf lam h) x - 1| ≤ 4 / 3 * |Aop T lam h x| ∧
        |FirstVariation.ratio T (flowOf lam h) x - 1| ≤ 2 * a / 3 ∧
        |gd (FirstVariation.ratio T (flowOf lam h) x)| ≤
          Cg (deriv (deriv g) 1) a (Gamma3W g a) *
            |FirstVariation.ratio T (flowOf lam h) x - 1|) ∧
      -- (3) the gradient, of density `D = P†ψ − rψ`
      (∀ s : Set S, MeasurableSet s →
        (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (psiP T lam gd w h y)).real s -
          (reversal T lam ∘ₘ lam.withDensity fun y => ENNReal.ofReal (-psiP T lam gd w h y)).real
            s -
          ∫ x in s, FirstVariation.ratio T (flowOf lam h) x * psiP T lam gd w h x ∂lam =
        ∫ x in s, gradD T lam gd w h x ∂lam) ∧
      MemLp (gradD T lam gd w h) 2 lam ∧
      (∀ u : S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ x ∂lam, |u x| ≤ C) →
        HasDerivAt (fun s => FirstVariation.loss T g (wMeas lam w)
            (FirstVariation.perturb (flowOf lam h) u s))
          (∫ x, gradD T lam gd w h x * (u x * (1 + h x)) ∂lam) 0) ∧
      (∀ D' : S → ℝ, MemLp D' 2 lam →
        (∀ u : S → ℝ, Measurable u → (∀ᵐ x ∂lam, |u x| ≤ 1 / 2) →
          HasDerivAt (fun s => FirstVariation.loss T g (wMeas lam w)
              (FirstVariation.perturb (flowOf lam h) u s))
            (∫ x, D' x * (u x * (1 + h x)) ∂lam) 0) →
        D' =ᵐ[lam] gradD T lam gd w h) ∧
      -- (4) `eq:linearized_flow`
      eLpNorm (fun x => gradD T lam gd w h x - linHess T lam w (deriv (deriv g) 1) h x) 2 lam ≤
          ENNReal.ofReal (Kexp (deriv (deriv g) 1) a (Gamma3W g a) (eLpNorm w ⊤ lam).toReal *
            eps) * eLpNorm (Aop T lam h) 2 lam ∧
      eLpNorm (Aop T lam h) 2 lam ≤ 2 * eLpNorm h 2 lam) ∧
    -- (5) the linearization of the flow at `λ` is `ḣ = −Hh`
    gradD T lam gd w (fun _ => 0) =ᵐ[lam] (fun _ => 0) ∧
    (∀ H' : (S → ℝ) → S → ℝ,
      (∀ f : S → ℝ, ∀ c : ℝ, H' (fun y => c * f y) =ᵐ[lam] fun x => c * H' f x) →
      (∀ f : S → ℝ, Measurable f → AEStronglyMeasurable (H' f) lam) →
      ∀ c : ℝ → ℝ, Tendsto c (𝓝[>] 0) (𝓝 0) →
      (∀ f : S → ℝ, Measurable f → ∀ δ : ℝ, 0 < δ → δ ≤ a / 4 → (∀ᵐ x ∂lam, |f x| ≤ δ) →
        eLpNorm (fun x => gradD T lam gd w f x - H' f x) 2 lam ≤
          ENNReal.ofReal (c δ) * eLpNorm f 2 lam) →
      ∀ f : S → ℝ, Measurable f → ∀ L : ℝ, 0 < L → (∀ᵐ x ∂lam, |f x| ≤ L) →
        H' f =ᵐ[lam] linHess T lam w (deriv (deriv g) 1) f) ∧
    -- (6) the reversible case, `w ≡ 1`
    (IsReversalPair lam T T →
      (∀ f : S → ℝ, linHess T lam (fun _ => 1) (deriv (deriv g) 1) f =ᵐ[lam]
        fun x => deriv (deriv g) 1 * IminusP T lam (IminusP T lam f) x) ∧
      (∀ (β : ℝ) (φ : S → ℝ), Pd T lam φ =ᵐ[lam] (fun x => β * φ x) →
        linHess T lam (fun _ => 1) (deriv (deriv g) 1) φ =ᵐ[lam]
          (fun x => deriv (deriv g) 1 * (1 - β) ^ 2 * φ x) ∧
        ∀ t : ℝ, ∀ᵐ x ∂lam,
          HasDerivAt (fun t => Real.exp (-(deriv (deriv g) 1 * (1 - β) ^ 2) * t) * φ x)
            (-linHess T lam (fun _ => 1) (deriv (deriv g) 1)
              (fun y => Real.exp (-(deriv (deriv g) 1 * (1 - β) ^ 2) * t) * φ y) x) t)) := by
  have hwb := ae_abs_le_eLpNorm_top hwinf
  have hW0 : 0 ≤ (eLpNorm w ⊤ lam).toReal := ENNReal.toReal_nonneg
  have hM3 : 0 ≤ Gamma3W g a := Gamma3W_nonneg ha hC3
  have htay := taylor_gext' (gd := gd) (taylor_bundle_of_C3On ha hC3 hgd hg'1)
  have hgdm : Measurable (gext' gd a) := (continuous_gext' ha hC3 hgd).measurable
  refine ⟨fun eps heps0 heps h hhm hh => ?_, ?_, fun H' hlin hm c hc hH' f hf L hL hfb => ?_,
    fun hrev => ⟨fun f => linHess_reversible hrev _ f, fun β φ heig =>
      ⟨linHess_eigen hrev _ β heig, fun t => eigenmode_decay hrev _ β heig t⟩⟩⟩
  · have heps4 : eps ≤ 1 / 4 := by linarith
    obtain ⟨c1, c2, c3, c4⟩ := gd_gradient (g := g) hinv hhm hh ha ha1 heps hC3 hgd hwm hw0 hwb
    obtain ⟨e1, e2⟩ := gd_expansion (gd := gext' gd a) hinv hhm hh ha1 heps0.le heps hgdm
      hg2.le hM3 htay hwm hwb hW0
    have hc : (fun x => gradD T lam (gext' gd a) w h x -
        linHess T lam w (deriv (deriv g) 1) h x) =ᵐ[lam]
        fun x => gradD T lam gd w h x - linHess T lam w (deriv (deriv g) 1) h x := by
      filter_upwards [gradD_eq_gext' (gd := gd) hinv ha1 heps w hhm hh] with x hx
      rw [hx]
    rw [eLpNorm_congr_ae hc] at e1
    exact ⟨ratio_flowOf hinv hhm hh heps4,
      gd_ratio_bounds hinv hhm hh ha ha1 heps hC3 hgd hg'1 hg2.le, c1, c2, c3, c4, e1, e2⟩
  · have h0 := gradD_zero (T := T) hinv ha ha1 hgdm hg2.le hM3 htay hwm hwb hW0
    filter_upwards [gradD_eq_gext' (gd := gd) hinv ha1 (le_refl _ |>.trans (by linarith :
        (0 : ℝ) ≤ a / 4)) w measurable_const
      (Filter.Eventually.of_forall fun _ => by simp : ∀ᵐ x ∂lam, |(fun _ : S => (0 : ℝ)) x| ≤ 0),
      h0] with x h1 h2
    rw [h1, h2]
  · refine linearization_unique hinv ha ha1 hgdm hg2.le hM3 htay hwm hwb hW0 H' hlin hm hc
      (fun f hf δ hδ0 hδ hfδ => ?_) hf hL hfb
    have hc : (fun x => gradD T lam (gext' gd a) w f x - H' f x) =ᵐ[lam]
        fun x => gradD T lam gd w f x - H' f x := by
      filter_upwards [gradD_eq_gext' (gd := gd) hinv ha1 hδ w hf hfδ] with x hx
      rw [hx]
    rw [eLpNorm_congr_ae hc]
    exact hH' f hf δ hδ0 hδ hfδ

end Paper

/-! ### `cor:db_gradient`: the DB gradient as the lifted FM gradient on `(𝒮², λ₂, K₂)` -/

section DB

open GFNBounds.Balance.LiftGeneral

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {pb : Kernel S S} [IsMarkovKernel pb] {lam : Measure S} [IsFiniteMeasure lam]

/-- **The DB loss with frozen backward policy** (`prop:db_lift`):
`𝓛_DB(μ) = ∫ g(F(ds')π_←(s'→ds) / F(ds)π_→^μ(s→ds')) dν̂`, `F = m₁μ`. The denominator
`F ⊗ π_→^μ` *is* `μ` (the disintegration), so the ratio is `d(π_← ⊗ F)/dμ`; `dbLoss_eq_condKernel`
restores the paper's form for every disintegration `π_→^μ`. -/
noncomputable def dbLoss (pb : Kernel S S) (g : ℝ → ℝ) (nu μ : Measure (S × S)) : ℝ :=
  ∫ p, g ((LiftGeneral.edgeMeasure pb μ.fst).rnDeriv μ p).toReal ∂nu

omit [StandardBorelSpace S] [Nonempty S] [IsMarkovKernel pb] [IsFiniteMeasure lam] in
/-- `dbLoss` in the paper's form: `F(ds')π_←(s'→ds)` over `F(ds)π_→^μ(s→ds')`, for every
disintegration `μ = F ⊗ π_→^μ`. -/
theorem dbLoss_eq_condKernel (g : ℝ → ℝ) (nu μ : Measure (S × S)) [IsFiniteMeasure μ]
    (pf : Kernel S S) [μ.IsCondKernel pf] :
    dbLoss pb g nu μ = ∫ p, g ((LiftGeneral.edgeMeasure pb μ.fst).rnDeriv (μ.fst ⊗ₘ pf) p).toReal ∂nu := by
  unfold dbLoss; rw [Measure.disintegrate μ pf]

omit [StandardBorelSpace S] [Nonempty S] [IsFiniteMeasure lam] in
/-- **`prop:db_lift`, read as a loss**: the DB loss is the balance loss of the edge lift `K₂`,
`𝓛_DB = 𝓛_{g,ν̂}` for `T = K₂`, at every s-finite edge flow. -/
theorem dbLoss_eq_loss (g : ℝ → ℝ) (nu μ : Measure (S × S)) [SFinite μ] :
    dbLoss pb g nu μ = FirstVariation.loss (LiftGeneral.edgeLift pb) g nu μ := by
  unfold dbLoss FirstVariation.loss FirstVariation.ratio
  rw [show LiftGeneral.edgeLift pb ∘ₘ μ = μ.bind (LiftGeneral.edgeLift pb) from rfl, LiftGeneral.bind_edgeLift]

/-- `K₂^{λ₂}`, the `λ₂`-reversal of `K₂`, is the forward edge kernel of `lem:lift_wellposed`,
`(s,s') ↦ (s', π_→^λ(s'))`, `λ₂`-a.e. -/
theorem reversal_edgeLift_ae (hinv : IsInvariant pb lam) :
    LiftGeneral.edgeLiftDual (pb†lam) =ᵐ[LiftGeneral.edgeMeasure pb lam] reversal (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) := by
  have hinv2 : IsInvariant (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) :=
    LiftGeneral.edgeMeasure_invariant pb lam hinv
  exact hinv2.ae_eq_reversal (LiftGeneral.edgeLift_duality pb (pb†lam) lam (LiftGeneral.isReversal_posterior pb lam hinv))

/-- **`cor:db_gradient`, on a standard Borel `𝒮`.** Under the hypotheses of
`theo:first_variation_full` on `(𝒮², λ₂, K₂)` — `μ ∈ 𝓜²(λ₂)`, `μ ∼ λ₂`, `μK₂ ≪ μ`,
`r̂ = d(μK₂)/dμ ∈ [a, b] ⊂ (0,∞)` `μ`-a.e., `ν̂` finite with `dν̂/dμ ∈ L^∞(μ)`, `g` `C¹` on `ℝ₊*`
with locally Lipschitz `g'` — the DB loss with frozen backward policy has, in `⟨·∣·⟩_{λ₂}`, the
gradient `(K₂^{λ₂} − r̂)[g'(r̂)(dν̂/dμ)λ₂]`, `K₂^{λ₂} = (s,s') ↦ (s', π_→^λ(s'))` the forward edge
kernel of `lem:lift_wellposed`: (1) that signed measure has `λ₂`-density `h = K₂ψ − r̂ψ`,
`ψ = g'(r̂)dν̂/dμ`; (2) `h ∈ L²(λ₂)`; (3) `h` represents the derivative of `𝓛_DB` along every
bounded direction; (4) uniquely. -/
theorem cor_db_gradient (hlam0 : lam ≠ 0) (hinv : IsInvariant pb lam) {μ : Measure (S × S)}
    (hμ2 : InM2 (LiftGeneral.edgeMeasure pb lam) μ) (hlμ : LiftGeneral.edgeMeasure pb lam ≪ μ)
    (hac : LiftGeneral.edgeLift pb ∘ₘ μ ≪ μ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ᵐ p ∂μ, a ≤ FirstVariation.ratio (LiftGeneral.edgeLift pb) μ p ∧
      FirstVariation.ratio (LiftGeneral.edgeLift pb) μ p ≤ b)
    {nu : Measure (S × S)} [IsFiniteMeasure nu] (hνμ : nu ≪ μ)
    (hw : MemLp (fun p => (nu.rnDeriv μ p).toReal) ⊤ μ)
    {g g' : ℝ → ℝ} (hgd : ∀ y, 0 < y → HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Ioi 0)) (hg'L : LocallyLipschitzOn (Ioi 0) g') :
    (∀ s : Set (S × S), MeasurableSet s →
      (LiftGeneral.edgeLiftDual (pb†lam) ∘ₘ (LiftGeneral.edgeMeasure pb lam).withDensity
          fun y => ENNReal.ofReal (FirstVariation.psi (LiftGeneral.edgeLift pb) g' nu μ y)).real s -
        (LiftGeneral.edgeLiftDual (pb†lam) ∘ₘ (LiftGeneral.edgeMeasure pb lam).withDensity
          fun y => ENNReal.ofReal (-FirstVariation.psi (LiftGeneral.edgeLift pb) g' nu μ y)).real s -
        ∫ p in s, FirstVariation.ratio (LiftGeneral.edgeLift pb) μ p *
          FirstVariation.psi (LiftGeneral.edgeLift pb) g' nu μ p ∂(LiftGeneral.edgeMeasure pb lam) =
      ∫ p in s, FirstVariation.gradDens (LiftGeneral.edgeLift pb) g' nu μ p ∂(LiftGeneral.edgeMeasure pb lam)) ∧
    MemLp (FirstVariation.gradDens (LiftGeneral.edgeLift pb) g' nu μ) 2 (LiftGeneral.edgeMeasure pb lam) ∧
    (∀ u : S × S → ℝ, Measurable u → ∀ C : ℝ, (∀ᵐ p ∂μ, |u p| ≤ C) →
      HasDerivAt (fun s => dbLoss pb g nu (FirstVariation.perturb μ u s))
        (∫ p, FirstVariation.gradDens (LiftGeneral.edgeLift pb) g' nu μ p *
          (u p * (μ.rnDeriv (LiftGeneral.edgeMeasure pb lam) p).toReal) ∂(LiftGeneral.edgeMeasure pb lam)) 0) ∧
    (∀ h' : S × S → ℝ, MemLp h' 2 (LiftGeneral.edgeMeasure pb lam) →
      (∀ u : S × S → ℝ, Measurable u → (∀ᵐ p ∂μ, |u p| ≤ 1 / 2) →
        HasDerivAt (fun s => dbLoss pb g nu (FirstVariation.perturb μ u s))
          (∫ p, h' p * (u p * (μ.rnDeriv (LiftGeneral.edgeMeasure pb lam) p).toReal)
            ∂(LiftGeneral.edgeMeasure pb lam)) 0) →
      h' =ᵐ[LiftGeneral.edgeMeasure pb lam] FirstVariation.gradDens (LiftGeneral.edgeLift pb) g' nu μ) := by
  haveI : IsFiniteMeasure μ := hμ2.1
  have hinv2 : IsInvariant (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) :=
    LiftGeneral.edgeMeasure_invariant pb lam hinv
  have hlam2 : LiftGeneral.edgeMeasure pb lam ≠ 0 := by
    intro h0
    apply hlam0
    rw [← Measure.measure_univ_eq_zero, ← LiftGeneral.edgeMeasure_univ pb lam, h0, Measure.coe_zero,
      Pi.zero_apply]
  obtain ⟨c1, -, c3, c4, c5, -⟩ := theo_first_variation_full hlam2 hinv2 hμ2 hlμ hac ha hab hr
    hνμ hw hgd hg'c hg'L (nuG := LiftGeneral.edgeMeasure pb lam) (Measure.AbsolutelyContinuous.refl _)
    (Measure.AbsolutelyContinuous.refl _)
  have hrev := reversal_edgeLift_ae hinv
  have hloss : ∀ u : S × S → ℝ, (fun s => dbLoss pb g nu (FirstVariation.perturb μ u s)) =
      fun s => FirstVariation.loss (LiftGeneral.edgeLift pb) g nu (FirstVariation.perturb μ u s) :=
    fun u => funext fun s => by
      haveI : SFinite (FirstVariation.perturb μ u s) := by
        unfold FirstVariation.perturb; infer_instance
      exact dbLoss_eq_loss g nu _
  refine ⟨fun s hs => ?_, c3, fun u hu C hub => ?_, fun h' hh' hrep => ?_⟩
  · have e : ∀ f : S × S → ℝ≥0∞,
        LiftGeneral.edgeLiftDual (pb†lam) ∘ₘ (LiftGeneral.edgeMeasure pb lam).withDensity f =
          reversal (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) ∘ₘ (LiftGeneral.edgeMeasure pb lam).withDensity f :=
      fun f => Measure.bind_congr_right
        ((withDensity_absolutelyContinuous _ _).ae_le hrev)
    rw [e, e]
    exact c1 s hs
  · rw [hloss u]; exact c4 u hu C hub
  · exact c5 h' hh' (fun u hu hub => by rw [← hloss u]; exact hrep u hu hub)

omit [StandardBorelSpace S] [Nonempty S] in
/-- **Non-vacuity of `cor_db_gradient`** (kb `0025`, `0027`): on every standard Borel space
carrying a probability `π`, the hypotheses of `cor_db_gradient` are met on the edge lift of the
resampling kernel `π_← = x ↦ π`, with `λ = π`, `μ = ν̂ = λ₂ = π ⊗ π_←`, `a = b = 1` (`λ₂` is
`K₂`-invariant, so `r̂ = 1` `λ₂`-a.e.) and the generator `g(x) = (x−1)²`, `g' = 2(x−1)`. -/
theorem cor_db_gradient_hypotheses_inhabited (π : Measure S) [IsProbabilityMeasure π] :
    π ≠ 0 ∧ IsInvariant (Kernel.const S π) π ∧
    InM2 (LiftGeneral.edgeMeasure (Kernel.const S π) π)
      (LiftGeneral.edgeMeasure (Kernel.const S π) π) ∧
    LiftGeneral.edgeMeasure (Kernel.const S π) π ≪ LiftGeneral.edgeMeasure (Kernel.const S π) π ∧
    LiftGeneral.edgeLift (Kernel.const S π) ∘ₘ LiftGeneral.edgeMeasure (Kernel.const S π) π ≪
      LiftGeneral.edgeMeasure (Kernel.const S π) π ∧
    (∀ᵐ p ∂(LiftGeneral.edgeMeasure (Kernel.const S π) π),
      1 ≤ FirstVariation.ratio (LiftGeneral.edgeLift (Kernel.const S π))
        (LiftGeneral.edgeMeasure (Kernel.const S π) π) p ∧
      FirstVariation.ratio (LiftGeneral.edgeLift (Kernel.const S π))
        (LiftGeneral.edgeMeasure (Kernel.const S π) π) p ≤ 1) ∧
    MemLp (fun p => ((LiftGeneral.edgeMeasure (Kernel.const S π) π).rnDeriv
      (LiftGeneral.edgeMeasure (Kernel.const S π) π) p).toReal) ⊤
      (LiftGeneral.edgeMeasure (Kernel.const S π) π) ∧
    (∀ y, 0 < y → HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (y - 1)) y) ∧
    ContinuousOn (fun y : ℝ => 2 * (y - 1)) (Ioi 0) ∧
    LocallyLipschitzOn (Ioi 0) (fun y : ℝ => 2 * (y - 1)) := by
  set l2 := LiftGeneral.edgeMeasure (Kernel.const S π) π with hl2
  have hinv := isInvariant_const π
  have hinv2 : IsInvariant (LiftGeneral.edgeLift (Kernel.const S π)) l2 :=
    LiftGeneral.edgeMeasure_invariant (Kernel.const S π) π hinv
  have hK : LiftGeneral.edgeLift (Kernel.const S π) ∘ₘ l2 = l2 := hinv2
  have hr : ∀ᵐ p ∂l2, FirstVariation.ratio (LiftGeneral.edgeLift (Kernel.const S π)) l2 p = 1 := by
    unfold FirstVariation.ratio
    rw [hK]
    filter_upwards [Measure.rnDeriv_self l2] with x hx
    simp [hx]
  have hm : MemLp (fun p => (l2.rnDeriv l2 p).toReal) ⊤ l2 :=
    (memLp_const (1 : ℝ)).ae_eq (by
      filter_upwards [Measure.rnDeriv_self l2] with x hx; simp [hx])
  refine ⟨IsProbabilityMeasure.ne_zero π, hinv, ?_, Measure.AbsolutelyContinuous.refl l2, ?_, ?_,
    hm, fun y _ => ?_, by fun_prop, ?_⟩
  · refine InM2.of_sigmaFinite (Measure.AbsolutelyContinuous.refl l2) ?_
    exact (memLp_const (1 : ℝ)).ae_eq (by
      filter_upwards [Measure.rnDeriv_self l2] with x hx; simp [hx])
  · rw [hK]
  · filter_upwards [hr] with x hx; rw [hx]; simp
  · have := ((hasDerivAt_id y).sub_const 1).pow 2
    exact this.congr_deriv (by simp)
  · exact ((by fun_prop : ContDiff ℝ 1 (fun y : ℝ => 2 * (y - 1))).locallyLipschitz)
      |>.locallyLipschitzOn

end DB

/-! ### The body twin `theo:gd_diffusion`, and non-vacuity -/

section Body

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  {pb : Kernel S S} [IsMarkovKernel pb] {lam : Measure S} [IsFiniteMeasure lam]

/-- **`theo:gd_diffusion` (body), the DB half**: on the edge lift `(𝒮², λ₂, K₂)`, the gradient
of the **DB loss** at `μ = (1+h)λ₂` is represented by `D = K₂ψ − r̂ψ` (along every bounded
direction), and `D` is `g''(1)A†M_wAh` up to `‖E‖ ≤ Kε‖Ah‖ ≤ 2Kε‖h‖` — the same statement as
for the FM loss (`theo_gd_diffusion_full` at `T = π_←`), transported by `prop:db_lift`. The
reversible `w ≡ 1` sentence of the body is about the FM loss and is `theo_gd_diffusion_full`(6). -/
theorem theo_gd_diffusion_DB (hinv : IsInvariant pb lam)
    {w : S × S → ℝ} (hwm : Measurable w) (hw0 : ∀ᵐ p ∂(LiftGeneral.edgeMeasure pb lam), 0 ≤ w p)
    {W : ℝ} (hwb : ∀ᵐ p ∂(LiftGeneral.edgeMeasure pb lam), |w p| ≤ W) (hW0 : 0 ≤ W)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {g gd : ℝ → ℝ} (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y) (hg'1 : deriv g 1 = 0)
    (hg2 : 0 < deriv (deriv g) 1) {eps : ℝ} (heps0 : 0 < eps) (heps : eps ≤ a / 4)
    {h : S × S → ℝ} (hhm : Measurable h)
    (hh : ∀ᵐ p ∂(LiftGeneral.edgeMeasure pb lam), |h p| ≤ eps) :
    (∀ u : S × S → ℝ, Measurable u → ∀ C : ℝ,
      (∀ᵐ p ∂(LiftGeneral.edgeMeasure pb lam), |u p| ≤ C) →
      HasDerivAt (fun s => dbLoss pb g (wMeas (LiftGeneral.edgeMeasure pb lam) w)
          (FirstVariation.perturb (flowOf (LiftGeneral.edgeMeasure pb lam) h) u s))
        (∫ p, gradD (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) gd w h p *
          (u p * (1 + h p)) ∂(LiftGeneral.edgeMeasure pb lam)) 0) ∧
    eLpNorm (fun p => gradD (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) gd w h p -
        linHess (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) w
          (deriv (deriv g) 1) h p) 2 (LiftGeneral.edgeMeasure pb lam) ≤
      ENNReal.ofReal (Kexp (deriv (deriv g) 1) a (Gamma3W g a) W * eps) *
        eLpNorm (Aop (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) h) 2
          (LiftGeneral.edgeMeasure pb lam) ∧
    eLpNorm (Aop (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) h) 2
        (LiftGeneral.edgeMeasure pb lam) ≤ 2 * eLpNorm h 2 (LiftGeneral.edgeMeasure pb lam) := by
  have hinv2 : IsInvariant (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) :=
    LiftGeneral.edgeMeasure_invariant pb lam hinv
  obtain ⟨-, -, c3, -⟩ := gd_gradient (g := g) hinv2 hhm hh ha ha1 heps hC3 hgd hwm hw0 hwb
  obtain ⟨e1, e2⟩ := gd_expansion (gd := gext' gd a) hinv2 hhm hh ha1 heps0.le heps
    (continuous_gext' ha hC3 hgd).measurable hg2.le (Gamma3W_nonneg ha hC3)
    (taylor_gext' (taylor_bundle_of_C3On ha hC3 hgd hg'1)) hwm hwb hW0
  have hc : (fun p => gradD (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam)
      (gext' gd a) w h p - linHess (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) w
        (deriv (deriv g) 1) h p) =ᵐ[LiftGeneral.edgeMeasure pb lam]
      fun p => gradD (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) gd w h p -
        linHess (LiftGeneral.edgeLift pb) (LiftGeneral.edgeMeasure pb lam) w
          (deriv (deriv g) 1) h p := by
    filter_upwards [gradD_eq_gext' (gd := gd) hinv2 ha1 heps w hhm hh] with p hp
    rw [hp]
  rw [eLpNorm_congr_ae hc] at e1
  refine ⟨fun u hu C hub => ?_, e1, e2⟩
  have := c3 u hu C hub
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  haveI : SFinite (FirstVariation.perturb (flowOf (LiftGeneral.edgeMeasure pb lam) h) u s) := by
    unfold FirstVariation.perturb flowOf; infer_instance
  exact dbLoss_eq_loss g _ _

/-- **Non-vacuity** (kb `0025`, `0027`): on every standard Borel space carrying a probability `π`,
the hypotheses of `theo_gd_diffusion_full` are met, including the reversible sentence, by the
resampling kernel `x ↦ π` (reversible), `λ = π ≠ 0`, `w ≡ 1`, `a = 1/2`, the generator
`g(x) = (x−1)²` with `g' = 2(x − 1)` (`C³`, `g(1) = g'(1) = 0`, `g''(1) = 2 > 0`), a non-zero
`h ≡ 1/8` with `‖h‖_{L^∞} ≤ ε = 1/8 = a/4`, and the eigenmode `φ ≡ 1`, `β = 1`. -/
theorem gd_diffusion_hypotheses_inhabited (π : Measure S) [IsProbabilityMeasure π] :
    π ≠ 0 ∧ IsInvariant (Kernel.const S π) π ∧
    IsReversalPair π (Kernel.const S π) (Kernel.const S π) ∧
    Measurable (fun _ : S => (1 : ℝ)) ∧ (∀ᵐ x ∂π, (0 : ℝ) ≤ (fun _ : S => (1 : ℝ)) x) ∧
    MemLp (fun _ : S => (1 : ℝ)) ⊤ π ∧
    ContDiffOn ℝ 3 (fun x : ℝ => (x - 1) ^ 2) (winC3 (1 / 2)) ∧
    (∀ y ∈ winC3 (1 / 2), HasDerivWithinAt (fun x : ℝ => (x - 1) ^ 2) (2 * (y - 1))
      (winC3 (1 / 2)) y) ∧
    (fun x : ℝ => (x - 1) ^ 2) 1 = 0 ∧ deriv (fun x : ℝ => (x - 1) ^ 2) 1 = 0 ∧
    0 < deriv (deriv (fun x : ℝ => (x - 1) ^ 2)) 1 ∧
    (0 : ℝ) < 1 / 8 ∧ (1 / 8 : ℝ) ≤ (1 / 2) / 4 ∧ Measurable (fun _ : S => (1 / 8 : ℝ)) ∧
    (∀ᵐ x ∂π, |(fun _ : S => (1 / 8 : ℝ)) x| ≤ 1 / 8) ∧
    Pd (Kernel.const S π) π (fun _ => (1 : ℝ)) =ᵐ[π] (fun x => (1 : ℝ) * (fun _ => (1 : ℝ)) x) := by
  have hrev := (LiftGeneral.isReversal_const π).1
  have hd : deriv (fun x : ℝ => (x - 1) ^ 2) = fun x => 2 * (x - 1) := by
    funext x
    simp
  have hd2 : deriv (fun x : ℝ => 2 * (x - 1)) 1 = 2 := by
    simp
  refine ⟨IsProbabilityMeasure.ne_zero π, isInvariant_const π, hrev, measurable_const,
    Filter.Eventually.of_forall fun _ => zero_le_one, memLp_top_const 1,
    (by fun_prop : ContDiff ℝ 3 (fun x : ℝ => (x - 1) ^ 2)).contDiffOn, fun y _ => ?_,
    by norm_num, by rw [hd]; norm_num, by rw [hd, hd2]; norm_num,
    by norm_num, by norm_num, measurable_const,
    Filter.Eventually.of_forall fun _ => by norm_num [abs_of_pos], ?_⟩
  · have := ((hasDerivAt_id y).sub_const 1).pow 2
    refine HasDerivAt.hasDerivWithinAt (this.congr_deriv ?_)
    simp
  · refine Filter.Eventually.of_forall fun x => ?_
    simp [Pd, Core.General.funAct]

end Body

end GFNBounds.Balance.GdDiffusionGeneral
