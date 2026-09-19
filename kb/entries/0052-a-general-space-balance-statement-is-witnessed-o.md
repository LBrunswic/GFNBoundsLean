---
id: 0052
title: A general-space balance statement is witnessed on Bool with the resampling kernel, and its flow lives in Lp
kind: pattern
tags: [measure, witness, vacuity, flow, generalization]
confidence: provisional
sources: [GFNBounds/Balance/FreezingGeneral2.lean]
created: 2026-09-19
---

## When

Lifting a finite `Balance/` statement about `r = d(μT)/dμ`, the gradient density `D = Tφ − rφ`
or the gradient flow to a general measurable space (Phase 4), and needing (kb 0025, 0027) a
witness that the hypotheses are inhabited **off balance**, or a statement about the flow.

## Do

* **Witness with `T = Kernel.const S π`** on any probability space. It is ergodic in the sense
  "every finite fixed `μ ≪ π` is a multiple" in three lines (`ergodicG_const`), `T ∘ₘ μ = μ(S) • π`
  (Mathlib's `Measure.const_comp`), and for `μ = (1 + h)π` the ratio is
  explicit, `r = μ(S)/(1 + h)` `π`-a.e. (`ratioG_const_pertG`): `Measure.rnDeriv_withDensity_right`
  then `Measure.rnDeriv_smul_left_of_ne_top'` and `Measure.rnDeriv_self`. On `Bool` with
  `π = 2⁻¹δ_true + 2⁻¹δ_false` this is the two-state chain `T(i → j) = 1/2`; read a.e. statements
  pointwise with `ae_iff_of_countable` (every atom has mass `1/2`). `h = (3/10, −3/10)` gives
  `r = (10/13, 10/7)`, band-valued for the `(5/8, 7/8) ∪ (11/8, 13/8)` bands and unbalanced.
* **`r > 0` needs no hypothesis**: `λ ≪ μ` and invariance give `λ ≪ μT`, so `μ ≪ μT` and
  `Measure.rnDeriv_pos'` applies. Balance is `Measure.rnDeriv_eq_one_iff_eq`.
* **The gradient flow is a curve `u : ℝ → Lp ℝ 2 λ`** with `HasDerivAt u (−D) t` for `t ≥ 0`,
  `D : Lp` a.e. equal to the gradient density. Then the invariant sphere is `HasDerivAt.norm_sq`
  with `L2.inner_def`; the mass is `⟪1, u t⟫` for `1 := (memLp_const 1).toLp _`, differentiated
  by `HasDerivAt.inner ℝ`; the travel bound is `norm_image_sub_le_of_norm_deriv_le_segment'` with
  the derivative chosen by `dite` on `0 ≤ t`, and `‖D‖ = (eLpNorm D 2 λ).toReal` (`Lp.norm_def`,
  `eLpNorm_congr_ae`). A constant curve at a frozen flow inhabits the predicate off balance.
* `SigmaFinite (λ.withDensity (ofReal ∘ f))` is an instance only syntactically: wrap such
  measures in a `def` and give the `def` its own instance (`SigmaFinite.withDensity_ofReal`).

## Why

The mass identity, the radial orthogonality and the freezing criticality each closed in a few
dozen lines once `D` was written with `Core.General.funAct`; what took the time was showing
that the hypotheses bundle (`FirstVariationSetting`) is satisfiable by an unbalanced flow, and
the resampling kernel on `Bool` does that with every quantity in closed form.
