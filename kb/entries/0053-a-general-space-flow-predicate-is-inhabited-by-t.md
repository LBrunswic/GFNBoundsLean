---
id: 0053
title: A general-space flow predicate is inhabited by transporting a finite ODE solution into Lp on Bool
kind: pattern
tags: [measure, witness, vacuity, flow, lp]
confidence: provisional
sources: [GFNBounds/Balance/FreezingGradientBridge.lean]
created: 2026-09-19
---
## When

A general-space theorem hypothesises a gradient flow `u : ℝ → Lp ℝ 2 λ` (`IsGradientFlowG`,
`IsGradientFlowPaper`) and kb 0025 asks for a **non-constant** solution off balance — the constant
curve at a frozen flow (kb 0052) does not exercise a strictly unimodal generator. The finite
library already has the ODE solution (`twoState_flow_exists_check_sq` in
GFNBounds/Balance/FlowExistence.lean).

## Do

Transport it rather than solving anything (`bool_unimodal_flow` in
GFNBounds/Balance/FreezingGradientBridge.lean):

* `boolLp : (Fin 2 → ℝ) →L[ℝ] Lp ℝ 2 boolUnif` is `LinearMap.toContinuousLinearMap` of
  `v ↦ (MemLp.of_discrete).toLp (v ∘ boolIdx)`; `map_add'` and `map_smul'` are `rfl`
  (`MemLp.toLp_add`/`toLp_const_smul` are `rfl`). Continuity is free (finite dimension).
* The derivative: `hasDerivAt_pi.2` turns the componentwise `IsGradientFlow` into a vector
  derivative, then `boolLp.hasFDerivAt.comp_hasDerivAt t`, and `map_neg` after `rw [show … = -… from rfl]`.
* Read every a.e. statement on `boolUnif` pointwise (`ae_iff_of_countable`, atoms `1/2`) and
  compute the measure-theoretic objects in closed form for `μ = π.withDensity (ofReal ∘ f)`,
  `f > 0`: `dμ/dπ = f`, `dπ/dμ = 1/f` (`Measure.rnDeriv_withDensity_right` + `rnDeriv_self`),
  `r = mean(f)/f` (`Measure.const_comp`), `D = mean(φ) − rφ` (`Kernel.const_apply`). The finite
  `lossGrad` unfolds (`simp only [lossGrad, lossGradDensity, gradDensity, funAct, …]` after
  rewriting `ratio` and `ν/(λu)` first) to the same formula; match `cases b`.
* `IsReversalPair π (const π) (const π)` is `Measure.compProd_const` + `Measure.prod_swap`: no
  standard-Borel reversal is needed for the resampling kernel.

## Why

The general flow half of `prop:no_distant_equilibrium`(2) had been recorded as "not shown
non-vacuous off balance". Transport closed it in ~250 lines with no new analysis. Pitfall met on
the way: for `ℝ`-valued `HasDerivAt`, `HasDerivAt.pow`/`.mul` elaborate at the normed-algebra
(function-valued) instance and leave `Pi` goals; use `(hasDerivAt_pow n _).comp` instead.
