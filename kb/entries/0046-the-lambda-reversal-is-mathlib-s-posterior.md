---
id: 0046
title: The λ-reversal of `lem:adjoint` is Mathlib's `posterior`; an image-density L² contraction needs no disintegration
kind: api
tags: [kernel, reversal, disintegration, measure-layer, adjoint]
confidence: established
sources: [GFNBounds/Balance/LiftGeneral.lean, .lake/packages/mathlib/Mathlib/Probability/Kernel/Posterior.lean]
created: 2026-09-19
---
## When

Any general-space (non-`Fintype`) statement that needs the `λ`-reversal `T^λ` of a Markov
kernel (`lem:adjoint`*(1)*, the dual forward policy `π_→^λ`, the edge-lift dual `K₂*`), or the
`L²` contraction of a conditional expectation / image density — i.e. obstruction 2 of kb `0006`.

## Do

* **Existence**: `ProbabilityTheory.posterior T λ` (`T†λ`, needs `[StandardBorelSpace S]
  [Nonempty S]`, finite `λ`, finite `T`) satisfies `compProd_posterior_eq_map_swap :
  (T ∘ₘ λ) ⊗ₘ T†λ = (λ ⊗ₘ T).map Prod.swap`. With `λ.bind T = λ` that is the paper's
  `λ ⊗ T^λ = T ⊗ λ` verbatim (paper's `A ⊗ λ` = Mathlib's `(λ ⊗ₘ A).map Prod.swap`).
  **Uniqueness**: `Kernel.ae_eq_of_compProd_eq` (countably generated). The file also has
  `posterior_posterior` (involution) and `posterior_comp_self` (invariance).
* Keep the general results parametric in a reversal `R` with the hypothesis
  `λ ⊗ₘ R = (λ ⊗ₘ T).map Prod.swap` (`LiftGeneral.IsReversal`); only construction needs standard
  Borel. Adjointness `∫ d(μA)/dρ · dν/dρ dρ = ∫ dμ/dρ · d(νR)/dρ dρ` then holds for all finite
  non-negative `μ, ν ≪ ρ` in `ℝ≥0∞` with no integrability hypothesis (`adjoint_of_isReversal`).
* **Contraction without disintegration**: `∫ (d(φ_*μ)/d(φ_*ρ))² ≤ ∫ (dμ/dρ)²` for any measurable
  `φ` (`lintegral_rnDeriv_map_sq_le`): test the truncation `w ⊓ n` against `w`
  (`lintegral_rnDeriv_mul` twice), Cauchy–Schwarz (`ENNReal.lintegral_mul_le_Lp_mul_Lq` with
  `Real.HolderConjugate.two_two`), cancel the finite `√A`, then `lintegral_iSup` with
  `ENNReal.iSup_pow`.
* Measure equalities on products: prove `∫⁻ f` agreement for every measurable `f` and conclude
  with indicators (`Measure.ext_of_lintegral`, already in Mathlib); inner-integral measurability is easiest read off
  a kernel form via `Measurable.lintegral_kernel_prod_right'` and a `funext`.

## Why

Every A-row blocked on "disintegration on standard Borel spaces" (kb `0006`, obstruction 2) was
written as if Mathlib lacked it. At `v4.31.0` it does not: the posterior is the reversal, with
uniqueness and involution already proved. The general `def:edge_lift`/`lem:lift_wellposed`
closed in one session on top of it.
