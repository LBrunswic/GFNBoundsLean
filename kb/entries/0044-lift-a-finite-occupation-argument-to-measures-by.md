---
id: 0044
title: Lift a finite occupation argument to measures by comparing masses, not by subtracting measures
kind: pattern
tags: [measure, sampler, rnDeriv, ennreal, generalization]
confidence: provisional
sources: [GFNBounds/Core/SamplingGeneral.lean, GFNBounds/Core/SamplingGeneralBounds.lean]
created: 2026-09-19
---

## When

A finite-state argument (kb `0038`) proves a sampler statement through the gap `ν := G/Z − Q`
between a super-solution and the occupation, and you are asked for the same statement on a
general measurable space, with `F_init, F_term, F⋆_out : Measure α` and `π⋆ : Kernel α α`. The
gap is a *difference of measures*, and Mathlib's `Measure` subtraction (`Measure.sub`) is a
truncated operation with a thin API.

## Do

Keep everything in `Measure α` / `ℝ≥0∞` and replace the gap by two facts:

* domination `Q ≤ H` from `μ₀ + step H ≤ H` by induction on partial sums, evaluated setwise
  (`Measure.le_iff`, `step_apply : step μ s = ∫⁻ x, cont x * P x s ∂μ`, then `lintegral_mono'`);
* **equal finite total mass**: on `univ`, `Q(𝒮) = μ₀(𝒮) + ∫⁻ cont dQ` and
  `∫⁻ cont dQ + ∫⁻ stop dQ = Q(𝒮)` (`cont + stop = 1` pointwise), so `∫⁻ stop dQ = μ₀(𝒮)`
  once `Q(𝒮) ≠ ∞`. Then `μ ≤ ν`, `ν` finite, `μ univ = ν univ` gives `μ = ν`
  (Mathlib's `MeasureTheory.Measure.eq_of_le_of_measure_univ_eq`, finiteness of `μ` from
  `isFiniteMeasure_of_le`; the local `eq_of_le_of_univ` is that wrapper).

Make the stopping rule total and pointwise bounded: `cont x := min (F⋆_out.rnDeriv G x) 1`,
`stop := 1 − cont`; prove `cont =ᵐ[G] F⋆_out.rnDeriv G` and `stop =ᵐ[G] F_term.rnDeriv G` from
`Measure.rnDeriv_add` + `Measure.rnDeriv_self`, then `withDensity_congr_ae` +
`Measure.withDensity_rnDeriv_eq` give `cont · G = F⋆_out`, `stop · G = F_term`. For `ℕ`-series of
masses use `tsum_eq_zero_add' ENNReal.summable` (the `Summable.tsum_eq_zero_add` form timed out
in `rw`). `withDensity_add_left` wants `Measurable`; for `AEMeasurable` densities go through
`ext` and `lintegral_add_left'`.

## Why

The finite proof "`ν` is invariant under `cont · P⋆`, so carried by `{stop = 0}`" needs `G/Z − Q`
as a measure and its invariance, i.e. subtraction commuting with `bind`. The mass comparison
needs neither, gives the stronger conclusion (the law of `s_τ` **equals** `F_term/F_term(𝒮)` as
measures), and is linear in `μ₀`, which is exactly what negative control then consumes
(`termLaw_add`). The whole general sampler, theorem and chain kernel included, is ~700 lines.
