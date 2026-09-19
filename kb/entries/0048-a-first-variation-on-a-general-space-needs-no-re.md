---
id: 0048
title: A first variation on a general space needs no reversal: linearize d((phi mu)T)/dmu, move T by snd_compProd
kind: pattern
tags: [measure, rnDeriv, first-variation, obstruction-2]
confidence: provisional
sources: [GFNBounds/Core/FirstVariationGeneral.lean]
created: 2026-09-19
---

## When

A Phase-4 row differentiates a functional of `d(μT)/dμ` (a balance loss, its DB lift) on a
general measurable space, along directions `δ = uμ` with `u` signed, and the paper routes the
computation through the invariant measure `λ` and `lem:adjoint`(3).

## Do

Work in `μ`-coordinates and bring `λ` in only to *name* the gradient
(`GFNBounds/Core/FirstVariationGeneral.lean`):

* Carry `μ + sδ` as `μ.withDensity (ofReal (1 + s·u))` and `d(δT)/dμ` as
  `d((u⁺μ)T)/dμ − d((u⁻μ)T)/dμ`. Linearity of `φ ↦ d(T ∘ₘ (φ⁺μ))/dμ` is `Measure.comp_add`,
  `Measure.comp_smul`, `withDensity_add_left` and `Measure.rnDeriv_add` (`pushDens_add4`,
  `pushDens_smul`); the one pointwise identity needed is `(1+x)⁺ + (−x)⁺ = 1 + x⁺` for `1+x ≥ 0`.
  `Measure.rnDeriv_withDensity_right` then gives `r(μ+sδ) = (r + s·v)/(1 + s·u)` a.e.
* The adjoint step `∫ ψ d(δT) = ∫ Tψ dδ` needs no reversal: `κ ∘ₘ m = (m ⊗ₘ κ).snd`
  (`Measure.snd_compProd`), `integral_map`, `Measure.integral_compProd`. Mathlib has no Bochner
  `integral_bind`; this is the substitute.
* Differentiate under the integral with `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the
  explicit quotient, after `HasDerivAt.congr_of_eventuallyEq` swaps the loss for it near `s = 0`.
* `g'` continuous only on `(0, ∞)` is not measurable: replace `g` by `g ∘ clamp c d` (continuous,
  equal on the essential range) and pass `Tψ` to a measurable version with `μT ≪ μ` plus
  `Measure.ae_ae_of_ae_comp`; `integral_congr_ae` needs no measurability of `ψ`.

## Why

Obstruction 2 was recorded as "a Radon–Nikodym calculus on `𝓜⁺`". The calculus needed is four
Mathlib lemmas. Going through `μ` rather than `λ` also showed that the paper's `dμ/dλ ∈ L²(λ)` and
`μT ≪ μ` are unused, and that the body twin's differentiability clause needs no invariant measure.
