---
id: 0045
title: The general lambda-reversal is Mathlib's posterior; the L^p Jensen step is eLpNorm monotonicity in the exponent
kind: api
tags: [measure, kernel, reversal, obstruction-2]
confidence: provisional
sources: [GFNBounds/Core/AdjointGeneral.lean]
created: 2026-09-19
---

## When

A Phase-4 row needs the `λ`-reversal `T^λ` of a general Markov kernel, the density action
`μ ↦ μT` on `𝓜²(λ)`, or the `L^p(λ)` contraction of a function action — the pieces kb 0006 lists
under obstruction 2. They are built: `GFNBounds.Core.General` in
`GFNBounds/Core/AdjointGeneral.lean`. Import it rather than re-deriving.

## Do

- `T^λ := T†λ` (`ProbabilityTheory.posterior`, `[StandardBorelSpace S] [Nonempty S]`). With
  `hinv : T ∘ₘ λ = λ`, `compProd_posterior_eq_map_swap` *is* the characterizing identity once
  `rw [hinv] at this` — `rw` goes through although `T†λ` carries an `IsFiniteMeasure` instance,
  because `T ∘ₘ λ` appears only in the first factor. To move the measure argument of `†` itself,
  use a `subst`-proved congruence (`posterior_congr_measure`), not `rw`.
- Density action as `A ∘ₘ μ` (`Measure.bind`); the identity `A ∘ₘ (λ.withDensity f) =
  λ.withDensity (∫⁻ f d(B ·))` for a reversal pair holds everywhere in `ℝ≥0∞` with no
  integrability (`IsReversalPair.comp_withDensity`); read off `rnDeriv` with
  `Measure.rnDeriv_withDensity`.
- Jensen `(∫⁻ f dν)^p ≤ ∫⁻ f^p dν` on a probability: `eLpNorm_le_eLpNorm_of_exponent_le` from
  `1` to `ofReal p`, then unfold both sides (`lintegral_rpow_le`). No `ConvexOn` and no
  integrability side-conditions.
- `λ`-null ⟹ `A x`-null for `λ`-a.e. `x`: `Measure.ae_ae_of_ae_comp` after `rw [hinv]`. This is
  what moves an `AEStronglyMeasurable u λ` function to its `mk` representative inside `∫ · d(A x)`.

## Why

The map's scope note for `lem:adjoint` long said a kernel Jensen was "GENUINELY MISSING FROM
MATHLIB" and that item (3) was obstruction 2 in full. Neither was true at this pin: the whole of
items (1)–(3) closed in one file of ~600 lines, with no `sorry`, in one session.
