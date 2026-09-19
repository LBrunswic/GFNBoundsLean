---
id: 0049
title: A density map between two L² spaces is E† ∘ P — sandwich the lifted operator, skip the reversal
kind: pattern
tags: [lift, l2, adjoint, density-action, mixing, measure-layer]
confidence: provisional
sources: [GFNBounds/Balance/LiftGeneralMixing.lean]
created: 2026-09-19
---
## When

A statement compares an operator on `L²(λ₂)` (a lifted kernel's density action, `P₂`) with one on
`L²(λ)` (`P`) — mixing coefficients, coercivity constants, spectral facts — and the paper's proof
goes through a conditional expectation or the `λ`-reversal. `Core.densityActionL2` exists only
for a kernel `α → α`, so the natural "density of the first marginal" map `L²(λ₂) → L²(λ)` has no
constructor in the library.

## Do

Build it from what exists (`GFNBounds/Balance/LiftGeneralMixing.lean`):

* `E φ := φ ∘ pr₂` as `(Lp.compMeasurePreservingₗᵢ ℝ Prod.snd hmp).toContinuousLinearMap`, an
  isometry because the marginal is `λ`; then `E† ∘L E = 1` is
  `ContinuousLinearMap.norm_map_iff_adjoint_comp_self`.
* The marginal map is `M := E† ∘L P₂`. It is linear and `‖M‖ ≤ 1` for free; the only analytic
  fact needed is `P₂ h ∈ range E` (read off `eq:muK2_density` on `h⁺λ₂`, `h⁻λ₂`, then
  `memLp_map_measure_iff`), which gives `E M = P₂`.
* Prove the intertwinings on representatives (`P₂ E = E P`, `P₂ D = E` for `D φ := φ ∘ pr₁`),
  then everything is algebra: `P₂^{n+1} − Π₂ = E (Pⁿ − Π) M`, so `‖·‖ ≤` by `‖E x‖ = ‖x‖`,
  `‖M‖ ≤ 1`, and `≥` by testing `D φ` (`M D = 1`). `Π₂ = E Π M` follows from
  `⟪E† y, 1⟫ = ⟪y, E 1⟫` and mass preservation.
* To move an `=ᵐ[λ]` through `pr₂`, use `ae_eq_comp` after rewriting `λ₂.map snd = λ`.

## Why

The paper's `lem:lift_mixing` passes to function actions (needing `‖A‖ = ‖A*‖`) and
`lem:lift_coercivity` uses `π_→^λ` (a disintegration). With the sandwich, both close on density
actions, on **any** measurable space, with no standard Borel hypothesis — about 250 lines for both
lemmas, where the finite forms (`Balance/LiftFinite.lean`) had needed a separate density/function
norm identification and an attainment hypothesis.
