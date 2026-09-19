---
id: 0050
title: P* = P on a general measurable space by Lp.induction on indicators, with no Riesz step and no reversal
kind: pattern
tags: [kernel, adjoint, measure-layer, obstruction-2, lp]
confidence: provisional
sources: [GFNBounds/Doubling/OperatorGeneral.lean]
created: 2026-09-19
---

## When

You need the `L²(λ)` adjointness of the density action `P = Core.densityActionL2` and the
function action `P⋆v(x) = ∫ v dT(x)` for a Markov kernel on an **arbitrary** measurable space,
and do not want the standard Borel hypothesis that the `λ`-reversal (`Core.General.reversal`,
Mathlib's `posterior`) brings.

## Do

Both operators are already bounded (`isBoundedDensityAction_two`; `funActLp` from
`General.IsInvariant.eLpNorm_funAct_le`), so check the identity on indicators only:
`⟪P𝟏_B, 𝟏_A⟫ = ∫_B T(x, A) dλ = ⟪𝟏_B, P⋆𝟏_A⟫`. The left side is
`Core.lintegral_bindDensity_mul` with `f = 𝟏_B`, `h = 𝟏_A`, read in `ℝ` by `integral_toReal`;
the right side is `integral_indicator_one`. Then run `MeasureTheory.Lp.induction (p := 2)
(hp_ne_top := ENNReal.ofNat_ne_top)` twice (first in `u` against a fixed `𝟏_A`, then in `v`):
the indicator case reduces `c • 𝟏` to `1 • 𝟏` (`Lp.simpleFunc.coe_indicatorConst` plus an
`Lp.ext`), `add` is `map_add`/`inner_add_left`, and `isClosed` is `isClosed_eq` of two
`Continuous.inner`s. Give `p := 2` explicitly or the `Fact (1 ≤ ?p)` instance fails to resolve.
`ContinuousLinearMap.eq_adjoint_iff` then gives `P⋆ = P*`, and `Π` self-adjoint gives
`‖P⋆ⁿ − Π‖ = ‖Pⁿ − Π‖` through `adjoint.norm_map`.

## Why

The paper proves the adjointness with Fubini plus Riesz representation, and the library's first
general route went through the reversal, which needs `[StandardBorelSpace]`. The density
argument needs neither, and it closed the whole of `lem:doubling_operator` at the paper's
"measurable space" generality in one file.
