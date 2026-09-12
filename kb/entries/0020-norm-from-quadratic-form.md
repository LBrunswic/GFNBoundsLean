---
id: 0020
title: The norm of a symmetric operator from its quadratic form, without a spectral theorem
kind: pattern
tags: [inner-product, operator-norm, self-adjoint, tactics]
confidence: established
sources: [GFNBounds/Balance/Discrete.lean:128, GFNBounds/Balance/Discrete.lean:153]
created: 2026-09-12
---
## When

You need `‖T x‖ ≤ c‖x‖` from a two-sided bound `0 ≤ ⟪y, T y⟫ ≤ c‖y‖²` on a `T`-invariant set,
and reach for `IsSymmetric`, `ContinuousLinearMap.adjoint` or the spectral theorem — none of
which this library has, and none of which it wants.

## Do

Two short lemmas, no `CompleteSpace`, no spectral theory.

1. Cauchy–Schwarz for the semi-definite form: for `T` symmetric with `∀ y, 0 ≤ ⟪y, T y⟫`,
   `⟪x, T y⟫² ≤ ⟪x, T x⟫ * ⟪y, T y⟫`, by `discrim_le_zero` applied to the non-negative quadratic
   `t ↦ ⟪x + t • y, T (x + t • y)⟫`.
2. Apply it at `(x, T x)`: symmetry turns `⟪x, T (T x)⟫` into `‖T x‖²`, so
   `‖T x‖⁴ ≤ (c‖x‖²)(c‖T x‖²)`. Split off `‖T x‖ = 0` and divide.

Both need `T` **symmetric**, and that is not a technicality you can drop — see below.

## Why

`theo:db_stable_frozen_full`'s discrete contraction factor `1 − εϱ` is exactly this bound, and
the obvious substitute loses a square root: the energy method gives
`‖(I − εH)h‖² ≤ (1 − εϱ)‖h‖²`, hence `√(1 − εϱ)`, which is strictly weaker whenever
`0 < εϱ < 1`. `Discrete.scalar_discrete_check` compiles that gap as a fact.

The reason the energy method needs symmetry too is worth keeping: `‖H x‖² ≤ ‖H‖⟪x, H x⟫` — the
inequality `GFNBounds/Balance/Flow.lean`'s SCOPE named as the missing ingredient — is **false**
without it. A rotation by a right angle has `⟪x, H x⟫ = 0` and `‖H x‖ = ‖x‖`. Over a real
space, `H ⪰ 0` does not imply `H` symmetric, so a positivity hypothesis does not supply it.
