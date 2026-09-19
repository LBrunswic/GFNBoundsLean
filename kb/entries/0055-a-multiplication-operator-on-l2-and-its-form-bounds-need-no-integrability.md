---
id: 0055
title: A multiplication operator on L²(λ) and its form bounds need no integrability; L²(0) is trivial
kind: pattern
tags: [measure, lp, operator, hessian, generalization]
confidence: provisional
sources: [GFNBounds/Balance/StableFrozenGeneral.lean]
created: 2026-09-19
---

## When

A general-space statement needs `M_w` (multiplication by `w ∈ L^∞(λ)`) as a bounded operator on
`Lp ℝ 2 λ`, e.g. to build `H = g''(1)A^†M_wA`, and bounds `w_min‖y‖² ≤ ⟪y, M_w y⟫ ≤ ‖w‖_∞‖y‖²`.

## Do

- Operator: `LinearMap.mkContinuous` with `toFun f := ((Lp.memLp f).mul' hw).toLp _` for
  `hw : MemLp w ⊤ λ` — the `HolderTriple ⊤ 2 2` instance is found (`instInfty` + `symm`); give the
  ascription `MemLp (fun x => w x * f x) 2 λ`. Bound constant `(eLpNorm w ⊤ λ).toReal`, proved by
  `Lp.norm_le_mul_norm_of_ae_le_mul`; the a.e. bound `‖w x‖ ≤ (eLpNorm w ⊤ λ).toReal` is
  `ae_le_eLpNormEssSup` + `eLpNorm_exponent_top` + `ENNReal.toReal_mono` + `toReal_enorm`.
  In `map_smul'` do `rw [RingHom.id_apply]` before `Lp.ext`.
- Form bounds: write `⟪y, M_w y⟫ − c‖y‖² = ⟪y, M_w y − c•y⟫`, identify the right argument a.e. as
  `(w − c)·y`, and conclude with `L2.inner_def` + `integral_nonneg_of_ae`. No integrability side
  goal ever appears. After `filter_upwards` the goal is `0 x ≤ …` (a `Pi` zero): `change (0:ℝ) ≤ _`.
- A statement on a finite `λ` that needs `λ ≠ 0` only in a degenerate corner (idempotence of `Π`,
  `w_min ≤ ‖w‖_∞`): split on `λ = 0` and kill that case with
  `Lp.eq_zero_iff_ae_eq_zero.2 (ae_iff.2 _)`, the null set read through
  `congrArg (fun m : Measure S => m {x | …}) hlam` — `rw [hlam]` fails, the `Lp` terms' types
  mention `λ`.
- `ContinuousLinearMap.ext_iff.1 (meanProj_idem hν) x` timed out at `whnf`; name the equation with
  its type first and apply `congrArg (fun L : Lp ℝ 2 λ →L[ℝ] Lp ℝ 2 λ => L x)`.

## Why

`theo:db_stable_frozen_full` on a general space needed exactly these four moves; the paper's
`H = g''(1)A^†M_wA` then has every property `Discrete.stable_frozen_discrete` carries as a
hypothesis (self-adjoint, `ΠH = 0`, coercive, form-bounded), and the carried `εϱ ≤ 1` became
derivable. The Mathlib `HSMul (Lp 𝕜 ⊤ μ) (Lp E 2 μ)` instance also exists
(`Mathlib/MeasureTheory/Function/Holder.lean`), but taking `w` as a plain function keeps
`‖w‖_{L^∞}` and the a.e. bound in the paper's shape.
