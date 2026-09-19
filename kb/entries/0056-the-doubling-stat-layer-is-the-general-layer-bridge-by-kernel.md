---
id: 0056
title: The doubling Stat layer is the general Core layer — bridge by building the kernel, then take adjoints
kind: pattern
tags: [measure, kernel, bridge, doubling, generalization, adjoint]
confidence: provisional
sources: [GFNBounds/Balance/TBvsDBClose.lean]
created: 2026-09-19
---
## When

A general-space theorem (`Core.densityActionL2`, `Core.meanProj`, `LiftGeneral.*`,
`Doubling.General.*`) must be applied to the counter-example graph, whose operators live on
`Stat S cap`'s `Lp ℝ 2 L.mu` as `L.pstarL2`, `L.densL2`, `L.piL2`, and whose constants
(`bhatK`, `betaHat`) are stated there. The map note said "no bridge exists"; it is short.

## Do

1. **The kernel.** `St` is countable with `MeasurableSpace := ⊤`, so
   `Kernel.ofFunOfCountable` turns the three cases of `pstar` into a kernel (`dirac`, a two-atom
   `ofReal ε • dirac + ofReal (1−ε) • dirac`, a finite `∑ ofReal row • dirac`). Every function is
   integrable against it (`integrable_dirac`, `integrable_finsetSum_measure`), and
   `integral_add_measure`/`integral_smul_measure`/`integral_dirac` give
   `General.funAct ker f = pstar S cap f` for **every** `f`, pointwise. Markov-ness falls out of the
   same identity at `f ≡ 1` (`pstar_const`).
2. **Invariance as a measure** from `Stat.inv` (integral form, bounded `f`): test indicators.
   `ker x A = ofReal (pstar (A.indicator 1) x)` (`integral_indicator_one`), then
   `Measure.bind_apply` + `lintegral_countable'` + `ENNReal.ofReal_tsum_of_nonneg` on both sides.
3. **Operators.** `funActLp ker = L.pstarL2` by `Lp.ext` on `coeFn_funActLp`/`coeFn_pstarL2`; then
   the density actions agree **because both are the adjoint of that one operator**:
   `rw [← General.adjoint_funActL2, funActLp_ker, L.adjoint_pstarL2]`. Never compare the two
   density actions directly — `Stat.dens` is a `λ`-weighted sum and `Core.densityAction` a
   Radon–Nikodym derivative. `meanProj L.mu 2 = L.piL2` is `integral_eq_tsum` + `inner_oneLp`.

## Why

Once `densityActionL2 ker L.mu _ = L.densL2 _` and `meanProj = piL2` hold, every constant of the
doubling layer (e.g. `isLeast_bhatK`'s coercivity at `B̂_K`) rewrites into the general layer's
hypotheses, and the general theorem applies verbatim — here `lift_coercivity_general` at
`C = B̂_K`, closing `rem:tb_vs_db`'s detailed-balance supply in ~150 lines. The adjoint route
avoids all Radon–Nikodym bookkeeping on the countable space.
