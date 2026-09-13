---
id: 0006
title: The three obstructions — check before starting, they are not yours to break
kind: obstruction
tags: [markov, scope, planning]
confidence: established
sources: [README.md, docs/COVERAGE.md]
created: 2026-09-07
---
## When

Before accepting any task. If the statement sits behind one of these, say so and stop; do not
spend a session rediscovering it.

## Do

**1. A chain — narrowed (survey of the pin, 2026-09-13).** Mathlib v4.31.0 has `Kernel.traj`
(Ionescu–Tulcea), hitting times and bounded optional stopping; it has no recurrence or transience
classification, no Foster criterion, no strong Markov property, no Perron–Frobenius, no coupling
or Doeblin theory, no total-variation distance for kernels. Of the rows once listed here,
`prop:doubling_length`, `lem:doubling_escape`, `lem:doubling_product` and `theo:doubling_sharp`
are closed without a chain; **only `prop:doubling_phase`** (Foster, transience) and the recurrence
labels of `theo:doubling_main`(1) are still behind it.

*But check first whether the statement really needs it.* Three precedents where it did not:
`Kac.lean` derives `λ(s₀)(2 + σ̄) = 1` from invariance alone, and the decay theorems are stated for
**any positive real sequence satisfying the cut-balance recursion** (`CutBalanceSeq`), with no
invariance, normalisation or recurrence anywhere; and `DescentStatement.lean` states an
almost-sure clause on a finite horizon for every allowed path (`kb/entries/0032`).

**2. The general measure layer.** On the doubling graph the `L^p` layer is built
(`GFNBounds/Doubling/LpLayer.lean`, committed) and `lem:doubling_fixed_points`,
`prop:doubling_unsolvable` are closed. What remains is the generality Appendix A states: the
density action on `L^p(λ)` for an arbitrary Markov kernel with its `λ`-reversal and adjoint, a
Radon–Nikodym calculus on `𝓜⁺`, disintegration. Rows blocked on it sit in bucket `D`, among them
`lem:doubling_operator` (any kernel) and `theo:first_variation_full`.

**3. Euler–Maclaurin — no longer a wall.** The pin has `trapezoidal_error_le`, which gives the
second-order window sum per unit interval; `lem:doubling_expansion` and `rem:doubling_parity` are
therefore bucket `B`, not `C`. `R0Bound.lean`'s first-order telescoping
(`|R₀(m) − 1| ≤ 16cτ/m`) stands. `rem:doubling_second_order` is terminal.

## Why

`docs/COVERAGE.md`'s bucket column is the standing answer: `C` means *attempted and blocked on a
named obstruction*, `D` means *needs a layer this library has not built*. A `C` or `D` row is a
claim that someone already tried. Beating it needs new material, and the honest move is to say
what new material you have before you start.
