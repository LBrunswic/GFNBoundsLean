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

**1. A chain.** Mathlib v4.31.0 has no discrete-time Markov chain theory at all: no recurrence or
transience, no Kac formula, no stationary-distribution existence, no Perron–Frobenius, no
coupling, no Doeblin, no total-variation distance for kernels. Blocked on it:
`prop:doubling_length` (optional stopping), `prop:doubling_phase` (Foster), `lem:doubling_escape`,
`lem:doubling_product`, `theo:doubling_sharp` and its three lemmas.

*But check first whether the statement really needs it.* Two precedents where it did not:
`Kac.lean` derives `λ(s₀)(2 + σ̄) = 1` from invariance alone, and the decay theorems are stated for
**any positive real sequence satisfying the cut-balance recursion** (`CutBalanceSeq`), with no
invariance, normalisation or recurrence anywhere.

**2. The `L^p` layer with its adjoint.** `lem:doubling_operator`(1)–(2),
`lem:doubling_fixed_points`' `P` half, `prop:doubling_unsolvable`. The *analysis* is done —
`eq:doubling_inf` is proved — and what is missing is the functional analysis around it. An
uncommitted spike exists at `GFNBounds/Doubling/LpLayer.lean`; read it before starting.

**3. Euler–Maclaurin — routed around, do not re-open casually.** `R0Bound.lean` gets
`|R₀(m) − 1| ≤ 16cτ/m` at every `m ≥ 1` by first-order telescoping. The refined expansion is now
needed only by `rem:doubling_parity` and `rem:doubling_second_order`, neither of which the paper
proves.

## Why

`docs/COVERAGE.md`'s bucket column is the standing answer: `C` means *attempted and blocked on a
named obstruction*, `D` means *needs a layer this library has not built*. A `C` or `D` row is a
claim that someone already tried. Beating it needs new material, and the honest move is to say
what new material you have before you start.
