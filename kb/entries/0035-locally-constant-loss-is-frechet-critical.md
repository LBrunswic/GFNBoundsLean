---
id: 0035
title: "Critical point" is a Fréchet derivative equal to zero, not a gradient formula equal to zero
kind: pitfall
tags: [calculus, fidelity, criticality]
confidence: established
sources: [GFNBounds/Balance/FreezingGeneral.lean:40, GFNBounds/Balance/FreezingGeneral.lean:58]
created: 2026-09-13
---
## When

The paper says "`μ` is a critical point of `𝓛`" and the library has a formula `D` that the paper
calls the gradient.

## Do

State criticality as `HasFDerivAt (fun u' => loss … u') 0 u`, for every training measure the paper
quantifies over. `D ≡ 0` is the paper's formula evaluating to zero; it is criticality only through
a first-variation theorem, whose hypotheses may not hold at the point. On a frozen band the loss is
locally constant, so the Fréchet form follows from `const_on_band_of_deriv_zero` directly.

## Why

In `prop:nonlinear_freezing`(1) the conjunct `lossGradDensity … = 0` is the paper's formula
`g̃'(r) = 0 ⇒ D = 0`, proved from `g̃' = 0` on the band alone; the audit of the widened file required
the separate Fréchet conjunct, which covers every `ν`, those vanishing on states included.
