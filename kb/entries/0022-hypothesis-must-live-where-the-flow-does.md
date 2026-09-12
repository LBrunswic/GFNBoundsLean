---
id: 0022
title: A standing hypothesis quantified over all of `ℝ` cannot be discharged on a half-line
kind: pitfall
tags: [flow, hypotheses, reuse, quantifiers]
confidence: established
sources: [GFNBounds/Balance/Flow.lean:571, GFNBounds/Balance/MassAscent.lean:538]
created: 2026-09-12
---
## When

Stating a theorem "along the gradient flow" that carries a standing bound, positivity or
monotonicity hypothesis on the trajectory.

## Do

Range it over the half-line the conclusion lives on — `∀ t : ℝ, 0 ≤ t → …` — never over all of
`ℝ`. When two such hypotheses sit in one signature, check they agree: a mismatch between them
is the tell.

## Why

`Flow.global_lojasiewicz_flow` carried `hL0 : ∀ t : ℝ, 𝓛(μ_t) ≤ L₀` beside
`hpos : ∀ t : ℝ, 0 ≤ t → 0 < 𝓛(μ_t)`. The only thing that could ever supply `hL0` is
antitonicity of the loss along the flow, which holds on `[0,∞)` and gives the **reverse**
inequality below `0` — so the hypothesis was undischargeable at the paper's own instantiation
`L₀ = 𝓛(μ₀)`, and `MassAscent` had to re-derive the theorem instead of applying it. The
hypothesis was used exactly once, in a context where `0 ≤ s` was already in scope and being
discarded. Repaired 2026-09-12; verified by elaborated type, not by source diff.

`lojasiewicz_integrated`'s `hpos` cost a comparable duplication for a neighbouring reason, and
`lojasiewicz_integrated_nonneg` now removes it: `−L' ≥ κ²L² ≥ 0` makes `L` antitone, so `0 ≤ L 0`
alone propagates positivity backwards over `[0,t]`.

A hypothesis costs nothing to state and everything to discharge. One nobody downstream can
produce is a theorem nobody downstream can use, and no gate in this repository will notice —
`sorry` has a firewall, hypothesis creep has only the docstring checklist.
