---
id: 0040
title: Read the paper's ∼ through app:notation before refuting a sampler clause
kind: pitfall
tags: [sampler, fidelity, notation, review]
confidence: provisional
sources: [GFNBounds/Graph/SamplerWiring.lean:1, GFNBounds/Graph/UniversalityClosing.lean:44]
created: 2026-09-18
---

## When

A statement of the paper says "its sampler satisfies `s_τ ∼ μ`" (or "`TV(s_τ ‖ κ)`") and you are
about to certify it, or to record it as false, because `μ` has the wrong mass, charges a state
outside `𝒮`, or is a terminal flow rather than a probability.

## Do

Check both readings before writing either verdict. `app:notation` fixes `x ∼ μ` as *the law of
`x` is `μ/μ(𝒮)`* for an unnormalized `μ`, and flows live on `𝒮 = 𝒱 ∖ {s₀, s_f}`. So state the
literal reading (the law **is** `μ`, as a function on `𝒱`) and the normalized one (the law is
`μ|_𝒮/μ(𝒮)`) as two theorems, and record which one fails. Quantify the TV over the law predicate,
not over a chosen normalization:

```lean
∀ μ, SamplerWiring.IsSamplerLaw G F μ → tvFin μ κ = …
```

`IsSamplerLaw` is unique (`IsSamplerLaw.unique`), so this costs nothing and keeps `termLaw` (which
normalizes over all of `𝒱`) out of the statement.

## Why

`theo:universality_graphs`(3) with an edge `s₀ → s_f`: finding 2 of `UniversalityClosing.lean`
recorded "`s_τ ∼ R/Z` fails". Read literally it does (`universality_graphs_sampler_iff`: the law is
`R/Z` iff no such edge, since `R/Z` charges `s₀`). Read through `app:notation` it holds in every
case (`universality_graphs_sampler`: the law is `R|_𝒮/R(𝒮)`). A finding reported on one reading
alone overstates the paper's error. Relatedly, `CycleDivergence.termLaw G F` divides by the
terminal mass over **all** of `𝒱`: it is the law of `s_τ` only when `F(s₀ → s_f) = 0`
(`Graph.Sampling.sampler_termLaw`'s `hss`); `samplerLaw` divides over `𝒮` and needs no hypothesis.
