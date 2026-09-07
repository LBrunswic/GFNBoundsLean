---
id: 0007
title: Constants are explicit formulas, never a bare `∃ C`
kind: convention
tags: [constants, effectivity]
confidence: established
sources: [GFNBounds/Doubling/R0Bound.lean:22]
created: 2026-09-07
---
## When

The paper says "there exist `c₄ > 0` and `ℓ₁` depending on `c` and `d` alone such that …".

## Do

Give the formula. `R0Bound.lean` is the precedent: where the paper has a non-effective `c₄`, the
Lean has

    c₄ = 16 c τ,   valid at every m ≥ 1,     ℓ₁ = max (d + 1) (32 c τ)

and `½ ≤ R₀ ≤ 2` follows for `m ≥ ℓ₁`. State the constant in the signature, not existentially.

## Why

Effectivizing is one of the project's two stated goals. `c₄` and `ℓ₁` are the root: `ℓ₂, ℓ₃, ℓ₄,
m₀, m₃, c₃, c₅, c₆, c₉, K₀, c₈` all inherit non-effectivity from them, so an `∃` here propagates
through the whole downstream block and is very expensive to remove later.

It is also the project's own quality check. The author has flagged the weakest link: `ϑ` is proved
at 0.0024 against a **measured** 0.22. A named constant can be tested against `exp20`
(`~/NonAcyclicGFN/results/exp20*.csv`); an existential cannot. Any Lean statement whose numerical
instance disagrees with that data is wrong — see [[0016-check-against-exp20]].
