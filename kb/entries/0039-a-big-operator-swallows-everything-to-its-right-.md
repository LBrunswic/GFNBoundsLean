---
id: 0039
title: A big operator swallows everything to its right: parenthesize it inside a statement
kind: pitfall
tags: [fidelity, big-operators, statements]
confidence: provisional
sources: [GFNBounds/Balance/TBGradient.lean]
created: 2026-09-18
---

## When

Transcribing a paper display that mixes a product or sum with a factor or quotient *after* it —
`F(x_ℓ) ∏_k a_k / (F(x_0) ∏_k b_k)`, `∑_k c_k + d`, `c · ∑_k f_k / w` — into a Lean statement.

## Do

Parenthesize every big operator whose scope ends before the end of the expression:

```lean
marg pb μ (τ (Fin.last ℓ)) * (∏ k : Fin ℓ, pb (τ k.succ) (τ k.castSucc))
  / (marg pb μ (τ 0) * ∏ k : Fin ℓ, fwd pb μ (τ k.castSucc) (τ k.succ))
```

and check the elaborated statement (hover, or read the goal after `intro`) against the display.

## Why

`∏ k, f k / c` parses as `∏ k, (f k / c)`: the binder body extends as far right as possible. The
unparenthesized telescoping identity of `prop:tb_gradient` elaborated to
`F(x_ℓ) · ∏_k (π_←(…) / (F(x_0) ∏ π_→^μ))` — a different formula, off by a power of the
denominator, that type-checks. Here the proof failed and exposed it; in a *hypothesis*, or in a
statement whose proof goes through anyway (e.g. at `ℓ = 1`, where both readings agree), nothing
would, and the file would certify a formula the paper does not print. The one-line checklist
review of kb `0004` compares prose to prose and does not see it.
