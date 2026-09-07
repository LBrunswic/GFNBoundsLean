---
id: 0003
title: `Stat.inv` only accepts *bounded* test functions — bound first, then sum
kind: pitfall
tags: [stat, tsum, summability]
confidence: established
sources: [GFNBounds/Doubling/Setting.lean:355]
created: 2026-09-07
---
## When

You want to use invariance of `λ`, or you are staring at a `Summable (fun x => L.lam x * f x)`
side goal.

## Do

Invariance is carried in integral form and takes the boundedness witness explicitly:

```lean
L.inv : ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) → ∑' x, L.lam x * pstar S cap f x = ∑' x, L.lam x * f x
```

So produce `⟨C, hC⟩` first. Then the two workhorses are free:

```lean
L.summable_mul   (hf : ∃ C, ∀ x, |f x| ≤ C) : Summable fun x => L.lam x * f x
L.tsum_sub_pstar (hf : ∃ C, ∀ x, |f x| ≤ C) : ∑' x, L.lam x * (f x - pstar S cap f x) = 0
```

`pstar_bounded` transports the bound across `P⋆` for free (`P⋆` is an average, so it cannot
enlarge the range) — that is how `tsum_sub_pstar` gets the *second* summability it needs.

## Why

`Stat` deliberately does not carry pointwise invariance `λT = λ`. The integral form is what every
downstream statement consumes (`prop:doubling_cut` tests it against an indicator), and it needs no
summability side condition **at the point of use** — the condition is discharged once, here, from
boundedness. Reaching for a pointwise form means proving the bridge `Stat.of_pointwise`, which is
open. Do not start there; bound the test function instead.
