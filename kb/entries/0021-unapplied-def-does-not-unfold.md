---
id: 0021
title: A `def` whose body is a trailing lambda will not unfold unapplied
kind: pitfall
tags: [simp, defs, rewriting, tactics]
confidence: established
sources: [GFNBounds/Balance/L2Toolkit.lean:235, GFNBounds/Balance/Expansion.lean:186]
created: 2026-09-12
---
## When

You define an operator in the shape the `Balance` and `Core` layers use throughout —

```lean
def perpL2 (lam h : V → ℝ) : V → ℝ := fun x => h x - Graph.meanL2 lam h
```

— and then rewrite somewhere the definition stands as a **function**, not applied to a state:
`ipL2 lam (perpL2 lam h) (perpL2 lam h)`, `funAct K (Aop K lam h) x`, `nrmL2 lam (Adj K φ)`.

## Do

Ship both equation lemmas beside the definition, and use the one matching the position:

```lean
theorem perpL2_eq (lam h : V → ℝ) : perpL2 lam h = fun x => h x - Graph.meanL2 lam h := rfl
theorem perpL2_apply (lam h : V → ℝ) (x : V) : perpL2 lam h x = h x - Graph.meanL2 lam h := rfl
```

`Core.densAct_apply` and `Core.funAct_apply` are the existing precedent for the second; the
first was missing across the whole layer and is now supplied for `Aop`, `Adj`, `perpL2` and
`linHess`.

A related cost of the same kind: `Core.funAct` and `Balance.funAct` are the *same* definition
but are not syntactically equal, so `rw` will not cross between them. Pin the defeq once with
an ascribed `have h : <the shape you want> := <the Core lemma>` and rewrite with `h`.

## Why

Lean generates the equation lemma of a `def` at full arity, binders of a trailing lambda
included, so `perpL2.eq_1` is about `perpL2 lam h x` and `simp only [perpL2]` silently makes
**no progress** on `perpL2 lam h` alone. The failure shows up as `simp made no progress` several
lines from the cause, or — inside a longer `simp only` list — as a goal that quietly does not
change. Two `rfl` lemmas per operator cost nothing and remove the whole class of failure.
