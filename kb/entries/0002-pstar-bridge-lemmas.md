---
id: 0002
title: Use the `pstar` bridge lemmas, not `pstar_lad_succ`, at a general `j ≥ 1`
kind: pattern
tags: [pstar, index-arithmetic]
confidence: established
sources: [GFNBounds/Doubling/Setting.lean:242]
created: 2026-09-07
---
## When

The state is `.lad j` with a hypothesis `1 ≤ j`, rather than a literal `.lad (j + 1)`.

## Do

```lean
pstar_lad_of_hasDouble    (hj : 1 ≤ j) (h :   HasDouble cap j) :
    pstar S cap f (.lad j) = S.eps j * f (.lad (2 * j)) + (1 - S.eps j) * f (.lad (j - 1))
pstar_lad_of_not_hasDouble (hj : 1 ≤ j) (h : ¬ HasDouble cap j) :
    pstar S cap f (.lad j) = f (.lad (j - 1))
```

## Why

`pstar_lad_succ` is stated at `.lad (j + 1)` because that is the shape of the defining match.
Rewriting a goal about `.lad j` into that shape by hand costs a `Nat.succ_pred_eq_of_pos` dance
every time (see [[0008-nat-predecessor-rfl]]); the two bridge lemmas have already paid it, and
they hand you the statement in the paper's own indexing, with truncated `j - 1` on the right.

`hasDouble_mono` is the companion: a surviving doubling edge at `m` survives at every `j ≤ m`.
That single monotonicity is why `lem:doubling_percut` needs only `2m ≤ K` to cover the whole
window `W(m)`.
