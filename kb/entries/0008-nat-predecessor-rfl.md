---
id: 0008
title: The ℕ-predecessor idiom: `obtain ⟨i, rfl⟩ : ∃ i, j = i + 1`
kind: pattern
tags: [nat, index-arithmetic, omega]
confidence: established
sources: [GFNBounds/Doubling/Setting.lean:245]
created: 2026-09-07
---
## When

You have `hj : 1 ≤ j` and need the goal in `j + 1` shape — typically to fire a `Nat.succ`-indexed
definitional lemma such as `pstar_lad_succ`.

## Do

```lean
obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, (Nat.succ_pred_eq_of_pos hj).symm⟩
```

The `rfl` substitutes throughout, so the truncated `j - 1` in the goal becomes a genuine `i` and
every `omega` downstream gets easier.

## Why

Truncated ℕ subtraction is the main source of friction in this library — `j - 1` at `j = 0` is
`0`, not `-1`, and no `simp` set will tell you that is where the proof went wrong. Substituting
the successor form removes the subtraction rather than reasoning about it.

Where the subtraction has to stay, `omega` is the tool: it knows truncated subtraction, `/`, and
`%` on ℕ, and it is used 154 times here. Cast to ℝ **after** the ℕ facts are settled
(`Nat.cast_sub` needs the inequality as a hypothesis), never before.
