---
id: 0015
title: Recursions on the window use `Nat.strong_induction_on`
kind: pattern
tags: [induction, cut-balance, descent]
confidence: established
sources: [GFNBounds/Doubling/Constant.lean:80]
created: 2026-09-07
---
## When

Proving a property of a `CutBalanceSeq` or of `Decay.extend` at every `m` — anything where the
value at `m` is determined by values on the window `W(m) = {⌈m/2⌉, …, m−1}`.

## Do

```lean
induction m using Nat.strong_induction_on with
| _ m ih => ...
```

`Constant.lean` uses exactly this five times over (`extend_cutBal`, `extend_unique`, `extend_pos`,
`extend_add`, `extend_smul`). Ordinary `Nat.rec` does not fit: the window reaches down to `⌈m/2⌉`,
not to `m - 1`.

## Why

This is the formal counterpart of the appendix's "by induction on `y`": the descent chain is
strictly decreasing and absorbed in at most `m` steps from a deterministic start, so every
quantity from `lem:doubling_descent` through `lem:doubling_coupling` is a **finite** path
expectation. That is precisely what makes the decay block reachable without any Markov chain
theory — see [[0006-three-obstructions]].
