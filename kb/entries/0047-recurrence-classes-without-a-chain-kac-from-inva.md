---
id: 0047
title: Recurrence classes without a chain: Kac from invariance, renewal by induction, solidarity by Green sums
kind: pattern
tags: [markov, recurrence, kac, renewal, least-solution]
confidence: provisional
sources: [GFNBounds/Doubling/RecurrenceClass.lean]
created: 2026-09-19
---

## When

A statement needs "recurrent", "transient", "positive/null recurrent", Kac's formula, or
uniqueness of an invariant probability on the doubling graph — the obstruction-1 labels of kb
`0006`. Mathlib has no recurrence theory, and none is needed.

## Do

Define every class through least solutions on the function action `pstar` (ruling R8), as
`GFNBounds/Doubling/RecurrenceClass.lean` does: `fpass y k` (first passage at
exactly `k`), `hitP = Σ fpass`, `hitT` (expected time, own recursion), `retP n = P⋆(hitP n)(y)`,
`retT n = 1 + P⋆(hitT n)(y)`. Then four moves close everything:

* **Kac from invariance.** `hitT (n+1) − P⋆ hitT n = 1 − retT n · 1_y` and
  `hitT (n+1) − hitT n = 1 − hitP n`; integrate both against `Stat` with `tsum_sub_pstar` and get
  `Σ λ·hitP n = λ(y)·retT n` (`Stat.kac_hitP`). Since `hitP ≤ 1`, any `Stat` makes every state
  positive recurrent; with `hitProb ≡ 1` and Tannery (`tendsto_tsum_of_dominated_convergence`)
  it gives `λ(y) = 1/E_yτ⁺`, hence uniqueness.
* **Renewal by induction, not generating functions.** `(P⋆)^[n] 1_y x = Σ_k fpass k x · u(n−k)`
  by induction on `n` generalizing `x`; the last-exit identity `Σ u(n) r(N−n) = 1` then follows by
  induction on `N` with `Finset.sum_range_reflect`. Linear/sublinear growth of the Green sums uses
  `Finset.sum_range_diag_flip`.
* **Solidarity** from `P⁽ᵃ⁺ⁿ⁺ᵇ⁾(x,x) ≥ P⁽ᵃ⁾(x,y)P⁽ⁿ⁾(y,y)P⁽ᵇ⁾(y,x)`, which is two applications
  of "`g ≥ g(w)·1_w` and `P⋆` is monotone" (`pstar_iterate_ge_ptFn_mul`); positivity of
  `P⁽ᵃ⁾(x,y)` from `Reach` by `edge_pstar_pos`.
* **Lyapunov criteria as comparisons.** Transience: `1 − P(σ > n) ≤ W/w` by induction on `n`
  (`ladder_survival_ge`). Recurrence: a maximum principle for `lim P(σ > n) − (Q(1−δ) + (Q/M)V)`
  on the finite window `(j₀, J]`, taking the *least* maximiser with `Nat.find`
  (`ladder_recurrent`).

## Why

Every one of these is a finite-sum or pointwise-limit argument on a recursion the library already
had, so none needs a path space, optional stopping or the strong Markov property. The two
`Stat`-based moves also bypass Foster's criterion entirely: existence of an invariant probability
(already proved) *implies* positive recurrence through Kac. Infinite expectations must be stated
as `¬ BddAbove` of the truncations — `⨆` of an unbounded real family is a junk value.
