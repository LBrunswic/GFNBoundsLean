---
id: 0051
title: A stationary window (path) measure on Fin tuples needs no path space — peel x_0 with Fin.consEquiv and induct
kind: pattern
tags: [markov, paths, window, fin, stationarity]
confidence: provisional
sources: [GFNBounds/Balance/TBHessian.lean]
created: 2026-09-19
---

## When

A statement integrates against an explicit trajectory measure on `𝒮^{ℓ+1}`, such as the window
measure `ν̂(x_0,…,x_ℓ) = λ(x_ℓ) ∏_k π(x_k → x_{k−1})` of `prop:tb_hessian`, and the proof says
"under `ν̂` the edges form a stationary Markov chain", then uses one- and two-time marginals
(`𝔼 u(e_j)u(e_k) = ⟨u, Q^{k−j}u⟩`). Mathlib's `Kernel.traj` is not needed, and neither is any
Markov-chain API.

## Do

Keep `ν̂` as a weight function on `τ : Fin (ℓ+1) → V` and prove everything by induction on `ℓ`,
peeling the **first** coordinate (the end the chain runs towards):

* `∑ τ, F τ = ∑ x, ∑ τ', F (Fin.cons x τ')` by
  `rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]; rfl`;
* `window (ℓ+1) (Fin.cons x τ) = π(τ 0, x) · window ℓ τ` by `simp only` with `Fin.prod_univ_succ`,
  `← Fin.succ_castSucc`, `Fin.cons_succ`, `Fin.cons_zero`, `← Fin.succ_last`;
* summing out `x_0` against a function of `Fin.tail τ` uses the row sums (`window_tail`); a function
  of `x_0` alone uses invariance (`window_state`, base case via `Equiv.funUnique (Fin 1) V`);
* the two-point law is one induction on `ℓ` with `Fin.cases` on both indices `j ≤ k`: `(0,0)` is
  `window_state`, `(0, k'+1)` turns the `x_0`-sum into `(Qa)(e'_0)` and recurses at index
  `⟨0, _⟩ : Fin ℓ` (not `0`, which needs `NeZero ℓ`), `(j'+1, k'+1)` is `window_tail`.

Get the variance `𝔼(∑_k u(e_k))²` by the same peeling (split off `u(e_0)` with
`Fin.sum_univ_succ`), not by counting pairs `j < k` with difference `m`: the recursion
`V_{ℓ+1} = V_ℓ + ‖u‖² + 2∑_{m<ℓ}⟨u,Q^{m+1}u⟩` closes with one `Finset.sum_range_succ`.

Do the combinatorics on `V → V → ℝ` (functions of pairs, `Q f (s,_) = ∑_z π(s,z) f(z,s)`) and
bridge to the edge subtype once, by `sum_edgeSet_eq` and an extension-by-zero `uAt`.

## Why

The whole of `eq:tb_window_variance` — marginals, two-point law, variance — took four short
inductions (~150 lines). The pair-counting route and any path-space route are both much longer,
and the peel-`x_0` recursion is exactly the paper's "backward chain started from `x_ℓ ∼ λ`" read
from the other end.
