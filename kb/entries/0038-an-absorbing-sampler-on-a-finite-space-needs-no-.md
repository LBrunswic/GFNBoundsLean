---
id: 0038
title: An absorbing sampler on a finite space needs no path measure: flag the stop and take marginals
kind: pattern
tags: [markov, modelling, sampler, fidelity]
confidence: provisional
sources: [GFNBounds/Core/Sampling.lean:1]
created: 2026-09-18
---

## When

A statement about a sampler with a random stopping time on a finite state space — "`𝔼(τ) ≤ …`",
"`s_τ ∼ μ`", "terminates almost surely" — over an **unbounded** horizon, so kb `0032`'s pathwise
reading does not apply, and `Kernel.traj` looks like the only way in.

## Do

Put the stop in the state: a chain on `V × Bool`, `(x, true)` absorbing, and define its law by the
forward recursion `law (n+1) z = ∑ w, law n w * K w z` (a `rfl` lemma `law_succ` first — `simp
only [law]` unfolds *every* `law n`, not just the head). By absorption every event is an event of
one marginal: `{τ > n} = {X_n ∈ V × {false}}`, `{τ ≤ n, s_τ = y} = {X_n = (y, true)}`, and
`𝔼(τ) = ∑ₙ P(τ > n)`. Then the analysis is linear algebra on `q n y := law n (y, false)`:
partial sums dominated by any non-negative solution of the occupation recursion (induction +
`summable_of_sum_range_le`), the occupation's own recursion by passing to the limit on both
sides (`tendsto_nhds_unique`, no `tsum` algebra), and `Summable.tendsto_atTop_zero` for
termination. `GFNBoundsScaffold/Core/Sampling.lean` is the worked instance (~570 lines with its witness, no
`Kernel.traj`).

## Why

Everything `theo:sampling_theorem` asserts is a function of the marginals, so a path measure adds
API cost (Ionescu–Tulcea, `partialTraj` projections) and no content. Disclose it in SCOPE as
"modelled by its time-`n` marginals". The occupation-measure step is where the draft once went
wrong: the occupation is the *minimal* solution, not `F_term + F⋆_out`; prove domination, never
equality (`Parked.strict` shows the gap).
