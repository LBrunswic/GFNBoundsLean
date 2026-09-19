---
id: 0043
title: Pumping a cycle under ONE Markov policy: simple cycle, first entry, last exit
kind: pattern
tags: [markov, cycle, walks, policy]
confidence: provisional
sources: [GFNBounds/Silva/PathSpaceMarkovGeneral.lean]
created: 2026-09-19
---

## When

A statement quantifies over **Markov** policies (`pol : V → V → ℝ`, one choice per state) and needs
a family of walks that wind `k` times around a cycle of an arbitrary graph, with a policy that
follows each walk with a controlled probability. The given data is a closed walk on some walk into
`x`, which may revisit states — and a pumped walk that revisits a state with two different
successors cannot be followed by a single Markov policy.

## Do

Normalise the walk into three pieces whose decisions never conflict
(`GFNBounds/Silva/PathSpaceMarkovGeneral.lean`):

1. **Simple cycle by minimality, as a function, not by list slicing.** Turn the closed walk into
   `p : ℕ → V` (`(v :: c).getD t v`), take `Nat.find` of the length among closed walks staying in
   the set `{y | Reach s₀ y ∧ Reach y x}`; a repeated state would give a shorter closed walk
   `t ↦ p (i + t)`. Package the result as an `L`-periodic `q : ℕ → V`, injective on `[0, L)`
   (`SimpleCycle`, `exists_simpleCycle`). Periodicity makes "wind `k` times" the index shift
   `k * L` (`q_add_mul`).
2. **First entry / last exit** by `Relation.ReflTransGen.head_induction_on`: a prefix whose
   states before the last are off the cycle (`first_entry`), a suffix whose states after the first
   are off it (`last_exit`, via the dichotomy `last_exit_or`).
3. The policy: on the cycle, extra weight `a` on the cycle successor plus `(1 − a)/deg` on every
   out-edge; off it, uniform. Off-cycle steps then cost a `k`-independent constant, cycle steps
   `≥ a`, the exit `≥ (1 − a)/|V|`.

Lower bounds multiply through `pathProb (l ++ b :: r) = pathProb (l ++ [b]) * pathProb (b :: r)`
(`pathProb_append_cons`). For **upper** bounds over every full-support Markov policy (`IsFullSupportMarkov`); the argument uses only non-negativity and row sums, so it extends to every Markov policy, but that is not stated. Count the passages
through the exit state along the cycle (`cnt`, `cnt_ge_mul`) and use `p^k (1 − p) ≤ 1/(k+1)`.

## Why

With `a = (m+1)/(m+2)` the pumped walk has probability `≍ 1/k`, never better
(`p^k(1−p) ≤ 1/(k+1)`), so `sup M' = +∞` must come from *summability* of `p_B` along the family
(`liminf (k+1) p_B(τ_k) = 0`), not from `inf p_B = 0`. That is the mechanism the 2026-09-18
rewording of `rem:path_space` states. The list-slicing route to a simple cycle (indices `i < j`
with `c[i] = c[j]`, `take`/`drop` chains, `getLast?` of a `take`) is much longer than the
`Nat.find`-on-functions route.
