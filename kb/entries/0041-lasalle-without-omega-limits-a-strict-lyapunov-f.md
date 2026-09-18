---
id: 0041
title: LaSalle without omega-limits: a strict Lyapunov function on a compact set gives a uniform rate off its maximiser
kind: pattern
tags: [flow, convergence, compactness, lyapunov]
confidence: provisional
sources: [GFNBounds/Balance/GlobalConvergenceFinite.lean]
created: 2026-09-18
---

## When

A paper proof concludes convergence of a flow "by LaSalle's principle" (the `ω`-limit lies in
`{V̇ = 0}`, which is one point). Mathlib v4.31.0 has no `ω`-limit sets for ODE trajectories, and
routing through a local exponential phase drags in a coercivity constant the statement never
names (that is what tied `GlobalConvergence.lean` to marked graphs).

## Do

If the trajectory is known to stay in a compact `𝒦` and `V` is monotone and bounded along it,
with `V̇ = F(u)`, `F` continuous on `𝒦` and positive off the maximiser:

1. Prove `V(u_t) → V*` by contradiction: assume `V(u_t) < V* − ε` for all `t` (monotonicity turns
   "not eventually" into "never"), shrink to `𝒦_ε := 𝒦 ∩ {V ≤ V* − ε}` (closed, via
   `isClosed_le`), take `IsCompact.exists_isMinOn` of `F` there — its minimum `η > 0` because the
   maximiser is not in `𝒦_ε` — and integrate: `t ↦ V(u_t) − ηt` is monotone
   (`monotoneOn_of_deriv_nonneg`), contradicting the bound at `t = (V* − V(u_0))/η + 1`.
2. Turn `V → V*` into convergence of the state with an identity that pins the state at `V*`
   (here Pythagoras on the invariant sphere: `‖u − Πu‖² = n₀² − (Πu)²`).

For `HasDerivAt (fun t => m t - η * t)` use `(h.fun_sub ((hasDerivAt_id' s).const_mul η))`;
`.sub` produces `m - fun y => η * y`, which `simpa` does not match against the lambda.

## Why

Needs no `ω`-limit calculus and no rate constant, and it certifies the paper's qualitative
sentence with its own Lyapunov function. `FlowGenerator.tendsto_of_flow` in the source file is the
worked instance (mass ascent on the `L²(λ)` sphere, floor `u_min` keeping `𝒦` in the open cone).
