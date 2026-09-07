---
id: 0014
title: The tactic economy of this library
kind: pattern
tags: [tactics, style]
confidence: established
sources: [docs/REPO-MAP.md]
created: 2026-09-07
---
## When

Choosing how to close a routine goal, or matching the surrounding style.

## Do

Measured over the 29 strict-library files, in order of use: `rw` (554), `linarith` (203), `omega`
(154), `ring` (147), `simp` (140), `positivity` (98), `exact_mod_cast` (86), `norm_num` (74),
`nlinarith` (69), `field_simp` (35), `calc` (35), `bound` (30), `gcongr` (10).

Rules of thumb that hold here:

- **ℕ index arithmetic, including `-`, `/`, `%`** → `omega`, before any cast to ℝ.
- **Linear real inequality from hypotheses in context** → `linarith`. Feed it the facts as `have`s
  first; it will not find `S.eps_lt_one hj` on its own.
- **`0 < x` / `0 ≤ x` for a product, power or `rpow`** → `positivity`.
- **Monotone rewriting inside a sum or a product** → `gcongr`, then `bound` for the leaves.
- **Chains of inequalities worth reading** → `calc`. 35 uses; this is a library people audit.
- `simp only [...]` with an explicit list, not bare `simp`, in the `pstar` case splits — the goal
  shapes are fragile and a bare `simp` makes the next Mathlib bump someone else's problem.

## Why

Not style for its own sake: the strict library is built with `warningAsError := true`, so an
unused-variable or deprecation warning is a **build failure**. Tactics that leave the goal in an
unpredictable shape cost more here than they do in ordinary Mathlib work.
