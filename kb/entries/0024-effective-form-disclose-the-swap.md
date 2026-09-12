---
id: 0024
title: 'When rule 1 and rule 3 collide: prove the effective form, disclose the swap'
kind: convention
tags: [fidelity, constants, effectivity, scope]
confidence: established
sources: [GFNBounds/Balance/Expansion.lean:88, kb/entries/0005-never-outrun-the-paper.md]
created: 2026-09-12
---
## When

The paper states a result with a *qualitative* constant — `c(ε) → 0`, `o(‖h‖)`, "there exists
`C`" — under a *weak* regularity hypothesis, and the effective version needs a stronger one.
Rule 1 says state the paper's theorem; rule 3 forbids its constant.

## Do

Prove the **effective** statement under the **stronger** hypothesis, and choose the
strengthening that the paper's own downstream consumer already assumes. Then:

- mark the checklist row `⚠ strengthened`;
- say in `SCOPE` that the weak-hypothesis statement is **not** stated, and that neither
  statement implies the other;
- record, in the same paragraph, how the weak form *would* be proved, so the gap is a named
  choice rather than an omission.

`theo:gd_diffusion_full` is the worked instance: its own statement is `C²` with a non-effective
`c(ε) → 0`; Step 1 of `theo:local_convergence_full` — the only consumer either display has —
uses `C³`. The Lean proves `c(ε) = 2Kε` under a `C³`-type Taylor bound, and its SCOPE says the
`C²` form is reachable by replacing the Taylor remainder with the modulus of continuity of `g'`
at `1`, and is deliberately unstated.

## Why

The alternatives are worse in both directions: an `∃ C` that no `exp*` run can test (kb `0016`),
or a `Tendsto` with no rate, which certifies nothing a reader wants. Both rules survive if the
swap is visible; only silence violates either. And the `sorry` firewall has no analogue for
hypothesis creep, so the docstring checklist is the only place it can be caught — see kb `0022`
for the same gap in its other direction.
