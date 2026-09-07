---
id: 0016
title: Test a formalized constant against `exp20` before believing it
kind: workflow
tags: [constants, validation, numerics]
confidence: established
sources: [README.md]
created: 2026-09-07
---
## When

You just proved a statement with an explicit constant, an exponent, or a numerical claim.

## Do

Instantiate it and compare with the measured run at `~/NonAcyclicGFN/results/exp20*.csv`:

| quantity | measured | predicted |
|---|---|---|
| `σ̄` at `c = 0.25` | `6.000000` | `j̄/(1−c)` with `j̄ = 4.5` |
| `σ̄` at `c = 0.5` | `8.99991` | same |
| fitted `p_*` | 4.130 / 2.659 / 1.719 / 1.269 | 4.1314 / 2.6599 / 1.7189 / 1.2691 |
| cut balance | exact to `0.0e0` | — |
| `1/λ(s₀) − σ̄` | `[1.999999994526, 2.000000000004]` | `2` — this is `Kac.lean`'s identity |

## Why

**Any Lean statement whose numerical instance disagrees with that data is wrong**, however green
the build. A type-correct theorem about the wrong object still type-checks, and on this material
that failure mode has occurred: the retraction list in the lab register shows careful checking
finding real errors after the claim was written down.

The gap also tells you when a bound is merely *true* rather than *good*: `ϑ` is proved at 0.0024
against a measured 0.22, which is the project's currently flagged weakest link.
