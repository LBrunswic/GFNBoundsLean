---
id: 0034
title: To widen a theorem to a second instance, abstract the facts its proof uses — do not copy the proof
kind: pattern
tags: [design, reuse, generators]
confidence: established
sources: [GFNBounds/Balance/SqGenerator.lean:133, GFNBounds/Balance/SqGenerator.lean:190]
created: 2026-09-13
---
## When

A proved theorem is hard-wired to one instance (`g = (log x)²`) and the paper claims it for another
(`(x − 1)²`) "by the same computation".

## Do

List the facts about the instance the proof actually consumes (a derivative formula, a far-field
bound), state a generic theorem taking them as hypotheses (`no_distant_equilibrium_three_far_of`),
and recover both instances by discharging them (`no_distant_equilibrium_three_sq`). If the chain
of files the proof runs through is hard-wired too, that is the cost to estimate before starting —
the `(x − 1)²` convergence was moved to Wave 2 for exactly that reason.

## Why

A copied proof doubles the maintenance and hides which facts the paper's "same computation"
really needs; the abstracted one makes that list a signature.
