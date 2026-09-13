---
id: 0032
title: An almost-sure clause about a finite-horizon chain can be stated pathwise, with no chain
kind: pattern
tags: [markov, modelling, paths, fidelity]
confidence: established
sources: [GFNBounds/Doubling/DescentStatement.lean:150, GFNBounds/Doubling/DescentStatement.lean:335]
created: 2026-09-13
---
## When

The paper says "almost surely the chain started at `m` does …" within a bounded number of steps,
and the library has no path-space measure for that chain.

## Do

State the clause for every allowed path (`IsDescentPath ℓ Y`): on a finite path space, "almost
surely" for a kernel with the stated support is exactly "for every path of positive probability",
and those are the allowed paths. Prove the allowed-path set non-empty (`exists_descentPath`) so the
statement is not vacuous, and record the pathwise modelling in the row's scope notes.

## Why

It avoids `Kernel.traj` entirely and loses nothing on a finite horizon. It does **not** transfer
to unbounded horizons, where a null set of paths can be infinite and "every allowed path" is
strictly stronger than "almost surely" — recurrence statements still need a chain.
