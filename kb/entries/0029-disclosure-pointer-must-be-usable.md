---
id: 0029
title: A disclosure must point at a theorem the file can apply, and name the real blocker
kind: pitfall
tags: [scope, disclosure, review, fidelity]
confidence: established
sources: [GFNBounds/Balance/LocalConvergenceClauses.lean:45, GFNBounds/Graph/CycleBlowup.lean]
created: 2026-09-13
---
## When

Writing a SCOPE bullet that says a clause "is `Foo.bar`" or "is blocked by obstruction N".

## Do

Check the pointed-at theorem's hypotheses against what the file has in hand; if the file cannot
discharge them, the pointer launders a gap — prove the local form instead. For a disclosed gap,
name the concrete missing piece (a definition, a Mathlib API, a layer), not a catalogue number
that may not be the one that binds.

## Why

`local_convergence_gd`'s third well-definedness clause (`D_k` is the gradient) pointed at
`FirstVariation`, whose lemmas need `g` differentiable everywhere; the discrete clause has it only
at the values `r` takes. The rework proved window-local forms (`hasDerivAt_loss_local`). In
`CycleBlowup.lean` (and the graduated `CycleExample.lean:66–68`) an uncovered clause cited
"obstruction 2", which is not what blocks it.
