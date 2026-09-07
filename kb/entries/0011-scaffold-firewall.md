---
id: 0011
title: The scaffold firewall: where to put a proof, and how to tag a `sorry`
kind: convention
tags: [sorry, audit, workflow]
confidence: established
sources: [scaffold/GFNBoundsScaffold.lean:1, scripts/sorry_audit.py]
created: 2026-09-07
---
## When

Writing anything that is not finished, or deciding which library a new file belongs in.

## Do

New work starts in `scaffold/GFNBoundsScaffold/`. `sorry` is a **compile error** in `GFNBounds/`
(`warningAsError := true`), so a file only moves there once it is closed — and that move is the
master session's call, not a sub-session's.

Every scaffold `sorry` must read, on one line:

```lean
  sorry -- SORRY(prop:doubling_phase): Foster's criterion for positive recurrence; Mathlib v4.31.0 has no discrete-time Markov-chain recurrence theory.
```

A bare `sorry` fails `scripts/sorry_audit.py`. Each is keyed by `sha1(label + decl)[:8]`, and the
audit fails if an id is **new** or the count **rose**. Deliberately adding one means
`python3 scripts/sorry_audit.py --accept`, which rewrites the baseline as a reviewable diff — a
decision to be taken explicitly, never as a way to get a build green.

## Why

Two locks, not one. `sorry`-as-compile-error catches a `sorry` *written* in `GFNBounds`; it does
not catch a theorem there resting on a tagged `sorry` reached through an import. That is why
`GFNBounds` never imports `GFNBoundsScaffold`, and why `GFNBounds/Audit.lean` re-checks every
certifying declaration with `#print axioms` — `scripts/axiom_audit.py` fails on `sorryAx` or on
any axiom outside `{propext, Classical.choice, Quot.sound}`.

Graduation being a *file move* is what makes "the sorry list only shrinks" enforceable by the
compiler rather than by discipline.
