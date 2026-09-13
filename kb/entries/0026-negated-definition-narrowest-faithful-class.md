---
id: 0026
title: A negated definition must be stated over its narrowest faithful class, read from the source
kind: pitfall
tags: [fidelity, negation, external-source, review]
confidence: established
sources: [GFNBounds/Graph/FrozenUnstableDB.lean:177, GFNBounds/Graph/FrozenUnstableDB.lean:469]
created: 2026-09-13
---
## When

Proving `¬ P` where `P` is a definition the paper takes from a cited source ("unstable in the sense
of …"), and `P` quantifies over a class of objects.

## Do

Read the cited definitions, not the proof prose that uses them, and transport the class exactly.
Then look for a witness that is `P` under the source's definition but not under yours; if one
exists the class is too wide and `¬ P` proves less than the paper claims. Narrow the class only
where the negation stays safe (fewer objects checked ⇒ source's `P` implies yours ⇒ your `¬ P`
implies the source's), and disclose each narrowing in the predicate's **docstring** as well as in
SCOPE — a later positive `P` result would certify less than the source's.

## Why

The first `Stable` of `prop:frozen_unstable_full` quantified over arbitrary non-negative edgeflows
and circulations read off the proof, wider than Definitions 1–3 of `brunswic2024theory`: the
auditor's loss `L(F) = −F(s_f → s₀)` is stable in the source's sense and not in the Lean's, so the
`¬ Stable` theorem type-checked under the paper's label while proving something weaker. The rework
(`IsFlow`, `IsZeroFlow`) transports the classes exactly, narrowing `0`-flows only at a possible
edge `s₀ → s_f`, the safe direction.
