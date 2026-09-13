---
id: 0027
title: Dropping a hypothesis can be vacuous — check the quantified structure is inhabited where it fails
kind: pitfall
tags: [hypotheses, vacuity, scope, review]
confidence: established
sources: [GFNBounds/Doubling/MainPackaging.lean:55, GFNBounds/Doubling/TruncationBhat.lean]
created: 2026-09-13
---
## When

A SCOPE note or checklist row says "hypothesis `H` of the paper is not needed", and the statement
quantifies over a structure (`Stat S (some K)`, an invariant probability, a flow).

## Do

Ask whether the structure exists at all where `H` fails. If it does not, the unrestricted
statement holds vacuously there: say "holds vacuously at ¬H, because …", name the non-vacuous case,
and point at the theorem showing that case is inhabited. Never write "`H` is not needed".

## Why

`B̂_K ≥ c₈ √K` was stated for every `K ≥ K₀` with the note "evenness not needed". At odd `K` the
ladder state `K` has no on-chain predecessor, invariance forces `λ^K(K) = 0` against on-chain
positivity, and no `Stat S (some K)` exists — so the odd case is empty, not proved. Both the prover
of `TruncationBhat.lean` and of `MainPackaging.lean` wrote the same sentence independently; the
auditor caught it in each.
