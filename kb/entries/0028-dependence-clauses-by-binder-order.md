---
id: 0028
title: "Depending only on" is binder order or a congruence — and a bundled bound field leaks into it
kind: pattern
tags: [constants, effectivity, quantifiers, structures]
confidence: established
sources: [GFNBounds/Doubling/TruncationBhat.lean:70, GFNBounds/Doubling/MainPackaging.lean]
created: 2026-09-13
---
## When

The paper says "there is `c > 0`, depending only on `c` and `d`, such that for every setting …",
and the proof's constants flow through a structure with free fields (`Setting.epsMax`).

## Do

Addendum to 0007 and 0010. Place the existentials **before** the setting: `∀ d, ∃ m₀ K₀ c₉, ∀ S,
S.d = d → …`; `∃` after `∀ S` expresses nothing about dependence. Where a witness is a formula,
certify the clause as a congruence (`c7Of_congr`: equal block data ⇒ equal constants). When a
lemma bounds through a free field the paper pins (`ε_max = c/2`), do not add a hypothesis
`S.epsMax = c/2` — rebuild the structure with the field replaced (`Setting.withEpsMax`) and prove
the replacement is the identity on everything the conclusion reads (`Stat.withEpsMax_lam`, `rfl`).

## Why

A hypothesis `S.epsMax = c/2` makes the constant depend on a field of `S`, which the dependence
clause forbids, and restricts the theorem to settings that happen to carry that field value. The
structure update removes both: the chain, `P⋆` and every invariant probability are unchanged.
