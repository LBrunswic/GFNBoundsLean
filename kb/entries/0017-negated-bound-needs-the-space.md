---
id: 0017
title: A "no bounded inverse" statement must quantify over the space the operator acts on
kind: pitfall
tags: [fidelity, review, unbounded, linfty, quantifiers]
confidence: established
sources: [GFNBounds/Doubling/Ramp.lean:239, GFNBounds/Doubling/Unbounded.lean:325]
created: 2026-09-07
---
## When

You render the paper's "no bounded operator `S` on `L^p(λ)` satisfies `S(Id−P⋆) = Id−Π`" as a
negated inequality `¬ ∃ B, ∀ f, … → ‖f‖ ≤ B ‖(Id−P⋆)f‖`, because the library builds no `L^p`
space for that `p` (here `p = ∞`). The statement type-checks, the proof closes with the paper's
witnesses, and the build is green.

## Do

Restrict the inner `∀ f` to the functions that *are* elements of the paper's space — for
`L^∞(λ)` that is `(∃ C, ∀ x, |f x| ≤ C) →`, as `no_bounded_inverse` already does for finite
`p`. Then check the direction: a bounded `S` would supply `B = ‖S‖` *for those `f`*, so the
negation over exactly those `f` is what implies the paper's clause. Before committing, ask of any
`¬ ∃ B, ∀ f, …`: **is there a trivial `f` outside the paper's space that satisfies every
hypothesis?** If yes, the statement is true for the wrong reason.

## Why

`Ramp.lean`'s `no_bounded_inverse_infty` was stated on 2026-09-07 morning over *all*
`f : St → ℝ`. The unclipped height `V` has defect bounded by `max(1, γ, j̄)` and is unbounded,
so the negation held trivially and encoded nothing about `L^∞(λ)`; the clipped ramps, and the
lemma `centredRamp_bounded` proved for them, were never needed. A statement-fidelity review
caught it (the proof-level gates cannot: the theorem *was* true). Adding the one hypothesis and
passing `centredRamp_bounded` to the proof repaired it the same evening. See
[[0005-never-outrun-the-paper]].
