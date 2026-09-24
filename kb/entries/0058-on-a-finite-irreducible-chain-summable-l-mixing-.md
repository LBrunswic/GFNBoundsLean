---
id: 0058
title: On a finite irreducible chain, summable L² mixing is aperiodicity: never tick 'no aperiodicity hypothesis' beside it
kind: pitfall
tags: [mixing, aperiodicity, hypotheses, fidelity, review]
confidence: provisional
sources: [GFNBounds/Balance/TrainingSpeedDB.lean, GFNBounds/Balance/RemarksA.lean]
created: 2026-09-24
---

## When

The situation:
- A statement carries summable mixing on a finite irreducible chain: `hsum`, `Core.Mixing`, or
  "B̂ < ∞", on a loop closure `π̂_←` or on its edge lift `K₂`.
- Its hypothesis checklist or `SCOPE` lists what it does *not* assume.

## Do

Read `hsum` as aperiodicity, and write "aperiodicity, carried as summable mixing".

On the loop closure, the equivalence is three lines from `RemarksA`:

```lean
rw [lifted_summable_iff hpc hpos hl]   -- K₂ → π̂_← (TrainingSpeedDB); omit for π̂_← itself
constructor
· rintro hs ⟨d, hper⟩
  exact (RemarksA.graphs_vs_L2_periodic hpc hpos hl hper).2.2.1 hs
· intro hap
  exact (RemarksA.graphs_vs_L2_aperiodic hpc hpos hl hap).1.summable
```

It is stated once as `TrainingSpeedDB.lifted_summable_iff_aperiodic`.

Name leveled (autoregressive) graphs as *one* class of periodic closures where it fails, not as
the whole of it.

## Why

The mistake:
- The first draft of `TrainingSpeedDB.lean` ticked "no aperiodicity hypothesis ✓ none carried"
  for the DB sentence of `theo:training_speed`. Its `hsum` is exactly aperiodicity of `π̂_←`.
- The phrase it mirrored belongs to the paper's *state-space* clause.
- This is kb 0027's pattern at one remove. The hypothesis is absent from the binders but present
  through an equivalent one, and no gate sees it. An independent auditor did.

What the same equivalence shows:
- The paper's DB sentence undersells. `prop:morozov_rate`(3) gives DB a local rate at
  `1 + B̂_σ` with no aperiodicity at all (`MorozovDB.local_convergence_full_DB_sigma`).
- That is a finding for `/writer`, not a Lean change.
