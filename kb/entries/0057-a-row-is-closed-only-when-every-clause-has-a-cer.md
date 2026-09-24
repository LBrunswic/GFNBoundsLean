---
id: 0057
title: A row is closed only when every clause has a certificate: a twin's bucket or a curated link can stand in for a clause with no Lean
kind: pitfall
tags: [paper-map, fidelity, twin, bucket, audit]
confidence: provisional
sources: [GFNBounds/Balance/TrainingSpeedDB.lean, paper-map.json, scripts/paper.py]
created: 2026-09-24
---

## When

A row's certificate is *borrowed* from somewhere else, and that borrowing is how it looks closed.
Two forms:

- **A body row with an appendix twin.** It carries the twin's files, declarations and bucket.
- **A curated link.** It points at the one module that assembles a restatement, for example
  Appendix I's `theo:lean_main` pointing at `Doubling/Main.lean`.

Or: the closure headline in `README.md`/`CLAUDE.md`, the ledger's `stats` and this map's
`coverage` disagree.

## Do

1. **Read the paper block clause by clause.** Name the declaration that certifies each clause.
   This includes:
   - "so that" and "that is" consequences;
   - pointers to other theorems (`theo:training_speed`'s last sentence, "the DB instance inherits
     a local rate … (Theorems \ref{…} and \ref{…})");
   - claims a definition makes without a citation.

   A clause with no declaration keeps the row in **B**, whatever the twin's bucket. Record the gap
   in `scope_notes`, then close it with an assembly theorem. `Balance/TrainingSpeedDB.lean` took
   one file and about 25 minutes of prover time, once `local_convergence_full_DB_paper` and
   `mixing_coercivity_finite` existed.
2. **Keep the two views' buckets equal.** Since 2026-09-24,
   `python3 formalization_ledger.py check` (paper side) fails on a map/ledger bucket
   disagreement. Treat a failure as a finding, never as noise to sync away. `sync-map` pushes the
   ledger's bucket **onto** the map, which would have overwritten the map's correct B.
3. **A statement the headline counts must be digested here.** Put its file in `scripts/paper.py`
   `SOURCES`, then run `python3 scripts/trace_check.py --init <file>`, then curate the rows. A
   curated link on the paper side alone is not digested, so an edit to the block goes unseen.

## Why

**The 2026-09-19 "96 of 96" headline rested on two borrowings.**

- **The twin's bucket.** `formalization_ledger.py` `build()` copies the twin's bucket onto a body
  row whose `restatement` is `verified`. `theo:training_speed` read A there for five days, while
  this map kept it in B because its DB sentence had no Lean.
  - The crosscheck compared status and spans only, so no gate saw the disagreement.
- **Curated links.** Appendix I's two rows were counted through curated links and had no map row,
  so this side counted 94 targets.
  - Their curated links certified the headline theorem but not the definition's embedded claims:
    the Lᵖ contraction, the standing range and the Cramér root all live outside
    `Doubling/Setting.lean`.
  - Nor did they certify item (5)'s "so that B̂_K < +∞", which lives in `TruncationBhat.lean`.

A borrowed certificate proves the part it was written for. The clause next to it needs its own.
