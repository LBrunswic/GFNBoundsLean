---
id: 0005
title: Never state more than the paper proves — mirror the flag instead
kind: convention
tags: [fidelity, review, scope]
confidence: established
sources: [README.md]
created: 2026-09-07
---
## When

Always, and especially when a Lean statement would be *easier* to prove in a stronger or cleaner
form than the appendix states.

## Do

If the appendix says a thing is open, formal, or non-explicit, this library says so too:

- `theo:doubling_main`(1) row (d), `c = 1/ln 2` — null recurrence versus transience is **open in
  the paper**. Not stated here. Do not add it as if settled.
- `rem:doubling_second_order` is "a formal matching computation and is not proved here".
- `prop:doubling_unsolvable`'s witness pair is non-explicit by construction (open mapping), so the
  Lean statement is an `∃`.
- `prop:doubling_unsolvable`(1) gives a *dense* range, so only **exact** `L²` flow matching is
  refuted; whether *weak* universality fails is open.

If formalizing forces a change to a statement in the draft, that change goes through `/writer`.
Nothing in this repository edits `app_doubling.tex`.

## Why

From the README: *"on this material, careful proof-checking has repeatedly found real errors
after the claim was written down"* — a Choquet–Deny route was caught invoking a named theorem in a
form more general than the one that holds. A Lean file that quietly proves a *weaker* statement
under the paper's label launders that gap into a green build. The `SCOPE (disclosed)` section and
the `partial` status in `paper-map.json` exist precisely so that the gap is a visible artefact
rather than an absence.
