---
id: 0013
title: Adding a certificate means editing `paper-map.json` in the same change
kind: workflow
tags: [paper-map, trace, audit]
confidence: established
sources: [scripts/trace_check.py, paper-map.json]
created: 2026-09-07
---
## When

You proved something that certifies part of an `app_doubling.tex` statement, or you renamed a
declaration that `paper-map.json` lists.

## Do

Edit the statement's entry: add the file to `lean_files`, the declaration's **fully qualified**
name to `decls`, update `status` (`open` / `partial` / `closed`), `bucket` (`A`–`D`, or `T` for a terminal
remark, whose `scope_notes` must carry the paper-side ledger's `terminal_reason`), and above
all `scope_notes` — for a `partial`, say *which items* are proved and which obstruction stops the
rest. Add the `#print axioms` line to `GFNBounds/Audit.lean` under a comment naming the label.
Then `python3 scripts/trace_check.py`.

If it reports `STALE: <label>`, the LaTeX block changed under you. **Re-read the paper block
first**, decide whether the Lean statement still matches it, and only then

```
python3 scripts/trace_check.py --reaffirm lem:doubling_percut
```

Digests are per statement, not per file, so an edit to one label does not stale the others.

`trace_check.py` **writes `paper-map.json` on every run**, and `sorry_audit.py` rewrites
`docs/SORRY-STATUS.md` and `docs/sorry.json`. So a sub-session told not to edit other files, or one
sharing the tree with a session editing the map, must not run them. It replicates invariant (c)
read-only instead: every label its file cites has a map row. (Learned 2026-09-24.)

Since 2026-09-24 the paper side's `formalization_ledger.py check` also fails when this map's
`bucket` disagrees with the ledger's, so a bucket you change here must be the ledger's too. See
kb 0057.

## Why

`trace_check` enforces four invariants: the label still exists; every listed declaration exists in
its listed file; **no Lean file cites a label absent from the map**; and every digest is current.
That third one means writing `lem:doubling_foo` in a docstring without mapping it fails the build
— which is deliberate: an unmapped citation is a claim nobody is tracking.
