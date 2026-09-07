# The knowledge base

What earlier sessions learned about proving *in this library*, written so the next session can act
on it without rediscovering it. [`INDEX.md`](INDEX.md) is the generated table of contents;
`entries/NNNN-slug.md` is one lesson per file.

This is **experience**, not documentation. Where the library records what is true
([`../docs/REPO-MAP.md`](../docs/REPO-MAP.md)) and how far it has got
([`../docs/COVERAGE.md`](../docs/COVERAGE.md)), the knowledge base records *what working here is
like* — which move to reach for, which one looks right and is not, which wall has already been hit.

## Reading it

At the **start** of a task, before opening a `.lean` file:

```
python3 scripts/kb.py search tsum summable      # ranked full-text
sed -n '1,200p' kb/INDEX.md                     # or just read the index; it is short
```

Two entries are mandatory reading whatever the task:

- [`0006`](entries/0006-three-obstructions.md) — the three obstructions. If the statement sits
  behind one, say so and stop.
- [`0005`](entries/0005-never-outrun-the-paper.md) — never state more than the paper proves.

Entries marked *provisional* held once and have not been confirmed since. Use them, but if one
turns out to be wrong, **say so and fix the entry** — a stale entry costs more than a missing one.

## Writing to it

Every session that touched Lean ends by asking: *did I learn something that would have saved me
time if it had been written down?* If yes, one entry. If no, none — the base is worth reading only
while its signal-to-noise is high.

```
python3 scripts/kb.py new --title "Stat.inv only accepts bounded test functions" \
    --kind pitfall --tags stat,tsum --source GFNBounds/Doubling/Setting.lean:355
```

Then fill in the three sections and run `python3 scripts/kb.py index`.

**What earns an entry**

- A goal shape that has a non-obvious right move here (`0001`, `0008`, `0015`).
- A move that looks right and is not, with what actually happens (`0003`).
- Where a lemma really lives, when finding it cost real time (`0009`).
- A house rule whose violation fails a gate or a review (`0004`, `0005`, `0011`).
- A wall you hit, named precisely enough that the next session does not re-hit it (`0006`).

**What does not**

- Generic Lean or Mathlib advice available in the Mathlib docs. "Lean has `linarith`" is noise.
- A restatement of what a file's own docstring already says. Link to it instead.
- The *result* of a proof. That belongs in the Lean file and in `paper-map.json`.
- Anything you have not actually checked in this repository. An unverified entry is worse than
  silence, because the next session will trust it.

**Before adding, search.** If an entry already covers the situation, extend or correct that one —
`kb.py lint` rejects duplicate ids, but nothing stops two entries drifting apart, and that is the
failure mode that kills a knowledge base. Link related entries with `[[0008-nat-predecessor-rfl]]`.

## Schema

```yaml
---
id: 0003                  # four digits, matches the filename prefix
title: ...                # one line, the lesson itself, not the topic
kind: pattern             # pattern | pitfall | api | convention | obstruction | workflow
tags: [stat, tsum]        # lowercase, non-empty
confidence: established   # established | provisional
sources: [GFNBounds/Doubling/Setting.lean:355]   # paths are checked to still exist
created: 2026-09-07
---
```

Body: `## When` (the situation — a goal shape or an error message, not the mathematics),
`## Do` (the move, copy-pasteable), `## Why` (what goes wrong otherwise). `## When` and `## Do`
are required; `kb.py lint` fails without them, and `make check` runs the lint.
