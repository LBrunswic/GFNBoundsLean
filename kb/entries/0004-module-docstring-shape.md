---
id: 0004
title: The module docstring is a five-part contract, and reviewers check it
kind: convention
tags: [docs, fidelity, review]
confidence: established
sources: [GFNBounds/Doubling/DecayNotation.lean:5, GFNBounds/Doubling/R0Bound.lean:4]
created: 2026-09-07
---
## When

Creating a new `.lean` file, or adding a paper statement to an existing one.

## Do

In order, in the `/-! ... -/` module docstring:

1. `# Title` — a sentence, not the label.
2. The label in bold, then its line span:

   ```
   **`lem:doubling_descent`** — `app_doubling.tex:965–1024`.
   ```

   `scripts/trace_check.py` scans the whole source for these labels and fails on one absent from
   `paper-map.json`.
3. A `>` block quote of the paper's own sentence(s). Quote, do not paraphrase: this is what an
   auditor diffs the Lean statement against.
4. A **Hypothesis checklist** table — `| paper hypothesis | here |` with `✓ carried`,
   `⚠ weakened`, `⚠ strengthened`. 21 of 29 files carry one. If a row says `⚠ strengthened`, that
   is a finding, not a note; see [[0005-never-outrun-the-paper]].
5. A `## SCOPE (disclosed)` section whenever the file proves less than its label, saying exactly
   what is missing and why. Then the standing closing line, which all 29 files carry:

   ```
   Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
   ```

## Why

The library's claim is not "these theorems compile", it is "these theorems are *the paper's*
theorems". Nothing in the toolchain can check that: `lake` type-checks the Lean, `trace_check`
checks the LaTeX block has not moved under it, and the gap between them is exactly what parts 3
and 4 close by hand. A file with a `#print axioms` line and no quoted statement is a certificate
of something nobody has read.
