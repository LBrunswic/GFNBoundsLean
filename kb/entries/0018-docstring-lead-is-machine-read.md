---
id: 0018
title: The bold lead of a declaration docstring is machine-read, not decoration
kind: convention
tags: [docs, blueprint, paper-map, review]
confidence: established
sources: [GFNBounds/Doubling/Product.lean:1, scripts/appendix.py:119]
created: 2026-09-08
---
## When

Writing or renaming a declaration that certifies part of a paper statement — any `theorem` or
`def` whose name goes into a `decls` list in `paper-map.json`.

## Do

Open its docstring with the label it carries, in bold, and say *which part* of that label it is:

```lean
/-- **`eq:doubling_product`, in the paper's own form**: at a level `ℓ ≥ ℓ₂` and a
starting state `m ≥ 2ℓ`, the expected weight of a descent is `1 + O(1/ℓ)`. -/
theorem prodW_two_sided_paper ...
```

The label may be the paper statement's own (`lem:doubling_product`) or an equation label
*defined inside* that statement (`eq:doubling_product`); either is found. What must not happen is
a certifying declaration whose docstring names no label at all, or names it only in the middle of
a long paragraph.

## Why

`scripts/appendix.py` uses the bold lead as its one signal for *this declaration is a result,
not a step*. Two things hang on it. It decides which of a proof's dependencies are worth naming
in a sketch — `main_truncation_sqrtK` reaches 393 declarations, of which 96 carry the lead and 6
are direct, and only those 6 belong in a paragraph. And it drives a build gate: if a proof
invokes a *theorem* carrying the lead and no sketch names it, the lint fails, on the grounds
that a result the argument leans on may not be silently dropped.

So a docstring that opens with the mathematics instead of a bold lead still compiles and still
passes every proof-level audit, while quietly removing its declaration from the appendix's
account of the development — and, worse, removing it from the gate that would have noticed.

Two consequences worth remembering: the convention is now load-bearing beyond review, so changing
a lead is a content change; and it costs nothing to satisfy, because the house style already
does it — 739 of the library's declaration docstrings were written this way before anything read
them. See [[0004-module-docstring-shape]] for the module-level contract and
[[0013-trace-map-upkeep]] for the map side of the same discipline.
