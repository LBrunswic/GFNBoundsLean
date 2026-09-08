---
id: 0019
title: '`ConstantInfo.value?` hides theorem proofs, and the failure is silent'
kind: pitfall
tags: [metaprogramming, environment, tooling]
confidence: established
sources: [scripts/lean_facts.lean:64, scripts/AxiomSweep.lean:15]
created: 2026-09-08
---
## When

Walking the environment to find out what a proof depends on — a dependency graph, a
provenance check, anything that reads proof terms rather than statements. The natural spelling
is `(env.find? n).value?` followed by `Expr.getUsedConstants`.

## Do

Project the value yourself:

```lean
def valueOf : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none
```

At mathlib `fabf563a` (`v4.31.0`), `ConstantInfo.value?` answers `none` for a `thmInfo` whose
proof is fully present. `.thmInfo v => v.value` returns it. Check the fix on a declaration whose
proof you can read: `main_unsolvable` is one line, `doubling_unsolvable L (growthCond_of_family
…)`, so its project dependencies must be exactly those two plus the vocabulary of its statement.

## Why

`scripts/lean_facts.lean` was written with `ci.value?` and ran clean over all 1109
declarations, reporting no error. Every `uses_value` came back `[]`, so the extracted dependency
graph was 1109 isolated nodes — which looks exactly like a project whose theorems happen not to
cite one another, and would have been believed. A probe on one known-good case found it in a
minute; nothing else would have.

Two consequences. **Anything derived from an empty dependency set fails open**, so a check built
on it passes vacuously — this is the same shape as the gate that passes because it never fires.
Test an extractor against a declaration whose answer you already know before trusting a run over
a thousand. And `Mathlib/Util/Export.lean:150` uses `ci.value!.getUsedConstants`, which works:
the partial projection is fine when you have already established the constant is not an axiom.

See [[0018-docstring-lead-is-machine-read]] for the other half of that pipeline.
