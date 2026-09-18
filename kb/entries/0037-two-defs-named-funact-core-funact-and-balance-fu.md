---
id: 0037
title: Two defs named funAct: Core.funAct and Balance.funAct are the same formula, and rw does not see it
kind: pitfall
tags: [defs, rewriting, duplicates]
confidence: provisional
sources: [GFNBounds/Doubling/Remarks.lean]
created: 2026-09-18
---

## When

You use a lemma about `funAct` from the `Balance` shelf (`L2Toolkit.funAct_const`,
`MassIdentity` lemmas) on a goal written with `Core.funAct` (`Core/Adjoint.lean:301`) — or the
reverse — and `rw` reports `did not find an occurrence of the pattern (Balance.funAct K)^[?n] …`
although the goal visibly contains `(Core.funAct K)^[n] …`.

## Do

The two definitions (`Core/Adjoint.lean:301`, `Balance/MassIdentity.lean:155`) are the same
formula `fun x => ∑ y, K x y * u y`, so they are definitionally equal. Restate the lemma at the
name the goal uses with a typed `have`, then rewrite with that:

```lean
have h1 : Core.funAct K (fun _ => (1 : ℝ)) = fun _ => 1 :=
  funext fun y => Balance.funAct_const hK.row_sum 1 y
rw [Function.iterate_fixed h1] at h
```

Search `docs/REPO-INDEX.md` for both names before proving a `funAct` fact: the one you need may
exist under the other namespace.

## Why

`rw` matches up to syntactic head symbols (instances reducible), not up to unfolding of a
non-reducible `def`, so `Balance.funAct K` and `Core.funAct K` never match each other. The
elaborator checking a type ascription does unfold them, which is why the typed `have` works.
