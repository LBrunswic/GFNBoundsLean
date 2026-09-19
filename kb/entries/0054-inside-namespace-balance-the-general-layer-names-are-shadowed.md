---
id: 0054
title: Inside namespace GFNBounds.Balance, funAct, ratio and edgeMeasure resolve to the finite defs
kind: pitfall
tags: [names, namespaces, general-layer, elaboration]
confidence: established
sources: [GFNBounds/Balance/GdDiffusionGeneral.lean, GFNBounds/Balance/MassIdentity.lean, GFNBounds/Balance/Lift.lean]
created: 2026-09-19
---

## When

You write a general-space file under `namespace GFNBounds.Balance.<X>` (so that the finite
constants `C4`, `Cg`, `Kexp`, `winC3`, `Gamma3W`, … resolve unqualified) and use the general
layer's `funAct`, `ratio`, `edgeMeasure`, `edgeLift`, `edgeLiftDual`, `bind_edgeLift`,
`edgeMeasure_invariant` after `open GFNBounds.Core.General GFNBounds.Balance.LiftGeneral`.

The symptom is not "ambiguous name" but a type error far from the cause:
`failed to synthesize Fintype S`, `argument reversal T lam has type Kernel S S but is expected to
have type S → S → ℝ`, or `Invalid field rnDeriv … of type ?m → ?m → ℝ` on `edgeMeasure pb μ.fst`.

## Do

Qualify every general-layer name that also exists on the finite `Balance` shelf:
`Core.General.funAct`, `FirstVariation.ratio` / `.loss` / `.psi` / `.gradDens` / `.perturb`,
`LiftGeneral.edgeMeasure`, `LiftGeneral.edgeLift`, `LiftGeneral.edgeMeasure_invariant`, … A
regex pass over one section (`(?<![\w.])name(?![\w'])` → `Prefix.name`) is quicker than chasing the
errors one by one. Names with no finite twin (`reversal`, `IsInvariant`, `winC3`, `clamp`) are
fine unqualified.

## Why

Name resolution tries the enclosing namespaces before the opened ones, and
`GFNBounds.Balance.funAct` (`MassIdentity.lean`), `GFNBounds.Balance.ratio`,
`GFNBounds.Balance.edgeMeasure` (`Lift.lean`) are all in an enclosing namespace of
`GFNBounds.Balance.<X>`. The finite defs take `V → V → ℝ` matrices and a `[Fintype V]`, so the
elaborator commits to them and fails on the arguments. See also `0037` (the two finite `funAct`s).
