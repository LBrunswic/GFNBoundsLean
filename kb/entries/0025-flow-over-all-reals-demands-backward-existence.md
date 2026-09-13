---
id: 0025
title: A flow predicate quantified over all of `ℝ` demands backward existence a dissipative flow lacks
kind: pitfall
tags: [flow, hypotheses, quantifiers, vacuity, fidelity]
confidence: established
sources: [GFNBounds/Balance/Flow.lean:275, GFNBounds/Balance/TrainingSpeed.lean]
created: 2026-09-13
---
## When

Defining "`u` is a solution of the ODE" as a predicate that theorems hypothesise, for a flow the
paper runs forward from an initial condition.

## Do

Quantify the ODE over the half-line the paper uses — `∀ t, 0 ≤ t → HasDerivAt …` — and before
trusting any theorem that hypothesises the predicate, exhibit one non-trivial curve satisfying it,
or at least check on the smallest instance that one exists. A predicate nobody instantiates is a
hypothesis nobody has shown inhabited.

## Why

`IsGradientFlow` asked `HasDerivAt (u · x) (−∇𝓛(u t) x) t` at every real `t`. For
`g = (log x)²` the backward flow leaves the positive cone in finite time with infinite speed: on
the two-vertex marked graph, `b(t)² ≥ 8 log(a₀/b₀)(t − t*)` forces blow-up at `t*`, so **no** curve
satisfies the predicate from any non-balanced start (proved by an independent check, 2026-09-13;
300/300 random starts on the five-cycle behave the same numerically, the generic case unproved).
51 `hflow` binders in 9 graduated files hypothesised it (first quoted as "56 theorems"; re-measured by the audit), among them two rows closed in the paper map;
every one is, as far as is known, vacuous off balanced starts. No gate caught it: `sorry`, axiom
and kernel audits certify proofs, and a vacuous hypothesis makes proofs easier, not harder. It
surfaced only when an auditor asked whether the composed global-convergence theorem could ever be
applied. This is 0022's class one level up — there a hypothesis on the trajectory, here the
definition of the trajectory itself.

**Repaired 2026-09-13**, at the author's approval: `IsGradientFlow` asks `∀ t, 0 ≤ t → …`, keeping
the two-sided derivative at `0` (a forward solution extends linearly to `t < 0`). The downstream
repair changed 17 auxiliary signatures — a `0 ≤ t` hypothesis, or `Continuous` weakened to
`ContinuousAt` on `[0,∞)` — and no paper-level statement; arguments that needed a function
continuous on all of `ℝ` now run on `s ↦ f(max s 0)`, which agrees with `f` on `[0,∞)`.
