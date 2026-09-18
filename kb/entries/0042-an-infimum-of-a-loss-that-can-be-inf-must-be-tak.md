---
id: 0042
title: An infimum of a loss that can be +inf must be taken in EReal, not over Lean's real garbage
kind: pitfall
tags: [fidelity, hypotheses, loss, ereal, pinsker]
confidence: established
sources: [GFNBounds/Core/ILBoundFull.lean]
created: 2026-09-18
---

## When

A paper loss takes values in `(−∞, +∞]` (a cross-entropy `−∫ k log g` with `g` allowed to vanish
on `supp k`, an `L^q` penalty of a function that need not be in `L^q`), the Lean definition is
real-valued (`Real.log 0 = 0`, `integral` of a non-integrable function `= 0`,
`(eLpNorm f q μ).toReal = 0` at `⊤`), and the statement to formalize is an **infimum over a family**
or a bound "for every flow".

## Do

Carry pointwise statements under an explicit finiteness predicate, and lift the loss to `EReal`
for anything quantified over the family:

```lean
structure LossFinite ν νT q k e : Prop where
  ac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0      -- κ ≪ κ̂
  ce : Integrable (fun x => k x * Real.log (max (e x) 0)) ν
  pen : MemLp (fun x => max (-e x) 0) q νT
open Classical in
noncomputable def ilLoss … : EReal :=
  if LossFinite ν νT q k e then ((wklfmLossE ν νT q b k e : ℝ) : EReal) else ⊤
```

Then `⨅ θ ∈ Θ, ilLoss … = 𝓗` is the paper's statement, the lower bound is unconditional
(`le_top` off the predicate), and TV bounds read `ilLoss ≠ ⊤ → …`. Justify the `⊤` branch by a
lemma where possible (`crossEntropy_posPart_integrable`: the positive part is always integrable,
so non-integrability means `−∞` for the integral, `+∞` for the loss). For the final `ε`-argument,
`EReal.rec` splits `⊥ / ⊤ / coe` in three lines (`ereal_le_of_forall_pos`).

Related: Pinsker is **not** in Mathlib v4.31.0, but `GFNBounds.Core.ILBoundFull.pinsker`
(`tvD ≤ (1/√2)√klD` on densities) now is in this library; reuse it rather than carrying Pinsker
as a hypothesis again.

## Why

With the real-valued loss, a member whose paper loss is `+∞` can have a Lean value *below* the
floor `𝓗` (drop `κ ≪ κ̂` and `log 0 = 0` erases the divergent term), so `sInf`/`⨅` over the real
values is not the paper's infimum and "`inf_Θ 𝓛 = 𝓗`" can be false in Lean while true in the
paper. `ILBound.isGLB_of_domination` sidestepped this by abstracting to a set of achievable values;
the `EReal` lift is what lets the family `Θ` itself be quantified over.
