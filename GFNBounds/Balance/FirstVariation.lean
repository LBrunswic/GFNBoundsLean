import GFNBounds.Core.Adjoint
import GFNBounds.Balance.Freezing

/-!
# The first variation of the balance loss: `D = Qφ − rφ` is a derivative, not a definition

**`theo:first_variation_full`** — statement `proofs.tex:447–453`, proof `proofs.tex:455–483`.
(The bold-backtick form of the label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> Under the hypotheses of Lemma `lem:adjoint`, let `μ ∈ 𝓜⁺(𝒮, ν_B)` with `μ ∼ λ`,
> `dμ/dλ ∈ L²(λ)`, `μT ≪ μ`, and let `r := d(μT)/dμ` be essentially bounded away from `0` and
> `∞`. For any finite measure `ν` with `dν/dμ ∈ L^∞(μ)`, define the associated `g`-divergence
> balance loss `𝓛_{g,ν}(μ) := ∫_𝒮 g(r) dν`. Then, for any `g : ℝ_+^* → ℝ` continuously
> differentiable with locally Lipschitz derivative, and any finite `ν_G ∈ 𝓜⁺(𝒮, ν_B)` with
> `ν_G ∼ λ`, the derivative of `𝓛_{g,ν}` — taken along directions `δ ≪ μ` with
> `‖dδ/dμ‖_{L^∞(μ)} < 1` and `d(δT)/dμ ∈ L^∞(μ)` — is represented by
> `∇^{ν_G}_μ 𝓛_{g,ν} = (dν_G/dλ)·(T^λ − r)[g'(r) (dν/dμ) λ]`.

> (proof) Let `r(x,μ) := d(μT)/dμ(x)` and, for an admissible direction `δ`, write `u := dδ/dμ`
> and `v := d(δT)/dμ`. Then `r(x, μ+δ) = (r+v)/(1+u) = r + v − r u + Δ(x,δ)`,
> `Δ = u(ru−v)/(1+u)`, so for `‖u‖_{L^∞(μ)} ≤ ½`, `|Δ| ≤ 2|u|(r|u|+|v|)`: the remainder is
> second order in `(u,v)`, uniformly […]. Lemma `lem:adjoint`*(3)* applies to that pair and, by
> the symmetry of `⟨·∣·⟩_λ`, gives
> `⟨g'(r)(dν/dμ)λ ∣ δT⟩_λ = ⟨[g'(r)(dν/dμ)λ]T^λ ∣ δ⟩_λ`. Hence the first variation of `𝓛_{g,ν}`
> is `δ𝓛_{g,ν} = ∫ g'(r) δr dν = ∫ g'(r)[d(δT)/dμ − r dδ/dμ] dν = ⟨[g'(r)(dν/dμ)λ](T^λ−r) ∣ δ⟩_λ`.
> Write `ψ := g'(r)(dν/dμ)` and `Φ := [ψλ](T^λ − r)`, so that `δ𝓛_{g,ν} = ⟨Φ ∣ δ⟩_λ`, and
> `ϖ := dν_G/dλ` […]. Hence `G = (dν_G/dλ)Φ` represents the derivative of `𝓛_{g,ν}` in
> `⟨·∣·⟩_{ν_G}`.

## Why this file exists

Three files of the strict library — `GFNBounds/Balance/MassIdentity.lean`,
`GFNBounds/Balance/Lojasiewicz.lean`, `GFNBounds/Balance/Freezing.lean` — take
`D := Qφ − rφ` (`MassIdentity.gradDensity`) as a **Lean definition** and disclose, in the same
words, that identifying it with `∇^λ 𝓛_{g,ν}(μ)` is this theorem's job and is not done there, so
that "every critical point of `𝓛_{g,ν}` is balanced" is *conditional* on that identification.

This file performs the identification, on a finite state space: `MassIdentity.lossGradDensity`
**is** the derivative of `Freezing.loss`, in the sense that for every direction the map
`t ↦ 𝓛_{g,ν}(μ + tδ)` has derivative `⟨D ∣ δ⟩_λ` at `t = 0` (`hasDerivAt_loss_ipL2`), that no
other function of the states represents that derivative (`lossGradDensity_unique`), and that a
genuine critical point — every directional derivative zero — is therefore balanced
(`balanced_of_hasDerivAt_zero`). Nothing here redefines `gradDensity`, `ratio`, `Invariant`,
`lossGradDensity`, `Balanced` or `loss`; they are imported and used as they stand.

## What is proved

| | |
|---|---|
| `ratio_expansion` | `(r+v)/(1+u) = r + v − ru + Δ` with `Δ = u(ru−v)/(1+u)` — `proofs.tex:463–464`, verbatim |
| `remainder_abs_le`, `ratio_second_order` | `‖u‖ ≤ ½ ⇒ |Δ| ≤ 2|u|(r|u|+|v|)`: the remainder is second order in `(u,v)`, *uniformly* — `proofs.tex:466` |
| `pushMass_perturb`, `ratio_perturb` | the perturbed ratio is a quotient of two affine functions of `t` |
| `dirDens`, `dirPush` | the paper's `u := dδ/dμ` and `v := d(δT)/dμ` for `δ = t·(dλ)` |
| `ratio_perturb_paper` | `r(μ + tδ) = (r + tv)/(1 + tu)`, the paper's own display at `proofs.tex:463` |
| `hasDerivAt_ratio` | `δr = v − r·u`, the second line of the first-variation display |
| `hasDerivAt_loss` | `δ𝓛_{g,ν} = ∫ g'(r)[d(δT)/dμ − r dδ/dμ] dν` — `proofs.tex:469–470` |
| `gradDensity_eq_densAct_reversal` | `Qφ` **is** the density action `[φλ]T^λ` of the `λ`-reversal, so `gradDensity` is the paper's `(T^λ − r)[φλ]` and not merely a matrix expression |
| `firstVariation_adjoint` | the adjoint step, `proofs.tex:471–475`, on `Core.ipL2_densAct_funAct` |
| `hasDerivAt_loss_ipL2` | **the theorem**: `δ𝓛_{g,ν} = ⟨Φ ∣ δ⟩_λ` with `Φ = MassIdentity.lossGradDensity` |
| `hasDerivAt_loss_ipL2_precond` | the same with a preconditioner `ν_G = ϖλ`, `ϖ > 0`: the represented density is unchanged, only the inner product moves |
| `lossGradDensity_unique` | *representative* is unambiguous: any `Ψ` representing the derivative equals `lossGradDensity` at every state |
| `balanced_of_hasDerivAt_zero` | **the payoff**: a critical point in the derivative sense is balanced. `MassIdentity.balanced_of_critical` ceases to be conditional |
| `balanced_of_hasDerivAt_zero_graph` | the same on the loop closure of a finite path-connected marked graph |
| `twoState_hasDerivAt_loss` | the theorem **evaluated**: `9/16`, against a derivative computed by hand off the formula. Non-vacuity and the sign, in one line |
| `freezing_hasDerivAt_zero` | `prop:nonlinear_freezing`*(1)*'s frozen flows are critical *in the derivative sense*, for every training measure — `Freezing.lean`'s reading of *critical* is discharged too |

## SCOPE (disclosed)

* **Finite state space**, as everywhere in `GFNBounds.Balance`: `∫ · dλ` is `∑ x, λ x * ·`, `a.e.`
  is `∀ x`, `𝓜²(λ)` and `L^∞` carry no content, and a measure is carried by a density. This is
  the *whole* reason the theorem is reachable at all: on a `Fintype` the loss is a function of
  finitely many real variables and the first variation is ordinary multivariable calculus, not a
  calculus of variations on `𝓜⁺(𝒮)`. `paper-map.json` records the general statement as bucket
  `D`, and it stays there: nothing below builds a Radon–Nikodym calculus, and the general case
  still needs one.
* **A directional derivative, not a Fréchet derivative.** What is proved is
  `HasDerivAt (fun t => 𝓛(μ + tδ)) ⟨Φ ∣ δ⟩_λ 0` for every direction `δ`, which is literally the
  paper's `δ𝓛_{g,ν} = ⟨Φ ∣ δ⟩_λ` and is what its proof computes. The paper's remainder estimate
  is *uniform* in the direction (`proofs.tex:466`), so its argument does deliver a Fréchet
  derivative on the admissible class; that stronger reading is **not** stated here, and the
  uniform bound is transcribed instead as a standalone inequality (`ratio_second_order`), which
  is the only place it is used. Two consequences are honest to name: the identification
  `Φ = lossGradDensity` is not weakened by this choice, because `lossGradDensity_unique` pins `Φ`
  from the directional derivatives alone; and `balanced_of_hasDerivAt_zero` hypothesises *every*
  directional derivative, which is weaker than Fréchet criticality and therefore gives a
  **stronger** theorem.
* **The remainder estimate is transcribed, not consumed.** `hasDerivAt_ratio` is proved by the
  quotient rule (`HasDerivAt.fun_div`) rather than by the expansion, the two being the same fact
  about `(a + tb)/(m + tn)`. `ratio_expansion`, `remainder_abs_le` and `ratio_second_order` state
  the paper's own route and are proved, but no theorem below cites them. They are here because
  the uniformity they express is the part of `proofs.tex:466` that a quotient rule does *not*
  supply, and because a file certifying this label with that display missing would be certifying
  a different proof.
* **The admissibility constraint `‖dδ/dμ‖_{L^∞(μ)} < 1` is absent from the derivative
  statements, and this is not a strengthening.** It is what keeps `μ + δ` a positive measure, so
  that `r(μ+δ)` is defined; along a *line* `t ↦ μ + tδ` it is automatic for small `t`, and
  `HasDerivAt … 0` is a statement about small `t` only. It reappears in the two statements that
  need `μ + δ` itself rather than a germ at `t = 0`: in `ratio_perturb_paper` as
  `|t·(dδ/dμ)| < 1`, verbatim, and in `ratio_second_order` as `|a| ≤ 1/2`, which is the sharper
  form the paper's remainder bound uses.
* **`g` is not carried; only a derivative is.** The hypothesis is
  `hg : ∀ y, 0 < y → HasDerivAt g (gd y) y`, i.e. `g` is differentiable on `ℝ_+^*` with
  derivative `gd`. The paper asks for `g` continuously differentiable with locally Lipschitz
  derivative: continuity of `g'` and the Lipschitz bound are what make the paper's remainder
  second order after composition with `g`, and on a finite space the composition is a finite sum
  of one-variable chain rules, for which differentiability at the point is enough. Admissibility
  of `g` is not carried either; it is unused, exactly as in `MassIdentity`.
* **The preconditioner.** `hasDerivAt_loss_ipL2` fixes `ν_G = λ`, which `proofs.tex:22` says is
  "the choice made throughout this appendix" and is what all three consumer files use.
  `hasDerivAt_loss_ipL2_precond` covers a general `ν_G = ϖλ` with `ϖ > 0`, so the disclosure is
  thinner than the `ν_G = λ` restriction alone would be: what is missing is not the
  preconditioner but the general measured space. The content of the general case is that
  `dG/dν_G = dΦ/dλ` — the *density* does not move, only the inner product does — and that is
  what the statement says.
* **`μT ≪ μ` and `r` essentially bounded are not hypotheses here.** On a `Fintype` with `λ > 0`
  and `u > 0` the first is automatic and the second vacuous, and `r > 0` — which the paper puts
  in the hypotheses as "bounded away from `0`" — is `MassIdentity.ratio_pos`, *derived* from
  invariance and positivity. `hasDerivAt_ratio` and `hasDerivAt_loss` need no lower bound on `r`
  at all; `hasDerivAt_loss` needs `0 < r x` only to know that `g` is differentiable there, which
  is the paper's `g : ℝ_+^* → ℝ`.
* **`T` Markov is never used, and invariance of `λ` is used only in the adjoint step.**
  `hasDerivAt_ratio` and `hasDerivAt_loss` hold for an arbitrary matrix `K`. That is not a claim
  the paper makes, and it is recorded rather than promoted: it means the derivative formula is
  insensitive to the chain, and that everything specific to `T` enters through
  `lem:adjoint`*(3)*.
* **What is *not* here.** `cor:gradient_formulas` (the `g = (x−1)²` and `g = |x−1|` instances) and
  `cor:db_gradient` (the same theorem on `(𝒮², λ₂, K₂)`) are not stated; neither is the general
  measured-space theorem. The `sorry` list is empty and this file adds nothing to it.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the hypotheses of `lem:adjoint`: `𝒮` Polish | ⚠ **finite** (`[Fintype V]`). See SCOPE — this is the disclosure the whole file rests on |
| `T` a Markov kernel | ⚠ **weakened to `K ≥ 0`** (`hK`), and even that is used only in the adjoint step; row-stochasticity is used nowhere. Free in the finite model |
| `λ` non-zero, finite, `T`-invariant | ⚠ finiteness automatic; invariance carried (`Invariant K lam`) and used only through `Core.ipL2_densAct_funAct` and `Core.reversal`; non-zeroness subsumed by `λ > 0` |
| `μ ∈ 𝓜⁺(𝒮, ν_B)` with `μ ∼ λ` | ✓ `μ = uλ` with `hu : ∀ x, 0 < u x` and `hlam : ∀ x, 0 < lam x` — mutual absolute continuity on a finite space, read on the support |
| `dμ/dλ ∈ L²(λ)` | ⚠ **vacuous** on a `Fintype`: every function is square-summable. Free in the finite model |
| `μT ≪ μ` | ⚠ **automatic** once `u > 0`: `μT` is given by its density. Free in the finite model |
| `r = d(μT)/dμ` essentially bounded away from `0` and `∞` | ⚠ **not hypothesised**: `∞` is vacuous on a `Fintype`, and `0 < r` is *derived* (`MassIdentity.ratio_pos`). Carried as `hr : ∀ x, 0 < ratio K lam u x` only where `g` must be differentiated on `ℝ_+^*` |
| `ν` finite with `dν/dμ ∈ L^∞(μ)` | ⚠ both **vacuous** on a `Fintype`. `ν` is carried as `nu : V → ℝ`, its own mass function, and `dν/dμ = nu/(λu)`. Free in the finite model |
| `g : ℝ_+^* → ℝ` continuously differentiable | ⚠ **weakened**: only `∀ y, 0 < y → HasDerivAt g (gd y) y`. Continuity of `g'` is unused. See SCOPE |
| `g'` locally Lipschitz | ⚠ **not carried**: it is what makes the paper's remainder second order after composition, and the finite-dimensional chain rule replaces it. See SCOPE |
| `ν_G ∈ 𝓜⁺(𝒮, ν_B)` finite with `ν_G ∼ λ` | ✓ `ν_G = ϖλ` with `hpi : ∀ x, 0 < varpi x`, in `hasDerivAt_loss_ipL2_precond`; the main statement fixes `ν_G = λ`, the appendix's own default (`proofs.tex:22`) |
| directions `δ ≪ μ` with `‖dδ/dμ‖_{L^∞(μ)} < 1`, `d(δT)/dμ ∈ L^∞(μ)` | ⚠ `δ = t·(dλ)` for an arbitrary `d : V → ℝ`: `δ ≪ μ` and the two `L^∞` conditions are automatic on a `Fintype`, and the size constraint is what `HasDerivAt … 0` quantifies away. See SCOPE |
| the conclusion `∇^{ν_G}_μ 𝓛 = (dν_G/dλ)(T^λ − r)[g'(r)(dν/dμ)λ]` | ✓ `hasDerivAt_loss_ipL2`, `hasDerivAt_loss_ipL2_precond`, `lossGradDensity_unique`; that `(T^λ − r)[φλ]` is `gradDensity` is `gradDensity_eq_densAct_reversal` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### The expansion of `r(μ + δ)` and its second-order remainder

`proofs.tex:462–466`, transcribed. Three statements about real numbers: the algebraic identity,
the bound on its remainder, and the two together. `a` is the paper's `u = dδ/dμ` at one state.
Nothing below consumes them; see the module SCOPE for why they are here. -/

/-- **`r(μ+δ) = (r+v)/(1+u) = r + v − ru + Δ` with `Δ = u(ru−v)/(1+u)`** (`proofs.tex:463–464`),
at one state, where `a` is the paper's `u`. Pure algebra: the only hypothesis is that the
perturbed density does not vanish. -/
theorem ratio_expansion {r v a : ℝ} (ha : 1 + a ≠ 0) :
    (r + v) / (1 + a) = r + v - r * a + a * (r * a - v) / (1 + a) := by
  field_simp
  ring

/-- **`|Δ| ≤ 2|u|(r|u| + |v|)` for `‖u‖ ≤ ½`** (`proofs.tex:466`): the remainder is second order
in `(u,v)`, and the bound is *uniform* — it depends on the direction only through `|u|` and `|v|`
at the same state. -/
theorem remainder_abs_le {r v a : ℝ} (hr : 0 ≤ r) (ha : |a| ≤ 1 / 2) :
    |a * (r * a - v) / (1 + a)| ≤ 2 * |a| * (r * |a| + |v|) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha
  have hden : (1 : ℝ) / 2 ≤ |1 + a| := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + a)]
    linarith
  have hdenpos : (0 : ℝ) < |1 + a| := by linarith
  have htri : |r * a - v| ≤ r * |a| + |v| := by
    have h := abs_add_le (r * a) (-v)
    rw [abs_mul, abs_of_nonneg hr] at h
    simpa [sub_eq_add_neg] using h
  have hnum : |a * (r * a - v)| ≤ |a| * (r * |a| + |v|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left htri (abs_nonneg a)
  rw [abs_div, div_le_iff₀ hdenpos]
  have habs : (0 : ℝ) ≤ |a| := abs_nonneg a
  have hfac : (0 : ℝ) ≤ r * |a| + |v| := add_nonneg (mul_nonneg hr habs) (abs_nonneg v)
  nlinarith [mul_nonneg habs hfac]

/-- **The remainder of `proofs.tex:463` is second order**, the identity and the bound in one
statement: `r(μ+δ)` differs from its linearization `r + v − ru` by at most `2|u|(r|u| + |v|)`. -/
theorem ratio_second_order {r v a : ℝ} (hr : 0 ≤ r) (ha : |a| ≤ 1 / 2) :
    |(r + v) / (1 + a) - (r + v - r * a)| ≤ 2 * |a| * (r * |a| + |v|) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha
  have hne : 1 + a ≠ 0 := by intro h; linarith [h]
  rw [ratio_expansion (v := v) (r := r) hne]
  simpa using remainder_abs_le (r := r) (v := v) (a := a) hr ha

/-! ### The perturbed flow, and its ratio

A direction is a signed measure `δ = dλ` carried by its `λ`-density `d : V → ℝ`, exactly as
`𝓜²(λ)` is carried in `GFNBounds.Core.Adjoint`; the perturbed flow is `μ + tδ`, i.e. the density
`u + t·d`. -/

/-- `pushMass` is affine along a direction: `(μ + tδ)T = μT + t·(δT)`. -/
theorem pushMass_perturb (K : V → V → ℝ) (lam u d : V → ℝ) (t : ℝ) (y : V) :
    pushMass K lam (fun x => u x + t * d x) y
      = pushMass K lam u y + t * pushMass K lam d y := by
  simp only [pushMass, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The ratio of the perturbed flow is a quotient of two affine functions of `t`. This is the
form the derivative is read off from. -/
theorem ratio_perturb (K : V → V → ℝ) (lam u d : V → ℝ) (t : ℝ) (y : V) :
    ratio K lam (fun x => u x + t * d x) y
      = (pushMass K lam u y + t * pushMass K lam d y)
          / (lam y * u y + t * (lam y * d y)) := by
  simp only [ratio, pushMass_perturb]
  congr 1
  ring

/-- **The paper's `u := dδ/dμ`** (`proofs.tex:461`) for the direction `δ = dλ`: `dδ/dμ = d/u`,
since `μ = uλ`. -/
noncomputable def dirDens (u d : V → ℝ) : V → ℝ := fun x => d x / u x

/-- **The paper's `v := d(δT)/dμ`** (`proofs.tex:461`) for the direction `δ = dλ`. -/
noncomputable def dirPush (K : V → V → ℝ) (lam u d : V → ℝ) : V → ℝ :=
  fun x => pushMass K lam d x / (lam x * u x)

/-- **`r(x, μ + δ) = (r + v)/(1 + u)`** (`proofs.tex:463`), in the paper's own letters, along the
ray `δ = t·(dλ)`: the paper's `u` is `t·dirDens` and its `v` is `t·dirPush`.

The hypothesis is the paper's admissibility constraint `‖dδ/dμ‖_{L^∞(μ)} < 1`, read at one state:
it is what keeps `μ + δ` from vanishing there, hence what makes both sides genuine quotients. -/
theorem ratio_perturb_paper {lam u : V → ℝ} (K : V → V → ℝ) (d : V → ℝ)
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x) (t : ℝ) (y : V)
    (hadm : |t * dirDens u d y| < 1) :
    ratio K lam (fun x => u x + t * d x) y
      = (ratio K lam u y + t * dirPush K lam u d y) / (1 + t * dirDens u d y) := by
  have h1 : lam y ≠ 0 := (hlam y).ne'
  have h2 : u y ≠ 0 := (hu y).ne'
  have hlt := (abs_lt.mp hadm).1
  have hR : (1 : ℝ) + t * (d y / u y) ≠ 0 := by
    have : (0 : ℝ) < 1 + t * dirDens u d y := by linarith
    simpa [dirDens] using this.ne'
  have hsplit : u y + t * d y = u y * (1 + t * (d y / u y)) := by field_simp
  have hL : lam y * u y + t * (lam y * d y) ≠ 0 := by
    have hrw : lam y * u y + t * (lam y * d y) = lam y * (u y * (1 + t * (d y / u y))) := by
      rw [← hsplit]; ring
    rw [hrw]
    exact mul_ne_zero h1 (mul_ne_zero h2 hR)
  rw [ratio_perturb]
  simp only [ratio, dirPush, dirDens]
  rw [div_eq_div_iff hL hR]
  field_simp

/-! ### The derivative of the ratio, and of the loss

`proofs.tex:469–470`: `δ𝓛_{g,ν} = ∫ g'(r) δr dν = ∫ g'(r)[d(δT)/dμ − r dδ/dμ] dν`. Neither
statement uses any property of `K`. -/

/-- **`δr = v − r·u`** (`proofs.tex:463`, `:470`): the derivative at `t = 0` of the perturbed
ratio, by the quotient rule on `ratio_perturb`. -/
theorem hasDerivAt_ratio {K : V → V → ℝ} {lam u : V → ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x) (d : V → ℝ) (y : V) :
    HasDerivAt (fun t : ℝ => ratio K lam (fun x => u x + t * d x) y)
      (dirPush K lam u d y - ratio K lam u y * dirDens u d y) 0 := by
  have h1 : lam y ≠ 0 := (hlam y).ne'
  have h2 : u y ≠ 0 := (hu y).ne'
  have hM : lam y * u y ≠ 0 := mul_ne_zero h1 h2
  have hfun : (fun t : ℝ => ratio K lam (fun x => u x + t * d x) y)
      = fun t : ℝ => (pushMass K lam u y + t * pushMass K lam d y)
          / (lam y * u y + t * (lam y * d y)) :=
    funext fun t => ratio_perturb K lam u d t y
  rw [hfun]
  have hone : HasDerivAt (fun t : ℝ => t) (1 : ℝ) (0 : ℝ) := hasDerivAt_id' 0
  have hN : HasDerivAt (fun t : ℝ => pushMass K lam u y + t * pushMass K lam d y)
      (pushMass K lam d y) 0 := by
    have h : HasDerivAt (fun t : ℝ => pushMass K lam u y + t * pushMass K lam d y)
        (0 + 1 * pushMass K lam d y) 0 :=
      (hasDerivAt_const (0 : ℝ) (pushMass K lam u y)).add (hone.mul_const (pushMass K lam d y))
    rwa [zero_add, one_mul] at h
  have hD : HasDerivAt (fun t : ℝ => lam y * u y + t * (lam y * d y)) (lam y * d y) 0 := by
    have h : HasDerivAt (fun t : ℝ => lam y * u y + t * (lam y * d y))
        (0 + 1 * (lam y * d y)) 0 :=
      (hasDerivAt_const (0 : ℝ) (lam y * u y)).add (hone.mul_const (lam y * d y))
    rwa [zero_add, one_mul] at h
  have hD0 : (fun t : ℝ => lam y * u y + t * (lam y * d y)) 0 ≠ 0 := by simpa using hM
  have hq := hN.fun_div hD hD0
  simp only [zero_mul, add_zero] at hq
  have hval : dirPush K lam u d y - ratio K lam u y * dirDens u d y
      = (pushMass K lam d y * (lam y * u y) - pushMass K lam u y * (lam y * d y))
        / (lam y * u y) ^ 2 := by
    simp only [dirPush, dirDens, ratio]
    field_simp
  rw [hval]
  exact hq

/-- **`δ𝓛_{g,ν} = ∫ g'(r)[d(δT)/dμ − r dδ/dμ] dν`** (`proofs.tex:469–470`): the first variation of
the balance loss, before the adjoint step.

`loss` is `GFNBounds.Balance.Freezing`'s — `𝓛_{g,ν}(μ) = ∫ g(r) dν` with the training measure `ν`
held fixed while `μ` varies, which is the whole point of differentiating it. `nu x` is `ν({x})`.

Only three things are used: `λ > 0`, `u > 0`, and differentiability of `g` at the values `r`
takes. `K` is an arbitrary matrix. -/
theorem hasDerivAt_loss {K : V → V → ℝ} {lam nu u : V → ℝ} {g gd : ℝ → ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x) (hr : ∀ x, 0 < ratio K lam u x)
    (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g)
      (∑ x, nu x * (gd (ratio K lam u x) *
        (dirPush K lam u d x - ratio K lam u x * dirDens u d x))) 0 := by
  have hz : (fun w => u w + (0 : ℝ) * d w) = u := by funext w; ring
  simp only [loss]
  refine HasDerivAt.fun_sum fun z _ => HasDerivAt.const_mul (nu z) ?_
  have hpt : HasDerivAt (fun t : ℝ => ratio K lam (fun w => u w + t * d w) z)
      (dirPush K lam u d z - ratio K lam u z * dirDens u d z) 0 :=
    hasDerivAt_ratio hlam hu d z
  have hgz : HasDerivAt g (gd (ratio K lam u z))
      (ratio K lam (fun w => u w + (0 : ℝ) * d w) z) := by
    rw [hz]; exact hg _ (hr z)
  exact hgz.comp (0 : ℝ) hpt

/-! ### The adjoint step

`proofs.tex:471–475`: `⟨ψλ ∣ δT⟩_λ = ⟨[ψλ]T^λ ∣ δ⟩_λ`, which is `lem:adjoint`*(3)* — closed on a
finite space in `GFNBounds/Core/Adjoint.lean` and reused here rather than reproved. -/

/-- **`Qφ` is the density action `[φλ]T^λ` of the `λ`-reversal**, so that `MassIdentity`'s
`gradDensity K r φ` is the paper's `(T^λ − r)[φλ]` read on densities (`proofs.tex:475`, `:478`).

`MassIdentity` calls `Q` "the paper's `P†`" and takes the identification on faith; this is it.
`Core.funAct_eq_densAct_reversal` on the pair `(K, T^λ)` supplies it at every state carrying
`λ`-mass. -/
theorem gradDensity_eq_densAct_reversal {K : V → V → ℝ} {lam : V → ℝ} (hinv : Invariant K lam)
    (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) (r phi : V → ℝ) (x : V) :
    gradDensity K r phi x
      = Core.densAct lam (Core.reversal lam K) phi x - r x * phi x := by
  have hI : Core.IsInvariant lam K := ⟨fun z => (hlam z).le, hinv⟩
  have hpair := hI.isReversalPair_reversal hK
  simp only [gradDensity]
  rw [Core.funAct_eq_densAct_reversal hpair phi (hlam x).ne']
  rfl

/-- **The adjoint step** (`proofs.tex:471–475`): the first variation of `hasDerivAt_loss`, which
pairs `ψ` against `δT`, is `⟨D ∣ δ⟩_λ` with `D = MassIdentity.lossGradDensity` — the paper's
`Φ = [ψλ](T^λ − r)`, `ψ := g'(r) dν/dμ`.

Two identities: the second term is bookkeeping, and the first is `lem:adjoint`*(3)* in the form
`Core.ipL2_densAct_funAct`, which is where invariance of `λ` and `K ≥ 0` are spent. `dν/dμ` is
`nu/(λu)`, `ν` being carried by its own mass function. -/
theorem firstVariation_adjoint {K : V → V → ℝ} {lam nu u : V → ℝ} {gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (d : V → ℝ) :
    (∑ x, nu x * (gd (ratio K lam u x) *
        (dirPush K lam u d x - ratio K lam u x * dirDens u d x)))
      = Graph.ipL2 lam (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd) d := by
  set psi : V → ℝ := fun z => gd (ratio K lam u z) * (nu z / (lam z * u z)) with hpsi
  have hI : Core.IsInvariant lam K := ⟨fun z => (hlam z).le, hinv⟩
  -- `lem:adjoint`(3), on the pair `(δ, ψ)`.
  have hadj := Core.ipL2_densAct_funAct hI hK d psi
  -- `λ(x)·d(δT)/dλ(x)` is the mass `pushMass`.
  have hpm : ∀ x : V, lam x * (Core.densAct lam K d x * psi x) = psi x * pushMass K lam d x := by
    intro x
    have hx : lam x ≠ 0 := (hlam x).ne'
    have hsum : (∑ z, lam z * K z x * d z) = pushMass K lam d x := by
      simp only [pushMass]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [Core.densAct_apply, ← hsum]
    field_simp
  have hleft : Graph.ipL2 lam (Core.densAct lam K d) psi = ∑ x, psi x * pushMass K lam d x :=
    Finset.sum_congr rfl fun x _ => hpm x
  have hright : Graph.ipL2 lam d (Core.funAct K psi) = ∑ x, lam x * (funAct K psi x * d x) :=
    Finset.sum_congr rfl fun x _ => by simp only [funAct, Core.funAct]; ring
  rw [hleft, hright] at hadj
  -- Now split both sides into the two terms of `D = Qψ − rψ`.
  have hL : (∑ x, nu x * (gd (ratio K lam u x) *
        (dirPush K lam u d x - ratio K lam u x * dirDens u d x)))
      = (∑ x, psi x * pushMass K lam d x)
        - ∑ x, lam x * (ratio K lam u x * psi x * d x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : lam x ≠ 0 := (hlam x).ne'
    have hux : u x ≠ 0 := (hu x).ne'
    simp only [hpsi, dirPush, dirDens]
    field_simp
  have hR : Graph.ipL2 lam (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd) d
      = (∑ x, lam x * (funAct K psi x * d x))
        - ∑ x, lam x * (ratio K lam u x * psi x * d x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [lossGradDensity, gradDensity, hpsi]
    ring
  rw [hL, hR, hadj]

/-! ### The theorem

`δ𝓛_{g,ν} = ⟨Φ ∣ δ⟩_λ` with `Φ = MassIdentity.lossGradDensity`, and what follows from it. -/

/-- **`theo:first_variation_full` at `ν_G = λ`** (`proofs.tex:450`, `:475`), on a finite state
space: the derivative of `t ↦ 𝓛_{g,ν}(μ + tδ)` at `t = 0` is `⟨D ∣ δ⟩_λ`, where `D` is
`MassIdentity.lossGradDensity` — the paper's `(T^λ − r)[g'(r)(dν/dμ)λ]`, read on densities by
`gradDensity_eq_densAct_reversal`.

**This is the statement the three consumer files disclose as missing.** `MassIdentity`,
`Lojasiewicz` and `Freezing` all take `D = Qφ − rφ` as a definition and say so; here it is a
derivative.

`ν_G = λ` is the appendix's own standing choice (`proofs.tex:22`); see
`hasDerivAt_loss_ipL2_precond` for a general preconditioner and the module SCOPE for the rest. -/
theorem hasDerivAt_loss_ipL2 {K : V → V → ℝ} {lam nu u : V → ℝ} {g gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g)
      (Graph.ipL2 lam (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd) d) 0 := by
  rw [← firstVariation_adjoint hinv hK hlam hu d]
  exact hasDerivAt_loss hlam hu (ratio_pos hinv hK hlam hu) hg d

/-- **`theo:first_variation_full` with its preconditioner** (`proofs.tex:450`, `:478–482`): for
`ν_G = ϖλ` with `ϖ > 0`, the derivative is `⟨G ∣ δ⟩_{ν_G}` where `G := (dν_G/dλ)Φ`.

The content is that `dG/dν_G = dΦ/dλ`: the represented *density* does not depend on the
preconditioner — `MassIdentity.lossGradDensity` again, unchanged — and only the inner product and
the direction's density move, `dδ/dν_G = (1/ϖ)(dδ/dλ)`. -/
theorem hasDerivAt_loss_ipL2_precond {K : V → V → ℝ} {lam nu u varpi : V → ℝ} {g gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hpi : ∀ x, 0 < varpi x)
    (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g)
      (Graph.ipL2 (fun x => varpi x * lam x)
        (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd)
        (fun x => d x / varpi x)) 0 := by
  have hchange : Graph.ipL2 (fun x => varpi x * lam x)
      (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd) (fun x => d x / varpi x)
      = Graph.ipL2 lam (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd) d := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : varpi x ≠ 0 := (hpi x).ne'
    field_simp
  rw [hchange]
  exact hasDerivAt_loss_ipL2 hinv hK hlam hu hg d

/-- **The representative is unique** (`proofs.tex:441`, "the inner product is non-degenerate, so
`μ ↦ μT^λ` is the only map satisfying this identity"; the same argument, one level up): if a
function `Ψ` represents every directional derivative of `𝓛_{g,ν}` in `⟨·∣·⟩_λ`, it *is*
`MassIdentity.lossGradDensity`, at every state.

This is what makes "`gradDensity` is the gradient" a determination and not merely an exhibition,
and it is why the directional reading of the derivative (module SCOPE) costs nothing. -/
theorem lossGradDensity_unique {K : V → V → ℝ} {lam nu u Psi : V → ℝ} {g gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hPsi : ∀ d : V → ℝ, HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g)
      (Graph.ipL2 lam Psi d) 0) (x : V) :
    Psi x = lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd x := by
  set Phi : V → ℝ := lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd
  set d : V → ℝ := fun z => Psi z - Phi z with hd
  have hEq : Graph.ipL2 lam Psi d = Graph.ipL2 lam Phi d :=
    (hPsi d).unique (hasDerivAt_loss_ipL2 hinv hK hlam hu hg d)
  have hzero : ∑ z, lam z * ((Psi z - Phi z) * (Psi z - Phi z)) = 0 := by
    have hsplit : ∑ z, lam z * ((Psi z - Phi z) * (Psi z - Phi z))
        = Graph.ipL2 lam Psi d - Graph.ipL2 lam Phi d := by
      simp only [Graph.ipL2, hd, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hsplit, hEq, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun z (_ : z ∈ (univ : Finset V)) =>
      mul_nonneg (hlam z).le (mul_self_nonneg (Psi z - Phi z)))).mp hzero x (mem_univ x)
  rcases _root_.mul_eq_zero.mp hterm with h | h
  · exact absurd h (hlam x).ne'
  · have := mul_self_eq_zero.mp h
    linarith

/-- **Every critical point of `𝓛_{g,ν}` is balanced** (`proofs.tex:790`), with *critical* read as
what it means: every directional derivative vanishes.

This is `MassIdentity.balanced_of_critical` with its hypothesis discharged. There, criticality was
`D = 0` pointwise and the docstring said in as many words that "this is criticality of `𝓛_{g,ν}`
is `theo:first_variation_full`'s identification and is **not** established here". It is
established here: `lossGradDensity_unique` turns vanishing derivatives into `D ≡ 0`, and
`MassIdentity` does the rest. -/
theorem balanced_of_hasDerivAt_zero {K : V → V → ℝ} {lam nu u : V → ℝ} {g gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hnu : ∀ x, 0 < nu x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hgd : StrictlyUnimodal gd)
    (hcrit : ∀ d : V → ℝ,
      HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g) 0 0) :
    Balanced K lam u := by
  have hzero : ∀ d : V → ℝ,
      HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g)
        (Graph.ipL2 lam (fun _ => (0 : ℝ)) d) 0 := by
    intro d
    have : Graph.ipL2 lam (fun _ => (0 : ℝ)) d = 0 := by simp [Graph.ipL2]
    rw [this]
    exact hcrit d
  have hD : ∀ x, lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd x = 0 := fun x =>
    (lossGradDensity_unique hinv hK hlam hu hg hzero x).symm
  exact balanced_of_critical hinv hK hlam hu
    (fun x => div_pos (hnu x) (mul_pos (hlam x) (hu x))) hgd hD

/-! ### On the loop closure of a finite marked graph

The setting `MassIdentity` records as the one every downstream use is in. -/

section MarkedGraph

open GFNBounds.Graph

variable [DecidableEq V] {G : MarkedGraph V} {B : BackwardPolicy G}

/-- **Every critical point of `𝓛_{g,ν}` is balanced, on the backward chain of a finite
path-connected marked graph** — `MassIdentity.balanced_of_critical_graph` with *critical* read as
a vanishing derivative rather than as `D = 0`. -/
theorem balanced_of_hasDerivAt_zero_graph {lam nu u : V → ℝ} {g gd : ℝ → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (h : B.IsInvProb lam)
    (hu : ∀ x, 0 < u x) (hnu : ∀ x, 0 < nu x)
    (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y) (hgd : StrictlyUnimodal gd)
    (hcrit : ∀ d : V → ℝ,
      HasDerivAt (fun t : ℝ => loss B.phat lam nu (fun x => u x + t * d x) g) 0 0) :
    Balanced B.phat lam u :=
  balanced_of_hasDerivAt_zero (invariant_of_isInvProb h) B.phat_nonneg (h.pos hpc hpos) hu hnu
    hg hgd hcrit

end MarkedGraph

/-! ### `prop:nonlinear_freezing`*(1)*, with *critical* read as a vanishing derivative

`GFNBounds/Balance/Freezing.lean` discloses that its *critical*, *gradient descent is stationary*
and *the gradient flow is constant* are all read as `D = 0`. The first of the three is now a
theorem about the derivative. -/

/-- **A band-valued flow is a critical point of `𝓛_{g,ν}` for every training measure**
(`proofs.tex:762`, proof `:774`), in the derivative sense: every directional derivative of
`t ↦ 𝓛_{g,ν}(μ + tδ)` vanishes at `t = 0`.

`Freezing.freezing_critical` proves `D ≡ 0` there; `hasDerivAt_loss_ipL2` turns that into a
vanishing derivative. The generator is the paper's own `F.g`, which is `C^∞`. -/
theorem freezing_hasDerivAt_zero (F : FreezingBands) {K : V → V → ℝ} {lam nu u : V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hband : ∀ x, ratio K lam u x ∈ F.bands) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) F.g) 0 0 := by
  have hg : ∀ y : ℝ, 0 < y → HasDerivAt F.g (deriv F.g y) y := fun y _ =>
    (F.differentiable_g y).hasDerivAt
  have hD := hasDerivAt_loss_ipL2 (nu := nu) (gd := deriv F.g) hinv hK hlam hu hg d
  have hz : Graph.ipL2 lam
      (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) (deriv F.g)) d = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [freezing_critical hband (fun _ hzz => F.deriv_g_eq_zero_of_mem_bands' hzz) x,
      zero_mul, mul_zero]
  rwa [hz] at hD

/-! ### One instance, computed

A formula that has never been evaluated is a formula nobody has checked. The two-state chain of
`prop:nonlinear_freezing`*(2)* — already in the library, with its ratios `r = (3/4, 3/2)` proved —
is the cheapest place to evaluate this one, and it doubles as the certificate that the hypotheses
of `hasDerivAt_loss_ipL2` are jointly satisfiable. -/

/-- **The theorem, evaluated.** On `T(i→j) = 1/2`, `λ = (1/2,1/2)`, `μ* = (1,1/2)` — i.e.
`u = (2,1)` — with `ν` the counting measure and `g(x) = (x−1)²`, the derivative of
`t ↦ 𝓛_{g,ν}(μ* + tδ)` along `δ = (1,0)·λ` is `9/16`.

Independently: `r_t = ((3+t)/(2(2+t)), (3+t)/2)`, so `ṙ = (−1/8, 1/2)` and
`𝓛̇ = 2(3/4−1)(−1/8) + 2(3/2−1)(1/2) = 1/16 + 1/2 = 9/16`. The gradient side computes
`ψ = (−1/2, 2)`, `Qψ ≡ 3/4`, `D(0) = 3/4 − (3/4)(−1/2) = 9/8` and `⟨D ∣ δ⟩_λ = (1/2)(9/8) = 9/16`.
The two agree, which fixes the sign and the normalization of `lossGradDensity` against something
outside the derivation. -/
theorem twoState_hasDerivAt_loss :
    HasDerivAt (fun t : ℝ => loss twoStateK twoStateLam (fun _ => 1)
        (fun x => twoStateU x + t * (![1, 0] : Fin 2 → ℝ) x) fun z => (z - 1) ^ 2)
      (9 / 16) 0 := by
  have hg : ∀ y : ℝ, 0 < y → HasDerivAt (fun z : ℝ => (z - 1) ^ 2) (2 * (y - 1)) y := fun y _ => by
    simpa using ((hasDerivAt_id' y).sub_const 1).fun_pow 2
  have hval : Graph.ipL2 twoStateLam
      (lossGradDensity twoStateK twoStateLam twoStateU
        (fun z => 1 / (twoStateLam z * twoStateU z)) fun z => 2 * (z - 1))
      (![1, 0] : Fin 2 → ℝ) = 9 / 16 := by
    simp only [Graph.ipL2, lossGradDensity, gradDensity, funAct, Fin.sum_univ_two,
      twoState_ratio_zero, twoState_ratio_one]
    norm_num [twoStateK, twoStateLam, twoStateU]
  rw [← hval]
  exact hasDerivAt_loss_ipL2 (nu := fun _ => (1 : ℝ)) (gd := fun z => 2 * (z - 1))
    twoStateK_invariant (fun _ _ => by norm_num [twoStateK]) twoStateLam_pos twoStateU_pos hg
    (![1, 0] : Fin 2 → ℝ)

end GFNBounds.Balance
