import GFNBounds.Graph.Morozov
import GFNBounds.Balance.MassIdentity

/-!
# Coercivity off balance, and the Łojasiewicz inequality it delivers

**`prop:no_distant_equilibrium`** **item *(3)***, its two static halves — statement
`proofs.tex:792–796` (inside the statement `proofs.tex:787–798`), proof `proofs.tex:809–813`
(inside `proofs.tex:800–814`).
**`cor:global_lojasiewicz`** — statement `proofs.tex:875–886`, proof `proofs.tex:887–898`;
**the static inequality only**, see SCOPE. (The bold-backtick form of each label is what
`scripts/trace_check.py` and the paper-side ledger machine-read; a label mentioned only in prose
is not a claim to certify it.)

> (`prop:no_distant_equilibrium`*(3)*) *Global convergence, quantitatively.* On a finite state
> space, for `g = (log x)²` and `w ≥ w_min > 0`: `|g'(x)(1−x)| ≥ δ²/2` whenever
> `|x−1| ≥ δ ∈ (0, ½]`, whence
> `‖∇^λ 𝓛_{g,ν}(μ)‖_{𝓜²(λ)} ≥ (w_min λ_min^{1/2}/‖u₀‖_{L²(λ)}) (δ²/2) λ(|r−1| ≥ δ)`,
> and the gradient flow from any `μ₀ ∼ λ` converges to the balanced flow of its sphere, entering
> the neighbourhood of Theorem `theo:local_convergence` in explicit time.

> (proof of *(3)*, first half) For `g = (log x)²`, `|g'(x)(1−x)| = 2|log x| |x−1|/x`. For
> `x ≤ 1−δ`: `|log x| ≥ δ` and `(1−x)/x ≥ δ`, so the product is `≥ 2δ²`. For `x ≥ 1+δ`:
> `log x ≥ δ/(1+δ)` and `(x−1)/x ≥ δ/(1+δ)`, so the product is `≥ 2δ²/(1+δ)² ≥ δ²/2` for
> `δ ≤ ½`. On the sphere, `u(x)²λ(x) ≤ ‖u₀‖²` gives `u ≤ ‖u₀‖λ_min^{−1/2}` pointwise, so
> `dν/dμ = w/u ≥ w_min λ_min^{1/2}/‖u₀‖`, and since `λ` is a probability measure,
> `‖D‖_{L²(λ)} ≥ |∫ D dλ| ≥ (w_min λ_min^{1/2}/‖u₀‖)(δ²/2) λ(|r−1| ≥ δ)`.

> (`cor:global_lojasiewicz`) In the setting of Proposition `prop:no_distant_equilibrium`*(3)* —
> `g = (log x)²`, finite state space, `ν = wλ` with `w_min ≤ w ≤ ‖w‖_{L^∞}` — set
> `M := max(1, √(𝓛(μ₀)/(w_min λ_min)))` and
> `κ := w_min λ_min^{1/2}/(‖u₀‖_{L²(λ)} ‖w‖_{L^∞} M)`. Then, along the gradient flow,
> `−d𝓛/dt ≥ κ² 𝓛²`, hence `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1} + κ² t)^{−1}`.

## The two boundaries

**The first is inherited.** `GFNBounds/Balance/MassIdentity.lean` closed item *(1)* and stated
the boundary this file also stands on: `D := Qφ − rφ` is a Lean **definition**, never derived,
and identifying it with `∇^λ 𝓛_{g,ν}(μ)` is `theo:first_variation_full`'s job — bucket D, not
formalized. So `‖∇^λ 𝓛‖` here is `Graph.nrmL2 lam (lossGradDensity …)`, the `L²(λ)` norm of that
expression, and not the norm of a derivative of anything. Nothing is redefined: `gradDensity`,
`ratio`, `Invariant`, `Balanced`, `lossGradDensity` and `integral_gradDensity_potential` come
from `MassIdentity`, `ipL2` and `nrmL2` from `GFNBounds/Graph/Morozov.lean`.

**Update, 2026-09-08 — this disclosure is now discharged elsewhere.**
`GFNBounds/Balance/FirstVariation.lean` proves `theo:first_variation_full` on a finite state
space: `hasDerivAt_loss_ipL2` shows that for every direction `d`, the directional derivative of
`𝓛_{g,ν}` at `μ` is `⟪lossGradDensity … ∣ d⟫_{L²(λ)}`, and `lossGradDensity_unique` shows no
other function represents those derivatives. So `D` **is** the gradient, and the readings below
are no longer conditional — with two residues, both still real: the state space is finite (the
general measured-space statement remains bucket `D`), and criticality is *directional* rather
than Fréchet. The wording of this bullet is kept as written because it records what **this
file** proves on its own.

**The second is new, and it is `cor:global_lojasiewicz`'s.** `−𝓛̇` is the time derivative of the
loss *along the gradient flow*, and the corollary's last step is the flow identity
`−𝓛' = ‖∇𝓛‖²`. **There is no gradient flow in this library** — no ODE on `𝓜²(λ)`, no existence
or uniqueness theorem, no LaSalle. What this file proves is therefore the inequality between the
two *static* quantities that the flow identity turns the display into,
`‖D‖²_{L²(λ)} ≥ κ² 𝓛²`, and the corollary as the paper states it is conditional on
`−𝓛̇ = ‖D‖²`. See SCOPE. The decay bound `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1} + κ²t)^{−1}` is **not** stated:
integrating a differential inequality needs the trajectory it is an inequality about.

## What is proved

| | |
|---|---|
| `sub_one_le_mul_log`, `Real.log_le_sub_one_of_pos` | the two logarithm inequalities everything below runs on |
| `log_le_neg_of_le_one_sub` | **bound 1 of four**: `x ≤ 1−δ ⇒ log x ≤ −δ`, i.e. `\|log x\| ≥ δ` |
| `le_one_sub_div_of_le_one_sub` | **bound 2 of four**: `x ≤ 1−δ ⇒ (1−x)/x ≥ δ` |
| `le_log_of_one_add_le` | **bound 3 of four**: `x ≥ 1+δ ⇒ log x ≥ δ/(1+δ)` |
| `le_sub_one_div_of_one_add_le` | **bound 4 of four**: `x ≥ 1+δ ⇒ (x−1)/x ≥ δ/(1+δ)`; stated before bound 3, which is proved through it |
| `logSqDeriv_mul_one_sub_le`, `le_abs_logSqDeriv_mul_one_sub` | item *(3)*'s pointwise inequality `\|g'(x)(1−x)\| ≥ δ²/2`, signed and in absolute value |
| `logSqDeriv_mul_one_sub_nonpos` | `g'(x)(1−x) ≤ 0` for every `x > 0` — strict unimodality unweighted, which is what makes the off-`S` terms of the integral harmless |
| `logSqDeriv_strictlyUnimodal` | `logSqDeriv` inhabits `MassIdentity`'s `StrictlyUnimodal` |
| `abs_mass_le_nrmL2` | `‖D‖_{L²(λ)} ≥ \|∫ D dλ\|`, Cauchy–Schwarz against `𝟏`, `λ` a probability |
| `le_density_ratio` | the sphere step: `dν/dμ = w/u ≥ w_min √λ_min/‖u₀‖` |
| `no_distant_equilibrium_three_far` | item *(3)*'s display, with `dν/dμ` bounded below by an abstract `c₀` and over any set of far ratios |
| `no_distant_equilibrium_three` | item *(3)*'s display verbatim, on `farSet` and with the paper's constant |
| `mul_abs_log_le` | `2M\|x−1\| ≥ x\|log x\|` on `(0, e^M]`, `M ≥ 1` — the corollary's three-case elementary step |
| `logSqDeriv_mul_one_sub_le_logSq_div` | `\|g'(x)(1−x)\| ≥ g(x)/M` on `(0, e^M]` |
| `logSq_le_of_loss`, `ratio_le_exp` | `g(r) ≤ 𝓛/(w_min λ_min) ≤ M²`, hence `r ≤ e^M` |
| `lossVal`, `lossVal_nonneg` | `𝓛_{g,ν}(μ) = ∑_x λ(x) w(x) g(r(x))`, a definition, and its nonnegativity |
| `lojasiewicz_termwise` | the arithmetic of `𝓛 ≤ ‖w‖_{L^∞} ∫ g(r) dλ`, one term at a time |
| `global_lojasiewicz_static` | `κ 𝓛 ≤ ‖D‖_{L²(λ)}` |
| `global_lojasiewicz_sq` | `κ² 𝓛² ≤ ‖D‖²_{L²(λ)}`, which is the paper's display once `−𝓛̇ = ‖D‖²` |

## SCOPE (disclosed)

* **There is no gradient flow here, so `cor:global_lojasiewicz` is certified in its static form
  only: what is proved is `‖D‖²_{L²(λ)} ≥ κ²𝓛²` between two quantities evaluated at one `μ`, and
  the paper's `−d𝓛/dt ≥ κ²𝓛²` follows from it only through the flow identity `−𝓛̇ = ‖D‖²`, which
  this library does not have and does not state.** Nothing below defines a trajectory `μ_t`,
  differentiates `𝓛` in time, or integrates the resulting differential inequality; the paper's
  second display `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1} + κ²t)^{−1}` is therefore absent. The paper's own `M` is
  built from `𝓛(μ₀)` because `𝓛` decreases along the flow; with no flow, monotonicity is
  unavailable, so `M` is built here from any `L₀` with `𝓛(μ) ≤ L₀` — which is what
  `𝓛(μ_t) ≤ 𝓛(μ₀)` would supply, and is weaker in hypothesis.
* **The identification of `D` with the gradient is not done here either**, exactly as in
  `MassIdentity`: `‖∇^λ 𝓛_{g,ν}(μ)‖` is read as `Graph.nrmL2 lam (lossGradDensity …)`. The
  norm `‖·‖_{𝓜²(λ)}` of the paper's display and the `‖·‖_{L²(λ)}` used here are identified by
  `μ = uλ ↦ u`, which is the identification `theo:first_variation_full` sets up and which is not
  formalized.
* **Only item *(3)*'s two static halves are added.** `prop:no_distant_equilibrium` stays
  `partial`: item *(1)* is `MassIdentity`'s, item *(2)* (scale invariance, `d/dt‖u_t‖ = 0`,
  monotone ascent of the mass, Cauchy–Schwarz on the sphere) is untouched, and item *(3)*'s
  **convergence half** — "the gradient flow from any `μ₀ ∼ λ` converges to the balanced flow of
  its sphere, entering the neighbourhood of Theorem `theo:local_convergence` in explicit time",
  whose proof runs on boundary blow-up of `𝓛`, LaSalle's invariance principle and
  `lem:sigma_mixing` — is **not** here and needs the same missing gradient-flow layer. What this
  file adds is the coercivity estimate that half consumes.
* **The sphere is a hypothesis, not a conclusion.** `‖u‖_{L²(λ)} = ‖u₀‖_{L²(λ)}` is assumed
  (`hsph`); that the flow preserves it is item *(2)*, which is not formalized. Every statement
  using `‖u₀‖` carries `hsph` explicitly.
* **`λ_min` and `‖w‖_{L^∞}` are parameters with their defining inequalities as hypotheses**
  (`∀ x, lamMin ≤ lam x`, `∀ x, wf x ≤ wsup`), not `min`/`max` over the vertex set. The bounds
  are therefore proved for *any* valid lower/upper bound, the paper's `min λ` and `‖w‖_∞`
  included, and no `MarkedGraph` is needed to name a minimum. `Graph.minOver`/`Graph.supAbs`
  instantiate them where a graph is at hand.
* **`λ(|r−1| ≥ δ)` is `∑_{x ∈ farSet} λ(x)`**, a `Finset` sum; `farSet` is `Finset.filter`, whose
  decidability comes from the classical `Real.decidableLE`, so the definition is `noncomputable`
  and carries no computational content. `no_distant_equilibrium_three_far` proves the bound for
  every `S` whose members are far, which is strictly more general.
* **Finite state space.** The paper's item *(3)* says "on a finite state space" in as many words,
  so this is the paper's own hypothesis and not a weakening; `∫ · dλ` is `∑ x, λ x * ·`.
* **`g` is `(log x)²` throughout, and only through `logSq` and `logSqDeriv`.** `g` is never
  differentiated: `logSqDeriv x := 2 log x / x` is *defined* to be the derivative the paper
  computes, and `logSq x := (log x)²` is *defined* to be the generator, the two being tied
  together nowhere in this file. That `logSqDeriv` is `deriv logSq` is elementary calculus, is
  not stated, and is not used; every inequality below is a relation between two named functions.
  `logSqDeriv_strictlyUnimodal` records that this is `MassIdentity`'s hypothesis, made concrete.
* **`ν = wλ` and `dν/dμ = w/u`.** `MassIdentity`'s third function argument is `dν/dμ`; the
  paper's `w` is `dν/dλ`. The two are related here by the *definition* `wnu := fun x => wf x/u x`,
  which is the Radon–Nikodym chain rule on a finite space with `u > 0`, and is not derived from
  any measure theory.
* **`𝓛_{g,ν}` is `lossVal`, a definition.** `lossVal lam wf gg r = ∑ x, λ(x)(w(x) g(r(x)))` is
  the paper's `∫ g(r) dν` for `ν = wλ` written as a finite sum. That this is the functional whose
  gradient `D` represents is again `theo:first_variation_full`'s, and is not established.

**Update, 2026-09-08 — discharged.** `GFNBounds/Balance/Flow.lean` closes the flow layer on a
finite state space: `hasDerivAt_loss_flow` proves the identity `−𝓛̇ = ‖D‖²_{L²(λ)}` (it is the
chain rule composed with `FirstVariation.hasDerivAt_loss_ipL2`, now that `D` is provably the
gradient), `lojasiewicz_integrated` integrates the differential inequality, and
`global_lojasiewicz_flow` states `cor:global_lojasiewicz`'s **second** display,
`𝓛(μ_t) ≤ (𝓛(μ₀)^{-1} + κ²t)^{-1}`, with `κ` the explicit formula below. It needs no existence
theorem — every claim is *for any curve satisfying the ODE*, which is how the paper's proof
reads. The sphere constraint `‖u_t‖ = ‖u₀‖`, a hypothesis here, is a **conclusion** there
(`nrmL2_const_of_flow`), so `‖u₀‖` in `κ` is literally `‖dμ₀/dλ‖`. The bullet below is kept as
written because it records what **this file** proves on its own.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| finite state space | ✓ `[Fintype V]`, the paper's own hypothesis in item *(3)* |
| `g = (log x)²` | ✓ `logSq`, with `logSqDeriv` its stated derivative; see SCOPE |
| `g` admissible, differentiable | ✗ not carried; `logSq` and `logSqDeriv` are two independent definitions |
| `(𝒮̂, λ, T)` ergodic | ⚠ **weakened to `λ`-invariance** (`Invariant K lam`), as in `MassIdentity` |
| `λ` a probability | ✓ carried here (`htot : ∑ x, lam x = 1`), unlike in `MassIdentity`: the step `‖D‖ ≥ \|∫ D dλ\|` is Cauchy–Schwarz against `𝟏` and needs `‖𝟏‖ = 1` |
| `λ_min := min_x λ(x) > 0` | ⚠ a parameter `lamMin` with `∀ x, lamMin ≤ lam x` and `0 < lamMin`; see SCOPE |
| `T` a Markov kernel | ⚠ only `K ≥ 0` (`hK`), and only to derive `r > 0` through `ratio_pos` |
| `μ ∼ λ`, `u = dμ/dλ` | ✓ `hu : ∀ x, 0 < u x` |
| `ν = wλ`, `w ≥ w_min > 0` | ✓ `hw : ∀ x, wmin ≤ wf x`, `hwmin : 0 < wmin` |
| `w ≤ ‖w‖_{L^∞}` (corollary only) | ⚠ a parameter `wsup` with `∀ x, wf x ≤ wsup`; see SCOPE |
| `dν/dμ > 0` | ✓ derived from `hw`, `hwmin`, `hu` — not hypothesised |
| the invariant sphere `‖u‖ = ‖u₀‖` | ⚠ **hypothesis** `hsph`, not conclusion; see SCOPE |
| `‖u₀‖ > 0` | ✓ `hu0`, needed to divide by it |
| `δ ∈ (0, ½]` | ✓ `hδ0 : 0 < δ`, `hδ1 : δ ≤ 1/2` |
| `M := max(1, √(𝓛(μ₀)/(w_min λ_min)))` | ⚠ `max 1 (√(L₀/(wmin·lamMin)))` for any `L₀ ≥ 𝓛(μ)`; see SCOPE |
| `𝓛` decreases along the flow | ✗ **not available** — replaced by the hypothesis `𝓛(μ) ≤ L₀` |
| `−𝓛̇ = ‖∇𝓛‖²` | ✗ **not available and not stated** — the corollary is conditional on it |
| `D = P†φ − rφ` | ⚠ **taken as a definition** in `MassIdentity`; inherited |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

/-! ### The generator `(log x)²`, and the two logarithm inequalities everything runs on -/

/-- **`g = (log x)²`**, the paper's practical generator (`proofs.tex:792`). -/
noncomputable def logSq (x : ℝ) : ℝ := Real.log x ^ 2

/-- **`g'(x) = 2 log x / x`** for `g = (log x)²` (`proofs.tex:809`).

A *definition*, not a derivative: nothing in this file differentiates `logSq`. See the module
SCOPE. -/
noncomputable def logSqDeriv (x : ℝ) : ℝ := 2 * Real.log x / x

theorem logSq_nonneg (x : ℝ) : 0 ≤ logSq x := sq_nonneg _

/-- `logSqDeriv` is `MassIdentity`'s `StrictlyUnimodal` hypothesis made concrete
(`proofs.tex:788`). -/
theorem logSqDeriv_strictlyUnimodal : StrictlyUnimodal logSqDeriv :=
  strictlyUnimodal_logSqDeriv

/-- **`x − 1 ≤ x log x`** for `x > 0`, i.e. `log x ≥ 1 − 1/x`.

Together with `Real.log_le_sub_one_of_pos` (`log x ≤ x − 1`) this is the whole analytic input of
the file: bounds 1 and 2 below use the second, bounds 3 and 4 and the corollary's `x ≥ 2` case use
the first. -/
theorem sub_one_le_mul_log {x : ℝ} (hx : 0 < x) : x - 1 ≤ x * Real.log x := by
  have h := Real.one_sub_inv_le_log_of_pos hx
  have hmul := mul_le_mul_of_nonneg_left h hx.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at hmul
  exact hmul

/-! ### The four elementary bounds of `proofs.tex:809`

Each is stated separately and proved separately, because the proposition's pointwise inequality is
exactly their product and the paper asserts them without proof. All four hold as written. -/

/-- **Bound 1 of 4** (`proofs.tex:809`): for `0 < x ≤ 1 − δ`, `log x ≤ −δ`, i.e. `|log x| ≥ δ`. -/
theorem log_le_neg_of_le_one_sub {x δ : ℝ} (hx : 0 < x) (h : x ≤ 1 - δ) :
    Real.log x ≤ -δ := by
  have h1 : (0:ℝ) < 1 - δ := lt_of_lt_of_le hx h
  calc Real.log x ≤ Real.log (1 - δ) := Real.log_le_log hx h
    _ ≤ (1 - δ) - 1 := Real.log_le_sub_one_of_pos h1
    _ = -δ := by ring

/-- **Bound 2 of 4** (`proofs.tex:809`): for `0 < x ≤ 1 − δ` and `δ > 0`, `(1 − x)/x ≥ δ`. -/
theorem le_one_sub_div_of_le_one_sub {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (h : x ≤ 1 - δ) :
    δ ≤ (1 - x) / x := by
  rw [le_div_iff₀ hx]
  nlinarith [mul_nonneg hδ.le (show (0:ℝ) ≤ 1 - x by linarith)]

/-- **Bound 4 of 4** (`proofs.tex:809`): for `1 + δ ≤ x` and `δ > 0`, `(x − 1)/x ≥ δ/(1 + δ)`.

Stated before bound 3 because bound 3 is proved through it: `log x ≥ (x−1)/x` by
`sub_one_le_mul_log`, and then this. -/
theorem le_sub_one_div_of_one_add_le {x δ : ℝ} (hδ : 0 < δ) (h : 1 + δ ≤ x) :
    δ / (1 + δ) ≤ (x - 1) / x := by
  have hx : 0 < x := by linarith
  rw [div_le_div_iff₀ (by linarith) hx]
  nlinarith

/-- **Bound 3 of 4** (`proofs.tex:809`): for `1 + δ ≤ x` and `δ > 0`, `log x ≥ δ/(1 + δ)`. -/
theorem le_log_of_one_add_le {x δ : ℝ} (hδ : 0 < δ) (h : 1 + δ ≤ x) :
    δ / (1 + δ) ≤ Real.log x := by
  have hx : 0 < x := by linarith
  have h2 : (x - 1) / x ≤ Real.log x := by
    rw [div_le_iff₀ hx]
    nlinarith [sub_one_le_mul_log hx]
  exact le_trans (le_sub_one_div_of_one_add_le hδ h) h2

/-! ### Item *(3)*'s pointwise inequality -/

/-- **`g'(x)(1 − x) ≤ −δ²/2` whenever `|x − 1| ≥ δ ∈ (0, ½]`** (`proofs.tex:792`, proof
`proofs.tex:809`), for `g = (log x)²`.

The signed form; `le_abs_logSqDeriv_mul_one_sub` is the paper's `|g'(x)(1−x)| ≥ δ²/2`. The two
branches are the paper's two, and each is the product of two of the four bounds above: `2δ²` on
the left, `2δ²/(1+δ)²` on the right, and `2δ²/(1+δ)² ≥ 8δ²/9 ≥ δ²/2` for `δ ≤ ½`. -/
theorem logSqDeriv_mul_one_sub_le {x δ : ℝ} (hx : 0 < x) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/2)
    (h : δ ≤ |x - 1|) : logSqDeriv x * (1 - x) ≤ -(δ ^ 2 / 2) := by
  have hx0 : x ≠ 0 := hx.ne'
  rcases le_abs.mp h with hR | hL
  · -- `x ≥ 1 + δ`: bounds 3 and 4.
    have hxge : 1 + δ ≤ x := by linarith
    have hA : δ / (1 + δ) ≤ Real.log x := le_log_of_one_add_le hδ0 hxge
    have hB : δ / (1 + δ) ≤ (x - 1) / x := le_sub_one_div_of_one_add_le hδ0 hxge
    have hq : (0:ℝ) ≤ δ / (1 + δ) := by positivity
    have hprod : δ / (1 + δ) * (δ / (1 + δ)) ≤ Real.log x * ((x - 1) / x) :=
      mul_le_mul hA hB hq (le_trans hq hA)
    have hval : δ / (1 + δ) * (δ / (1 + δ)) = δ * δ / ((1 + δ) * (1 + δ)) :=
      div_mul_div_comm δ (1 + δ) δ (1 + δ)
    have hsq : δ ^ 2 / 2 ≤ 2 * (δ / (1 + δ) * (δ / (1 + δ))) := by
      rw [hval, ← mul_div_assoc, le_div_iff₀ (by positivity : (0:ℝ) < (1 + δ) * (1 + δ))]
      nlinarith [mul_nonneg (mul_nonneg hδ0.le hδ0.le) (show (0:ℝ) ≤ 1/2 - δ by linarith),
        mul_nonneg (mul_nonneg (mul_nonneg hδ0.le hδ0.le) hδ0.le)
          (show (0:ℝ) ≤ 1/2 - δ by linarith), sq_nonneg δ]
    have heq : logSqDeriv x * (1 - x) = -(2 * (Real.log x * ((x - 1) / x))) := by
      simp only [logSqDeriv]; field_simp; ring
    rw [heq]
    linarith
  · -- `x ≤ 1 − δ`: bounds 1 and 2.
    have hxle : x ≤ 1 - δ := by linarith
    have hA : Real.log x ≤ -δ := log_le_neg_of_le_one_sub hx hxle
    have hB : δ ≤ (1 - x) / x := le_one_sub_div_of_le_one_sub hx hδ0 hxle
    have h1 : Real.log x * ((1 - x) / x) ≤ -δ * ((1 - x) / x) :=
      mul_le_mul_of_nonneg_right hA (le_trans hδ0.le hB)
    have h2 : -δ * ((1 - x) / x) ≤ -δ * δ := by nlinarith
    have heq : logSqDeriv x * (1 - x) = 2 * (Real.log x * ((1 - x) / x)) := by
      simp only [logSqDeriv]; field_simp
    rw [heq]
    nlinarith

/-- **`|g'(x)(1 − x)| ≥ δ²/2` whenever `|x − 1| ≥ δ ∈ (0, ½]`** (`proofs.tex:792`) — the
proposition's own wording, from the signed form. -/
theorem le_abs_logSqDeriv_mul_one_sub {x δ : ℝ} (hx : 0 < x) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/2)
    (h : δ ≤ |x - 1|) : δ ^ 2 / 2 ≤ |logSqDeriv x * (1 - x)| := by
  have hle := logSqDeriv_mul_one_sub_le hx hδ0 hδ1 h
  have : δ ^ 2 / 2 ≤ -(logSqDeriv x * (1 - x)) := by linarith
  exact le_trans this (neg_le_abs _)

/-- `g'(x)(1 − x) ≤ 0` for every `x > 0` — strict unimodality, unweighted
(`proofs.tex:805`, `proofs.tex:809`). -/
theorem logSqDeriv_mul_one_sub_nonpos {x : ℝ} (hx : 0 < x) : logSqDeriv x * (1 - x) ≤ 0 := by
  have hlog : Real.log x * (1 - x) ≤ 0 := by
    rcases le_or_gt x 1 with h | h
    · nlinarith [Real.log_nonpos hx.le h]
    · nlinarith [Real.log_nonneg h.le]
  have heq : logSqDeriv x * (1 - x) = 2 * (Real.log x * (1 - x)) / x := by
    simp only [logSqDeriv]; field_simp
  rw [heq, div_nonpos_iff]
  exact Or.inr ⟨by linarith, hx.le⟩

/-! ### `L²(λ)` bounds the mass, and the sphere bounds `dν/dμ` -/

variable {V : Type*} [Fintype V]

/-- **`‖a‖_{L²(λ)} ≥ |∫ a dλ|`** (`proofs.tex:809`: "since `λ` is a probability measure"),
Cauchy–Schwarz against `𝟏`. This is where `λ` being a probability is spent — `MassIdentity` does
not need it. -/
theorem abs_mass_le_nrmL2 {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1)
    (a : V → ℝ) : |∑ x, lam x * a x| ≤ Graph.nrmL2 lam a := by
  have hone : Graph.nrmL2 lam (fun _ => (1:ℝ)) = 1 := by
    have : Graph.ipL2 lam (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) = 1 := by
      simp only [Graph.ipL2, mul_one]
      exact htot
    simp only [Graph.nrmL2, this, Real.sqrt_one]
  have key : ∀ b : V → ℝ, ∑ x, lam x * b x ≤ Graph.nrmL2 lam b := by
    intro b
    have hcs := Graph.ipL2_le_mul_nrmL2 hnn b (fun _ => (1:ℝ))
    rw [hone, mul_one] at hcs
    simpa [Graph.ipL2] using hcs
  have hneg : Graph.nrmL2 lam (fun x => -(a x)) = Graph.nrmL2 lam a := by
    simp only [Graph.nrmL2, Graph.ipL2]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  refine abs_le.mpr ⟨?_, key a⟩
  have h := key (fun x => -(a x))
  rw [hneg] at h
  have hs : ∑ x, lam x * -(a x) = -∑ x, lam x * a x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hs] at h
  linarith

/-- **`u ≤ ‖u₀‖ λ_min^{−1/2}` on the sphere, hence `dν/dμ = w/u ≥ w_min √λ_min/‖u₀‖`**
(`proofs.tex:809`, restated at `proofs.tex:897`).

This is where `λ_min` enters the constant, and it enters only through
`λ_min u(x)² ≤ ∑_y λ(y)u(y)² = ‖u‖²`. -/
theorem le_density_ratio {lam u u0 wf : V → ℝ} {lamMin wmin : ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hu : ∀ x, 0 < u x) (hwmin : 0 ≤ wmin) (hw : ∀ x, wmin ≤ wf x)
    (hsph : Graph.nrmL2 lam u = Graph.nrmL2 lam u0) (hu0 : 0 < Graph.nrmL2 lam u0) (x : V) :
    wmin * Real.sqrt lamMin / Graph.nrmL2 lam u0 ≤ wf x / u x := by
  have hterm : lamMin * (u x * u x) ≤ Graph.ipL2 lam u u := by
    refine le_trans (mul_le_mul_of_nonneg_right (hlmin x) (mul_self_nonneg (u x))) ?_
    exact Finset.single_le_sum (f := fun z => lam z * (u z * u z))
      (fun z _ => mul_nonneg (hnn z) (mul_self_nonneg (u z))) (Finset.mem_univ x)
  have hbd : Real.sqrt lamMin * u x ≤ Graph.nrmL2 lam u0 := by
    rw [← hsph]
    calc Real.sqrt lamMin * u x
        = Real.sqrt (lamMin * (u x * u x)) := by
          rw [Real.sqrt_mul hlmin0.le, Real.sqrt_mul_self (hu x).le]
      _ ≤ Graph.nrmL2 lam u := Real.sqrt_le_sqrt hterm
  rw [div_le_div_iff₀ hu0 (hu x)]
  nlinarith [mul_le_mul_of_nonneg_left hbd hwmin,
    mul_le_mul_of_nonneg_right (hw x) hu0.le]

/-! ### Item *(3)*'s display -/

/-- The set `{x : |r(x) − 1| ≥ δ}` whose `λ`-mass the display carries (`proofs.tex:794`).
`noncomputable` because the predicate's decidability is the classical `Real.decidableLE`. -/
noncomputable def farSet (r : V → ℝ) (δ : ℝ) : Finset V :=
  Finset.univ.filter fun x => δ ≤ |r x - 1|

theorem mem_farSet {r : V → ℝ} {δ : ℝ} {x : V} : x ∈ farSet r δ ↔ δ ≤ |r x - 1| := by
  simp [farSet]

/-- **`prop:no_distant_equilibrium`*(3)*, the display, over any set of far ratios and with
`dν/dμ` bounded below by an abstract `c₀`** (statement `proofs.tex:792–796`, proof
`proofs.tex:809–811`).

Stated for every `S` whose members are far — the paper's `{|r−1| ≥ δ}` is the largest such, so
this is strictly more general — and with the constant left as `c₀ ≤ dν/dμ`, so that
`le_density_ratio` supplies the paper's `w_min √λ_min/‖u₀‖` in `no_distant_equilibrium_three`
without either step having to know the other.

`D` is `lossGradDensity`, a **definition**; see the module SCOPE. -/
theorem no_distant_equilibrium_three_far
    {K : V → V → ℝ} {lam u wnu : V → ℝ} {δ c₀ : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hc₀ : 0 < c₀) (hwnu : ∀ x, c₀ ≤ wnu x) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/2)
    (S : Finset V) (hS : ∀ x ∈ S, δ ≤ |ratio K lam u x - 1|) :
    c₀ * (δ ^ 2 / 2) * (∑ x ∈ S, lam x)
      ≤ Graph.nrmL2 lam (lossGradDensity K lam u wnu logSqDeriv) := by
  set r := ratio K lam u with hrdef
  have hr : ∀ y, 0 < r y := ratio_pos hinv hK hlam hu
  have hmass : ∑ x, lam x * lossGradDensity K lam u wnu logSqDeriv x
      = ∑ x, lam x * (logSqDeriv (r x) * (1 - r x) * wnu x) := by
    simp only [lossGradDensity, hrdef]
    exact integral_gradDensity_potential hinv logSqDeriv (ratio K lam u) wnu
  -- the integrand of `−∫ D dλ`, nonnegative everywhere
  set ψ : V → ℝ := fun x => -(lam x * (logSqDeriv (r x) * (1 - r x) * wnu x)) with hψdef
  have hψnn : ∀ x, 0 ≤ ψ x := by
    intro x
    have h1 : logSqDeriv (r x) * (1 - r x) ≤ 0 := logSqDeriv_mul_one_sub_nonpos (hr x)
    have h2 : 0 < wnu x := lt_of_lt_of_le hc₀ (hwnu x)
    have := mul_nonneg (mul_nonneg (hlam x).le (neg_nonneg.mpr h1)) h2.le
    simp only [hψdef]
    nlinarith [this]
  -- on `S` each term is at least `c₀ (δ²/2) λ(x)`
  have hlow : ∀ x ∈ S, c₀ * (δ ^ 2 / 2) * lam x ≤ ψ x := by
    intro x hx
    have h1 : logSqDeriv (r x) * (1 - r x) ≤ -(δ ^ 2 / 2) :=
      logSqDeriv_mul_one_sub_le (hr x) hδ0 hδ1 (hS x hx)
    have h2 : c₀ ≤ wnu x := hwnu x
    have hδsq : (0:ℝ) ≤ δ ^ 2 / 2 := by positivity
    have hstep : c₀ * (δ ^ 2 / 2) ≤ wnu x * -(logSqDeriv (r x) * (1 - r x)) :=
      mul_le_mul h2 (by linarith) hδsq (le_trans hc₀.le h2)
    have := mul_le_mul_of_nonneg_left hstep (hlam x).le
    simp only [hψdef]
    nlinarith [this]
  calc c₀ * (δ ^ 2 / 2) * (∑ x ∈ S, lam x)
      = ∑ x ∈ S, c₀ * (δ ^ 2 / 2) * lam x := by rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ S, ψ x := Finset.sum_le_sum hlow
    _ ≤ ∑ x, ψ x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hψnn i
    _ = -∑ x, lam x * lossGradDensity K lam u wnu logSqDeriv x := by
        rw [hmass, ← Finset.sum_neg_distrib]
    _ ≤ |∑ x, lam x * lossGradDensity K lam u wnu logSqDeriv x| := neg_le_abs _
    _ ≤ Graph.nrmL2 lam (lossGradDensity K lam u wnu logSqDeriv) :=
        abs_mass_le_nrmL2 (fun x => (hlam x).le) htot _

/-- **`prop:no_distant_equilibrium`*(3)*'s display verbatim** (statement `proofs.tex:792–796`,
proof `proofs.tex:809–811`):
`‖∇^λ 𝓛_{g,ν}(μ)‖ ≥ (w_min λ_min^{1/2}/‖u₀‖)(δ²/2) λ(|r−1| ≥ δ)` for `g = (log x)²`,
`ν = wλ` with `w ≥ w_min > 0`, on the sphere `‖u‖ = ‖u₀‖`.

`dν/dμ` is `w/u`, the chain rule on a finite space; `‖∇^λ 𝓛‖` is the `L²(λ)` norm of
`lossGradDensity`, a **definition**. See the module SCOPE. -/
theorem no_distant_equilibrium_three
    {K : V → V → ℝ} {lam u u0 wf : V → ℝ} {lamMin wmin δ : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hsph : Graph.nrmL2 lam u = Graph.nrmL2 lam u0) (hu0 : 0 < Graph.nrmL2 lam u0)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/2) :
    wmin * Real.sqrt lamMin / Graph.nrmL2 lam u0 * (δ ^ 2 / 2)
        * (∑ x ∈ farSet (ratio K lam u) δ, lam x)
      ≤ Graph.nrmL2 lam (lossGradDensity K lam u (fun x => wf x / u x) logSqDeriv) := by
  have hc₀ : 0 < wmin * Real.sqrt lamMin / Graph.nrmL2 lam u0 := by
    have : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
    positivity
  exact no_distant_equilibrium_three_far hinv hK hlam htot hu hc₀
    (fun x => le_density_ratio (fun y => (hlam y).le) hlmin hlmin0 hu hwmin.le hw hsph hu0 x)
    hδ0 hδ1 _ fun x hx => mem_farSet.mp hx

/-! ### `cor:global_lojasiewicz`: the elementary step -/

/-- **`x|log x| ≤ 2M|x − 1|` on `(0, e^M]` for `M ≥ 1`** (`proofs.tex:888`).

The corollary's three cases, in the paper's order: `x ≤ 1` is `x log(1/x) ≤ 1 − x`, i.e.
`sub_one_le_mul_log`; `1 ≤ x ≤ 2` is `x log x ≤ x(x−1) ≤ 2M(x−1)`; `x ≥ 2` is
`x log x ≤ Mx ≤ 2M(x−1)`, the last inequality being `x ≥ 2`. -/
theorem mul_abs_log_le {x M : ℝ} (hx : 0 < x) (hM : 1 ≤ M) (hxe : x ≤ Real.exp M) :
    x * |Real.log x| ≤ 2 * M * |x - 1| := by
  rcases le_or_gt x 1 with hle | hgt
  · rw [abs_of_nonpos (Real.log_nonpos hx.le hle), abs_of_nonpos (by linarith : x - 1 ≤ 0)]
    nlinarith [sub_one_le_mul_log hx,
      mul_nonneg (show (0:ℝ) ≤ 2 * M - 1 by linarith) (show (0:ℝ) ≤ 1 - x by linarith)]
  · rw [abs_of_nonneg (Real.log_nonneg hgt.le), abs_of_nonneg (by linarith : (0:ℝ) ≤ x - 1)]
    rcases le_or_gt x 2 with hle2 | hgt2
    · nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hx.le,
        mul_nonneg (show (0:ℝ) ≤ 2 - x by linarith) (show (0:ℝ) ≤ x - 1 by linarith),
        mul_nonneg (show (0:ℝ) ≤ 2 * M - 2 by linarith) (show (0:ℝ) ≤ x - 1 by linarith)]
    · have hlogM : Real.log x ≤ M := (Real.log_le_iff_le_exp hx).mpr hxe
      nlinarith [mul_le_mul_of_nonneg_left hlogM hx.le,
        mul_nonneg (show (0:ℝ) ≤ M by linarith) (show (0:ℝ) ≤ x - 2 by linarith)]

/-- **`g'(x)(1 − x) ≤ −g(x)/M` on `(0, e^M]` for `M ≥ 1`** (`proofs.tex:890`), for
`g = (log x)²` — the corollary's pointwise step, in signed form.

It is `mul_abs_log_le` multiplied by `|log x|/(Mx) ≥ 0`. -/
theorem logSqDeriv_mul_one_sub_le_logSq_div {x M : ℝ} (hx : 0 < x) (hM : 1 ≤ M)
    (hxe : x ≤ Real.exp M) : logSqDeriv x * (1 - x) ≤ -(logSq x / M) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hM0 : (0:ℝ) < M := by linarith
  have hsign : 0 ≤ Real.log x * (x - 1) := by
    rcases le_or_gt x 1 with h | h
    · nlinarith [Real.log_nonpos hx.le h]
    · nlinarith [Real.log_nonneg h.le]
  have hprod : Real.log x * (x - 1) = |Real.log x| * |x - 1| := by
    rw [← abs_mul, abs_of_nonneg hsign]
  have hkey := mul_abs_log_le hx hM hxe
  have hmul : x * |Real.log x| * |Real.log x| ≤ 2 * M * |x - 1| * |Real.log x| :=
    mul_le_mul_of_nonneg_right hkey (abs_nonneg _)
  have hfin : |Real.log x| * |Real.log x| / M ≤ 2 * (|Real.log x| * |x - 1|) / x := by
    rw [div_le_div_iff₀ hM0 hx]
    nlinarith [hmul]
  have heq1 : logSqDeriv x * (1 - x) = -(2 * (|Real.log x| * |x - 1|) / x) := by
    simp only [logSqDeriv]
    rw [← hprod]
    field_simp
    ring
  have heq2 : logSq x = |Real.log x| * |Real.log x| := by
    simp only [logSq]
    rw [abs_mul_abs_self]
    ring
  rw [heq1, heq2]
  linarith

/-! ### `cor:global_lojasiewicz`: the static inequality -/

/-- **`𝓛_{g,ν}(μ) = ∫ g(r) dν = ∑_x λ(x) w(x) g(r(x))`** for `ν = wλ` (`proofs.tex:876`).

A definition; that `lossGradDensity` is its gradient is `theo:first_variation_full`'s and is not
established here. See the module SCOPE. -/
noncomputable def lossVal (lam wf : V → ℝ) (gg : ℝ → ℝ) (r : V → ℝ) : ℝ :=
  ∑ x, lam x * (wf x * gg (r x))

theorem lossVal_nonneg {lam wf r : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (hw : ∀ x, 0 ≤ wf x) :
    0 ≤ lossVal lam wf logSq r :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hnn x) (mul_nonneg (hw x) (logSq_nonneg _))

/-- **`λ_min w_min g(r(x)) ≤ 𝓛`** (`proofs.tex:892`: "`g(r_t(x)) ≤ 𝓛(μ_t)/(w_min λ_min)`"),
one term of a sum of nonnegative terms. -/
theorem logSq_le_of_loss {lam wf r : V → ℝ} {lamMin wmin : ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (x : V) :
    lamMin * wmin * logSq (r x) ≤ lossVal lam wf logSq r := by
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun z => lam z * (wf z * logSq (r z)))
    (fun z _ => mul_nonneg (hnn z)
      (mul_nonneg (le_trans hwmin.le (hw z)) (logSq_nonneg _))) (Finset.mem_univ x))
  have h1 : lamMin ≤ lam x := hlmin x
  have h2 : wmin ≤ wf x := hw x
  have hg : 0 ≤ logSq (r x) := logSq_nonneg _
  have hstep : lamMin * wmin ≤ lam x * wf x :=
    mul_le_mul h1 h2 hwmin.le (le_trans hlmin0.le h1)
  calc lamMin * wmin * logSq (r x) ≤ lam x * wf x * logSq (r x) :=
        mul_le_mul_of_nonneg_right hstep hg
    _ = lam x * (wf x * logSq (r x)) := by ring

/-- **`r(x) ≤ e^M`** (`proofs.tex:892`), for `M := max(1, √(L₀/(w_min λ_min)))` and any
`L₀ ≥ 𝓛(μ)`.

The paper takes `L₀ = 𝓛(μ₀)` because `𝓛` decreases along the flow; with no flow available the
hypothesis is carried instead. See the module SCOPE. -/
theorem ratio_le_exp {lam wf r : V → ℝ} {lamMin wmin L0 : ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hr : ∀ x, 0 < r x)
    (hL0 : lossVal lam wf logSq r ≤ L0) (x : V) :
    r x ≤ Real.exp (max 1 (Real.sqrt (L0 / (wmin * lamMin)))) := by
  set M := max 1 (Real.sqrt (L0 / (wmin * lamMin))) with hMdef
  have hM1 : (1:ℝ) ≤ M := le_max_left _ _
  have hbase : lamMin * wmin * logSq (r x) ≤ L0 :=
    le_trans (logSq_le_of_loss hnn hlmin hlmin0 hwmin hw x) hL0
  have hL0nn : 0 ≤ L0 := by nlinarith [logSq_nonneg (r x), mul_pos hlmin0 hwmin]
  have hquot : L0 / (wmin * lamMin) ≤ M ^ 2 := by
    have hs : Real.sqrt (L0 / (wmin * lamMin)) ≤ M := le_max_right _ _
    have hsq : Real.sqrt (L0 / (wmin * lamMin)) ^ 2 = L0 / (wmin * lamMin) :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (L0 / (wmin * lamMin))]
  have hsq : Real.log (r x) ^ 2 ≤ M ^ 2 := by
    have hdiv : logSq (r x) ≤ L0 / (wmin * lamMin) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    simpa [logSq] using le_trans hdiv hquot
  have hlogle : Real.log (r x) ≤ M := by nlinarith [hsq, hM1]
  exact (Real.log_le_iff_le_exp (hr x)).mp hlogle

/-- The arithmetic step inside the corollary's integrand: `𝓛 ≤ ‖w‖_{L^∞} ∫ g(r) dλ`, read one
term at a time as `c₀/(M‖w‖_∞) · w(x) g ≤ (g/M) c₀` (`proofs.tex:895`).

Stated on bare reals because `set` in the caller makes `c₀` a local definition that `rw` sees
through. -/
theorem lojasiewicz_termwise {c₀ M wsup wx g : ℝ}
    (hc₀ : 0 < c₀) (hM : 0 < M) (hwsup : 0 < wsup) (hg : 0 ≤ g) (hle : wx ≤ wsup) :
    c₀ / (M * wsup) * (wx * g) ≤ g / M * c₀ := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hM]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hc₀.le hg) hM.le) (sub_nonneg.mpr hle)]

/-- **`cor:global_lojasiewicz`, the static inequality** (statement `proofs.tex:875–886`, proof
`proofs.tex:887–898`):
`‖∇𝓛‖_{L²(λ)} ≥ κ 𝓛` with `κ = w_min λ_min^{1/2}/(‖u₀‖ ‖w‖_{L^∞} M)` and
`M = max(1, √(L₀/(w_min λ_min)))`.

**This is not the corollary as stated.** The corollary reads `−d𝓛/dt ≥ κ²𝓛²` along the gradient
flow, and gets there from this inequality by `−𝓛' = ‖∇𝓛‖²`; there is no gradient flow in this
library, so that last step is not taken. See the module SCOPE, and `global_lojasiewicz_sq` for
the squared form the flow identity consumes. -/
theorem global_lojasiewicz_static
    {K : V → V → ℝ} {lam u u0 wf : V → ℝ} {lamMin wmin wsup L0 : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hsph : Graph.nrmL2 lam u = Graph.nrmL2 lam u0) (hu0 : 0 < Graph.nrmL2 lam u0)
    (hL0 : lossVal lam wf logSq (ratio K lam u) ≤ L0) :
    wmin * Real.sqrt lamMin
        / (Graph.nrmL2 lam u0 * wsup * max 1 (Real.sqrt (L0 / (wmin * lamMin))))
        * lossVal lam wf logSq (ratio K lam u)
      ≤ Graph.nrmL2 lam (lossGradDensity K lam u (fun x => wf x / u x) logSqDeriv) := by
  set r := ratio K lam u with hrdef
  set M := max 1 (Real.sqrt (L0 / (wmin * lamMin))) with hMdef
  set c₀ := wmin * Real.sqrt lamMin / Graph.nrmL2 lam u0 with hc₀def
  set wnu : V → ℝ := fun x => wf x / u x with hwnudef
  set L := lossVal lam wf logSq r with hLdef
  have hM1 : (1:ℝ) ≤ M := le_max_left _ _
  have hM0 : (0:ℝ) < M := by linarith
  have hsqrtpos : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
  have hc₀ : 0 < c₀ := by rw [hc₀def]; positivity
  have hr : ∀ y, 0 < r y := ratio_pos hinv hK hlam hu
  have hwnu : ∀ x, c₀ ≤ wnu x := fun x =>
    le_density_ratio (fun y => (hlam y).le) hlmin hlmin0 hu hwmin.le hw hsph hu0 x
  -- `V` is nonempty because `λ` is a probability, so `0 < wsup`
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at htot
    norm_num at htot
  obtain ⟨x0, -⟩ := hne
  have hwsup0 : 0 < wsup := lt_of_lt_of_le hwmin (le_trans (hw x0) (hwsup x0))
  -- the mass identity, and the pointwise Łojasiewicz step under it
  have hmass : ∑ x, lam x * lossGradDensity K lam u wnu logSqDeriv x
      = ∑ x, lam x * (logSqDeriv (r x) * (1 - r x) * wnu x) := by
    simp only [lossGradDensity, hrdef]
    exact integral_gradDensity_potential hinv logSqDeriv (ratio K lam u) wnu
  have hpt : ∀ x, logSqDeriv (r x) * (1 - r x) ≤ -(logSq (r x) / M) := fun x =>
    logSqDeriv_mul_one_sub_le_logSq_div (hr x) hM1
      (ratio_le_exp (fun y => (hlam y).le) hlmin hlmin0 hwmin hw hr hL0 x)
  -- termwise: `c₀/(M wsup) · λ(x) w(x) g(r(x)) ≤ −λ(x) g'(r)(1−r)(dν/dμ)`
  have hterm : ∀ x, c₀ / (M * wsup) * (lam x * (wf x * logSq (r x)))
      ≤ -(lam x * (logSqDeriv (r x) * (1 - r x) * wnu x)) := by
    intro x
    have hg : 0 ≤ logSq (r x) := logSq_nonneg _
    have h1 : c₀ / (M * wsup) * (wf x * logSq (r x)) ≤ logSq (r x) / M * c₀ :=
      lojasiewicz_termwise hc₀ hM0 hwsup0 hg (hwsup x)
    have h2 : logSq (r x) / M * c₀ ≤ -(logSqDeriv (r x) * (1 - r x)) * wnu x := by
      have hA : logSq (r x) / M ≤ -(logSqDeriv (r x) * (1 - r x)) := by linarith [hpt x]
      have hB : c₀ ≤ wnu x := hwnu x
      exact mul_le_mul hA hB hc₀.le (le_trans (by positivity) hA)
    have h3 : c₀ / (M * wsup) * (wf x * logSq (r x))
        ≤ -(logSqDeriv (r x) * (1 - r x)) * wnu x := le_trans h1 h2
    have := mul_le_mul_of_nonneg_left h3 (hlam x).le
    nlinarith [this]
  calc wmin * Real.sqrt lamMin / (Graph.nrmL2 lam u0 * wsup * M) * L
      = c₀ / (M * wsup) * L := by rw [hc₀def]; field_simp
    _ = ∑ x, c₀ / (M * wsup) * (lam x * (wf x * logSq (r x))) := by
        rw [hLdef, lossVal, Finset.mul_sum]
    _ ≤ ∑ x, -(lam x * (logSqDeriv (r x) * (1 - r x) * wnu x)) := Finset.sum_le_sum
        fun x _ => hterm x
    _ = -∑ x, lam x * lossGradDensity K lam u wnu logSqDeriv x := by
        rw [hmass, ← Finset.sum_neg_distrib]
    _ ≤ |∑ x, lam x * lossGradDensity K lam u wnu logSqDeriv x| := neg_le_abs _
    _ ≤ Graph.nrmL2 lam (lossGradDensity K lam u wnu logSqDeriv) :=
        abs_mass_le_nrmL2 (fun x => (hlam x).le) htot _

/-- **`cor:global_lojasiewicz`'s display, statically**: `κ²𝓛² ≤ ‖D‖²_{L²(λ)}`.

The paper writes `−d𝓛/dt ≥ κ²𝓛²`; its proof's last words are "conclude with `−𝓛' = ‖∇𝓛‖²`". That
identity holds along the gradient flow, which this library does not have — so what is certified
is the inequality between the two static quantities the identity turns the display into, and the
corollary as the paper states it is **conditional on `−𝓛̇ = ‖D‖²`**. See the module SCOPE. -/
theorem global_lojasiewicz_sq
    {K : V → V → ℝ} {lam u u0 wf : V → ℝ} {lamMin wmin wsup L0 : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hsph : Graph.nrmL2 lam u = Graph.nrmL2 lam u0) (hu0 : 0 < Graph.nrmL2 lam u0)
    (hL0 : lossVal lam wf logSq (ratio K lam u) ≤ L0) :
    (wmin * Real.sqrt lamMin
        / (Graph.nrmL2 lam u0 * wsup * max 1 (Real.sqrt (L0 / (wmin * lamMin))))) ^ 2
        * lossVal lam wf logSq (ratio K lam u) ^ 2
      ≤ Graph.nrmL2 lam (lossGradDensity K lam u (fun x => wf x / u x) logSqDeriv) ^ 2 := by
  have hbase := global_lojasiewicz_static hinv hK hlam htot hu hlmin hlmin0 hwmin hw hwsup
    hsph hu0 hL0
  have hLnn : 0 ≤ lossVal lam wf logSq (ratio K lam u) :=
    lossVal_nonneg (fun x => (hlam x).le) fun x => le_trans hwmin.le (hw x)
  have hκnn : 0 ≤ wmin * Real.sqrt lamMin
      / (Graph.nrmL2 lam u0 * wsup * max 1 (Real.sqrt (L0 / (wmin * lamMin)))) := by
    have hM1 : (1:ℝ) ≤ max 1 (Real.sqrt (L0 / (wmin * lamMin))) := le_max_left _ _
    have hne : (Finset.univ : Finset V).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h, Finset.sum_empty] at htot
      norm_num at htot
    obtain ⟨x0, -⟩ := hne
    have hwsup0 : 0 < wsup := lt_of_lt_of_le hwmin (le_trans (hw x0) (hwsup x0))
    have : 0 ≤ Real.sqrt lamMin := Real.sqrt_nonneg _
    positivity
  have hprod : 0 ≤ wmin * Real.sqrt lamMin
      / (Graph.nrmL2 lam u0 * wsup * max 1 (Real.sqrt (L0 / (wmin * lamMin))))
      * lossVal lam wf logSq (ratio K lam u) := mul_nonneg hκnn hLnn
  calc (wmin * Real.sqrt lamMin
        / (Graph.nrmL2 lam u0 * wsup * max 1 (Real.sqrt (L0 / (wmin * lamMin))))) ^ 2
        * lossVal lam wf logSq (ratio K lam u) ^ 2
      = (wmin * Real.sqrt lamMin
        / (Graph.nrmL2 lam u0 * wsup * max 1 (Real.sqrt (L0 / (wmin * lamMin))))
        * lossVal lam wf logSq (ratio K lam u)) ^ 2 := by ring
    _ ≤ Graph.nrmL2 lam (lossGradDensity K lam u (fun x => wf x / u x) logSqDeriv) ^ 2 := by
        exact pow_le_pow_left₀ hprod hbase 2

end GFNBounds.Balance
