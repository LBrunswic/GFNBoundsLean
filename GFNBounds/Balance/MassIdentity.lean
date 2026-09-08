import GFNBounds.Graph.Setting

/-!
# The mass identity: a strictly unimodal generator admits no distant equilibrium

**`prop:no_distant_equilibrium`** **item *(1)*** — statement `proofs.tex:789–790` (inside the
statement `proofs.tex:787–798`), proof `proofs.tex:801–805` (inside `proofs.tex:800–814`).
**`theo:global_dichotomy_full`** **item *(1)***, its mass-identity half — statement
`proofs.tex:820–826` (its standing hypotheses at `:821`, item *(1)* at `:823`), proof
`proofs.tex:828–830`, which reads "item *1*
is Proposition `prop:no_distant_equilibrium`, items *(1)* and *(3)*". (The bold-backtick form of
each label is what `scripts/trace_check.py` and the paper-side ledger machine-read; a label
mentioned only in prose is not a claim to certify it.)

> (`prop:no_distant_equilibrium`) Let `g` be admissible and differentiable with
> `sign g'(x) = sign(x − 1)` for `x ≠ 1` (*strictly unimodal*; e.g. `(log x)²` and `(x − 1)²`),
> let `(𝒮̂, λ, T)` be ergodic, and write `u := dμ/dλ`.
> *(1)* **Mass identity.** For any `ν` with `dν/dμ > 0` `μ`-a.e., the total mass of
> `∇^λ 𝓛_{g,ν}(μ)` is `∫ g'(r)(1 − r) (dν/dμ) dλ ≤ 0`, with equality if and only if `μ` is
> balanced. Every critical point of `𝓛_{g,ν}` is therefore balanced.

> (proof of *(1)*) The gradient density is `D = P†φ − rφ` with `φ := g'(r) dν/dμ`. Since
> `P𝟏 = 𝟏` (`λ` is `T`-invariant), `∫ P†φ dλ = ⟨φ, P𝟏⟩ = ∫ φ dλ`, so
> `∫ D dλ = ∫ φ(1 − r) dλ = ∫ g'(r)(1 − r) (dν/dμ) dλ`. Strict unimodality makes
> `g'(r)(1 − r) < 0` wherever `r ≠ 1`, so the integrand is nonpositive and the integral vanishes
> if and only if `r = 1` holds `(dν/dμ)λ`-a.e., i.e. `μ`-a.e., i.e. `μT = μ`. At a critical point
> `D = 0`, so the mass vanishes and `μ` is balanced.

> (`theo:global_dichotomy_full`) *(1)* If `g` is *strictly unimodal* […] then the total mass of
> `∇^λ 𝓛_{g,ν}` equals `∫ g'(r)(1 − r) (dν/dμ) dλ ≤ 0`, with equality only at balance: *every
> critical point of `𝓛_{g,ν}` is balanced*, for every training measure with positive density, on
> every graph, cycles included.

## The one modelling decision, and it is a boundary

The proof's first sentence, "*the gradient density is `D = P†φ − rφ`*", is the **output of
`theo:first_variation_full`** (`proofs.tex:447–483`), which computes the first variation of
`𝓛_{g,ν}` on `𝓜²(λ)` and represents it in `⟨·|·⟩_λ`. That computation needs a calculus of
variations on measures — Radon–Nikodym derivatives along a perturbation, a second-order remainder
estimate, and the adjoint of `lem:adjoint`*(3)* — none of which Mathlib v4.31.0 supplies and none
of which this library has built.

So `D := Qφ − rφ` is **taken as a definition here** (`gradDensity`), with `Q` the function action
`(Qφ)(x) = ∑_y K(x,y) φ(y)` of the chain — the paper's `P†`, which on `L²(λ)` is the adjoint of
the density action `P`. What is then proved is a theorem *about that expression*, and its only
input is `λ`-invariance. See SCOPE.

## What is proved

| | |
|---|---|
| `integral_funAct` | `∫ Qφ dλ = ∫ φ dλ` — the paper's `⟨φ, P𝟏⟩ = ∫ φ dλ`, from `λ`-invariance alone |
| `integral_gradDensity` | `∫ D dλ = ∫ φ(1 − r) dλ` |
| `integral_gradDensity_potential` | with `φ = g'(r)·(dν/dμ)`: `∫ D dλ = ∫ g'(r)(1 − r)(dν/dμ) dλ` |
| `term_neg`, `term_nonpos`, `term_eq_zero_iff` | strict unimodality pointwise: `g'(r)(1 − r) ≤ 0`, `< 0` off `r = 1` |
| `ratio_pos` | `r > 0` is *derived* from invariance and positivity, not hypothesised |
| `ratio_eq_one_iff_balanced` | `r ≡ 1 ↔ μT = μ` |
| `no_distant_equilibrium_one` | the three conjuncts of item *(1)*: the identity, `≤ 0`, and equality iff balanced |
| `balanced_of_critical` | "every critical point of `𝓛_{g,ν}` is therefore balanced", read as `D = 0 ⇒ μT = μ` |
| `global_dichotomy_full_one` | the same three conjuncts under the dichotomy's label, proved by the previous one |
| `strictlyUnimodal_sqDeriv`, `strictlyUnimodal_logSqDeriv` | the hypothesis is inhabited: `(x−1)²` and `(log x)²` |
| `no_distant_equilibrium_one_graph`, `balanced_of_critical_graph` | the same, on the loop closure of a finite marked graph, over `GFNBounds.Graph`'s `phat` and `IsInvProb` |

## SCOPE (disclosed)

* **The identification of `D` with the gradient of `𝓛_{g,ν}` is `theo:first_variation_full`'s job
  and is not done here: what is certified below is the mass of *this expression*, and the words
  "every critical point of `𝓛_{g,ν}` is balanced" are conditional on that identification.**
  Nothing in this file defines `𝓛_{g,ν}`, differentiates anything, or knows that `gradDensity` is
  a gradient; `critical` is read as `D = 0` and not as "the first variation vanishes in every
  admissible direction". `theo:first_variation_full` is bucket D in `paper-map.json` and is not
  formalized; until it is, `balanced_of_critical` is a statement about the vanishing of an
  expression that the paper — not this file — identifies with `∇^λ 𝓛_{g,ν}(μ)`.
* **Items *(2)* and *(3)* of `prop:no_distant_equilibrium` are not here**, and neither is the
  second half of `theo:global_dichotomy_full`*(1)* (convergence of the gradient flow from every
  initialization) nor its item *(2)* (`prop:nonlinear_freezing`). Item *(2)* — scale invariance,
  `d/dt‖u_t‖ = 0`, monotone ascent of the mass, Cauchy–Schwarz on the sphere — and item *(3)* —
  the coercivity bound, LaSalle's invariance principle, the entry time into the local
  neighbourhood — are statements about the *trajectory* of an ODE on `𝓜²(λ)`. They need a
  gradient-flow layer (existence, uniqueness, `ω`-limit sets, LaSalle) that this library does not
  have, and no part of them is attempted. The map records both labels as **partial**.
* **Finite state space.** The paper states the proposition for an ergodic `(𝒮̂, λ, T)`; this file
  proves it on a `Fintype`, with `∫ · dλ` read as `∑ x, λ x * ·` and `a.e.` as `∀ x`. See the
  checklist for what that costs. Every downstream use in the paper —
  `theo:global_dichotomy_full`, `prop:morozov_rate`, `cor:global_lojasiewicz` — is on a finite
  graph, and `rem:freezing`*(iv)* says in as many words that on finite state spaces the
  proposition settles the global question, so nothing the paper needs is lost.
* **Ergodicity is not assumed, and is not used.** The paper hypothesizes `(𝒮̂, λ, T)` ergodic;
  item *(1)*'s proof uses only that `λ` is `T`-invariant, which is what `Invariant` carries.
  Assuming less is safe here — the statement proved is weaker in hypothesis, identical in
  conclusion — but it is recorded rather than passed over, because it means the file does *not*
  certify that the balanced flow is unique, which is where ergodicity is spent elsewhere.
* **Admissibility of `g` is not carried**, `g` itself is not carried, and `g'` appears only as an
  opaque `gd : ℝ → ℝ`. Item *(1)* uses no property of `g` beyond the sign condition on its
  derivative: not `g(1) = 0`, not `g > 0` elsewhere, not `g''(1) = 2`, not the quadratic growth
  bound, and not differentiability itself, `g'` entering only through its values at the ratios.
  `strictlyUnimodal_sqDeriv` and `strictlyUnimodal_logSqDeriv` show the hypothesis is inhabited by
  the two generators the paper names, but they too speak of the derivative, not of `g`.
* **`𝓜²(λ)` and `L²(λ)` are absent.** On a `Fintype` every function is square-summable, so the
  paper's ambient Hilbert space carries no content here and no norm is used. The `𝓜²(λ)` norm
  appears in items *(2)*–*(3)* only.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `g` admissible | ✗ **not carried** — unused by item *(1)*; see SCOPE |
| `g` differentiable | ✗ not carried; only the values `g'(r(x))` enter, as `gd (r x)` |
| `sign g'(x) = sign(x − 1)` for `x ≠ 1` | ✓ `StrictlyUnimodal gd : ∀ x, 0 < x → x ≠ 1 → 0 < gd x * (x − 1)`, which is that sign condition on `ℝ_+^*`, where `g` lives |
| `(𝒮̂, λ, T)` ergodic | ⚠ **weakened to `λ`-invariance** (`Invariant K lam`); ergodicity is unused by item *(1)*. See SCOPE |
| `𝒮̂` a general measurable space | ⚠ **finite** (`[Fintype V]`). See SCOPE |
| `λ` a probability | ⚠ not carried: only `λ > 0` pointwise is used, and `∑ λ = 1` nowhere. Weaker, and recorded |
| `T` a Markov kernel | ⚠ only `K ≥ 0` (`hK`) is carried, and only to derive `r > 0`; the rows are never summed |
| `μ ∼ λ`, `u = dμ/dλ` | ✓ `u : V → ℝ` with `hu : ∀ x, 0 < u x` — mutual absolute continuity, on a finite space |
| `μT ≪ μ`, `r = d(μT)/dμ` | ✓ `ratio K lam u`, defined; `μT ≪ μ` is automatic once `u > 0` |
| `r` essentially bounded away from `0` and `∞` | ⚠ **not hypothesised**: `0 < r` is *derived* (`ratio_pos`) and boundedness is vacuous on a `Fintype`. The hypothesis belongs to `theo:first_variation_full`, which this file does not prove |
| `dν/dμ > 0` `μ`-a.e. | ✓ `hw : ∀ x, 0 < w x`, with `w = dν/dμ` |
| `ν` finite, `dν/dμ ∈ L^∞(μ)` | ⚠ not carried: vacuous on a `Fintype`. Belongs to `theo:first_variation_full` |
| `D = P†φ − rφ` | ⚠ **taken as a definition**, not derived — the boundary of this file. See SCOPE |
| `μ` balanced `⟺ μT = μ` | ✓ `Balanced K lam u : ∀ y, ∑ x, λ(x) u(x) K(x,y) = λ(y) u(y)` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### The chain, its function action, and its invariant measure -/

/-- **`λ` is invariant for the kernel `K`**: `λK = λ`, written as a finite sum. This is the
paper's "`λ` is `T`-invariant", and — read on the density action `P` of `T` — it is exactly the
paper's `P𝟏 = 𝟏`. -/
def Invariant (K : V → V → ℝ) (lam : V → ℝ) : Prop := ∀ y, ∑ x, lam x * K x y = lam y

/-- The **function action** of the kernel, `(Qφ)(x) = ∑_y K(x,y) φ(y)`. This is the paper's
`P†`: on `L²(λ)` it is the adjoint of the density action `P`, and `⟨Pu, v⟩_λ = ⟨u, Qv⟩_λ` is the
elementary Fubini exchange that `integral_funAct` performs inline. -/
def funAct (K : V → V → ℝ) (φ : V → ℝ) : V → ℝ := fun x => ∑ y, K x y * φ y

/-- **`∫ Qφ dλ = ∫ φ dλ`** — the paper's `∫ P†φ dλ = ⟨φ, P𝟏⟩ = ∫ φ dλ`.

Its only input is invariance of `λ`. Row-stochasticity of `K` is *not* used: exchanging the two
sums leaves `∑_y φ(y) (∑_x λ(x) K(x,y))`, and it is the inner sum that invariance collapses. -/
theorem integral_funAct {K : V → V → ℝ} {lam : V → ℝ} (h : Invariant K lam) (φ : V → ℝ) :
    ∑ x, lam x * funAct K φ x = ∑ x, lam x * φ x := by
  have hexp : ∀ x : V, lam x * funAct K φ x = ∑ y, lam x * K x y * φ y := by
    intro x
    simp only [funAct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul, h y]

/-! ### The gradient density, taken as a definition -/

/-- **`D = Qφ − rφ`**, the gradient density of `prop:no_distant_equilibrium`'s proof
(`proofs.tex:801`).

**This is a definition, not a derivation.** That `D` represents `∇^λ 𝓛_{g,ν}(μ)` is
`theo:first_variation_full` (`proofs.tex:447–483`), which is not formalized; see the module
SCOPE. Everything below is a theorem about this expression. -/
def gradDensity (K : V → V → ℝ) (r φ : V → ℝ) : V → ℝ := fun x => funAct K φ x - r x * φ x

/-- **`∫ D dλ = ∫ φ(1 − r) dλ`** (`proofs.tex:803`), from `integral_funAct`. -/
theorem integral_gradDensity {K : V → V → ℝ} {lam : V → ℝ} (h : Invariant K lam) (r φ : V → ℝ) :
    ∑ x, lam x * gradDensity K r φ x = ∑ x, lam x * (φ x * (1 - r x)) := by
  have hexp : ∀ x : V, lam x * gradDensity K r φ x
      = lam x * funAct K φ x - lam x * (r x * φ x) := by
    intro x; simp only [gradDensity]; ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x, Finset.sum_sub_distrib,
    integral_funAct h φ, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **`∫ D dλ = ∫ g'(r)(1 − r)(dν/dμ) dλ`** (`proofs.tex:803`), the mass identity itself, at
`φ = g'(r)·(dν/dμ)`. No property of `gd` is used. -/
theorem integral_gradDensity_potential {K : V → V → ℝ} {lam : V → ℝ} (h : Invariant K lam)
    (gd : ℝ → ℝ) (r w : V → ℝ) :
    ∑ x, lam x * gradDensity K r (fun y => gd (r y) * w y) x
      = ∑ x, lam x * (gd (r x) * (1 - r x) * w x) := by
  rw [integral_gradDensity h r fun y => gd (r y) * w y]
  exact Finset.sum_congr rfl fun x _ => by ring

/-! ### Strict unimodality, pointwise -/

/-- **Strict unimodality** (`proofs.tex:788`): `sign g'(x) = sign(x − 1)` for `x ≠ 1`, on the
domain `ℝ_+^*` of the generator. "Same sign, and non-zero" is `0 < g'(x)(x − 1)`.

Only the derivative is carried; `g` itself never appears. See the module SCOPE. -/
def StrictlyUnimodal (gd : ℝ → ℝ) : Prop := ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < gd x * (x - 1)

/-- **`g'(r)(1 − r) < 0` wherever `r ≠ 1`** (`proofs.tex:805`), weighted by `λ > 0` and
`dν/dμ > 0`. -/
theorem term_neg {gd : ℝ → ℝ} (hg : StrictlyUnimodal gd) {l rx wx : ℝ}
    (hl : 0 < l) (hr : 0 < rx) (hw : 0 < wx) (hne : rx ≠ 1) :
    l * (gd rx * (1 - rx) * wx) < 0 := by
  have hpos : 0 < gd rx * (rx - 1) := hg rx hr hne
  have hrw : l * (gd rx * (1 - rx) * wx) = -((l * wx) * (gd rx * (rx - 1))) := by ring
  rw [hrw, neg_lt_zero]
  exact mul_pos (mul_pos hl hw) hpos

/-- The integrand of the mass identity is nonpositive (`proofs.tex:805`). -/
theorem term_nonpos {gd : ℝ → ℝ} (hg : StrictlyUnimodal gd) {l rx wx : ℝ}
    (hl : 0 ≤ l) (hr : 0 < rx) (hw : 0 < wx) :
    l * (gd rx * (1 - rx) * wx) ≤ 0 := by
  rcases eq_or_ne rx 1 with h | h
  · rw [h]; simp
  · rcases hl.lt_or_eq with hlt | heq
    · exact (term_neg hg hlt hr hw h).le
    · rw [← heq]; simp

/-- It vanishes exactly at `r = 1` (`proofs.tex:805`), where `λ > 0` and `dν/dμ > 0` are what
turns "vanishes" into "`r = 1`". -/
theorem term_eq_zero_iff {gd : ℝ → ℝ} (hg : StrictlyUnimodal gd) {l rx wx : ℝ}
    (hl : 0 < l) (hr : 0 < rx) (hw : 0 < wx) :
    l * (gd rx * (1 - rx) * wx) = 0 ↔ rx = 1 := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_lt (term_neg hg hl hr hw hne))
  · intro h; rw [h]; simp

/-! ### The ratio `r = d(μT)/dμ`, and balance -/

/-- The measure `μT` as a vector against the counting structure: `y ↦ ∑_x λ(x) u(x) K(x,y)`,
which is `d(μT)/dλ · λ` for `μ = uλ`. -/
def pushMass (K : V → V → ℝ) (lam u : V → ℝ) : V → ℝ := fun y => ∑ x, lam x * u x * K x y

/-- **`μ` is balanced**: `μT = μ` (`proofs.tex:805`). -/
def Balanced (K : V → V → ℝ) (lam u : V → ℝ) : Prop := ∀ y, pushMass K lam u y = lam y * u y

/-- **`r = d(μT)/dμ`** (`proofs.tex:448`, restated at `proofs.tex:821`) for `μ = uλ`. -/
noncomputable def ratio (K : V → V → ℝ) (lam u : V → ℝ) : V → ℝ :=
  fun y => pushMass K lam u y / (lam y * u y)

/-- **`r > 0` is derived, not hypothesised.** Invariance gives `∑_x λ(x)K(x,y) = λ(y) > 0`, so
some `x` sends positive mass into `y`; `u > 0` then makes the numerator of `r(y)` positive.

The paper hypothesises `r` essentially bounded away from `0` and `∞` — in
`theo:first_variation_full`, where the first variation is computed. Here the lower bound comes
free. -/
theorem ratio_pos {K : V → V → ℝ} {lam u : V → ℝ} (hinv : Invariant K lam)
    (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x) (y : V) :
    0 < ratio K lam u y := by
  have hsum : 0 < ∑ x, lam x * K x y := by rw [hinv y]; exact hlam y
  obtain ⟨x0, hx0⟩ : ∃ x0 : V, 0 < lam x0 * K x0 y := by
    by_contra hc
    have hle : ∀ x : V, lam x * K x y ≤ 0 := fun x => not_lt.mp (not_exists.mp hc x)
    have hzero : ∑ x, lam x * K x y = 0 :=
      Finset.sum_eq_zero fun x _ => le_antisymm (hle x) (mul_nonneg (hlam x).le (hK x y))
    rw [hzero] at hsum
    exact lt_irrefl 0 hsum
  have hnum : 0 < pushMass K lam u y := by
    simp only [pushMass]
    refine Finset.sum_pos' (fun x _ => mul_nonneg (mul_nonneg (hlam x).le (hu x).le) (hK x y))
      ⟨x0, mem_univ x0, ?_⟩
    have hrw : lam x0 * u x0 * K x0 y = u x0 * (lam x0 * K x0 y) := by ring
    rw [hrw]
    exact mul_pos (hu x0) hx0
  exact div_pos hnum (mul_pos (hlam y) (hu y))

/-- **`r ≡ 1` if and only if `μT = μ`** (`proofs.tex:805`: "`r = 1` […] `μ`-a.e., i.e.
`μT = μ`"). -/
theorem ratio_eq_one_iff_balanced {K : V → V → ℝ} {lam u : V → ℝ}
    (hpos : ∀ y, 0 < lam y * u y) :
    (∀ y, ratio K lam u y = 1) ↔ Balanced K lam u := by
  constructor
  · intro h y
    have hy := h y
    simp only [ratio] at hy
    rw [div_eq_iff (ne_of_gt (hpos y)), one_mul] at hy
    exact hy
  · intro h y
    simp only [ratio, h y]
    exact div_self (ne_of_gt (hpos y))

/-! ### The gradient density of the balance loss, and its mass -/

/-- The gradient density `D = Qφ − rφ` at `φ = g'(r)·(dν/dμ)`, with `r` the ratio of `μ = uλ` and
`w = dν/dμ`. A definition, on the reading disclosed in the module SCOPE. -/
noncomputable def lossGradDensity (K : V → V → ℝ) (lam u w : V → ℝ) (gd : ℝ → ℝ) : V → ℝ :=
  gradDensity K (ratio K lam u) fun y => gd (ratio K lam u y) * w y

/-- **The total mass of `∇^λ 𝓛_{g,ν}(μ)`**, `∫ D dλ`, on that same reading. -/
noncomputable def gradMass (K : V → V → ℝ) (lam u w : V → ℝ) (gd : ℝ → ℝ) : ℝ :=
  ∑ x, lam x * lossGradDensity K lam u w gd x

/-- **`prop:no_distant_equilibrium`*(1)*, the mass identity** (statement `proofs.tex:789–790`,
proof `proofs.tex:801–805`).

The three conjuncts are the paper's three assertions, in its order: the total mass of
`∇^λ 𝓛_{g,ν}(μ)` *is* `∫ g'(r)(1 − r)(dν/dμ) dλ`; it is `≤ 0`; and it vanishes if and only if
`μ` is balanced.

`w` is `dν/dμ`, positive as the paper requires; `u` is `dμ/dλ`; `gd` is `g'`. What the mass is
the mass *of* is `lossGradDensity`, which is `D = Qφ − rφ` **by definition** — the identification
with the gradient is `theo:first_variation_full`'s and is not performed here. -/
theorem no_distant_equilibrium_one {K : V → V → ℝ} {lam u w : V → ℝ} {gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hw : ∀ x, 0 < w x) (hg : StrictlyUnimodal gd) :
    gradMass K lam u w gd
        = ∑ x, lam x * (gd (ratio K lam u x) * (1 - ratio K lam u x) * w x)
      ∧ gradMass K lam u w gd ≤ 0
      ∧ (gradMass K lam u w gd = 0 ↔ Balanced K lam u) := by
  have hr : ∀ y, 0 < ratio K lam u y := ratio_pos hinv hK hlam hu
  have hid : gradMass K lam u w gd
      = ∑ x, lam x * (gd (ratio K lam u x) * (1 - ratio K lam u x) * w x) := by
    simp only [gradMass, lossGradDensity]
    exact integral_gradDensity_potential hinv gd (ratio K lam u) w
  refine ⟨hid, ?_, ?_⟩
  · rw [hid]
    exact Finset.sum_nonpos fun x _ => term_nonpos hg (hlam x).le (hr x) (hw x)
  · rw [hid]
    rw [← ratio_eq_one_iff_balanced (fun y => mul_pos (hlam y) (hu y))]
    constructor
    · intro h y
      have hnp : ∀ x ∈ (univ : Finset V),
          lam x * (gd (ratio K lam u x) * (1 - ratio K lam u x) * w x) ≤ 0 :=
        fun x _ => term_nonpos hg (hlam x).le (hr x) (hw x)
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp h y (mem_univ y)
      exact (term_eq_zero_iff hg (hlam y) (hr y) (hw y)).mp hzero
    · intro h
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [h x]
      ring

/-- **"Every critical point of `𝓛_{g,ν}` is therefore balanced"** (`proofs.tex:790`, proof
`proofs.tex:805`: "at a critical point `D = 0`, so the mass vanishes and `μ` is balanced").

*Critical* is read as `D = 0` pointwise, `D` being `lossGradDensity`. That this is criticality of
`𝓛_{g,ν}` is `theo:first_variation_full`'s identification and is **not** established here; see the
module SCOPE. -/
theorem balanced_of_critical {K : V → V → ℝ} {lam u w : V → ℝ} {gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hw : ∀ x, 0 < w x) (hg : StrictlyUnimodal gd)
    (hD : ∀ x, lossGradDensity K lam u w gd x = 0) :
    Balanced K lam u := by
  obtain ⟨-, -, hiff⟩ := no_distant_equilibrium_one hinv hK hlam hu hw hg
  refine hiff.mp ?_
  simp only [gradMass]
  exact Finset.sum_eq_zero fun x _ => by rw [hD x, mul_zero]

/-- **`theo:global_dichotomy_full`*(1)*, the mass-identity half** (statement `proofs.tex:820–826`,
item *(1)* at `:823`; proof `proofs.tex:828–830`).

Word for word the first horn of the dichotomy: for a strictly unimodal generator the total mass of
`∇^λ 𝓛_{g,ν}` equals `∫ g'(r)(1 − r)(dν/dμ) dλ ≤ 0`, with equality only at balance, *for every
training measure with positive density* (`w` is arbitrary subject to `w > 0`) *on every graph,
cycles included* (`K` is an arbitrary non-negative kernel with an invariant `λ > 0`; nothing
excludes cycles).

It is the same identity as `no_distant_equilibrium_one` and is proved by it, exactly as the
paper's own proof does. **The second half of item *(1)* — convergence of the gradient flow from
every initialization, which the paper takes from `prop:no_distant_equilibrium`*(3)* — is not
here**, and neither is item *(2)*; see the module SCOPE. -/
theorem global_dichotomy_full_one {K : V → V → ℝ} {lam u w : V → ℝ} {gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hw : ∀ x, 0 < w x) (hg : StrictlyUnimodal gd) :
    gradMass K lam u w gd
        = ∑ x, lam x * (gd (ratio K lam u x) * (1 - ratio K lam u x) * w x)
      ∧ gradMass K lam u w gd ≤ 0
      ∧ (gradMass K lam u w gd = 0 ↔ Balanced K lam u) :=
  no_distant_equilibrium_one hinv hK hlam hu hw hg

/-! ### The hypothesis is inhabited: the paper's two generators -/

/-- `g = (x − 1)²`, so `g'(x) = 2(x − 1)`, is strictly unimodal (`proofs.tex:788`). -/
theorem strictlyUnimodal_sqDeriv : StrictlyUnimodal fun x : ℝ => 2 * (x - 1) := by
  intro x _ hne
  have hne' : x - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < (x - 1) * (x - 1) := mul_self_pos.mpr hne'
  nlinarith

/-- `g = (log x)²`, so `g'(x) = 2 log x / x`, is strictly unimodal (`proofs.tex:788`) — the
paper's practical generator. -/
theorem strictlyUnimodal_logSqDeriv :
    StrictlyUnimodal fun x : ℝ => 2 * Real.log x / x := by
  intro x hx hne
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hlog : Real.log x < 0 := Real.log_neg hx hlt
    have h1 : 2 * Real.log x / x < 0 := div_neg_of_neg_of_pos (by linarith) hx
    exact mul_pos_of_neg_of_neg h1 (by linarith)
  · exact absurd heq hne
  · have hlog : 0 < Real.log x := Real.log_pos hgt
    have h1 : 0 < 2 * Real.log x / x := div_pos (by linarith) hx
    exact mul_pos h1 (by linarith)

/-! ### On the loop closure of a finite marked graph -/

section MarkedGraph

open GFNBounds.Graph

variable [DecidableEq V] {G : MarkedGraph V} {B : BackwardPolicy G}

/-- `GFNBounds.Graph`'s `IsInvProb` supplies this file's `Invariant` verbatim: `IsInvProb.inv` is
`∀ y, ∑ x, λ(x) π̂_←(x,y) = λ(y)`. Nothing is redefined. -/
theorem invariant_of_isInvProb {lam : V → ℝ} (h : B.IsInvProb lam) : Invariant B.phat lam := h.inv

/-- **`prop:no_distant_equilibrium`*(1)* and `theo:global_dichotomy_full`*(1)* on the backward
chain of a finite path-connected marked graph**, the setting every downstream use is in.

`λ` is the invariant probability of `theo:universality_graphs`*(1)*, positive by `IsInvProb.pos`;
`K` is the loop closure `π̂_←`, non-negative by `phat_nonneg`. "On every graph, cycles included" is
literal: nothing here excludes a cycle in `G`. -/
theorem no_distant_equilibrium_one_graph {lam u w : V → ℝ} {gd : ℝ → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (h : B.IsInvProb lam)
    (hu : ∀ x, 0 < u x) (hw : ∀ x, 0 < w x) (hg : StrictlyUnimodal gd) :
    gradMass B.phat lam u w gd
        = ∑ x, lam x * (gd (ratio B.phat lam u x) * (1 - ratio B.phat lam u x) * w x)
      ∧ gradMass B.phat lam u w gd ≤ 0
      ∧ (gradMass B.phat lam u w gd = 0 ↔ Balanced B.phat lam u) :=
  no_distant_equilibrium_one (invariant_of_isInvProb h) B.phat_nonneg (h.pos hpc hpos) hu hw hg

/-- **Every critical point is balanced, on a finite marked graph** — on the reading of *critical*
disclosed in the module SCOPE. -/
theorem balanced_of_critical_graph {lam u w : V → ℝ} {gd : ℝ → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (h : B.IsInvProb lam)
    (hu : ∀ x, 0 < u x) (hw : ∀ x, 0 < w x) (hg : StrictlyUnimodal gd)
    (hD : ∀ x, lossGradDensity B.phat lam u w gd x = 0) :
    Balanced B.phat lam u :=
  balanced_of_critical (invariant_of_isInvProb h) B.phat_nonneg (h.pos hpc hpos) hu hw hg hD

end MarkedGraph

end GFNBounds.Balance
