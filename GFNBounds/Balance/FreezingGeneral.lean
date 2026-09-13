import GFNBounds.Balance.FirstVariation

/-!
# Nonlinear freezing for every generator that is flat and positive on the bands

**`prop:nonlinear_freezing`** — statement `proofs.tex:780–788`, item *(1)* at `:783`, proof of
*(1)* at `:793–797`. This file certifies item *(1)* in the generality the draft has stated since
2026-09-13: for **every** generator `g̃` flat and positive on the bands, not only the constructed
`g`. The construction, item *(2)* and the `g`-specific form of item *(1)* are closed in
`GFNBounds/Balance/Freezing.lean`; item *(2)*'s mixing parenthesis in
`GFNBounds/Balance/WeightedL2Norm.lean`. (The bold-backtick form of the label is
what `scripts/trace_check.py` and the paper-side ledger machine-read.)

> (`proofs.tex:781`) Let `U⁻` and `U⁺` be nonempty bounded open intervals with
> `closure U⁻ ⊂ (0,1)` and `closure U⁺ ⊂ (1,+∞)`, […]

> (`proofs.tex:783`) *(1)* for every `g̃ : ℝ⁺* → ℝ` continuously differentiable with locally
> Lipschitz derivative, positive on `U⁻ ∪ U⁺` and with `g̃' ≡ 0` there, `g` included, and every
> ergodic `(𝒮̂, λ, T)`, every `μ` whose ratio `r = d(μT)/dμ` takes values in `U⁻ ∪ U⁺`
> `λ`-almost everywhere is a critical point of `𝓛_{g̃,ν}` for *every* training measure `ν`; on a
> finite state space the set of such `μ` is open, and `𝓛_{g̃,ν}` is locally constant and positive
> on it;

> (proof, `proofs.tex:793–797`) […] `d/ds 𝓛_{g̃,ν}(μ+sδ)|_{s=0} = ∫ g̃'(r)[d(δT)/dμ − r dδ/dμ] dν
> = 0`, since `g̃'(r) = 0` `ν`-almost everywhere (`ν ≪ μ ∼ λ`): `μ` is critical for every `ν`. On
> a finite state space, `μ ↦ r(μ)` is continuous on `{μ > 0}`, so band-valued ratios persist under
> small perturbations and the set is open; `g̃'` vanishing identically on each band makes `g̃`
> constant on each of the two intervals, so every `g̃(r(x))`, hence `𝓛_{g̃,ν}`, is locally
> constant — and positive, since `g̃ > 0` on the bands.

## What is proved

| | |
|---|---|
| `const_on_band_of_deriv_zero` | a function with derivative `0` at every point of an open interval is constant on it — the proof's "`g̃'` vanishing identically on each band makes `g̃` constant on each of the two intervals" |
| `FreezingBands.pos_of_mem_bands` | the bands lie in `(0,∞)` |
| `eventually_loss_eq_of` | `𝓛_{g̃,ν}` is locally constant on the frozen set, for every `g̃` differentiable with zero derivative on the bands |
| `loss_pos_of` | `𝓛_{g̃,ν}` is positive on the frozen set, for every `g̃ > 0` on the bands and `ν > 0` pointwise |
| `loss_pos_of_nonneg` | the same under the paper's weaker `ν ≥ 0`, `ν ≠ 0` |
| `hasFDerivAt_loss_zero_of` | **Fréchet criticality**: for every `ν`, `u' ↦ 𝓛_{g̃,ν}(u')` has Fréchet derivative `0` at a band-valued `u` — the loss is locally constant there |
| `freezing_item_one_general` | **item *(1)* in full**, for every such `g̃`: `D ≡ 0` for every `ν`, Fréchet criticality for every `ν`, the frozen set is open, the loss is locally constant and positive there |
| `freezing_hasDerivAt_zero_general` | the directional form, through `FirstVariation.hasDerivAt_loss`: every directional derivative of `t ↦ 𝓛_{g̃,ν}(μ + tδ)` vanishes at `0`. Implied by the Fréchet form; kept because it runs through the paper's own first-variation formula |
| `freezing_item_one_of_general` | `Freezing.freezing_item_one`'s exact statement, recovered as the instance `(g̃, g̃') = (F.g, deriv F.g)` — "`g` included" |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `U⁻`, `U⁺` nonempty bounded open intervals, `closure U⁻ ⊂ (0,1)`, `closure U⁺ ⊂ (1,+∞)` | ✓ `F : FreezingBands`: `U⁻ = Ioo a b`, `U⁺ = Ioo c d` with `0 < a < b < 1 < c < d`. A nonempty bounded open interval is `(a,b)` with `a < b`; its closure `[a,b]` lies in `(0,1)` iff `0 < a` and `b < 1`, and `[c,d] ⊂ (1,∞)` iff `1 < c`. Exact match — `Freezing.lean`'s `⚠` on `1 < c` predates the 2026-09-08 repair |
| `g̃ : ℝ⁺* → ℝ` | ⚠ `gt : ℝ → ℝ`; values off the bands are never read by `freezing_item_one_general`, and off `(0,∞)` by none of the theorems here |
| `g̃` continuously differentiable | ⚠ **weakened**: `freezing_item_one_general` takes only `hd : ∀ x ∈ F.bands, HasDerivAt gt (gd x) x`; `freezing_hasDerivAt_zero_general` takes differentiability on `(0,∞)` (`hg`). Continuity of the derivative is used nowhere. See SCOPE |
| `g̃'` locally Lipschitz | ✗ **not carried, unused**. See SCOPE |
| `g̃ > 0` on `U⁻ ∪ U⁺` | ✓ `hpos : ∀ z ∈ F.bands, 0 < gt z` |
| `g̃' ≡ 0` on `U⁻ ∪ U⁺` | ✓ `hgd0 : ∀ z ∈ F.bands, gd z = 0`, with `gd` pinned to `g̃'` on the bands by `hd` |
| "`g` included" | ✓ `freezing_item_one_of_general`, from `FreezingBands.differentiable_g` and `deriv_g_eq_zero_of_mem_bands'`, `g_pos` |
| `(𝒮̂, λ, T)` ergodic | ⚠ weakened to nothing, in every theorem here: no `Invariant K lam`, no `0 ≤ K`. Positivity of the ratios, which `FirstVariation.hasDerivAt_loss` needs, comes from the bands (`0 < a`, `FreezingBands.pos_of_mem_bands`) rather than from invariance |
| `μ` with `r` band-valued `λ`-a.e. | ✓ `u ∈ frozen K lam F.bands`: `u > 0` and `∀ x, ratio K lam u x ∈ F.bands` |
| critical point of `𝓛_{g̃,ν}` for every `ν` | ✓ `∀ nu', HasFDerivAt (fun u' => loss K lam nu' u' gt) 0 u` — **Fréchet** criticality in `V → ℝ`, for every `ν` including those vanishing on states. The conjunct `∀ w, ∀ x, lossGradDensity K lam u w gd x = 0` is the paper's formula `g̃'(r) = 0 ⇒ D = 0`, proved from `hgd0` alone and not by itself a criticality statement |
| (finite state space) the set of such `μ` is open | ✓ `IsOpen (frozen K lam F.bands)`, the product topology of `V → ℝ` |
| `𝓛_{g̃,ν}` locally constant on it | ✓ `∀ᶠ u' in nhds u, loss K lam nu u' gt = loss K lam nu u gt` |
| `𝓛_{g̃,ν}` positive on it | ⚠ **strengthened hypothesis** in `freezing_item_one_general`: `ν > 0` pointwise (`hnu`), where the paper's training measure may vanish on states. Positivity needs only `ν ≥ 0` and `ν ≠ 0` (a zero `ν` gives loss `0`, so the paper is entitled to that much); that form is `loss_pos_of_nonneg`. `hnu` is kept in the bundled theorem so that it restates `Freezing.freezing_item_one`'s hypotheses exactly |

## SCOPE (disclosed)

* **The locally Lipschitz derivative is unused, and is not carried.** None of the five
  conclusions consumes it: criticality is `g̃'(r) = 0`, openness is continuity of `u ↦ r(u)`, local
  constancy is a zero derivative on an open interval, Fréchet criticality is local constancy,
  positivity is `g̃ > 0` on the bands, and the directional form needs only `HasDerivAt` on
  `(0,∞)`. Carrying it as a hypothesis
  would be an unused variable, a build failure under `warningAsError`. The paper's hypothesis is
  there for the dynamics — well-posedness of the gradient flow — which item *(1)* does not state.
  Continuity of `g̃'` is likewise never used. Every theorem here therefore holds for a strictly
  larger class of generators than the paper's; nothing is claimed about a generator outside that
  class that the paper's class does not already cover by restriction.
* **The reading of *critical*.** `hasFDerivAt_loss_zero_of` certifies it outright: the loss has
  Fréchet derivative `0` at every band-valued `u`, for every `ν`, in `V → ℝ` with its product
  topology (on a `Fintype` the topology of `𝓜²(λ)`). The route is local constancy, not the
  first-variation formula, so it needs no invariance and no differentiability of `g̃` off the
  bands. The `D = 0` conjunct is kept beside it as the paper's formula — `gd` enters `D` only at
  the ratio values, where `hd` pins `gd = g̃'` — but it is not by itself a criticality statement.
* **Finite state space**, as everywhere in `GFNBounds.Balance`: `∫ · dλ` is `∑ x, λ x * ·`, and
  `a.e.` is `∀ x`. The paper states criticality for a general ergodic system and openness,
  constancy and positivity "on a finite state space"; only the finite case of the first half is
  certified.
* **Not this file's**: the construction of `g`, item *(2)*, item *(3)* and the proposition's closing
  sentence — see `Freezing.lean`'s SCOPE, which this file does not alter.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

/-- **A zero derivative on an open interval makes a function constant there** (`proofs.tex:797`:
"`g̃'` vanishing identically on each band makes `g̃` constant on each of the two intervals").
Differentiability is asked on the interval only. -/
theorem const_on_band_of_deriv_zero {gt gd : ℝ → ℝ} {p q : ℝ}
    (hd : ∀ x ∈ Set.Ioo p q, HasDerivAt gt (gd x) x) (h0 : ∀ x ∈ Set.Ioo p q, gd x = 0)
    {x y : ℝ} (hx : x ∈ Set.Ioo p q) (hy : y ∈ Set.Ioo p q) : gt x = gt y :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hd z hz).deriv, h0 z hz]; rfl) hx hy

/-- **Every point of the bands is positive**: `U⁻ ⊂ (0,1)` because `0 < a`, `U⁺ ⊂ (1,∞)`. -/
theorem FreezingBands.pos_of_mem_bands (F : FreezingBands) {z : ℝ} (hz : z ∈ F.bands) : 0 < z := by
  rcases hz with h | h
  · exact F.a_pos.trans (Set.mem_Ioo.1 h).1
  · exact (zero_lt_one.trans F.one_lt_c).trans (Set.mem_Ioo.1 h).1

section Frozen

variable {V : Type*} [Fintype V]

/-- **`𝓛_{g̃,ν}` is locally constant on the frozen set** (`proofs.tex:783`, `:797`), for every
`g̃` with zero derivative on the bands: near a band-valued `u`, each ratio stays inside its own
band, on which `g̃` is constant. -/
theorem eventually_loss_eq_of (F : FreezingBands) {gt gd : ℝ → ℝ}
    (hd : ∀ x ∈ F.bands, HasDerivAt gt (gd x) x) (hgd0 : ∀ x ∈ F.bands, gd x = 0)
    {K : V → V → ℝ} {lam nu : V → ℝ} (hlam : ∀ x, 0 < lam x) {u0 : V → ℝ}
    (hu0 : u0 ∈ frozen K lam F.bands) :
    ∀ᶠ u in nhds u0, loss K lam nu u gt = loss K lam nu u0 gt := by
  obtain ⟨hpos, hband⟩ := hu0
  have hdl : ∀ z ∈ F.lower, HasDerivAt gt (gd z) z := fun z hz => hd z (Or.inl hz)
  have h0l : ∀ z ∈ F.lower, gd z = 0 := fun z hz => hgd0 z (Or.inl hz)
  have hdu : ∀ z ∈ F.upper, HasDerivAt gt (gd z) z := fun z hz => hd z (Or.inr hz)
  have h0u : ∀ z ∈ F.upper, gd z = 0 := fun z hz => hgd0 z (Or.inr hz)
  have key : ∀ x : V, ∀ᶠ u in nhds u0, gt (ratio K lam u x) = gt (ratio K lam u0 x) := by
    intro x
    have hcont : ContinuousAt (fun u => ratio K lam u x) u0 :=
      continuousAt_ratio x (mul_pos (hlam x) (hpos x)).ne'
    rcases hband x with h | h
    · filter_upwards [hcont.preimage_mem_nhds (F.isOpen_lower.mem_nhds h)] with u hu
      exact const_on_band_of_deriv_zero hdl h0l hu h
    · filter_upwards [hcont.preimage_mem_nhds (F.isOpen_upper.mem_nhds h)] with u hu
      exact const_on_band_of_deriv_zero hdu h0u hu h
  filter_upwards [Filter.eventually_all.2 key] with u hu
  exact Finset.sum_congr rfl fun x _ => by rw [hu x]

/-- **`𝓛_{g̃,ν}` is positive on the frozen set** (`proofs.tex:783`, `:797`: "positive, since
`g̃ > 0` on the bands"). -/
theorem loss_pos_of (F : FreezingBands) [Nonempty V] {gt : ℝ → ℝ}
    (hpos : ∀ z ∈ F.bands, 0 < gt z) {K : V → V → ℝ} {lam nu u : V → ℝ}
    (hnu : ∀ x, 0 < nu x) (hband : ∀ x, ratio K lam u x ∈ F.bands) :
    0 < loss K lam nu u gt :=
  Finset.sum_pos (fun x _ => mul_pos (hnu x) (hpos _ (hband x))) Finset.univ_nonempty

/-- **`𝓛_{g̃,ν}` is positive on the frozen set for every nonzero `ν ≥ 0`** (`proofs.tex:783`,
`:797`): the paper's training measure may vanish on states, and one state of positive mass
suffices. -/
theorem loss_pos_of_nonneg (F : FreezingBands) {gt : ℝ → ℝ}
    (hpos : ∀ z ∈ F.bands, 0 < gt z) {K : V → V → ℝ} {lam nu u : V → ℝ}
    (hnu0 : ∀ x, 0 ≤ nu x) (hnu : ∃ x, 0 < nu x) (hband : ∀ x, ratio K lam u x ∈ F.bands) :
    0 < loss K lam nu u gt := by
  obtain ⟨x0, hx0⟩ := hnu
  exact Finset.sum_pos' (fun x _ => mul_nonneg (hnu0 x) (hpos _ (hband x)).le)
    ⟨x0, Finset.mem_univ x0, mul_pos hx0 (hpos _ (hband x0))⟩

/-- **A band-valued flow is a Fréchet critical point of `𝓛_{g̃,ν}` for every training measure**
(`proofs.tex:783`, proof `:793–797`): the loss is locally constant near `u`, so its Fréchet
derivative there is `0`. No invariance, and no differentiability of `g̃` off the bands. -/
theorem hasFDerivAt_loss_zero_of (F : FreezingBands) {gt gd : ℝ → ℝ}
    (hd : ∀ x ∈ F.bands, HasDerivAt gt (gd x) x) (hgd0 : ∀ x ∈ F.bands, gd x = 0)
    {K : V → V → ℝ} {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) {u : V → ℝ}
    (hu : u ∈ frozen K lam F.bands) (nu : V → ℝ) :
    HasFDerivAt (fun u' => loss K lam nu u' gt) (0 : (V → ℝ) →L[ℝ] ℝ) u :=
  (hasFDerivAt_const _ u).congr_of_eventuallyEq (eventually_loss_eq_of F hd hgd0 hlam hu)

/-- **`prop:nonlinear_freezing`*(1)* in full, for every generator flat and positive on the bands**
(`proofs.tex:783`, proof `:793–797`), on a finite state space: a band-valued flow is a critical
point of `𝓛_{g̃,ν}` for every training measure; the set of such flows is open; and on it the loss
is locally constant and positive.

The first conjunct is the paper's formula `g̃'(r) = 0 ⇒ D = 0`; the second is criticality proper,
a Fréchet derivative `0` for every `ν`. The paper's `C¹` and locally-Lipschitz-derivative
hypotheses are not consumed, and `hnu` is stronger than positivity needs
(`loss_pos_of_nonneg`); see the module checklist. -/
theorem freezing_item_one_general (F : FreezingBands) [Nonempty V] {gt gd : ℝ → ℝ}
    (hd : ∀ x ∈ F.bands, HasDerivAt gt (gd x) x) (hgd0 : ∀ x ∈ F.bands, gd x = 0)
    (hpos : ∀ z ∈ F.bands, 0 < gt z) {K : V → V → ℝ} {lam nu u : V → ℝ}
    (hlam : ∀ x, 0 < lam x) (hnu : ∀ x, 0 < nu x) (hu : u ∈ frozen K lam F.bands) :
    (∀ w : V → ℝ, ∀ x, lossGradDensity K lam u w gd x = 0)
      ∧ (∀ nu' : V → ℝ, HasFDerivAt (fun u' => loss K lam nu' u' gt) (0 : (V → ℝ) →L[ℝ] ℝ) u)
      ∧ IsOpen (frozen K lam F.bands)
      ∧ (∀ᶠ u' in nhds u, loss K lam nu u' gt = loss K lam nu u gt)
      ∧ 0 < loss K lam nu u gt :=
  ⟨fun w => freezing_critical hu.2 hgd0 (w := w), hasFDerivAt_loss_zero_of F hd hgd0 hlam hu,
    isOpen_frozen hlam F.isOpen_bands, eventually_loss_eq_of F hd hgd0 hlam hu,
    loss_pos_of F hpos hnu hu.2⟩

/-- **`prop:nonlinear_freezing`*(1)*, criticality in the derivative sense, for every generator
flat on the bands** (`proofs.tex:783`, proof `:795–797`): every directional derivative of
`t ↦ 𝓛_{g̃,ν}(μ + tδ)` vanishes at `t = 0`.

`hg` is differentiability of `g̃` on `ℝ⁺*`, which the paper's `C¹` supplies; the ratios are
band-valued, hence positive (`FreezingBands.pos_of_mem_bands`), so no invariance is needed, and
`hgd0` is read only where `hg` pins `gd = g̃'`. `hasFDerivAt_loss_zero_of` is the stronger,
Fréchet form. -/
theorem freezing_hasDerivAt_zero_general (F : FreezingBands) {gt gd : ℝ → ℝ}
    (hg : ∀ y : ℝ, 0 < y → HasDerivAt gt (gd y) y) (hgd0 : ∀ z ∈ F.bands, gd z = 0)
    {K : V → V → ℝ} {lam nu u : V → ℝ} (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hband : ∀ x, ratio K lam u x ∈ F.bands) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) gt) 0 0 := by
  have hD := hasDerivAt_loss (nu := nu) hlam hu (fun x => F.pos_of_mem_bands (hband x)) hg d
  have hz : (∑ x, nu x * (gd (ratio K lam u x) *
      (dirPush K lam u d x - ratio K lam u x * dirDens u d x))) = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [hgd0 _ (hband x), zero_mul, mul_zero]
  rwa [hz] at hD

/-- **`Freezing.freezing_item_one` recovered as an instance** — the paper's "`g` included": the
constructed generator is differentiable with `g' ≡ 0` and `g > 0` on the bands, so
`freezing_item_one_general` at `(g̃, g̃') = (F.g, deriv F.g)` is exactly the `g`-specific
statement. -/
theorem freezing_item_one_of_general (F : FreezingBands) [Nonempty V] {K : V → V → ℝ}
    {lam nu u : V → ℝ} (hlam : ∀ x, 0 < lam x) (hnu : ∀ x, 0 < nu x)
    (hu : u ∈ frozen K lam F.bands) :
    (∀ w : V → ℝ, ∀ x, lossGradDensity K lam u w (deriv F.g) x = 0)
      ∧ IsOpen (frozen K lam F.bands)
      ∧ (∀ᶠ u' in nhds u, loss K lam nu u' F.g = loss K lam nu u F.g)
      ∧ 0 < loss K lam nu u F.g :=
  have h := freezing_item_one_general F (fun x _ => (F.differentiable_g x).hasDerivAt)
    (fun _ hz => F.deriv_g_eq_zero_of_mem_bands' hz)
    (fun _ hz => F.g_pos fun h1 => F.one_notMem_bands (h1 ▸ hz)) hlam hnu hu
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end Frozen

end GFNBounds.Balance
