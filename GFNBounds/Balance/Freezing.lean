import GFNBounds.Balance.MassIdentity

/-!
# Nonlinear freezing: an admissible generator whose gradient vanishes on an open set of flows

**`prop:nonlinear_freezing`** — statement `proofs.tex:759–767` (the construction and item *(1)* at
`:760–762`, item *(2)* at `:763`, item *(3)* at `:764`), proof `proofs.tex:769–781`; the four
comments explaining why the construction must look like this are `rem:freezing`,
`proofs.tex:783–786`. (The bold-backtick form of the label is what `scripts/trace_check.py` and the
paper-side ledger machine-read; a label mentioned only in prose is not a claim to certify it.)

> Let `U⁻ ⊂ (0,1)` and `U⁺ ⊂ (1,+∞)` be nonempty bounded open intervals, let `m : ℝ⁺* → ℝ₊` be
> `C^∞`, bounded, with `m(1) = 2`, `m ≡ 0` on `U⁻ ∪ U⁺` and `m > 0` elsewhere, and set
> `g(x) := ∫₁ˣ m(t)(t−1) dt`. Then `g` is a `C^∞` admissible generator — `g(1) = 0`, `g > 0`
> elsewhere, `g''(1) = 2`, `|g(x)| ≤ C(1 + |x|²)` — with `g' ≡ 0` on `U⁻ ∪ U⁺`, and:
> *(1)* for every ergodic `(𝒮̂, λ, T)`, every `μ` whose ratio `r = d(μT)/dμ` takes values in
> `U⁻ ∪ U⁺` `λ`-almost everywhere is a critical point of `𝓛_{g,ν}` for *every* training measure
> `ν`; on a finite state space the set of such `μ` is open, and `𝓛_{g,ν}` is locally constant and
> positive on it;
> *(2)* on the two-state chain `T(i→j) = 1/2`, `λ = (1/2,1/2)` — for which `β̂ₙ = 0` for all
> `n ≥ 1`, `B̂ = 1`, and the rate `ϱ = 2w_min` of Theorem `theo:db_stable_frozen` is maximal — the
> choice `3/4 ∈ U⁻ ⊂ (5/8,7/8)`, `3/2 ∈ U⁺ ⊂ (11/8,13/8)` yields a nonempty open set of flows, on
> which every ratio deviates from `1` by at least `1/8`, where gradient flow and gradient descent
> (any step, any `ν`) are stationary.

> (proof, *Admissibility*) `g` is `C^∞` with `g'(x) = m(x)(x−1)`, so `g' ≡ 0` on `U⁻ ∪ U⁺` and
> `g''(1) = m(1) = 2`. For `x > 1`, `g(x) = ∫₁ˣ m(t)(t−1) dt > 0` since the integrand is
> nonnegative and positive near `1` (`m(1) = 2`, `m` continuous); symmetrically `g(x) > 0` for
> `x < 1`. Boundedness of `m` gives `|g'(x)| ≤ ‖m‖_∞|x−1|`, hence
> `|g(x)| ≤ (‖m‖_∞/2)(x−1)² ≤ C(1 + |x|²)`.

> (proof of *(1)*) […] `∫ g'(r)[d(δT)/dμ − r dδ/dμ] dν = 0`, since `g'(r) = 0` `ν`-almost
> everywhere (`ν ≪ μ ∼ λ`): `μ` is critical for every `ν`. On a finite state space, `μ ↦ r(μ)` is
> continuous on `{μ > 0}`, so band-valued ratios persist under small perturbations and the set is
> open; `g'` vanishing identically on each band makes `g` constant on each of the two intervals, so
> every `g(r(x))`, hence `𝓛_{g,ν}`, is locally constant — and positive, since the bands do not
> contain `1` and `g > 0` on them.

> (proof of *(2)*) On the two-state chain, the density action is `Ph = (∫h dλ)𝟏 = Πh`, so
> `Pⁿ − Π = 0` for every `n ≥ 1` […]. For `μ* = (1, 1/2)`: `μ*T = (3/4, 3/4)`, so
> `r = (3/4, 3/2) ∈ U⁻ × U⁺`. By continuity, a whole neighbourhood of `μ*` has band-valued ratios,
> and *(1)* applies: the gradient of `𝓛_{g,ν}` vanishes there for every `ν`, so the gradient flow
> is constant and gradient descent is fixed for every step. Every ratio in
> `(5/8,7/8) ∪ (11/8,13/8)` deviates from `1` by at least `1/8`.

## What is proved

The load-bearing claim is that **spurious equilibria exist for some admissible generator** — the
claim that makes the strict-unimodality hypothesis of `prop:no_distant_equilibrium` necessary
rather than decorative. It is delivered in full, with an explicit `g`.

| | |
|---|---|
| `lossGradDensity_eq_zero_of_deriv_vanishes` | `g'(r) ≡ 0 ⇒ φ ≡ 0 ⇒ D ≡ 0`, for every `w` |
| `freezing_critical`, `freezing_gradMass_eq_zero` | item *(1)*, first half: a band-valued ratio is a critical point, for every training measure |
| `flatFactor`, `FreezingBands.m` | the multiplier: `C^∞`, in `[0, 8/scale]`, `m(1) = 2`, vanishing **exactly** on `[a,b] ∪ [c,d]` |
| `FreezingBands.g` | `g(x) = ∫₁ˣ m(t)(t−1) dt`, and `contDiff_g` — genuinely `C^∞`, not a weaker class |
| `g_one`, `g_pos`, `deriv_deriv_g_one`, `abs_g_le_growth` | the four admissibility clauses, in the paper's order |
| `deriv_g`, `deriv_g_eq_zero_of_mem_bands` | `g'(x) = m(x)(x−1)`, hence `g' ≡ 0` on the bands |
| `g_const_on_lower`, `g_const_on_upper` | `g` is constant on each band — the paper's "`g'` vanishing identically on each band makes `g` constant on each of the two intervals" |
| `isOpen_frozen` | item *(1)*, second half: the set of band-valued flows is open |
| `eventually_loss_eq`, `loss_pos` | item *(1)*, second half: `𝓛_{g,ν}` is locally constant and positive there |
| `twoState_*` | item *(2)*: the ratios `(3/4, 3/2)`, the frozen nonempty open set, the `1/8` deviation, and stationarity of every gradient step |

## SCOPE (disclosed)

* **The identification of `D` with the gradient of `𝓛_{g,ν}` is `theo:first_variation_full`'s job
  and is not done here.** This file reuses `GFNBounds.Balance.MassIdentity`'s `gradDensity`,
  `ratio`, `Invariant` and `lossGradDensity` verbatim, and inherits that file's boundary word for
  word: `D = P†φ − rφ` with `φ = g'(r)·(dν/dμ)` is a **definition**, *critical* is read as `D = 0`,
  *gradient descent is stationary* is read as `u ↦ u − η·D` fixing `u`, and *the gradient flow is
  constant* is read as `D = 0` — there is no ODE layer here, and none is claimed. Nothing here
  differentiates `𝓛_{g,ν}` on `𝓜²(λ)`.
* **The paper's hypothesis on `m` is inconsistent as literally written, and is repaired here in
  the only way continuity permits.** `m` continuous with `m ≡ 0` on `U⁻ ∪ U⁺` and `m > 0`
  *elsewhere* would make the nonempty open set `U⁻ ∪ U⁺` closed in the connected space `ℝ⁺*`,
  hence all of it — contradicting `m(1) = 2`. The zero set of a continuous `m` is closed, so what
  is built here is `m > 0` off the **closures** `[a,b] ∪ [c,d]`, which contain `U⁻ ∪ U⁺` and are
  disjoint from `1`. This is *stronger* than what the proposition's proof consumes (which is only
  `m ≥ 0`, `m` continuous, `m(1) = 2`, and `m ≡ 0` on the bands) and it is a paper-side finding,
  not a Lean-side weakening. For the same reason the construction takes `closure U⁻ ⊂ (0,1)` and
  `closure U⁺ ⊂ (1,∞)`: with `U⁻ = (a,1)` no continuous `m` vanishing on `U⁻` has `m(1) = 2`.
* **`C^∞`, not a weaker class.** `contDiff_g : ContDiff ℝ ∞ F.g` is proved, from
  `expNegInvGlue.contDiff` and `contDiff_infty_iff_deriv`; no smoothness was traded away.
* **The proposition's closing sentence is not formalized either** — "no bound on the time for the
  training dynamics to reach a given loss level can hold in terms of `g''(1)`, the mixing
  coefficients and `w` alone" (`proofs.tex:766`). It is a statement *about* the rate theorems, and
  quantifies over bounds; it presupposes item *(3)* and the rate machinery of
  `theo:local_convergence`, neither of which is here.
* **Item *(3)* is not formalized.** The `|g'| ≤ ε` perturbation — the gradient field has norm at
  most `C'ε` on the band-valued configurations with `‖h‖_∞ ≤ 1/2`, so the trajectory needs time
  `≥ d/(C'ε)` to move a distance `d` — is a statement about the *trajectory* of an ODE on
  `𝓜²(λ)`, and needs the gradient-flow layer that `MassIdentity`'s SCOPE records as absent. Its
  static half (the pointwise bound on `D`) would be cheap; the exit-time half is not, and stating
  only the half would misrepresent the item, so neither is stated.
* **The mixing side of item *(2)* is represented by `P = Π`, not by the coefficients.**
  `twoState_funAct_eq_mean` and `twoState_densityAction_eq_mean` prove exactly the sentence the
  paper's proof of *(2)* opens with — "the density action is `Ph = (∫h dλ)𝟏 = Πh`" — from which
  `β̂ₙ = ‖Pⁿ − Π‖ = 0` for `n ≥ 1` follows in one line. The coefficients `β̂ₙ`, `B̂ = 1` and the
  rate `ϱ = 2w_min` of `theo:db_stable_frozen` are **not** stated: `GFNBounds.Core.Mixing.beta` is
  defined for a continuous linear map on a normed space, and instantiating it here would require
  building the `L²(λ)` operator and computing `‖Id − Π‖ = 1`. That is a detour, and the paper's
  own use of those numbers in item *(2)* is to say the freezing survives *maximal* mixing, which
  `P = Π` already says.
* **The paper's `ν` and `MassIdentity`'s `w`.** The paper fixes a training measure `ν` and writes
  `dν/dμ`; `MassIdentity` carries `w = dν/dμ` as the primitive. Criticality is stated here for
  *every* `w > 0`, which is the paper's "for every training measure `ν`". The loss, where `ν` must
  be held fixed while `μ` varies, is defined directly on `ν` (`loss`), and the two readings are
  connected by `nu x = lam x * u x * w x`; no theorem below needs that identity.
* **Ergodicity is not assumed and is not used**, exactly as in `MassIdentity`: item *(1)*'s
  criticality is a pointwise identity, and the openness and local constancy are statements about
  the finite-dimensional map `u ↦ r(u)`.
* **Finite state space**, as in `MassIdentity`: `∫ · dλ` is `∑ x, λ x * ·` and `a.e.` is `∀ x`.
  The paper's item *(1)* is stated for a general ergodic system for the criticality half and
  explicitly "on a finite state space" for the openness half.

**Update, 2026-09-08 — this disclosure is now discharged elsewhere.**
`GFNBounds/Balance/FirstVariation.lean` proves `theo:first_variation_full` on a finite state
space: `hasDerivAt_loss_ipL2` shows that for every direction `d`, the directional derivative of
`𝓛_{g,ν}` at `μ` is `⟪lossGradDensity … ∣ d⟫_{L²(λ)}`, and `lossGradDensity_unique` shows no
other function represents those derivatives. So `D` **is** the gradient, and the readings below
are no longer conditional — with two residues, both still real: the state space is finite (the
general measured-space statement remains bucket `D`), and criticality is *directional* rather
than Fréchet. The wording of this bullet is kept as written because it records what **this
file** proves on its own.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `U⁻ ⊂ (0,1)` nonempty bounded open interval | ⚠ `Set.Ioo a b` with `0 < a < b < 1`: **`b < 1` strictly**, i.e. `closure U⁻ ⊂ (0,1)`. See SCOPE |
| `U⁺ ⊂ (1,∞)` nonempty bounded open interval | ⚠ `Set.Ioo c d` with `1 < c < d`: **`1 < c` strictly**. See SCOPE |
| `m : ℝ⁺* → ℝ₊` | ⚠ `m : ℝ → ℝ` with `0 ≤ m` everywhere; the restriction to `ℝ⁺*` is the paper's, and nothing below needs the domain to be cut |
| `m` is `C^∞` | ✓ `contDiff_m : ContDiff ℝ ∞ F.m` |
| `m` bounded | ✓ `m_le_bound : F.m t ≤ F.bound` with `F.bound = 8 / F.scale` — an explicit formula, per the house rule on constants |
| `m(1) = 2` | ✓ `m_one` |
| `m ≡ 0` on `U⁻ ∪ U⁺` | ✓ `m_eq_zero_of_mem_bands`, on the closed `[a,b] ∪ [c,d]` ⊇ `U⁻ ∪ U⁺` |
| `m > 0` elsewhere | ⚠ **repaired**: `m_pos` gives `m > 0` off `[a,b] ∪ [c,d]`. The literal hypothesis is inconsistent; see SCOPE |
| `g(x) = ∫₁ˣ m(t)(t−1) dt` | ✓ `FreezingBands.g`, definitionally |
| `(𝒮̂, λ, T)` ergodic | ⚠ weakened to nothing at all for criticality: `freezing_critical` assumes no relation between `K`, `lam` and `u`. `Invariant` is needed only where `MassIdentity`'s `ratio_pos` is used |
| `μ` with `r` band-valued `λ`-a.e. | ✓ `∀ x, ratio K lam u x ∈ F.bands` |
| critical point of `𝓛_{g,ν}` for every `ν` | ⚠ `∀ w, ∀ x, lossGradDensity K lam u w (deriv F.g) x = 0`; *critical* read as `D = 0`. See SCOPE |
| the set of such `μ` is open | ✓ `isOpen_frozen`, in the product topology of `V → ℝ` |
| `𝓛_{g,ν}` locally constant on it | ✓ `eventually_loss_eq` |
| `𝓛_{g,ν}` positive on it | ✓ `loss_pos`, from `g_pos` and `1 ∉ F.bands` |
| two-state chain `T(i→j) = 1/2`, `λ = (1/2,1/2)` | ✓ `twoStateK`, `twoStateLam` on `Fin 2` |
| `β̂ₙ = 0`, `B̂ = 1`, `ϱ = 2w_min` maximal | ⚠ **not stated**; represented by `P = Π`. See SCOPE |
| `μ* = (1, 1/2)`, `r = (3/4, 3/2)` | ✓ `twoState_ratio_zero`, `twoState_ratio_one` |
| every ratio deviates from `1` by `≥ 1/8` | ✓ `twoState_bands_deviate` |
| gradient descent fixed for every step | ⚠ `freezing_descent_stationary : u − η·D = u`, applied in `twoState_freezing`, on the reading of `D` disclosed above |
| item *(3)*, the `|g'| ≤ ε` slowdown | ✗ **not formalized**. See SCOPE |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset
open scoped ContDiff

/-! ### The criticality argument

Item *(1)*'s first half, and the shortest part of the proposition: it needs nothing of `g` beyond
the vanishing of `g'` at the values the ratio takes. -/

section Criticality

variable {V : Type*} [Fintype V]

/-- **`prop:nonlinear_freezing`*(1)*, the pointwise identity behind it** (`proofs.tex:774`): if
`g'(r) = 0` at every state, the potential `φ = g'(r)·(dν/dμ)` vanishes identically and so does the
gradient density `D = P†φ − rφ`, whatever `dν/dμ` is.

This is where the paper's "`g'(r) = 0` `ν`-almost everywhere (`ν ≪ μ ∼ λ`)" lands on a finite
state space: `ν`-a.e. is `∀ x`, and the conclusion holds for every `w`. -/
theorem lossGradDensity_eq_zero_of_deriv_vanishes {K : V → V → ℝ} {lam u w : V → ℝ} {gd : ℝ → ℝ}
    (h : ∀ x, gd (ratio K lam u x) = 0) (x : V) :
    lossGradDensity K lam u w gd x = 0 := by
  have hphi : ∀ y, gd (ratio K lam u y) * w y = 0 := fun y => by rw [h y, zero_mul]
  simp only [lossGradDensity, gradDensity, funAct, hphi, mul_zero, Finset.sum_const_zero,
    sub_zero]

/-- **`prop:nonlinear_freezing`*(1)*, first half** (`proofs.tex:762`, proof `proofs.tex:772–775`):
*every `μ` whose ratio takes values in `U⁻ ∪ U⁺` is a critical point of `𝓛_{g,ν}` for every
training measure `ν`* — provided `g'` vanishes on `U⁻ ∪ U⁺`.

`U` is any set on which `g'` vanishes, `w = dν/dμ` is arbitrary, and *critical* is `D = 0`; see the
module SCOPE. -/
theorem freezing_critical {K : V → V → ℝ} {lam u w : V → ℝ} {gd : ℝ → ℝ} {U : Set ℝ}
    (hband : ∀ x, ratio K lam u x ∈ U) (hgd : ∀ z ∈ U, gd z = 0) (x : V) :
    lossGradDensity K lam u w gd x = 0 :=
  lossGradDensity_eq_zero_of_deriv_vanishes (fun y => hgd _ (hband y)) x

/-- **The total mass of the gradient vanishes too**, so the criticality of
`prop:nonlinear_freezing`*(1)* is compatible with `prop:no_distant_equilibrium`*(1)* only because
its generator is not strictly unimodal: there the mass vanishes *iff* `μ` is balanced. -/
theorem freezing_gradMass_eq_zero {K : V → V → ℝ} {lam u w : V → ℝ} {gd : ℝ → ℝ} {U : Set ℝ}
    (hband : ∀ x, ratio K lam u x ∈ U) (hgd : ∀ z ∈ U, gd z = 0) :
    gradMass K lam u w gd = 0 := by
  simp only [gradMass]
  exact Finset.sum_eq_zero fun x _ => by
    rw [freezing_critical hband hgd x, mul_zero]

/-- **Gradient descent is stationary** (`proofs.tex:778`: "the gradient flow is constant and
gradient descent is fixed for every step"), read as the update `u ↦ u − η·D` fixing `u`. -/
theorem freezing_descent_stationary {K : V → V → ℝ} {lam u w : V → ℝ} {gd : ℝ → ℝ} {U : Set ℝ}
    (hband : ∀ x, ratio K lam u x ∈ U) (hgd : ∀ z ∈ U, gd z = 0) (eta : ℝ) :
    (fun x => u x - eta * lossGradDensity K lam u w gd x) = u := by
  funext x
  rw [freezing_critical hband hgd x, mul_zero, sub_zero]

end Criticality

/-! ### The multiplier `m`

`m` has to be `C^∞`, nonnegative, bounded, equal to `2` at `1`, and to vanish on two intervals
straddling `1`. Mathlib's `expNegInvGlue` — `t ↦ e^{-1/t}` for `t > 0` and `0` for `t ≤ 0` — gives
each half of a band in one term: `flatFactor p q` is `C^∞`, and vanishes exactly on `[p, q]`. -/

/-- `e^{-1/x} ≤ 1`: the exponent `-1/x` is nonpositive wherever the glue is not already `0`. -/
theorem expNegInvGlue_le_one (x : ℝ) : expNegInvGlue x ≤ 1 := by
  rcases le_or_gt x 0 with h | h
  · rw [expNegInvGlue.zero_of_nonpos h]; norm_num
  · simp only [expNegInvGlue, if_neg (not_le.2 h)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (inv_pos.2 h).le)

/-- **The flat factor of a band**: `flatFactor p q t = e^{-1/(p−t)} + e^{-1/(t−q)}`, a `C^∞`
function with values in `[0, 2]` vanishing **exactly** on `[p, q]`.

The zero set of a continuous function is closed, which is why the band this vanishes on is the
closed `[p, q]` and not an open interval; see the module SCOPE. -/
noncomputable def flatFactor (p q t : ℝ) : ℝ :=
  expNegInvGlue (p - t) + expNegInvGlue (t - q)

theorem flatFactor_nonneg (p q t : ℝ) : 0 ≤ flatFactor p q t :=
  add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

theorem flatFactor_le_two (p q t : ℝ) : flatFactor p q t ≤ 2 := by
  have h1 := expNegInvGlue_le_one (p - t)
  have h2 := expNegInvGlue_le_one (t - q)
  simp only [flatFactor]
  linarith

/-- **`flatFactor p q` vanishes exactly on `[p, q]`.** -/
theorem flatFactor_eq_zero_iff {p q t : ℝ} : flatFactor p q t = 0 ↔ t ∈ Set.Icc p q := by
  have hA := expNegInvGlue.nonneg (p - t)
  have hB := expNegInvGlue.nonneg (t - q)
  constructor
  · intro h
    rw [flatFactor] at h
    have h1 : expNegInvGlue (p - t) = 0 := by linarith
    have h2 : expNegInvGlue (t - q) = 0 := by linarith
    rw [expNegInvGlue.zero_iff_nonpos] at h1 h2
    exact Set.mem_Icc.2 ⟨by linarith, by linarith⟩
  · intro h
    rw [Set.mem_Icc] at h
    rw [flatFactor, expNegInvGlue.zero_of_nonpos (by linarith [h.1]),
      expNegInvGlue.zero_of_nonpos (by linarith [h.2]), add_zero]

theorem flatFactor_pos {p q t : ℝ} (h : t ∉ Set.Icc p q) : 0 < flatFactor p q t :=
  (flatFactor_nonneg p q t).lt_of_ne fun hc => h (flatFactor_eq_zero_iff.1 hc.symm)

theorem contDiff_flatFactor (p q : ℝ) : ContDiff ℝ ∞ (flatFactor p q) := by
  have h1 : ContDiff ℝ ∞ fun t : ℝ => expNegInvGlue (p - t) :=
    (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => expNegInvGlue (t - q) :=
    (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)
  exact h1.add h2

/-- **The two bands of `prop:nonlinear_freezing`**: `U⁻ = (a, b)` with `0 < a < b < 1` and
`U⁺ = (c, d)` with `1 < c < d`.

The strict inequalities `b < 1` and `1 < c` are the paper's `U⁻ ⊂ (0,1)`, `U⁺ ⊂ (1,+∞)` read so
that a continuous multiplier can vanish on the closures and still satisfy `m(1) = 2`; see the
module SCOPE. -/
structure FreezingBands where
  /-- left endpoint of the lower band -/
  a : ℝ
  /-- right endpoint of the lower band -/
  b : ℝ
  /-- left endpoint of the upper band -/
  c : ℝ
  /-- right endpoint of the upper band -/
  d : ℝ
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_one : b < 1
  one_lt_c : 1 < c
  c_lt_d : c < d

namespace FreezingBands

variable (F : FreezingBands)

/-- `U⁻`, the lower band. -/
def lower : Set ℝ := Set.Ioo F.a F.b

/-- `U⁺`, the upper band. -/
def upper : Set ℝ := Set.Ioo F.c F.d

/-- `U⁻ ∪ U⁺`. -/
def bands : Set ℝ := F.lower ∪ F.upper

theorem one_notMem_lower_Icc : (1 : ℝ) ∉ Set.Icc F.a F.b := fun h =>
  absurd (Set.mem_Icc.1 h).2 (not_le.2 F.b_lt_one)

theorem one_notMem_upper_Icc : (1 : ℝ) ∉ Set.Icc F.c F.d := fun h =>
  absurd (Set.mem_Icc.1 h).1 (not_le.2 F.one_lt_c)

/-- The normalisation `m(1) = 2` divides by this. It is positive because neither closed band
contains `1`. -/
noncomputable def scale : ℝ := flatFactor F.a F.b 1 * flatFactor F.c F.d 1

theorem scale_pos : 0 < F.scale :=
  mul_pos (flatFactor_pos F.one_notMem_lower_Icc) (flatFactor_pos F.one_notMem_upper_Icc)

/-- **The multiplier `m` of `prop:nonlinear_freezing`** (`proofs.tex:760`): `C^∞`, nonnegative,
bounded by `8/scale`, equal to `2` at `1`, and vanishing exactly on `[a,b] ∪ [c,d]`. -/
noncomputable def m : ℝ → ℝ := fun t =>
  2 / F.scale * (flatFactor F.a F.b t * flatFactor F.c F.d t)

/-- The explicit bound `‖m‖_∞ ≤ 8/scale`, the constant every growth estimate below inherits. -/
noncomputable def bound : ℝ := 8 / F.scale

theorem bound_pos : 0 < F.bound := div_pos (by norm_num) F.scale_pos

theorem m_nonneg (t : ℝ) : 0 ≤ F.m t :=
  mul_nonneg (div_nonneg (by norm_num) F.scale_pos.le)
    (mul_nonneg (flatFactor_nonneg _ _ _) (flatFactor_nonneg _ _ _))

/-- **`m(1) = 2`.** -/
theorem m_one : F.m 1 = 2 := by
  have hs : F.scale ≠ 0 := F.scale_pos.ne'
  have h : F.m 1 = 2 / F.scale * F.scale := rfl
  rw [h]
  field_simp

/-- **`m ≡ 0` on the bands** (`proofs.tex:760`), on the closed `[a,b] ∪ [c,d]`. -/
theorem m_eq_zero_of_mem_bands {t : ℝ} (h : t ∈ Set.Icc F.a F.b ∪ Set.Icc F.c F.d) : F.m t = 0 := by
  rcases h with h | h
  · simp only [m, flatFactor_eq_zero_iff.2 h, zero_mul, mul_zero]
  · simp only [m, flatFactor_eq_zero_iff.2 h, mul_zero]

/-- **`m > 0` off the bands** (`proofs.tex:760`, repaired: off their *closures*; see SCOPE). -/
theorem m_pos {t : ℝ} (h1 : t ∉ Set.Icc F.a F.b) (h2 : t ∉ Set.Icc F.c F.d) : 0 < F.m t :=
  mul_pos (div_pos (by norm_num) F.scale_pos) (mul_pos (flatFactor_pos h1) (flatFactor_pos h2))

/-- Between the bands — in particular on a punctured neighbourhood of `1` — `m` is positive. This
is the paper's "the integrand is nonnegative and positive near `1`". -/
theorem m_pos_of_mem_Ioo {t : ℝ} (h1 : F.b < t) (h2 : t < F.c) : 0 < F.m t :=
  F.m_pos (fun h => absurd (Set.mem_Icc.1 h).2 (not_le.2 h1))
    (fun h => absurd (Set.mem_Icc.1 h).1 (not_le.2 h2))

/-- **`m` is bounded**, by the explicit `8/scale`. -/
theorem m_le_bound (t : ℝ) : F.m t ≤ F.bound := by
  have h4 : flatFactor F.a F.b t * flatFactor F.c F.d t ≤ 4 := by
    have h := mul_le_mul (flatFactor_le_two F.a F.b t) (flatFactor_le_two F.c F.d t)
      (flatFactor_nonneg F.c F.d t) (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have hc : (0:ℝ) ≤ 2 / F.scale := div_nonneg (by norm_num) F.scale_pos.le
  have := mul_le_mul_of_nonneg_left h4 hc
  simp only [m, bound]
  calc 2 / F.scale * (flatFactor F.a F.b t * flatFactor F.c F.d t) ≤ 2 / F.scale * 4 := this
    _ = 8 / F.scale := by ring

theorem contDiff_m : ContDiff ℝ ∞ F.m :=
  (contDiff_const.mul ((contDiff_flatFactor F.a F.b).mul (contDiff_flatFactor F.c F.d)))

theorem continuous_m : Continuous F.m := F.contDiff_m.continuous

/-- The integrand `t ↦ m(t)(t−1)` of `g`. -/
theorem continuous_integrand : Continuous fun t => F.m t * (t - 1) :=
  F.continuous_m.mul (continuous_id.sub continuous_const)

theorem intervalIntegrable_integrand (p q : ℝ) :
    IntervalIntegrable (fun t => F.m t * (t - 1)) MeasureTheory.volume p q :=
  F.continuous_integrand.intervalIntegrable p q

end FreezingBands

/-! ### The generator `g`, and the four admissibility clauses -/

/-- `∫_p^q (t − 1) dt = ((q−1)² − (p−1)²)/2`, the only primitive computed below. -/
theorem integral_sub_one (p q : ℝ) :
    (∫ t in p..q, (t - 1)) = ((q - 1) ^ 2 - (p - 1) ^ 2) / 2 := by
  have h : (∫ t in p..q, (t - 1)) = (∫ t in p..q, t) - ∫ _ in p..q, (1:ℝ) :=
    intervalIntegral.integral_sub (continuous_id.intervalIntegrable p q)
      (intervalIntegrable_const)
  rw [h, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

namespace FreezingBands

variable (F : FreezingBands)

/-- **The generator `g` of `prop:nonlinear_freezing`** (`proofs.tex:760`):
`g(x) := ∫₁ˣ m(t)(t−1) dt`. -/
noncomputable def g : ℝ → ℝ := fun x => ∫ t in (1:ℝ)..x, F.m t * (t - 1)

/-- **`g(1) = 0`**, the first admissibility clause (`proofs.tex:760`). -/
theorem g_one : F.g 1 = 0 := intervalIntegral.integral_same

/-- **`g'(x) = m(x)(x−1)`** (`proofs.tex:770`), by the fundamental theorem of calculus, the
integrand being continuous. -/
theorem deriv_g : deriv F.g = fun x => F.m x * (x - 1) := by
  funext x
  exact Continuous.deriv_integral _ F.continuous_integrand 1 x

theorem differentiable_g : Differentiable ℝ F.g := fun x =>
  (F.continuous_integrand.integral_hasStrictDerivAt 1 x).hasDerivAt.differentiableAt

/-- **`g` is `C^∞`** (`proofs.tex:760`, `:770`): its derivative is `m ·(x−1)`, and `m` is `C^∞`. -/
theorem contDiff_g : ContDiff ℝ ∞ F.g := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨F.differentiable_g, ?_⟩
  rw [F.deriv_g]
  exact F.contDiff_m.mul (contDiff_id.sub contDiff_const)

theorem continuous_g : Continuous F.g := F.differentiable_g.continuous

/-- **`g' ≡ 0` on `U⁻ ∪ U⁺`** (`proofs.tex:760`, `:770`) — the property the whole proposition turns
on, here on the closed bands. -/
theorem deriv_g_eq_zero_of_mem_bands {x : ℝ} (h : x ∈ Set.Icc F.a F.b ∪ Set.Icc F.c F.d) :
    deriv F.g x = 0 := by
  simp only [F.deriv_g, F.m_eq_zero_of_mem_bands h, zero_mul]

theorem deriv_g_eq_zero_of_mem_bands' {x : ℝ} (h : x ∈ F.bands) : deriv F.g x = 0 := by
  refine F.deriv_g_eq_zero_of_mem_bands ?_
  rcases h with h | h
  · exact Or.inl (Set.mem_Icc.2 ⟨(Set.mem_Ioo.1 h).1.le, (Set.mem_Ioo.1 h).2.le⟩)
  · exact Or.inr (Set.mem_Icc.2 ⟨(Set.mem_Ioo.1 h).1.le, (Set.mem_Ioo.1 h).2.le⟩)

/-- **`g > 0` away from `1`**, the second admissibility clause (`proofs.tex:760`, proof
`proofs.tex:770`): the integrand is nonnegative on `[1, x]`, negative-signed on `[x, 1]`, and
strictly positive somewhere on either, because `m > 0` between the bands. -/
theorem g_pos {x : ℝ} (hx : x ≠ 1) : 0 < F.g x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hmax : max x F.b < 1 := max_lt h F.b_lt_one
    set t0 : ℝ := (max x F.b + 1) / 2 with ht0
    have hlow : max x F.b < t0 := by rw [ht0]; linarith
    have hhigh : t0 < 1 := by rw [ht0]; linarith
    have hmem : t0 ∈ Set.Icc x 1 :=
      Set.mem_Icc.2 ⟨le_of_lt (lt_of_le_of_lt (le_max_left x F.b) hlow), hhigh.le⟩
    have hmpos : 0 < F.m t0 :=
      F.m_pos_of_mem_Ioo (lt_of_le_of_lt (le_max_right x F.b) hlow) (hhigh.trans F.one_lt_c)
    have key : (0:ℝ) < ∫ t in x..(1:ℝ), -(F.m t * (t - 1)) := by
      refine intervalIntegral.integral_pos h F.continuous_integrand.neg.continuousOn ?_
        ⟨t0, hmem, ?_⟩
      · intro t ht
        have h1 : t ≤ 1 := (Set.mem_Ioc.1 ht).2
        nlinarith [F.m_nonneg t]
      · nlinarith
    rw [intervalIntegral.integral_neg] at key
    have hsym : F.g x = -∫ t in x..(1:ℝ), F.m t * (t - 1) := intervalIntegral.integral_symm x 1
    rw [hsym]
    linarith
  · have hmin : 1 < min x F.c := lt_min h F.one_lt_c
    set t0 : ℝ := (1 + min x F.c) / 2 with ht0
    have hlow : 1 < t0 := by rw [ht0]; linarith
    have hhigh : t0 < min x F.c := by rw [ht0]; linarith
    have hmem : t0 ∈ Set.Icc 1 x :=
      Set.mem_Icc.2 ⟨hlow.le, le_of_lt (lt_of_lt_of_le hhigh (min_le_left x F.c))⟩
    have hmpos : 0 < F.m t0 :=
      F.m_pos_of_mem_Ioo (F.b_lt_one.trans hlow) (lt_of_lt_of_le hhigh (min_le_right x F.c))
    have key : (0:ℝ) < ∫ t in (1:ℝ)..x, F.m t * (t - 1) := by
      refine intervalIntegral.integral_pos h F.continuous_integrand.continuousOn ?_ ⟨t0, hmem, ?_⟩
      · intro t ht
        have h1 : 1 ≤ t := (Set.mem_Ioc.1 ht).1.le
        nlinarith [F.m_nonneg t]
      · nlinarith
    exact key

theorem g_nonneg (x : ℝ) : 0 ≤ F.g x := by
  rcases eq_or_ne x 1 with h | h
  · rw [h, F.g_one]
  · exact (F.g_pos h).le

/-- **`g''(1) = 2`**, the third admissibility clause (`proofs.tex:760`, proof `proofs.tex:770`:
"`g''(1) = m(1) = 2`"). -/
theorem deriv_deriv_g_one : deriv (deriv F.g) 1 = 2 := by
  rw [F.deriv_g]
  have hm : HasDerivAt F.m (deriv F.m 1) 1 :=
    ((F.contDiff_m.differentiable (by simp)) 1).hasDerivAt
  have h : HasDerivAt (fun y : ℝ => F.m y * (y - 1))
      (deriv F.m 1 * (1 - 1) + F.m 1 * 1) 1 := hm.mul ((hasDerivAt_id (1:ℝ)).sub_const 1)
  rw [h.deriv, F.m_one]
  ring

/-- **`|g(x)| ≤ (‖m‖_∞/2)(x−1)²`**, the quantitative form of the fourth admissibility clause
(`proofs.tex:770`), with the explicit `‖m‖_∞ ≤ 8/scale`. -/
theorem abs_g_le (x : ℝ) : |F.g x| ≤ F.bound * (x - 1) ^ 2 / 2 := by
  rw [abs_of_nonneg (F.g_nonneg x)]
  rcases le_total 1 x with h | h
  · have hmono : (∫ t in (1:ℝ)..x, F.m t * (t - 1)) ≤ ∫ t in (1:ℝ)..x, F.bound * (t - 1) := by
      refine intervalIntegral.integral_mono_on h (F.intervalIntegrable_integrand 1 x)
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable 1 x) ?_
      intro t ht
      have h1 : 1 ≤ t := (Set.mem_Icc.1 ht).1
      nlinarith [F.m_le_bound t]
    have hval : (∫ t in (1:ℝ)..x, F.bound * (t - 1)) = F.bound * (x - 1) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_sub_one]
      ring
    calc F.g x = ∫ t in (1:ℝ)..x, F.m t * (t - 1) := rfl
      _ ≤ ∫ t in (1:ℝ)..x, F.bound * (t - 1) := hmono
      _ = F.bound * (x - 1) ^ 2 / 2 := hval
  · have hmono : (∫ t in x..(1:ℝ), -(F.m t * (t - 1)))
        ≤ ∫ t in x..(1:ℝ), -(F.bound * (t - 1)) := by
      refine intervalIntegral.integral_mono_on h (F.intervalIntegrable_integrand x 1).neg
        ((continuous_const.mul (continuous_id.sub continuous_const)).neg.intervalIntegrable x 1) ?_
      intro t ht
      have h1 : t ≤ 1 := (Set.mem_Icc.1 ht).2
      nlinarith [F.m_le_bound t]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, integral_sub_one] at hmono
    have hsym : F.g x = -∫ t in x..(1:ℝ), F.m t * (t - 1) := intervalIntegral.integral_symm x 1
    rw [hsym]
    linarith

/-- **`|g(x)| ≤ C(1 + |x|²)`**, the fourth admissibility clause as the paper states it
(`proofs.tex:760`), with `C = 8/scale` explicit. -/
theorem abs_g_le_growth (x : ℝ) : |F.g x| ≤ F.bound * (1 + |x| ^ 2) := by
  have h := F.abs_g_le x
  have hb := F.bound_pos
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [sq_nonneg (x + 1)]

/-- **`g` is constant on each band** (`proofs.tex:776`: "`g'` vanishing identically on each band
makes `g` constant on each of the two intervals"), proved from the vanishing of the integrand
rather than from a mean-value argument. -/
theorem g_eq_of_uIcc_flat {x y : ℝ} (hband : ∀ t ∈ Set.uIcc x y, F.m t = 0) :
    F.g x = F.g y := by
  have hxy : (∫ t in x..y, F.m t * (t - 1)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) fun t ht => by
      rw [hband t ht, zero_mul]]
    simp
  have hadd : (∫ t in (1:ℝ)..x, F.m t * (t - 1)) + ∫ t in x..y, F.m t * (t - 1)
      = ∫ t in (1:ℝ)..y, F.m t * (t - 1) :=
    intervalIntegral.integral_add_adjacent_intervals (F.intervalIntegrable_integrand 1 x)
      (F.intervalIntegrable_integrand x y)
  have hgx : F.g x = ∫ t in (1:ℝ)..x, F.m t * (t - 1) := rfl
  have hgy : F.g y = ∫ t in (1:ℝ)..y, F.m t * (t - 1) := rfl
  rw [hgx, hgy, ← hadd, hxy, add_zero]

theorem g_const_on_lower {x y : ℝ} (hx : x ∈ Set.Icc F.a F.b) (hy : y ∈ Set.Icc F.a F.b) :
    F.g x = F.g y :=
  F.g_eq_of_uIcc_flat fun _ ht =>
    F.m_eq_zero_of_mem_bands (Or.inl (Set.uIcc_subset_Icc hx hy ht))

theorem g_const_on_upper {x y : ℝ} (hx : x ∈ Set.Icc F.c F.d) (hy : y ∈ Set.Icc F.c F.d) :
    F.g x = F.g y :=
  F.g_eq_of_uIcc_flat fun _ ht =>
    F.m_eq_zero_of_mem_bands (Or.inr (Set.uIcc_subset_Icc hx hy ht))

/-- **`1 ∉ U⁻ ∪ U⁺`** — the bands do not contain `1`, which is what makes the frozen loss
*positive* and not merely constant. -/
theorem one_notMem_bands : (1:ℝ) ∉ F.bands := by
  rintro (h | h)
  · exact absurd (Set.mem_Ioo.1 h).2 (not_lt.2 F.b_lt_one.le)
  · exact absurd (Set.mem_Ioo.1 h).1 (not_lt.2 F.one_lt_c.le)

theorem isOpen_lower : IsOpen F.lower := isOpen_Ioo

theorem isOpen_upper : IsOpen F.upper := isOpen_Ioo

theorem isOpen_bands : IsOpen F.bands := F.isOpen_lower.union F.isOpen_upper

theorem mem_Icc_of_mem_lower {x : ℝ} (h : x ∈ F.lower) : x ∈ Set.Icc F.a F.b :=
  Set.mem_Icc.2 ⟨(Set.mem_Ioo.1 h).1.le, (Set.mem_Ioo.1 h).2.le⟩

theorem mem_Icc_of_mem_upper {x : ℝ} (h : x ∈ F.upper) : x ∈ Set.Icc F.c F.d :=
  Set.mem_Icc.2 ⟨(Set.mem_Ioo.1 h).1.le, (Set.mem_Ioo.1 h).2.le⟩

/-- **`prop:nonlinear_freezing`, admissibility** (`proofs.tex:760`, proof `proofs.tex:770`): `g` is
a `C^∞` admissible generator — `g(1) = 0`, `g > 0` elsewhere, `g''(1) = 2`,
`|g(x)| ≤ C(1 + |x|²)` — with `g' ≡ 0` on `U⁻ ∪ U⁺`.

The constant is `C = 8/scale`, explicit as the house rule requires. -/
theorem admissible :
    ContDiff ℝ ∞ F.g ∧ F.g 1 = 0 ∧ (∀ x ≠ (1:ℝ), 0 < F.g x) ∧ deriv (deriv F.g) 1 = 2 ∧
      (∀ x, |F.g x| ≤ F.bound * (1 + |x| ^ 2)) ∧ (∀ x ∈ F.bands, deriv F.g x = 0) :=
  ⟨F.contDiff_g, F.g_one, fun _ hx => F.g_pos hx, F.deriv_deriv_g_one, F.abs_g_le_growth,
    fun _ hx => F.deriv_g_eq_zero_of_mem_bands' hx⟩

end FreezingBands

/-! ### Item *(1)*, second half: the frozen set is open, and the loss is locally constant there

The paper: "on a finite state space, `μ ↦ r(μ)` is continuous on `{μ > 0}`, so band-valued ratios
persist under small perturbations and the set is open; `g'` vanishing identically on each band
makes `g` constant on each of the two intervals, so every `g(r(x))`, hence `𝓛_{g,ν}`, is locally
constant — and positive, since the bands do not contain `1` and `g > 0` on them"
(`proofs.tex:776`). `V → ℝ` carries its product topology, which on a `Fintype` is the topology of
`𝓜²(λ)`. -/

section Frozen

variable {V : Type*} [Fintype V]

/-- **`μ ↦ r(μ)` is continuous on `{μ > 0}`** (`proofs.tex:776`): the ratio is a quotient of a
finite sum by `λ(y)u(y)`, and the denominator does not vanish. -/
theorem continuousAt_ratio {K : V → V → ℝ} {lam u0 : V → ℝ} (y : V) (h : lam y * u0 y ≠ 0) :
    ContinuousAt (fun u => ratio K lam u y) u0 := by
  have hnum : Continuous fun u : V → ℝ => pushMass K lam u y := by
    simp only [pushMass]
    exact continuous_finsetSum _ fun x _ => by fun_prop
  have hden : Continuous fun u : V → ℝ => lam y * u y := (continuous_apply y).const_mul _
  simp only [ratio]
  exact hnum.continuousAt.div hden.continuousAt h

/-- **The set of band-valued flows**: the `μ` of `prop:nonlinear_freezing`*(1)*, as densities
`u = dμ/dλ`. -/
def frozen (K : V → V → ℝ) (lam : V → ℝ) (U : Set ℝ) : Set (V → ℝ) :=
  {u | (∀ x, 0 < u x) ∧ ∀ x, ratio K lam u x ∈ U}

/-- **The set of such `μ` is open** (`proofs.tex:762`, `:776`). -/
theorem isOpen_frozen {K : V → V → ℝ} {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) {U : Set ℝ}
    (hU : IsOpen U) : IsOpen (frozen K lam U) := by
  rw [isOpen_iff_mem_nhds]
  rintro u0 ⟨hpos, hband⟩
  have hset : {u : V → ℝ | ∀ x, 0 < u x} = ⋂ x, {u : V → ℝ | 0 < u x} := by
    ext u; simp
  have hposn : ∀ᶠ u in nhds u0, ∀ x, 0 < u x := by
    refine IsOpen.mem_nhds ?_ hpos
    rw [hset]
    exact isOpen_iInter_of_finite fun x => isOpen_lt continuous_const (continuous_apply x)
  have hbandn : ∀ᶠ u in nhds u0, ∀ x, ratio K lam u x ∈ U :=
    Filter.eventually_all.2 fun x =>
      (continuousAt_ratio x (mul_pos (hlam x) (hpos x)).ne').preimage_mem_nhds
        (hU.mem_nhds (hband x))
  exact hposn.and hbandn

/-- **The loss `𝓛_{g,ν}(μ) = ∫ g(r) dν`** on a finite state space, at a **fixed** training measure
`ν` — the measure is held fixed while `μ` varies, which is what "locally constant" is about. -/
noncomputable def loss (K : V → V → ℝ) (lam nu u : V → ℝ) (gg : ℝ → ℝ) : ℝ :=
  ∑ x, nu x * gg (ratio K lam u x)

/-- **`𝓛_{g,ν}` is locally constant on the frozen set** (`proofs.tex:762`, `:776`): near a
band-valued `u`, each ratio stays inside *its own* band, on which `g` is constant. -/
theorem eventually_loss_eq (F : FreezingBands) {K : V → V → ℝ} {lam nu : V → ℝ}
    (hlam : ∀ x, 0 < lam x) {u0 : V → ℝ} (hu0 : u0 ∈ frozen K lam F.bands) :
    ∀ᶠ u in nhds u0, loss K lam nu u F.g = loss K lam nu u0 F.g := by
  obtain ⟨hpos, hband⟩ := hu0
  have key : ∀ x : V, ∀ᶠ u in nhds u0, F.g (ratio K lam u x) = F.g (ratio K lam u0 x) := by
    intro x
    have hcont : ContinuousAt (fun u => ratio K lam u x) u0 :=
      continuousAt_ratio x (mul_pos (hlam x) (hpos x)).ne'
    rcases hband x with h | h
    · filter_upwards [hcont.preimage_mem_nhds (F.isOpen_lower.mem_nhds h)] with u hu
      exact F.g_const_on_lower (F.mem_Icc_of_mem_lower hu) (F.mem_Icc_of_mem_lower h)
    · filter_upwards [hcont.preimage_mem_nhds (F.isOpen_upper.mem_nhds h)] with u hu
      exact F.g_const_on_upper (F.mem_Icc_of_mem_upper hu) (F.mem_Icc_of_mem_upper h)
  filter_upwards [Filter.eventually_all.2 key] with u hu
  exact Finset.sum_congr rfl fun x _ => by rw [hu x]

/-- **`𝓛_{g,ν}` is positive on the frozen set** (`proofs.tex:762`, `:776`: "positive, since the
bands do not contain `1` and `g > 0` on them"). -/
theorem loss_pos (F : FreezingBands) [Nonempty V] {K : V → V → ℝ} {lam nu u : V → ℝ}
    (hnu : ∀ x, 0 < nu x) (hband : ∀ x, ratio K lam u x ∈ F.bands) :
    0 < loss K lam nu u F.g := by
  refine Finset.sum_pos (fun x _ => mul_pos (hnu x) (F.g_pos ?_)) Finset.univ_nonempty
  intro hc
  exact F.one_notMem_bands (hc ▸ hband x)

/-- **`prop:nonlinear_freezing`*(1)* in full** (`proofs.tex:762`), on a finite state space: a
band-valued flow is a critical point of `𝓛_{g,ν}` for every training measure; the set of such
flows is open; and on it the loss is locally constant and positive.

*Critical* is `D = 0`, on the reading disclosed in the module SCOPE. -/
theorem freezing_item_one (F : FreezingBands) [Nonempty V] {K : V → V → ℝ} {lam nu u : V → ℝ}
    (hlam : ∀ x, 0 < lam x) (hnu : ∀ x, 0 < nu x) (hu : u ∈ frozen K lam F.bands) :
    (∀ w : V → ℝ, ∀ x, lossGradDensity K lam u w (deriv F.g) x = 0)
      ∧ IsOpen (frozen K lam F.bands)
      ∧ (∀ᶠ u' in nhds u, loss K lam nu u' F.g = loss K lam nu u F.g)
      ∧ 0 < loss K lam nu u F.g :=
  ⟨fun w => freezing_critical hu.2 (fun _ hz => F.deriv_g_eq_zero_of_mem_bands' hz) (w := w),
    isOpen_frozen hlam F.isOpen_bands, eventually_loss_eq F hlam hu, loss_pos F hnu hu.2⟩

end Frozen

/-! ### Item *(2)*: the two-state chain

`T(i→j) = 1/2`, `λ = (1/2,1/2)`, `μ* = (1,1/2)` — i.e. `u = dμ*/dλ = (2,1)` — and the bands
`(5/8,7/8)`, `(11/8,13/8)`. -/

section TwoState

/-- The bands of `prop:nonlinear_freezing`*(2)*: `U⁻ = (5/8, 7/8) ∋ 3/4` and
`U⁺ = (11/8, 13/8) ∋ 3/2`. -/
noncomputable def twoStateBands : FreezingBands where
  a := 5 / 8
  b := 7 / 8
  c := 11 / 8
  d := 13 / 8
  a_pos := by norm_num
  a_lt_b := by norm_num
  b_lt_one := by norm_num
  one_lt_c := by norm_num
  c_lt_d := by norm_num

/-- The two-state chain `T(i→j) = 1/2` (`proofs.tex:763`). -/
noncomputable def twoStateK : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 2

/-- Its invariant measure `λ = (1/2, 1/2)` (`proofs.tex:763`). -/
noncomputable def twoStateLam : Fin 2 → ℝ := fun _ => 1 / 2

/-- The flow `μ* = (1, 1/2)` of `proofs.tex:778`, as the density `u = dμ*/dλ = (2, 1)`. -/
def twoStateU : Fin 2 → ℝ := ![2, 1]

theorem twoStateLam_pos : ∀ x, 0 < twoStateLam x := fun _ => by norm_num [twoStateLam]

theorem twoStateU_pos : ∀ x, 0 < twoStateU x := by
  intro x
  fin_cases x <;> norm_num [twoStateU]

theorem twoStateK_invariant : Invariant twoStateK twoStateLam := by
  intro y
  simp [twoStateK, twoStateLam]

/-- **`P† = Π` on the two-state chain**: the function action is the `λ`-average
(`proofs.tex:778`: "the density action is `Ph = (∫h dλ)𝟏 = Πh`"), from which `β̂ₙ = 0` for
`n ≥ 1`. The coefficients themselves are not stated here; see the module SCOPE. -/
theorem twoState_funAct_eq_mean (phi : Fin 2 → ℝ) (x : Fin 2) :
    funAct twoStateK phi x = ∑ y, twoStateLam y * phi y := by
  simp [funAct, twoStateK, twoStateLam, Fin.sum_univ_two]

/-- **`P = Π` on the two-state chain**, on densities: `d(μT)/dλ = ∫ u dλ`, constant. -/
theorem twoState_densityAction_eq_mean (u : Fin 2 → ℝ) (y : Fin 2) :
    pushMass twoStateK twoStateLam u y / twoStateLam y = ∑ x, twoStateLam x * u x := by
  simp [pushMass, twoStateK, twoStateLam, Fin.sum_univ_two]
  ring

/-- **`μ*T = (3/4, 3/4)`, so `r(0) = 3/4 ∈ U⁻`** (`proofs.tex:778`). -/
theorem twoState_ratio_zero : ratio twoStateK twoStateLam twoStateU 0 = 3 / 4 := by
  norm_num [ratio, pushMass, twoStateK, twoStateLam, twoStateU, Fin.sum_univ_two]

/-- **`r(1) = 3/2 ∈ U⁺`** (`proofs.tex:778`). -/
theorem twoState_ratio_one : ratio twoStateK twoStateLam twoStateU 1 = 3 / 2 := by
  norm_num [ratio, pushMass, twoStateK, twoStateLam, twoStateU, Fin.sum_univ_two]

/-- **`μ*` is band-valued** (`proofs.tex:778`: "`r = (3/4, 3/2) ∈ U⁻ × U⁺`"). -/
theorem twoState_mem_frozen :
    twoStateU ∈ frozen twoStateK twoStateLam twoStateBands.bands := by
  refine ⟨twoStateU_pos, ?_⟩
  rw [Fin.forall_fin_two]
  refine ⟨Or.inl ?_, Or.inr ?_⟩
  · rw [twoState_ratio_zero]
    exact Set.mem_Ioo.2 (by norm_num [twoStateBands])
  · rw [twoState_ratio_one]
    exact Set.mem_Ioo.2 (by norm_num [twoStateBands])

/-- **Every ratio in `U⁻ ∪ U⁺` deviates from `1` by at least `1/8`** (`proofs.tex:778`). -/
theorem twoState_bands_deviate {z : ℝ} (h : z ∈ twoStateBands.bands) : 1 / 8 ≤ |z - 1| := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 h
    simp only [twoStateBands] at h1 h2
    rw [abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 h
    simp only [twoStateBands] at h1 h2
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **`prop:nonlinear_freezing`*(2)*** (`proofs.tex:763`, proof `proofs.tex:778`): on the two-state
chain the freezing set is a **nonempty open** set of flows, every ratio on it deviates from `1` by
at least `1/8`, and there the gradient vanishes and every gradient-descent step is fixed, for every
training measure and every step size. -/
theorem twoState_freezing :
    IsOpen (frozen twoStateK twoStateLam twoStateBands.bands)
      ∧ twoStateU ∈ frozen twoStateK twoStateLam twoStateBands.bands
      ∧ (∀ u ∈ frozen twoStateK twoStateLam twoStateBands.bands, ∀ x, 1 / 8 ≤
          |ratio twoStateK twoStateLam u x - 1|)
      ∧ (∀ u ∈ frozen twoStateK twoStateLam twoStateBands.bands, ∀ w : Fin 2 → ℝ, ∀ x,
          lossGradDensity twoStateK twoStateLam u w (deriv twoStateBands.g) x = 0)
      ∧ (∀ u ∈ frozen twoStateK twoStateLam twoStateBands.bands, ∀ w : Fin 2 → ℝ, ∀ eta : ℝ,
          (fun x => u x - eta * lossGradDensity twoStateK twoStateLam u w
            (deriv twoStateBands.g) x) = u) := by
  refine ⟨isOpen_frozen twoStateLam_pos twoStateBands.isOpen_bands, twoState_mem_frozen,
    fun u hu x => twoState_bands_deviate (hu.2 x), fun u hu w => ?_, fun u hu w eta => ?_⟩
  · exact freezing_critical hu.2 (fun _ hz => twoStateBands.deriv_g_eq_zero_of_mem_bands' hz)
  · exact freezing_descent_stationary hu.2
      (fun _ hz => twoStateBands.deriv_g_eq_zero_of_mem_bands' hz) eta

end TwoState

end GFNBounds.Balance
