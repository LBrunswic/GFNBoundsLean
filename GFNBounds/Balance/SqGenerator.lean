import GFNBounds.Balance.Lojasiewicz

/-!
# The generator `(x − 1)²` is coercive off balance, and item *(3)*'s display holds for it

**`prop:no_distant_equilibrium`** **item *(3)***, the display only, for `g = (x − 1)²` —
statement `proofs.tex:808–819` (item *(3)* at `:813–817`), proof `proofs.tex:821–835` (the
`(x − 1)²` sentence and the display at `:830–833`). The `(log x)²` case of the same display is
closed in `GFNBounds/Balance/Lojasiewicz.lean`; item *(3)* was extended to `(x − 1)²` on
2026-09-13, and this file certifies the extension's static half. (The bold-backtick form of the
label is what `scripts/trace_check.py` and the paper-side ledger machine-read.)

> (`prop:no_distant_equilibrium`*(3)*, `proofs.tex:813`) *Global convergence, quantitatively.*
> On a finite state space, for `g = (log x)²` or `g = (x−1)²` and `w ≥ w_min > 0`:
> `|g'(x)(1−x)| ≥ δ²/2` whenever `|x−1| ≥ δ ∈ (0, ½]`, whence
> `‖∇^λ 𝓛_{g,ν}(μ)‖_{𝓜²(λ)} ≥ (w_min λ_min^{1/2}/‖u₀‖_{L²(λ)}) (δ²/2) λ(|r−1| ≥ δ)`,
> and the gradient flow from any `μ₀ ∼ λ` converges to the balanced flow of its sphere, entering
> the neighbourhood of Theorem `theo:local_convergence` in explicit time.

> (proof of *(3)*, `proofs.tex:830`) For `g = (x−1)²`, `|g'(x)(1−x)| = 2(x−1)² ≥ 2δ² ≥ δ²/2`
> whenever `|x−1| ≥ δ`. On the sphere, `u(x)²λ(x) ≤ ‖u₀‖²` gives `u ≤ ‖u₀‖λ_min^{−1/2}`
> pointwise, so `dν/dμ = w/u ≥ w_min λ_min^{1/2}/‖u₀‖`, and since `λ` is a probability measure,
> `‖D‖_{L²(λ)} ≥ |∫ D dλ| ≥ (w_min λ_min^{1/2}/‖u₀‖)(δ²/2) λ(|r−1| ≥ δ)`.

## What is proved

| | |
|---|---|
| `sqDeriv_mul_one_sub_le_sharp` | `2(x−1)(1−x) ≤ −2δ²` whenever `0 ≤ δ ≤ \|x−1\|`: the paper's `2(x−1)² ≥ 2δ²`, signed |
| `sqDeriv_mul_one_sub_le` | `2(x−1)(1−x) ≤ −δ²/2` under the same two hypotheses: the paper's `2δ² ≥ δ²/2` |
| `le_abs_sqDeriv_mul_one_sub` | `\|g'(x)(1−x)\| ≥ δ²/2`, the proposition's own wording |
| `sqDeriv_mul_one_sub_nonpos` | `2(x−1)(1−x) ≤ 0` for **every** real `x` |
| `no_distant_equilibrium_three_far_of` | the display over any far set, with `dν/dμ ≥ c₀` abstract, for **any** `g'` satisfying the two pointwise facts it consumes |
| `no_distant_equilibrium_three_sq` | the display with the paper's constant on `farSet`, at `g' = fun x => 2(x−1)` |

`no_distant_equilibrium_three_far_of` is `Lojasiewicz.no_distant_equilibrium_three_far` with its
two uses of `(log x)²` — `logSqDeriv_mul_one_sub_nonpos` and `logSqDeriv_mul_one_sub_le` — lifted
into hypotheses `hnp` and `hfar`. It is re-proved here rather than by editing `Lojasiewicz.lean`,
which is shared; the master may later route the `(log x)²` form through it.

## SCOPE (disclosed)

* **The convergence clause of item *(3)* for `g = (x − 1)²` is not here.** "The gradient flow
  from any `μ₀ ∼ λ` converges to the balanced flow of its sphere, entering the neighbourhood of
  Theorem `theo:local_convergence` in explicit time" runs, for `(log x)²`, through
  `GFNBounds/Balance/BoundaryBlowup.lean`, whose ratio cap and positivity floor are written for
  `logSq`/`logSqDeriv`; the `(x − 1)²` case needs a generator-parametric rewrite of that file and
  is Wave 2's. Only the coercivity estimate that clause consumes, and the display, are certified.
* **The generator is carried only through its derivative.** `g'(x) = 2(x − 1)` is written as the
  lambda `fun x => 2 * (x - 1)`, the same one `MassIdentity.strictlyUnimodal_sqDeriv` uses; `g`
  itself never appears and is never differentiated. That `2(x − 1)` is `deriv (fun x => (x−1)²)`
  is elementary and is neither stated nor used.
* **Inherited from `Lojasiewicz.lean`, unchanged:** `D = lossGradDensity` is a definition (its
  identification with the gradient is `GFNBounds/Balance/FirstVariation.lean`'s, on a finite
  state space); ergodicity is weakened to `λ`-invariance; `λ_min` is a parameter with its
  defining inequality; `dν/dμ` is the definition `w/u`; the sphere `‖u‖ = ‖u₀‖` is the hypothesis
  `hsph`; `λ(|r − 1| ≥ δ)` is the `Finset` sum over `farSet`.
* **`δ ≤ ½` is dropped and `0 < δ` weakened to `0 ≤ δ`, in the safe direction.** The paper's
  range `δ ∈ (0, ½]` is spent only by the `(log x)²` branch (`2δ²/(1+δ)² ≥ δ²/2`); the paper's
  own `(x − 1)²` sentence carries no restriction on `δ`, and nothing here uses one. `0 ≤ δ` is
  necessary: at `δ < 0` the pointwise bound fails at `x = 1`. The paper's form is the
  specialisation `0 < δ ≤ ½`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| finite state space | ✓ `[Fintype V]`, the paper's own hypothesis in item *(3)* |
| `g = (x − 1)²` | ✓ through `g' = fun x => 2 * (x - 1)` only; see SCOPE |
| `g` admissible, differentiable | ✗ not carried; only `g'` appears |
| `(𝒮̂, λ, T)` ergodic | ⚠ **weakened to `λ`-invariance** (`Invariant K lam`), as in `Lojasiewicz` |
| `λ` a probability | ✓ `htot : ∑ x, lam x = 1`, spent in `‖D‖ ≥ \|∫ D dλ\|` |
| `λ_min > 0` | ⚠ a parameter `lamMin` with `∀ x, lamMin ≤ lam x`, `0 < lamMin`, as in `Lojasiewicz` |
| `T` a Markov kernel | ⚠ only `K ≥ 0`, to derive `r > 0` through `ratio_pos` |
| `μ ∼ λ`, `u = dμ/dλ` | ✓ `hu : ∀ x, 0 < u x` |
| `ν = wλ`, `w ≥ w_min > 0` | ✓ `hw`, `hwmin : 0 < wmin` |
| the invariant sphere `‖u‖ = ‖u₀‖` | ⚠ **hypothesis** `hsph`, as in `Lojasiewicz` |
| `‖u₀‖ > 0` | ✓ `hu0` |
| `δ ∈ (0, ½]` | ⚠ **weakened** to `0 ≤ δ`; see SCOPE |
| (generic form) `dν/dμ ≥ c₀ > 0` | ⚠ **weakened** to `0 ≤ c₀` in `no_distant_equilibrium_three_far_of` |
| `D = P†φ − rφ` | ⚠ **taken as a definition** in `MassIdentity`; inherited |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

/-! ### The pointwise coercivity of `(x − 1)²` -/

/-- **`g'(x)(1 − x) ≤ −2δ²` whenever `0 ≤ δ ≤ |x − 1|`**, for `g = (x − 1)²` — the sharp form,
the paper's `2(x−1)² ≥ 2δ²` (`proofs.tex:830`). Neither `x > 0` nor `δ ≤ ½` is needed. -/
theorem sqDeriv_mul_one_sub_le_sharp {x δ : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ |x - 1|) :
    2 * (x - 1) * (1 - x) ≤ -(2 * δ ^ 2) := by
  have hsq : δ ^ 2 ≤ |x - 1| ^ 2 := pow_le_pow_left₀ hδ h 2
  rw [sq_abs] at hsq
  nlinarith [hsq]

/-- **`g'(x)(1 − x) ≤ −δ²/2` whenever `0 ≤ δ ≤ |x − 1|`**, for `g = (x − 1)²`
(`proofs.tex:813`, proof `proofs.tex:830`: `2δ² ≥ δ²/2`). -/
theorem sqDeriv_mul_one_sub_le {x δ : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ |x - 1|) :
    2 * (x - 1) * (1 - x) ≤ -(δ ^ 2 / 2) := by
  have hs := sqDeriv_mul_one_sub_le_sharp hδ h
  nlinarith [sq_nonneg δ]

/-- **`|g'(x)(1 − x)| ≥ δ²/2` whenever `0 ≤ δ ≤ |x − 1|`**, for `g = (x − 1)²`
(`proofs.tex:813`) — the proposition's own wording, from the signed form. -/
theorem le_abs_sqDeriv_mul_one_sub {x δ : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ |x - 1|) :
    δ ^ 2 / 2 ≤ |2 * (x - 1) * (1 - x)| := by
  have hle := sqDeriv_mul_one_sub_le hδ h
  have : δ ^ 2 / 2 ≤ -(2 * (x - 1) * (1 - x)) := by linarith
  exact le_trans this (neg_le_abs _)

/-- **`g'(x)(1 − x) ≤ 0` for every `x`**, for `g = (x − 1)²` — strict unimodality, unweighted
(`proofs.tex:826`). -/
theorem sqDeriv_mul_one_sub_nonpos (x : ℝ) : 2 * (x - 1) * (1 - x) ≤ 0 := by
  nlinarith [sq_nonneg (x - 1)]

/-! ### Item *(3)*'s display, generator-parametric -/

variable {V : Type*} [Fintype V]

/-- **`prop:no_distant_equilibrium`*(3)*, the display, for any `g'` with the two pointwise facts
it consumes** (statement `proofs.tex:813–817`, proof `proofs.tex:830–833`): over any set `S` of
far ratios and with `dν/dμ ≥ c₀`,
`c₀ (δ²/2) λ(S) ≤ ‖D‖_{L²(λ)}` whenever `g'(x)(1 − x) ≤ 0` on `x > 0` (`hnp`) and
`g'(x)(1 − x) ≤ −δ²/2` on `x > 0` with `|x − 1| ≥ δ` (`hfar`).

This is `Lojasiewicz.no_distant_equilibrium_three_far` with `logSqDeriv` abstracted to `gd`; the
two lemmas that proof used about `logSqDeriv` are exactly `hnp` and `hfar`. `D` is
`lossGradDensity`, a **definition**; see the module SCOPE. -/
theorem no_distant_equilibrium_three_far_of
    {K : V → V → ℝ} {lam u wnu : V → ℝ} {δ c₀ : ℝ} {gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hc₀ : 0 ≤ c₀) (hwnu : ∀ x, c₀ ≤ wnu x)
    (hnp : ∀ x : ℝ, 0 < x → gd x * (1 - x) ≤ 0)
    (hfar : ∀ x : ℝ, 0 < x → δ ≤ |x - 1| → gd x * (1 - x) ≤ -(δ ^ 2 / 2))
    (S : Finset V) (hS : ∀ x ∈ S, δ ≤ |ratio K lam u x - 1|) :
    c₀ * (δ ^ 2 / 2) * (∑ x ∈ S, lam x)
      ≤ Graph.nrmL2 lam (lossGradDensity K lam u wnu gd) := by
  set r := ratio K lam u with hrdef
  have hr : ∀ y, 0 < r y := ratio_pos hinv hK hlam hu
  have hmass : ∑ x, lam x * lossGradDensity K lam u wnu gd x
      = ∑ x, lam x * (gd (r x) * (1 - r x) * wnu x) := by
    simp only [lossGradDensity, hrdef]
    exact integral_gradDensity_potential hinv gd (ratio K lam u) wnu
  -- the integrand of `−∫ D dλ`, nonnegative everywhere
  set ψ : V → ℝ := fun x => -(lam x * (gd (r x) * (1 - r x) * wnu x)) with hψdef
  have hψnn : ∀ x, 0 ≤ ψ x := by
    intro x
    have h1 : gd (r x) * (1 - r x) ≤ 0 := hnp (r x) (hr x)
    have h2 : 0 ≤ wnu x := le_trans hc₀ (hwnu x)
    have := mul_nonneg (mul_nonneg (hlam x).le (neg_nonneg.mpr h1)) h2
    simp only [hψdef]
    nlinarith [this]
  -- on `S` each term is at least `c₀ (δ²/2) λ(x)`
  have hlow : ∀ x ∈ S, c₀ * (δ ^ 2 / 2) * lam x ≤ ψ x := by
    intro x hx
    have h1 : gd (r x) * (1 - r x) ≤ -(δ ^ 2 / 2) := hfar (r x) (hr x) (hS x hx)
    have h2 : c₀ ≤ wnu x := hwnu x
    have hδsq : (0:ℝ) ≤ δ ^ 2 / 2 := by positivity
    have hstep : c₀ * (δ ^ 2 / 2) ≤ wnu x * -(gd (r x) * (1 - r x)) :=
      mul_le_mul h2 (by linarith) hδsq (le_trans hc₀ h2)
    have := mul_le_mul_of_nonneg_left hstep (hlam x).le
    simp only [hψdef]
    nlinarith [this]
  calc c₀ * (δ ^ 2 / 2) * (∑ x ∈ S, lam x)
      = ∑ x ∈ S, c₀ * (δ ^ 2 / 2) * lam x := by rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ S, ψ x := Finset.sum_le_sum hlow
    _ ≤ ∑ x, ψ x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hψnn i
    _ = -∑ x, lam x * lossGradDensity K lam u wnu gd x := by
        rw [hmass, ← Finset.sum_neg_distrib]
    _ ≤ |∑ x, lam x * lossGradDensity K lam u wnu gd x| := neg_le_abs _
    _ ≤ Graph.nrmL2 lam (lossGradDensity K lam u wnu gd) :=
        abs_mass_le_nrmL2 (fun x => (hlam x).le) htot _

/-! ### Item *(3)*'s display for `g = (x − 1)²` -/

/-- **`prop:no_distant_equilibrium`*(3)*'s display for `g = (x − 1)²`** (statement
`proofs.tex:813–817`, proof `proofs.tex:830–833`):
`‖∇^λ 𝓛_{g,ν}(μ)‖ ≥ (w_min λ_min^{1/2}/‖u₀‖)(δ²/2) λ(|r−1| ≥ δ)` for `g' = 2(x − 1)`,
`ν = wλ` with `w ≥ w_min > 0`, on the sphere `‖u‖ = ‖u₀‖`, for every `δ ≥ 0` (the paper's
`δ ∈ (0, ½]` included; see the module SCOPE).

The `(x − 1)²` twin of `Lojasiewicz.no_distant_equilibrium_three`, with the same constant and the
same reading of `dν/dμ = w/u` and of `‖∇^λ 𝓛‖` as the `L²(λ)` norm of `lossGradDensity`. -/
theorem no_distant_equilibrium_three_sq
    {K : V → V → ℝ} {lam u u0 wf : V → ℝ} {lamMin wmin δ : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hsph : Graph.nrmL2 lam u = Graph.nrmL2 lam u0) (hu0 : 0 < Graph.nrmL2 lam u0)
    (hδ : 0 ≤ δ) :
    wmin * Real.sqrt lamMin / Graph.nrmL2 lam u0 * (δ ^ 2 / 2)
        * (∑ x ∈ farSet (ratio K lam u) δ, lam x)
      ≤ Graph.nrmL2 lam
          (lossGradDensity K lam u (fun x => wf x / u x) fun x => 2 * (x - 1)) := by
  have hc₀ : 0 ≤ wmin * Real.sqrt lamMin / Graph.nrmL2 lam u0 := by positivity
  exact no_distant_equilibrium_three_far_of hinv hK hlam htot hu hc₀
    (fun x => le_density_ratio (fun y => (hlam y).le) hlmin hlmin0 hu hwmin.le hw hsph hu0 x)
    (fun x _ => sqDeriv_mul_one_sub_nonpos x)
    (fun _ _ hx => sqDeriv_mul_one_sub_le hδ hx)
    _ fun x hx => mem_farSet.mp hx

end GFNBounds.Balance
