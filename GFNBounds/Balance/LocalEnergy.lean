import GFNBounds.Balance.Expansion
import GFNBounds.Balance.MassAscent
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Steps 2 and 3 of the local convergence theorem: the energy estimate, and the drift of the mass

**`theo:local_convergence_full`** — statement `proofs.tex:612–618`, proof `proofs.tex:620–657`;
**Steps 2 and 3 only** (`proofs.tex:634–641`). Step 1 is `GFNBounds/Balance/Expansion.lean`;
Steps 4 and 5, and the gradient-descent clause of `proofs.tex:653–657`, are not here.
(The bold-backtick form of the label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (Step 2, energy estimate) Using
> `⟨h^⊥, A†[g''(1)wAh^⊥]⟩ = g''(1)⟨Ah^⊥, wAh^⊥⟩ ≥ g''(1)w_min‖Ah^⊥‖²` and
> `‖h^⊥‖ ≤ B̂‖Ah^⊥‖` (Lemma `lem:sigma_mixing`), for `ε ≤ ε₁ := g''(1)w_min/(2KB̂)`,
> `d/dt ½‖h^⊥‖² = −⟨h^⊥,D⟩ ≤ −(g''(1)w_min/2)‖Ah^⊥‖² ≤ −(ϱ/2)‖h^⊥‖²`,
> whence `‖h_t^⊥‖ ≤ e^{−ϱt/2}‖h_0^⊥‖` and `∫_0^∞‖Ah_s^⊥‖²ds ≤ ‖h_0^⊥‖²/(g''(1)w_min)`.

> (Step 3, drift of the mass) Since `P†` preserves `λ`-integrals,
> `ṁ = −∫D dλ = ∫(r−1)φ dλ`, so `|ṁ| ≤ C₆‖Ah^⊥‖²` with `C₆ := 4C_g‖w‖_{L^∞}`. By Step 2, `m_t`
> converges to some `m_∞` with `|m_∞−m_t| ≤ (4C₆/ϱ)e^{−ϱt}‖h_0^⊥‖²` and
> `|m_t−m_0| ≤ C₇‖h_0^⊥‖²`, `C₇ := C₆/(g''(1)w_min)`.

## The setting, in this file's variables

`u_t = 1 + h_t` is the `λ`-density of `μ_t`, carried as `fun s x => 1 + h s x` so that every
statement of `Expansion.lean` applies verbatim; `IsGradientFlow K lam (λw) gd` is the ODE
`u̇ = −D(u)` of `Flow.lean`, hypothesised of a given curve and never solved. `m_t` is
`Graph.meanL2 lam (h t)`, `h_t^⊥` is `perpL2 lam (h t)`, and `D_t` is
`lossGrad K lam (λw) gd (1 + h t)`. The window of Steps 1–3 is the hypothesis
`hwin : ∀ s ∈ Set.Icc 0 T, ∀ x, |h s x| ≤ eps`; making it hold on all of `ℝ₊` is Step 4's job
and is not done here.

## What is proved

| | |
|---|---|
| `eps1`, `C6`, `C7`, `rhoL` | the four constants, as the paper's printed formulas and not as `∃ C`. `Expansion.C4/Cg/C5/Kexp` are reused |
| `Kexp_mul_eps_mul_Bhat_le` | **`ε₁` is exactly the half-absorption threshold**: `KεB̂ ≤ g''(1)w_min/2` under `ε ≤ ε₁`, with equality at `ε = ε₁` |
| **`energy_lower`** | **Step 2's first inequality** (`proofs.tex:636`): `(g''(1)w_min/2)‖Ah^⊥‖² ≤ ⟨h^⊥,D⟩` |
| **`energy_lower_perp`** | **Step 2's second inequality** (`proofs.tex:637`): `(ϱ/2)‖h^⊥‖² ≤ ⟨h^⊥,D⟩` |
| `meanL2_perpL2` | `Πh^⊥ = 0`, the fact that makes the mean's drift drop out of `d/dt‖h^⊥‖²` |
| `hasDerivAt_flowDev`, `continuous_flowDev` | `ḣ = −D` state by state, and the continuity it gives |
| **`hasDerivAt_mean`** | **`ṁ = −∫D dλ`** (`proofs.tex:641`), from `MassAscent.hasDerivAt_mass_flow` and `Πh = ∫u dλ − 1` |
| **`hasDerivAt_perp_sq`** | **`d/dt‖h^⊥‖² = −2⟨h^⊥,D⟩`** (`proofs.tex:636`), assembled on the explicit sum: `V → ℝ` is not an `InnerProductSpace` here, so there is no `HasDerivAt.inner` to call |
| `continuous_perp_flow`, `continuous_Aop_perp_flow`, `continuous_energy_flow` | `s ↦ ‖Ah_s^⊥‖²` is continuous — the *only* integrand this file ever integrates. See SCOPE |
| **`perp_decay_on`** | **`‖h_t^⊥‖ ≤ e^{−ϱt/2}‖h_0^⊥‖`** on `[0,T]` (`proofs.tex:639`), by Grönwall |
| `energy_integral_Icc`, **`energy_integral_on`** | **`g''(1)w_min∫_{t₀}^{t₁}‖Ah^⊥‖² ≤ ‖h_{t₀}^⊥‖²`** (`proofs.tex:639`), on a sub-interval and on `[0,T]` |
| **`energy_integral_Ioi`** | **`∫_0^∞‖Ah_s^⊥‖²ds ≤ ‖h_0^⊥‖²/(g''(1)w_min)`** (`proofs.tex:639`), the improper integral, under the global window |
| `abs_ratio_sub_one_mul_phi_sq_le` | `|(r−1)φ| ≤ (64/27)C_g‖w‖_{L^∞}(Ah^⊥)²` — the sharp form of Step 3's pointwise bound |
| `abs_ratio_sub_one_mul_phi_sq_le_C6` | the same with the paper's `C₆ = 4C_g‖w‖_{L^∞}` |
| **`abs_deriv_mean_le`** | **`|ṁ| ≤ C₆‖Ah^⊥‖²`** (`proofs.tex:641`) |
| `abs_mean_sub_le_energy_integral` | `|m_{t₁} − m_{t₀}| ≤ C₆∫_{t₀}^{t₁}‖Ah^⊥‖²` |
| **`mean_drift_on`** | **`|m_t − m_0| ≤ C₇‖h_0^⊥‖²`** (`proofs.tex:641`) |
| **`mean_cauchy_on`** | **`|m_t − m_s| ≤ (4C₆/ϱ)e^{−ϱs}‖h_0^⊥‖²`** (`proofs.tex:641`), the paper's constant by the paper's route |
| `mean_cauchy_on_sharp` | the same with `C₇` in place of `4C₆/ϱ = 4B̂²C₇`. **Sharper than the paper.** See SCOPE |
| `energyH`, `twoState_coercivity`, `twoState_energy_check` | Step 2 **evaluated** on the two-state chain at `ε = 1/40 ≤ ε₁ = 3/80`: `(g''(1)w_min/2)‖Ah^⊥‖² = 1/1600` against `⟨h^⊥,D⟩ = 5129600/4088324799` |

## Hypothesis checklist — `theo:local_convergence_full`, Steps 2 and 3

| paper hypothesis | here |
|---|---|
| `T` ergodic with invariant `λ`; `𝒮` a general state space | ⚠ **weakened and restricted**: `Core.IsMarkovOn lam K`, `Core.IsInvariant lam K`, `λ > 0`, `∑λ = 1`, on a `Fintype`. Ergodicity is used nowhere: it is what makes `Πh` a scalar, and `Graph.meanL2` is that scalar by definition. Same reading as `Expansion.lean` |
| `ν = wλ` with `w ∈ L^∞(λ)` | ✓ `nu = fun z => lam z * w z`, `hwsup : ∀ x, |w x| ≤ wsup`, `hwsup0 : 0 ≤ wsup` |
| `g` is `C²` near `1` with `g(1)=g'(1)=0`, `g''(1)>0`, and `C³` on `[1−a,1+a]` with `a∈(0,1)`, `M₃` its third-derivative bound | ⚠ **weakened to the consequence used**, exactly as in `Expansion.lean`: only `g'` appears (as `gd`), the Taylor bound is the hypothesis `htaylor`, `0 ≤ g2` replaces `g''(1) > 0`, and `0 ≤ a`, `0 ≤ M₃` replace `a ∈ (0,1)` and the supremum. **`g'` is never assumed continuous** — see SCOPE |
| `T` ergodic with summable `L²`-mixing, `B̂ := ∑β̂_n < ∞` | ⚠ **replaced by the finite hypothesis it produces**: `hcoer : ∀ f, ‖f^⊥‖_{L²(λ)} ≤ B̂‖Af‖_{L²(λ)}`, plus `hB0 : 0 ≤ B̂`. No mixing coefficient, no operator series, no `Core.Mixing`. See SCOPE |
| `w ≥ w_min > 0` | ⚠ **weakened**: `hwmin : ∀ x, wmin ≤ w x` and `hwmin0 : 0 ≤ wmin`. `0 < g''(1)w_min` is carried *only* by `energy_integral_Ioi`, `mean_drift_on` and `mean_cauchy_on_sharp`, which divide by it |
| `ϱ := g''(1)w_min/B̂²` | ✓ `rhoL`, the printed formula. `0 < ϱ` is a hypothesis of `mean_cauchy_on` alone |
| `‖·‖_{L^∞(λ)} ≤ C_∞‖·‖_{L²(λ)}`, `C_∞ = (min λ)^{−1/2}` | ✗ not needed by Steps 2–3 — it is Step 4's. `L2Toolkit.abs_le_nrmL2_div_sqrt` carries it |
| `‖h‖_{L^∞} ≤ ε ≤ min(a,1)/4` (Step 1's radius) | ✓ `heps`, `heps0`, and `hwin` at each time |
| `ε ≤ ε₁ := g''(1)w_min/(2KB̂)` | ✓ `heps1`, with `Expansion.Kexp` for `K` |
| the flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` | ⚠ `IsGradientFlow K lam (λw) gd (fun s x => 1 + h s x)`, **hypothesised of a given curve**; no existence theorem, as in `Flow.lean` |
| `⟨h^⊥, A†[g''(1)wAh^⊥]⟩ ≥ g''(1)w_min‖Ah^⊥‖²` | ✓ `Expansion.linHess_coercive`, reused |
| `d/dt ½‖h^⊥‖² = −⟨h^⊥,D⟩` | ✓ `hasDerivAt_perp_sq`, as `d/dt‖h^⊥‖² = −2⟨h^⊥,D⟩` |
| `≤ −(g''(1)w_min/2)‖Ah^⊥‖²`, `≤ −(ϱ/2)‖h^⊥‖²` | ✓ `energy_lower`, `energy_lower_perp` |
| `‖h_t^⊥‖ ≤ e^{−ϱt/2}‖h_0^⊥‖` | ⚠ **on the window `[0,T]`** (`perp_decay_on`). The paper states it for all `t ≥ 0` because Step 4 makes the window all of `ℝ₊`; Step 4 is not here |
| `∫_0^∞‖Ah_s^⊥‖²ds ≤ ‖h_0^⊥‖²/(g''(1)w_min)` | ✓ `energy_integral_Ioi`, under the global window and `0 < g''(1)w_min`; `energy_integral_on` is the finite-horizon form, which needs neither |
| `ṁ = −∫D dλ = ∫(r−1)φ dλ` | ✓ `hasDerivAt_mean` for the first equality, `MassIdentity.integral_gradDensity` inside `abs_deriv_mean_le` for the second |
| `|ṁ| ≤ C₆‖Ah^⊥‖²`, `C₆ = 4C_g‖w‖_{L^∞}` | ✓ `abs_deriv_mean_le`, with the printed constant. `(64/27)C_g‖w‖_{L^∞}` also proved; see SCOPE |
| "`m_t` converges to some `m_∞`" | ✗ **not stated.** No limit is formed. `mean_cauchy_on` is the estimate the convergence follows from; `m_∞` and `c_∞` are Step 5's objects. See SCOPE |
| `|m_∞ − m_t| ≤ (4C₆/ϱ)e^{−ϱt}‖h_0^⊥‖²` | ⚠ **between two finite times**: `mean_cauchy_on` gives `|m_t − m_s| ≤ (4C₆/ϱ)e^{−ϱs}‖h_0^⊥‖²` for `0 ≤ s ≤ t ≤ T`, which is the same statement with the limit not taken |
| `|m_t − m_0| ≤ C₇‖h_0^⊥‖²`, `C₇ = C₆/(g''(1)w_min)` | ✓ `mean_drift_on`, printed constant |
| Step 1; Steps 4–5; `ε₀`, `c_∞`, `L`, `γ₀`; the discrete clause | ✗ Step 1 is `Expansion.lean`; the rest is **not here** |

## SCOPE (disclosed)

* **Finite state space**, as everywhere in `GFNBounds.Balance`: `∫·dλ` is `∑ x, lam x * ·`, a
  measure is carried by a density, and `⟪·∣·⟫_λ`, `‖·‖_λ`, `Π` are `Graph.ipL2`, `Graph.nrmL2`,
  `Graph.meanL2`. `paper-map.json` recorded `theo:local_convergence_full` as bucket `D` when this file was written;
  it is `closed`/`B` now, this file and its sibling being why. Nothing
  here moves it.
* **The coercivity `‖f^⊥‖ ≤ B̂‖Af‖` is a hypothesis, not `Core.Mixing`.** The paper reaches it
  from summable `L²`-mixing through `lem:sigma_mixing`, which is closed in
  `GFNBounds/Core/Mixing.lean` — but on an abstract inner-product space with bundled
  `ContinuousLinearMap`s, and `(V → ℝ, ⟪·∣·⟫_λ)` is not an `InnerProductSpace` instance in this
  library (the bridge is the missing piece `Expansion.lean` names and does not build). So the
  finite-state face of the conclusion is taken as the hypothesis `hcoer`. It is **not vacuous**:
  `Graph.BackwardPolicy.coercivity_lamMin` is exactly it with `B̂ = σ_*/√(min λ)`, and
  `twoState_coercivity` below inhabits it with `B̂ = 1`, exactly.
* **The window is a hypothesis, and making it global is Step 4.** Every statement here is
  conditioned on `∀ s ∈ [0,T], ‖h_s‖_{L^∞} ≤ ε`. The paper discharges that by the continuation
  argument of `proofs.tex:643`, whose shape is already in the library as
  `L2Toolkit.bootstrap_of_continuous`; assembling it, and Step 5's `c_∞`, is another file's.
  Nothing here asserts that `m_t` converges, or names `m_∞`.
* **The generator's derivative is never assumed continuous, and that dictates the shape of every
  integration below.** The natural route to `∫‖Ah^⊥‖²` and to `|m_t − m_s|` is the fundamental
  theorem applied to `d/dt‖h^⊥‖²` and to `ṁ`; both carry `g'` through `D`, of which this file
  assumes only the Taylor bound `htaylor`, so neither is known to be integrable. Instead each
  estimate is run as a **monotonicity** argument on
  `τ ↦ ‖h_τ^⊥‖² + g''(1)w_min∫_{t₀}^τ‖Ah^⊥‖²` and on `τ ↦ C₆∫_{t₀}^τ‖Ah^⊥‖² ∓ m_τ`, and the
  only function ever integrated is `s ↦ ‖Ah_s^⊥‖²`, which is continuous for reasons independent
  of `g` (`continuous_energy_flow`). Assuming `g` continuously differentiable would remove the
  obstruction and weaken the theorem; it was not assumed.
* **`ε₁` is exactly the threshold at which the expansion error eats half the coercivity, and
  that was verified rather than copied.** `Expansion.gradient_expansion` bounds the error by
  `Kε‖Ah^⊥‖`; Cauchy–Schwarz and `hcoer` turn `⟨h^⊥, E⟩` into at most `KεB̂‖Ah^⊥‖²`, and
  `KεB̂ ≤ g''(1)w_min/2` exactly when `ε ≤ ε₁`, with equality at `ε = ε₁` —
  `Kexp_mul_eps_mul_Bhat_le`. The paper's `ε₁` is correct as printed, the factor `1/2` included.
* **`C₆ = 4C_g‖w‖_{L^∞}` is valid but not sharp; `(64/27)C_g‖w‖_{L^∞}` suffices.** The chain is
  `|r−1|·C_g|r−1|·(4/3)‖w‖_{L^∞}` with `|r−1| ≤ (4/3)|Ah^⊥|` used twice, so the constant is
  `(4/3)³ = 64/27 ≈ 2.370` against the printed `4`. Both are stated —
  `abs_ratio_sub_one_mul_phi_sq_le` and `abs_ratio_sub_one_mul_phi_sq_le_C6` — and everything
  downstream uses the paper's.
* **`|m_∞ − m_t| ≤ (4C₆/ϱ)e^{−ϱt}‖h_0^⊥‖²` is valid but not sharp either.** The paper's route
  spends `‖Ah^⊥‖² ≤ 4‖h^⊥‖²` and integrates the exponential; restarting the *energy* estimate at
  time `s` instead gives `C₇e^{−ϱs}‖h_0^⊥‖²`, and `4C₆/ϱ = 4B̂²C₇` with `B̂ ≥ 1` in the paper's
  setting, so the sharper constant is smaller by a factor `4B̂²`. `mean_cauchy_on` is the paper's,
  `mean_cauchy_on_sharp` is the sharper one. This matters downstream: Step 4's
  `ε₀ := min(ε/(2C_∞(2+C₇)), ϱ/(4C₆), 1)` has `ϱ/(4C₆)` as its second entry, the reciprocal of
  the paper's constant, so the basin widens by the same `4B̂²` if the sharper estimate is used.
  **The paper is not wrong; it is loose, and the looseness lands in the basin.**
* **`D` is `Flow.lossGrad`, which is a definition.** That it represents `∇^λ𝓛_{g,ν}(μ)` is
  `theo:first_variation_full`, formalized on a finite state space in
  `GFNBounds/Balance/FirstVariation.lean` and disclosed there; nothing below re-derives it.
* **No existence theorem for the flow, and none is needed.** Every statement quantifies over
  curves satisfying `IsGradientFlow`, exactly as `Flow.lean` does and as the paper's own proofs
  read.
* **`sorry`-free and axiom-clean.** `#print axioms` on `energy_lower`, `energy_lower_perp`,
  `hasDerivAt_mean`, `hasDerivAt_perp_sq`, `perp_decay_on`, `energy_integral_on`,
  `energy_integral_Ioi`, `abs_deriv_mean_le`, `mean_drift_on`, `mean_cauchy_on`,
  `mean_cauchy_on_sharp` and `twoState_energy_check` returns
  `[propext, Classical.choice, Quot.sound]`. Graduated into the strict library on 2026-09-12.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### The four constants of Steps 2 and 3 -/

/-- **`ε₁ := g''(1)w_min/(2KB̂)`** (`proofs.tex:634`). -/
noncomputable def eps1 (g2 wmin Kexp Bhat : ℝ) : ℝ := g2 * wmin / (2 * Kexp * Bhat)

/-- **`C₆ := 4C_g‖w‖_{L^∞}`** (`proofs.tex:641`). -/
noncomputable def C6 (Cg wsup : ℝ) : ℝ := 4 * Cg * wsup

/-- **`C₇ := C₆/(g''(1)w_min)`** (`proofs.tex:641`). -/
noncomputable def C7 (C6 g2 wmin : ℝ) : ℝ := C6 / (g2 * wmin)

/-- **`ϱ := g''(1)w_min/B̂²`** (`proofs.tex:595`). -/
noncomputable def rhoL (g2 wmin Bhat : ℝ) : ℝ := g2 * wmin / Bhat ^ 2

theorem Kexp_nonneg {g2 a M3 wsup : ℝ} (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a)
    (hwsup0 : 0 ≤ wsup) : 0 ≤ Kexp g2 a M3 wsup := by
  simp only [Kexp, C4, C5, Cg]; positivity

theorem rhoL_nonneg {g2 wmin Bhat : ℝ} (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) :
    0 ≤ rhoL g2 wmin Bhat := by
  simp only [rhoL]; positivity

/-! ### Step 2, the pointwise energy estimate -/

/-- **`Kεδ ≤ g''(1)w_min/2` at `ε ≤ ε₁`** — the arithmetic that names `ε₁`: it is *exactly* the
threshold at which the expansion error eats half of the coercivity, no more and no less. -/
theorem Kexp_mul_eps_mul_Bhat_le {g2 wmin Bhat eps kap : ℝ} (hg2wmin : 0 ≤ g2 * wmin)
    (hkap : 0 ≤ kap) (hB0 : 0 ≤ Bhat) (heps1 : eps ≤ eps1 g2 wmin kap Bhat) :
    kap * eps * Bhat ≤ g2 * wmin / 2 := by
  rcases eq_or_lt_of_le (mul_nonneg hkap hB0) with hz | hpos
  · have h1 : kap * eps * Bhat = eps * (kap * Bhat) := by ring
    rw [h1, ← hz, mul_zero]
    linarith
  · have h2 : (0 : ℝ) < 2 * kap * Bhat := by nlinarith
    rw [eps1, le_div_iff₀ h2] at heps1
    nlinarith

/-- **Step 2's first inequality** (`proofs.tex:636–637`): at `‖h‖_{L^∞} ≤ ε ≤ ε₁`,
`⟨h^⊥, D⟩ ≥ (g''(1)w_min/2)‖Ah^⊥‖²`.

`Expansion.linHess_coercive` gives the whole `g''(1)w_min‖Ah^⊥‖²`; `Expansion.gradient_expansion`
bounds the error by `Kε‖Ah^⊥‖`, Cauchy–Schwarz turns `⟨h^⊥, E⟩` into `‖h^⊥‖·Kε‖Ah^⊥‖`, and the
coercivity hypothesis `‖h^⊥‖ ≤ B̂‖Ah^⊥‖` makes that `KεB̂‖Ah^⊥‖²`. At `ε = ε₁` that is exactly
half of `g''(1)w_min‖Ah^⊥‖²`. -/
theorem energy_lower {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup wmin Bhat eps : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat) :
    g2 * wmin / 2 * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) ^ 2
      ≤ Graph.ipL2 lam (perpL2 lam h)
          (lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z)) := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  set D : V → ℝ := lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z) with hD
  set Hh : V → ℝ := linHess K lam w g2 (perpL2 lam h) with hH
  set A : V → ℝ := Aop K lam (perpL2 lam h) with hA
  have hAeq : Aop K lam (perpL2 lam h) = Aop K lam h :=
    funext fun y => Aop_perpL2 hinv h (hlam y).ne'
  -- coercivity of the linear part
  have hco : g2 * wmin * Graph.nrmL2 lam A ^ 2 ≤ Graph.ipL2 lam (perpL2 lam h) Hh :=
    linHess_coercive hinv hK.nonneg hwmin hg2 (perpL2 lam h)
  -- the expansion error
  have hexp : Graph.nrmL2 lam (fun x => D x - Hh x)
      ≤ Kexp g2 a M3 wsup * eps * Graph.nrmL2 lam A :=
    gradient_expansion hK hinv hlam hg2 hM3 ha0 hwsup0 hwsup htaylor hh heps0 heps
  -- Cauchy–Schwarz against the error
  have hcs : -Graph.ipL2 lam (perpL2 lam h) (fun x => D x - Hh x)
      ≤ Graph.nrmL2 lam (perpL2 lam h) * Graph.nrmL2 lam (fun x => D x - Hh x) := by
    have h1 := Graph.ipL2_le_mul_nrmL2 hnn (perpL2 lam h) (fun x => -(D x - Hh x))
    have h2 : Graph.ipL2 lam (perpL2 lam h) (fun x => -(D x - Hh x))
        = -Graph.ipL2 lam (perpL2 lam h) (fun x => D x - Hh x) := by
      simp only [Graph.ipL2, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rwa [h2, nrmL2_neg] at h1
  -- the coercivity hypothesis, read at `Ah^⊥`
  have hpB : Graph.nrmL2 lam (perpL2 lam h) ≤ Bhat * Graph.nrmL2 lam A := by
    rw [hA, hAeq]; exact hcoer h
  have hAnn : 0 ≤ Graph.nrmL2 lam A := Graph.nrmL2_nonneg _ _
  have hpnn : 0 ≤ Graph.nrmL2 lam (perpL2 lam h) := Graph.nrmL2_nonneg _ _
  have hKnn : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2 hM3 ha0 hwsup0
  have habs : Kexp g2 a M3 wsup * eps * Bhat ≤ g2 * wmin / 2 :=
    Kexp_mul_eps_mul_Bhat_le (mul_nonneg hg2 hwmin0) hKnn hB0 heps1
  -- the error is at most half the coercivity
  have herr : -Graph.ipL2 lam (perpL2 lam h) (fun x => D x - Hh x)
      ≤ g2 * wmin / 2 * Graph.nrmL2 lam A ^ 2 := by
    refine le_trans hcs ?_
    have hstep : Graph.nrmL2 lam (perpL2 lam h) * Graph.nrmL2 lam (fun x => D x - Hh x)
        ≤ (Bhat * Graph.nrmL2 lam A) * (Kexp g2 a M3 wsup * eps * Graph.nrmL2 lam A) :=
      mul_le_mul hpB hexp (Graph.nrmL2_nonneg _ _) (mul_nonneg hB0 hAnn)
    nlinarith [hstep, sq_nonneg (Graph.nrmL2 lam A)]
  have hsplit : Graph.ipL2 lam (perpL2 lam h) D
      = Graph.ipL2 lam (perpL2 lam h) Hh + Graph.ipL2 lam (perpL2 lam h) (fun x => D x - Hh x) := by
    rw [ipL2_sub_right]; ring
  rw [hsplit]
  linarith [hco, herr]

/-- **Step 2's second inequality** (`proofs.tex:637`): `⟨h^⊥, D⟩ ≥ (ϱ/2)‖h^⊥‖²`, the same
estimate after `lem:sigma_mixing` replaces `‖Ah^⊥‖` by `‖h^⊥‖/B̂`. -/
theorem energy_lower_perp {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup wmin Bhat eps : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat) :
    rhoL g2 wmin Bhat / 2 * Graph.nrmL2 lam (perpL2 lam h) ^ 2
      ≤ Graph.ipL2 lam (perpL2 lam h)
          (lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z)) := by
  have hbase := energy_lower hK hinv hlam hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin hB0 hcoer
    htaylor hh heps0 heps heps1
  have hAeq : Aop K lam (perpL2 lam h) = Aop K lam h :=
    funext fun y => Aop_perpL2 hinv h (hlam y).ne'
  have hpB : Graph.nrmL2 lam (perpL2 lam h) ≤ Bhat * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) := by
    rw [hAeq]; exact hcoer h
  have hAnn : 0 ≤ Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) := Graph.nrmL2_nonneg _ _
  have hpnn : 0 ≤ Graph.nrmL2 lam (perpL2 lam h) := Graph.nrmL2_nonneg _ _
  have hgw : 0 ≤ g2 * wmin := mul_nonneg hg2 hwmin0
  refine le_trans ?_ hbase
  rcases eq_or_lt_of_le hB0 with hz | hpos
  · have hrho : rhoL g2 wmin Bhat = 0 := by
      simp only [rhoL, ← hz]; norm_num
    rw [hrho]
    have : 0 ≤ g2 * wmin / 2 * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) ^ 2 := by positivity
    linarith
  · have hsq : Graph.nrmL2 lam (perpL2 lam h) ^ 2
        ≤ Bhat ^ 2 * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) ^ 2 := by
      nlinarith [hpB, hpnn, hAnn]
    have hB2 : (0 : ℝ) < Bhat ^ 2 := by positivity
    rw [rhoL, div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < Bhat ^ 2 * 2)]
    nlinarith [hsq, hgw]


/-! ### The curve, its derivative, and the two derivatives Steps 2 and 3 differentiate -/

/-- **`Πh^⊥ = 0`** when `λ` is a probability: the mean-zero part has mean zero. -/
theorem meanL2_perpL2 {lam : V → ℝ} (htot : ∑ x, lam x = 1) (f : V → ℝ) :
    Graph.meanL2 lam (perpL2 lam f) = 0 := by
  have hexp : ∀ x : V, lam x * perpL2 lam f x
      = lam x * f x - Graph.meanL2 lam f * lam x := by
    intro x; rw [perpL2_apply]; ring
  simp only [Graph.meanL2]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x, Finset.sum_sub_distrib,
    ← Finset.mul_sum, htot, mul_one]
  exact sub_self _

/-- **`ḣ_t = −D_t` state by state**: the gradient-flow ODE for `μ_t = (1+h_t)λ`, read on `h`. -/
theorem hasDerivAt_flowDev {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd fun s x => 1 + h s x) (t : ℝ) (x : V) :
    HasDerivAt (fun s : ℝ => h s x) (-lossGrad K lam nu gd (fun z => 1 + h t z) x) t := by
  have h1 := (hflow t x).sub_const 1
  simpa using h1

/-- `s ↦ h_s(x)` is continuous, being differentiable. -/
theorem continuous_flowDev {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd fun s x => 1 + h s x) (x : V) :
    Continuous fun s : ℝ => h s x := by
  have hdiff : Differentiable ℝ fun s : ℝ => h s x :=
    fun s => (hasDerivAt_flowDev hflow s x).differentiableAt
  exact hdiff.continuous

/-- **`ṁ = −∫D dλ`** (`proofs.tex:641`) at `m_t = Πh_t`: `MassAscent.hasDerivAt_mass_flow`
differentiates `∫u_t dλ`, and `Πh_t = ∫u_t dλ − 1` because `λ` is a probability. -/
theorem hasDerivAt_mean {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    (htot : ∑ x, lam x = 1)
    (hflow : IsGradientFlow K lam nu gd fun s x => 1 + h s x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Graph.meanL2 lam (h s))
      (-Graph.meanL2 lam (lossGrad K lam nu gd fun z => 1 + h t z)) t := by
  have hshift : ∀ s : ℝ, Graph.meanL2 lam (h s)
      = Graph.meanL2 lam (fun x => 1 + h s x) - 1 := by
    intro s
    have hexp : ∀ x : V, lam x * (1 + h s x) = lam x + lam x * h s x := fun x => by ring
    simp only [Graph.meanL2]
    rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x,
      Finset.sum_add_distrib, htot]
    ring
  have hm := (hasDerivAt_mass_flow hflow t).sub_const 1
  simp only [hshift]
  exact hm

/-- **`d/dt‖h^⊥_t‖² = −2⟨h^⊥_t, D_t⟩`** (`proofs.tex:636`), the quantity Grönwall is applied to.

Assembled on the explicit sum `∑_x λ(x)h^⊥_t(x)²`: `(V → ℝ, ⟪·∣·⟫_λ)` is not an
`InnerProductSpace` in this library, so there is no `HasDerivAt.inner` to call. The mean drifts
too, and its contribution vanishes because `Πh^⊥ = 0`. -/
theorem hasDerivAt_perp_sq {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1)
    (hflow : IsGradientFlow K lam nu gd fun s x => 1 + h s x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Graph.nrmL2 lam (perpL2 lam (h s)) ^ 2)
      (-(2 * Graph.ipL2 lam (perpL2 lam (h t))
          (lossGrad K lam nu gd fun z => 1 + h t z))) t := by
  set D : V → ℝ := lossGrad K lam nu gd (fun z => 1 + h t z) with hD
  set md : ℝ := Graph.meanL2 lam D with hmd
  have hdp : ∀ x : V, HasDerivAt (fun s : ℝ => perpL2 lam (h s) x) (-D x - -md) t := by
    intro x
    simp only [perpL2_apply]
    exact (hasDerivAt_flowDev hflow t x).sub (hasDerivAt_mean htot hflow t)
  have hsq : (fun s : ℝ => Graph.nrmL2 lam (perpL2 lam (h s)) ^ 2)
      = fun s : ℝ => ∑ x, lam x * (perpL2 lam (h s) x * perpL2 lam (h s) x) := by
    funext s
    rw [Graph.sq_nrmL2 hnn]
    rfl
  rw [hsq]
  have hsum : HasDerivAt (fun s : ℝ => ∑ x, lam x * (perpL2 lam (h s) x * perpL2 lam (h s) x))
      (∑ x, lam x * ((-D x - -md) * perpL2 lam (h t) x
        + perpL2 lam (h t) x * (-D x - -md))) t :=
    HasDerivAt.fun_sum fun x _ => HasDerivAt.const_mul (lam x) ((hdp x).fun_mul (hdp x))
  have hval : (∑ x, lam x * ((-D x - -md) * perpL2 lam (h t) x
        + perpL2 lam (h t) x * (-D x - -md)))
      = -(2 * Graph.ipL2 lam (perpL2 lam (h t)) D) := by
    have hexp : ∀ x : V, lam x * ((-D x - -md) * perpL2 lam (h t) x
        + perpL2 lam (h t) x * (-D x - -md))
        = 2 * md * (lam x * perpL2 lam (h t) x)
          - 2 * (lam x * (perpL2 lam (h t) x * D x)) := fun x => by ring
    rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h0 : (∑ x, lam x * perpL2 lam (h t) x) = 0 := meanL2_perpL2 htot (h t)
    rw [h0, mul_zero, zero_sub]
    rfl
  rwa [hval] at hsum


/-! ### Continuity of the energy density `s ↦ ‖Ah^⊥_s‖²`

The integrals of Steps 2 and 3 are integrals of this one function. It is continuous for a reason
that has nothing to do with `g`: `A` and `Π` are finite linear combinations of the coordinates,
and each coordinate is differentiable in time. `g'` is never assumed continuous anywhere in this
file, which is why no argument below integrates `Ḋ` or `ṁ` directly. -/

theorem continuous_perp_flow {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd fun s x => 1 + h s x) (x : V) :
    Continuous fun s : ℝ => perpL2 lam (h s) x := by
  simp only [perpL2_apply, Graph.meanL2]
  exact (continuous_flowDev hflow x).sub
    (continuous_finsetSum _ fun y _ => continuous_const.mul (continuous_flowDev hflow y))

theorem continuous_Aop_perp_flow {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd fun s x => 1 + h s x) (y : V) :
    Continuous fun s : ℝ => Aop K lam (perpL2 lam (h s)) y := by
  simp only [Aop_apply, Core.densAct_apply]
  exact ((continuous_finsetSum _ fun x _ =>
      continuous_const.mul (continuous_perp_flow hflow x)).div_const _).sub
    (continuous_perp_flow hflow y)

/-- **`s ↦ ‖Ah^⊥_s‖²` is continuous**, hence interval-integrable — the only integrability fact
Steps 2 and 3 need. -/
theorem continuous_energy_flow {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    (hnn : ∀ x, 0 ≤ lam x)
    (hflow : IsGradientFlow K lam nu gd fun s x => 1 + h s x) :
    Continuous fun s : ℝ => Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2 := by
  have hrw : (fun s : ℝ => Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2)
      = fun s : ℝ => ∑ x, lam x * (Aop K lam (perpL2 lam (h s)) x
          * Aop K lam (perpL2 lam (h s)) x) := by
    funext s
    rw [Graph.sq_nrmL2 hnn]
    rfl
  rw [hrw]
  exact continuous_finsetSum _ fun x _ => continuous_const.mul
    ((continuous_Aop_perp_flow hflow x).mul (continuous_Aop_perp_flow hflow x))

/-! ### Step 2, integrated: the exponential decay of `‖h^⊥_t‖` -/

/-- **`‖h_t^⊥‖ ≤ e^{−ϱt/2}‖h_0^⊥‖` on the window** (`proofs.tex:639`).

`hasDerivAt_perp_sq` turns `energy_lower_perp` into `d/dt‖h^⊥‖² ≤ −ϱ‖h^⊥‖²`, and Grönwall —
`Mathlib.le_gronwallBound_of_liminf_deriv_right_le` at `K = −ϱ`, `ε = 0`, on `Icc 0 T` — closes
it; the square root is taken at the end. The half in the exponent is the square root's, not the
estimate's: `ϱ` is the rate of `‖h^⊥‖²`. -/
theorem perp_decay_on {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat eps T : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ x, |h s x| ≤ eps) :
    ∀ t ∈ Set.Icc (0:ℝ) T, Graph.nrmL2 lam (perpL2 lam (h t))
      ≤ Real.exp (-(rhoL g2 wmin Bhat * t / 2)) * Graph.nrmL2 lam (perpL2 lam (h 0)) := by
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  set F : ℝ → ℝ := fun s => Graph.nrmL2 lam (perpL2 lam (h s)) ^ 2 with hF
  set Dv : ℝ → ℝ := fun s => -(2 * Graph.ipL2 lam (perpL2 lam (h s))
      (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + h s z)) with hDv
  have hFd : ∀ s : ℝ, HasDerivAt F (Dv s) s :=
    fun s => hasDerivAt_perp_sq (fun x => (hlam x).le) htot hflow s
  have hFbound : ∀ s ∈ Set.Ico (0:ℝ) T, Dv s ≤ -rhoL g2 wmin Bhat * F s + 0 := by
    intro s hs
    have hlow := energy_lower_perp hK hinv hlam hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin hB0 hcoer
      htaylor (hwin s ⟨hs.1, le_of_lt hs.2⟩) heps0 heps heps1
    simp only [hDv, hF, add_zero]
    linarith
  have hcont : ContinuousOn F (Set.Icc 0 T) :=
    fun s _ => ((hFd s).continuousAt).continuousWithinAt
  have hslope : ∀ s ∈ Set.Ico (0:ℝ) T, ∀ r : ℝ, Dv s < r →
      ∃ᶠ z in nhdsWithin s (Set.Ioi s), (z - s)⁻¹ * (F z - F s) < r := by
    intro s _ r hr
    have := (hFd s).hasDerivWithinAt.liminf_right_slope_le hr
    simpa [slope, vsub_eq_sub] using this
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (f := F) (f' := Dv) (δ := F 0)
    (K := -rhoL g2 wmin Bhat) (ε := 0) hcont hslope le_rfl hFbound t ⟨ht0, htT⟩
  rw [gronwallBound_ε0] at hgron
  have hexp : F 0 * Real.exp (-rhoL g2 wmin Bhat * (t - 0))
      = (Real.exp (-(rhoL g2 wmin Bhat * t / 2)) * Graph.nrmL2 lam (perpL2 lam (h 0))) ^ 2 := by
    have hsplit : Real.exp (-rhoL g2 wmin Bhat * (t - 0))
        = Real.exp (-(rhoL g2 wmin Bhat * t / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [hsplit, hF]
    ring
  rw [hexp] at hgron
  have hnn : 0 ≤ Real.exp (-(rhoL g2 wmin Bhat * t / 2)) * Graph.nrmL2 lam (perpL2 lam (h 0)) :=
    mul_nonneg (Real.exp_nonneg _) (Graph.nrmL2_nonneg _ _)
  have hroot := Real.sqrt_le_sqrt hgron
  rwa [hF, Real.sqrt_sq (Graph.nrmL2_nonneg _ _), Real.sqrt_sq hnn] at hroot


/-! ### Step 2's integrated form: `∫‖Ah^⊥‖² ≤ ‖h_0^⊥‖²/(g''(1)w_min)` -/

/-- **`g''(1)w_min ∫_{t₀}^{t₁}‖Ah_s^⊥‖²ds ≤ ‖h_{t₀}^⊥‖²`** on any sub-interval of the window
(`proofs.tex:639`, restarted at `t₀`).

The route is *not* the fundamental theorem applied to `d/dt‖h^⊥‖²`: that derivative is
`−2⟨h^⊥,D⟩`, and `D` carries `g'`, of which this file assumes only a Taylor bound — never
continuity, so it need not be integrable. Instead `τ ↦ ‖h_τ^⊥‖² + g''(1)w_min∫_{t₀}^τ‖Ah^⊥‖²`
is *antitone*, having non-positive derivative by `energy_lower`, and only the continuous
integrand is ever integrated. -/
theorem energy_integral_Icc {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat eps T t₀ t₁ : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ x, |h s x| ≤ eps)
    (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T) :
    g2 * wmin * (∫ s in t₀..t₁, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2)
      ≤ Graph.nrmL2 lam (perpL2 lam (h t₀)) ^ 2 := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  set N : ℝ → ℝ := fun s => Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2 with hN
  have hNc : Continuous N := continuous_energy_flow hnn hflow
  have hNnn : ∀ s : ℝ, 0 ≤ N s := fun s => sq_nonneg _
  set J : ℝ → ℝ := fun τ => ∫ s in t₀..τ, N s with hJ
  have hJd : ∀ τ : ℝ, HasDerivAt J (N τ) τ := fun τ =>
    intervalIntegral.integral_hasDerivAt_right (hNc.intervalIntegrable _ _)
      (hNc.stronglyMeasurableAtFilter _ _) hNc.continuousAt
  set F : ℝ → ℝ := fun s => Graph.nrmL2 lam (perpL2 lam (h s)) ^ 2 with hF
  set Dv : ℝ → ℝ := fun s => -(2 * Graph.ipL2 lam (perpL2 lam (h s))
      (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + h s z)) with hDv
  have hFd : ∀ s : ℝ, HasDerivAt F (Dv s) s :=
    fun s => hasDerivAt_perp_sq hnn htot hflow s
  set Phi : ℝ → ℝ := fun τ => F τ + g2 * wmin * J τ with hPhi
  have hPhid : ∀ τ : ℝ, HasDerivAt Phi (Dv τ + g2 * wmin * N τ) τ :=
    fun τ => (hFd τ).add ((hJd τ).const_mul (g2 * wmin))
  have hPhi' : ∀ τ ∈ Set.Icc t₀ t₁, Dv τ + g2 * wmin * N τ ≤ 0 := by
    intro τ hτ
    have hlow := energy_lower hK hinv hlam hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin hB0 hcoer
      htaylor (hwin τ ⟨le_trans h0 hτ.1, le_trans hτ.2 h1T⟩) heps0 heps heps1
    simp only [hDv, hN]
    linarith
  have hanti : AntitoneOn Phi (Set.Icc t₀ t₁) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun τ _ => ((hPhid τ).continuousAt).continuousWithinAt)
      (fun τ _ => ((hPhid τ).differentiableAt).differentiableWithinAt)
      (fun τ hτ => by
        rw [(hPhid τ).deriv]
        rw [interior_Icc] at hτ
        exact hPhi' τ (Set.Ioo_subset_Icc_self hτ))
  have hstep := hanti (Set.left_mem_Icc.2 h01) (Set.right_mem_Icc.2 h01) h01
  have hJ0 : J t₀ = 0 := intervalIntegral.integral_same
  have hFnn : 0 ≤ F t₁ := sq_nonneg _
  simp only [hPhi, hJ0, mul_zero, add_zero] at hstep
  linarith

/-- **`g''(1)w_min ∫_0^T‖Ah_s^⊥‖²ds ≤ ‖h_0^⊥‖²`** (`proofs.tex:639`), the display as printed. -/
theorem energy_integral_on {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat eps T : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ x, |h s x| ≤ eps) (hT : 0 ≤ T) :
    g2 * wmin * (∫ s in (0:ℝ)..T, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2)
      ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 :=
  energy_integral_Icc hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin hB0 hcoer htaylor
    heps0 heps heps1 hflow hwin le_rfl hT le_rfl

/-- **`∫_0^∞‖Ah_s^⊥‖²ds ≤ ‖h_0^⊥‖²/(g''(1)w_min)`** (`proofs.tex:639`), the improper integral of
the display, under the *global* window Step 4 supplies.

`τ ↦ ∫_0^τ‖Ah^⊥‖²` is monotone with a uniform bound, hence convergent, and
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg` identifies the limit with the improper
integral. `0 < g''(1)w_min` is needed here and nowhere else in Step 2: it is what makes the
uniform bound a bound on the primitive rather than on `g''(1)w_min` times it. -/
theorem energy_integral_Ioi {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat eps : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat) (hgw : 0 < g2 * wmin)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ s : ℝ, 0 ≤ s → ∀ x, |h s x| ≤ eps) :
    g2 * wmin * (∫ s in Set.Ioi (0:ℝ), Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2)
      ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  set N : ℝ → ℝ := fun s => Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2 with hN
  have hNc : Continuous N := continuous_energy_flow hnn hflow
  have hNnn : ∀ s : ℝ, 0 ≤ N s := fun s => sq_nonneg _
  set J : ℝ → ℝ := fun τ => ∫ s in (0:ℝ)..τ, N s with hJ
  have hJd : ∀ τ : ℝ, HasDerivAt J (N τ) τ := fun τ =>
    intervalIntegral.integral_hasDerivAt_right (hNc.intervalIntegrable _ _)
      (hNc.stronglyMeasurableAtFilter _ _) hNc.continuousAt
  have hJmono : Monotone J :=
    monotone_of_deriv_nonneg (fun τ => (hJd τ).differentiableAt)
      (fun τ => by rw [(hJd τ).deriv]; exact hNnn τ)
  have hJ0 : J 0 = 0 := intervalIntegral.integral_same
  have hF0 : 0 ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := sq_nonneg _
  have hbound : ∀ τ : ℝ, 0 ≤ τ → g2 * wmin * J τ
      ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
    intro τ hτ
    exact energy_integral_on (T := τ) hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin
      hB0 hcoer htaylor heps0 heps heps1 hflow (fun s hs => hwin s hs.1) hτ
  have hbdd : BddAbove (Set.range J) := by
    refine ⟨Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 / (g2 * wmin), ?_⟩
    rintro y ⟨τ, rfl⟩
    rcases le_or_gt 0 τ with hτ | hτ
    · rw [le_div_iff₀ hgw]
      have := hbound τ hτ
      linarith
    · have h1 : J τ ≤ J 0 := hJmono hτ.le
      have h2 : (0:ℝ) ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 / (g2 * wmin) := by positivity
      rw [hJ0] at h1
      linarith
  have hlim := tendsto_atTop_ciSup hJmono hbdd
  have hint : (∫ x in Set.Ioi (0:ℝ), N x) = (⨆ i, J i) - J 0 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg
      ((hJd 0).continuousAt).continuousWithinAt (fun x _ => hJd x) (fun x _ => hNnn x) hlim
  have hlim' : Filter.Tendsto (fun τ => g2 * wmin * J τ) Filter.atTop
      (nhds (g2 * wmin * ⨆ i, J i)) := hlim.const_mul _
  have hle : g2 * wmin * (⨆ i, J i) ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 :=
    le_of_tendsto hlim' (Filter.eventually_atTop.2 ⟨0, fun τ hτ => hbound τ hτ⟩)
  rw [hint, hJ0, sub_zero]
  exact hle


/-! ### Step 3, the pointwise bound on the drift of the mass

`proofs.tex:641`. The paper's `C₆ = 4C_g‖w‖_{L^∞}`; the route below reaches `(64/27)C_g‖w‖_∞`,
which is proved first and then relaxed to the printed constant. -/

/-- **`|(r−1)φ| ≤ (64/27)C_g‖w‖_{L^∞}(Ah^⊥)²`** — Step 3's pointwise estimate, *quadratic* in
`Ah^⊥` rather than the `ε|Ah^⊥|` of Step 1.

The chain is `|r−1| · C_g|r−1| · (4/3)‖w‖_{L^∞}` with `|r−1| ≤ (4/3)|Ah^⊥|` used twice, so the
constant is `(4/3)³ = 64/27 ≈ 2.370`. The paper prints `4`; see
`abs_ratio_sub_one_mul_phi_sq_le_C6`. -/
theorem abs_ratio_sub_one_mul_phi_sq_le {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup eps : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    {y : V} (hy : lam y ≠ 0) :
    |(ratio K lam (fun x => 1 + h x) y - 1)
        * (gd (ratio K lam (fun x => 1 + h x) y) * (w y / (1 + h y)))|
      ≤ 64 / 27 * (Cg g2 a M3 * wsup) * Aop K lam (perpL2 lam h) y ^ 2 := by
  have heps4 : eps ≤ 1 / 4 := le_trans heps (by have := min_le_right a 1; linarith)
  have hden : 3 / 4 ≤ 1 + h y := one_add_ge_of_le hh heps4 y
  have hdpos : (0 : ℝ) < 1 + h y := by linarith
  have hwsup0 : 0 ≤ wsup := le_trans (abs_nonneg _) (hwsup y)
  set r : ℝ := ratio K lam (fun x => 1 + h x) y with hrdef
  set Ay : ℝ := Aop K lam (perpL2 lam h) y with hAdef
  have hra : |r - 1| ≤ a := abs_ratio_sub_one_le_a hKnn hinv hh heps0 heps hy
  have hCg0 : 0 ≤ Cg g2 a M3 := by
    have ha0 : 0 ≤ a := le_trans (abs_nonneg _) hra
    simp only [Cg]; positivity
  have hgd : |gd r| ≤ Cg g2 a M3 * |r - 1| := abs_gd_le_Cg hg2 hM3 htaylor (by simpa using hra)
  have hfrac : |w y / (1 + h y)| ≤ wsup * (4 / 3) := by
    rw [abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
    nlinarith [hwsup y, abs_nonneg (w y)]
  have h43 : |r - 1| ≤ 4 / 3 * |Ay| := abs_ratio_sub_one_le_four_thirds hinv hh heps4 hy
  have hsq : |r - 1| * |r - 1| ≤ (4 / 3 * |Ay|) * (4 / 3 * |Ay|) :=
    mul_self_le_mul_self (abs_nonneg _) h43
  have hCW : (0 : ℝ) ≤ 4 / 3 * (Cg g2 a M3 * wsup) :=
    mul_nonneg (by norm_num) (mul_nonneg hCg0 hwsup0)
  have hstep : |r - 1| * (|gd r| * |w y / (1 + h y)|)
      ≤ |r - 1| * (Cg g2 a M3 * |r - 1| * (wsup * (4 / 3))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hgd hfrac (abs_nonneg _) (by positivity))
      (abs_nonneg _)
  rw [abs_mul, abs_mul]
  calc |r - 1| * (|gd r| * |w y / (1 + h y)|)
      ≤ |r - 1| * (Cg g2 a M3 * |r - 1| * (wsup * (4 / 3))) := hstep
    _ = 4 / 3 * (Cg g2 a M3 * wsup) * (|r - 1| * |r - 1|) := by ring
    _ ≤ 4 / 3 * (Cg g2 a M3 * wsup) * ((4 / 3 * |Ay|) * (4 / 3 * |Ay|)) :=
        mul_le_mul_of_nonneg_left hsq hCW
    _ = 64 / 27 * (Cg g2 a M3 * wsup) * (|Ay| * |Ay|) := by ring
    _ = 64 / 27 * (Cg g2 a M3 * wsup) * Ay ^ 2 := by rw [abs_mul_abs_self]; ring

/-- **`|(r−1)φ| ≤ C₆(Ah^⊥)²` with the paper's `C₆ = 4C_g‖w‖_{L^∞}`** (`proofs.tex:641`), the
same estimate with the printed constant. -/
theorem abs_ratio_sub_one_mul_phi_sq_le_C6 {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup eps : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    {y : V} (hy : lam y ≠ 0) :
    |(ratio K lam (fun x => 1 + h x) y - 1)
        * (gd (ratio K lam (fun x => 1 + h x) y) * (w y / (1 + h y)))|
      ≤ C6 (Cg g2 a M3) wsup * Aop K lam (perpL2 lam h) y ^ 2 := by
  refine le_trans (abs_ratio_sub_one_mul_phi_sq_le hKnn hinv hg2 hM3 hwsup htaylor hh heps0
    heps hy) ?_
  have hCg0 : 0 ≤ Cg g2 a M3 := by simp only [Cg]; positivity
  have hA : (0 : ℝ) ≤ Aop K lam (perpL2 lam h) y ^ 2 := sq_nonneg _
  simp only [C6]
  nlinarith [mul_nonneg hCg0 hwsup0]

/-- **`|ṁ| ≤ C₆‖Ah^⊥‖²`** (`proofs.tex:641`), Step 3's estimate on the drift of the mass.

`MassIdentity.integral_gradDensity` turns `∫D dλ` into `∫(r−1)φ dλ` — the step the paper opens
with, and the only place `P†` preserving `λ`-integrals is spent — and the pointwise bound is
integrated against `λ`. -/
theorem abs_deriv_mean_le {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup eps : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4) :
    |Graph.meanL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + h z)|
      ≤ C6 (Cg g2 a M3) wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) ^ 2 := by
  have hinv' : Invariant K lam := invariant_of_isInvariant hinv
  set r : V → ℝ := ratio K lam (fun z => 1 + h z) with hr
  set phi : V → ℝ := fun x => gd (r x) * (w x / (1 + h x)) with hphi
  have hid : Graph.meanL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + h z)
      = ∑ x, lam x * (phi x * (1 - r x)) := by
    rw [lossGrad_of_weight hlam]
    simp only [Graph.meanL2, lossGradDensity, hphi, hr]
    exact integral_gradDensity hinv' _ _
  rw [hid]
  have hstep : ∀ x : V, |lam x * (phi x * (1 - r x))|
      ≤ lam x * (C6 (Cg g2 a M3) wsup * Aop K lam (perpL2 lam h) x ^ 2) := by
    intro x
    rw [abs_mul, abs_of_nonneg (hlam x).le]
    refine mul_le_mul_of_nonneg_left ?_ (hlam x).le
    have hneg : phi x * (1 - r x) = -((r x - 1) * phi x) := by ring
    rw [hneg, abs_neg]
    exact abs_ratio_sub_one_mul_phi_sq_le_C6 hKnn hinv hg2 hM3 ha0 hwsup0 hwsup htaylor hh
      heps0 heps (hlam x).ne'
  have hfin : (∑ x, lam x * (C6 (Cg g2 a M3) wsup * Aop K lam (perpL2 lam h) x ^ 2))
      = C6 (Cg g2 a M3) wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) ^ 2 := by
    rw [Graph.sq_nrmL2 fun x => (hlam x).le]
    simp only [Graph.ipL2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  calc |∑ x, lam x * (phi x * (1 - r x))|
      ≤ ∑ x, |lam x * (phi x * (1 - r x))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, lam x * (C6 (Cg g2 a M3) wsup * Aop K lam (perpL2 lam h) x ^ 2) :=
        Finset.sum_le_sum fun x _ => hstep x
    _ = C6 (Cg g2 a M3) wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) ^ 2 := hfin


/-! ### Step 3, integrated: the drift and the Cauchy estimate on the mass -/

/-- **`|m_{t₁} − m_{t₀}| ≤ C₆∫_{t₀}^{t₁}‖Ah^⊥‖²`** — Step 3's pointwise bound integrated.

Again not by the fundamental theorem applied to `ṁ`, which carries `g'`: the two functions
`τ ↦ C₆∫_{t₀}^τ‖Ah^⊥‖² ∓ m_τ` have non-negative derivative, hence are monotone, and only the
continuous integrand is integrated. -/
theorem abs_mean_sub_le_energy_integral {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ}
    {h : ℝ → V → ℝ} {g2 a M3 wsup eps T t₀ t₁ : ℝ}
    (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x) (hKnn : ∀ x y, 0 ≤ K x y)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ x, |h s x| ≤ eps)
    (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T) :
    |Graph.meanL2 lam (h t₁) - Graph.meanL2 lam (h t₀)|
      ≤ C6 (Cg g2 a M3) wsup
          * ∫ s in t₀..t₁, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2 := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  set c6 : ℝ := C6 (Cg g2 a M3) wsup with hc6
  set N : ℝ → ℝ := fun s => Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2 with hN
  have hNc : Continuous N := continuous_energy_flow hnn hflow
  set J : ℝ → ℝ := fun τ => ∫ s in t₀..τ, N s with hJ
  have hJd : ∀ τ : ℝ, HasDerivAt J (N τ) τ := fun τ =>
    intervalIntegral.integral_hasDerivAt_right (hNc.intervalIntegrable _ _)
      (hNc.stronglyMeasurableAtFilter _ _) hNc.continuousAt
  set Th : ℝ → ℝ := fun τ => Graph.meanL2 lam (h τ) with hTh
  set Dm : ℝ → ℝ := fun τ =>
    Graph.meanL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + h τ z) with hDm
  have hThd : ∀ τ : ℝ, HasDerivAt Th (-Dm τ) τ := fun τ => hasDerivAt_mean htot hflow τ
  have hbnd : ∀ τ ∈ Set.Icc t₀ t₁, |Dm τ| ≤ c6 * N τ := by
    intro τ hτ
    exact abs_deriv_mean_le hKnn hinv hlam hg2 hM3 ha0 hwsup0 hwsup htaylor
      (hwin τ ⟨le_trans h0 hτ.1, le_trans hτ.2 h1T⟩) heps0 heps
  have hd1 : ∀ τ : ℝ, HasDerivAt (fun z : ℝ => c6 * J z - Th z) (c6 * N τ - -Dm τ) τ :=
    fun τ => ((hJd τ).const_mul c6).sub (hThd τ)
  have hd2 : ∀ τ : ℝ, HasDerivAt (fun z : ℝ => c6 * J z + Th z) (c6 * N τ + -Dm τ) τ :=
    fun τ => ((hJd τ).const_mul c6).add (hThd τ)
  have hmono1 : MonotoneOn (fun τ => c6 * J τ - Th τ) (Set.Icc t₀ t₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun τ _ => (((hd1 τ)).continuousAt).continuousWithinAt)
      (fun τ _ => (((hd1 τ)).differentiableAt).differentiableWithinAt)
      (fun τ hτ => ?_)
    rw [(hd1 τ).deriv]
    rw [interior_Icc] at hτ
    have hb := hbnd τ (Set.Ioo_subset_Icc_self hτ)
    have h2 := (abs_le.mp hb).1
    linarith
  have hmono2 : MonotoneOn (fun τ => c6 * J τ + Th τ) (Set.Icc t₀ t₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun τ _ => (((hd2 τ)).continuousAt).continuousWithinAt)
      (fun τ _ => (((hd2 τ)).differentiableAt).differentiableWithinAt)
      (fun τ hτ => ?_)
    rw [(hd2 τ).deriv]
    rw [interior_Icc] at hτ
    have hb := hbnd τ (Set.Ioo_subset_Icc_self hτ)
    have h2 := (abs_le.mp hb).2
    linarith
  have e1 := hmono1 (Set.left_mem_Icc.2 h01) (Set.right_mem_Icc.2 h01) h01
  have e2 := hmono2 (Set.left_mem_Icc.2 h01) (Set.right_mem_Icc.2 h01) h01
  have hJ0 : J t₀ = 0 := intervalIntegral.integral_same
  simp only [hJ0, mul_zero, zero_sub, zero_add] at e1 e2
  rw [abs_le]
  constructor <;> linarith

/-- **`|m_t − m_0| ≤ C₇‖h_0^⊥‖²`** (`proofs.tex:641`), with `C₇ = C₆/(g''(1)w_min)`. -/
theorem mean_drift_on {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat eps T t : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat) (hgw : 0 < g2 * wmin)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ x, |h s x| ≤ eps) (ht : t ∈ Set.Icc (0:ℝ) T) :
    |Graph.meanL2 lam (h t) - Graph.meanL2 lam (h 0)|
      ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
  have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by simp only [C6, Cg]; positivity
  have hint := abs_mean_sub_le_energy_integral hinv hlam hK.nonneg htot hg2 hM3 ha0 hwsup0 hwsup
    htaylor heps0 heps hflow hwin le_rfl ht.1 ht.2
  have henergy := energy_integral_Icc hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin
    hB0 hcoer htaylor heps0 heps heps1 hflow hwin le_rfl ht.1 ht.2
  refine le_trans hint ?_
  have hJle : (∫ s in (0:ℝ)..t, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2)
      ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 / (g2 * wmin) := by
    rw [le_div_iff₀ hgw]
    linarith
  calc C6 (Cg g2 a M3) wsup
        * ∫ s in (0:ℝ)..t, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2
      ≤ C6 (Cg g2 a M3) wsup * (Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 / (g2 * wmin)) :=
        mul_le_mul_of_nonneg_left hJle hc60
    _ = C7 (C6 (Cg g2 a M3) wsup) g2 wmin * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
        simp only [C7]; ring

/-- **`|m_t − m_s| ≤ C₇e^{−ϱs}‖h_0^⊥‖²` — sharper than the paper's Step 3.**

`proofs.tex:641` states `|m_∞ − m_t| ≤ (4C₆/ϱ)e^{−ϱt}‖h_0^⊥‖²`, reached by bounding
`‖Ah^⊥‖² ≤ 4‖h^⊥‖²` and integrating the exponential. Restarting the *energy* estimate at time
`s` instead gives `C₇e^{−ϱs}‖h_0^⊥‖²`, and `4C₆/ϱ = 4B̂²C₇` with `B̂ ≥ 1` in the paper's setting,
so this is smaller by a factor `4B̂²`. The paper's version is `mean_cauchy_on`; this one is
recorded because `ε₀` of Step 4 is inversely proportional to that constant. -/
theorem mean_cauchy_on_sharp {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat eps T s t : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat) (hgw : 0 < g2 * wmin)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ x, |h r x| ≤ eps)
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    |Graph.meanL2 lam (h t) - Graph.meanL2 lam (h s)|
      ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin * Real.exp (-(rhoL g2 wmin Bhat * s))
          * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
  have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by simp only [C6, Cg]; positivity
  have hint := abs_mean_sub_le_energy_integral hinv hlam hK.nonneg htot hg2 hM3 ha0 hwsup0 hwsup
    htaylor heps0 heps hflow hwin hs0 hst htT
  have henergy := energy_integral_Icc hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin
    hB0 hcoer htaylor heps0 heps heps1 hflow hwin hs0 hst htT
  have hdecay := perp_decay_on hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin hB0 hcoer
    htaylor heps0 heps heps1 hflow hwin s ⟨hs0, le_trans hst htT⟩
  have hP0 : 0 ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) := Graph.nrmL2_nonneg _ _
  have hPs : 0 ≤ Graph.nrmL2 lam (perpL2 lam (h s)) := Graph.nrmL2_nonneg _ _
  have hsq : Graph.nrmL2 lam (perpL2 lam (h s)) ^ 2
      ≤ Real.exp (-(rhoL g2 wmin Bhat * s)) * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
    have hexp : Real.exp (-(rhoL g2 wmin Bhat * s / 2)) ^ 2
        = Real.exp (-(rhoL g2 wmin Bhat * s)) := by
      rw [sq, ← Real.exp_add]; ring_nf
    nlinarith [hdecay, hPs, hP0, Real.exp_nonneg (-(rhoL g2 wmin Bhat * s / 2))]
  refine le_trans hint ?_
  have hJle : (∫ r in s..t, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) ^ 2)
      ≤ (Real.exp (-(rhoL g2 wmin Bhat * s)) * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2)
          / (g2 * wmin) := by
    rw [le_div_iff₀ hgw]
    nlinarith [henergy, hsq]
  calc C6 (Cg g2 a M3) wsup
        * ∫ r in s..t, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) ^ 2
      ≤ C6 (Cg g2 a M3) wsup
          * ((Real.exp (-(rhoL g2 wmin Bhat * s))
              * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2) / (g2 * wmin)) :=
        mul_le_mul_of_nonneg_left hJle hc60
    _ = C7 (C6 (Cg g2 a M3) wsup) g2 wmin * Real.exp (-(rhoL g2 wmin Bhat * s))
          * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
        simp only [C7]; ring


/-- **`|m_t − m_s| ≤ (4C₆/ϱ)e^{−ϱs}‖h_0^⊥‖²`** (`proofs.tex:641`), the paper's Step 3 Cauchy
estimate, by the paper's route: `‖Ah^⊥‖² ≤ 4‖h^⊥‖²` and the exponential decay of `‖h^⊥‖`
integrated over `[s,t]`.

`mean_cauchy_on_sharp` is the same statement with `C₇` in place of `4C₆/ϱ = 4B̂²C₇`. -/
theorem mean_cauchy_on {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat eps T s t : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat)
    (hrho : 0 < rhoL g2 wmin Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ x, |h r x| ≤ eps)
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    |Graph.meanL2 lam (h t) - Graph.meanL2 lam (h s)|
      ≤ 4 * C6 (Cg g2 a M3) wsup / rhoL g2 wmin Bhat
          * Real.exp (-(rhoL g2 wmin Bhat * s)) * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
  have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by simp only [C6, Cg]; positivity
  have hP0 : 0 ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) := Graph.nrmL2_nonneg _ _
  have hint := abs_mean_sub_le_energy_integral hinv hlam hK.nonneg htot hg2 hM3 ha0 hwsup0 hwsup
    htaylor heps0 heps hflow hwin hs0 hst htT
  have hdecay := perp_decay_on hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin hB0 hcoer
    htaylor heps0 heps heps1 hflow hwin
  -- `∫_s^t‖Ah^⊥‖² ≤ 4‖h_0^⊥‖²e^{−ϱs}/ϱ`
  have hbig : (∫ r in s..t, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) ^ 2)
      ≤ 4 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
          * Real.exp (-(rhoL g2 wmin Bhat * s)) / rhoL g2 wmin Bhat := by
    have hMk : Core.IsMarkov K := hK.toIsMarkov hlam
    have hNc : Continuous fun r : ℝ => Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) ^ 2 :=
      continuous_energy_flow (fun x => (hlam x).le) hflow
    have hEc : Continuous fun r : ℝ => Real.exp (-(rhoL g2 wmin Bhat * r)) := by fun_prop
    have hgc : Continuous fun r : ℝ =>
        4 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
          * Real.exp (-(rhoL g2 wmin Bhat * r)) := continuous_const.mul hEc
    have hNle : ∀ r ∈ Set.Icc s t,
        Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) ^ 2
          ≤ 4 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
              * Real.exp (-(rhoL g2 wmin Bhat * r)) := by
      intro r hr
      have h2 := hdecay r ⟨le_trans hs0 hr.1, le_trans hr.2 htT⟩
      have h1 : Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r)))
          ≤ 2 * Graph.nrmL2 lam (perpL2 lam (h r)) := nrmL2_Aop_le_two hMk hinv _
      have h3 : (0:ℝ) ≤ Graph.nrmL2 lam (perpL2 lam (h r)) := Graph.nrmL2_nonneg _ _
      have h4 : (0:ℝ) ≤ Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) := Graph.nrmL2_nonneg _ _
      have h5 : (0:ℝ) ≤ Real.exp (-(rhoL g2 wmin Bhat * r / 2)) := (Real.exp_pos _).le
      have hexp : Real.exp (-(rhoL g2 wmin Bhat * r / 2)) ^ 2
          = Real.exp (-(rhoL g2 wmin Bhat * r)) := by
        rw [sq, ← Real.exp_add]; ring_nf
      calc Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) ^ 2
          ≤ (2 * Graph.nrmL2 lam (perpL2 lam (h r))) ^ 2 := by nlinarith
        _ ≤ (2 * (Real.exp (-(rhoL g2 wmin Bhat * r / 2))
              * Graph.nrmL2 lam (perpL2 lam (h 0)))) ^ 2 := by nlinarith
        _ = 4 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
              * Real.exp (-(rhoL g2 wmin Bhat * r)) := by rw [← hexp]; ring
    have hmono : (∫ r in s..t, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) ^ 2)
        ≤ ∫ r in s..t, 4 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
            * Real.exp (-(rhoL g2 wmin Bhat * r)) :=
      intervalIntegral.integral_mono_on hst (hNc.intervalIntegrable _ _)
        (hgc.intervalIntegrable _ _) hNle
    have hEint : (∫ r in s..t, Real.exp (-(rhoL g2 wmin Bhat * r)))
        = (Real.exp (-(rhoL g2 wmin Bhat * s)) - Real.exp (-(rhoL g2 wmin Bhat * t)))
            / rhoL g2 wmin Bhat := by
      have hG : ∀ r : ℝ, HasDerivAt
          (fun z : ℝ => -Real.exp (-(rhoL g2 wmin Bhat * z)) / rhoL g2 wmin Bhat)
          (Real.exp (-(rhoL g2 wmin Bhat * r))) r := by
        intro r
        have h1 : HasDerivAt (fun z : ℝ => -(rhoL g2 wmin Bhat * z))
            (-rhoL g2 wmin Bhat) r := by
          have hb : HasDerivAt (fun z : ℝ => rhoL g2 wmin Bhat * z)
              (rhoL g2 wmin Bhat * 1) r := (hasDerivAt_id' r).const_mul _
          rw [mul_one] at hb
          exact hb.neg
        have h3 := (h1.exp.neg).div_const (rhoL g2 wmin Bhat)
        have hval : -(Real.exp (-(rhoL g2 wmin Bhat * r)) * -rhoL g2 wmin Bhat)
            / rhoL g2 wmin Bhat = Real.exp (-(rhoL g2 wmin Bhat * r)) := by
          field_simp
        rwa [hval] at h3
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hG r)
        (hEc.intervalIntegrable _ _)]
      field_simp
      ring
    rw [intervalIntegral.integral_const_mul, hEint] at hmono
    refine le_trans hmono ?_
    have hEt : (0:ℝ) < Real.exp (-(rhoL g2 wmin Bhat * t)) := Real.exp_pos _
    have hkey : (0:ℝ) ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
        * (Real.exp (-(rhoL g2 wmin Bhat * t)) / rhoL g2 wmin Bhat) :=
      mul_nonneg (sq_nonneg _) (div_pos hEt hrho).le
    have hsplit : (Real.exp (-(rhoL g2 wmin Bhat * s)) - Real.exp (-(rhoL g2 wmin Bhat * t)))
        / rhoL g2 wmin Bhat
        = Real.exp (-(rhoL g2 wmin Bhat * s)) / rhoL g2 wmin Bhat
          - Real.exp (-(rhoL g2 wmin Bhat * t)) / rhoL g2 wmin Bhat := by ring
    rw [hsplit]
    have hgoal : 4 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
        * Real.exp (-(rhoL g2 wmin Bhat * s)) / rhoL g2 wmin Bhat
        = 4 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
          * (Real.exp (-(rhoL g2 wmin Bhat * s)) / rhoL g2 wmin Bhat) := by ring
    rw [hgoal]
    nlinarith [hkey]
  refine le_trans hint ?_
  calc C6 (Cg g2 a M3) wsup
        * ∫ r in s..t, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h r))) ^ 2
      ≤ C6 (Cg g2 a M3) wsup * (4 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
          * Real.exp (-(rhoL g2 wmin Bhat * s)) / rhoL g2 wmin Bhat) :=
        mul_le_mul_of_nonneg_left hbig hc60
    _ = 4 * C6 (Cg g2 a M3) wsup / rhoL g2 wmin Bhat
          * Real.exp (-(rhoL g2 wmin Bhat * s))
          * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
        field_simp


/-! ### One instance, computed

The two-state chain of `prop:nonlinear_freezing`*(2)* — `T(i→j) = 1/2`, `λ = (1/2,1/2)` — at
`h = (1/40, −1/40)`, `w ≡ 1`, `g(x) = (x−1)²` (so `g'(y) = 2(y−1)`, `g''(1) = 2`, `M₃ = 0`),
`a = 4/5`, `w_min = ‖w‖_{L^∞} = 1` and `B̂ = 1`.

**Computed by hand first**, off the paper's own displays and before any Lean ran. On this chain
`P` is the `λ`-average, so `Af = Πf − f = −f^⊥` and `B̂ = 1` is *exact*; `K = 2C₄ + C₅ = 80/3`
(`C₄ = 8`, `C_g = 2`, `C₅ = 32/3`), hence `ε₁ = g''(1)w_min/(2KB̂) = 2/(160/3) = 3/80`. The radius
`ε = 1/40 = 2/80` sits inside it — **`ε = 1/5`, the value `Expansion.twoState_expansion_check`
uses, does not**, which is what makes `ε₁` a real constraint and not decoration.

`Πh = 0`, so `h^⊥ = h` and `Ah^⊥ = (−1/40, 1/40)`, `‖Ah^⊥‖² = 1/1600`, and the left-hand side of
Step 2 is `(g''(1)w_min/2)‖Ah^⊥‖² = 1/1600`. On the right, `u = (41/40, 39/40)`,
`r = (40/41, 40/39)`, `φ = 2(r−1)/u = (−80/1681, 80/1521)`, `P†φ ≡ 6400/2556801`, so
`D = (6400/2556801 + 3200/68921, 6400/2556801 − 3200/59319)` and
`⟨h^⊥, D⟩ = (D₀ − D₁)/80 = 40(39³+41³)/(39·41)³ = 5129600/4088324799 ≈ 0.0012547`, against
`1/1600 = 0.000625`. The estimate is off by a factor `2.008`: at this radius the expansion error
is negligible and it is the paper's own halving that is being paid. -/

section TwoStateEnergy

/-- `h = (1/40, −1/40)`: mean zero, `L^∞` norm `1/40`, inside `ε₁ = 3/80`. -/
noncomputable def energyH : Fin 2 → ℝ := ![1 / 40, -(1 / 40)]

theorem energyH_abs_le : ∀ x, |energyH x| ≤ 1 / 40 := by
  intro x
  fin_cases x <;> norm_num [energyH]

/-- `Πh = 0`, so `h^⊥ = h`. -/
theorem twoState_perpL2_energyH : perpL2 twoStateLam energyH = energyH := by
  funext x
  have hm : Graph.meanL2 twoStateLam energyH = 0 := by
    simp only [Graph.meanL2, Fin.sum_univ_two]
    norm_num [twoStateLam, energyH]
  rw [perpL2_apply, hm, sub_zero]

/-- **`Af = −f^⊥` on the two-state chain**: `P` is the `λ`-average, so `A` is minus the
mean-zero projection. -/
theorem twoState_Aop_eq_neg_perp (f : Fin 2 → ℝ) :
    Aop twoStateK twoStateLam f = fun y => -(perpL2 twoStateLam f y) := by
  funext y
  fin_cases y <;>
    · simp only [Aop_apply, Core.densAct_apply, perpL2_apply, Graph.meanL2, Fin.sum_univ_two,
        twoStateK, twoStateLam]
      norm_num
      ring

/-- **`B̂ = 1` is exact here**: the coercivity hypothesis of Step 2, with equality. -/
theorem twoState_coercivity (f : Fin 2 → ℝ) :
    Graph.nrmL2 twoStateLam (perpL2 twoStateLam f)
      ≤ 1 * Graph.nrmL2 twoStateLam (Aop twoStateK twoStateLam f) := by
  rw [twoState_Aop_eq_neg_perp, nrmL2_neg, one_mul]

/-- **`(g''(1)w_min/2)‖Ah^⊥‖² = 1/1600`** on this instance. -/
theorem twoState_energy_lhs :
    (2 : ℝ) * 1 / 2 * Graph.nrmL2 twoStateLam
        (Aop twoStateK twoStateLam (perpL2 twoStateLam energyH)) ^ 2 = 1 / 1600 := by
  rw [twoState_perpL2_energyH, Graph.sq_nrmL2 fun x => (twoStateLam_pos x).le]
  simp only [Graph.ipL2, Fin.sum_univ_two, Aop_apply, Core.densAct_apply]
  norm_num [twoStateK, twoStateLam, energyH]

/-- **`⟨h^⊥, D⟩ = 5129600/4088324799`** on this instance — the number computed by hand in the
section preamble. -/
theorem twoState_energy_rhs :
    Graph.ipL2 twoStateLam (perpL2 twoStateLam energyH)
        (lossGrad twoStateK twoStateLam (fun z => twoStateLam z * 1) (fun z => 2 * (z - 1))
          fun z => 1 + energyH z)
      = 5129600 / 4088324799 := by
  rw [twoState_perpL2_energyH]
  simp only [Graph.ipL2, Fin.sum_univ_two, lossGrad, lossGradDensity, gradDensity, funAct,
    ratio, pushMass]
  norm_num [twoStateK, twoStateLam, energyH]

/-- **`energy_lower`, evaluated and checked against a hand computation.**

Three things at once: both sides are the numbers computed by hand, the theorem's hypotheses are
jointly satisfiable at `B̂ = 1`, `ε = 1/40 ≤ ε₁ = 3/80` (so nothing above is vacuous), and its
conclusion holds on this instance with a factor `2.008` to spare. A type-correct theorem about
the wrong object would still compile; this is what says the object is the paper's. -/
theorem twoState_energy_check :
    ((2 : ℝ) * 1 / 2 * Graph.nrmL2 twoStateLam
        (Aop twoStateK twoStateLam (perpL2 twoStateLam energyH)) ^ 2 = 1 / 1600)
      ∧ (Graph.ipL2 twoStateLam (perpL2 twoStateLam energyH)
          (lossGrad twoStateK twoStateLam (fun z => twoStateLam z * 1) (fun z => 2 * (z - 1))
            fun z => 1 + energyH z) = 5129600 / 4088324799)
      ∧ (1 : ℝ) / 1600 ≤ 5129600 / 4088324799 := by
  refine ⟨twoState_energy_lhs, twoState_energy_rhs, ?_⟩
  have hbound := energy_lower (K := twoStateK) (lam := twoStateLam) (w := fun _ => 1)
    (h := energyH) (gd := fun z => 2 * (z - 1)) (g2 := 2) (a := 4 / 5) (M3 := 0) (wsup := 1)
    (wmin := 1) (Bhat := 1) (eps := 1 / 40)
    twoState_isMarkovOn twoState_isInvariant twoStateLam_pos (by norm_num) le_rfl (by norm_num)
    (by norm_num) (fun _ => by norm_num) (by norm_num) (fun _ => le_rfl) (by norm_num)
    twoState_coercivity (fun y _ => by norm_num) energyH_abs_le (by norm_num) (by norm_num)
    (by norm_num [eps1, Kexp, C4, C5, Cg])
  rwa [twoState_energy_lhs, twoState_energy_rhs] at hbound

end TwoStateEnergy

end GFNBounds.Balance
