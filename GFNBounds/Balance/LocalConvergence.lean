import GFNBounds.Balance.LocalEnergy

/-!
# Steps 4 and 5 of the local convergence theorem, and its gradient-descent clause

**`theo:local_convergence_full`** — statement `proofs.tex:612–618`, proof `proofs.tex:620–657`;
**Steps 4, 5 and the discrete clause** (`proofs.tex:643–657`). Step 1 is
`GFNBounds/Balance/Expansion.lean`, Steps 2 and 3 are `GFNBounds/Balance/LocalEnergy.lean`, and
everything below rests on those two files and on `GFNBounds/Balance/L2Toolkit.lean`.
(The bold-backtick form of the label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (Step 4, continuation) Set `ε := min(min(a,1)/4, ε₁)` and
> `ε₀ := min(ε/(2C_∞(2+C₇)), ϱ/(4C₆), 1)`. If `‖h₀‖ ≤ ε₀`, then on any interval where
> `‖h_s‖_{L^∞} ≤ ε` the estimates above give
> `‖h_t‖_{L^∞} ≤ C_∞(|m_t| + ‖h_t^⊥‖) ≤ C_∞ε₀(2+C₇) ≤ ε/2`: by continuity the interval is all
> of `ℝ₊`, and Steps 1–3 hold globally in time.

> (Step 5, conclusion) With `c_∞ := 1 + m_∞`, `|c_∞ − 1 − Πh₀| ≤ C₇‖h₀^⊥‖²` and
> `‖h_t − (c_∞−1)‖ ≤ |m_∞ − m_t| + ‖h_t^⊥‖ ≤ e^{−ϱt/2}‖h₀^⊥‖(1 + (4C₆/ϱ)ε₀)
> ≤ 2e^{−ϱt/2}‖h₀^⊥‖`.

> (the discrete clause) For gradient descent, `eq:gradient_expansion` gives `‖D‖ ≤ L‖Ah^⊥‖` with
> `L := 2g''(1)‖w‖_{L^∞} + Kε ≤ 3g''(1)‖w‖_{L^∞}`; for `γ ≤ γ₀ := g''(1)w_min/(2L²)`,
> `‖h^⊥_{k+1}‖² ≤ ‖h^⊥_k‖² − γ(g''(1)w_min − γL²)‖Ah^⊥_k‖² ≤ (1 − γϱ/2)‖h^⊥_k‖²`, hence a
> contraction factor `≤ 1 − γϱ/4` on `‖h^⊥_k‖`; the drift and continuation arguments are
> identical, the per-step drift `γC₆‖Ah_k^⊥‖²` being summable by the telescoped energy
> inequality.

## Three findings, each of them load-bearing

1. **The theorem's `C ≥ 1` is never assigned by its proof.** Step 5 produces
   `C₇ = C₆/(g''(1)w_min)`, which can be smaller than `1` — on the two-state instance below it
   is `4`, but nothing in the hypotheses forces `C₇ ≥ 1`. The repair is `C := max(1, C₇)`; the
   Lean statement carries the sharper `C₇` and says so.
2. **"The drift and continuation arguments are identical" is false for the continuation, and
   the drift constant doubles.** In discrete time there is no continuity, so the first-failure
   argument of Step 4 does not run: a single step of size `γ‖D‖` can jump across the barrier
   `ε/2` that the flow has to cross continuously. What replaces it is an **induction** carrying
   the weaker invariant `‖h_k‖_{L^∞} ≤ ε` — enough, because that is all the per-step estimate
   consumes. And the discrete energy inequality retains `g''(1)w_min/2` where the flow's
   retains `g''(1)w_min`, the quadratic term `γ²‖D‖²` eating the other half, so the telescoped
   drift is `|m_k − m_0| ≤ 2C₇‖h_0^⊥‖²` and not `C₇‖h_0^⊥‖²`. **`ε₀` as printed still
   suffices**, with no change: `C_∞ε₀(2 + 2C₇) ≤ 2C_∞ε₀(2 + C₇) ≤ ε`.
3. **`L ≤ 3g''(1)‖w‖_{L^∞}` is valid but not sharp; `5/2` suffices** (`Lgd_le`), because
   `Kε ≤ g''(1)w_min/(2B̂) ≤ g''(1)‖w‖_{L^∞}/2` once `B̂ ≥ 1`. Nothing downstream uses either:
   `γ₀` is stated at the exact `L = 2g''(1)‖w‖_{L^∞} + Kε`, as the paper does. On the two-state
   instance `L = 5` and the sharper bound is **attained**.

The square-root step of the discrete clause — `‖h^⊥_{k+1}‖² ≤ (1−γϱ/2)‖h^⊥_k‖²` read as a
factor `1 − γϱ/4` on the norm — is **correct here**, `√(1−x) ≤ 1−x/2` being available at
`x = γϱ/2 ≤ 1/16` (`gamma_rho_le`). It is not the defect that `GFNBounds/Balance/Discrete.lean`
records in the superficially identical sentence of `theo:db_stable_frozen_full`, where the
printed factor is the one the energy method does *not* deliver.

## What is proved

| | |
|---|---|
| `Cinf`, `epsW`, `eps0`, `Lgd`, `gamma0` | the five constants, as the paper's printed formulas and not as `∃ C` (kb 0007). `Expansion.Kexp/C4/C5/Cg` and `LocalEnergy.eps1/C6/C7/rhoL` are reused |
| `one_le_Cinf`, `abs_le_Cinf_mul_nrmL2`, `abs_le_Cinf_mean_add_perp` | `C_∞ ≥ 1` — free, and used by Step 4 without being named — and the two sup bounds it buys |
| `nrmL2_const`, `meanL2_sub_smul`, `perpL2_sub_smul`, `sq_nrmL2_sub_smul`, `ipL2_perpL2_right` | the `L²` algebra of a descent step, which the toolkit did not carry |
| **`sup_bootstrap_step`** | **Step 4's inner estimate** (`proofs.tex:643`): the window on `[0,t]` and `‖h_0‖ ≤ ε₀` give `‖h_t‖_{L^∞} ≤ ε/2` |
| **`sup_global`** | **Step 4** (`proofs.tex:643`): the window is global, by `L2Toolkit.bootstrap_of_continuous`. Its `hstart` is the `t = 0` case, **which the paper does not state** |
| `tendsto_atTop_of_monotoneOn_Ici`, `tendsto_atTop_of_deriv_dominated` | the shape of Step 3's convergence argument with the flow removed: `A` grows, `B` drifts no faster, both bounded, so `B` converges |
| **`mean_tendsto`** | **Step 5's first half** (`proofs.tex:646`): `m_t → m_∞`, with `|m_∞ − m_0| ≤ C₇‖h_0^⊥‖²` and `|m_∞ − m_t| ≤ (4C₆/ϱ)e^{−ϱt}‖h_0^⊥‖²` |
| **`local_convergence_full`** | **the theorem** (`proofs.tex:612–618`): `∃ c_∞` with `\|c_∞ − 1 − Πh_0\| ≤ C₇‖h_0^⊥‖²` and `‖h_t − (c_∞−1)‖ ≤ 2e^{−ϱt/2}‖h_0^⊥‖` for all `t ≥ 0` |
| **`nrmL2_lossGrad_le`** | **`‖D‖ ≤ L‖Ah^⊥‖`** (`proofs.tex:654`), off `eq:gradient_expansion` |
| `Lgd_le` | `L ≤ (5/2)g''(1)‖w‖_{L^∞}`, sharper than the paper's `3`. See finding 3 |
| `gamma_mul_Lsq_le`, **`gamma_rho_le`** | `γ ≤ γ₀` is `γL² ≤ g''(1)w_min/2`; and `γϱ/2 ≤ 1/16`, which is what makes the square root legitimate |
| **`gd_energy_step`** | **the discrete energy inequality** (`proofs.tex:655`), with `g''(1)w_min/2` — half the flow's. See finding 2 |
| **`gd_contract_step`** | **`‖h^⊥_{k+1}‖ ≤ (1 − γϱ/4)‖h^⊥_k‖`** (`proofs.tex:656`) at one step |
| **`gd_drift_step`** | the discrete drift, telescoping: `\|m_{k+1} − m_k\| ≤ 2C₇(‖h^⊥_k‖² − ‖h^⊥_{k+1}‖²)` |
| **`local_convergence_gd`** | **the discrete clause** (`proofs.tex:653–657`): the contraction at **every** step, the window carried by induction |
| `twoState_*`, **`twoState_local_convergence_check`** | the five constants **evaluated**: `ε = 3/80`, `C_∞ = √2`, `C₇ = 4`, `ϱ = 2`, `ε₀ = √2/640`, `L = 5`, `γ₀ = 1/25`, `γ₀ϱ/2 = 1/25 ≤ 1/16`; `ε₀ > 0`, and `ε₀ < 1/40 < ε` |

## Hypothesis checklist — `theo:local_convergence_full`, Steps 4–5 and the discrete clause

| paper hypothesis | here |
|---|---|
| `T` ergodic with invariant `λ`; a general state space | ⚠ **weakened and restricted**, exactly as in `Expansion.lean` and `LocalEnergy.lean`: `Core.IsMarkovOn lam K`, `Core.IsInvariant lam K`, `λ > 0`, `∑λ = 1`, on a `Fintype`. Ergodicity is used nowhere; it is what makes `Πh` a scalar, and `Graph.meanL2` is that scalar by definition |
| `ν = wλ` with `w ∈ L^∞(λ)` | ✓ `nu = fun z => lam z * w z`, `hwsup : ∀ x, \|w x\| ≤ wsup` |
| `w ≥ w_min > 0` | ✓ `hwmin : ∀ x, wmin ≤ w x` with `hwmin0 : 0 < wmin`. `w_min ≤ ‖w‖_{L^∞}` is **derived**, not assumed, and `0 < ‖w‖_{L^∞}` with it — both need the state space non-empty, which `∑λ = 1` supplies (`nonempty_of_total`) |
| `g` is `C²` near `1` with `g(1)=g'(1)=0`, `g''(1)>0` | ⚠ **weakened to the consequence used**: only `g'` appears (as `gd`), and `hg2 : 0 < g2` replaces `g''(1) > 0`. `g'` is never assumed continuous |
| `g` is `C³` on `[1−a,1+a]`, `M₃` its third-derivative bound | ⚠ **weakened to the Taylor bound it is used through**, `htaylor`, as in `Expansion.lean`; `hM3 : 0 ≤ M3` replaces the supremum |
| `a ∈ (0,1)` | ⚠ **half-used**: `ha : 0 < a` is carried (it is what makes `ε > 0`, hence what lets the continuation start); **`a < 1` is never used**, `min(a,1)` absorbing it |
| `T` ergodic with summable `L²`-mixing, `B̂ := ∑β̂_n < ∞` | ⚠ **replaced by the finite hypothesis it produces**, `hcoer : ‖f^⊥‖ ≤ B̂‖Af‖`, as in `LocalEnergy.lean`; and ⚠ **`hB1 : 1 ≤ B̂` is added**. The paper has `β̂₀ = 1`, so `B̂ = ∑β̂_n ≥ 1` is true of its `B̂`, but it is nowhere stated and `LocalEnergy` carries only `0 ≤ B̂`. It is spent twice: on `ϱ > 0`, and on `γϱ/2 ≤ 1/16` in the discrete clause |
| `ϱ := g''(1)w_min/B̂²` | ✓ `LocalEnergy.rhoL`, the printed formula |
| `‖·‖_{L^∞(λ)} ≤ C_∞‖·‖_{L²(λ)}` with `C_∞ = (min λ)^{−1/2}` | ⚠ **a parameter `lamMin` with `0 < lamMin ≤ λ`**, not a minimum over a vertex set, and `Cinf lamMin := 1/√lamMin`; `L2Toolkit.abs_le_nrmL2_div_sqrt` is the bound. Same reading as `Lojasiewicz.lean`. `C_∞ ≥ 1` is **derived** (`one_le_Cinf`) |
| the flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` | ⚠ `IsGradientFlow K lam (λw) gd (fun s x => 1 + h s x)`, **hypothesised of a given curve**; no existence theorem, as in `Flow.lean` |
| "there are explicit `ε₀ > 0` and `C ≥ 1` depending only on `g''(1)`, `M₃`, `a`, `w_min`, `‖w‖_{L^∞}`, `B̂` and `C_∞`" | ⚠ `ε₀` is the printed formula and depends on exactly those; **`C` is `C₇`, and `C ≥ 1` is not delivered** — finding 1. `ε₀ > 0` is not a conjunct of the theorem here: it is `eps0_pos`, and `twoState_local_convergence_check` exhibits it |
| `‖h_0‖_{L²(λ)} ≤ ε₀` | ✓ `hnorm0` |
| Step 4's `ε := min(min(a,1)/4, ε₁)` and `ε₀ := min(…)` | ✓ `epsW`, `eps0`, printed formulas |
| "on any interval where `‖h_s‖ ≤ ε` … `≤ ε/2`" | ✓ `sup_bootstrap_step`. Four inequalities it uses without naming are supplied: `ε₀ ≤ 1`, `\|Πh_0\| ≤ ‖h_0‖`, `‖h_0^⊥‖ ≤ ‖h_0‖`, `C_∞ ≥ 1` |
| "by continuity the interval is all of `ℝ₊`" | ✓ `sup_global`, through `L2Toolkit.bootstrap_of_continuous`. ⚠ its `t = 0` base case **is not in the paper**; it holds, and is proved |
| "`m_t` converges to some `m_∞`" | ✓ `mean_tendsto` — the limit is *formed* here; `LocalEnergy` stops at the Cauchy estimate, which is what the paper writes |
| `\|c_∞ − 1 − Πh_0\| ≤ C‖h_0^⊥‖²` | ✓ with `C = C₇`; see finding 1 |
| `μ_t → c_∞λ`, "converges to a balanced flow" | ⚠ **read as the displayed estimate**, which is the only sense the proof gives it: `‖h_t − (c_∞−1)‖_{L²(λ)} → 0` geometrically. No separate topological statement about measures is made, and `c_∞λ` being *balanced* is `theo:first_variation_full`'s reading of `D`, disclosed in `FirstVariation.lean` |
| `‖h_t − (c_∞−1)‖ ≤ 2e^{−ϱt/2}‖h_0^⊥‖` | ✓ `local_convergence_full`, for every `t ≥ 0`, by the paper's route (the `4C₆/ϱ` constant, which is what `ε₀`'s second entry pairs with) |
| `‖D‖ ≤ L‖Ah^⊥‖`, `L := 2g''(1)‖w‖_{L^∞} + Kε` | ✓ `nrmL2_lossGrad_le`, printed constant |
| `L ≤ 3g''(1)‖w‖_{L^∞}` | ⚠ **valid, not sharp, and unused**: `5/2` is proved (`Lgd_le`), and `γ₀` is stated at the exact `L` |
| `γ ≤ γ₀ := g''(1)w_min/(2L²)` | ✓ `gamma0`, printed formula, plus `hgam0 : 0 ≤ γ`, which the paper leaves implicit in "step `γ`" |
| `‖h^⊥_{k+1}‖² ≤ (1 − γϱ/2)‖h^⊥_k‖²`, "hence `1 − γϱ/4`" | ✓ `gd_energy_step` and `gd_contract_step`. The square root is `L2Toolkit.sqrt_one_sub_le` and needs `γϱ/2 ≤ 1`, which `gamma_rho_le` supplies as `1/16` — an inequality the paper does not state |
| "the drift and continuation arguments are identical" | ⚠ **they are not** — finding 2. The continuation is an induction, the drift constant is `2C₇`, and both are proved rather than inherited |
| "the per-step drift `γC₆‖Ah_k^⊥‖²` being summable by the telescoped energy inequality" | ✓ `gd_drift_step`, in the telescoped form directly, so no series is ever formed |

## SCOPE (disclosed)

* **Finite state space**, as everywhere in `GFNBounds.Balance`: `∫·dλ` is `∑ x, lam x * ·`, and
  `⟪·∣·⟫_λ`, `‖·‖_λ`, `Π` are `Graph.ipL2`, `Graph.nrmL2`, `Graph.meanL2`. `paper-map.json`
  records `theo:local_convergence_full` as bucket `B`; nothing here moves it.
* **`hcoer` is a hypothesis, not `Core.Mixing`**, and `hB1 : 1 ≤ B̂` is an addition. See
  `LocalEnergy.lean`'s SCOPE for the first; the second is true of the paper's `B̂` and is not
  written there.
* **`C := max(1, C₇)`**: the theorem as printed promises a `C ≥ 1` and the proof supplies `C₇`.
  The Lean statement carries `C₇`, which is the stronger claim wherever `C₇ < 1` and the same
  claim otherwise. This is a paper finding, not a formalization gap.
* **The paper's `ε₀`, not the sharper one.** `LocalEnergy.mean_cauchy_on_sharp` would widen the
  basin by `4B̂²`, its constant being `C₇` against the paper's `4C₆/ϱ = 4B̂²C₇`. Step 5 below
  runs on the **paper's** constant, so `ε₀`'s second entry `ϱ/(4C₆)` is the one that pairs with
  it and the theorem is the paper's as printed. A second version off the sharp constant is not
  stated: it would change `ε₀`, hence the statement, and choosing the basin is the author's.
* **The discrete clause carries the window at `ε`, not at `ε/2`.** The flow needs the strict
  margin to run a first-failure argument; the induction does not, and could not get it —
  `2 + 2C₇` against `2(2 + C₇)` leaves room for `ε` and not for `ε/2`. What is proved is
  therefore the contraction at every step, which is the clause's own claim, and not a discrete
  analogue of `sup_global`'s `ε/2`.
* **`D` is `Flow.lossGrad`, which is a definition.** That it represents the gradient of
  `𝓛_{g,ν}` is `theo:first_variation_full`, disclosed in
  `GFNBounds/Balance/FirstVariation.lean`; nothing below re-derives it.
* **No existence theorem for the flow, and none for the descent sequence**: both are
  hypothesised, as `IsGradientFlow` and as `hstep`.
* **`sorry`-free and axiom-clean.** `#print axioms` on `sup_bootstrap_step`, `sup_global`,
  `mean_tendsto`, `local_convergence_full`, `nrmL2_lossGrad_le`, `Lgd_le`, `gamma_rho_le`,
  `gd_energy_step`, `gd_contract_step`, `gd_drift_step`, `local_convergence_gd`,
  `tendsto_atTop_of_deriv_dominated` and `twoState_local_convergence_check` returns
  `[propext, Classical.choice, Quot.sound]`. Graduated into the strict library on 2026-09-12.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### The five constants of Steps 4–5 and the discrete clause -/

/-- **`C_∞ := (min λ)^{−1/2}`** (`proofs.tex:613`), with `λ_min` a parameter. -/
noncomputable def Cinf (lamMin : ℝ) : ℝ := 1 / Real.sqrt lamMin

/-- **`ε := min(min(a,1)/4, ε₁)`** (`proofs.tex:643`), Step 4's window radius. -/
noncomputable def epsW (a g2 wmin Kexp Bhat : ℝ) : ℝ :=
  min (min a 1 / 4) (eps1 g2 wmin Kexp Bhat)

/-- **`ε₀ := min(ε/(2C_∞(2+C₇)), ϱ/(4C₆), 1)`** (`proofs.tex:643`), the basin radius. -/
noncomputable def eps0 (epsW Cinf C7 rhoL C6 : ℝ) : ℝ :=
  min (min (epsW / (2 * Cinf * (2 + C7))) (rhoL / (4 * C6))) 1

/-- **`L := 2g''(1)‖w‖_{L^∞} + Kε`** (`proofs.tex:654`). -/
noncomputable def Lgd (g2 wsup Kexp epsW : ℝ) : ℝ := 2 * g2 * wsup + Kexp * epsW

/-- **`γ₀ := g''(1)w_min/(2L²)`** (`proofs.tex:654`). -/
noncomputable def gamma0 (g2 wmin Lgd : ℝ) : ℝ := g2 * wmin / (2 * Lgd ^ 2)

/-! ### Algebra the `L²` toolkit does not carry -/

/-- The state space is non-empty as soon as `λ` is a probability. -/
theorem nonempty_of_total {lam : V → ℝ} (htot : ∑ x, lam x = 1) : Nonempty V := by
  by_contra hemp
  haveI : IsEmpty V := not_nonempty_iff.mp hemp
  rw [Finset.univ_eq_empty, Finset.sum_empty] at htot
  exact absurd htot (by norm_num)

/-- `‖c‖_{L²(λ)} = |c|` for a constant, `λ` being a probability. -/
theorem nrmL2_const {lam : V → ℝ} (htot : ∑ x, lam x = 1) (c : ℝ) :
    Graph.nrmL2 lam (fun _ => c) = |c| := by
  have h1 : Graph.ipL2 lam (fun _ => c) (fun _ => c) = c ^ 2 := by
    simp only [Graph.ipL2]
    rw [show (∑ _x : V, lam _x * (c * c)) = (∑ x, lam x) * (c * c) by rw [Finset.sum_mul], htot]
    ring
  simp only [Graph.nrmL2, h1, Real.sqrt_sq_eq_abs]

/-- `Π(a − cb) = Πa − cΠb`. -/
theorem meanL2_sub_smul (lam a b : V → ℝ) (c : ℝ) :
    Graph.meanL2 lam (fun x => a x - c * b x)
      = Graph.meanL2 lam a - c * Graph.meanL2 lam b := by
  simp only [Graph.meanL2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `(a − cb)^⊥ = a^⊥ − cb^⊥`. -/
theorem perpL2_sub_smul (lam a b : V → ℝ) (c : ℝ) :
    perpL2 lam (fun x => a x - c * b x) = fun x => perpL2 lam a x - c * perpL2 lam b x := by
  funext x
  simp only [perpL2_apply, meanL2_sub_smul]
  ring

/-- `‖a − cb‖² = ‖a‖² − 2c⟪a∣b⟫ + c²‖b‖²`. -/
theorem sq_nrmL2_sub_smul {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a b : V → ℝ) (c : ℝ) :
    Graph.nrmL2 lam (fun x => a x - c * b x) ^ 2
      = Graph.nrmL2 lam a ^ 2 - 2 * c * Graph.ipL2 lam a b + c ^ 2 * Graph.nrmL2 lam b ^ 2 := by
  rw [Graph.sq_nrmL2 hnn, Graph.sq_nrmL2 hnn, Graph.sq_nrmL2 hnn]
  simp only [Graph.ipL2, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `⟪a ∣ b^⊥⟫ = ⟪a ∣ b⟫` when `Πa = 0`. -/
theorem ipL2_perpL2_right {lam a : V → ℝ} (ha : Graph.meanL2 lam a = 0) (b : V → ℝ) :
    Graph.ipL2 lam a (perpL2 lam b) = Graph.ipL2 lam a b := by
  have hexp : ∀ x : V, lam x * (a x * perpL2 lam b x)
      = lam x * (a x * b x) - Graph.meanL2 lam b * (lam x * a x) := by
    intro x; rw [perpL2_apply]; ring
  simp only [Graph.ipL2]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  have h0 : (∑ x, lam x * a x) = 0 := ha
  rw [h0, mul_zero, sub_zero]

/-! ### `C_∞`, and the sup bound it buys -/

/-- **`C_∞ ≥ 1`** — free, and used by Step 4 without being named: applying the sup bound to a
constant gives `√λ_min ≤ 1`. -/
theorem one_le_Cinf {lam : V → ℝ} {lamMin : ℝ} (hlmin0 : 0 < lamMin)
    (hlmin : ∀ x, lamMin ≤ lam x) (htot : ∑ x, lam x = 1) : 1 ≤ Cinf lamMin := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hnn : ∀ x, 0 ≤ lam x := fun x => le_trans hlmin0.le (hlmin x)
  have hsingle : lam x0 ≤ ∑ x, lam x :=
    Finset.single_le_sum (f := lam) (fun i _ => hnn i) (Finset.mem_univ x0)
  have hle1 : lamMin ≤ 1 := by rw [htot] at hsingle; linarith [hlmin x0]
  have hs0 : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
  have hs1 : Real.sqrt lamMin ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hle1
  simp only [Cinf]
  rw [le_div_iff₀ hs0]
  linarith

theorem Cinf_pos {lamMin : ℝ} (hlmin0 : 0 < lamMin) : 0 < Cinf lamMin := by
  simp only [Cinf]
  exact div_pos one_pos (Real.sqrt_pos.mpr hlmin0)

/-- **`‖f‖_{L^∞} ≤ C_∞‖f‖_{L²(λ)}`** (`proofs.tex:613`), the hypothesis Step 4 spends. -/
theorem abs_le_Cinf_mul_nrmL2 {lam : V → ℝ} {lamMin : ℝ} (hlmin0 : 0 < lamMin)
    (hlmin : ∀ x, lamMin ≤ lam x) (f : V → ℝ) (x : V) :
    |f x| ≤ Cinf lamMin * Graph.nrmL2 lam f := by
  have hs0 : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
  have h1 := abs_le_nrmL2_div_sqrt hlmin0 hlmin f x
  have h2 : Cinf lamMin * Graph.nrmL2 lam f = Graph.nrmL2 lam f / Real.sqrt lamMin := by
    simp only [Cinf]; ring
  rw [h2, le_div_iff₀ hs0, mul_comm]
  exact h1

/-- **`‖f‖_{L^∞} ≤ C_∞(|Πf| + ‖f^⊥‖)`** — the split Step 4 reads the sup bound through. -/
theorem abs_le_Cinf_mean_add_perp {lam : V → ℝ} {lamMin : ℝ} (hlmin0 : 0 < lamMin)
    (hlmin : ∀ x, lamMin ≤ lam x) (htot : ∑ x, lam x = 1) (f : V → ℝ) (x : V) :
    |f x| ≤ Cinf lamMin * (|Graph.meanL2 lam f| + Graph.nrmL2 lam (perpL2 lam f)) := by
  have hC1 : 1 ≤ Cinf lamMin := one_le_Cinf hlmin0 hlmin htot
  have h1 : |perpL2 lam f x| ≤ Cinf lamMin * Graph.nrmL2 lam (perpL2 lam f) :=
    abs_le_Cinf_mul_nrmL2 hlmin0 hlmin _ x
  have h2 : f x = Graph.meanL2 lam f + perpL2 lam f x := by rw [perpL2_apply]; ring
  have h3 : |f x| ≤ |Graph.meanL2 lam f| + |perpL2 lam f x| := by
    rw [h2]; exact abs_add_le _ _
  have h4 : (0 : ℝ) ≤ |Graph.meanL2 lam f| := abs_nonneg _
  have h5 : |Graph.meanL2 lam f| ≤ Cinf lamMin * |Graph.meanL2 lam f| := by nlinarith
  linarith

/-! ### Positivity of the five constants -/

/-- `w_min > 0` forces `‖w‖_{L^∞} > 0`, read at one state — which a probability `λ` supplies
through `nonempty_of_total`. -/
theorem wsup_pos {wsup wmin wx : ℝ} (hwmin0 : 0 < wmin) (hwmin : wmin ≤ wx)
    (hwsup : |wx| ≤ wsup) : 0 < wsup := by
  have h1 : wx ≤ |wx| := le_abs_self _
  linarith

theorem Kexp_pos {g2 a M3 wsup : ℝ} (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a)
    (hwsup : 0 < wsup) : 0 < Kexp g2 a M3 wsup := by
  simp only [Kexp, C4, C5, Cg]
  nlinarith [mul_pos hg2 hwsup, mul_nonneg hM3 hwsup.le,
    mul_nonneg (mul_nonneg ha0 hM3) hwsup.le]

theorem epsW_nonneg {a g2 wmin Kex Bhat : ℝ} (ha0 : 0 ≤ a) (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin)
    (hK0 : 0 ≤ Kex) (hB0 : 0 ≤ Bhat) : 0 ≤ epsW a g2 wmin Kex Bhat := by
  refine le_min (div_nonneg (le_min ha0 zero_le_one) (by norm_num)) ?_
  exact div_nonneg (mul_nonneg hg2 hwmin0)
    (mul_nonneg (mul_nonneg (by norm_num) hK0) hB0)

theorem epsW_pos {a g2 wmin Kex Bhat : ℝ} (ha : 0 < a) (hg2 : 0 < g2) (hwmin0 : 0 < wmin)
    (hK0 : 0 < Kex) (hB0 : 0 < Bhat) : 0 < epsW a g2 wmin Kex Bhat := by
  refine lt_min (div_pos (lt_min ha one_pos) (by norm_num)) ?_
  exact div_pos (mul_pos hg2 hwmin0) (mul_pos (mul_pos two_pos hK0) hB0)

theorem epsW_le_window (a g2 wmin Kex Bhat : ℝ) : epsW a g2 wmin Kex Bhat ≤ min a 1 / 4 :=
  min_le_left _ _

theorem epsW_le_eps1 (a g2 wmin Kex Bhat : ℝ) :
    epsW a g2 wmin Kex Bhat ≤ eps1 g2 wmin Kex Bhat := min_le_right _ _

theorem C6_pos {g2 a M3 wsup : ℝ} (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a)
    (hwsup : 0 < wsup) : 0 < C6 (Cg g2 a M3) wsup := by
  simp only [C6, Cg]
  nlinarith [mul_pos hg2 hwsup, mul_nonneg (mul_nonneg ha0 hM3) hwsup.le]

theorem C7_nonneg {c6 g2 wmin : ℝ} (hc6 : 0 ≤ c6) (hgw : 0 ≤ g2 * wmin) :
    0 ≤ C7 c6 g2 wmin := div_nonneg hc6 hgw

theorem rhoL_pos {g2 wmin Bhat : ℝ} (hgw : 0 < g2 * wmin) (hB : 0 < Bhat) :
    0 < rhoL g2 wmin Bhat := div_pos hgw (by positivity)

theorem eps0_le_one (eW Ci c7 rho c6 : ℝ) : eps0 eW Ci c7 rho c6 ≤ 1 := min_le_right _ _

theorem eps0_le_basin (eW Ci c7 rho c6 : ℝ) :
    eps0 eW Ci c7 rho c6 ≤ eW / (2 * Ci * (2 + c7)) :=
  le_trans (min_le_left _ _) (min_le_left _ _)

theorem eps0_le_drift (eW Ci c7 rho c6 : ℝ) : eps0 eW Ci c7 rho c6 ≤ rho / (4 * c6) :=
  le_trans (min_le_left _ _) (min_le_right _ _)

theorem eps0_nonneg {eW Ci c7 rho c6 : ℝ} (heW : 0 ≤ eW) (hCi : 0 < Ci) (hc7 : 0 ≤ c7)
    (hrho : 0 ≤ rho) (hc6 : 0 ≤ c6) : 0 ≤ eps0 eW Ci c7 rho c6 := by
  refine le_min (le_min (div_nonneg heW ?_) (div_nonneg hrho (by linarith))) zero_le_one
  nlinarith

theorem eps0_pos {eW Ci c7 rho c6 : ℝ} (heW : 0 < eW) (hCi : 0 < Ci) (hc7 : 0 ≤ c7)
    (hrho : 0 < rho) (hc6 : 0 < c6) : 0 < eps0 eW Ci c7 rho c6 := by
  refine lt_min (lt_min (div_pos heW ?_) (div_pos hrho (by linarith))) one_pos
  nlinarith

/-! ### Step 4, the continuation -/

/-- **Step 4's inner estimate** (`proofs.tex:643`): on an interval where the window
`‖h_s‖_{L^∞} ≤ ε` holds, `‖h_0‖ ≤ ε₀` gives `‖h_t‖_{L^∞} ≤ C_∞(|m_t| + ‖h_t^⊥‖) ≤
C_∞ε₀(2+C₇) ≤ ε/2`.

Four inequalities the paper's sentence uses without naming: `ε₀ ≤ 1` (which is what turns
`C₇‖h_0^⊥‖²` into `C₇ε₀`), `|Πh_0| ≤ ‖h_0‖`, `‖h_0^⊥‖ ≤ ‖h_0‖` and `C_∞ ≥ 1`. The last is free
(`one_le_Cinf`); the first is the third entry of `ε₀`'s own `min`. -/
theorem sup_bootstrap_step {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat lamMin t : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hnorm0 : Graph.nrmL2 lam (h 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) (Cinf lamMin)
          (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup))
    (ht0 : 0 ≤ t)
    (hwin : ∀ s ∈ Set.Icc (0:ℝ) t, ∀ x, |h s x| ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) :
    ∀ x, |h t x| ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat / 2 := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hwsup0 : 0 ≤ wsup := (wsup_pos hwmin0 (hwmin x0) (hwsup x0)).le
  have hB0 : 0 ≤ Bhat := le_trans zero_le_one hB1
  have hgw : 0 < g2 * wmin := mul_pos hg2 hwmin0
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2.le hM3 ha0 hwsup0
  have hew0 : 0 ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat :=
    epsW_nonneg ha0 hg2.le hwmin0.le hK0 hB0
  have hewA := epsW_le_window a g2 wmin (Kexp g2 a M3 wsup) Bhat
  have hewB := epsW_le_eps1 a g2 wmin (Kexp g2 a M3 wsup) Bhat
  have hc70 : 0 ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin := by
    simp only [C7, C6, Cg]; positivity
  have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by simp only [C6, Cg]; positivity
  have hrho0 : 0 ≤ rhoL g2 wmin Bhat := rhoL_nonneg hg2.le hwmin0.le
  have hCi1 : 1 ≤ Cinf lamMin := one_le_Cinf hlmin0 hlmin htot
  have hCi0 : 0 < Cinf lamMin := Cinf_pos hlmin0
  -- the two estimates of Steps 2 and 3, read on the window `[0,t]`
  have hdrift := mean_drift_on hK hinv hlam htot hg2.le hM3 ha0 hwsup0 hwsup hwmin0.le hwmin
    hB0 hgw hcoer htaylor hew0 hewA hewB hflow hwin (Set.mem_Icc.mpr ⟨ht0, le_rfl⟩)
  have hdecay := perp_decay_on hK hinv hlam htot hg2.le hM3 ha0 hwsup0 hwsup hwmin0.le hwmin
    hB0 hcoer htaylor hew0 hewA hewB hflow hwin t (Set.mem_Icc.mpr ⟨ht0, le_rfl⟩)
  set eW := epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat with heWdef
  set c7 := C7 (C6 (Cg g2 a M3) wsup) g2 wmin with hc7def
  set Ci := Cinf lamMin with hCidef
  set e0 := eps0 eW Ci c7 (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup) with he0def
  have he0A : e0 ≤ eW / (2 * Ci * (2 + c7)) := eps0_le_basin _ _ _ _ _
  have he01 : e0 ≤ 1 := eps0_le_one _ _ _ _ _
  have he00 : 0 ≤ e0 := eps0_nonneg hew0 hCi0 hc70 hrho0 hc60
  -- `‖h_0^⊥‖ ≤ ‖h_0‖ ≤ ε₀` and `|Πh_0| ≤ ‖h_0‖ ≤ ε₀`
  have hP0 : Graph.nrmL2 lam (perpL2 lam (h 0)) ≤ Graph.nrmL2 lam (h 0) :=
    nrmL2_perpL2_le hnn htot (h 0)
  have hm0 : |Graph.meanL2 lam (h 0)| ≤ Graph.nrmL2 lam (h 0) :=
    abs_meanL2_le_nrmL2 hnn htot (h 0)
  have hPe : Graph.nrmL2 lam (perpL2 lam (h 0)) ≤ e0 := le_trans hP0 hnorm0
  have hP0nn : 0 ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) := Graph.nrmL2_nonneg _ _
  have hsq0 : Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 ≤ e0 := by nlinarith
  -- `‖h_t^⊥‖ ≤ ‖h_0^⊥‖`, the exponential being at most `1`
  have hexp1 : Real.exp (-(rhoL g2 wmin Bhat * t / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hPt : Graph.nrmL2 lam (perpL2 lam (h t)) ≤ Graph.nrmL2 lam (perpL2 lam (h 0)) := by
    refine le_trans hdecay ?_
    nlinarith [Real.exp_nonneg (-(rhoL g2 wmin Bhat * t / 2))]
  -- `|m_t| ≤ |m_0| + C₇‖h_0^⊥‖² ≤ ε₀ + C₇ε₀`
  have hmt : |Graph.meanL2 lam (h t)| ≤ e0 + c7 * e0 := by
    have h1 : |Graph.meanL2 lam (h t)| - |Graph.meanL2 lam (h 0)|
        ≤ |Graph.meanL2 lam (h t) - Graph.meanL2 lam (h 0)| := abs_sub_abs_le_abs_sub _ _
    have h2 : c7 * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 ≤ c7 * e0 :=
      mul_le_mul_of_nonneg_left hsq0 hc70
    linarith
  intro x
  have hsplit := abs_le_Cinf_mean_add_perp hlmin0 hlmin htot (h t) x
  have hsum : |Graph.meanL2 lam (h t)| + Graph.nrmL2 lam (perpL2 lam (h t))
      ≤ e0 * (2 + c7) := by nlinarith
  have hpos : (0 : ℝ) < 2 * Ci * (2 + c7) := by nlinarith
  have hkey : e0 * (2 * Ci * (2 + c7)) ≤ eW := (le_div_iff₀ hpos).mp he0A
  calc |h t x| ≤ Ci * (|Graph.meanL2 lam (h t)| + Graph.nrmL2 lam (perpL2 lam (h t))) := hsplit
    _ ≤ Ci * (e0 * (2 + c7)) := mul_le_mul_of_nonneg_left hsum hCi0.le
    _ ≤ eW / 2 := by nlinarith

/-- **Step 4** (`proofs.tex:643`): `‖h_0‖ ≤ ε₀` makes the window global — `‖h_t‖_{L^∞} ≤ ε/2`
for every `t ≥ 0`, so Steps 1–3 hold on all of `ℝ₊`.

`L2Toolkit.bootstrap_of_continuous` is the continuation argument; `sup_bootstrap_step` is its
`hboot`, and its `hstart` is the `t = 0` case, **which the paper's Step 4 does not state**. It
holds for the same reason and by a shorter route: `‖h_0‖_{L^∞} ≤ C_∞‖h_0‖ ≤ C_∞ε₀ ≤ ε/4`. -/
theorem sup_global {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat lamMin : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hnorm0 : Graph.nrmL2 lam (h 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) (Cinf lamMin)
          (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup)) :
    ∀ t : ℝ, 0 ≤ t → ∀ x, |h t x| ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat / 2 := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hwsupp : 0 < wsup := wsup_pos hwmin0 (hwmin x0) (hwsup x0)
  have hBpos : (0 : ℝ) < Bhat := lt_of_lt_of_le zero_lt_one hB1
  have hepsWpos : 0 < epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat :=
    epsW_pos ha hg2 hwmin0 (Kexp_pos hg2 hM3 ha.le hwsupp) hBpos
  refine bootstrap_of_continuous hepsWpos (fun x => continuous_flowDev hflow x) ?_ ?_
  · -- the `t = 0` base case, unstated in the paper
    intro x
    have hc70 : 0 ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin := by
      have hwsup0 : 0 ≤ wsup := hwsupp.le
      have ha0 : 0 ≤ a := ha.le
      simp only [C7, C6, Cg]; positivity
    have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by
      have hwsup0 : 0 ≤ wsup := hwsupp.le
      have ha0 : 0 ≤ a := ha.le
      simp only [C6, Cg]; positivity
    have hrho0 : 0 ≤ rhoL g2 wmin Bhat := rhoL_nonneg hg2.le hwmin0.le
    have hCi0 : 0 < Cinf lamMin := Cinf_pos hlmin0
    set eW := epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat with heWdef
    set c7 := C7 (C6 (Cg g2 a M3) wsup) g2 wmin with hc7def
    set Ci := Cinf lamMin with hCidef
    set e0 := eps0 eW Ci c7 (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup) with he0def
    have he00 : 0 ≤ e0 := eps0_nonneg hepsWpos.le hCi0 hc70 hrho0 hc60
    have hpos : (0 : ℝ) < 2 * Ci * (2 + c7) := by nlinarith
    have hkey : e0 * (2 * Ci * (2 + c7)) ≤ eW :=
      (le_div_iff₀ hpos).mp (eps0_le_basin eW Ci c7 (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup))
    have h1 : |h 0 x| ≤ Ci * Graph.nrmL2 lam (h 0) := abs_le_Cinf_mul_nrmL2 hlmin0 hlmin _ x
    have h2 : Ci * Graph.nrmL2 lam (h 0) ≤ Ci * e0 := mul_le_mul_of_nonneg_left hnorm0 hCi0.le
    have h3 : 0 ≤ Ci * e0 * c7 := by positivity
    linarith
  · intro t ht hwin
    exact sup_bootstrap_step hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha.le hwsup hwmin0 hwmin
      hB1 hcoer htaylor hflow hnorm0 ht hwin

/-! ### Step 5, the limit of the mass

The paper says "`m_t` converges to some `m_∞`" and moves on. The convergence is a **Cauchy**
statement, and `ℝ` being complete is not by itself enough to run it against the filter `atTop`
without producing the limit; the two functions `C₆∫_0^τ‖Ah^⊥‖² ∓ m_τ` of Step 3's proof are
monotone and bounded, so the limit is a supremum and no Cauchy machinery is needed. -/

/-- A function that is monotone on `[0,∞)` and bounded above there converges at `+∞`.
`Mathlib.tendsto_atTop_ciSup` wants **global** monotonicity; `τ ↦ f(max 0 τ)` supplies it and
agrees with `f` eventually. -/
theorem tendsto_atTop_of_monotoneOn_Ici {f : ℝ → ℝ} {C : ℝ}
    (hmono : MonotoneOn f (Set.Ici (0:ℝ))) (hbd : ∀ τ : ℝ, 0 ≤ τ → f τ ≤ C) :
    ∃ l : ℝ, Filter.Tendsto f Filter.atTop (nhds l) := by
  have hgmono : Monotone fun τ : ℝ => f (max 0 τ) := fun p q hpq =>
    hmono (Set.mem_Ici.mpr (le_max_left 0 p)) (Set.mem_Ici.mpr (le_max_left 0 q))
      (max_le_max le_rfl hpq)
  have hgbdd : BddAbove (Set.range fun τ : ℝ => f (max 0 τ)) := by
    refine ⟨C, ?_⟩
    rintro y ⟨τ, rfl⟩
    exact hbd _ (le_max_left 0 τ)
  refine ⟨⨆ i : ℝ, f (max 0 i), Filter.Tendsto.congr' ?_ (tendsto_atTop_ciSup hgmono hgbdd)⟩
  exact Filter.eventually_atTop.2 ⟨0, fun τ hτ => by simp only [max_eq_right hτ]⟩

/-- **The shape of Step 3's convergence argument, with the flow removed.** `A` grows, `B` drifts
no faster than `A` grows, both are bounded on `[0,∞)`: then `B` converges at `+∞`, because
`A ± B` are monotone and bounded and `B = ((A+B) − (A−B))/2`. -/
theorem tendsto_atTop_of_deriv_dominated {A B b beta : ℝ → ℝ} {CA CB : ℝ}
    (hA : ∀ τ : ℝ, HasDerivAt A (b τ) τ) (hB : ∀ τ : ℝ, HasDerivAt B (beta τ) τ)
    (hdom : ∀ τ : ℝ, 0 ≤ τ → |beta τ| ≤ b τ)
    (hAbd : ∀ τ : ℝ, 0 ≤ τ → A τ ≤ CA) (hBbd : ∀ τ : ℝ, 0 ≤ τ → |B τ| ≤ CB) :
    ∃ l : ℝ, Filter.Tendsto B Filter.atTop (nhds l) := by
  have hd1 : ∀ τ : ℝ, HasDerivAt (fun z => A z - B z) (b τ - beta τ) τ :=
    fun τ => (hA τ).sub (hB τ)
  have hd2 : ∀ τ : ℝ, HasDerivAt (fun z => A z + B z) (b τ + beta τ) τ :=
    fun τ => (hA τ).add (hB τ)
  have hm1 : MonotoneOn (fun τ => A τ - B τ) (Set.Ici (0:ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun τ _ => ((hd1 τ).continuousAt).continuousWithinAt)
      (fun τ _ => ((hd1 τ).differentiableAt).differentiableWithinAt) (fun τ hτ => ?_)
    rw [(hd1 τ).deriv]
    rw [interior_Ici] at hτ
    have hb := abs_le.mp (hdom τ (Set.mem_Ioi.mp hτ).le)
    linarith [hb.2]
  have hm2 : MonotoneOn (fun τ => A τ + B τ) (Set.Ici (0:ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun τ _ => ((hd2 τ).continuousAt).continuousWithinAt)
      (fun τ _ => ((hd2 τ).differentiableAt).differentiableWithinAt) (fun τ hτ => ?_)
    rw [(hd2 τ).deriv]
    rw [interior_Ici] at hτ
    have hb := abs_le.mp (hdom τ (Set.mem_Ioi.mp hτ).le)
    linarith [hb.1]
  obtain ⟨l1, hl1⟩ := tendsto_atTop_of_monotoneOn_Ici (C := CA + CB) hm1 (fun τ hτ => by
    have h1 := hAbd τ hτ
    have h2 := abs_le.mp (hBbd τ hτ)
    linarith [h2.1])
  obtain ⟨l2, hl2⟩ := tendsto_atTop_of_monotoneOn_Ici (C := CA + CB) hm2 (fun τ hτ => by
    have h1 := hAbd τ hτ
    have h2 := abs_le.mp (hBbd τ hτ)
    linarith [h2.2])
  refine ⟨(l2 - l1) / 2, Filter.Tendsto.congr (fun τ => ?_) ((hl2.sub hl1).div_const 2)⟩
  ring

/-- **Step 5's first half** (`proofs.tex:641`, `:646`): under the global window, `m_t = Πh_t`
converges to some `m_∞`, with `|m_∞ − m_0| ≤ C₇‖h_0^⊥‖²` and
`|m_∞ − m_t| ≤ (4C₆/ϱ)e^{−ϱt}‖h_0^⊥‖²`.

The limit is *formed* here — `LocalEnergy` stops at the Cauchy estimate between two finite
times, which is what the paper writes. Both displayed bounds are that estimate passed to the
limit, `le_of_tendsto` against the eventual bound. -/
theorem mean_tendsto {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat eps : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat) (hgw : 0 < g2 * wmin)
    (hrho : 0 < rhoL g2 wmin Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hwin : ∀ s : ℝ, 0 ≤ s → ∀ x, |h s x| ≤ eps) :
    ∃ minf : ℝ, Filter.Tendsto (fun t => Graph.meanL2 lam (h t)) Filter.atTop (nhds minf)
      ∧ |minf - Graph.meanL2 lam (h 0)|
          ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
      ∧ ∀ t : ℝ, 0 ≤ t → |minf - Graph.meanL2 lam (h t)|
          ≤ 4 * C6 (Cg g2 a M3) wsup / rhoL g2 wmin Bhat
              * Real.exp (-(rhoL g2 wmin Bhat * t)) * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by simp only [C6, Cg]; positivity
  have hNc : Continuous fun s : ℝ => Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2 :=
    continuous_energy_flow hnn hflow
  -- the primitive of the energy, scaled by `C₆`, and the mass
  have hA : ∀ τ : ℝ, HasDerivAt
      (fun z : ℝ => C6 (Cg g2 a M3) wsup
        * ∫ s in (0:ℝ)..z, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2)
      (C6 (Cg g2 a M3) wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam (h τ))) ^ 2) τ :=
    fun τ => (intervalIntegral.integral_hasDerivAt_right (hNc.intervalIntegrable _ _)
      (hNc.stronglyMeasurableAtFilter _ _) hNc.continuousAt).const_mul _
  have hB : ∀ τ : ℝ, HasDerivAt (fun z : ℝ => Graph.meanL2 lam (h z))
      (-Graph.meanL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + h τ z)) τ :=
    fun τ => hasDerivAt_mean htot hflow τ
  have hdom : ∀ τ : ℝ, 0 ≤ τ →
      |(-Graph.meanL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + h τ z))|
        ≤ C6 (Cg g2 a M3) wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam (h τ))) ^ 2 := by
    intro τ hτ
    rw [abs_neg]
    exact abs_deriv_mean_le hK.nonneg hinv hlam hg2 hM3 ha0 hwsup0 hwsup htaylor (hwin τ hτ)
      heps0 heps
  have hAbd : ∀ τ : ℝ, 0 ≤ τ → C6 (Cg g2 a M3) wsup
      * (∫ s in (0:ℝ)..τ, Graph.nrmL2 lam (Aop K lam (perpL2 lam (h s))) ^ 2)
      ≤ C6 (Cg g2 a M3) wsup * (Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 / (g2 * wmin)) := by
    intro τ hτ
    refine mul_le_mul_of_nonneg_left ?_ hc60
    rw [le_div_iff₀ hgw]
    have := energy_integral_on (T := τ) hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin
      hB0 hcoer htaylor heps0 heps heps1 hflow (fun s hs => hwin s hs.1) hτ
    linarith
  have hdrift : ∀ τ : ℝ, 0 ≤ τ → |Graph.meanL2 lam (h τ) - Graph.meanL2 lam (h 0)|
      ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
    intro τ hτ
    exact mean_drift_on (T := τ) (t := τ) hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0
      hwmin hB0 hgw hcoer htaylor heps0 heps heps1 hflow (fun s hs => hwin s hs.1)
      (Set.mem_Icc.mpr ⟨hτ, le_rfl⟩)
  have hBbd : ∀ τ : ℝ, 0 ≤ τ → |Graph.meanL2 lam (h τ)|
      ≤ |Graph.meanL2 lam (h 0)| + C7 (C6 (Cg g2 a M3) wsup) g2 wmin
          * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2 := by
    intro τ hτ
    have h1 : |Graph.meanL2 lam (h τ)| - |Graph.meanL2 lam (h 0)|
        ≤ |Graph.meanL2 lam (h τ) - Graph.meanL2 lam (h 0)| := abs_sub_abs_le_abs_sub _ _
    linarith [hdrift τ hτ]
  obtain ⟨minf, hlim⟩ := tendsto_atTop_of_deriv_dominated hA hB hdom hAbd hBbd
  refine ⟨minf, hlim, ?_, ?_⟩
  · have habs : Filter.Tendsto (fun s : ℝ => |Graph.meanL2 lam (h s) - Graph.meanL2 lam (h 0)|)
        Filter.atTop (nhds |minf - Graph.meanL2 lam (h 0)|) :=
      (hlim.sub_const _).abs
    exact le_of_tendsto habs (Filter.eventually_atTop.2 ⟨0, fun s hs => hdrift s hs⟩)
  · intro t ht
    have habs : Filter.Tendsto (fun s : ℝ => |Graph.meanL2 lam (h s) - Graph.meanL2 lam (h t)|)
        Filter.atTop (nhds |minf - Graph.meanL2 lam (h t)|) :=
      (hlim.sub_const _).abs
    refine le_of_tendsto habs (Filter.eventually_atTop.2 ⟨t, fun s hs => ?_⟩)
    exact mean_cauchy_on (T := s) (s := t) (t := s) hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup
      hwmin0 hwmin hB0 hrho hcoer htaylor heps0 heps heps1 hflow
      (fun r hr => hwin r hr.1) ht hs le_rfl

/-! ### The theorem -/

/-- **`theo:local_convergence_full`, Steps 4 and 5** (`proofs.tex:612–618`, proof `:643–652`):
from `‖h_0‖ ≤ ε₀` the nonlinear gradient flow converges to a balanced flow `c_∞λ`, with
`|c_∞ − 1 − Πh_0| ≤ C₇‖h_0^⊥‖²` and
`‖h_t − (c_∞−1)‖ ≤ 2e^{−ϱt/2}‖h_0^⊥‖` for every `t ≥ 0`.

The theorem's `C ≥ 1` is **not** what the proof produces: the proof produces `C₇`, which may be
smaller than `1`. The statement here carries `C₇`; `C := max(1, C₇)` is the repair on the paper
side, and it weakens nothing. -/
theorem local_convergence_full {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
    {g2 a M3 wsup wmin Bhat lamMin : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hnorm0 : Graph.nrmL2 lam (h 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) (Cinf lamMin)
          (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup)) :
    ∃ cinf : ℝ,
      |cinf - 1 - Graph.meanL2 lam (h 0)|
          ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (fun x => h t x - (cinf - 1))
            ≤ 2 * Real.exp (-(rhoL g2 wmin Bhat * t / 2))
                * Graph.nrmL2 lam (perpL2 lam (h 0)) := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have ha0 : 0 ≤ a := ha.le
  have hwsupp : 0 < wsup := wsup_pos hwmin0 (hwmin x0) (hwsup x0)
  have hwsup0 : 0 ≤ wsup := hwsupp.le
  have hB0 : 0 ≤ Bhat := le_trans zero_le_one hB1
  have hBpos : (0 : ℝ) < Bhat := lt_of_lt_of_le zero_lt_one hB1
  have hgw : 0 < g2 * wmin := mul_pos hg2 hwmin0
  have hrho : 0 < rhoL g2 wmin Bhat := rhoL_pos hgw hBpos
  have hc6p : 0 < C6 (Cg g2 a M3) wsup := C6_pos hg2 hM3 ha0 hwsupp
  have hc70 : 0 ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin := by simp only [C7, C6, Cg]; positivity
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2.le hM3 ha0 hwsup0
  have hew0 : 0 ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat :=
    epsW_nonneg ha0 hg2.le hwmin0.le hK0 hB0
  -- Step 4: the window is global
  have hsup := sup_global hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha hwsup hwmin0 hwmin hB1
    hcoer htaylor hflow hnorm0
  have hwinG : ∀ s : ℝ, 0 ≤ s → ∀ x, |h s x| ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat := by
    intro s hs x
    linarith [hsup s hs x]
  -- Step 5: the mass converges
  obtain ⟨minf, hlim, hm0, hmt⟩ := mean_tendsto hK hinv hlam htot hg2.le hM3 ha0 hwsup0 hwsup
    hwmin0.le hwmin hB0 hgw hrho hcoer htaylor hew0
    (epsW_le_window a g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (epsW_le_eps1 a g2 wmin (Kexp g2 a M3 wsup) Bhat) hflow hwinG
  refine ⟨1 + minf, ?_, ?_⟩
  · have hrw : (1 : ℝ) + minf - 1 - Graph.meanL2 lam (h 0) = minf - Graph.meanL2 lam (h 0) := by
      ring
    rw [hrw]
    exact hm0
  · intro t ht
    set P0 := Graph.nrmL2 lam (perpL2 lam (h 0)) with hP0def
    set E := Real.exp (-(rhoL g2 wmin Bhat * t / 2)) with hEdef
    set Q := 4 * C6 (Cg g2 a M3) wsup / rhoL g2 wmin Bhat with hQdef
    set e0 := eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) (Cinf lamMin)
      (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup) with he0def
    have hP0nn : 0 ≤ P0 := Graph.nrmL2_nonneg _ _
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hrho.le])
    have hQpos : 0 < Q := by rw [hQdef]; positivity
    have hP0e0 : P0 ≤ e0 := le_trans (nrmL2_perpL2_le hnn htot (h 0)) hnorm0
    have hQe0 : Q * e0 ≤ 1 := by
      have h1 : e0 * (4 * C6 (Cg g2 a M3) wsup) ≤ rhoL g2 wmin Bhat :=
        (le_div_iff₀ (by positivity)).mp (eps0_le_drift _ _ _ _ _)
      rw [hQdef, div_mul_eq_mul_div, div_le_one hrho]
      linarith
    -- the two estimates at time `t`
    have hdecay := perp_decay_on (T := t) hK hinv hlam htot hg2.le hM3 ha0 hwsup0 hwsup
      hwmin0.le hwmin hB0 hcoer htaylor hew0
      (epsW_le_window a g2 wmin (Kexp g2 a M3 wsup) Bhat)
      (epsW_le_eps1 a g2 wmin (Kexp g2 a M3 wsup) Bhat) hflow
      (fun s hs => hwinG s hs.1) t (Set.mem_Icc.mpr ⟨ht, le_rfl⟩)
    have hcau := hmt t ht
    have hEsq : Real.exp (-(rhoL g2 wmin Bhat * t)) = E ^ 2 := by
      rw [hEdef, sq, ← Real.exp_add]; ring_nf
    rw [hEsq] at hcau
    -- `‖h_t − m_∞‖ ≤ ‖h_t^⊥‖ + |m_t − m_∞|`
    have hdecomp : (fun x => h t x - (1 + minf - 1))
        = fun x => perpL2 lam (h t) x + (Graph.meanL2 lam (h t) - minf) := by
      funext x; rw [perpL2_apply]; ring
    rw [hdecomp]
    have htri : Graph.nrmL2 lam
        (fun x => perpL2 lam (h t) x + (Graph.meanL2 lam (h t) - minf))
        ≤ Graph.nrmL2 lam (perpL2 lam (h t)) + |Graph.meanL2 lam (h t) - minf| := by
      have h1 := nrmL2_add_le hnn (perpL2 lam (h t))
        (fun _ : V => Graph.meanL2 lam (h t) - minf)
      rw [nrmL2_const htot] at h1
      exact h1
    have hswap : |Graph.meanL2 lam (h t) - minf| = |minf - Graph.meanL2 lam (h t)| :=
      abs_sub_comm _ _
    -- `Q E² P0² ≤ E P0`
    have hmul : Q * (E ^ 2 * P0 ^ 2) ≤ E * P0 := by
      have h2 : Q * P0 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hP0e0 hQpos.le) hQe0
      have h3 : E ^ 2 * P0 ≤ E * P0 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hE1) (mul_nonneg hE0 hP0nn)]
      calc Q * (E ^ 2 * P0 ^ 2) = (Q * P0) * (E ^ 2 * P0) := by ring
        _ ≤ 1 * (E ^ 2 * P0) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = E ^ 2 * P0 := one_mul _
        _ ≤ E * P0 := h3
    rw [hswap] at htri
    have hcau' : |minf - Graph.meanL2 lam (h t)| ≤ E * P0 := by
      refine le_trans hcau ?_
      calc Q * E ^ 2 * P0 ^ 2 = Q * (E ^ 2 * P0 ^ 2) := by ring
        _ ≤ E * P0 := hmul
    linarith

/-! ### The gradient-descent clause

`proofs.tex:653–657`. Three differences from the flow, none of them cosmetic: the energy
inequality loses a factor `2` to the quadratic term `γ²‖D‖²`, so the telescoped drift constant
is `2C₇` and not `C₇`; the square root of `1 − γϱ/2` has to be taken, which is legitimate here
because `γϱ/2 ≤ 1/16`; and the continuation is an **induction**, there being no continuity to
run a first-failure argument on. -/

/-- **`‖D‖ ≤ L‖Ah^⊥‖` with `L := 2g''(1)‖w‖_{L^∞} + Kε`** (`proofs.tex:654`), read off
`eq:gradient_expansion`: the linear part contributes `‖A†‖·g''(1)‖w‖_{L^∞} ≤ 2g''(1)‖w‖_{L^∞}`
and the error `Kε`. -/
theorem nrmL2_lossGrad_le {K : V → V → ℝ} {lam w u : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup eps : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |u x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4) :
    Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z)
      ≤ Lgd g2 wsup (Kexp g2 a M3 wsup) eps
          * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hexp := gradient_expansion hK hinv hlam hg2 hM3 ha0 hwsup0 hwsup htaylor hh heps0 heps
  have hAnn : 0 ≤ Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) := Graph.nrmL2_nonneg _ _
  -- `‖Hh^⊥‖ ≤ 2g''(1)‖w‖_{L^∞}‖Ah^⊥‖`
  have h1 : Graph.nrmL2 lam (fun y => w y * Aop K lam (perpL2 lam u) y)
      ≤ wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) := by
    refine nrmL2_le_of_abs_le hnn hwsup0 fun y => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hwsup y) (abs_nonneg _)
  have h2 : Graph.nrmL2 lam (Adj K fun y => w y * Aop K lam (perpL2 lam u) y)
      ≤ 2 * Graph.nrmL2 lam (fun y => w y * Aop K lam (perpL2 lam u) y) :=
    nrmL2_Adj_le_two hK hinv _
  have h3 : Graph.nrmL2 lam (linHess K lam w g2 (perpL2 lam u))
      = g2 * Graph.nrmL2 lam (Adj K fun y => w y * Aop K lam (perpL2 lam u) y) := by
    rw [linHess_eq, nrmL2_smul, abs_of_nonneg hg2]
  have hlin : Graph.nrmL2 lam (linHess K lam w g2 (perpL2 lam u))
      ≤ 2 * g2 * wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) := by
    rw [h3]
    nlinarith [Graph.nrmL2_nonneg lam (fun y => w y * Aop K lam (perpL2 lam u) y)]
  -- the triangle inequality against the expansion
  have hrw : (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z)
      = fun x => linHess K lam w g2 (perpL2 lam u) x
        + ((lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z) x
            - linHess K lam w g2 (perpL2 lam u) x) := by
    funext x; ring
  have htri : Graph.nrmL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z)
      ≤ Graph.nrmL2 lam (linHess K lam w g2 (perpL2 lam u))
        + Graph.nrmL2 lam (fun x =>
            (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z) x
              - linHess K lam w g2 (perpL2 lam u) x) := by
    conv_lhs => rw [hrw]
    exact nrmL2_add_le hnn _ _
  simp only [Lgd]
  nlinarith [htri, hlin, hexp]

/-- **`L ≤ (5/2)g''(1)‖w‖_{L^∞}`, sharper than the paper's `3g''(1)‖w‖_{L^∞}`**
(`proofs.tex:654`). The slack is `Kε ≤ g''(1)w_min/(2B̂) ≤ g''(1)‖w‖_{L^∞}/2`, using `B̂ ≥ 1`.
Nothing downstream uses it: `γ₀` is stated at the exact `L`. -/
theorem Lgd_le {g2 a M3 wsup wmin Bhat eps : ℝ} (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a)
    (hwsup0 : 0 ≤ wsup) (hwmin0 : 0 ≤ wmin) (hwmw : wmin ≤ wsup) (hB1 : 1 ≤ Bhat)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat) :
    Lgd g2 wsup (Kexp g2 a M3 wsup) eps ≤ 5 / 2 * (g2 * wsup) := by
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2 hM3 ha0 hwsup0
  have hB0 : (0 : ℝ) ≤ Bhat := le_trans zero_le_one hB1
  have hkey : Kexp g2 a M3 wsup * eps ≤ g2 * wmin / 2 := by
    rcases eq_or_lt_of_le hK0 with hz | hpos
    · rw [← hz, zero_mul]
      positivity
    · rw [eps1, le_div_iff₀ (by positivity)] at heps1
      nlinarith [mul_nonneg (mul_nonneg hK0 heps0) (sub_nonneg.mpr hB1)]
  simp only [Lgd]
  nlinarith

/-- `γ ≤ γ₀` is `γL² ≤ g''(1)w_min/2`. -/
theorem gamma_mul_Lsq_le {g2 wmin L gam : ℝ} (hL : 0 < L) (hgam : gam ≤ gamma0 g2 wmin L) :
    gam * L ^ 2 ≤ g2 * wmin / 2 := by
  rw [gamma0, le_div_iff₀ (by positivity)] at hgam
  nlinarith

/-- **The discrete energy inequality** (`proofs.tex:655`): one step of `h ↦ h − γD(h)` obeys
`‖h^⊥_{k+1}‖² ≤ ‖h^⊥_k‖² − γ(g''(1)w_min − γL²)‖Ah^⊥_k‖² ≤ ‖h^⊥_k‖² − γ(g''(1)w_min/2)‖Ah^⊥_k‖²`.

`Πh^⊥ = 0` is what lets `⟪h^⊥, D^⊥⟫` be replaced by `⟪h^⊥, D⟫`, and `‖D^⊥‖ ≤ ‖D‖` is what lets
the quadratic term be paid for by `‖D‖ ≤ L‖Ah^⊥‖`. **The surviving coefficient is
`g''(1)w_min/2`, half the flow's** — the difference the paper's "the drift and continuation
arguments are identical" hides, and the reason the discrete drift constant below is `2C₇`. -/
theorem gd_energy_step {K : V → V → ℝ} {lam w u v : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup wmin Bhat eps gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |u x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hgam0 : 0 ≤ gam) (hgamL : gam * Lgd g2 wsup (Kexp g2 a M3 wsup) eps ^ 2 ≤ g2 * wmin / 2)
    (hv : v = fun x => u x - gam * (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z) x) :
    Graph.nrmL2 lam (perpL2 lam v) ^ 2 + gam * (g2 * wmin / 2) * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2
      ≤ Graph.nrmL2 lam (perpL2 lam u) ^ 2 := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2 hM3 ha0 hwsup0
  have hL0 : 0 ≤ Lgd g2 wsup (Kexp g2 a M3 wsup) eps := by simp only [Lgd]; positivity
  have hAnn : 0 ≤ Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) := Graph.nrmL2_nonneg _ _
  have hDpnn : 0 ≤ Graph.nrmL2 lam (perpL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z)) :=
    Graph.nrmL2_nonneg _ _
  have henergy := energy_lower hK hinv hlam hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin hB0 hcoer
    htaylor hh heps0 heps heps1
  have hDL := nrmL2_lossGrad_le hK hinv hlam hg2 hM3 ha0 hwsup0 hwsup htaylor hh heps0 heps
  have hZL : Graph.nrmL2 lam (perpL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z))
      ≤ Lgd g2 wsup (Kexp g2 a M3 wsup) eps
        * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) :=
    le_trans (nrmL2_perpL2_le hnn htot _) hDL
  have hZ2 : Graph.nrmL2 lam (perpL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z)) ^ 2
      ≤ Lgd g2 wsup (Kexp g2 a M3 wsup) eps ^ 2
        * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2 := by nlinarith
  have e1 : gam * (g2 * wmin / 2 * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2)
      ≤ gam * Graph.ipL2 lam (perpL2 lam u) (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z) :=
    mul_le_mul_of_nonneg_left henergy hgam0
  have e2 : gam * Lgd g2 wsup (Kexp g2 a M3 wsup) eps ^ 2
        * (gam * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2)
      ≤ g2 * wmin / 2 * (gam * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2) :=
    mul_le_mul_of_nonneg_right hgamL (mul_nonneg hgam0 (sq_nonneg _))
  have e3 : gam ^ 2 * Graph.nrmL2 lam (perpL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z)) ^ 2
      ≤ gam ^ 2 * (Lgd g2 wsup (Kexp g2 a M3 wsup) eps ^ 2
          * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2) :=
    mul_le_mul_of_nonneg_left hZ2 (sq_nonneg gam)
  have hperp : perpL2 lam v
      = fun x => perpL2 lam u x - gam * perpL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z) x := by
    rw [hv]; exact perpL2_sub_smul lam u _ gam
  have hip : Graph.ipL2 lam (perpL2 lam u) (perpL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z))
      = Graph.ipL2 lam (perpL2 lam u)
          (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z) :=
    ipL2_perpL2_right (meanL2_perpL2 htot u) _
  rw [hperp, sq_nrmL2_sub_smul hnn, hip]
  linarith

/-- **`γϱ/2 ≤ 1/16` at `γ ≤ γ₀`** — the inequality that makes the square-root step of
`proofs.tex:656` legitimate, and the only place `B̂ ≥ 1` and `w_min ≤ ‖w‖_{L^∞}` are spent.
`L ≥ 2g''(1)‖w‖_{L^∞} ≥ 2g''(1)w_min` gives `γ ≤ 1/(8g''(1)w_min)`. -/
theorem gamma_rho_le {g2 a M3 wsup wmin Bhat eps gam : ℝ}
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwmin0 : 0 < wmin)
    (hwmw : wmin ≤ wsup) (hB1 : 1 ≤ Bhat) (heps0 : 0 ≤ eps) (hgam0 : 0 ≤ gam)
    (hgamL : gam * Lgd g2 wsup (Kexp g2 a M3 wsup) eps ^ 2 ≤ g2 * wmin / 2) :
    gam * rhoL g2 wmin Bhat / 2 ≤ 1 / 16 := by
  have hBpos : (0 : ℝ) < Bhat := lt_of_lt_of_le zero_lt_one hB1
  have hgpos : 0 < g2 * wmin := mul_pos hg2 hwmin0
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2.le hM3 ha0 hwsup0
  have hLge : 2 * (g2 * wmin) ≤ Lgd g2 wsup (Kexp g2 a M3 wsup) eps := by
    simp only [Lgd]
    nlinarith [mul_nonneg hK0 heps0]
  have hLsq : 4 * (g2 * wmin) ^ 2 ≤ Lgd g2 wsup (Kexp g2 a M3 wsup) eps ^ 2 := by nlinarith
  have hgamg : gam * (g2 * wmin) ≤ 1 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hLsq hgam0]
  have hB2 : (1 : ℝ) ≤ Bhat ^ 2 := by nlinarith
  have hrle : rhoL g2 wmin Bhat ≤ g2 * wmin := by
    rw [rhoL, div_le_iff₀ (by positivity)]
    nlinarith
  have h1 : gam * rhoL g2 wmin Bhat ≤ gam * (g2 * wmin) :=
    mul_le_mul_of_nonneg_left hrle hgam0
  linarith

/-- **The per-step contraction** (`proofs.tex:656`): `‖h^⊥_{k+1}‖ ≤ (1 − γϱ/4)‖h^⊥_k‖`.

`gd_energy_step` and `lem:sigma_mixing` give `‖h^⊥_{k+1}‖² ≤ (1 − γϱ/2)‖h^⊥_k‖²`; the square
root is taken with `L2Toolkit.sqrt_one_sub_le`, `√(1−x) ≤ 1 − x/2`, which needs `x = γϱ/2 ≤ 1`
— `gamma_rho_le` gives `1/16`. **This square-root step is correct here**, unlike the
superficially similar sentence of `theo:db_stable_frozen_full`, where the printed factor is the
one the energy method does *not* deliver (`Discrete.lean`). -/
theorem gd_contract_step {K : V → V → ℝ} {lam w u v : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup wmin Bhat eps gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |u x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hgam0 : 0 ≤ gam) (hgamL : gam * Lgd g2 wsup (Kexp g2 a M3 wsup) eps ^ 2 ≤ g2 * wmin / 2)
    (hv : v = fun x => u x - gam * (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z) x) :
    Graph.nrmL2 lam (perpL2 lam v) ≤ (1 - gam * rhoL g2 wmin Bhat / 4) * Graph.nrmL2 lam (perpL2 lam u) := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hwsup0 : 0 ≤ wsup := (wsup_pos hwmin0 (hwmin x0) (hwsup x0)).le
  have hwmw : wmin ≤ wsup := le_trans (hwmin x0) (le_trans (le_abs_self _) (hwsup x0))
  have hBpos : (0 : ℝ) < Bhat := lt_of_lt_of_le zero_lt_one hB1
  have hB0 : (0 : ℝ) ≤ Bhat := hBpos.le
  have hgpos : 0 < g2 * wmin := mul_pos hg2 hwmin0
  have hrho0 : 0 ≤ rhoL g2 wmin Bhat := rhoL_nonneg hg2.le hwmin0.le
  have hadm : gam * rhoL g2 wmin Bhat / 2 ≤ 1 / 16 :=
    gamma_rho_le hg2 hM3 ha0 hwsup0 hwmin0 hwmw hB1 heps0 hgam0 hgamL
  have hEner := gd_energy_step hK hinv hlam htot hg2.le hM3 ha0 hwsup0 hwsup hwmin0.le hwmin
    hB0 hcoer htaylor hh heps0 heps heps1 hgam0 hgamL hv
  -- `‖h^⊥‖ ≤ B̂‖Ah^⊥‖`, read through `Ah = Ah^⊥`
  have hAeq : Aop K lam (perpL2 lam u) = Aop K lam u :=
    funext fun y => Aop_perpL2 hinv u (hlam y).ne'
  have hpB : Graph.nrmL2 lam (perpL2 lam u) ≤ Bhat * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) := by
    rw [hAeq]; exact hcoer u
  have hPnn : 0 ≤ Graph.nrmL2 lam (perpL2 lam u) := Graph.nrmL2_nonneg _ _
  have hQnn : 0 ≤ Graph.nrmL2 lam (perpL2 lam v) := Graph.nrmL2_nonneg _ _
  have hAnn : 0 ≤ Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) := Graph.nrmL2_nonneg _ _
  have hPsq : Graph.nrmL2 lam (perpL2 lam u) ^ 2
      ≤ Bhat ^ 2 * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2 := by nlinarith
  have hrn : rhoL g2 wmin Bhat * Graph.nrmL2 lam (perpL2 lam u) ^ 2
      ≤ g2 * wmin * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2 := by
    rw [rhoL, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hPsq hgpos.le]
  have hsq : Graph.nrmL2 lam (perpL2 lam v) ^ 2
      ≤ (1 - gam * rhoL g2 wmin Bhat / 2) * Graph.nrmL2 lam (perpL2 lam u) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hrn hgam0
    nlinarith
  have hxnn : 0 ≤ gam * rhoL g2 wmin Bhat / 2 := by positivity
  have hx1 : gam * rhoL g2 wmin Bhat / 2 ≤ 1 := by linarith
  have hroot : Real.sqrt (1 - gam * rhoL g2 wmin Bhat / 2)
      ≤ 1 - gam * rhoL g2 wmin Bhat / 4 := by
    have := sqrt_one_sub_le hxnn hx1
    linarith [this]
  calc Graph.nrmL2 lam (perpL2 lam v)
      = Real.sqrt (Graph.nrmL2 lam (perpL2 lam v) ^ 2) := (Real.sqrt_sq hQnn).symm
    _ ≤ Real.sqrt ((1 - gam * rhoL g2 wmin Bhat / 2) * Graph.nrmL2 lam (perpL2 lam u) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (1 - gam * rhoL g2 wmin Bhat / 2) * Graph.nrmL2 lam (perpL2 lam u) := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hPnn]
    _ ≤ (1 - gam * rhoL g2 wmin Bhat / 4) * Graph.nrmL2 lam (perpL2 lam u) :=
        mul_le_mul_of_nonneg_right hroot hPnn

/-- **The discrete drift of the mass**, in the telescoping form the continuation needs:
`|m_{k+1} − m_k| ≤ 2C₇(‖h^⊥_k‖² − ‖h^⊥_{k+1}‖²)`.

`|ṁ| ≤ C₆‖Ah^⊥‖²` becomes `|m_{k+1} − m_k| ≤ γC₆‖Ah^⊥_k‖²`, and the discrete energy inequality
pays for it — **at `2C₇`, not `C₇`**, the discrete energy inequality having `g''(1)w_min/2`
where the flow's has `g''(1)w_min`. Summed over `k` this gives `|m_k − m_0| ≤ 2C₇‖h_0^⊥‖²`,
against the flow's `C₇‖h_0^⊥‖²`; the paper's `ε₀` still suffices, because `2 + 2C₇ ≤ 2(2+C₇)`. -/
theorem gd_drift_step {K : V → V → ℝ} {lam w u v : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup wmin Bhat eps gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat) (hgw : 0 < g2 * wmin)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |u x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    (heps1 : eps ≤ eps1 g2 wmin (Kexp g2 a M3 wsup) Bhat)
    (hgam0 : 0 ≤ gam) (hgamL : gam * Lgd g2 wsup (Kexp g2 a M3 wsup) eps ^ 2 ≤ g2 * wmin / 2)
    (hv : v = fun x => u x - gam * (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z) x) :
    |Graph.meanL2 lam v - Graph.meanL2 lam u|
      ≤ 2 * C7 (C6 (Cg g2 a M3) wsup) g2 wmin
          * (Graph.nrmL2 lam (perpL2 lam u) ^ 2 - Graph.nrmL2 lam (perpL2 lam v) ^ 2) := by
  have hg2pos : 0 < g2 := by
    rcases eq_or_lt_of_le hg2 with hz | hp
    · exfalso; rw [← hz] at hgw; simp at hgw
    · exact hp
  have hwpos : 0 < wmin := by
    rcases eq_or_lt_of_le hwmin0 with hz | hp
    · exfalso; rw [← hz] at hgw; simp at hgw
    · exact hp
  have hg2ne : g2 ≠ 0 := ne_of_gt hg2pos
  have hwne : wmin ≠ 0 := ne_of_gt hwpos
  have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by simp only [C6, Cg]; positivity
  have hEner := gd_energy_step hK hinv hlam htot hg2 hM3 ha0 hwsup0 hwsup hwmin0 hwmin hB0
    hcoer htaylor hh heps0 heps heps1 hgam0 hgamL hv
  have hbnd := abs_deriv_mean_le hK.nonneg hinv hlam hg2 hM3 ha0 hwsup0 hwsup htaylor hh
    heps0 heps
  have hmv : Graph.meanL2 lam v - Graph.meanL2 lam u
      = -(gam * Graph.meanL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z)) := by
    rw [hv, meanL2_sub_smul]; ring
  rw [hmv, abs_neg, abs_mul, abs_of_nonneg hgam0]
  have hstep : gam * |Graph.meanL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + u z)|
      ≤ gam * (C6 (Cg g2 a M3) wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2) :=
    mul_le_mul_of_nonneg_left hbnd hgam0
  simp only [C7]
  have h1 : gam * (g2 * wmin / 2) * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2
      ≤ Graph.nrmL2 lam (perpL2 lam u) ^ 2 - Graph.nrmL2 lam (perpL2 lam v) ^ 2 := by linarith
  have h2 : 2 * (C6 (Cg g2 a M3) wsup / (g2 * wmin)) * (gam * (g2 * wmin / 2) * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2)
      ≤ 2 * (C6 (Cg g2 a M3) wsup / (g2 * wmin))
          * (Graph.nrmL2 lam (perpL2 lam u) ^ 2 - Graph.nrmL2 lam (perpL2 lam v) ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 2 * (C6 (Cg g2 a M3) wsup / (g2 * wmin)) * (gam * (g2 * wmin / 2) * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2)
      = gam * (C6 (Cg g2 a M3) wsup * Graph.nrmL2 lam (Aop K lam (perpL2 lam u)) ^ 2) := by
    field_simp
  linarith

/-- **`theo:local_convergence_full`, the gradient-descent clause** (`proofs.tex:653–657`): with
`h_{k+1} = h_k − γD(h_k)`, `γ ≤ γ₀` and `‖h_0‖ ≤ ε₀`, `‖h^⊥_k‖` contracts by `1 − γϱ/4` at
**every** step.

The paper closes this with "the drift and continuation arguments are identical". They are not
identical, and the difference is the whole content of the induction below.

* There is no continuity in discrete time, so the first-failure argument of Step 4 does not run:
  a single step can jump across the barrier `ε/2` that the flow has to cross continuously. The
  window is instead carried as an **induction hypothesis**, and what is propagated is the weaker
  `‖h_k‖_{L^∞} ≤ ε` — which is all `gd_contract_step` consumes, and which the discrete argument
  can supply where it cannot supply `ε/2`.
* The telescoped drift constant is **`2C₇`, not `C₇`** (`gd_drift_step`).
* `ε₀` as printed nevertheless suffices, with no slack to spare in the shape of the bound:
  `C_∞ε₀(2 + 2C₇) ≤ 2C_∞ε₀(2 + C₇) ≤ ε`. -/
theorem local_convergence_gd {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {hk : ℕ → V → ℝ}
    {g2 a M3 wsup wmin Bhat lamMin gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hstep : ∀ k : ℕ, hk (k + 1) = fun x =>
      hk k x - gam * lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + hk k z) x)
    (hgam0 : 0 ≤ gam)
    (hgam : gam ≤ gamma0 g2 wmin
      (Lgd g2 wsup (Kexp g2 a M3 wsup) (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat)))
    (hnorm0 : Graph.nrmL2 lam (hk 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) (Cinf lamMin)
          (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup)) :
    ∀ k : ℕ, Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))
      ≤ (1 - gam * rhoL g2 wmin Bhat / 4) * Graph.nrmL2 lam (perpL2 lam (hk k)) := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hwsupp : 0 < wsup := wsup_pos hwmin0 (hwmin x0) (hwsup x0)
  have hwsup0 : 0 ≤ wsup := hwsupp.le
  have hB0 : (0 : ℝ) ≤ Bhat := le_trans zero_le_one hB1
  have hgw : 0 < g2 * wmin := mul_pos hg2 hwmin0
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2.le hM3 ha0 hwsup0
  have hew0 : 0 ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat :=
    epsW_nonneg ha0 hg2.le hwmin0.le hK0 hB0
  have hewA := epsW_le_window a g2 wmin (Kexp g2 a M3 wsup) Bhat
  have hewB := epsW_le_eps1 a g2 wmin (Kexp g2 a M3 wsup) Bhat
  have hLpos : 0 < Lgd g2 wsup (Kexp g2 a M3 wsup) (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) := by
    simp only [Lgd]
    have h1 : 0 < g2 * wsup := mul_pos hg2 hwsupp
    linarith [mul_nonneg hK0 hew0]
  have hgamL := gamma_mul_Lsq_le hLpos hgam
  have hc60 : 0 ≤ C6 (Cg g2 a M3) wsup := by simp only [C6, Cg]; positivity
  have hc70 : 0 ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin := by simp only [C7, C6, Cg]; positivity
  have hrho0 : 0 ≤ rhoL g2 wmin Bhat := rhoL_nonneg hg2.le hwmin0.le
  have hCi0 : 0 < Cinf lamMin := Cinf_pos hlmin0
  set eW := epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat with heWdef
  set c7 := C7 (C6 (Cg g2 a M3) wsup) g2 wmin with hc7def
  set Ci := Cinf lamMin with hCidef
  set e0 := eps0 eW Ci c7 (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup) with he0def
  have he01 : e0 ≤ 1 := eps0_le_one _ _ _ _ _
  have he00 : 0 ≤ e0 := eps0_nonneg hew0 hCi0 hc70 hrho0 hc60
  have hposC : (0 : ℝ) < 2 * Ci * (2 + c7) :=
    mul_pos (by linarith : (0:ℝ) < 2 * Ci) (by linarith : (0:ℝ) < 2 + c7)
  have hkey : e0 * (2 * Ci * (2 + c7)) ≤ eW :=
    (le_div_iff₀ hposC).mp (eps0_le_basin _ _ _ _ _)
  have hCie0 : 0 ≤ Ci * e0 := mul_nonneg hCi0.le he00
  have hP0nn : 0 ≤ Graph.nrmL2 lam (perpL2 lam (hk 0)) := Graph.nrmL2_nonneg _ _
  have hP0le : Graph.nrmL2 lam (perpL2 lam (hk 0)) ≤ e0 :=
    le_trans (nrmL2_perpL2_le hnn htot _) hnorm0
  have hsq0 : Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2 ≤ e0 := by nlinarith [hP0le, hP0nn, he01]
  have hm0 : |Graph.meanL2 lam (hk 0)| ≤ e0 := le_trans (abs_meanL2_le_nrmL2 hnn htot _) hnorm0
  -- the discrete continuation, as an induction
  have key : ∀ k : ℕ, (∀ x, |hk k x| ≤ eW) ∧ Graph.nrmL2 lam (perpL2 lam (hk k)) ≤ Graph.nrmL2 lam (perpL2 lam (hk 0))
      ∧ |Graph.meanL2 lam (hk k) - Graph.meanL2 lam (hk 0)|
          ≤ 2 * c7 * (Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2 - Graph.nrmL2 lam (perpL2 lam (hk k)) ^ 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun x => ?_, le_rfl, by simp⟩
      have h1 : |hk 0 x| ≤ Ci * Graph.nrmL2 lam (hk 0) :=
        abs_le_Cinf_mul_nrmL2 hlmin0 hlmin _ x
      have h2 : Ci * Graph.nrmL2 lam (hk 0) ≤ Ci * e0 :=
        mul_le_mul_of_nonneg_left hnorm0 hCi0.le
      have h3 : 0 ≤ Ci * e0 * c7 := mul_nonneg hCie0 hc70
      linarith
    | succ k ih =>
      obtain ⟨hwk, hPk, hmk⟩ := ih
      have hc := gd_contract_step hK hinv hlam htot hg2 hM3 ha0 hwsup hwmin0 hwmin hB1 hcoer
        htaylor hwk hew0 hewA hewB hgam0 hgamL (hstep k)
      have hd := gd_drift_step hK hinv hlam htot hg2.le hM3 ha0 hwsup0 hwsup hwmin0.le hwmin
        hB0 hgw hcoer htaylor hwk hew0 hewA hewB hgam0 hgamL (hstep k)
      have hPknn : 0 ≤ Graph.nrmL2 lam (perpL2 lam (hk k)) := Graph.nrmL2_nonneg _ _
      have hPk1nn : 0 ≤ Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) := Graph.nrmL2_nonneg _ _
      have hgr : 0 ≤ gam * rhoL g2 wmin Bhat / 4 := by positivity
      have hmono : Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ≤ Graph.nrmL2 lam (perpL2 lam (hk 0)) := by
        have hx : 0 ≤ gam * rhoL g2 wmin Bhat / 4 * Graph.nrmL2 lam (perpL2 lam (hk k)) :=
          mul_nonneg hgr hPknn
        linarith
      have htri : |Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk 0)|
          ≤ |Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk k)|
            + |Graph.meanL2 lam (hk k) - Graph.meanL2 lam (hk 0)| := by
        have hsp : Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk 0)
            = (Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk k)) + (Graph.meanL2 lam (hk k) - Graph.meanL2 lam (hk 0)) := by ring
        rw [hsp]
        exact abs_add_le _ _
      have hdrift : |Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk 0)|
          ≤ 2 * c7 * (Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2 - Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ^ 2) := by linarith
      refine ⟨fun x => ?_, hmono, hdrift⟩
      have hsplit := abs_le_Cinf_mean_add_perp hlmin0 hlmin htot (hk (k + 1)) x
      have hmk1 : |Graph.meanL2 lam (hk (k + 1))| ≤ e0 + 2 * c7 * e0 := by
        have h1 : |Graph.meanL2 lam (hk (k + 1))| - |Graph.meanL2 lam (hk 0)|
            ≤ |Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk 0)| := abs_sub_abs_le_abs_sub _ _
        have hle : Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2 - Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ^ 2 ≤ e0 := by
          linarith [sq_nonneg (Graph.nrmL2 lam (perpL2 lam (hk (k + 1))))]
        have h2 : 2 * c7 * (Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2 - Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ^ 2)
            ≤ 2 * c7 * e0 :=
          mul_le_mul_of_nonneg_left hle (by linarith)
        linarith
      have hPk1e0 : Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ≤ e0 := le_trans hmono hP0le
      have hsum : |Graph.meanL2 lam (hk (k + 1))| + Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))
          ≤ e0 * (2 + 2 * c7) := by linarith
      calc |hk (k + 1) x|
          ≤ Ci * (|Graph.meanL2 lam (hk (k + 1))| + Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))) := hsplit
        _ ≤ Ci * (e0 * (2 + 2 * c7)) := mul_le_mul_of_nonneg_left hsum hCi0.le
        _ ≤ eW := by linarith
  intro k
  exact gd_contract_step hK hinv hlam htot hg2 hM3 ha0 hwsup hwmin0 hwmin hB1 hcoer htaylor
    (key k).1 hew0 hewA hewB hgam0 hgamL (hstep k)

/-! ### One instance, computed

The two-state chain of `prop:nonlinear_freezing`*(2)* again — `T(i→j) = 1/2`, `λ = (1/2,1/2)`,
`w ≡ 1`, `g(x) = (x−1)²` (so `g''(1) = 2`, `M₃ = 0`), `a = 4/5`, `B̂ = 1`, `λ_min = 1/2`.

**Computed by hand first, in exact arithmetic, before any Lean ran.** `K = 80/3` and
`ε₁ = 3/80` are `LocalEnergy`'s; then `min(a,1)/4 = 1/5 > 3/80`, so the window is
`ε = ε₁ = 3/80` — Step 4's radius is the *mixing* constraint here, not the `C³` one.
`C_g = 2`, `C₆ = 8`, `C₇ = 4`, `ϱ = 2`, `C_∞ = (1/2)^{−1/2} = √2`, and

  `ε₀ = min( (3/80)/(2·√2·6), 2/32, 1 ) = min( √2/640, 1/16, 1 ) = √2/640 ≈ 0.00221`,

the first entry binding. `L = 2·2·1 + (80/3)(3/80) = 5`, which is **exactly** the sharper
`(5/2)g''(1)‖w‖_{L^∞} = 5` of `Lgd_le` and strictly below the paper's `3g''(1)‖w‖_{L^∞} = 6`;
`γ₀ = 2/(2·25) = 1/25`, and `γ₀ϱ/2 = 1/25 ≤ 1/16`, the square-root step's margin.

Two things the numbers say. The basin is **17× smaller than the window** —
`ε/ε₀ = 2C_∞(2+C₇) = 12√2 ≈ 16.97` — so `LocalEnergy`'s own test vector, `h = (1/40,−1/40)`
with `‖h‖_{L^∞} = 1/40 = 0.025`, sits *inside* the window and *outside* the basin. And `ε₀ > 0`:
the theorem is not vacuous. -/

section TwoStateConstants

theorem twoState_Kexp : Kexp 2 (4 / 5) 0 1 = 80 / 3 := by
  norm_num [Kexp, C4, C5, Cg]

theorem twoState_C6 : C6 (Cg 2 (4 / 5) 0) 1 = 8 := by norm_num [C6, Cg]

theorem twoState_C7 : C7 (C6 (Cg 2 (4 / 5) 0) 1) 2 1 = 4 := by norm_num [C7, C6, Cg]

theorem twoState_rhoL : rhoL 2 1 1 = 2 := by norm_num [rhoL]

/-- **`ε = ε₁ = 3/80`**: on this chain Step 4's window is cut by the mixing constant, the `C³`
radius `min(a,1)/4 = 1/5` being the larger of the two. -/
theorem twoState_epsW : epsW (4 / 5) 2 1 (Kexp 2 (4 / 5) 0 1) 1 = 3 / 80 := by
  rw [epsW, twoState_Kexp]
  norm_num [eps1]

/-- **`C_∞ = √2`** at `λ_min = 1/2`. -/
theorem twoState_Cinf : Cinf (1 / 2 : ℝ) = Real.sqrt 2 := by
  have hs : Real.sqrt (1 / 2 : ℝ) * Real.sqrt 2 = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1 / 2)]
    norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
  simp only [Cinf]
  field_simp
  linarith

theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-- **`ε₀ = √2/640`**, the first entry of the `min` binding. -/
theorem twoState_eps0 : eps0 (3 / 80) (Real.sqrt 2) 4 2 8 = Real.sqrt 2 / 640 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hA : (3 / 80 : ℝ) / (2 * Real.sqrt 2 * (2 + 4)) = Real.sqrt 2 / 640 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    nlinarith [hsq]
  have h2 : Real.sqrt 2 ≤ 2 := sqrt_two_le_two
  simp only [eps0, hA]
  rw [min_eq_left (by nlinarith : Real.sqrt 2 / 640 ≤ (2 : ℝ) / (4 * 8)),
    min_eq_left (by nlinarith : Real.sqrt 2 / 640 ≤ (1 : ℝ))]

theorem twoState_Lgd : Lgd 2 1 (Kexp 2 (4 / 5) 0 1) (3 / 80) = 5 := by
  rw [Lgd, twoState_Kexp]
  norm_num

theorem twoState_gamma0 : gamma0 2 1 5 = 1 / 25 := by norm_num [gamma0]

/-- **The five constants of Steps 4–5 and the discrete clause, evaluated.**

Every entry was computed by hand in exact arithmetic before the Lean was written, and every
one agreed on the first run. The last three lines are the content: `γ₀ϱ/2 = 1/25 ≤ 1/16`, so the
square root of `1 − γϱ/2` is legitimate on this instance; `ε₀ > 0`, so the basin is a genuine
ball and nothing above is vacuous; and `ε₀ < 1/40 < ε`, so `LocalEnergy.energyH` — the vector at
which Step 2 was checked — lies in the window and outside the basin. -/
theorem twoState_local_convergence_check :
    Kexp 2 (4 / 5) 0 1 = 80 / 3
      ∧ epsW (4 / 5) 2 1 (Kexp 2 (4 / 5) 0 1) 1 = 3 / 80
      ∧ Cinf (1 / 2 : ℝ) = Real.sqrt 2
      ∧ C6 (Cg 2 (4 / 5) 0) 1 = 8
      ∧ C7 (C6 (Cg 2 (4 / 5) 0) 1) 2 1 = 4
      ∧ rhoL 2 1 1 = 2
      ∧ eps0 (3 / 80) (Real.sqrt 2) 4 2 8 = Real.sqrt 2 / 640
      ∧ Lgd 2 1 (Kexp 2 (4 / 5) 0 1) (3 / 80) = 5
      ∧ Lgd 2 1 (Kexp 2 (4 / 5) 0 1) (3 / 80) = 5 / 2 * (2 * 1)
      ∧ gamma0 2 1 5 = 1 / 25
      ∧ gamma0 2 1 5 * rhoL 2 1 1 / 2 ≤ 1 / 16
      ∧ (0 : ℝ) < eps0 (3 / 80) (Real.sqrt 2) 4 2 8
      ∧ eps0 (3 / 80) (Real.sqrt 2) 4 2 8 < 1 / 40 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨twoState_Kexp, twoState_epsW, twoState_Cinf, twoState_C6, twoState_C7, twoState_rhoL,
    twoState_eps0, twoState_Lgd, ?_, twoState_gamma0, ?_, ?_, ?_⟩
  · rw [twoState_Lgd]; norm_num
  · rw [twoState_gamma0, twoState_rhoL]; norm_num
  · rw [twoState_eps0]; positivity
  · rw [twoState_eps0]; nlinarith [sqrt_two_le_two]

end TwoStateConstants

end GFNBounds.Balance
