import GFNBounds.Balance.Flow
import GFNBounds.Balance.L2Toolkit

/-!
# The gradient field at `μ = (1+h)λ`: `D = A†[g''(1) w Ah_⊥] + E` with `‖E‖ ≤ Kε‖Ah_⊥‖`

**`theo:gd_diffusion_full`** — statement `proofs.tex:563–575`, proof `proofs.tex:577–579`;
**the expansion only**, with an explicit `c(ε)` under a `C³`-type Taylor bound, see SCOPE.
**`theo:local_convergence_full`** — statement `proofs.tex:612–618`, proof `proofs.tex:620–657`;
**Step 1 only** (`proofs.tex:623–632`), the expansion of the gradient field and its five
constants. Steps 2–5 are not here.
(The bold-backtick form of each label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (`theo:gd_diffusion_full`) Let `T` be ergodic with invariant `λ`, let `ν = wλ` with
> `w ∈ L^∞(λ)`, and let `g` be `C²` near `1` with `g(1)=g'(1)=0`, `g''(1)>0`. Then the gradient
> field of `𝓛_{g,ν}` at `μ = (1+h)λ` satisfies, for `h` in an `L^∞`-neighborhood of `0`,
> `∇^λ 𝓛_{g,ν} = g''(1) (P† − I)[ w (P − I) h ] λ + err(h)`, with
> `‖err(h)‖ ≤ c(ε)‖h‖_{L²(λ)}` and `c(ε) → 0` as the `L^∞` radius `ε` of the neighborhood
> shrinks. The linearization of the gradient flow `μ̇_t = −∇^λ 𝓛_{g,ν}(μ_t)` is therefore
> `ḣ = − g''(1) A† M_w A h`. In particular for `w ≡ 1` and `P̂` reversible with respect to `λ`,
> `ḣ = −g''(1)(I−P)² h`: training is the *square* of the backward-policy heat flow
> `ḣ = −(I−P)h`, and each eigenmode `Pφ = βφ` of the backward policy decays at rate
> `g''(1)(1−β)²`.

> (`theo:local_convergence_full`, Step 1) *Step 1 (expansion of the gradient field).* Assume
> `‖h‖_{L^∞} ≤ ε ≤ min(a,1)/4`. Then `r − 1 = Ah^⊥/(1+h)` satisfies, pointwise,
> `|r−1| ≤ (4/3)|Ah^⊥|` and `|r−1| ≤ 2ε/(1−ε) ≤ a`. The gradient density is `D = P†φ − rφ` with
> `φ := g'(r) w/(1+h)`. Taylor's formula `g'(r) = g''(1)(r−1) + R`, `|R| ≤ (M₃/2)(r−1)²`,
> together with `(r−1)/(1+h) = Ah^⊥ + Ah^⊥(1/(1+h)² − 1)`, `|1/(1+h)² − 1| ≤ 4ε` and
> `(r−1)² ≤ 4ε|Ah^⊥|`, gives `φ = g''(1) w Ah^⊥ + e`, `|e| ≤ C₄ε|Ah^⊥|`,
> `C₄ := ‖w‖_{L^∞}(4g''(1) + 3M₃)`. Since `rφ = φ + (r−1)φ` and `|g'(r)| ≤ C_g|r−1|` with
> `C_g := g''(1) + aM₃/2`, so that `|(r−1)φ| ≤ C₅ε|Ah^⊥|` with `C₅ := (16/3)C_g‖w‖_{L^∞}`,
> `D = A†[g''(1) w Ah^⊥] + E`, `‖E‖ ≤ Kε‖Ah^⊥‖`, `K := 2C₄ + C₅`.

## What is proved

| | |
|---|---|
| `C4`, `Cg`, `C5`, `Kexp` | the four constants, as the paper's formulas and not as `∃ C` |
| `linHess` | the paper's `H = g''(1) A† M_w A`, as a map `(V → ℝ) → (V → ℝ)` |
| `ratio_one_add_sub_one` | `r − 1 = Ah/(1+h)` at `u = 1 + h` — `proofs.tex:578`, `:623` |
| `abs_Aop_le_two_sup` | `|Ah| ≤ 2ε` pointwise: `P` is an average, by invariance |
| `abs_ratio_sub_one_le_four_thirds`, `abs_ratio_sub_one_le_two_eps_div`, `abs_ratio_sub_one_le_a` | the three pointwise bounds on `r − 1` of `proofs.tex:623` |
| `abs_inv_sq_sub_one_le` | `|1/(1+h)² − 1| ≤ 4ε` |
| `sq_ratio_sub_one_le` | `(r−1)² ≤ 4ε|Ah_⊥|` |
| `phi_expansion` | `φ = g''(1) w Ah_⊥ + e`, `|e| ≤ C₄ε|Ah_⊥|` — `proofs.tex:625–626` |
| `abs_gd_le_Cg`, `abs_ratio_sub_one_mul_phi_le` | `|g'(r)| ≤ C_g|r−1|` and `|(r−1)φ| ≤ C₅ε|Ah_⊥|` — `proofs.tex:628` |
| `lossGrad_eq_Adj_sub` | `D = A†φ − (r−1)φ`, the rearrangement of `gradDensity` the proof uses |
| **`gradient_expansion`** | **`eq:gradient_expansion`** (`proofs.tex:630–631`): `‖D − H h_⊥‖ ≤ Kε‖Ah_⊥‖` |
| `gd_diffusion_display` | **`eq:linearized_flow`** (`proofs.tex:566–568`) with `c(ε) = 2Kε` explicit |
| `linHess_reversible`, `linHess_eigen` | the "in particular" of `proofs.tex:573–574`: `H = g''(1)(I−P)²` and `Hφ = g''(1)(1−β)²φ` |
| `linHess_symm`, `linHess_nonneg`, `meanL2_linHess`, `linHess_upper`, `linHess_coercive` | the five properties of `H` that `theo:db_stable_frozen_full`'s proof uses |
| `twoState_expansion_lossGrad`, `twoState_expansion_linHess`, `twoState_expansion_check` | the expansion **evaluated**: `D = (175/432, −175/288)`, `Hh = (2/5, −2/5)`, `‖E‖² = 805093/37324800` against the theorem's `16/15` |

## Hypothesis checklist — `theo:gd_diffusion_full`

| paper hypothesis | here |
|---|---|
| `T` ergodic with invariant `λ` | ⚠ **weakened**: `Core.IsMarkovOn lam K` and `Core.IsInvariant lam K`, plus `λ > 0`. Ergodicity is used nowhere below — it is what makes `Π h` a scalar, and `Graph.meanL2` is that scalar by definition |
| `𝒮` a general state space, `L²(λ)` a Lebesgue space | ⚠ **restricted to a `Fintype`**, as everywhere in `GFNBounds.Balance`. See SCOPE |
| `ν = wλ` with `w ∈ L^∞(λ)` | ✓ `nu = fun x => lam x * w x`, and `‖w‖_{L^∞}` is a hypothesis `hwsup : ∀ x, |w x| ≤ wsup`. Positivity of `w` is **not** needed for the expansion and is not assumed |
| `g` is `C²` near `1`, `g(1)=g'(1)=0`, `g''(1)>0` | ⚠ **strengthened and weakened at once**. Strengthened: the second-order remainder is carried as an explicit bound `htaylor`, which `C²` alone does not give — this is a `C³`-type hypothesis, the one Step 1 of `theo:local_convergence_full` actually uses. Weakened: only `g'` appears (as `gd`), `g(1)=0` is never used, `g'(1)=0` is implied by `htaylor` at `y=1`, and `g''(1)>0` is relaxed to `0 ≤ g2`. See SCOPE |
| `h` in an `L^∞`-neighborhood of `0` | ✓ `hh : ∀ x, |h x| ≤ eps` with `heps : eps ≤ min a 1 / 4`, the radius of `proofs.tex:623`, and `heps0 : 0 ≤ eps` |
| `‖w‖_{L^∞} ≥ 0`, `a > 0` | ✓ carried as `hwsup0 : 0 ≤ wsup` and `ha0 : 0 ≤ a`. Both are true of the paper's objects (`wsup` is a supremum of absolute values, `a ∈ (0,1)`) and neither is derivable from `hwsup`/`heps` when `V` is empty, so they are hypotheses rather than facts |
| the display `eq:linearized_flow` with `‖err(h)‖ ≤ c(ε)‖h‖`, `c(ε) → 0` | ⚠ **`c(ε) = 2·Kexp·ε` explicitly** (`gd_diffusion_display`), not a limit. See SCOPE |
| "the linearization of the gradient flow is `ḣ = −g''(1)A†M_wA h`" | ✗ **not stated**: no flow, no ODE. `linHess` is exhibited; that it is the linearization of anything is not claimed here. See SCOPE |
| "in particular for `w ≡ 1` and `P̂` reversible, `ḣ = −g''(1)(I−P)²h`" | ✓ as an **operator identity**, `linHess_reversible`; the flow is again absent |
| "each eigenmode `Pφ = βφ` decays at rate `g''(1)(1−β)²`" | ✓ as `linHess_eigen : Hφ = g''(1)(1−β)²φ`; "decays at rate" is the flow statement and is not made |

## Hypothesis checklist — `theo:local_convergence_full`, Step 1

| paper hypothesis | here |
|---|---|
| the setting of `theo:db_stable_frozen_full`, hence of `theo:gd_diffusion_full` | ⚠ as in the table above |
| `g` is `C³` on `[1−a,1+a]`, `a ∈ (0,1)`, `M₃ := sup∣g'''∣` | ⚠ **weakened to the consequence used**: `htaylor : ∀ y, |y−1| ≤ a → |g'(y) − g''(1)(y−1)| ≤ (M₃/2)(y−1)²`, with `0 ≤ a` in place of `a ∈ (0,1)` and `0 ≤ M₃`. Taylor–Lagrange gives `htaylor` from `C³`; nothing below needs `g'''` to exist. This is a *weaker hypothesis*, hence a *stronger theorem*, and it is why `⚠ weakened` and not `⚠ strengthened`. It is not vacuous: `GFNBounds.Balance.logSqDeriv_taylor` is exactly `htaylor` for the paper's practical generator `g = (log x)²`, at `g''(1) = 2`, `M₃ = 80`, `a = 1/2` |
| `‖·‖_{L^∞(λ)} ≤ C_∞‖·‖_{L²(λ)}` | ✗ not needed by Step 1 — it is Step 4's. `L2Toolkit.abs_le_nrmL2_div_sqrt` carries it |
| `‖h‖_{L^∞} ≤ ε ≤ min(a,1)/4` | ✓ `hh`, `heps` |
| `w ≥ w_min > 0` | ✗ not needed by Step 1; carried only by `linHess_coercive`, which is Step 2's |
| `B̂ < ∞`, `ϱ := g''(1)w_min/B̂²` | ✗ not carried: no mixing coefficient and no rate appears below |
| `|r−1| ≤ (4/3)|Ah^⊥|`, `|r−1| ≤ 2ε/(1−ε) ≤ a` | ✓ `abs_ratio_sub_one_le_four_thirds`, `abs_ratio_sub_one_le_two_eps_div`, `abs_ratio_sub_one_le_a` |
| `D = P†φ − rφ`, `φ := g'(r)w/(1+h)` | ✓ `lossGrad_eq_Adj_sub`, in the equivalent form `D = A†φ − (r−1)φ`. `D` is `Flow.lossGrad`, which is `MassIdentity.gradDensity` **by definition**; that it is the gradient is `theo:first_variation_full`. See SCOPE |
| `|1/(1+h)² − 1| ≤ 4ε`, `(r−1)² ≤ 4ε|Ah^⊥|` | ✓ `abs_inv_sq_sub_one_le`, `sq_ratio_sub_one_le` |
| `C₄ = ‖w‖_{L^∞}(4g''(1)+3M₃)`, `C_g = g''(1)+aM₃/2`, `C₅ = (16/3)C_g‖w‖_{L^∞}`, `K = 2C₄+C₅` | ✓ the paper's formulas verbatim, as `C4`, `Cg`, `C5`, `Kexp`. Each was re-derived here independently; see SCOPE for the two places where the paper's constant is valid but not sharp |
| `eq:gradient_expansion`: `D = A†[g''(1)wAh^⊥] + E`, `‖E‖ ≤ Kε‖Ah^⊥‖` | ✓ `gradient_expansion` |
| Steps 2–5, `C₆`, `C₇`, `L`, `ε₀`, `ε₁`, `γ₀`, `c_∞` | ✗ **not here.** No energy estimate, no mass drift, no continuation, no conclusion |

## SCOPE (disclosed)

* **Finite state space.** `∫ · dλ` is `∑ x, lam x * ·`, a measure is carried by a density, and
  `⟪·∣·⟫_λ`, `‖·‖_λ`, `Π` are `Graph.ipL2`, `Graph.nrmL2`, `Graph.meanL2`. `paper-map.json`
  recorded both labels as bucket `D` when this file was written; both are `B` now, and
  `theo:local_convergence_full` is `closed`.
* **The `C²` statement of `theo:gd_diffusion_full` is *not* what is proved, and the difference
  is a real tension between two of this library's rules.** Rule 1 ("never state more than the
  paper proves") points at the paper's own hypothesis, `g` merely `C²`, under which `c(ε) → 0`
  holds with a **non-explicit** modulus — the modulus of continuity of `g'` at `1`, which `C²`
  supplies and does not quantify. Rule 3 ("constants are explicit formulas") forbids exactly
  such a `c(ε)`. The resolution taken here is to prove the **explicit** form,
  `c(ε) = 2·Kexp·ε`, under the **stronger** Taylor hypothesis `htaylor`, and to disclose that
  this is not the `C²` statement: neither statement implies the other. The choice is not
  arbitrary — `c(ε) = 2Kε` under a `C³`-type bound is the shape Step 1 of
  `theo:local_convergence_full` uses, and that is the only consumer either display has in the
  paper. **The `C²` form, with its non-explicit `c(ε)`, is not stated anywhere below.**
* **The flow sentence of `theo:gd_diffusion_full` is not stated.** "The linearization of the
  gradient flow `μ̇_t = −∇^λ 𝓛(μ_t)` is therefore `ḣ = −g''(1)A†M_wA h`" is a statement about
  an ODE; what is proved here is the expansion of the field, and `linHess` is the operator the
  sentence names. Passing from the expansion to the flow needs the linearized ODE and an
  existence statement, neither of which is here; `GFNBounds/Balance/Flow.lean`'s
  `stable_frozen_decay` takes the linearized flow as a hypothesis for the same reason.
  `linHess_reversible` and `linHess_eigen` are correspondingly **operator identities**, not
  decay rates.
* **`D` is `lossGrad`, which is a definition.** That `lossGrad` represents `∇^λ 𝓛_{g,ν}(μ)` is
  `theo:first_variation_full`, formalized on a finite state space in
  `GFNBounds/Balance/FirstVariation.lean` and disclosed there; nothing below re-derives it.
* **The weighted-`L²` bridge to a Mathlib `InnerProductSpace` does not exist in this library,
  and building it is out of scope.** The five facts `linHess_symm`, `linHess_nonneg`,
  `meanL2_linHess`, `linHess_upper` and `linHess_coercive` are the finite-state faces of exactly
  the hypotheses `GFNBounds.Balance.stable_frozen_discrete` takes of an
  abstract `H : E →L[ℝ] E` on an inner-product space (`hHsa`, `hPiH`, `hcoer`, `hup`). They
  **cannot be plugged into it**: `(V → ℝ, ⟪·∣·⟫_λ)` is not an `InnerProductSpace ℝ` instance
  here, `linHess` is not a `ContinuousLinearMap`, and `Graph.meanL2` is a scalar rather than a
  projection operator. Supplying that bridge — a `WithLp`-style instance on `V → ℝ` carrying
  `λ`, and `Aop`, `Adj`, `linHess`, `perpL2` as bundled maps — would let `Discrete.lean` and
  `Flow.lean`'s `stable_frozen_decay` consume `theo:gd_diffusion_full` directly, and would
  close the "the linearization is a hypothesis, not a derivation" disclosure those two files
  carry. **Built on 2026-09-12 in `GFNBounds/Balance/WeightedL2.lean`**, by an isometry
  `a ↦ √λ·a` into `EuclideanSpace ℝ V` rather than a new instance, and the five facts below are
  now actually consumed: `theo:db_stable_frozen_full` holds at this `H`, in both halves. The
  paragraph above records what the gap was; it is closed.
* **`w` is not assumed positive, or even non-negative, by the expansion.** The paper's `ν = wλ`
  is a measure, so its `w` is `≥ 0`; the expansion never uses the sign, so only
  `|w| ≤ wsup` is carried. `linHess_nonneg`, `linHess_upper` and `linHess_coercive` do take the
  sign, each in the form its own inequality needs.
* **The four constants are the paper's, and two of them carry slack this file did not remove.**
  Each was re-derived from scratch before being compared. `C₄`'s `3M₃` is reached with `8/3M₃`:
  the route gives `|e| ≤ ‖w‖_{L^∞}(4g''(1) + (8/3)M₃)ε|Ah^⊥|`, and `8/3 ≤ 3`. `(r−1)² ≤ 4ε|Ah^⊥|`
  is reached with `32/9 ≈ 3.56`, from `|r−1| ≤ 8ε/3` and `|r−1| ≤ (4/3)|Ah^⊥|`. `C_g` and `C₅`
  come out exactly as printed. The paper's values are **used as printed**; the slack is recorded
  rather than spent.
* **`|1/(1+h)² − 1| ≤ 4ε` is not tight at `ε = 1/4`; the *step* the paper routes through is.**
  `(2ε+ε²)/(1−ε)² ≤ 4ε` is equivalent to `(4ε−1)(ε−2) ≥ 0` and therefore holds exactly on
  `[0, 1/4] ∪ [2, ∞)` — which is what pins `ε ≤ 1/4`. But that step bounds `|2t+t²|` at `t = +ε`
  against `(1+t)²` at `t = −ε`, and the two extremes are not attained together: the true
  supremum of `|1/(1+t)² − 1|` over `|t| ≤ ε` is `(2ε−ε²)/(1−ε)²`, which at `ε = 1/4` is
  `7/9 ≈ 0.778` against `4ε = 1`. The sharp constant on `[0,1/4]` is `28/9 ≈ 3.11`, and `4ε`
  survives up to `ε = (7−√17)/8 ≈ 0.3596`. `abs_inv_sq_sub_one_le` is proved directly rather
  than through the paper's step, so it carries this slack rather than the step's; the statement
  is the paper's either way.
* **`sorry`-free and axiom-clean.** Nothing below is open; `#print axioms` on
  `gradient_expansion`, `gd_diffusion_display`, `phi_expansion`, `lossGrad_eq_Adj_sub`,
  `ratio_one_add_sub_one`, `linHess_reversible`, `linHess_eigen`, the five `linHess_*` facts
  and the three numerical checks returns `[propext, Classical.choice, Quot.sound]`. Graduated
  into the strict library on 2026-09-12.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### The four constants of Step 1

`proofs.tex:626`, `:628`, `:631`. Explicit formulas, not existentials — `kb/0007`. -/

/-- **`C₄ := ‖w‖_{L^∞}(4g''(1) + 3M₃)`** (`proofs.tex:626`), the constant of the pointwise
remainder in the expansion of `φ`. -/
noncomputable def C4 (wsup g2 M3 : ℝ) : ℝ := wsup * (4 * g2 + 3 * M3)

/-- **`C_g := g''(1) + aM₃/2`** (`proofs.tex:628`), the Lipschitz constant of `g'` at `1` on the
window `[1−a, 1+a]`. -/
noncomputable def Cg (g2 a M3 : ℝ) : ℝ := g2 + a * M3 / 2

/-- **`C₅ := (16/3)C_g‖w‖_{L^∞}`** (`proofs.tex:628`), the constant of the `(r−1)φ` term. -/
noncomputable def C5 (g2 a M3 wsup : ℝ) : ℝ := 16 / 3 * Cg g2 a M3 * wsup

/-- **`K := 2C₄ + C₅`** (`proofs.tex:631`), the constant of `eq:gradient_expansion`. The `2` is
`‖A†‖ ≤ 2`. -/
noncomputable def Kexp (g2 a M3 wsup : ℝ) : ℝ := 2 * C4 wsup g2 M3 + C5 g2 a M3 wsup

/-- **The paper's `H = g''(1) A† M_w A`** (`proofs.tex:571`), read on densities: the operator
whose `h_⊥`-image is the linear part of the gradient field. -/
noncomputable def linHess (K : V → V → ℝ) (lam w : V → ℝ) (g2 : ℝ) (h : V → ℝ) : V → ℝ :=
  fun x => g2 * Adj K (fun y => w y * Aop K lam h y) x

/-- The unapplied form of `linHess`; see the `perpL2`/`Aop` twins in `L2Toolkit`. -/
theorem linHess_eq (K : V → V → ℝ) (lam w : V → ℝ) (g2 : ℝ) (h : V → ℝ) :
    linHess K lam w g2 h = fun x => g2 * Adj K (fun y => w y * Aop K lam h y) x := rfl

theorem linHess_apply (K : V → V → ℝ) (lam w : V → ℝ) (g2 : ℝ) (h : V → ℝ) (x : V) :
    linHess K lam w g2 h x = g2 * Adj K (fun y => w y * Aop K lam h y) x := rfl

/-! ### Linearity the toolkit does not carry

`L2Toolkit` has `funAct_sub`, `densAct_sub` and `meanL2_sub`; the expansion also needs the
scalar-multiple forms, and the `Adj` face of the subtraction. -/

/-- `A†(a − b) = A†a − A†b`. -/
theorem Adj_sub (K : V → V → ℝ) (a b : V → ℝ) (x : V) :
    Adj K (fun y => a y - b y) x = Adj K a x - Adj K b x := by
  simp only [Adj_apply, funAct_sub]
  ring

/-- `A†(c·a) = c·A†a`. -/
theorem Adj_smul (K : V → V → ℝ) (c : ℝ) (a : V → ℝ) (x : V) :
    Adj K (fun y => c * a y) x = c * Adj K a x := by
  have hsum : ∑ y, K x y * (c * a y) = c * ∑ y, K x y * a y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  simp only [Adj_apply, funAct, hsum]
  ring

/-- `P(c·u) = c·Pu`, at every state and with no hypothesis. -/
theorem densAct_smul (lam : V → ℝ) (K : V → V → ℝ) (c : ℝ) (u : V → ℝ) (y : V) :
    Core.densAct lam K (fun z => c * u z) y = c * Core.densAct lam K u y := by
  have hsum : ∑ x, lam x * K x y * (c * u x) = c * ∑ x, lam x * K x y * u x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [Core.densAct_apply, hsum, mul_div_assoc]

/-- `A(c·u) = c·Au`. -/
theorem Aop_smul (lam : V → ℝ) (K : V → V → ℝ) (c : ℝ) (u : V → ℝ) (y : V) :
    Aop K lam (fun z => c * u z) y = c * Aop K lam u y := by
  rw [Aop_apply, Aop_apply, densAct_smul]
  ring

/-- `Π(c·a) = c·Πa`. -/
theorem meanL2_const_mul (lam : V → ℝ) (c : ℝ) (a : V → ℝ) :
    Graph.meanL2 lam (fun x => c * a x) = c * Graph.meanL2 lam a := by
  simp only [Graph.meanL2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `⟪a ∣ c·b⟫_λ = c⟪a ∣ b⟫_λ`. -/
theorem ipL2_smul_right (lam a b : V → ℝ) (c : ℝ) :
    Graph.ipL2 lam a (fun x => c * b x) = c * Graph.ipL2 lam a b := by
  simp only [Graph.ipL2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-! ### `r − 1 = Ah/(1+h)`, and the three pointwise bounds on it

`proofs.tex:578` (`r = (1+Ph)/(1+h)`, so `r − 1 = Ah/(1+h)`) and `proofs.tex:623`. -/

/-- **`r − 1 = Ah/(1+h)`** (`proofs.tex:578`, restated at `proofs.tex:623`) at the flow
`μ = (1+h)λ`. The numerator is `Ah = Ph − h`, `P` the density action; invariance is what makes
`P𝟏 = 𝟏`, hence `P(1+h) = 1 + Ph`. -/
theorem ratio_one_add_sub_one {K : V → V → ℝ} {lam h : V → ℝ}
    (hinv : Core.IsInvariant lam K) {y : V} (hy : lam y ≠ 0) (hu : 1 + h y ≠ 0) :
    ratio K lam (fun x => 1 + h x) y - 1 = Aop K lam h y / (1 + h y) := by
  have hsplit : ∑ x, lam x * (1 + h x) * K x y
      = (∑ x, lam x * K x y) + ∑ x, lam x * K x y * h x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hpush : pushMass K lam (fun x => 1 + h x) y
      = lam y * (1 + Core.densAct lam K h y) := by
    simp only [pushMass, Core.densAct_apply]
    rw [hsplit, hinv.inv y]
    field_simp
  simp only [ratio, hpush, Aop_apply]
  field_simp
  ring

/-- **`|Ah| ≤ 2ε` pointwise** when `|h| ≤ ε`: `Ph(y)` is the average of `h` against the weights
`λ(x)K(x,y)/λ(y)`, which sum to `1` in `x` by invariance, so `|Ph| ≤ ε`; the identity costs
another `ε`. Where `λ` vanishes `P` returns `0` and the bound is `ε`. -/
theorem abs_Aop_le_two_sup {K : V → V → ℝ} {lam h : V → ℝ} {eps : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hh : ∀ x, |h x| ≤ eps) (y : V) :
    |Aop K lam h y| ≤ 2 * eps := by
  have heps : 0 ≤ eps := le_trans (abs_nonneg _) (hh y)
  have hd : |Core.densAct lam K h y| ≤ eps := by
    rcases eq_or_ne (lam y) 0 with h0 | h0
    · simp only [Core.densAct_apply, h0, div_zero, abs_zero]
      exact heps
    · have hpos : 0 < lam y := lt_of_le_of_ne (hinv.nonneg y) (Ne.symm h0)
      rw [Core.densAct_apply, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      calc |∑ x, lam x * K x y * h x| ≤ ∑ x, |lam x * K x y * h x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x, lam x * K x y * eps := by
            refine Finset.sum_le_sum fun x _ => ?_
            rw [abs_mul, abs_of_nonneg (mul_nonneg (hinv.nonneg x) (hKnn x y))]
            exact mul_le_mul_of_nonneg_left (hh x) (mul_nonneg (hinv.nonneg x) (hKnn x y))
        _ = lam y * eps := by rw [← Finset.sum_mul, hinv.inv y]
        _ = eps * lam y := by ring
  have htri : |Core.densAct lam K h y - h y| ≤ |Core.densAct lam K h y| + |h y| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le (Core.densAct lam K h y) (-h y)
  rw [Aop_apply]
  linarith [hh y]

omit [Fintype V] in
/-- **`3/4 ≤ 1 + h(y)`** for `|h| ≤ ε ≤ 1/4` — the denominator bound every estimate of Step 1
divides by. -/
theorem one_add_ge_of_le {h : V → ℝ} {eps : ℝ} (hh : ∀ x, |h x| ≤ eps) (heps : eps ≤ 1 / 4)
    (y : V) : 3 / 4 ≤ 1 + h y := by
  have := abs_le.mp (hh y)
  linarith [this.1]

/-- **`|r−1| ≤ (4/3)|Ah^⊥|`** (`proofs.tex:623`): `Ah = Ah^⊥` by invariance, and `1+h ≥ 3/4`. -/
theorem abs_ratio_sub_one_le_four_thirds {K : V → V → ℝ} {lam h : V → ℝ} {eps : ℝ}
    (hinv : Core.IsInvariant lam K) (hh : ∀ x, |h x| ≤ eps) (heps : eps ≤ 1 / 4)
    {y : V} (hy : lam y ≠ 0) :
    |ratio K lam (fun x => 1 + h x) y - 1| ≤ 4 / 3 * |Aop K lam (perpL2 lam h) y| := by
  have hden : 3 / 4 ≤ 1 + h y := one_add_ge_of_le hh heps y
  have hdpos : (0 : ℝ) < 1 + h y := by linarith
  rw [ratio_one_add_sub_one hinv hy (ne_of_gt hdpos), ← Aop_perpL2 hinv h hy,
    abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  nlinarith [abs_nonneg (Aop K lam (perpL2 lam h) y)]

/-- **`|r−1| ≤ 2ε/(1−ε)`** (`proofs.tex:623`), the form that compares to `a`. -/
theorem abs_ratio_sub_one_le_two_eps_div {K : V → V → ℝ} {lam h : V → ℝ} {eps : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hh : ∀ x, |h x| ≤ eps) (heps : eps ≤ 1 / 4) {y : V} (hy : lam y ≠ 0) :
    |ratio K lam (fun x => 1 + h x) y - 1| ≤ 2 * eps / (1 - eps) := by
  have heps0 : 0 ≤ eps := le_trans (abs_nonneg _) (hh y)
  have hden : 3 / 4 ≤ 1 + h y := one_add_ge_of_le hh heps y
  have hdpos : (0 : ℝ) < 1 + h y := by linarith
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  have hlow : 1 - eps ≤ 1 + h y := by linarith [(abs_le.mp (hh y)).1]
  have hA : |Aop K lam h y| ≤ 2 * eps := abs_Aop_le_two_sup hKnn hinv hh y
  rw [ratio_one_add_sub_one hinv hy (ne_of_gt hdpos), abs_div, abs_of_pos hdpos,
    div_le_div_iff₀ hdpos h1e]
  nlinarith [abs_nonneg (Aop K lam h y)]

/-- **`2ε/(1−ε) ≤ a`** for `ε ≤ min(a,1)/4` (`proofs.tex:623`): with `ε ≤ 1/4` the left side is
at most `8ε/3`, and `ε ≤ a/4` makes that at most `2a/3`. -/
theorem two_eps_div_le_a {eps a : ℝ} (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4) :
    2 * eps / (1 - eps) ≤ a := by
  have h1 : eps ≤ 1 / 4 := le_trans heps (by have := min_le_right a 1; linarith)
  have h2 : eps ≤ a / 4 := le_trans heps (by have := min_le_left a 1; linarith)
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  rw [div_le_iff₀ h1e]
  nlinarith

/-- **`|r−1| ≤ a`** — the two previous bounds chained, which is what puts `r` inside the window
`[1−a, 1+a]` on which `htaylor` speaks. -/
theorem abs_ratio_sub_one_le_a {K : V → V → ℝ} {lam h : V → ℝ} {eps a : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    {y : V} (hy : lam y ≠ 0) :
    |ratio K lam (fun x => 1 + h x) y - 1| ≤ a := by
  have h1 : eps ≤ 1 / 4 :=
    le_trans heps (by have := min_le_right a 1; linarith)
  exact le_trans (abs_ratio_sub_one_le_two_eps_div hKnn hinv hh h1 hy)
    (two_eps_div_le_a heps0 heps)

/-- **`|1/(1+t)² − 1| ≤ 4ε`** for `|t| ≤ ε ≤ 1/4` (`proofs.tex:623`).

Proved directly rather than through the paper's `(2ε+ε²)/(1−ε)²`; see the module SCOPE for why
the two are not the same inequality, and for where each is tight. -/
theorem abs_inv_sq_sub_one_le {t eps : ℝ} (ht : |t| ≤ eps) (heps : eps ≤ 1 / 4) :
    |1 / (1 + t) ^ 2 - 1| ≤ 4 * eps := by
  have heps0 : 0 ≤ eps := le_trans (abs_nonneg _) ht
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  have hd : (3 : ℝ) / 4 ≤ 1 + t := by linarith
  have hdpos : (0 : ℝ) < (1 + t) ^ 2 := by nlinarith
  have hrw : 1 / (1 + t) ^ 2 - 1 = -(2 * t + t ^ 2) / (1 + t) ^ 2 := by
    field_simp
    ring
  rw [hrw, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos, abs_neg]
  refine abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- **`(r−1)² ≤ 4ε|Ah^⊥|`** (`proofs.tex:623`), from `|r−1| ≤ 8ε/3` and `|r−1| ≤ (4/3)|Ah^⊥|`.
The product of the two constants is `32/9 ≈ 3.56`; the paper's `4` is used as printed. -/
theorem sq_ratio_sub_one_le {K : V → V → ℝ} {lam h : V → ℝ} {eps : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hh : ∀ x, |h x| ≤ eps) (heps : eps ≤ 1 / 4) {y : V} (hy : lam y ≠ 0) :
    (ratio K lam (fun x => 1 + h x) y - 1) ^ 2
      ≤ 4 * eps * |Aop K lam (perpL2 lam h) y| := by
  have heps0 : 0 ≤ eps := le_trans (abs_nonneg _) (hh y)
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  have hb1 : |ratio K lam (fun x => 1 + h x) y - 1| ≤ 8 * eps / 3 := by
    refine le_trans (abs_ratio_sub_one_le_two_eps_div hKnn hinv hh heps hy) ?_
    rw [div_le_div_iff₀ h1e (by norm_num : (0:ℝ) < 3)]
    nlinarith
  have hb2 : |ratio K lam (fun x => 1 + h x) y - 1|
      ≤ 4 / 3 * |Aop K lam (perpL2 lam h) y| :=
    abs_ratio_sub_one_le_four_thirds hinv hh heps hy
  have hsq : (ratio K lam (fun x => 1 + h x) y - 1) ^ 2
      = |ratio K lam (fun x => 1 + h x) y - 1| * |ratio K lam (fun x => 1 + h x) y - 1| := by
    rw [abs_mul_abs_self]; ring
  rw [hsq]
  have hA : (0 : ℝ) ≤ |Aop K lam (perpL2 lam h) y| := abs_nonneg _
  calc |ratio K lam (fun x => 1 + h x) y - 1| * |ratio K lam (fun x => 1 + h x) y - 1|
      ≤ (8 * eps / 3) * (4 / 3 * |Aop K lam (perpL2 lam h) y|) :=
        mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
    _ ≤ 4 * eps * |Aop K lam (perpL2 lam h) y| := by nlinarith

/-! ### `φ = g''(1) w Ah^⊥ + e`, and the two remainder bounds

`proofs.tex:625–628`. `φ = g'(r)·w/(1+h)` is the potential of `theo:first_variation_full`, and
`e` is what separates it from its linearization. -/

/-- **`φ = g''(1) w Ah^⊥ + e` with `|e| ≤ C₄ε|Ah^⊥|`** (`proofs.tex:625–626`), pointwise.

The two ingredients are Taylor's formula for `g'` at `1` and the identity
`(r−1)/(1+h) = Ah^⊥ + Ah^⊥(1/(1+h)² − 1)`; the constant collects `4g''(1)ε` from the second and
`(8/3)M₃ε` from the first, and `8/3 ≤ 3` is the slack in the paper's `C₄`. -/
theorem phi_expansion {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup eps : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    {y : V} (hy : lam y ≠ 0) :
    |gd (ratio K lam (fun x => 1 + h x) y) * (w y / (1 + h y))
        - g2 * (w y * Aop K lam (perpL2 lam h) y)|
      ≤ C4 wsup g2 M3 * eps * |Aop K lam (perpL2 lam h) y| := by
  have heps4 : eps ≤ 1 / 4 := le_trans heps (by have := min_le_right a 1; linarith)
  have hden : 3 / 4 ≤ 1 + h y := one_add_ge_of_le hh heps4 y
  have hdpos : (0 : ℝ) < 1 + h y := by linarith
  have hwsup0 : 0 ≤ wsup := le_trans (abs_nonneg _) (hwsup y)
  set r : ℝ := ratio K lam (fun x => 1 + h x) y with hrdef
  set Ay : ℝ := Aop K lam (perpL2 lam h) y with hAdef
  have hA0 : (0 : ℝ) ≤ |Ay| := abs_nonneg _
  -- `r − 1 = Ay/(1+h)`
  have hr1 : r - 1 = Ay / (1 + h y) := by
    rw [hrdef, hAdef, ratio_one_add_sub_one hinv hy (ne_of_gt hdpos), Aop_perpL2 hinv h hy]
  -- the algebraic split
  have e1 : (r - 1) * (w y / (1 + h y)) = w y * Ay * (1 / (1 + h y) ^ 2) := by
    rw [hr1]; field_simp
  have hmain : gd r * (w y / (1 + h y)) - g2 * (w y * Ay)
      = (gd r - g2 * (r - 1)) * (w y / (1 + h y))
        + g2 * (w y * Ay * (1 / (1 + h y) ^ 2 - 1)) := by
    linear_combination g2 * e1
  -- the two pieces
  have hra : |r - 1| ≤ a := abs_ratio_sub_one_le_a hKnn hinv hh heps0 heps hy
  have htay : |gd r - g2 * (r - 1)| ≤ M3 / 2 * (4 * eps * |Ay|) := by
    refine le_trans (htaylor r (by simpa using hra)) ?_
    have := sq_ratio_sub_one_le (K := K) (lam := lam) (h := h) hKnn hinv hh heps4 hy
    rw [← hrdef, ← hAdef] at this
    nlinarith
  have hfrac : |w y / (1 + h y)| ≤ wsup * (4 / 3) := by
    rw [abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
    nlinarith [hwsup y, abs_nonneg (w y)]
  have hb1 : |(gd r - g2 * (r - 1)) * (w y / (1 + h y))|
      ≤ (M3 / 2 * (4 * eps * |Ay|)) * (wsup * (4 / 3)) := by
    rw [abs_mul]
    exact mul_le_mul htay hfrac (abs_nonneg _) (by positivity)
  have hb2 : |g2 * (w y * Ay * (1 / (1 + h y) ^ 2 - 1))| ≤ g2 * (wsup * (|Ay| * (4 * eps))) := by
    rw [abs_mul, abs_of_nonneg hg2, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ hg2
    have hX : |1 / (1 + h y) ^ 2 - 1| ≤ 4 * eps := abs_inv_sq_sub_one_le (hh y) heps4
    have t1 : |w y| * |Ay| ≤ wsup * |Ay| :=
      mul_le_mul_of_nonneg_right (hwsup y) (abs_nonneg Ay)
    calc |w y| * |Ay| * |1 / (1 + h y) ^ 2 - 1|
        ≤ wsup * |Ay| * (4 * eps) :=
          mul_le_mul t1 hX (abs_nonneg _) (mul_nonneg hwsup0 (abs_nonneg Ay))
      _ = wsup * (|Ay| * (4 * eps)) := by ring
  rw [hmain]
  refine le_trans (abs_add_le _ _) ?_
  have hkey : (0 : ℝ) ≤ M3 * wsup * eps * |Ay| := by positivity
  simp only [C4]
  nlinarith [hb1, hb2, hkey]

/-- **`|g'(y)| ≤ C_g|y−1|` on `[1−a, 1+a]`** (`proofs.tex:628`), with
`C_g = g''(1) + aM₃/2`. -/
theorem abs_gd_le_Cg {gd : ℝ → ℝ} {g2 a M3 : ℝ} (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    {y : ℝ} (hy : |y - 1| ≤ a) :
    |gd y| ≤ Cg g2 a M3 * |y - 1| := by
  have h1 : |gd y| ≤ |gd y - g2 * (y - 1)| + |g2 * (y - 1)| := by
    simpa using abs_add_le (gd y - g2 * (y - 1)) (g2 * (y - 1))
  have h2 := htaylor y hy
  have h3 : |g2 * (y - 1)| = g2 * |y - 1| := by rw [abs_mul, abs_of_nonneg hg2]
  have h4 : (y - 1) ^ 2 = |y - 1| * |y - 1| := by rw [abs_mul_abs_self]; ring
  simp only [Cg]
  rw [h3] at h1
  rw [h4] at h2
  nlinarith [abs_nonneg (y - 1),
    mul_nonneg (mul_nonneg hM3 (abs_nonneg (y - 1))) (sub_nonneg.mpr hy)]

/-- **`|(r−1)φ| ≤ C₅ε|Ah^⊥|`** (`proofs.tex:628`), with `C₅ = (16/3)C_g‖w‖_{L^∞}`. The chain is
`|r−1|·C_g|r−1|·(4/3)wsup` and `(r−1)² ≤ 4ε|Ah^⊥|`, whose product is exactly `16/3`. -/
theorem abs_ratio_sub_one_mul_phi_le {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup eps : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    {y : V} (hy : lam y ≠ 0) :
    |(ratio K lam (fun x => 1 + h x) y - 1)
        * (gd (ratio K lam (fun x => 1 + h x) y) * (w y / (1 + h y)))|
      ≤ C5 g2 a M3 wsup * eps * |Aop K lam (perpL2 lam h) y| := by
  have heps4 : eps ≤ 1 / 4 := le_trans heps (by have := min_le_right a 1; linarith)
  have hden : 3 / 4 ≤ 1 + h y := one_add_ge_of_le hh heps4 y
  have hdpos : (0 : ℝ) < 1 + h y := by linarith
  have hwsup0 : 0 ≤ wsup := le_trans (abs_nonneg _) (hwsup y)
  set r : ℝ := ratio K lam (fun x => 1 + h x) y with hrdef
  set Ay : ℝ := Aop K lam (perpL2 lam h) y with hAdef
  have hA0 : (0 : ℝ) ≤ |Ay| := abs_nonneg _
  have hra : |r - 1| ≤ a := abs_ratio_sub_one_le_a hKnn hinv hh heps0 heps hy
  have hCg0 : 0 ≤ Cg g2 a M3 := by
    have ha0 : 0 ≤ a := le_trans (abs_nonneg _) hra
    simp only [Cg]; positivity
  have hgd : |gd r| ≤ Cg g2 a M3 * |r - 1| := abs_gd_le_Cg hg2 hM3 htaylor (by simpa using hra)
  have hfrac : |w y / (1 + h y)| ≤ wsup * (4 / 3) := by
    rw [abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
    nlinarith [hwsup y, abs_nonneg (w y)]
  have hsq : (r - 1) ^ 2 ≤ 4 * eps * |Ay| := by
    have := sq_ratio_sub_one_le (K := K) (lam := lam) (h := h) hKnn hinv hh heps4 hy
    rw [← hrdef, ← hAdef] at this
    exact this
  have hstep : |r - 1| * (|gd r| * |w y / (1 + h y)|)
      ≤ |r - 1| * (Cg g2 a M3 * |r - 1| * (wsup * (4 / 3))) := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul hgd hfrac (abs_nonneg _) (by positivity)
  have habs : |r - 1| * |r - 1| = (r - 1) ^ 2 := by rw [abs_mul_abs_self]; ring
  rw [abs_mul, abs_mul]
  refine le_trans hstep ?_
  simp only [C5]
  nlinarith [hsq, hCg0, hwsup0, habs, mul_nonneg hCg0 hwsup0]

/-! ### `D = A†φ − (r−1)φ`

`proofs.tex:623`, where the paper writes `D = P†φ − rφ`; the split `rφ = φ + (r−1)φ`
(`proofs.tex:628`) turns `P† − r` into `A† − (r−1)`. -/

/-- **`D = A†φ − (r−1)φ` with `φ = g'(r)·w/u`** — the gradient density of `theo:first_variation_full`
rearranged, for `ν = wλ` and `μ = uλ`. Pure algebra on `MassIdentity.gradDensity`; `λ > 0` enters
only through `lossGrad_of_weight`, the Radon–Nikodym step `dν/dμ = w/u`. -/
theorem lossGrad_eq_Adj_sub {K : V → V → ℝ} {lam w u : V → ℝ} {gd : ℝ → ℝ}
    (hlam : ∀ x, 0 < lam x) (x : V) :
    lossGrad K lam (fun z => lam z * w z) gd u x
      = Adj K (fun y => gd (ratio K lam u y) * (w y / u y)) x
        - (ratio K lam u x - 1) * (gd (ratio K lam u x) * (w x / u x)) := by
  rw [lossGrad_of_weight hlam]
  simp only [lossGradDensity, gradDensity, Adj_apply]
  ring

/-! ### `eq:gradient_expansion` -/

/-- **`eq:gradient_expansion`** (`proofs.tex:630–631`): at `μ = (1+h)λ` and `ν = wλ`,
`D = A†[g''(1) w Ah^⊥] + E` with `‖E‖_{L²(λ)} ≤ Kε‖Ah^⊥‖_{L²(λ)}`, `K = 2C₄ + C₅`.

`E = A†e − (r−1)φ`: the first term is `‖A†‖ ≤ 2` against `phi_expansion`, the second is
`abs_ratio_sub_one_mul_phi_le`, and both pointwise bounds become `L²(λ)` bounds through
`nrmL2_le_of_abs_le`, the weight `λ` being non-negative. -/
theorem gradient_expansion {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup eps : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup)
    (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4) :
    Graph.nrmL2 lam (fun x =>
        lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z) x
          - linHess K lam w g2 (perpL2 lam h) x)
      ≤ Kexp g2 a M3 wsup * eps
          * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) := by
  set phi : V → ℝ := fun y => gd (ratio K lam (fun z => 1 + h z) y) * (w y / (1 + h y)) with hphi
  set Ah : V → ℝ := Aop K lam (perpL2 lam h) with hAh
  set e : V → ℝ := fun y => phi y - g2 * (w y * Ah y) with he
  have hC40 : 0 ≤ C4 wsup g2 M3 := by simp only [C4]; positivity
  have hC50 : 0 ≤ C5 g2 a M3 wsup := by simp only [C5, Cg]; positivity
  -- the pointwise identity `D − H h_⊥ = A†e − (r−1)φ`
  have hsplit : ∀ x, lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z) x
        - linHess K lam w g2 (perpL2 lam h) x
      = Adj K e x - (ratio K lam (fun z => 1 + h z) x - 1) * phi x := by
    intro x
    rw [lossGrad_eq_Adj_sub hlam, linHess_apply, he, hphi]
    rw [Adj_sub K _ (fun y => g2 * (w y * Ah y)) x, Adj_smul K g2 (fun y => w y * Ah y) x]
    ring
  -- the two `L²` bounds
  have hbe : Graph.nrmL2 lam e ≤ C4 wsup g2 M3 * eps * Graph.nrmL2 lam Ah := by
    refine nrmL2_le_of_abs_le hinv.nonneg (by positivity) fun x => ?_
    rw [he, hphi, hAh]
    exact phi_expansion hK.nonneg hinv hg2 hM3 hwsup htaylor hh heps0 heps (hlam x).ne'
  have hbr : Graph.nrmL2 lam (fun x => (ratio K lam (fun z => 1 + h z) x - 1) * phi x)
      ≤ C5 g2 a M3 wsup * eps * Graph.nrmL2 lam Ah := by
    refine nrmL2_le_of_abs_le hinv.nonneg (by positivity) fun x => ?_
    rw [hphi, hAh]
    exact abs_ratio_sub_one_mul_phi_le hK.nonneg hinv hg2 hM3 hwsup htaylor hh heps0 heps
      (hlam x).ne'
  have hAdj : Graph.nrmL2 lam (Adj K e) ≤ 2 * Graph.nrmL2 lam e :=
    nrmL2_Adj_le_two hK hinv e
  have htri : Graph.nrmL2 lam (fun x =>
      lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z) x
        - linHess K lam w g2 (perpL2 lam h) x)
      ≤ Graph.nrmL2 lam (Adj K e)
        + Graph.nrmL2 lam (fun x => (ratio K lam (fun z => 1 + h z) x - 1) * phi x) := by
    have hfun : (fun x => lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z) x
        - linHess K lam w g2 (perpL2 lam h) x)
        = fun x => Adj K e x - (ratio K lam (fun z => 1 + h z) x - 1) * phi x :=
      funext hsplit
    rw [hfun]
    exact nrmL2_sub_le hinv.nonneg (Adj K e) _
  simp only [Kexp]
  nlinarith [htri, hAdj, hbe, hbr, Graph.nrmL2_nonneg lam Ah, heps0, hC40, hC50]

/-- **`Ah = Ah^⊥` lifted to `H`**: `linHess` sees only `Ah`, so it does not distinguish `h` from
its mean-zero part. Under `λ > 0` this holds at every state. -/
theorem linHess_perpL2 {K : V → V → ℝ} {lam w : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (g2 : ℝ) (h : V → ℝ) :
    linHess K lam w g2 (perpL2 lam h) = linHess K lam w g2 h := by
  have hfun : (fun y => w y * Aop K lam (perpL2 lam h) y) = fun y => w y * Aop K lam h y :=
    funext fun y => by rw [Aop_perpL2 hinv h (hlam y).ne']
  simp only [linHess_eq, hfun]

/-- **`eq:linearized_flow`** (`proofs.tex:566–568`) in its own shape:
`∇^λ 𝓛_{g,ν} = g''(1)(P† − I)[w(P − I)h]λ + err(h)` with `‖err(h)‖ ≤ c(ε)‖h‖_{L²(λ)}` and
**`c(ε) = 2Kε` explicit**.

`‖Ah^⊥‖ ≤ 2‖h^⊥‖ ≤ 2‖h‖` turns `gradient_expansion` into a bound against `‖h‖`; the first step
is `‖A‖ ≤ 2` and the second is Pythagoras, both from `L2Toolkit`. The paper's `c(ε) → 0` is not
what is proved — see the module SCOPE. -/
theorem gd_diffusion_display {K : V → V → ℝ} {lam w h : V → ℝ} {gd : ℝ → ℝ}
    {g2 a M3 wsup eps : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup0 : 0 ≤ wsup)
    (hwsup : ∀ x, |w x| ≤ wsup)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4) :
    Graph.nrmL2 lam (fun x =>
        lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z) x
          - linHess K lam w g2 h x)
      ≤ 2 * Kexp g2 a M3 wsup * eps * Graph.nrmL2 lam h := by
  have hMk : Core.IsMarkov K := hK.toIsMarkov hlam
  have hstep := gradient_expansion hK hinv hlam hg2 hM3 ha0 hwsup0 hwsup htaylor hh heps0 heps
  rw [linHess_perpL2 hinv hlam g2 h] at hstep
  have hA : Graph.nrmL2 lam (Aop K lam (perpL2 lam h))
      ≤ 2 * Graph.nrmL2 lam (perpL2 lam h) :=
    nrmL2_Aop_le_two hMk hinv (perpL2 lam h)
  have hp : Graph.nrmL2 lam (perpL2 lam h) ≤ Graph.nrmL2 lam h :=
    nrmL2_perpL2_le hinv.nonneg htot h
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := by
    simp only [Kexp, C4, C5, Cg]
    positivity
  calc Graph.nrmL2 lam (fun x =>
        lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + h z) x
          - linHess K lam w g2 h x)
      ≤ Kexp g2 a M3 wsup * eps * Graph.nrmL2 lam (Aop K lam (perpL2 lam h)) := hstep
    _ ≤ Kexp g2 a M3 wsup * eps * (2 * Graph.nrmL2 lam h) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK0 heps0)
        linarith
    _ = 2 * Kexp g2 a M3 wsup * eps * Graph.nrmL2 lam h := by ring

/-! ### The "in particular": `w ≡ 1` and a reversible policy

`proofs.tex:573–574`. Reversibility is `Core.IsReversalPair lam K K`, i.e. detailed balance
`λ(x)K(x,y) = λ(y)K(y,x)`; it is what makes `P† = P`, hence `A† = A` and `H = g''(1)(I−P)²`. -/

/-- **`H = g''(1)(I − P)²` for `w ≡ 1` and `K` reversible** (`proofs.tex:573`). `(P−I)² = (I−P)²`,
so `Aop ∘ Aop` is the paper's `(I−P)²`; training is the square of the backward-policy heat flow.

Reversibility is **not** removable: with `w ≡ 1` the operator is `g''(1)A†A`, which equals
`g''(1)A²` exactly when `A† = A`. -/
theorem linHess_reversible {K : V → V → ℝ} {lam : V → ℝ}
    (hrev : Core.IsReversalPair lam K K) (hlam : ∀ x, 0 < lam x) (g2 : ℝ) (h : V → ℝ) (x : V) :
    linHess K lam (fun _ => 1) g2 h x = g2 * Aop K lam (Aop K lam h) x := by
  have hdf : ∀ (u : V → ℝ) (z : V), Core.densAct lam K u z = funAct K u z := by
    intro u z
    have h1 : Core.densAct lam K u z = Core.funAct K u z :=
      Core.funAct_eq_densAct_reversal hrev u (hlam z).ne'
    have h2 : Core.funAct K u z = funAct K u z := rfl
    rw [h1, h2]
  have hL : linHess K lam (fun _ => 1) g2 h x
      = g2 * (funAct K (Aop K lam h) x - Aop K lam h x) := by
    have h1 : (fun y => (1 : ℝ) * Aop K lam h y) = Aop K lam h := by funext y; ring
    rw [linHess_apply, h1, Adj_apply]
  have hR : Aop K lam (Aop K lam h) x = funAct K (Aop K lam h) x - Aop K lam h x := by
    rw [Aop_apply, hdf]
  rw [hL, hR]

/-- **Each eigenmode `Pφ = βφ` is an eigenmode of `H`, with eigenvalue `g''(1)(1−β)²`**
(`proofs.tex:574`). The paper reads this as a decay rate along the linearized flow; the flow is
not stated here, so what is delivered is the eigenvalue. -/
theorem linHess_eigen {K : V → V → ℝ} {lam : V → ℝ}
    (hrev : Core.IsReversalPair lam K K) (hlam : ∀ x, 0 < lam x) (g2 beta : ℝ) (phi : V → ℝ)
    (heig : ∀ y, Core.densAct lam K phi y = beta * phi y) (x : V) :
    linHess K lam (fun _ => 1) g2 phi x = g2 * (1 - beta) ^ 2 * phi x := by
  have hAphi : Aop K lam phi = fun y => (beta - 1) * phi y := by
    funext y
    rw [Aop_apply, heig y]
    ring
  rw [linHess_reversible hrev hlam g2 phi x, hAphi, Aop_smul, Aop_apply, heig x]
  ring

/-! ### The five facts about `H` that the energy estimate uses

`proofs.tex:605–609` and `proofs.tex:634`. These are the finite-state faces of the hypotheses
`GFNBounds.Balance.stable_frozen_discrete` takes of an abstract operator; see
the module SCOPE for why they cannot be plugged into it. -/

/-- **`⟪a ∣ Hb⟫_λ = g''(1)⟪w·Ab ∣ Aa⟫_λ`** — the one identity the other four read off, and the
place `lem:adjoint`*(3)* is spent. -/
theorem ipL2_linHess {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hKnn : ∀ x y, 0 ≤ K x y) (w : V → ℝ) (g2 : ℝ) (a b : V → ℝ) :
    Graph.ipL2 lam a (linHess K lam w g2 b)
      = g2 * Graph.ipL2 lam (fun y => w y * Aop K lam b y) (Aop K lam a) := by
  have h1 : Graph.ipL2 lam a (linHess K lam w g2 b)
      = g2 * Graph.ipL2 lam (Adj K (fun y => w y * Aop K lam b y)) a := by
    simp only [Graph.ipL2, linHess_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h1, ipL2_Adj_left hinv hKnn]

/-- **`H` is symmetric for `⟪·∣·⟫_λ`** — `Discrete.stable_frozen_discrete`'s `hHsa`. -/
theorem linHess_symm {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hKnn : ∀ x y, 0 ≤ K x y) (w : V → ℝ) (g2 : ℝ) (a b : V → ℝ) :
    Graph.ipL2 lam a (linHess K lam w g2 b) = Graph.ipL2 lam (linHess K lam w g2 a) b := by
  rw [ipL2_linHess hinv hKnn w g2 a b, ipL2_comm lam (linHess K lam w g2 a) b,
    ipL2_linHess hinv hKnn w g2 b a]
  have hswap : Graph.ipL2 lam (fun y => w y * Aop K lam b y) (Aop K lam a)
      = Graph.ipL2 lam (fun y => w y * Aop K lam a y) (Aop K lam b) := by
    simp only [Graph.ipL2]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hswap]

/-- **`H ⪰ 0`** (`proofs.tex:605`: "`H := g''(1)A†M_wA ⪰ 0`"), read as
`0 ≤ ⟪h ∣ Hh⟫_λ` — which is all the energy estimate uses. -/
theorem linHess_nonneg {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hKnn : ∀ x y, 0 ≤ K x y) {w : V → ℝ} {g2 : ℝ} (hw : ∀ x, 0 ≤ w x) (hg2 : 0 ≤ g2)
    (h : V → ℝ) : 0 ≤ Graph.ipL2 lam h (linHess K lam w g2 h) := by
  rw [ipL2_linHess hinv hKnn w g2 h h]
  refine mul_nonneg hg2 ?_
  simp only [Graph.ipL2]
  refine Finset.sum_nonneg fun x _ => ?_
  have : lam x * (w x * Aop K lam h x * Aop K lam h x)
      = (lam x * w x) * (Aop K lam h x * Aop K lam h x) := by ring
  rw [this]
  exact mul_nonneg (mul_nonneg (hinv.nonneg x) (hw x)) (mul_self_nonneg _)

/-- **`ΠH = 0`** (`proofs.tex:605`: "since `P†` preserves integrals"), which is what conserves
the total-flow normalization — `Discrete.stable_frozen_discrete`'s `hPiH`. -/
theorem meanL2_linHess {K : V → V → ℝ} {lam : V → ℝ} (hinv : Invariant K lam) (w : V → ℝ)
    (g2 : ℝ) (h : V → ℝ) : Graph.meanL2 lam (linHess K lam w g2 h) = 0 := by
  rw [linHess_eq, meanL2_const_mul lam g2 (Adj K fun y => w y * Aop K lam h y),
    meanL2_Adj hinv, mul_zero]

/-- **`⟪h ∣ Hh⟫ ≤ 4g''(1)‖w‖_{L^∞}‖h‖²`** — the paper's `‖H‖ ≤ 4g''(1)‖w‖_{L^∞}`
(`proofs.tex:609`), read as the quadratic form, which is what
`Discrete.stable_frozen_discrete`'s `hup` asks for. The `4` is `‖A‖² ≤ 4`. -/
theorem linHess_upper {K : V → V → ℝ} {lam : V → ℝ} (hK : Core.IsMarkov K)
    (hinv : Core.IsInvariant lam K) {w : V → ℝ} {g2 wsup : ℝ} (hw : ∀ x, w x ≤ wsup)
    (hg2 : 0 ≤ g2) (hwsup0 : 0 ≤ wsup) (h : V → ℝ) :
    Graph.ipL2 lam h (linHess K lam w g2 h) ≤ 4 * g2 * wsup * Graph.nrmL2 lam h ^ 2 := by
  rw [ipL2_linHess hinv hK.nonneg w g2 h h]
  have hle : Graph.ipL2 lam (fun y => w y * Aop K lam h y) (Aop K lam h)
      ≤ wsup * Graph.ipL2 lam (Aop K lam h) (Aop K lam h) := by
    simp only [Graph.ipL2, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hrw1 : lam x * (w x * Aop K lam h x * Aop K lam h x)
        = (lam x * (Aop K lam h x * Aop K lam h x)) * w x := by ring
    have hrw2 : wsup * (lam x * (Aop K lam h x * Aop K lam h x))
        = (lam x * (Aop K lam h x * Aop K lam h x)) * wsup := by ring
    rw [hrw1, hrw2]
    exact mul_le_mul_of_nonneg_left (hw x)
      (mul_nonneg (hinv.nonneg x) (mul_self_nonneg _))
  have hsq : Graph.ipL2 lam (Aop K lam h) (Aop K lam h)
      = Graph.nrmL2 lam (Aop K lam h) ^ 2 := (Graph.sq_nrmL2 hinv.nonneg _).symm
  have hA : Graph.nrmL2 lam (Aop K lam h) ≤ 2 * Graph.nrmL2 lam h :=
    nrmL2_Aop_le_two hK hinv h
  have hA0 : 0 ≤ Graph.nrmL2 lam (Aop K lam h) := Graph.nrmL2_nonneg _ _
  have hh0 : 0 ≤ Graph.nrmL2 lam h := Graph.nrmL2_nonneg _ _
  rw [hsq] at hle
  have hsq2 : Graph.nrmL2 lam (Aop K lam h) ^ 2 ≤ 4 * Graph.nrmL2 lam h ^ 2 := by nlinarith
  calc g2 * Graph.ipL2 lam (fun y => w y * Aop K lam h y) (Aop K lam h)
      ≤ g2 * (wsup * Graph.nrmL2 lam (Aop K lam h) ^ 2) := mul_le_mul_of_nonneg_left hle hg2
    _ ≤ g2 * (wsup * (4 * Graph.nrmL2 lam h ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq2 hwsup0) hg2
    _ = 4 * g2 * wsup * Graph.nrmL2 lam h ^ 2 := by ring

/-- **`g''(1)w_min‖Ah‖² ≤ ⟪h ∣ Hh⟫`** (`proofs.tex:606`, `proofs.tex:634`) — the coercivity the
energy estimate feeds to `lem:sigma_mixing`, which then replaces `‖Ah‖` by `‖h^⊥‖/B̂`. -/
theorem linHess_coercive {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hKnn : ∀ x y, 0 ≤ K x y) {w : V → ℝ} {g2 wmin : ℝ} (hw : ∀ x, wmin ≤ w x) (hg2 : 0 ≤ g2)
    (h : V → ℝ) :
    g2 * wmin * Graph.nrmL2 lam (Aop K lam h) ^ 2
      ≤ Graph.ipL2 lam h (linHess K lam w g2 h) := by
  rw [ipL2_linHess hinv hKnn w g2 h h, Graph.sq_nrmL2 hinv.nonneg (Aop K lam h)]
  have hle : wmin * Graph.ipL2 lam (Aop K lam h) (Aop K lam h)
      ≤ Graph.ipL2 lam (fun y => w y * Aop K lam h y) (Aop K lam h) := by
    simp only [Graph.ipL2, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hrw1 : lam x * (w x * Aop K lam h x * Aop K lam h x)
        = (lam x * (Aop K lam h x * Aop K lam h x)) * w x := by ring
    have hrw2 : wmin * (lam x * (Aop K lam h x * Aop K lam h x))
        = (lam x * (Aop K lam h x * Aop K lam h x)) * wmin := by ring
    rw [hrw1, hrw2]
    exact mul_le_mul_of_nonneg_left (hw x)
      (mul_nonneg (hinv.nonneg x) (mul_self_nonneg _))
  calc g2 * wmin * Graph.ipL2 lam (Aop K lam h) (Aop K lam h)
      = g2 * (wmin * Graph.ipL2 lam (Aop K lam h) (Aop K lam h)) := by ring
    _ ≤ g2 * Graph.ipL2 lam (fun y => w y * Aop K lam h y) (Aop K lam h) :=
        mul_le_mul_of_nonneg_left hle hg2

/-! ### One instance, computed

The two-state chain of `prop:nonlinear_freezing`*(2)* — `T(i→j) = 1/2`, `λ = (1/2,1/2)` — at
`h = (1/5, −1/5)`, `w ≡ 1`, `g(x) = (x−1)²` (so `g'(y) = 2(y−1)`, `g''(1) = 2`, `M₃ = 0`),
`a = 4/5` and `ε = 1/5`, which sits exactly on the boundary `ε = min(a,1)/4`.

**Computed by hand first**, off the paper's own displays and before any Lean ran. `P` is the
`λ`-average, so `Ph ≡ 0` and `Ah = (−1/5, 1/5)`; `Πh = 0`, so `h^⊥ = h`. Then
`u = 1 + h = (6/5, 4/5)`, `r − 1 = Ah/(1+h) = (−1/6, 1/4)`, `dν/dμ = 1/u = (5/6, 5/4)`, and
`φ = g'(r)·(dν/dμ) = 2(r−1)/u = (−5/18, 5/8)`. `P†φ ≡ (φ₀+φ₁)/2 = 25/144` at both states, so
`D = P†φ − rφ = (25/144 + 25/108, 25/144 − 25/32) = (175/432, −175/288)`. For the linear part,
`A†[Ah] = (1/5, −1/5)` and `H h^⊥ = 2·A†[Ah] = (2/5, −2/5)` — which is also what
`linHess_eigen` predicts, `Ph = 0` being the eigenmode `β = 0` with rate `g''(1)(1−0)² = 2`.
Hence `E = D − Hh^⊥ = (11/2160, −299/1440)` and
`‖E‖² = ½(11/2160)² + ½(299/1440)² = 805093/37324800 ≈ 0.02157`, against the theorem's
`Kε‖Ah^⊥‖ = (80/3)(1/5)(1/5) = 16/15 ≈ 1.067`. -/

section TwoStateExpansion

/-- `h = (1/5, −1/5)` on the two-state chain: mean zero, `L^∞` norm `1/5`. -/
noncomputable def expH : Fin 2 → ℝ := ![1 / 5, -(1 / 5)]

theorem expH_abs_le : ∀ x, |expH x| ≤ 1 / 5 := by
  intro x
  fin_cases x <;> norm_num [expH]

theorem twoState_isMarkovOn : Core.IsMarkovOn twoStateLam twoStateK :=
  ⟨fun _ _ => by norm_num [twoStateK], fun {x} _ => by norm_num [twoStateK, Fin.sum_univ_two]⟩

theorem twoState_isInvariant : Core.IsInvariant twoStateLam twoStateK :=
  ⟨fun _ => by norm_num [twoStateLam], twoStateK_invariant⟩

/-- `Πh = 0`, so `h^⊥ = h`. -/
theorem twoState_perpL2_expH : perpL2 twoStateLam expH = expH := by
  funext x
  have hm : Graph.meanL2 twoStateLam expH = 0 := by
    simp only [Graph.meanL2, Fin.sum_univ_two]
    norm_num [twoStateLam, expH]
  rw [perpL2_apply, hm, sub_zero]

/-- **`Ah = (−1/5, 1/5)`**, `P` being the `λ`-average on this chain. -/
theorem twoState_Aop_expH :
    Aop twoStateK twoStateLam expH 0 = -(1 / 5) ∧ Aop twoStateK twoStateLam expH 1 = 1 / 5 := by
  constructor <;>
    · simp only [Aop_apply, Core.densAct_apply, Fin.sum_univ_two]
      norm_num [twoStateK, twoStateLam, expH]

/-- **`D = (175/432, −175/288)`**, the gradient density evaluated — the number computed by hand
in the section preamble, against the paper's `D = P†φ − rφ`. -/
theorem twoState_expansion_lossGrad :
    lossGrad twoStateK twoStateLam (fun z => twoStateLam z * 1) (fun z => 2 * (z - 1))
        (fun z => 1 + expH z) 0 = 175 / 432
      ∧ lossGrad twoStateK twoStateLam (fun z => twoStateLam z * 1) (fun z => 2 * (z - 1))
        (fun z => 1 + expH z) 1 = -(175 / 288) := by
  constructor <;>
    · simp only [lossGrad, lossGradDensity, gradDensity, funAct, ratio, pushMass,
        Fin.sum_univ_two]
      norm_num [twoStateK, twoStateLam, expH]

/-- **`Hh^⊥ = (2/5, −2/5)`**, the linear part evaluated — `g''(1)(1−β)²h` at `β = 0`. -/
theorem twoState_expansion_linHess :
    linHess twoStateK twoStateLam (fun _ => 1) 2 (perpL2 twoStateLam expH) 0 = 2 / 5
      ∧ linHess twoStateK twoStateLam (fun _ => 1) 2 (perpL2 twoStateLam expH) 1
          = -(2 / 5) := by
  rw [twoState_perpL2_expH]
  constructor <;>
    · simp only [linHess_apply, Adj_apply, funAct, Aop_apply, Core.densAct_apply,
        Fin.sum_univ_two]
      norm_num [twoStateK, twoStateLam, expH]

/-- **`‖Ah^⊥‖_{L²(λ)} = 1/5`** on this instance. -/
theorem twoState_nrmL2_Aop :
    Graph.nrmL2 twoStateLam (Aop twoStateK twoStateLam (perpL2 twoStateLam expH)) = 1 / 5 := by
  rw [twoState_perpL2_expH]
  have hip : Graph.ipL2 twoStateLam (Aop twoStateK twoStateLam expH)
      (Aop twoStateK twoStateLam expH) = 1 / 25 := by
    simp only [Graph.ipL2, Fin.sum_univ_two, twoState_Aop_expH.1, twoState_Aop_expH.2]
    norm_num [twoStateLam]
  simp only [Graph.nrmL2, hip]
  rw [show (1 : ℝ) / 25 = (1 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **`gradient_expansion`, evaluated and checked against a hand computation.**

Three things at once: the error is the number computed by hand (`‖E‖² = 805093/37324800`), the
theorem's own bound holds on this instance and reads `16/15`, and the two are consistent with a
factor of about `7.3` to spare. A type-correct theorem about the wrong object would still
compile; this is what says the object is the paper's. -/
theorem twoState_expansion_check :
    Graph.nrmL2 twoStateLam (fun x =>
        lossGrad twoStateK twoStateLam (fun z => twoStateLam z * 1) (fun z => 2 * (z - 1))
            (fun z => 1 + expH z) x
          - linHess twoStateK twoStateLam (fun _ => 1) 2 (perpL2 twoStateLam expH) x) ^ 2
        = 805093 / 37324800
      ∧ Graph.nrmL2 twoStateLam (fun x =>
          lossGrad twoStateK twoStateLam (fun z => twoStateLam z * 1) (fun z => 2 * (z - 1))
              (fun z => 1 + expH z) x
            - linHess twoStateK twoStateLam (fun _ => 1) 2 (perpL2 twoStateLam expH) x)
          ≤ 16 / 15 := by
  have hlam : ∀ x, 0 < twoStateLam x := twoStateLam_pos
  have hval : Graph.nrmL2 twoStateLam (fun x =>
      lossGrad twoStateK twoStateLam (fun z => twoStateLam z * 1) (fun z => 2 * (z - 1))
          (fun z => 1 + expH z) x
        - linHess twoStateK twoStateLam (fun _ => 1) 2 (perpL2 twoStateLam expH) x) ^ 2
      = 805093 / 37324800 := by
    rw [Graph.sq_nrmL2 fun x => (hlam x).le]
    simp only [Graph.ipL2, Fin.sum_univ_two, twoState_expansion_lossGrad.1,
      twoState_expansion_lossGrad.2, twoState_expansion_linHess.1,
      twoState_expansion_linHess.2]
    norm_num [twoStateLam]
  refine ⟨hval, ?_⟩
  have hbound := gradient_expansion (K := twoStateK) (lam := twoStateLam) (w := fun _ => 1)
    (h := expH) (gd := fun z => 2 * (z - 1)) (g2 := 2) (a := 4 / 5) (M3 := 0) (wsup := 1)
    (eps := 1 / 5)
    twoState_isMarkovOn twoState_isInvariant hlam (by norm_num) (le_refl 0) (by norm_num)
    (by norm_num) (fun _ => by norm_num)
    (fun y _ => by norm_num)
    expH_abs_le (by norm_num) (by norm_num)
  rw [twoState_nrmL2_Aop] at hbound
  refine le_trans hbound (le_of_eq ?_)
  simp only [Kexp, C4, C5, Cg]
  norm_num

end TwoStateExpansion

end GFNBounds.Balance
