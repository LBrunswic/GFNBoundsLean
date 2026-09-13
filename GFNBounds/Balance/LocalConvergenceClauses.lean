import GFNBounds.Balance.LocalConvergence

/-!
# The four clauses the local convergence theorem gained on 2026-09-13

**`theo:local_convergence_full`** — statement `proofs.tex:612–618`, proof `proofs.tex:620–678`.
`GFNBounds/Balance/LocalConvergence.lean` certifies the theorem's two estimates (the flow and the
gradient-descent contraction). On 2026-09-13 the statement gained four clauses that the strict
file does not export; this file exports them, without editing it.

> Then there are explicit `ε₀ ∈ (0, a/(16C_∞)]` and `C ≥ 1`, depending only on `g''(1)`,
> `sup_{[1−a,1+a]}|g'''|`, `a`, `w_min`, `‖w‖_{L^∞}`, `B̂` and `C_∞`, such that for every
> initialization `μ₀ = (1+h₀)λ` with `‖h₀‖_{L²(λ)} ≤ ε₀`, the *nonlinear* gradient flow
> `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` converges to a balanced flow `c_∞λ` with
> `|c_∞ − 1 − Πh₀| ≤ C‖h₀ − Πh₀‖²` and `‖h_t − (c_∞−1)‖_{L²(λ)} ≤ 2e^{−ϱt/2}‖h₀ − Πh₀‖_{L²(λ)}`.
> There is moreover an explicit `γ₀ > 0`, depending only on the same quantities, such that for
> every such `h₀` and every step `0 < γ ≤ γ₀` the gradient descent `h_{k+1} := h_k − γD_k`, `D_k`
> the density against `λ` of `∇^λ𝓛_{g,ν}((1+h_k)λ)`, is well defined and satisfies
> `‖h_{k+1} − Πh_{k+1}‖_{L²(λ)} ≤ (1 − γϱ/4)‖h_k − Πh_k‖_{L²(λ)}` for every `k ≥ 0`.

> (Step 4) `ε₀ := min(ε/(2C_∞(2+C₇)), ϱ/(4C₆), 1)`; since `C₇ ≥ 0` and `a < 1`,
> `ε₀ ≤ ε/(4C_∞) ≤ a/(16C_∞)`.
> (Step 5) With `c_∞ := 1 + m_∞` and `C := max(1, C₇)`, `|c_∞ − 1 − Πh₀| ≤ C₇‖h₀^⊥‖² ≤ C‖h₀^⊥‖²`.
> (Step 6) Set `L := 2g''(1)‖w‖_{L^∞} + Kε` and `γ₀ := g''(1)w_min/(2L²)` … the induction
> `‖h_k‖_{L^∞} ≤ ε`, `‖h^⊥_k‖ ≤ ‖h^⊥_0‖`, `|m_k − m_0| ≤ 2C₇(‖h^⊥_0‖² − ‖h^⊥_k‖²)` …
> This closes the induction: `h_k` is well defined and `eq:gd_contraction` holds at every `k ≥ 0`.
>
> (Step 6, `:662`) By Step 1 the ratio `r` at `(1+h_k)λ` is defined and satisfies
> `|r−1| ≤ 2ε/(1−ε) ≤ 2a/3`, as `ε ≤ a/4`; the ratio at `(1+h_k)λ+δ` is `(r+v)/(1+u)` … so it lies
> in `(1−a,1+a)` once `‖u‖_{L^∞}+‖v‖_{L^∞}` is small enough, and `D_k` is defined by Theorem
> `theo:first_variation_full` applied to the generator equal to `g` on `[1−a,1+a]` with derivative
> extended by constants outside it, which is continuously differentiable on `ℝ₊*` with locally
> Lipschitz derivative and has the same balance loss as `g` at every such perturbation.

## What is proved

| clause | declaration |
|---|---|
| `ε₀ ≤ a/(16C_∞)` | `eps0_le_a_div` — for the abstract `eps0 (epsW a …) Ci c7 ρ c₆`, from `0 ≤ a`, `0 < Ci`, `0 ≤ c7` alone |
| `ε₀ ∈ (0, a/(16C_∞)]` | **`eps0_mem_Ioc`** — at the theorem's constants, under the theorem's hypotheses |
| `C ≥ 1` with `C := max(1, C₇)` | `one_le_max_C7`, and **`local_convergence_full_C`**: `local_convergence_full` with `C₇` replaced by `max(1, C₇)` |
| `γ₀ > 0` | `gamma0_pos` (from `0 < L`), `Lgd_pos`, and **`gamma0_pos_of_weights`** at the theorem's constants and hypotheses |
| "the gradient descent … is well defined" (i) | `local_convergence_gd_window`: `‖h_k‖_{L^∞} ≤ ε` and `0 < 1 + h_k` at every `k` |
| … (ii) `\|r_k − 1\| ≤ 2a/3` | `abs_ratio_sub_one_le_two_a_div_three` |
| … (iii) `D_k` is the gradient of the loss | `hasDerivAt_loss_local`, `hasDerivAt_loss_ipL2_local` (`FirstVariation`'s two lemmas with `g` differentiable only at the values `r` takes) |
| … all three, at every `k` | **`local_convergence_gd_welldefined`** |

## Hypothesis checklist

The hypotheses are `LocalConvergence.lean`'s, row for row; its checklist applies verbatim and is
not repeated. The rows specific to these four clauses:

| paper hypothesis | here |
|---|---|
| `a ∈ (0,1)`, invoked by Step 4 as "`a < 1`" for `ε₀ ≤ a/(16C_∞)` | ⚠ **weakened**: `eps0_le_a_div` needs only `0 ≤ a`, since `ε ≤ min(a,1)/4 ≤ a/4` for every `a ≥ 0` — **that step does not use `a < 1`**; `eps0_mem_Ioc` carries `0 < a` for the left end. `a < 1` is not carried anywhere in the Lean; in the paper it is not idle (see SCOPE) |
| `C₇ ≥ 0`, `C_∞ > 0` in the Step 4 chain | ✓ derived (`C7_nonneg`, `Cinf_pos`) in `eps0_mem_Ioc`; hypotheses of the abstract `eps0_le_a_div` |
| `C := max(1, C₇)` | ✓ printed formula, `max 1 (C7 …)` |
| `γ₀ > 0` "depending only on the same quantities" | ✓ `gamma0` at the printed `L`; positivity uses `g''(1) > 0`, `w_min > 0` and `‖w‖_{L^∞} > 0`, the last derived from `w ≥ w_min` at one state of a probability `λ` (`nonempty_of_total`, `wsup_pos`) |
| `0 < γ ≤ γ₀` | ⚠ **weakened** to `0 ≤ γ ≤ γ₀`, as in `local_convergence_gd` |
| `g` is `C³` on `[1−a,1+a]` (for part (iii), through `g' = gd` there) | ⚠ **weakened to the consequence used**: `hg : ∀ y, \|y−1\| < a → HasDerivAt g (gd y) y`, differentiability on the **open** window only, beside `htaylor`, which ties `gd` to `g''(1)` and `M₃`. Nothing outside the window is asked of `g` — this is the paper's point in extending `g'` by constants, and the global `hg` of `FirstVariation.hasDerivAt_loss_ipL2` (every `y > 0`) is not used |
| "is well defined" (i): `1 + h_k > 0` | ✓ `local_convergence_gd_window` (with the window `‖h_k‖_{L^∞} ≤ ε`) and `local_convergence_gd_welldefined` |
| (ii): `\|r_k − 1\| ≤ 2ε/(1−ε) ≤ 2a/3` | ✓ `abs_ratio_sub_one_le_two_a_div_three`, second conjunct of `local_convergence_gd_welldefined` |
| (iii): `D_k` is given by `theo:first_variation_full`, applied to the generator equal to `g` on `[1−a,1+a]` with `g'` extended by constants | ✓ **by a different route**: third conjunct of `local_convergence_gd_welldefined`, `t ↦ 𝓛_{g,ν}((1+h_k+td)λ)` has derivative `⟨D_k ∣ d⟩_λ` at `0`, for **every** `k` and **every** direction `d`, with `D_k = Flow.lossGrad`. It is the derivative of the loss **with `g` itself**; no modified generator is formed, because on a finite state space the derivative at `t = 0` only sees `g` near the values `r_k` takes (`hasDerivAt_loss_local`), and those lie in the window by (ii). The paper's sentence that the perturbed ratio stays in `(1−a,1+a)` for small `δ` is therefore not needed and not stated. The derivative is directional (Gâteaux) in every direction, as in `FirstVariation.lean`, not a Fréchet statement |
| `0 < a` for (ii)–(iii) | ✓ `ha : 0 < a` in `local_convergence_gd_welldefined` (at `a = 0` the open window is empty); `local_convergence_gd_window` needs only `0 ≤ a` |

## SCOPE (disclosed)

* **Finding: the inequality `ε₀ ≤ a/(16C_∞)` does not use `a < 1`.** Step 4 writes "since
  `C₇ ≥ 0` and `a < 1`"; the chain is `ε₀ ≤ ε/(2C_∞(2+C₇)) ≤ (a/4)/(4C_∞)`, and
  `ε ≤ min(a,1)/4 ≤ a/4` for every `a ≥ 0`. This is a remark on that one step, **not** on the
  hypothesis: in the paper `a < 1` keeps `[1−a,1+a]` inside `ℝ₊*`, where `g` is required to be
  `C³`, and it is not idle there. It is idle in the Lean only because `g` enters through
  hypotheses stated on the window (`htaylor`, `hg`), which at `a ≥ 1` simply ask more of `g`
  (e.g. differentiability at `0`).
* **The window induction is re-proved, not reused.** The invariant of Step 6 is a local `have`
  inside the strict `local_convergence_gd`; it is copied here (`local_convergence_gd_window`)
  rather than extracted, so the strict file is untouched. On graduation the two copies could be
  merged by exporting the invariant from `LocalConvergence.lean`; that is the master's call.
* **"Well defined" is proved in all three of its parts** (`local_convergence_gd_welldefined`),
  part (iii) by a route that forms no modified generator; see the checklist. `hg` is an added
  hypothesis of that one theorem, the consequence of the paper's `C³` that part (iii) consumes.
  The first-variation adjoint step is `FirstVariation.firstVariation_adjoint`, reused; its own
  disclosures (finite state space, directional derivative) apply.
* **Finite state space, `hcoer` in place of summable mixing, `hB1 : 1 ≤ B̂` added**, exactly as in
  `LocalConvergence.lean`.
* `sorry`-free.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### `ε₀ ∈ (0, a/(16C_∞)]` -/

/-- **`ε₀ ≤ a/(16C_∞)`** (`proofs.tex:643`): `ε₀ ≤ ε/(2C_∞(2+C₇)) ≤ (a/4)/(4C_∞)`. The paper
invokes `a < 1`; only `0 ≤ a` is used, `ε ≤ min(a,1)/4 ≤ a/4` holding for every `a ≥ 0`. -/
theorem eps0_le_a_div {a g2 wmin Kex Bhat Ci c7 rho c6 : ℝ} (ha0 : 0 ≤ a) (hCi : 0 < Ci)
    (hc7 : 0 ≤ c7) :
    eps0 (epsW a g2 wmin Kex Bhat) Ci c7 rho c6 ≤ a / (16 * Ci) := by
  have hden : 0 < 2 * Ci * (2 + c7) := by positivity
  have h4 : 4 * Ci ≤ 2 * Ci * (2 + c7) := by nlinarith
  have hwin : epsW a g2 wmin Kex Bhat ≤ a / 4 :=
    le_trans (epsW_le_window a g2 wmin Kex Bhat)
      (div_le_div_of_nonneg_right (min_le_left a 1) (by norm_num))
  have h1 : epsW a g2 wmin Kex Bhat / (2 * Ci * (2 + c7)) ≤ a / 4 / (2 * Ci * (2 + c7)) :=
    div_le_div_of_nonneg_right hwin hden.le
  have h2 : a / 4 / (2 * Ci * (2 + c7)) ≤ a / 4 / (4 * Ci) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h4
  have h3 : a / 4 / (4 * Ci) = a / (16 * Ci) := by
    rw [div_div]; ring_nf
  calc eps0 (epsW a g2 wmin Kex Bhat) Ci c7 rho c6
      ≤ epsW a g2 wmin Kex Bhat / (2 * Ci * (2 + c7)) := eps0_le_basin _ _ _ _ _
    _ ≤ a / 4 / (2 * Ci * (2 + c7)) := h1
    _ ≤ a / 4 / (4 * Ci) := h2
    _ = a / (16 * Ci) := h3

/-- **`ε₀ ∈ (0, a/(16C_∞)]`** (`proofs.tex:613`, chain at Step 4, `:643`), at the theorem's constants and under its
hypotheses. `‖w‖_{L^∞} > 0` is derived from `w ≥ w_min > 0` at one state. -/
theorem eps0_mem_Ioc {lam w : V → ℝ} {g2 a M3 wsup wmin Bhat lamMin : ℝ}
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat) :
    eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) (Cinf lamMin)
        (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup)
      ∈ Set.Ioc 0 (a / (16 * Cinf lamMin)) := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hwsupp : 0 < wsup := wsup_pos hwmin0 (hwmin x0) (hwsup x0)
  have hBpos : (0 : ℝ) < Bhat := lt_of_lt_of_le zero_lt_one hB1
  have hgw : 0 < g2 * wmin := mul_pos hg2 hwmin0
  have hc6 : 0 < C6 (Cg g2 a M3) wsup := C6_pos hg2 hM3 ha.le hwsupp
  have hc7 : 0 ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin := C7_nonneg hc6.le hgw.le
  have hCi : 0 < Cinf lamMin := Cinf_pos hlmin0
  have heW : 0 < epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat :=
    epsW_pos ha hg2 hwmin0 (Kexp_pos hg2 hM3 ha.le hwsupp) hBpos
  exact ⟨eps0_pos heW hCi hc7 (rhoL_pos hgw hBpos) hc6, eps0_le_a_div ha.le hCi hc7⟩

/-! ### `C := max(1, C₇) ≥ 1` -/

/-- **`C := max(1, C₇) ≥ 1`** (`proofs.tex:645`). -/
theorem one_le_max_C7 (c6 g2 wmin : ℝ) : 1 ≤ max 1 (C7 c6 g2 wmin) := le_max_left _ _

/-- **`theo:local_convergence_full`, the flow clause with the printed `C := max(1, C₇)`**
(`proofs.tex:612–618`, Step 5 at `:645`): `local_convergence_full` with `C₇` weakened to
`max(1, C₇)` by `le_max_right`. -/
theorem local_convergence_full_C {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ} {h : ℝ → V → ℝ}
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
          ≤ max 1 (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (fun x => h t x - (cinf - 1))
            ≤ 2 * Real.exp (-(rhoL g2 wmin Bhat * t / 2))
                * Graph.nrmL2 lam (perpL2 lam (h 0)) := by
  obtain ⟨cinf, h1, h2⟩ := local_convergence_full hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha
    hwsup hwmin0 hwmin hB1 hcoer htaylor hflow hnorm0
  exact ⟨cinf, le_trans h1 (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)), h2⟩

/-! ### `γ₀ > 0` -/

/-- **`γ₀ > 0`** (`proofs.tex:617`, formula at Step 6, `:652`) as soon as `L > 0`. -/
theorem gamma0_pos {g2 wmin L : ℝ} (hg2 : 0 < g2) (hwmin0 : 0 < wmin) (hL : 0 < L) :
    0 < gamma0 g2 wmin L := by
  simp only [gamma0]
  positivity

/-- `L = 2g''(1)‖w‖_{L^∞} + Kε > 0`. -/
theorem Lgd_pos {g2 wsup Kex eps : ℝ} (hg2 : 0 < g2) (hwsup : 0 < wsup) (hK0 : 0 ≤ Kex)
    (heps0 : 0 ≤ eps) : 0 < Lgd g2 wsup Kex eps := by
  simp only [Lgd]
  have h1 : 0 < g2 * wsup := mul_pos hg2 hwsup
  nlinarith [mul_nonneg hK0 heps0]

/-- **`γ₀ > 0`** at the theorem's constants and under its hypotheses; `‖w‖_{L^∞} > 0` is derived
by `wsup_pos`, as `local_convergence_gd` does. -/
theorem gamma0_pos_of_weights {lam w : V → ℝ} {g2 a M3 wsup wmin Bhat : ℝ}
    (htot : ∑ x, lam x = 1) (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB0 : 0 ≤ Bhat) :
    0 < gamma0 g2 wmin
      (Lgd g2 wsup (Kexp g2 a M3 wsup) (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat)) := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hwsupp : 0 < wsup := wsup_pos hwmin0 (hwmin x0) (hwsup x0)
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2.le hM3 ha0 hwsupp.le
  exact gamma0_pos hg2 hwmin0
    (Lgd_pos hg2 hwsupp hK0 (epsW_nonneg ha0 hg2.le hwmin0.le hK0 hB0))

/-! ### The descent iteration is well defined -/

/-- **`theo:local_convergence_full`, "the gradient descent … is well defined"**
(`proofs.tex:617`, the invariant `eq:gd_invariant` of Step 6 at `:669–677`): under the
hypotheses of `local_convergence_gd`, every iterate satisfies `‖h_k‖_{L^∞} ≤ ε`, hence
`0 < 1 + h_k` — the density `(1 + h_k)λ` is positive along the whole iteration. (The sharper
`3/4 ≤ 1 + h_k` is `Expansion.one_add_ge_of_le` applied to the first conjunct; it is not a
conjunct here.)

The induction is `local_convergence_gd`'s, re-proved: there it is a local `have`. -/
theorem local_convergence_gd_window {K : V → V → ℝ} {lam w : V → ℝ} {gd : ℝ → ℝ}
    {hk : ℕ → V → ℝ} {g2 a M3 wsup wmin Bhat lamMin gam : ℝ}
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
    ∀ k : ℕ, ∀ x : V, |hk k x| ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat ∧ 0 < 1 + hk k x := by
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
  have hLpos : 0 < Lgd g2 wsup (Kexp g2 a M3 wsup) (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) :=
    Lgd_pos hg2 hwsupp hK0 hew0
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
  -- the invariant `eq:gd_invariant`, by induction (copied from `local_convergence_gd`)
  have key : ∀ k : ℕ, (∀ x, |hk k x| ≤ eW)
      ∧ Graph.nrmL2 lam (perpL2 lam (hk k)) ≤ Graph.nrmL2 lam (perpL2 lam (hk 0))
      ∧ |Graph.meanL2 lam (hk k) - Graph.meanL2 lam (hk 0)|
          ≤ 2 * c7 * (Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2
            - Graph.nrmL2 lam (perpL2 lam (hk k)) ^ 2) := by
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
      have hgr : 0 ≤ gam * rhoL g2 wmin Bhat / 4 := by positivity
      have hmono : Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))
          ≤ Graph.nrmL2 lam (perpL2 lam (hk 0)) := by
        have hx : 0 ≤ gam * rhoL g2 wmin Bhat / 4 * Graph.nrmL2 lam (perpL2 lam (hk k)) :=
          mul_nonneg hgr hPknn
        linarith
      have htri : |Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk 0)|
          ≤ |Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk k)|
            + |Graph.meanL2 lam (hk k) - Graph.meanL2 lam (hk 0)| := by
        have hsp : Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk 0)
            = (Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk k))
              + (Graph.meanL2 lam (hk k) - Graph.meanL2 lam (hk 0)) := by ring
        rw [hsp]
        exact abs_add_le _ _
      have hdrift : |Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk 0)|
          ≤ 2 * c7 * (Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2
            - Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ^ 2) := by linarith
      refine ⟨fun x => ?_, hmono, hdrift⟩
      have hsplit := abs_le_Cinf_mean_add_perp hlmin0 hlmin htot (hk (k + 1)) x
      have hmk1 : |Graph.meanL2 lam (hk (k + 1))| ≤ e0 + 2 * c7 * e0 := by
        have h1 : |Graph.meanL2 lam (hk (k + 1))| - |Graph.meanL2 lam (hk 0)|
            ≤ |Graph.meanL2 lam (hk (k + 1)) - Graph.meanL2 lam (hk 0)| :=
          abs_sub_abs_le_abs_sub _ _
        have hle : Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2
            - Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ^ 2 ≤ e0 := by
          linarith [sq_nonneg (Graph.nrmL2 lam (perpL2 lam (hk (k + 1))))]
        have h2 : 2 * c7 * (Graph.nrmL2 lam (perpL2 lam (hk 0)) ^ 2
            - Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ^ 2) ≤ 2 * c7 * e0 :=
          mul_le_mul_of_nonneg_left hle (by linarith)
        linarith
      have hPk1e0 : Graph.nrmL2 lam (perpL2 lam (hk (k + 1))) ≤ e0 := le_trans hmono hP0le
      have hsum : |Graph.meanL2 lam (hk (k + 1))| + Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))
          ≤ e0 * (2 + 2 * c7) := by linarith
      calc |hk (k + 1) x|
          ≤ Ci * (|Graph.meanL2 lam (hk (k + 1))| + Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))) :=
            hsplit
        _ ≤ Ci * (e0 * (2 + 2 * c7)) := mul_le_mul_of_nonneg_left hsum hCi0.le
        _ ≤ eW := by linarith
  intro k x
  have hwin : |hk k x| ≤ eW := (key k).1 x
  have hquarter : eW ≤ 1 / 4 :=
    le_trans hewA (div_le_div_of_nonneg_right (min_le_right a 1) (by norm_num))
  refine ⟨hwin, ?_⟩
  have hneg : -eW ≤ hk k x := (abs_le.mp hwin).1
  linarith

/-! ### `D_k` is the gradient of the loss, with `g` differentiable only on the window

`proofs.tex:662`: "the ratio `r` at `(1+h_k)λ` … satisfies `|r−1| ≤ 2ε/(1−ε) ≤ 2a/3` … and `D_k`
is defined by Theorem `theo:first_variation_full` applied to the generator equal to `g` on
`[1−a,1+a]` with derivative extended by constants outside it". `FirstVariation.hasDerivAt_loss_ipL2`
asks `g` differentiable at **every** `y > 0`, the global hypothesis the paper avoids; the two
local variants below ask it only at the values the ratio takes. On a finite state space the
derivative at `t = 0` is local, so no modified generator is needed: the window is enough. -/

/-- **`|r − 1| ≤ 2a/3`** (`proofs.tex:662`) at `μ = (1+h)λ` with `|h| ≤ ε ≤ min(a,1)/4`:
`2ε/(1−ε) ≤ 2a/3`, as `1 − ε ≥ 3/4` and `ε ≤ a/4`. -/
theorem abs_ratio_sub_one_le_two_a_div_three {K : V → V → ℝ} {lam h : V → ℝ} {eps a : ℝ}
    (hKnn : ∀ x y, 0 ≤ K x y) (hinv : Core.IsInvariant lam K)
    (hh : ∀ x, |h x| ≤ eps) (heps0 : 0 ≤ eps) (heps : eps ≤ min a 1 / 4)
    {y : V} (hy : lam y ≠ 0) :
    |ratio K lam (fun x => 1 + h x) y - 1| ≤ 2 * a / 3 := by
  have h1 : eps ≤ 1 / 4 := le_trans heps (by have := min_le_right a 1; linarith)
  have h2 : eps ≤ a / 4 := le_trans heps (by have := min_le_left a 1; linarith)
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  have hq : 2 * eps / (1 - eps) ≤ 2 * a / 3 := by
    rw [div_le_iff₀ h1e]
    nlinarith
  exact le_trans (abs_ratio_sub_one_le_two_eps_div hKnn hinv hh h1 hy) hq

/-- **`FirstVariation.hasDerivAt_loss` with `g` differentiable only at the values `r` takes.**
The proof is that lemma's, whose `hg` is consumed at `r(x)` and nowhere else; `r > 0` is then not
needed either. -/
theorem hasDerivAt_loss_local {K : V → V → ℝ} {lam nu u : V → ℝ} {g gd : ℝ → ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x)
    (hg : ∀ x, HasDerivAt g (gd (ratio K lam u x)) (ratio K lam u x)) (d : V → ℝ) :
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
    rw [hz]; exact hg z
  exact hgz.comp (0 : ℝ) hpt

/-- **`theo:first_variation_full` at `ν_G = λ`, with `g` differentiable only at the values `r`
takes**: `FirstVariation.hasDerivAt_loss_ipL2` under the local hypothesis. The adjoint step is
`FirstVariation.firstVariation_adjoint`, reused. -/
theorem hasDerivAt_loss_ipL2_local {K : V → V → ℝ} {lam nu u : V → ℝ} {g gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hg : ∀ x, HasDerivAt g (gd (ratio K lam u x)) (ratio K lam u x))
    (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g)
      (Graph.ipL2 lam (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd) d) 0 := by
  rw [← firstVariation_adjoint hinv hK hlam hu d]
  exact hasDerivAt_loss_local hlam hu hg d

/-- **`theo:local_convergence_full`, "the gradient descent … is well defined"**, all three parts
(`proofs.tex:617`, proof `:662`): under the hypotheses of `local_convergence_gd`, with `0 < a` and
`g` differentiable with derivative `gd` on the open window `|y − 1| < a`, every iterate satisfies

* `0 < 1 + h_k` — the density of `(1 + h_k)λ` is positive;
* `|r_k − 1| ≤ 2a/3`, `r_k` the ratio at `(1 + h_k)λ`;
* `D_k = lossGrad(1 + h_k)` **is the gradient of `𝓛_{g,ν}`** at `(1 + h_k)λ`: for every direction
  `d`, `t ↦ 𝓛_{g,ν}((1 + h_k + t·d)λ)` has derivative `⟨D_k ∣ d⟩_λ` at `t = 0`.

`Core.IsInvariant lam K` is bridged to `Invariant K lam` by `invariant_of_isInvariant`, and
`Core.IsMarkovOn lam K` gives `K ≥ 0` by its `nonneg` field. -/
theorem local_convergence_gd_welldefined {K : V → V → ℝ} {lam w : V → ℝ} {g gd : ℝ → ℝ}
    {hk : ℕ → V → ℝ} {g2 a M3 wsup wmin Bhat lamMin gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (hg : ∀ y : ℝ, |y - 1| < a → HasDerivAt g (gd y) y)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hstep : ∀ k : ℕ, hk (k + 1) = fun x =>
      hk k x - gam * lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + hk k z) x)
    (hgam0 : 0 ≤ gam)
    (hgam : gam ≤ gamma0 g2 wmin
      (Lgd g2 wsup (Kexp g2 a M3 wsup) (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat)))
    (hnorm0 : Graph.nrmL2 lam (hk 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat) (Cinf lamMin)
          (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) (rhoL g2 wmin Bhat) (C6 (Cg g2 a M3) wsup)) :
    ∀ k : ℕ, (∀ x : V, 0 < 1 + hk k x)
      ∧ (∀ x : V, |ratio K lam (fun z => 1 + hk k z) x - 1| ≤ 2 * a / 3)
      ∧ ∀ d : V → ℝ,
          HasDerivAt
            (fun t : ℝ => loss K lam (fun z => lam z * w z) (fun x => 1 + hk k x + t * d x) g)
            (Graph.ipL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + hk k z) d) 0 := by
  obtain ⟨x0⟩ := nonempty_of_total htot
  have hwsup0 : 0 ≤ wsup := (wsup_pos hwmin0 (hwmin x0) (hwsup x0)).le
  have hB0 : (0 : ℝ) ≤ Bhat := le_trans zero_le_one hB1
  have hK0 : 0 ≤ Kexp g2 a M3 wsup := Kexp_nonneg hg2.le hM3 ha.le hwsup0
  have hew0 : 0 ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat :=
    epsW_nonneg ha.le hg2.le hwmin0.le hK0 hB0
  have hewA := epsW_le_window a g2 wmin (Kexp g2 a M3 wsup) Bhat
  have hwin := local_convergence_gd_window hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha.le hwsup
    hwmin0 hwmin hB1 hcoer htaylor hstep hgam0 hgam hnorm0
  intro k
  have hwk : ∀ x, |hk k x| ≤ epsW a g2 wmin (Kexp g2 a M3 wsup) Bhat := fun x => (hwin k x).1
  have hpos : ∀ x, 0 < 1 + hk k x := fun x => (hwin k x).2
  have hr : ∀ x, |ratio K lam (fun z => 1 + hk k z) x - 1| ≤ 2 * a / 3 := fun x =>
    abs_ratio_sub_one_le_two_a_div_three hK.nonneg hinv hwk hew0 hewA (hlam x).ne'
  refine ⟨hpos, hr, fun d => ?_⟩
  have hgr : ∀ x, HasDerivAt g (gd (ratio K lam (fun z => 1 + hk k z) x))
      (ratio K lam (fun z => 1 + hk k z) x) := fun x =>
    hg _ (lt_of_le_of_lt (hr x) (by linarith))
  exact hasDerivAt_loss_ipL2_local (nu := fun z => lam z * w z) (invariant_of_isInvariant hinv)
    hK.nonneg hlam hpos hgr d

end GFNBounds.Balance
