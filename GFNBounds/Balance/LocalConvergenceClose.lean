import GFNBounds.Balance.TrainingSpeedAssembled

/-!
# Theorem 10 as one statement: the flow is the gradient flow, it converges, at the actual `λ_min`

**`theo:local_convergence_full`** — statement `proofs.tex:666–672`, proof `proofs.tex:674–727`
(line numbers drift, kb 0036; the label is the anchor). Its body twin `theo:local_convergence`
(`cv_divergence.tex`) is certified through it.

> In the setting of Theorem `theo:db_stable_frozen_full`, assume moreover that `g(1)=g'(1)=0`, that
> `g` is `C³` on `[1−a,1+a]` for some `a∈(0,1)`, and that the state space `𝒮` is finite, with `λ` a
> probability and `λ(x)>0` for every `x∈𝒮`; set `λ_min:=min_{x∈𝒮}λ(x)` and `C_∞:=λ_min^{−1/2}`, so
> that `C_∞≥1`. For the DB loss, `T=K₂` […] is taken on the set `E` of pairs `(s,s')∈𝒮²` with
> `π_←(s'→s)>0` […]; `E` plays the role of `𝒮` and the probability `λ₂` that of `λ` — in particular
> `λ_min:=min_{e∈E}λ₂(e)` and `C_∞:=λ_min^{−1/2}`. Then there are explicit `ε₀∈(0,a/(16C_∞)]` and
> `C≥1`, depending only on `g''(1)`, `sup_{[1−a,1+a]}|g'''|`, `a`, `w_min`, `‖w‖_{L^∞}`, `B̂` and
> `C_∞`, such that for every initialization `μ₀=(1+h₀)λ` with `‖h₀‖_{L²(λ)}≤ε₀`, the *nonlinear*
> gradient flow `μ̇_t=−∇^λ𝓛_{g,ν}(μ_t)` converges to a balanced flow `c_∞λ` with
> `|c_∞−1−Πh₀|≤C‖h₀−Πh₀‖²` and `‖h_t−(c_∞−1)‖_{L²(λ)} ≤ 2e^{−ϱt/2}‖h₀−Πh₀‖_{L²(λ)}`. There is
> moreover an explicit `γ₀>0`, depending only on the same quantities, such that for every such `h₀`
> and every step `0<γ≤γ₀` the gradient descent `h_{k+1}:=h_k−γD_k`, `D_k` the density against `λ`
> of `∇^λ𝓛_{g,ν}((1+h_k)λ)`, is well defined and satisfies
> `‖h_{k+1}−Πh_{k+1}‖_{L²(λ)}≤(1−γϱ/4)‖h_k−Πh_k‖_{L²(λ)}` for every `k≥0`.

## Why this file exists

`TrainingSpeedAssembled.lean` closes every clause of the theorem (`C³` on the closed window,
existence and uniqueness of the flow, the DB instance) in separate declarations. Three readings
remained between those declarations and the printed sentence, each closed here:

1. **"the gradient flow `μ̇ = −∇^λ𝓛`"**: `local_convergence_full_exists` produces a solution of
   `IsGradientFlow … gd`, the ODE driven by the *formula* `lossGrad`; it did not state that this
   field **is** the `L²(λ)` gradient of `𝓛_{g,ν}` along the solution (the descent clause did, for
   `D_k`). Here it is a conjunct, at every `t ≥ 0` and in every direction, by
   `hasDerivAt_loss_ipL2_local` — the solution's ratios stay within `2a/3` of `1`, where `gd` is the
   classical `g'`.
2. **"converges to a balanced flow `c_∞λ`"** is stated as a limit, `‖h_t − (c_∞−1)‖ → 0`, besides
   the rate.
3. **`λ_min`, `‖w‖_{L^∞}` are the actual minimum and maximum** (`lamMinOf`, `supAbsOf`), not bounds,
   and `C_∞ ≥ 1` is a conjunct — "so that `C_∞ ≥ 1`". The bound readings of the library imply these
   (the exact value is one admissible bound), so nothing is lost; this is the literal form.

The whole theorem — constants, flow clause, descent clause — is one declaration for each loss:
`local_convergence_full_paper` (FM, any finite Markov kernel `T` with invariant probability
`λ > 0`) and `local_convergence_full_DB_paper` (`T = K₂` on `E`, `λ₂`, the minimum taken over `E`).

## What is proved

| | |
|---|---|
| `lamMinOf`, `lamMinOf_le`, `exists_lamMinOf_eq`, `lamMinOf_pos`, `supAbsOf`, `abs_le_supAbsOf`, `exists_supAbsOf_eq` | `λ_min := min λ` and `‖w‖_{L^∞} := max |w|`, attained |
| `tendsto_of_exp_decay` | a nonnegative quantity below `c e^{−ϱt/2}` on `[0,∞)` tends to `0` |
| **`local_convergence_full_paper`** | the theorem for the FM loss, as one statement |
| **`local_convergence_full_DB_paper`** | the theorem for the DB loss on `(E, K₂, λ₂)`, as one statement |
| **`twoState_DB_exists_check`** | inhabitation (kb 0025): the DB clause produces a gradient flow from a **non-balanced** start |

## Hypothesis checklist

| paper | here |
|---|---|
| setting of `theo:db_stable_frozen_full`: `T` Markov, `λ` invariant, `ν = wλ`, `w ≥ w_min > 0`, `g''(1) > 0`, `B̂ ≥ 1` a coercivity constant | ✓ `hK`, `hinv`, `fun z => lam z * w z`, `hwmin0`, `hwmin`, `hg2`, `hB1`, `hcoer`. `T` ergodic is not carried: `hcoer` forces it |
| `g(1) = g'(1) = 0`, `g` `C³` on `[1−a,1+a]`, `a ∈ (0,1)` | ✓ `hg1`, `hC3` (one-sided at `1 ± a`), `ha`; ✗ `g(1) = 0` and `a < 1` not carried (unused: a stronger theorem — both are inhabited, `(log x)²` at `a = 1/2`) |
| `g'` | ✓ `gd`, a derivative of `g` within the window (`hgd`); it is `deriv g` on the open window, the only place any solution evaluates it |
| `𝒮` finite, `λ` a probability, `λ > 0` | ✓ `[Fintype V]`, `htot`, `hlam` |
| `λ_min := min λ`, `C_∞ := λ_min^{−1/2} ≥ 1` | ✓ `lamMinOf lam` (attained, `≤ λ`), `Cinf`, `1 ≤ Cinf (lamMinOf lam)` |
| `‖w‖_{L^∞}` | ✓ `supAbsOf w = max |w|` |
| `ε₀ ∈ (0, a/(16C_∞)]`, `C ≥ 1`, `γ₀ > 0`, explicit, depending only on the listed quantities | ✓ `eps0W`, `CW`, `gamma0W` (printed formulas); dependence: `TrainingSpeedAssembled.constW_congr` |
| the flow from `(1+h₀)λ` is the gradient flow of `𝓛_{g,ν}` | ✓ exists, `IsGradientFlow`, and its field is the `L²(λ)` gradient at every `t ≥ 0`; unique among all solutions from `μ₀`; positive |
| converges to `c_∞λ` balanced, the two bounds | ✓ `Balanced`, the two printed bounds, and the limit |
| the descent, `0 < γ ≤ γ₀`, well defined, contraction `1 − γϱ/4` | ✓ every `hk` with `hk 0 = h₀` and the step recursion: `1 + h_k > 0`, ratios within `2a/3`, `D_k` the gradient, the contraction |
| DB: `T = K₂` on `E`, `λ₂`, `λ_min` over `E` | ✓ `local_convergence_full_DB_paper`: `edgeKernelE`, `edgeMeasureE`, `lamMinOf (edgeMeasureE pb lam)`, `w : E → ℝ`; that the balance loss on `E` is the DB loss is `C3Wrappers.loss_edgeE_eq_db`, that `K₂` maps `E` into itself `C3Wrappers.edgeKernel_mem_edgeSet` |

## SCOPE (disclosed)

* **Finite state space**, which is the paper's own setting for this theorem (no narrowing).
* **`g(1) = 0` and `a < 1` are not carried**; both unused. The theorem is not vacuous where they hold: it
  is inhabited at `g = (log x)²`, `a = 1/2` (`twoState_DB_exists_check`,
  `TrainingSpeedAssembled.twoState_exists_check`).
* **`g'` is a derivative `gd` within the window**, as in `TrainingSpeedAssembled.lean`; outside the
  window `gd` is arbitrary and invisible to every solution from the basin (their ratios stay within
  `2a/3` of `1`), but the flow predicate names it.
* **`B̂` is a hypothesis**, as printed ("`B̂ ≥ 1` a coercivity constant").
* **Uniqueness** is among all solutions of `IsGradientFlow` from `μ₀` with the same `gd`, the
  derivative at `t = 0` two-sided (kb 0025's convention).
* **`sorry`-free**; axioms `[propext, Classical.choice, Quot.sound]`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset Set Filter Topology

section ActualExtrema

variable {V : Type*} [Fintype V]

/-- **`λ_min := min_{x∈𝒮} λ(x)`**, the actual minimum (`1` on an empty space, never used there). -/
noncomputable def lamMinOf (lam : V → ℝ) : ℝ :=
  if h : (univ : Finset V).Nonempty then univ.inf' h lam else 1

/-- **`‖w‖_{L^∞} := max_{x∈𝒮} |w(x)|`**, the actual maximum (`0` on an empty space). -/
noncomputable def supAbsOf (w : V → ℝ) : ℝ :=
  if h : (univ : Finset V).Nonempty then univ.sup' h (fun x => |w x|) else 0

theorem lamMinOf_le (lam : V → ℝ) (x : V) : lamMinOf lam ≤ lam x := by
  have h : (univ : Finset V).Nonempty := ⟨x, mem_univ x⟩
  rw [lamMinOf, dif_pos h]
  exact inf'_le _ (mem_univ x)

theorem exists_lamMinOf_eq [Nonempty V] (lam : V → ℝ) : ∃ x, lam x = lamMinOf lam := by
  have h : (univ : Finset V).Nonempty := univ_nonempty
  obtain ⟨x, -, hx⟩ := exists_mem_eq_inf' h lam
  exact ⟨x, by rw [lamMinOf, dif_pos h, hx]⟩

theorem lamMinOf_pos [Nonempty V] {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) : 0 < lamMinOf lam := by
  obtain ⟨x, hx⟩ := exists_lamMinOf_eq lam
  rw [← hx]
  exact hlam x

theorem abs_le_supAbsOf (w : V → ℝ) (x : V) : |w x| ≤ supAbsOf w := by
  have h : (univ : Finset V).Nonempty := ⟨x, mem_univ x⟩
  rw [supAbsOf, dif_pos h]
  exact le_sup' (fun x => |w x|) (mem_univ x)

theorem exists_supAbsOf_eq [Nonempty V] (w : V → ℝ) : ∃ x, |w x| = supAbsOf w := by
  have h : (univ : Finset V).Nonempty := univ_nonempty
  obtain ⟨x, -, hx⟩ := exists_mem_eq_sup' h (fun x => |w x|)
  exact ⟨x, by rw [supAbsOf, dif_pos h, hx]⟩

end ActualExtrema

/-- A nonnegative quantity bounded by `c·e^{−ϱt/2}` on `[0,∞)`, `ϱ > 0`, tends to `0`. -/
theorem tendsto_of_exp_decay {f : ℝ → ℝ} {rho c : ℝ} (hrho : 0 < rho)
    (hnn : ∀ t, 0 ≤ f t) (hle : ∀ t : ℝ, 0 ≤ t → f t ≤ 2 * Real.exp (-(rho * t / 2)) * c) :
    Tendsto f atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => rho * t / 2) atTop atTop :=
    (tendsto_id.const_mul_atTop hrho).atTop_div_const two_pos
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rho * t / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hup : Tendsto (fun t : ℝ => 2 * Real.exp (-(rho * t / 2)) * c) atTop (𝓝 0) := by
    have := (hexp.const_mul 2).mul_const c
    simpa only [mul_zero, zero_mul] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall hnn) ((eventually_ge_atTop 0).mono hle)

section Paper

variable {V : Type*} [Fintype V]

/-- **`theo:local_convergence_full`, the FM loss, as printed** (`proofs.tex:666–672`): for any
Markov kernel `T` on a finite space with invariant probability `λ > 0`, a generator `C³` on
`[1−a,1+a]` with `g'(1) = 0 < g''(1)`, `ν = wλ` with `w ≥ w_min > 0`, and a coercivity constant
`B̂ ≥ 1`: with `λ_min := min λ`, `‖w‖_{L^∞} := max |w|`, `C_∞ := λ_min^{−1/2} ≥ 1`, the explicit
`ε₀ ∈ (0, a/(16C_∞)]`, `C ≥ 1`, `γ₀ > 0` are such that from every `‖h₀‖ ≤ ε₀`

* the gradient flow of `𝓛_{g,ν}` from `(1+h₀)λ` **exists**, its field **is** the `L²(λ)` gradient
  of `𝓛_{g,ν}` at every `t ≥ 0`, it is positive with ratios within `2a/3` of `1`, **unique** among
  all solutions from `μ₀`, and converges to a balanced `c_∞λ` with the two printed bounds;
* for every `0 < γ ≤ γ₀`, the gradient descent from `h₀` is well defined (`1 + h_k > 0`, `D_k` the
  gradient) and contracts `‖h_k − Πh_k‖` by `1 − γϱ/4` at every step. -/
theorem local_convergence_full_paper {K : V → V → ℝ} {lam w : V → ℝ} {g gd : ℝ → ℝ}
    {a wmin Bhat : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f)) :
    ((∃ x, lam x = lamMinOf lam) ∧ (∀ x, lamMinOf lam ≤ lam x) ∧ 1 ≤ Cinf (lamMinOf lam))
    ∧ (eps0W g a wmin (supAbsOf w) Bhat (lamMinOf lam) ∈ Set.Ioc 0 (a / (16 * Cinf (lamMinOf lam)))
        ∧ 1 ≤ CW g a wmin (supAbsOf w) ∧ 0 < gamma0W g a wmin (supAbsOf w) Bhat)
    ∧ ∀ h0 : V → ℝ, Graph.nrmL2 lam h0 ≤ eps0W g a wmin (supAbsOf w) Bhat (lamMinOf lam) →
      (∃ h : ℝ → V → ℝ, h 0 = h0
        ∧ IsGradientFlow K lam (fun z => lam z * w z) gd (fun s x => 1 + h s x)
        ∧ (∀ t : ℝ, 0 ≤ t → ∀ d : V → ℝ,
            HasDerivAt
              (fun s : ℝ => loss K lam (fun z => lam z * w z) (fun x => 1 + h t x + s * d x) g)
              (Graph.ipL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + h t z) d) 0)
        ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < 1 + h t x
            ∧ |ratio K lam (fun z => 1 + h t z) x - 1| ≤ 2 * a / 3)
        ∧ (∀ h' : ℝ → V → ℝ, h' 0 = h0 →
            IsGradientFlow K lam (fun z => lam z * w z) gd (fun s x => 1 + h' s x) →
            ∀ t : ℝ, 0 ≤ t → h' t = h t)
        ∧ ∃ cinf : ℝ, Balanced K lam (fun _ => cinf)
            ∧ |cinf - 1 - Graph.meanL2 lam h0|
                ≤ CW g a wmin (supAbsOf w) * Graph.nrmL2 lam (perpL2 lam h0) ^ 2
            ∧ (∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (fun x => h t x - (cinf - 1))
                ≤ 2 * Real.exp (-(rhoL (deriv (deriv g) 1) wmin Bhat * t / 2))
                    * Graph.nrmL2 lam (perpL2 lam h0))
            ∧ Tendsto (fun t => Graph.nrmL2 lam (fun x => h t x - (cinf - 1))) atTop (𝓝 0))
      ∧ ∀ gam : ℝ, 0 < gam → gam ≤ gamma0W g a wmin (supAbsOf w) Bhat →
        ∀ hk : ℕ → V → ℝ, hk 0 = h0 →
        (∀ k : ℕ, hk (k + 1) = fun x =>
          hk k x - gam * lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + hk k z) x) →
        ∀ k : ℕ, ((∀ x : V, 0 < 1 + hk k x)
          ∧ (∀ x : V, |ratio K lam (fun z => 1 + hk k z) x - 1| ≤ 2 * a / 3)
          ∧ ∀ d : V → ℝ,
              HasDerivAt
                (fun t : ℝ => loss K lam (fun z => lam z * w z) (fun x => 1 + hk k x + t * d x) g)
                (Graph.ipL2 lam (lossGrad K lam (fun z => lam z * w z) gd
                  fun z => 1 + hk k z) d) 0)
          ∧ Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))
              ≤ (1 - gam * rhoL (deriv (deriv g) 1) wmin Bhat / 4)
                  * Graph.nrmL2 lam (perpL2 lam (hk k)) := by
  haveI := nonempty_of_total htot
  have hlmin0 : 0 < lamMinOf lam := lamMinOf_pos hlam
  have hlmin : ∀ x, lamMinOf lam ≤ lam x := lamMinOf_le lam
  have hwsup : ∀ x, |w x| ≤ supAbsOf w := abs_le_supAbsOf w
  have hBpos : (0 : ℝ) < Bhat := lt_of_lt_of_le zero_lt_one hB1
  have hrho : 0 < rhoL (deriv (deriv g) 1) wmin Bhat := rhoL_pos (mul_pos hg2 hwmin0) hBpos
  refine ⟨⟨exists_lamMinOf_eq lam, hlmin, one_le_Cinf hlmin0 hlmin htot⟩,
    constW_bounds htot hlmin0 ha hC3 hg2 hwsup hwmin0 hwmin hB1, fun h0 hnorm0 => ⟨?_, ?_⟩⟩
  · obtain ⟨h, hh0, hflow, hpr, huniq, cinf, hbal, hc, hdec⟩ :=
      local_convergence_full_exists hK hinv hlam htot hlmin0 hlmin ha hC3 hgd hg1 hg2 hwsup
        hwmin0 hwmin hB1 hcoer hnorm0
    refine ⟨h, hh0, hflow, fun t ht d => ?_, hpr, huniq, cinf, hbal, hc, hdec,
      tendsto_of_exp_decay hrho (fun t => Graph.nrmL2_nonneg _ _) hdec⟩
    have hpos : ∀ x, 0 < 1 + h t x := fun x => (hpr t ht x).1
    have hgr : ∀ x, HasDerivAt g (gd (ratio K lam (fun z => 1 + h t z) x))
        (ratio K lam (fun z => 1 + h t z) x) := fun x => by
      have hr := (hpr t ht x).2
      have hy' : ratio K lam (fun z => 1 + h t z) x ∈ Ioo (1 - a) (1 + a) :=
        ⟨by linarith [(abs_le.mp hr).1], by linarith [(abs_le.mp hr).2]⟩
      exact (hgd _ (Ioo_subset_Icc_self hy')).hasDerivAt (mem_nhds_winC3 hy')
    exact hasDerivAt_loss_ipL2_local (nu := fun z => lam z * w z) (invariant_of_isInvariant hinv)
      hK.nonneg hlam hpos hgr d
  · intro gam hgam0 hgam hk hk0 hstep
    exact local_convergence_gd_C3On hK hinv hlam htot hlmin0 hlmin ha hC3 hgd hg1 hg2 hwsup
      hwmin0 hwmin hB1 hcoer hstep hgam0.le hgam (hk0 ▸ hnorm0)

end Paper

section PaperDB

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`theo:local_convergence_full`, the DB loss, as printed**: `local_convergence_full_paper` on
`E = {(s,s') : π_←(s'→s) > 0}` with `T = K₂` and `λ₂` in place of `λ`, `λ_min := min_{e∈E} λ₂(e)`,
`‖w‖_{L^∞} := max_E |w|`. The Markov property, invariance, positivity and total mass of `(K₂, λ₂)`
on `E` are proved from the backward policy (`C3Wrappers`); that the balance loss on `E` is the DB
loss is `C3Wrappers.loss_edgeE_eq_db`. -/
theorem local_convergence_full_DB_paper {pb : V → V → ℝ} {lam : V → ℝ} {w : EdgeSet pb → ℝ}
    {g gd : ℝ → ℝ} {a wmin Bhat : ℝ}
    (hpb : Core.IsMarkovOn lam pb) (hinvpb : Core.IsInvariant lam pb) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (ha : 0 < a) (hC3 : ContDiffOn ℝ 3 g (winC3 a))
    (hgd : ∀ y ∈ winC3 a, HasDerivWithinAt g (gd y) (winC3 a) y)
    (hg1 : deriv g 1 = 0) (hg2 : 0 < deriv (deriv g) 1)
    (hwmin0 : 0 < wmin) (hwmin : ∀ e, wmin ≤ w e)
    (hB1 : 1 ≤ Bhat)
    (hcoer : ∀ f : EdgeSet pb → ℝ,
      Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) f)
        ≤ Bhat * Graph.nrmL2 (edgeMeasureE pb lam)
            (Aop (edgeKernelE pb) (edgeMeasureE pb lam) f)) :
    ((∃ e, edgeMeasureE pb lam e = lamMinOf (edgeMeasureE pb lam))
        ∧ (∀ e, lamMinOf (edgeMeasureE pb lam) ≤ edgeMeasureE pb lam e)
        ∧ 1 ≤ Cinf (lamMinOf (edgeMeasureE pb lam)))
    ∧ (eps0W g a wmin (supAbsOf w) Bhat (lamMinOf (edgeMeasureE pb lam))
          ∈ Set.Ioc 0 (a / (16 * Cinf (lamMinOf (edgeMeasureE pb lam))))
        ∧ 1 ≤ CW g a wmin (supAbsOf w) ∧ 0 < gamma0W g a wmin (supAbsOf w) Bhat)
    ∧ ∀ h0 : EdgeSet pb → ℝ, Graph.nrmL2 (edgeMeasureE pb lam) h0
          ≤ eps0W g a wmin (supAbsOf w) Bhat (lamMinOf (edgeMeasureE pb lam)) →
      (∃ h : ℝ → EdgeSet pb → ℝ, h 0 = h0
        ∧ IsGradientFlow (edgeKernelE pb) (edgeMeasureE pb lam)
            (fun z => edgeMeasureE pb lam z * w z) gd (fun s x => 1 + h s x)
        ∧ (∀ t : ℝ, 0 ≤ t → ∀ d : EdgeSet pb → ℝ,
            HasDerivAt
              (fun s : ℝ => loss (edgeKernelE pb) (edgeMeasureE pb lam)
                (fun z => edgeMeasureE pb lam z * w z) (fun x => 1 + h t x + s * d x) g)
              (Graph.ipL2 (edgeMeasureE pb lam) (lossGrad (edgeKernelE pb) (edgeMeasureE pb lam)
                (fun z => edgeMeasureE pb lam z * w z) gd fun z => 1 + h t z) d) 0)
        ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < 1 + h t x
            ∧ |ratio (edgeKernelE pb) (edgeMeasureE pb lam) (fun z => 1 + h t z) x - 1|
                ≤ 2 * a / 3)
        ∧ (∀ h' : ℝ → EdgeSet pb → ℝ, h' 0 = h0 →
            IsGradientFlow (edgeKernelE pb) (edgeMeasureE pb lam)
              (fun z => edgeMeasureE pb lam z * w z) gd (fun s x => 1 + h' s x) →
            ∀ t : ℝ, 0 ≤ t → h' t = h t)
        ∧ ∃ cinf : ℝ, Balanced (edgeKernelE pb) (edgeMeasureE pb lam) (fun _ => cinf)
            ∧ |cinf - 1 - Graph.meanL2 (edgeMeasureE pb lam) h0|
                ≤ CW g a wmin (supAbsOf w)
                    * Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) h0) ^ 2
            ∧ (∀ t : ℝ, 0 ≤ t → Graph.nrmL2 (edgeMeasureE pb lam) (fun x => h t x - (cinf - 1))
                ≤ 2 * Real.exp (-(rhoL (deriv (deriv g) 1) wmin Bhat * t / 2))
                    * Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) h0))
            ∧ Tendsto (fun t => Graph.nrmL2 (edgeMeasureE pb lam) (fun x => h t x - (cinf - 1)))
                atTop (𝓝 0))
      ∧ ∀ gam : ℝ, 0 < gam → gam ≤ gamma0W g a wmin (supAbsOf w) Bhat →
        ∀ hk : ℕ → EdgeSet pb → ℝ, hk 0 = h0 →
        (∀ k : ℕ, hk (k + 1) = fun x =>
          hk k x - gam * lossGrad (edgeKernelE pb) (edgeMeasureE pb lam)
            (fun z => edgeMeasureE pb lam z * w z) gd (fun z => 1 + hk k z) x) →
        ∀ k : ℕ, ((∀ x, 0 < 1 + hk k x)
          ∧ (∀ x, |ratio (edgeKernelE pb) (edgeMeasureE pb lam) (fun z => 1 + hk k z) x - 1|
              ≤ 2 * a / 3)
          ∧ ∀ d : EdgeSet pb → ℝ,
              HasDerivAt
                (fun t : ℝ => loss (edgeKernelE pb) (edgeMeasureE pb lam)
                  (fun z => edgeMeasureE pb lam z * w z) (fun x => 1 + hk k x + t * d x) g)
                (Graph.ipL2 (edgeMeasureE pb lam) (lossGrad (edgeKernelE pb) (edgeMeasureE pb lam)
                  (fun z => edgeMeasureE pb lam z * w z) gd fun z => 1 + hk k z) d) 0)
          ∧ Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) (hk (k + 1)))
              ≤ (1 - gam * rhoL (deriv (deriv g) 1) wmin Bhat / 4)
                  * Graph.nrmL2 (edgeMeasureE pb lam) (perpL2 (edgeMeasureE pb lam) (hk k)) := by
  have hrow : ∀ x, ∑ y, pb x y = 1 := fun x => hpb.row_sum (hlam x).ne'
  exact local_convergence_full_paper (edgeKernelE_isMarkovOn hpb.nonneg hrow)
    (edgeMeasureE_isInvariant hpb.nonneg hinvpb.nonneg (invariant_of_isInvariant hinvpb))
    (edgeMeasureE_pos hlam) (edgeMeasureE_total hpb.nonneg hrow htot) ha hC3 hgd hg1 hg2
    hwmin0 hwmin hB1 hcoer

end PaperDB

section Checks

/-- **The DB clause is inhabited off balance** (kb 0025): on the uniform two-state policy
(`E = 𝒮²`, `λ₂ ≡ 1/4`, `B̂ = 2` by `C3Wrappers.coer_edgeU`), `g = (log x)²` at `a = 1/2`, `w ≡ 1`,
`local_convergence_full_DB_paper` produces a gradient flow from the **non-balanced** start
`h₀ = ε₀·(1_{(0,0)} − 1_{(0,1)})`. The earlier DB witness (`C3Wrappers`) used the trivial flow
`h ≡ 0`. -/
theorem twoState_DB_exists_check :
    ∃ h : ℝ → EdgeSet pbU → ℝ,
      IsGradientFlow (edgeKernelE pbU) (edgeMeasureE pbU lamU)
          (fun z => edgeMeasureE pbU lamU z * 1) logSqDeriv (fun s e => 1 + h s e)
        ∧ ¬ Balanced (edgeKernelE pbU) (edgeMeasureE pbU lamU) (fun e => 1 + h 0 e) := by
  obtain ⟨hC3, hgd, hg1, hg2⟩ := logSq_C3On_bundle
  have hlam2 : ∀ e, edgeMeasureE pbU lamU e = 1/4 := fun e => by
    simp only [edgeMeasureE, edgeMeasure, pbU, lamU]; norm_num
  obtain ⟨-, hconst, hmain⟩ := local_convergence_full_DB_paper (w := fun _ => (1:ℝ))
    (g := logSq) (gd := logSqDeriv) (a := 1/2) (wmin := 1) (Bhat := 2)
    pbU_markov pbU_invariant (fun _ => by norm_num [lamU])
    (by simp only [lamU, Fin.sum_univ_two]; norm_num) (by norm_num) hC3 hgd hg1 hg2 one_pos
    (fun _ => le_rfl) (by norm_num) coer_edgeU
  set ε := eps0W logSq (1/2) 1 (supAbsOf fun _ : EdgeSet pbU => (1:ℝ)) 2
    (lamMinOf (edgeMeasureE pbU lamU)) with hεdef
  have hεpos : 0 < ε := hconst.1.1
  set h0 : EdgeSet pbU → ℝ := fun e =>
    if e.1.1 = 0 then (if e.1.2 = 0 then ε else -ε) else 0 with hh0def
  have hnorm : Graph.nrmL2 (edgeMeasureE pbU lamU) h0 ≤ ε := by
    have hval : Graph.nrmL2 (edgeMeasureE pbU lamU) h0 = Real.sqrt (ε ^ 2 / 2) := by
      simp only [Graph.nrmL2, Graph.ipL2, hlam2]
      rw [sum_edgeSetU]
      congr 1
      simp only [hh0def]
      norm_num
      ring
    rw [hval]
    have h2 : ε ^ 2 / 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]
    calc Real.sqrt (ε ^ 2 / 2) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h2
      _ = ε := Real.sqrt_sq hεpos.le
  obtain ⟨⟨h, hh0, hflow, -⟩, -⟩ := hmain h0 hnorm
  refine ⟨h, hflow, fun hbal => ?_⟩
  have h1 := hbal ⟨(0, 0), pbU_pos _⟩
  have hK : ∀ e e' : EdgeSet pbU, edgeKernelE pbU e e' = if e'.1.2 = e.1.1 then 1/2 else 0 :=
    fun e e' => by simp only [edgeKernelE, edgeKernel, pbU]
  simp only [pushMass, hlam2, hK, hh0] at h1
  rw [sum_edgeSetU] at h1
  simp only [hh0def] at h1
  norm_num at h1
  linarith

end Checks

end GFNBounds.Balance
