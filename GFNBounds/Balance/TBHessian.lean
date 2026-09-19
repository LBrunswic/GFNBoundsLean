import GFNBounds.Balance.TBGradient
import GFNBounds.Balance.LiftFinite

/-!
# The trajectory-balance Hessian at the balanced edge flow, on a finite state space

**`prop:tb_hessian`** — statement and proof in `proofs.tex` right after `prop:tb_gradient`
(label is the anchor; line citations drift, kb `0036`). **`eq:tb_window_variance`** and
**`eq:tb_theta_bound`** are displays of its proof.

> In the setting of Proposition `prop:tb_gradient`, let `g(x) = (log x)²` and let `ν̂` be the
> window measure `ν̂(x_0,…,x_ℓ) := λ(x_ℓ) ∏_{k=1}^{ℓ} π_←(x_k → x_{k−1})`. Write `P` for the
> density action `h ↦ d((hλ₂)K₂)/dλ₂` of `K₂` on `L²(λ₂)`, `Q := P†`, `A := P − I`, `Π₂` for the
> `λ₂`-mean projection, `β̂_m := ‖K₂^m − Π₂‖_{L²(λ₂)}` as in Lemma `lem:lift_mixing`,
> `B̂′ := ∑_{m≥1} β̂_m`, and `Θ_ℓ := I + ∑_{m=1}^{ℓ−1}(1 − m/ℓ)(Q^m + (Q†)^m)`,
> `H_TB := ℓ g''(1) A†Θ_ℓA`, `H_DB := g''(1)A†A`. Then every edge marginal `ν̂_k` is `λ₂`, and for
> every norm `‖·‖` on `ℝ^E`, as `h → 0` in `ℝ^E`,
> `𝓛_{TB,g,ν̂}((1+h)λ₂) = ½⟨h, H_TB h⟩_{L²(λ₂)} + O(‖h‖³)`.
> The operator `Θ_ℓ` is self-adjoint and positive semi-definite on `L²(λ₂)`, and
> `Θ_ℓ ⪯ (1+2B̂′) I` on the mean-zero functions; consequently `0 ⪯ H_TB ⪯ ℓ(1+2B̂′) H_DB`,
> where `H_DB` is `H_TB` at `ℓ = 1`, at which `𝓛_{TB,g,ν̂}` is the DB loss `𝓛_{DB,g,λ₂}` of
> Proposition `prop:db_lift`. If `𝒮̂` has at least two states, `B̂′ ≥ 1`.

Every clause is certified, on the finite state space the statement is set in (the author's ruling
of 2026-09-14 put `prop:tb_gradient` and this proposition in finite form), with the proof's
explicit remainder `10ℓ²‖h‖³_∞` as well as the `O(‖h‖³)` form.

## What is proved

| | |
|---|---|
| `window` | the window measure `ν̂`, **as printed** |
| `window_along` | `ν̂` charges only trajectories along `E` — the hypothesis `prop:tb_gradient` puts on `ν̂` |
| **`edgeMarg_window`** | **every edge marginal `ν̂_k` is `λ₂`** (`TBGradient.edgeMarg`) |
| `window_state`, `window_tail`, **`window_two`** | the proof's first bullet: `x_0 ∼ λ`, and under `ν̂` the edges `e_ℓ, …, e_1` form a stationary `K₂`-chain: `𝔼 a(e_j)b(e_k) = ∫ b K₂^{k−j}a dλ₂` |
| `window_sq`, **`window_variance`** | **`eq:tb_window_variance`**: `𝔼_{ν̂}(∑_k u(e_k))² = ℓ⟨u, Θ_ℓ u⟩` for every `u ∈ L²(λ₂)` |
| `Theta`, `HTB`, `HDB`, `betaHat` | `Θ_ℓ`, `H_TB`, `H_DB`, `β̂_m` as printed; `A = Aop`, `A† = Adj` (`L2Toolkit`), `β̂_m` the operator norm of the density deviation (`LiftFinite.densDeviation`, `opNorm`) |
| `adj_Q` | **`Q = P†`**: the function action of `K₂` is the `L²(λ₂)`-adjoint of its density action, at every power |
| **`Theta_selfAdjoint`**, **`Theta_psd`** | `Θ_ℓ` self-adjoint and `⪰ 0` |
| `Theta_le_cesaro`, **`Theta_le`** | **`eq:tb_theta_bound`**: `⟨u,Θ_ℓu⟩ ≤ (1+2∑_{m<ℓ}(1−m/ℓ)β̂_m)‖u‖² ≤ (1+2B̂′)‖u‖²` on mean-zero `u` |
| `cesaro_sum`, `abs_ip_Theta_le` | `1 + 2∑(1−m/ℓ) = ℓ`, hence `‖Θ_ℓ‖ ≤ ℓ` (proof, expansion bullet) |
| `loss_eq_window`, `ratio_perturb`, `abs_densAct_le`, `abs_log_one_add_sub_le` | the expansion's steps: `𝓛_TB = 𝔼(∑ log r̂(e_k))²`, `r̂ = (1+Ph)/(1+h)`, `|Ph| ≤ ‖h‖_∞`, `|log(1+t) − t| ≤ t²` on `|t| ≤ ½` |
| **`expansion_explicit`** | **the expansion with the proof's remainder**: `|𝓛_TB((1+h)λ₂) − ½⟨h,H_TB h⟩| ≤ 10ℓ²δ³` whenever `‖h‖_∞ ≤ δ ≤ ½` |
| **`expansion_isBigO`** | **the expansion as printed**, `O(‖h‖³)` at `0` **for every norm on `ℝ^E`** |
| **`HTB_nonneg`**, **`HTB_le`** | **`0 ⪯ H_TB ⪯ ℓ(1+2B̂′)H_DB`** (with `mean_Aop`: `Ah` is mean-zero) |
| **`HTB_one`**, **`loss_one`** | **`H_DB = H_TB` at `ℓ = 1`**, and **at `ℓ = 1` the TB loss is the DB loss** `Freezing.loss K₂ λ₂ λ₂ (μ/λ₂) g`, which `C3Wrappers.loss_edgeE_eq_db` identifies with the detailed-balance loss of `prop:db_lift`; for every `g` |
| **`betaHat_one`**, **`one_le_Bprime`** | **`β̂₁ = β₀ = 1`** when `𝒮̂` has two states, hence **`B̂′ ≥ 1`** |
| `stepCap` | `rem:tb_vs_db`'s step cap: a bound `L` on `H_DB` gives `ℓ(1+2B̂′)L` on `H_TB` |
| `witness` | **inhabitation** (kb `0025`): the uniform two-state chain satisfies every hypothesis, has `β̂₁ = 1`, `β̂_m = 0` for `m ≥ 2`, so `B = 1` bounds `B̂′` and `HTB_le` is non-vacuous there |

## SCOPE (disclosed)

* **Finite state space**, as the statement is (`prop:tb_gradient`'s setting). `E`, `λ₂`, `K₂` are
  `C3Wrappers`' `EdgeSet`, `edgeMeasureE`, `edgeKernelE`; `L²(λ₂)` is `E → ℝ` with
  `Graph.ipL2`/`Graph.nrmL2` against `λ₂ > 0`; measures on `E` are weight vectors (the paper's
  own identification), so `(1+h)λ₂` is `fun e => (1 + h e) * λ₂ e`.
* **`Q := P†` is realized as the function action `funAct K₂`**, and `(Q†)^m` as `P^m`
  (`Core.densAct`); `adj_Q` proves the adjoint relation at every power, which is what makes these
  the paper's `Q`, `Q†`. `A† = Q − I` is `L2Toolkit.Adj`, whose adjointness is `ipL2_Adj_left`.
* **`B̂′ = ∑_{m≥1}β̂_m` may be `+∞`** (e.g. a periodic chain). Every inequality in `B̂′` is stated
  for every real bound `B` of its partial sums (kb `0031`), vacuous exactly when `B̂′ = +∞`, where
  the paper's inequality is vacuous too. `Theta_le_cesaro` is the sharper finite form the proof
  writes first.
* **"For every norm `‖·‖` on `ℝ^E`"** is carried as: every normed space `F` with a linear
  isomorphism `φ : F ≃ₗ ℝ^E` (the norm transported). The explicit form is in `‖h‖_∞`, the proof's
  norm; `Pi`'s sup norm is Mathlib's default norm on `E → ℝ`.
* **`g''(1)` is `deriv (deriv logSq) 1`** in `HTB`/`HDB`, equal to `2` (`logSq_deriv2_one`).
* **"`𝓛_{TB}` is the DB loss `𝓛_{DB,g,λ₂}` at `ℓ = 1`"** is certified as equality with the library's
  balance loss of `K₂` on `(E, λ₂)` at the density `μ/λ₂` (`loss_one`), which is how the DB loss of
  `prop:db_lift` is read on `E` elsewhere in the library (`C3Wrappers.loss_edgeE_eq_db`); `loss_one`
  holds for every `g`, not only `(log x)²`.
* **`ℓ ≥ 1` is not carried** where it is not used: `window_variance`, `Theta_psd`, the expansion
  and the sandwich hold at `ℓ = 0` too (`Θ_0 = I`, `H_TB = 0`, the loss is `0`); `abs_ip_Theta_le`
  and `cesaro_sum` ask `1 ≤ ℓ`.
* **The `sorry` list is empty and this file adds nothing to it.**

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒮̂` finite, `π_←` a Markov kernel | ✓ `[Fintype V]`, `hnn : ∀ x y, 0 ≤ pb x y`, `hrow : ∀ x, ∑ y, pb x y = 1` |
| `λ` a `π_←`-invariant probability, `λ > 0` | ✓ `hinv : Invariant pb lam`, `htot : ∑ λ = 1`, `hlam : ∀ x, 0 < lam x` (each declaration carries only what it uses) |
| `E`, `K₂`, `λ₂`, `L²(λ₂)` | ✓ as in `TBGradient.lean` |
| `g(x) = (log x)²` | ✓ `logSq` |
| `ν̂` the window measure | ✓ `window pb lam ℓ`, verbatim |
| `P`, `Q = P†`, `A`, `Π₂`, `β̂_m`, `B̂′`, `Θ_ℓ`, `H_TB`, `H_DB` | ✓ see SCOPE for `Q`, `B̂′` |
| "for every norm on `ℝ^E`, as `h → 0`" | ✓ `expansion_isBigO`, every normed `F ≃ₗ ℝ^E` |
| "if `𝒮̂` has at least two states" | ✓ `x ≠ y` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance.TBHessian

open Finset

variable {V : Type*}

/-! ### The window measure and its path calculus -/

section Path

variable [Fintype V]

variable (pb : V → V → ℝ) (lam : V → ℝ)

/-- **`prop:tb_hessian`, the window measure** `ν̂(x_0, …, x_ℓ) := λ(x_ℓ) ∏_{k=1}^{ℓ} π_←(x_k → x_{k−1})`, the paper's
display, on trajectories `τ : Fin (ℓ+1) → 𝒮̂`. -/
def window (ℓ : ℕ) (τ : Fin (ℓ + 1) → V) : ℝ :=
  lam (τ (Fin.last ℓ)) * ∏ k : Fin ℓ, pb (τ k.succ) (τ k.castSucc)

/-- The function action of `K₂` on functions of pairs, `(K₂f)(s,s') = ∑_z π_←(s → z) f(z,s)`
(`Lift.funActEdge_apply`). -/
def Qv (f : V → V → ℝ) : V → V → ℝ := fun s _ => ∑ z, pb s z * f z s

variable {pb lam}

omit [Fintype V] in
theorem window_cons (ℓ : ℕ) (x : V) (τ : Fin (ℓ + 1) → V) :
    window pb lam (ℓ + 1) (Fin.cons x τ) = pb (τ 0) x * window pb lam ℓ τ := by
  simp only [window, Fin.prod_univ_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.castSucc_zero,
    Fin.cons_zero, ← Fin.succ_last]
  ring

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → V) → ℝ) :
    ∑ τ, F τ = ∑ x, ∑ τ : Fin n → V, F (Fin.cons x τ) := by
  rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
  rfl

omit [Fintype V] in
/-- The trajectory weights charge only trajectories along `E`. -/
theorem window_along (hnn : ∀ x y, 0 ≤ pb x y) {ℓ : ℕ} (τ : Fin (ℓ + 1) → V)
    (h : window pb lam ℓ τ ≠ 0) : TBGradient.AlongE pb τ := by
  intro k
  have hp : ∏ k : Fin ℓ, pb (τ k.succ) (τ k.castSucc) ≠ 0 := right_ne_zero_of_mul h
  have hk := (Finset.prod_ne_zero_iff.mp hp) k (Finset.mem_univ k)
  exact lt_of_le_of_ne (hnn _ _) (Ne.symm hk)

/-- Summing out `x_0`: a function of the tail sees the window measure of length `ℓ`. -/
theorem window_tail (hrow : ∀ x, ∑ y, pb x y = 1) (ℓ : ℕ) (G : (Fin (ℓ + 1) → V) → ℝ) :
    ∑ τ, window pb lam (ℓ + 1) τ * G (Fin.tail τ) = ∑ τ, window pb lam ℓ τ * G τ := by
  rw [sum_cons, Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [window_cons, Fin.tail_cons]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hrow, one_mul]

/-- **Stationarity of `x_0`**: `∑_τ ν̂(τ) φ(x_0) = ∫ φ dλ`. -/
theorem window_state (hinv : Invariant pb lam) : ∀ (ℓ : ℕ) (φ : V → ℝ),
    ∑ τ, window pb lam ℓ τ * φ (τ 0) = ∑ x, lam x * φ x
  | 0, φ => by
      rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [window]
  | ℓ + 1, φ => by
      rw [sum_cons, Finset.sum_comm]
      have ih := window_state hinv ℓ (fun y => ∑ x, pb y x * φ x)
      have h1 : ∀ τ : Fin (ℓ + 1) → V, ∑ x, window pb lam (ℓ + 1) (Fin.cons x τ)
          * φ ((Fin.cons x τ : Fin (ℓ + 2) → V) 0)
          = window pb lam ℓ τ * ∑ x, pb (τ 0) x * φ x := by
        intro τ
        simp only [window_cons, Fin.cons_zero, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [Finset.sum_congr rfl fun τ _ => h1 τ, ih]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hinv x, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring

/-- **The two-point law of the edges**: for `j ≤ k` (Lean indices), under `ν̂` the edge `e_j` is
the state at time `k − j` of the `K₂`-chain started from `e_k ∼ λ₂`, so
`∑_τ ν̂(τ) a(e_j) b(e_k) = ∫ b · K₂^{k−j} a dλ₂`. -/
theorem window_two (hinv : Invariant pb lam) (hrow : ∀ x, ∑ y, pb x y = 1) :
    ∀ (ℓ : ℕ) (j k : Fin ℓ), j ≤ k → ∀ a b : V → V → ℝ,
      ∑ τ, window pb lam ℓ τ * (a (τ j.castSucc) (τ j.succ) * b (τ k.castSucc) (τ k.succ))
        = ∑ s, ∑ s', edgeMeasure pb lam s s' * (b s s' * (Qv pb)^[k.val - j.val] a s s')
  | 0, j, _, _, _, _ => j.elim0
  | ℓ + 1, j, k, hjk, a, b => by
      induction j using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero =>
          rw [sum_cons, Finset.sum_comm]
          have h1 : ∀ τ : Fin (ℓ + 1) → V, ∑ x, window pb lam (ℓ + 1) (Fin.cons x τ)
              * (a ((Fin.cons x τ : Fin (ℓ + 2) → V) (0 : Fin (ℓ + 1)).castSucc)
                  ((Fin.cons x τ : Fin (ℓ + 2) → V) (0 : Fin (ℓ + 1)).succ)
                * b ((Fin.cons x τ : Fin (ℓ + 2) → V) (0 : Fin (ℓ + 1)).castSucc)
                  ((Fin.cons x τ : Fin (ℓ + 2) → V) (0 : Fin (ℓ + 1)).succ))
              = window pb lam ℓ τ * ∑ x, pb (τ 0) x * (a x (τ 0) * b x (τ 0)) := by
            intro τ
            simp only [window_cons, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
              Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
          have hs := window_state hinv ℓ (fun y => ∑ x, pb y x * (a x y * b x y))
          rw [Finset.sum_congr rfl fun τ _ => h1 τ, hs]
          simp only [Fin.val_zero, Nat.sub_self, Function.iterate_zero, id, edgeMeasure,
            Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
        | succ k' =>
          rw [sum_cons, Finset.sum_comm]
          have hℓ : 0 < ℓ := Nat.lt_of_le_of_lt (Nat.zero_le _) k'.isLt
          have ih := window_two hinv hrow ℓ ⟨0, hℓ⟩ k' (show (0 : ℕ) ≤ k'.val from Nat.zero_le _) (Qv pb a) b
          have h1 : ∀ τ : Fin (ℓ + 1) → V, ∑ x, window pb lam (ℓ + 1) (Fin.cons x τ)
              * (a ((Fin.cons x τ : Fin (ℓ + 2) → V) (0 : Fin (ℓ + 1)).castSucc)
                  ((Fin.cons x τ : Fin (ℓ + 2) → V) (0 : Fin (ℓ + 1)).succ)
                * b ((Fin.cons x τ : Fin (ℓ + 2) → V) k'.succ.castSucc)
                  ((Fin.cons x τ : Fin (ℓ + 2) → V) k'.succ.succ))
              = window pb lam ℓ τ * (Qv pb a (τ (⟨0, hℓ⟩ : Fin ℓ).castSucc)
                  (τ (⟨0, hℓ⟩ : Fin ℓ).succ) * b (τ k'.castSucc) (τ k'.succ)) := by
            intro τ
            simp only [window_cons, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
              ← Fin.succ_castSucc, Qv]
            have h0 : (⟨0, hℓ⟩ : Fin ℓ).castSucc = 0 := rfl
            rw [h0, Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
          rw [Finset.sum_congr rfl fun τ _ => h1 τ, ih]
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
          simp only [Fin.val_succ, Fin.val_zero, Nat.sub_zero]
          rw [Function.iterate_succ_apply]
      | succ j' =>
        induction k using Fin.cases with
        | zero => exact absurd hjk (not_le.mpr (Fin.succ_pos j'))
        | succ k' =>
          have hjk' : j' ≤ k' := Fin.succ_le_succ_iff.mp hjk
          have ih := window_two hinv hrow ℓ j' k' hjk' a b
          have htail := window_tail (lam := lam) hrow ℓ
            (fun τ => a (τ j'.castSucc) (τ j'.succ) * b (τ k'.castSucc) (τ k'.succ))
          simp only [Fin.tail] at htail
          simp only [← Fin.succ_castSucc]
          rw [htail, ih]
          simp only [Fin.val_succ, Nat.add_sub_add_right]

variable (pb lam) in
/-- `∫ U · K₂^n U dλ₂`, on functions of pairs. -/
noncomputable def corr (U : V → V → ℝ) (n : ℕ) : ℝ :=
  ∑ s, ∑ s', edgeMeasure pb lam s s' * (U s s' * (Qv pb)^[n] U s s')

/-- **The window variance** (`eq:tb_window_variance`, before the regrouping into `Θ_ℓ`):
`∑_τ ν̂(τ) (∑_k U(e_k))² = ℓ ∫U² dλ₂ + 2 ∑_{m=1}^{ℓ} (ℓ − m) ∫ U K₂^m U dλ₂`. -/
theorem window_sq (hinv : Invariant pb lam) (hrow : ∀ x, ∑ y, pb x y = 1) (U : V → V → ℝ) :
    ∀ ℓ : ℕ, ∑ τ, window pb lam ℓ τ * (∑ k : Fin ℓ, U (τ k.castSucc) (τ k.succ)) ^ 2
      = ℓ * corr pb lam U 0
        + 2 * ∑ m ∈ range ℓ, ((ℓ : ℝ) - (m + 1)) * corr pb lam U (m + 1)
  | 0 => by simp
  | ℓ + 1 => by
      have hA : ∑ τ, window pb lam (ℓ + 1) τ
          * (U (τ (0 : Fin (ℓ + 1)).castSucc) (τ (0 : Fin (ℓ + 1)).succ)
            * U (τ (0 : Fin (ℓ + 1)).castSucc) (τ (0 : Fin (ℓ + 1)).succ))
          = corr pb lam U 0 := by
        rw [window_two hinv hrow (ℓ + 1) 0 0 le_rfl U U]
        simp only [corr, Nat.sub_self, Function.iterate_zero, id]
      have hB : ∀ k' : Fin ℓ, ∑ τ, window pb lam (ℓ + 1) τ
          * (U (τ (0 : Fin (ℓ + 1)).castSucc) (τ (0 : Fin (ℓ + 1)).succ)
            * U (τ k'.succ.castSucc) (τ k'.succ.succ))
          = corr pb lam U (k'.val + 1) := by
        intro k'
        rw [window_two hinv hrow (ℓ + 1) 0 k'.succ (Fin.zero_le _) U U]
        simp only [corr, Fin.val_succ, Fin.val_zero, Nat.sub_zero]
      have hC := window_tail (lam := lam) hrow ℓ
        (fun τ => (∑ k : Fin ℓ, U (τ k.castSucc) (τ k.succ)) ^ 2)
      simp only [Fin.tail, Fin.succ_castSucc] at hC
      have ih := window_sq hinv hrow U ℓ
      have hexp : ∀ τ : Fin (ℓ + 2) → V,
          window pb lam (ℓ + 1) τ * (∑ k : Fin (ℓ + 1), U (τ k.castSucc) (τ k.succ)) ^ 2
          = window pb lam (ℓ + 1) τ
              * (U (τ (0 : Fin (ℓ + 1)).castSucc) (τ (0 : Fin (ℓ + 1)).succ)
                * U (τ (0 : Fin (ℓ + 1)).castSucc) (τ (0 : Fin (ℓ + 1)).succ))
            + 2 * ∑ k' : Fin ℓ, window pb lam (ℓ + 1) τ
              * (U (τ (0 : Fin (ℓ + 1)).castSucc) (τ (0 : Fin (ℓ + 1)).succ)
                * U (τ k'.succ.castSucc) (τ k'.succ.succ))
            + window pb lam (ℓ + 1) τ
              * (∑ k : Fin ℓ, U (τ k.succ.castSucc) (τ k.succ.succ)) ^ 2 := by
        intro τ
        rw [Fin.sum_univ_succ, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
      rw [Finset.sum_congr rfl fun τ _ => hexp τ, Finset.sum_add_distrib, Finset.sum_add_distrib,
        hA, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun k' _ => hB k', hC, ih,
        Fin.sum_univ_eq_sum_range (fun m => corr pb lam U (m + 1)) ℓ, Finset.sum_range_succ]
      push_cast
      have hsplit : ∑ m ∈ range ℓ, ((ℓ : ℝ) + 1 - (m + 1)) * corr pb lam U (m + 1)
          = ∑ m ∈ range ℓ, ((ℓ : ℝ) - (m + 1)) * corr pb lam U (m + 1)
            + ∑ m ∈ range ℓ, corr pb lam U (m + 1) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ => by ring
      rw [hsplit]
      ring

end Path

/-! ### On the edge set `E`: the operators of the statement -/

section Edge

variable [Fintype V] [DecidableEq V] {pb : V → V → ℝ} {lam : V → ℝ}

/-- A function on `E`, extended by `0` to all pairs. -/
noncomputable def uAt (u : EdgeSet pb → ℝ) (s s' : V) : ℝ :=
  if h : 0 < pb s' s then u ⟨(s, s'), h⟩ else 0

omit [Fintype V] [DecidableEq V] in
theorem uAt_edge (u : EdgeSet pb → ℝ) (e : EdgeSet pb) : uAt u e.1.1 e.1.2 = u e := by
  simp only [uAt, dif_pos e.2]

omit [DecidableEq V] in
/-- A sum over pairs against `λ₂` is a sum over `E`. -/
theorem pair_sum_eq (hnn : ∀ x y, 0 ≤ pb x y) (F : V → V → ℝ) :
    ∑ s, ∑ s', edgeMeasure pb lam s s' * F s s'
      = ∑ e : EdgeSet pb, edgeMeasureE pb lam e * F e.1.1 e.1.2 := by
  have h := sum_edgeSet_eq (pb := pb) (fun p : V × V => edgeMeasure pb lam p.1 p.2 * F p.1 p.2)
    (fun p hp => by rw [edgeMeasure_eq_zero_of_not_mem hnn lam hp, zero_mul])
  rw [← Fintype.sum_prod_type' (fun s s' => edgeMeasure pb lam s s' * F s s'), ← h]
  rfl

/-- `K₂` on pairs, read on `E`, is the function action of `K₂` on `E`, iterates included. -/
theorem Qv_iterate_uAt (hnn : ∀ x y, 0 ≤ pb x y) (u : EdgeSet pb → ℝ) :
    ∀ (n : ℕ) (e : EdgeSet pb),
      (Qv pb)^[n] (uAt u) e.1.1 e.1.2 = (funAct (edgeKernelE pb))^[n] u e
  | 0, e => uAt_edge u e
  | n + 1, e => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      let f : V × V → ℝ := fun p =>
        if p.2 = e.1.1 then pb e.1.1 p.1 * (Qv pb)^[n] (uAt u) p.1 p.2 else 0
      have hf : ∀ p : V × V, ¬ 0 < pb p.2 p.1 → f p = 0 := by
        intro p hp
        simp only [f]
        split_ifs with h
        · have h0 : pb e.1.1 p.1 = 0 := by
            rw [← h]; exact le_antisymm (not_lt.mp hp) (hnn _ _)
          rw [h0, zero_mul]
        · rfl
      have hR : funAct (edgeKernelE pb) ((funAct (edgeKernelE pb))^[n] u) e
          = ∑ e' : EdgeSet pb, f e'.1 := by
        simp only [funAct, f]
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [TBGradient.K2_apply, ← Qv_iterate_uAt hnn u n e']
        split_ifs <;> simp
      rw [hR, sum_edgeSet_eq f hf, Fintype.sum_prod_type]
      simp only [Qv, f]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp

/-- `∫ U K₂^n U dλ₂` for `U` a function on `E` is `⟨u, Q^n u⟩_{L²(λ₂)}`. -/
theorem corr_uAt (hnn : ∀ x y, 0 ≤ pb x y) (u : EdgeSet pb → ℝ) (n : ℕ) :
    corr pb lam (uAt u) n
      = Graph.ipL2 (edgeMeasureE pb lam) u ((funAct (edgeKernelE pb))^[n] u) := by
  rw [corr, pair_sum_eq hnn]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [uAt_edge, Qv_iterate_uAt hnn u n e]

variable (pb lam)

/-- **`Θ_ℓ := I + ∑_{m=1}^{ℓ−1} (1 − m/ℓ)(Q^m + (Q†)^m)`**, with `Q = P†` the function action
`funAct K₂` and `Q† = P` the density action `Core.densAct λ₂ K₂` (`adj_Q`). -/
noncomputable def Theta (ℓ : ℕ) (u : EdgeSet pb → ℝ) : EdgeSet pb → ℝ :=
  fun e => u e + ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ)
    * ((funAct (edgeKernelE pb))^[m] u e
      + (Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] u e)

/-- **`H_TB := ℓ g''(1) A†Θ_ℓ A`**, `g = (log x)²`, `A = P − I` (`Aop`), `A† = Q − I` (`Adj`). -/
noncomputable def HTB (ℓ : ℕ) (h : EdgeSet pb → ℝ) : EdgeSet pb → ℝ :=
  fun e => ℓ * deriv (deriv logSq) 1
    * Adj (edgeKernelE pb) (Theta pb lam ℓ (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h)) e

/-- **`H_DB := g''(1) A†A`**. -/
noncomputable def HDB (h : EdgeSet pb → ℝ) : EdgeSet pb → ℝ :=
  fun e => deriv (deriv logSq) 1
    * Adj (edgeKernelE pb) (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h) e

/-- **`β̂_m := ‖K₂^m − Π₂‖_{L²(λ₂)}`** as in `lem:lift_mixing`: the operator norm of the density
deviation `P^m − Π₂` on `L²(λ₂)` over `E`. -/
noncomputable def betaHat (m : ℕ) : ℝ :=
  opNorm (edgeMeasureE pb lam) (densDeviation (edgeKernelE pb) (edgeMeasureE pb lam) m)

variable {pb lam}

theorem edgeKernelE_isMarkov (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1) :
    Core.IsMarkov (edgeKernelE pb) :=
  ⟨fun _ _ => edgeKernel_nonneg hnn _ _ _ _, TBGradient.K2_row_sum hnn hrow⟩

theorem edgeMeasureE_isInvariant' (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x)
    (hinv : Invariant pb lam) : Core.IsInvariant (edgeMeasureE pb lam) (edgeKernelE pb) :=
  edgeMeasureE_isInvariant hnn (fun x => (hlam x).le) hinv

/-- **`Q = P†`**: the function action of `K₂` is the `L²(λ₂)`-adjoint of its density action, at
every power — `lem:adjoint`*(3)* on `E`. -/
theorem adj_Q (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam)
    (m : ℕ) (u v : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] u) v
      = Graph.ipL2 (edgeMeasureE pb lam) u ((funAct (edgeKernelE pb))^[m] v) :=
  ipL2_densAct_iterate (edgeMeasureE_isInvariant' hnn hlam hinv)
    (fun _ _ => edgeKernel_nonneg hnn _ _ _ _) m u v

omit [Fintype V] in
theorem funAct_iterate_add {α : Type*} [Fintype α] (K : α → α → ℝ) :
    ∀ (m : ℕ) (a b : α → ℝ), (funAct K)^[m] (fun x => a x + b x)
      = fun x => (funAct K)^[m] a x + (funAct K)^[m] b x
  | 0, _, _ => rfl
  | m + 1, a, b => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        Balance.funAct_add, funAct_iterate_add K m]

omit [Fintype V] in
theorem densAct_iterate_add {α : Type*} [Fintype α] (w : α → ℝ) (K : α → α → ℝ) :
    ∀ (m : ℕ) (a b : α → ℝ), (Core.densAct w K)^[m] (fun x => a x + b x)
      = fun x => (Core.densAct w K)^[m] a x + (Core.densAct w K)^[m] b x
  | 0, _, _ => rfl
  | m + 1, a, b => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        funext (Balance.densAct_add w K a b), densAct_iterate_add w K m]

/-- `Θ_ℓ` is additive. -/
theorem Theta_add (ℓ : ℕ) (a b : EdgeSet pb → ℝ) :
    Theta pb lam ℓ (fun e => a e + b e)
      = fun e => Theta pb lam ℓ a e + Theta pb lam ℓ b e := by
  funext e
  simp only [Theta, funAct_iterate_add, densAct_iterate_add]
  rw [add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by ring

omit [DecidableEq V] in
theorem ipL2_add_right {α : Type*} [Fintype α] (w a b c : α → ℝ) :
    Graph.ipL2 w a (fun x => b x + c x) = Graph.ipL2 w a b + Graph.ipL2 w a c := by
  simp only [Graph.ipL2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `⟨w, Θ_ℓ u⟩ = ⟨w, u⟩ + ∑_{m=1}^{ℓ−1} (1 − m/ℓ)(⟨w, Q^m u⟩ + ⟨w, (Q†)^m u⟩)`. -/
theorem ip_Theta (ℓ : ℕ) (w u : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) w (Theta pb lam ℓ u)
      = Graph.ipL2 (edgeMeasureE pb lam) w u
        + ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ)
          * (Graph.ipL2 (edgeMeasureE pb lam) w ((funAct (edgeKernelE pb))^[m] u)
            + Graph.ipL2 (edgeMeasureE pb lam) w
                ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] u)) := by
  have key : ∀ e, edgeMeasureE pb lam e * (w e * Theta pb lam ℓ u e)
      = edgeMeasureE pb lam e * (w e * u e)
        + ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ)
          * (edgeMeasureE pb lam e * (w e * (funAct (edgeKernelE pb))^[m] u e)
            + edgeMeasureE pb lam e
              * (w e * (Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] u e)) := by
    intro e
    simp only [Theta]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [Graph.ipL2]
  rw [Finset.sum_congr rfl fun e _ => key e, Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]

/-- `⟨u, (Q†)^m u⟩ = ⟨u, Q^m u⟩`. -/
theorem ip_P_self (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam)
    (m : ℕ) (u : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) u ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] u)
      = Graph.ipL2 (edgeMeasureE pb lam) u ((funAct (edgeKernelE pb))^[m] u) := by
  rw [ipL2_comm, adj_Q hnn hlam hinv]

/-- **`prop:tb_hessian`, `eq:tb_window_variance`**: `𝔼_{τ∼ν̂}(∑_{k=1}^{ℓ} u(e_k))² = ℓ⟨u, Θ_ℓ u⟩` for every
`u ∈ L²(λ₂)`. -/
theorem window_variance (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (ℓ : ℕ) (u : EdgeSet pb → ℝ) :
    ∑ τ, window pb lam ℓ τ * (∑ k : Fin ℓ, uAt u (τ k.castSucc) (τ k.succ)) ^ 2
      = ℓ * Graph.ipL2 (edgeMeasureE pb lam) u (Theta pb lam ℓ u) := by
  rw [window_sq hinv hrow, ip_Theta]
  simp only [corr_uAt hnn, ip_P_self hnn hlam hinv, Function.iterate_zero, id]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [sub_self, zero_mul, add_zero]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm 1 k]
  field_simp
  ring

omit [DecidableEq V] in
omit [Fintype V] in
theorem window_nonneg (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 ≤ lam x) {ℓ : ℕ}
    (τ : Fin (ℓ + 1) → V) : 0 ≤ window pb lam ℓ τ :=
  mul_nonneg (hlam _) (Finset.prod_nonneg fun _ _ => hnn _ _)

/-- **`prop:tb_hessian`, `Θ_ℓ ⪰ 0`**. -/
theorem Theta_psd (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (ℓ : ℕ) (u : EdgeSet pb → ℝ) :
    0 ≤ Graph.ipL2 (edgeMeasureE pb lam) u (Theta pb lam ℓ u) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have h0 : Theta pb lam 0 u = u := by funext e; simp [Theta]
    rw [h0, ← Graph.sq_nrmL2 fun e => (edgeMeasureE_pos hlam e).le]
    exact sq_nonneg _
  · have h := window_variance hnn hrow hlam hinv ℓ u
    have h0 : 0 ≤ ∑ τ, window pb lam ℓ τ * (∑ k : Fin ℓ, uAt u (τ k.castSucc) (τ k.succ)) ^ 2 :=
      Finset.sum_nonneg fun τ _ =>
        mul_nonneg (window_nonneg hnn (fun x => (hlam x).le) τ) (sq_nonneg _)
    rw [h] at h0
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg (show (0 : ℝ) < ℓ by exact_mod_cast hℓ) hneg
    linarith

/-- **`prop:tb_hessian`, `Θ_ℓ` is self-adjoint** on `L²(λ₂)`. -/
theorem Theta_selfAdjoint (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x)
    (hinv : Invariant pb lam) (ℓ : ℕ) (u v : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) (Theta pb lam ℓ u) v
      = Graph.ipL2 (edgeMeasureE pb lam) u (Theta pb lam ℓ v) := by
  have h1 : ∀ m, Graph.ipL2 (edgeMeasureE pb lam) v ((funAct (edgeKernelE pb))^[m] u)
      = Graph.ipL2 (edgeMeasureE pb lam) u
          ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] v) := by
    intro m; rw [← adj_Q hnn hlam hinv, ipL2_comm]
  have h2 : ∀ m, Graph.ipL2 (edgeMeasureE pb lam) v
        ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] u)
      = Graph.ipL2 (edgeMeasureE pb lam) u ((funAct (edgeKernelE pb))^[m] v) := by
    intro m; rw [ipL2_comm, adj_Q hnn hlam hinv]
  rw [ipL2_comm, ip_Theta, ip_Theta, ipL2_comm _ v u]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h1 m, h2 m, add_comm]

/-! #### Bounds on `Θ_ℓ` -/

theorem sum_range_succ_cast (n : ℕ) : ∑ k ∈ range n, ((k : ℝ) + 1) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **The Cesàro weights**: `1 + 2∑_{m=1}^{ℓ−1}(1 − m/ℓ) = ℓ` for `ℓ ≥ 1`, whence `‖Θ_ℓ‖ ≤ ℓ`. -/
theorem cesaro_sum {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    1 + 2 * ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ) = ℓ := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have h := sum_range_succ_cast n
  have h' : ∑ k ∈ range n, ((1 + k : ℕ) : ℝ) = n * (n + 1) / 2 := by
    rw [← h]; exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  rw [h']
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

omit [DecidableEq V] in
theorem abs_ipL2_le {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (a b : α → ℝ) :
    |Graph.ipL2 w a b| ≤ Graph.nrmL2 w a * Graph.nrmL2 w b := by
  refine abs_le.2 ⟨?_, Graph.ipL2_le_mul_nrmL2 hw a b⟩
  have h := Graph.ipL2_le_mul_nrmL2 hw (fun x => -a x) b
  have hn : Graph.nrmL2 w (fun x => -a x) = Graph.nrmL2 w a := nrmL2_neg w a
  have he : Graph.ipL2 w (fun x => -a x) b = -Graph.ipL2 w a b := by
    simp only [Graph.ipL2, neg_mul, mul_neg, Finset.sum_neg_distrib]
  rw [hn, he] at h
  linarith

omit [DecidableEq V] in
theorem nrmL2_densAct_iterate_le {α : Type*} [Fintype α] {w : α → ℝ} {K : α → α → ℝ}
    (hK : Core.IsMarkov K) (hI : Core.IsInvariant w K) :
    ∀ (m : ℕ) (u : α → ℝ), Graph.nrmL2 w ((Core.densAct w K)^[m] u) ≤ Graph.nrmL2 w u
  | 0, _ => le_rfl
  | m + 1, u => by
      rw [Function.iterate_succ_apply']
      exact (nrmL2_densAct_le hK hI _).trans (nrmL2_densAct_iterate_le hK hI m u)

/-- **`‖Θ_ℓ‖ ≤ ℓ`**, in the form the remainder estimate uses: `|⟨w, Θ_ℓ v⟩| ≤ ℓ‖w‖‖v‖`. -/
theorem abs_ip_Theta_le (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (w v : EdgeSet pb → ℝ) :
    |Graph.ipL2 (edgeMeasureE pb lam) w (Theta pb lam ℓ v)|
      ≤ ℓ * (Graph.nrmL2 (edgeMeasureE pb lam) w * Graph.nrmL2 (edgeMeasureE pb lam) v) := by
  have hw : ∀ e, 0 ≤ edgeMeasureE pb lam e := fun e => (edgeMeasureE_pos hlam e).le
  have hK := edgeKernelE_isMarkov hnn hrow
  have hI := edgeMeasureE_isInvariant' hnn hlam hinv
  set N := Graph.nrmL2 (edgeMeasureE pb lam) w * Graph.nrmL2 (edgeMeasureE pb lam) v
  have hN0 : 0 ≤ N := mul_nonneg (Graph.nrmL2_nonneg _ _) (Graph.nrmL2_nonneg _ _)
  have hQ : ∀ m, |Graph.ipL2 (edgeMeasureE pb lam) w ((funAct (edgeKernelE pb))^[m] v)| ≤ N :=
    fun m => (abs_ipL2_le hw _ _).trans (mul_le_mul_of_nonneg_left
      (nrmL2_funAct_iterate_le (hK.toIsMarkovOn _) hI m v) (Graph.nrmL2_nonneg _ _))
  have hP : ∀ m, |Graph.ipL2 (edgeMeasureE pb lam) w
      ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] v)| ≤ N :=
    fun m => (abs_ipL2_le hw _ _).trans (mul_le_mul_of_nonneg_left
      (nrmL2_densAct_iterate_le hK hI m v) (Graph.nrmL2_nonneg _ _))
  have hc : ∀ m ∈ Finset.Ico 1 ℓ, 0 ≤ 1 - (m : ℝ) / ℓ := by
    intro m hm
    have hml : (m : ℝ) < ℓ := by exact_mod_cast (Finset.mem_Ico.mp hm).2
    have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    rw [sub_nonneg, div_le_one hℓ0]; exact hml.le
  rw [ip_Theta]
  calc _ ≤ |Graph.ipL2 (edgeMeasureE pb lam) w v|
        + ∑ m ∈ Finset.Ico 1 ℓ, |(1 - (m : ℝ) / ℓ)
          * (Graph.ipL2 (edgeMeasureE pb lam) w ((funAct (edgeKernelE pb))^[m] v)
            + Graph.ipL2 (edgeMeasureE pb lam) w
                ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] v))| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ N + ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ) * (2 * N) := by
        refine add_le_add (abs_ipL2_le hw w v) (Finset.sum_le_sum fun m hm => ?_)
        rw [abs_mul, abs_of_nonneg (hc m hm)]
        refine mul_le_mul_of_nonneg_left ?_ (hc m hm)
        linarith [abs_add_le (Graph.ipL2 (edgeMeasureE pb lam) w ((funAct (edgeKernelE pb))^[m] v))
          (Graph.ipL2 (edgeMeasureE pb lam) w
            ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] v)), hQ m, hP m]
    _ = (1 + 2 * ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ)) * N := by
        rw [add_mul, one_mul, mul_assoc, Finset.sum_mul, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = ℓ * N := by rw [cesaro_sum hℓ]

/-- `β̂_m` bounds `P^m − Π₂` on `L²(λ₂)`: the infimum is attained in finite dimension. -/
theorem betaHat_opBound (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1) (m : ℕ) :
    OpBound (edgeMeasureE pb lam) (densDeviation (edgeKernelE pb) (edgeMeasureE pb lam) m)
      (betaHat pb lam m) := by
  have hw : ∀ e, 0 ≤ edgeMeasureE pb lam e := fun e => (edgeMeasureE_pos hlam e).le
  have hK := edgeKernelE_isMarkov hnn hrow
  have hI := edgeMeasureE_isInvariant' hnn hlam hinv
  exact opBound_opNorm ⟨2, opBound_of_adjoint hw (ipL2_densDeviation hI hK.nonneg m)
    (opBound_deviation_two (hK.toIsMarkovOn _) hI (edgeMeasureE_total hnn hrow htot) m)⟩

/-- On mean-zero `u`, `⟨u, Q^m u⟩ ≤ β̂_m ‖u‖²`. -/
theorem ip_Q_le_betaHat (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1) (m : ℕ)
    {u : EdgeSet pb → ℝ} (hu : ∑ e, edgeMeasureE pb lam e * u e = 0) :
    Graph.ipL2 (edgeMeasureE pb lam) u ((funAct (edgeKernelE pb))^[m] u)
      ≤ betaHat pb lam m * Graph.ipL2 (edgeMeasureE pb lam) u u := by
  have hw : ∀ e, 0 ≤ edgeMeasureE pb lam e := fun e => (edgeMeasureE_pos hlam e).le
  have hdev : densDeviation (edgeKernelE pb) (edgeMeasureE pb lam) m u
      = (Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] u := by
    funext e; rw [densDeviation_apply_eq, hu, sub_zero]
  have hb := (betaHat_opBound hnn hrow hlam hinv htot m).2 u
  rw [l2norm_eq_nrmL2, l2norm_eq_nrmL2, hdev] at hb
  rw [← adj_Q hnn hlam hinv, ← Graph.sq_nrmL2 hw, sq]
  calc _ ≤ Graph.nrmL2 (edgeMeasureE pb lam)
            ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] u)
          * Graph.nrmL2 (edgeMeasureE pb lam) u := Graph.ipL2_le_mul_nrmL2 hw _ _
    _ ≤ betaHat pb lam m * Graph.nrmL2 (edgeMeasureE pb lam) u
          * Graph.nrmL2 (edgeMeasureE pb lam) u :=
        mul_le_mul_of_nonneg_right hb (Graph.nrmL2_nonneg _ _)
    _ = _ := by ring

/-- **`prop:tb_hessian`, `eq:tb_theta_bound`, first inequality**: on mean-zero `u`,
`⟨u, Θ_ℓ u⟩ ≤ (1 + 2∑_{m=1}^{ℓ−1}(1 − m/ℓ)β̂_m)‖u‖²`. -/
theorem Theta_le_cesaro (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1) (ℓ : ℕ)
    {u : EdgeSet pb → ℝ} (hu : ∑ e, edgeMeasureE pb lam e * u e = 0) :
    Graph.ipL2 (edgeMeasureE pb lam) u (Theta pb lam ℓ u)
      ≤ (1 + 2 * ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ) * betaHat pb lam m)
        * Graph.ipL2 (edgeMeasureE pb lam) u u := by
  have hc : ∀ m ∈ Finset.Ico 1 ℓ, 0 ≤ 1 - (m : ℝ) / ℓ := by
    intro m hm
    have hml : (m : ℝ) < ℓ := by exact_mod_cast (Finset.mem_Ico.mp hm).2
    have hℓ0 : (0 : ℝ) < ℓ := lt_of_le_of_lt (Nat.cast_nonneg m) hml
    rw [sub_nonneg, div_le_one hℓ0]; exact hml.le
  rw [ip_Theta]
  simp only [ip_P_self hnn hlam hinv]
  rw [add_mul, one_mul, mul_assoc, Finset.sum_mul, Finset.mul_sum]
  refine add_le_add le_rfl (Finset.sum_le_sum fun m hm => ?_)
  have := ip_Q_le_betaHat hnn hrow hlam hinv htot m hu
  nlinarith [hc m hm]

/-- **`prop:tb_hessian`, `Θ_ℓ ⪯ (1 + 2B̂′) I` on the mean-zero functions**, `B̂′ = ∑_{m≥1} β̂_m`, for every real
bound `B` of the partial sums of `B̂′` (vacuous exactly when `B̂′ = +∞`, kb `0031`). -/
theorem Theta_le (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1) (ℓ : ℕ)
    {B : ℝ} (hB : ∀ N, ∑ m ∈ range N, betaHat pb lam (m + 1) ≤ B)
    {u : EdgeSet pb → ℝ} (hu : ∑ e, edgeMeasureE pb lam e * u e = 0) :
    Graph.ipL2 (edgeMeasureE pb lam) u (Theta pb lam ℓ u)
      ≤ (1 + 2 * B) * Graph.ipL2 (edgeMeasureE pb lam) u u := by
  have hw : ∀ e, 0 ≤ edgeMeasureE pb lam e := fun e => (edgeMeasureE_pos hlam e).le
  have huu : 0 ≤ Graph.ipL2 (edgeMeasureE pb lam) u u := by
    rw [← Graph.sq_nrmL2 hw]; exact sq_nonneg _
  refine (Theta_le_cesaro hnn hrow hlam hinv htot ℓ hu).trans
    (mul_le_mul_of_nonneg_right ?_ huu)
  have hβ : ∀ m, 0 ≤ betaHat pb lam m := fun m => (betaHat_opBound hnn hrow hlam hinv htot m).1
  have h1 : ∑ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ) * betaHat pb lam m
      ≤ ∑ m ∈ Finset.Ico 1 ℓ, betaHat pb lam m := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hml : (m : ℝ) < ℓ := by exact_mod_cast (Finset.mem_Ico.mp hm).2
    have hm0 : (0 : ℝ) ≤ m / ℓ := div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg ℓ)
    nlinarith [hβ m]
  have h2 : ∑ m ∈ Finset.Ico 1 ℓ, betaHat pb lam m ≤ B := by
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [add_comm 1] using hB (ℓ - 1)
  linarith

/-! #### The loss at `μ = (1 + h)λ₂` -/

/-- `|log(1 + t) − t| ≤ t²` for `|t| ≤ 1/2` (the proof's `∑_{n≥2}|t|^n/n ≤ t²`). -/
theorem abs_log_one_add_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |Real.log (1 + t) - t| ≤ t ^ 2 := by
  have hx : |(-t)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at h
  norm_num at h
  have ha : 0 ≤ |t| := abs_nonneg t
  have h1 : |t| ^ 5 / (1 - |t|) ≤ 2 * |t| ^ 5 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg ha 5]
  have hb := abs_le.mp (h.trans h1)
  have e2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have e3 : |t| ^ 3 ≤ |t| ^ 2 / 2 := by nlinarith [pow_nonneg ha 2]
  have e4 : |t| ^ 4 ≤ |t| ^ 2 / 4 := by nlinarith [pow_nonneg ha 2, pow_nonneg ha 3]
  have e5 : |t| ^ 5 ≤ |t| ^ 2 / 8 := by
    nlinarith [pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4]
  have t3 : |t ^ 3| = |t| ^ 3 := abs_pow t 3
  have t4 : t ^ 4 = |t| ^ 4 := by rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
  have h3 := abs_le.mp (le_of_eq t3)
  rw [abs_le]
  constructor <;> nlinarith [hb.1, hb.2, h3.1, h3.2]

/-- **The TB loss is the window variance of `log r̂`**: at every `μ ∈ (0,+∞)^E`, with `g = (log x)²`,
`𝓛_{TB}(μ) = ∑_τ ν̂(τ) (∑_k log r̂(e_k))²`. -/
theorem loss_eq_window (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (ℓ : ℕ)
    {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e) :
    TBGradient.loss pb (window pb lam ℓ) logSq μ
      = ∑ τ, window pb lam ℓ τ
          * (∑ k : Fin ℓ, uAt (fun e => Real.log (TBGradient.ratio pb μ e))
              (τ k.castSucc) (τ k.succ)) ^ 2 := by
  have hF := TBGradient.marg_pos hinv hlam hμ
  unfold TBGradient.loss
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  unfold logSq TBGradient.rho
  rw [Real.log_prod]
  · congr 2
    funext k
    unfold TBGradient.ratioAt uAt
    split_ifs
    · rfl
    · exact Real.log_one
  · intro k _
    unfold TBGradient.ratioAt
    split_ifs
    · exact (TBGradient.ratio_pos hμ hF _).ne'
    · exact one_ne_zero

/-- `|Ph| ≤ ‖h‖_∞`: the density action of `K₂` is an average. -/
theorem abs_densAct_le (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x)
    (hinv : Invariant pb lam) {h : EdgeSet pb → ℝ} {δ : ℝ} (hh : ∀ e, |h e| ≤ δ)
    (e : EdgeSet pb) :
    |Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb) h e| ≤ δ := by
  have hI := edgeMeasureE_isInvariant' hnn hlam hinv
  have hw := edgeMeasureE_pos hlam e
  rw [Core.densAct_apply, abs_div, abs_of_pos hw, div_le_iff₀ hw]
  calc _ ≤ ∑ x, |edgeMeasureE pb lam x * edgeKernelE pb x e * h x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, edgeMeasureE pb lam x * edgeKernelE pb x e * δ := by
        refine Finset.sum_le_sum fun x _ => ?_
        have hx : 0 ≤ edgeMeasureE pb lam x * edgeKernelE pb x e :=
          mul_nonneg (edgeMeasureE_pos hlam x).le (edgeKernel_nonneg hnn _ _ _ _)
        rw [abs_mul, abs_of_nonneg hx]
        exact mul_le_mul_of_nonneg_left (hh x) hx
    _ = δ * edgeMeasureE pb lam e := by rw [← Finset.sum_mul, hI.inv e, mul_comm]

/-- **`r̂ = (1 + Ph)/(1 + h)`** at `μ = (1 + h)λ₂`. -/
theorem ratio_perturb (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x)
    (hinv : Invariant pb lam) (h : EdgeSet pb → ℝ) (e : EdgeSet pb) :
    TBGradient.ratio pb (fun e => (1 + h e) * edgeMeasureE pb lam e) e
      = (1 + Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb) h e) / (1 + h e) := by
  have hI := edgeMeasureE_isInvariant' hnn hlam hinv
  have hw := (edgeMeasureE_pos hlam e).ne'
  have hpush : TBGradient.push pb (fun e => (1 + h e) * edgeMeasureE pb lam e) e
      = edgeMeasureE pb lam e * (1 + Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb) h e) := by
    simp only [TBGradient.push, TBGradient.measAct, Core.densAct_apply]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hw, ← hI.inv e, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [TBGradient.ratio, hpush, mul_comm (1 + h e)]
  exact mul_div_mul_left _ _ hw

omit [DecidableEq V] in
theorem nrmL2_le_const {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    (htot : ∑ x, w x = 1) {f : α → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x, |f x| ≤ c) :
    Graph.nrmL2 w f ≤ c := by
  have h := nrmL2_le_of_abs_le (b := fun _ => (1 : ℝ)) hw hc (fun x => by simpa using hf x)
  have h1 : Graph.nrmL2 w (fun _ => (1 : ℝ)) = 1 := by
    simp only [Graph.nrmL2, Graph.ipL2, mul_one, htot, Real.sqrt_one]
  rwa [h1, mul_one] at h

/-- `½⟨h, H_TB h⟩ = ℓ⟨Ah, Θ_ℓ Ah⟩` (`g''(1) = 2`). -/
theorem half_ip_HTB (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam)
    (ℓ : ℕ) (h : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) h (HTB pb lam ℓ h)
      = ℓ * deriv (deriv logSq) 1 * Graph.ipL2 (edgeMeasureE pb lam)
          (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h)
          (Theta pb lam ℓ (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h)) := by
  have hI := edgeMeasureE_isInvariant' hnn hlam hinv
  unfold HTB
  rw [Balance.ipL2_smul_right, ipL2_comm, ipL2_Adj_left hI (fun _ _ => edgeKernel_nonneg hnn _ _ _ _),
    ipL2_comm]

/-- `⟨h, H_DB h⟩ = g''(1)‖Ah‖²`. -/
theorem ip_HDB (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam)
    (h : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) h (HDB pb lam h)
      = deriv (deriv logSq) 1 * Graph.ipL2 (edgeMeasureE pb lam)
          (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h)
          (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h) := by
  have hI := edgeMeasureE_isInvariant' hnn hlam hinv
  unfold HDB
  rw [Balance.ipL2_smul_right, ipL2_comm, ipL2_Adj_left hI (fun _ _ => edgeKernel_nonneg hnn _ _ _ _)]

/-- **`prop:tb_hessian`, the expansion with the proof's explicit remainder**: for `‖h‖_∞ ≤ δ ≤ 1/2`,
`|𝓛_{TB,g,ν̂}((1+h)λ₂) − ½⟨h, H_TB h⟩_{L²(λ₂)}| ≤ 10ℓ²δ³`. -/
theorem expansion_explicit (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1) (ℓ : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) {h : EdgeSet pb → ℝ} (hh : ∀ e, |h e| ≤ δ) :
    |TBGradient.loss pb (window pb lam ℓ) logSq (fun e => (1 + h e) * edgeMeasureE pb lam e)
        - 1 / 2 * Graph.ipL2 (edgeMeasureE pb lam) h (HTB pb lam ℓ h)|
      ≤ 10 * ℓ ^ 2 * δ ^ 3 := by
  have hw : ∀ e, 0 ≤ edgeMeasureE pb lam e := fun e => (edgeMeasureE_pos hlam e).le
  have htotE := edgeMeasureE_total hnn hrow htot
  set Ph := Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb) h with hPh_def
  have hPh : ∀ e, |Ph e| ≤ δ := abs_densAct_le hnn hlam hinv hh
  set a := Aop (edgeKernelE pb) (edgeMeasureE pb lam) h with ha_def
  have ha : ∀ e, a e = Ph e - h e := fun e => rfl
  have hpos1 : ∀ e, 0 < 1 + h e := fun e => by
    have := (abs_le.mp (hh e)).1; linarith
  have hpos2 : ∀ e, 0 < 1 + Ph e := fun e => by
    have := (abs_le.mp (hPh e)).1; linarith
  have hμ : ∀ e, 0 < (1 + h e) * edgeMeasureE pb lam e :=
    fun e => mul_pos (hpos1 e) (edgeMeasureE_pos hlam e)
  set u : EdgeSet pb → ℝ := fun e => Real.log
    (TBGradient.ratio pb (fun e => (1 + h e) * edgeMeasureE pb lam e) e) with hu_def
  set R : EdgeSet pb → ℝ := fun e => u e - a e with hR_def
  have hR : ∀ e, |R e| ≤ 2 * δ ^ 2 := by
    intro e
    have hue : u e = Real.log (1 + Ph e) - Real.log (1 + h e) := by
      simp only [hu_def]
      rw [ratio_perturb hnn hlam hinv, Real.log_div (hpos2 e).ne' (hpos1 e).ne']
    have hre : R e = (Real.log (1 + Ph e) - Ph e) - (Real.log (1 + h e) - h e) := by
      simp only [hR_def]; rw [hue, ha]; ring
    have h1 := abs_log_one_add_sub_le ((hPh e).trans hδ)
    have h2 := abs_log_one_add_sub_le ((hh e).trans hδ)
    have hP2 : Ph e ^ 2 ≤ δ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hPh e) 2
    have hh2 : h e ^ 2 ≤ δ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hh e) 2
    rw [hre]
    calc _ ≤ |Real.log (1 + Ph e) - Ph e| + |Real.log (1 + h e) - h e| := abs_sub _ _
      _ ≤ _ := by linarith
  have hua : u = fun e => a e + R e := by funext e; simp only [hR_def]; ring
  have hL : TBGradient.loss pb (window pb lam ℓ) logSq (fun e => (1 + h e) * edgeMeasureE pb lam e)
      = ℓ * Graph.ipL2 (edgeMeasureE pb lam) u (Theta pb lam ℓ u) := by
    rw [loss_eq_window hlam hinv ℓ hμ, window_variance hnn hrow hlam hinv]
  have hH : 1 / 2 * Graph.ipL2 (edgeMeasureE pb lam) h (HTB pb lam ℓ h)
      = ℓ * Graph.ipL2 (edgeMeasureE pb lam) a (Theta pb lam ℓ a) := by
    rw [half_ip_HTB hnn hlam hinv, logSq_deriv2_one]; ring
  have hsa := Theta_selfAdjoint hnn hlam hinv ℓ R a
  have hexp : Graph.ipL2 (edgeMeasureE pb lam) u (Theta pb lam ℓ u)
      - Graph.ipL2 (edgeMeasureE pb lam) a (Theta pb lam ℓ a)
      = 2 * Graph.ipL2 (edgeMeasureE pb lam) a (Theta pb lam ℓ R)
        + Graph.ipL2 (edgeMeasureE pb lam) R (Theta pb lam ℓ R) := by
    rw [hua, Theta_add, ipL2_add_right]
    have hl : ∀ b, Graph.ipL2 (edgeMeasureE pb lam) (fun e => a e + R e) b
        = Graph.ipL2 (edgeMeasureE pb lam) a b + Graph.ipL2 (edgeMeasureE pb lam) R b := by
      intro b; rw [ipL2_comm, ipL2_add_right, ipL2_comm _ b, ipL2_comm _ b]
    rw [hl, hl, ← hsa, ipL2_comm _ (Theta pb lam ℓ R) a]
    ring
  rw [hL, hH, ← mul_sub, hexp]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  have hna : Graph.nrmL2 (edgeMeasureE pb lam) a ≤ 2 * δ :=
    nrmL2_le_const hw htotE (by linarith) fun e => by
      rw [ha]; linarith [abs_sub (Ph e) (h e), hPh e, hh e]
  have hnR : Graph.nrmL2 (edgeMeasureE pb lam) R ≤ 2 * δ ^ 2 :=
    nrmL2_le_const hw htotE (by positivity) hR
  have b1 := abs_ip_Theta_le hnn hrow hlam hinv hℓ a R
  have b2 := abs_ip_Theta_le hnn hrow hlam hinv hℓ R R
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have n0a := Graph.nrmL2_nonneg (edgeMeasureE pb lam) a
  have n0R := Graph.nrmL2_nonneg (edgeMeasureE pb lam) R
  have hprod1 : Graph.nrmL2 (edgeMeasureE pb lam) a * Graph.nrmL2 (edgeMeasureE pb lam) R
      ≤ 2 * δ * (2 * δ ^ 2) := mul_le_mul hna hnR n0R (by linarith)
  have hprod2 : Graph.nrmL2 (edgeMeasureE pb lam) R * Graph.nrmL2 (edgeMeasureE pb lam) R
      ≤ 2 * δ ^ 2 * (2 * δ ^ 2) := mul_le_mul hnR hnR n0R (by positivity)
  have hδ4 : 4 * δ ^ 4 ≤ 2 * δ ^ 3 := by nlinarith [pow_nonneg hδ0 3]
  rw [abs_mul, abs_of_nonneg hℓ0]
  calc (ℓ : ℝ) * |2 * Graph.ipL2 (edgeMeasureE pb lam) a (Theta pb lam ℓ R)
        + Graph.ipL2 (edgeMeasureE pb lam) R (Theta pb lam ℓ R)|
      ≤ ℓ * (2 * |Graph.ipL2 (edgeMeasureE pb lam) a (Theta pb lam ℓ R)|
        + |Graph.ipL2 (edgeMeasureE pb lam) R (Theta pb lam ℓ R)|) := by
        refine mul_le_mul_of_nonneg_left ?_ hℓ0
        calc _ ≤ |2 * Graph.ipL2 (edgeMeasureE pb lam) a (Theta pb lam ℓ R)|
              + |Graph.ipL2 (edgeMeasureE pb lam) R (Theta pb lam ℓ R)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_two]
    _ ≤ ℓ * (2 * (ℓ * (2 * δ * (2 * δ ^ 2))) + ℓ * (2 * δ ^ 2 * (2 * δ ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hℓ0
        have := mul_le_mul_of_nonneg_left hprod1 hℓ0
        have := mul_le_mul_of_nonneg_left hprod2 hℓ0
        linarith
    _ ≤ 10 * ℓ ^ 2 * δ ^ 3 := by
        have : (ℓ : ℝ) * (ℓ * (4 * δ ^ 4)) ≤ ℓ * (ℓ * (2 * δ ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ4 hℓ0) hℓ0
        nlinarith

open Asymptotics Filter Topology in
/-- **`prop:tb_hessian`, the expansion as printed**: "for every norm `‖·‖` on `ℝ^E`, as `h → 0`,
`𝓛_{TB}((1+h)λ₂) = ½⟨h, H_TB h⟩ + O(‖h‖³)`". A norm on `ℝ^E` is carried as a normed space `F`
with a linear isomorphism `φ : F ≃ ℝ^E`; the remainder is `O(‖x‖³)` at `0` for every such `F`. -/
theorem expansion_isBigO (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1) (ℓ : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : F ≃ₗ[ℝ] (EdgeSet pb → ℝ)) :
    (fun x : F => TBGradient.loss pb (window pb lam ℓ) logSq
        (fun e => (1 + φ x e) * edgeMeasureE pb lam e)
        - 1 / 2 * Graph.ipL2 (edgeMeasureE pb lam) (φ x) (HTB pb lam ℓ (φ x)))
      =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
  haveI : FiniteDimensional ℝ F := φ.symm.finiteDimensional
  set T : F →L[ℝ] (EdgeSet pb → ℝ) := LinearMap.toContinuousLinearMap φ.toLinearMap
  have hT : ∀ x, φ x = T x := fun x => rfl
  set C := ‖T‖
  have hC0 : 0 ≤ C := norm_nonneg _
  refine IsBigO.of_bound (10 * ℓ ^ 2 * C ^ 3) ?_
  have hr : (0 : ℝ) < 1 / (2 * (C + 1)) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : F) hr] with x hx
  rw [mem_ball_zero_iff] at hx
  have hTx : ‖φ x‖ ≤ C * ‖x‖ := by rw [hT]; exact T.le_opNorm x
  have hsmall : ‖φ x‖ ≤ 1 / 2 := by
    calc ‖φ x‖ ≤ C * ‖x‖ := hTx
      _ ≤ (C + 1) * (1 / (2 * (C + 1))) :=
          mul_le_mul (by linarith) hx.le (norm_nonneg _) (by linarith)
      _ = 1 / 2 := by field_simp
  have hb := expansion_explicit hnn hrow hlam hinv htot ℓ (norm_nonneg (φ x)) hsmall
    (fun e => norm_le_pi_norm (φ x) e)
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  refine hb.trans ?_
  have h3 : ‖φ x‖ ^ 3 ≤ (C * ‖x‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hTx 3
  have hl : (0 : ℝ) ≤ 10 * ℓ ^ 2 := by positivity
  calc 10 * (ℓ : ℝ) ^ 2 * ‖φ x‖ ^ 3 ≤ 10 * ℓ ^ 2 * (C * ‖x‖) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 hl
    _ = 10 * ℓ ^ 2 * C ^ 3 * ‖x‖ ^ 3 := by ring

/-- **`prop:tb_hessian`, "every edge marginal `ν̂_k` is `λ₂`"**. -/
theorem edgeMarg_window (hinv : Invariant pb lam) (hrow : ∀ x, ∑ y, pb x y = 1) (ℓ : ℕ)
    (k : Fin ℓ) (e : EdgeSet pb) :
    TBGradient.edgeMarg pb (window pb lam ℓ) k e = edgeMeasureE pb lam e := by
  have h := window_two hinv hrow ℓ k k le_rfl (fun s s' => if (s, s') = e.1 then 1 else 0)
    (fun _ _ => 1)
  simp only [Nat.sub_self, Function.iterate_zero, id, one_mul, mul_one] at h
  unfold TBGradient.edgeMarg
  rw [show (∑ τ, if (τ k.castSucc, τ k.succ) = e.1 then window pb lam ℓ τ else 0)
      = ∑ τ, window pb lam ℓ τ * (if (τ k.castSucc, τ k.succ) = e.1 then 1 else 0) from
    Finset.sum_congr rfl fun τ _ => by split_ifs <;> simp, h]
  rw [← Fintype.sum_prod_type' (fun s s' => edgeMeasure pb lam s s' * if (s, s') = e.1 then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, Prod.mk.eta, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- `A h = Ph − h` is mean-zero against `λ₂`: `P` preserves `λ₂`-integrals. -/
theorem mean_Aop (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (h : EdgeSet pb → ℝ) :
    ∑ e, edgeMeasureE pb lam e * Aop (edgeKernelE pb) (edgeMeasureE pb lam) h e = 0 := by
  have hK := edgeKernelE_isMarkov hnn hrow
  have hP : ∑ e, edgeMeasureE pb lam e * Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb) h e
      = ∑ e, edgeMeasureE pb lam e * h e := by
    simp only [Core.densAct_apply]
    rw [Finset.sum_congr rfl fun e _ => mul_div_cancel₀ _ (edgeMeasureE_pos hlam e).ne',
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hK.row_sum x, mul_one]
  simp only [Aop, mul_sub, Finset.sum_sub_distrib, hP, sub_self]

/-- **`prop:tb_hessian`, `0 ⪯ H_TB`**. -/
theorem HTB_nonneg (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (ℓ : ℕ) (h : EdgeSet pb → ℝ) :
    0 ≤ Graph.ipL2 (edgeMeasureE pb lam) h (HTB pb lam ℓ h) := by
  rw [half_ip_HTB hnn hlam hinv, logSq_deriv2_one]
  exact mul_nonneg (by positivity) (Theta_psd hnn hrow hlam hinv ℓ _)

/-- **`prop:tb_hessian`, `H_TB ⪯ ℓ(1 + 2B̂′) H_DB`**, for every real bound `B` of the partial sums of `B̂′`. -/
theorem HTB_le (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1) (ℓ : ℕ)
    {B : ℝ} (hB : ∀ N, ∑ m ∈ range N, betaHat pb lam (m + 1) ≤ B) (h : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) h (HTB pb lam ℓ h)
      ≤ ℓ * (1 + 2 * B) * Graph.ipL2 (edgeMeasureE pb lam) h (HDB pb lam h) := by
  rw [half_ip_HTB hnn hlam hinv, ip_HDB hnn hlam hinv, logSq_deriv2_one]
  have := Theta_le hnn hrow hlam hinv htot ℓ hB (mean_Aop hnn hrow hlam h)
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  calc (ℓ : ℝ) * 2 * Graph.ipL2 (edgeMeasureE pb lam) (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h)
        (Theta pb lam ℓ (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h))
      ≤ ℓ * 2 * ((1 + 2 * B) * Graph.ipL2 (edgeMeasureE pb lam)
          (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h)
          (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- **`prop:tb_hessian`, `H_DB` is `H_TB` at `ℓ = 1`**. -/
theorem HTB_one : HTB pb lam 1 = HDB pb lam := by
  have hT : ∀ u, Theta pb lam 1 u = u := fun u => by funext e; simp [Theta]
  funext h e
  simp only [HTB, HDB, hT, Nat.cast_one, one_mul]

/-- **`prop:tb_hessian`, at `ℓ = 1` the loss is the DB loss `𝓛_{DB,g,λ₂}`** of `prop:db_lift` for the training
distribution `λ₂`, read on `E` (`Freezing.loss` of `K₂` on `(E, λ₂)` at the density `μ/λ₂`, which
`C3Wrappers.loss_edgeE_eq_db` identifies with the detailed-balance loss of `(F, π_→^μ)`); any `g`. -/
theorem loss_one (hlam : ∀ x, 0 < lam x) (hnn : ∀ x y, 0 ≤ pb x y) (g : ℝ → ℝ)
    {μ : EdgeSet pb → ℝ} :
    TBGradient.loss pb (window pb lam 1) g μ
      = loss (edgeKernelE pb) (edgeMeasureE pb lam) (edgeMeasureE pb lam)
          (fun e => μ e / edgeMeasureE pb lam e) g := by
  have hr : ∀ e : EdgeSet pb, Balance.ratio (edgeKernelE pb) (edgeMeasureE pb lam)
      (fun e => μ e / edgeMeasureE pb lam e) e = TBGradient.ratio pb μ e := by
    intro e
    simp only [Balance.ratio, pushMass, TBGradient.ratio, TBGradient.push, TBGradient.measAct]
    rw [mul_div_cancel₀ _ (edgeMeasureE_pos hlam e).ne']
    congr 1
    exact Finset.sum_congr rfl fun x _ => by rw [mul_div_cancel₀ _ (edgeMeasureE_pos hlam x).ne']
  unfold TBGradient.loss loss
  simp only [hr]
  rw [sum_cons]
  have h1 : ∀ x (τ : Fin 1 → V), window pb lam 1 (Fin.cons x τ)
      * g (TBGradient.rho pb μ (Fin.cons x τ))
      = edgeMeasure pb lam x (τ 0) * g (TBGradient.ratioAt pb μ x (τ 0)) := by
    intro x τ
    simp only [window, TBGradient.rho, Fin.prod_univ_one, Fin.castSucc_zero,
      Fin.cons_zero, Fin.succ_zero_eq_one, edgeMeasure]
    rw [show ((1 : Fin 2)) = (0 : Fin 1).succ from rfl, Fin.cons_succ]
    rw [show (Fin.last 1 : Fin 2) = (0 : Fin 1).succ from rfl, Fin.cons_succ]
    ring
  simp only [h1]
  have h2 : ∀ x, ∑ τ : Fin 1 → V, edgeMeasure pb lam x (τ 0) * g (TBGradient.ratioAt pb μ x (τ 0))
      = ∑ y, edgeMeasure pb lam x y * g (TBGradient.ratioAt pb μ x y) := by
    intro x
    exact (Equiv.funUnique (Fin 1) V).sum_comp (fun y => edgeMeasure pb lam x y
      * g (TBGradient.ratioAt pb μ x y))
  simp only [h2]
  rw [pair_sum_eq hnn]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [TBGradient.ratioAt, dif_pos e.2]

omit [DecidableEq V] in
/-- `‖I − Π‖_{L²(w)} = 1` on a finite space with a positive probability `w` and two states. -/
theorem opNorm_densDeviation_zero {α : Type*} [Fintype α] [DecidableEq α] {w : α → ℝ}
    (hw : ∀ x, 0 < w x) (htot : ∑ x, w x = 1) {x y : α} (hxy : x ≠ y) (K : α → α → ℝ) :
    opNorm w (densDeviation K w 0) = 1 := by
  have hw0 : ∀ z, 0 ≤ w z := fun z => (hw z).le
  have hb1 : OpBound w (densDeviation K w 0) 1 := by
    refine ⟨zero_le_one, fun g => ?_⟩
    rw [l2norm_eq_nrmL2, l2norm_eq_nrmL2, one_mul]
    exact nrmL2_perpL2_le hw0 htot g
  refine le_antisymm (csInf_le ⟨0, fun _ hb => hb.1⟩ hb1) ?_
  have hb := (opBound_opNorm ⟨1, hb1⟩).2
  set v : α → ℝ := fun z => (if z = x then 1 else 0) - w x
  have hmean : ∑ z, w z * v z = 0 := by
    simp only [v, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, htot, one_mul, sub_self]
  have hdv : densDeviation K w 0 v = v := by
    funext z; rw [densDeviation_apply_eq, hmean, sub_zero]; rfl
  have hpos : 0 < Graph.nrmL2 w v := by
    apply Real.sqrt_pos.mpr
    have hterm : 0 < w y * (v y * v y) := by
      have : v y = -w x := by simp only [v, if_neg hxy.symm, zero_sub]
      rw [this]; exact mul_pos (hw y) (mul_self_pos.mpr (neg_ne_zero.mpr (hw x).ne'))
    exact lt_of_lt_of_le hterm (Finset.single_le_sum
      (f := fun z => w z * (v z * v z)) (fun z _ => mul_nonneg (hw0 z) (mul_self_nonneg _))
      (Finset.mem_univ y))
  have := hb v
  rw [l2norm_eq_nrmL2, l2norm_eq_nrmL2, hdv] at this
  by_contra hlt
  push Not at hlt
  have := mul_lt_mul_of_pos_right hlt hpos
  linarith

/-- **`prop:tb_hessian`, `β̂₁ = β₀ = ‖I − Π‖ = 1`** when `𝒮̂` has at least two states (`lem:lift_mixing` at `n = 1`,
then `I − Π` a non-zero orthogonal projection). -/
theorem betaHat_one (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1)
    {x y : V} (hxy : x ≠ y) : betaHat pb lam 1 = 1 := by
  have h1 : betaHat pb lam 1
      = opNorm (fun e : {q : V × V // 0 < pb q.2 q.1} => pairMeasure pb lam e.1)
          (densDeviation (fun e e' : {q : V × V // 0 < pb q.2 q.1} => pairKernel pb e.1 e'.1)
            (fun e => pairMeasure pb lam e.1) 1) := rfl
  rw [h1, opNorm_densDeviation_restrict (pairMeasure_eq_zero_off hnn lam),
    lift_mixing_dens hnn hrow (fun z => (hlam z).le) hinv htot 0]
  exact opNorm_densDeviation_zero hlam htot hxy pb

/-- **`prop:tb_hessian`, "if `𝒮̂` has at least two states, `B̂′ ≥ 1`"**: every real bound of the partial sums of
`B̂′ = ∑_{m≥1} β̂_m` is at least `1` (and if there is none, `B̂′ = +∞ ≥ 1`). -/
theorem one_le_Bprime (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1)
    {x y : V} (hxy : x ≠ y) {B : ℝ} (hB : ∀ N, ∑ m ∈ range N, betaHat pb lam (m + 1) ≤ B) :
    1 ≤ B := by
  have := hB 1
  rwa [Finset.sum_range_one, zero_add, betaHat_one hnn hrow hlam hinv htot hxy] at this

/-- **`rem:tb_vs_db`, the step cap**: a quadratic-form bound `L` on `H_DB` gives the bound
`ℓ(1 + 2B)L` on `H_TB`, so a step cap derived from `H_DB` stays sufficient for TB once divided by
`ℓ(1 + 2B̂′)`. -/
theorem stepCap (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1)
    (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam) (htot : ∑ x, lam x = 1) (ℓ : ℕ)
    {B : ℝ} (hB : ∀ N, ∑ m ∈ range N, betaHat pb lam (m + 1) ≤ B) {L : ℝ}
    (hL : ∀ h, Graph.ipL2 (edgeMeasureE pb lam) h (HDB pb lam h)
      ≤ L * Graph.ipL2 (edgeMeasureE pb lam) h h) (h : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) h (HTB pb lam ℓ h)
      ≤ ℓ * (1 + 2 * B) * L * Graph.ipL2 (edgeMeasureE pb lam) h h := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hc : (0 : ℝ) ≤ ℓ * (1 + 2 * B) := by positivity
  calc _ ≤ ℓ * (1 + 2 * B) * Graph.ipL2 (edgeMeasureE pb lam) h (HDB pb lam h) :=
        HTB_le hnn hrow hlam hinv htot ℓ hB h
    _ ≤ ℓ * (1 + 2 * B) * (L * Graph.ipL2 (edgeMeasureE pb lam) h h) :=
        mul_le_mul_of_nonneg_left (hL h) hc
    _ = _ := by ring

end Edge

/-! ### Inhabitation (kb `0025`): the uniform two-state chain, where `B̂′ = 1` -/

section Witness

theorem pbU_nonneg : ∀ x y, 0 ≤ pbU x y := fun _ _ => by norm_num [pbU]

theorem pbU_row : ∀ x, ∑ y, pbU x y = 1 := fun _ => by
  simp only [pbU, Fin.sum_univ_two]; norm_num

theorem lamU_pos : ∀ x, 0 < lamU x := fun _ => by norm_num [lamU]

theorem lamU_inv : Invariant pbU lamU := fun _ => by
  simp only [lamU, pbU, Fin.sum_univ_two]; norm_num

theorem lamU_tot : ∑ x, lamU x = 1 := by simp only [lamU, Fin.sum_univ_two]; norm_num

theorem opNorm_zero_op {α : Type*} [Fintype α] (w : α → ℝ) :
    opNorm w (fun _ _ => (0 : ℝ)) = 0 := by
  have hb : OpBound w (fun _ _ => (0 : ℝ)) 0 := ⟨le_rfl, fun g => by
    simp [l2norm, l2sq]⟩
  exact le_antisymm (csInf_le ⟨0, fun _ hb => hb.1⟩ hb) (le_csInf ⟨0, hb⟩ fun _ hb => hb.1)

/-- On the uniform chain `P` is the mean projection, so `β_m = 0` for `m ≥ 1`. -/
theorem densDeviation_pbU (m : ℕ) : densDeviation pbU lamU (m + 1) = fun _ _ => 0 := by
  have hP : ∀ u : Fin 2 → ℝ, Core.densAct lamU pbU u = fun _ => ∑ x, lamU x * u x := by
    intro u; funext y
    simp only [Core.densAct_apply, lamU, pbU, Fin.sum_univ_two]; ring
  have hc : ∀ c : ℝ, Core.densAct lamU pbU (fun _ => c) = fun _ => c := by
    intro c; rw [hP]; funext y; simp only [lamU, Fin.sum_univ_two]; ring
  have hit : ∀ (n : ℕ) (u : Fin 2 → ℝ), (Core.densAct lamU pbU)^[n + 1] u
      = fun _ => ∑ x, lamU x * u x := by
    intro n
    induction n with
    | zero => intro u; exact hP u
    | succ n ih =>
        intro u
        rw [Function.iterate_succ_apply', ih, hc]
  funext u y
  rw [densDeviation_apply_eq, hit, sub_self]

/-- **`prop:tb_hessian`, inhabitation with a finite `B̂′`**: on the uniform
two-state chain every hypothesis holds, `β̂₁ = 1` and `β̂_m = 0` for `m ≥ 2`, so `B = 1` bounds
every partial sum of `B̂′` and `HTB_le` gives `H_TB ⪯ 3ℓ H_DB` there. -/
theorem witness (ℓ : ℕ) (h : EdgeSet pbU → ℝ) :
    betaHat pbU lamU 1 = 1 ∧ (∀ m, betaHat pbU lamU (m + 2) = 0) ∧
    (∀ N, ∑ m ∈ range N, betaHat pbU lamU (m + 1) ≤ 1) ∧
    Graph.ipL2 (edgeMeasureE pbU lamU) h (HTB pbU lamU ℓ h)
      ≤ ℓ * (1 + 2 * 1) * Graph.ipL2 (edgeMeasureE pbU lamU) h (HDB pbU lamU h) := by
  have h1 : betaHat pbU lamU 1 = 1 :=
    betaHat_one pbU_nonneg pbU_row lamU_pos lamU_inv lamU_tot (x := 0) (y := 1) (by decide)
  have h2 : ∀ m, betaHat pbU lamU (m + 2) = 0 := by
    intro m
    have e : betaHat pbU lamU (m + 2)
        = opNorm (fun e : {q : Fin 2 × Fin 2 // 0 < pbU q.2 q.1} => pairMeasure pbU lamU e.1)
            (densDeviation (fun e e' : {q : Fin 2 × Fin 2 // 0 < pbU q.2 q.1} =>
              pairKernel pbU e.1 e'.1) (fun e => pairMeasure pbU lamU e.1) (m + 1 + 1)) := rfl
    rw [e, opNorm_densDeviation_restrict (pairMeasure_eq_zero_off pbU_nonneg lamU),
      lift_mixing_dens pbU_nonneg pbU_row (fun z => (lamU_pos z).le) lamU_inv lamU_tot (m + 1),
      densDeviation_pbU, opNorm_zero_op]
  have hB : ∀ N, ∑ m ∈ range N, betaHat pbU lamU (m + 1) ≤ 1 := by
    intro N
    rcases N with _ | N
    · simp
    · rw [Finset.sum_range_succ']
      simp only [zero_add, h1]
      have : ∑ m ∈ range N, betaHat pbU lamU (m + 1 + 1) = 0 :=
        Finset.sum_eq_zero fun m _ => h2 m
      linarith
  exact ⟨h1, h2, hB, HTB_le pbU_nonneg pbU_row lamU_pos lamU_inv lamU_tot ℓ hB h⟩

end Witness

end GFNBounds.Balance.TBHessian
