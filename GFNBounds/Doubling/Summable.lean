import GFNBounds.Doubling.CutBalance
import GFNBounds.Doubling.Range

/-!
# The cut balance is summable at `s = 1`, `0 < c < 1`

Ingredient of **`prop:doubling_phase`** Step 5 — `app_doubling.tex:510–624` — and a weak,
*unconditional* form of **`theo:doubling_decay`**(2) — `app_doubling.tex:1155–1228`.

> (`prop:doubling_cut`) `λ_m(1 − ε(m)) = Σ_{j=⌈m/2⌉}^{m−1} λ_j ε(j)` for every `m > d`.
>
> (`theo:doubling_decay`(2)) there are `0 < c₁ ≤ c₂` with `c₁ j^{−p_*} ≤ λ_j ≤ c₂ j^{−p_*}` for
> every `j ≥ 1`.

At `s = 1` and `0 < c < 1` the Cramér root has `p_* > 1` (`lem:doubling_cramer_root`(1)), so
`theo:doubling_decay`(2) makes `(λ_j)` summable. That route is not available here:
`theo:doubling_decay` is proved in this library only conditionally on `eq:doubling_product`
(see `Descent.lean`). **Summability does not need it.** Summing the cut balance over
`m ∈ {1,…,N}` and exchanging the double sum gives, with no asymptotics and no chain,

  `(1 − c) Σ_{m=1}^{N} λ_m ≤ Σ_{m=1}^{N} g_m`

whenever `λ_m(1 − ε(m)) ≤ Σ_{j ∈ W(m)} λ_j ε(j) + g_m` on that range, because each `j` occurs in
exactly `min(N, 2j) − j ≤ j` of the windows `W(1),…,W(N)`, and `ε(j)(1 + j) = c` exactly at
`s = 1`. That is `partial_sum_le`, and it is where `c < 1` is spent.

## SCOPE (disclosed)

* **This is weaker than `theo:doubling_decay`(2)** and is not a substitute for it: it gives no
  pointwise decay rate, only `Σ_{j≥1} λ_j ≤ (Σ_{j≤d} λ_j)/(1−c)`. What it is good for is exactly
  what the pointwise rate is used for downstream of `prop:doubling_phase` Step 5 — normalising an
  invariant measure — and there it is unconditional where the decay theorem is not.
* **`s = 1` is essential, not a convenience.** `partial_sum_le` consumes `ε(j)(1+j) = c`, which is
  `prop:doubling_drift`'s "constant drift iff `s = 1`". At `s ≠ 1` the same computation gives
  `ε(j)(1+j) = c(j+1)^{1−s}`, unbounded for `s < 1` and vanishing for `s > 1`, and the argument
  says nothing.
* The hypothesis is an **inequality**, `≤`, not the cut balance itself, and the excess `g` is a
  parameter. Both instances need that: a `CutBalanceSeq` satisfies the recursion only above `d`,
  and `GFNBounds.Doubling.StatExists` builds a sequence satisfying a *row-corrected* recursion
  whose excess is the tail of the target row.
* Nothing here asserts positivity, invariance or normalisation of `λ`; `hlam` is `0 ≤ λ_j` alone.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1` | ✓ carried, pointwise on the ladder (`heps`) |
| `0 < c < 1` | ✓ carried; `c < 1` is what makes the conclusion finite |
| `eq:doubling_cut` at every `m > d` | ✓ carried (`CutBalanceSeq S lam ⊤`); ⚠ weakened to `≤` in `partial_sum_le` |
| `(λ_j)` positive | ⚠ weakened to non-negative |
| `theo:doubling_decay`'s `eq:doubling_product` | ✗ not used — that is the point |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-- `j` lies in the window of `m` with `1 ≤ m ≤ N` exactly when `j + 1 ≤ m ≤ min(N, 2j)` and
`1 ≤ j ≤ N`: the index swap behind `window_double_sum`. -/
theorem window_swap (N : ℕ) : ∀ (m j : ℕ),
    (m ∈ Finset.Icc 1 N ∧ j ∈ window m) ↔
      (m ∈ Finset.Icc (j + 1) (min N (2 * j)) ∧ j ∈ Finset.Icc 1 N) := by
  intro m j
  simp only [Finset.mem_Icc, window, Finset.mem_Ico, le_min_iff]
  omega

/-- **The double-counting step.** Each ladder index `j` is carried across a cut by exactly
`min(N, 2j) − j` of the windows `W(1), …, W(N)`. -/
theorem window_double_sum (N : ℕ) (F : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 N, ∑ j ∈ window m, F j
      = ∑ j ∈ Finset.Icc 1 N, ((min N (2 * j) - j : ℕ) : ℝ) * F j := by
  rw [Finset.sum_comm' (window_swap N) (f := fun _ j => F j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  congr 2
  omega

variable {S : Setting}

/-- **The partial-sum bound.** At `s = 1`, a non-negative sequence obeying the cut balance up to
an excess `g` on `{1,…,N}` has `(1 − c) Σ_{m≤N} λ_m ≤ Σ_{m≤N} g_m`.

The whole content is that `min(N, 2j) − j ≤ j`, so the coefficient of `λ_j` after the exchange is
at least `1 − ε(j)(1 + j) = 1 − c`. -/
theorem partial_sum_le {c : ℝ} (hc0 : 0 < c)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1))
    {lam g : ℕ → ℝ} (hlam : ∀ j, 0 ≤ lam j) (N : ℕ)
    (hrec : ∀ m, 1 ≤ m → m ≤ N →
      lam m * (1 - S.eps m) ≤ ∑ j ∈ window m, lam j * S.eps j + g m) :
    (1 - c) * ∑ m ∈ Finset.Icc 1 N, lam m ≤ ∑ m ∈ Finset.Icc 1 N, g m := by
  have hsum : ∑ m ∈ Finset.Icc 1 N, lam m * (1 - S.eps m)
      ≤ ∑ m ∈ Finset.Icc 1 N, (∑ j ∈ window m, lam j * S.eps j + g m) :=
    Finset.sum_le_sum fun m hm =>
      hrec m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
  rw [Finset.sum_add_distrib, window_double_sum] at hsum
  have hkey : (1 - c) * ∑ m ∈ Finset.Icc 1 N, lam m
      ≤ ∑ m ∈ Finset.Icc 1 N, lam m * (1 - S.eps m)
        - ∑ j ∈ Finset.Icc 1 N, ((min N (2 * j) - j : ℕ) : ℝ) * (lam j * S.eps j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hj1, _⟩ := Finset.mem_Icc.mp hj
    have hb : (0:ℝ) < (j : ℝ) + 1 := base_pos j
    have hk : ((min N (2 * j) - j : ℕ) : ℝ) ≤ (j : ℝ) := by
      have h : (min N (2 * j) - j : ℕ) ≤ j := by omega
      exact_mod_cast h
    have hk0 : (0:ℝ) ≤ ((min N (2 * j) - j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hepsj : S.eps j = c / ((j : ℝ) + 1) := heps j hj1
    have hle : S.eps j * (1 + ((min N (2 * j) - j : ℕ) : ℝ)) ≤ c := by
      rw [hepsj, div_mul_eq_mul_div, div_le_iff₀ hb]
      nlinarith
    nlinarith [hlam j, mul_le_mul_of_nonneg_left hle (hlam j)]
  linarith

/-- The instance for `CutBalanceSeq`: the excess is carried by the boundary data alone, the
recursion being an equality above `d`. -/
theorem cutBalance_partial_sum_le {c : ℝ} (hc0 : 0 < c)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1))
    {lam : ℕ → ℝ} (hlam : ∀ j, 0 ≤ lam j) (hcb : CutBalanceSeq S lam ⊤) (N : ℕ) :
    (1 - c) * ∑ m ∈ Finset.Icc 1 N, lam m ≤ ∑ m ∈ Finset.Icc 1 S.d, lam m := by
  refine le_trans (partial_sum_le hc0 heps hlam N
    (g := fun m => if m ≤ S.d then lam m * (1 - S.eps m) else 0) ?_) ?_
  · intro m hm1 _
    by_cases hmd : m ≤ S.d
    · simp only [hmd, if_true]
      have hw : (0:ℝ) ≤ ∑ j ∈ window m, lam j * S.eps j := by
        refine Finset.sum_nonneg fun j hj => mul_nonneg (hlam j) (S.eps_pos ?_).le
        have h := mem_window.mp hj
        omega
      linarith
    · simp only [hmd, if_false, add_zero]
      exact le_of_eq (hcb m (by omega) le_top)
  · have hstep : ∀ m ∈ Finset.Icc 1 N,
        (if m ≤ S.d then lam m * (1 - S.eps m) else 0)
          ≤ if m ∈ Finset.Icc 1 S.d then lam m else 0 := by
      intro m hm
      obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
      by_cases hmd : m ≤ S.d
      · have hmem : m ∈ Finset.Icc 1 S.d := Finset.mem_Icc.mpr ⟨hm1, hmd⟩
        simp only [hmd, if_true, hmem]
        nlinarith [hlam m, (S.eps_pos hm1).le, S.eps_le hm1, S.epsMax_lt_one]
      · simp only [hmd, if_false]
        split_ifs with hmem
        · exact hlam m
        · exact le_rfl
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_ite_mem]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun i _ _ => hlam i

/-- **The conclusion.** At `s = 1`, `0 < c < 1`, every non-negative solution of the cut balance is
summable, with the explicit bound `Σ_{j≥1} λ_j ≤ (Σ_{j≤d} λ_j)/(1−c)`. -/
theorem summable_of_cutBalanceSeq {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1))
    {lam : ℕ → ℝ} (hlam : ∀ j, 0 ≤ lam j) (hcb : CutBalanceSeq S lam ⊤) : Summable lam := by
  have hc : (0:ℝ) < 1 - c := by linarith
  refine summable_of_sum_range_le (f := lam) hlam (c := lam 0 + (∑ m ∈ Finset.Icc 1 S.d, lam m) / (1 - c)) ?_
  intro n
  have hsplit : ∑ i ∈ Finset.range n, lam i
      ≤ lam 0 + ∑ m ∈ Finset.Icc 1 n, lam m := by
    have hsub : Finset.range n ⊆ insert 0 (Finset.Icc 1 n) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hlam i) ?_
    rw [Finset.sum_insert (by simp)]
  have hb := cutBalance_partial_sum_le hc0 heps hlam hcb n
  have : ∑ m ∈ Finset.Icc 1 n, lam m ≤ (∑ m ∈ Finset.Icc 1 S.d, lam m) / (1 - c) := by
    rw [le_div_iff₀ hc]
    linarith
  linarith

end GFNBounds.Doubling
