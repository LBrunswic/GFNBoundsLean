import GFNBounds.Doubling.LeakageInstance

/-!
# The matched-mass flow of the doubling graph, and the flow whose sampler escapes

`Leak.sampler_escapes_doubling` says what the sampler of a flow at matched mass does on a
transient row; this file shows that such a flow exists, on every row of every setting. It is
built by the cut balance. Across the cut above the rung `N`, a balanced flow `λ` on the rungs
carries down `λ(N + 1)(1 − ε(N + 1))`, carries up the doublings out of the rungs `N/2 < j ≤ N`,
takes in the target mass of the rungs `j ≤ N`, and gives the source `λ(1)(1 − ε(1))`. At matched
mass the last is the whole target mass, so
`λ(N + 1)(1 − ε(N + 1)) = Σ_{j > N} row(j) + Σ_{N/2 < j ≤ N} λ(j)ε(j)`,
a recursion with non-negative terms only. It defines a positive finite flow, and the difference of
two consecutive cuts is the balance at a rung.

On a transient row the flow so built is the one the conjecture asks for: its sampler escapes to
infinity with probability `1 − P_{s₀}(τ⁺_{s₀} < ∞) > 0`, and stops at `x` with probability
`ρ(x)h(x)`.

## What is proved

| | |
|---|---|
| `rowTail`, `rowTail_zero`, `rowTail_succ` | the target mass beyond a rung |
| `mflow`, `mflow_succ`, `mflow_cut` | the flow on the rungs, by the cut balance |
| **`mflow_pos`** | it is positive on every rung |
| `mflow_one` | `λ(1)(1 − ε(1)) = 1`: the initial mass is the target mass |
| **`mflow_balance`** | it is balanced at every rung |
| `mflowE`, `tsum_mul_Q`, `mflowE_balance`, `mflowE_mass` | the same in `ℝ≥0∞`, scaled by `Z`, in the form of `Graph.Leakage` |
| **`exists_matched_flow`** | a positive, finite, balanced flow at matched mass exists, on every row |
| **`matched_flow_unique`** | it is the only balanced flow at matched mass |
| **`exists_escaping_flow`** | on a transient row, a flow exists whose sampler escapes with probability `1 − P_{s₀}(τ⁺_{s₀} < ∞) > 0` and otherwise draws `ρh` |

## Hypothesis checklist

| hypothesis | here |
|---|---|
| the loop closure of the doubling graph | `Q`, `k`, `ρ` of `Leak`, at `cap = none` |
| a target row | `S.row`, a probability supported in `{1, …, d}` |
| a transient row | `ε = ε_{c,s}` with `s < 1`, or `s = 1` and `c > 1/ln 2` |
| the terminal mass | `Z`, positive and finite |

## SCOPE (disclosed)

* **No `sorry`.**

Provenance: mathlib tag `v4.31.0`, pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open scoped ENNReal

namespace Leak

variable {S : Setting}

/-- **The target mass beyond the rung `N`**: `Σ_{N < j ≤ d} row(j)`. -/
noncomputable def rowTail (S : Setting) (N : ℕ) : ℝ := ∑ j ∈ Finset.Ioc N S.d, S.row j

theorem rowTail_nonneg (N : ℕ) : 0 ≤ rowTail S N :=
  Finset.sum_nonneg fun j _ => S.row_nonneg j

/-- All of the target mass lies beyond the source. -/
theorem rowTail_zero : rowTail S 0 = 1 := by
  have h : Finset.Ioc 0 S.d = Finset.Icc 1 S.d := by
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [rowTail, h, S.row_sum]

theorem rowTail_succ (n : ℕ) : rowTail S n = S.row (n + 1) + rowTail S (n + 1) := by
  unfold rowTail
  rcases le_or_gt (n + 1) S.d with h | h
  · rw [← Finset.sum_Ioc_consecutive _ (by omega : n ≤ n + 1) h,
      Finset.sum_Ioc_succ_top (le_refl n), Finset.Ioc_self, Finset.sum_empty, zero_add]
  · have h1 : Finset.Ioc n S.d = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    have h2 : Finset.Ioc (n + 1) S.d = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    have hr : S.row (n + 1) = 0 := by
      by_contra hne
      have := (S.row_supp hne).2
      omega
    rw [h1, h2, hr, Finset.sum_empty, add_zero]

/-- **The matched-mass flow on the rungs**, by the cut balance above the rung `N`:
`λ(N + 1) = (Σ_{j > N} row(j) + Σ_{N/2 < j ≤ N} λ(j)ε(j))/(1 − ε(N + 1))`. -/
noncomputable def mflow (S : Setting) : ℕ → ℝ
  | 0 => 0
  | N + 1 => (rowTail S N + ∑ j ∈ Finset.Ioc (N / 2) N,
      if _h : j < N + 1 then mflow S j * S.eps j else 0) / (1 - S.eps (N + 1))

theorem mflow_succ (N : ℕ) :
    mflow S (N + 1) = (rowTail S N + ∑ j ∈ Finset.Ioc (N / 2) N, mflow S j * S.eps j)
      / (1 - S.eps (N + 1)) := by
  have hs : (∑ j ∈ Finset.Ioc (N / 2) N, if _h : j < N + 1 then mflow S j * S.eps j else 0)
      = ∑ j ∈ Finset.Ioc (N / 2) N, mflow S j * S.eps j :=
    Finset.sum_congr rfl fun j hj => dif_pos (by have := (Finset.mem_Ioc.mp hj).2; omega)
  rw [mflow, hs]

/-- **The cut balance** above the rung `N`. -/
theorem mflow_cut (N : ℕ) :
    mflow S (N + 1) * (1 - S.eps (N + 1))
      = rowTail S N + ∑ j ∈ Finset.Ioc (N / 2) N, mflow S j * S.eps j := by
  rw [mflow_succ, div_mul_cancel₀ _ (S.one_sub_eps_pos (by omega)).ne']

/-- **The flow is positive on every rung.** -/
theorem mflow_pos (N : ℕ) : 0 < mflow S (N + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rw [mflow_succ]
    refine div_pos ?_ (S.one_sub_eps_pos (by omega))
    have hnn : ∀ j ∈ Finset.Ioc (N / 2) N, 0 ≤ mflow S j * S.eps j := by
      intro j hj
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact mul_nonneg (ih i (by omega)).le (S.eps_pos (by omega)).le
    have hsum := Finset.sum_nonneg hnn
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      rw [rowTail_zero]
      linarith
    · obtain ⟨i, hi⟩ : ∃ i, N = i + 1 := ⟨N - 1, by omega⟩
      have hterm : 0 < mflow S N * S.eps N := by
        rw [hi]
        exact mul_pos (ih i (by omega)) (S.eps_pos (by omega))
      have hle : mflow S N * S.eps N ≤ ∑ j ∈ Finset.Ioc (N / 2) N, mflow S j * S.eps j :=
        Finset.single_le_sum (f := fun j => mflow S j * S.eps j) hnn
          (Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩)
      linarith [rowTail_nonneg (S := S) N]

/-- **The initial mass is the target mass**: `λ(1)(1 − ε(1)) = 1`. -/
theorem mflow_one : mflow S 1 * (1 - S.eps 1) = 1 := by
  have h := mflow_cut (S := S) 0
  rw [Nat.zero_div, Finset.Ioc_self, Finset.sum_empty, add_zero, rowTail_zero] at h
  exact h

/-- **The flow is balanced at every rung**: the rung `n + 1` takes in what steps down from the rung
`n + 2`, what doubles from the rung `(n + 1)/2` when `n + 1` is even, and its target mass. -/
theorem mflow_balance (n : ℕ) :
    mflow S (n + 1) = mflow S (n + 1 + 1) * (1 - S.eps (n + 1 + 1))
      + (if n % 2 = 1 then mflow S (n / 2 + 1) * S.eps (n / 2 + 1) else 0) + S.row (n + 1) := by
  have hc1 := mflow_cut (S := S) (n + 1)
  have hc0 := mflow_cut (S := S) n
  have ht := rowTail_succ (S := S) n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : 2 * k / 2 = k := by omega
    rw [h1, Finset.sum_Ioc_succ_top (by omega : k ≤ 2 * k)] at hc1
    rw [h2] at hc0
    rw [if_neg (by omega)]
    linear_combination -hc1 + hc0 + ht
  · have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    rw [h1, Finset.sum_Ioc_succ_top (by omega : k + 1 ≤ 2 * k + 1)] at hc1
    rw [h2, ← Finset.sum_Ioc_consecutive _ (by omega : k ≤ k + 1) (by omega : k + 1 ≤ 2 * k + 1),
      Finset.sum_Ioc_succ_top (le_refl k), Finset.Ioc_self, Finset.sum_empty, zero_add] at hc0
    rw [if_pos (by omega), h2]
    linear_combination -hc1 + hc0 + ht

/-- **The matched-mass flow**, in the form of `Graph.Leakage`: `μ(i) = Z·λ(i + 1)`. -/
noncomputable def mflowE (S : Setting) (Z : ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  Z * ENNReal.ofReal (mflow S (i + 1))

/-- **What enters the rung `y + 1` from the rungs**: the step down from `y + 2`, and the doubling
from `(y + 1)/2` when `y + 1` is even. -/
theorem tsum_mul_Q (μ : ℕ → ℝ≥0∞) (y : ℕ) :
    ∑' x, μ x * Q S x y
      = (if y % 2 = 1 then μ (y / 2) * ENNReal.ofReal (S.eps (y / 2 + 1)) else 0)
        + μ (y + 1) * ENNReal.ofReal (1 - S.eps (y + 1 + 1)) := by
  have hsplit : ∀ x, μ x * Q S x y
      = μ x * (if y = 2 * x + 1 then ENNReal.ofReal (S.eps (x + 1)) else 0)
        + μ x * (if y + 1 = x then ENNReal.ofReal (1 - S.eps (x + 1)) else 0) :=
    fun x => by rw [Q, mul_add]
  rw [tsum_congr hsplit, ENNReal.tsum_add]
  congr 1
  · rcases Nat.mod_two_eq_zero_or_one y with hy | hy
    · rw [if_neg (by omega)]
      exact ENNReal.tsum_eq_zero.mpr fun x => by rw [if_neg (by omega), mul_zero]
    · rw [if_pos hy, tsum_eq_single (y / 2) fun b hb => by rw [if_neg (by omega), mul_zero],
        if_pos (by omega)]
  · rw [tsum_eq_single (y + 1) fun b hb => by rw [if_neg (by omega), mul_zero], if_pos rfl]

theorem mflowE_ne_zero {Z : ℝ≥0∞} (hZ0 : Z ≠ 0) (y : ℕ) : mflowE S Z y ≠ 0 :=
  mul_ne_zero hZ0 (ENNReal.ofReal_pos.mpr (mflow_pos y)).ne'

theorem mflowE_ne_top {Z : ℝ≥0∞} (hZt : Z ≠ ∞) (y : ℕ) : mflowE S Z y ≠ ∞ :=
  ENNReal.mul_ne_top hZt ENNReal.ofReal_ne_top

/-- **The flow is balanced**, in the form `μ = μQ + Zρ` of `Graph.Leakage`. -/
theorem mflowE_balance (Z : ℝ≥0∞) (y : ℕ) :
    mflowE S Z y = (∑' x, mflowE S Z x * Q S x y) + Z * ρ S y := by
  rw [tsum_mul_Q]
  have hb := mflow_balance (S := S) y
  have h1 : 0 ≤ mflow S (y + 1 + 1) := (mflow_pos (y + 1)).le
  have he1 : 0 ≤ 1 - S.eps (y + 1 + 1) := one_sub_eps_nonneg (y + 1)
  simp only [mflowE, ρ]
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy
  · rw [if_neg (by omega)] at hb ⊢
    rw [hb, add_zero, ENNReal.ofReal_add (mul_nonneg h1 he1) (S.row_nonneg _),
      ENNReal.ofReal_mul h1]
    ring
  · rw [if_pos hy] at hb ⊢
    have hh : 0 ≤ mflow S (y / 2 + 1) := (mflow_pos (y / 2)).le
    have heh : 0 ≤ S.eps (y / 2 + 1) := eps_nonneg (y / 2)
    rw [hb, ENNReal.ofReal_add (add_nonneg (mul_nonneg h1 he1) (mul_nonneg hh heh))
        (S.row_nonneg _), ENNReal.ofReal_add (mul_nonneg h1 he1) (mul_nonneg hh heh),
      ENNReal.ofReal_mul h1, ENNReal.ofReal_mul hh]
    ring

/-- **The initial mass is the terminal mass**: `Σ μ(x)k(x) = Z`. -/
theorem mflowE_mass {Z : ℝ≥0∞} : Z = ∑' x, mflowE S Z x * k S x := by
  rw [tsum_eq_single 0 fun b hb => by rw [k, if_neg hb, mul_zero]]
  rw [mflowE, k, if_pos rfl, mul_assoc, ← ENNReal.ofReal_mul (mflow_pos 0).le,
    show mflow S (0 + 1) * (1 - S.eps 1) = 1 from mflow_one, ENNReal.ofReal_one, mul_one]

/-- **A flow at matched mass exists, on every row.** On the loop closure of the doubling graph,
for every target row and every terminal mass `Z`, positive and finite, there is a flow of the
frozen family, positive and finite on every rung and balanced at every rung, whose initial mass is
`Z`. -/
theorem exists_matched_flow {Z : ℝ≥0∞} (hZ0 : Z ≠ 0) (hZt : Z ≠ ∞) :
    ∃ μ : ℕ → ℝ≥0∞, (∀ y, μ y ≠ 0) ∧ (∀ y, μ y ≠ ∞)
      ∧ (∀ y, μ y = (∑' x, μ x * Q S x y) + Z * ρ S y)
      ∧ Z = ∑' x, μ x * k S x :=
  ⟨mflowE S Z, mflowE_ne_zero hZ0, mflowE_ne_top hZt, mflowE_balance Z, mflowE_mass⟩

/-- **On a transient row there is a flow whose sampler escapes.** For `ε = ε_{c,s}` with `s < 1`,
or `s = 1` and `c > 1/ln 2`, and every terminal mass `Z`, positive and finite, there is a flow of
the frozen family, positive, finite, balanced and at matched mass, whose sampler stops at `x` with
probability `ρ(x)h(x)`, stops at all with probability `P_{s₀}(τ⁺_{s₀} < ∞) < 1`, and escapes to
infinity otherwise. -/
theorem exists_escaping_flow {c s : ℝ} (hc : 0 < c) (hS : ∀ j, S.eps j = epsCS c s j)
    (hrow : s < 1 ∨ (s = 1 ∧ 1 / Real.log 2 < c)) {Z : ℝ≥0∞} (hZ0 : Z ≠ 0) (hZt : Z ≠ ∞) :
    ∃ μ : ℕ → ℝ≥0∞, (∀ y, μ y ≠ 0) ∧ (∀ y, μ y ≠ ∞)
      ∧ (∀ y, μ y = (∑' x, μ x * Q S x y) + Z * ρ S y)
      ∧ Z = ∑' x, μ x * k S x
      ∧ (∀ x, Graph.Leakage.stopLaw (Q S) (k S) μ Z Z (ρ S) x
          = ρ S x * Graph.Leakage.absorb (Q S) (k S) x)
      ∧ (∑' i, Graph.Leakage.stopLaw (Q S) (k S) μ Z Z (ρ S) i)
          = ENNReal.ofReal (retProb S none St.src)
      ∧ (∑' i, Graph.Leakage.stopLaw (Q S) (k S) μ Z Z (ρ S) i) < 1 := by
  obtain ⟨μ, h0, ht, hb, hm⟩ := exists_matched_flow (S := S) hZ0 hZt
  obtain ⟨hlaw, -⟩ := Graph.Leakage.sampler_leaks_matched h0 ht hb hm hZ0 hZt
  obtain ⟨htot, hlt⟩ := sampler_escapes_doubling hc hS hrow h0 ht hb hm hZ0 hZt
  exact ⟨μ, h0, ht, hb, hm, hlaw, htot, hlt⟩

/-- **The matched-mass flow is unique.** On the loop closure of the doubling graph, with a finite
terminal mass `Z`, every flow of the frozen family that is balanced at every rung and has initial
mass `Z` is the flow built by the cut balance: the initial mass fixes the lowest rung, and the
balance at a rung fixes the next one. -/
theorem matched_flow_unique {Z : ℝ≥0∞} (hZt : Z ≠ ∞) {μ : ℕ → ℝ≥0∞}
    (hbal : ∀ y, μ y = (∑' x, μ x * Q S x y) + Z * ρ S y)
    (hm : Z = ∑' x, μ x * k S x) : μ = mflowE S Z := by
  funext y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    rcases y with _ | y
    · have ha0 : ENNReal.ofReal (1 - S.eps 1) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (S.one_sub_eps_pos le_rfl)).ne'
      have h1 : Z = μ 0 * ENNReal.ofReal (1 - S.eps 1) := by
        rw [hm, tsum_eq_single 0 fun b hb => by rw [k, if_neg hb, mul_zero], k, if_pos rfl]
      have h2 := mflowE_mass (S := S) (Z := Z)
      rw [tsum_eq_single 0 fun b hb => by rw [k, if_neg hb, mul_zero], k, if_pos rfl] at h2
      exact (ENNReal.mul_left_inj ha0 ENNReal.ofReal_ne_top).mp (h1.symm.trans h2)
    · have hb := hbal y
      have hb' := mflowE_balance (S := S) Z y
      rw [tsum_mul_Q] at hb hb'
      rw [ih y (Nat.lt_succ_self y), ih (y / 2) (by omega)] at hb
      have ha0 : ENNReal.ofReal (1 - S.eps (y + 1 + 1)) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (S.one_sub_eps_pos (by omega))).ne'
      have hD : (if y % 2 = 1 then mflowE S Z (y / 2) * ENNReal.ofReal (S.eps (y / 2 + 1))
          else 0) ≠ ∞ := by
        split_ifs
        · exact ENNReal.mul_ne_top (mflowE_ne_top hZt _) ENNReal.ofReal_ne_top
        · exact ENNReal.zero_ne_top
      have hR : Z * ρ S y ≠ ∞ := ENNReal.mul_ne_top hZt ENNReal.ofReal_ne_top
      have h := (ENNReal.add_right_inj hD).mp ((ENNReal.add_left_inj hR).mp (hb.symm.trans hb'))
      exact (ENNReal.mul_left_inj ha0 ENNReal.ofReal_ne_top).mp h

end Leak

end GFNBounds.Doubling
