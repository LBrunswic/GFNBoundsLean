import GFNBounds.Doubling.Tail

/-!
# Sums of a power over a window, by telescoping

Support for `lem:doubling_expansion`'s weak form. The paper's Step 2 is Euler–Maclaurin for
`t^{−r}` with a complete-monotonicity remainder; what the appendix actually consumes downstream is
only `eq:doubling_R0`, `½ ≤ R₀(m) ≤ 2` and `|R₀(m) − 1| ≤ c₄/m`, and those need no more than a
first-order comparison. This file does that comparison by telescoping against `j ↦ j^{−r}`, exactly
as `Tail.lean` does for the infinite tail, and with the same two increments.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-- `t^{−r} − (t+1)^{−r} ≤ r t^{−r−1}` for `r > 0`, `t > 0`. -/
theorem incr_le' {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    t ^ (-r) - (t + 1) ^ (-r) ≤ r * t ^ (-r - 1) := by
  have h := incr_le (p := r + 1) (by linarith) ht
  have e1 : (1 : ℝ) - (r + 1) = -r := by ring
  have e2 : -(r + 1) = -r - 1 := by ring
  rw [e1, e2] at h
  have e3 : r + 1 - 1 = r := by ring
  rw [e3] at h
  exact h

/-- `r (t+1)^{−r−1} ≤ t^{−r} − (t+1)^{−r}` for `r > 0`, `t > 0`. -/
theorem le_incr' {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    r * (t + 1) ^ (-r - 1) ≤ t ^ (-r) - (t + 1) ^ (-r) := by
  have h := le_incr (p := r + 1) (by linarith) ht
  have e1 : (1 : ℝ) - (r + 1) = -r := by ring
  have e2 : -(r + 1) = -r - 1 := by ring
  rw [e1, e2] at h
  have e3 : r + 1 - 1 = r := by ring
  rw [e3] at h
  exact h

/-- Telescoping over `Ico a b`. -/
theorem telescope_Ico (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (f j - f (j + 1)) = f a - f b := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hcong : ∑ k ∈ Finset.range (b - a), (f (a + k) - f (a + k + 1))
      = ∑ k ∈ Finset.range (b - a), (f (a + k) - f (a + (k + 1))) :=
    Finset.sum_congr rfl fun k _ => by rw [Nat.add_assoc]
  rw [hcong, Finset.sum_range_sub' (fun i : ℕ => f (a + i)) (b - a)]
  have hab' : a + (b - a) = b := by omega
  rw [hab', Nat.add_zero]

/-- **Lower bound.** `(a^{−r} − b^{−r})/r ≤ Σ_{j=a}^{b−1} j^{−r−1}`. -/
theorem sum_window_ge {r : ℝ} (hr : 0 < r) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ((a : ℝ) ^ (-r) - (b : ℝ) ^ (-r)) / r
      ≤ ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-r - 1) := by
  have hstep : ∀ j ∈ Finset.Ico a b,
      ((j : ℝ) ^ (-r) - ((j + 1 : ℕ) : ℝ) ^ (-r)) / r ≤ (j : ℝ) ^ (-r - 1) := by
    intro j hj
    have hj1 : 1 ≤ j := le_trans ha (Finset.mem_Ico.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hcast : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast, div_le_iff₀ hr]
    have := incr_le' hr hjpos
    linarith
  have hsum := Finset.sum_le_sum hstep
  rw [← Finset.sum_div, telescope_Ico (fun j : ℕ => ((j : ℝ) ^ (-r))) hab] at hsum
  exact hsum

/-- **Upper bound.** `Σ_{j=a}^{b−1} j^{−r−1} ≤ a^{−r−1} + (a^{−r} − b^{−r})/r`. -/
theorem sum_window_le {r : ℝ} (hr : 0 < r) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-r - 1)
      ≤ (a : ℝ) ^ (-r - 1) + ((a : ℝ) ^ (-r) - (b : ℝ) ^ (-r)) / r := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · simp only [Finset.Ico_self, Finset.sum_empty, sub_self, zero_div, add_zero]
    positivity
  · -- split off the first term and telescope the rest
    have hsplit : ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-r - 1)
        = (a : ℝ) ^ (-r - 1) + ∑ j ∈ Finset.Ico (a + 1) b, (j : ℝ) ^ (-r - 1) :=
      Finset.sum_eq_sum_Ico_succ_bot hlt _
    have hstep : ∀ j ∈ Finset.Ico (a + 1) b,
        (j : ℝ) ^ (-r - 1) ≤ (((j - 1 : ℕ)) : ℝ) ^ (-r) / r - (j : ℝ) ^ (-r) / r := by
      intro j hj
      have hja : a + 1 ≤ j := (Finset.mem_Ico.mp hj).1
      have hj1 : 1 ≤ j := by omega
      have hjm : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by
        have : 1 ≤ j - 1 + 1 := by omega
        have h2 : 1 ≤ j - 1 := by omega
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h2
      have hcast : (((j - 1 : ℕ)) : ℝ) + 1 = (j : ℝ) := by
        have : (1 : ℕ) ≤ j := hj1
        push_cast [Nat.cast_sub this]; ring
      have h := le_incr' hr hjm
      rw [hcast] at h
      rw [← sub_div, le_div_iff₀ hr]
      linarith
    have hsum := Finset.sum_le_sum hstep
    have htel := telescope_Ico (fun j : ℕ => (((j - 1 : ℕ)) : ℝ) ^ (-r) / r)
      (by omega : a + 1 ≤ b)
    simp only [Nat.add_sub_cancel] at htel
    rw [htel] at hsum
    have hbm : (((b - 1 : ℕ)) : ℝ) ^ (-r) ≥ (b : ℝ) ^ (-r) := by
      have hb1 : 1 ≤ b := by omega
      have h1 : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by
        have h2 : 1 ≤ b - 1 := by omega
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h2
      have h2 : (((b - 1 : ℕ)) : ℝ) ≤ (b : ℝ) := by
        have : b - 1 ≤ b := by omega
        exact_mod_cast this
      exact rpow_le_rpow_of_nonpos h1 h2 (by linarith)
    rw [hsplit]
    have : ((a : ℝ) ^ (-r) - (b : ℝ) ^ (-r)) / r
        = (a : ℝ) ^ (-r) / r - (b : ℝ) ^ (-r) / r := by ring
    rw [this]
    have hdiv : (b : ℝ) ^ (-r) / r ≤ (((b - 1 : ℕ)) : ℝ) ^ (-r) / r := by gcongr
    linarith [hsum, hdiv]

end GFNBounds.Doubling
