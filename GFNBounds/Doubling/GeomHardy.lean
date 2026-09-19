import Mathlib

/-!
# A weighted discrete Hardy inequality under a geometric tail

The analytic core of the finite diffusion constant on the doubling graph under a geometrically
decaying doubling probability (`GeomOperator.lean`). It is a statement about real sequences and
knows nothing of the chain.

Let `λ : ℕ → ℝ` be non-negative and `T` a positive sequence dominating it, `λ_k ≤ T_k`, which
decays geometrically, `T_{k+1} ≤ q T_k` with `q < 1`, and is dominated back, `T_k ≤ B λ_k`
(`T` is the tail `Σ_{j ≥ k} λ_j` at the point of use). Then for every sequence `D` and every `N`

  `Σ_{x=1}^{N} λ_x (Σ_{k=1}^{x} D_k)² ≤ B/(1 − √q)² · Σ_{k=1}^{N} λ_k D_k²`.

The proof is Cauchy–Schwarz with the weights `√T_k`, then an exchange of the two finite sums; the
two geometric series it leaves are summed by induction, with no `tsum` anywhere.

## SCOPE (disclosed)

A lemma of this library's own, used by the geometric row of the policy table; it is not a
statement of the paper. Finite sums only: the passage to `N → ∞` is made where it is consumed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Finset

namespace Hardy

variable {lam T D : ℕ → ℝ} {q B : ℝ}

/-- `√T_{x+1} ≤ √q · √T_x`. -/
theorem sqrt_step (hq0 : 0 ≤ q) (hTq : ∀ k, 1 ≤ k → T (k + 1) ≤ q * T k) {x : ℕ} (hx : 1 ≤ x) :
    Real.sqrt (T (x + 1)) ≤ Real.sqrt q * Real.sqrt (T x) := by
  rw [← Real.sqrt_mul hq0]
  exact Real.sqrt_le_sqrt (hTq x hx)

/-- `√T_{k+j} ≤ (√q)^j √T_k`. -/
theorem sqrt_geom (hq0 : 0 ≤ q) (hTq : ∀ k, 1 ≤ k → T (k + 1) ≤ q * T k) {k : ℕ} (hk : 1 ≤ k) :
    ∀ j : ℕ, Real.sqrt (T (k + j)) ≤ Real.sqrt q ^ j * Real.sqrt (T k) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have h := sqrt_step (T := T) hq0 hTq (x := k + j) (by omega)
      calc Real.sqrt (T (k + (j + 1))) = Real.sqrt (T (k + j + 1)) := by rw [Nat.add_assoc]
        _ ≤ Real.sqrt q * Real.sqrt (T (k + j)) := h
        _ ≤ Real.sqrt q * (Real.sqrt q ^ j * Real.sqrt (T k)) :=
            mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg q)
        _ = Real.sqrt q ^ (j + 1) * Real.sqrt (T k) := by ring

/-- `Σ_{j<n} r^j ≤ 1/(1 − r)` for `0 ≤ r < 1`. -/
theorem geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ range n, r ^ j ≤ 1 / (1 - r) := by
  have h1 : 0 < 1 - r := by linarith
  rw [le_div_iff₀ h1, geom_sum_mul_neg]
  have hrn : 0 ≤ r ^ n := pow_nonneg hr0 n
  linarith

/-- **The inner sum.** `Σ_{k=1}^{x} 1/√T_k ≤ 1/((1 − √q)√T_x)`. -/
theorem sum_inv_sqrt_le (hq0 : 0 ≤ q) (hq1 : q < 1) (hTpos : ∀ k, 1 ≤ k → 0 < T k)
    (hTq : ∀ k, 1 ≤ k → T (k + 1) ≤ q * T k) :
    ∀ x : ℕ, 1 ≤ x →
      ∑ k ∈ Icc 1 x, 1 / Real.sqrt (T k) ≤ 1 / ((1 - Real.sqrt q) * Real.sqrt (T x)) := by
  set r := Real.sqrt q with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hr1 : r < 1 := by
    rw [hr, Real.sqrt_lt' one_pos]; simpa using hq1
  have h1r : 0 < 1 - r := by linarith
  intro x hx
  induction x, hx using Nat.le_induction with
  | base =>
      simp only [Icc_self, sum_singleton]
      have hs : 0 < Real.sqrt (T 1) := Real.sqrt_pos.mpr (hTpos 1 le_rfl)
      rw [div_le_div_iff₀ hs (mul_pos h1r hs)]
      nlinarith
  | succ x hx ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hs : 0 < Real.sqrt (T x) := Real.sqrt_pos.mpr (hTpos x hx)
      have hs1 : 0 < Real.sqrt (T (x + 1)) := Real.sqrt_pos.mpr (hTpos (x + 1) (by omega))
      have hstep : Real.sqrt (T (x + 1)) ≤ r * Real.sqrt (T x) := sqrt_step hq0 hTq hx
      -- `1/√T_x ≤ r/√T_{x+1}`
      have hinv : 1 / Real.sqrt (T x) ≤ r / Real.sqrt (T (x + 1)) := by
        rw [div_le_div_iff₀ hs hs1]; linarith
      calc ∑ k ∈ Icc 1 x, 1 / Real.sqrt (T k) + 1 / Real.sqrt (T (x + 1))
          ≤ 1 / ((1 - r) * Real.sqrt (T x)) + 1 / Real.sqrt (T (x + 1)) := by linarith
        _ = (1 / (1 - r)) * (1 / Real.sqrt (T x)) + 1 / Real.sqrt (T (x + 1)) := by
            field_simp
        _ ≤ (1 / (1 - r)) * (r / Real.sqrt (T (x + 1))) + 1 / Real.sqrt (T (x + 1)) := by
            gcongr
        _ = 1 / ((1 - r) * Real.sqrt (T (x + 1))) := by
            field_simp
            ring

/-- **The outer sum.** `Σ_{x=k}^{N} λ_x/√T_x ≤ √T_k/(1 − √q)`. -/
theorem sum_lam_div_sqrt_le (hq0 : 0 ≤ q) (hq1 : q < 1) (hTpos : ∀ k, 1 ≤ k → 0 < T k)
    (hTq : ∀ k, 1 ≤ k → T (k + 1) ≤ q * T k)
    (hlamT : ∀ k, 1 ≤ k → lam k ≤ T k) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ∑ x ∈ Icc k N, lam x / Real.sqrt (T x) ≤ Real.sqrt (T k) / (1 - Real.sqrt q) := by
  set r := Real.sqrt q with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hr1 : r < 1 := by
    rw [hr, Real.sqrt_lt' one_pos]; simpa using hq1
  -- each term is at most `√T_x`, which is at most `r^(x-k) √T_k`
  have hterm : ∀ x ∈ Icc k N, lam x / Real.sqrt (T x) ≤ Real.sqrt (T x) := by
    intro x hxm
    have hx1 : 1 ≤ x := le_trans hk (mem_Icc.mp hxm).1
    have hs : 0 < Real.sqrt (T x) := Real.sqrt_pos.mpr (hTpos x hx1)
    rw [div_le_iff₀ hs, Real.mul_self_sqrt (hTpos x hx1).le]
    exact hlamT x hx1
  have hsum : ∑ x ∈ Icc k N, Real.sqrt (T x) ≤ Real.sqrt (T k) / (1 - r) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    calc ∑ j ∈ range (N + 1 - k), Real.sqrt (T (k + j))
        ≤ ∑ j ∈ range (N + 1 - k), r ^ j * Real.sqrt (T k) :=
          sum_le_sum fun j _ => sqrt_geom hq0 hTq hk j
      _ = (∑ j ∈ range (N + 1 - k), r ^ j) * Real.sqrt (T k) := by rw [sum_mul]
      _ ≤ (1 / (1 - r)) * Real.sqrt (T k) :=
          mul_le_mul_of_nonneg_right (geom_le hr0 hr1 _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (T k) / (1 - r) := by ring
  exact (sum_le_sum hterm).trans hsum

/-- **The weighted discrete Hardy inequality.**
`Σ_{x=1}^{N} λ_x (Σ_{k=1}^{x} D_k)² ≤ B/(1 − √q)² · Σ_{k=1}^{N} λ_k D_k²`. -/
theorem hardy (hq0 : 0 ≤ q) (hq1 : q < 1) (hTpos : ∀ k, 1 ≤ k → 0 < T k)
    (hTq : ∀ k, 1 ≤ k → T (k + 1) ≤ q * T k) (hlam0 : ∀ k, 0 ≤ lam k)
    (hlamT : ∀ k, 1 ≤ k → lam k ≤ T k) (hTB : ∀ k, 1 ≤ k → T k ≤ B * lam k) (N : ℕ) :
    ∑ x ∈ Icc 1 N, lam x * (∑ k ∈ Icc 1 x, D k) ^ 2
      ≤ B / (1 - Real.sqrt q) ^ 2 * ∑ k ∈ Icc 1 N, lam k * D k ^ 2 := by
  set r := Real.sqrt q with hr
  have hr1 : r < 1 := by
    rw [hr, Real.sqrt_lt' one_pos]; simpa using hq1
  have h1r : 0 < 1 - r := by linarith
  set s : ℕ → ℝ := fun k => Real.sqrt (T k) with hs_def
  have hspos : ∀ k, 1 ≤ k → 0 < s k := fun k hk => Real.sqrt_pos.mpr (hTpos k hk)
  -- Step 1: Cauchy–Schwarz with the weights `√T_k`
  have hCS : ∀ x ∈ Icc 1 N, (∑ k ∈ Icc 1 x, D k) ^ 2
      ≤ (∑ k ∈ Icc 1 x, 1 / s k) * ∑ k ∈ Icc 1 x, s k * D k ^ 2 := by
    intro x _
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
    · exact (one_div_pos.mpr (hspos k (mem_Icc.mp hk).1)).le
    · exact mul_nonneg (hspos k (mem_Icc.mp hk).1).le (sq_nonneg _)
    · have := (hspos k (mem_Icc.mp hk).1).ne'
      refine le_of_eq ?_
      field_simp
  -- Step 2: the inner sum
  have hstep2 : ∀ x ∈ Icc 1 N, lam x * (∑ k ∈ Icc 1 x, D k) ^ 2
      ≤ ∑ k ∈ Icc 1 x, (1 / (1 - r)) * (lam x / s x) * (s k * D k ^ 2) := by
    intro x hx
    have hx1 : 1 ≤ x := (mem_Icc.mp hx).1
    have hinner := sum_inv_sqrt_le hq0 hq1 hTpos hTq x hx1
    have hB : 0 ≤ ∑ k ∈ Icc 1 x, s k * D k ^ 2 :=
      sum_nonneg fun k hk => mul_nonneg (hspos k (mem_Icc.mp hk).1).le (sq_nonneg _)
    calc lam x * (∑ k ∈ Icc 1 x, D k) ^ 2
        ≤ lam x * ((∑ k ∈ Icc 1 x, 1 / s k) * ∑ k ∈ Icc 1 x, s k * D k ^ 2) :=
          mul_le_mul_of_nonneg_left (hCS x hx) (hlam0 x)
      _ ≤ lam x * ((1 / ((1 - r) * s x)) * ∑ k ∈ Icc 1 x, s k * D k ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinner hB) (hlam0 x)
      _ = ∑ k ∈ Icc 1 x, (1 / (1 - r)) * (lam x / s x) * (s k * D k ^ 2) := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun k _ => ?_
          have := (hspos x hx1).ne'
          have := h1r.ne'
          field_simp
  -- Step 3: exchange the sums
  have hswap : ∑ x ∈ Icc 1 N, ∑ k ∈ Icc 1 x, (1 / (1 - r)) * (lam x / s x) * (s k * D k ^ 2)
      = ∑ k ∈ Icc 1 N, ∑ x ∈ Icc k N, (1 / (1 - r)) * (lam x / s x) * (s k * D k ^ 2) := by
    refine sum_comm' fun x k => ?_
    simp only [mem_Icc]
    omega
  -- Step 4: the outer sum
  have hstep4 : ∀ k ∈ Icc 1 N,
      ∑ x ∈ Icc k N, (1 / (1 - r)) * (lam x / s x) * (s k * D k ^ 2)
        ≤ (1 / (1 - r) ^ 2) * (T k * D k ^ 2) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have houter := sum_lam_div_sqrt_le (lam := lam) hq0 hq1 hTpos hTq hlamT hk1 N
    have hsk : 0 ≤ s k * D k ^ 2 := mul_nonneg (hspos k hk1).le (sq_nonneg _)
    rw [← sum_mul, ← mul_sum]
    calc (1 / (1 - r) * ∑ x ∈ Icc k N, lam x / s x) * (s k * D k ^ 2)
        = 1 / (1 - r) * ((∑ x ∈ Icc k N, lam x / s x) * (s k * D k ^ 2)) := by ring
      _ ≤ 1 / (1 - r) * ((s k / (1 - r)) * (s k * D k ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right houter hsk)
            (one_div_pos.mpr h1r).le
      _ = (1 / (1 - r) ^ 2) * ((s k * s k) * D k ^ 2) := by field_simp
      _ = (1 / (1 - r) ^ 2) * (T k * D k ^ 2) := by
          rw [hs_def]; simp only; rw [Real.mul_self_sqrt (hTpos k hk1).le]
  calc ∑ x ∈ Icc 1 N, lam x * (∑ k ∈ Icc 1 x, D k) ^ 2
      ≤ ∑ x ∈ Icc 1 N, ∑ k ∈ Icc 1 x, (1 / (1 - r)) * (lam x / s x) * (s k * D k ^ 2) :=
        sum_le_sum hstep2
    _ = ∑ k ∈ Icc 1 N, ∑ x ∈ Icc k N, (1 / (1 - r)) * (lam x / s x) * (s k * D k ^ 2) := hswap
    _ ≤ ∑ k ∈ Icc 1 N, (1 / (1 - r) ^ 2) * (T k * D k ^ 2) := sum_le_sum hstep4
    _ ≤ ∑ k ∈ Icc 1 N, (1 / (1 - r) ^ 2) * (B * lam k * D k ^ 2) := by
        refine sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
        have : T k * D k ^ 2 ≤ B * lam k * D k ^ 2 :=
          mul_le_mul_of_nonneg_right (hTB k hk1) (sq_nonneg _)
        gcongr
    _ = B / (1 - r) ^ 2 * ∑ k ∈ Icc 1 N, lam k * D k ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        ring

end Hardy

end GFNBounds.Doubling
