import GFNBounds.Doubling.GeomOperator
import GFNBounds.Doubling.PhaseExists

/-!
# The geometric row of the policy table: `ε(j) = a ρ^j` has a finite diffusion constant

For a doubling probability whose successive ratios eventually fall below a constant `< 1`,

  `ε(i+1) ≤ θ (1 − ε(i+1)) ε(i)`  for `i ≥ i₀`, some `θ < 1` and `i₀ > d`,

the tail of the invariant probability is comparable to the mass at the cut, `L(k) ≤ B λ_k`, and
`GeomOperator.exists_diffusionOp_of_tail` applies: `B̂ < +∞`. The geometric family
`ε(j) = a ρ^j` satisfies the ratio condition, and carries an invariant probability by the
threshold criterion `PhaseExists.exists_stat_of_threshold`.

The tail bound, with `a_i := λ_i ε(i)` and `c(m) := ⌈m/2⌉`:

1. `λ_{i+1}(1 − ε(i+1)) ≤ λ_i` past `d` (the cut balance at `i+1` and at `i`), hence
   `a_{i+1} ≤ θ a_i` past `i₀`;
2. the cut balance at `m` reads `λ_m(1 − ε(m)) = Σ_{j ∈ [c(m), m)} a_j`, so
   `a_{c(m)} ≤ λ_m` and `(1 − ε_max) λ_m ≤ a_{c(m)}/(1 − θ)`;
3. `A(m) := a_{c(m)}` has `A(m+1) ≤ A(m)` and `A(m+2) ≤ θ A(m)`, so `Σ_{t ≥ 0} A(r+t) ≤ 2A(r)/(1 − θ)`,
   and `L(r) ≤ 2 λ_r / ((1 − θ)²(1 − ε_max))` for `r ≥ max(2 i₀, d + 1)`;
4. below that threshold, `L(k) ≤ 1` and `λ_k` is bounded below on a finite set.

This is the row the polynomial family fails: there `ε(i+1)/ε(i) → 1`, and
`theo:doubling_unbounded` gives `B̂ = +∞`.

## SCOPE (disclosed)

Loop closure only. Not a statement of the paper as of 2026-09-19: the geometric row of the
policy table requested by the author that day, measured by `exp22` (`B̂_K` flat in `K`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology Finset
open scoped InnerProductSpace

variable {S : Setting}

namespace Stat

variable (L : Stat S none)

/-- `a_i = λ_i ε(i)`, the mass doubling out of `i`. -/
noncomputable def dbl (i : ℕ) : ℝ := L.lam (.lad i) * S.eps i

theorem dbl_nonneg {i : ℕ} (hi : 1 ≤ i) : 0 ≤ L.dbl i :=
  mul_nonneg (L.nonneg _) (S.eps_pos hi).le

/-- **Step 1.** `λ_{i+1}(1 − ε(i+1)) ≤ λ_i` past `d`. -/
theorem decr_le {i : ℕ} (hi : S.d < i) :
    L.lam (.lad (i + 1)) * (1 - S.eps (i + 1)) ≤ L.lam (.lad i) := by
  have h1 := cut_balance L (m := i + 1) (by omega) trivial
  have h0 := cut_balance L (m := i) hi trivial
  have hd := S.d_pos
  have hsub : window (i + 1) ⊆ insert i (window i) := by
    intro j hj
    rw [mem_window] at hj
    rw [Finset.mem_insert, mem_window]
    omega
  have hnot : i ∉ window i := by rw [mem_window]; omega
  have hnn : ∀ j ∈ insert i (window i), 0 ≤ L.lam (.lad j) * S.eps j := by
    intro j hj
    rw [Finset.mem_insert, mem_window] at hj
    exact mul_nonneg (L.nonneg _) (S.eps_pos (by omega)).le
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hnn j hj
  rw [Finset.sum_insert hnot] at hle
  rw [h1]
  have : L.lam (.lad i) * S.eps i + L.lam (.lad i) * (1 - S.eps i) = L.lam (.lad i) := by ring
  linarith

variable {θ : ℝ} {i₀ : ℕ}

/-- `a_{i+1} ≤ θ a_i` past `i₀`. -/
theorem dbl_step (hθ0 : 0 ≤ θ) (hi0 : S.d < i₀)
    (hrat : ∀ i, i₀ ≤ i → S.eps (i + 1) ≤ θ * (1 - S.eps (i + 1)) * S.eps i) {i : ℕ}
    (hi : i₀ ≤ i) : L.dbl (i + 1) ≤ θ * L.dbl i := by
  unfold dbl
  have hd := decr_le L (i := i) (by omega)
  have hl := L.nonneg (.lad (i + 1))
  have he : 0 ≤ S.eps i := (S.eps_pos (by have := S.d_pos; omega)).le
  calc L.lam (.lad (i + 1)) * S.eps (i + 1)
      ≤ L.lam (.lad (i + 1)) * (θ * (1 - S.eps (i + 1)) * S.eps i) :=
        mul_le_mul_of_nonneg_left (hrat i hi) hl
    _ = θ * S.eps i * (L.lam (.lad (i + 1)) * (1 - S.eps (i + 1))) := by ring
    _ ≤ θ * S.eps i * L.lam (.lad i) := mul_le_mul_of_nonneg_left hd (mul_nonneg hθ0 he)
    _ = θ * (L.lam (.lad i) * S.eps i) := by ring

theorem dbl_geom (hθ0 : 0 ≤ θ) (hi0 : S.d < i₀)
    (hrat : ∀ i, i₀ ≤ i → S.eps (i + 1) ≤ θ * (1 - S.eps (i + 1)) * S.eps i) {i : ℕ}
    (hi : i₀ ≤ i) : ∀ t : ℕ, L.dbl (i + t) ≤ θ ^ t * L.dbl i := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      calc L.dbl (i + (t + 1)) = L.dbl (i + t + 1) := by rw [Nat.add_assoc]
        _ ≤ θ * L.dbl (i + t) := L.dbl_step hθ0 hi0 hrat (by omega)
        _ ≤ θ * (θ ^ t * L.dbl i) := mul_le_mul_of_nonneg_left ih hθ0
        _ = θ ^ (t + 1) * L.dbl i := by ring

/-- **Step 2, lower half.** `a_{c(m)} ≤ λ_m`. -/
theorem dbl_half_le {m : ℕ} (hm : S.d < m) (h2 : 2 ≤ m) : L.dbl ((m + 1) / 2) ≤ L.lam (.lad m) := by
  have h := cut_balance L hm trivial
  have hmem : (m + 1) / 2 ∈ window m := by rw [mem_window]; omega
  have hnn : ∀ j ∈ window m, 0 ≤ L.lam (.lad j) * S.eps j := by
    intro j hj; rw [mem_window] at hj
    exact mul_nonneg (L.nonneg _) (S.eps_pos (by omega)).le
  have h1 : L.dbl ((m + 1) / 2) ≤ ∑ j ∈ window m, L.lam (.lad j) * S.eps j :=
    Finset.single_le_sum hnn hmem
  have hl := L.nonneg (.lad m)
  have he : 0 ≤ S.eps m := (S.eps_pos (by omega)).le
  nlinarith

/-- **Step 2, upper half.** `(1 − ε_max) λ_m ≤ a_{c(m)}/(1 − θ)`. -/
theorem lam_le_dbl_half (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hi0 : S.d < i₀)
    (hrat : ∀ i, i₀ ≤ i → S.eps (i + 1) ≤ θ * (1 - S.eps (i + 1)) * S.eps i) {m : ℕ}
    (hm : S.d < m) (hc : i₀ ≤ (m + 1) / 2) :
    (1 - S.epsMax) * L.lam (.lad m) ≤ L.dbl ((m + 1) / 2) / (1 - θ) := by
  have h := cut_balance L hm trivial
  have hwin : ∑ j ∈ window m, L.lam (.lad j) * S.eps j
      ≤ L.dbl ((m + 1) / 2) / (1 - θ) := by
    rw [window, sum_Ico_eq_sum_range]
    calc ∑ t ∈ range (m - (m + 1) / 2), L.lam (.lad ((m + 1) / 2 + t)) * S.eps ((m + 1) / 2 + t)
        = ∑ t ∈ range (m - (m + 1) / 2), L.dbl ((m + 1) / 2 + t) := rfl
      _ ≤ ∑ t ∈ range (m - (m + 1) / 2), θ ^ t * L.dbl ((m + 1) / 2) :=
          sum_le_sum fun t _ => L.dbl_geom hθ0 hi0 hrat hc t
      _ = (∑ t ∈ range (m - (m + 1) / 2), θ ^ t) * L.dbl ((m + 1) / 2) := by rw [sum_mul]
      _ ≤ (1 / (1 - θ)) * L.dbl ((m + 1) / 2) :=
          mul_le_mul_of_nonneg_right (Hardy.geom_le hθ0 hθ1 _)
            (L.dbl_nonneg (by have := S.d_pos; omega))
      _ = L.dbl ((m + 1) / 2) / (1 - θ) := by ring
  have he : S.eps m ≤ S.epsMax := S.eps_le (by omega)
  have hl := L.nonneg (.lad m)
  have : (1 - S.epsMax) * L.lam (.lad m) ≤ L.lam (.lad m) * (1 - S.eps m) := by nlinarith
  linarith

/-- **Step 3.** Past `R₀ = 2 i₀`, `L(r) ≤ 2 λ_r / ((1 − θ)²(1 − ε_max))`. -/
theorem tail_le_far (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hi0 : S.d < i₀)
    (hrat : ∀ i, i₀ ≤ i → S.eps (i + 1) ≤ θ * (1 - S.eps (i + 1)) * S.eps i) {r : ℕ}
    (hr : 2 * i₀ ≤ r) :
    L.tailMass r ≤ 2 / ((1 - θ) ^ 2 * (1 - S.epsMax)) * L.lam (.lad r) := by
  have hd1 := S.d_pos
  have h1e : 0 < 1 - S.epsMax := by linarith [S.epsMax_lt_one]
  have h1θ : 0 < 1 - θ := by linarith
  set f : ℕ → ℝ := fun t => L.dbl ((t + r + 1) / 2) with hfdef
  have hf0 : ∀ t, 0 ≤ f t := fun t => L.dbl_nonneg (by omega)
  have hg : HasSum (fun t : ℕ => L.lam (.lad (t + r))) (L.tailMass r) := L.hasSum_tailShift r
  have hfg : ∀ t, f t ≤ L.lam (.lad (t + r)) := fun t =>
    L.dbl_half_le (m := t + r) (by omega) (by omega)
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hfg hg.summable
  -- `A(m+2) ≤ θ A(m)` and `A(m+1) ≤ A(m)`
  have hf2 : ∀ t, f (t + 2) ≤ θ * f t := by
    intro t
    have hc : (t + 2 + r + 1) / 2 = (t + r + 1) / 2 + 1 := by omega
    show L.dbl ((t + 2 + r + 1) / 2) ≤ θ * L.dbl ((t + r + 1) / 2)
    rw [hc]
    exact L.dbl_step hθ0 hi0 hrat (by omega)
  have hf1 : f 1 ≤ f 0 := by
    show L.dbl ((1 + r + 1) / 2) ≤ L.dbl ((0 + r + 1) / 2)
    rcases Nat.even_or_odd r with ⟨u, hu⟩ | ⟨u, hu⟩
    · have e1 : (1 + r + 1) / 2 = (0 + r + 1) / 2 + 1 := by omega
      rw [e1]
      have := L.dbl_step hθ0 hi0 hrat (i := (0 + r + 1) / 2) (by omega)
      have hnn := L.dbl_nonneg (i := (0 + r + 1) / 2) (by omega)
      nlinarith
    · have e1 : (1 + r + 1) / 2 = (0 + r + 1) / 2 := by omega
      rw [e1]
  -- `Σ A(r+t) ≤ 2 A(r)/(1 − θ)`
  have hsplit := hfs.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
  have hshift : ∑' t, f (t + 2) ≤ θ * ∑' t, f t := by
    rw [← tsum_mul_left]
    exact ((summable_nat_add_iff 2).mpr hfs).tsum_le_tsum hf2 (hfs.mul_left θ)
  have hS : ∑' t, f t ≤ 2 * f 0 / (1 - θ) := by
    rw [le_div_iff₀ h1θ]
    nlinarith
  -- the tail against the `A`'s
  have hlam : ∀ t, L.lam (.lad (t + r)) ≤ f t / ((1 - θ) * (1 - S.epsMax)) := by
    intro t
    have h := L.lam_le_dbl_half hθ0 hθ1 hi0 hrat (m := t + r) (by omega) (by omega)
    rw [le_div_iff₀ (mul_pos h1θ h1e)]
    rw [le_div_iff₀ h1θ] at h
    nlinarith
  have hT : L.tailMass r ≤ (∑' t, f t) / ((1 - θ) * (1 - S.epsMax)) := by
    rw [← hg.tsum_eq, ← tsum_div_const]
    exact hg.summable.tsum_le_tsum hlam (hfs.div_const _)
  have hf0r : f 0 ≤ L.lam (.lad r) := by simpa using hfg 0
  calc L.tailMass r ≤ (∑' t, f t) / ((1 - θ) * (1 - S.epsMax)) := hT
    _ ≤ (2 * f 0 / (1 - θ)) / ((1 - θ) * (1 - S.epsMax)) := by gcongr
    _ = 2 / ((1 - θ) ^ 2 * (1 - S.epsMax)) * f 0 := by field_simp
    _ ≤ 2 / ((1 - θ) ^ 2 * (1 - S.epsMax)) * L.lam (.lad r) := by gcongr

/-- **Steps 3–4. The tail is comparable to the mass at the cut**, at every ladder state. -/
theorem tail_bound_of_ratio (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hi0 : S.d < i₀)
    (hrat : ∀ i, i₀ ≤ i → S.eps (i + 1) ≤ θ * (1 - S.eps (i + 1)) * S.eps i) :
    ∃ B : ℝ, ∀ k, 1 ≤ k → L.tailMass k ≤ B * L.lam (.lad k) := by
  have hne : (Finset.Icc 1 (2 * i₀)).Nonempty := ⟨1, by rw [Finset.mem_Icc]; omega⟩
  obtain ⟨k₀, hk₀, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 (2 * i₀))
    (fun k => L.lam (.lad k)) hne
  set m := L.lam (.lad k₀) with hm
  have hmpos : 0 < m := L.pos trivial
  refine ⟨max (2 / ((1 - θ) ^ 2 * (1 - S.epsMax))) (1 / m), fun k hk => ?_⟩
  have hl := L.nonneg (.lad k)
  rcases le_or_gt (2 * i₀) k with hfar | hnear
  · exact (L.tail_le_far hθ0 hθ1 hi0 hrat hfar).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)
  · have hkm : m ≤ L.lam (.lad k) := hmin k (by rw [Finset.mem_Icc]; omega)
    have h1 : L.tailMass k ≤ 1 := L.tailMass_le_one k
    have h2 : 1 ≤ 1 / m * L.lam (.lad k) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hmpos, one_mul]; exact hkm
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hl))

/-- **`B̂ < +∞` under the ratio condition.** -/
theorem exists_diffusionOp_of_ratio (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hi0 : S.d < i₀)
    (hrat : ∀ i, i₀ ≤ i → S.eps (i + 1) ≤ θ * (1 - S.eps (i + 1)) * S.eps i) :
    ∃ R : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
      (1 - L.pstarL2 (rowOnChain_none S) + L.piL2) * R = 1
      ∧ R * (1 - L.pstarL2 (rowOnChain_none S) + L.piL2) = 1
      ∧ (1 - L.pstarL2 (rowOnChain_none S)) * (R - L.piL2) = 1 - L.piL2
      ∧ (R - L.piL2) * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2
      ∧ L.piL2 * (R - L.piL2) = 0
      ∧ (R - L.piL2) * L.piL2 = 0 := by
  obtain ⟨B, hB⟩ := L.tail_bound_of_ratio hθ0 hθ1 hi0 hrat
  exact L.exists_diffusionOp_of_tail hB

end Stat

/-! ## The geometric family `ε(j) = a ρ^j` -/

section Geometric

variable {a ρ : ℝ}

/-- The geometric family satisfies the ratio condition with `θ = (1 + ρ)/2`. -/
theorem geometric_ratio (ha : 0 < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (heps : ∀ j, 1 ≤ j → S.eps j = a * ρ ^ j) :
    ∃ i₀ : ℕ, S.d < i₀ ∧
      ∀ i, i₀ ≤ i → S.eps (i + 1) ≤ (1 + ρ) / 2 * (1 - S.eps (i + 1)) * S.eps i := by
  set δ := (1 - ρ) / (1 + ρ) with hδ
  have hδpos : 0 < δ := div_pos (by linarith) (by linarith)
  have hlim : Tendsto (fun n : ℕ => a * ρ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul a
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (Iic_mem_nhds hδpos))
  refine ⟨max N (S.d + 1), by omega, fun i hi => ?_⟩
  have hsmall : a * ρ ^ (i + 1) ≤ δ := hN (i + 1) (by omega)
  rw [heps (i + 1) (by omega), heps i (by omega)]
  have hx : 0 ≤ a * ρ ^ i := mul_nonneg ha.le (pow_nonneg hρ0.le i)
  have hpow : a * ρ ^ (i + 1) = ρ * (a * ρ ^ i) := by ring
  have hkey : ρ ≤ (1 + ρ) / 2 * (1 - a * ρ ^ (i + 1)) := by
    have h1 : (1 + ρ) / 2 * (1 - δ) = ρ := by
      rw [hδ]; field_simp; ring
    have h2 : (1 + ρ) / 2 * (1 - δ) ≤ (1 + ρ) / 2 * (1 - a * ρ ^ (i + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  calc a * ρ ^ (i + 1) = ρ * (a * ρ ^ i) := hpow
    _ ≤ (1 + ρ) / 2 * (1 - a * ρ ^ (i + 1)) * (a * ρ ^ i) :=
        mul_le_mul_of_nonneg_right hkey hx

/-- **Positive recurrence of the geometric family**: the loop closure carries an invariant
probability. The drift coefficient `(m + 1) a ρ^m` tends to `0`. -/
theorem geometric_exists_stat (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (heps : ∀ j, 1 ≤ j → S.eps j = a * ρ ^ j) : Nonempty (Stat S none) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * ρ ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hρ0.le hρ1
  have h2 : Tendsto (fun n : ℕ => ρ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (a * ρ ^ n)) atTop (𝓝 0) := by
    have := (h1.add h2).const_mul a
    simp only [add_zero, mul_zero] at this
    refine this.congr fun n => ?_
    ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1 / 2)))
  refine exists_stat_of_threshold S (θ := 1 / 2) (by norm_num) (by norm_num) N fun m hm hNm => ?_
  rw [heps m hm]
  exact hN m hNm

/-- **The geometric row of the policy table.** For the doubling probability `ε(j) = a ρ^j`,
`0 < ρ < 1`, the loop-closed backward chain on the infinite doubling graph is positive recurrent,
and at its invariant probability `Id − P⋆ + Π` is invertible on `L²(λ)`, the diffusion operator
`S = (Id − P⋆ + Π)^{-1} − Π` satisfying `eq:doubling_resolvent`: `B̂ = ‖S‖ < +∞`.

Contrast `UnboundedL2.no_diffusionOp`: for the polynomial family `c/(j+1)^s` no bounded `S` has
`S(Id − P⋆) = Id − Π`. -/
theorem main_geometric (ha : 0 < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (heps : ∀ j, 1 ≤ j → S.eps j = a * ρ ^ j) :
    Nonempty (Stat S none) ∧
      ∀ L : Stat S none, ∃ R : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
        (1 - L.pstarL2 (rowOnChain_none S) + L.piL2) * R = 1
        ∧ R * (1 - L.pstarL2 (rowOnChain_none S) + L.piL2) = 1
        ∧ (1 - L.pstarL2 (rowOnChain_none S)) * (R - L.piL2) = 1 - L.piL2
        ∧ (R - L.piL2) * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2
        ∧ L.piL2 * (R - L.piL2) = 0
        ∧ (R - L.piL2) * L.piL2 = 0 := by
  refine ⟨geometric_exists_stat hρ0 hρ1 heps, fun L => ?_⟩
  obtain ⟨i₀, hi0, hrat⟩ := geometric_ratio ha hρ0 hρ1 heps
  exact L.exists_diffusionOp_of_ratio (θ := (1 + ρ) / 2) (by linarith) (by linarith) hi0 hrat

/-- **`B̂ < +∞`, in the form `no_diffusionOp` negates.** Some bounded `S` on `L²(λ)` has
`S(Id − P⋆) = Id − Π`. -/
theorem geometric_diffusionOp (ha : 0 < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (heps : ∀ j, 1 ≤ j → S.eps j = a * ρ ^ j) (L : Stat S none) :
    ∃ Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
      Sop * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2 := by
  obtain ⟨R, -, -, -, h, -, -⟩ := (main_geometric ha hρ0 hρ1 heps).2 L
  exact ⟨R - L.piL2, h⟩

end Geometric

end GFNBounds.Doubling
