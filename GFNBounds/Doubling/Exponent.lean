import GFNBounds.Doubling.R0Bound

/-!
# The decay exponent is a Cramér root

**`prop:doubling_exponent`** — `app_doubling.tex:693–709`.

> Let `s = 1` and let `c > 0` — inside the standing range or not — so that `ε(j) = c/(j+1)`, and
> let `(λ_j)_{j≥1}` be a positive sequence satisfying `eq:doubling_cut` for every `m > d`. If
> `λ_j = A j^{−p}(1+o(1))` as `j → ∞` for some `A > 0` and some `p ≠ 0`, then `p` satisfies the
> Cramér equation `c(2^p − 1) = p`.

## The route

The paper compares `Σ_{j∈W(m)} j^{−p−1}` with `∫_{m/2}^m u^{−p−1}du` "up to a relative `O(1/m)`".
Here that is `sum_Ico_rpow_sub_integral_le`, Mathlib's monotone sum/integral comparison read for
`x ↦ x^q` at **any** real `q ≠ −1` — so `p < 0` is covered, which the statement requires and which
the standing range does not. The limit `m^p Σ_{W(m)} j^{−p}/(j+1) → (2^p−1)/p` is then a squeeze
through `⌈m/2⌉/m → ½`, and the "uniformly for `⌈m/2⌉ ≤ j ≤ m−1`" of the paper is the sandwich
`(A−t)V(m) ≤ Σ u_j w_j ≤ (A+t)V(m)` at every `t > 0`, which holds as soon as the window lies past
the index where `|u_j − A| ≤ t`.

## SCOPE (disclosed)

* `λ_j = A j^{−p}(1+o(1))` is carried as `Tendsto (fun j => λ_j j^p) atTop (𝓝 A)`, its exact
  meaning.
* `c` is any positive real; the cut balance is carried with `ε(j) = c/(j+1)` written out, so
  nothing ties it to a `Setting` (whose `ε_max < 1` would exclude `c ≥ 2`).
* Positivity of `(λ_j)` is **not** used: ⚠ weakened. The paper's proof never uses it either.

## Hypothesis checklist against `prop:doubling_exponent`

| paper hypothesis | here |
|---|---|
| `s = 1`, `c > 0` | ✓ carried (`hc`, and the shape of `ε` in `hcut`) |
| `eq:doubling_cut` at every `m > d` | ✓ carried (`hcut`) |
| `(λ_j)` positive | ⚠ weakened — not needed |
| `A > 0`, `p ≠ 0` | ✓ carried |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

/-! ### The comparison of a window sum with its integral, for any real exponent -/

/-- `Σ_{j=a}^{b−1} j^q` against `∫_a^b x^q dx`, within `|a^q − b^q|`, for every real `q`. -/
theorem sum_Ico_rpow_sub_integral_le {q : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∑ j ∈ Finset.Ico a b, (j : ℝ) ^ q) - ∫ x in (a : ℝ)..(b : ℝ), x ^ q|
      ≤ |(a : ℝ) ^ q - (b : ℝ) ^ q| := by
  set n := b - a with hn
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbn : (b : ℝ) = (a : ℝ) + (n : ℝ) := by
    rw [hn, Nat.cast_sub hab]; ring
  have hsum : ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ q
      = ∑ i ∈ Finset.range n, ((a : ℝ) + (i : ℝ)) ^ q := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
  have hshift : ∑ i ∈ Finset.range n, ((a : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ q
      = ∑ i ∈ Finset.range n, ((a : ℝ) + (i : ℝ)) ^ q - (a : ℝ) ^ q + (b : ℝ) ^ q := by
    have h1 := Finset.sum_range_succ' (fun i : ℕ => ((a : ℝ) + (i : ℝ)) ^ q) n
    have h2 := Finset.sum_range_succ (fun i : ℕ => ((a : ℝ) + (i : ℝ)) ^ q) n
    simp only [Nat.cast_zero, add_zero] at h1 h2
    have h3 : ∑ i ∈ Finset.range n, ((a : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ q
        = ∑ i ∈ Finset.range n, ((a : ℝ) + ((i : ℝ) + 1)) ^ q := by
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
    rw [h3, hbn]
    linarith [h1, h2]
  have hzero : (0 : ℝ) ∉ Set.Icc (a : ℝ) ((a : ℝ) + (n : ℝ)) := by
    intro h; linarith [h.1]
  rcases le_or_gt q 0 with hq | hq
  · -- antitone
    have hanti : AntitoneOn (fun x : ℝ => x ^ q) (Set.Icc (a : ℝ) ((a : ℝ) + (n : ℝ))) := by
      intro x hx y hy hxy
      exact rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy hq
    have h1 := hanti.integral_le_sum
    have h2 := hanti.sum_le_integral
    rw [hshift] at h2
    rw [hsum, ← hbn] at *
    rw [abs_le]
    have hfa : (b : ℝ) ^ q ≤ (a : ℝ) ^ q :=
      rpow_le_rpow_of_nonpos hapos (by exact_mod_cast hab) hq
    rw [abs_of_nonneg (by linarith)]
    constructor <;> linarith
  · -- monotone
    have hmono : MonotoneOn (fun x : ℝ => x ^ q) (Set.Icc (a : ℝ) ((a : ℝ) + (n : ℝ))) := by
      intro x hx y hy hxy
      exact rpow_le_rpow (by linarith [hx.1]) hxy hq.le
    have h1 := hmono.sum_le_integral
    have h2 := hmono.integral_le_sum
    rw [hshift] at h2
    rw [hsum, ← hbn] at *
    rw [abs_le]
    have hfa : (a : ℝ) ^ q ≤ (b : ℝ) ^ q :=
      rpow_le_rpow hapos.le (by exact_mod_cast hab) hq.le
    rw [abs_of_nonpos (by linarith)]
    constructor <;> linarith

/-- The integral itself, at `q = −p−1`, `p ≠ 0`. -/
theorem integral_rpow_window {p : ℝ} (hp : p ≠ 0) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ x in (a : ℝ)..(b : ℝ), x ^ (-p - 1) = ((a : ℝ) ^ (-p) - (b : ℝ) ^ (-p)) / p := by
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hne : (-p - 1 : ℝ) ≠ -1 := by intro h; apply hp; linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc (a : ℝ) (b : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hab)]
    intro h; linarith [h.1]
  rw [integral_rpow (Or.inr ⟨hne, hzero⟩)]
  have e : (-p - 1 + 1 : ℝ) = -p := by ring
  rw [e]
  field_simp
  ring

/-! ### The limit of the rescaled window sum -/

section Limit

variable {p : ℝ}

/-- The foot of the window, `⌈m/2⌉`, is at least `m/2`, hence tends to `+∞`. -/
theorem tendsto_foot_atTop :
    Tendsto (fun m : ℕ => (((m + 1) / 2 : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun m => Decay.foot_le m) ?_
  exact (tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)

/-- `⌈m/2⌉/m → ½`. -/
theorem tendsto_foot_ratio :
    Tendsto (fun m : ℕ => (((m + 1) / 2 : ℕ) : ℝ) / (m : ℝ)) atTop (𝓝 (1 / 2)) := by
  have hup : Tendsto (fun m : ℕ => (1 : ℝ) / 2 + 1 / 2 * (1 / (m : ℝ))) atTop (𝓝 (1 / 2)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_mul (1 / 2 : ℝ)
    simpa using tendsto_const_nhds.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    rw [le_div_iff₀ hmpos]
    have := Decay.foot_le m
    linarith
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    rw [div_le_iff₀ hmpos]
    have := Decay.le_foot m
    field_simp
    linarith

/-- `m^p · ⌈m/2⌉^{−p} → 2^p`. -/
theorem tendsto_mpow_foot (p : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ p * (((m + 1) / 2 : ℕ) : ℝ) ^ (-p)) atTop (𝓝 ((2 : ℝ) ^ p)) := by
  have h := (tendsto_foot_ratio).rpow_const (p := -p) (Or.inl (by norm_num))
  have e : ((1 : ℝ) / 2) ^ (-p) = (2 : ℝ) ^ p := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hapos : (0 : ℝ) < (((m + 1) / 2 : ℕ) : ℝ) := by
    have : 1 ≤ (m + 1) / 2 := Decay.one_le_foot hm
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  rw [Real.div_rpow hapos.le hmpos.le, Real.rpow_neg hmpos.le, div_eq_mul_inv, inv_inv]
  ring

/-- **The rescaled window sum of the pure power.** `m^p Σ_{j∈W(m)} j^{−p−1} → (2^p − 1)/p`. -/
theorem tendsto_windowPower (hp : p ≠ 0) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ p * ∑ j ∈ window m, (j : ℝ) ^ (-p - 1)) atTop
      (𝓝 (((2 : ℝ) ^ p - 1) / p)) := by
  -- main term and error term
  set I : ℕ → ℝ := fun m =>
    (m : ℝ) ^ p * (((((m + 1) / 2 : ℕ) : ℝ) ^ (-p) - (m : ℝ) ^ (-p)) / p) with hI
  set E : ℕ → ℝ := fun m =>
    (m : ℝ) ^ p * ∑ j ∈ window m, (j : ℝ) ^ (-p - 1) - I m with hE
  have hIlim : Tendsto I atTop (𝓝 (((2 : ℝ) ^ p - 1) / p)) := by
    have h1 := tendsto_mpow_foot p
    have h2 : Tendsto (fun m : ℕ => (m : ℝ) ^ p * (m : ℝ) ^ (-p)) atTop (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with m hm
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      rw [← Real.rpow_add hmpos]; simp
    have := (h1.sub h2).div_const p
    refine this.congr fun m => ?_
    rw [hI]; ring
  have hElim : Tendsto E atTop (𝓝 0) := by
    -- `|E m| ≤ m^p (a^{-p-1} + m^{-p-1}) = (m^p a^{-p}) / a + 1/m`
    have hbound : Tendsto (fun m : ℕ =>
        (m : ℝ) ^ p * (((m + 1) / 2 : ℕ) : ℝ) ^ (-p) * (1 / (((m + 1) / 2 : ℕ) : ℝ))
          + 1 / (m : ℝ)) atTop (𝓝 0) := by
      have h1 := (tendsto_mpow_foot p).mul
        (tendsto_foot_atTop.inv_tendsto_atTop)
      have h2 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
      have := h1.add h2
      simp only [mul_zero, add_zero] at this
      refine this.congr fun m => ?_
      simp [one_div]
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmp : (0 : ℝ) < (m : ℝ) ^ p := rpow_pos_of_pos hmpos _
    set a : ℕ := (m + 1) / 2 with ha
    have ha1 : 1 ≤ a := Decay.one_le_foot hm
    have ham : a ≤ m := Decay.foot_le_self hm
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha1
    have hcmp := sum_Ico_rpow_sub_integral_le (q := -p - 1) ha1 ham
    rw [integral_rpow_window hp ha1 ham] at hcmp
    have hwin : window m = Finset.Ico a m := rfl
    rw [Real.norm_eq_abs]
    have hEeq : E m = (m : ℝ) ^ p *
        ((∑ j ∈ Finset.Ico a m, (j : ℝ) ^ (-p - 1)) - ((a : ℝ) ^ (-p) - (m : ℝ) ^ (-p)) / p) := by
      simp only [hE, hI]
      rw [hwin]; ring
    rw [hEeq, abs_mul, abs_of_pos hmp]
    have hsplit : (a : ℝ) ^ (-p - 1) = (a : ℝ) ^ (-p) * (1 / (a : ℝ)) := by
      rw [rpow_sub_one_eq hapos, div_eq_mul_one_div]
    have hsplit2 : (m : ℝ) ^ (-p - 1) = (m : ℝ) ^ (-p) * (1 / (m : ℝ)) := by
      rw [rpow_sub_one_eq hmpos, div_eq_mul_one_div]
    have hmm : (m : ℝ) ^ p * (m : ℝ) ^ (-p) = 1 := by rw [← Real.rpow_add hmpos]; simp
    have habs : |(a : ℝ) ^ (-p - 1) - (m : ℝ) ^ (-p - 1)|
        ≤ (a : ℝ) ^ (-p - 1) + (m : ℝ) ^ (-p - 1) := by
      have h1 : (0 : ℝ) ≤ (a : ℝ) ^ (-p - 1) := rpow_nonneg hapos.le _
      have h2 : (0 : ℝ) ≤ (m : ℝ) ^ (-p - 1) := rpow_nonneg hmpos.le _
      rw [abs_le]; constructor <;> linarith
    calc (m : ℝ) ^ p *
          |(∑ j ∈ Finset.Ico a m, (j : ℝ) ^ (-p - 1)) - ((a : ℝ) ^ (-p) - (m : ℝ) ^ (-p)) / p|
        ≤ (m : ℝ) ^ p * ((a : ℝ) ^ (-p - 1) + (m : ℝ) ^ (-p - 1)) :=
          mul_le_mul_of_nonneg_left (le_trans hcmp habs) hmp.le
      _ = (m : ℝ) ^ p * (a : ℝ) ^ (-p) * (1 / (a : ℝ))
            + ((m : ℝ) ^ p * (m : ℝ) ^ (-p)) * (1 / (m : ℝ)) := by
          rw [hsplit, hsplit2]; ring
      _ = (m : ℝ) ^ p * (a : ℝ) ^ (-p) * (1 / (a : ℝ)) + 1 / (m : ℝ) := by
          rw [hmm, one_mul]
  have := hIlim.add hElim
  rw [add_zero] at this
  refine this.congr fun m => ?_
  rw [hE]; ring

/-- The window weights `w_m(j) = m^p j^{−p}/(j+1)` are positive on the window. -/
theorem windowWeight_pos {m j : ℕ} (hm : 1 ≤ m) (hj : j ∈ window m) :
    0 < (m : ℝ) ^ p * (j : ℝ) ^ (-p) / ((j : ℝ) + 1) := by
  have hj1 : 1 ≤ j := Decay.one_le_of_mem_window' hm hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have := rpow_pos_of_pos hmpos p
  have := rpow_pos_of_pos hjpos (-p)
  positivity

/-- **`V(m) → (2^p−1)/p`.** The rescaled window sum with the true weights `1/(j+1)` in place of
`1/j`: the two differ by a relative `1/(⌈m/2⌉+1)`. -/
theorem tendsto_windowV (hp : p ≠ 0) :
    Tendsto (fun m : ℕ => ∑ j ∈ window m, (m : ℝ) ^ p * (j : ℝ) ^ (-p) / ((j : ℝ) + 1)) atTop
      (𝓝 (((2 : ℝ) ^ p - 1) / p)) := by
  set L : ℝ := ((2 : ℝ) ^ p - 1) / p with hL
  have hS := tendsto_windowPower hp
  -- lower bound `m^p S (1 − 1/(a+1))`, upper bound `m^p S`
  have hlow : Tendsto (fun m : ℕ =>
      ((m : ℝ) ^ p * ∑ j ∈ window m, (j : ℝ) ^ (-p - 1))
        * (1 - 1 / ((((m + 1) / 2 : ℕ) : ℝ) + 1))) atTop (𝓝 L) := by
    have h1 : Tendsto (fun m : ℕ => (1 : ℝ) - 1 / ((((m + 1) / 2 : ℕ) : ℝ) + 1)) atTop (𝓝 1) := by
      have := (tendsto_foot_atTop.atTop_add tendsto_const_nhds (C := (1 : ℝ))).inv_tendsto_atTop
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub this
      simpa [one_div] using h
    have := hS.mul h1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hS ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmp : (0 : ℝ) < (m : ℝ) ^ p := rpow_pos_of_pos hmpos _
    set a : ℕ := (m + 1) / 2 with ha
    have ha1 : 1 ≤ a := Decay.one_le_foot hm
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha1
    -- termwise: `w_j ≥ m^p j^{-p-1} (1 − 1/(a+1))`
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := Decay.one_le_of_mem_window' hm hj
    have hja : a ≤ j := (Finset.mem_Ico.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hjar : (a : ℝ) ≤ (j : ℝ) := by exact_mod_cast hja
    have hjn : (0 : ℝ) ≤ (j : ℝ) ^ (-p) := rpow_nonneg hjpos.le _
    rw [rpow_sub_one_eq hjpos]
    -- `j^{-p}/j · (1 − 1/(a+1)) ≤ j^{-p}/(j+1)`  ⟸  `(1 − 1/(a+1))/j ≤ 1/(j+1)`  ⟸  `a ≤ j`
    have hkey : (1 - 1 / ((a : ℝ) + 1)) / (j : ℝ) ≤ 1 / ((j : ℝ) + 1) := by
      rw [div_le_div_iff₀ hjpos (by positivity)]
      have : 1 - 1 / ((a : ℝ) + 1) = (a : ℝ) / ((a : ℝ) + 1) := by field_simp; ring
      rw [this, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hjar]
    calc (m : ℝ) ^ p * ((j : ℝ) ^ (-p) / (j : ℝ) * (1 - 1 / ((a : ℝ) + 1)))
        = (m : ℝ) ^ p * (j : ℝ) ^ (-p) * ((1 - 1 / ((a : ℝ) + 1)) / (j : ℝ)) := by ring
      _ ≤ (m : ℝ) ^ p * (j : ℝ) ^ (-p) * (1 / ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (m : ℝ) ^ p * (j : ℝ) ^ (-p) / ((j : ℝ) + 1) := by ring
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmp : (0 : ℝ) < (m : ℝ) ^ p := rpow_pos_of_pos hmpos _
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := Decay.one_le_of_mem_window' hm hj
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hjn : (0 : ℝ) ≤ (j : ℝ) ^ (-p) := rpow_nonneg hjpos.le _
    rw [rpow_sub_one_eq hjpos]
    have : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / (j : ℝ) :=
      one_div_le_one_div_of_le hjpos (by linarith)
    calc (m : ℝ) ^ p * (j : ℝ) ^ (-p) / ((j : ℝ) + 1)
        = (m : ℝ) ^ p * (j : ℝ) ^ (-p) * (1 / ((j : ℝ) + 1)) := by ring
      _ ≤ (m : ℝ) ^ p * (j : ℝ) ^ (-p) * (1 / (j : ℝ)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (m : ℝ) ^ p * ((j : ℝ) ^ (-p) / (j : ℝ)) := by ring

end Limit

/-! ### `prop:doubling_exponent` -/

/-- **`prop:doubling_exponent`.** If a sequence satisfying `eq:doubling_cut` at every `m > d` has
`λ_j j^p → A > 0`, then `p` is a root of the Cramér equation. -/
theorem exponent_is_cramer_root {c : ℝ} (hc : 0 < c) {d : ℕ} {lam : ℕ → ℝ}
    (hcut : ∀ m : ℕ, d < m →
      lam m * (1 - c / ((m : ℝ) + 1)) = ∑ j ∈ window m, lam j * (c / ((j : ℝ) + 1)))
    {A p : ℝ} (hA : 0 < A) (hp : p ≠ 0)
    (hlim : Tendsto (fun j : ℕ => lam j * (j : ℝ) ^ p) atTop (𝓝 A)) :
    psi c p = 0 := by
  set L : ℝ := ((2 : ℝ) ^ p - 1) / p with hL
  set u : ℕ → ℝ := fun j => lam j * (j : ℝ) ^ p with hu
  set w : ℕ → ℕ → ℝ := fun m j => (m : ℝ) ^ p * (j : ℝ) ^ (-p) / ((j : ℝ) + 1) with hw
  set V : ℕ → ℝ := fun m => ∑ j ∈ window m, w m j with hV
  have hVlim : Tendsto V atTop (𝓝 L) := tendsto_windowV hp
  -- the cut balance, rescaled: `u_m (1 − ε(m)) = c Σ u_j w_m(j)`
  have hresc : ∀ m : ℕ, d < m → 1 ≤ m →
      u m * (1 - c / ((m : ℝ) + 1)) = c * ∑ j ∈ window m, u j * w m j := by
    intro m hdm hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have h := congrArg (fun x => x * (m : ℝ) ^ p) (hcut m hdm)
    rw [Finset.sum_mul] at h
    rw [Finset.mul_sum]
    have hterm : ∀ j ∈ window m,
        lam j * (c / ((j : ℝ) + 1)) * (m : ℝ) ^ p = c * (u j * w m j) := by
      intro j hj
      have hj1 : 1 ≤ j := Decay.one_le_of_mem_window' hm hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      have hjj : (j : ℝ) ^ p * (j : ℝ) ^ (-p) = 1 := by rw [← Real.rpow_add hjpos]; simp
      rw [hu, hw]
      simp only
      calc lam j * (c / ((j : ℝ) + 1)) * (m : ℝ) ^ p
          = c * (lam j * ((j : ℝ) ^ p * (j : ℝ) ^ (-p)) * ((m : ℝ) ^ p / ((j : ℝ) + 1))) := by
            rw [hjj]; ring
        _ = c * (lam j * (j : ℝ) ^ p * ((m : ℝ) ^ p * (j : ℝ) ^ (-p) / ((j : ℝ) + 1))) := by
            ring
    rw [Finset.sum_congr rfl hterm] at h
    rw [hu]; simp only
    rw [show lam m * (m : ℝ) ^ p * (1 - c / ((m : ℝ) + 1))
        = lam m * (1 - c / ((m : ℝ) + 1)) * (m : ℝ) ^ p by ring, h]
  -- the left side tends to `A`
  have hLHS : Tendsto (fun m : ℕ => u m * (1 - c / ((m : ℝ) + 1))) atTop (𝓝 A) := by
    have h1 : Tendsto (fun m : ℕ => (1 : ℝ) - c / ((m : ℝ) + 1)) atTop (𝓝 1) := by
      have h := tendsto_const_div_atTop_nhds_zero_nat c
      have h' : Tendsto (fun m : ℕ => c / ((m : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1:ℝ)))
        exact Tendsto.div_atTop tendsto_const_nhds this
      simpa using tendsto_const_nhds.sub h'
    have := hlim.mul h1
    simpa using this
  -- the sandwich at every `t > 0`
  have hsand : ∀ t : ℝ, 0 < t →
      c * (A - t) * L ≤ A ∧ A ≤ c * (A + t) * L := by
    intro t ht
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) t ht
    have hev : ∀ᶠ m : ℕ in atTop,
        c * (A - t) * V m ≤ u m * (1 - c / ((m : ℝ) + 1)) ∧
          u m * (1 - c / ((m : ℝ) + 1)) ≤ c * (A + t) * V m := by
      filter_upwards [eventually_ge_atTop (2 * N + 1), eventually_ge_atTop (d + 1)] with m hmN hmd
      have hm1 : 1 ≤ m := by omega
      have hdm : d < m := by omega
      rw [hresc m hdm hm1, hV]
      simp only
      have hjbig : ∀ j ∈ window m, N ≤ j := by
        intro j hj
        have := (Finset.mem_Ico.mp hj).1; omega
      have hs1 : (A - t) * ∑ j ∈ window m, w m j ≤ ∑ j ∈ window m, u j * w m j := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        have hd := hN j (hjbig j hj)
        rw [Real.dist_eq, abs_lt] at hd
        have hwpos : 0 < w m j := windowWeight_pos hm1 hj
        have := mul_pos (show (0 : ℝ) < u j - (A - t) by linarith [hd.1]) hwpos
        linarith
      have hs2 : ∑ j ∈ window m, u j * w m j ≤ (A + t) * ∑ j ∈ window m, w m j := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        have hd := hN j (hjbig j hj)
        rw [Real.dist_eq, abs_lt] at hd
        have hwpos : 0 < w m j := windowWeight_pos hm1 hj
        have := mul_pos (show (0 : ℝ) < (A + t) - u j by linarith [hd.2]) hwpos
        linarith
      constructor
      · calc c * (A - t) * ∑ j ∈ window m, w m j
            = c * ((A - t) * ∑ j ∈ window m, w m j) := by ring
          _ ≤ c * ∑ j ∈ window m, u j * w m j := mul_le_mul_of_nonneg_left hs1 hc.le
      · calc c * ∑ j ∈ window m, u j * w m j
            ≤ c * ((A + t) * ∑ j ∈ window m, w m j) := mul_le_mul_of_nonneg_left hs2 hc.le
          _ = c * (A + t) * ∑ j ∈ window m, w m j := by ring
    have hlo : Tendsto (fun m : ℕ => c * (A - t) * V m) atTop (𝓝 (c * (A - t) * L)) :=
      hVlim.const_mul _
    have hhi : Tendsto (fun m : ℕ => c * (A + t) * V m) atTop (𝓝 (c * (A + t) * L)) :=
      hVlim.const_mul _
    exact ⟨le_of_tendsto_of_tendsto hlo hLHS (hev.mono fun m h => h.1),
      le_of_tendsto_of_tendsto hLHS hhi (hev.mono fun m h => h.2)⟩
  -- `cL > 0`, then `A = cAL`
  have hcL : 0 < c * L := by
    have := (hsand 1 one_pos).2
    by_contra hcon
    have hcon' : c * L ≤ 0 := not_lt.mp hcon
    nlinarith [this, hA, hcon']
  have hcLne : c * L ≠ 0 := hcL.ne'
  have hkey : ∀ ε : ℝ, c * (ε / (c * L)) * L = ε := by
    intro ε
    have h : c * (ε / (c * L)) * L = ε * (c * L) / (c * L) := by ring
    rw [h, mul_div_assoc, div_self hcLne, mul_one]
  have hup : A ≤ c * A * L := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := (hsand (ε / (c * L)) (by positivity)).2
    have e : c * (A + ε / (c * L)) * L = c * A * L + ε := by
      calc c * (A + ε / (c * L)) * L = c * A * L + c * (ε / (c * L)) * L := by ring
        _ = c * A * L + ε := by rw [hkey]
    linarith [this, e]
  have hlo : c * A * L ≤ A := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := (hsand (ε / (c * L)) (by positivity)).1
    have e : c * (A - ε / (c * L)) * L = c * A * L - ε := by
      calc c * (A - ε / (c * L)) * L = c * A * L - c * (ε / (c * L)) * L := by ring
        _ = c * A * L - ε := by rw [hkey]
    linarith [this, e]
  have heq : c * L = 1 := by
    have h : A * (c * L) = A * 1 := by nlinarith [hup, hlo]
    exact mul_left_cancel₀ hA.ne' h
  -- unwind `L`
  rw [hL] at heq
  rw [psi, sub_eq_zero]
  field_simp at heq
  linarith [heq]

end GFNBounds.Doubling
