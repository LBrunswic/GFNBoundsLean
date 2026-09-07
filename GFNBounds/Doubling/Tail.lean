import GFNBounds.Doubling.Descent

/-!
# The tail of the invariant measure

**`cor:doubling_tail`** — `app_doubling.tex:1230–1268`.

> Let `s = 1`, `0 < c < 1`, let `(λ_j)` be positive and satisfy `eq:doubling_cut` for every
> `m > d`, let `0 < c₁ ≤ c₂` satisfy `eq:doubling_decay` and let `L` be the tail. Then there are
> `ξ_m` with `Σ_{j≥m} j^{−p_*} = m^{1−p_*}(1+ξ_m)/(p_*−1)`, `0 ≤ ξ_m ≤ (p_*−1)/m`, and
> `c₁ m^{1−p_*}/(p_*−1) ≤ L(m) ≤ c₂ p_* m^{1−p_*}/(p_*−1)`,
> `c₁ m/(c₂(p_*−1)) ≤ L(m)/λ_m ≤ c₂ p_* m/(c₁(p_*−1))`;
> in particular `L(m) → 0` and `L(m)/λ_m → +∞`.

## The route

The paper compares `Σ_{j≥m} j^{−p}` with `∫_m^∞ t^{−p} dt`. Mathlib v4.31.0 has the finite
sum/integral comparison but not the improper one, so the comparison here is done by **telescoping**
against `j ↦ j^{1−p}`, whose two increments are exactly the two bounds:

  `(p−1)(j+1)^{−p} ≤ j^{1−p} − (j+1)^{1−p} ≤ (p−1) j^{−p}`,

and both follow from one tangent-line inequality, `rpow_ge_tangent`: `u^q ≥ 1 + q(u−1)` for
`q ≤ 0` and `u > 0`, itself `exp x ≥ 1+x` composed with `log u ≤ u−1`. Summing telescopes to
`m^{1−p} − (m+n)^{1−p}` and the limit `n → ∞` kills the second term. No integral appears.

## SCOPE (disclosed)

* The `ξ_m` of `eq:doubling_powertail` are not named; the two inequalities they encode —
  `powerTail_ge` and `powerTail_le` — are what the corollary uses and are proved.
* `L(m) → 0` is proved on the loop closure in `Unbounded.lean` (`Stat.tailMass_tendsto_zero`),
  from summability rather than from this bound; it is not re-proved here.
* The statement is about a *sequence* `λ` and its tail `Σ_{j ≥ m} λ_j`, as the paper's is, and not
  about `Stat.tailMass`; `tailSeq_eq_tailMass` is the bridge on the loop closure.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1`, `p = p_*` | ✓ carried by `Decay` |
| `(λ_j)` positive with `eq:doubling_cut` | ✓ carried; only `eq:doubling_decay` is used |
| `0 < c₁ ≤ c₂` with `eq:doubling_decay` | ✓ carried as hypotheses |
| `m ≥ 1` | ✓ carried |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

/-- The tangent-line inequality for a non-positive exponent: `u^q ≥ 1 + q(u−1)`.

`exp x ≥ 1 + x` gives `u^q = exp(q log u) ≥ 1 + q log u`, and `log u ≤ u − 1` with `q ≤ 0` gives
`q log u ≥ q(u−1)`. -/
theorem rpow_ge_tangent {q u : ℝ} (hq : q ≤ 0) (hu : 0 < u) : 1 + q * (u - 1) ≤ u ^ q := by
  have hexp : q * Real.log u + 1 ≤ Real.exp (q * Real.log u) := Real.add_one_le_exp _
  have hlog : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu
  have hmul : q * (u - 1) ≤ q * Real.log u := mul_le_mul_of_nonpos_left hlog hq
  have hrw : u ^ q = Real.exp (q * Real.log u) := by
    rw [rpow_def_of_pos hu, mul_comm]
  rw [hrw]; linarith

section PowerTail

variable {p : ℝ}

/-- **The upper increment.** `j^{1−p} − (j+1)^{1−p} ≤ (p−1) j^{−p}` for `j ≥ 1`, `p > 1`. -/
theorem incr_le {t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    t ^ (1 - p) - (t + 1) ^ (1 - p) ≤ (p - 1) * t ^ (-p) := by
  have htp : (0 : ℝ) < t ^ (1 - p) := rpow_pos_of_pos ht _
  have hu : (0 : ℝ) < (t + 1) / t := by positivity
  have htan := rpow_ge_tangent (q := 1 - p) (u := (t + 1) / t) (by linarith) hu
  have hdiv : ((t + 1) / t) ^ (1 - p) = (t + 1) ^ (1 - p) / t ^ (1 - p) :=
    Real.div_rpow (by linarith) ht.le (1 - p)
  have hminus : (t + 1) / t - 1 = 1 / t := by field_simp; ring
  rw [hdiv, hminus] at htan
  -- `1 + (1−p)/t ≤ (t+1)^{1−p}/t^{1−p}`
  have hmul : t ^ (1 - p) * (1 + (1 - p) * (1 / t)) ≤ (t + 1) ^ (1 - p) := by
    rw [← le_div_iff₀' htp]
    exact htan
  have hsplit : t ^ (1 - p) * ((1 - p) * (1 / t)) = -((p - 1) * t ^ (-p)) := by
    have h1 : t ^ (1 - p) * (1 / t) = t ^ (-p) := by
      have hh : t ^ (1 - p) = t ^ (-p) * t := by
        rw [show (1 : ℝ) - p = -p + 1 by ring, rpow_add ht, rpow_one]
      rw [hh, mul_one_div, mul_div_assoc, div_self ht.ne', mul_one]
    calc t ^ (1 - p) * ((1 - p) * (1 / t)) = (1 - p) * (t ^ (1 - p) * (1 / t)) := by ring
      _ = (1 - p) * t ^ (-p) := by rw [h1]
      _ = -((p - 1) * t ^ (-p)) := by ring
  nlinarith [hmul, hsplit]

/-- **The lower increment.** `(p−1)(j+1)^{−p} ≤ j^{1−p} − (j+1)^{1−p}` for `j ≥ 1`, `p > 1`. -/
theorem le_incr {t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    (p - 1) * (t + 1) ^ (-p) ≤ t ^ (1 - p) - (t + 1) ^ (1 - p) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have ht1p : (0 : ℝ) < (t + 1) ^ (1 - p) := rpow_pos_of_pos ht1 _
  have hu : (0 : ℝ) < t / (t + 1) := by positivity
  have htan := rpow_ge_tangent (q := 1 - p) (u := t / (t + 1)) (by linarith) hu
  have hdiv : (t / (t + 1)) ^ (1 - p) = t ^ (1 - p) / (t + 1) ^ (1 - p) :=
    Real.div_rpow ht.le ht1.le (1 - p)
  have hminus : t / (t + 1) - 1 = -(1 / (t + 1)) := by field_simp; ring
  rw [hdiv, hminus] at htan
  have hmul : (t + 1) ^ (1 - p) * (1 + (1 - p) * -(1 / (t + 1))) ≤ t ^ (1 - p) := by
    rw [← le_div_iff₀' ht1p]
    exact htan
  have hsplit : (t + 1) ^ (1 - p) * ((1 - p) * -(1 / (t + 1))) = (p - 1) * (t + 1) ^ (-p) := by
    have h1 : (t + 1) ^ (1 - p) * (1 / (t + 1)) = (t + 1) ^ (-p) := by
      have hh : (t + 1) ^ (1 - p) = (t + 1) ^ (-p) * (t + 1) := by
        rw [show (1 : ℝ) - p = -p + 1 by ring, rpow_add ht1, rpow_one]
      rw [hh, mul_one_div, mul_div_assoc, div_self ht1.ne', mul_one]
    calc (t + 1) ^ (1 - p) * ((1 - p) * -(1 / (t + 1)))
        = (p - 1) * ((t + 1) ^ (1 - p) * (1 / (t + 1))) := by ring
      _ = (p - 1) * (t + 1) ^ (-p) := by rw [h1]
  nlinarith [hmul, hsplit]

/-- `j ↦ j^{−p}` is summable for `p > 1`. -/
theorem summable_rpow_neg (hp : 1 < p) : Summable fun j : ℕ => (j : ℝ) ^ (-p) := by
  have h := Real.summable_nat_rpow_inv.mpr hp
  refine h.congr fun j => ?_
  rw [rpow_neg (Nat.cast_nonneg j)]

/-- `Σ_{j ≥ m} j^{−p}`, the tail of the pure power. -/
noncomputable def powerTail (p : ℝ) (m : ℕ) : ℝ := ∑' k : ℕ, ((k + m : ℕ) : ℝ) ^ (-p)

theorem hasSum_powerTail (hp : 1 < p) (m : ℕ) :
    HasSum (fun k : ℕ => ((k + m : ℕ) : ℝ) ^ (-p)) (powerTail p m) :=
  ((summable_nat_add_iff m).mpr (summable_rpow_neg hp)).hasSum

theorem powerTail_succ (hp : 1 < p) (m : ℕ) :
    powerTail p m = (m : ℝ) ^ (-p) + powerTail p (m + 1) := by
  have h0 := hasSum_powerTail hp m
  have h1 : HasSum (fun n : ℕ => ((n + 1 + m : ℕ) : ℝ) ^ (-p)) (powerTail p (m + 1)) := by
    have h := hasSum_powerTail hp (m + 1)
    have he : (fun k : ℕ => ((k + (m + 1) : ℕ) : ℝ) ^ (-p))
        = fun n : ℕ => ((n + 1 + m : ℕ) : ℝ) ^ (-p) := by
      funext n; congr 2; omega
    rwa [he] at h
  have h2 := (hasSum_nat_add_iff (f := fun k : ℕ => ((k + m : ℕ) : ℝ) ^ (-p)) 1).mp h1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.zero_add] at h2
  have h3 := h0.unique h2
  rw [h3]; ring

/-- The vanishing of the telescoped remainder: `(m+n)^{1−p} → 0`. -/
theorem tendsto_shift_rpow (hp : 1 < p) (m : ℕ) :
    Tendsto (fun n : ℕ => ((n + m : ℕ) : ℝ) ^ (1 - p)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => ((n + m : ℕ) : ℝ)) atTop atTop := by
    have : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono (fun n => ?_) this
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hneg : Tendsto (fun x : ℝ => x ^ (-(p - 1))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have := hneg.comp hbase
  refine this.congr fun n => ?_
  simp only [Function.comp_apply]
  congr 1
  ring

/-- **`eq:doubling_powertail`, lower half.** `m^{1−p}/(p−1) ≤ Σ_{j≥m} j^{−p}`. -/
theorem powerTail_ge (hp : 1 < p) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ^ (1 - p) / (p - 1) ≤ powerTail p m := by
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hpartial : ∀ n : ℕ,
      (m : ℝ) ^ (1 - p) - ((n + m : ℕ) : ℝ) ^ (1 - p)
        ≤ (p - 1) * ∑ k ∈ Finset.range n, ((k + m : ℕ) : ℝ) ^ (-p) := by
    intro n
    have htel := Finset.sum_range_sub' (fun i : ℕ => ((i + m : ℕ) : ℝ) ^ (1 - p)) n
    simp only [Nat.zero_add] at htel
    have hstep : ∀ k ∈ Finset.range n,
        ((k + m : ℕ) : ℝ) ^ (1 - p) - ((k + 1 + m : ℕ) : ℝ) ^ (1 - p)
          ≤ (p - 1) * ((k + m : ℕ) : ℝ) ^ (-p) := by
      intro k _
      have ht : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by
        have : 1 ≤ k + m := by omega
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
      have hcast : (((k + 1 + m : ℕ)) : ℝ) = ((k + m : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact incr_le hp ht
    have hsum := Finset.sum_le_sum hstep
    rw [htel, ← Finset.mul_sum] at hsum
    exact hsum
  have hlim : Tendsto (fun n : ℕ =>
      (m : ℝ) ^ (1 - p) - ((n + m : ℕ) : ℝ) ^ (1 - p)) atTop (𝓝 ((m : ℝ) ^ (1 - p))) := by
    have := (tendsto_const_nhds (x := (m : ℝ) ^ (1 - p)) (f := atTop (α := ℕ))).sub
      (tendsto_shift_rpow hp m)
    simpa using this
  have hlim2 : Tendsto (fun n : ℕ => (p - 1) * ∑ k ∈ Finset.range n, ((k + m : ℕ) : ℝ) ^ (-p))
      atTop (𝓝 ((p - 1) * powerTail p m)) :=
    ((hasSum_powerTail hp m).tendsto_sum_nat).const_mul _
  have hle : (m : ℝ) ^ (1 - p) ≤ (p - 1) * powerTail p m :=
    le_of_tendsto_of_tendsto' hlim hlim2 hpartial
  rw [div_le_iff₀ hp1]
  linarith

/-- **`eq:doubling_powertail`, upper half.** `Σ_{j≥m} j^{−p} ≤ m^{−p} + m^{1−p}/(p−1)`. -/
theorem powerTail_le (hp : 1 < p) {m : ℕ} (hm : 1 ≤ m) :
    powerTail p m ≤ (m : ℝ) ^ (-p) + (m : ℝ) ^ (1 - p) / (p - 1) := by
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpartial : ∀ n : ℕ,
      (p - 1) * ∑ k ∈ Finset.range n, ((k + (m + 1) : ℕ) : ℝ) ^ (-p) ≤ (m : ℝ) ^ (1 - p) := by
    intro n
    have htel := Finset.sum_range_sub' (fun i : ℕ => ((i + m : ℕ) : ℝ) ^ (1 - p)) n
    simp only [Nat.zero_add] at htel
    have hstep : ∀ k ∈ Finset.range n,
        (p - 1) * ((k + (m + 1) : ℕ) : ℝ) ^ (-p)
          ≤ ((k + m : ℕ) : ℝ) ^ (1 - p) - ((k + 1 + m : ℕ) : ℝ) ^ (1 - p) := by
      intro k _
      have ht : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by
        have h1 : 1 ≤ k + m := by omega
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
      have hcast1 : (((k + 1 + m : ℕ)) : ℝ) = ((k + m : ℕ) : ℝ) + 1 := by push_cast; ring
      have hcast2 : (((k + (m + 1) : ℕ)) : ℝ) = ((k + m : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast1, hcast2]
      exact le_incr hp ht
    have hsum := Finset.sum_le_sum hstep
    rw [← Finset.mul_sum, htel] at hsum
    have hnn : (0 : ℝ) ≤ ((n + m : ℕ) : ℝ) ^ (1 - p) :=
      rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hlim2 : Tendsto
      (fun n : ℕ => (p - 1) * ∑ k ∈ Finset.range n, ((k + (m + 1) : ℕ) : ℝ) ^ (-p))
      atTop (𝓝 ((p - 1) * powerTail p (m + 1))) :=
    ((hasSum_powerTail hp (m + 1)).tendsto_sum_nat).const_mul _
  have hle : (p - 1) * powerTail p (m + 1) ≤ (m : ℝ) ^ (1 - p) :=
    le_of_tendsto_of_tendsto' hlim2 tendsto_const_nhds hpartial
  have hsucc := powerTail_succ hp m
  rw [hsucc]
  have : powerTail p (m + 1) ≤ (m : ℝ) ^ (1 - p) / (p - 1) := by
    rw [le_div_iff₀ hp1]; linarith
  linarith

end PowerTail

/-! ## The tail of the invariant measure -/

/-- `L(m) = Σ_{j ≥ m} λ_j`, the tail of the sequence. -/
noncomputable def tailSeq (lam : ℕ → ℝ) (m : ℕ) : ℝ := ∑' k : ℕ, lam (k + m)

namespace Decay

variable (D : Decay)


/-- **`eq:doubling_tailratio`, both pairs.** With `c₁ j^{−p} ≤ λ_j ≤ c₂ j^{−p}` on `j ≥ 1`,
the tail and the ratio of the tail to the mass at the cut are pinned to a power and to `m`.

The summability of `λ` is a hypothesis, as it must be: `eq:doubling_decay` alone gives it
(comparison with `j^{−p}`, `p > 1`), but the comparison is done here on the sums, not on the
summability. -/
theorem tail_bounds {lam : ℕ → ℝ} {c₁ c₂ : ℝ} (hsum : Summable lam)
    (hc1 : 0 < c₁) (hbelow : ∀ j : ℕ, 1 ≤ j → c₁ * (j : ℝ) ^ (-D.p) ≤ lam j)
    (habove : ∀ j : ℕ, 1 ≤ j → lam j ≤ c₂ * (j : ℝ) ^ (-D.p))
    {m : ℕ} (hm : 1 ≤ m) :
    c₁ * ((m : ℝ) ^ (1 - D.p) / (D.p - 1)) ≤ tailSeq lam m ∧
      tailSeq lam m ≤ c₂ * ((m : ℝ) ^ (-D.p) + (m : ℝ) ^ (1 - D.p) / (D.p - 1)) := by
  have hp := D.p_gt_one
  have hpt := hasSum_powerTail (p := D.p) hp m
  have hlam : HasSum (fun k : ℕ => lam (k + m)) (tailSeq lam m) :=
    ((summable_nat_add_iff m).mpr hsum).hasSum
  constructor
  · have hcmp : ∀ k : ℕ, c₁ * ((k + m : ℕ) : ℝ) ^ (-D.p) ≤ lam (k + m) := fun k =>
      hbelow (k + m) (by omega)
    have := Summable.tsum_le_tsum hcmp ((hpt.mul_left c₁).summable) hlam.summable
    rw [(hpt.mul_left c₁).tsum_eq, hlam.tsum_eq] at this
    refine le_trans ?_ this
    exact mul_le_mul_of_nonneg_left (powerTail_ge hp hm) hc1.le
  · have hcmp : ∀ k : ℕ, lam (k + m) ≤ c₂ * ((k + m : ℕ) : ℝ) ^ (-D.p) := fun k =>
      habove (k + m) (by omega)
    have hc2 : 0 ≤ c₂ := by
      have h1 := hbelow 1 le_rfl
      have h2 := habove 1 le_rfl
      have hone : ((1 : ℕ) : ℝ) ^ (-D.p) = 1 := by norm_num
      rw [hone] at h1 h2
      nlinarith [h1, h2, hc1]
    have := Summable.tsum_le_tsum hcmp hlam.summable ((hpt.mul_left c₂).summable)
    rw [(hpt.mul_left c₂).tsum_eq, hlam.tsum_eq] at this
    exact le_trans this (mul_le_mul_of_nonneg_left (powerTail_le hp hm) hc2)

/-- **`eq:doubling_tailratio`, second pair, lower half.** `c₁ m λ_m ≤ c₂(p−1) L(m)`, the
denominator-free form of `L(m)/λ_m ≥ c₁ m/(c₂(p−1))`. This is what drives `L(m)/λ_m → +∞` and,
through `lem:doubling_percut`, the `√m` rate of `cor:doubling_family`. -/
theorem tail_ratio_ge {lam : ℕ → ℝ} {c₁ c₂ : ℝ} (hsum : Summable lam)
    (hc1 : 0 < c₁) (hbelow : ∀ j : ℕ, 1 ≤ j → c₁ * (j : ℝ) ^ (-D.p) ≤ lam j)
    (habove : ∀ j : ℕ, 1 ≤ j → lam j ≤ c₂ * (j : ℝ) ^ (-D.p))
    {m : ℕ} (hm : 1 ≤ m) :
    c₁ * (m : ℝ) * lam m ≤ c₂ * (D.p - 1) * tailSeq lam m := by
  have hp := D.p_gt_one
  have hp1 : (0 : ℝ) < D.p - 1 := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmp : (0 : ℝ) < (m : ℝ) ^ (-D.p) := rpow_pos_of_pos hmpos _
  have hup := habove m hm
  have hlo := hbelow m hm
  have hc2pos : 0 < c₂ := by nlinarith [hmp, hc1, hup, hlo]
  obtain ⟨hlow, -⟩ := D.tail_bounds hsum hc1 hbelow habove hm
  have hshift : (m : ℝ) ^ (1 - D.p) = (m : ℝ) * (m : ℝ) ^ (-D.p) := by
    rw [show (1 : ℝ) - D.p = 1 + -D.p by ring, rpow_add hmpos, rpow_one]
  rw [hshift] at hlow
  have h2 : c₂ * (D.p - 1) * (c₁ * ((m : ℝ) * (m : ℝ) ^ (-D.p) / (D.p - 1)))
      = c₁ * (m : ℝ) * (c₂ * (m : ℝ) ^ (-D.p)) := by
    field_simp
  calc c₁ * (m : ℝ) * lam m ≤ c₁ * (m : ℝ) * (c₂ * (m : ℝ) ^ (-D.p)) :=
        mul_le_mul_of_nonneg_left hup (by positivity)
    _ = c₂ * (D.p - 1) * (c₁ * ((m : ℝ) * (m : ℝ) ^ (-D.p) / (D.p - 1))) := h2.symm
    _ ≤ c₂ * (D.p - 1) * tailSeq lam m :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-! ## `cor:doubling_tail_sharp`, quantitatively -/

/-- **`eq:doubling_tail_sharp`, first line, in explicit form.** If the rescaled profile is within
`t` of `C` past `m₀`, then `(p_*−1) m^{p_*−1} L(m)` is within `t(1 + (p_*−1)/m) + |C|(p_*−1)/m`
of `C` at every `m ≥ m₀`.

This is the corollary's content with the limit unwound: the paper's `t → 0` argument is the
statement read at every `t`, and it converts to `L(m) = C m^{1−p_*}(1+o(1))/(p_*−1)` as soon as
`theo:doubling_sharp` supplies the limit. It is stated this way because the limit is open and the
inequality is not. -/
theorem tail_sharp {lam : ℕ → ℝ} {C t : ℝ} (hsum : Summable lam) {m₀ m : ℕ}
    (hm : m₀ ≤ m) (hm1 : 1 ≤ m)
    (hclose : ∀ j : ℕ, m₀ ≤ j → |lam j * (j : ℝ) ^ D.p - C| ≤ t) :
    |(D.p - 1) * (m : ℝ) ^ (D.p - 1) * tailSeq lam m - C|
      ≤ t * (1 + (D.p - 1) / (m : ℝ)) + |C| * ((D.p - 1) / (m : ℝ)) := by
  have hp := D.p_gt_one
  have hp1 : (0 : ℝ) < D.p - 1 := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  set P : ℝ := powerTail D.p m with hP
  set W : ℝ := (D.p - 1) * (m : ℝ) ^ (D.p - 1) with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  have hmm : (m : ℝ) ^ (D.p - 1) * (m : ℝ) ^ (1 - D.p) = 1 := by
    rw [← rpow_add hmpos]; simp
  have hmm2 : (m : ℝ) ^ (D.p - 1) * (m : ℝ) ^ (-D.p) = ((m : ℝ))⁻¹ := by
    rw [← rpow_add hmpos, show D.p - 1 + -D.p = -1 by ring, rpow_neg_one]
  -- the pure-power tail, rescaled, is between `1` and `1 + (p−1)/m`
  have hWP_lo : (1 : ℝ) ≤ W * P := by
    have h := powerTail_ge (p := D.p) hp hm1
    rw [← hP] at h
    have h2 : W * ((m : ℝ) ^ (1 - D.p) / (D.p - 1)) = 1 := by
      rw [hW]; field_simp; linarith [hmm]
    calc (1 : ℝ) = W * ((m : ℝ) ^ (1 - D.p) / (D.p - 1)) := h2.symm
      _ ≤ W * P := mul_le_mul_of_nonneg_left h hWpos.le
  have hWP_hi : W * P ≤ 1 + (D.p - 1) / (m : ℝ) := by
    have h := powerTail_le (p := D.p) hp hm1
    rw [← hP] at h
    have h2 : W * ((m : ℝ) ^ (-D.p) + (m : ℝ) ^ (1 - D.p) / (D.p - 1))
        = (D.p - 1) / (m : ℝ) + 1 := by
      rw [hW]
      have e1 : (D.p - 1) * (m : ℝ) ^ (D.p - 1) * (m : ℝ) ^ (-D.p)
          = (D.p - 1) * ((m : ℝ) ^ (D.p - 1) * (m : ℝ) ^ (-D.p)) := by ring
      have e2 : (D.p - 1) * (m : ℝ) ^ (D.p - 1) * ((m : ℝ) ^ (1 - D.p) / (D.p - 1))
          = (m : ℝ) ^ (D.p - 1) * (m : ℝ) ^ (1 - D.p) := by field_simp
      rw [mul_add, e1, e2, hmm, hmm2, ← one_div, ← div_eq_mul_one_div]
    calc W * P ≤ W * ((m : ℝ) ^ (-D.p) + (m : ℝ) ^ (1 - D.p) / (D.p - 1)) :=
          mul_le_mul_of_nonneg_left h hWpos.le
      _ = (D.p - 1) / (m : ℝ) + 1 := h2
      _ = 1 + (D.p - 1) / (m : ℝ) := by ring
  have hPnn : 0 ≤ P := by
    have := hWP_lo; nlinarith [hWpos]
  -- the sequence is within `t` of the pure power, in tail sum
  have hpt := hasSum_powerTail (p := D.p) hp m
  have hlamS : HasSum (fun k : ℕ => lam (k + m)) (tailSeq lam m) :=
    ((summable_nat_add_iff m).mpr hsum).hasSum
  have hterm : ∀ k : ℕ, |lam (k + m) - C * ((k + m : ℕ) : ℝ) ^ (-D.p)|
      ≤ t * ((k + m : ℕ) : ℝ) ^ (-D.p) := by
    intro k
    have hj1 : 1 ≤ k + m := by omega
    have hjpos : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by exact_mod_cast hj1
    have hJn : (0 : ℝ) < ((k + m : ℕ) : ℝ) ^ (-D.p) := rpow_pos_of_pos hjpos _
    have hmul : ((k + m : ℕ) : ℝ) ^ D.p * ((k + m : ℕ) : ℝ) ^ (-D.p) = 1 := by
      rw [← rpow_add hjpos]; simp
    have hcancel : lam (k + m) * ((k + m : ℕ) : ℝ) ^ D.p * ((k + m : ℕ) : ℝ) ^ (-D.p)
        = lam (k + m) := by rw [mul_assoc, hmul, mul_one]
    have hfac : lam (k + m) - C * ((k + m : ℕ) : ℝ) ^ (-D.p)
        = (lam (k + m) * ((k + m : ℕ) : ℝ) ^ D.p - C) * ((k + m : ℕ) : ℝ) ^ (-D.p) := by
      calc lam (k + m) - C * ((k + m : ℕ) : ℝ) ^ (-D.p)
          = lam (k + m) * ((k + m : ℕ) : ℝ) ^ D.p * ((k + m : ℕ) : ℝ) ^ (-D.p)
            - C * ((k + m : ℕ) : ℝ) ^ (-D.p) := by rw [hcancel]
        _ = (lam (k + m) * ((k + m : ℕ) : ℝ) ^ D.p - C) * ((k + m : ℕ) : ℝ) ^ (-D.p) := by
            ring
    rw [hfac, abs_mul, abs_of_pos hJn]
    exact mul_le_mul_of_nonneg_right (hclose (k + m) (by omega)) hJn.le
  have hdiff : HasSum (fun k : ℕ => lam (k + m) - C * ((k + m : ℕ) : ℝ) ^ (-D.p))
      (tailSeq lam m - C * P) := by
    have := hlamS.sub (hpt.mul_left C)
    rw [hP]; exact this
  have hbound : |tailSeq lam m - C * P| ≤ t * P := by
    have hsummable : Summable fun k : ℕ => ‖lam (k + m) - C * ((k + m : ℕ) : ℝ) ^ (-D.p)‖ :=
      hdiff.summable.abs
    have h1 : ‖tailSeq lam m - C * P‖
        ≤ ∑' k : ℕ, ‖lam (k + m) - C * ((k + m : ℕ) : ℝ) ^ (-D.p)‖ := by
      rw [← hdiff.tsum_eq]
      exact norm_tsum_le_tsum_norm hsummable
    have h2 : ∑' k : ℕ, ‖lam (k + m) - C * ((k + m : ℕ) : ℝ) ^ (-D.p)‖ ≤ t * P := by
      have hcmp := Summable.tsum_le_tsum (f := fun k : ℕ =>
          ‖lam (k + m) - C * ((k + m : ℕ) : ℝ) ^ (-D.p)‖)
        (g := fun k : ℕ => t * ((k + m : ℕ) : ℝ) ^ (-D.p))
        (fun k => by simpa [Real.norm_eq_abs] using hterm k) hsummable (hpt.mul_left t).summable
      rwa [(hpt.mul_left t).tsum_eq, ← hP] at hcmp
    simpa [Real.norm_eq_abs] using le_trans h1 h2
  -- assemble
  have hsplit : W * tailSeq lam m - C
      = W * (tailSeq lam m - C * P) + C * (W * P - 1) := by ring
  have hb1 : |W * (tailSeq lam m - C * P)| ≤ W * (t * P) := by
    rw [abs_mul, abs_of_pos hWpos]
    exact mul_le_mul_of_nonneg_left hbound hWpos.le
  have hb2 : W * (t * P) ≤ t * (1 + (D.p - 1) / (m : ℝ)) := by
    have ht0 : 0 ≤ t := le_trans (abs_nonneg _) (hclose m hm)
    have : W * (t * P) = t * (W * P) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hWP_hi ht0
  have hb3 : |C * (W * P - 1)| ≤ |C| * ((D.p - 1) / (m : ℝ)) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    rw [abs_of_nonneg (by linarith [hWP_lo])]
    linarith [hWP_hi]
  calc |(D.p - 1) * (m : ℝ) ^ (D.p - 1) * tailSeq lam m - C|
      = |W * (tailSeq lam m - C * P) + C * (W * P - 1)| := by rw [hW, ← hsplit]
    _ ≤ |W * (tailSeq lam m - C * P)| + |C * (W * P - 1)| := abs_add_le _ _
    _ ≤ t * (1 + (D.p - 1) / (m : ℝ)) + |C| * ((D.p - 1) / (m : ℝ)) := by
        linarith [hb1, hb2, hb3]

end Decay

end GFNBounds.Doubling
