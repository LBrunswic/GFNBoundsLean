import GFNBounds.Doubling.WindowSum
import GFNBounds.Doubling.DecayNotation

/-!
# `eq:doubling_R0`: the total window weight is `1 + O(1/m)`, effectively

**`lem:doubling_descent`, `eq:doubling_R0`** — `app_doubling.tex:965–1024`.

> Then there are `c₄ > 0` and an integer `ℓ₁ > d`, depending on `c` and `d` alone, with
> `½ ≤ R₀(m) ≤ 2` and `|R₀(m) − 1| ≤ c₄/m` for every `m ≥ ℓ₁`.

## What this file changes

The paper reads these two bounds off `eq:doubling_Rexp`, whose proof is Euler–Maclaurin for
`t^{−r}` with a complete-monotonicity remainder — the one tool mathlib v4.31.0 does not have, and
the reason `theo:doubling_decay` carries them as hypotheses in `Descent.lean`. But the *refined*
expansion, with its named coefficients `A₀, A₁, Γ`, is needed only by `rem:doubling_parity` and
`rem:doubling_second_order`. What the descent block consumes is only `eq:doubling_R0`, and that
needs no more than a **first-order** comparison, which `WindowSum.lean` supplies by telescoping.

So the two bounds are proved here, and — the point — with an **explicit** constant:

  `c₄ = 16 c τ`,  valid for every `m ≥ 1`,

against the paper's non-effective `c₄`. Since `ℓ₂, ℓ₃, ℓ₄, m₀, m₃, c₃, c₅, c₆, c₉, K₀, c₈` all
inherit their non-effectivity from `c₄` and `ℓ₁`, this is where effectivization starts. `ℓ₁` here
is `max(d+1, 32cτ)`, the second requirement being what turns `|R₀ − 1| ≤ c₄/m` into `½ ≤ R₀ ≤ 2`.

## SCOPE (disclosed)

`eq:doubling_Rexp` itself is still open: nothing here gives the `1/m` coefficient, only its size.
`lem:doubling_expansion` therefore stays partial. What is now closed is the part of
`lem:doubling_descent` that `Descent.lean` had been carrying as a hypothesis, so
`R0_sub_one_le` can be fed to `Decay.decay_block` directly.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

theorem rpow_sub_one_eq {t q : ℝ} (ht : 0 < t) : t ^ (q - 1) = t ^ q / t := by
  rw [rpow_sub ht, rpow_one]

namespace Decay

variable (D : Decay)

/-- The foot of the window, `⌈m/2⌉`. -/
theorem window_eq (m : ℕ) : window m = Finset.Ico ((m + 1) / 2) m := rfl

theorem foot_le (m : ℕ) : ((m : ℝ)) / 2 ≤ (((m + 1) / 2 : ℕ) : ℝ) := by
  have h : m ≤ 2 * ((m + 1) / 2) := by omega
  have h' : (m : ℝ) ≤ 2 * (((m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h
  linarith

theorem le_foot (m : ℕ) : (((m + 1) / 2 : ℕ) : ℝ) ≤ ((m : ℝ) + 1) / 2 := by
  have h : 2 * ((m + 1) / 2) ≤ m + 1 := by omega
  have h' : 2 * (((m + 1) / 2 : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h
  linarith

theorem one_le_foot {m : ℕ} (hm : 1 ≤ m) : 1 ≤ (m + 1) / 2 := by omega

theorem foot_le_self {m : ℕ} (hm : 1 ≤ m) : (m + 1) / 2 ≤ m := by omega

/-- `R₀(m)` in the form the comparison uses: a constant times `m^p` times a window sum. -/
theorem R0_eq {m : ℕ} (hm : 1 ≤ m) :
    D.R0 m = D.c / (1 - D.eps m) *
      ((m : ℝ) ^ D.p * ∑ j ∈ window m, (j : ℝ) ^ (-D.p) / ((j : ℝ) + 1)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [R0, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := one_le_of_mem_window' hm hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hb : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hne : (1 : ℝ) - D.eps m ≠ 0 := (D.one_sub_eps_pos hm).ne'
  have hpow : ((m : ℝ) / (j : ℝ)) ^ D.p = (m : ℝ) ^ D.p * (j : ℝ) ^ (-D.p) := by
    rw [Real.div_rpow hmpos.le hjpos.le, rpow_neg hjpos.le, div_eq_mul_inv]
  rw [wm, D.qm_eq, hpow]
  field_simp

/-! ### The two comparisons on the window sum -/

section Window

/-- Term by term: `j^{−p}/(j+1) ≤ j^{−p−1}`. -/
theorem term_le {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ^ (-D.p) / ((j : ℝ) + 1) ≤ (j : ℝ) ^ (-D.p - 1) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hnn : (0 : ℝ) ≤ (j : ℝ) ^ (-D.p) := rpow_nonneg hjpos.le _
  rw [rpow_sub_one_eq hjpos]
  apply div_le_div_of_nonneg_left hnn hjpos
  linarith

/-- Term by term: `j^{−p−1} − j^{−p−2} ≤ j^{−p}/(j+1)`, since `(j−1)(j+1) ≤ j²`. -/
theorem le_term {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ^ (-D.p - 1) - (j : ℝ) ^ (-D.p - 1 - 1) ≤ (j : ℝ) ^ (-D.p) / ((j : ℝ) + 1) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hnn : (0 : ℝ) ≤ (j : ℝ) ^ (-D.p) := rpow_nonneg hjpos.le _
  rw [rpow_sub_one_eq hjpos, rpow_sub_one_eq hjpos, rpow_sub_one_eq hjpos]
  have hgap : (j : ℝ) ^ (-D.p) / (j : ℝ) - (j : ℝ) ^ (-D.p) / (j : ℝ) / (j : ℝ)
      = (j : ℝ) ^ (-D.p) * (((j : ℝ) - 1) / ((j : ℝ) * (j : ℝ))) := by
    field_simp
  rw [hgap]
  have hcmp : ((j : ℝ) - 1) / ((j : ℝ) * (j : ℝ)) ≤ 1 / ((j : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc (j : ℝ) ^ (-D.p) * (((j : ℝ) - 1) / ((j : ℝ) * (j : ℝ)))
      ≤ (j : ℝ) ^ (-D.p) * (1 / ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left hcmp hnn
    _ = (j : ℝ) ^ (-D.p) / ((j : ℝ) + 1) := by ring

/-- The window sum, above. -/
theorem windowSum_le {m : ℕ} (hm : 1 ≤ m) :
    ∑ j ∈ window m, (j : ℝ) ^ (-D.p) / ((j : ℝ) + 1)
      ≤ ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 1) :=
  Finset.sum_le_sum fun _ hj => D.term_le (one_le_of_mem_window' hm hj)

/-- The window sum, below. -/
theorem windowSum_ge {m : ℕ} (hm : 1 ≤ m) :
    (∑ j ∈ window m, (j : ℝ) ^ (-D.p - 1)) - ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 1 - 1)
      ≤ ∑ j ∈ window m, (j : ℝ) ^ (-D.p) / ((j : ℝ) + 1) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun _ hj => D.le_term (one_le_of_mem_window' hm hj)

end Window

/-! ### The foot of the window against the pure power -/

section Foot

variable {m : ℕ}

theorem half_rpow (hm : 1 ≤ m) :
    ((m : ℝ) / 2) ^ (-D.p) = D.tau * (m : ℝ) ^ (-D.p) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Real.div_rpow hmpos.le (by norm_num), rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [tau, div_eq_mul_inv, inv_inv]
  ring

/-- `a^{−p} ≤ τ m^{−p}`, since `a ≥ m/2`. -/
theorem foot_rpow_le (hm : 1 ≤ m) :
    (((m + 1) / 2 : ℕ) : ℝ) ^ (-D.p) ≤ D.tau * (m : ℝ) ^ (-D.p) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [← D.half_rpow hm]
  exact rpow_le_rpow_of_nonpos (by positivity) (foot_le m) (by linarith [D.p_pos])

/-- `τ m^{−p}(1 − p/m) ≤ a^{−p}`, since `a ≤ (m+1)/2` and `(1+x)^{−p} ≥ 1 − px`. -/
theorem le_foot_rpow (hm : 1 ≤ m) :
    D.tau * (m : ℝ) ^ (-D.p) * (1 - D.p / (m : ℝ)) ≤ (((m + 1) / 2 : ℕ) : ℝ) ^ (-D.p) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hapos : (0 : ℝ) < (((m + 1) / 2 : ℕ) : ℝ) := by
    have : 1 ≤ (m + 1) / 2 := one_le_foot hm
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hstep : (((m : ℝ) + 1) / 2) ^ (-D.p) ≤ (((m + 1) / 2 : ℕ) : ℝ) ^ (-D.p) :=
    rpow_le_rpow_of_nonpos hapos (le_foot m) (by linarith [D.p_pos])
  refine le_trans ?_ hstep
  -- `((m+1)/2)^{-p} = τ (m+1)^{-p}` and `(m+1)^{-p} = m^{-p}(1+1/m)^{-p} ≥ m^{-p}(1 - p/m)`
  have hsplit : ((m : ℝ) + 1) / 2 = ((m : ℝ) * (1 + 1 / (m : ℝ))) / 2 := by
    field_simp
  have hprod : (((m : ℝ) + 1) / 2) ^ (-D.p)
      = D.tau * ((m : ℝ) ^ (-D.p) * (1 + 1 / (m : ℝ)) ^ (-D.p)) := by
    rw [hsplit, Real.div_rpow (by positivity) (by norm_num),
      Real.mul_rpow hmpos.le (by positivity),
      rpow_neg (by norm_num : (0:ℝ) ≤ 2), tau, div_eq_mul_inv, inv_inv]
    ring
  rw [hprod]
  have htan : 1 - D.p / (m : ℝ) ≤ (1 + 1 / (m : ℝ)) ^ (-D.p) := by
    have h := rpow_ge_tangent (q := -D.p) (u := 1 + 1 / (m : ℝ))
      (by linarith [D.p_pos]) (by positivity)
    have he : 1 + -D.p * ((1 + 1 / (m : ℝ)) - 1) = 1 - D.p / (m : ℝ) := by
      field_simp; ring
    linarith [h, he.symm.le, he.le]
  have hτ : (0 : ℝ) < D.tau := D.tau_pos
  have hmp : (0 : ℝ) < (m : ℝ) ^ (-D.p) := rpow_pos_of_pos hmpos _
  have h1 : (m : ℝ) ^ (-D.p) * (1 - D.p / (m : ℝ))
      ≤ (m : ℝ) ^ (-D.p) * (1 + 1 / (m : ℝ)) ^ (-D.p) :=
    mul_le_mul_of_nonneg_left htan hmp.le
  calc D.tau * (m : ℝ) ^ (-D.p) * (1 - D.p / (m : ℝ))
      = D.tau * ((m : ℝ) ^ (-D.p) * (1 - D.p / (m : ℝ))) := by ring
    _ ≤ D.tau * ((m : ℝ) ^ (-D.p) * (1 + 1 / (m : ℝ)) ^ (-D.p)) :=
        mul_le_mul_of_nonneg_left h1 hτ.le

end Foot

/-! ### `eq:doubling_R0`, with an explicit constant -/

section Bound

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
/-- **`eq:doubling_R0`, second half, effectivized.** `|R₀(m) − 1| ≤ 16cτ/m` at every `m ≥ 1`. -/
theorem R0_sub_one_le (hm : 1 ≤ m) :
    |D.R0 m - 1| ≤ 16 * D.c * D.tau / (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hp := D.p_gt_one
  have hppos := D.p_pos
  have hτ2 := D.tau_gt_two
  have hτpos : (0 : ℝ) < D.tau := D.tau_pos
  have hc := D.c_pos
  have hc1 := D.c_lt_one
  set a : ℕ := (m + 1) / 2 with ha
  have ha1 : 1 ≤ a := one_le_foot hm
  have ham : a ≤ m := foot_le_self hm
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha1
  have hage : (m : ℝ) / 2 ≤ (a : ℝ) := foot_le m
  set A : ℝ := (a : ℝ) ^ (-D.p) with hA
  set Mm : ℝ := (m : ℝ) ^ (-D.p) with hMm
  have hApos : 0 < A := rpow_pos_of_pos hapos _
  have hMpos : 0 < Mm := rpow_pos_of_pos hmpos _
  set S1 : ℝ := ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 1) with hS1
  set S2 : ℝ := ∑ j ∈ window m, (j : ℝ) ^ (-D.p - 1 - 1) with hS2
  set Sf : ℝ := ∑ j ∈ window m, (j : ℝ) ^ (-D.p) / ((j : ℝ) + 1) with hSf
  -- the two window comparisons
  have hwin : window m = Finset.Ico a m := rfl
  have hS1lo : (A - Mm) / D.p ≤ S1 := by
    rw [hS1, hwin]; exact sum_window_ge hppos ha1 ham
  have hS1hi : S1 ≤ (a : ℝ) ^ (-D.p - 1) + (A - Mm) / D.p := by
    rw [hS1, hwin]; exact sum_window_le hppos ha1 ham
  -- `S2 ≤ S1 / a`
  have hS2le : S2 ≤ S1 / (a : ℝ) := by
    rw [hS2, hS1, Finset.sum_div]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := one_le_of_mem_window' hm hj
    have hja : a ≤ j := (Finset.mem_Ico.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hjar : (a : ℝ) ≤ (j : ℝ) := by exact_mod_cast hja
    rw [rpow_sub_one_eq hjpos]
    exact div_le_div_of_nonneg_left (rpow_nonneg hjpos.le _) hapos hjar
  -- `a^{-p-1} = A / a`
  have hapow : (a : ℝ) ^ (-D.p - 1) = A / (a : ℝ) := by rw [hA, rpow_sub_one_eq hapos]
  have haA : A ≤ (a : ℝ) * A := by nlinarith [hApos, hapos, (by exact_mod_cast ha1 : (1:ℝ) ≤ (a:ℝ))]
  -- `|Sf - (A - Mm)/p| ≤ 2 A / a`
  have hgapU : Sf - (A - Mm) / D.p ≤ A / (a : ℝ) := by
    have h1 := D.windowSum_le hm
    rw [← hSf, ← hS1] at h1
    rw [← hapow]; linarith [h1, hS1hi]
  have hS2b : S2 ≤ 2 * (A / (a : ℝ)) := by
    have hone : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have h1 : S1 ≤ A / (a : ℝ) + A / D.p := by
      rw [hapow] at hS1hi
      have hdd : (A - Mm) / D.p ≤ A / D.p := by gcongr; linarith
      linarith
    have h2 : S1 / (a : ℝ) ≤ (A / (a : ℝ) + A / D.p) / (a : ℝ) := by gcongr
    have h3 : (A / (a : ℝ) + A / D.p) / (a : ℝ) ≤ 2 * (A / (a : ℝ)) := by
      have hAa : A / (a : ℝ) ≤ A := by
        rw [div_le_iff₀ hapos]; nlinarith [hApos, hone]
      have hAp : A / D.p ≤ A := by
        rw [div_le_iff₀ hppos]; nlinarith [hApos]
      have hkey : A / (a : ℝ) + A / D.p ≤ 2 * A := by linarith
      have hdiv : (A / (a : ℝ) + A / D.p) / (a : ℝ) ≤ 2 * A / (a : ℝ) := by gcongr
      have heq : 2 * A / (a : ℝ) = 2 * (A / (a : ℝ)) := by ring
      linarith [hdiv, heq.le, heq.ge]
    linarith [hS2le, h2, h3]
  have hgapL : (A - Mm) / D.p - Sf ≤ 2 * (A / (a : ℝ)) := by
    have h2 := D.windowSum_ge hm
    rw [← hSf, ← hS1, ← hS2] at h2
    linarith [h2, hS1lo, hS2b]
  -- the constant `K = c/(1−ε(m))`, between `c` and `2c`
  set K : ℝ := D.c / (1 - D.eps m) with hK
  set im : ℝ := 1 / (m : ℝ) with him
  have himpos : 0 < im := by rw [him]; positivity
  have hεpos : 0 < D.eps m := D.eps_pos m
  have hεle : D.eps m ≤ D.c * im := by
    rw [D.eps_eq, him, div_le_iff₀ (by positivity)]
    have h1 : D.c * (1 / (m : ℝ)) * ((m : ℝ) + 1) = D.c * (((m : ℝ) + 1) / (m : ℝ)) := by
      field_simp
    have h2 : (1 : ℝ) ≤ ((m : ℝ) + 1) / (m : ℝ) := by
      rw [le_div_iff₀ hmpos]; linarith
    rw [h1]
    nlinarith [hc, h2]
  have honesub : (1 : ℝ) / 2 ≤ 1 - D.eps m := by
    have := D.eps_le_half hm; linarith
  have honesub' : 1 - D.eps m ≤ 1 := by linarith
  have hKlo : D.c ≤ K := by rw [hK, le_div_iff₀ (by linarith)]; nlinarith
  have hKhi : K ≤ 2 * D.c := by rw [hK, div_le_iff₀ (by linarith)]; nlinarith
  have hKpos : 0 < K := lt_of_lt_of_le hc hKlo
  -- the main term
  have hmppos : (0 : ℝ) < (m : ℝ) ^ D.p := rpow_pos_of_pos hmpos _
  have hmm : (m : ℝ) ^ D.p * Mm = 1 := by rw [hMm, ← rpow_add hmpos]; simp
  have hfoot := D.foot_rpow_le hm
  set Z : ℝ := (m : ℝ) ^ D.p * A with hZ
  have hZup : Z ≤ D.tau := by
    have h1 : (m : ℝ) ^ D.p * A ≤ (m : ℝ) ^ D.p * (D.tau * Mm) :=
      mul_le_mul_of_nonneg_left hfoot hmppos.le
    have h2 : (m : ℝ) ^ D.p * (D.tau * Mm) = D.tau * ((m : ℝ) ^ D.p * Mm) := by ring
    rw [h2, hmm, mul_one] at h1
    rw [hZ]; exact h1
  have hZlo : D.tau * (1 - D.p * im) ≤ Z := by
    have hpm : D.p / (m : ℝ) = D.p * im := by rw [him]; ring
    have h1 : (m : ℝ) ^ D.p * (D.tau * Mm * (1 - D.p / (m : ℝ))) ≤ (m : ℝ) ^ D.p * A :=
      mul_le_mul_of_nonneg_left (D.le_foot_rpow hm) hmppos.le
    have h2 : (m : ℝ) ^ D.p * (D.tau * Mm * (1 - D.p / (m : ℝ)))
        = D.tau * ((m : ℝ) ^ D.p * Mm) * (1 - D.p / (m : ℝ)) := by ring
    rw [h2, hmm, mul_one, hpm] at h1
    rw [hZ]; exact h1
  set X : ℝ := (m : ℝ) ^ D.p * Sf with hX
  set Y : ℝ := (m : ℝ) ^ D.p * ((A - Mm) / D.p) with hY
  have hYeq : Y = (Z - 1) / D.p := by
    rw [hY, hZ, ← hmm]; field_simp
  -- the error term, `m^p (A/a) ≤ 2 τ im`
  have hAa : (m : ℝ) ^ D.p * (A / (a : ℝ)) ≤ 2 * D.tau * im := by
    have key : A / (a : ℝ) ≤ 2 * (D.tau * Mm) / (m : ℝ) := by
      rw [div_le_div_iff₀ hapos hmpos]
      have k1 : A * (m : ℝ) ≤ D.tau * Mm * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hfoot hmpos.le
      have k2 : 2 * (D.tau * Mm) * ((m : ℝ) / 2) ≤ 2 * (D.tau * Mm) * (a : ℝ) :=
        mul_le_mul_of_nonneg_left hage (by positivity)
      linarith [k1, k2]
    have hfin : (m : ℝ) ^ D.p * (2 * (D.tau * Mm) / (m : ℝ)) = 2 * D.tau * im := by
      rw [him]
      have h : (m : ℝ) ^ D.p * (2 * (D.tau * Mm) / (m : ℝ))
          = 2 * D.tau * ((m : ℝ) ^ D.p * Mm) * (1 / (m : ℝ)) := by
        rw [div_eq_mul_one_div]; ring
      rw [h, hmm, mul_one]
    calc (m : ℝ) ^ D.p * (A / (a : ℝ))
        ≤ (m : ℝ) ^ D.p * (2 * (D.tau * Mm) / (m : ℝ)) :=
          mul_le_mul_of_nonneg_left key hmppos.le
      _ = 2 * D.tau * im := hfin
  have hXY1 : X - Y ≤ 2 * D.tau * im := by
    have h : X - Y = (m : ℝ) ^ D.p * (Sf - (A - Mm) / D.p) := by rw [hX, hY]; ring
    rw [h]
    exact le_trans (mul_le_mul_of_nonneg_left hgapU hmppos.le) hAa
  have hXY2 : Y - X ≤ 4 * D.tau * im := by
    have h : Y - X = (m : ℝ) ^ D.p * ((A - Mm) / D.p - Sf) := by rw [hX, hY]; ring
    rw [h]
    have h2 : (m : ℝ) ^ D.p * ((A - Mm) / D.p - Sf)
        ≤ (m : ℝ) ^ D.p * (2 * (A / (a : ℝ))) :=
      mul_le_mul_of_nonneg_left hgapL hmppos.le
    have h3 : (m : ℝ) ^ D.p * (2 * (A / (a : ℝ))) = 2 * ((m : ℝ) ^ D.p * (A / (a : ℝ))) := by
      ring
    rw [h3] at h2
    linarith [h2, hAa]
  -- `K Y = 1 + O(im)`
  have hKcram : K * ((D.tau - 1) / D.p) = 1 / (1 - D.eps m) := by
    rw [hK, div_mul_eq_mul_div, D.cramer]
  have hinvup : 1 / (1 - D.eps m) ≤ 1 + 2 * D.c * im := by
    rw [div_le_iff₀ (by linarith)]
    have hh : 2 * (D.c * im) * (1 / 2) ≤ 2 * (D.c * im) * (1 - D.eps m) :=
      mul_le_mul_of_nonneg_left honesub (by positivity)
    linarith [hh, hεle]
  have hinvlo : (1 : ℝ) ≤ 1 / (1 - D.eps m) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hKYup : K * Y ≤ 1 + 2 * D.c * im := by
    have h1 : Y ≤ (D.tau - 1) / D.p := by rw [hYeq]; gcongr
    have h2 : K * Y ≤ K * ((D.tau - 1) / D.p) := mul_le_mul_of_nonneg_left h1 hKpos.le
    rw [hKcram] at h2
    linarith [h2, hinvup]
  have hKYlo : 1 - 2 * (D.c * D.tau * im) ≤ K * Y := by
    have hd : (D.tau * (1 - D.p * im) - 1) / D.p = (D.tau - 1) / D.p - D.tau * im := by
      field_simp; ring
    have h1 : (D.tau - 1) / D.p - D.tau * im ≤ Y := by
      rw [hYeq, ← hd]; gcongr
    have h2 : K * ((D.tau - 1) / D.p - D.tau * im) ≤ K * Y :=
      mul_le_mul_of_nonneg_left h1 hKpos.le
    have h3 : K * ((D.tau - 1) / D.p - D.tau * im)
        = K * ((D.tau - 1) / D.p) - K * (D.tau * im) := by ring
    rw [h3, hKcram] at h2
    have h4 : K * (D.tau * im) ≤ 2 * D.c * (D.tau * im) :=
      mul_le_mul_of_nonneg_right hKhi (by positivity)
    linarith [h2, hinvlo, h4]
  -- assemble
  have hprod : 0 < D.c * D.tau * im := by positivity
  have hcτim : D.c * im ≤ D.c * D.tau * im := by nlinarith [hc, hτ2, himpos]
  have hKX1 : K * X - K * Y ≤ 4 * (D.c * D.tau * im) := by
    have h1 : K * (X - Y) ≤ K * (2 * D.tau * im) := mul_le_mul_of_nonneg_left hXY1 hKpos.le
    have h2 : K * (2 * D.tau * im) ≤ 2 * D.c * (2 * D.tau * im) :=
      mul_le_mul_of_nonneg_right hKhi (by positivity)
    have h3 : K * (X - Y) = K * X - K * Y := by ring
    rw [h3] at h1
    linarith [h1, h2]
  have hKX2 : K * Y - K * X ≤ 8 * (D.c * D.tau * im) := by
    have h1 : K * (Y - X) ≤ K * (4 * D.tau * im) := mul_le_mul_of_nonneg_left hXY2 hKpos.le
    have h2 : K * (4 * D.tau * im) ≤ 2 * D.c * (4 * D.tau * im) :=
      mul_le_mul_of_nonneg_right hKhi (by positivity)
    have h3 : K * (Y - X) = K * Y - K * X := by ring
    rw [h3] at h1
    linarith [h1, h2]
  have hR0 : D.R0 m = K * X := by rw [D.R0_eq hm, ← hSf, ← hX, ← hK]
  have htarget : 16 * D.c * D.tau / (m : ℝ) = 16 * (D.c * D.tau * im) := by rw [him]; ring
  rw [abs_le, hR0, htarget]
  constructor
  · linarith [hKX2, hKYlo, hprod]
  · linarith [hKX1, hKYup, hcτim, hprod]

/-- **`eq:doubling_R0`, first half.** `½ ≤ R₀(m) ≤ 2` once `m ≥ 32cτ`. -/
theorem R0_between (hm : 1 ≤ m) (hmb : 32 * D.c * D.tau ≤ (m : ℝ)) :
    1 / 2 ≤ D.R0 m ∧ D.R0 m ≤ 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h := D.R0_sub_one_le hm
  rw [abs_le] at h
  have hbd : 16 * D.c * D.tau / (m : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hmpos]; linarith
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end Bound

end Decay

end GFNBounds.Doubling
