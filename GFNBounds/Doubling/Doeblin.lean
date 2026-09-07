import GFNBounds.Doubling.DescentLaw
import GFNBounds.Doubling.HarmonicWindow

/-!
# `lem:doubling_doeblin`: the exit from a block charges a fixed fraction of one reference law

**`lem:doubling_doeblin`** — `app_doubling.tex:1385–1473`.

> In the setting of Definitions `def:doubling_setting` and `def:doubling_decay_notation`, with the
> integer `ℓ₃` of `lem:doubling_weight`, put `ω := (c²/16) ln(5/4) ln(8/5)`, which lies in `(0,1)`
> and depends on `c` alone. Then there is an integer `ℓ₄ ≥ ℓ₃`, depending on `c` and `d` alone,
> with the following property. Let `ℓ ≥ ℓ₄` and `i ≥ 1` be integers, write `a := 2^{i−1}ℓ`, so
> that `I_{i−1}(ℓ) = [a,2a)` and `I_i(ℓ) = [2a,4a)`, and let `ϖ_i` be the probability on the
> integers of `[⌈5a/4⌉,2a)` proportional to `j ↦ 1/(j+1)`. Let `(Y_n)` be the descent chain at the
> level `ℓ` and `ς := inf{n ≥ 0 : Y_n ∉ I_i(ℓ)}` its exit time from `I_i(ℓ)`. Then, for every
> state `y ∈ I_i(ℓ)`, `ς ≤ y` and `Y_ς ∈ I_{i−1}(ℓ)` almost surely, and
> `P(Y_ς = j | Y_0 = y) ≥ ω ϖ_i(j)` for every integer `j`.

## The modelling decision, and what `ℓ₄` is here

The chain's exit law from `I_i(ℓ) = [2a,4a)` is, in the representation of `DescentLaw.lean`,
the exit law of the **descent at the level `a`**: `μ_y = exitLaw a y`. That is the content of
"`ς ≤ N_ℓ` and `Y_ς ∈ I_{i−1}(ℓ)`", and here it holds by construction rather than by an argument
— `exitLaw a` is carried by `[a,2a)` (`DescentLaw.exitLaw_sum`) and the recursion terminates
(`lem:doubling_descent`(1), which is `window_lt`). So the two "almost surely" claims of the
statement are not separate theorems here; they are the typing of `exitLaw`.

What is left is the arithmetic, and it is done with **explicit constants**:

  `ω = (c²/16) ln(5/4) ln(8/5)`,  exactly the paper's, and `ω ≥ 3c²/640 > 0`.

The paper's `ℓ₄ = max(ℓ₃, ⌈4/ln(5/4)⌉)` becomes the pair of hypotheses `20 ≤ a` and `32cτ ≤ a`:
the first replaces `⌈4/ln(5/4)⌉ = 18` (see `HarmonicWindow.lean` — `ln(5/4) ≥ 1/5` is used in
place of a decimal expansion, so the threshold rises from 18 to 20), and the second is `ℓ₁` of
`R0Bound.lean`, which is where `R₀(z) ≤ 2` comes from. Both are **effective**, and `ℓ₃` — which
the paper inherits from the non-effective `c₄`, `γ`, `c₅`, `ℓ₂` — does not appear.

## SCOPE (disclosed)

* Stated at a level `a` with `20 ≤ a` and `32cτ ≤ a` directly, rather than at `a = 2^{i−1}ℓ` with
  `ℓ ≥ ℓ₄`; `Coupling.lean` supplies `a = 2^{i−1}ℓ ≥ ℓ` and both hypotheses follow.
* `ς ≤ y` is not stated. It is the recursion's termination, already carried by `descP`'s
  well-foundedness, and nothing downstream in the sharp block uses the bound on `ς` itself.
* `ℓ₃` and hence `lem:doubling_weight` are **not** inputs here. The paper's `ℓ₄ ≥ ℓ₃` couples the
  two only so that one level serves both lemmas; `Sharp.lean` re-imposes that coupling.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `0 < c < 1` | ✓ carried (`Decay`) |
| `s = 1`, `p = p_*` | ✓ carried (`Decay`) |
| `ℓ ≥ ℓ₄ ≥ ⌈4/ln(5/4)⌉ = 18` | ⚠ **strengthened** to `20 ≤ a`, for effectivity (see above) |
| `ℓ ≥ ℓ₄ ≥ ℓ₃ ≥ ℓ₂ ≥ 2ℓ₁`, giving `R₀(z) ≤ 2` | ⚠ **replaced** by the effective `32cτ ≤ a` of `R0Bound.lean` |
| `ℓ ≥ ℓ₄ ≥ ℓ₃`, coupling to `lem:doubling_weight` | ⚠ not carried here; `Sharp.lean` carries it |
| `i ≥ 1`, `a = 2^{i−1}ℓ` | ⚠ weakened to `a` arbitrary subject to the two bounds |
| `ϖ_i` the probability on `[⌈5a/4⌉,2a)` proportional to `1/(j+1)` | ✓ carried (`Decay.varpi`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

variable (D : Decay)

/-- **`ω := (c²/16) ln(5/4) ln(8/5)`**, the minorization constant of `lem:doubling_doeblin`. -/
noncomputable def omeg : ℝ := D.c ^ 2 / 16 * Real.log (5 / 4) * Real.log (8 / 5)

/-- `ω > 0`. -/
theorem omeg_pos : 0 < D.omeg := by
  have h3 : (0 : ℝ) < D.c ^ 2 / 16 := div_pos (pow_pos D.c_pos 2) (by norm_num)
  rw [omeg]
  exact mul_pos (mul_pos h3 log_five_four_pos) log_eight_five_pos

/-- **An effective lower bound**: `ω ≥ 3c²/640`, from `ln(5/4) ≥ 1/5` and `ln(8/5) ≥ 3/8`. -/
theorem omeg_ge : 3 * D.c ^ 2 / 640 ≤ D.omeg := by
  have h1 := log_five_four_ge
  have h2 := log_eight_five_ge
  have hL : (3 : ℝ) / 40 ≤ Real.log (5 / 4) * Real.log (8 / 5) := by
    nlinarith [log_five_four_pos, log_eight_five_pos]
  have ht : (0 : ℝ) < D.c ^ 2 / 16 := div_pos (pow_pos D.c_pos 2) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hL ht.le
  rw [omeg, mul_assoc]
  linarith [hmul]

/-- `ω < 1`, since `c < 1`, `ln(5/4) < 1` and `ln(8/5) < 1`. -/
theorem omeg_lt_one : D.omeg < 1 := by
  have hc2 : D.c ^ 2 / 16 ≤ 1 / 16 := by nlinarith [D.c_pos, D.c_lt_one]
  have e1 : D.c ^ 2 / 16 * Real.log (5 / 4) ≤ 1 / 16 :=
    le_trans (mul_le_mul_of_nonneg_right hc2 log_five_four_pos.le)
      (by linarith [log_five_four_lt_one])
  rw [omeg]
  calc D.c ^ 2 / 16 * Real.log (5 / 4) * Real.log (8 / 5)
      ≤ (1 / 16) * Real.log (8 / 5) := mul_le_mul_of_nonneg_right e1 log_eight_five_pos.le
    _ < 1 := by linarith [log_eight_five_lt_one]

/-- `(c/4) ln(5/4) ≤ 1`, so `ω ≤ (c/4) ln(8/5)`: the two cases of the proof combine. -/
theorem omeg_le_case_one : D.omeg ≤ D.c / 4 * Real.log (8 / 5) := by
  have hfac : D.c / 4 * Real.log (5 / 4) ≤ 1 := by
    nlinarith [D.c_pos, D.c_lt_one, log_five_four_pos, log_five_four_lt_one]
  have hpos : 0 ≤ D.c / 4 * Real.log (8 / 5) := by
    have := log_eight_five_pos
    have := D.c_pos
    positivity
  have hid : D.omeg = (D.c / 4 * Real.log (5 / 4)) * (D.c / 4 * Real.log (8 / 5)) := by
    rw [omeg]; ring
  rw [hid]
  calc (D.c / 4 * Real.log (5 / 4)) * (D.c / 4 * Real.log (8 / 5))
      ≤ 1 * (D.c / 4 * Real.log (8 / 5)) := mul_le_mul_of_nonneg_right hfac hpos
    _ = D.c / 4 * Real.log (8 / 5) := one_mul _

/-! ## The reference law `ϖ_i` -/

/-- `ϖ_i`, the probability on the integers of `[⌈5a/4⌉,2a)` proportional to `j ↦ 1/(j+1)`. -/
noncomputable def varpi (a j : ℕ) : ℝ :=
  (if j ∈ Jlow a then 1 / ((j : ℝ) + 1) else 0) / ∑ j' ∈ Jlow a, 1 / ((j' : ℝ) + 1)

theorem varpi_nonneg {a : ℕ} (ha : 20 ≤ a) (j : ℕ) : 0 ≤ varpi a j := by
  rw [varpi]
  refine div_nonneg ?_ (sum_Jlow_pos ha).le
  by_cases h : j ∈ Jlow a
  · rw [if_pos h]; positivity
  · rw [if_neg h]

theorem varpi_of_not_mem {a j : ℕ} (h : j ∉ Jlow a) : varpi a j = 0 := by
  rw [varpi, if_neg h, zero_div]

/-- `ϖ_i` is a probability on `I_{i−1}(ℓ) = [a,2a)`. -/
theorem varpi_sum {a : ℕ} (ha : 20 ≤ a) : ∑ z ∈ Finset.Ico a (2 * a), varpi a z = 1 := by
  have hS := sum_Jlow_pos ha
  have hstep : ∑ z ∈ Finset.Ico a (2 * a), varpi a z
      = (∑ z ∈ Finset.Ico a (2 * a), if z ∈ Jlow a then 1 / ((z : ℝ) + 1) else 0)
        / ∑ j' ∈ Jlow a, 1 / ((j' : ℝ) + 1) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun z _ => rfl
  have hmem : (∑ z ∈ Finset.Ico a (2 * a), if z ∈ Jlow a then 1 / ((z : ℝ) + 1) else 0)
      = ∑ z ∈ Jlow a, 1 / ((z : ℝ) + 1) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Jlow_subset a)]
  rw [hstep, hmem, div_self hS.ne']

/-- `ϖ_i(j) ≤ 2/(ln(8/5)(j+1))` on `J`: the normalising sum is at least `½ ln(8/5)`. -/
theorem varpi_le {a : ℕ} (ha : 20 ≤ a) (j : ℕ) :
    D.c / 4 * Real.log (8 / 5) * varpi a j ≤ D.c / (2 * ((j : ℝ) + 1)) := by
  by_cases h : j ∈ Jlow a
  · have hSpos := sum_Jlow_pos ha
    set S : ℝ := ∑ j' ∈ Jlow a, 1 / ((j' : ℝ) + 1) with hSdef
    have hS : (1 / 2) * Real.log (8 / 5) ≤ S := sum_Jlow_half ha
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hv : varpi a j = (1 / ((j : ℝ) + 1)) / S := by rw [varpi, if_pos h]
    have hkey : D.c / 4 * Real.log (8 / 5) ≤ D.c / 2 * S := by
      have hmul := mul_le_mul_of_nonneg_left hS (by linarith [D.c_pos] : (0 : ℝ) ≤ D.c / 2)
      linarith [hmul]
    have hle : D.c / 4 * Real.log (8 / 5) / S ≤ D.c / 2 := (div_le_iff₀ hSpos).mpr hkey
    have hrw : D.c / 4 * Real.log (8 / 5) * (1 / ((j : ℝ) + 1) / S)
        = (D.c / 4 * Real.log (8 / 5) / S) * (1 / ((j : ℝ) + 1)) := by
      field_simp
    have hrw2 : D.c / (2 * ((j : ℝ) + 1)) = (D.c / 2) * (1 / ((j : ℝ) + 1)) := by
      rw [div_mul_div_comm, mul_one]
    rw [hv, hrw, hrw2]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  · rw [varpi_of_not_mem h, mul_zero]
    have hc := D.c_pos
    positivity

/-! ## `eq:doubling_doeblin` -/

section Doeblin

variable {a : ℕ}

/-- `R₀(z) ≤ 2` at every state of the two blocks in play. -/
theorem R0_le_two_of (haτ : 32 * D.c * D.tau ≤ (a : ℝ)) (ha : 20 ≤ a) {z : ℕ} (hz : a ≤ z) :
    D.R0 z ≤ 2 := by
  have hz1 : 1 ≤ z := by omega
  have hcast : (a : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  exact (D.R0_between hz1 (le_trans haτ hcast)).2

/-- **Third bullet of `lem:doubling_doeblin`.** A state `y ∈ I_i(ℓ)` below `⌈5a/2⌉` leaves the
block, in one step, with law at least `(c/4)ln(8/5) ϖ_i`. -/
theorem doeblin_low (ha : 20 ≤ a) (haτ : 32 * D.c * D.tau ≤ (a : ℝ))
    {y : ℕ} (h1 : 2 * a ≤ y) (h2 : y < (5 * a + 1) / 2) (j : ℕ) :
    D.c / 4 * Real.log (8 / 5) * varpi a j ≤ D.exitLaw a y j := by
  have ha1 : 1 ≤ a := by omega
  have hy2 : 2 ≤ y := by omega
  have hylt : ¬ y < 2 * a := by omega
  have hyge : 2 * a ≤ y := h1
  have hnn : ∀ z ∈ window y, 0 ≤ D.kern y z * D.exitLaw a z j := by
    intro z hz
    exact mul_nonneg (D.kern_nonneg hy2 hz)
      (D.exitLaw_nonneg ha1 j z (le_of_mem_window_of_ge hyge hz))
  by_cases hj : j ∈ Jlow a
  · -- `j ∈ J ⊆ W(y)`, and a first step into `J` is already the exit
    have hjw : j ∈ window y := Jlow_subset_window h1 h2 hj
    have hjmem : j ∈ Finset.Ico a (2 * a) := Jlow_subset a hj
    have hjlt : j < 2 * a := (Finset.mem_Ico.mp hjmem).2
    have hself : D.exitLaw a j j = 1 := by rw [D.exitLaw_of_lt hjlt, if_pos rfl]
    have hsingle : D.kern y j * D.exitLaw a j j
        ≤ ∑ z ∈ window y, D.kern y z * D.exitLaw a z j :=
      Finset.single_le_sum hnn hjw
    rw [hself, mul_one] at hsingle
    have hkern : D.c / (2 * ((j : ℝ) + 1)) ≤ D.kern y j :=
      D.kern_ge hy2 (D.R0_le_two_of haτ ha (by omega)) hjw
    rw [D.exitLaw_of_ge hylt j]
    exact le_trans (le_trans (D.varpi_le ha j) hkern) hsingle
  · rw [varpi_of_not_mem hj, mul_zero]
    exact D.exitLaw_nonneg ha1 j y (by omega)

/-- **`eq:doubling_doeblin`.** Every state of `I_i(ℓ) = [2a,4a)` leaves the block with law at
least `ω ϖ_i`. -/
theorem doeblin (ha : 20 ≤ a) (haτ : 32 * D.c * D.tau ≤ (a : ℝ))
    {y : ℕ} (h1 : 2 * a ≤ y) (h2 : y < 4 * a) (j : ℕ) :
    D.omeg * varpi a j ≤ D.exitLaw a y j := by
  have ha1 : 1 ≤ a := by omega
  by_cases hcase : y < (5 * a + 1) / 2
  · exact le_trans (mul_le_mul_of_nonneg_right D.omeg_le_case_one (varpi_nonneg ha j))
      (D.doeblin_low ha haτ h1 hcase j)
  · -- the second case: step into `J'`, then apply the first case at each of its states
    have hcase' : (5 * a + 1) / 2 ≤ y := by omega
    have hy2 : 2 ≤ y := by omega
    have hylt : ¬ y < 2 * a := by omega
    have hsub : Jhigh a ⊆ window y := Jhigh_subset_window hcase' h2
    set K : ℝ := D.c / 4 * Real.log (8 / 5) with hK
    have hKnn : 0 ≤ K := by
      have := log_eight_five_pos
      have := D.c_pos
      rw [hK]; positivity
    have hvnn : 0 ≤ varpi a j := varpi_nonneg ha j
    have hnn : ∀ z ∈ window y, 0 ≤ D.kern y z * D.exitLaw a z j := by
      intro z hz
      exact mul_nonneg (D.kern_nonneg hy2 hz)
        (D.exitLaw_nonneg ha1 j z (le_of_mem_window_of_ge h1 hz))
    -- restrict to `J'`
    have hrestrict : ∑ z ∈ Jhigh a, D.kern y z * D.exitLaw a z j
        ≤ ∑ z ∈ window y, D.kern y z * D.exitLaw a z j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun z hz _ => hnn z hz
    -- on `J'` the first case applies
    have hstep : ∀ z ∈ Jhigh a,
        D.c / (2 * ((z : ℝ) + 1)) * (K * varpi a j) ≤ D.kern y z * D.exitLaw a z j := by
      intro z hz
      rw [mem_Jhigh] at hz
      have hzmem : z ∈ window y := hsub (mem_Jhigh.mpr hz)
      have hz4 : z < 4 * a := by omega
      have hkz : D.c / (2 * ((z : ℝ) + 1)) ≤ D.kern y z :=
        D.kern_ge hy2 (D.R0_le_two_of haτ ha (by omega)) hzmem
      have hez : K * varpi a j ≤ D.exitLaw a z j := D.doeblin_low ha haτ hz.1 hz.2 j
      have hcz : 0 ≤ D.c / (2 * ((z : ℝ) + 1)) := by
        have := D.c_pos; positivity
      exact mul_le_mul hkz hez (mul_nonneg hKnn hvnn) (le_trans hcz hkz)
    have hsum1 : ∑ z ∈ Jhigh a, D.c / (2 * ((z : ℝ) + 1)) * (K * varpi a j)
        ≤ ∑ z ∈ Jhigh a, D.kern y z * D.exitLaw a z j := Finset.sum_le_sum hstep
    -- the window sum on `J'`
    have hsplit : ∑ z ∈ Jhigh a, D.c / (2 * ((z : ℝ) + 1))
        = D.c / 2 * ∑ z ∈ Jhigh a, 1 / ((z : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [div_mul_div_comm, mul_one]
    have hfac : ∑ z ∈ Jhigh a, D.c / (2 * ((z : ℝ) + 1)) * (K * varpi a j)
        = (D.c / 2 * ∑ z ∈ Jhigh a, 1 / ((z : ℝ) + 1)) * (K * varpi a j) := by
      rw [← hsplit, Finset.sum_mul]
    have hJ := sum_Jhigh_half (a := a) (by omega)
    have hlow : D.c / 4 * Real.log (5 / 4) ≤ D.c / 2 * ∑ z ∈ Jhigh a, 1 / ((z : ℝ) + 1) := by
      have hc := D.c_pos
      nlinarith [hJ, hc]
    have homeg : D.omeg * varpi a j
        ≤ (D.c / 2 * ∑ z ∈ Jhigh a, 1 / ((z : ℝ) + 1)) * (K * varpi a j) := by
      have hid : D.omeg * varpi a j = (D.c / 4 * Real.log (5 / 4)) * (K * varpi a j) := by
        rw [omeg, hK]; ring
      rw [hid]
      exact mul_le_mul_of_nonneg_right hlow (mul_nonneg hKnn hvnn)
    rw [D.exitLaw_of_ge hylt j]
    calc D.omeg * varpi a j
        ≤ (D.c / 2 * ∑ z ∈ Jhigh a, 1 / ((z : ℝ) + 1)) * (K * varpi a j) := homeg
      _ = ∑ z ∈ Jhigh a, D.c / (2 * ((z : ℝ) + 1)) * (K * varpi a j) := hfac.symm
      _ ≤ ∑ z ∈ Jhigh a, D.kern y z * D.exitLaw a z j := hsum1
      _ ≤ ∑ z ∈ window y, D.kern y z * D.exitLaw a z j := hrestrict

end Doeblin

end Decay

end GFNBounds.Doubling
