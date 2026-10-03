import GFNBounds.Doubling.PhaseRecurrence
import GFNBounds.Graph.Leakage

/-!
# The doubling graph leaks: the sampler on a transient row

`Graph.Leakage.sampler_leaks` says what the sampler of a flow of a frozen backward policy does on
any countable state space: it stops at `x` with probability `Zρ(x)h(x)/m`, `h` the probability that
the backward walk reaches the source. This file reads it on the doubling graph of
`def:doubling_setting`, at the loop closure (`cap = none`), and identifies the stopping probability
with the return probability of the backward chain to the source: `⟨ρ,h⟩ = P_{s₀}(τ⁺_{s₀} < ∞)`. On
a transient row of the family that is below one, so the sampler of every flow at matched mass
escapes with positive probability.

The internal states are the rungs `j ≥ 1`, indexed by `i ↦ j = i + 1`. From the rung `i + 1` the
backward chain doubles to the rung `2(i + 1)` with probability `ε(i + 1)` and steps down to the rung
`i` otherwise; the rung `0` is the source, so the step to the source is the step down from the
lowest rung. The sink row is the target row.

## What is proved

| | |
|---|---|
| **`absorbN_eq`** | `(Qⁿk)(i) = P_{i+1}(τ_{s₀} = n + 1)`, the first-passage law of `RecurrenceClass` |
| **`absorb_eq`** | `h(i) = P_{i+1}(τ_{s₀} < ∞)`, the least solution `hitProb` of the hitting recursion |
| **`tsum_rho_absorb`** | `⟨ρ,h⟩ = P_{s₀}(τ⁺_{s₀} < ∞)`, the return probability `retProb` of the source |
| **`sampler_leaks_doubling`** | for every flow of the frozen family, the sampler stops with probability `Z·P_{s₀}(τ⁺_{s₀} < ∞)/m`, and `m ≥ Z·P_{s₀}(τ⁺_{s₀} < ∞)` |
| **`retProb_src_lt_one`** | on the transient rows of the family, `s < 1`, or `s = 1` and `c > 1/ln 2`, the return probability is below one |
| **`sampler_escapes_doubling`** | on those rows the sampler of every flow at matched mass stops with probability `P_{s₀}(τ⁺_{s₀} < ∞) < 1`, and escapes otherwise |

## Hypothesis checklist

| hypothesis | here |
|---|---|
| the loop closure of the doubling graph | `cap = none`; every doubling edge present (`hasDouble_none`) |
| the frozen backward policy | `Q`, `k`, `ρ` below, read off `pstar` and the target row |
| a flow of the frozen family | `μ : ℕ → ℝ≥0∞`, positive and finite on every rung, balanced: `μ = μQ + Zρ` |
| the family `ε = ε_{c,s}` | `epsCS c s`, `0 < c`, through `main_phase_classes` |

## SCOPE (disclosed)

* **Matched mass is a hypothesis here.** `sampler_escapes_doubling` holds for every flow of the
  frozen family whose initial mass equals its terminal mass. Such a flow exists on every row: it is
  built by the cut balance in `Doubling/MatchedFlow.lean` (`exists_matched_flow`,
  `exists_escaping_flow`). The general statement, `sampler_leaks_doubling`, holds for every flow,
  at every initial mass.
* **Probabilities are least solutions**, as throughout `RecurrenceClass`: no path space is built,
  as in `Graph.Leakage`, whose sampler is its sequence of laws.
* **No `sorry`.**

Provenance: mathlib tag `v4.31.0`, pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open scoped ENNReal
open Filter Topology

namespace Leak

variable (S : Setting)

/-- **The backward step among the rungs.** From the rung `i + 1` to the rung `2(i + 1)` with
probability `ε(i + 1)`, and to the rung `i` with probability `1 − ε(i + 1)` when `i ≥ 1`. -/
noncomputable def Q (i i' : ℕ) : ℝ≥0∞ :=
  (if i' = 2 * i + 1 then ENNReal.ofReal (S.eps (i + 1)) else 0)
    + (if i' + 1 = i then ENNReal.ofReal (1 - S.eps (i + 1)) else 0)

/-- **The backward step to the source**, from the lowest rung only. -/
noncomputable def k (i : ℕ) : ℝ≥0∞ := if i = 0 then ENNReal.ofReal (1 - S.eps 1) else 0

/-- **The sink row**: the target row. -/
noncomputable def ρ (i : ℕ) : ℝ≥0∞ := ENNReal.ofReal (S.row (i + 1))

variable {S}

theorem lad_ne_src {j : ℕ} (hj : j ≠ 0) : St.lad j ≠ St.src := by
  intro h
  exact hj (St.lad.inj h)

theorem lad_succ_ne_src (i : ℕ) : St.lad (i + 1) ≠ St.src := lad_ne_src (Nat.succ_ne_zero i)

theorem pstar_lad_none (f : St → ℝ) (i : ℕ) :
    pstar S none f (St.lad (i + 1))
      = S.eps (i + 1) * f (St.lad (2 * i + 1 + 1)) + (1 - S.eps (i + 1)) * f (St.lad i) := by
  rw [pstar_lad_succ, if_pos (hasDouble_none _)]
  have h2 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
  rw [h2]

theorem eps_nonneg (i : ℕ) : 0 ≤ S.eps (i + 1) := (S.eps_pos (by omega)).le

theorem one_sub_eps_nonneg (i : ℕ) : 0 ≤ 1 - S.eps (i + 1) := by
  have h := S.eps_le (show 1 ≤ i + 1 by omega)
  linarith [S.epsMax_lt_one]

/-- **The backward absorption read as a first passage**: `(Qⁿk)(i) = P_{i+1}(τ_{s₀} = n + 1)`. -/
theorem absorbN_eq (n i : ℕ) :
    Graph.Leakage.absorbN (Q S) (k S) n i
      = ENNReal.ofReal (fpass S none St.src (n + 1) (St.lad (i + 1))) := by
  induction n generalizing i with
  | zero =>
    show k S i = _
    rw [fpass_succ_of_ne (lad_succ_ne_src i), fpass_zero, pstar_lad_none,
      ptFn_of_ne (lad_succ_ne_src (2 * i + 1))]
    cases i with
    | zero => simp [k, ptFn]
    | succ j => simp [k, ptFn_of_ne (lad_succ_ne_src j)]
  | succ n ih =>
    have hdown : ∀ i' : ℕ, i' ≠ 2 * i + 1 →
        (if i' = 2 * i + 1 then ENNReal.ofReal (S.eps (i + 1)) else 0)
          * Graph.Leakage.absorbN (Q S) (k S) n i' = 0 := by
      intro i' h
      rw [if_neg h, zero_mul]
    have hsplit : Graph.Leakage.absorbN (Q S) (k S) (n + 1) i
        = ENNReal.ofReal (S.eps (i + 1)) * Graph.Leakage.absorbN (Q S) (k S) n (2 * i + 1)
          + ∑' i', (if i' + 1 = i then ENNReal.ofReal (1 - S.eps (i + 1)) else 0)
              * Graph.Leakage.absorbN (Q S) (k S) n i' := by
      show ∑' i', Q S i i' * Graph.Leakage.absorbN (Q S) (k S) n i' = _
      simp only [Q, add_mul]
      rw [ENNReal.tsum_add, tsum_eq_single (2 * i + 1) hdown, if_pos rfl]
    rw [hsplit, fpass_succ_of_ne (lad_succ_ne_src i), pstar_lad_none, ih (2 * i + 1),
      ENNReal.ofReal_add (mul_nonneg (eps_nonneg i) (fpass_nonneg _ _))
        (mul_nonneg (one_sub_eps_nonneg i) (fpass_nonneg _ _)),
      ENNReal.ofReal_mul (eps_nonneg i)]
    congr 1
    cases i with
    | zero =>
      have hz : ∀ i' : ℕ, (if i' + 1 = 0 then ENNReal.ofReal (1 - S.eps (0 + 1)) else 0)
          * Graph.Leakage.absorbN (Q S) (k S) n i' = 0 := by
        intro i'
        rw [if_neg (Nat.succ_ne_zero i'), zero_mul]
      rw [tsum_congr hz, tsum_zero]
      have hsrc : fpass S none St.src (n + 1) (St.lad 0) = 0 := fpass_succ_self n
      rw [hsrc, mul_zero, ENNReal.ofReal_zero]
    | succ j =>
      have hj : ∀ i' : ℕ, i' ≠ j →
          (if i' + 1 = j + 1 then ENNReal.ofReal (1 - S.eps (j + 1 + 1)) else 0)
            * Graph.Leakage.absorbN (Q S) (k S) n i' = 0 := by
        intro i' h
        rw [if_neg (by omega), zero_mul]
      rw [tsum_eq_single j hj, if_pos rfl, ih j, ENNReal.ofReal_mul (one_sub_eps_nonneg (j + 1))]

/-- **The absorption probability is the hitting probability of the source**:
`h(i) = P_{i+1}(τ_{s₀} < ∞)`. -/
theorem absorb_eq (i : ℕ) :
    Graph.Leakage.absorb (Q S) (k S) i
      = ENNReal.ofReal (hitProb S none St.src (St.lad (i + 1))) := by
  have hx : St.lad (i + 1) ≠ St.src := lad_succ_ne_src i
  have hf0 : ∀ n, 0 ≤ fpass S none St.src (n + 1) (St.lad (i + 1)) := fun n => fpass_nonneg _ _
  have hpart : ∀ N, ∑ n ∈ Finset.range N, fpass S none St.src (n + 1) (St.lad (i + 1))
      = hitP S none St.src N (St.lad (i + 1)) := by
    intro N
    rw [hitP, Finset.sum_range_succ', fpass_zero, ptFn_of_ne hx, add_zero]
  have hsum : Summable fun n => fpass S none St.src (n + 1) (St.lad (i + 1)) :=
    summable_of_sum_range_le hf0 fun N => by rw [hpart N]; exact hitP_le_one N _
  have hlim : ∑' n, fpass S none St.src (n + 1) (St.lad (i + 1))
      = hitProb S none St.src (St.lad (i + 1)) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    simp only [hpart] at h1
    exact tendsto_nhds_unique h1 (tendsto_hitP _)
  unfold Graph.Leakage.absorb
  simp only [absorbN_eq]
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hsum, hlim]

/-- **The stopping probability is the return probability of the source**:
`⟨ρ,h⟩ = P_{s₀}(τ⁺_{s₀} < ∞)`. -/
theorem tsum_rho_absorb :
    ∑' i, ρ S i * Graph.Leakage.absorb (Q S) (k S) i
      = ENNReal.ofReal (retProb S none St.src) := by
  have hret : retProb S none St.src
      = ∑ j ∈ Finset.range S.d, S.row (j + 1) * hitProb S none St.src (St.lad (j + 1)) := by
    have hsink : St.sink ≠ St.src := by intro h; cases h
    have hI : Finset.Icc 1 S.d = Finset.Ico 1 (S.d + 1) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [retProb, pstar_src, hitProb_solution hsink, pstar_sink, hI,
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_comm 1 j]
  have hsupp : ∀ i ∉ Finset.range S.d, ρ S i * Graph.Leakage.absorb (Q S) (k S) i = 0 := by
    intro i hi
    have hrow : S.row (i + 1) = 0 := by
      by_contra h
      have := (S.row_supp h).2
      rw [Finset.mem_range] at hi
      omega
    rw [ρ, hrow, ENNReal.ofReal_zero, zero_mul]
  rw [tsum_eq_sum hsupp, hret,
    ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (S.row_nonneg _) (hitProb_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [absorb_eq, ρ, ← ENNReal.ofReal_mul (S.row_nonneg _)]

/-- **The doubling graph leaks.** For every flow of the frozen family on the loop closure of the
doubling graph, the sampler stops with probability `Z·P_{s₀}(τ⁺_{s₀} < ∞)/m`, and the initial mass
is at least `Z·P_{s₀}(τ⁺_{s₀} < ∞)`. -/
theorem sampler_leaks_doubling {μ : ℕ → ℝ≥0∞} {m Z : ℝ≥0∞}
    (hμ0 : ∀ y, μ y ≠ 0) (hμt : ∀ y, μ y ≠ ∞)
    (hbal : ∀ y, μ y = (∑' x, μ x * Q S x y) + Z * ρ S y)
    (hm : m = ∑' x, μ x * k S x) (hm0 : m ≠ 0) (hmt : m ≠ ∞) :
    (∑' i, Graph.Leakage.stopLaw (Q S) (k S) μ m Z (ρ S) i)
        = Z * ENNReal.ofReal (retProb S none St.src) / m
      ∧ Z * ENNReal.ofReal (retProb S none St.src) ≤ m := by
  obtain ⟨-, htot, -, hle⟩ := Graph.Leakage.sampler_leaks hμ0 hμt hbal hm hm0 hmt
  rw [tsum_rho_absorb] at htot hle
  exact ⟨htot, hle⟩

/-- **The transient rows**: for `ε = ε_{c,s}` with `s < 1`, or `s = 1` and `c > 1/ln 2`, the
backward chain started at the source returns to it with probability below one. -/
theorem retProb_src_lt_one {c s : ℝ} (hc : 0 < c) (hS : ∀ j, S.eps j = epsCS c s j)
    (hrow : s < 1 ∨ (s = 1 ∧ 1 / Real.log 2 < c)) :
    retProb S none St.src < 1 := by
  obtain ⟨-, htr1, -, -, -, htr2, -⟩ := main_phase_classes hc hS
  have htr : IsTransient S none := by
    rcases hrow with h | ⟨h1, h2⟩
    · exact htr1 h
    · exact htr2 h1 h2
  exact htr St.src (onChain_none _)

/-- **On a transient row the sampler escapes.** For every flow of the frozen family at matched
mass, `m = Z`, the sampler stops with probability `P_{s₀}(τ⁺_{s₀} < ∞)`, which is below one. -/
theorem sampler_escapes_doubling {c s : ℝ} (hc : 0 < c) (hS : ∀ j, S.eps j = epsCS c s j)
    (hrow : s < 1 ∨ (s = 1 ∧ 1 / Real.log 2 < c))
    {μ : ℕ → ℝ≥0∞} {Z : ℝ≥0∞}
    (hμ0 : ∀ y, μ y ≠ 0) (hμt : ∀ y, μ y ≠ ∞)
    (hbal : ∀ y, μ y = (∑' x, μ x * Q S x y) + Z * ρ S y)
    (hm : Z = ∑' x, μ x * k S x) (hZ0 : Z ≠ 0) (hZt : Z ≠ ∞) :
    (∑' i, Graph.Leakage.stopLaw (Q S) (k S) μ Z Z (ρ S) i)
        = ENNReal.ofReal (retProb S none St.src)
      ∧ (∑' i, Graph.Leakage.stopLaw (Q S) (k S) μ Z Z (ρ S) i) < 1 := by
  obtain ⟨-, htot⟩ := Graph.Leakage.sampler_leaks_matched hμ0 hμt hbal hm hZ0 hZt
  rw [tsum_rho_absorb] at htot
  refine ⟨htot, ?_⟩
  rw [htot]
  exact ENNReal.ofReal_lt_one.mpr (retProb_src_lt_one hc hS hrow)

end Leak

end GFNBounds.Doubling
