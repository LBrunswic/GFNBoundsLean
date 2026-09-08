import GFNBounds.Doubling.Tail
import GFNBounds.Doubling.Unbounded

/-!
# An explicit divergent family: the `√m` rate

**`cor:doubling_family`** — `app_doubling.tex:2087–2124`.

> Let `s = 1` and `0 < c < 1`, so that the loop-closed chain is positive recurrent and `λ`, `L`
> and the centred tail indicators `f_m` are those of `def:doubling_setting`. Then there are
> `c₇ > 0` and an integer `m₂ > d` with
> `‖f_m‖_{L²(λ)} / ‖(Id − P⋆)f_m‖_{L²(λ)} ≥ c₇ √m` for every `m ≥ m₂`.

## The chain of inputs, and what is assumed

`c₁ m λ_m ≤ c₂(p−1) L(m)` (`Decay.tail_ratio_ge`, from `eq:doubling_decay`) meets
`‖(Id−P⋆)f_m‖² ≤ 2λ_m` and `‖f_m‖² = L(1−L)` (`lem:doubling_percut`), and `1 − L(m) ≥ ½` past
`m₂` (`Stat.tailMass_tendsto_zero`). The two-sided decay `eq:doubling_decay` itself is a
hypothesis here, so `exists_rayleigh_family` is conditional on the pair `(c₁,c₂)`;
`theo:doubling_decay` supplies it unconditionally (`Decay.decay_two_sided_of_cutBal`,
`Product.lean`), and `main_rate` in `Main.lean` is the corollary with that hypothesis
discharged — the paper's unconditional statement.

## SCOPE (disclosed)

* Stated in the **squared, denominator-free** form `c₁ m ‖(Id−P⋆)f_m‖² ≤ 4c₂(p−1) ‖f_m‖²`, which
  is `eq:doubling_explicit` squared and cleared: `c₇ = √(c₁/(4c₂(p−1)))`. The square root is not
  taken, so no positivity side condition on the denominator is needed at the point of use.
* Positive recurrence is the hypothesis `Stat S none`, not a conclusion: `prop:doubling_phase`
  row (b) supplies it (`exists_stat_of_family`, `StatExists.lean`).

## Hypothesis checklist against `cor:doubling_family`

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1` | ⚠ weakened: `D : Decay` supplies only `p`; no `heps` ties `S.eps` to the family, so the statement holds for every `Setting` and every `λ` with the two-sided decay |
| positive recurrence, `λ` | ✓ carried as `Stat S none` |
| `eq:doubling_decay` with `0 < c₁ ≤ c₂` | ✓ carried as hypotheses (`theo:doubling_decay` is its source) |
| `m ≥ m₂ > d` | ✓ carried |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting}

namespace Stat

variable (L : Stat S none)

/-- The bridge: on the loop closure the tail of `λ` as a sequence is `Stat.tailMass`. -/
theorem tailSeq_eq_tailMass (m : ℕ) :
    tailSeq (fun j => L.lam (.lad j)) m = L.tailMass m :=
  (L.hasSum_tailShift m).tsum_eq

/-- **`eq:doubling_explicit`, squared and cleared of denominators.**
`c₁ m ‖(Id−P⋆)f_m‖²_{L²(λ)} ≤ 4c₂(p−1) ‖f_m‖²_{L²(λ)}`, i.e. the Rayleigh quotient of the centred
tail indicator at the cut `m` is `O(1/m)` and its reciprocal is `Ω(√m)` after taking roots. -/
theorem rayleigh_family (D : Decay) {c₁ c₂ : ℝ} (hc1 : 0 < c₁)
    (hbelow : ∀ j : ℕ, 1 ≤ j → c₁ * (j : ℝ) ^ (-D.p) ≤ L.lam (.lad j))
    (habove : ∀ j : ℕ, 1 ≤ j → L.lam (.lad j) ≤ c₂ * (j : ℝ) ^ (-D.p))
    {m : ℕ} (hdm : S.d < m) (hhalf : (1 : ℝ) / 2 ≤ 1 - L.tailMass m) :
    c₁ * (m : ℝ) * L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
      ≤ 4 * c₂ * (D.p - 1) * L.mass 2 (L.centredTail m) := by
  have hp := D.p_gt_one
  have hp1 : (0 : ℝ) < D.p - 1 := by linarith
  have hm1 : 1 ≤ m := by have := S.d_pos; omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmp : (0 : ℝ) < (m : ℝ) ^ (-D.p) := rpow_pos_of_pos hmpos _
  have hc2pos : 0 < c₂ := by
    have h1 := hbelow m hm1
    have h2 := habove m hm1
    nlinarith [hmp, hc1]
  -- the numerator
  have hnum : L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
      ≤ 2 * L.lam (.lad m) := L.mass_defect_le hdm trivial (by norm_num)
  -- the denominator
  have hden : L.mass 2 (L.centredTail m) = L.tailMass m * (1 - L.tailMass m) :=
    L.mass_two_centredTail m
  -- the tail ratio
  have hratio : c₁ * (m : ℝ) * L.lam (.lad m)
      ≤ c₂ * (D.p - 1) * L.tailMass m := by
    have h := D.tail_ratio_ge (lam := fun j => L.lam (.lad j)) L.summable_lad hc1 hbelow habove hm1
    rwa [L.tailSeq_eq_tailMass m] at h
  have hLpos : 0 < L.tailMass m := L.tailMass_pos m
  calc c₁ * (m : ℝ) * L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
      ≤ c₁ * (m : ℝ) * (2 * L.lam (.lad m)) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = 2 * (c₁ * (m : ℝ) * L.lam (.lad m)) := by ring
    _ ≤ 2 * (c₂ * (D.p - 1) * L.tailMass m) := by linarith
    _ ≤ 4 * c₂ * (D.p - 1) * (L.tailMass m * (1 - L.tailMass m)) := by
        have hk : (0 : ℝ) ≤ 4 * c₂ * (D.p - 1) * L.tailMass m := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hhalf hk]
    _ = 4 * c₂ * (D.p - 1) * L.mass 2 (L.centredTail m) := by rw [hden]

/-- **`cor:doubling_family`.** The cut `m₂` past which the rate holds exists, because
`L(m) → 0`. -/
theorem exists_rayleigh_family (D : Decay) {c₁ c₂ : ℝ} (hc1 : 0 < c₁)
    (hbelow : ∀ j : ℕ, 1 ≤ j → c₁ * (j : ℝ) ^ (-D.p) ≤ L.lam (.lad j))
    (habove : ∀ j : ℕ, 1 ≤ j → L.lam (.lad j) ≤ c₂ * (j : ℝ) ^ (-D.p)) :
    ∃ m₂ : ℕ, S.d < m₂ ∧ ∀ m : ℕ, m₂ ≤ m →
      c₁ * (m : ℝ) * L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
        ≤ 4 * c₂ * (D.p - 1) * L.mass 2 (L.centredTail m) := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → L.tailMass m ≤ 1 / 2 := by
    have h : ∀ᶠ m : ℕ in atTop, L.tailMass m < 1 / 2 :=
      L.tailMass_tendsto_zero.eventually_lt_const (by norm_num)
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp h
    exact ⟨m₀, fun m hm => (hm₀ m hm).le⟩
  refine ⟨max m₀ (S.d + 1), lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _), ?_⟩
  intro m hm
  have hdm : S.d < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) hm)
  have hhalf : (1 : ℝ) / 2 ≤ 1 - L.tailMass m := by
    have := hm₀ m (le_trans (le_max_left _ _) hm); linarith
  exact L.rayleigh_family D hc1 hbelow habove hdm hhalf

end Stat

end GFNBounds.Doubling
