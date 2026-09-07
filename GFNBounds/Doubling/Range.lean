import GFNBounds.Doubling.Setting

/-!
# The family `ε_{c,s}` and its standing range

**`lem:doubling_range`** — `app_doubling.tex:86–100` (Lemma 89 of the ICLR build).

> In the setting of Definition `def:doubling_setting`, let `s ≥ 0` and `0 < c < 2^s`. Then
> `j ↦ ε_{c,s}(j)` is non-increasing on `{1,2,3,…}` with values in `(0,1)`, its supremum is
> `ε_{c,s}(1) = c·2^{-s} < 1`, and the decrement edge out of the state `1` carries the
> probability `1 − c·2^{-s} > 0`.

`ε_{c,s}(j) := c/(j+1)^s` is `eq:doubling_family`, and the *standing range* `s ≥ 0`, `0 < c < 2^s`
is where it takes its values in `(0,1)`.

## SCOPE (disclosed)

The family is introduced here as one **instance** of `Setting`, never baked into it: the four
statements of the appendix that do the real work — `lem:doubling_percut`, `theo:doubling_unbounded`,
`lem:doubling_ramp`, `prop:doubling_unsolvable` — hypothesize `ε` abstractly and are explicitly not
confined to the standing range (`app_doubling.tex:36–39`).

## Hypothesis checklist against `lem:doubling_range`

| paper hypothesis | here |
|---|---|
| `s ≥ 0` | ✓ carried (`hs`) |
| `0 < c` | ✓ carried (`hc`) |
| `c < 2^s` | ✓ carried (`hcs`) |
| conclusions on `j ≥ 1` only | ✓ carried (the `1 ≤ j` guards) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-- `ε_{c,s}(j) = c/(j+1)^s` of `eq:doubling_family`. -/
noncomputable def epsCS (c s : ℝ) (j : ℕ) : ℝ := c / ((j : ℝ) + 1) ^ s

theorem base_pos (j : ℕ) : (0 : ℝ) < (j : ℝ) + 1 := by positivity

/-- `ε_{c,s} > 0` — the doubling edge is present at every ladder state. -/
theorem epsCS_pos {c : ℝ} (hc : 0 < c) (s : ℝ) (j : ℕ) : 0 < epsCS c s j :=
  div_pos hc (rpow_pos_of_pos (base_pos j) s)

/-- `ε_{c,s}` is non-increasing on `{1,2,3,…}`: the doubling probability decays along the ladder.
Stated for all of `ℕ`, which is stronger and costs nothing. -/
theorem epsCS_antitone {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) : Antitone (epsCS c s) := by
  intro i j hij
  have hb : ((i : ℝ) + 1) ^ s ≤ ((j : ℝ) + 1) ^ s := by
    apply rpow_le_rpow (le_of_lt (base_pos i)) _ hs
    exact_mod_cast Nat.add_le_add_right hij 1
  exact div_le_div_of_nonneg_left hc.le (rpow_pos_of_pos (base_pos i) s) hb

/-- The supremum of the family, `ε_{c,s}(1) = c·2^{-s}`. -/
theorem epsCS_one (c s : ℝ) : epsCS c s 1 = c * 2 ^ (-s) := by
  have : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
  rw [epsCS, this, rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv]

/-- Every value of the family on the ladder is at most `ε_{c,s}(1) = c·2^{-s}`. -/
theorem epsCS_le_one_val {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) {j : ℕ} (hj : 1 ≤ j) :
    epsCS c s j ≤ c * 2 ^ (-s) := by
  rw [← epsCS_one]; exact epsCS_antitone hc hs hj

/-- `c < 2^s` is exactly what makes `ε_{c,s}(1) < 1`, hence the decrement edge out of the state
`1` carry the positive probability `1 − c·2^{-s}`. -/
theorem epsCS_one_lt_one {c s : ℝ} (hcs : c < 2 ^ s) : c * 2 ^ (-s) < 1 := by
  have h2 : (0 : ℝ) < 2 ^ s := rpow_pos_of_pos (by norm_num) s
  rw [rpow_neg (by norm_num : (0:ℝ) ≤ 2), ← div_eq_mul_inv, div_lt_one h2]
  exact hcs

/-- The decrement edge out of the state `1` carries positive probability. -/
theorem one_sub_epsCS_one_pos {c s : ℝ} (hcs : c < 2 ^ s) : 0 < 1 - c * 2 ^ (-s) := by
  have := epsCS_one_lt_one hcs; linarith

/-- The family, packaged as a `Setting`: `lem:doubling_range` is exactly the proof obligation that
`ε_{c,s}` on the standing range satisfies the standing hypotheses, with `ε_max = c·2^{-s}`.

The target row is supplied by the caller, `def:doubling_setting` leaving it a parameter of the
setting alongside `d` and `j̄`. -/
noncomputable def Setting.ofFamily (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) (hcs : c < 2 ^ s)
    (d : ℕ) (hd : 1 ≤ d) (row : ℕ → ℝ) (hrow : ∀ j, 0 ≤ row j)
    (hsupp : ∀ ⦃j⦄, row j ≠ 0 → 1 ≤ j ∧ j ≤ d)
    (hsum : ∑ j ∈ Finset.Icc 1 d, row j = 1) : Setting where
  d := d
  d_pos := hd
  eps := epsCS c s
  eps_pos := fun _ _ => epsCS_pos hc s _
  epsMax := c * 2 ^ (-s)
  eps_le := fun _ hj => epsCS_le_one_val hc hs hj
  epsMax_lt_one := epsCS_one_lt_one hcs
  row := row
  row_nonneg := hrow
  row_supp := hsupp
  row_sum := hsum

@[simp] theorem Setting.ofFamily_eps (c s : ℝ) (hc hs hcs) (d hd row hrow hsupp hsum) :
    (Setting.ofFamily c s hc hs hcs d hd row hrow hsupp hsum).eps = epsCS c s := rfl

end GFNBounds.Doubling
