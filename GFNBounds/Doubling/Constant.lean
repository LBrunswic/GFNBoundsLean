import GFNBounds.Doubling.DecayNotation

/-!
# The solutions of the cut balance form a `d`-dimensional space

**`prop:doubling_constant`, Step 1** — `app_doubling.tex:1702–1763`.

> Then the real sequences `(λ_j)_{j≥1}` satisfying `eq:doubling_cut` at every integer `m > d` form
> a real vector space, the map `(λ_j) ↦ (λ_1,…,λ_d)` is a linear isomorphism of it onto `ℝ^d`, and
> such a sequence is positive if and only if `λ_1,…,λ_d` are. […] and `ν_j = 0` whenever `2j ≤ d`.

## SCOPE (disclosed)

Step 1 of the proposition is proved, in the constructive form that makes it usable: `extend`
is the unique solution with prescribed boundary data, and

* `extend_cutBal` — it solves `eq:doubling_cut`;
* `extend_unique` — nothing else with the same boundary data does (the isomorphism);
* `extend_pos` — positivity of the sequence is positivity of the boundary data;
* `extend_add`, `extend_smul` — the map is linear;
* `extend_congr_high` — the value at `m > d` does not see `λ_j` for `2j ≤ d`, which is the
  mechanism behind `ν_j = 0` there.

**Steps 2 and 3 are not here.** They identify `C = lim λ_m m^{p_*}` as a linear functional and fix
the signs of its coefficients, and both consume `theo:doubling_sharp`, which is open. What
`extend_congr_high` gives is the *independence* half of Step 3, ready for the moment `C` exists:
if `C` is a function of the sequence, it is a function of `λ_j` for `d/2 < j ≤ d` alone.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1` | ✓ carried by `Decay` |
| `eq:doubling_cut` at every `m > d` | ✓ carried (`Decay.CutBal d · ⊤`) |
| the sequence is indexed from `1` | ✓ carried; index `0` is boundary data and is never used |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

/-- The solution of `eq:doubling_avg` with boundary data `b` on `{0,…,d}`. Well-founded because
every `j ∈ W(m)` is below `m`. -/
noncomputable def extend (D : Decay) (d : ℕ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m ≤ d then b m
  else ∑ j ∈ (window m).attach, D.qm m j.1 * extend D d b j.1
termination_by m
decreasing_by exact window_lt j.2

variable (D : Decay) {d : ℕ}

theorem extend_of_le (b : ℕ → ℝ) {m : ℕ} (h : m ≤ d) : D.extend d b m = b m := by
  rw [extend, if_pos h]

theorem extend_of_gt (b : ℕ → ℝ) {m : ℕ} (h : d < m) :
    D.extend d b m = ∑ j ∈ window m, D.qm m j * D.extend d b j := by
  rw [extend, if_neg (by omega)]
  exact Finset.sum_attach (window m) fun j => D.qm m j * D.extend d b j

/-- `extend` solves the cut balance. -/
theorem extend_cutBal (b : ℕ → ℝ) (hd : 1 ≤ d) : D.CutBal d (D.extend d b) ⊤ := by
  intro m hm _
  have hm1 : 1 ≤ m := by omega
  have hpos := D.one_sub_eps_pos hm1
  rw [D.extend_of_gt b hm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hb : ((j : ℝ) + 1) ≠ 0 := (base_pos j).ne'
  rw [D.qm_eq, D.eps_eq j]
  field_simp

/-- Nothing else with the same boundary data solves it: the coordinate map is injective. -/
theorem extend_unique {lam b : ℕ → ℝ} (h : D.CutBal d lam ⊤) (hd : 1 ≤ d)
    (hb : ∀ j ≤ d, lam j = b j) : ∀ m, lam m = D.extend d b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      by_cases hle : m ≤ d
      · rw [D.extend_of_le b hle, hb m hle]
      · have hgt : d < m := by omega
        have hm1 : 1 ≤ m := by omega
        rw [D.extend_of_gt b hgt, D.avg_of_cutBal h hm1 hgt le_top]
        exact Finset.sum_congr rfl fun j hj => by rw [ih j (window_lt hj)]

/-- Positivity of the sequence is positivity of the boundary data. -/
theorem extend_pos (b : ℕ → ℝ) (hd : 1 ≤ d) (hb : ∀ j, 1 ≤ j → j ≤ d → 0 < b j) :
    ∀ m, 1 ≤ m → 0 < D.extend d b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hm1
      by_cases hle : m ≤ d
      · rw [D.extend_of_le b hle]; exact hb m hm1 hle
      · have hgt : d < m := by omega
        rw [D.extend_of_gt b hgt]
        refine Finset.sum_pos (fun j hj => ?_) ⟨m - 1, by rw [mem_window]; omega⟩
        have hj1 : 1 ≤ j := one_le_of_mem_window' hm1 hj
        exact mul_pos (D.qm_pos hm1 j) (ih j (window_lt hj) hj1)

/-- The extension is additive in the boundary data. -/
theorem extend_add (b₁ b₂ : ℕ → ℝ) (m : ℕ) :
    D.extend d (fun j => b₁ j + b₂ j) m = D.extend d b₁ m + D.extend d b₂ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      by_cases hle : m ≤ d
      · rw [D.extend_of_le _ hle, D.extend_of_le _ hle, D.extend_of_le _ hle]
      · have hgt : d < m := by omega
        rw [D.extend_of_gt _ hgt, D.extend_of_gt _ hgt, D.extend_of_gt _ hgt, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [ih j (window_lt hj)]; ring

/-- The extension is homogeneous in the boundary data. -/
theorem extend_smul (t : ℝ) (b : ℕ → ℝ) (m : ℕ) :
    D.extend d (fun j => t * b j) m = t * D.extend d b m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      by_cases hle : m ≤ d
      · rw [D.extend_of_le _ hle, D.extend_of_le _ hle]
      · have hgt : d < m := by omega
        rw [D.extend_of_gt _ hgt, D.extend_of_gt _ hgt, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [ih j (window_lt hj)]; ring

/-- **The mechanism behind `ν_j = 0` for `2j ≤ d`.** Above the cut `d`, the solution does not see
the boundary data at an index `j` with `2j ≤ d`: every window of an `m > d` starts at
`⌈m/2⌉ ≥ (d+1)/2 > d/2`. -/
theorem extend_congr_high (b₁ b₂ : ℕ → ℝ) (hb : ∀ j, d < 2 * j → j ≤ d → b₁ j = b₂ j) :
    ∀ m : ℕ, d < m → D.extend d b₁ m = D.extend d b₂ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hm
      rw [D.extend_of_gt _ hm, D.extend_of_gt _ hm]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjw := mem_window.mp hj
      have hjlow : d < 2 * j := by omega
      by_cases hjd : j ≤ d
      · rw [D.extend_of_le _ hjd, D.extend_of_le _ hjd, hb j hjlow hjd]
      · rw [ih j (window_lt hj) (by omega)]

end Decay

end GFNBounds.Doubling
