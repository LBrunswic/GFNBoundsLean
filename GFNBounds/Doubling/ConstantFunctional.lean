import GFNBounds.Doubling.Constant
import GFNBounds.Doubling.SharpFull

/-!
# The constant of the sharp asymptotic is a non-negative linear functional of the boundary data

**`prop:doubling_constant`, Steps 2 and 3** — `app_doubling.tex:1702–1763`.

> Let `s = 1` and `0 < c < 1`, in the notation of Definitions `def:doubling_setting` and
> `def:doubling_decay_notation`, and let `C` be the limit of `eq:doubling_sharp`, which
> Theorem `theo:doubling_sharp` attaches to every positive sequence satisfying `eq:doubling_cut` at
> every integer `m > d`. […] There are reals `ν_1,…,ν_d` with
> `C = Σ_{j=1}^{d} ν_j λ_j` (`eq:doubling_constant`) at every positive such sequence, and they
> satisfy `ν_j ≥ 0` for every `j`, `Σ_{j=1}^{d} ν_j > 0`, and `ν_j = 0` whenever `2j ≤ d`.

Step 1 — the space, its coordinates and its positive cone — is `Constant.lean` (`Decay.extend`
and its lemmas). This file consumes it together with `SharpFull.sharp_of_cutBal`, which is
`theo:doubling_sharp` with no hypothesis beyond the cut balance and positivity.

## What the coefficients are

`ν_j` is **defined**, not chosen: writing `C(b)` for the limit of the rescaled profile of the
solution with boundary data `b` (`Decay.climit`, a `limUnder`, and the actual limit whenever `b` is
positive on `1..d`), and `e_j` for the indicator of the index `j`,

    ν_j := C(1 + e_j) − C(1).

Both `1` and `1 + e_j` are positive data, so `theo:doubling_sharp` applies to their solutions and
`ν_j` is a difference of two genuine limits. This is the paper's Step 2 read at the canonical basis
— its `C(λ − λ') := C(λ) − C(λ')` — with the positive sequence `1` as the reference point, so that
no choice is made and no `∃` is left in the definition. The paper's coefficients are determined by
`eq:doubling_constant` at the positive sequences, hence agree with these.

## SCOPE (disclosed)

* **Not restated:** the vector-space, isomorphism and positive-cone clauses (Step 1); they are
  `Constant.lean`'s `extend_cutBal`, `extend_unique`, `extend_pos`, `extend_add`, `extend_smul`.
* **Strengthened, and flagged:** `tendsto_of_cutBal` gives the convergence
  `λ_m m^{p_*} → Σ_j ν_j λ_j` for **every** real solution of the cut balance, positivity not
  assumed. The paper asserts `eq:doubling_constant` only at positive sequences and *defines* `C`
  on the rest of the space as the linear extension; here that extension is shown to be the limit
  itself, because every solution is a finite linear combination of the solutions with data `1 + e_j`
  and `1`, whose profiles converge. The paper-shaped statement with the positivity hypothesis is
  `constant_functional`; nothing open is settled by the stronger form.
* `nu_eq_zero` holds at `j = 0` too (the datum `λ_0` is never read above the cut); the paper's
  clause is over `1 ≤ j ≤ d`, and `constant_functional` states it that way.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1`, `p = p_*` | ✓ carried (`Decay`) |
| `d ≥ 1` (`def:doubling_setting`) | ✓ carried (`hd : 1 ≤ d`) |
| `eq:doubling_cut` at every integer `m > d` | ✓ carried (`D.CutBal d lam ⊤`) |
| the sequence is positive | ✓ carried in `constant_functional`; ⚠ **dropped** in `tendsto_of_cutBal`, see SCOPE |
| `theo:doubling_sharp`, `theo:doubling_decay`(2) | ✓ carried, and **proved** (`sharp_of_cutBal`, which returns `0 < c₁ ≤ C`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

namespace Decay

/-- The indicator `e_j` of the index `j`, as boundary data. -/
def ind (j : ℕ) : ℕ → ℝ := fun i => if i = j then 1 else 0

theorem ind_nonneg (j i : ℕ) : 0 ≤ ind j i := by
  unfold ind; split_ifs <;> norm_num

/-- `C(b) := lim_m (extend d b)_m m^{p_*}`, the constant `theo:doubling_sharp` attaches to the
solution of the cut balance with boundary data `b`. Stated as a `limUnder`; it is the actual limit
whenever `b` is positive on `1..d` (`tendsto_climit_of_pos`), and in fact for every `b`
(`climit_eq_sum`). -/
noncomputable def climit (D : Decay) (d : ℕ) (b : ℕ → ℝ) : ℝ :=
  limUnder atTop (fun m : ℕ => D.extend d b m * (m : ℝ) ^ D.p)

/-- **The coefficients of `eq:doubling_constant`:** `ν_j := C(1 + e_j) − C(1)`, a difference of two
limits that `theo:doubling_sharp` provides, both data being positive. -/
noncomputable def nu (D : Decay) (d : ℕ) (j : ℕ) : ℝ :=
  D.climit d (fun i => 1 + ind j i) - D.climit d (fun _ => 1)

variable (D : Decay) {d : ℕ}

/-! ## Step 1, completed: the solution is linear in the data over any finite sum, and monotone -/

theorem extend_zero (m : ℕ) : D.extend d (fun _ => (0 : ℝ)) m = 0 := by
  have h := D.extend_smul (d := d) 0 (fun _ => (0 : ℝ)) m
  simpa using h

/-- Linearity of `extend` in the data, over a finite sum. -/
theorem extend_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (m : ℕ) :
    D.extend d (fun i => ∑ j ∈ s, f j i) m = ∑ j ∈ s, D.extend d (f j) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact D.extend_zero m
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [D.extend_add, ih]

/-- Non-negative data give a non-negative solution at every `m ≥ 1` — the induction of
`extend_pos` with `≤` in place of `<`. -/
theorem extend_nonneg (b : ℕ → ℝ) (hb : ∀ j, 1 ≤ j → j ≤ d → 0 ≤ b j) :
    ∀ m, 1 ≤ m → 0 ≤ D.extend d b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hm1
      by_cases hle : m ≤ d
      · rw [D.extend_of_le b hle]; exact hb m hm1 hle
      · have hgt : d < m := by omega
        rw [D.extend_of_gt b hgt]
        refine Finset.sum_nonneg fun j hj => ?_
        have hj1 : 1 ≤ j := one_le_of_mem_window' hm1 hj
        exact mul_nonneg (D.qm_pos hm1 j).le (ih j (window_lt hj) hj1)

/-- Above index `0`, the solution is the sum of its data on `1..d` against the solutions with
indicator data: `(extend d b)_m = Σ_{j=1}^{d} b_j (extend d e_j)_m` for `m ≥ 1`. -/
theorem extend_eq_sum_ind (hd : 1 ≤ d) (b : ℕ → ℝ) :
    ∀ m, 1 ≤ m → D.extend d b m = ∑ j ∈ Finset.Icc 1 d, b j * D.extend d (ind j) m := by
  intro m hm
  have hagree : ∀ j, 1 ≤ j → j ≤ d →
      D.extend d b j = D.extend d (fun i => ∑ k ∈ Finset.Icc 1 d, b k * ind k i) j := by
    intro j hj1 hjd
    rw [D.extend_of_le _ hjd, D.extend_of_le _ hjd]
    simp [ind, Finset.mem_Icc, hj1, hjd]
  rw [D.cutBal_unique (D.extend_cutBal b hd) (D.extend_cutBal _ hd) hagree m hm, D.extend_sum]
  exact Finset.sum_congr rfl fun j _ => D.extend_smul (b j) (ind j) m

/-! ## Step 2: the limit exists on positive data, and is linear -/

/-- **`theo:doubling_sharp` at the solution with positive data `b`:** the rescaled profile
converges to `C(b)`, and `C(b) > 0`. -/
theorem tendsto_climit_of_pos (hd : 1 ≤ d) (b : ℕ → ℝ) (hb : ∀ j, 1 ≤ j → j ≤ d → 0 < b j) :
    Tendsto (fun m : ℕ => D.extend d b m * (m : ℝ) ^ D.p) atTop (𝓝 (D.climit d b)) ∧
      0 < D.climit d b := by
  obtain ⟨C, c₁, -, -, hc₁, hC1, -, -, -, hlim, -⟩ :=
    D.sharp_of_cutBal (D.extend_cutBal b hd) (D.extend_pos b hd hb)
  have hC : D.climit d b = C := hlim.limUnder_eq
  rw [hC]
  exact ⟨hlim, lt_of_lt_of_le hc₁ hC1⟩

/-- The rescaled profile of the solution with indicator data `e_j` converges to `ν_j`. -/
theorem tendsto_ind (hd : 1 ≤ d) (j : ℕ) :
    Tendsto (fun m : ℕ => D.extend d (ind j) m * (m : ℝ) ^ D.p) atTop (𝓝 (D.nu d j)) := by
  have h1 := (D.tendsto_climit_of_pos hd (fun i => 1 + ind j i)
    (fun i _ _ => by have := ind_nonneg j i; linarith)).1
  have h0 := (D.tendsto_climit_of_pos hd (fun _ => 1) (fun _ _ _ => one_pos)).1
  unfold nu
  refine (h1.sub h0).congr' (Eventually.of_forall fun m => ?_)
  have hadd : D.extend d (fun i => 1 + ind j i) m
      = D.extend d (fun _ => (1 : ℝ)) m + D.extend d (ind j) m :=
    D.extend_add (d := d) (fun _ => (1 : ℝ)) (ind j) m
  simp only [hadd]
  ring

/-- **Step 2, `eq:doubling_constant` on the whole space of data:** for every boundary data `b`,
`(extend d b)_m m^{p_*} → Σ_{j=1}^{d} ν_j b_j`. -/
theorem tendsto_extend (hd : 1 ≤ d) (b : ℕ → ℝ) :
    Tendsto (fun m : ℕ => D.extend d b m * (m : ℝ) ^ D.p) atTop
      (𝓝 (∑ j ∈ Finset.Icc 1 d, D.nu d j * b j)) := by
  have hlim : Tendsto
      (fun m : ℕ => ∑ j ∈ Finset.Icc 1 d, b j * (D.extend d (ind j) m * (m : ℝ) ^ D.p))
      atTop (𝓝 (∑ j ∈ Finset.Icc 1 d, b j * D.nu d j)) :=
    tendsto_finsetSum _ fun j _ => (D.tendsto_ind hd j).const_mul (b j)
  have hsum : ∑ j ∈ Finset.Icc 1 d, b j * D.nu d j = ∑ j ∈ Finset.Icc 1 d, D.nu d j * b j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [← hsum]
  refine hlim.congr' ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨1, fun m hm => ?_⟩
  rw [D.extend_eq_sum_ind hd b m hm, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `C(b) = Σ_{j=1}^{d} ν_j b_j` for every data `b`: the `limUnder` is the linear functional. -/
theorem climit_eq_sum (hd : 1 ≤ d) (b : ℕ → ℝ) :
    D.climit d b = ∑ j ∈ Finset.Icc 1 d, D.nu d j * b j :=
  (D.tendsto_extend hd b).limUnder_eq

/-- **`eq:doubling_constant`, for the sequence itself.** Every real solution of the cut balance
at every `m > d` has `λ_m m^{p_*} → Σ_{j=1}^{d} ν_j λ_j`. Positivity is not needed (see SCOPE):
the solution is `extend d λ`, and `tendsto_extend` applies. -/
theorem tendsto_of_cutBal (hd : 1 ≤ d) {lam : ℕ → ℝ} (hcut : D.CutBal d lam ⊤) :
    Tendsto (fun m : ℕ => lam m * (m : ℝ) ^ D.p) atTop
      (𝓝 (∑ j ∈ Finset.Icc 1 d, D.nu d j * lam j)) := by
  have heq : lam = D.extend d lam := funext (D.extend_unique hcut hd fun _ _ => rfl)
  have h := D.tendsto_extend hd lam
  rwa [← heq] at h

/-- **`eq:doubling_constant`, in the paper's words:** the constant `C` of `theo:doubling_sharp` at
a positive solution is `Σ_{j=1}^{d} ν_j λ_j`. -/
theorem constant_eq (hd : 1 ≤ d) {lam : ℕ → ℝ} (hcut : D.CutBal d lam ⊤) {C : ℝ}
    (hC : Tendsto (fun m : ℕ => lam m * (m : ℝ) ^ D.p) atTop (𝓝 C)) :
    C = ∑ j ∈ Finset.Icc 1 d, D.nu d j * lam j :=
  tendsto_nhds_unique hC (D.tendsto_of_cutBal hd hcut)

/-! ## Step 3: the signs, and the indices carrying no weight -/

/-- **Step 3, first clause: `ν_j ≥ 0`.** The solution with indicator data is non-negative, so its
profile is, and so is the limit. -/
theorem nu_nonneg (hd : 1 ≤ d) (j : ℕ) : 0 ≤ D.nu d j := by
  refine ge_of_tendsto (D.tendsto_ind hd j) ?_
  rw [eventually_atTop]
  refine ⟨1, fun m hm => ?_⟩
  exact mul_nonneg (D.extend_nonneg (ind j) (fun i _ _ => ind_nonneg j i) m hm) (by positivity)

/-- **Step 3, second clause: `Σ_{j=1}^{d} ν_j > 0`.** At the data `λ_1 = … = λ_d = 1` the sum is
`C(1)`, which `theo:doubling_sharp` puts above the `c₁ > 0` of `theo:doubling_decay`. -/
theorem sum_nu_pos (hd : 1 ≤ d) : 0 < ∑ j ∈ Finset.Icc 1 d, D.nu d j := by
  obtain ⟨h1, hpos⟩ := D.tendsto_climit_of_pos hd (fun _ => 1) (fun _ _ _ => one_pos)
  have heq : D.climit d (fun _ => 1) = ∑ j ∈ Finset.Icc 1 d, D.nu d j * 1 :=
    tendsto_nhds_unique h1 (D.tendsto_extend hd (fun _ => (1 : ℝ)))
  rw [heq] at hpos
  simpa using hpos

/-- **Step 3, third clause: `ν_j = 0` whenever `2j ≤ d`.** Above the cut the solutions with data
`1 + e_j` and `1` coincide (`extend_congr_high`), so the profile of `e_j`'s solution is eventually
`0`. -/
theorem nu_eq_zero (hd : 1 ≤ d) {j : ℕ} (h2j : 2 * j ≤ d) : D.nu d j = 0 := by
  have hzero : Tendsto (fun m : ℕ => D.extend d (ind j) m * (m : ℝ) ^ D.p) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    refine ⟨d + 1, fun m hm => ?_⟩
    have hhigh := D.extend_congr_high (d := d) (fun i => 1 + ind j i) (fun _ => (1 : ℝ))
      (fun i hi _ => by
        have hij : i ≠ j := by omega
        simp [ind, hij]) m (by omega)
    have hadd : D.extend d (fun i => 1 + ind j i) m
        = D.extend d (fun _ => (1 : ℝ)) m + D.extend d (ind j) m :=
      D.extend_add (d := d) (fun _ => (1 : ℝ)) (ind j) m
    rw [hhigh] at hadd
    have hz : D.extend d (ind j) m = 0 := by linarith
    rw [hz, zero_mul]
  exact tendsto_nhds_unique (D.tendsto_ind hd j) hzero

/-- **`prop:doubling_constant`, Steps 2 and 3, packaged in the paper's shape.** There are
`ν_1,…,ν_d ≥ 0` with `Σ ν_j > 0` and `ν_j = 0` for `2j ≤ d` such that every positive solution of the
cut balance at every `m > d` has `λ_m m^{p_*} → Σ_{j=1}^{d} ν_j λ_j`, i.e. `eq:doubling_constant`.
The witness is `D.nu d`, defined above as a difference of limits. -/
theorem constant_functional (hd : 1 ≤ d) :
    ∃ ν : ℕ → ℝ, (∀ j, 0 ≤ ν j) ∧ 0 < ∑ j ∈ Finset.Icc 1 d, ν j ∧
      (∀ j, 1 ≤ j → 2 * j ≤ d → ν j = 0) ∧
      ∀ lam : ℕ → ℝ, D.CutBal d lam ⊤ → (∀ j, 1 ≤ j → 0 < lam j) →
        Tendsto (fun m : ℕ => lam m * (m : ℝ) ^ D.p) atTop
          (𝓝 (∑ j ∈ Finset.Icc 1 d, ν j * lam j)) :=
  ⟨D.nu d, D.nu_nonneg hd, D.sum_nu_pos hd, fun _ _ h2j => D.nu_eq_zero hd h2j,
    fun _ hcut _ => D.tendsto_of_cutBal hd hcut⟩

end Decay

end GFNBounds.Doubling
