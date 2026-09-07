import GFNBounds.Doubling.Summable
import GFNBounds.Doubling.PointwiseInv

/-!
# The loop closure carries an invariant probability at `s = 1`, `0 < c < 1`

**`prop:doubling_phase`(3), Step 5** — `app_doubling.tex:510–624` (Proposition 99 of the ICLR
build), and `theo:doubling_main`(1).

> if `s = 1`, then `X` is positive recurrent for `0 < c < 1`, with `E(σ | X₀ = j) = j/(1−c)` at
> every ladder state `j ≥ 1` […]
>
> *Step 5.* By Proposition `prop:doubling_length`, `E(σ | X₀ = j) = j/(1−c)` at every ladder state
> `j` and `σ̄ = j̄/(1−c)`. The return time of `X` to `s₀` is one step to `s_f`, one step into
> `{1,…,d}` and then `σ`, so its expectation is `2 + σ̄ < +∞`; with Step 1, `X` is positive
> recurrent.

## What is proved, and in which form

Positive recurrence is a statement about a chain and Mathlib v4.31.0 has no discrete-time
recurrence theory. But every consumer of Step 5 in this library — `lem:doubling_percut` case (1),
`theo:doubling_unbounded`, `lem:doubling_ramp`, `cor:doubling_family`, `theo:doubling_main` —
takes positive recurrence as the hypothesis `Stat S none`, an invariant probability. That object
is what is constructed here, and it is constructed rather than deduced from a chain:

* `statSeq` solves the cut balance `eq:doubling_cut` **with the target row as its source term**,
  by well-founded recursion on `m`, normalised by `λ(s₀) = 1`. Only `def:doubling_setting` is
  used: `1 − ε(m) > 0` makes the recursion well posed and `Σ_k P̂_B(s_f→k) = 1` starts it.
* `statSeq_point` turns that recursion into the *pointwise* balance at every ladder state, by
  differencing the cuts at `m` and `m+1`: the window `W(m+1)` gains `m` and, when `m` is even,
  loses `m/2`.
* Summability — the one place `c < 1` is spent — is `GFNBounds.Doubling.Summable`, which gives the
  explicit bound `Σ_{m≥1} λ_m ≤ j̄/(1−c)`. That number is exactly the paper's `σ̄ ≤ j̄/(1−c)` of
  `lem:doubling_supersolution`, reached here without a chain and without `prop:doubling_length`.
* `GFNBounds.Doubling.PointwiseInv` promotes the pointwise balance to the integral invariance
  `Stat` asks for, and `PreStat.toStatNone` supplies positivity from
  `lem:doubling_irreducible`.

## SCOPE (disclosed)

* **This is not "the chain is positive recurrent".** It is the existence of an invariant
  probability, which for an irreducible chain is equivalent to positive recurrence but is here a
  construction, not a translation of one. Nothing in this file mentions a return time, and the
  identity `Σ_x λ_x = 2 + σ̄` of Step 5 is not asserted — `Kac.lean` derives its `s₀` shadow
  `λ(s₀)(2 + σ̄) = 1` from an arbitrary `Stat`, and this file now supplies the `Stat` that theorem
  was waiting for at `s = 1`, `0 < c < 1`.
* **Uniqueness is not claimed.** The paper does not need it at this point and it is not proved
  here; `TruncationStat.lean` proves it at a finite cap, by an argument that does not transfer.
* **The other rows of the phase diagram are untouched.** `s > 1` (Step 3), `s < 1` (Step 4),
  `s = 1` with `c ≥ 1` (Steps 6–8) are Lyapunov arguments, and their analytic halves are
  `GFNBounds.Doubling.Lyapunov`; their chain conclusions remain open, as does row (d),
  `c = 1/ln 2`, which is open in the paper itself.
* The construction fixes `λ(s₀) = λ(s_f) = 1` before normalising. That is a choice of scale, not
  of solution: any invariant probability has `λ(s_f) = λ(s₀)` by the single edge into the sink.

## Hypothesis checklist against `prop:doubling_phase`(3)

| paper hypothesis | here |
|---|---|
| standing range, `s = 1` | ✓ carried, pointwise on the ladder (`heps`) |
| `0 < c < 1` | ✓ carried; `c < 1` is spent exactly once, in summability |
| the loop closure | ✓ carried (`cap = none`) |
| `prop:doubling_length` (`E(σ\|X₀=j) = j/(1−c)`) | ⚠ not used: the bound `j̄/(1−c)` is obtained from the cut balance directly |
| Foster's criterion | ✗ not used and not available |
| the conclusion "positive recurrent" | ⚠ weakened to `Nonempty (Stat S none)`, which is what every consumer in this library takes |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

variable {S : Setting}

/-! ## The source term: the tail of the target row -/

/-- `R(m) = Σ_{k ≥ m} P̂_B(s_f → k)`, the mass the target row sends at or above `m`. -/
noncomputable def rowTail (S : Setting) (m : ℕ) : ℝ := ∑ k ∈ Finset.Icc m S.d, S.row k

theorem rowTail_nonneg (S : Setting) (m : ℕ) : 0 ≤ rowTail S m :=
  Finset.sum_nonneg fun k _ => S.row_nonneg k

theorem rowTail_one : rowTail S 1 = 1 := S.row_sum

theorem rowTail_sub (S : Setting) (m : ℕ) : rowTail S m - rowTail S (m + 1) = S.row m := by
  by_cases hmd : m ≤ S.d
  · have hins : Finset.Icc m S.d = insert m (Finset.Icc (m + 1) S.d) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m ∉ Finset.Icc (m + 1) S.d := by simp
    unfold rowTail
    rw [hins, Finset.sum_insert hnot]
    ring
  · have h1 : Finset.Icc m S.d = ∅ := Finset.Icc_eq_empty (by omega)
    have h2 : Finset.Icc (m + 1) S.d = ∅ := Finset.Icc_eq_empty (by omega)
    have h3 : S.row m = 0 := by
      by_contra hne
      exact absurd (S.row_supp hne).2 hmd
    unfold rowTail
    rw [h1, h2, h3]
    simp

theorem rowTail_swap (S : Setting) (N : ℕ) : ∀ (m k : ℕ),
    (m ∈ Finset.Icc 1 N ∧ k ∈ Finset.Icc m S.d) ↔
      (m ∈ Finset.Icc 1 (min N k) ∧ k ∈ Finset.Icc 1 S.d) := by
  intro m k
  simp only [Finset.mem_Icc, le_min_iff]
  omega

/-- The source term contributes at most the mean `j̄` of the target row, however far the cuts are
summed: each `k` is counted `min(N, k) ≤ k` times. -/
theorem sum_rowTail_le (N : ℕ) : ∑ m ∈ Finset.Icc 1 N, rowTail S m ≤ S.jbar := by
  have h : ∑ m ∈ Finset.Icc 1 N, rowTail S m
      = ∑ k ∈ Finset.Icc 1 S.d, ((min N k : ℕ) : ℝ) * S.row k := by
    unfold rowTail
    rw [Finset.sum_comm' (rowTail_swap S N) (f := fun _ k => S.row k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    norm_num
  rw [h, Setting.jbar]
  refine Finset.sum_le_sum fun k _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (S.row_nonneg k)
  have hmin : (min N k : ℕ) ≤ k := min_le_right _ _
  exact_mod_cast hmin

/-! ## The invariant sequence -/

/-- The invariant sequence of the loop closure: the solution of the cut balance with the target
row as source term, normalised by `λ(s₀) = 1`.

Well-founded because every `j ∈ W(m)` has `j < m`; the division is legitimate because
`1 − ε(m) > 0` on the standing range. -/
noncomputable def statSeq (S : Setting) (m : ℕ) : ℝ :=
  if m = 0 then 1
  else ((∑ j ∈ (window m).attach, statSeq S j.1 * S.eps j.1) + rowTail S m) / (1 - S.eps m)
termination_by m
decreasing_by exact window_lt j.2

@[simp] theorem statSeq_zero : statSeq S 0 = 1 := by rw [statSeq]; simp

theorem statSeq_eq {m : ℕ} (hm : 1 ≤ m) :
    statSeq S m
      = ((∑ j ∈ window m, statSeq S j * S.eps j) + rowTail S m) / (1 - S.eps m) := by
  rw [statSeq, if_neg (by omega)]
  congr 2
  exact Finset.sum_attach (window m) fun j => statSeq S j * S.eps j

/-- **The cut balance with the row correction.** This is `eq:doubling_cut` at every `m ≥ 1`, not
only at `m > d`; the extra term is the mass the target row sends at or above `m`, and it is what
makes the cut identity hold below `d` as well. -/
theorem statSeq_cut {m : ℕ} (hm : 1 ≤ m) :
    statSeq S m * (1 - S.eps m) = (∑ j ∈ window m, statSeq S j * S.eps j) + rowTail S m := by
  rw [statSeq_eq hm, div_mul_cancel₀]
  exact (S.one_sub_eps_pos hm).ne'

theorem statSeq_pos (S : Setting) : ∀ m : ℕ, 0 < statSeq S m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · rw [statSeq_eq hm]
        refine div_pos ?_ (S.one_sub_eps_pos hm)
        have hw : (0:ℝ) ≤ ∑ j ∈ window m, statSeq S j * S.eps j := by
          refine Finset.sum_nonneg fun j hj =>
            mul_nonneg (ih j (window_lt hj)).le (S.eps_pos ?_).le
          have h := mem_window.mp hj
          omega
        rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · have hm1 : m = 1 := by omega
          subst hm1
          have h1 : rowTail S 1 = (1:ℝ) := rowTail_one
          linarith
        · have hmem : m - 1 ∈ window m := by rw [mem_window]; omega
          have hpos : 0 < ∑ j ∈ window m, statSeq S j * S.eps j := by
            refine Finset.sum_pos (fun j hj => ?_) ⟨m - 1, hmem⟩
            refine mul_pos (ih j (window_lt hj)) (S.eps_pos ?_)
            have h := mem_window.mp hj
            omega
          have := rowTail_nonneg S m
          linarith

theorem statSeq_nonneg (S : Setting) (m : ℕ) : 0 ≤ statSeq S m := (statSeq_pos S m).le

/-- **Summability with the paper's constant.** `Σ_{m=1}^{N} λ_m ≤ j̄/(1−c)` at every `N` — the
same number as `σ̄ ≤ j̄/(1−c)` in `lem:doubling_supersolution`, obtained from the cut balance
alone. -/
theorem statSeq_partial_sum_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, statSeq S m ≤ S.jbar / (1 - c) := by
  have hc : (0:ℝ) < 1 - c := by linarith
  rw [le_div_iff₀ hc]
  have h := partial_sum_le hc0 heps (statSeq_nonneg S) N (g := rowTail S)
    (fun m hm1 _ => le_of_eq (statSeq_cut hm1))
  have h2 := sum_rowTail_le (S := S) N
  linarith

theorem summable_statSeq {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) : Summable (statSeq S) := by
  refine summable_of_sum_range_le (f := statSeq S) (statSeq_nonneg S)
    (c := 1 + S.jbar / (1 - c)) ?_
  intro n
  have hsub : Finset.range n ⊆ insert 0 (Finset.Icc 1 n) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => statSeq_nonneg S i
  rw [Finset.sum_insert (by simp), statSeq_zero] at hle
  have := statSeq_partial_sum_le hc0 hc1 heps (S := S) n
  linarith

/-! ## From the cut balance to the pointwise balance -/

/-- The window moves by one: passing from the cut at `k` to the cut at `k+1` adds the state `k`
and, when `k` is even, drops the state `k/2`. -/
theorem window_succ_sum {k : ℕ} (hk : 1 ≤ k) (F : ℕ → ℝ) :
    (∑ j ∈ window (k + 1), F j) + (if 2 ∣ k then F (k / 2) else 0)
      = (∑ j ∈ window k, F j) + F k := by
  by_cases hpar : 2 ∣ k
  · have hA1 : window (k + 1) = insert k (Finset.Ico (k / 2 + 1) k) := by
      ext j; simp only [window, Finset.mem_Ico, Finset.mem_insert]; omega
    have hA2 : window k = insert (k / 2) (Finset.Ico (k / 2 + 1) k) := by
      ext j; simp only [window, Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot1 : k ∉ Finset.Ico (k / 2 + 1) k := by simp
    have hnot2 : k / 2 ∉ Finset.Ico (k / 2 + 1) k := by simp only [Finset.mem_Ico]; omega
    rw [hA1, hA2, Finset.sum_insert hnot1, Finset.sum_insert hnot2, if_pos hpar]
    ring
  · have hA1 : window (k + 1) = insert k (window k) := by
      ext j; simp only [window, Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : k ∉ window k := by simp only [window, Finset.mem_Ico]; omega
    rw [hA1, Finset.sum_insert hnot, if_neg hpar]
    ring

/-- **The pointwise invariance equation on the ladder.** Mass at `k` comes from the decrement out
of `k+1`, from the doubling out of `k/2` when `k` is even and positive, and from the target row.
At `k = 0` — which is `s₀` — it reads `1 = λ_1(1 − ε(1))`, the cut at `1`. -/
theorem statSeq_point (S : Setting) (k : ℕ) :
    statSeq S k = statSeq S (k + 1) * (1 - S.eps (k + 1))
      + (if 1 ≤ k ∧ 2 ∣ k then statSeq S (k / 2) * S.eps (k / 2) else 0) + S.row k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 := statSeq_cut (S := S) (m := 1) le_rfl
    have hw : window 1 = ∅ := by simp [window]
    have hr0 : S.row 0 = 0 := by
      by_contra hne
      exact absurd (S.row_supp hne).1 (by omega)
    rw [hw, Finset.sum_empty, zero_add, rowTail_one] at h1
    simp only [statSeq_zero, hr0]
    norm_num
    linarith
  · have hck := statSeq_cut (S := S) hk
    have hck1 := statSeq_cut (S := S) (m := k + 1) (by omega)
    have hws := window_succ_sum hk (fun j => statSeq S j * S.eps j)
    have hrt := rowTail_sub S k
    have hck' : statSeq S k - statSeq S k * S.eps k
        = (∑ j ∈ window k, statSeq S j * S.eps j) + rowTail S k := by
      rw [← hck]; ring
    have hif : (if 1 ≤ k ∧ 2 ∣ k then statSeq S (k / 2) * S.eps (k / 2) else 0)
        = (if 2 ∣ k then statSeq S (k / 2) * S.eps (k / 2) else 0) := by
      by_cases hpar : 2 ∣ k
      · rw [if_pos ⟨hk, hpar⟩, if_pos hpar]
      · rw [if_neg (fun h => hpar h.2), if_neg hpar]
    rw [hif]
    linarith

/-! ## The invariant probability -/

/-- The unnormalised invariant measure on `St`: `statSeq` along the ladder, `1` at the sink. Note
`statSeq S 0 = 1` as well, which is the balance at the sink, `λ(s_f) = λ(s₀)`. -/
noncomputable def statMeas (S : Setting) : St → ℝ
  | .lad j => statSeq S j
  | .sink => 1

@[simp] theorem statMeas_lad (j : ℕ) : statMeas S (.lad j) = statSeq S j := rfl
@[simp] theorem statMeas_sink : statMeas S .sink = 1 := rfl

theorem statMeas_pos (S : Setting) (x : St) : 0 < statMeas S x := by
  rcases x with j | _
  · exact statSeq_pos S j
  · norm_num

/-- **`prop:doubling_phase`(3), the `0 < c < 1` half, in the form this library consumes.** The
loop-closed chain at `s = 1`, `0 < c < 1` carries an invariant probability, positive at every
state. -/
theorem exists_stat_none {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) : Nonempty (Stat S none) := by
  have hsummable : Summable (statSeq S) := summable_statSeq hc0 hc1 heps
  have hladder : HasSum (fun k : ℕ => statMeas S (.lad k)) (∑' k, statSeq S k) :=
    hsummable.hasSum
  have hZ : HasSum (statMeas S) ((∑' k, statSeq S k) + 1) := by
    have h := hasSum_st (g := statMeas S) hladder
    simpa using h
  set Z : ℝ := (∑' k, statSeq S k) + 1 with hZ_def
  have hZpos : 0 < Z := by
    have h1 : (0:ℝ) ≤ ∑' k, statSeq S k := tsum_nonneg (statSeq_nonneg S)
    rw [hZ_def]; linarith
  have hnn : ∀ x, 0 ≤ statMeas S x := fun x => (statMeas_pos S x).le
  have hsum : Summable (fun k : ℕ => statMeas S (.lad k)) := hladder.summable
  have hsink : statMeas S .sink = statMeas S (.lad 0) := by simp
  have hpt : ∀ k : ℕ, statMeas S (.lad k)
      = statMeas S (.lad (k + 1)) * (1 - S.eps (k + 1))
        + (if 1 ≤ k ∧ 2 ∣ k then statMeas S (.lad (k / 2)) * S.eps (k / 2) else 0)
        + statMeas S .sink * S.row k := by
    intro k
    simp only [statMeas_lad, statMeas_sink, one_mul]
    exact statSeq_point S k
  have hscale : ∀ g : St → ℝ,
      ∑' x, statMeas S x / Z * g x = Z⁻¹ * ∑' x, statMeas S x * g x := by
    intro g
    rw [← tsum_mul_left]
    exact tsum_congr fun x => by ring
  refine ⟨PreStat.toStatNone
    { lam := fun x => statMeas S x / Z
      nonneg := fun x => div_nonneg (hnn x) hZpos.le
      vanish := fun x hx => absurd trivial hx
      summable := hZ.summable.div_const Z
      total := by
        have h : ∑' x, statMeas S x / Z = Z⁻¹ * ∑' x, statMeas S x := by
          rw [← tsum_mul_left]
          exact tsum_congr fun x => by ring
        rw [h, hZ.tsum_eq]
        field_simp
      inv := by
        intro f hf
        rw [hscale, hscale, inv_of_pointwise S hnn hsum hsink hpt f hf] }⟩

/-- The same statement with `ε` given as the family `ε_{c,1}` rather than pointwise: the form
`GFNBoundsScaffold.Doubling.exists_stat_of_lt_one` states. -/
theorem exists_stat_of_family {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Setting) (hS : S.eps = epsCS c 1) : Nonempty (Stat S none) :=
  exists_stat_none hc0 hc1 (fun j _ => by rw [hS, epsCS, Real.rpow_one])

end GFNBounds.Doubling
