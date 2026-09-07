import GFNBounds.Doubling.CutBalance
import GFNBounds.Doubling.Drift
import GFNBounds.Doubling.Lyapunov

/-!
# The loop closure carries no invariant probability when the doubling flux is supercritical

**`prop:doubling_phase`(2) and (3)** — `app_doubling.tex:510–624` (Proposition 99 of the ICLR
build), and `theo:doubling_main`(1), rows `s < 1` and `s = 1, 1 ≤ c < 2`.

> In the setting of Definition `def:doubling_setting`, let `(c,s)` lie in the standing range and
> let `X` be the loop-closed backward chain on the infinite graph. Then `X` is irreducible, and:
> […] (2) if `s < 1`, then `X` is transient; (3) if `s = 1`, then […] for every `1 ≤ c < 2`,
> `E(σ | X₀ = j) = +∞` at every ladder state `j ≥ 1` and `X` **is not positive recurrent**; and
> `X` is null recurrent for `1 ≤ c < 1/ln 2` and transient for `1/ln 2 < c < 2`.
>
> *Step 7.* […] An irreducible chain whose expected return time at one state is infinite is not
> positive recurrent: `X` is not positive recurrent at any `1 ≤ c < 2`.

## The modelling decision: the cut balance alone refutes normalisability

The paper reaches "not positive recurrent" through a chain — optional stopping on
`(X_{n∧σ})`, then `E(σ) = +∞`, then the return-time criterion at `s = 1`; a bounded
supermartingale off a finite set at `s < 1`. None of that is available here, and none of it is
needed for the conclusion this library states, `IsEmpty (Stat S none)`: an invariant probability
satisfies the cut balance `eq:doubling_cut`, and the cut balance alone forbids a **summable**
positive solution as soon as the drift coefficient `(m+1)ε(m)` is `≥ 1` past some index.

The identity behind it is `GFNBounds.Doubling.window_double_sum` run from a shifted foot. Summing
`eq:doubling_cut` over the cuts `m ∈ (M, 2T]` and counting each source index `j` by the cuts it
crosses — exactly `min(2T,2j) − max(M,j)` of them — gives, keeping only `j = M` and
`j ∈ (M, T]`,

  `Σ_{m ∈ (M,2T]} λ_m(1 − ε(m)) ≥ M λ_M ε(M) + Σ_{j ∈ (M,T]} j λ_j ε(j)`,

and `(j+1)ε(j) ≥ 1` turns `j λ_j ε(j)` into `λ_j(1 − ε(j))`, which cancels against the same
window on the left. What survives is

  `Σ_{m ∈ (T,2T]} λ_m ≥ M λ_M ε(M) > 0`   at **every** `T ≥ M`,

so the dyadic blocks `(T, 2T]` each carry a fixed mass and the partial sums of `λ` grow without
bound. A summable `λ` cannot do that. This is `cut_tail_ge` and `isEmpty_stat_of_supercritical`.

## SCOPE (disclosed)

* **Only "not positive recurrent" is proved, and only in the form `IsEmpty (Stat S none)`** — the
  loop closure carries no invariant probability. That is the paper's own wording for row (3)
  (`app_doubling.tex:598–601`) and it is weaker than what rows (2) and (3) also claim:
  - `s < 1`: the paper proves **transience**. Transience is not stated here, and the
    supermartingale criterion it uses is not available.
  - `s = 1`, `1 ≤ c < 2`: the paper also proves `E(σ | X₀ = j) = +∞` at every ladder `j`, which
    needs optional stopping (`prop:doubling_length`'s obstruction), and it splits the row into
    **null recurrent** for `c < 1/ln 2` and **transient** for `c > 1/ln 2`. Neither half of that
    dichotomy is stated here: distinguishing them is a chain statement with no counterpart in this
    library's objects, and the analytic input to Steps 6 and 8 is already in
    `GFNBounds.Doubling.Lyapunov` (`exists_logHeight_drift_nonpos`, `exists_Wpow_drift_neg`).
  - Row (d), `c = 1/ln 2`, is **open in the paper itself** and is untouched; it is covered by the
    `c ≥ 1` statement here only in as much as `1/ln 2 > 1`, which settles "not positive recurrent"
    there and nothing else — as the paper's own closing sentence does.
* **`ε` is not confined to the family.** `isEmpty_stat_of_supercritical` hypothesizes the drift
  coefficient directly, `1 ≤ (m+1)ε(m)` past `M`; the two family instances are corollaries. The
  standing range enters only through the existence of the `Setting`.
* The refutation is **effective in the foot**: the mass carried by each dyadic block is
  `M λ_M ε(M)` with `M` the explicit index past which the drift coefficient is `≥ 1`, namely
  `M = d` at `s = 1` and `M ≥ max(d, 1, c^{−1/(1−s)})` at `s < 1`.

## Hypothesis checklist against `prop:doubling_phase`(2)–(3)

| paper hypothesis | here |
|---|---|
| standing range `s ≥ 0`, `0 < c < 2^s` | ⚠ weakened: only `0 < c`, and the range through the `Setting` |
| `s < 1` (row 2) | ✓ carried (`hs`) |
| `s = 1`, `1 ≤ c < 2` (row 3) | ✓ carried (`hc1`; `c < 2` only through the `Setting`) |
| the loop closure | ✓ carried (`cap = none`) |
| `eq:doubling_cut` at every `m > d` | ✓ carried, via `cut_balance` |
| `λ` positive at every state | ✓ carried (`Stat.pos`, `lem:doubling_irreducible`) |
| optional stopping, the strong Markov property, the return-time criterion | ✗ not used and not available |
| the bounded-supermartingale transience criterion | ✗ not used and not available |
| the conclusion "transient" (row 2) | ⚠ **weakened** to "not positive recurrent" |
| the conclusion "null recurrent / transient" (row 3) | ⚠ **weakened** to "not positive recurrent" |
| the conclusion "not positive recurrent" | ⚠ weakened to `IsEmpty (Stat S none)` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-! ## Two interval rewrites

`Finset.sum_Ioc_consecutive` splits a sum at an interior point; the cut balance is indexed by
`Icc`. These convert. -/

/-- `{1,…,b} = (0,b]`. -/
theorem Icc_one_eq_Ioc_zero (b : ℕ) : Finset.Icc 1 b = Finset.Ioc 0 b := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- `{a+1,…,b} = (a,b]`. -/
theorem Icc_succ_eq_Ioc (a b : ℕ) : Finset.Icc (a + 1) b = Finset.Ioc a b := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-! ## Double counting from a shifted foot

`GFNBounds.Doubling.window_double_sum` counts the cuts `m ∈ {1,…,N}` crossed by a source index
`j`; here the cuts start at `M+1` instead, because the cut balance holds only above `d`. The count
becomes `min(N,2j) − max(M,j)`. -/

/-- The index swap: `m ∈ (M,N]` and `j ∈ W(m)` iff `m ∈ (max(M,j), min(N,2j)]` and `j ∈ {1,…,N}`.

`1 ≤ j` is forced: `m ≤ 2j` with `m ≥ 1`. -/
theorem window_swap_shift (M N : ℕ) : ∀ (m j : ℕ),
    (m ∈ Finset.Icc (M + 1) N ∧ j ∈ window m) ↔
      (m ∈ Finset.Icc (max M j + 1) (min N (2 * j)) ∧ j ∈ Finset.Icc 1 N) := by
  intro m j
  simp only [Finset.mem_Icc, window, Finset.mem_Ico]
  omega

/-- **The double-counting step from a shifted foot.** The source index `j` is carried across
exactly `min(N,2j) − max(M,j)` of the cuts `M+1, …, N`. -/
theorem window_double_sum_shift (M N : ℕ) (F : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc (M + 1) N, ∑ j ∈ window m, F j
      = ∑ j ∈ Finset.Icc 1 N, ((min N (2 * j) - max M j : ℕ) : ℝ) * F j := by
  rw [Finset.sum_comm' (window_swap_shift M N) (f := fun _ j => F j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  congr 2
  omega

/-! ## Each dyadic block carries a fixed mass -/

variable {S : Setting}

/-- **The block estimate.** Let `λ ≥ 0` satisfy the cut balance above `M` and let the drift
coefficient `(m+1)ε(m)` be at least `1` above `M`. Then every dyadic block `(T, 2T]` with `T ≥ M`
carries at least `M λ_M ε(M)` of mass.

The mass is the same at every `T`: it is what the foot `M` sends across its own cut, and the
supercritical drift is exactly what stops it being absorbed lower down. -/
theorem cut_tail_ge (S : Setting) {lam : ℕ → ℝ} (hlam : ∀ j, 0 ≤ lam j)
    {M T : ℕ} (hM1 : 1 ≤ M) (hMT : M ≤ T)
    (hcb : ∀ m, M < m → lam m * (1 - S.eps m) = ∑ j ∈ window m, lam j * S.eps j)
    (hthr : ∀ m, M < m → 1 ≤ ((m : ℝ) + 1) * S.eps m) :
    (M : ℝ) * (lam M * S.eps M) ≤ ∑ m ∈ Finset.Icc (T + 1) (2 * T), lam m := by
  have hTN : T ≤ 2 * T := by omega
  -- the cuts above `M`, counted by source index
  have hdouble : ∑ m ∈ Finset.Icc (M + 1) (2 * T), lam m * (1 - S.eps m)
      = ∑ j ∈ Finset.Icc 1 (2 * T),
          ((min (2 * T) (2 * j) - max M j : ℕ) : ℝ) * (lam j * S.eps j) := by
    rw [← window_double_sum_shift M (2 * T) (fun j => lam j * S.eps j)]
    refine Finset.sum_congr rfl fun m hm => hcb m ?_
    have := Finset.mem_Icc.mp hm
    omega
  -- keep only the foot `M` and the window `(M, T]`
  have hsubset : insert M (Finset.Icc (M + 1) T) ⊆ Finset.Icc 1 (2 * T) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_Icc] at hj ⊢
    omega
  have hnn : ∀ j ∈ Finset.Icc 1 (2 * T),
      0 ≤ ((min (2 * T) (2 * j) - max M j : ℕ) : ℝ) * (lam j * S.eps j) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hlam j) (S.eps_pos hj1).le)
  have hsub_le : ∑ j ∈ insert M (Finset.Icc (M + 1) T),
        ((min (2 * T) (2 * j) - max M j : ℕ) : ℝ) * (lam j * S.eps j)
      ≤ ∑ j ∈ Finset.Icc 1 (2 * T),
        ((min (2 * T) (2 * j) - max M j : ℕ) : ℝ) * (lam j * S.eps j) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i hi _ => hnn i hi)
  have hnotmem : M ∉ Finset.Icc (M + 1) T := by simp only [Finset.mem_Icc]; omega
  have heval : ∑ j ∈ insert M (Finset.Icc (M + 1) T),
        ((min (2 * T) (2 * j) - max M j : ℕ) : ℝ) * (lam j * S.eps j)
      = (M : ℝ) * (lam M * S.eps M)
        + ∑ j ∈ Finset.Icc (M + 1) T, (j : ℝ) * (lam j * S.eps j) := by
    rw [Finset.sum_insert hnotmem]
    have hM : ((min (2 * T) (2 * M) - max M M : ℕ) : ℝ) = (M : ℝ) := by
      have h : (min (2 * T) (2 * M) - max M M : ℕ) = M := by omega
      rw [h]
    rw [hM]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hmem := Finset.mem_Icc.mp hj
    have h : (min (2 * T) (2 * j) - max M j : ℕ) = j := by omega
    rw [h]
  -- the supercritical drift converts the window into the same window on the left
  have hthr' : ∀ j ∈ Finset.Icc (M + 1) T,
      lam j * (1 - S.eps j) ≤ (j : ℝ) * (lam j * S.eps j) := by
    intro j hj
    have hjM : M < j := by have := Finset.mem_Icc.mp hj; omega
    have h := hthr j hjM
    nlinarith [hlam j]
  have hthrsum := Finset.sum_le_sum hthr'
  -- split the left-hand side at `T`
  have hsplit : ∑ m ∈ Finset.Icc (M + 1) (2 * T), lam m * (1 - S.eps m)
      = (∑ m ∈ Finset.Icc (M + 1) T, lam m * (1 - S.eps m))
        + ∑ m ∈ Finset.Icc (T + 1) (2 * T), lam m * (1 - S.eps m) := by
    rw [Icc_succ_eq_Ioc M (2 * T), Icc_succ_eq_Ioc M T, Icc_succ_eq_Ioc T (2 * T)]
    exact (Finset.sum_Ioc_consecutive _ hMT hTN).symm
  have htail : ∑ m ∈ Finset.Icc (T + 1) (2 * T), lam m * (1 - S.eps m)
      ≤ ∑ m ∈ Finset.Icc (T + 1) (2 * T), lam m := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := by have := Finset.mem_Icc.mp hm; omega
    nlinarith [hlam m, (S.eps_pos hm1).le]
  rw [hdouble] at hsplit
  linarith

/-! ## No invariant probability -/

/-- **`prop:doubling_phase`(2)–(3), in the form this library consumes.** If the drift coefficient
`(m+1)ε(m)` is at least `1` past an index `M ≥ max(d,1)`, the loop-closed chain carries no
invariant probability.

`Stat.pos` — `lem:doubling_irreducible` — is what makes the foot mass `M λ_M ε(M)` strictly
positive, and `Stat.summable` is what it contradicts. -/
theorem isEmpty_stat_of_supercritical (S : Setting) {M : ℕ} (hM1 : 1 ≤ M) (hMd : S.d ≤ M)
    (hthr : ∀ m, M < m → 1 ≤ ((m : ℝ) + 1) * S.eps m) : IsEmpty (Stat S none) := by
  constructor
  intro L
  have hlam : ∀ j, 0 ≤ L.lam (.lad j) := fun j => L.nonneg _
  have hpos : ∀ j, 0 < L.lam (.lad j) := fun _ => L.pos trivial
  have hcb : ∀ m, M < m →
      L.lam (.lad m) * (1 - S.eps m) = ∑ j ∈ window m, L.lam (.lad j) * S.eps j :=
    fun m hm => cut_balance L (lt_of_le_of_lt hMd hm) trivial
  have hinj : Function.Injective (fun j : ℕ => (St.lad j)) := by
    intro a b h; injection h
  have hsummable : Summable (fun j : ℕ => L.lam (.lad j)) := L.summable.comp_injective hinj
  have hδpos : 0 < (M : ℝ) * (L.lam (.lad M) * S.eps M) := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    exact mul_pos hMpos (mul_pos (hpos M) (S.eps_pos hM1))
  -- every dyadic block carries the same mass, so the partial sums grow without bound
  have hgrow : ∀ k : ℕ, (k : ℝ) * ((M : ℝ) * (L.lam (.lad M) * S.eps M))
      ≤ ∑ m ∈ Finset.Icc 1 (2 ^ k * M), L.lam (.lad m) := by
    intro k
    induction k with
    | zero =>
        have h := Finset.sum_nonneg
          (fun i (_ : i ∈ Finset.Icc 1 (2 ^ 0 * M)) => hlam i)
        simpa using h
    | succ k ih =>
        have hMT : M ≤ 2 ^ k * M :=
          Nat.le_mul_of_pos_left M (Nat.two_pow_pos k)
        have hstep := cut_tail_ge S hlam hM1 hMT hcb hthr
        have hpow : 2 ^ (k + 1) * M = 2 * (2 ^ k * M) := by ring
        have hsplit : ∑ m ∈ Finset.Icc 1 (2 * (2 ^ k * M)), L.lam (.lad m)
            = (∑ m ∈ Finset.Icc 1 (2 ^ k * M), L.lam (.lad m))
              + ∑ m ∈ Finset.Icc (2 ^ k * M + 1) (2 * (2 ^ k * M)), L.lam (.lad m) := by
          rw [Icc_one_eq_Ioc_zero (2 * (2 ^ k * M)), Icc_one_eq_Ioc_zero (2 ^ k * M),
            Icc_succ_eq_Ioc (2 ^ k * M) (2 * (2 ^ k * M))]
          exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)).symm
        rw [hpow, hsplit]
        push_cast
        linarith
  have hbound : ∀ k : ℕ, ∑ m ∈ Finset.Icc 1 (2 ^ k * M), L.lam (.lad m)
      ≤ ∑' j, L.lam (.lad j) :=
    fun k => hsummable.sum_le_tsum _ (fun i _ => hlam i)
  obtain ⟨k, hk⟩ := exists_nat_gt ((∑' j, L.lam (.lad j)) / ((M : ℝ) * (L.lam (.lad M) * S.eps M)))
  rw [div_lt_iff₀ hδpos] at hk
  linarith [hgrow k, hbound k]

/-! ## The family: rows (a), (c) and (e) of the phase diagram -/

/-- **`prop:doubling_phase`(3), the `1 ≤ c < 2` half.** At `s = 1` the drift coefficient is the
constant `c`, so `c ≥ 1` already forbids an invariant probability — with no threshold to find.

`c < 2` enters only through the existence of `S` (`lem:doubling_range`). -/
theorem isEmpty_stat_of_family_ge_one {c : ℝ} (hc1 : 1 ≤ c)
    (S : Setting) (hS : S.eps = epsCS c 1) : IsEmpty (Stat S none) := by
  refine isEmpty_stat_of_supercritical S (M := S.d) S.d_pos le_rfl ?_
  intro m _
  rw [hS, base_mul_epsCS, sub_self, Real.rpow_zero, mul_one]
  exact hc1

/-- **`prop:doubling_phase`(2), weakened to non-existence.** At `s < 1` the drift coefficient
`c(m+1)^{1−s}` grows without bound, so it passes `1` at an explicit index and the loop closure
carries no invariant probability.

The paper proves the stronger statement that `X` is *transient*; that is not claimed here. -/
theorem isEmpty_stat_of_family_lt_one {c s : ℝ} (hc : 0 < c) (hs : s < 1)
    (S : Setting) (hS : S.eps = epsCS c s) : IsEmpty (Stat S none) := by
  obtain ⟨m₀, hm₀⟩ := exists_threshold_rpow (c := 1 / c) (e := 1 - s) (by positivity) (by linarith)
  refine isEmpty_stat_of_supercritical S (M := max m₀ (max S.d 1)) (le_max_of_le_right
    (le_max_right S.d 1)) (le_max_of_le_right (le_max_left S.d 1)) ?_
  intro m hm
  have hm0 : m₀ ≤ m := le_of_lt (lt_of_le_of_lt (le_max_left m₀ (max S.d 1)) hm)
  have hb := hm₀ m hm0
  rw [hS, base_mul_epsCS]
  rw [div_le_iff₀ hc] at hb
  linarith

end GFNBounds.Doubling
