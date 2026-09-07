import GFNBounds.Doubling.StatExists
import GFNBounds.Doubling.Drift
import GFNBounds.Doubling.Lyapunov

/-!
# The loop closure carries an invariant probability whenever the doubling flux is subcritical

**`prop:doubling_phase`(1), Step 3** — `app_doubling.tex:510–624` (Proposition 99 of the ICLR
build), and `theo:doubling_main`(1), row `s > 1`.

> In the setting of Definition `def:doubling_setting`, let `(c,s)` lie in the standing range and
> let `X` be the loop-closed backward chain on the infinite graph. Then `X` is irreducible, and:
> (1) if `s > 1`, then `X` is positive recurrent […]
>
> *Step 3 (positive recurrence for `s>1`).* Define `V₁` on the whole loop closure by `V₁(j) := j`
> at a ladder state `j` and `V₁(s₀) = V₁(s_f) := 0`. By Proposition `prop:doubling_drift` the
> drift of `V₁` at a ladder state `j` is `c(j+1)^{1−s} − 1`, which tends to `−1` as
> `j → ∞` because `s > 1`; fix `j₀` with `c(j+1)^{1−s} − 1 ≤ −½` for `j > j₀`. Then `V₁ ≥ 0` has
> finite sublevel sets, `E(V₁(X₁) | X₀ = x) < +∞` for every `x`, and the drift is at most `−½` off
> the finite set `{s₀,s_f,1,…,j₀}`: Foster's criterion for positive recurrence applies, and `X` is
> positive recurrent.

## What is proved, and in which form

Exactly as in `GFNBounds.Doubling.StatExists`, which closes row (b) of the phase diagram, the
conclusion delivered is the existence of an invariant probability — `Nonempty (Stat S none)` —
and it is *constructed*, not deduced from a chain. `statSeq` of `StatExists.lean` already solves
the row-corrected cut balance at **every** `Setting`, and `statSeq_point` already turns it into
the pointwise balance; the only ingredient that was special to `s = 1`, `0 < c < 1` was
summability. This file replaces that ingredient by a threshold hypothesis that covers both rows:

  `(m+1)ε(m) ≤ θ < 1` for every `m ≥ m₀`.

`(m+1)ε(m)` is the paper's own drift coefficient. `prop:doubling_drift` gives the drift of
`V₁(j) = j` at `j` as `(j+1)ε(j) − 1`, so the hypothesis says exactly that Step 3's Foster drift
is at most `θ − 1 < 0` past `m₀` — the same inequality, consumed by a summability estimate
instead of by Foster's criterion. At `s = 1` it holds with `θ = c` and `m₀ = 0` (row (b), Step 5);
at `s > 1` with `θ = ½` and the paper's own `m₀ ≥ (2c)^{1/(s−1)}` (row (f), Step 3).

The estimate itself is the double-counting of `GFNBounds.Doubling.Summable`, carried one step
further: summing the cut balance over `m ∈ {1,…,N}` and exchanging the double sum gives

  `Σ_{m≤N} λ_m (1 − (m+1)ε(m)) ≤ Σ_{m≤N} g_m`

for any excess `g` dominating the boundary data, because each `j` occurs in exactly
`min(N,2j) − j ≤ j` of the windows `W(1),…,W(N)`. That is `partial_sum_weighted_le`, and it is
`Summable.partial_sum_le` with `ε(j)(1+j) = c` no longer substituted — which is what frees it
from `s = 1`.

## SCOPE (disclosed)

* **This is not "the chain is positive recurrent".** It is the existence of an invariant
  probability, which for an irreducible chain is equivalent to positive recurrence but is here a
  construction, not a translation of one. No return time is mentioned, Foster's criterion is not
  available and is not used, and uniqueness is not claimed.
* **The threshold is the only hypothesis.** Nothing here needs `s ≥ 0`, `c < 2^s` or the family
  at all: the standing range enters only through the existence of the `Setting`, whose
  `epsMax_lt_one` field is `lem:doubling_range`. `exists_stat_of_family_gt_one` is the instance at
  `ε = ε_{c,s}`, `s > 1`.
* **Row (b) is re-derived, not re-proved.** `exists_stat_of_family_one` is the same general lemma
  at `θ = c`, `m₀ = 0`; `GFNBounds.Doubling.exists_stat_of_family` remains the primary certificate
  for that row. It is kept because it is the consistency check that the general threshold
  specialises correctly.
* **The other rows are untouched.** `s < 1` (Step 4) and `s = 1` with `c ≥ 1` (Steps 6–8) are
  non-existence statements and live in `GFNBounds.Doubling.PhaseEmpty`; row (d), `c = 1/ln 2`, is
  open in the paper itself.
* The constant is effective: `Σ_{m=1}^{N} λ_m ≤ (j̄ + Σ_{m≤m₀} λ_m (m+1)ε(m))/(1−θ)` at every `N`,
  with `m₀` the paper's `(2c)^{1/(s−1)}` at `s > 1`. At `s = 1`, `m₀ = 0` and the bound collapses
  to `StatExists.lean`'s `j̄/(1−c)`.

## Hypothesis checklist against `prop:doubling_phase`(1)

| paper hypothesis | here |
|---|---|
| standing range `s ≥ 0`, `0 < c < 2^s` | ⚠ weakened: only `0 < c`, and the range through the `Setting` |
| `s > 1` | ✓ carried (`hs`) |
| the loop closure | ✓ carried (`cap = none`) |
| `prop:doubling_drift`'s drift `c(j+1)^{1−s} − 1` | ✓ carried, as the threshold `(m+1)ε(m) ≤ θ` |
| `j₀` with drift `≤ −½` past it | ✓ carried and explicit: `m₀ ≥ (2c)^{1/(s−1)}` (`exists_threshold_rpow`) |
| `V₁ ≥ 0` has finite sublevel sets; `E(V₁(X₁)) < ∞` | ✗ not needed: no Foster |
| Foster's criterion | ✗ not used and not available |
| the conclusion "positive recurrent" | ⚠ weakened to `Nonempty (Stat S none)`, which is what every consumer in this library takes |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

variable {S : Setting}

/-! ## The weighted partial-sum bound

`GFNBounds.Doubling.partial_sum_le` substitutes `ε(j)(1+j) = c` at the last step, which is where
it becomes an `s = 1` statement. Stopping one step earlier keeps the coefficient
`1 − (m+1)ε(m)` — the paper's drift of `V₁` at `m`, up to sign — and costs nothing. -/

/-- **The partial-sum bound, before the family is substituted.** A non-negative sequence obeying
the cut balance up to an excess `g` on `{1,…,N}` satisfies
`Σ_{m≤N} λ_m(1 − (m+1)ε(m)) ≤ Σ_{m≤N} g_m`.

The whole content is that `min(N,2j) − j ≤ j`, so the coefficient of `λ_j` after the exchange of
the double sum is at least `1 − ε(j)(1+j)`. -/
theorem partial_sum_weighted_le {lam g : ℕ → ℝ} (hlam : ∀ j, 0 ≤ lam j) (N : ℕ)
    (hrec : ∀ m, 1 ≤ m → m ≤ N →
      lam m * (1 - S.eps m) ≤ ∑ j ∈ window m, lam j * S.eps j + g m) :
    ∑ m ∈ Finset.Icc 1 N, lam m * (1 - ((m : ℝ) + 1) * S.eps m)
      ≤ ∑ m ∈ Finset.Icc 1 N, g m := by
  have hsum : ∑ m ∈ Finset.Icc 1 N, lam m * (1 - S.eps m)
      ≤ ∑ m ∈ Finset.Icc 1 N, (∑ j ∈ window m, lam j * S.eps j + g m) :=
    Finset.sum_le_sum fun m hm =>
      hrec m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
  rw [Finset.sum_add_distrib, window_double_sum] at hsum
  have hcount : ∑ j ∈ Finset.Icc 1 N, ((min N (2 * j) - j : ℕ) : ℝ) * (lam j * S.eps j)
      ≤ ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * (lam j * S.eps j) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hk : ((min N (2 * j) - j : ℕ) : ℝ) ≤ (j : ℝ) := by
      have h : (min N (2 * j) - j : ℕ) ≤ j := by omega
      exact_mod_cast h
    exact mul_le_mul_of_nonneg_right hk (mul_nonneg (hlam j) (S.eps_pos hj1).le)
  have hsplit : ∑ m ∈ Finset.Icc 1 N, lam m * (1 - ((m : ℝ) + 1) * S.eps m)
      = ∑ m ∈ Finset.Icc 1 N, lam m * (1 - S.eps m)
        - ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * (lam j * S.eps j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsplit]
  linarith

/-- **The threshold form.** If `(m+1)ε(m) ≤ θ` past `m₀`, the partial sums of `λ` are bounded by
the excess plus the finitely many terms below `m₀`, divided by `1 − θ`.

The terms below `m₀` are kept as they stand rather than estimated: `λ` is the unknown there, and
the bound has to be uniform in `N` only. -/
theorem partial_sum_le_of_threshold {lam g : ℕ → ℝ} (hlam : ∀ j, 0 ≤ lam j)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (m₀ : ℕ)
    (hthr : ∀ m, 1 ≤ m → m₀ ≤ m → ((m : ℝ) + 1) * S.eps m ≤ θ)
    (hrec : ∀ m, 1 ≤ m → lam m * (1 - S.eps m) ≤ ∑ j ∈ window m, lam j * S.eps j + g m)
    (N : ℕ) :
    (1 - θ) * ∑ m ∈ Finset.Icc 1 N, lam m
      ≤ (∑ m ∈ Finset.Icc 1 N, g m)
        + ∑ m ∈ Finset.Icc 1 m₀, lam m * (((m : ℝ) + 1) * S.eps m) := by
  have hkey := partial_sum_weighted_le hlam N (fun m hm1 _ => hrec m hm1)
  have hstep : (1 - θ) * ∑ m ∈ Finset.Icc 1 N, lam m
      ≤ ∑ m ∈ Finset.Icc 1 N, lam m * (1 - ((m : ℝ) + 1) * S.eps m)
        + ∑ m ∈ Finset.Icc 1 N,
            (if m ≤ m₀ then lam m * (((m : ℝ) + 1) * S.eps m) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    by_cases hmm : m ≤ m₀
    · rw [if_pos hmm]
      nlinarith [mul_nonneg hθ0 (hlam m)]
    · rw [if_neg hmm]
      have h := hthr m hm1 (by omega)
      nlinarith [mul_le_mul_of_nonneg_left h (hlam m)]
  have hcut : ∑ m ∈ Finset.Icc 1 N, (if m ≤ m₀ then lam m * (((m : ℝ) + 1) * S.eps m) else 0)
      ≤ ∑ m ∈ Finset.Icc 1 m₀, lam m * (((m : ℝ) + 1) * S.eps m) := by
    have hstep2 : ∀ m ∈ Finset.Icc 1 N,
        (if m ≤ m₀ then lam m * (((m : ℝ) + 1) * S.eps m) else 0)
          ≤ if m ∈ Finset.Icc 1 m₀ then lam m * (((m : ℝ) + 1) * S.eps m) else 0 := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      by_cases hmm : m ≤ m₀
      · rw [if_pos hmm, if_pos (Finset.mem_Icc.mpr ⟨hm1, hmm⟩)]
      · rw [if_neg hmm, if_neg (fun hmem => hmm (Finset.mem_Icc.mp hmem).2)]
    refine le_trans (Finset.sum_le_sum hstep2) ?_
    rw [Finset.sum_ite_mem]
    refine Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right ?_
    intro i hi _
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    exact mul_nonneg (hlam i) (mul_nonneg (base_pos i).le (S.eps_pos hi1).le)
  linarith

/-! ## Summability of the constructed sequence -/

/-- **The uniform bound on the partial sums of `statSeq`.** At `θ = c`, `m₀ = 0` this is
`statSeq_partial_sum_le`'s `j̄/(1−c)`. -/
theorem statSeq_partial_sum_bounded {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (m₀ : ℕ)
    (hthr : ∀ m, 1 ≤ m → m₀ ≤ m → ((m : ℝ) + 1) * S.eps m ≤ θ) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, statSeq S m
      ≤ (S.jbar + ∑ m ∈ Finset.Icc 1 m₀, statSeq S m * (((m : ℝ) + 1) * S.eps m)) / (1 - θ) := by
  have hpos : (0 : ℝ) < 1 - θ := by linarith
  rw [le_div_iff₀ hpos]
  have h := partial_sum_le_of_threshold (S := S) (statSeq_nonneg S) hθ0 m₀ hthr
    (g := rowTail S) (fun m hm => le_of_eq (statSeq_cut hm)) N
  have h2 := sum_rowTail_le (S := S) N
  linarith

/-- **Summability under the threshold.** The one place `θ < 1` is spent. -/
theorem summable_statSeq_of_threshold {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (m₀ : ℕ)
    (hthr : ∀ m, 1 ≤ m → m₀ ≤ m → ((m : ℝ) + 1) * S.eps m ≤ θ) : Summable (statSeq S) := by
  refine summable_of_sum_range_le (f := statSeq S) (statSeq_nonneg S)
    (c := 1 + (S.jbar + ∑ m ∈ Finset.Icc 1 m₀,
      statSeq S m * (((m : ℝ) + 1) * S.eps m)) / (1 - θ)) ?_
  intro n
  have hsub : Finset.range n ⊆ insert 0 (Finset.Icc 1 n) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => statSeq_nonneg S i
  rw [Finset.sum_insert (by simp), statSeq_zero] at hle
  have := statSeq_partial_sum_bounded (S := S) hθ0 hθ1 m₀ hthr n
  linarith

/-! ## The invariant probability -/

/-- **The construction, given summability.** Everything but summability in `exists_stat_none` is
independent of the family: `statSeq` solves the row-corrected cut balance at every `Setting`,
`statSeq_point` is its pointwise form, and `inv_of_pointwise` promotes that to the integral
invariance `Stat` asks for. -/
theorem exists_stat_none_of_summable (S : Setting) (hsummable : Summable (statSeq S)) :
    Nonempty (Stat S none) := by
  have hladder : HasSum (fun k : ℕ => statMeas S (.lad k)) (∑' k, statSeq S k) :=
    hsummable.hasSum
  have hZ : HasSum (statMeas S) ((∑' k, statSeq S k) + 1) := by
    have h := hasSum_st (g := statMeas S) hladder
    simpa using h
  set Z : ℝ := (∑' k, statSeq S k) + 1 with hZ_def
  have hZpos : 0 < Z := by
    have h1 : (0 : ℝ) ≤ ∑' k, statSeq S k := tsum_nonneg (statSeq_nonneg S)
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

/-- **The threshold criterion.** A backward policy whose drift coefficient `(m+1)ε(m)` is
eventually at most some `θ < 1` carries an invariant probability on the loop closure. -/
theorem exists_stat_of_threshold (S : Setting) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (m₀ : ℕ)
    (hthr : ∀ m, 1 ≤ m → m₀ ≤ m → ((m : ℝ) + 1) * S.eps m ≤ θ) : Nonempty (Stat S none) :=
  exists_stat_none_of_summable S (summable_statSeq_of_threshold hθ0 hθ1 m₀ hthr)

/-! ## The family: rows (b) and (f) of the phase diagram -/

/-- **Step 3's `j₀`, made explicit.** At `s > 1` the drift coefficient falls below `½` past
`m₀ ≥ (2c)^{1/(s−1)}` — the paper's "fix `j₀` with `c(j+1)^{1−s} − 1 ≤ −½` for `j > j₀`". -/
theorem exists_threshold_family {c s : ℝ} (hc : 0 < c) (hs : 1 < s) :
    ∃ m₀ : ℕ, ∀ m : ℕ, 1 ≤ m → m₀ ≤ m → ((m : ℝ) + 1) * epsCS c s m ≤ 1 / 2 := by
  obtain ⟨m₀, hm₀⟩ := exists_threshold_rpow (c := 2 * c) (e := s - 1) (by linarith) (by linarith)
  refine ⟨m₀, fun m _ hm => ?_⟩
  have hu : (0 : ℝ) < (m : ℝ) + 1 := base_pos m
  have hb := hm₀ m hm
  have hpos : (0 : ℝ) < ((m : ℝ) + 1) ^ (s - 1) := Real.rpow_pos_of_pos hu _
  have hpow : ((m : ℝ) + 1) ^ (1 - s) = (((m : ℝ) + 1) ^ (s - 1))⁻¹ := by
    rw [show (1 : ℝ) - s = -(s - 1) by ring, Real.rpow_neg hu.le]
  rw [base_mul_epsCS, hpow, mul_inv_le_iff₀ hpos]
  linarith

/-- **`prop:doubling_phase`(1), in the form this library consumes.** At `s > 1` the loop-closed
chain carries an invariant probability, positive at every state.

The standing range `0 < c < 2^s` enters only through the existence of `S`: `lem:doubling_range`
is what makes `ε_{c,s}` a `Setting`. -/
theorem exists_stat_of_family_gt_one {c s : ℝ} (hc : 0 < c) (hs : 1 < s)
    (S : Setting) (hS : S.eps = epsCS c s) : Nonempty (Stat S none) := by
  obtain ⟨m₀, hm₀⟩ := exists_threshold_family hc hs
  refine exists_stat_of_threshold S (θ := 1 / 2) (by norm_num) (by norm_num) m₀ ?_
  intro m hm1 hm
  rw [hS]
  exact hm₀ m hm1 hm

/-- **Row (b) re-derived from the same threshold**, at `θ = c` and `m₀ = 0`: at `s = 1` the drift
coefficient is the constant `c`. `GFNBounds.Doubling.exists_stat_of_family` is the primary
certificate for this row; this is the consistency check that the general criterion specialises to
it. -/
theorem exists_stat_of_family_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Setting) (hS : S.eps = epsCS c 1) : Nonempty (Stat S none) := by
  refine exists_stat_of_threshold S (θ := c) hc0.le hc1 0 ?_
  intro m _ _
  rw [hS, base_mul_epsCS, sub_self, Real.rpow_zero, mul_one]

end GFNBounds.Doubling
