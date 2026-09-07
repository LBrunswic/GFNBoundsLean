import GFNBounds.Doubling.Irreducible

/-!
# Pointwise invariance implies the integral form

**`def:doubling_setting`** — `app_doubling.tex:13–84`, the bridge its Lean rendering names but
leaves open.

> `Stat` carries invariance in the **integral** form `∫P⋆f dλ = ∫f dλ` against bounded `f` […]
> The pointwise form `λT = λ` is equivalent on a countable space; that bridge is
> `Stat.of_pointwise`, and nothing below is blocked while it is open.
> (`GFNBounds/Doubling/Setting.lean:327–330`)

This file supplies that bridge on the loop closure. The pointwise form is written out rather than
abstracted, because on this graph the incoming edges of a ladder state are explicit: `k` receives
the decrement out of `k+1`, the doubling out of `k/2` when `k` is even and positive, and the
target row.

## The modelling decision

**No density action `P` is introduced.** `inv_of_pointwise` takes the three balance equations as
hypotheses — one at the sink, one at each ladder state — and derives the integral identity by
splitting `∫P⋆f dμ` into four `HasSum`s and matching them against the four terms of `∫f dμ`. The
only non-trivial step is that the doubling flux, indexed by its *source* `k+1`, is the same sum as
the doubling flux indexed by its *target* `2(k+1)`; that is `Function.Injective.hasSum_iff` along
`n ↦ 2(n+1)`, whose complement in `ℕ` is exactly `{0} ∪ (odd numbers)`, where the target-indexed
summand vanishes.

## SCOPE (disclosed)

* Stated for `cap = none` only. On the truncation the incoming edges differ at the cap
  (`lem:doubling_truncation_irreducible`), and `GFNBounds.Doubling.TruncationStat` already
  constructs `Stat S (some K)` by finite linear algebra, so no truncated version is needed here.
* The equation at the source is not separate: `s₀ = lad 0`, and `hpt` at `k = 0` is the balance
  there. What is separate is `hsink`, `μ(s_f) = μ(s₀)`, the sink having the single incoming edge
  `s₀ → s_f`.
* Non-negativity of `μ` is used only for the domination bounds that give summability of the two
  flux series; no positivity is needed and none is concluded.

## Hypothesis checklist

| what the equivalence needs | here |
|---|---|
| `μ ≥ 0` | ✓ carried (`hnn`) |
| `μ` summable along the ladder | ✓ carried (`hsum`); summability on `St` follows |
| `μT = μ` at every state | ✓ carried as `hsink` and `hpt` |
| `f` bounded | ✓ carried, exactly as `Stat.inv` states it |
| normalisation `Σμ = 1` | ⚠ weakened: not needed, and not assumed |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

variable {S : Setting}

/-- `ℕ ≃ St`: `0 ↦ s_f` and `k+1 ↦ lad k`. It is the enumeration that makes a sum over `St` a sum
over `ℕ` with the sink split off first. -/
def stEquiv : ℕ ≃ St where
  toFun := fun n => match n with | 0 => .sink | (k + 1) => .lad k
  invFun := fun x => match x with | .sink => 0 | .lad k => k + 1
  left_inv := by intro n; cases n <;> rfl
  right_inv := by rintro (k | _) <;> rfl

/-- A summable family on the ladder extends to `St` by adding the value at the sink. -/
theorem hasSum_st {g : St → ℝ} {A : ℝ} (h : HasSum (fun k : ℕ => g (.lad k)) A) :
    HasSum g (A + g .sink) := by
  rw [← Equiv.hasSum_iff stEquiv]
  have h1 : (fun n : ℕ => (g ∘ stEquiv) (n + 1)) = fun k : ℕ => g (St.lad k) := rfl
  have h2 : HasSum (fun n : ℕ => (g ∘ stEquiv) (n + 1)) A := by rw [h1]; exact h
  have h3 := (hasSum_nat_add_iff (f := g ∘ stEquiv) 1).mp h2
  rw [Finset.sum_range_one] at h3
  exact h3

/-- **`Stat.of_pointwise`, on the loop closure.** A non-negative, ladder-summable measure on `St`
satisfying the pointwise balance equations satisfies the integral invariance `∫P⋆f dμ = ∫f dμ`
against every bounded `f` — which is the `inv` field of `Stat` and of `PreStat`. -/
theorem inv_of_pointwise (S : Setting) {mu : St → ℝ}
    (hnn : ∀ x, 0 ≤ mu x)
    (hsum : Summable (fun k : ℕ => mu (.lad k)))
    (hsink : mu .sink = mu (.lad 0))
    (hpt : ∀ k : ℕ, mu (.lad k)
      = mu (.lad (k + 1)) * (1 - S.eps (k + 1))
        + (if 1 ≤ k ∧ 2 ∣ k then mu (.lad (k / 2)) * S.eps (k / 2) else 0)
        + mu .sink * S.row k)
    (f : St → ℝ) (hf : ∃ C, ∀ x, |f x| ≤ C) :
    ∑' x, mu x * pstar S none f x = ∑' x, mu x * f x := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC .sink)
  have hsum1 : Summable (fun k : ℕ => mu (St.lad (k + 1))) := (summable_nat_add_iff 1).mpr hsum
  set a : ℕ → ℝ := fun k => mu (.lad (k + 1)) * (1 - S.eps (k + 1)) * f (.lad k) with ha_def
  set b : ℕ → ℝ := fun k =>
    (if 1 ≤ k ∧ 2 ∣ k then mu (.lad (k / 2)) * S.eps (k / 2) else 0) * f (.lad k) with hb_def
  set c : ℕ → ℝ := fun k => mu .sink * S.row k * f (.lad k) with hc_def
  set e : ℕ → ℝ := fun k => mu (.lad (k + 1)) * S.eps (k + 1) * f (.lad (2 * (k + 1))) with he_def
  have hepsle : ∀ k : ℕ, S.eps (k + 1) ≤ 1 :=
    fun k => le_trans (S.eps_le (Nat.le_add_left 1 k)) S.epsMax_lt_one.le
  have heps0 : ∀ k : ℕ, 0 ≤ S.eps (k + 1) := fun k => (S.eps_pos (Nat.le_add_left 1 k)).le
  have hA : Summable a := by
    refine Summable.of_norm_bounded (g := fun k => C * mu (St.lad (k + 1))) (hsum1.mul_left C) ?_
    intro k
    rw [Real.norm_eq_abs, ha_def]
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg (hnn _), abs_of_nonneg (by linarith [hepsle k, heps0 k])]
    have h1 : |f (St.lad k)| ≤ C := hC _
    have hM : 0 ≤ mu (St.lad (k + 1)) := hnn _
    have hs0 : 0 ≤ 1 - S.eps (k + 1) := by linarith [hepsle k]
    have hs1 : 1 - S.eps (k + 1) ≤ 1 := by linarith [heps0 k]
    calc mu (St.lad (k + 1)) * (1 - S.eps (k + 1)) * |f (St.lad k)|
        ≤ mu (St.lad (k + 1)) * (1 - S.eps (k + 1)) * C :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hM hs0)
      _ ≤ mu (St.lad (k + 1)) * 1 * C :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 hM) hC0
      _ = C * mu (St.lad (k + 1)) := by ring
  have hE : Summable e := by
    refine Summable.of_norm_bounded (g := fun k => C * mu (St.lad (k + 1))) (hsum1.mul_left C) ?_
    intro k
    rw [Real.norm_eq_abs, he_def]
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg (hnn _), abs_of_nonneg (heps0 k)]
    have h1 : |f (St.lad (2 * (k + 1)))| ≤ C := hC _
    have hM : 0 ≤ mu (St.lad (k + 1)) := hnn _
    calc mu (St.lad (k + 1)) * S.eps (k + 1) * |f (St.lad (2 * (k + 1)))|
        ≤ mu (St.lad (k + 1)) * S.eps (k + 1) * C :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hM (heps0 k))
      _ ≤ mu (St.lad (k + 1)) * 1 * C :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hepsle k) hM) hC0
      _ = C * mu (St.lad (k + 1)) := by ring
  have hinj : Function.Injective (fun n : ℕ => 2 * (n + 1)) := by
    intro x y h
    simp only at h
    omega
  have hzero : ∀ x ∉ Set.range (fun n : ℕ => 2 * (n + 1)), b x = 0 := by
    intro x hx
    have hcond : ¬ (1 ≤ x ∧ 2 ∣ x) := by
      rintro ⟨hx1, m, rfl⟩
      refine hx ⟨m - 1, ?_⟩
      simp only
      omega
    rw [hb_def]
    simp only [hcond, if_false, zero_mul]
  have hcomp : b ∘ (fun n : ℕ => 2 * (n + 1)) = e := by
    funext n
    have h1 : (2 * (n + 1)) / 2 = n + 1 := by omega
    have h2 : (1 ≤ 2 * (n + 1) ∧ 2 ∣ 2 * (n + 1)) := ⟨by omega, ⟨n + 1, rfl⟩⟩
    simp only [Function.comp_apply, hb_def, he_def, h1, if_pos h2]
  have hBsum : HasSum b (∑' k, e k) := by
    rw [← hinj.hasSum_iff hzero, hcomp]
    exact hE.hasSum
  have hCsum : HasSum c (∑ k ∈ Finset.Icc 1 S.d, c k) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro k hk
    have hrow : S.row k = 0 := by
      by_contra hne
      exact hk (Finset.mem_Icc.mpr (S.row_supp hne))
    rw [hc_def]
    simp [hrow]
  have hCval : ∑ k ∈ Finset.Icc 1 S.d, c k = mu .sink * pstar S none f .sink := by
    rw [pstar_sink, Finset.mul_sum, hc_def]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hR1 : HasSum (fun k : ℕ => mu (.lad k) * f (.lad k))
      (∑' k, a k + ∑' k, e k + ∑ k ∈ Finset.Icc 1 S.d, c k) := by
    refine ((hA.hasSum.add hBsum).add hCsum).congr_fun ?_
    intro k
    rw [hpt k, ha_def, hb_def, hc_def]
    ring
  have hR := hasSum_st (g := fun x => mu x * f x) hR1
  have hL1 : HasSum (fun k : ℕ => mu (.lad (k + 1)) * pstar S none f (.lad (k + 1)))
      (∑' k, e k + ∑' k, a k) := by
    refine (hE.hasSum.add hA.hasSum).congr_fun ?_
    intro k
    rw [pstar_lad_succ, if_pos (by trivial), ha_def, he_def]
    ring
  have hL2 := (hasSum_nat_add_iff
    (f := fun k : ℕ => mu (.lad k) * pstar S none f (.lad k)) 1).mp hL1
  rw [Finset.sum_range_one] at hL2
  have hL := hasSum_st (g := fun x => mu x * pstar S none f x) hL2
  rw [hL.tsum_eq, hR.tsum_eq, hCval, hsink]
  simp only [pstar_src]
  ring

end GFNBounds.Doubling
