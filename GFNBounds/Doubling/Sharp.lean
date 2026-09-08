import GFNBounds.Doubling.Coupling

/-!
# `theo:doubling_sharp`: the rescaled profile converges, and its limit is determined

**`theo:doubling_sharp`** — `app_doubling.tex:1323–1341`, proof at `1535–1658`.

> Let `s = 1` and `0 < c < 1`, with the integer `m₀` of `theo:doubling_decay`, and let `(λ_j)` be
> any positive sequence satisfying `eq:doubling_cut` for every `m > d`. Then
> `lim_j λ_j j^{p_*}` exists and lies in `[c₁',c₂']` for every pair `0 < c₁' ≤ c₂'` for which
> `eq:doubling_decay` holds with `c₁'` and `c₂'`; writing `C` for that limit,
> `λ_j = C j^{−p_*}(1+o(1))`, `C` is determined by `c`, `d` and `λ_1,…,λ_d`, and there are
> `ϑ ∈ (0,1)` depending on `c` alone and `c₆ > 0` with `|λ_j j^{p_*} − C| ≤ c₆ j^{−ϑ}`.

## What is proved here, and what is carried as a hypothesis

Everything except the **rate** `eq:doubling_rate`. Precisely:

* `uu_diff_le` — the paper's two "profiles differ by little" bullets, merged into one and with a
  better constant: for every level `ℓ ≥ L` and every `i`, two indices `m, m' ≥ 2^i ℓ` have
  `|u_m − u_{m'}| ≤ c₂(1−ω)^i + 2c₂c₃/ℓ`. The paper's second bullet gets `3c₂c₃/ℓ`; the saving is
  `Coupling.coupling_above`, which removes the need for a second descent at the level `2^jℓ`.
* `sharp_limit` — the third bullet: `u_m` is Cauchy, hence converges to a `C ∈ [c₁,c₂]`, and
  `|u_m − C| ≤ c₂(1−ω)^i + 2c₂c₃/ℓ` at every `m ≥ 2^i ℓ`. Since `u_m = λ_m m^{p_*}`, this is
  `eq:doubling_sharp`.
* `cutBal_unique` — the fifth bullet: the cut balance determines the whole sequence, hence `C`,
  from `c`, `d` and `λ_1,…,λ_d`.

The one input taken as a hypothesis here is `lem:doubling_weight` (`app_doubling.tex:1343–1383`),
proved in `Weight.lean` (`Decay.weight_bound`, from `lem:doubling_escape` and
`lem:doubling_product`) and discharged in `SharpFull.lean`. It enters as the named hypothesis

  `hweight : ∀ ℓ y, L ≤ ℓ → 2ℓ ≤ y → |descW ℓ u y − descP ℓ u y| ≤ c₂c₃/ℓ`,

which is `E(|Z_ℓ − 1| ∣ Y_0 = y) ≤ c₃/ℓ` combined with `0 < u ≤ c₂`, since
`descW ℓ u y − descP ℓ u y = E((Z_ℓ − 1) u_{Y_{N_ℓ}} ∣ Y_0 = y)`. This is the same discipline as
`Decay.decay_block` in `Descent.lean`: the input is a hypothesis here and is discharged one file
up.

## SCOPE (disclosed)

* **`eq:doubling_rate` is not proved in this file.** The convergence is proved with the explicit
  error `c₂(1−ω)^i + 2c₂c₃/ℓ`, valid at every level `ℓ ≥ L` and every `i` with `2^iℓ ≤ m`; the
  optimisation over `ℓ = ⌈m^ϑ⌉`, `i = ⌊log₂(m/ℓ)⌋` that turns it into `c₆ m^{−ϑ}` with
  `ϑ = α/(1+α)`, `α = log₂(1/(1−ω))`, is `SharpRate.lean` (`Decay.sharp_rate_explicit`), and the
  assembled theorem is `SharpFull.lean` (`Decay.sharp_of_cutBal`, `Decay.sharp_explicit`). `ϑ`
  and `c₆` therefore do not appear here.
* The paper's `ℓ₄` and `ℓ₃` are replaced by one integer `L` subject to three effective conditions
  (`20 ≤ L`, `32cτ ≤ L`, `d < 2L`); see `Doeblin.lean`.
* `theo:doubling_decay`(2) — the two-sided bound `c₁ ≤ u_m ≤ c₂` — is a hypothesis, as it is in
  the paper's own proof; `Descent.decay_two_sided` proves it from `eq:doubling_product`.
* `C > 0` is delivered (`c₁ ≤ C` with `c₁ > 0`), and the statement "`C` lies in `[c₁',c₂']` for
  *every* admissible pair" is exactly `sharp_limit`'s conclusion `c₁ ≤ C ∧ C ≤ c₂` read at the
  pair supplied.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1`, `p = p_*` | ✓ carried (`Decay`) |
| `(λ_j)` positive satisfying `eq:doubling_cut` at every `m > d` | ✓ carried (`Decay.CutBal d lam ⊤`) |
| `theo:doubling_decay`(2): `0 < c₁ ≤ u_m ≤ c₂` | ✓ carried as the hypothesis `hbd` |
| `lem:doubling_weight`: `E(\|Z_ℓ−1\|) ≤ c₃/ℓ` at `ℓ ≥ ℓ₃`, `y ≥ 2ℓ` | ⚠ **carried as the hypothesis `hweight`**, in the form the proof consumes |
| `ℓ ≥ ℓ₄ ≥ ℓ₃`, `m₀` | ⚠ **replaced** by `20 ≤ L`, `32cτ ≤ L`, `d < 2L`, all effective |
| `eq:doubling_pathid` | ✓ carried, and **proved** (`Descent.descW_uu`) |
| `eq:doubling_coupling` | ✓ carried, and **proved** (`Coupling.coupling`, `coupling_above`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

namespace Decay

variable (D : Decay)

/-! ## The cut balance determines the sequence -/

/-- **Fifth bullet of the proof of `theo:doubling_sharp`.** Two sequences satisfying
`eq:doubling_cut` at every `m > d` and agreeing on `λ_1,…,λ_d` agree everywhere; so `c`, `d` and
the boundary data determine the whole sequence, and with it the limit `C`. -/
theorem cutBal_unique {d : ℕ} {lam lam' : ℕ → ℝ} (h : D.CutBal d lam ⊤) (h' : D.CutBal d lam' ⊤)
    (hagree : ∀ j, 1 ≤ j → j ≤ d → lam j = lam' j) : ∀ m : ℕ, 1 ≤ m → lam m = lam' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hdm : m ≤ d
    · exact hagree m hm hdm
    · have hdm' : d < m := by omega
      rw [D.avg_of_cutBal h hm hdm' le_top, D.avg_of_cutBal h' hm hdm' le_top]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ih j (window_lt hj) (one_le_of_mem_window' hm hj)]

/-! ## The two "profiles differ by little" bullets -/

section Sharp

variable {d L : ℕ} {lam : ℕ → ℝ} {c₁ c₂ c₃ : ℝ}

/-- The difference of two descent averages, as one sum against the difference of the exit laws. -/
theorem descP_diff_eq {ℓ : ℕ} (u : ℕ → ℝ) {y y' : ℕ} (hy : ℓ ≤ y) (hy' : ℓ ≤ y') :
    D.descP ℓ u y - D.descP ℓ u y'
      = ∑ k ∈ Finset.Ico ℓ (2 * ℓ), u k * (D.exitLaw ℓ y k - D.exitLaw ℓ y' k) := by
  have e : (∑ k ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ y k * u k)
        - ∑ k ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ y' k * u k
      = ∑ k ∈ Finset.Ico ℓ (2 * ℓ), (D.exitLaw ℓ y k * u k - D.exitLaw ℓ y' k * u k) :=
    (Finset.sum_sub_distrib _ _).symm
  rw [D.descP_eq_sum u y hy, D.descP_eq_sum u y' hy', e]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The coupling step.** Two descent averages of the profile, started above `2^iℓ`, differ by at
most `c₂(1−ω)^i`. This is the first bullet of the proof of `theo:doubling_sharp` minus its two
weight terms. -/
theorem descP_uu_diff_le (hc₁ : 0 < c₁)
    (hbd : ∀ j, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂)
    {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hℓτ : 32 * D.c * D.tau ≤ (ℓ : ℝ)) (i : ℕ) {m m' : ℕ}
    (hm : 2 ^ i * ℓ ≤ m) (hm' : 2 ^ i * ℓ ≤ m') :
    |D.descP ℓ (D.uu lam) m - D.descP ℓ (D.uu lam) m'| ≤ c₂ * (1 - D.omeg) ^ i := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hla : ℓ ≤ 2 ^ i * ℓ := le_pow_mul i ℓ
  have hym : ℓ ≤ m := le_trans hla hm
  have hym' : ℓ ≤ m' := le_trans hla hm'
  have hF : (Finset.Ico ℓ (2 * ℓ)).Nonempty := ⟨ℓ, by rw [Finset.mem_Ico]; omega⟩
  have hc₂ : c₁ ≤ c₂ := le_trans (hbd 1 le_rfl).1 (hbd 1 le_rfl).2
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le hc₁ hc₂
  have hmass : ∑ k ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ m k
      = ∑ k ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ m' k := by
    rw [D.exitLaw_sum hℓ1 hym, D.exitLaw_sum hℓ1 hym']
  have hf : ∀ k ∈ Finset.Ico ℓ (2 * ℓ), c₁ ≤ D.uu lam k ∧ D.uu lam k ≤ c₂ := by
    intro k hk
    exact hbd k (by have := (Finset.mem_Ico.mp hk).1; omega)
  rw [D.descP_diff_eq (D.uu lam) hym hym']
  have hstep := abs_sum_sub_le hF hf hmass
  have htv : tvOn (Finset.Ico ℓ (2 * ℓ)) (D.exitLaw ℓ m) (D.exitLaw ℓ m') ≤ (1 - D.omeg) ^ i :=
    D.coupling_above hℓ hℓτ i hm hm'
  have htv0 : 0 ≤ tvOn (Finset.Ico ℓ (2 * ℓ)) (D.exitLaw ℓ m) (D.exitLaw ℓ m') :=
    tvOn_nonneg _ _ _
  calc |∑ k ∈ Finset.Ico ℓ (2 * ℓ), D.uu lam k * (D.exitLaw ℓ m k - D.exitLaw ℓ m' k)|
      ≤ (c₂ - c₁) * tvOn (Finset.Ico ℓ (2 * ℓ)) (D.exitLaw ℓ m) (D.exitLaw ℓ m') := hstep
    _ ≤ c₂ * (1 - D.omeg) ^ i := by nlinarith [htv, htv0, hc₁, hc₂pos]

/-- **The weight step.** The profile differs from its own descent average by at most `c₂c₃/ℓ`.
Below `2ℓ` the two are equal, and above it this is `eq:doubling_pathid` (proved) together with
`lem:doubling_weight` (the hypothesis `hweight`). -/
theorem uu_sub_descP_le (hcut : D.CutBal d lam ⊤) (hLd : d < 2 * L) (hc₃ : 0 ≤ c₃)
    (hc₂ : 0 ≤ c₂)
    (hweight : ∀ ℓ y : ℕ, L ≤ ℓ → 2 * ℓ ≤ y →
      |D.descW ℓ (D.uu lam) y - D.descP ℓ (D.uu lam) y| ≤ c₂ * c₃ / ℓ)
    {ℓ : ℕ} (hℓ : L ≤ ℓ) (y : ℕ) :
    |D.uu lam y - D.descP ℓ (D.uu lam) y| ≤ c₂ * c₃ / ℓ := by
  by_cases hlt : y < 2 * ℓ
  · rw [D.descP_of_lt _ hlt, sub_self, abs_zero]
    positivity
  · have hge : 2 * ℓ ≤ y := by omega
    have hd : d < 2 * ℓ := by omega
    rw [D.descW_uu hcut hd y le_top]
    exact hweight ℓ y hℓ hge

/-- **The two bullets of the proof of `theo:doubling_sharp`, merged.** At every level `ℓ ≥ L` and
every `i`, two indices above `2^iℓ` have profiles differing by at most
`c₂(1−ω)^i + 2c₂c₃/ℓ` — the paper's `3c₂c₃/ℓ`, improved to `2`. -/
theorem uu_diff_le (hcut : D.CutBal d lam ⊤) (hLd : d < 2 * L) (hL : 20 ≤ L)
    (hLτ : 32 * D.c * D.tau ≤ (L : ℝ)) (hc₁ : 0 < c₁) (hc₃ : 0 ≤ c₃)
    (hbd : ∀ j, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂)
    (hweight : ∀ ℓ y : ℕ, L ≤ ℓ → 2 * ℓ ≤ y →
      |D.descW ℓ (D.uu lam) y - D.descP ℓ (D.uu lam) y| ≤ c₂ * c₃ / ℓ)
    {ℓ : ℕ} (hℓ : L ≤ ℓ) (i : ℕ) {m m' : ℕ} (hm : 2 ^ i * ℓ ≤ m) (hm' : 2 ^ i * ℓ ≤ m') :
    |D.uu lam m - D.uu lam m'| ≤ c₂ * (1 - D.omeg) ^ i + 2 * (c₂ * c₃ / ℓ) := by
  have hℓ20 : 20 ≤ ℓ := le_trans hL hℓ
  have hℓτ : 32 * D.c * D.tau ≤ (ℓ : ℝ) := by
    refine le_trans hLτ ?_
    exact_mod_cast (Nat.cast_le (α := ℝ)).mpr hℓ
  have hla : ℓ ≤ 2 ^ i * ℓ := le_pow_mul i ℓ
  have hym : ℓ ≤ m := le_trans hla hm
  have hym' : ℓ ≤ m' := le_trans hla hm'
  have hc₂ : (0 : ℝ) ≤ c₂ := le_trans hc₁.le (le_trans (hbd 1 le_rfl).1 (hbd 1 le_rfl).2)
  have h1 := D.uu_sub_descP_le hcut hLd hc₃ hc₂ hweight hℓ m
  have h2 := D.uu_sub_descP_le hcut hLd hc₃ hc₂ hweight hℓ m'
  have h3 := D.descP_uu_diff_le hc₁ hbd hℓ20 hℓτ i hm hm'
  have hsplit : D.uu lam m - D.uu lam m'
      = (D.uu lam m - D.descP ℓ (D.uu lam) m)
        + (D.descP ℓ (D.uu lam) m - D.descP ℓ (D.uu lam) m')
        - (D.uu lam m' - D.descP ℓ (D.uu lam) m') := by ring
  rw [hsplit]
  calc |(D.uu lam m - D.descP ℓ (D.uu lam) m)
          + (D.descP ℓ (D.uu lam) m - D.descP ℓ (D.uu lam) m')
          - (D.uu lam m' - D.descP ℓ (D.uu lam) m')|
      ≤ |(D.uu lam m - D.descP ℓ (D.uu lam) m)
          + (D.descP ℓ (D.uu lam) m - D.descP ℓ (D.uu lam) m')|
        + |D.uu lam m' - D.descP ℓ (D.uu lam) m'| := abs_sub _ _
    _ ≤ (|D.uu lam m - D.descP ℓ (D.uu lam) m|
          + |D.descP ℓ (D.uu lam) m - D.descP ℓ (D.uu lam) m'|)
        + |D.uu lam m' - D.descP ℓ (D.uu lam) m'| := by
          have := abs_add_le (D.uu lam m - D.descP ℓ (D.uu lam) m)
            (D.descP ℓ (D.uu lam) m - D.descP ℓ (D.uu lam) m')
          linarith
    _ ≤ c₂ * (1 - D.omeg) ^ i + 2 * (c₂ * c₃ / ℓ) := by linarith

/-! ## The limit -/

/-- **`eq:doubling_sharp`.** The rescaled profile `u_m = λ_m m^{p_*}` converges; its limit lies in
`[c₁,c₂]`; and the convergence carries the explicit error `c₂(1−ω)^i + 2c₂c₃/ℓ` at every level
`ℓ ≥ L` and every `i` with `2^iℓ ≤ m`.

This is the third bullet of the proof of `theo:doubling_sharp`, with the Cauchy criterion; the
paper's optimisation of the error over `ℓ` and `i` — `eq:doubling_rate` — is not carried out. -/
theorem sharp_limit (hcut : D.CutBal d lam ⊤) (hLd : d < 2 * L) (hL : 20 ≤ L)
    (hLτ : 32 * D.c * D.tau ≤ (L : ℝ)) (hc₁ : 0 < c₁) (hc₃ : 0 ≤ c₃)
    (hbd : ∀ j, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂)
    (hweight : ∀ ℓ y : ℕ, L ≤ ℓ → 2 * ℓ ≤ y →
      |D.descW ℓ (D.uu lam) y - D.descP ℓ (D.uu lam) y| ≤ c₂ * c₃ / ℓ) :
    ∃ C : ℝ, Tendsto (fun m : ℕ => D.uu lam m) atTop (𝓝 C) ∧ c₁ ≤ C ∧ C ≤ c₂ ∧
      ∀ ℓ i m : ℕ, L ≤ ℓ → 2 ^ i * ℓ ≤ m →
        |D.uu lam m - C| ≤ c₂ * (1 - D.omeg) ^ i + 2 * (c₂ * c₃ / ℓ) := by
  have hc₂ : c₁ ≤ c₂ := le_trans (hbd 1 le_rfl).1 (hbd 1 le_rfl).2
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le hc₁ hc₂
  have hω0 : 0 ≤ 1 - D.omeg := by linarith [D.omeg_lt_one]
  have hω1 : 1 - D.omeg < 1 := by linarith [D.omeg_pos]
  -- the Cauchy criterion
  have hcauchy : CauchySeq (fun m : ℕ => D.uu lam m) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- choose the level
    obtain ⟨n, hn⟩ := exists_nat_gt (4 * (c₂ * c₃) / ε)
    set ℓ : ℕ := max L n with hℓdef
    have hℓL : L ≤ ℓ := le_max_left _ _
    have hℓn : (n : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast le_max_right L n
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by
      have : 20 ≤ ℓ := le_trans hL hℓL
      have : (20 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast this
      linarith
    have hsmall : 2 * (c₂ * c₃ / (ℓ : ℝ)) < ε / 2 := by
      have h4 : 4 * (c₂ * c₃) < (ℓ : ℝ) * ε := (div_lt_iff₀ hε).mp (lt_of_lt_of_le hn hℓn)
      rw [← mul_div_assoc, div_lt_iff₀ hℓpos]
      nlinarith [h4]
    -- choose the index
    obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hε) hc₂pos) hω1
    have hi' : c₂ * (1 - D.omeg) ^ i < ε / 2 := by
      rw [lt_div_iff₀ hc₂pos] at hi
      linarith [hi]
    refine ⟨2 ^ i * ℓ, fun m hm m' hm' => ?_⟩
    have hbound := D.uu_diff_le hcut hLd hL hLτ hc₁ hc₃ hbd hweight hℓL i hm hm'
    rw [Real.dist_eq]
    linarith [hbound, hi', hsmall]
  obtain ⟨C, hC⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · refine ge_of_tendsto hC ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (hbd m hm).1
  · refine le_of_tendsto hC ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (hbd m hm).2
  · intro ℓ i m hℓ hm
    have hlim : Tendsto (fun m' : ℕ => |D.uu lam m - D.uu lam m'|) atTop
        (𝓝 |D.uu lam m - C|) := (hC.const_sub (D.uu lam m)).abs
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (2 ^ i * ℓ)] with m' hm'
    exact D.uu_diff_le hcut hLd hL hLτ hc₁ hc₃ hbd hweight hℓ i hm hm'

end Sharp

end Decay

end GFNBounds.Doubling
