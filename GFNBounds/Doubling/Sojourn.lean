import GFNBounds.Doubling.Escape

/-!
# `lem:doubling_escape`, Step 2: the sojourn in a dyadic block

**`lem:doubling_escape`** — `app_doubling.tex:1026–1108`.

> for every `i ≥ 1` and every `y ∈ I_i(ℓ)`, the exit time `ς := inf{n ≥ 0 : Y_n ∉ I_i(ℓ)}` obeys
> `P(ς > 2r | Y₀ = y) ≤ (1−γ²)^r` `(r ≥ 0)`,  `E(ς | Y₀ = y) ≤ 2/γ²`,
> `E(ζ^ς | Y₀ = y) ≤ 1 + c₅(ζ−1)` for `1 ≤ ζ ≤ 1 + γ²/6`,  `(eq:doubling_sojourn)`
> with `c₅ := 6/γ²`.

## The modelling decision

**No chain, again.** As `Descent.lean` models `E(Z_ℓ g(Y_{N_ℓ}))` by the recursion `descW`, the
survival function of the exit time is modelled here by the recursion in the *number of steps*:

  `surv L 0 z = 1_I(z)`,   `surv L (r+1) z = 1_I(z) · Σ_{j ∈ W(z)} p(z,j) · surv L r j`,

with `I = [L, 2L)` and `p(z,j) := w_z(j)/R₀(z)` the transition law of `lem:doubling_descent`
(`Decay.pk`). This is `P(ς > r | Y₀ = z)`: the event `{ς > r}` is `{Y_0, …, Y_r ∈ I}`, and that is
exactly what the display above computes. No well-founded recursion and no measure theory are
needed — the recursion is structural in `r`.

**All three lines of `eq:doubling_sojourn` are proved.** The first
(`Decay.surv_two_pow`) goes through the paper's own two-step estimate, which is `Decay.two_step`:

  `Σ_j p(z,j) · 1_I(j) · Σ_k p(j,k) · 1_I(k)  ≤  1 − γ²`   for `z ∈ I`.

The paper obtains it by conditioning twice; here it is a finite-sum computation with three inputs:
`Σ_{j ∈ W(z)} p(z,j) = 1` (`sum_pk`), `Σ_{j ≤ z/√2} p(z,j) ≥ γ` (`escape_pk`, which is Step 1),
and the observation that **two halvings leave the block** — `j ≤ z/√2` and `k ≤ j/√2` with
`z < 2L` give `k ≤ z/2 < L` (`halve_halve_lt`). That last is where `I_i(ℓ)` being dyadic is used,
and it is the reason the estimate is two-step and not one-step.

The two expectations are modelled the same way, each by the equation that characterises it, this
time by well-founded recursion on the **state** (every `j ∈ W(z)` has `j < z`):

  `sojMean L z = 1_I(z) · (1 + Σ_j p(z,j) · sojMean L j)`,
  `sojGF L ζ z = if z ∉ I then 1 else ζ · Σ_j p(z,j) · sojGF L ζ j`.

Neither is postulated to equal a tail sum: `sojMean_eq_sum` and `sojGF_eq_sum` **prove**
`E(ς) = Σ_{n<N} P(ς>n)` and `E(ζ^ς) = 1 + (ζ−1) Σ_{n<N} ζⁿ P(ς>n)` from the two recursions, for
every `N` past the block width — the paper's own two identities. The sums are finite because
`surv L r z = 0` once `z < L + r` (`surv_eq_zero_of_lt`), which is the descent falling by at least
one per step. `E(ς) ≤ 2/γ²` and `E(ζ^ς) ≤ 1 + c₅(ζ−1)` then follow by pairing consecutive terms,
exactly as the paper does with `ς̃ = ⌈ς/2⌉`.

## SCOPE (disclosed)

* The block is taken as a general `I = [L, 2L)` with `32cτ ≤ L`, which covers `I_i(ℓ)` for every
  `i ≥ 1` and `ℓ ≥ ℓ₂` — the paper's range — since then `2^i ℓ ≥ 2ℓ ≥ 32cτ`. `i = 0` is excluded
  in the paper too.
* `sojMean_le` and `sojGF_le` do **not** assume `L ≤ y`; only `y < 2L` is used, the recursions
  returning `0` and `1` below the block. That is weaker than the paper's `y ∈ I_i(ℓ)`, hence a
  strengthening of the statement, not of a hypothesis.
* `c₅` is the paper's `6/γ²` verbatim (`Decay.c5`). The proof of the third line runs with the
  slack constant `49/16 < 6`, so `c₅` is not tight here either; it is the paper's value that is
  certified, not a better one.
* The three bounds are about the exit time from **one** block. `lem:doubling_product`, which
  chains them across `i`, is not in this file.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1`, `p = p_*`, `τ = 2^{p_*}` | ✓ carried by `Decay` |
| `ℓ ≥ ℓ₂`, `i ≥ 1`, `y ∈ I_i(ℓ)` | ✓ carried, as `32cτ ≤ L` and `L ≤ z < 2L` (see SCOPE) |
| the transition law `w_y(j)/R₀(y)` on `W(y)` | ✓ carried as `Decay.pk`, with `Σ = 1` proved |
| `γ = √τ/(2(√τ+1))`, `c₅ = 6/γ²` | ✓ carried (`Decay.gam`, `Decay.c5`) |
| `P(ς > 2r) ≤ (1−γ²)^r` | ✓ proved (`Decay.surv_two_pow`, `Decay.surv_le_pow`) |
| `E(ς) ≤ 2/γ²` | ✓ proved (`Decay.sojMean_le`) |
| `1 ≤ ζ ≤ 1 + γ²/6` and `E(ζ^ς) ≤ 1 + c₅(ζ−1)` | ✓ proved (`Decay.sojGF_le`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

variable (D : Decay)

/-! ### The transition law of the descent chain -/

/-- **The transition law of `lem:doubling_descent`.** `P(Y₁ = j | Y₀ = z) = w_z(j)/R₀(z)` for
`j ∈ W(z)`. -/
noncomputable def pk (z j : ℕ) : ℝ := D.wm z j / D.R0 z

section Kernel

variable {z : ℕ}

/-- `R₀(z) ≥ ½` above the threshold: `eq:doubling_R0`, first half. -/
theorem half_le_R0 (hz : 32 * D.c * D.tau ≤ (z : ℝ)) : 1 / 2 ≤ D.R0 z := by
  have hz1 : 1 ≤ z := D.one_le_of_thr hz
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith [D.thirty_two_lt hz]
  have hR := D.R0_sub_one_le hz1
  rw [abs_le] at hR
  have h16 : 16 * D.c * D.tau / (z : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hzpos]; linarith [D.ctau_pos]
  linarith [hR.1]

theorem pk_nonneg (hz : 32 * D.c * D.tau ≤ (z : ℝ)) {j : ℕ} (hj : j ∈ window z) :
    0 ≤ D.pk z j := by
  have hz1 : 1 ≤ z := D.one_le_of_thr hz
  have hj1 : 1 ≤ j := one_le_of_mem_window' hz1 hj
  exact div_nonneg (D.wm_nonneg hz1 hj1) (by linarith [D.half_le_R0 hz])

/-- The transition law is a probability on `W(z)`: `Σ_{j ∈ W(z)} w_z(j)/R₀(z) = 1`. -/
theorem sum_pk (hz : 32 * D.c * D.tau ≤ (z : ℝ)) : ∑ j ∈ window z, D.pk z j = 1 := by
  have hR := D.half_le_R0 hz
  simp only [pk]
  rw [← Finset.sum_div, sum_wm]
  exact div_self (by linarith)

/-- **`eq:doubling_escape` as a mass.** `Σ_{j ≤ y/√2} P(Y₁ = j | Y₀ = y) ≥ γ`. -/
theorem escape_pk (hz : 32 * D.c * D.tau ≤ (z : ℝ)) :
    D.gam ≤ ∑ j ∈ halveIco z, D.pk z j := by
  have h := D.escape hz
  rw [Finset.sum_div] at h
  exact h

theorem halveIco_subset (hz : 32 * D.c * D.tau ≤ (z : ℝ)) : halveIco z ⊆ window z := by
  rw [D.halveIco_eq_filter hz]; exact Finset.filter_subset _ _

end Kernel

/-! ### The dyadic block -/

/-- The indicator of the block `I = [L, 2L)`; `I_i(ℓ)` at `L = 2^i ℓ`. -/
noncomputable def indB (L z : ℕ) : ℝ := if L ≤ z ∧ z < 2 * L then 1 else 0

theorem indB_nonneg (L z : ℕ) : 0 ≤ indB L z := by rw [indB]; split <;> norm_num

theorem indB_le_one (L z : ℕ) : indB L z ≤ 1 := by rw [indB]; split <;> norm_num

theorem indB_eq_zero {L z : ℕ} (h : z < L) : indB L z = 0 := by rw [indB, if_neg]; omega

/-- **Two halvings leave the block.** If `j ≤ z/√2`, `k ≤ j/√2` and `z < 2L`, then `k < L`.
This is what makes the paper's estimate two-step: one halving from `z < 2L` only reaches
`√2 L`, which is still inside the block. -/
theorem halve_halve_lt {L z j k : ℕ} (hzthr : 32 * D.c * D.tau ≤ (z : ℝ))
    (hjthr : 32 * D.c * D.tau ≤ (j : ℝ)) (hz2 : z < 2 * L)
    (hj : j ∈ halveIco z) (hk : k ∈ halveIco j) : k < L := by
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith [D.thirty_two_lt hzthr]
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith [D.thirty_two_lt hjthr]
  have hjr : (j : ℝ) ≤ (z : ℝ) / Real.sqrt 2 := by
    rw [halveIco, Finset.mem_Ico] at hj
    exact (Nat.le_floor_iff (by positivity)).mp (by omega)
  have hkr : (k : ℝ) ≤ (j : ℝ) / Real.sqrt 2 := by
    rw [halveIco, Finset.mem_Ico] at hk
    exact (Nat.le_floor_iff (by positivity)).mp (by omega)
  have hstep : (j : ℝ) / Real.sqrt 2 ≤ ((z : ℝ) / Real.sqrt 2) / Real.sqrt 2 :=
    div_le_div_of_nonneg_right hjr sqrt_two_pos.le
  have hhalf : ((z : ℝ) / Real.sqrt 2) / Real.sqrt 2 = (z : ℝ) / 2 := by
    rw [div_div, Real.mul_self_sqrt (by norm_num)]
  have hzL : (z : ℝ) < 2 * (L : ℝ) := by exact_mod_cast hz2
  have hkL : (k : ℝ) < (L : ℝ) := by rw [hhalf] at hstep; linarith
  exact_mod_cast hkL

/-! ### The two-step estimate -/

/-- **One step out of the block, from an already halved state.** If every halving of `j` leaves
the block, then the chance of staying in it at the next step is at most `1 − γ`. -/
theorem inner_le {L j : ℕ} (hjthr : 32 * D.c * D.tau ≤ (j : ℝ))
    (hout : ∀ k ∈ halveIco j, k < L) :
    ∑ k ∈ window j, D.pk j k * indB L k ≤ 1 - D.gam := by
  classical
  have hsub := D.halveIco_subset hjthr
  have hsplit := Finset.sum_sdiff (f := fun k => D.pk j k * indB L k) hsub
  have hzero : ∑ k ∈ halveIco j, D.pk j k * indB L k = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [indB_eq_zero (hout k hk), mul_zero]
  have hbound : ∑ k ∈ window j \ halveIco j, D.pk j k * indB L k
      ≤ ∑ k ∈ window j \ halveIco j, D.pk j k := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hkw : k ∈ window j := (Finset.mem_sdiff.mp hk).1
    have hp := D.pk_nonneg hjthr hkw
    nlinarith [indB_le_one L k]
  have hdiff : ∑ k ∈ window j \ halveIco j, D.pk j k = 1 - ∑ k ∈ halveIco j, D.pk j k := by
    rw [Finset.sum_sdiff_eq_sub hsub, D.sum_pk hjthr]
  have hesc := D.escape_pk hjthr
  rw [hzero, add_zero] at hsplit
  rw [hdiff] at hbound
  linarith [hsplit, hbound]

/-- **The two-step estimate.** `P(Y₂ ∈ I | Y₀ = z) ≤ 1 − γ²` for every `z ∈ I = [L, 2L)`.
This is the display the paper reaches by conditioning first on `Y₀,…,Y₁` and then on `Y₀`. -/
theorem two_step {L z : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hz1 : L ≤ z) (hz2 : z < 2 * L) :
    ∑ j ∈ window z, D.pk z j * (indB L j * ∑ k ∈ window j, D.pk j k * indB L k)
      ≤ 1 - D.gam ^ 2 := by
  classical
  have hLr : (L : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) := le_trans hL hLr
  have hgpos := D.gam_pos
  have hghalf := D.gam_lt_half
  set g : ℕ → ℝ := fun j => indB L j * ∑ k ∈ window j, D.pk j k * indB L k with hg
  have hg1 : ∀ j : ℕ, g j ≤ 1 := by
    intro j
    by_cases hb : L ≤ j ∧ j < 2 * L
    · have hjr : (L : ℝ) ≤ (j : ℝ) := by exact_mod_cast hb.1
      have hjthr : 32 * D.c * D.tau ≤ (j : ℝ) := le_trans hL hjr
      rw [hg]
      simp only [indB, if_pos hb, one_mul]
      calc ∑ k ∈ window j, D.pk j k * indB L k ≤ ∑ k ∈ window j, D.pk j k := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hp := D.pk_nonneg hjthr hk
            nlinarith [indB_le_one L k]
        _ = 1 := D.sum_pk hjthr
    · rw [hg]; simp only [indB, if_neg hb, zero_mul]; norm_num
  have hg2 : ∀ j ∈ halveIco z, g j ≤ 1 - D.gam := by
    intro j hj
    by_cases hb : L ≤ j ∧ j < 2 * L
    · have hjr : (L : ℝ) ≤ (j : ℝ) := by exact_mod_cast hb.1
      have hjthr : 32 * D.c * D.tau ≤ (j : ℝ) := le_trans hL hjr
      rw [hg]
      simp only [indB, if_pos hb, one_mul]
      exact D.inner_le hjthr (fun k hk => D.halve_halve_lt hzthr hjthr hz2 hj hk)
    · rw [hg]; simp only [indB, if_neg hb, zero_mul]; linarith
  have hsub := D.halveIco_subset hzthr
  have hsplit := Finset.sum_sdiff (f := fun j => D.pk z j * g j) hsub
  set A : ℝ := ∑ j ∈ halveIco z, D.pk z j with hA
  have hAge : D.gam ≤ A := D.escape_pk hzthr
  have hdiff : ∑ j ∈ window z \ halveIco z, D.pk z j = 1 - A := by
    rw [Finset.sum_sdiff_eq_sub hsub, D.sum_pk hzthr, hA]
  have h1 : ∑ j ∈ halveIco z, D.pk z j * g j ≤ (1 - D.gam) * A := by
    rw [hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hp := D.pk_nonneg hzthr (hsub hj)
    have hgj := hg2 j hj
    nlinarith
  have h2 : ∑ j ∈ window z \ halveIco z, D.pk z j * g j ≤ 1 - A := by
    rw [← hdiff]
    refine Finset.sum_le_sum fun j hj => ?_
    have hp := D.pk_nonneg hzthr (Finset.mem_sdiff.mp hj).1
    nlinarith [hg1 j]
  have hfin : ∑ j ∈ window z, D.pk z j * g j ≤ 1 - D.gam * A := by
    linarith [hsplit, h1, h2]
  nlinarith [hfin, hAge, hgpos]

/-! ### The survival function of the exit time -/

/-- **`P(ς > r | Y₀ = z)`**, where `ς` is the exit time from `I = [L, 2L)`, as the recursion in
the number of steps that characterises it: `{ς > r} = {Y₀, …, Y_r ∈ I}`. -/
noncomputable def surv (D : Decay) (L : ℕ) : ℕ → ℕ → ℝ
  | 0, z => indB L z
  | r + 1, z => indB L z * ∑ j ∈ window z, D.pk z j * surv D L r j

theorem surv_zero (L z : ℕ) : D.surv L 0 z = indB L z := rfl

theorem surv_succ (L r z : ℕ) :
    D.surv L (r + 1) z = indB L z * ∑ j ∈ window z, D.pk z j * D.surv L r j := rfl

theorem surv_of_out {L z : ℕ} (h : ¬ (L ≤ z ∧ z < 2 * L)) (r : ℕ) : D.surv L r z = 0 := by
  cases r with
  | zero => rw [surv_zero, indB, if_neg h]
  | succ n => rw [surv_succ, indB, if_neg h, zero_mul]

/-- The descent falls by at least one at each step, so it cannot stay in a block of width `L`
for `L` steps: `surv L r z = 0` as soon as `z < L + r`. This is what makes the tail sums of
`E(ς)` and `E(ζ^ς)` finite. -/
theorem surv_eq_zero_of_lt {L : ℕ} : ∀ (r z : ℕ), z < L + r → D.surv L r z = 0 := by
  intro r
  induction r with
  | zero => intro z hz; rw [surv_zero, indB, if_neg]; omega
  | succ n ih =>
    intro z hz
    by_cases hb : L ≤ z ∧ z < 2 * L
    · rw [surv_succ, indB, if_pos hb, one_mul]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjz : j < z := window_lt hj
      rw [ih j (by omega), mul_zero]
    · exact D.surv_of_out hb _

/-- **`eq:doubling_sojourn`, first line.** `P(ς > 2r | Y₀ = y) ≤ (1 − γ²)^r`, and — the sharper
form the induction needs — the bound is carried by the block indicator. -/
theorem surv_two_pow {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) :
    ∀ (r z : ℕ), D.surv L (2 * r) z ≤ (1 - D.gam ^ 2) ^ r * indB L z := by
  have hgpos := D.gam_pos
  have hghalf := D.gam_lt_half
  have hq : (0 : ℝ) ≤ 1 - D.gam ^ 2 := by nlinarith
  intro r
  induction r with
  | zero => intro z; rw [Nat.mul_zero, surv_zero, pow_zero, one_mul]
  | succ n ih =>
    intro z
    have hidx : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [hidx, surv_succ]
    by_cases hb : L ≤ z ∧ z < 2 * L
    · have hLr : (L : ℝ) ≤ (z : ℝ) := by exact_mod_cast hb.1
      have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) := le_trans hL hLr
      have hqn : (0 : ℝ) ≤ (1 - D.gam ^ 2) ^ n := pow_nonneg hq n
      have hstep : ∀ j ∈ window z, D.pk z j * D.surv L (2 * n + 1) j
          ≤ D.pk z j * ((1 - D.gam ^ 2) ^ n *
              (indB L j * ∑ k ∈ window j, D.pk j k * indB L k)) := by
        intro j hj
        have hp := D.pk_nonneg hzthr hj
        refine mul_le_mul_of_nonneg_left ?_ hp
        by_cases hbj : L ≤ j ∧ j < 2 * L
        · have hjr : (L : ℝ) ≤ (j : ℝ) := by exact_mod_cast hbj.1
          have hjthr : 32 * D.c * D.tau ≤ (j : ℝ) := le_trans hL hjr
          rw [surv_succ, indB, if_pos hbj, one_mul, one_mul, Finset.mul_sum]
          refine Finset.sum_le_sum fun k hk => ?_
          have hpk := D.pk_nonneg hjthr hk
          calc D.pk j k * D.surv L (2 * n) k
              ≤ D.pk j k * ((1 - D.gam ^ 2) ^ n * indB L k) :=
                mul_le_mul_of_nonneg_left (ih k) hpk
            _ = (1 - D.gam ^ 2) ^ n * (D.pk j k * indB L k) := by ring
        · rw [surv_succ, indB, if_neg hbj, zero_mul, zero_mul, mul_zero]
      have hsum := Finset.sum_le_sum hstep
      have hpull : ∑ j ∈ window z, D.pk z j * ((1 - D.gam ^ 2) ^ n *
            (indB L j * ∑ k ∈ window j, D.pk j k * indB L k))
          = (1 - D.gam ^ 2) ^ n * ∑ j ∈ window z, D.pk z j *
              (indB L j * ∑ k ∈ window j, D.pk j k * indB L k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [hpull] at hsum
      have hts := D.two_step hL hb.1 hb.2
      have hchain : ∑ j ∈ window z, D.pk z j * D.surv L (2 * n + 1) j
          ≤ (1 - D.gam ^ 2) ^ n * (1 - D.gam ^ 2) :=
        le_trans hsum (mul_le_mul_of_nonneg_left hts hqn)
      rw [indB, if_pos hb, one_mul, mul_one, pow_succ]
      exact hchain
    · rw [indB, if_neg hb, zero_mul, mul_zero]

/-- **`eq:doubling_sojourn`, first line, as stated in the paper.** -/
theorem surv_le_pow {L z : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hz1 : L ≤ z) (hz2 : z < 2 * L)
    (r : ℕ) : D.surv L (2 * r) z ≤ (1 - D.gam ^ 2) ^ r := by
  have h := D.surv_two_pow hL r z
  rwa [indB, if_pos ⟨hz1, hz2⟩, mul_one] at h

/-! ### `E(ς)` and `E(ζ^ς)` -/

/-- `Σ_{i<n} x^i ≤ 1/(1−x)` for `0 ≤ x < 1`. -/
theorem geom_sum_le_inv {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i ≤ 1 / (1 - x) := by
  have h1 : (1 - x) * ∑ i ∈ Finset.range n, x ^ i = 1 - x ^ n := by
    rw [Finset.mul_sum]
    induction n with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [le_div_iff₀ (by linarith)]
  nlinarith [pow_nonneg hx0 n]

/-- `P(ς > r)` is non-increasing in `r`. -/
theorem surv_antitone {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) :
    ∀ (r z : ℕ), D.surv L (r + 1) z ≤ D.surv L r z := by
  intro r
  induction r with
  | zero =>
    intro z
    by_cases hb : L ≤ z ∧ z < 2 * L
    · have hLr : (L : ℝ) ≤ (z : ℝ) := by exact_mod_cast hb.1
      have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) := le_trans hL hLr
      rw [surv_succ, surv_zero, indB, if_pos hb, one_mul]
      calc ∑ j ∈ window z, D.pk z j * D.surv L 0 j
          ≤ ∑ j ∈ window z, D.pk z j := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hp := D.pk_nonneg hzthr hj
            rw [surv_zero]
            nlinarith [indB_le_one L j]
        _ = 1 := D.sum_pk hzthr
    · rw [D.surv_of_out hb, D.surv_of_out hb]
  | succ n ih =>
    intro z
    by_cases hb : L ≤ z ∧ z < 2 * L
    · have hLr : (L : ℝ) ≤ (z : ℝ) := by exact_mod_cast hb.1
      have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) := le_trans hL hLr
      rw [surv_succ, surv_succ, indB, if_pos hb, one_mul, one_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      exact mul_le_mul_of_nonneg_left (ih j) (D.pk_nonneg hzthr hj)
    · rw [D.surv_of_out hb, D.surv_of_out hb]

/-- `P(ς > 2m | Y₀ = z) ≤ (1−γ²)^m` at every state, the indicator dropped. -/
theorem surv_two_pow_le {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (m z : ℕ) :
    D.surv L (2 * m) z ≤ (1 - D.gam ^ 2) ^ m := by
  have hgpos := D.gam_pos
  have hghalf := D.gam_lt_half
  have hq : (0 : ℝ) ≤ 1 - D.gam ^ 2 := by nlinarith
  have h := D.surv_two_pow hL m z
  nlinarith [indB_le_one L z, pow_nonneg hq m, indB_nonneg L z]

/-- Consecutive terms of the tail sum, paired: this is the paper's `ς̃ = ⌈ς/2⌉`. -/
theorem surv_partial_sum {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (z : ℕ) :
    ∀ R : ℕ, ∑ n ∈ Finset.range (2 * R), D.surv L n z
      ≤ 2 * ∑ r ∈ Finset.range R, (1 - D.gam ^ 2) ^ r := by
  intro R
  induction R with
  | zero => simp
  | succ m ih =>
    have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [hidx, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : D.surv L (2 * m) z ≤ (1 - D.gam ^ 2) ^ m := D.surv_two_pow_le hL m z
    have h2 : D.surv L (2 * m + 1) z ≤ D.surv L (2 * m) z := D.surv_antitone hL (2 * m) z
    linarith

end Decay

/-- **`E(ς | Y₀ = z)`**, the expected sojourn in `I = [L,2L)`, as the recursion that characterises
it: leave at once outside the block, else one step plus the expectation after it. -/
noncomputable def Decay.sojMean (D : Decay) (L : ℕ) (z : ℕ) : ℝ :=
  if L ≤ z ∧ z < 2 * L then 1 + ∑ j ∈ (window z).attach, D.pk z j.1 * D.sojMean L j.1 else 0
termination_by z
decreasing_by exact window_lt j.2

/-- **`E(ζ^ς | Y₀ = z)`**, as the recursion that characterises it. -/
noncomputable def Decay.sojGF (D : Decay) (L : ℕ) (zeta : ℝ) (z : ℕ) : ℝ :=
  if L ≤ z ∧ z < 2 * L then
    zeta * ∑ j ∈ (window z).attach, D.pk z j.1 * D.sojGF L zeta j.1
  else 1
termination_by z
decreasing_by exact window_lt j.2

namespace Decay

variable (D : Decay)

/-- **`c₅ := 6/γ²`** of `lem:doubling_escape`. -/
noncomputable def c5 : ℝ := 6 / D.gam ^ 2

theorem sojMean_of_out {L z : ℕ} (h : ¬ (L ≤ z ∧ z < 2 * L)) : D.sojMean L z = 0 := by
  rw [sojMean, if_neg h]

theorem sojMean_of_in {L z : ℕ} (h : L ≤ z ∧ z < 2 * L) :
    D.sojMean L z = 1 + ∑ j ∈ window z, D.pk z j * D.sojMean L j := by
  rw [sojMean, if_pos h]
  congr 1
  exact Finset.sum_attach (window z) fun j => D.pk z j * D.sojMean L j

/-- **The tail formula.** `E(ς) = Σ_{n<N} P(ς > n)` for every `N` past the block width — proved
from the two recursions, not assumed. -/
theorem sojMean_eq_sum {L : ℕ} :
    ∀ (z N : ℕ), z < L + N → D.sojMean L z = ∑ n ∈ Finset.range N, D.surv L n z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro N hzN
    by_cases hb : L ≤ z ∧ z < 2 * L
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [D.sojMean_of_in hb, Finset.sum_range_succ' (fun n => D.surv L n z) M, surv_zero,
        indB, if_pos hb]
      have hterm : ∀ j ∈ window z, D.pk z j * D.sojMean L j
          = ∑ n ∈ Finset.range M, D.pk z j * D.surv L n j := by
        intro j hj
        have hjz : j < z := window_lt hj
        rw [ih j hjz M (by omega), Finset.mul_sum]
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      have hrow : ∀ n ∈ Finset.range M, ∑ j ∈ window z, D.pk z j * D.surv L n j
          = D.surv L (n + 1) z := by
        intro n _
        rw [surv_succ, indB, if_pos hb, one_mul]
      rw [Finset.sum_congr rfl hrow]
      ring
    · rw [D.sojMean_of_out hb]
      symm
      exact Finset.sum_eq_zero fun n _ => D.surv_of_out hb n

/-- **`eq:doubling_sojourn`, second line.** `E(ς | Y₀ = y) ≤ 2/γ²`. -/
theorem sojMean_le {L z : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hz2 : z < 2 * L) :
    D.sojMean L z ≤ 2 / D.gam ^ 2 := by
  have hgpos := D.gam_pos
  have hghalf := D.gam_lt_half
  have hGpos : (0 : ℝ) < D.gam ^ 2 := by positivity
  have hx0 : (0 : ℝ) ≤ 1 - D.gam ^ 2 := by nlinarith
  have hx1 : (1 : ℝ) - D.gam ^ 2 < 1 := by nlinarith
  rw [D.sojMean_eq_sum z (2 * L) (by omega)]
  have h1 := D.surv_partial_sum hL z L
  have h2 := geom_sum_le_inv hx0 hx1 L
  have h3 : (1 : ℝ) - (1 - D.gam ^ 2) = D.gam ^ 2 := by ring
  rw [h3] at h2
  calc ∑ n ∈ Finset.range (2 * L), D.surv L n z
      ≤ 2 * ∑ r ∈ Finset.range L, (1 - D.gam ^ 2) ^ r := h1
    _ ≤ 2 * (1 / D.gam ^ 2) := by linarith
    _ = 2 / D.gam ^ 2 := by ring

theorem sojGF_of_out {L : ℕ} {zeta : ℝ} {z : ℕ} (h : ¬ (L ≤ z ∧ z < 2 * L)) :
    D.sojGF L zeta z = 1 := by
  rw [sojGF, if_neg h]

theorem sojGF_of_in {L : ℕ} {zeta : ℝ} {z : ℕ} (h : L ≤ z ∧ z < 2 * L) :
    D.sojGF L zeta z = zeta * ∑ j ∈ window z, D.pk z j * D.sojGF L zeta j := by
  rw [sojGF, if_pos h]
  congr 1
  exact Finset.sum_attach (window z) fun j => D.pk z j * D.sojGF L zeta j

/-- **The paper's expansion `ζ^ς = 1 + (ζ−1) Σ_{n<ς} ζⁿ`, in expectation.** -/
theorem sojGF_eq_sum {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (zeta : ℝ) :
    ∀ (z N : ℕ), z < L + N →
      D.sojGF L zeta z = 1 + (zeta - 1) * ∑ n ∈ Finset.range N, zeta ^ n * D.surv L n z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro N hzN
    by_cases hb : L ≤ z ∧ z < 2 * L
    · have hLr : (L : ℝ) ≤ (z : ℝ) := by exact_mod_cast hb.1
      have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) := le_trans hL hLr
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [D.sojGF_of_in hb,
        Finset.sum_range_succ' (fun n => zeta ^ n * D.surv L n z) M, surv_zero,
        indB, if_pos hb]
      have hterm : ∀ j ∈ window z, D.pk z j * D.sojGF L zeta j
          = D.pk z j
            + (zeta - 1) * ∑ n ∈ Finset.range M, zeta ^ n * (D.pk z j * D.surv L n j) := by
        intro j hj
        have hjz : j < z := window_lt hj
        rw [ih j hjz M (by omega), Finset.mul_sum, mul_add, mul_one, Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, D.sum_pk hzthr,
        ← Finset.mul_sum, Finset.sum_comm]
      have hrow : ∀ n ∈ Finset.range M, ∑ j ∈ window z, zeta ^ n * (D.pk z j * D.surv L n j)
          = zeta ^ n * D.surv L (n + 1) z := by
        intro n _
        rw [surv_succ, indB, if_pos hb, one_mul, Finset.mul_sum]
      rw [Finset.sum_congr rfl hrow]
      have hpow : ∀ n ∈ Finset.range M, zeta ^ (n + 1) * D.surv L (n + 1) z
          = zeta * (zeta ^ n * D.surv L (n + 1) z) := by
        intro n _; rw [pow_succ]; ring
      rw [Finset.sum_congr rfl hpow, ← Finset.mul_sum]
      ring
    · rw [D.sojGF_of_out hb]
      have hzero : ∑ n ∈ Finset.range N, zeta ^ n * D.surv L n z = 0 :=
        Finset.sum_eq_zero fun n _ => by rw [D.surv_of_out hb n, mul_zero]
      rw [hzero, mul_zero, add_zero]

/-- The `ζ`-weighted tail sum, paired two by two. -/
theorem surv_partial_zeta {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (z : ℕ) {zeta : ℝ}
    (hz : 1 ≤ zeta) :
    ∀ R : ℕ, ∑ n ∈ Finset.range (2 * R), zeta ^ n * D.surv L n z
      ≤ (1 + zeta) * ∑ r ∈ Finset.range R, (zeta ^ 2 * (1 - D.gam ^ 2)) ^ r := by
  have hgpos := D.gam_pos
  have hghalf := D.gam_lt_half
  have hq : (0 : ℝ) ≤ 1 - D.gam ^ 2 := by nlinarith
  intro R
  induction R with
  | zero => simp
  | succ m ih =>
    have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [hidx, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hzp : (0 : ℝ) < zeta := by linarith
    have hpm : zeta ^ (2 * m) = (zeta ^ 2) ^ m := by rw [pow_mul]
    have hpmpos : (0 : ℝ) < zeta ^ (2 * m) := by positivity
    have ha : D.surv L (2 * m) z ≤ (1 - D.gam ^ 2) ^ m := D.surv_two_pow_le hL m z
    have hb : D.surv L (2 * m + 1) z ≤ (1 - D.gam ^ 2) ^ m :=
      le_trans (D.surv_antitone hL (2 * m) z) ha
    have hsplit : (zeta ^ 2 * (1 - D.gam ^ 2)) ^ m = zeta ^ (2 * m) * (1 - D.gam ^ 2) ^ m := by
      rw [mul_pow, hpm]
    have e1 : zeta ^ (2 * m) * D.surv L (2 * m) z ≤ zeta ^ (2 * m) * (1 - D.gam ^ 2) ^ m :=
      mul_le_mul_of_nonneg_left ha hpmpos.le
    have e2 : zeta ^ (2 * m + 1) * D.surv L (2 * m + 1) z
        ≤ zeta * (zeta ^ (2 * m) * (1 - D.gam ^ 2) ^ m) := by
      have hrw : zeta ^ (2 * m + 1) = zeta ^ (2 * m) * zeta := by rw [pow_succ]
      rw [hrw]
      calc zeta ^ (2 * m) * zeta * D.surv L (2 * m + 1) z
          ≤ zeta ^ (2 * m) * zeta * (1 - D.gam ^ 2) ^ m :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = zeta * (zeta ^ (2 * m) * (1 - D.gam ^ 2) ^ m) := by ring
    rw [hsplit]
    nlinarith [ih, e1, e2]

/-- **`eq:doubling_sojourn`, third line.** `E(ζ^ς | Y₀ = y) ≤ 1 + c₅(ζ−1)` for
`1 ≤ ζ ≤ 1 + γ²/6`, with `c₅ = 6/γ²`. -/
theorem sojGF_le {L z : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hz2 : z < 2 * L) {zeta : ℝ}
    (h1 : 1 ≤ zeta) (h2 : zeta ≤ 1 + D.gam ^ 2 / 6) :
    D.sojGF L zeta z ≤ 1 + D.c5 * (zeta - 1) := by
  have hgpos := D.gam_pos
  have hghalf := D.gam_lt_half
  set G : ℝ := D.gam ^ 2 with hG
  have hGpos : 0 < G := by rw [hG]; positivity
  have hGsmall : G < 1 / 4 := by rw [hG]; nlinarith
  have hzp : (0 : ℝ) < zeta := by linarith
  set x : ℝ := zeta ^ 2 * (1 - G) with hx
  have hx0 : (0 : ℝ) ≤ x := by rw [hx]; nlinarith
  have hsq : zeta ^ 2 ≤ (1 + G / 6) ^ 2 := by nlinarith
  have hGle : (0 : ℝ) ≤ 1 - G := by linarith
  have hstep1 : zeta ^ 2 * (1 - G) ≤ (1 + G / 6) ^ 2 * (1 - G) :=
    mul_le_mul_of_nonneg_right hsq hGle
  have hG2 : (0 : ℝ) ≤ G ^ 2 := sq_nonneg G
  have hG3 : (0 : ℝ) ≤ G ^ 3 := by positivity
  have hstep2 : (1 + G / 6) ^ 2 * (1 - G) ≤ 1 - 2 * G / 3 := by nlinarith [hG2, hG3]
  have hxup : x ≤ 1 - 2 * G / 3 := by rw [hx]; linarith
  have hx1 : x < 1 := by linarith
  have hinv : 1 / (1 - x) ≤ 3 / (2 * G) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hpart := D.surv_partial_zeta hL z h1 L
  have hone_zeta : 1 + zeta ≤ 49 / 24 := by linarith
  have hsumnn : (0 : ℝ) ≤ ∑ r ∈ Finset.range L, x ^ r :=
    Finset.sum_nonneg fun r _ => pow_nonneg hx0 r
  have hkey : ∑ n ∈ Finset.range (2 * L), zeta ^ n * D.surv L n z
      ≤ (49 / 24) * (3 / (2 * G)) := by
    have hgeoL := geom_sum_le_inv hx0 hx1 L
    calc ∑ n ∈ Finset.range (2 * L), zeta ^ n * D.surv L n z
        ≤ (1 + zeta) * ∑ r ∈ Finset.range L, x ^ r := hpart
      _ ≤ (49 / 24) * ∑ r ∈ Finset.range L, x ^ r :=
          mul_le_mul_of_nonneg_right hone_zeta hsumnn
      _ ≤ (49 / 24) * (3 / (2 * G)) :=
          mul_le_mul_of_nonneg_left (le_trans hgeoL hinv) (by norm_num)
  rw [D.sojGF_eq_sum hL zeta z (2 * L) (by omega), c5, ← hG]
  have hzm : (0 : ℝ) ≤ zeta - 1 := by linarith
  have hfin : (zeta - 1) * ∑ n ∈ Finset.range (2 * L), zeta ^ n * D.surv L n z
      ≤ (zeta - 1) * ((49 / 24) * (3 / (2 * G))) := mul_le_mul_of_nonneg_left hkey hzm
  have hcmpeq : (49 / 24 : ℝ) * (3 / (2 * G)) = (49 / 16) / G := by field_simp; ring
  have hcmp : (49 / 24 : ℝ) * (3 / (2 * G)) ≤ 6 / G := by
    rw [hcmpeq]
    exact div_le_div_of_nonneg_right (by norm_num) hGpos.le
  have hlast : (zeta - 1) * ((49 / 24) * (3 / (2 * G))) ≤ (zeta - 1) * (6 / G) :=
    mul_le_mul_of_nonneg_left hcmp hzm
  have hcomm : (zeta - 1) * (6 / G) = (6 / G) * (zeta - 1) := by ring
  linarith [hfin, hlast, hcomm.le, hcomm.ge]

/-! ### `eq:doubling_sojourn` on the paper's blocks `I_i(ℓ)` -/

/-- The threshold holds on `I_i(ℓ)` for `i ≥ 1` and `ℓ ≥ ℓ₂`, since `2^i ℓ ≥ 2ℓ ≥ 32cτ`. -/
theorem thr_of_block {d ℓ i : ℕ} (hℓ : D.ell2 d ≤ ℓ) (hi : 1 ≤ i) :
    32 * D.c * D.tau ≤ ((2 ^ i * ℓ : ℕ) : ℝ) := by
  refine D.thr_of_level hℓ ?_
  have h2 : 2 ≤ 2 ^ i := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  exact Nat.mul_le_mul_right ℓ h2

/-- **`eq:doubling_sojourn`.** All three bounds, on the paper's own block `I_i(ℓ)` at `i ≥ 1`
and `ℓ ≥ ℓ₂`, for the exit time `ς` from that block. -/
theorem sojourn_block {d ℓ i : ℕ} (hℓ : D.ell2 d ≤ ℓ) (hi : 1 ≤ i) {y : ℕ}
    (hy : y ∈ block i ℓ) :
    (∀ r : ℕ, D.surv (2 ^ i * ℓ) (2 * r) y ≤ (1 - D.gam ^ 2) ^ r) ∧
      D.sojMean (2 ^ i * ℓ) y ≤ 2 / D.gam ^ 2 ∧
      ∀ zeta : ℝ, 1 ≤ zeta → zeta ≤ 1 + D.gam ^ 2 / 6 →
        D.sojGF (2 ^ i * ℓ) zeta y ≤ 1 + D.c5 * (zeta - 1) := by
  have hL := D.thr_of_block hℓ hi
  rw [mem_block] at hy
  have hy2 : y < 2 * (2 ^ i * ℓ) := by
    have hpow : 2 ^ (i + 1) * ℓ = 2 * (2 ^ i * ℓ) := by ring
    omega
  exact ⟨fun r => D.surv_le_pow hL hy.1 hy2 r, D.sojMean_le hL hy2,
    fun zeta h1 h2 => D.sojGF_le hL hy2 h1 h2⟩

end Decay

end GFNBounds.Doubling
