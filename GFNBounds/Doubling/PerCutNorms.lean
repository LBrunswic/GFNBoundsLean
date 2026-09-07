import GFNBounds.Doubling.CutBalance

/-!
# The `L^p(λ)` mass of the per-cut defect

**`lem:doubling_percut`, Steps 3–4** — `app_doubling.tex:1848–1944`,
`eq:doubling_step2` and `eq:doubling_stepp`.

> `‖(Id − P⋆)1_A‖²_{L²(λ)} ≤ λ_m(1−ε(m))(1−ε(m)+ε_max) ≤ 2λ_m`
>
> and for every `p ∈ [1,∞)`, `‖(Id − P⋆)f_m‖^p_{L^p(λ)} ≤ λ_m(1 + ε_max^{p−1}) ≤ 2λ_m`.

The point of the whole block: the defect of the tail indicator has mass of order `λ_m` — the mass
at the *cut* — while the indicator itself has mass of order `L(m)`, the mass of the whole *tail*.
Since `L(m)/λ_m → ∞`, the Rayleigh quotient collapses and no bounded `S` can exist.

The computation is the one the paper describes: `eq:doubling_step1` has **disjoint supports**, so
the `L^p` mass is a bare sum of point masses, and `eq:doubling_cut` collapses the window sum.

## The norm layer

`Stat.mass p f := ∑' x, |f x|^p * λ x` is the `p`-th power of `‖f‖_{L^p(λ)}`, in plain `ℝ`. Every
estimate of the appendix lives here: they are arithmetic on `tsum`s of nonnegative reals, and in
`eLpNorm` the same two-line arguments become `ℝ≥0∞` round-trips through `toReal`/`ofReal`. The
`MeasureTheory.Lp` layer is built separately and consumed only by the four operator-theoretic
statements (`lem:doubling_operator`, `lem:doubling_fixed_points`, the "no bounded `S`" half of
`theo:doubling_unbounded`, `prop:doubling_unsolvable`).

## SCOPE (disclosed)

Together with `PerCutIdentity`, this file closes **all four steps** of `lem:doubling_percut`:
Step 1 (`0 < λ_m ≤ L ≤ 1 − λ_1 < 1`), Step 2 (`eq:doubling_step1`, in `PerCutIdentity`), Step 3
(`eq:doubling_step2` with its middle term `λ_m(1−ε(m))(1−ε(m)+ε_max)`, `Π f_m = 0`,
`‖f_m‖² = L(1−L)`, and the ratio `eq:doubling_step3`) and Step 4 (`eq:doubling_stepp`, both lines).

Two disclosed deviations, neither a narrowing:

- **`eq:doubling_step3` is stated squared.** `Stat.mass p f` is the `p`-th power of the norm, so
  the ratio appears as `mass 2 ((Id−P⋆)f_m) / mass 2 (f_m) ≤ 2λ_m/(L(1−L))` rather than the
  paper's `‖·‖/‖·‖ ≤ √(2λ_m/(L(1−L)))`. The two are equivalent; keeping the `p`-th powers avoids
  square roots in every downstream estimate, which is what `theo:doubling_unbounded` wants anyway.
- **`Stat.mass_centredTail` needs no hypothesis on `p`.** The paper states it for `p ∈ [1,∞)`;
  `f_m` takes only two values, so the computation is exact at every exponent.

## Hypothesis checklist against `lem:doubling_percut`

| paper hypothesis | here |
|---|---|
| `ε(j) > 0` for every `j ≥ 1`, `ε_max < 1` | ✓ carried (in `Setting`) |
| case (1) or case (2) | ✓ both, via `cap`; `hdm` and `hD` as in `PerCutIdentity` |
| `p ∈ [1, ∞)` | ✓ carried (`hp`) |
| positive recurrence | ⚠ weakened: only the existence of a `Stat` is used, which is what it supplies |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

variable {S : Setting} {cap : Option ℕ}

/-- The `p`-th power of the `L^p(λ)` norm, in plain `ℝ`. -/
noncomputable def Stat.mass (L : Stat S cap) (p : ℝ) (f : St → ℝ) : ℝ :=
  ∑' x, |f x| ^ p * L.lam x

theorem hasSum_dirac (j : ℕ) : HasSum (dirac j) 1 := hasSum_ite_eq _ _

/-- `m` is not in its own window. -/
theorem not_mem_window_self (m : ℕ) : m ∉ window m := by
  rw [mem_window]; omega

theorem cutFn_at_cut (S : Setting) (m : ℕ) : cutFn S m (.lad m) = 1 - S.eps m := by
  rw [cutFn_lad, if_pos rfl, if_neg (not_mem_window_self m)]; ring

theorem cutFn_at_window (S : Setting) {m y : ℕ} (hy : y ∈ window m) :
    cutFn S m (.lad y) = -S.eps y := by
  rw [cutFn_lad, if_neg (by have := window_lt hy; omega), if_pos hy]; ring

theorem cutFn_eq_zero (S : Setting) {m j : ℕ} (h1 : j ≠ m) (h2 : j ∉ window m) :
    cutFn S m (.lad j) = 0 := by
  rw [cutFn_lad, if_neg h1, if_neg h2]; ring

/-- **`eq:doubling_step2` / `eq:doubling_stepp`, the identity.** The `L^p(λ)` mass of the per-cut
defect is a bare sum of point masses: `eq:doubling_step1` has disjoint supports. -/
theorem mass_cutFn (L : Stat S cap) {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 1 ≤ p) :
    L.mass p (cutFn S m)
      = L.lam (.lad m) * (1 - S.eps m) ^ p + ∑ y ∈ window m, L.lam (.lad y) * S.eps y ^ p := by
  have hp0 : p ≠ 0 := by linarith
  have hhalf : 1 ≤ (m + 1) / 2 := by omega
  have hpt : ∀ x : St, |cutFn S m x| ^ p * L.lam x
      = ((1 - S.eps m) ^ p * L.lam (.lad m)) * dirac m x
        + ∑ y ∈ window m, (S.eps y ^ p * L.lam (.lad y)) * dirac y x := by
    intro x
    rcases x with j | _
    · by_cases hjm : j = m
      · subst hjm
        rw [cutFn_at_cut, abs_of_nonneg (S.one_sub_eps_pos hm).le]
        have hw : ∀ y ∈ window j, (S.eps y ^ p * L.lam (.lad y)) * dirac y (.lad j) = 0 := by
          intro y hy
          rw [dirac_lad, if_neg (by have := window_lt hy; omega), mul_zero]
        rw [Finset.sum_congr rfl hw, Finset.sum_const_zero, dirac_lad, if_pos rfl]
        ring
      · by_cases hjw : j ∈ window m
        · rw [cutFn_at_window S hjw, abs_neg, abs_of_nonneg (S.eps_pos (by
            have := (mem_window.mp hjw).1; omega)).le, dirac_lad, if_neg hjm, mul_zero, zero_add,
            sum_dirac_gen]
          exact (if_pos hjw).symm
        · rw [cutFn_eq_zero S hjm hjw, abs_zero, zero_rpow hp0, zero_mul, dirac_lad,
            if_neg hjm, mul_zero, zero_add, sum_dirac_gen, if_neg hjw]
    · have hw : ∀ y ∈ window m, (S.eps y ^ p * L.lam (.lad y)) * dirac y (.sink : St) = 0 := by
        intro y _; rw [dirac_sink, mul_zero]
      rw [cutFn_sink, abs_zero, zero_rpow hp0, zero_mul, dirac_sink, mul_zero, zero_add,
        Finset.sum_congr rfl hw, Finset.sum_const_zero]
  have h1 : HasSum (fun x => ((1 - S.eps m) ^ p * L.lam (.lad m)) * dirac m x)
      ((1 - S.eps m) ^ p * L.lam (.lad m)) := by
    simpa using (hasSum_dirac m).mul_left ((1 - S.eps m) ^ p * L.lam (.lad m))
  have h2 : HasSum (fun x => ∑ y ∈ window m, (S.eps y ^ p * L.lam (.lad y)) * dirac y x)
      (∑ y ∈ window m, S.eps y ^ p * L.lam (.lad y)) :=
    hasSum_sum fun y _ => by simpa using (hasSum_dirac y).mul_left (S.eps y ^ p * L.lam (.lad y))
  have : HasSum (fun x => |cutFn S m x| ^ p * L.lam x)
      ((1 - S.eps m) ^ p * L.lam (.lad m) + ∑ y ∈ window m, S.eps y ^ p * L.lam (.lad y)) := by
    rw [funext hpt]; exact h1.add h2
  rw [Stat.mass, this.tsum_eq, mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _


/-- `x^p = x^(p-1) · x` for `x > 0`. -/
private theorem rpow_split {x p : ℝ} (hx : 0 < x) : x ^ p = x ^ (p - 1) * x := by
  conv_lhs => rw [show p = (p - 1) + 1 by ring]
  rw [rpow_add hx, rpow_one]

/-- **`eq:doubling_step2`, the middle term.** Cut balance collapses the window sum: the defect's
`L^p(λ)` mass is at most `λ_m(1−ε(m))·((1−ε(m))^{p−1} + ε_max^{p−1})`, which at `p = 2` is the
paper's `λ_m(1−ε(m))(1−ε(m)+ε_max)`. -/
theorem mass_cutFn_le_mid (L : Stat S cap) {m : ℕ} (hdm : S.d < m) (hD : HasDouble cap m)
    {p : ℝ} (hp : 1 ≤ p) :
    L.mass p (cutFn S m)
      ≤ L.lam (.lad m) * (1 - S.eps m) * ((1 - S.eps m) ^ (p - 1) + S.epsMax ^ (p - 1)) := by
  have hd1 : 1 ≤ S.d := S.d_pos
  have hm : 1 ≤ m := by omega
  have hhalf : 1 ≤ (m + 1) / 2 := by omega
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  have hem : 0 < 1 - S.eps m := S.one_sub_eps_pos hm
  have hstep : ∀ y ∈ window m, L.lam (.lad y) * S.eps y ^ p
      ≤ S.epsMax ^ (p - 1) * (L.lam (.lad y) * S.eps y) := by
    intro y hy
    have hy1 : 1 ≤ y := by have := (mem_window.mp hy).1; omega
    have hey : 0 < S.eps y := S.eps_pos hy1
    have hbase : S.eps y ^ (p - 1) ≤ S.epsMax ^ (p - 1) :=
      rpow_le_rpow hey.le (S.eps_le hy1) hp1
    have hlam : 0 ≤ L.lam (.lad y) := L.nonneg _
    rw [rpow_split hey]
    nlinarith [mul_nonneg hlam hey.le]
  have hsum : ∑ y ∈ window m, L.lam (.lad y) * S.eps y ^ p
      ≤ S.epsMax ^ (p - 1) * (L.lam (.lad m) * (1 - S.eps m)) := by
    calc ∑ y ∈ window m, L.lam (.lad y) * S.eps y ^ p
        ≤ ∑ y ∈ window m, S.epsMax ^ (p - 1) * (L.lam (.lad y) * S.eps y) :=
          Finset.sum_le_sum hstep
      _ = S.epsMax ^ (p - 1) * ∑ y ∈ window m, L.lam (.lad y) * S.eps y := by
          rw [Finset.mul_sum]
      _ = S.epsMax ^ (p - 1) * (L.lam (.lad m) * (1 - S.eps m)) := by
          rw [cut_balance L hdm hD]
  rw [mass_cutFn L hm hp, rpow_split hem]
  nlinarith [hsum]

/-- **`eq:doubling_step2` / `eq:doubling_stepp`, the bound.** The defect's `L^p(λ)` mass is at most
`2 λ_m` — twice the mass at the cut — for every `p ∈ [1, ∞)`, uniformly in `p`.

This is the whole point of the block: the defect is controlled by `λ_m`, while the indicator it is
the defect of has mass `L(m)`, the mass of the entire tail. -/
theorem mass_cutFn_le_two (L : Stat S cap) {m : ℕ} (hdm : S.d < m) (hD : HasDouble cap m)
    {p : ℝ} (hp : 1 ≤ p) :
    L.mass p (cutFn S m) ≤ 2 * L.lam (.lad m) := by
  have hd1 : 1 ≤ S.d := S.d_pos
  have hm : 1 ≤ m := by omega
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  have hem : 0 < 1 - S.eps m := S.one_sub_eps_pos hm
  have hepos : 0 < S.eps m := S.eps_pos hm
  have hlam : 0 ≤ L.lam (.lad m) := L.nonneg _
  have h1 : (1 - S.eps m) ^ (p - 1) ≤ 1 := rpow_le_one hem.le (by linarith) hp1
  have h2 : S.epsMax ^ (p - 1) ≤ 1 := rpow_le_one S.epsMax_pos.le S.epsMax_lt_one.le hp1
  have hprod : 0 ≤ L.lam (.lad m) * (1 - S.eps m) := mul_nonneg hlam hem.le
  refine le_trans (mass_cutFn_le_mid L hdm hD hp) ?_
  nlinarith


/-! ## The centred tail indicator `f_m` -/

/-- `L(m) = λ([m,∞))` on the loop closure, `λ^K([m,K])` on the truncation — the tail mass. -/
noncomputable def Stat.tailMass (L : Stat S cap) (m : ℕ) : ℝ := ∑' x, L.lam x * tailInd cap m x

theorem Stat.hasSum_tailMass (L : Stat S cap) (m : ℕ) :
    HasSum (fun x => L.lam x * tailInd cap m x) (L.tailMass m) :=
  (L.summable_mul tailInd_bounded).hasSum

theorem Stat.tailMass_nonneg (L : Stat S cap) (m : ℕ) : 0 ≤ L.tailMass m :=
  (L.hasSum_tailMass m).nonneg fun x => mul_nonneg (L.nonneg x) (tailInd_nonneg x)

theorem Stat.hasSum_one (L : Stat S cap) : HasSum L.lam 1 := L.total ▸ L.summable.hasSum

/-- The complement carries `1 − L(m)`. -/
theorem Stat.hasSum_coTail (L : Stat S cap) (m : ℕ) :
    HasSum (fun x => L.lam x * (1 - tailInd cap m x)) (1 - L.tailMass m) := by
  have h : (fun x => L.lam x * (1 - tailInd cap m x))
      = (fun x => L.lam x - L.lam x * tailInd cap m x) := by funext x; ring
  rw [h]; exact L.hasSum_one.sub (L.hasSum_tailMass m)

theorem Stat.tailMass_le_one (L : Stat S cap) (m : ℕ) : L.tailMass m ≤ 1 := by
  have := (L.hasSum_coTail m).nonneg fun x =>
    mul_nonneg (L.nonneg x) (by have := tailInd_le_one (cap := cap) (m := m) x; linarith)
  linarith

/-- `f_m := 1_A − L(m)`, the **centred tail indicator** of `def:doubling_setting`. -/
noncomputable def Stat.centredTail (L : Stat S cap) (m : ℕ) : St → ℝ :=
  fun x => tailInd cap m x - L.tailMass m

/-- **`Π f_m = 0`.** Centring is exactly subtracting the `λ`-mean. -/
theorem Stat.tsum_centredTail (L : Stat S cap) (m : ℕ) :
    ∑' x, L.lam x * L.centredTail m x = 0 := by
  have h : (fun x => L.lam x * L.centredTail m x)
      = (fun x => L.lam x * tailInd cap m x - L.tailMass m * L.lam x) := by
    funext x; rw [Stat.centredTail]; ring
  have : HasSum (fun x => L.lam x * L.centredTail m x)
      (L.tailMass m - L.tailMass m * 1) := by
    rw [h]; exact (L.hasSum_tailMass m).sub (L.hasSum_one.mul_left _)
  rw [this.tsum_eq]; ring

/-- **The defect of `f_m` is the defect of `1_A`.** Centring changes nothing: `P⋆` fixes the
constants (`pstar_const`), so the constant is a `0`-flow. This is why `mass_cutFn_le_two` bounds
the numerator of the Rayleigh quotient in `eq:doubling_step3` directly. -/
theorem centredTail_defect (L : Stat S cap) {m : ℕ} (hdm : S.d < m) (hD : HasDouble cap m)
    {x : St} (hx : OnChain cap x) :
    L.centredTail m x - pstar S cap (L.centredTail m) x = cutFn S m x := by
  have hsplit : L.centredTail m = tailInd cap m + (fun _ => -L.tailMass m) := by
    funext y; rw [Stat.centredTail]; simp; ring
  rw [hsplit, pstar_add, pstar_const]
  simp only [Pi.add_apply]
  rw [← percut_id S cap hdm hD hx]
  ring

/-- **`eq:doubling_stepp`, second line.** `‖f_m‖^p_{L^p(λ)} = L(1−L)^p + (1−L)L^p`.

⚠ weakened hypothesis: the paper states this for `p ∈ [1,∞)`, but the identity needs nothing about
`p` at all — `f_m` takes only the two values `1 − L` and `−L`, so the computation is exact at every
exponent. The hypothesis is dropped rather than carried unused. -/
theorem Stat.mass_centredTail (L : Stat S cap) (m : ℕ) (p : ℝ) :
    L.mass p (L.centredTail m)
      = L.tailMass m * (1 - L.tailMass m) ^ p + (1 - L.tailMass m) * L.tailMass m ^ p := by
  have hL0 : 0 ≤ L.tailMass m := L.tailMass_nonneg m
  have hL1 : L.tailMass m ≤ 1 := L.tailMass_le_one m
  have hpt : ∀ x : St, |L.centredTail m x| ^ p * L.lam x
      = (1 - L.tailMass m) ^ p * (L.lam x * tailInd cap m x)
        + L.tailMass m ^ p * (L.lam x * (1 - tailInd cap m x)) := by
    intro x
    rcases eq_or_ne (tailInd cap m x) 1 with h | h
    · rw [Stat.centredTail, h, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - L.tailMass m)]
      ring
    · have h0 : tailInd cap m x = 0 := by
        rcases x with j | _
        · rw [tailInd_lad] at h ⊢; split at h <;> simp_all
        · rfl
      rw [Stat.centredTail, h0, zero_sub, abs_neg, abs_of_nonneg hL0]
      ring
  have hsum : HasSum (fun x => |L.centredTail m x| ^ p * L.lam x)
      ((1 - L.tailMass m) ^ p * L.tailMass m + L.tailMass m ^ p * (1 - L.tailMass m)) := by
    rw [funext hpt]
    exact ((L.hasSum_tailMass m).mul_left _).add ((L.hasSum_coTail m).mul_left _)
  rw [Stat.mass, hsum.tsum_eq]
  ring

/-- The denominator of `eq:doubling_step3`, bounded below: `‖f_m‖^p ≥ L(1−L)^p`. -/
theorem Stat.mass_centredTail_ge (L : Stat S cap) (m : ℕ) (p : ℝ) :
    L.tailMass m * (1 - L.tailMass m) ^ p ≤ L.mass p (L.centredTail m) := by
  have hL0 : 0 ≤ L.tailMass m := L.tailMass_nonneg m
  have hL1 : L.tailMass m ≤ 1 := L.tailMass_le_one m
  rw [L.mass_centredTail m p]
  have : 0 ≤ (1 - L.tailMass m) * L.tailMass m ^ p :=
    mul_nonneg (by linarith) (rpow_nonneg hL0 p)
  linarith


/-! ## The Rayleigh quotient of `eq:doubling_step3` -/

/-- Masses only see the chain: `λ` vanishes off it, so two functions agreeing on the chain have
the same `L^p(λ)` mass. This is what lets the off-chain failure of `percut_id` be harmless. -/
theorem Stat.mass_congr_onChain (L : Stat S cap) (p : ℝ) {f g : St → ℝ}
    (h : ∀ x, OnChain cap x → f x = g x) : L.mass p f = L.mass p g := by
  refine tsum_congr fun x => ?_
  by_cases hx : OnChain cap x
  · rw [h x hx]
  · rw [L.vanish hx, mul_zero, mul_zero]

/-- The `L^p(λ)` mass of `(Id − P⋆)f_m` is that of the per-cut defect. -/
theorem Stat.mass_centredTail_defect (L : Stat S cap) {m : ℕ} (hdm : S.d < m)
    (hD : HasDouble cap m) (p : ℝ) :
    L.mass p (fun x => L.centredTail m x - pstar S cap (L.centredTail m) x)
      = L.mass p (cutFn S m) :=
  L.mass_congr_onChain p fun _ hx => centredTail_defect L hdm hD hx

/-- **The numerator of `eq:doubling_step3`.** `‖(Id − P⋆)f_m‖^p_{L^p(λ)} ≤ 2 λ_m`, for every
`p ∈ [1,∞)` and on either chain. -/
theorem Stat.mass_defect_le (L : Stat S cap) {m : ℕ} (hdm : S.d < m) (hD : HasDouble cap m)
    {p : ℝ} (hp : 1 ≤ p) :
    L.mass p (fun x => L.centredTail m x - pstar S cap (L.centredTail m) x)
      ≤ 2 * L.lam (.lad m) := by
  rw [L.mass_centredTail_defect hdm hD p]
  exact mass_cutFn_le_two L hdm hD hp

/-- **`‖f_m‖²_{L²(λ)} = L(1−L)`**, exactly — the denominator of `eq:doubling_step3`.

The two terms of `mass_centredTail` collapse: `L(1−L)² + (1−L)L² = L(1−L)[(1−L) + L]`. -/
theorem Stat.mass_two_centredTail (L : Stat S cap) (m : ℕ) :
    L.mass 2 (L.centredTail m) = L.tailMass m * (1 - L.tailMass m) := by
  have hsq : ∀ y : ℝ, y ^ (2 : ℝ) = y * y := by
    intro y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
    ring
  rw [L.mass_centredTail m 2, hsq, hsq]
  ring

/-- **`eq:doubling_step3`, squared.** The squared Rayleigh quotient of `f_m` is at most
`2λ_m / (L(1−L))`: the defect is controlled by the mass at the *cut*, the function by the mass of
the whole *tail*.

Since `L(m)/λ_m → ∞` (`cor:doubling_tail`), this is what drives the infimum of
`theo:doubling_unbounded` to zero. -/
theorem Stat.rayleigh_two_le (L : Stat S cap) {m : ℕ} (hdm : S.d < m) (hD : HasDouble cap m)
    (hpos : 0 < L.tailMass m * (1 - L.tailMass m)) :
    L.mass 2 (fun x => L.centredTail m x - pstar S cap (L.centredTail m) x)
        / L.mass 2 (L.centredTail m)
      ≤ 2 * L.lam (.lad m) / (L.tailMass m * (1 - L.tailMass m)) := by
  rw [L.mass_two_centredTail m]
  gcongr
  exact L.mass_defect_le hdm hD (by norm_num)


/-! ## `lem:doubling_percut` Step 1: the tail is not degenerate

> Since `m > d ≥ 1`, the state `1` lies outside `A` and the state `m` lies in `A`, so
> `0 < λ_m ≤ L ≤ 1 − λ_1 < 1`.
-/

/-- `λ_m ≤ L(m)`: the cut itself lies in the tail. -/
theorem Stat.lam_le_tailMass (L : Stat S cap) {m : ℕ} (hm : inTail cap m m) :
    L.lam (.lad m) ≤ L.tailMass m := by
  have h := le_hasSum (L.hasSum_tailMass m) (St.lad m)
    fun j _ => mul_nonneg (L.nonneg j) (tailInd_nonneg j)
  rwa [tailInd_one hm, mul_one] at h

/-- `λ_1 ≤ 1 − L(m)`: the state `1` lies outside the tail, since `m > d ≥ 1`. -/
theorem Stat.lam_one_le_coTailMass (L : Stat S cap) {m : ℕ} (hm1 : 1 < m) :
    L.lam (.lad 1) ≤ 1 - L.tailMass m := by
  have h := le_hasSum (L.hasSum_coTail m) (St.lad 1) fun j _ =>
    mul_nonneg (L.nonneg j) (by have := tailInd_le_one (cap := cap) (m := m) j; linarith)
  rwa [tailInd_zero (not_inTail_of_lt hm1), sub_zero, mul_one] at h

/-- **`lem:doubling_percut` Step 1.** `0 < λ_m ≤ L(m) ≤ 1 − λ_1 < 1`, so `‖f_m‖² = L(1−L) > 0`
and the Rayleigh quotient of `eq:doubling_step3` is well posed. -/
theorem Stat.tailMass_mul_coTail_pos (L : Stat S cap) {m : ℕ} (hdm : S.d < m)
    (hD : HasDouble cap m) : 0 < L.tailMass m * (1 - L.tailMass m) := by
  have hd1 : 1 ≤ S.d := S.d_pos
  have hm1 : 1 < m := by omega
  have hchain : OnChain cap (St.lad m) := onChain_lad_of_hasDouble hD le_rfl
  have h1 : 0 < L.lam (.lad m) := L.pos hchain
  have h2 : 0 < L.lam (.lad 1) := L.pos (onChain_lad_of_hasDouble hD (by omega))
  have hL : 0 < L.tailMass m := lt_of_lt_of_le h1 (L.lam_le_tailMass (inTail_of le_rfl hchain))
  have hcoL : 0 < 1 - L.tailMass m := lt_of_lt_of_le h2 (L.lam_one_le_coTailMass hm1)
  exact mul_pos hL hcoL

/-- **`eq:doubling_step3`**, with the positivity hypothesis discharged by Step 1. -/
theorem Stat.rayleigh_two_le' (L : Stat S cap) {m : ℕ} (hdm : S.d < m) (hD : HasDouble cap m) :
    L.mass 2 (fun x => L.centredTail m x - pstar S cap (L.centredTail m) x)
        / L.mass 2 (L.centredTail m)
      ≤ 2 * L.lam (.lad m) / (L.tailMass m * (1 - L.tailMass m)) :=
  L.rayleigh_two_le hdm hD (L.tailMass_mul_coTail_pos hdm hD)

end GFNBounds.Doubling
