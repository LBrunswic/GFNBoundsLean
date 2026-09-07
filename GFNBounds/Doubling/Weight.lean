import GFNBounds.Doubling.Product
import GFNBounds.Doubling.DescentLaw

/-!
# `lem:doubling_weight`: the weight of a descent deviates from `1` by `O(1/ℓ)` in mean

**`lem:doubling_weight`** — `app_doubling.tex:1343–1383`.

> In the setting of `def:doubling_setting` and `def:doubling_decay_notation`, with the constant
> `c₄` of `lem:doubling_descent` and `γ`, `c₅`, `ℓ₂` of `lem:doubling_escape`, put `c₃ := 8c₅c₄`
> and `ℓ₃ := max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)`, which depend on `c` and `d` alone. Let
> `ℓ ≥ ℓ₃` be an integer, let `(Y_n)` and `N_ℓ` be the descent chain of `lem:doubling_descent`
> at the level `ℓ` and its exit time, and let `Z_ℓ := ∏_{n<N_ℓ} R₀(Y_n)` be the weight of
> `lem:doubling_descent`(3). Then, for every integer `m ≥ 2ℓ`,
> `E(|Z_ℓ − 1| ∣ Y_0 = m) ≤ c₃/ℓ`.   `(eq:doubling_weight)`

## The modelling decision

**No chain, and no absolute-deviation transform either.** `E(|Z_ℓ − 1|)` is not a recursion in the
state — `|R₀(y)·Z' − 1|` does not decompose — so the paper's own statement is not the one to
formalize. What `theo:doubling_sharp` consumes is its *consequence*, and that one **is** a
recursion: for a test function `g` bounded by `B`,

  `|descW ℓ g y − descP ℓ g y| = |E((Z_ℓ − 1) g(Y_{N_ℓ}) ∣ Y_0 = y)| ≤ B · E|Z_ℓ − 1|`,

`descW` being the unnormalised descent transform of `Descent.lean` (which carries `Z_ℓ`) and
`descP` the normalised one of `DescentLaw.lean` (which does not). That difference is bounded here
directly, by strong induction on the state, against the product transform `prodW` of
`Product.lean`:

  `|descW ℓ g y − descP ℓ g y| ≤ B · (prodW ℓ b y − 1)`   whenever `|R₀ − 1| ≤ b` above `2ℓ`
  (`Decay.abs_descW_sub_descP_le`),

which replaces the paper's pathwise `|Z_ℓ − 1| ≤ ∏_{n<N_ℓ}(1 + b̃(Y_n)) − 1`. The induction step is
the single identity

  `descW y − descP y = R₀(y)·(SW − SP) + (R₀(y) − 1)·descP y`,   `SW, SP` the one-step averages,

and the elementary inequality `Decay.weight_step` behind it: with `t := SQ − 1 ≥ 0` and
`|r − 1| ≤ β`, `r·B·t + β·B ≤ B·((1+β)(1+t) − 1)` because the difference is `B·t·(1 + β − r) ≥ 0`.

Because the comparison is against `R₀` itself and not against a pathwise product of exponentials,
`b` may be taken to be `c₄/y` rather than the paper's `b̃(y) = e^{2c₄/y} − 1`, so `H := c₄` rather
than `4c₄` and the constant improves by a factor of `4`:

  `c₃ = 32 c₅ c τ = 192 cτ/γ²`   against the paper's `8c₅c₄ = 128 c₅ cτ`,

and `ℓ₃ = max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉)`, the paper's four requirements collapsing to two.

## SCOPE (disclosed)

* **The paper's `eq:doubling_weight` is not stated**, because `Z_ℓ` is a random variable and this
  library builds no chain. What is proved is the inequality on transforms displayed above, at
  every bounded `g` and every state — which is what `Sharp.lean` and `SharpRate.lean` take as
  their hypothesis `hweight`, and the only use `lem:doubling_weight` has in the appendix.
* The bound is proved at **every** starting state `y`, not only `y ≥ 2ℓ`: below `2ℓ` both
  transforms are `g y` and the difference is `0`.
* `c₃` and `ℓ₃` are **effective** here, inheriting `c₄ = 16cτ` from `R0Bound.lean` and
  `γ = √τ/(2(√τ+1))`, `c₅ = 6/γ²` from `Escape.lean` and `Sojourn.lean`. The paper's are not.
* `d` does not occur: `ℓ₃` needs `ℓ ≥ ℓ₂` only through `32cτ ≤ 2ℓ`, and the `d + 1` half of `ℓ₂`
  is consumed elsewhere (by the cut balance, in `Sharp.lean`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1`, `p = p_*`, `τ = 2^{p_*}` | ✓ carried by `Decay` |
| `ℓ ≥ ℓ₃`, with `ℓ₃` from `ℓ₂, c₄, γ, c₅` | ✓ carried, and made effective (`Decay.ell3`) |
| `m ≥ 2ℓ` | ⚠ weakened: dropped, the statement holding at every state |
| `Z_ℓ = ∏_{n<N_ℓ} R₀(Y_n)`, `E(|Z_ℓ−1|) ≤ c₃/ℓ` | ⚠ **replaced** by the transform inequality (see SCOPE) |
| `eq:doubling_R0`: `|R₀(m) − 1| ≤ c₄/m` | ✓ carried, and **proved** (`Decay.R0_sub_one_le`) |
| `eq:doubling_product` at `b̃`, `H = 4c₄` | ✓ carried, and **proved** (`Decay.prodW_two_sided`), at `b = c₄/y`, `H = c₄` |
| `e^x − 1 ≤ 2x` on `[0,1]` | ✓ carried (`GFNBounds.Doubling.exp_sub_one_le_two_mul`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-- **`e^x − 1 ≤ 2x` on `[0,1]`**, the paper's last inequality in the proof of
`lem:doubling_weight`. -/
theorem exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have h := Real.exp_bound' hx0 hx1 (n := 2) (by norm_num)
  simp [Finset.sum_range_succ] at h
  nlinarith [h, sq_nonneg x]

/-- **The induction step of `lem:doubling_weight`, as arithmetic.** With `r` the total window
weight, `β` a bound for `|r − 1|`, `SW`, `SP` the one-step averages of the two transforms and
`SQ ≥ 1` the one-step average of the product transform, the step of the recursion propagates the
bound `B·(SQ − 1)` to `B·((1+β)·SQ − 1)`.

The margin is exactly `B·(SQ − 1)·(1 + β − r) ≥ 0`. -/
theorem weight_step {r beta B SW SP SQ : ℝ} (hB : 0 ≤ B) (hrnn : 0 ≤ r)
    (hrb : |r - 1| ≤ beta) (h1 : |SW - SP| ≤ B * (SQ - 1)) (h2 : |SP| ≤ B) (h3 : 1 ≤ SQ) :
    |r * SW - SP| ≤ B * ((1 + beta) * SQ - 1) := by
  have hbeta : 0 ≤ beta := le_trans (abs_nonneg _) hrb
  have hrle : r - 1 ≤ beta := le_trans (le_abs_self _) hrb
  have hsplit : r * SW - SP = r * (SW - SP) + (r - 1) * SP := by ring
  have e1 : |r * (SW - SP)| = r * |SW - SP| := by rw [abs_mul, abs_of_nonneg hrnn]
  have e2 : |(r - 1) * SP| = |r - 1| * |SP| := abs_mul _ _
  have s1 : r * |SW - SP| ≤ r * (B * (SQ - 1)) := mul_le_mul_of_nonneg_left h1 hrnn
  have s2 : |r - 1| * |SP| ≤ beta * B := mul_le_mul hrb h2 (abs_nonneg _) hbeta
  have hadd : |r * SW - SP| ≤ |r * (SW - SP)| + |(r - 1) * SP| := by
    rw [hsplit]; exact abs_add_le _ _
  rw [e1, e2] at hadd
  nlinarith [mul_nonneg (mul_nonneg hB (by linarith : (0 : ℝ) ≤ SQ - 1))
    (by linarith : (0 : ℝ) ≤ 1 + beta - r)]

namespace Decay

variable (D : Decay)

/-- The one-step law of `DescentLaw.lean` and the one of `Sojourn.lean` are the same function. -/
theorem kern_eq_pk (z j : ℕ) : D.kern z j = D.pk z j := rfl

/-- The product transform is at least `1` when its factors are: `prodW ℓ b ≥ 1` for `b ≥ 0`
above `2ℓ`. -/
theorem one_le_prodW {ℓ : ℕ} (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) {b : ℕ → ℝ}
    (hb : ∀ y : ℕ, 2 * ℓ ≤ y → 0 ≤ b y) (z : ℕ) : 1 ≤ D.prodW ℓ b z := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    by_cases h : z < 2 * ℓ
    · rw [D.prodW_of_lt b h]
    · have hz2l : 2 * ℓ ≤ z := by omega
      have hzthr := D.thr_of_two_level hℓ hz2l
      rw [D.prodW_of_ge b h]
      have hsum : (1 : ℝ) ≤ ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j := by
        calc (1 : ℝ) = ∑ j ∈ window z, D.pk z j := (D.sum_pk hzthr).symm
          _ ≤ ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j :=
              Finset.sum_le_sum fun j hj =>
                le_mul_of_one_le_right (D.pk_nonneg hzthr hj) (ih j (window_lt hj))
      nlinarith [hb z hz2l, hsum]

/-- The normalised transform of a function bounded by `B` is bounded by `B`: it is an average. -/
theorem abs_descP_le {ℓ : ℕ} (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) {B : ℝ} {g : ℕ → ℝ}
    (hg : ∀ j, |g j| ≤ B) (y : ℕ) : |D.descP ℓ g y| ≤ B := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    by_cases hlt : y < 2 * ℓ
    · rw [D.descP_of_lt g hlt]; exact hg y
    · have hy2l : 2 * ℓ ≤ y := by omega
      have hythr := D.thr_of_two_level hℓ hy2l
      rw [D.descP_of_ge g hlt]
      simp only [Decay.kern_eq_pk]
      calc |∑ j ∈ window y, D.pk y j * D.descP ℓ g j|
          ≤ ∑ j ∈ window y, |D.pk y j * D.descP ℓ g j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ window y, D.pk y j * B := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [abs_mul, abs_of_nonneg (D.pk_nonneg hythr hj)]
            exact mul_le_mul_of_nonneg_left (ih j (window_lt hj)) (D.pk_nonneg hythr hj)
        _ = B := by rw [← Finset.sum_mul, D.sum_pk hythr, one_mul]

/-- **`lem:doubling_weight`, in the form the sharp block consumes.** The unnormalised and the
normalised descent transforms of a function bounded by `B` differ by at most `B·(prodW − 1)`,
where `prodW` is the product transform at any `b` dominating `|R₀ − 1|` above `2ℓ`.

Proved by strong induction on the state; the step is `Decay.weight_step`. This replaces the
paper's pathwise `|Z_ℓ − 1| ≤ ∏_{n<N_ℓ}(1 + b̃(Y_n)) − 1`. -/
theorem abs_descW_sub_descP_le {ℓ : ℕ} (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) {b : ℕ → ℝ}
    (hbR : ∀ y : ℕ, 2 * ℓ ≤ y → |D.R0 y - 1| ≤ b y) {B : ℝ} {g : ℕ → ℝ}
    (hg : ∀ j, |g j| ≤ B) :
    ∀ y : ℕ, |D.descW ℓ g y - D.descP ℓ g y| ≤ B * (D.prodW ℓ b y - 1) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg (g 0)) (hg 0)
  have hb : ∀ y : ℕ, 2 * ℓ ≤ y → 0 ≤ b y := fun y hy => le_trans (abs_nonneg _) (hbR y hy)
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    by_cases hlt : y < 2 * ℓ
    · rw [D.descW_of_lt g hlt, D.descP_of_lt g hlt, D.prodW_of_lt b hlt]
      simp
    · have hy2l : 2 * ℓ ≤ y := by omega
      have hythr : 32 * D.c * D.tau ≤ (y : ℝ) := D.thr_of_two_level hℓ hy2l
      have hR0half : (1 : ℝ) / 2 ≤ D.R0 y := D.half_le_R0 hythr
      have hR0nn : (0 : ℝ) ≤ D.R0 y := by linarith
      have hR0ne : D.R0 y ≠ 0 := by intro hc; rw [hc] at hR0half; norm_num at hR0half
      have hpkmul : ∀ j : ℕ, D.R0 y * D.pk y j = D.wm y j := by
        intro j; rw [pk]; field_simp
      have hsumW : ∑ j ∈ window y, D.wm y j * D.descW ℓ g j
          = D.R0 y * ∑ j ∈ window y, D.pk y j * D.descW ℓ g j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [← hpkmul j]; ring
      -- the three one-step averages
      have h1 : |(∑ j ∈ window y, D.pk y j * D.descW ℓ g j)
              - ∑ j ∈ window y, D.pk y j * D.descP ℓ g j|
          ≤ B * ((∑ j ∈ window y, D.pk y j * D.prodW ℓ b j) - 1) := by
        have hdiff : (∑ j ∈ window y, D.pk y j * D.descW ℓ g j)
              - ∑ j ∈ window y, D.pk y j * D.descP ℓ g j
            = ∑ j ∈ window y, D.pk y j * (D.descW ℓ g j - D.descP ℓ g j) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hdiff]
        calc |∑ j ∈ window y, D.pk y j * (D.descW ℓ g j - D.descP ℓ g j)|
            ≤ ∑ j ∈ window y, |D.pk y j * (D.descW ℓ g j - D.descP ℓ g j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ window y, D.pk y j * (B * (D.prodW ℓ b j - 1)) := by
              refine Finset.sum_le_sum fun j hj => ?_
              rw [abs_mul, abs_of_nonneg (D.pk_nonneg hythr hj)]
              exact mul_le_mul_of_nonneg_left (ih j (window_lt hj)) (D.pk_nonneg hythr hj)
          _ = ∑ j ∈ window y, (B * (D.pk y j * D.prodW ℓ b j) - B * D.pk y j) :=
              Finset.sum_congr rfl fun j _ => by ring
          _ = B * (∑ j ∈ window y, D.pk y j * D.prodW ℓ b j)
                - B * ∑ j ∈ window y, D.pk y j := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = B * ((∑ j ∈ window y, D.pk y j * D.prodW ℓ b j) - 1) := by
              rw [D.sum_pk hythr]; ring
      have h2 : |∑ j ∈ window y, D.pk y j * D.descP ℓ g j| ≤ B := by
        have hh := D.abs_descP_le hℓ hg y
        rw [D.descP_of_ge g hlt] at hh
        simpa only [Decay.kern_eq_pk] using hh
      have h3 : (1 : ℝ) ≤ ∑ j ∈ window y, D.pk y j * D.prodW ℓ b j := by
        calc (1 : ℝ) = ∑ j ∈ window y, D.pk y j := (D.sum_pk hythr).symm
          _ ≤ ∑ j ∈ window y, D.pk y j * D.prodW ℓ b j :=
              Finset.sum_le_sum fun j hj =>
                le_mul_of_one_le_right (D.pk_nonneg hythr hj) (D.one_le_prodW hℓ hb j)
      rw [D.descW_of_ge g hlt, D.descP_of_ge g hlt, D.prodW_of_ge b hlt, hsumW]
      simp only [Decay.kern_eq_pk]
      exact weight_step hB hR0nn (hbR y hy2l) h1 h2 h3

/-! ### The constants -/

/-- **`ℓ₃`, made effective.** `ℓ₃ := max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉)`: the first requirement is
`32cτ ≤ 2ℓ`, under which `eq:doubling_R0` and the one-step law are available; the second is
`c₄ ≤ γ²ℓ/6`, the hypothesis of `eq:doubling_product` at `H := c₄`, and simultaneously
`c₅c₄/ℓ ≤ 1`, which is what `e^x − 1 ≤ 2x` needs. -/
noncomputable def ell3 (D : Decay) : ℕ :=
  max 1 (max ⌈16 * D.c * D.tau⌉₊ ⌈96 * D.c * D.tau / D.gam ^ 2⌉₊)

theorem one_le_ell3 : 1 ≤ D.ell3 := le_max_left _ _

/-- **`c₃`, made effective.** `c₃ := 32c₅c₄/4 = 32c₅cτ = 192cτ/γ²`. -/
noncomputable def c3 (D : Decay) : ℝ := 32 * D.c5 * D.c * D.tau

theorem c5_pos : 0 < D.c5 := by
  have := D.gam_pos
  rw [c5]; positivity

theorem c3_nonneg : 0 ≤ D.c3 := by
  have h := mul_pos D.c5_pos D.ctau_pos
  rw [c3]; nlinarith

/-- **`lem:doubling_weight`**, with both constants explicit: at every level `ℓ ≥ ℓ₃`, every
function `g` bounded by `B` and every state `y`,

  `|descW ℓ g y − descP ℓ g y| ≤ B c₃/ℓ`,   `c₃ = 32c₅cτ`, `ℓ₃ = max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉)`.

This is `eq:doubling_weight` in the form `theo:doubling_sharp` consumes. -/
theorem weight_bound {ℓ : ℕ} (hℓ : D.ell3 ≤ ℓ) {B : ℝ} {g : ℕ → ℝ} (hg : ∀ j, |g j| ≤ B)
    (y : ℕ) : |D.descW ℓ g y - D.descP ℓ g y| ≤ B * D.c3 / (ℓ : ℝ) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg (g 0)) (hg 0)
  have hgp := D.gam_pos
  have hg2 : (0 : ℝ) < D.gam ^ 2 := by positivity
  have hct := D.ctau_pos
  have hℓ1 : 1 ≤ ℓ := le_trans D.one_le_ell3 hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have h16 : (16 : ℝ) * D.c * D.tau ≤ (ℓ : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hℓ
  have h96 : (96 : ℝ) * D.c * D.tau / D.gam ^ 2 ≤ (ℓ : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hℓ
  have hthr : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ) := by linarith
  have hH0 : (0 : ℝ) ≤ 16 * D.c * D.tau := by nlinarith
  have h96' : (96 : ℝ) * D.c * D.tau ≤ D.gam ^ 2 * (ℓ : ℝ) := by
    rw [div_le_iff₀ hg2] at h96; linarith
  have hH : (16 : ℝ) * D.c * D.tau ≤ D.gam ^ 2 * (ℓ : ℝ) / 6 := by linarith
  set b : ℕ → ℝ := fun w => 16 * D.c * D.tau / (w : ℝ) with hbdef
  have hbR : ∀ w : ℕ, 2 * ℓ ≤ w → |D.R0 w - 1| ≤ b w := by
    intro w hw
    exact D.R0_sub_one_le (by omega : 1 ≤ w)
  have hbb : ∀ w : ℕ, ℓ ≤ w → |b w| ≤ (16 * D.c * D.tau) / (w : ℝ) := by
    intro w hw
    have hw1 : (0 : ℝ) < (w : ℝ) := by
      have : 1 ≤ w := le_trans hℓ1 hw
      exact_mod_cast this
    rw [hbdef, abs_of_nonneg (by positivity)]
  -- the product transform is `1 + O(1/ℓ)`
  have hprod : D.prodW ℓ b y ≤ Real.exp (D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)) :=
    (D.prodW_two_sided hthr hH0 hH hbb y).2
  have hxdef : D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ) = 96 * D.c * D.tau / D.gam ^ 2 / (ℓ : ℝ) := by
    rw [c5]; field_simp; ring
  have hx0 : (0 : ℝ) ≤ D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ) :=
    div_nonneg (mul_nonneg D.c5_pos.le hH0) hℓpos.le
  have hx1 : D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ) ≤ 1 := by
    rw [hxdef, div_le_one hℓpos]; exact h96
  have hexp := exp_sub_one_le_two_mul hx0 hx1
  have hc3eq : 2 * (D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)) = D.c3 / (ℓ : ℝ) := by
    rw [c3]; ring
  have hstep : D.prodW ℓ b y - 1 ≤ D.c3 / (ℓ : ℝ) := by
    rw [← hc3eq]; linarith
  calc |D.descW ℓ g y - D.descP ℓ g y| ≤ B * (D.prodW ℓ b y - 1) :=
        D.abs_descW_sub_descP_le hthr hbR hg y
    _ ≤ B * (D.c3 / (ℓ : ℝ)) := mul_le_mul_of_nonneg_left hstep hB
    _ = B * D.c3 / (ℓ : ℝ) := by ring

end Decay

end GFNBounds.Doubling
