import GFNBounds.Doubling.Sojourn
import GFNBounds.Doubling.Descent

/-!
# `lem:doubling_product`: the weight of a descent is `1 + O(1/ℓ)` in expectation

**`lem:doubling_product`** — `app_doubling.tex:1110–1153`.

> Let `s = 1` and `0 < c < 1`, in the notation of `def:doubling_setting` and
> `def:doubling_decay_notation`, with the constants `γ`, `c₅` and `ℓ₂` of
> `lem:doubling_escape`. Let `ℓ ≥ ℓ₂`, let `(Y_n)` and `N_ℓ` be the descent chain of
> `lem:doubling_descent` at the level `ℓ` and its exit time, let `m ≥ 2ℓ`, let `H` be a number
> with `0 ≤ H ≤ γ²ℓ/6`, and let `b` be a function on the integers `≥ ℓ` with `|b(y)| ≤ H/y` for
> every integer `y ≥ ℓ`. Then
> `e^{−c₅H/ℓ} ≤ E(∏_{n<N_ℓ}(1+b(Y_n)) | Y₀ = m) ≤ e^{c₅H/ℓ}`.   `(eq:doubling_product)`

## The modelling decision

**No chain, and no strong Markov property.** As `Descent.lean` models `E(Z_ℓ g(Y_{N_ℓ}))` by the
recursion `descW`, and `Sojourn.lean` models the exit law by `surv`/`sojMean`/`sojGF`, the path
functional of `eq:doubling_product` is modelled here by the recursion in the **state**

  `prodW ℓ b z = if z < 2ℓ then 1 else (1 + b z) · Σ_{j ∈ W(z)} p(z,j) · prodW ℓ b j`,

well-founded because every `j ∈ W(z)` has `j < z` — which is `lem:doubling_descent`(1). This is
`Ψ(z) := E(∏_{n<N_ℓ}(1+b(Y_n)) | Y₀ = z)`: the factor at the current state times the average of
`Ψ` after one step, and `1` once the descent has fallen below `2ℓ`.

The paper's proof conditions on the exit time `ς` from the dyadic block `I_i(ℓ)` and invokes the
strong Markov property there. **That step is replaced by a comparison lemma**, proved by strong
induction on the state inside one block: with `A` a bound for `Ψ` below the block,

* `prodW_block_le` — if `1 + b ≤ ζ` on `I = [L,2L)` and `Ψ ≤ A` below `L`, then
  `Ψ(z) ≤ A · E(ζ^ς | Y₀ = z)` for every `z < 2L`;
* `prodW_block_ge` — if `1 + b ≥ 1 − x` on `I` and `Ψ ≥ A ≥ 0` below `L`, then
  `Ψ(z) ≥ A · (1 − x·E(ς | Y₀ = z))` for every `z < 2L`.

Both are one line of algebra past the recursion once `Σ_{j∈W(z)} p(z,j) = 1` (`sum_pk`) and the
recursions `sojGF_of_in`, `sojMean_of_in` are in hand; the second reproduces the paper's
`(1−x)^ς ≥ 1 − ςx` exactly, the slack `x²(E(ς)−1) ≥ 0` being what makes the induction close.
Feeding them the sojourn bounds of `Sojourn.lean` and iterating over `i` gives
`eq:doubling_product`, in the form of the two **level invariants**

  `Ψ(z) ≤ exp(c₅H/ℓ · (1 − 2^{-i}))` and `Ψ(z) ≥ exp(−4H/(γ²ℓ) · (1 − 2^{-i}))`
  for every `z < 2^{i+1}ℓ`,

which are the paper's `φ_i ≤ e^{c₅H/ℓ}` and `φ_i ≥ e^{−4H/(γ²ℓ)}` with the partial geometric sum
kept, so that the induction on `i` is exact rather than asymptotic.

## What this closes: **`theo:doubling_decay` is now unconditional**

`eq:doubling_product` at `b := R₀ − 1`, `H := c₄ = 16cτ` is exactly the pair of hypotheses
`hlo`/`hhi` that `Descent.lean`'s `theo:doubling_decay` carries, and which `Descent.lean` names
as the one thing the decay block assumes. They are discharged here:

* `prodW_R0_eq_descOne` — `prodW ℓ (R₀ − 1) = descOne ℓ`, the two recursions being the same one,
  since `(1 + (R₀(z) − 1))·(w_z(j)/R₀(z)) = w_z(j)`;
* `descOne_two_sided` — `e^{−c₅c₄/ℓ} ≤ E(Z_ℓ | Y₀ = y) ≤ e^{c₅c₄/ℓ}` at every level `ℓ ≥ m₀`,
  with `m₀ = max(ℓ₂, ⌈6c₄/γ²⌉) = max(ℓ₂, ⌈96cτ/γ²⌉)` the integer `theo:doubling_decay` names,
  explicit here because `c₄`, `ℓ₂` and `γ` are;
* `decay_block_of_cutBal` — `eq:doubling_block`, `theo:doubling_decay`(1);
* `decay_two_sided_of_cutBal` — `eq:doubling_decay`, `theo:doubling_decay`(2), with no
  hypothesis left beyond the cut balance and positivity of the sequence.

## SCOPE (disclosed)

* **The level condition is the effective `32cτ ≤ 2ℓ`**, not the paper's `ℓ ≥ ℓ₂`. This is the
  same replacement `Escape.lean` and `Sojourn.lean` already make, and it is weaker than the
  paper's hypothesis: `Decay.ell2 d ≤ ℓ` implies it, since `ell2 d = max(d+1, ⌈16cτ⌉)`.
  `prodW_two_sided_paper` is the statement back in the paper's `ℓ ≥ ℓ₂` form. In particular `d`
  does not occur in `prodW_two_sided`: the recursion is built from `w` and `R₀` alone.
* **`m ≥ 2ℓ` is dropped.** The bounds are proved at *every* state `z`, the recursion returning `1`
  below `2ℓ` and `1` lying in `[e^{−c₅H/ℓ}, e^{c₅H/ℓ}]`. That is a weaker hypothesis than the
  paper's, hence a stronger statement; `prodW_two_sided_paper` restates the paper's exact form.
  `decay_block_of_cutBal` likewise runs at `ℓ ≤ m` where the paper writes `2ℓ ≤ m`.
* **The lower bound is proved with the paper's own intermediate constant** `e^{−4H/(γ²ℓ)}`,
  sharper than the stated `e^{−c₅H/ℓ} = e^{−6H/(γ²ℓ)}`; `prodW_level_ge` records the sharper
  form and `prodW_two_sided` then weakens it to the paper's.
* `c₅ = 6/γ²` and `γ = √τ/(2(√τ+1))` are `Sojourn.lean`'s and `Escape.lean`'s, carried verbatim,
  and `c₄ = 16cτ` is `R0Bound.lean`'s. No constant is improved here beyond the one just named.
* Nothing about `N_ℓ` itself is proved here: `prodW` is the expectation, and the fact that the
  product runs over the states strictly before the exit is how the recursion is written, not a
  theorem about a stopping time. The same reading of `descW` is `Descent.lean`'s, and
  `prodW_R0_eq_descOne` is what makes the two readings agree where they must.
* `theo:doubling_decay`(2)'s "`c₁`, `c₂` depend on `c`, `d` and `λ_1,…,λ_{2m₀}` alone" is **not**
  formalized: the Lean statement is the existential, as `Descent.lean`'s already was.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1`, `p = p_*`, `τ = 2^{p_*}` | ✓ carried by `Decay` |
| `ℓ ≥ ℓ₂` | ⚠ weakened to `32cτ ≤ 2ℓ`; `ell2 d ≤ ℓ` implies it (`prodW_two_sided_paper`) |
| the descent chain and `N_ℓ` at level `ℓ` | ✓ carried, as the recursion `prodW` |
| `m ≥ 2ℓ` | ⚠ weakened: dropped (see SCOPE); the paper's form is `prodW_two_sided_paper` |
| `0 ≤ H ≤ γ²ℓ/6` | ✓ carried |
| `|b(y)| ≤ H/y` for every integer `y ≥ ℓ` | ✓ carried |
| `e^{−c₅H/ℓ} ≤ E(∏) ≤ e^{c₅H/ℓ}` | ✓ proved (`prodW_two_sided`) |
| `theo:doubling_decay`: `ℓ ≥ m₀`, `m₀ = max(ℓ₂,⌈6c₄/γ²⌉)` | ✓ carried (`Decay.m0`), and effective |
| `theo:doubling_decay`(1): `2ℓ ≤ m ≤ M₁`, `(λ_j)` positive | ⚠ weakened to `ℓ ≤ m ≤ M₁`; positivity not needed for the block, only for (2) |
| `theo:doubling_decay`(2): `c₁,c₂` depend on `c,d,λ_1..λ_{2m₀}` | ✗ not formalized (see SCOPE) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-! ### Two elementary exponential comparisons

`1 + t ≤ e^t` is `Real.add_one_le_exp`; the lower one is the paper's `1 − x ≥ e^{−2x}` on
`[0,½]`, which it uses to turn the product `∏(1 − y_r)` into a single exponential. -/

/-- **`1 − y ≥ e^{−2y}` on `[0,½]`**, the paper's inequality in the last line of the proof of
`lem:doubling_product`. -/
theorem exp_neg_two_mul_le_one_sub {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    Real.exp (-(2 * y)) ≤ 1 - y := by
  have hpos : (0 : ℝ) < 1 + 2 * y := by linarith
  have h1 : (1 : ℝ) + 2 * y ≤ Real.exp (2 * y) := by
    have := Real.add_one_le_exp (2 * y); linarith
  have hE : (0 : ℝ) < Real.exp (-(2 * y)) := Real.exp_pos _
  have key : Real.exp (-(2 * y)) * (1 + 2 * y) ≤ 1 := by
    calc Real.exp (-(2 * y)) * (1 + 2 * y)
        ≤ Real.exp (-(2 * y)) * Real.exp (2 * y) := mul_le_mul_of_nonneg_left h1 hE.le
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith [key, hpos, hy0, hy1]

namespace Decay

/-- **The weighted product of a descent.**
`prodW ℓ b z = E(∏_{n<N_ℓ}(1 + b(Y_n)) | Y₀ = z)`, as the recursion in the state that
characterises it: the factor at the current state times the average of the same quantity after
one step of the transition law `Decay.pk`, and `1` once the descent has fallen below `2ℓ`.

Well-founded because every `j ∈ W(z)` has `j < z` — `lem:doubling_descent`(1). -/
noncomputable def prodW (D : Decay) (ℓ : ℕ) (b : ℕ → ℝ) (z : ℕ) : ℝ :=
  if z < 2 * ℓ then 1
  else (1 + b z) * ∑ j ∈ (window z).attach, D.pk z j.1 * prodW D ℓ b j.1
termination_by z
decreasing_by exact window_lt j.2

variable (D : Decay)

theorem prodW_of_lt {ℓ : ℕ} (b : ℕ → ℝ) {z : ℕ} (h : z < 2 * ℓ) : D.prodW ℓ b z = 1 := by
  rw [prodW, if_pos h]

theorem prodW_of_ge {ℓ : ℕ} (b : ℕ → ℝ) {z : ℕ} (h : ¬ z < 2 * ℓ) :
    D.prodW ℓ b z = (1 + b z) * ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j := by
  rw [prodW, if_neg h]
  congr 1
  exact Finset.sum_attach (window z) fun j => D.pk z j * D.prodW ℓ b j

/-- Every state `≥ 2ℓ` clears the threshold `32cτ`, at a level `ℓ` with `32cτ ≤ 2ℓ`. -/
theorem thr_of_two_level {ℓ y : ℕ} (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) (hy : 2 * ℓ ≤ y) :
    32 * D.c * D.tau ≤ (y : ℝ) := by
  have : (2 : ℝ) * (ℓ : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  linarith

/-- The product of non-negative factors is non-negative: the paper's "the factors being
positive". -/
theorem prodW_nonneg {ℓ : ℕ} (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) {b : ℕ → ℝ}
    (hb : ∀ y : ℕ, 2 * ℓ ≤ y → 0 ≤ 1 + b y) (z : ℕ) : 0 ≤ D.prodW ℓ b z := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    by_cases h : z < 2 * ℓ
    · rw [D.prodW_of_lt b h]; norm_num
    · rw [D.prodW_of_ge b h]
      have hzthr := D.thr_of_two_level hℓ (by omega : 2 * ℓ ≤ z)
      exact mul_nonneg (hb z (by omega))
        (Finset.sum_nonneg fun j hj => mul_nonneg (D.pk_nonneg hzthr hj) (ih j (window_lt hj)))

/-- `E(ς)` is non-negative, at every state. -/
theorem sojMean_nonneg {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (z : ℕ) :
    0 ≤ D.sojMean L z := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    by_cases hb : L ≤ z ∧ z < 2 * L
    · have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) :=
        le_trans hL (by exact_mod_cast hb.1)
      rw [D.sojMean_of_in hb]
      have : (0 : ℝ) ≤ ∑ j ∈ window z, D.pk z j * D.sojMean L j :=
        Finset.sum_nonneg fun j hj => mul_nonneg (D.pk_nonneg hzthr hj) (ih j (window_lt hj))
      linarith
    · rw [D.sojMean_of_out hb]

/-- `E(ς) ≥ 1` inside the block: one step is always taken there. -/
theorem one_le_sojMean {L z : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hz : L ≤ z ∧ z < 2 * L) :
    1 ≤ D.sojMean L z := by
  have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) := le_trans hL (by exact_mod_cast hz.1)
  rw [D.sojMean_of_in hz]
  have : (0 : ℝ) ≤ ∑ j ∈ window z, D.pk z j * D.sojMean L j :=
    Finset.sum_nonneg fun j hj =>
      mul_nonneg (D.pk_nonneg hzthr hj) (D.sojMean_nonneg hL j)
  linarith

/-! ### The block step — what replaces the strong Markov property at `ς` -/

/-- **The block step, upper half.** If `1 + b ≤ ζ` on `I = [L,2L)` and `Ψ ≤ A` below `L`, then
`Ψ(z) ≤ A · E(ζ^ς | Y₀ = z)` for every `z < 2L`.

This is the paper's `Ψ(z) = E(∏_{n<ς}(1+b(Y_n)) Ψ(Y_ς))` followed by `|b| ≤ ζ − 1` on the block,
with the strong Markov property at `ς` replaced by strong induction on the state. -/
theorem prodW_block_le {ℓ L : ℕ} (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ))
    (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hLℓ : 2 * ℓ ≤ L) {b : ℕ → ℝ}
    (hbnn : ∀ y : ℕ, 2 * ℓ ≤ y → 0 ≤ 1 + b y) {zeta A : ℝ} (hzeta : 0 ≤ zeta)
    (hup : ∀ y : ℕ, L ≤ y → y < 2 * L → 1 + b y ≤ zeta)
    (hbelow : ∀ w : ℕ, w < L → D.prodW ℓ b w ≤ A) :
    ∀ z : ℕ, z < 2 * L → D.prodW ℓ b z ≤ A * D.sojGF L zeta z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hz2
    by_cases hb : L ≤ z ∧ z < 2 * L
    · have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) := le_trans hL (by exact_mod_cast hb.1)
      have hz2ℓ : ¬ z < 2 * ℓ := by omega
      rw [D.prodW_of_ge b hz2ℓ, D.sojGF_of_in hb]
      have hSnn : (0 : ℝ) ≤ ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j :=
        Finset.sum_nonneg fun j hj =>
          mul_nonneg (D.pk_nonneg hzthr hj) (D.prodW_nonneg hℓ hbnn j)
      have hstep : ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j
          ≤ ∑ j ∈ window z, D.pk z j * (A * D.sojGF L zeta j) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjz : j < z := window_lt hj
        exact mul_le_mul_of_nonneg_left (ih j hjz (by omega)) (D.pk_nonneg hzthr hj)
      have hpull : ∑ j ∈ window z, D.pk z j * (A * D.sojGF L zeta j)
          = A * ∑ j ∈ window z, D.pk z j * D.sojGF L zeta j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hpull] at hstep
      have hfac : 1 + b z ≤ zeta := hup z hb.1 hb.2
      have h1 : (1 + b z) * ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j
          ≤ zeta * ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j :=
        mul_le_mul_of_nonneg_right hfac hSnn
      have h2 : zeta * ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j
          ≤ zeta * (A * ∑ j ∈ window z, D.pk z j * D.sojGF L zeta j) :=
        mul_le_mul_of_nonneg_left hstep hzeta
      calc (1 + b z) * ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j
          ≤ zeta * (A * ∑ j ∈ window z, D.pk z j * D.sojGF L zeta j) := le_trans h1 h2
        _ = A * (zeta * ∑ j ∈ window z, D.pk z j * D.sojGF L zeta j) := by ring
    · have hzL : z < L := by omega
      rw [D.sojGF_of_out hb, mul_one]
      exact hbelow z hzL

/-- **The block step, lower half.** If `1 − x ≤ 1 + b` on `I = [L,2L)` and `A ≤ Ψ` below `L`,
then `A · (1 − x·E(ς | Y₀ = z)) ≤ Ψ(z)` for every `z < 2L`.

This is the paper's `(1−x)^ς ≥ 1 − ςx`, in the form the induction can carry: the step produces
`(1−x)·A·(1 − x·E(ς) + x) = A·(1 − x·E(ς)) + A·x²·(E(ς) − 1)`, and `E(ς) ≥ 1` inside the block
is what makes the extra term non-negative. -/
theorem prodW_block_ge {ℓ L : ℕ} (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ))
    (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hLℓ : 2 * ℓ ≤ L) {b : ℕ → ℝ}
    (hbnn : ∀ y : ℕ, 2 * ℓ ≤ y → 0 ≤ 1 + b y) {x A : ℝ} (hx1 : x ≤ 1) (hA : 0 ≤ A)
    (hlow : ∀ y : ℕ, L ≤ y → y < 2 * L → 1 - x ≤ 1 + b y)
    (hbelow : ∀ w : ℕ, w < L → A ≤ D.prodW ℓ b w) :
    ∀ z : ℕ, z < 2 * L → A * (1 - x * D.sojMean L z) ≤ D.prodW ℓ b z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hz2
    by_cases hb : L ≤ z ∧ z < 2 * L
    · have hzthr : 32 * D.c * D.tau ≤ (z : ℝ) := le_trans hL (by exact_mod_cast hb.1)
      have hz2ℓ : ¬ z < 2 * ℓ := by omega
      rw [D.prodW_of_ge b hz2ℓ]
      have hstep : ∑ j ∈ window z, D.pk z j * (A * (1 - x * D.sojMean L j))
          ≤ ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjz : j < z := window_lt hj
        exact mul_le_mul_of_nonneg_left (ih j hjz (by omega)) (D.pk_nonneg hzthr hj)
      have hrec : D.sojMean L z = 1 + ∑ j ∈ window z, D.pk z j * D.sojMean L j :=
        D.sojMean_of_in hb
      have hSm : ∑ j ∈ window z, D.pk z j * D.sojMean L j = D.sojMean L z - 1 := by
        linarith
      have hexpand : ∑ j ∈ window z, D.pk z j * (A * (1 - x * D.sojMean L j))
          = A * (1 - x * (D.sojMean L z - 1)) := by
        have hterm : ∀ j ∈ window z, D.pk z j * (A * (1 - x * D.sojMean L j))
            = A * D.pk z j - (A * x) * (D.pk z j * D.sojMean L j) := fun j _ => by ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, D.sum_pk hzthr, hSm]
        ring
      have hSnn : (0 : ℝ) ≤ ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j :=
        Finset.sum_nonneg fun j hj =>
          mul_nonneg (D.pk_nonneg hzthr hj) (D.prodW_nonneg hℓ hbnn j)
      have hfac : 1 - x ≤ 1 + b z := hlow z hb.1 hb.2
      have hone : 1 ≤ D.sojMean L z := D.one_le_sojMean hL hb
      have hkey : A * (1 - x * D.sojMean L z)
          ≤ (1 - x) * (A * (1 - x * (D.sojMean L z - 1))) := by
        nlinarith [mul_nonneg (mul_nonneg hA (sq_nonneg x)) (sub_nonneg.mpr hone)]
      have hmid : (1 - x) * (A * (1 - x * (D.sojMean L z - 1)))
          ≤ (1 - x) * ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [← hexpand]; exact hstep
      have hfin : (1 - x) * ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j
          ≤ (1 + b z) * ∑ j ∈ window z, D.pk z j * D.prodW ℓ b j :=
        mul_le_mul_of_nonneg_right hfac hSnn
      linarith
    · have hzL : z < L := by omega
      rw [D.sojMean_of_out hb, mul_zero, sub_zero, mul_one]
      exact hbelow z hzL

/-! ### The level invariants — the paper's induction on the dyadic index `i` -/

section Level

variable {ℓ : ℕ} {b : ℕ → ℝ} {H : ℝ}

/-- The level clears `16`: `2ℓ ≥ 32cτ > 32`, because `cτ = p_* + c > 1` (`one_lt_ctau`). -/
theorem sixteen_lt_level (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) : (16 : ℝ) < (ℓ : ℝ) := by
  have h := D.one_lt_ctau
  linarith

theorem gam_sq_lt_quarter : D.gam ^ 2 < 1 / 4 := by
  have h1 := D.gam_pos
  have h2 := D.gam_lt_half
  nlinarith

/-- **Every factor of the product is positive.** `|b| ≤ H/(2ℓ) ≤ γ²/12 < 1` above `2ℓ`, which is
the paper's "every factor lies in `[½,3/2]`" in the only direction the recursion needs. -/
theorem one_add_b_nonneg (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) (hH0 : 0 ≤ H)
    (hH : H ≤ D.gam ^ 2 * (ℓ : ℝ) / 6) (hbb : ∀ y : ℕ, ℓ ≤ y → |b y| ≤ H / (y : ℝ)) :
    ∀ y : ℕ, 2 * ℓ ≤ y → 0 ≤ 1 + b y := by
  intro y hy
  have hℓ16 := D.sixteen_lt_level hℓ
  have hℓpos : (0 : ℝ) < 2 * (ℓ : ℝ) := by linarith
  have hyge : (2 : ℝ) * (ℓ : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have h1 : |b y| ≤ H / (y : ℝ) := hbb y (by omega)
  have h2 : H / (y : ℝ) ≤ H / (2 * (ℓ : ℝ)) := div_le_div_of_nonneg_left hH0 hℓpos hyge
  have h3 : H / (2 * (ℓ : ℝ)) ≤ D.gam ^ 2 / 12 := by
    rw [div_le_div_iff₀ hℓpos (by norm_num : (0 : ℝ) < 12)]
    linarith
  have h4 := D.gam_sq_lt_quarter
  have h5 := (abs_le.mp h1).1
  linarith

/-- Above a block floor `L ≥ ℓ`, the bound `|b(y)| ≤ H/y` reads `|b(y)| ≤ H/L`. -/
theorem abs_b_le_block (hH0 : 0 ≤ H) (hbb : ∀ y : ℕ, ℓ ≤ y → |b y| ≤ H / (y : ℝ))
    {L : ℕ} (hℓL : ℓ ≤ L) (hLpos : (0 : ℝ) < (L : ℝ)) {y : ℕ} (hy : L ≤ y) :
    |b y| ≤ H / (L : ℝ) := by
  have h1 : |b y| ≤ H / (y : ℝ) := hbb y (le_trans hℓL hy)
  have hLy : (L : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  exact le_trans h1 (div_le_div_of_nonneg_left hH0 hLpos hLy)

/-- **One block of the paper's induction, upper half.** `φ_i ≤ φ_{i−1}(1 + c₅H/L)` at
`L = 2^i ℓ`: the block comparison `prodW_block_le` at `ζ = 1 + H/L`, followed by the third line
of `eq:doubling_sojourn`. -/
theorem prodW_step_le (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) (hH0 : 0 ≤ H)
    (hH : H ≤ D.gam ^ 2 * (ℓ : ℝ) / 6) (hbb : ∀ y : ℕ, ℓ ≤ y → |b y| ≤ H / (y : ℝ))
    {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hLℓ : 2 * ℓ ≤ L) {A : ℝ} (hA : 0 ≤ A)
    (hbelow : ∀ w : ℕ, w < L → D.prodW ℓ b w ≤ A) :
    ∀ z : ℕ, z < 2 * L → D.prodW ℓ b z ≤ A * (1 + D.c5 * H / (L : ℝ)) := by
  intro z hz
  have hℓ16 := D.sixteen_lt_level hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hLr : (2 : ℝ) * (ℓ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLℓ
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hbnn := D.one_add_b_nonneg hℓ hH0 hH hbb
  have hHL0 : 0 ≤ H / (L : ℝ) := div_nonneg hH0 hLpos.le
  have hHL6 : H / (L : ℝ) ≤ D.gam ^ 2 / 6 := by
    have h2 : H / (L : ℝ) ≤ H / (2 * (ℓ : ℝ)) :=
      div_le_div_of_nonneg_left hH0 (by linarith) hLr
    have h3 : H / (2 * (ℓ : ℝ)) ≤ D.gam ^ 2 / 12 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 12)]
      linarith
    have hg2 : (0 : ℝ) < D.gam ^ 2 := by have := D.gam_pos; positivity
    linarith
  have hup : ∀ y : ℕ, L ≤ y → y < 2 * L → 1 + b y ≤ 1 + H / (L : ℝ) := by
    intro y hy1 _
    have := abs_le.mp (abs_b_le_block hH0 hbb (by omega) hLpos hy1)
    linarith [this.2]
  have hblk := D.prodW_block_le hℓ hL hLℓ hbnn (by linarith : (0 : ℝ) ≤ 1 + H / (L : ℝ))
    hup hbelow z hz
  have hsoj := D.sojGF_le hL hz (by linarith : (1 : ℝ) ≤ 1 + H / (L : ℝ))
    (by linarith : (1 : ℝ) + H / (L : ℝ) ≤ 1 + D.gam ^ 2 / 6)
  have hrw : 1 + D.c5 * ((1 + H / (L : ℝ)) - 1) = 1 + D.c5 * H / (L : ℝ) := by
    field_simp
    ring
  calc D.prodW ℓ b z ≤ A * D.sojGF L (1 + H / (L : ℝ)) z := hblk
    _ ≤ A * (1 + D.c5 * ((1 + H / (L : ℝ)) - 1)) := mul_le_mul_of_nonneg_left hsoj hA
    _ = A * (1 + D.c5 * H / (L : ℝ)) := by rw [hrw]

/-- **One block of the paper's induction, lower half.** `φ̲_i ≥ φ̲_{i−1}(1 − 2H/(γ²L))` at
`L = 2^i ℓ`: the block comparison `prodW_block_ge` at `x = H/L`, followed by the second line of
`eq:doubling_sojourn`. -/
theorem prodW_step_ge (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) (hH0 : 0 ≤ H)
    (hH : H ≤ D.gam ^ 2 * (ℓ : ℝ) / 6) (hbb : ∀ y : ℕ, ℓ ≤ y → |b y| ≤ H / (y : ℝ))
    {L : ℕ} (hL : 32 * D.c * D.tau ≤ (L : ℝ)) (hLℓ : 2 * ℓ ≤ L) {A : ℝ} (hA : 0 ≤ A)
    (hbelow : ∀ w : ℕ, w < L → A ≤ D.prodW ℓ b w) :
    ∀ z : ℕ, z < 2 * L → A * (1 - 2 * H / (D.gam ^ 2 * (L : ℝ))) ≤ D.prodW ℓ b z := by
  intro z hz
  have hℓ16 := D.sixteen_lt_level hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hLr : (2 : ℝ) * (ℓ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLℓ
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hgp := D.gam_pos
  have hg2 : (0 : ℝ) < D.gam ^ 2 := by positivity
  have hbnn := D.one_add_b_nonneg hℓ hH0 hH hbb
  have hHL0 : 0 ≤ H / (L : ℝ) := div_nonneg hH0 hLpos.le
  have hHL6 : H / (L : ℝ) ≤ D.gam ^ 2 / 6 := by
    have h2 : H / (L : ℝ) ≤ H / (2 * (ℓ : ℝ)) :=
      div_le_div_of_nonneg_left hH0 (by linarith) hLr
    have h3 : H / (2 * (ℓ : ℝ)) ≤ D.gam ^ 2 / 12 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 12)]
      linarith
    linarith
  have hq := D.gam_sq_lt_quarter
  have hlow : ∀ y : ℕ, L ≤ y → y < 2 * L → 1 - H / (L : ℝ) ≤ 1 + b y := by
    intro y hy1 _
    have := abs_le.mp (abs_b_le_block hH0 hbb (by omega) hLpos hy1)
    linarith [this.1]
  have hblk := D.prodW_block_ge hℓ hL hLℓ hbnn (by linarith : H / (L : ℝ) ≤ 1) hA hlow hbelow z hz
  have hsm := D.sojMean_le hL hz
  have hsm0 := D.sojMean_nonneg hL z
  have hprod : H / (L : ℝ) * D.sojMean L z ≤ H / (L : ℝ) * (2 / D.gam ^ 2) :=
    mul_le_mul_of_nonneg_left hsm hHL0
  have heq : H / (L : ℝ) * (2 / D.gam ^ 2) = 2 * H / (D.gam ^ 2 * (L : ℝ)) := by
    field_simp
  rw [heq] at hprod
  have : A * (1 - 2 * H / (D.gam ^ 2 * (L : ℝ))) ≤ A * (1 - H / (L : ℝ) * D.sojMean L z) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  linarith

/-- **The level invariant, upper half.** `Ψ(z) ≤ exp(c₅H/ℓ·(1 − 2^{−i}))` for every
`z < 2^{i+1}ℓ` — the paper's `φ_i ≤ ∏_{r≤i}(1 + c₅H2^{−r}/ℓ)`, with the partial geometric sum
kept, so that the induction on `i` is exact rather than asymptotic. -/
theorem prodW_level_le (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) (hH0 : 0 ≤ H)
    (hH : H ≤ D.gam ^ 2 * (ℓ : ℝ) / 6) (hbb : ∀ y : ℕ, ℓ ≤ y → |b y| ≤ H / (y : ℝ)) :
    ∀ i z : ℕ, z < 2 ^ (i + 1) * ℓ →
      D.prodW ℓ b z ≤ Real.exp (D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ i)) := by
  have hℓ16 := D.sixteen_lt_level hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hgp := D.gam_pos
  have hc5pos : (0 : ℝ) < D.c5 := by rw [c5]; positivity
  have hT0 : 0 ≤ D.c5 * H / (ℓ : ℝ) := div_nonneg (mul_nonneg hc5pos.le hH0) hℓpos.le
  intro i
  induction i with
  | zero =>
    intro z hz
    have hz' : z < 2 * ℓ := by simpa using hz
    rw [D.prodW_of_lt b hz']
    norm_num
  | succ i ih =>
    intro z hz
    have hdouble : 2 * (2 ^ (i + 1) * ℓ) = 2 ^ (i + 1 + 1) * ℓ := by ring
    have hz2 : z < 2 * (2 ^ (i + 1) * ℓ) := by rw [hdouble]; exact hz
    have hpow2 : (2 : ℕ) ≤ 2 ^ (i + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hLℓ : 2 * ℓ ≤ 2 ^ (i + 1) * ℓ := Nat.mul_le_mul_right ℓ hpow2
    have hLcast : ((2 ^ (i + 1) * ℓ : ℕ) : ℝ) = (2 : ℝ) ^ (i + 1) * (ℓ : ℝ) := by push_cast; ring
    have hLr : (2 : ℝ) * (ℓ : ℝ) ≤ ((2 ^ (i + 1) * ℓ : ℕ) : ℝ) := by exact_mod_cast hLℓ
    have hL : 32 * D.c * D.tau ≤ ((2 ^ (i + 1) * ℓ : ℕ) : ℝ) := by linarith
    have hA : (0 : ℝ) ≤ Real.exp (D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ i)) :=
      (Real.exp_pos _).le
    have hstep := D.prodW_step_le hℓ hH0 hH hbb hL hLℓ hA ih z hz2
    have hpi : (0 : ℝ) < (2 : ℝ) ^ (i + 1) := by positivity
    have hval : D.c5 * H / ((2 ^ (i + 1) * ℓ : ℕ) : ℝ)
        = D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1)) := by
      rw [hLcast]; field_simp
    have hexp : (1 : ℝ) + D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1))
        ≤ Real.exp (D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1))) := by
      have := Real.add_one_le_exp (D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1)))
      linarith
    have hmul : Real.exp (D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ i))
          * (1 + D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1)))
        ≤ Real.exp (D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ i))
          * Real.exp (D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1))) :=
      mul_le_mul_of_nonneg_left hexp hA
    have hsum : D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ i)
          + D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1))
        = D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ (i + 1)) := by
      have hpi' : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
      field_simp
      ring
    calc D.prodW ℓ b z
        ≤ Real.exp (D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ i))
            * (1 + D.c5 * H / ((2 ^ (i + 1) * ℓ : ℕ) : ℝ)) := hstep
      _ = Real.exp (D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ i))
            * (1 + D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1))) := by rw [hval]
      _ ≤ Real.exp (D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ i))
            * Real.exp (D.c5 * H / (ℓ : ℝ) * (1 / (2 : ℝ) ^ (i + 1))) := hmul
      _ = Real.exp (D.c5 * H / (ℓ : ℝ) * (1 - 1 / (2 : ℝ) ^ (i + 1))) := by
            rw [← Real.exp_add, hsum]

/-- **The level invariant, lower half.** `Ψ(z) ≥ exp(−4H/(γ²ℓ)·(1 − 2^{−i}))` for every
`z < 2^{i+1}ℓ` — the paper's `φ̲_i ≥ e^{−4H/(γ²ℓ)}`, again with the partial sum kept. -/
theorem prodW_level_ge (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) (hH0 : 0 ≤ H)
    (hH : H ≤ D.gam ^ 2 * (ℓ : ℝ) / 6) (hbb : ∀ y : ℕ, ℓ ≤ y → |b y| ≤ H / (y : ℝ)) :
    ∀ i z : ℕ, z < 2 ^ (i + 1) * ℓ →
      Real.exp (-(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ i)))
        ≤ D.prodW ℓ b z := by
  have hℓ16 := D.sixteen_lt_level hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hgp := D.gam_pos
  have hg2 : (0 : ℝ) < D.gam ^ 2 := by positivity
  have hK0 : 0 ≤ 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) := by
    apply div_nonneg (by linarith) (by positivity)
  have hK23 : 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  intro i
  induction i with
  | zero =>
    intro z hz
    have hz' : z < 2 * ℓ := by simpa using hz
    rw [D.prodW_of_lt b hz']
    norm_num
  | succ i ih =>
    intro z hz
    have hdouble : 2 * (2 ^ (i + 1) * ℓ) = 2 ^ (i + 1 + 1) * ℓ := by ring
    have hz2 : z < 2 * (2 ^ (i + 1) * ℓ) := by rw [hdouble]; exact hz
    have hpow2 : (2 : ℕ) ≤ 2 ^ (i + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hLℓ : 2 * ℓ ≤ 2 ^ (i + 1) * ℓ := Nat.mul_le_mul_right ℓ hpow2
    have hLcast : ((2 ^ (i + 1) * ℓ : ℕ) : ℝ) = (2 : ℝ) ^ (i + 1) * (ℓ : ℝ) := by push_cast; ring
    have hLr : (2 : ℝ) * (ℓ : ℝ) ≤ ((2 ^ (i + 1) * ℓ : ℕ) : ℝ) := by exact_mod_cast hLℓ
    have hL : 32 * D.c * D.tau ≤ ((2 ^ (i + 1) * ℓ : ℕ) : ℝ) := by linarith
    have hA : (0 : ℝ) ≤ Real.exp (-(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ i))) :=
      (Real.exp_pos _).le
    have hstep := D.prodW_step_ge hℓ hH0 hH hbb hL hLℓ hA ih z hz2
    have hpi : (0 : ℝ) < (2 : ℝ) ^ (i + 1) := by positivity
    -- the block's loss, in terms of the level constant `K = 4H/(γ²ℓ)`
    have hval : 2 * H / (D.gam ^ 2 * ((2 ^ (i + 1) * ℓ : ℕ) : ℝ))
        = 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 / (2 : ℝ) ^ (i + 2)) := by
      rw [hLcast]; field_simp; ring
    have hy0 : (0 : ℝ) ≤ 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 / (2 : ℝ) ^ (i + 2)) := by
      have : (0 : ℝ) < (2 : ℝ) ^ (i + 2) := by positivity
      positivity
    have hy1 : 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 / (2 : ℝ) ^ (i + 2)) ≤ 1 / 2 := by
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (i + 2) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (i + 2) := by
              apply pow_le_pow_right₀ (by norm_num) (by omega)
      have hinv : 1 / (2 : ℝ) ^ (i + 2) ≤ 1 / 4 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
      nlinarith
    have hexp := exp_neg_two_mul_le_one_sub hy0 hy1
    have hmul : Real.exp (-(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ i)))
          * Real.exp (-(2 * (4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 / (2 : ℝ) ^ (i + 2)))))
        ≤ Real.exp (-(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ i)))
          * (1 - 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 / (2 : ℝ) ^ (i + 2))) :=
      mul_le_mul_of_nonneg_left hexp hA
    have hsum : -(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ i))
          + -(2 * (4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 / (2 : ℝ) ^ (i + 2))))
        = -(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ (i + 1))) := by
      have hpi' : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
      field_simp
      ring
    calc Real.exp (-(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ (i + 1))))
        = Real.exp (-(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ i)))
            * Real.exp (-(2 * (4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 / (2 : ℝ) ^ (i + 2))))) := by
          rw [← Real.exp_add, hsum]
      _ ≤ Real.exp (-(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ i)))
            * (1 - 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 / (2 : ℝ) ^ (i + 2))) := hmul
      _ = Real.exp (-(4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ i)))
            * (1 - 2 * H / (D.gam ^ 2 * ((2 ^ (i + 1) * ℓ : ℕ) : ℝ))) := by rw [hval]
      _ ≤ D.prodW ℓ b z := hstep

/-! ### `eq:doubling_product` -/

/-- **`eq:doubling_product`.** `e^{−c₅H/ℓ} ≤ E(∏_{n<N_ℓ}(1+b(Y_n)) | Y₀ = z) ≤ e^{c₅H/ℓ}`.

Stated at every starting state `z`, the paper's `m ≥ 2ℓ` being unnecessary: below `2ℓ` the
product is empty and `1` lies in the interval. -/
theorem prodW_two_sided (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) (hH0 : 0 ≤ H)
    (hH : H ≤ D.gam ^ 2 * (ℓ : ℝ) / 6) (hbb : ∀ y : ℕ, ℓ ≤ y → |b y| ≤ H / (y : ℝ)) (z : ℕ) :
    Real.exp (-(D.c5 * H / (ℓ : ℝ))) ≤ D.prodW ℓ b z ∧
      D.prodW ℓ b z ≤ Real.exp (D.c5 * H / (ℓ : ℝ)) := by
  have hℓ16 := D.sixteen_lt_level hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hℓ1 : 1 ≤ ℓ := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (ℓ : ℝ))
  have hgp := D.gam_pos
  have hg2 : (0 : ℝ) < D.gam ^ 2 := by positivity
  have hc5pos : (0 : ℝ) < D.c5 := by rw [c5]; positivity
  have hT0 : 0 ≤ D.c5 * H / (ℓ : ℝ) := div_nonneg (mul_nonneg hc5pos.le hH0) hℓpos.le
  have hK0 : 0 ≤ 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) := div_nonneg (by linarith) (by positivity)
  have hpz : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
  have hfrac : 0 ≤ 1 / (2 : ℝ) ^ z := by positivity
  have hfrac1 : 1 / (2 : ℝ) ^ z ≤ 1 := by
    rw [div_le_one hpz]
    calc (1 : ℝ) = 2 ^ 0 := by norm_num
      _ ≤ 2 ^ z := by apply pow_le_pow_right₀ (by norm_num) (by omega)
  -- the starting state lies in `I_i(ℓ)` for `i = z`, since `z < 2^z ≤ 2^{z+1}ℓ`
  have hzlt : z < 2 ^ (z + 1) * ℓ := by
    have h1 : z < 2 ^ z := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ z ≤ 2 ^ (z + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (z + 1) * 1 ≤ 2 ^ (z + 1) * ℓ := Nat.mul_le_mul_left _ hℓ1
    rw [mul_one] at h3
    exact lt_of_lt_of_le h1 (le_trans h2 h3)
  have hKT : 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) ≤ D.c5 * H / (ℓ : ℝ) := by
    have hden : (0 : ℝ) < D.gam ^ 2 * (ℓ : ℝ) := by positivity
    have hc5eq : D.c5 * H / (ℓ : ℝ) = 6 * H / (D.gam ^ 2 * (ℓ : ℝ)) := by
      rw [c5]; field_simp
    rw [hc5eq, div_le_div_iff₀ hden hden]
    nlinarith [mul_nonneg hH0 hden.le]
  constructor
  · have hlow := D.prodW_level_ge hℓ hH0 hH hbb z z hzlt
    refine le_trans (Real.exp_le_exp.mpr ?_) hlow
    have : 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) * (1 - 1 / (2 : ℝ) ^ z)
        ≤ 4 * H / (D.gam ^ 2 * (ℓ : ℝ)) := by nlinarith
    linarith
  · have hupp := D.prodW_level_le hℓ hH0 hH hbb z z hzlt
    refine le_trans hupp (Real.exp_le_exp.mpr ?_)
    nlinarith

/-- **`eq:doubling_product`, in the paper's own form**: at a level `ℓ ≥ ℓ₂` and a starting state
`m ≥ 2ℓ`. -/
theorem prodW_two_sided_paper {d : ℕ} (hℓ : D.ell2 d ≤ ℓ) (hH0 : 0 ≤ H)
    (hH : H ≤ D.gam ^ 2 * (ℓ : ℝ) / 6) (hbb : ∀ y : ℕ, ℓ ≤ y → |b y| ≤ H / (y : ℝ))
    {m : ℕ} (_hm : 2 * ℓ ≤ m) :
    Real.exp (-(D.c5 * H / (ℓ : ℝ))) ≤ D.prodW ℓ b m ∧
      D.prodW ℓ b m ≤ Real.exp (D.c5 * H / (ℓ : ℝ)) := by
  have hthr : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ) := by
    have h := D.thr_of_level hℓ (le_refl (2 * ℓ))
    push_cast at h
    linarith
  exact D.prodW_two_sided hthr hH0 hH hbb m

end Level

/-! ### `theo:doubling_decay`, unconditional

`eq:doubling_product` at `b := R₀ − 1` and `H := c₄ = 16cτ` is exactly the pair of hypotheses
`hlo`/`hhi` that `Descent.lean` carries. Discharging them makes `theo:doubling_decay`(2)
unconditional. -/

/-- The two recursions coincide at `b := R₀ − 1`: `(1 + (R₀(z) − 1))·(w_z(j)/R₀(z)) = w_z(j)`,
so `prodW ℓ (R₀ − 1) = descOne ℓ`. -/
theorem prodW_R0_eq_descOne {ℓ : ℕ} (hℓ : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ)) {bb : ℕ → ℝ}
    (hbb : ∀ y : ℕ, bb y = D.R0 y - 1) (z : ℕ) : D.prodW ℓ bb z = D.descOne ℓ z := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    by_cases h : z < 2 * ℓ
    · rw [D.prodW_of_lt bb h, D.descOne_of_lt h]
    · have hzthr := D.thr_of_two_level hℓ (by omega : 2 * ℓ ≤ z)
      have hR0 : (1 : ℝ) / 2 ≤ D.R0 z := D.half_le_R0 hzthr
      have hR0ne : D.R0 z ≠ 0 := by intro hc; rw [hc] at hR0; norm_num at hR0
      rw [D.prodW_of_ge bb h, D.descOne_of_ge h, hbb z, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ih j (window_lt hj), pk]
      field_simp
      ring

/-- **`m₀` of `theo:doubling_decay`**, `max(ℓ₂, ⌈6c₄/γ²⌉)`: the level at which
`eq:doubling_product` may be run at `b := R₀ − 1` and `H := c₄`, i.e. at which `c₄ ≤ γ²ℓ/6`.
With `R0Bound.lean`'s effective `c₄ = 16cτ` and `Escape.lean`'s effective `ℓ₂` it is explicit:
`m₀ = max(ℓ₂, ⌈96cτ/γ²⌉)`. -/
noncomputable def m0 (D : Decay) (d : ℕ) : ℕ :=
  max (D.ell2 d) ⌈96 * D.c * D.tau / D.gam ^ 2⌉₊

theorem ell2_le_m0 (d : ℕ) : D.ell2 d ≤ D.m0 d := le_max_left _ _

theorem lt_m0 (d : ℕ) : d < D.m0 d := lt_of_lt_of_le (D.lt_ell2 d) (D.ell2_le_m0 d)

/-- **`eq:doubling_product` at `b := R₀ − 1`, `H := c₄`.** The expected weight of a descent is
`1 + O(1/ℓ)`, two-sidedly: `e^{−c₅c₄/ℓ} ≤ E(Z_ℓ | Y₀ = y) ≤ e^{c₅c₄/ℓ}` with `c₄ = 16cτ`.

This is the hypothesis `hlo`/`hhi` of `Decay.decay_block`, discharged. -/
theorem descOne_two_sided {d ℓ : ℕ} (hℓ : D.m0 d ≤ ℓ) (y : ℕ) :
    Real.exp (-(D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ))) ≤ D.descOne ℓ y ∧
      D.descOne ℓ y ≤ Real.exp (D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)) := by
  have hℓ2 : D.ell2 d ≤ ℓ := le_trans (D.ell2_le_m0 d) hℓ
  have hthr : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ) := by
    have h := D.thr_of_level hℓ2 (le_refl (2 * ℓ))
    push_cast at h
    linarith
  have hℓ16 := D.sixteen_lt_level hthr
  have hgp := D.gam_pos
  have hg2 : (0 : ℝ) < D.gam ^ 2 := by positivity
  have hct := D.ctau_pos
  have hH0 : (0 : ℝ) ≤ 16 * D.c * D.tau := by nlinarith
  have hceil : (96 * D.c * D.tau / D.gam ^ 2 : ℝ) ≤ (ℓ : ℝ) := by
    have h1 : (96 * D.c * D.tau / D.gam ^ 2 : ℝ) ≤ (⌈96 * D.c * D.tau / D.gam ^ 2⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : (⌈96 * D.c * D.tau / D.gam ^ 2⌉₊ : ℝ) ≤ (ℓ : ℝ) := by
      exact_mod_cast le_trans (le_max_right (D.ell2 d) _) hℓ
    linarith
  have hH : (16 * D.c * D.tau : ℝ) ≤ D.gam ^ 2 * (ℓ : ℝ) / 6 := by
    rw [div_le_iff₀ hg2] at hceil
    nlinarith
  have hℓ1 : 1 ≤ ℓ := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (ℓ : ℝ))
  have hbb : ∀ w : ℕ, ℓ ≤ w → |D.R0 w - 1| ≤ (16 * D.c * D.tau) / (w : ℝ) := by
    intro w hw
    exact D.R0_sub_one_le (by omega : 1 ≤ w)
  have hmain := D.prodW_two_sided hthr hH0 hH hbb y
  rw [D.prodW_R0_eq_descOne hthr (fun _ => rfl) y] at hmain
  exact hmain

/-- **`eq:doubling_block`, unconditional.** One block of the rescaled profile bounds every index
above it, within `e^{±c₅c₄/ℓ}` — `theo:doubling_decay`(1), with `min`/`max` over `[ℓ,2ℓ)`
replaced by any pair bracketing the profile there, which is what `Decay.decay_block` takes and
what its two uses supply.

Stated at every `m ≥ ℓ`, the paper's `m ≥ 2ℓ` being unnecessary. -/
theorem decay_block_of_cutBal {d ℓ : ℕ} {lam : ℕ → ℝ} {M₁ : ℕ∞} (h : D.CutBal d lam M₁)
    (hℓ : D.m0 d ≤ ℓ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : ∀ j, ℓ ≤ j → j < 2 * ℓ → a ≤ D.uu lam j ∧ D.uu lam j ≤ b)
    {m : ℕ} (hm : ℓ ≤ m) (hM : (m : ℕ∞) ≤ M₁) :
    a * Real.exp (-(D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ))) ≤ D.uu lam m ∧
      D.uu lam m ≤ b * Real.exp (D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)) := by
  have hd : d < ℓ := lt_of_lt_of_le (D.lt_m0 d) hℓ
  have hℓ2 : D.ell2 d ≤ ℓ := le_trans (D.ell2_le_m0 d) hℓ
  have hthr : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ) := by
    have h' := D.thr_of_level hℓ2 (le_refl (2 * ℓ))
    push_cast at h'
    linarith
  have hℓ16 := D.sixteen_lt_level hthr
  exact D.decay_block h (by omega) (by omega) (fun y _ => (D.descOne_two_sided hℓ y).1)
    (fun y _ => (D.descOne_two_sided hℓ y).2) ha hab hm hM

/-- **`theo:doubling_decay`(2), unconditional.** Every positive sequence satisfying the cut
balance above `d` obeys `c₁ j^{−p_*} ≤ λ_j ≤ c₂ j^{−p_*}` for every `j ≥ 1`, with no hypothesis
left beyond the cut balance and positivity: `eq:doubling_product` has discharged `hlo`/`hhi`. -/
theorem decay_two_sided_of_cutBal {d ℓ : ℕ} {lam : ℕ → ℝ} (h : D.CutBal d lam ⊤)
    (hpos : ∀ j, 1 ≤ j → 0 < lam j) (hℓ : D.m0 d ≤ ℓ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ j : ℕ, 1 ≤ j →
        c₁ * (j : ℝ) ^ (-D.p) ≤ lam j ∧ lam j ≤ c₂ * (j : ℝ) ^ (-D.p) := by
  have hd : d < ℓ := lt_of_lt_of_le (D.lt_m0 d) hℓ
  have hℓ2 : D.ell2 d ≤ ℓ := le_trans (D.ell2_le_m0 d) hℓ
  have hthr : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ) := by
    have h' := D.thr_of_level hℓ2 (le_refl (2 * ℓ))
    push_cast at h'
    linarith
  have hℓ16 := D.sixteen_lt_level hthr
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hgp := D.gam_pos
  have hc5pos : (0 : ℝ) < D.c5 := by rw [c5]; positivity
  have hct := D.ctau_pos
  have hH0 : (0 : ℝ) ≤ 16 * D.c * D.tau := by nlinarith
  have hT0 : 0 ≤ D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ) :=
    div_nonneg (mul_nonneg hc5pos.le hH0) hℓpos.le
  refine D.decay_two_sided h hpos (by omega) (by omega) (Real.exp_pos _) ?_ ?_
    (fun y _ => (D.descOne_two_sided hℓ y).1) (fun y _ => (D.descOne_two_sided hℓ y).2)
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hT0

/-- **`eq:doubling_decay` in the `u` variable, with the constants written out.** If the rescaled
profile lies in `[a, b]` on the initial block `1 ≤ j < 2ℓ`, `ℓ ≥ m₀`, then on the whole ladder it
lies in `[a e^{−c₅c₄/ℓ}, b e^{c₅c₄/ℓ}]`, `c₄ = 16cτ`. This is the dependence clause of
`theo:doubling_decay`(2) made precise: the constants are functions of `c`, `d` (through `m₀`) and
`λ_1, …, λ_{2ℓ−1}` (through `a`, `b`) alone. -/
theorem uu_bounded_explicit {d ℓ : ℕ} {lam : ℕ → ℝ} (h : D.CutBal d lam ⊤) (hℓ : D.m0 d ≤ ℓ)
    {a b : ℝ} (ha : 0 ≤ a)
    (hab : ∀ j, 1 ≤ j → j < 2 * ℓ → a ≤ D.uu lam j ∧ D.uu lam j ≤ b) :
    ∀ j : ℕ, 1 ≤ j →
      a * Real.exp (-(D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ))) ≤ D.uu lam j ∧
        D.uu lam j ≤ b * Real.exp (D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)) := by
  intro j hj
  have hd : d < ℓ := lt_of_lt_of_le (D.lt_m0 d) hℓ
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hgp := D.gam_pos
  have hc5pos : (0 : ℝ) < D.c5 := by rw [c5]; positivity
  have hct := D.ctau_pos
  have hH0 : (0 : ℝ) ≤ 16 * D.c * D.tau := by nlinarith
  have hT0 : 0 ≤ D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ) :=
    div_nonneg (mul_nonneg hc5pos.le hH0) hℓpos.le
  have hZ1 : Real.exp (-(D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ))) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hZ2 : 1 ≤ Real.exp (D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hT0
  have hb : 0 ≤ b :=
    le_trans ha ((hab 1 le_rfl (by omega)).1.trans (hab 1 le_rfl (by omega)).2)
  by_cases hjs : j < 2 * ℓ
  · obtain ⟨h1, h2⟩ := hab j hj hjs
    exact ⟨le_trans (mul_le_of_le_one_right ha hZ1) h1,
      le_trans h2 (le_mul_of_one_le_right hb hZ2)⟩
  · exact D.decay_block_of_cutBal h hℓ ha (fun j h1 h2 => hab j (le_trans hℓ1 h1) h2)
      (by omega : ℓ ≤ j) le_top

/-- **`eq:doubling_decay` with the constants written out** — `theo:doubling_decay`(2) and its
dependence clause. With `a ≤ λ_j j^{p_*} ≤ b` on `1 ≤ j < 2ℓ`, `ℓ ≥ m₀`, `0 ≤ a`:
`a e^{−c₅c₄/ℓ} j^{−p_*} ≤ λ_j ≤ b e^{c₅c₄/ℓ} j^{−p_*}` for every `j ≥ 1`, `c₄ = 16cτ`. The
existential form is `decay_two_sided_of_cutBal`; this is its witness. -/
theorem decay_two_sided_explicit {d ℓ : ℕ} {lam : ℕ → ℝ} (h : D.CutBal d lam ⊤)
    (hℓ : D.m0 d ≤ ℓ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : ∀ j, 1 ≤ j → j < 2 * ℓ → a ≤ D.uu lam j ∧ D.uu lam j ≤ b) :
    ∀ j : ℕ, 1 ≤ j →
      a * Real.exp (-(D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ))) * (j : ℝ) ^ (-D.p) ≤ lam j ∧
        lam j ≤ b * Real.exp (D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)) * (j : ℝ) ^ (-D.p) := by
  intro j hj
  obtain ⟨h1, h2⟩ := D.uu_bounded_explicit h hℓ ha hab j hj
  have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hjp : (0 : ℝ) < (j : ℝ) ^ D.p := Real.rpow_pos_of_pos hj' D.p
  have hneg : (j : ℝ) ^ (-D.p) = ((j : ℝ) ^ D.p)⁻¹ := by
    rw [Real.rpow_neg hj'.le]
  rw [uu] at h1 h2
  rw [hneg]
  constructor
  · rw [mul_inv_le_iff₀ hjp]; linarith
  · rw [le_mul_inv_iff₀ hjp]; linarith

end Decay

end GFNBounds.Doubling
