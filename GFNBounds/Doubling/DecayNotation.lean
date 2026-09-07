import GFNBounds.Doubling.Cramer
import GFNBounds.Doubling.CutBalance
import GFNBounds.Doubling.Range

/-!
# Notation for the decay estimates, and the averaging form of the cut balance

**`def:doubling_decay_notation`** — `app_doubling.tex:789–812`
and **`lem:doubling_averaging`** — `app_doubling.tex:814–846`.

> (notation) let `s = 1` and `0 < c < 1`, and with `p_*` the root of `lem:doubling_cramer_root`
> write `p := p_*` and `τ := 2^p`. For `m > d` the window, the parity and the cut weights at `m`
> are `W(m) = {⌈m/2⌉,…,m−1}`, `δ(m) = m − 2⌊m/2⌋`, `q_m(j) = c/((j+1)(1−ε(m)))`. For `α ∈ ℝ` put
> `Φ_α(j) = j^{−p−1}(j+α)` and `R_α(m) = Φ_α(m)^{-1} Σ_{j∈W(m)} q_m(j) Φ_α(j)`, and
> `w_m(j) = q_m(j)(m/j)^p`. The rescaled profile is `u_m := λ_m m^p`, and `I_i(ℓ) = [2^i ℓ, 2^{i+1}ℓ)`.
>
> (averaging) `q_m > 0` on `W(m)`, and (1) a sequence satisfying `eq:doubling_cut` at `m` satisfies
> `λ_m = Σ_{j∈W(m)} q_m(j) λ_j`; (2) a sequence satisfying that satisfies `u_m = Σ w_m(j) u_j` and
> `Σ_{j∈W(m)} w_m(j) = R_0(m)`.

## SCOPE (disclosed)

`Decay` bundles `c` and a non-zero root `p` of the Cramér equation; `lem:doubling_cramer_root`
supplies `1 < p` (`Decay.p_gt_one`) and `τ > 2`. The exponent `s = 1` is not a parameter: it is
the shape `ε(j) = c/(j+1)` of `Decay.eps`, and `Decay.cutBal_of_setting` is the bridge from a
`Setting` whose `eps` has that shape.

`Decay.CutBal` is `CutBalanceSeq` with `Setting` replaced by the pair `(d, D)`, so that the decay
block does not carry a target row it never uses. The two agree under `heps` — that is the bridge
lemma, and it is what lets `cor:doubling_truncation` feed `λ^K` in later.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1` | ✓ carried, as the shape of `Decay.eps` |
| `0 < c < 1` | ✓ carried (`Decay.c_pos`, `Decay.c_lt_one`) |
| `p = p_*` the Cramér root | ✓ carried (`Decay.root`, `Decay.p_ne`) |
| `m > d` in the averaging | ✓ carried; `1 ≤ m` is what the proof needs and is implied |
| `(λ_j)` positive | ⚠ weakened: the identities of `lem:doubling_averaging` are linear and need no sign |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-- The decay parameters: `c` in the standing range at `s = 1`, and a non-zero root `p` of the
Cramér equation `c(2^p − 1) = p`. -/
structure Decay where
  c : ℝ
  p : ℝ
  c_pos : 0 < c
  c_lt_one : c < 1
  p_ne : p ≠ 0
  root : psi c p = 0

namespace Decay

variable (D : Decay)

/-- `p_* > 1` at `0 < c < 1` (`lem:doubling_cramer_root`(1)). -/
theorem p_gt_one : 1 < D.p := cramer_root_gt_one D.c_pos D.c_lt_one D.p_ne D.root

theorem p_pos : 0 < D.p := lt_trans one_pos D.p_gt_one

/-- `τ := 2^{p_*}`. -/
noncomputable def tau : ℝ := (2 : ℝ) ^ D.p

theorem tau_gt_two : 2 < D.tau := (cramer_ineq D.c_pos D.c_lt_one D.p_ne D.root).1

theorem tau_pos : 0 < D.tau := two_rpow_pos D.p

/-- **`eq:doubling_cramer_form`.** `c(τ−1)/p = 1`. -/
theorem cramer : D.c * ((D.tau - 1) / D.p) = 1 := cramer_form D.p_ne D.root

/-- `ε(j) = c/(j+1)`, the family at `s = 1`. -/
noncomputable def eps (j : ℕ) : ℝ := D.c / ((j : ℝ) + 1)

theorem eps_eq (j : ℕ) : D.eps j = D.c / ((j : ℝ) + 1) := rfl

theorem eps_pos (j : ℕ) : 0 < D.eps j := div_pos D.c_pos (base_pos j)

theorem eps_le_half {j : ℕ} (hj : 1 ≤ j) : D.eps j ≤ D.c / 2 := by
  have hb : (2 : ℝ) ≤ (j : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  rw [D.eps_eq]
  exact div_le_div_of_nonneg_left D.c_pos.le (by norm_num) hb

theorem one_sub_eps_pos {j : ℕ} (hj : 1 ≤ j) : 0 < 1 - D.eps j := by
  have h1 := D.eps_le_half hj
  have h2 := D.c_lt_one
  linarith

/-- `q_m(j) = c/((j+1)(1−ε(m)))`, the cut weights of `eq:doubling_window`. -/
noncomputable def qm (m j : ℕ) : ℝ := D.c / (((j : ℝ) + 1) * (1 - D.eps m))

theorem qm_eq (m j : ℕ) : D.qm m j = D.c / (((j : ℝ) + 1) * (1 - D.eps m)) := rfl

theorem qm_pos {m : ℕ} (hm : 1 ≤ m) (j : ℕ) : 0 < D.qm m j :=
  div_pos D.c_pos (mul_pos (base_pos j) (D.one_sub_eps_pos hm))

/-- `w_m(j) = q_m(j)(m/j)^p`, the rescaled cut weights. -/
noncomputable def wm (m j : ℕ) : ℝ := D.qm m j * ((m : ℝ) / (j : ℝ)) ^ D.p

theorem wm_pos {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j) : 0 < D.wm m j := by
  refine mul_pos (D.qm_pos hm j) (rpow_pos_of_pos ?_ D.p)
  have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  positivity

theorem wm_nonneg {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j) : 0 ≤ D.wm m j := (D.wm_pos hm hj).le

/-- `R_0(m) = Σ_{j ∈ W(m)} w_m(j)`, the total weight of the window — `eq:doubling_R` at `α = 0`. -/
noncomputable def R0 (m : ℕ) : ℝ := ∑ j ∈ window m, D.wm m j

/-- The rescaled profile `u_m := λ_m m^p` of `def:doubling_decay_notation`. -/
noncomputable def uu (lam : ℕ → ℝ) (m : ℕ) : ℝ := lam m * (m : ℝ) ^ D.p

/-- `Φ_α(j) = j^{−p−1}(j+α)`. -/
noncomputable def Phi (α : ℝ) (j : ℕ) : ℝ := (j : ℝ) ^ (-D.p - 1) * ((j : ℝ) + α)

/-- `R_α(m)` of `eq:doubling_R`. -/
noncomputable def Ralpha (α : ℝ) (m : ℕ) : ℝ :=
  (∑ j ∈ window m, D.qm m j * D.Phi α j) / D.Phi α m

/-- The parity `δ(m) = m − 2⌊m/2⌋`. -/
def delta (m : ℕ) : ℕ := m - 2 * (m / 2)

theorem delta_lt_two (m : ℕ) : delta m < 2 := by
  rw [delta]; omega

/-- The dyadic block `I_i(ℓ) = [2^i ℓ, 2^{i+1} ℓ)`. -/
def block (i ℓ : ℕ) : Finset ℕ := Finset.Ico (2 ^ i * ℓ) (2 ^ (i + 1) * ℓ)

theorem mem_block {i ℓ n : ℕ} : n ∈ block i ℓ ↔ 2 ^ i * ℓ ≤ n ∧ n < 2 ^ (i + 1) * ℓ :=
  Finset.mem_Ico

/-- `eq:doubling_cut` as a predicate on a bare sequence, with `ε` the family at `s = 1`. -/
def CutBal (d : ℕ) (lam : ℕ → ℝ) (M₁ : ℕ∞) : Prop :=
  ∀ m : ℕ, d < m → (m : ℕ∞) ≤ M₁ →
    lam m * (1 - D.eps m) = ∑ j ∈ window m, lam j * D.eps j

/-- The bridge: a `Setting` whose `ε` is the family at `s = 1` gives `Decay.CutBal`. -/
theorem cutBal_of_setting {S : Setting} {lam : ℕ → ℝ} {M₁ : ℕ∞}
    (heps : ∀ j, S.eps j = D.eps j) (h : CutBalanceSeq S lam M₁) : D.CutBal S.d lam M₁ := by
  intro m hm hM
  have := h m hm hM
  rw [heps m] at this
  rw [this]
  exact Finset.sum_congr rfl fun j _ => by rw [heps j]

/-! ## `lem:doubling_averaging` -/

/-- Every index of `W(m)` is a positive integer, `m` being positive. -/
theorem one_le_of_mem_window' {m j : ℕ} (hm : 1 ≤ m) (hj : j ∈ window m) : 1 ≤ j := by
  rcases Nat.eq_zero_or_pos j with rfl | h
  · rw [mem_window] at hj; omega
  · exact h

/-- **`eq:doubling_avg`.** Dividing `eq:doubling_cut` by `1 − ε(m)` turns the balance across the
cut into an *average* of the sequence over the window below it. -/
theorem avg_of_cutBal {d : ℕ} {lam : ℕ → ℝ} {M₁ : ℕ∞} (h : D.CutBal d lam M₁)
    {m : ℕ} (hm : 1 ≤ m) (hdm : d < m) (hM : (m : ℕ∞) ≤ M₁) :
    lam m = ∑ j ∈ window m, D.qm m j * lam j := by
  have hpos := D.one_sub_eps_pos hm
  have hbal := h m hdm hM
  have hterm : ∀ j ∈ window m, D.qm m j * lam j = lam j * D.eps j / (1 - D.eps m) := by
    intro j hj
    have hb : ((j : ℝ) + 1) ≠ 0 := (base_pos j).ne'
    have hden : (1 - D.eps m) ≠ 0 := hpos.ne'
    rw [D.qm_eq, D.eps_eq j]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← hbal]
  field_simp

/-- **`eq:doubling_uavg`, first line.** The same average, on the rescaled profile. -/
theorem uavg_of_avg {lam : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (h : lam m = ∑ j ∈ window m, D.qm m j * lam j) :
    D.uu lam m = ∑ j ∈ window m, D.wm m j * D.uu lam j := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hterm : ∀ j ∈ window m, D.wm m j * D.uu lam j = D.qm m j * lam j * (m : ℝ) ^ D.p := by
    intro j hj
    have hj1 : 1 ≤ j := one_le_of_mem_window' hm hj
    have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    rw [wm, uu, Real.div_rpow hm'.le hj'.le]
    field_simp
  rw [uu, h, Finset.sum_congr rfl hterm, ← Finset.sum_mul]

/-- **`eq:doubling_uavg`, second line.** The total weight of the window is `R_0(m)`, by definition
of `R_0` — recorded so that the descent recursion may cite it. -/
theorem sum_wm (m : ℕ) : ∑ j ∈ window m, D.wm m j = D.R0 m := rfl

/-- **`lem:doubling_averaging`, both items at once.** -/
theorem uavg_of_cutBal {d : ℕ} {lam : ℕ → ℝ} {M₁ : ℕ∞} (h : D.CutBal d lam M₁)
    {m : ℕ} (hm : 1 ≤ m) (hdm : d < m) (hM : (m : ℕ∞) ≤ M₁) :
    D.uu lam m = ∑ j ∈ window m, D.wm m j * D.uu lam j :=
  D.uavg_of_avg hm (D.avg_of_cutBal h hm hdm hM)

end Decay

end GFNBounds.Doubling
