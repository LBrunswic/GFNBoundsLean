import GFNBounds.Doubling.Descent
import GFNBounds.Doubling.R0Bound

/-!
# The exit law of a descent, as a recursion, and its strong Markov property

Support for **`lem:doubling_doeblin`** — `app_doubling.tex:1385–1473` — and
**`lem:doubling_coupling`** — `app_doubling.tex:1475–1533`.

> (descent) `(Y_n)` is the Markov chain on the integers `≥ ℓ` with
> `P(Y_{n+1}=j | Y_n=y) = w_y(j)/R_0(y)` on `W(y)` when `y ≥ 2ℓ` and `Y_{n+1}=Y_n` when `y < 2ℓ`,
> and `N_ℓ := inf{n : Y_n < 2ℓ}`.
>
> (coupling, third bullet) At `i ≥ 1`, `π_y = ∑_{z ∈ I_{i−1}(ℓ)} μ_y(z) π_z`. The exit time `ς`
> is a stopping time with `ς ≤ N_ℓ` … the descent chain at the level `ℓ` is time-homogeneous, so
> the strong Markov property at `ς` gives the identity.

## The modelling decision

`Descent.lean` models `E(Z_ℓ · g(Y_{N_ℓ}) | Y_0 = m)` — an expectation against the *unnormalised*
weights — by the recursion `descW`, which is what the decay block needs. The Doeblin block needs
the honest **law** instead, so this file carries the *normalised* recursion

  `descP ℓ g m = if m < 2ℓ then g m else ∑_{j ∈ W(m)} k_m(j) · descP ℓ g j`,   `k_m(j) := w_m(j)/R₀(m)`,

which is `E(g(Y_{N_ℓ}) | Y_0 = m)`, and the exit law `exitLaw ℓ y j := descP ℓ 1_{·=j} y`, which is
`P(Y_{N_ℓ} = j | Y_0 = y)`. Three facts come out, none of them needing a chain:

* `descP_eq_sum` — `descP ℓ g y = ∑_{z ∈ [ℓ,2ℓ)} exitLaw ℓ y z · g z`, i.e. the exit law is a law
  on the base block. It is the paper's `lem:doubling_descent`(2) plus normalisation, by strong
  induction on `y`.
* `descP_comp` — **the strong Markov property**, `descP ℓ g = descP a (descP ℓ g)` for `ℓ ≤ a`.
  In this representation it is a two-line strong induction: below `2a` the two sides agree by
  definition, and above it both expand by the *same* one-step kernel. No stopping time is
  constructed, and no measurability is discussed.
* `exitLaw_mix` — the paper's `π_y = ∑_{z ∈ I_{i−1}(ℓ)} μ_y(z) π_z`, the two combined. This is
  what `TotalVariation.tvOn_mix_le` consumes in `Coupling.lean`.

`kern_ge` is the second bullet of the proof of `lem:doubling_doeblin` — one step from a state
`z ≥ 2ℓ` gives every `j ∈ W(z)` mass at least `c/(2(j+1))` — and is the only place `R₀ ≤ 2` is
used. That bound is `R0Bound.R0_between`, effective at `32cτ ≤ z`.

## SCOPE (disclosed)

* Nothing here says that `descP ℓ g m` is an expectation for an actual stochastic process; the
  recursion *is* the definition, exactly as in `Descent.lean`. What is proved is that it is an
  average: non-negative, normalised, carried by `[ℓ,2ℓ)`.
* `descP` is *not* related here to `descW`: the two differ by the weight `Z_ℓ`. The bound on
  their difference — `lem:doubling_weight` in the transform form `Sharp.lean` consumes — is
  `Decay.weight_bound` in `Weight.lean`, with effective constants.
* The recursion is total: at `m < 2ℓ` it returns `g m` whatever `m` is, so statements are
  restricted to `ℓ ≤ m` where the paper's chain lives.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ℓ ≥ ℓ₁ > d` | ✓ carried as `1 ≤ ℓ`, which is all the recursion uses |
| `R₀(y) > 0`, so that the transition law is a probability | ✓ carried, and **proved** (`R0_pos`) at `2 ≤ y` |
| `R₀(z) ≤ 2` in the one-step bound | ✓ carried as `32cτ ≤ z`, via `R0Bound.R0_between` |
| `ς` a stopping time, `ς ≤ N_ℓ`, time-homogeneity | ⚠ **replaced**: `descP_comp` needs only `ℓ ≤ a`, and the recursion is homogeneous by construction |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

variable (D : Decay)

/-! ## The one-step law -/

/-- The one-step transition law of the descent chain, `k_y(j) = w_y(j)/R₀(y)`. -/
noncomputable def kern (y j : ℕ) : ℝ := D.wm y j / D.R0 y

/-- The window is non-empty from `m = 2` on: `⌈m/2⌉ < m`. -/
theorem window_nonempty {m : ℕ} (hm : 2 ≤ m) : (window m).Nonempty := by
  refine ⟨(m + 1) / 2, ?_⟩
  rw [mem_window]
  omega

/-- `R₀(m) > 0` at `m ≥ 2`: it is a sum of positive terms over a non-empty window. -/
theorem R0_pos {m : ℕ} (hm : 2 ≤ m) : 0 < D.R0 m := by
  rw [R0]
  refine Finset.sum_pos (fun j hj => D.wm_pos (by omega) (one_le_of_mem_window' (by omega) hj))
    (window_nonempty hm)

theorem kern_nonneg {m : ℕ} (hm : 2 ≤ m) {j : ℕ} (hj : j ∈ window m) : 0 ≤ D.kern m j :=
  div_nonneg (D.wm_nonneg (by omega) (one_le_of_mem_window' (by omega) hj)) (D.R0_pos hm).le

/-- The one-step law is a probability on the window. -/
theorem sum_kern {m : ℕ} (hm : 2 ≤ m) : ∑ j ∈ window m, D.kern m j = 1 := by
  have h : ∑ j ∈ window m, D.kern m j = (∑ j ∈ window m, D.wm m j) / D.R0 m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [h, ← R0, div_self (D.R0_pos hm).ne']

/-- **Second bullet of the proof of `lem:doubling_doeblin`.** One step from a state `z` with
`R₀(z) ≤ 2` gives every `j ∈ W(z)` mass at least `c/(2(j+1))`.

The paper's three ingredients: `(z/j)^p ≥ 1` because `j ≤ z − 1`; `q_z(j) ≥ c/(j+1)` because
`0 < 1 − ε(z) < 1`; and `R₀(z) ≤ 2`. -/
theorem kern_ge {z : ℕ} (hz : 2 ≤ z) (hR : D.R0 z ≤ 2) {j : ℕ} (hj : j ∈ window z) :
    D.c / (2 * ((j : ℝ) + 1)) ≤ D.kern z j := by
  have hz1 : 1 ≤ z := by omega
  have hj1 : 1 ≤ j := one_le_of_mem_window' hz1 hj
  have hjz : j < z := window_lt hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hjz' : (j : ℝ) ≤ (z : ℝ) := by exact_mod_cast hjz.le
  -- `(z/j)^p ≥ 1`
  have hratio : (1 : ℝ) ≤ ((z : ℝ) / (j : ℝ)) ^ D.p := by
    have h1 : (1 : ℝ) ≤ (z : ℝ) / (j : ℝ) := (one_le_div hjpos).mpr hjz'
    calc (1 : ℝ) = (1 : ℝ) ^ D.p := (Real.one_rpow D.p).symm
      _ ≤ ((z : ℝ) / (j : ℝ)) ^ D.p := Real.rpow_le_rpow (by norm_num) h1 D.p_pos.le
  -- `q_z(j) ≥ c/(j+1)`
  have hone : 1 - D.eps z ≤ 1 := by linarith [D.eps_pos z]
  have hspos : 0 < 1 - D.eps z := D.one_sub_eps_pos hz1
  have hbpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hq : D.c / ((j : ℝ) + 1) ≤ D.qm z j := by
    rw [D.qm_eq]
    refine div_le_div_of_nonneg_left D.c_pos.le (mul_pos hbpos hspos) ?_
    nlinarith
  -- combine
  have hw : D.c / ((j : ℝ) + 1) ≤ D.wm z j := by
    rw [wm]
    nlinarith [D.qm_pos hz1 j, hq, hratio]
  have hR0pos := D.R0_pos hz
  rw [kern, le_div_iff₀ hR0pos]
  have : D.c / (2 * ((j : ℝ) + 1)) * D.R0 z ≤ D.c / (2 * ((j : ℝ) + 1)) * 2 := by
    have hcnn : 0 ≤ D.c / (2 * ((j : ℝ) + 1)) := div_nonneg D.c_pos.le (by positivity)
    nlinarith
  have heq : D.c / (2 * ((j : ℝ) + 1)) * 2 = D.c / ((j : ℝ) + 1) := by
    field_simp
  linarith [hw, this, heq.le, heq.ge]

/-! ## The normalised descent transform -/

/-- **`E(g(Y_{N_ℓ}) | Y_0 = m)`**, as a recursion. -/
noncomputable def descP (D : Decay) (ℓ : ℕ) (g : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < 2 * ℓ then g m
  else ∑ j ∈ (window m).attach, D.kern m j.1 * descP D ℓ g j.1
termination_by m
decreasing_by exact window_lt j.2

theorem descP_of_lt {ℓ : ℕ} (g : ℕ → ℝ) {m : ℕ} (h : m < 2 * ℓ) : D.descP ℓ g m = g m := by
  rw [descP, if_pos h]

theorem descP_of_ge {ℓ : ℕ} (g : ℕ → ℝ) {m : ℕ} (h : ¬ m < 2 * ℓ) :
    D.descP ℓ g m = ∑ j ∈ window m, D.kern m j * D.descP ℓ g j := by
  rw [descP, if_neg h]
  exact Finset.sum_attach (window m) fun j => D.kern m j * D.descP ℓ g j

/-- **The exit law** `π_y = P(Y_{N_ℓ} ∈ · | Y_0 = y)`. -/
noncomputable def exitLaw (ℓ y j : ℕ) : ℝ := D.descP ℓ (fun z => if z = j then 1 else 0) y

theorem exitLaw_of_lt {ℓ y j : ℕ} (h : y < 2 * ℓ) :
    D.exitLaw ℓ y j = if y = j then 1 else 0 := D.descP_of_lt _ h

theorem exitLaw_of_ge {ℓ y : ℕ} (h : ¬ y < 2 * ℓ) (j : ℕ) :
    D.exitLaw ℓ y j = ∑ z ∈ window y, D.kern y z * D.exitLaw ℓ z j := D.descP_of_ge _ h

/-- **`lem:doubling_descent`(2), normalised.** The exit law is a law on the base block:
`descP ℓ g y = ∑_{z ∈ [ℓ,2ℓ)} exitLaw ℓ y z · g z` for every `y ≥ ℓ`.

Proved by strong induction on `y`, as the paper's item (2) is. -/
theorem descP_eq_sum {ℓ : ℕ} (g : ℕ → ℝ) :
    ∀ y : ℕ, ℓ ≤ y →
      D.descP ℓ g y = ∑ z ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ y z * g z := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy
    by_cases hlt : y < 2 * ℓ
    · have hmem : y ∈ Finset.Ico ℓ (2 * ℓ) := by rw [Finset.mem_Ico]; omega
      rw [D.descP_of_lt _ hlt]
      have hterm : ∀ z ∈ Finset.Ico ℓ (2 * ℓ),
          D.exitLaw ℓ y z * g z = if y = z then g z else 0 := by
        intro z _
        rw [D.exitLaw_of_lt hlt]
        by_cases hyz : y = z <;> simp [hyz]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq, if_pos hmem]
    · have hge : 2 * ℓ ≤ y := by omega
      rw [D.descP_of_ge _ hlt]
      have hterm : ∀ j ∈ window y, D.kern y j * D.descP ℓ g j
          = ∑ z ∈ Finset.Ico ℓ (2 * ℓ), D.kern y j * D.exitLaw ℓ j z * g z := by
        intro j hj
        have hjℓ : ℓ ≤ j := le_of_mem_window_of_ge hge hj
        rw [ih j (window_lt hj) hjℓ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [D.exitLaw_of_ge hlt z, Finset.sum_mul]

/-- The exit law is non-negative on the base block. -/
theorem exitLaw_nonneg {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (j : ℕ) : ∀ y : ℕ, ℓ ≤ y → 0 ≤ D.exitLaw ℓ y j := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy
    by_cases hlt : y < 2 * ℓ
    · rw [D.exitLaw_of_lt hlt]
      by_cases hyj : y = j <;> simp [hyj]
    · have hge : 2 * ℓ ≤ y := by omega
      have hy2 : 2 ≤ y := by omega
      rw [D.exitLaw_of_ge hlt j]
      refine Finset.sum_nonneg fun z hz => ?_
      exact mul_nonneg (D.kern_nonneg hy2 hz)
        (ih z (window_lt hz) (le_of_mem_window_of_ge hge hz))

/-- `descP ℓ 1 = 1`: the recursion preserves the constants, `k_y` being a probability. -/
theorem descP_one {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : ∀ y : ℕ, ℓ ≤ y → D.descP ℓ (fun _ => 1) y = 1 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy
    by_cases hlt : y < 2 * ℓ
    · rw [D.descP_of_lt _ hlt]
    · have hge : 2 * ℓ ≤ y := by omega
      have hy2 : 2 ≤ y := by omega
      rw [D.descP_of_ge _ hlt]
      have hterm : ∀ j ∈ window y, D.kern y j * D.descP ℓ (fun _ => 1) j = D.kern y j := by
        intro j hj
        rw [ih j (window_lt hj) (le_of_mem_window_of_ge hge hj), mul_one]
      rw [Finset.sum_congr rfl hterm, D.sum_kern hy2]

/-- **The exit law is a probability on `[ℓ,2ℓ)`.** -/
theorem exitLaw_sum {ℓ y : ℕ} (hℓ : 1 ≤ ℓ) (hy : ℓ ≤ y) :
    ∑ z ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ y z = 1 := by
  have h := D.descP_eq_sum (fun _ => 1) y hy
  rw [D.descP_one hℓ y hy] at h
  have h2 : ∑ z ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ y z * 1
      = ∑ z ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ y z :=
    Finset.sum_congr rfl fun z _ => mul_one _
  rw [h2] at h
  exact h.symm

/-! ## The strong Markov property -/

/-- **The strong Markov property at the block-exit time**, in the recursion's own terms:
descending to the base block `[ℓ,2ℓ)` is descending to the block `[a,2a)` and then continuing.

The paper's third bullet in the proof of `lem:doubling_coupling`. Here it needs only `ℓ ≤ a`. -/
theorem descP_comp {ℓ a : ℕ} (hla : ℓ ≤ a) (g : ℕ → ℝ) :
    ∀ y : ℕ, D.descP ℓ g y = D.descP a (fun z => D.descP ℓ g z) y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    by_cases hlt : y < 2 * a
    · rw [D.descP_of_lt _ hlt]
    · have hltℓ : ¬ y < 2 * ℓ := by omega
      rw [D.descP_of_ge _ hlt, D.descP_of_ge _ hltℓ]
      exact Finset.sum_congr rfl fun j hj => by rw [ih j (window_lt hj)]

/-- **`π_y = ∑_{z ∈ [a,2a)} μ_y(z) π_z`.** The mixture identity of `lem:doubling_coupling`, third
bullet, with `μ_y` the exit law from the block `[a,2a)` and `π` the exit laws to `[ℓ,2ℓ)`. -/
theorem exitLaw_mix {ℓ a : ℕ} (hla : ℓ ≤ a) {y : ℕ} (hy : a ≤ y) (k : ℕ) :
    D.exitLaw ℓ y k = ∑ z ∈ Finset.Ico a (2 * a), D.exitLaw a y z * D.exitLaw ℓ z k := by
  have h1 := D.descP_comp hla (fun z => if z = k then 1 else 0) y
  have h2 := D.descP_eq_sum
      (fun z => D.descP ℓ (fun w => if w = k then 1 else 0) z) y hy
  rw [exitLaw, h1, h2]
  exact Finset.sum_congr rfl fun z _ => rfl

end Decay

end GFNBounds.Doubling
