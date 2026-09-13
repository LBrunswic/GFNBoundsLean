import GFNBounds.Doubling.DescentLaw

/-!
# The descent chain, stated in the paper's shape with its constants named

**`lem:doubling_descent`** — `app_doubling.tex:968–1027`.

> Let `s = 1` and `0 < c < 1`, in the notation of Definitions `def:doubling_setting` and
> `def:doubling_decay_notation`. Then there are `c₄ > 0` and an integer `ℓ₁ > d`, depending on
> `c` and `d` alone, with the following property. The bounds
> `½ ≤ R₀(m) ≤ 2` and `|R₀(m) − 1| ≤ c₄/m` (`eq:doubling_R0`)
> hold for every `m ≥ ℓ₁`; and for every integer `ℓ ≥ ℓ₁`, with `(Y_n)_{n≥0}` the Markov chain on
> the integers `≥ ℓ` with, for every state `y ≥ ℓ`, `P(Y_{n+1} = j | Y_n = y) = w_y(j)/R₀(y)` for
> every `j ∈ W(y)` when `y ≥ 2ℓ` — a probability on `W(y)`, since `w_y > 0` there and
> `Σ_{j∈W(y)} w_y(j) = R₀(y) > 0` by `eq:doubling_R` at `α = 0` and `eq:doubling_R0` — and
> `Y_{n+1} = Y_n` when `y < 2ℓ`, and with `N_ℓ := inf{n ≥ 0 : Y_n < 2ℓ}`, the following hold for
> every starting state `m ≥ 2ℓ`:
> 1. `⌈Y_n/2⌉ ≤ Y_{n+1} ≤ Y_n − 1` for every `n < N_ℓ`, and `N_ℓ ≤ m`;
> 2. `Y_{N_ℓ} ∈ [ℓ, 2ℓ)` almost surely;
> 3. if `M₁ ∈ {2ℓ, 2ℓ+1, …} ∪ {+∞}`, if `(λ_j)_{j≥1}` is a positive sequence satisfying
>    `eq:doubling_cut` at every integer `y` with `d < y ≤ M₁`, and if `2ℓ ≤ m ≤ M₁`, then, with
>    `Z_ℓ := ∏_{n<N_ℓ} R₀(Y_n)`, which is positive, `u_m = E(Z_ℓ u_{Y_{N_ℓ}} | Y_0 = m)`
>    (`eq:doubling_pathid`).

## What this file adds

Every ingredient was already proved (`Descent.lean`, `R0Bound.lean`, `DescentLaw.lean`); no
theorem had the lemma's shape. This file names the two constants as **explicit formulas**,

  `c₄ := 16 c τ`,   `ℓ₁ := max(d + 1, ⌈32 c τ⌉)`,

both functions of `(D, d)` alone (`D` bundles `c` and its Cramér root `p_*`, `τ = 2^{p_*}`), and
proves `Decay.doubling_descent : D.DescentStatement d`, a `Prop`-structure whose fields are the
lemma's clauses, named after them.

## The modelling decision, and how the chain appears

No Markov chain is constructed (obstruction 1 of kb `0006`). The chain enters in two faithful,
chain-free guises:

* **Pathwise.** `IsDescentPath ℓ Y` says `Y : ℕ → ℕ` obeys the support of the transition law:
  `Y_{n+1} ∈ W(Y_n)` when `Y_n ≥ 2ℓ`, `Y_{n+1} = Y_n` when `Y_n < 2ℓ`. Since the law puts
  positive mass on every point of `W(y)` (field `law`), these are exactly the paths of positive
  probability. The reading is **exact** because item (1) bounds the horizon: from `m` every allowed
  path exits within `m` steps and is constant afterwards, so the law of the chain from `m` is a
  finite distribution charging each of finitely many allowed paths, and for a finite law
  "almost surely" and "on every allowed path" coincide. `exitTime ℓ Y := sInf {n | Y n < 2ℓ}` is
  the paper's `N_ℓ` verbatim. Items (1), (2) and the positivity of `Z_ℓ` are proved for **every**
  such path, and `exists_descentPath` (the greedy path, stepping to the bottom `⌈y/2⌉` of the
  window until exit) shows the class is non-empty from every start, so none of them is vacuous.
* **In law.** `descP ℓ g m` (`DescentLaw.lean`) is `E(g(Y_{N_ℓ}) | Y_0 = m)` as a first-step
  recursion, `exitLaw ℓ m j` is `P(Y_{N_ℓ} = j | Y_0 = m)`, and `descZ ℓ g m` below is
  `E(Z_ℓ g(Y_{N_ℓ}) | Y_0 = m)` as the first-step recursion with the multiplicative weight `R₀`
  per step — literally the paper's display `Σ_{j∈W(y)} (w_y(j)/R₀(y)) R₀(y) u_j`.
  `descZ_eq_descW` identifies it with `Descent.lean`'s unnormalised `descW`, on which
  `eq:doubling_pathid` was already proved (`descW_uu`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1` | ✓ carried (`Decay`: the shape of `Decay.eps`, `c_pos`, `c_lt_one`) |
| `c₄ > 0`, `ℓ₁ > d`, depending on `c`, `d` alone | ✓ carried, **explicit**: `c4 D = 16cτ`, `ell1 D d = max(d+1, ⌈32cτ⌉₊)` |
| `eq:doubling_R0` for `m ≥ ℓ₁` | ✓ carried (`R0_half_two`, `R0_sub_one`); the second half in fact holds at every `m ≥ 1` (`R0_sub_one_le`) |
| `ℓ ≥ ℓ₁` | ✓ carried |
| transition law a probability on `W(y)`, `y ≥ 2ℓ` | ✓ carried (`law`: `R₀(y) > 0`, `w_y(j)/R₀(y) > 0` on `W(y)`, total `1`) |
| starting state `m ≥ 2ℓ` | ✓ carried |
| (1) `⌈Y_n/2⌉ ≤ Y_{n+1} ≤ Y_n − 1` for `n < N_ℓ`, `N_ℓ ≤ m` | ✓ carried, pathwise (`item1_path`, non-vacuous by `path_exists`) and as the support of one step (`item1_step`) |
| (2) `Y_{N_ℓ} ∈ [ℓ,2ℓ)` a.s. | ✓ carried, pathwise (`item2_path`) and in law (`item2_law`: exit law non-negative, zero off `[ℓ,2ℓ)`, total mass `1` on it, and `descP ℓ g m = Σ_{[ℓ,2ℓ)} exitLaw · g`) |
| (3) `M₁ ∈ {2ℓ,…} ∪ {∞}` | ✓ implied: `M₁ : ℕ∞` with `2ℓ ≤ m ≤ M₁` |
| (3) `(λ_j)` **positive** | ⚠ weakened (dropped): `eq:doubling_pathid` is linear in `λ` and the proof never uses the sign, as in `DecayNotation.lean` |
| (3) `eq:doubling_cut` at every `d < y ≤ M₁` | ✓ carried (`Decay.CutBal d lam M₁`) |
| (3) `Z_ℓ > 0` | ✓ carried, pathwise (`item3_Z_pos`) |
| (3) `u_m = E(Z_ℓ u_{Y_{N_ℓ}} | Y_0 = m)` | ✓ carried in law (`item3`, via `descZ`; also in `descW` form) |

## SCOPE (disclosed)

* `E(· | Y_0 = m)` is a first-step recursion (`descP`, `descZ`), not an integral against a
  constructed path measure; the pathwise statements quantify over the allowed paths, not over a
  probability space. The two guises are **deliberately** not linked by a theorem here. The link is
  not obstruction 1: item (1) bounds the horizon, so the law from `m` is a finite distribution over
  the finitely many allowed paths and the link is a finite-sum identity (`descZ ℓ g m` is the sum
  over those paths of probability × `Z_ℓ` × `g(Y_{N_ℓ})`). It is left out because the pathwise
  reading loses nothing — for a finite law, "almost surely" and "on every allowed path" coincide —
  and because every consumer (`Weight.lean`, `Product.lean`, `Doeblin.lean`, `Coupling.lean`) uses
  the recursions.
* `N_ℓ ≤ m` is proved; the proof's sharper `N_ℓ ≤ m − 2ℓ + 1` is not stated, as the paper does not
  state it either.
* The paper derives `eq:doubling_R0` from `eq:doubling_Rexp` (Euler–Maclaurin); here it comes from
  `R0Bound.lean`'s telescoping with the explicit `c₄`, so `lem:doubling_expansion` is not consumed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

variable (D : Decay)

/-! ## The constants `c₄` and `ℓ₁` -/

/-- **`c₄`, made effective.** `c₄ := 16 c τ`. -/
noncomputable def c4 (D : Decay) : ℝ := 16 * D.c * D.tau

theorem c4_pos : 0 < D.c4 := mul_pos (mul_pos (by norm_num) D.c_pos) D.tau_pos

/-- **`ℓ₁`, made effective.** `ℓ₁ := max(d + 1, ⌈32 c τ⌉)`: the first requirement is `ℓ₁ > d`, the
second turns `|R₀ − 1| ≤ c₄/m` into `½ ≤ R₀ ≤ 2`. -/
noncomputable def ell1 (D : Decay) (d : ℕ) : ℕ := max (d + 1) ⌈32 * D.c * D.tau⌉₊

theorem lt_ell1 (d : ℕ) : d < D.ell1 d := lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_left _ _)

theorem one_le_of_ell1_le {d m : ℕ} (hm : D.ell1 d ≤ m) : 1 ≤ m := by
  have h : d + 1 ≤ D.ell1 d := le_max_left _ _
  omega

theorem thr_of_ell1 {d m : ℕ} (hm : D.ell1 d ≤ m) : 32 * D.c * D.tau ≤ (m : ℝ) := by
  have h1 : 32 * D.c * D.tau ≤ (⌈32 * D.c * D.tau⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈32 * D.c * D.tau⌉₊ : ℝ) ≤ (D.ell1 d : ℝ) := by
    exact_mod_cast le_max_right (d + 1) ⌈32 * D.c * D.tau⌉₊
  have h3 : ((D.ell1 d : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- **`eq:doubling_R0`, first half, at `m ≥ ℓ₁`.** -/
theorem R0_between_of_ell1 {d m : ℕ} (hm : D.ell1 d ≤ m) : 1 / 2 ≤ D.R0 m ∧ D.R0 m ≤ 2 :=
  D.R0_between (D.one_le_of_ell1_le hm) (D.thr_of_ell1 hm)

/-- **`eq:doubling_R0`, second half, at `m ≥ ℓ₁`.** -/
theorem R0_sub_one_le_c4 {d m : ℕ} (hm : D.ell1 d ≤ m) : |D.R0 m - 1| ≤ D.c4 / (m : ℝ) :=
  D.R0_sub_one_le (D.one_le_of_ell1_le hm)

/-! ## The chain, pathwise -/

/-- **A path of the descent chain at the level `ℓ`**: `Y_{n+1} ∈ W(Y_n)` when `Y_n ≥ 2ℓ`, and
`Y_{n+1} = Y_n` when `Y_n < 2ℓ` — the support of the transition law of `lem:doubling_descent`. -/
def IsDescentPath (ℓ : ℕ) (Y : ℕ → ℕ) : Prop :=
  ∀ n, (2 * ℓ ≤ Y n → Y (n + 1) ∈ window (Y n)) ∧ (Y n < 2 * ℓ → Y (n + 1) = Y n)

/-- **`N_ℓ := inf{n ≥ 0 : Y_n < 2ℓ}`.** -/
noncomputable def exitTime (ℓ : ℕ) (Y : ℕ → ℕ) : ℕ := sInf {n | Y n < 2 * ℓ}

/-- One greedy step: to the bottom `⌈y/2⌉ = (y+1)/2` of the window while `y ≥ 2ℓ`, else stay. -/
def greedyStep (ℓ y : ℕ) : ℕ := if 2 * ℓ ≤ y then (y + 1) / 2 else y

/-- **The pathwise fields are not vacuous.** From every start `m` there is a path of the descent
chain at the level `ℓ ≥ 1`: the greedy path `n ↦ greedyStep ℓ^[n] m`. -/
theorem exists_descentPath {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (m : ℕ) : ∃ Y : ℕ → ℕ, IsDescentPath ℓ Y ∧ Y 0 = m := by
  refine ⟨fun n => (greedyStep ℓ)^[n] m, fun n => ?_, rfl⟩
  simp only [Function.iterate_succ_apply']
  constructor
  · intro h
    rw [greedyStep, if_pos h, mem_window]
    omega
  · intro h
    rw [greedyStep, if_neg (by omega)]

/-- `⌈y/2⌉ ≤ j ≤ y − 1` on `W(y)`: the paper's reading of `j ∈ W(y)`. -/
theorem ceil_le_of_mem_window {y j : ℕ} (hj : j ∈ window y) :
    ⌈(y : ℝ) / 2⌉₊ ≤ j ∧ j ≤ y - 1 := by
  rw [mem_window] at hj
  refine ⟨Nat.ceil_le.mpr ?_, by omega⟩
  have h : y ≤ j * 2 := by omega
  have h' : (y : ℝ) ≤ (j : ℝ) * 2 := by exact_mod_cast h
  rw [div_le_iff₀ two_pos]
  exact h'

/-- Along a path that has not yet exited, each step loses at least one: `Y_n + n ≤ m`. -/
theorem path_add_le {ℓ m : ℕ} {Y : ℕ → ℕ} (hY : IsDescentPath ℓ Y) (h0 : Y 0 = m) :
    ∀ n, (∀ k < n, 2 * ℓ ≤ Y k) → Y n + n ≤ m := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
    intro hk
    have h1 := ih fun k hk' => hk k (by omega)
    have h2 : Y (n + 1) < Y n := window_lt ((hY n).1 (hk n (by omega)))
    omega

/-- **`N_ℓ` is attained, `N_ℓ ≤ m`, and `N_ℓ ≥ 1`.** -/
theorem exitTime_spec {ℓ m : ℕ} {Y : ℕ → ℕ} (hY : IsDescentPath ℓ Y) (h0 : Y 0 = m)
    (hm : 2 * ℓ ≤ m) :
    exitTime ℓ Y ≤ m ∧ Y (exitTime ℓ Y) < 2 * ℓ ∧ (∀ n < exitTime ℓ Y, 2 * ℓ ≤ Y n) ∧
      1 ≤ exitTime ℓ Y := by
  have hne : ∃ k, k ≤ m ∧ Y k < 2 * ℓ := by
    by_contra hcon
    have hall : ∀ k < m + 1, 2 * ℓ ≤ Y k := fun k hk => by
      by_contra hk'
      exact hcon ⟨k, by omega, by omega⟩
    have := path_add_le hY h0 (m + 1) hall
    omega
  obtain ⟨k, hkm, hk⟩ := hne
  have hmem : k ∈ {n | Y n < 2 * ℓ} := hk
  have hle : exitTime ℓ Y ≤ k := Nat.sInf_le hmem
  have hN : Y (exitTime ℓ Y) < 2 * ℓ := Nat.sInf_mem ⟨k, hmem⟩
  have hbefore : ∀ n < exitTime ℓ Y, 2 * ℓ ≤ Y n := fun n hn => by
    have h := Nat.notMem_of_lt_sInf hn
    simp only [Set.mem_setOf_eq, not_lt] at h
    exact h
  refine ⟨by omega, hN, hbefore, ?_⟩
  rcases Nat.eq_zero_or_pos (exitTime ℓ Y) with h | h
  · rw [h, h0] at hN
    omega
  · exact h

/-- **`lem:doubling_descent`(1), pathwise.** -/
theorem descent_item1_path {ℓ m : ℕ} {Y : ℕ → ℕ} (hY : IsDescentPath ℓ Y) (h0 : Y 0 = m)
    (hm : 2 * ℓ ≤ m) :
    (∀ n < exitTime ℓ Y, ⌈(Y n : ℝ) / 2⌉₊ ≤ Y (n + 1) ∧ Y (n + 1) ≤ Y n - 1) ∧
      exitTime ℓ Y ≤ m := by
  obtain ⟨hle, -, hbefore, -⟩ := exitTime_spec hY h0 hm
  exact ⟨fun n hn => ceil_le_of_mem_window ((hY n).1 (hbefore n hn)), hle⟩

/-- **`lem:doubling_descent`(2), pathwise.** `Y_{N_ℓ} ∈ [ℓ, 2ℓ)` on every path. -/
theorem descent_item2_path {ℓ m : ℕ} {Y : ℕ → ℕ} (hY : IsDescentPath ℓ Y) (h0 : Y 0 = m)
    (hm : 2 * ℓ ≤ m) :
    ℓ ≤ Y (exitTime ℓ Y) ∧ Y (exitTime ℓ Y) < 2 * ℓ := by
  obtain ⟨-, hN, hbefore, h1⟩ := exitTime_spec hY h0 hm
  refine ⟨?_, hN⟩
  have hprev : 2 * ℓ ≤ Y (exitTime ℓ Y - 1) := hbefore _ (by omega)
  have hstep := (hY (exitTime ℓ Y - 1)).1 hprev
  have hidx : exitTime ℓ Y - 1 + 1 = exitTime ℓ Y := by omega
  rw [hidx, mem_window] at hstep
  omega

/-- **`Z_ℓ := ∏_{n<N_ℓ} R₀(Y_n)` is positive**, on every path. -/
theorem descent_Z_pos {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) {Y : ℕ → ℕ} (hY : IsDescentPath ℓ Y)
    (h0 : Y 0 = m) (hm : 2 * ℓ ≤ m) :
    0 < ∏ n ∈ Finset.range (exitTime ℓ Y), D.R0 (Y n) := by
  obtain ⟨-, -, hbefore, -⟩ := exitTime_spec hY h0 hm
  refine Finset.prod_pos fun n hn => D.R0_pos ?_
  have := hbefore n (Finset.mem_range.mp hn)
  omega

/-! ## The chain, in law -/

/-- The exit law vanishes off the base block: `P(Y_{N_ℓ} = j | Y_0 = y) = 0` for `j ∉ [ℓ,2ℓ)`. -/
theorem exitLaw_eq_zero_of_notMem {ℓ j : ℕ} (hj : j ∉ Finset.Ico ℓ (2 * ℓ)) :
    ∀ y : ℕ, ℓ ≤ y → D.exitLaw ℓ y j = 0 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy
    by_cases hlt : y < 2 * ℓ
    · rw [D.exitLaw_of_lt hlt]
      have hyj : y ≠ j := by
        rintro rfl
        exact hj (Finset.mem_Ico.mpr ⟨hy, hlt⟩)
      rw [if_neg hyj]
    · have hge : 2 * ℓ ≤ y := by omega
      rw [D.exitLaw_of_ge hlt j]
      refine Finset.sum_eq_zero fun z hz => ?_
      rw [ih z (window_lt hz) (le_of_mem_window_of_ge hge hz), mul_zero]

/-- **`E(Z_ℓ g(Y_{N_ℓ}) | Y_0 = m)`**, as the first-step recursion of the normalised chain with
weight `R₀` per step: `Σ_{j∈W(m)} (w_m(j)/R₀(m)) · R₀(m) · descZ g j`. -/
noncomputable def descZ (D : Decay) (ℓ : ℕ) (g : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < 2 * ℓ then g m
  else ∑ j ∈ (window m).attach, D.kern m j.1 * (D.R0 m * descZ D ℓ g j.1)
termination_by m
decreasing_by exact window_lt j.2

theorem descZ_of_lt {ℓ : ℕ} (g : ℕ → ℝ) {m : ℕ} (h : m < 2 * ℓ) : D.descZ ℓ g m = g m := by
  rw [descZ, if_pos h]

theorem descZ_of_ge {ℓ : ℕ} (g : ℕ → ℝ) {m : ℕ} (h : ¬ m < 2 * ℓ) :
    D.descZ ℓ g m = ∑ j ∈ window m, D.kern m j * (D.R0 m * D.descZ ℓ g j) := by
  rw [descZ, if_neg h]
  exact Finset.sum_attach (window m) fun j => D.kern m j * (D.R0 m * D.descZ ℓ g j)

/-- **The normalisations cancel.** `E(Z_ℓ g(Y_{N_ℓ}) | Y_0 = m)` in the normalised form is the
unnormalised transform `descW` of `Descent.lean`. -/
theorem descZ_eq_descW {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (g : ℕ → ℝ) : ∀ m : ℕ, D.descZ ℓ g m = D.descW ℓ g m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hlt : m < 2 * ℓ
    · rw [D.descZ_of_lt _ hlt, D.descW_of_lt _ hlt]
    · have hm2 : 2 ≤ m := by omega
      have hR : D.R0 m ≠ 0 := (D.R0_pos hm2).ne'
      rw [D.descZ_of_ge _ hlt, D.descW_of_ge _ hlt]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ih j (window_lt hj), kern]
      field_simp

/-! ## `lem:doubling_descent`, in the paper's shape -/

/-- **`lem:doubling_descent`**, clause by clause, with `c₄ = c4 D` and `ℓ₁ = ell1 D d`. -/
structure DescentStatement (D : Decay) (d : ℕ) : Prop where
  /-- `c₄ > 0`. -/
  c4_pos : 0 < D.c4
  /-- `ℓ₁ > d`. -/
  lt_ell1 : d < D.ell1 d
  /-- `eq:doubling_R0`, first half, for every `m ≥ ℓ₁`. -/
  R0_half_two : ∀ m : ℕ, D.ell1 d ≤ m → 1 / 2 ≤ D.R0 m ∧ D.R0 m ≤ 2
  /-- `eq:doubling_R0`, second half, for every `m ≥ ℓ₁`. -/
  R0_sub_one : ∀ m : ℕ, D.ell1 d ≤ m → |D.R0 m - 1| ≤ D.c4 / (m : ℝ)
  /-- The transition law at a state `y ≥ 2ℓ` is a probability on `W(y)`. -/
  law : ∀ ℓ : ℕ, D.ell1 d ≤ ℓ → ∀ y : ℕ, 2 * ℓ ≤ y →
    0 < D.R0 y ∧ (∀ j ∈ window y, 0 < D.wm y j ∧ 0 < D.kern y j) ∧
      ∑ j ∈ window y, D.kern y j = 1
  /-- Item (1), one step: `⌈y/2⌉ ≤ j ≤ y − 1` for every `j` the law charges from `y ≥ 2ℓ`. -/
  item1_step : ∀ ℓ : ℕ, D.ell1 d ≤ ℓ → ∀ y : ℕ, 2 * ℓ ≤ y →
    ∀ j ∈ window y, ⌈(y : ℝ) / 2⌉₊ ≤ j ∧ j ≤ y - 1
  /-- The pathwise fields below are not vacuous: an allowed path starts from every `m`. -/
  path_exists : ∀ ℓ : ℕ, D.ell1 d ≤ ℓ → ∀ m : ℕ, ∃ Y : ℕ → ℕ, IsDescentPath ℓ Y ∧ Y 0 = m
  /-- Item (1), on every path from `m ≥ 2ℓ`: `⌈Y_n/2⌉ ≤ Y_{n+1} ≤ Y_n − 1` for `n < N_ℓ`, and
  `N_ℓ ≤ m`. -/
  item1_path : ∀ ℓ : ℕ, D.ell1 d ≤ ℓ → ∀ m : ℕ, 2 * ℓ ≤ m → ∀ Y : ℕ → ℕ,
    IsDescentPath ℓ Y → Y 0 = m →
      (∀ n < exitTime ℓ Y, ⌈(Y n : ℝ) / 2⌉₊ ≤ Y (n + 1) ∧ Y (n + 1) ≤ Y n - 1) ∧
        exitTime ℓ Y ≤ m
  /-- Item (2), on every path from `m ≥ 2ℓ`: `Y_{N_ℓ} ∈ [ℓ,2ℓ)`. -/
  item2_path : ∀ ℓ : ℕ, D.ell1 d ≤ ℓ → ∀ m : ℕ, 2 * ℓ ≤ m → ∀ Y : ℕ → ℕ,
    IsDescentPath ℓ Y → Y 0 = m → ℓ ≤ Y (exitTime ℓ Y) ∧ Y (exitTime ℓ Y) < 2 * ℓ
  /-- Item (2), in law from `m ≥ 2ℓ`: the exit law is a probability carried by `[ℓ,2ℓ)`, and
  `E(g(Y_{N_ℓ}) | Y_0 = m)` is its integral. -/
  item2_law : ∀ ℓ : ℕ, D.ell1 d ≤ ℓ → ∀ m : ℕ, 2 * ℓ ≤ m →
    (∀ j, 0 ≤ D.exitLaw ℓ m j) ∧ (∀ j ∉ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ m j = 0) ∧
      ∑ z ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ m z = 1 ∧
      ∀ g : ℕ → ℝ, D.descP ℓ g m = ∑ z ∈ Finset.Ico ℓ (2 * ℓ), D.exitLaw ℓ m z * g z
  /-- Item (3), `Z_ℓ > 0`, on every path from `m ≥ 2ℓ`. -/
  item3_Z_pos : ∀ ℓ : ℕ, D.ell1 d ≤ ℓ → ∀ m : ℕ, 2 * ℓ ≤ m → ∀ Y : ℕ → ℕ,
    IsDescentPath ℓ Y → Y 0 = m → 0 < ∏ n ∈ Finset.range (exitTime ℓ Y), D.R0 (Y n)
  /-- Item (3), `eq:doubling_pathid`: `u_m = E(Z_ℓ u_{Y_{N_ℓ}} | Y_0 = m)`, in the normalised
  form `descZ` and in the unnormalised form `descW`. -/
  item3 : ∀ ℓ : ℕ, D.ell1 d ≤ ℓ → ∀ m : ℕ, 2 * ℓ ≤ m → ∀ (M₁ : ℕ∞) (lam : ℕ → ℝ),
    D.CutBal d lam M₁ → (m : ℕ∞) ≤ M₁ →
      D.uu lam m = D.descZ ℓ (D.uu lam) m ∧ D.uu lam m = D.descW ℓ (D.uu lam) m

/-- **`lem:doubling_descent`.** With `c₄ := 16cτ` and `ℓ₁ := max(d+1, ⌈32cτ⌉)`, every clause of
the lemma holds. -/
theorem doubling_descent (d : ℕ) : D.DescentStatement d where
  c4_pos := D.c4_pos
  lt_ell1 := D.lt_ell1 d
  R0_half_two := fun _ hm => D.R0_between_of_ell1 hm
  R0_sub_one := fun _ hm => D.R0_sub_one_le_c4 hm
  law := by
    intro ℓ hℓ y hy
    have hℓ1 := D.one_le_of_ell1_le hℓ
    have hy2 : 2 ≤ y := by omega
    have hR := D.R0_pos hy2
    refine ⟨hR, fun j hj => ?_, D.sum_kern hy2⟩
    have hw := D.wm_pos (m := y) (by omega) (one_le_of_mem_window' (by omega) hj)
    exact ⟨hw, div_pos hw hR⟩
  item1_step := fun _ _ _ _ _ hj => ceil_le_of_mem_window hj
  path_exists := fun _ hℓ m => exists_descentPath (D.one_le_of_ell1_le hℓ) m
  item1_path := fun _ _ _ hm _ hY h0 => descent_item1_path hY h0 hm
  item2_path := fun _ _ _ hm _ hY h0 => descent_item2_path hY h0 hm
  item2_law := by
    intro ℓ hℓ m hm
    have hℓ1 := D.one_le_of_ell1_le hℓ
    have hℓm : ℓ ≤ m := by omega
    refine ⟨fun j => D.exitLaw_nonneg hℓ1 j m hℓm, fun j hj => D.exitLaw_eq_zero_of_notMem hj m hℓm,
      D.exitLaw_sum hℓ1 hℓm, fun g => D.descP_eq_sum g m hℓm⟩
  item3_Z_pos := fun _ hℓ _ hm _ hY h0 => D.descent_Z_pos (D.one_le_of_ell1_le hℓ) hY h0 hm
  item3 := by
    intro ℓ hℓ m _ M₁ lam hcut hM
    have hℓ1 := D.one_le_of_ell1_le hℓ
    have hd : d < 2 * ℓ := by have := D.lt_ell1 d; omega
    have hW := D.descW_uu hcut hd m hM
    exact ⟨hW.trans (D.descZ_eq_descW hℓ1 _ m).symm, hW⟩

end Decay

end GFNBounds.Doubling
