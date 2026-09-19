import GFNBounds.Doubling.Main

/-!
# Recurrence classes of the doubling chain, in the language of least solutions

Infrastructure for **`prop:doubling_phase`** and item (1) of **`theo:doubling_main`**, under the
author's ruling R8 (2026-09-14): *recurrence and transience via hitting-probability recursions
(least nonnegative solutions)*. No chain is built; every probabilistic quantity is the least
nonnegative solution of its one-step recursion, exactly as `hitExp` is in `Supersolution.lean`.

## The definitions

For a target state `y` of the chain in play (`pstar S cap`):

* `fpass y k x` is `P_x(τ_y = k)`, `τ_y` the hitting time of `y`, time `0` included: `fpass y 0`
  is the point mass at `y`, and `fpass y (k+1) x = [x ≠ y]·(P⋆ fpass y k)(x)`.
* `hitP y n = Σ_{k ≤ n} fpass y k` is `P_x(τ_y ≤ n)`; it satisfies `hitP y (n+1) = 1` at `y` and
  `P⋆(hitP y n)` off `y` (`hitP_succ`). `hitProb y = ⨆ₙ hitP y n` is **the least nonnegative
  solution** of `h(y) = 1`, `h = P⋆h` off `y` (`hitProb_solution`, `hitProb_le_of_super`).
* `retProb y = (P⋆ hitProb y)(y)` is the return probability `P_y(τ_y⁺ < ∞)`.
* `hitT y n` is `E_x(τ_y ∧ n)`, by the recursion `hitT y (n+1) = 0` at `y`, `1 + P⋆(hitT y n)` off
  `y`; every nonnegative supersolution of `m = 1 + P⋆m` off `y` dominates it
  (`hitT_le_of_super`), and when it is bounded its supremum is the least nonnegative solution
  (`hitTime_solution`). `retT y n = 1 + (P⋆ hitT y n)(y)` is `E_y(τ_y⁺ ∧ (n+1))`.

A state is **recurrent** when `retProb y = 1`, **transient** when `retProb y < 1`, **positive
recurrent** when it is recurrent and the least solution of the expected-return-time recursion is
finite, i.e. `retT y` is bounded, and **null recurrent** when it is recurrent and `retT y` is
unbounded. The chain is positive recurrent, null recurrent or transient when **every** state is.

## What is proved here

1. **Kac, from invariance alone** (`Stat.kac_hitP`): for any invariant probability `λ` of the
   chain in play and any state `y`, `Σ_x λ(x) P_x(τ_y ≤ n) = λ(y)·E_y(τ_y⁺ ∧ (n+1))`. Hence an
   invariant probability makes **every** state positive recurrent (`Stat.isPosRecurrentAt`).
2. **The renewal identities** (`iter_ptFn_eq`, `renewal_key`): `P⁽ⁿ⁾(y,y)` solves the renewal
   equation against the first-return law, and `Σ_{n≤N} P⁽ⁿ⁾(y,y)·P_y(τ⁺ > N−n) = 1`. From them,
   by elementary sequence arguments: the Green sums `Σ_{n≤N} P⁽ⁿ⁾(y,y)` are bounded at a transient
   state and unbounded at a recurrent one; they grow at least linearly at a positive recurrent
   state and sublinearly at a null recurrent one.
3. **Solidarity on the loop closure** (`recurrent_solidarity`, `posRecurrent_solidarity`): the
   loop closure is irreducible (`lem:doubling_irreducible`), so recurrence, transience and
   positive recurrence at one state pass to every state.
4. **Uniqueness of the invariant probability on the loop closure** (`stat_unique_none`), with the
   exact Kac formula `λ(y)·E_y τ_y⁺ = 1` at every state (`Stat.kac_eq`), for **any** `Setting` —
   the uniqueness `def:doubling_setting` and `theo:doubling_main`(2) presuppose in 'its invariant
   probability' (the paper cites Levin–Peres only for the finite chain, `lem:doubling_operator`(2),
   and for the class facts of `prop:doubling_phase` Step 7).

## SCOPE (disclosed)

* The probabilistic quantities are **defined** by their recursions (ruling R8), as
  `lem:doubling_supersolution` defines `E(σ ∧ n)`. That the least solution of the return
  recursion *is* the return probability of a Markov chain is the modelling decision, not a
  theorem here: no path space is built.
* `E_y τ_y⁺ = +∞` is carried as "`retT y` is not bounded above": in `ℝ` a supremum of an
  unbounded family is a junk value, so the infinite case is stated as unboundedness.
* The solidarity and uniqueness theorems are stated on the loop closure (`cap = none`), which is
  where the paper states them; the definitions and Kac's identity hold for every `cap`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting} {cap : Option ℕ}

/-! ### `P⋆` on finite sums, and against a point mass -/

theorem pstar_const_mul (r : ℝ) (f : St → ℝ) (x : St) :
    pstar S cap (fun z => r * f z) x = r * pstar S cap f x := by
  have h : (fun z => r * f z) = r • f := by funext z; simp
  rw [h, pstar_smul]; rfl

theorem pstar_one_sub (f : St → ℝ) (x : St) :
    pstar S cap (fun z => 1 - f z) x = 1 - pstar S cap f x := by
  have h : (fun z => 1 - f z) = (fun _ => (1 : ℝ)) - f := by funext z; simp
  rw [h, pstar_sub, pstar_const]; rfl

/-- **A point mass under `P⋆`.** For `g ≥ 0`, `P(x,w)·g(w) ≤ (P⋆g)(x)`. -/
theorem pstar_ge_ptFn_mul {g : St → ℝ} (hg : ∀ z, 0 ≤ g z) (w x : St) :
    pstar S cap (ptFn w) x * g w ≤ pstar S cap g x := by
  have hle : ∀ z, g w * ptFn w z ≤ g z := by
    intro z
    by_cases hz : z = w
    · subst hz; simp
    · rw [ptFn_of_ne hz, mul_zero]; exact hg z
  have := pstar_mono (S := S) (cap := cap) hle x
  rw [pstar_const_mul] at this
  linarith

theorem pstar_iterate_mono {f g : St → ℝ} (h : ∀ x, f x ≤ g x) (n : ℕ) (x : St) :
    (pstar S cap)^[n] f x ≤ (pstar S cap)^[n] g x := by
  induction n generalizing f g with
  | zero => exact h x
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (fun z => pstar_mono h z)

theorem pstar_iterate_nonneg {f : St → ℝ} (h : ∀ x, 0 ≤ f x) (n : ℕ) (x : St) :
    0 ≤ (pstar S cap)^[n] f x := by
  induction n generalizing f with
  | zero => exact h x
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (fun z => pstar_nonneg h z)

theorem pstar_iterate_const_mul (r : ℝ) (f : St → ℝ) (n : ℕ) (x : St) :
    (pstar S cap)^[n] (fun z => r * f z) x = r * (pstar S cap)^[n] f x := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have h : pstar S cap (fun z => r * f z) = fun z => r * pstar S cap f z := by
        funext z; exact pstar_const_mul r f z
      rw [h, ih]

/-- **A point mass under `P⋆ⁿ`.** For `g ≥ 0`, `P⁽ⁿ⁾(x,w)·g(w) ≤ (P⋆ⁿg)(x)`. -/
theorem pstar_iterate_ge_ptFn_mul {g : St → ℝ} (hg : ∀ z, 0 ≤ g z) (n : ℕ) (w x : St) :
    (pstar S cap)^[n] (ptFn w) x * g w ≤ (pstar S cap)^[n] g x := by
  have hle : ∀ z, g w * ptFn w z ≤ g z := by
    intro z
    by_cases hz : z = w
    · subst hz; simp
    · rw [ptFn_of_ne hz, mul_zero]; exact hg z
  have := pstar_iterate_mono (S := S) (cap := cap) hle n x
  rw [pstar_iterate_const_mul] at this
  linarith

/-! ### First passage and hitting probabilities -/

/-- `P_x(τ_y = k)`: the law of the hitting time of `y`, time `0` included. -/
noncomputable def fpass (S : Setting) (cap : Option ℕ) (y : St) : ℕ → St → ℝ
  | 0 => ptFn y
  | k + 1 => fun x => if x = y then 0 else pstar S cap (fpass S cap y k) x

variable {y : St}

@[simp] theorem fpass_zero : fpass S cap y 0 = ptFn y := rfl

theorem fpass_succ (k : ℕ) (x : St) :
    fpass S cap y (k + 1) x = if x = y then 0 else pstar S cap (fpass S cap y k) x := rfl

theorem fpass_succ_self (k : ℕ) : fpass S cap y (k + 1) y = 0 := by simp [fpass_succ]

theorem fpass_succ_of_ne {x : St} (hx : x ≠ y) (k : ℕ) :
    fpass S cap y (k + 1) x = pstar S cap (fpass S cap y k) x := by simp [fpass_succ, hx]

theorem fpass_nonneg (k : ℕ) (x : St) : 0 ≤ fpass S cap y k x := by
  induction k generalizing x with
  | zero => exact ptFn_nonneg y x
  | succ k ih =>
      rw [fpass_succ]
      split
      · exact le_rfl
      · exact pstar_nonneg ih x

/-- `P_x(τ_y ≤ n)`. -/
noncomputable def hitP (S : Setting) (cap : Option ℕ) (y : St) (n : ℕ) (x : St) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), fpass S cap y k x

theorem hitP_zero (x : St) : hitP S cap y 0 x = ptFn y x := by simp [hitP]

theorem hitP_nonneg (n : ℕ) (x : St) : 0 ≤ hitP S cap y n x :=
  Finset.sum_nonneg fun k _ => fpass_nonneg k x

theorem hitP_mono {n m : ℕ} (h : n ≤ m) (x : St) : hitP S cap y n x ≤ hitP S cap y m x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    fun k _ _ => fpass_nonneg k x

/-- **The hitting recursion.** `P_x(τ_y ≤ n+1)` is `1` at `y` and `(P⋆ P_·(τ_y ≤ n))(x)` off it. -/
theorem hitP_succ (n : ℕ) (x : St) :
    hitP S cap y (n + 1) x = if x = y then 1 else pstar S cap (hitP S cap y n) x := by
  have hsum : pstar S cap (hitP S cap y n) x
      = ∑ k ∈ Finset.range (n + 1), pstar S cap (fpass S cap y k) x := by
    have := pstar_finsetSum (S := S) (cap := cap) (Finset.range (n + 1))
      (fun k => fpass S cap y k) x
    exact this
  unfold hitP
  rw [Finset.sum_range_succ']
  by_cases hx : x = y
  · subst hx
    simp only [fpass_succ_self, Finset.sum_const_zero, fpass_zero, ptFn_self, zero_add, if_true]
  · simp only [fpass_succ_of_ne hx, fpass_zero, ptFn_of_ne hx, add_zero, if_neg hx]
    exact hsum.symm

theorem hitP_self (n : ℕ) : hitP S cap y n y = 1 := by
  cases n with
  | zero => simp [hitP_zero]
  | succ n => simp [hitP_succ]

theorem hitP_succ_of_ne {x : St} (hx : x ≠ y) (n : ℕ) :
    hitP S cap y (n + 1) x = pstar S cap (hitP S cap y n) x := by
  rw [hitP_succ, if_neg hx]

theorem hitP_le_one (n : ℕ) (x : St) : hitP S cap y n x ≤ 1 := by
  induction n generalizing x with
  | zero =>
      rw [hitP_zero]
      by_cases hx : x = y
      · subst hx; simp
      · rw [ptFn_of_ne hx]; norm_num
  | succ n ih =>
      rw [hitP_succ]
      split
      · exact le_rfl
      · have := pstar_mono (S := S) (cap := cap) (f := hitP S cap y n) (g := fun _ => 1) ih x
        rw [pstar_const] at this
        exact this

theorem hitP_bdd (x : St) : BddAbove (Set.range fun n => hitP S cap y n x) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact hitP_le_one n x⟩

/-- `P_x(τ_y < ∞)`, the supremum of the truncated hitting probabilities. -/
noncomputable def hitProb (S : Setting) (cap : Option ℕ) (y : St) (x : St) : ℝ :=
  ⨆ n, hitP S cap y n x

theorem tendsto_hitP (x : St) :
    Tendsto (fun n => hitP S cap y n x) atTop (𝓝 (hitProb S cap y x)) :=
  tendsto_atTop_ciSup (fun _ _ h => hitP_mono h x) (hitP_bdd x)

theorem hitP_le_hitProb (n : ℕ) (x : St) : hitP S cap y n x ≤ hitProb S cap y x :=
  le_ciSup (hitP_bdd x) n

theorem hitProb_nonneg (x : St) : 0 ≤ hitProb S cap y x :=
  le_trans (hitP_nonneg 0 x) (hitP_le_hitProb 0 x)

theorem hitProb_le_one (x : St) : hitProb S cap y x ≤ 1 :=
  ciSup_le fun n => hitP_le_one n x

theorem hitProb_self : hitProb S cap y y = 1 := by
  simp [hitProb, hitP_self]

/-- **`hitProb y` solves the hitting recursion** off `y`. -/
theorem hitProb_solution {x : St} (hx : x ≠ y) :
    hitProb S cap y x = pstar S cap (hitProb S cap y) x := by
  have h1 : Tendsto (fun n => hitP S cap y (n + 1) x) atTop (𝓝 (hitProb S cap y x)) :=
    (tendsto_hitP x).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => pstar S cap (hitP S cap y n) x) atTop
      (𝓝 (pstar S cap (hitProb S cap y) x)) := tendsto_pstar (fun z => tendsto_hitP z) x
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [hitP_succ_of_ne hx]

/-- **Minimality (ruling R8).** Every nonnegative supersolution of the hitting recursion dominates
the truncated hitting probabilities, hence `hitProb y`: it is the *least* nonnegative solution. -/
theorem hitP_le_of_super {u : St → ℝ} (hu0 : ∀ x, 0 ≤ u x) (huy : 1 ≤ u y)
    (hsup : ∀ x, x ≠ y → pstar S cap u x ≤ u x) (n : ℕ) (x : St) : hitP S cap y n x ≤ u x := by
  induction n generalizing x with
  | zero =>
      rw [hitP_zero]
      by_cases hx : x = y
      · subst hx; simpa using huy
      · rw [ptFn_of_ne hx]; exact hu0 x
  | succ n ih =>
      rw [hitP_succ]
      split_ifs with hx
      · subst hx; exact huy
      · exact le_trans (pstar_mono ih x) (hsup x hx)

theorem hitProb_le_of_super {u : St → ℝ} (hu0 : ∀ x, 0 ≤ u x) (huy : 1 ≤ u y)
    (hsup : ∀ x, x ≠ y → pstar S cap u x ≤ u x) (x : St) : hitProb S cap y x ≤ u x :=
  ciSup_le fun n => hitP_le_of_super hu0 huy hsup n x

/-! ### Return probability -/

/-- `P_y(τ_y⁺ ≤ n + 1)`. -/
noncomputable def retP (S : Setting) (cap : Option ℕ) (y : St) (n : ℕ) : ℝ :=
  pstar S cap (hitP S cap y n) y

/-- `P_y(τ_y⁺ < ∞)`, one step followed by the least solution of the hitting recursion. -/
noncomputable def retProb (S : Setting) (cap : Option ℕ) (y : St) : ℝ :=
  pstar S cap (hitProb S cap y) y

theorem retP_nonneg (n : ℕ) : 0 ≤ retP S cap y n := pstar_nonneg (hitP_nonneg n) y

theorem retP_le_one (n : ℕ) : retP S cap y n ≤ 1 := by
  have := pstar_mono (S := S) (cap := cap) (f := hitP S cap y n) (g := fun _ => 1)
    (hitP_le_one n) y
  rw [pstar_const] at this
  exact this

theorem retP_mono {n m : ℕ} (h : n ≤ m) : retP S cap y n ≤ retP S cap y m :=
  pstar_mono (fun x => hitP_mono h x) y

theorem tendsto_retP : Tendsto (fun n => retP S cap y n) atTop (𝓝 (retProb S cap y)) :=
  tendsto_pstar (fun z => tendsto_hitP z) y

theorem retP_le_retProb (n : ℕ) : retP S cap y n ≤ retProb S cap y :=
  pstar_mono (fun x => hitP_le_hitProb n x) y

theorem retProb_le_one : retProb S cap y ≤ 1 := by
  have := pstar_mono (S := S) (cap := cap) (f := hitProb S cap y) (g := fun _ => 1)
    hitProb_le_one y
  rw [pstar_const] at this
  exact this

theorem retProb_nonneg : 0 ≤ retProb S cap y := pstar_nonneg hitProb_nonneg y

/-! ### Expected hitting and return times -/

/-- `E_x(τ_y ∧ n)`, by its one-step recursion. -/
noncomputable def hitT (S : Setting) (cap : Option ℕ) (y : St) : ℕ → St → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => if x = y then 0 else 1 + pstar S cap (hitT S cap y n) x

@[simp] theorem hitT_zero (x : St) : hitT S cap y 0 x = 0 := rfl

theorem hitT_succ (n : ℕ) (x : St) :
    hitT S cap y (n + 1) x = if x = y then 0 else 1 + pstar S cap (hitT S cap y n) x := rfl

@[simp] theorem hitT_self (n : ℕ) : hitT S cap y n y = 0 := by
  cases n <;> simp [hitT_succ]

/-- **The increment of the truncated hitting time is the survival probability.**
`E_x(τ_y ∧ (n+1)) − E_x(τ_y ∧ n) = P_x(τ_y > n)`. -/
theorem hitT_succ_sub (n : ℕ) (x : St) :
    hitT S cap y (n + 1) x - hitT S cap y n x = 1 - hitP S cap y n x := by
  induction n generalizing x with
  | zero =>
      rw [hitT_succ, hitP_zero]
      by_cases hx : x = y
      · subst hx; simp
      · simp only [if_neg hx, ptFn_of_ne hx, hitT_zero]
        have : pstar S cap (fun _ => (0 : ℝ)) x = 0 := by rw [pstar_const]
        rw [show (hitT S cap y 0) = fun _ => (0 : ℝ) from rfl, this]; ring
  | succ n ih =>
      by_cases hx : x = y
      · subst hx; simp [hitP_self]
      · rw [hitT_succ, hitT_succ, if_neg hx, if_neg hx, hitP_succ_of_ne hx]
        have h1 : (hitT S cap y (n + 1)) = fun z => hitT S cap y n z + (1 - hitP S cap y n z) := by
          funext z; linarith [ih z]
        have h2 : pstar S cap (fun z => hitT S cap y n z + (1 - hitP S cap y n z)) x
            = pstar S cap (hitT S cap y n) x + (1 - pstar S cap (hitP S cap y n) x) := by
          have := congrFun (pstar_add (S := S) (cap := cap) (f := hitT S cap y n)
            (g := fun z => 1 - hitP S cap y n z)) x
          simp only [Pi.add_apply] at this
          rw [show (fun z => hitT S cap y n z + (1 - hitP S cap y n z))
              = hitT S cap y n + fun z => 1 - hitP S cap y n z from rfl, this, pstar_one_sub]
        rw [h1, h2]; ring

theorem hitT_nonneg (n : ℕ) (x : St) : 0 ≤ hitT S cap y n x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [hitT_succ]
      split
      · exact le_rfl
      · have := pstar_nonneg (S := S) (cap := cap) ih x; linarith

theorem hitT_mono_succ (n : ℕ) (x : St) : hitT S cap y n x ≤ hitT S cap y (n + 1) x := by
  have := hitT_succ_sub (S := S) (cap := cap) (y := y) n x
  have := hitP_le_one (S := S) (cap := cap) (y := y) n x
  linarith

theorem hitT_mono {n m : ℕ} (h : n ≤ m) (x : St) : hitT S cap y n x ≤ hitT S cap y m x := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by omega)) (hitT_mono_succ m x)

theorem hitT_le_nat (n : ℕ) (x : St) : hitT S cap y n x ≤ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have := hitT_succ_sub (S := S) (cap := cap) (y := y) n x
      have := hitP_nonneg (S := S) (cap := cap) (y := y) n x
      push_cast; linarith [ih x]

theorem hitT_bounded (n : ℕ) : ∃ C, ∀ x, |hitT S cap y n x| ≤ C :=
  ⟨n, fun x => by rw [abs_of_nonneg (hitT_nonneg n x)]; exact hitT_le_nat n x⟩

/-- **Minimality (ruling R8).** Every nonnegative supersolution of the hitting-time recursion
dominates the truncated expected hitting times. -/
theorem hitT_le_of_super {v : St → ℝ} (hv0 : ∀ x, 0 ≤ v x)
    (hsup : ∀ x, x ≠ y → 1 + pstar S cap v x ≤ v x) (n : ℕ) (x : St) :
    hitT S cap y n x ≤ v x := by
  induction n generalizing x with
  | zero => exact hv0 x
  | succ n ih =>
      rw [hitT_succ]
      split_ifs with hx
      · exact hv0 x
      · exact le_trans (by linarith [pstar_mono (S := S) (cap := cap) ih x]) (hsup x hx)

/-- **When it is finite, the supremum of the truncated hitting times solves the recursion**, and
by `hitT_le_of_super` it is the least nonnegative solution. -/
theorem hitTime_solution (hbdd : ∀ x, BddAbove (Set.range fun n => hitT S cap y n x))
    {x : St} (hx : x ≠ y) :
    (⨆ n, hitT S cap y n x) = 1 + pstar S cap (fun z => ⨆ n, hitT S cap y n z) x := by
  have ht : ∀ z, Tendsto (fun n => hitT S cap y n z) atTop (𝓝 (⨆ n, hitT S cap y n z)) :=
    fun z => tendsto_atTop_ciSup (fun _ _ h => hitT_mono h z) (hbdd z)
  have h1 := (ht x).comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_pstar (S := S) (cap := cap) ht x).const_add 1
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  simp only [Function.comp, hitT_succ, if_neg hx]

/-- `E_y(τ_y⁺ ∧ (n + 1))`. -/
noncomputable def retT (S : Setting) (cap : Option ℕ) (y : St) (n : ℕ) : ℝ :=
  1 + pstar S cap (hitT S cap y n) y

theorem retT_zero : retT S cap y 0 = 1 := by
  simp only [retT]
  rw [show hitT S cap y 0 = fun _ => (0 : ℝ) from rfl, pstar_const]; ring

theorem retT_succ_sub (n : ℕ) : retT S cap y (n + 1) - retT S cap y n = 1 - retP S cap y n := by
  simp only [retT, retP]
  have h : hitT S cap y (n + 1) = fun z => hitT S cap y n z + (1 - hitP S cap y n z) := by
    funext z; linarith [hitT_succ_sub (S := S) (cap := cap) (y := y) n z]
  rw [h]
  have := congrFun (pstar_add (S := S) (cap := cap) (f := hitT S cap y n)
    (g := fun z => 1 - hitP S cap y n z)) y
  simp only [Pi.add_apply] at this
  rw [show (fun z => hitT S cap y n z + (1 - hitP S cap y n z))
      = hitT S cap y n + fun z => 1 - hitP S cap y n z from rfl, this, pstar_one_sub]
  ring

theorem retT_mono {n m : ℕ} (h : n ≤ m) : retT S cap y n ≤ retT S cap y m := by
  simp only [retT]
  have := pstar_mono (S := S) (cap := cap) (f := hitT S cap y n) (g := hitT S cap y m)
    (fun x => hitT_mono h x) y
  linarith

theorem one_le_retT (n : ℕ) : 1 ≤ retT S cap y n := by
  have := retT_mono (S := S) (cap := cap) (y := y) (Nat.zero_le n)
  rwa [retT_zero] at this

/-! ### The classes -/

/-- `y` is recurrent: the least solution of the return recursion is `1`. -/
def IsRecurrentAt (S : Setting) (cap : Option ℕ) (y : St) : Prop := retProb S cap y = 1

/-- `y` is transient: the least solution of the return recursion is below `1`. -/
def IsTransientAt (S : Setting) (cap : Option ℕ) (y : St) : Prop := retProb S cap y < 1

/-- `y` is positive recurrent: recurrent, with a finite expected return time. -/
def IsPosRecurrentAt (S : Setting) (cap : Option ℕ) (y : St) : Prop :=
  IsRecurrentAt S cap y ∧ BddAbove (Set.range (retT S cap y))

/-- `y` is null recurrent: recurrent, with an infinite expected return time. -/
def IsNullRecurrentAt (S : Setting) (cap : Option ℕ) (y : St) : Prop :=
  IsRecurrentAt S cap y ∧ ¬ BddAbove (Set.range (retT S cap y))

/-- The chain is positive recurrent: every state of it is. -/
def IsPositiveRecurrent (S : Setting) (cap : Option ℕ) : Prop :=
  ∀ y, OnChain cap y → IsPosRecurrentAt S cap y

/-- The chain is null recurrent: every state of it is. -/
def IsNullRecurrent (S : Setting) (cap : Option ℕ) : Prop :=
  ∀ y, OnChain cap y → IsNullRecurrentAt S cap y

/-- The chain is recurrent: every state of it is. -/
def IsRecurrent (S : Setting) (cap : Option ℕ) : Prop :=
  ∀ y, OnChain cap y → IsRecurrentAt S cap y

/-- The chain is transient: every state of it is. -/
def IsTransient (S : Setting) (cap : Option ℕ) : Prop :=
  ∀ y, OnChain cap y → IsTransientAt S cap y

theorem isTransientAt_iff_not_recurrent :
    IsTransientAt S cap y ↔ ¬ IsRecurrentAt S cap y := by
  unfold IsTransientAt IsRecurrentAt
  constructor
  · intro h h'; linarith
  · intro h; exact lt_of_le_of_ne retProb_le_one h

/-- A finite expected return time forces a certain return. -/
theorem isRecurrentAt_of_bdd (hb : BddAbove (Set.range (retT S cap y))) :
    IsRecurrentAt S cap y := by
  obtain ⟨B, hB⟩ := hb
  have hB' : ∀ n, retT S cap y n ≤ B := fun n => hB ⟨n, rfl⟩
  -- the increments `1 − retP n` are nonnegative with bounded partial sums
  have hsum : Summable fun n => 1 - retP S cap y n := by
    refine summable_of_sum_range_le (c := B)
      (fun n => by linarith [retP_le_one (S := S) (cap := cap) (y := y) n]) fun n => ?_
    have htel : ∑ i ∈ Finset.range n, (1 - retP S cap y i) = retT S cap y n - retT S cap y 0 := by
      rw [← Finset.sum_range_sub (fun i => retT S cap y i) n]
      exact Finset.sum_congr rfl fun i _ => (retT_succ_sub i).symm
    rw [htel, retT_zero]; linarith [hB' n]
  have h0 := hsum.tendsto_atTop_zero
  have h1 : Tendsto (fun n => retP S cap y n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    simpa using this
  exact tendsto_nhds_unique tendsto_retP h1

/-! ### Kac's identity, from invariance alone -/

namespace Stat

variable (L : Stat S cap)

theorem summable_mul_sub_pstar {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) :
    Summable fun x => L.lam x * (f x - pstar S cap f x) := by
  obtain ⟨C, hC⟩ := hf
  refine L.summable_mul ⟨2 * C, fun x => ?_⟩
  have h1 := hC x
  have h2 := pstar_bounded (S := S) (cap := cap) hC x
  calc |f x - pstar S cap f x| ≤ |f x| + |pstar S cap f x| := abs_sub _ _
    _ ≤ 2 * C := by linarith

/-- **Kac's identity.** For every invariant probability `λ` and every state `y`,
`Σ_x λ(x) P_x(τ_y ≤ n) = λ(y)·E_y(τ_y⁺ ∧ (n+1))`. -/
theorem kac_hitP (y : St) (n : ℕ) :
    ∑' x, L.lam x * hitP S cap y n x = L.lam y * retT S cap y n := by
  have hb : ∃ C, ∀ x, |hitT S cap y n x| ≤ C := hitT_bounded n
  have hdef : ∀ x, hitT S cap y (n + 1) x - pstar S cap (hitT S cap y n) x
      = 1 - retT S cap y n * ptFn y x := by
    intro x
    by_cases hx : x = y
    · subst hx; simp only [hitT_succ, if_true, retT, ptFn_self]; ring
    · rw [hitT_succ, if_neg hx, ptFn_of_ne hx]; ring
  have hpt : (fun x => L.lam x * (1 - hitP S cap y n x)) = fun x =>
      L.lam x * (1 - retT S cap y n * ptFn y x)
        - L.lam x * (hitT S cap y n x - pstar S cap (hitT S cap y n) x) := by
    funext x
    rw [← hdef x, ← hitT_succ_sub (S := S) (cap := cap) (y := y) n x]; ring
  have h1 : HasSum (fun x => L.lam x * (1 - retT S cap y n * ptFn y x))
      (1 - retT S cap y n * L.lam y) := by
    have e : (fun x => L.lam x * (1 - retT S cap y n * ptFn y x))
        = fun x => L.lam x - retT S cap y n * (L.lam x * ptFn y x) := by funext x; ring
    rw [e]; exact L.hasSum_one.sub ((hasSum_lam_mul_ptFn L y).mul_left _)
  have h2 : HasSum (fun x => L.lam x * (hitT S cap y n x - pstar S cap (hitT S cap y n) x)) 0 := by
    have := (L.summable_mul_sub_pstar hb).hasSum
    rwa [L.tsum_sub_pstar hb] at this
  have h3 : HasSum (fun x => L.lam x * (1 - hitP S cap y n x)) (1 - retT S cap y n * L.lam y) := by
    rw [hpt]; simpa using h1.sub h2
  have hsP : Summable fun x => L.lam x * hitP S cap y n x :=
    L.summable_mul ⟨1, fun x => by
      rw [abs_of_nonneg (hitP_nonneg n x)]; exact hitP_le_one n x⟩
  have h4 : HasSum (fun x => L.lam x * (1 - hitP S cap y n x))
      (1 - ∑' x, L.lam x * hitP S cap y n x) := by
    have e : (fun x => L.lam x * (1 - hitP S cap y n x))
        = fun x => L.lam x - L.lam x * hitP S cap y n x := by funext x; ring
    rw [e]; exact L.hasSum_one.sub hsP.hasSum
  have := h3.unique h4
  linarith

/-- **Kac's inequality.** `λ(y)·E_y(τ_y⁺ ∧ (n+1)) ≤ 1`. -/
theorem lam_mul_retT_le (y : St) (n : ℕ) : L.lam y * retT S cap y n ≤ 1 := by
  rw [← L.kac_hitP y n, ← L.total]
  refine Summable.tsum_le_tsum (fun x => ?_) (L.summable_mul ⟨1, fun x => by
      rw [abs_of_nonneg (hitP_nonneg n x)]; exact hitP_le_one n x⟩) L.summable
  have := hitP_le_one (S := S) (cap := cap) (y := y) n x
  nlinarith [L.nonneg x, hitP_nonneg (S := S) (cap := cap) (y := y) n x]

theorem retT_bdd (L : Stat S cap) {y : St} (hy : OnChain cap y) : BddAbove (Set.range (retT S cap y)) := by
  have hpos := L.pos hy
  refine ⟨1 / L.lam y, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [le_div_iff₀ hpos, mul_comm]
  exact L.lam_mul_retT_le y n

/-- **An invariant probability makes every state of the chain positive recurrent.** -/
theorem isPosRecurrentAt (L : Stat S cap) {y : St} (hy : OnChain cap y) :
    IsPosRecurrentAt S cap y :=
  ⟨isRecurrentAt_of_bdd (L.retT_bdd hy), L.retT_bdd hy⟩

theorem isPositiveRecurrent (L : Stat S cap) : IsPositiveRecurrent S cap := fun _ hy => L.isPosRecurrentAt hy

end Stat

/-! ### A recurrent state is hit with certainty from everywhere it reaches -/

theorem hitProb_eq_one_of_reach (hrec : IsRecurrentAt S cap y) {x : St}
    (hr : Reach S cap y x) : hitProb S cap y x = 1 := by
  set q : St → ℝ := fun z => 1 - hitProb S cap y z with hq
  have hq0 : ∀ z, 0 ≤ q z := fun z => by
    have := hitProb_le_one (S := S) (cap := cap) (y := y) z
    simp only [hq]; linarith
  have hPq : ∀ w, q w = 0 → pstar S cap q w = 0 := by
    intro w hw
    rw [hq, pstar_one_sub]
    by_cases hwy : w = y
    · subst hwy; unfold IsRecurrentAt retProb at hrec; rw [hrec]; ring
    · rw [← hitProb_solution hwy]; simpa [hq] using hw
  suffices h : q x = 0 by simp only [hq] at h; linarith
  induction hr with
  | refl => simp [hq, hitProb_self]
  | @tail w z _ he ih =>
      have h1 := pstar_ge_ptFn_mul (S := S) (cap := cap) hq0 z w
      rw [hPq w ih] at h1
      have h2 := edge_pstar_pos he
      have h3 := hq0 z
      nlinarith

/-! ### Kac's formula and uniqueness on the loop closure -/

theorem reach_iterate_pos {x z : St} (h : Reach S cap x z) :
    ∃ a, 0 < (pstar S cap)^[a] (ptFn z) x := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail w v _ he ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      have h1 := pstar_iterate_ge_ptFn_mul (S := S) (cap := cap)
        (g := pstar S cap (ptFn v)) (fun z => pstar_nonneg (ptFn_nonneg v) z) a w x
      have h2 := edge_pstar_pos he
      nlinarith

namespace Stat

/-- **Kac's formula on the loop closure.** `λ(y)·E_y τ_y⁺ = 1` at every state, for every
invariant probability `λ`, with `E_y τ_y⁺ = ⨆ₙ E_y(τ_y⁺ ∧ (n+1))`. -/
theorem kac_eq (L : Stat S none) (y : St) : L.lam y * (⨆ n, retT S none y n) = 1 := by
  have hrec : IsRecurrentAt S none y := (L.isPosRecurrentAt (onChain_none y)).1
  have hone : ∀ x, hitProb S none y x = 1 := fun x =>
    hitProb_eq_one_of_reach hrec (reach_all_none S y x)
  -- `Σ λ P(τ_y ≤ n) → Σ λ = 1` by dominated convergence
  have hT : Tendsto (fun n => ∑' x, L.lam x * hitP S none y n x) atTop (𝓝 (∑' x, L.lam x * 1)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := L.lam) L.summable
      (fun x => ?_) (Eventually.of_forall fun n x => ?_)
    · have := (tendsto_hitP (S := S) (cap := none) (y := y) x).const_mul (L.lam x)
      rwa [hone x] at this
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (L.nonneg x) (hitP_nonneg n x))]
      have := hitP_le_one (S := S) (cap := none) (y := y) n x
      nlinarith [L.nonneg x]
  simp only [mul_one, L.total] at hT
  have hR : Tendsto (retT S none y) atTop (𝓝 (⨆ n, retT S none y n)) :=
    tendsto_atTop_ciSup (fun _ _ h => retT_mono h) (L.retT_bdd (onChain_none y))
  have h2 : Tendsto (fun n => L.lam y * retT S none y n) atTop (𝓝 1) :=
    hT.congr fun n => L.kac_hitP y n
  exact tendsto_nhds_unique (hR.const_mul _) h2

/-- **Uniqueness of the invariant probability of the loop closure**, for any `Setting`:
`λ(y) = 1/E_y τ_y⁺` at every state. -/
theorem lam_eq_inv (L : Stat S none) (y : St) : L.lam y = (⨆ n, retT S none y n)⁻¹ := by
  have h := L.kac_eq y
  have hne : (⨆ n, retT S none y n) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact zero_ne_one h
  field_simp
  linarith

end Stat

/-- **The loop closure carries at most one invariant probability.** -/
theorem stat_unique_none (L L' : Stat S none) : L.lam = L'.lam := by
  funext y; rw [L.lam_eq_inv y, L'.lam_eq_inv y]

/-! ### Four facts about renewal sequences

`u` plays `P⁽ⁿ⁾(y,y)` and `r` plays `P_y(τ_y⁺ > m)`; the hypothesis `key` is the last-exit
identity `Σ_{n ≤ N} u(n) r(N−n) = 1`. -/

section RenewalSeq

variable {u r : ℕ → ℝ}

/-- **Transient case.** If `r ≥ ε > 0`, the Green sums are bounded by `1/ε`. -/
theorem renewal_green_le {ε : ℝ} (hε : 0 < ε) (hu : ∀ n, 0 ≤ u n) (hr : ∀ m, ε ≤ r m)
    (key : ∀ N, ∑ n ∈ Finset.range (N + 1), u n * r (N - n) = 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), u n ≤ 1 / ε := by
  rw [le_div_iff₀ hε, ← key N, Finset.sum_mul]
  exact Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hr _) (hu n)

/-- **Recurrent case.** If `r ↓ 0` with `r ≤ 1`, the Green sums are unbounded. -/
theorem renewal_green_unbdd (hu : ∀ n, 0 ≤ u n) (hr0 : ∀ m, 0 ≤ r m) (hr1 : ∀ m, r m ≤ 1)
    (hanti : Antitone r) (hlim : Tendsto r atTop (𝓝 0))
    (key : ∀ N, ∑ n ∈ Finset.range (N + 1), u n * r (N - n) = 1) :
    ¬ BddAbove (Set.range fun N => ∑ n ∈ Finset.range (N + 1), u n) := by
  rintro ⟨B, hB⟩
  set U : ℕ → ℝ := fun N => ∑ n ∈ Finset.range (N + 1), u n with hU
  have hUB : ∀ N, U N ≤ B := fun N => hB ⟨N, rfl⟩
  have hUmono : Monotone U := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun n _ _ => hu n
  have hUconv : Tendsto U atTop (𝓝 (⨆ N, U N)) :=
    tendsto_atTop_ciSup hUmono ⟨B, by rintro _ ⟨N, rfl⟩; exact hUB N⟩
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg fun n _ => hu n) (hUB 0)
  -- for every `K`, `1 ≤ r K · B + (U (M+K) − U M)`
  have hsplit : ∀ K M, 1 ≤ r K * B + (U (M + K) - U M) := by
    intro K M
    have hk := key (M + K)
    have hrange : Finset.range (M + K + 1) = Finset.range (M + 1) ∪ Finset.Ico (M + 1) (M + K + 1) := by
      ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range (M + 1)) (Finset.Ico (M + 1) (M + K + 1)) := by
      rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_range] at h1; simp only [Finset.mem_Ico] at h2; omega
    rw [hrange, Finset.sum_union hdisj] at hk
    have hA : ∑ n ∈ Finset.range (M + 1), u n * r (M + K - n) ≤ r K * U M := by
      rw [hU, Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have := hanti (show K ≤ M + K - n by omega)
      nlinarith [hu n, hr0 (M + K - n)]
    have hC : ∑ n ∈ Finset.Ico (M + 1) (M + K + 1), u n * r (M + K - n)
        ≤ U (M + K) - U M := by
      have hUsplit : U (M + K) = U M + ∑ n ∈ Finset.Ico (M + 1) (M + K + 1), u n := by
        simp only [hU]; rw [hrange, Finset.sum_union hdisj]
      rw [hUsplit]
      have : ∑ n ∈ Finset.Ico (M + 1) (M + K + 1), u n * r (M + K - n)
          ≤ ∑ n ∈ Finset.Ico (M + 1) (M + K + 1), u n :=
        Finset.sum_le_sum fun n _ => by nlinarith [hu n, hr1 (M + K - n), hr0 (M + K - n)]
      linarith
    have hUMB := hUB M
    have : r K * U M ≤ r K * B := mul_le_mul_of_nonneg_left hUMB (hr0 K)
    linarith
  -- let `M → ∞`: `1 ≤ r K · B`
  have hK : ∀ K, 1 ≤ r K * B := by
    intro K
    have h1 : Tendsto (fun M => U (M + K) - U M) atTop (𝓝 0) := by
      have := (hUconv.comp (tendsto_add_atTop_nat K)).sub hUconv
      simpa using this
    have h2 : Tendsto (fun M => r K * B + (U (M + K) - U M)) atTop (𝓝 (r K * B)) := by
      simpa using tendsto_const_nhds.add h1
    exact ge_of_tendsto h2 (Eventually.of_forall fun M => hsplit K M)
  -- let `K → ∞`: `1 ≤ 0`
  have h3 : Tendsto (fun K => r K * B) atTop (𝓝 0) := by simpa using hlim.mul_const B
  have := ge_of_tendsto h3 (Eventually.of_forall hK)
  linarith

/-- The last-exit identity, summed along `N ≤ M`: `Σ_{n ≤ M} u(n) R(M+1−n) = M + 1`, with
`R(j) = Σ_{i<j} r(i)`. -/
theorem renewal_summed (key : ∀ N, ∑ n ∈ Finset.range (N + 1), u n * r (N - n) = 1) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), u n * ∑ j ∈ Finset.range (M + 1 - n), r j = (M : ℝ) + 1 := by
  have h := Finset.sum_range_diag_flip (M + 1) (fun k j => u k * r j)
  have hl : ∑ m ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (m + 1), u k * r (m - k)
      = (M : ℝ) + 1 := by
    rw [Finset.sum_congr rfl fun m _ => key m]; simp
  rw [hl] at h
  rw [h]
  exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]

/-- **Positive case.** If `Σ_{m<M} r(m) ≤ μ` for every `M`, the Green sums grow at least linearly:
`M + 1 ≤ μ·Σ_{n ≤ M} u(n)`. -/
theorem renewal_green_ge {μ : ℝ} (hu : ∀ n, 0 ≤ u n) (hR : ∀ M, ∑ m ∈ Finset.range M, r m ≤ μ)
    (key : ∀ N, ∑ n ∈ Finset.range (N + 1), u n * r (N - n) = 1) (M : ℕ) :
    (M : ℝ) + 1 ≤ μ * ∑ n ∈ Finset.range (M + 1), u n := by
  rw [← renewal_summed key M, Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ => by
    have := hR (M + 1 - n); nlinarith [hu n]

/-- **Null case.** If `Σ_{m<M} r(m)` is unbounded, the Green sums grow sublinearly: for every
`δ > 0` there is `K` with `Σ_{n ≤ M} u(n) ≤ δ(M + K + 1)` for every `M`. -/
theorem renewal_green_sublinear (hu : ∀ n, 0 ≤ u n) (hr0 : ∀ m, 0 ≤ r m)
    (hR : ¬ BddAbove (Set.range fun M => ∑ m ∈ Finset.range M, r m))
    (key : ∀ N, ∑ n ∈ Finset.range (N + 1), u n * r (N - n) = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ M : ℕ, ∑ n ∈ Finset.range (M + 1), u n ≤ δ * ((M : ℝ) + K + 1) := by
  have hRmono : Monotone fun M => ∑ m ∈ Finset.range M, r m := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) fun m _ _ => hr0 m
  obtain ⟨K, hK⟩ : ∃ K, 1 / δ ≤ ∑ m ∈ Finset.range K, r m := by
    by_contra hcon
    push Not at hcon
    exact hR ⟨1 / δ, by rintro _ ⟨M, rfl⟩; exact (hcon M).le⟩
  have hRK : 0 < ∑ m ∈ Finset.range K, r m := lt_of_lt_of_le (by positivity) hK
  refine ⟨K, fun M => ?_⟩
  have hsum := renewal_summed key (M + K)
  have hsub : ∑ n ∈ Finset.range (M + 1), u n * ∑ m ∈ Finset.range K, r m
      ≤ ∑ n ∈ Finset.range (M + K + 1), u n * ∑ j ∈ Finset.range (M + K + 1 - n), r j := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun n _ _ =>
        mul_nonneg (hu n) (Finset.sum_nonneg fun j _ => hr0 j))
    have hn' : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    exact mul_le_mul_of_nonneg_left (hRmono (show K ≤ M + K + 1 - n by omega)) (hu n)
  rw [hsum, ← Finset.sum_mul] at hsub
  push_cast at hsub
  have h1 : (∑ n ∈ Finset.range (M + 1), u n) * (1 / δ)
      ≤ (∑ n ∈ Finset.range (M + 1), u n) * ∑ m ∈ Finset.range K, r m :=
    mul_le_mul_of_nonneg_left hK (Finset.sum_nonneg fun n _ => hu n)
  have h2 : (∑ n ∈ Finset.range (M + 1), u n) * (1 / δ) ≤ (M : ℝ) + K + 1 := by linarith
  rw [mul_one_div, div_le_iff₀ hδ] at h2
  linarith

end RenewalSeq

/-! ### The renewal structure at a state -/

/-- `P⁽ⁿ⁾(y,y)`. -/
noncomputable def uRet (S : Setting) (cap : Option ℕ) (y : St) (n : ℕ) : ℝ :=
  (pstar S cap)^[n] (ptFn y) y

/-- `P_y(τ_y⁺ = k + 1)`. -/
noncomputable def fRet (S : Setting) (cap : Option ℕ) (y : St) (k : ℕ) : ℝ :=
  pstar S cap (fpass S cap y k) y

/-- `P_y(τ_y⁺ > m)`. -/
noncomputable def rTail (S : Setting) (cap : Option ℕ) (y : St) (m : ℕ) : ℝ :=
  1 - ∑ k ∈ Finset.range m, fRet S cap y k

theorem uRet_nonneg (n : ℕ) : 0 ≤ uRet S cap y n := pstar_iterate_nonneg (ptFn_nonneg y) n y

theorem fRet_nonneg (k : ℕ) : 0 ≤ fRet S cap y k := pstar_nonneg (fpass_nonneg k) y

theorem retP_eq_sum (n : ℕ) : retP S cap y n = ∑ k ∈ Finset.range (n + 1), fRet S cap y k := by
  unfold retP fRet
  exact pstar_finsetSum (S := S) (cap := cap) (Finset.range (n + 1))
    (fun k => fpass S cap y k) y

theorem rTail_zero : rTail S cap y 0 = 1 := by simp [rTail]

theorem rTail_succ (m : ℕ) : rTail S cap y (m + 1) = 1 - retP S cap y m := by
  rw [rTail, retP_eq_sum]

theorem rTail_nonneg (m : ℕ) : 0 ≤ rTail S cap y m := by
  cases m with
  | zero => rw [rTail_zero]; norm_num
  | succ m => rw [rTail_succ]; linarith [retP_le_one (S := S) (cap := cap) (y := y) m]

theorem rTail_le_one (m : ℕ) : rTail S cap y m ≤ 1 := by
  unfold rTail; linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.range m) =>
    fRet_nonneg (S := S) (cap := cap) (y := y) k]

theorem rTail_anti : Antitone (rTail S cap y) := by
  refine antitone_nat_of_succ_le fun m => ?_
  unfold rTail
  rw [Finset.sum_range_succ]
  linarith [fRet_nonneg (S := S) (cap := cap) (y := y) m]

theorem retT_eq_sum (n : ℕ) : retT S cap y n = ∑ m ∈ Finset.range (n + 1), rTail S cap y m := by
  induction n with
  | zero => simp [retT_zero, rTail_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, rTail_succ]
      linarith [retT_succ_sub (S := S) (cap := cap) (y := y) n]

/-- **First-passage decomposition.** `P⁽ⁿ⁾(x,y) = Σ_{k ≤ n} P_x(τ_y = k) P⁽ⁿ⁻ᵏ⁾(y,y)`. -/
theorem iter_ptFn_eq (n : ℕ) (x : St) :
    (pstar S cap)^[n] (ptFn y) x
      = ∑ k ∈ Finset.range (n + 1), fpass S cap y k x * uRet S cap y (n - k) := by
  induction n generalizing x with
  | zero => simp [uRet]
  | succ n ih =>
      rw [Finset.sum_range_succ']
      by_cases hx : x = y
      · subst hx
        simp only [fpass_succ_self, zero_mul, Finset.sum_const_zero, fpass_zero, ptFn_self,
          one_mul, zero_add, Nat.sub_zero, uRet]
      · simp only [fpass_zero, ptFn_of_ne hx, zero_mul, add_zero]
        rw [Function.iterate_succ_apply']
        have hfun : (pstar S cap)^[n] (ptFn y)
            = fun z => ∑ k ∈ Finset.range (n + 1), fpass S cap y k z * uRet S cap y (n - k) := by
          funext z; exact ih z
        rw [hfun]
        have := pstar_finsetSum (S := S) (cap := cap) (Finset.range (n + 1))
          (fun k z => fpass S cap y k z * uRet S cap y (n - k)) x
        rw [this]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [show (fun z => fpass S cap y k z * uRet S cap y (n - k))
            = fun z => uRet S cap y (n - k) * fpass S cap y k z by funext z; ring,
          pstar_const_mul, fpass_succ_of_ne hx, show n + 1 - (k + 1) = n - k by omega]
        ring

/-- **The renewal equation.** `P⁽ⁿ⁺¹⁾(y,y) = Σ_{k ≤ n} P_y(τ_y⁺ = k+1) P⁽ⁿ⁻ᵏ⁾(y,y)`. -/
theorem uRet_succ (n : ℕ) :
    uRet S cap y (n + 1) = ∑ k ∈ Finset.range (n + 1), fRet S cap y k * uRet S cap y (n - k) := by
  unfold uRet
  rw [Function.iterate_succ_apply']
  have hfun : (pstar S cap)^[n] (ptFn y)
      = fun z => ∑ k ∈ Finset.range (n + 1), fpass S cap y k z * uRet S cap y (n - k) := by
    funext z; exact iter_ptFn_eq n z
  rw [hfun]
  have := pstar_finsetSum (S := S) (cap := cap) (Finset.range (n + 1))
    (fun k z => fpass S cap y k z * uRet S cap y (n - k)) y
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (fun z => fpass S cap y k z * uRet S cap y (n - k))
      = fun z => uRet S cap y (n - k) * fpass S cap y k z by funext z; ring, pstar_const_mul]
  unfold fRet uRet; ring

/-- **The last-exit identity.** `Σ_{n ≤ N} P⁽ⁿ⁾(y,y)·P_y(τ_y⁺ > N − n) = 1`. -/
theorem renewal_key (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), uRet S cap y n * rTail S cap y (N - n) = 1 := by
  induction N with
  | zero => simp [uRet, rTail_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, Nat.sub_self, rTail_zero, mul_one]
      have hstep : ∀ n ∈ Finset.range (N + 1),
          uRet S cap y n * rTail S cap y (N + 1 - n)
            = uRet S cap y n * rTail S cap y (N - n)
              - uRet S cap y n * fRet S cap y (N - n) := by
        intro n hn
        have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        rw [show N + 1 - n = (N - n) + 1 by omega]
        unfold rTail; rw [Finset.sum_range_succ]; ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ih, uRet_succ]
      have hrefl : ∑ k ∈ Finset.range (N + 1), fRet S cap y k * uRet S cap y (N - k)
          = ∑ n ∈ Finset.range (N + 1), uRet S cap y n * fRet S cap y (N - n) := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        rw [show N + 1 - 1 - n = N - n by omega, show N - (N - n) = n by omega]; ring
      rw [hrefl]; ring

/-- The Green sums `Σ_{n ≤ N} P⁽ⁿ⁾(y,y)`. -/
noncomputable def green (S : Setting) (cap : Option ℕ) (y : St) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), uRet S cap y n

theorem green_le_of_transient (ht : IsTransientAt S cap y) (N : ℕ) :
    green S cap y N ≤ 1 / (1 - retProb S cap y) := by
  have hε : 0 < 1 - retProb S cap y := by unfold IsTransientAt at ht; linarith
  refine renewal_green_le hε (fun n => uRet_nonneg n) (fun m => ?_) renewal_key N
  cases m with
  | zero => rw [rTail_zero]; linarith [retProb_nonneg (S := S) (cap := cap) (y := y)]
  | succ m => rw [rTail_succ]; linarith [retP_le_retProb (S := S) (cap := cap) (y := y) m]

theorem green_unbdd_of_recurrent (hrec : IsRecurrentAt S cap y) :
    ¬ BddAbove (Set.range (green S cap y)) := by
  have hlim : Tendsto (rTail S cap y) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_retP (S := S) (cap := cap) (y := y))
    unfold IsRecurrentAt at hrec
    rw [hrec, sub_self] at h
    refine (h.comp (tendsto_sub_atTop_nat 1)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [rTail_succ]
  exact renewal_green_unbdd (fun n => uRet_nonneg n) (fun m => rTail_nonneg m)
    (fun m => rTail_le_one m) rTail_anti hlim renewal_key

theorem green_ge_of_posRecurrent (hp : IsPosRecurrentAt S cap y) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ M : ℕ, (M : ℝ) + 1 ≤ μ * green S cap y M := by
  obtain ⟨μ, hμ⟩ := hp.2
  have hμ' : ∀ n, retT S cap y n ≤ μ := fun n => hμ ⟨n, rfl⟩
  have hμ1 : 1 ≤ μ := le_trans (one_le_retT 0) (hμ' 0)
  refine ⟨μ, by linarith, fun M => renewal_green_ge (fun n => uRet_nonneg n) (fun K => ?_)
    renewal_key M⟩
  cases K with
  | zero => simp; linarith
  | succ K => rw [← retT_eq_sum]; exact hμ' K

theorem green_sublinear_of_not_bdd (hn : ¬ BddAbove (Set.range (retT S cap y))) {δ : ℝ}
    (hδ : 0 < δ) : ∃ K : ℕ, ∀ M : ℕ, green S cap y M ≤ δ * ((M : ℝ) + K + 1) := by
  refine renewal_green_sublinear (fun n => uRet_nonneg n) (fun m => rTail_nonneg m) ?_
    renewal_key hδ
  rintro ⟨B, hB⟩
  exact hn ⟨B, by rintro _ ⟨n, rfl⟩; rw [retT_eq_sum]; exact hB ⟨n + 1, rfl⟩⟩

/-! ### Solidarity on the loop closure -/

/-- `P⁽ᵃ⁺ⁿ⁺ᵇ⁾(x,x) ≥ P⁽ᵃ⁾(x,y)·P⁽ⁿ⁾(y,y)·P⁽ᵇ⁾(y,x)`. -/
theorem uRet_comparison (x y : St) (a b n : ℕ) :
    (pstar S cap)^[a] (ptFn y) x * (pstar S cap)^[b] (ptFn x) y * uRet S cap y n
      ≤ uRet S cap x (a + (n + b)) := by
  unfold uRet
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have hH : ∀ z, 0 ≤ (pstar S cap)^[b] (ptFn x) z := pstar_iterate_nonneg (ptFn_nonneg x) b
  have hG : ∀ z, 0 ≤ (pstar S cap)^[n] ((pstar S cap)^[b] (ptFn x)) z :=
    pstar_iterate_nonneg hH n
  have h1 := pstar_iterate_ge_ptFn_mul (S := S) (cap := cap) hG a y x
  have h2 := pstar_iterate_ge_ptFn_mul (S := S) (cap := cap) hH n y y
  have hA : 0 ≤ (pstar S cap)^[a] (ptFn y) x := pstar_iterate_nonneg (ptFn_nonneg y) a x
  have := mul_le_mul_of_nonneg_left h2 hA
  nlinarith

theorem green_comparison (x y : St) (a b N : ℕ) :
    (pstar S cap)^[a] (ptFn y) x * (pstar S cap)^[b] (ptFn x) y * green S cap y N
      ≤ green S cap x (a + b + N) := by
  unfold green
  rw [Finset.mul_sum]
  calc ∑ n ∈ Finset.range (N + 1), (pstar S cap)^[a] (ptFn y) x * (pstar S cap)^[b] (ptFn x) y
          * uRet S cap y n
      ≤ ∑ n ∈ Finset.range (N + 1), uRet S cap x (a + b + n) :=
        Finset.sum_le_sum fun n _ => by
          have := uRet_comparison (S := S) (cap := cap) x y a b n
          rwa [show a + (n + b) = a + b + n by omega] at this
    _ = ∑ m ∈ Finset.Ico (a + b) (a + b + N + 1), uRet S cap x m := by
        rw [Finset.sum_Ico_eq_sum_range, show a + b + N + 1 - (a + b) = N + 1 by omega]
    _ ≤ ∑ m ∈ Finset.range (a + b + N + 1), uRet S cap x m :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro m; simp only [Finset.mem_Ico, Finset.mem_range]; omega)
          fun m _ _ => uRet_nonneg m

theorem exists_comparison_const (x y : St) :
    ∃ a b : ℕ, 0 < (pstar S none)^[a] (ptFn y) x * (pstar S none)^[b] (ptFn x) y := by
  obtain ⟨a, ha⟩ := reach_iterate_pos (reach_all_none S x y)
  obtain ⟨b, hb⟩ := reach_iterate_pos (reach_all_none S y x)
  exact ⟨a, b, mul_pos ha hb⟩

/-- **Solidarity of recurrence.** On the loop closure, a state is recurrent as soon as one is. -/
theorem recurrent_solidarity {x y : St} (hy : IsRecurrentAt S none y) : IsRecurrentAt S none x := by
  by_contra hx
  have ht : IsTransientAt S none x := isTransientAt_iff_not_recurrent.mpr hx
  obtain ⟨a, b, hC⟩ := exists_comparison_const (S := S) x y
  apply green_unbdd_of_recurrent hy
  refine ⟨(1 / (1 - retProb S none x)) / ((pstar S none)^[a] (ptFn y) x
    * (pstar S none)^[b] (ptFn x) y), ?_⟩
  rintro _ ⟨N, rfl⟩
  rw [le_div_iff₀ hC, mul_comm]
  exact le_trans (green_comparison x y a b N) (green_le_of_transient ht _)

theorem transient_solidarity {x y : St} (hy : IsTransientAt S none y) : IsTransientAt S none x := by
  rw [isTransientAt_iff_not_recurrent] at hy ⊢
  exact fun hx => hy (recurrent_solidarity hx)

/-- **Solidarity of positive recurrence.** On the loop closure, a state is positive recurrent as
soon as one is. -/
theorem posRecurrent_solidarity {x y : St} (hy : IsPosRecurrentAt S none y) :
    IsPosRecurrentAt S none x := by
  have hxrec : IsRecurrentAt S none x := recurrent_solidarity hy.1
  refine ⟨hxrec, ?_⟩
  by_contra hn
  obtain ⟨a, b, hC⟩ := exists_comparison_const (S := S) x y
  set C := (pstar S none)^[a] (ptFn y) x * (pstar S none)^[b] (ptFn x) y with hCdef
  obtain ⟨μ, hμ, hgrow⟩ := green_ge_of_posRecurrent hy
  obtain ⟨K, hK⟩ := green_sublinear_of_not_bdd hn (δ := C / (2 * μ)) (by positivity)
  set N := a + b + K with hN
  have h1 := hgrow N
  have h2 := green_comparison (S := S) (cap := none) x y a b N
  have h3 := hK (a + b + N)
  -- `C (N+1) ≤ μ C green_y N ≤ μ green_x (a+b+N) ≤ C (a+b+N+K+1)/2`
  have h4 : C * ((N : ℝ) + 1) ≤ μ * (C / (2 * μ) * (((a + b + N : ℕ) : ℝ) + K + 1)) := by
    have := mul_le_mul_of_nonneg_left h1 hC.le
    have h5 : C * (μ * green S none y N) ≤ μ * green S none x (a + b + N) := by
      have := mul_le_mul_of_nonneg_left h2 hμ.le; nlinarith
    have h6 := mul_le_mul_of_nonneg_left h3 hμ.le
    linarith
  have h7 : μ * (C / (2 * μ) * (((a + b + N : ℕ) : ℝ) + K + 1))
      = C * ((((a + b + N : ℕ) : ℝ) + K + 1) / 2) := by field_simp
  rw [h7] at h4
  have h8 : ((N : ℝ) + 1) ≤ (((a + b + N : ℕ) : ℝ) + K + 1) / 2 := le_of_mul_le_mul_left h4 hC
  rw [hN] at h8
  push_cast at h8
  have : (0 : ℝ) ≤ (a : ℝ) + b + K := by positivity
  linarith

theorem nullRecurrent_solidarity {x y : St} (hy : IsNullRecurrentAt S none y) :
    IsNullRecurrentAt S none x :=
  ⟨recurrent_solidarity hy.1, fun hb =>
    hy.2 (posRecurrent_solidarity ⟨recurrent_solidarity hy.1, hb⟩).2⟩

end GFNBounds.Doubling
