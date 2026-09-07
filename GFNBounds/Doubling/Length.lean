import GFNBounds.Doubling.Kac

/-!
# The closed-form backward length

**`prop:doubling_length`** — `app_doubling.tex:476–501`.

> In the setting of Definition `def:doubling_setting`, let `s = 1` and `0 < c < 1`. Then
> `E(σ | X₀ = j) = j/(1−c)` for every ladder state `j ≥ 1`, and `σ̄ = j̄/(1−c)`.

`lem:doubling_supersolution` supplies `≤` (`Supersolution.lean`: `hitExp_iSup_le`, `sigmaBar_le`).
This file supplies the matching `≥`, so the two clauses of the proposition are
`hitExp_iSup_eq` and `sbar_iSup_eq`.

## The modelling decision

The paper's Step 3 is optional stopping for `X_{n∧σ} + (1−c)(n∧σ)`, dominated by the integrable
excursion maximum of `lem:doubling_excursion`. **No martingale is built.** Two observations turn
that step into a statement about a recursion, and the recursion is the one
`lem:doubling_supersolution` already introduced.

First, a chain started at a ladder state visits only ladder states before `σ`, and `pstar` at
`lad (j+1)` names only ladder states, so the whole argument lives on `ℕ` with `0` absorbing:
`ladT` is `P⋆` restricted there, `hitLad n = E(σ ∧ n)`, and `hitLad (n+1) = 1 + ladT (hitLad n)`
away from the source (`hitLad_succ`) is the paper's own display.

Second, the martingale identity is an induction. `ladT` sends `x ↦ x` to `x ↦ x − (1−c)` at every
ladder state — that is `eq:doubling_superstep` — so

  `(ladT)ⁿ(x ↦ x)(m) = m − (1−c)·E(σ ∧ n | X₀ = m)`   (`ladT_iterate_id_eq`),

which *is* `E(X_{n∧σ}) = m − (1−c)E(n∧σ)` with the expectation read off the iterate. The
proposition is therefore equivalent to `(ladT)ⁿ(x ↦ x)(m) → 0` (`tendsto_ladT_iterate_id`), and
that is what dominated convergence delivers in the paper.

**Dominated convergence is replaced by an explicit superlinear supersolution.** Uniform
integrability of `X_{n∧σ}` is packaged as one function,

  `W(m) = Σ_{i=1}^m (⌊log₂ i⌋ + 1)`   (`wLog`),

which is (i) superlinear — for every `δ > 0` there is `K` with `x ≤ δW + K` on the ladder
(`wLog_superlinear`), the increments being monotone and unbounded — and (ii) a supersolution up
to a bounded defect, `ladT W ≤ W + 2` (`ladT_wLog_le`), because doubling adds `m` increments of
size `⌊log₂ m⌋ + 2` against a decrement of `⌊log₂ m⌋ + 1` and `c < 1`. The defect is harmless:
it accumulates only against the survival weights `(ladT)ⁿ1`, whose sum is `E(σ ∧ n) ≤ m/(1−c)`,
giving `(ladT)ⁿW ≤ W + 2E(σ ∧ n)` (`ladT_iterate_wLog_le`). Since the survival weights themselves
vanish (`tendsto_ladT_iterate_stepCost` — a summable non-negative series, by the same bound),
monotonicity and linearity of the iterate give

  `(ladT)ⁿ(x ↦ x)(m) ≤ δ(W(m) + 2m/(1−c)) + K·(ladT)ⁿ1(m)`,

so the limit is `≤ δ·const` for every `δ > 0`, hence `0`. That is the argument, and it is
complete: nothing here is assumed that the paper proves.

`ladHarmonic_eq_zero` records the same conclusion in the form the reduction takes — a
non-negative solution of the homogeneous equation `g(m) = ε(m)g(2m) + (1−ε(m))g(m−1)` with at
most linear growth is identically zero.

## SCOPE (disclosed)

* `E(σ | X₀ = x)` is `⨆ₙ hitExp S none n x`, and `σ̄` is `⨆ₙ sbar S none n`, exactly as in
  `lem:doubling_supersolution` and `Kac.lean`. That these suprema *are* the expectation of a
  stopping time is the modelling decision of `Supersolution.lean`, not a theorem here; what is
  proved is the value of the supremum, which is what every downstream statement consumes.
* **Loop closure only** (`cap = none`), as in the paper: on the truncation at `K` the doubling
  edge is missing above `K/2` and only the inequality `σ̄_K ≤ j̄/(1−c)` holds, which is
  `sigmaBar_le`.
* `lem:doubling_excursion` is **not** used. It exists in the paper to dominate `X_{n∧σ}`; the
  domination is done here by `wLog`, which is explicit, so the excursion bound is not consumed.
  This is a change of route, not a weakening: the conclusion is the paper's, with the paper's
  hypotheses.
* The constant in the supersolution defect is effective (`2`), and so is the comparison constant
  `K = 2^N` for any `N` with `N > 1/δ`. Nothing here is non-effective.
* `m = 0` is included in `hitExp_iSup_eq`, where both sides are `0`; the paper states `j ≥ 1`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the setting of `def:doubling_setting` | ✓ carried (`Setting`, `pstar` at `cap = none`) |
| `s = 1`, i.e. `ε(j) = c/(j+1)` | ✓ carried as `heps`, at every `j ≥ 1` |
| `0 < c < 1` | ✓ carried as `hc0`, `hc1` |
| `j` a ladder state, `j ≥ 1` | ⚠ weakened: `j = 0` is allowed, both sides being `0` |
| the target row is a probability with mean `j̄` | ✓ carried (`Setting.row_sum`, `Setting.jbar`) |
| `lem:doubling_excursion` (integrable excursion maximum) | ⚠ not consumed; replaced by `wLog` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting}

/-- The one-step operator of the loop closure, restricted to the ladder and absorbed at `s₀`. -/
noncomputable def ladT (S : Setting) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => S.eps (m + 1) * f (2 * (m + 1)) + (1 - S.eps (m + 1)) * f m

/-- The source absorbs: `P⋆` is read as `0` there, which is `h(s₀) = 0` of
`lem:doubling_supersolution`. -/
@[simp] theorem ladT_zero (f : ℕ → ℝ) : ladT S f 0 = 0 := rfl

/-- At a ladder state the operator is the two-term convex combination of `eq:doubling_policy`:
the doubling edge is present at every state of the loop closure. -/
theorem ladT_succ (f : ℕ → ℝ) (m : ℕ) :
    ladT S f (m + 1) = S.eps (m + 1) * f (2 * (m + 1)) + (1 - S.eps (m + 1)) * f m := rfl

/-- `P⋆` is monotone, being an average over the one-step law. -/
theorem ladT_mono {f g : ℕ → ℝ} (h : ∀ k, f k ≤ g k) (m : ℕ) : ladT S f m ≤ ladT S g m := by
  cases m with
  | zero => simp
  | succ j =>
      have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
      have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
      have ha := h (2 * (j + 1))
      have hb := h j
      rw [ladT_succ, ladT_succ]
      nlinarith

theorem ladT_const_zero : ladT S (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  funext m
  cases m with
  | zero => simp
  | succ j => rw [ladT_succ]; ring

theorem ladT_nonneg {f : ℕ → ℝ} (h : ∀ k, 0 ≤ f k) (m : ℕ) : 0 ≤ ladT S f m := by
  have := ladT_mono (S := S) (f := fun _ => (0 : ℝ)) (g := f) h m
  rwa [ladT_const_zero] at this

theorem ladT_sub (f g : ℕ → ℝ) (m : ℕ) :
    ladT S (fun k => f k - g k) m = ladT S f m - ladT S g m := by
  cases m with
  | zero => simp
  | succ j => rw [ladT_succ, ladT_succ, ladT_succ]; ring

/-- `P⋆` is linear. -/
theorem ladT_lin (r t : ℝ) (f g : ℕ → ℝ) :
    ladT S (fun k => r * f k + t * g k) = fun m => r * ladT S f m + t * ladT S g m := by
  funext m
  cases m with
  | zero => simp
  | succ j => rw [ladT_succ, ladT_succ, ladT_succ]; ring

/-- Monotonicity passes to the iterates, which is what compares the identity with a
supersolution at every `n`. -/
theorem ladT_iterate_mono {f g : ℕ → ℝ} (h : ∀ k, f k ≤ g k) (n m : ℕ) :
    (ladT S)^[n] f m ≤ (ladT S)^[n] g m := by
  induction n generalizing f g with
  | zero => simpa using h m
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (fun k => ladT_mono (S := S) h k)

theorem ladT_iterate_nonneg {f : ℕ → ℝ} (h : ∀ k, 0 ≤ f k) (n m : ℕ) :
    0 ≤ (ladT S)^[n] f m := by
  have hz : ∀ n : ℕ, (ladT S)^[n] (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply, ladT_const_zero, ih]
  have := ladT_iterate_mono (S := S) (f := fun _ => (0 : ℝ)) (g := f) h n m
  rwa [hz n] at this

/-- Linearity passes to the iterates. -/
theorem ladT_iterate_lin (r t : ℝ) (n : ℕ) (f g : ℕ → ℝ) (m : ℕ) :
    (ladT S)^[n] (fun k => r * f k + t * g k) m = r * (ladT S)^[n] f m + t * (ladT S)^[n] g m := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, ladT_lin]
      exact ih _ _

/-! ### The truncated hitting expectations, read on the ladder -/

/-- The cost of one step: `1` at every ladder state `j ≥ 1`, `0` at the source. -/
def stepCost : ℕ → ℝ := fun m => if m = 0 then 0 else 1

@[simp] theorem stepCost_zero : stepCost 0 = 0 := rfl

@[simp] theorem stepCost_succ (m : ℕ) : stepCost (m + 1) = 1 := if_neg (Nat.succ_ne_zero m)

theorem stepCost_nonneg (m : ℕ) : 0 ≤ stepCost m := by
  cases m with
  | zero => simp
  | succ j => simp

/-- `E(σ ∧ n | X₀ = m)` on the loop closure, read on the ladder. -/
noncomputable def hitLad (S : Setting) (n m : ℕ) : ℝ := hitExp S none n (.lad m)

@[simp] theorem hitLad_zero (m : ℕ) : hitLad S 0 m = 0 := rfl

@[simp] theorem hitLad_src (n : ℕ) : hitLad S n 0 = 0 := hitExp_src n

theorem hitLad_fun_zero : hitLad S 0 = fun _ => (0 : ℝ) := rfl

theorem hitLad_nonneg (n m : ℕ) : 0 ≤ hitLad S n m := hitExp_nonneg n _

theorem hitLad_mono {n n' : ℕ} (h : n ≤ n') (m : ℕ) : hitLad S n m ≤ hitLad S n' m :=
  hitExp_mono h _

/-- **The recursion of `lem:doubling_supersolution`, Step 3, on the ladder.** -/
theorem hitLad_succ (n m : ℕ) : hitLad S (n + 1) m = stepCost m + ladT S (hitLad S n) m := by
  cases m with
  | zero => simp
  | succ j =>
      rw [hitLad, hitExp_succ_lad, ladT_succ, stepCost_succ, pstar_lad_succ,
        if_pos (hasDouble_none (j + 1))]
      rfl

/-- The recursion, solved for the operator: `P⋆u_n = u_{n+1} − 1` away from the source. -/
theorem ladT_hitLad (n m : ℕ) : ladT S (hitLad S n) m = hitLad S (n + 1) m - stepCost m := by
  rw [hitLad_succ]; ring

/-- `E(σ ∧ n | X₀ = m) ≤ m/(1−c)`, `lem:doubling_supersolution` read on the ladder. -/
theorem hitLad_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (n m : ℕ) :
    hitLad S n m ≤ (m : ℝ) / (1 - c) := by
  have := hitExp_le_linSuper (S := S) (cap := none) hc0 hc1 heps n (St.lad m)
  rwa [linSuper_lad] at this

/-! ### The survival weights and their summability -/

/-- `P(σ > n | X₀ = m)`, as the `n`-th iterate of the operator on the step cost. -/
theorem ladT_iterate_stepCost (n : ℕ) :
    (ladT S)^[n] stepCost = fun m => hitLad S (n + 1) m - hitLad S n m := by
  induction n with
  | zero =>
      funext m
      rw [Function.iterate_zero_apply, hitLad_succ, hitLad_fun_zero, ladT_const_zero]
      simp
  | succ n ih =>
      funext m
      rw [Function.iterate_succ_apply', ih, ladT_sub, ladT_hitLad, ladT_hitLad]
      ring

/-- The survival weights vanish in the limit: their partial sums are the hitting expectations,
which are bounded by `m/(1−c)`. -/
theorem tendsto_ladT_iterate_stepCost {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (m : ℕ) :
    Tendsto (fun n => (ladT S)^[n] stepCost m) atTop (𝓝 0) := by
  refine Summable.tendsto_atTop_zero ?_
  refine summable_of_sum_range_le
    (c := (m : ℝ) / (1 - c)) (fun n => ladT_iterate_nonneg stepCost_nonneg n m) ?_
  intro n
  have hsum : ∀ i : ℕ, (ladT S)^[i] stepCost m = hitLad S (i + 1) m - hitLad S i m := by
    intro i; rw [ladT_iterate_stepCost]
  calc ∑ i ∈ Finset.range n, (ladT S)^[i] stepCost m
      = ∑ i ∈ Finset.range n, (hitLad S (i + 1) m - hitLad S i m) :=
        Finset.sum_congr rfl fun i _ => hsum i
    _ = hitLad S n m - hitLad S 0 m := Finset.sum_range_sub (fun i => hitLad S i m) n
    _ ≤ (m : ℝ) / (1 - c) := by rw [hitLad_zero]; simpa using hitLad_le hc0 hc1 heps n m

/-! ### A superlinear supersolution -/

/-- `W(m) = Σ_{i=1}^m (⌊log₂ i⌋ + 1)`: non-negative, vanishing at the source, superlinear, and a
supersolution up to the bounded defect `2`. -/
noncomputable def wLog (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, ((Nat.log 2 (i + 1) : ℝ) + 1)

@[simp] theorem wLog_zero : wLog 0 = 0 := by simp [wLog]

theorem wLog_nonneg (m : ℕ) : 0 ≤ wLog m :=
  Finset.sum_nonneg fun i _ => by positivity

theorem wLog_succ (m : ℕ) : wLog (m + 1) = wLog m + ((Nat.log 2 (m + 1) : ℝ) + 1) :=
  Finset.sum_range_succ _ m

/-- Doubling adds at most `m` terms, each at most `⌊log₂ m⌋ + 2`. -/
theorem wLog_two_mul_le {m : ℕ} (hm : m ≠ 0) :
    wLog (2 * m) ≤ wLog m + (m : ℝ) * ((Nat.log 2 m : ℝ) + 2) := by
  have hle : m ≤ 2 * m := by omega
  have hsplit : ∑ i ∈ Finset.Ico m (2 * m), ((Nat.log 2 (i + 1) : ℝ) + 1) = wLog (2 * m) - wLog m :=
    Finset.sum_Ico_eq_sub _ hle
  have hlog2 : Nat.log 2 (2 * m) = Nat.log 2 m + 1 := by
    rw [Nat.mul_comm]; exact Nat.log_mul_base (by norm_num) hm
  have hterm : ∀ i ∈ Finset.Ico m (2 * m), ((Nat.log 2 (i + 1) : ℝ) + 1)
      ≤ (Nat.log 2 m : ℝ) + 2 := by
    intro i hi
    have hi2 : i + 1 ≤ 2 * m := by
      have := (Finset.mem_Ico.mp hi).2
      omega
    have : Nat.log 2 (i + 1) ≤ Nat.log 2 m + 1 := by
      rw [← hlog2]; exact Nat.log_mono_right hi2
    have : ((Nat.log 2 (i + 1) : ℕ) : ℝ) ≤ ((Nat.log 2 m + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hcard : (Finset.Ico m (2 * m)).card = m := by
    rw [Nat.card_Ico]; omega
  have := Finset.sum_le_card_nsmul (Finset.Ico m (2 * m))
    (fun i => ((Nat.log 2 (i + 1) : ℝ) + 1)) ((Nat.log 2 m : ℝ) + 2) hterm
  rw [hsplit, hcard, nsmul_eq_mul] at this
  linarith

/-- **The supersolution inequality.** `P⋆W ≤ W + 2` at every ladder state. -/
theorem ladT_wLog_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (m : ℕ) :
    ladT S wLog m ≤ wLog m + 2 * stepCost m := by
  cases m with
  | zero => simp
  | succ j =>
      set e := S.eps (j + 1) with he
      set a : ℝ := (Nat.log 2 (j + 1) : ℝ) + 1 with ha
      have hMR : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have he0 : 0 < e := S.eps_pos (Nat.le_add_left 1 j)
      have hval : e = c / ((j : ℝ) + 2) := by
        rw [he, heps (j + 1) (Nat.le_add_left 1 j)]
        push_cast
        ring_nf
      have h1 : e * ((j : ℝ) + 2) = c := by
        rw [hval]; field_simp
      have ha1 : 1 ≤ a := by
        rw [ha]; have : (0 : ℝ) ≤ (Nat.log 2 (j + 1) : ℝ) := by positivity
        linarith
      have haM : a ≤ (j : ℝ) + 2 := by
        have : Nat.log 2 (j + 1) ≤ j + 1 := Nat.log_le_self 2 (j + 1)
        have : ((Nat.log 2 (j + 1) : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this
        rw [ha]; linarith
      have hw : wLog (2 * (j + 1)) ≤ wLog (j + 1) + ((j : ℝ) + 1) * (a + 1) := by
        have := wLog_two_mul_le (m := j + 1) (Nat.succ_ne_zero j)
        push_cast at this ⊢
        rw [ha]
        linarith
      have hwj : wLog j = wLog (j + 1) - a := by rw [wLog_succ, ha]; ring
      have hcomb : e * wLog (2 * (j + 1)) ≤ e * (wLog (j + 1) + ((j : ℝ) + 1) * (a + 1)) :=
        mul_le_mul_of_nonneg_left hw he0.le
      have hea : e * a ≤ c := by nlinarith
      have heM : e * ((j : ℝ) + 1) = c - e := by linarith
      have hprod : e * (((j : ℝ) + 1) * (a + 1)) ≤ c * (a + 1) := by nlinarith
      rw [ladT_succ, stepCost_succ, hwj]
      nlinarith

/-- **`W` is superlinear.** For every `δ > 0` there is a constant `K` with `m ≤ δW(m) + K` at
every ladder state — the increments `⌊log₂ m⌋ + 1` are monotone and unbounded. -/
theorem wLog_superlinear {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, (m : ℝ) ≤ δ * wLog m + K * stepCost m := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨((2 ^ N : ℕ) : ℝ), by positivity, ?_⟩
  intro m
  cases m with
  | zero => simp
  | succ j =>
      rw [stepCost_succ, mul_one]
      by_cases hm : j + 1 ≤ 2 ^ N
      · have hcast : ((j + 1 : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast hm
        have := wLog_nonneg (j + 1)
        nlinarith
      · have hle : 2 ^ N ≤ j + 1 := (Nat.not_le.mp hm).le
        have hsplit : ∑ i ∈ Finset.Ico (2 ^ N) (j + 1), ((Nat.log 2 (i + 1) : ℝ) + 1)
            = wLog (j + 1) - wLog (2 ^ N) := Finset.sum_Ico_eq_sub _ hle
        have hterm : ∀ i ∈ Finset.Ico (2 ^ N) (j + 1), (N : ℝ) ≤ (Nat.log 2 (i + 1) : ℝ) + 1 := by
          intro i hi
          have hpow : 2 ^ N ≤ i + 1 := le_trans (Finset.mem_Ico.mp hi).1 (Nat.le_succ i)
          have : N ≤ Nat.log 2 (i + 1) := Nat.le_log_of_pow_le (by norm_num) hpow
          have : (N : ℝ) ≤ (Nat.log 2 (i + 1) : ℝ) := by exact_mod_cast this
          linarith
        have hcard := Finset.card_nsmul_le_sum (Finset.Ico (2 ^ N) (j + 1))
          (fun i => ((Nat.log 2 (i + 1) : ℝ) + 1)) (N : ℝ) hterm
        rw [hsplit, Nat.card_Ico, nsmul_eq_mul] at hcard
        have hsub : ((j + 1 - 2 ^ N : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) - ((2 ^ N : ℕ) : ℝ) := by
          rw [Nat.cast_sub hle]
        rw [hsub] at hcard
        have hw0 : 0 ≤ wLog (2 ^ N) := wLog_nonneg _
        have hdiff : 0 ≤ ((j + 1 : ℕ) : ℝ) - ((2 ^ N : ℕ) : ℝ) := by
          have : ((2 ^ N : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hle
          linarith
        have hδN : 1 ≤ δ * (N : ℝ) := by
          rw [div_lt_iff₀ hδ] at hN
          linarith
        have hstep : (((j + 1 : ℕ) : ℝ) - ((2 ^ N : ℕ) : ℝ)) * (N : ℝ) ≤ wLog (j + 1) := by
          linarith
        have hmul := mul_le_mul_of_nonneg_left hstep hδ.le
        nlinarith

/-! ### The two iterated bounds -/

/-- `P⋆ⁿW ≤ W + 2·E(σ ∧ n)`: the bounded defect of the supersolution accumulates against the
survival weights, whose sum is the hitting expectation. -/
theorem ladT_iterate_wLog_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (n : ℕ) :
    ∀ m : ℕ, (ladT S)^[n] wLog m ≤ wLog m + 2 * hitLad S n m := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
      intro m
      rw [Function.iterate_succ_apply']
      have h1 : ladT S ((ladT S)^[n] wLog) m
          ≤ ladT S (fun k => 1 * wLog k + 2 * hitLad S n k) m :=
        ladT_mono (fun k => by simpa using ih k) m
      have h2 : ladT S (fun k => 1 * wLog k + 2 * hitLad S n k) m
          = 1 * ladT S wLog m + 2 * ladT S (hitLad S n) m := by
        rw [ladT_lin]
      have h3 := ladT_wLog_le (S := S) hc0 hc1 heps m
      have h4 := ladT_hitLad (S := S) n m
      rw [h2, h4] at h1
      linarith

/-- The height function `x ↦ x` on the ladder, `0` at the source. -/
noncomputable def ladId : ℕ → ℝ := fun m => (m : ℝ)

@[simp] theorem ladId_apply (m : ℕ) : ladId m = (m : ℝ) := rfl

/-- The one-step image of the identity: `P⋆(x ↦ x)(m) = m − (1 − c)` at every ladder state, which
is `eq:doubling_superstep`. -/
theorem ladT_id {c : ℝ} (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (m : ℕ) :
    ladT S ladId m = (m : ℝ) + (c - 1) * stepCost m := by
  cases m with
  | zero => simp
  | succ j =>
      have hne : ((j : ℝ) + 2) ≠ 0 := by positivity
      have hval : S.eps (j + 1) = c / ((j : ℝ) + 2) := by
        rw [heps (j + 1) (Nat.le_add_left 1 j)]; push_cast; ring_nf
      rw [ladT_succ, stepCost_succ, hval, ladId_apply, ladId_apply]
      push_cast
      field_simp
      ring

/-- **The martingale identity, as a recursion.**
`E(X_{n∧σ} | X₀ = m) = m − (1 − c)E(σ ∧ n | X₀ = m)`, proved by induction from
`eq:doubling_superstep` and the hitting recursion — no chain. -/
theorem ladT_iterate_id_eq {c : ℝ} (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (n : ℕ) :
    ∀ m : ℕ, (ladT S)^[n] ladId m = (m : ℝ) - (1 - c) * hitLad S n m := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
      intro m
      rw [Function.iterate_succ_apply']
      have hfun : (ladT S)^[n] ladId
          = fun k : ℕ => 1 * ladId k + (-(1 - c)) * hitLad S n k := by
        funext k; rw [ih k, ladId_apply]; ring
      rw [hfun]
      simp only [ladT_lin]
      rw [ladT_id (S := S) heps, ladT_hitLad, hitLad_succ]
      ring

/-! ### The matching lower bound -/

/-- **`prop:doubling_length` on the ladder.** `E(σ | X₀ = m) = m/(1−c)` at every ladder state of
the loop closure. -/
theorem hitLad_iSup_eq {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (m : ℕ) :
    ⨆ n, hitLad S n m = (m : ℝ) / (1 - c) := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hbdd : BddAbove (Set.range fun n => hitLad S n m) :=
    ⟨(m : ℝ) / (1 - c), by rintro _ ⟨n, rfl⟩; exact hitLad_le hc0 hc1 heps n m⟩
  have hvle : (⨆ n, hitLad S n m) ≤ (m : ℝ) / (1 - c) :=
    ciSup_le fun n => hitLad_le hc0 hc1 heps n m
  have htend : Tendsto (fun n => hitLad S n m) atTop (𝓝 (⨆ n, hitLad S n m)) :=
    tendsto_atTop_ciSup (fun a b hab => hitLad_mono hab m) hbdd
  set v := ⨆ n, hitLad S n m with hvdef
  have hA : Tendsto (fun n => (ladT S)^[n] ladId m) atTop (𝓝 ((m : ℝ) - (1 - c) * v)) := by
    have h := (htend.const_mul (1 - c)).const_sub ((m : ℝ))
    exact h.congr fun n => (ladT_iterate_id_eq heps n m).symm
  have hmnn : (0 : ℝ) ≤ (m : ℝ) / (1 - c) := by positivity
  have hL : (m : ℝ) - (1 - c) * v ≤ 0 := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    set C : ℝ := wLog m + 2 * ((m : ℝ) / (1 - c)) with hCdef
    have hC0 : 0 ≤ C := by have := wLog_nonneg m; rw [hCdef]; linarith
    have hδ : 0 < ε / (C + 1) := by positivity
    obtain ⟨K, hK0, hKle⟩ := wLog_superlinear hδ
    have hbound : ∀ n, (ladT S)^[n] ladId m
        ≤ ε / (C + 1) * C + K * ((ladT S)^[n] stepCost m) := by
      intro n
      have step1 : (ladT S)^[n] ladId m
          ≤ (ladT S)^[n] (fun k => ε / (C + 1) * wLog k + K * stepCost k) m :=
        ladT_iterate_mono (fun k => by simpa using hKle k) n m
      have step2 : (ladT S)^[n] (fun k => ε / (C + 1) * wLog k + K * stepCost k) m
          = ε / (C + 1) * ((ladT S)^[n] wLog m) + K * ((ladT S)^[n] stepCost m) :=
        ladT_iterate_lin _ _ n _ _ m
      have step3 : (ladT S)^[n] wLog m ≤ C := by
        have h4 := ladT_iterate_wLog_le hc0 hc1 heps n m
        have h5 := hitLad_le hc0 hc1 heps n m
        rw [hCdef]; linarith
      have step4 : ε / (C + 1) * ((ladT S)^[n] wLog m) ≤ ε / (C + 1) * C :=
        mul_le_mul_of_nonneg_left step3 hδ.le
      linarith [step1, step2.le, step2.ge]
    have hlim : Tendsto (fun n => ε / (C + 1) * C + K * ((ladT S)^[n] stepCost m)) atTop
        (𝓝 (ε / (C + 1) * C)) := by
      have h := (tendsto_ladT_iterate_stepCost hc0 hc1 heps m).const_mul K
      simpa using tendsto_const_nhds.add h
    have hle := le_of_tendsto_of_tendsto' hA hlim hbound
    have hfin : ε / (C + 1) * C ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < C + 1)]
      nlinarith
    linarith
  have hge : (m : ℝ) / (1 - c) ≤ v := by
    rw [div_le_iff₀ h1c]
    nlinarith
  linarith

/-- The scalar case of `ladT_iterate_lin`. -/
theorem ladT_iterate_const_mul (r : ℝ) (n : ℕ) (f : ℕ → ℝ) (m : ℕ) :
    (ladT S)^[n] (fun k => r * f k) m = r * (ladT S)^[n] f m := by
  have h := ladT_iterate_lin (S := S) r 0 n f f m
  simpa using h

/-- `E(σ ∧ n | X₀ = m) → m/(1−c)`. -/
theorem tendsto_hitLad {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (m : ℕ) :
    Tendsto (fun n => hitLad S n m) atTop (𝓝 ((m : ℝ) / (1 - c))) := by
  have hbdd : BddAbove (Set.range fun n => hitLad S n m) :=
    ⟨(m : ℝ) / (1 - c), by rintro _ ⟨n, rfl⟩; exact hitLad_le hc0 hc1 heps n m⟩
  have h := tendsto_atTop_ciSup (f := fun n => hitLad S n m)
    (fun a b hab => hitLad_mono hab m) hbdd
  rwa [hitLad_iSup_eq hc0 hc1 heps m] at h

/-- **`E(X_{n∧σ} | X₀ = m) → 0`.** The conclusion of the optional-stopping step of
`prop:doubling_length`, here a statement about the recursion. -/
theorem tendsto_ladT_iterate_id {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (m : ℕ) :
    Tendsto (fun n => (ladT S)^[n] ladId m) atTop (𝓝 0) := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have h := ((tendsto_hitLad hc0 hc1 heps m).const_mul (1 - c)).const_sub ((m : ℝ))
  have hz : (m : ℝ) - (1 - c) * ((m : ℝ) / (1 - c)) = 0 := by
    field_simp
    ring
  rw [hz] at h
  exact h.congr fun n => (ladT_iterate_id_eq heps n m).symm

/-- **The uniqueness statement `prop:doubling_length` reduces to.** A non-negative solution of the
homogeneous equation `g(m) = ε(m)g(2m) + (1−ε(m))g(m−1)` with at most linear growth vanishes
identically — the optional-stopping argument, with no martingale. -/
theorem ladHarmonic_eq_zero {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) {g : ℕ → ℝ} {B : ℝ}
    (hnn : ∀ m, 0 ≤ g m) (hlin : ∀ m, g m ≤ B * (m : ℝ)) (hharm : ∀ m, g m = ladT S g m)
    (m : ℕ) : g m = 0 := by
  have hfix : ∀ n : ℕ, (ladT S)^[n] g = g := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        rw [ih]
        funext k; exact (hharm k).symm
  have hle : ∀ n : ℕ, g m ≤ B * ((ladT S)^[n] ladId m) := by
    intro n
    have h1 : (ladT S)^[n] g m ≤ (ladT S)^[n] (fun k => B * ladId k) m :=
      ladT_iterate_mono (fun k => by simpa using hlin k) n m
    rw [hfix n, ladT_iterate_const_mul] at h1
    exact h1
  have hlim : Tendsto (fun n => B * ((ladT S)^[n] ladId m)) atTop (𝓝 0) := by
    have := (tendsto_ladT_iterate_id hc0 hc1 heps m).const_mul B
    simpa using this
  have := le_of_tendsto_of_tendsto' (f := fun _ : ℕ => g m) tendsto_const_nhds hlim hle
  exact le_antisymm this (hnn m)

/-! ### `prop:doubling_length` -/

/-- **`prop:doubling_length`, first clause.** On the loop closure at `s = 1`, `0 < c < 1`,
`E(σ | X₀ = j) = j/(1−c)` at every ladder state `j`. -/
theorem hitExp_iSup_eq {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (j : ℕ) :
    ⨆ n, hitExp S none n (.lad j) = (j : ℝ) / (1 - c) :=
  hitLad_iSup_eq hc0 hc1 heps j

/-- **`prop:doubling_length`, second clause.** `σ̄ = j̄/(1−c)`: the target-row average of the
expected hitting times, which is `σ̄` in the sense of `Kac.lean`. -/
theorem sbar_iSup_eq {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) :
    ⨆ n, sbar S none n = S.jbar / (1 - c) := by
  have hbdd : BddAbove (Set.range (sbar S none)) :=
    ⟨S.jbar / (1 - c), by rintro _ ⟨n, rfl⟩; exact sigmaBar_le hc0 hc1 heps n⟩
  have h1 : Tendsto (sbar S none) atTop (𝓝 (⨆ n, sbar S none n)) :=
    tendsto_atTop_ciSup sbar_mono hbdd
  have h2 : Tendsto (sbar S none) atTop (𝓝 (S.jbar / (1 - c))) := by
    have hsum : Tendsto (fun n => ∑ k ∈ Finset.Icc 1 S.d, S.row k * hitLad S n k) atTop
        (𝓝 (∑ k ∈ Finset.Icc 1 S.d, S.row k * ((k : ℝ) / (1 - c)))) :=
      tendsto_finsetSum _ fun k _ => (tendsto_hitLad hc0 hc1 heps k).const_mul (S.row k)
    have hval : ∑ k ∈ Finset.Icc 1 S.d, S.row k * ((k : ℝ) / (1 - c)) = S.jbar / (1 - c) := by
      have hterm : ∀ k ∈ Finset.Icc 1 S.d,
          S.row k * ((k : ℝ) / (1 - c)) = (k : ℝ) * S.row k / (1 - c) := fun k _ => by ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Setting.jbar]
    rw [← hval]
    exact hsum
  exact tendsto_nhds_unique h1 h2

/-- **`prop:doubling_length`, first clause, in the shape of `lem:doubling_supersolution`.** The
linear supersolution is attained at every state of the loop closure — the sink included, where
both sides are `0`. Together with `hitExp_iSup_le` this closes `≤` and `≥`. -/
theorem hitExp_iSup_eq_linSuper {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (x : St) :
    ⨆ n, hitExp S none n x = linSuper c x := by
  rcases x with j | _
  · rw [linSuper_lad]; exact hitExp_iSup_eq hc0 hc1 heps j
  · simp only [hitExp_sink, ciSup_const, linSuper, height_sink, zero_div]

/-- **The fixed-point form.** `E(σ | X₀ = ·)` itself solves `eq:doubling_super`,
`v(j) = 1 + (P⋆v)(j)` at every ladder state `j ≥ 1` of the loop closure — the identity
`lem:doubling_supersolution` proves for the supersolution, now carried by the supremum it
bounds. -/
theorem hitExp_iSup_fixed {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) {j : ℕ} (hj : 1 ≤ j) :
    (⨆ n, hitExp S none n (.lad j))
      = 1 + pstar S none (fun x => ⨆ n, hitExp S none n x) (.lad j) := by
  have hfun : (fun x => ⨆ n, hitExp S none n x) = linSuper c := by
    funext x; exact hitExp_iSup_eq_linSuper hc0 hc1 heps x
  rw [hfun, hitExp_iSup_eq_linSuper hc0 hc1 heps]
  exact linSuper_eq hc1 heps hj (hasDouble_none j)

end GFNBounds.Doubling
