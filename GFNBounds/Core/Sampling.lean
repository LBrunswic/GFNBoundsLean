import Mathlib

/-!
# The sampling theorem for generative flows, on a finite state space

**`theo:sampling_theorem`** — `proofs.tex`, the theorem cited from `bengio2021flow,
brunswic2024theory` just before `theo:negative_control` (Theorem 13 of the ICLR build). Line
numbers drift (kb `0036`); the label is the anchor.

> Let `F_init`, and `F_term` be unnormalized distributions with `F_term ≠ 0` and let
> `(π⋆_→, F⋆_out)` be a generative flow. If the flow-matching constraint
> `F_init + F⋆_out π⋆_→ = F_term + F⋆_out` is satisfied then `F_init(𝒮) = F_term(𝒮)` and:
> `𝔼(τ) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1`, `s_τ ∼ F_term`.

The sampler it speaks of is defined in `brunswic2024theory` (and in the body of this paper):

> it induces a Markov chain `(s_t)_{t ≥ 1}` defined by `s_1 ∼ F_init` and `s_{t+1} = π⋆_→(s_t)`.
> Define the sampling time `τ ∈ ℕ_{≥1}` […] by `P(τ ≥ 1) = 1` and
> `P(τ = t | τ ≥ t) = dF_term/d(F_term + F⋆_out)(s_t)`. […] sampling `s_τ`.

and `app:notation` fixes the reading of `∼`: "even when `μ` is an unnormalized distribution, we
write `x ∼ μ` for 'the law of `x` is `μ/μ(𝒮)`'".

The paper does not prove the theorem; the ruling of 2026-09-13 (iii) puts it in scope, to be
formalized from its sources and not assumed. Neither source prints a proof either
(`Generativeflows.tex` states it for finite flows on a pointed state space without one), so the
proof here is this file's own, and it is the one the retraction register of the draft's
`CLAUDE.md` records as the correct one: **the occupation measure of the sampler is the minimal
non-negative solution of `μ = F_init + (μ · cont) P⋆`, and `F_term + F⋆_out` is merely *a*
solution.**

## The sampler, as a Markov chain

The chain lives on `V × Bool`, the flag recording whether the sampler has stopped (the paper's
"extending the sampling Markov chain with a sink `s_f`", with the stopped state remembered):

* `X₀ = (s₁, false)`, `s₁ ∼ F_init / F_init(𝒮)` (`init`);
* from `(x, false)`: to `(x, true)` with probability `stop(x)`, to `(y, false)` with probability
  `cont(x) P⋆(x, y)`, where `cont(x) = F⋆_out(x)/(F_term(x) + F⋆_out(x))` and
  `stop = 1 − cont` — the paper's `dF_term/d(F_term + F⋆_out)`;
* `(x, true)` is absorbing (`K`, stochastic by `K_row`).

`law n` is the law of `X_n`, by the forward recursion `law (n+1) = law n · K` (a probability for
every `n`, `law_sum`). Absorption makes every event of the theorem a function of these
marginals: `{τ > n} = {X_n ∈ V × {false}}` and `{τ ≤ n, s_τ = y} = {X_n = (y, true)}`, so

* `P(τ > n) = tailProb n`, and `𝔼(τ) = ∑_{n ≥ 0} P(τ > n) = expectedTau` (tail-sum formula for an
  `ℕ≥1 ∪ {∞}`-valued time);
* `P(τ ≤ n, s_τ = y) = law n (y, true)`, whose limit is `P(τ < ∞, s_τ = y)`.

## The proof

With `G := F_term + F⋆_out`, `Z := F_init(𝒮)` and `q_n(y) := P(τ > n, s_{n+1} = y)`:

1. Summing flow matching over `𝒮`, `P⋆` being stochastic: `F_init(𝒮) = F_term(𝒮)` (`mass_eq`).
2. Flow matching reads `G = F_init + (cont · G) P⋆` (`G_recursion`, from `cont · G = F⋆_out`),
   and `q` obeys `q_{n+1} = (cont · q_n) P⋆`, `q_0 = F_init/Z`. By induction every partial sum
   `∑_{n<N} q_n ≤ G/Z` (`partial_le`): the occupation is dominated by any non-negative solution.
3. Hence `∑_n P(τ > n) ≤ G(𝒮)/Z = F⋆_out(𝒮)/F_init(𝒮) + 1` (`expectedTau_le`), and
   `P(τ > n) → 0` (`tailProb_tendsto_zero`).
4. The occupation `Q = ∑_n q_n` solves `Q = F_init/Z + (cont · Q) P⋆` (`occ_recursion`), so
   `ν := G/Z − Q ≥ 0` is invariant under `cont · P⋆`; summing, `∑ stop · ν = 0`, so `ν` is
   carried by `{stop = 0}` and `stop · Q = stop · G/Z = F_term/Z` everywhere (`stop_mul_occ`).
   Since `P(τ ≤ n, s_τ = y) = stop(y) ∑_{k<n} q_k(y)` (`law_true_eq`), it tends to
   `F_term(y)/Z = F_term(y)/F_term(𝒮)` (`law_true_tendsto`).

## What is proved

| | |
|---|---|
| `FlowData`, `IsGenFlow`, `FlowMatching` | a generative flow with initial and terminal distributions on a finite `V`, and `equ:FM_const` |
| `cont`, `stop`, `K`, `init`, `law` | the sampler as an absorbing Markov chain on `V × Bool` |
| `K_row`, `law_sum`, `law_nonneg` | `K` is stochastic and every `law n` is a probability |
| `tailProb`, `expectedTau`, `tailProb_succ`, `stopped_sum` | `P(τ > n)`, `𝔼(τ)`; `P(τ = n+1)` is the mass stopped at step `n`; `P(τ ≤ n) = 1 − P(τ > n)` |
| `mass_eq` | `F_init(𝒮) = F_term(𝒮)` |
| `partial_le`, `occ_recursion`, `stop_mul_occ` | the minimal-solution argument |
| `unstopped_eq_zero_of_G_zero` | a state with `F_term + F⋆_out = 0` is never visited, so the convention `stop = 1` there is immaterial |
| **`sampling_theorem`** | the theorem, all clauses |
| `Parked.strict` | the bound can be strict: `𝔼(τ) = 1` against a bound of `41` |
| `Parked.inhabited` | the hypotheses of `sampling_theorem` are met by a non-trivial flow |

## Hypothesis checklist

| paper | here |
|---|---|
| `F_init`, `F_term` unnormalized distributions | ✓ non-negative functions on a finite `V` (`IsGenFlow`) |
| `F_term ≠ 0` | ✓ `hterm` |
| `(π⋆_→, F⋆_out)` a generative flow | ✓ `P⋆` a stochastic matrix, `F⋆_out ≥ 0` (`IsGenFlow`); finiteness of `F⋆_out` is automatic |
| flow matching `F_init + F⋆_out π⋆_→ = F_term + F⋆_out` | ✓ `FlowMatching`, pointwise on `V` |
| `F_init(𝒮) = F_term(𝒮)` | ✓ clause 1 |
| `𝔼(τ) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1` | ✓ clauses 2–3: the series converges and is bounded |
| `s_τ ∼ F_term` | ✓ clause 6, with `P(τ < ∞) = 1` as clauses 4–5 |
| a Polish state space with a finite background measure | ⚠ **narrowed to a finite `V`**; see SCOPE |

## SCOPE (disclosed)

* **Finite state space only.** The paper states the theorem on a Polish space with measures
  `F_init, F_term, F⋆_out` and a Markov kernel `π⋆_→`. Here `V` is a `Fintype`, measures are
  functions `V → ℝ` and the kernel is a stochastic matrix. The general measurable form is
  `Core/SamplingGeneral.lean` (`MFlow.sampling_theorem`), which closes the row in A; this file is
  its finite-state counterpart, proved independently.
* **The sampler is modelled by its time-`n` marginals, not by a path-space measure.** `law n` is
  the forward (Chapman–Kolmogorov) recursion of the absorbing chain on `V × Bool`, which is the
  law of `X_n` for the chain `Kernel.traj` would build; no trajectory measure is constructed. It
  loses nothing: by absorption `{τ > n}` and `{τ ≤ n, s_τ = y}` are events of `X_n` alone, and
  `𝔼(τ)` is the tail sum `∑_{n ≥ 0} P(τ > n)`, which is its value for a time in `ℕ≥1 ∪ {∞}`.
* **"`s_τ ∼ F_term`" is delivered as `P(τ ≤ n, s_τ = y) → F_term(y)/F_term(𝒮)`**, together with
  `P(τ ≤ n) → 1`. The limit is `P(τ < ∞, s_τ = y)`, and termination with probability one is
  clause 4: it follows from the summability of `P(τ > n)`, i.e. from `𝔼(τ) < ∞`.
* **Stopping where `F_term + F⋆_out = 0`.** The paper's `dF_term/d(F_term + F⋆_out)` is defined
  only `(F_term + F⋆_out)`-a.e.; here `cont = 0/0 = 0`, so `stop = 1`, at such a state.
  `unstopped_eq_zero_of_G_zero` shows the sampler never stands there, so any other convention
  gives the same chain on the states it visits.
* **The bound is not an equality**, and nothing here claims it is: `Parked.strict` exhibits a
  flow-matching flow with `𝔼(τ) = 1` and `F⋆_out(𝒮)/F_init(𝒮) + 1 = 41`. The lower half of the
  sandwich `W₁(f_init, κ) + 1 ≤ 𝔼(τ)` recorded in the draft's retraction register is not part of
  `theo:sampling_theorem` and is not stated.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core.Sampling

open Finset Filter Topology

/-- The data of `theo:sampling_theorem` on a finite state space: initial and terminal
distributions `F_init`, `F_term`, the star outflow `F⋆_out` and the star forward policy `P⋆`. -/
structure FlowData (V : Type*) where
  finit : V → ℝ
  fterm : V → ℝ
  fout : V → ℝ
  P : V → V → ℝ

namespace FlowData

variable {V : Type*} [Fintype V] [DecidableEq V] (F : FlowData V)

/-- `(P⋆, F⋆_out)` is a generative flow and `F_init`, `F_term` are unnormalized distributions:
all four are non-negative and `P⋆` is stochastic. -/
structure IsGenFlow : Prop where
  finit_nonneg : ∀ x, 0 ≤ F.finit x
  fterm_nonneg : ∀ x, 0 ≤ F.fterm x
  fout_nonneg : ∀ x, 0 ≤ F.fout x
  P_nonneg : ∀ x y, 0 ≤ F.P x y
  P_row : ∀ x, ∑ y, F.P x y = 1

/-- The flow-matching constraint `equ:FM_const`, `F_init + F⋆_out P⋆ = F_term + F⋆_out`. -/
def FlowMatching : Prop :=
  ∀ y, F.finit y + ∑ x, F.fout x * F.P x y = F.fterm y + F.fout y

/-- The probability of moving on from `x`, `F⋆_out(x)/(F_term(x) + F⋆_out(x))`. -/
noncomputable def cont (x : V) : ℝ := F.fout x / (F.fterm x + F.fout x)

/-- The probability of stopping at `x`, the paper's `dF_term/d(F_term + F⋆_out)(x)`. -/
noncomputable def stop (x : V) : ℝ := 1 - F.cont x

/-- The sampler's transition matrix on `V × Bool`; `true` flags a stopped sampler. -/
noncomputable def K : V × Bool → V × Bool → ℝ
  | (x, false), (y, false) => F.cont x * F.P x y
  | (x, false), (y, true) => if y = x then F.stop x else 0
  | (x, true), (y, b) => if y = x ∧ b = true then 1 else 0

/-- The sampler's initial law: `s₁ ∼ F_init/F_init(𝒮)`, not stopped. -/
noncomputable def init : V × Bool → ℝ
  | (y, false) => F.finit y / ∑ x, F.finit x
  | (_, true) => 0

/-- The law of the sampler's chain at time `n`. -/
noncomputable def law : ℕ → V × Bool → ℝ
  | 0 => F.init
  | n + 1 => fun z => ∑ w, law n w * F.K w z

/-- `P(τ > n)`: the mass not yet stopped at time `n`. -/
noncomputable def tailProb (n : ℕ) : ℝ := ∑ y, F.law n (y, false)

/-- `𝔼(τ) = ∑_{n ≥ 0} P(τ > n)`. -/
noncomputable def expectedTau : ℝ := ∑' n, F.tailProb n

theorem law_succ (n : ℕ) (z : V × Bool) : F.law (n + 1) z = ∑ w, F.law n w * F.K w z := rfl

theorem law_succ_false (n : ℕ) (y : V) :
    F.law (n + 1) (y, false) = ∑ x, F.cont x * F.law n (x, false) * F.P x y := by
  rw [law_succ]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, K, Bool.false_eq_true, and_false,
    if_false, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem law_succ_true (n : ℕ) (y : V) :
    F.law (n + 1) (y, true) = F.law n (y, true) + F.law n (y, false) * F.stop y := by
  rw [law_succ]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, K, and_true, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem law_zero_false (y : V) : F.law 0 (y, false) = F.finit y / ∑ x, F.finit x := rfl

theorem law_zero_true (y : V) : F.law 0 (y, true) = 0 := rfl

variable {F}

omit [DecidableEq V] in
theorem cont_nonneg (hF : F.IsGenFlow) (x : V) : 0 ≤ F.cont x :=
  div_nonneg (hF.fout_nonneg x) (add_nonneg (hF.fterm_nonneg x) (hF.fout_nonneg x))

omit [DecidableEq V] in
theorem cont_le_one (hF : F.IsGenFlow) (x : V) : F.cont x ≤ 1 := by
  unfold cont
  rcases (add_nonneg (hF.fterm_nonneg x) (hF.fout_nonneg x)).eq_or_lt with h | h
  · rw [← h, div_zero]; exact zero_le_one
  · rw [div_le_one h]; linarith [hF.fterm_nonneg x]

omit [DecidableEq V] in
theorem stop_nonneg (hF : F.IsGenFlow) (x : V) : 0 ≤ F.stop x := by
  unfold stop; linarith [cont_le_one hF x]

omit [DecidableEq V] in
theorem cont_mul (hF : F.IsGenFlow) (x : V) :
    F.cont x * (F.fterm x + F.fout x) = F.fout x := by
  unfold cont
  by_cases h : F.fterm x + F.fout x = 0
  · have : F.fout x = 0 := by linarith [hF.fterm_nonneg x, hF.fout_nonneg x]
    rw [h, this, div_zero, zero_mul]
  · field_simp

omit [DecidableEq V] in
theorem stop_mul (hF : F.IsGenFlow) (x : V) :
    F.stop x * (F.fterm x + F.fout x) = F.fterm x := by
  have := cont_mul hF x
  unfold stop; linarith [show (1 - F.cont x) * (F.fterm x + F.fout x)
    = (F.fterm x + F.fout x) - F.cont x * (F.fterm x + F.fout x) by ring]

theorem K_nonneg (hF : F.IsGenFlow) (w z : V × Bool) : 0 ≤ F.K w z := by
  rcases w with ⟨x, _ | _⟩ <;> rcases z with ⟨y, _ | _⟩
  · exact mul_nonneg (cont_nonneg hF x) (hF.P_nonneg x y)
  · show 0 ≤ (if y = x then F.stop x else 0)
    split_ifs
    · exact stop_nonneg hF x
    · exact le_rfl
  · show 0 ≤ (if y = x ∧ false = true then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  · show 0 ≤ (if y = x ∧ true = true then (1 : ℝ) else 0)
    split_ifs <;> norm_num

/-- The augmented kernel is stochastic: each row sums to `1`. -/
theorem K_row (hF : F.IsGenFlow) (w : V × Bool) : ∑ z, F.K w z = 1 := by
  rcases w with ⟨x, _ | _⟩
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, K]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hF.P_row, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, stop]
    ring
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, K, and_true, Bool.false_eq_true, and_false, if_false,
      add_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem law_nonneg (hF : F.IsGenFlow) : ∀ (n : ℕ) (z : V × Bool), 0 ≤ F.law n z
  | 0, (y, false) => div_nonneg (hF.finit_nonneg y) (Finset.sum_nonneg fun x _ => hF.finit_nonneg x)
  | 0, (_, true) => le_rfl
  | n + 1, z => by
    rw [law_succ]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (law_nonneg hF n w) (K_nonneg hF w z)

/-- The sampler's time-`n` law is a probability distribution on `V × Bool`. -/
theorem law_sum (hF : F.IsGenFlow) (hZ : 0 < ∑ x, F.finit x) :
    ∀ n : ℕ, ∑ z, F.law n z = 1
  | 0 => by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, law_zero_true, law_zero_false, zero_add]
    rw [← Finset.sum_div, div_self hZ.ne']
  | n + 1 => by
    simp only [law_succ]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, K_row hF, mul_one]
    exact law_sum hF hZ n

omit [DecidableEq V] in
/-- **Mass conservation**: flow matching forces `F_init(𝒮) = F_term(𝒮)`. -/
theorem mass_eq (hF : F.IsGenFlow) (hFM : F.FlowMatching) :
    ∑ x, F.finit x = ∑ x, F.fterm x := by
  have h := Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hFM y
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm] at h
  simp only [← Finset.mul_sum, hF.P_row, mul_one] at h
  linarith

omit [DecidableEq V] in
/-- Flow matching read through the stopping rule: `G = F_init + ((cont · G) P⋆)` with
`G := F_term + F⋆_out`. -/
theorem G_recursion (hF : F.IsGenFlow) (hFM : F.FlowMatching) (y : V) :
    F.fterm y + F.fout y
      = F.finit y + ∑ x, F.cont x * (F.fterm x + F.fout x) * F.P x y := by
  rw [← hFM y]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cont_mul hF x]

/-- **The occupation measure is dominated by `(F_term + F⋆_out)/F_init(𝒮)`**: every partial sum
of the unstopped laws `P(τ > n, s_{n+1} = y)` is at most `G(y)/Z`. -/
theorem partial_le (hF : F.IsGenFlow) (hFM : F.FlowMatching) (hZ : 0 < ∑ x, F.finit x) :
    ∀ (N : ℕ) (y : V),
      ∑ n ∈ Finset.range N, F.law n (y, false) ≤ (F.fterm y + F.fout y) / ∑ x, F.finit x
  | 0, y => by
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg (add_nonneg (hF.fterm_nonneg y) (hF.fout_nonneg y)) hZ.le
  | N + 1, y => by
    rw [Finset.sum_range_succ']
    simp only [law_succ_false]
    rw [Finset.sum_comm, law_zero_false]
    have hstep : ∀ x : V, ∑ n ∈ Finset.range N, F.cont x * F.law n (x, false) * F.P x y
        ≤ F.cont x * ((F.fterm x + F.fout x) / ∑ z, F.finit z) * F.P x y := by
      intro x
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (partial_le hF hFM hZ N x) (cont_nonneg hF x))
        (hF.P_nonneg x y)
    calc ∑ x, ∑ n ∈ Finset.range N, F.cont x * F.law n (x, false) * F.P x y
          + F.finit y / ∑ x, F.finit x
        ≤ ∑ x, F.cont x * ((F.fterm x + F.fout x) / ∑ z, F.finit z) * F.P x y
          + F.finit y / ∑ x, F.finit x := by
          gcongr with x
          exact hstep x
      _ = (F.fterm y + F.fout y) / ∑ x, F.finit x := by
          rw [G_recursion hF hFM y, add_div, Finset.sum_div]
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          ring

theorem summable_unstopped (hF : F.IsGenFlow) (hFM : F.FlowMatching) (hZ : 0 < ∑ x, F.finit x)
    (y : V) : Summable fun n => F.law n (y, false) :=
  summable_of_sum_range_le (fun n => law_nonneg hF n _) (partial_le hF hFM hZ · y)

/-- The sampler never stands at a state with `F_term + F⋆_out = 0`: the stopping convention
there is immaterial. -/
theorem unstopped_eq_zero_of_G_zero (hF : F.IsGenFlow) (hFM : F.FlowMatching)
    (hZ : 0 < ∑ x, F.finit x) {y : V} (hy : F.fterm y + F.fout y = 0) (n : ℕ) :
    F.law n (y, false) = 0 := by
  have h := partial_le hF hFM hZ (n + 1) y
  rw [hy, zero_div, Finset.sum_range_succ] at h
  have h0 : 0 ≤ ∑ k ∈ Finset.range n, F.law k (y, false) :=
    Finset.sum_nonneg fun k _ => law_nonneg hF k _
  exact le_antisymm (by linarith) (law_nonneg hF n _)

/-- `P(τ ≤ n, s_τ = y) = stop(y) · ∑_{k<n} P(τ > k, s_{k+1} = y)`. -/
theorem law_true_eq (n : ℕ) (y : V) :
    F.law n (y, true) = F.stop y * ∑ k ∈ Finset.range n, F.law k (y, false) := by
  induction n with
  | zero => simp only [law_zero_true, Finset.range_zero, Finset.sum_empty, mul_zero]
  | succ n ih => rw [law_succ_true, ih, Finset.sum_range_succ]; ring

/-- **`E(τ)` is finite and bounded** — `∑_n P(τ > n)` converges, with partial sums at most
`(F_term(𝒮) + F⋆_out(𝒮))/F_init(𝒮)`. -/
theorem summable_tailProb (hF : F.IsGenFlow) (hFM : F.FlowMatching) (hZ : 0 < ∑ x, F.finit x) :
    Summable F.tailProb :=
  summable_sum fun y _ => summable_unstopped hF hFM hZ y

theorem expectedTau_le (hF : F.IsGenFlow) (hFM : F.FlowMatching) (hZ : 0 < ∑ x, F.finit x) :
    F.expectedTau ≤ (∑ x, F.fout x) / (∑ x, F.finit x) + 1 := by
  have hbound : ∀ N, ∑ n ∈ Finset.range N, F.tailProb n
      ≤ (∑ x, F.fout x) / (∑ x, F.finit x) + 1 := by
    intro N
    unfold tailProb
    rw [Finset.sum_comm]
    calc ∑ y, ∑ n ∈ Finset.range N, F.law n (y, false)
        ≤ ∑ y, (F.fterm y + F.fout y) / ∑ x, F.finit x :=
          Finset.sum_le_sum fun y _ => partial_le hF hFM hZ N y
      _ = (∑ x, F.fout x) / (∑ x, F.finit x) + 1 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← mass_eq hF hFM, add_div,
            div_self hZ.ne', add_comm]
  exact Real.tsum_le_of_sum_range_le
    (fun n => Finset.sum_nonneg fun y _ => law_nonneg hF n _) hbound

/-- **Termination**: `P(τ > n) → 0`. -/
theorem tailProb_tendsto_zero (hF : F.IsGenFlow) (hFM : F.FlowMatching)
    (hZ : 0 < ∑ x, F.finit x) : Tendsto F.tailProb atTop (𝓝 0) :=
  (summable_tailProb hF hFM hZ).tendsto_atTop_zero

/-- The total occupation `Q(y) = ∑_n P(τ > n, s_{n+1} = y)` solves the occupation recursion
`Q = F_init/Z + (cont · Q) P⋆`. -/
theorem occ_recursion (hF : F.IsGenFlow) (hFM : F.FlowMatching) (hZ : 0 < ∑ x, F.finit x)
    (y : V) :
    ∑' n, F.law n (y, false)
      = F.finit y / (∑ x, F.finit x) + ∑ x, F.cont x * (∑' n, F.law n (x, false)) * F.P x y := by
  have hS : ∀ x, Tendsto (fun N => ∑ n ∈ Finset.range N, F.law n (x, false)) atTop
      (𝓝 (∑' n, F.law n (x, false))) :=
    fun x => (summable_unstopped hF hFM hZ x).hasSum.tendsto_sum_nat
  have hL := (hS y).comp (tendsto_add_atTop_nat 1)
  have hR : Tendsto (fun N => F.finit y / (∑ x, F.finit x)
      + ∑ x, F.cont x * (∑ n ∈ Finset.range N, F.law n (x, false)) * F.P x y) atTop
      (𝓝 (F.finit y / (∑ x, F.finit x) + ∑ x, F.cont x * (∑' n, F.law n (x, false)) * F.P x y)) :=
    tendsto_const_nhds.add (tendsto_finsetSum _ fun x _ =>
      ((hS x).const_mul (F.cont x)).mul_const (F.P x y))
  refine tendsto_nhds_unique hL (hR.congr fun N => ?_)
  simp only [Function.comp]
  rw [Finset.sum_range_succ', law_zero_false]
  simp only [law_succ_false]
  rw [Finset.sum_comm, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

/-- **The key step.** The gap `ν := G/Z − Q` between the dominating solution and the occupation
is invariant under the sub-stochastic kernel `cont · P⋆`, hence carried where `stop = 0`; so
`stop(y) Q(y) = stop(y) G(y)/Z = F_term(y)/Z` at every `y`. -/
theorem stop_mul_occ (hF : F.IsGenFlow) (hFM : F.FlowMatching) (hZ : 0 < ∑ x, F.finit x)
    (y : V) :
    F.stop y * ∑' n, F.law n (y, false) = F.fterm y / ∑ x, F.finit x := by
  set Z := ∑ x, F.finit x with hZdef
  set Q : V → ℝ := fun x => ∑' n, F.law n (x, false) with hQ
  set ν : V → ℝ := fun x => (F.fterm x + F.fout x) / Z - Q x with hν
  have hνnn : ∀ x, 0 ≤ ν x := fun x => by
    simp only [hν, hQ, sub_nonneg]
    exact Real.tsum_le_of_sum_range_le (fun n => law_nonneg hF n _)
      (partial_le hF hFM hZ · x)
  have hGZ : ∀ y, (F.fterm y + F.fout y) / Z
      = F.finit y / Z + ∑ x, F.cont x * ((F.fterm x + F.fout x) / Z) * F.P x y := by
    intro y
    rw [G_recursion hF hFM y, add_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hνrec : ∀ y, ν y = ∑ x, F.cont x * ν x * F.P x y := by
    intro y
    simp only [hν, hQ]
    rw [hGZ y, occ_recursion hF hFM hZ y, ← hZdef]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hmass : ∑ x, F.stop x * ν x = 0 := by
    have h1 : ∑ y, ν y = ∑ x, F.cont x * ν x := by
      rw [Finset.sum_congr rfl fun y _ => hνrec y, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum, hF.P_row, mul_one]
    simp only [stop, sub_mul, one_mul, Finset.sum_sub_distrib]
    rw [h1, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
    mul_nonneg (stop_nonneg hF x) (hνnn x)).mp hmass y (Finset.mem_univ y)
  simp only [hν, hQ] at hzero
  have hsm := stop_mul hF y
  have : F.stop y * ((F.fterm y + F.fout y) / Z) = F.fterm y / Z := by
    rw [← mul_div_assoc, hsm]
  change F.stop y * Q y = F.fterm y / Z
  linarith [show F.stop y * ((F.fterm y + F.fout y) / Z - Q y)
    = F.stop y * ((F.fterm y + F.fout y) / Z) - F.stop y * Q y by ring]

/-- **The law of the stopped state**: `P(τ ≤ n, s_τ = y) → F_term(y)/F_term(𝒮)`. -/
theorem law_true_tendsto (hF : F.IsGenFlow) (hFM : F.FlowMatching) (hZ : 0 < ∑ x, F.finit x)
    (y : V) :
    Tendsto (fun n => F.law n (y, true)) atTop (𝓝 (F.fterm y / ∑ x, F.fterm x)) := by
  rw [← mass_eq hF hFM, ← stop_mul_occ hF hFM hZ y]
  simp only [law_true_eq]
  exact ((summable_unstopped hF hFM hZ y).hasSum.tendsto_sum_nat).const_mul _

/-- The tail recursion: `P(τ > n+1) = P(τ > n) − P(τ = n+1)`, with
`P(τ = n+1) = ∑_y P(τ > n, s_{n+1} = y) stop(y)`: the tail probabilities decrease by exactly
the mass the stopping rule removes. -/
theorem tailProb_succ (hF : F.IsGenFlow) (n : ℕ) :
    F.tailProb (n + 1) = F.tailProb n - ∑ y, F.law n (y, false) * F.stop y := by
  unfold tailProb
  simp only [law_succ_false]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hF.P_row, mul_one]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by unfold stop; ring

/-- `P(τ ≤ n) = 1 − P(τ > n)`: at every time the sampler has either stopped or not. -/
theorem stopped_sum (hF : F.IsGenFlow) (hZ : 0 < ∑ x, F.finit x) (n : ℕ) :
    ∑ y, F.law n (y, true) = 1 - F.tailProb n := by
  have h := law_sum hF hZ n
  rw [Fintype.sum_prod_type] at h
  simp only [Fintype.sum_bool, Finset.sum_add_distrib] at h
  unfold tailProb
  linarith

/-- **`theo:sampling_theorem`, finite state space.** Let `F_init, F_term` be non-negative with
`F_term ≠ 0` and `(P⋆, F⋆_out)` a generative flow on a finite `V`. If the flow-matching constraint
`F_init + F⋆_out P⋆ = F_term + F⋆_out` holds, then

1. `F_init(𝒮) = F_term(𝒮)`;
2. `E(τ) = ∑_{n ≥ 0} P(τ > n)` converges;
3. `E(τ) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1`;
4. the sampler terminates: `P(τ > n) → 0`;
5. equivalently, `P(τ ≤ n) → 1`;
6. `s_τ ∼ F_term`: `P(τ ≤ n, s_τ = y) → F_term(y)/F_term(𝒮)` at every `y`. -/
theorem sampling_theorem (hF : F.IsGenFlow) (hterm : F.fterm ≠ 0) (hFM : F.FlowMatching) :
    (∑ x, F.finit x = ∑ x, F.fterm x) ∧
    Summable F.tailProb ∧
    F.expectedTau ≤ (∑ x, F.fout x) / (∑ x, F.finit x) + 1 ∧
    Tendsto F.tailProb atTop (𝓝 0) ∧
    Tendsto (fun n => ∑ y, F.law n (y, true)) atTop (𝓝 1) ∧
    ∀ y, Tendsto (fun n => F.law n (y, true)) atTop (𝓝 (F.fterm y / ∑ x, F.fterm x)) := by
  have hmass := mass_eq hF hFM
  have hZ : 0 < ∑ x, F.finit x := by
    rw [hmass]
    obtain ⟨x₀, hx₀⟩ : ∃ x, F.fterm x ≠ 0 := by
      by_contra hc
      exact hterm (funext fun x => not_not.mp (not_exists.mp hc x))
    exact Finset.sum_pos' (fun i _ => hF.fterm_nonneg i)
      ⟨x₀, Finset.mem_univ _, (hF.fterm_nonneg x₀).lt_of_ne (Ne.symm hx₀)⟩
  have htail := tailProb_tendsto_zero hF hFM hZ
  refine ⟨hmass, summable_tailProb hF hFM hZ, expectedTau_le hF hFM hZ, htail, ?_,
    law_true_tendsto hF hFM hZ⟩
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub htail
  rw [sub_zero] at h
  exact h.congr fun n => (stopped_sum hF hZ n).symm

end FlowData

/-! ### The bound is not an equality -/

namespace Parked

/-- The retraction register's instance, two states: the answer `true` receives and emits unit
mass, and the parked state `false` carries outflow `40` on a self-loop that no initial mass ever
reaches. Flow matching is exact. -/
noncomputable def flow : FlowData Bool where
  finit := fun b => if b then 1 else 0
  fterm := fun b => if b then 1 else 0
  fout := fun b => if b then 0 else 40
  P := fun x y => if x = y then 1 else 0

theorem isGenFlow : flow.IsGenFlow where
  finit_nonneg b := by cases b <;> norm_num [flow]
  fterm_nonneg b := by cases b <;> norm_num [flow]
  fout_nonneg b := by cases b <;> norm_num [flow]
  P_nonneg x y := by unfold flow; dsimp only; split_ifs <;> norm_num
  P_row x := by cases x <;> simp [flow]

theorem flowMatching : flow.FlowMatching := by
  unfold FlowData.FlowMatching
  intro y
  cases y <;> norm_num [flow]

theorem fterm_ne : flow.fterm ≠ 0 := by
  intro h; have := congrFun h true; simp [flow] at this

theorem law_false_succ : ∀ (n : ℕ) (y : Bool), flow.law (n + 1) (y, false) = 0
  | 0, y => by
    rw [FlowData.law_succ_false]
    cases y <;> norm_num [FlowData.law_zero_false, FlowData.cont, flow]
  | n + 1, y => by
    rw [FlowData.law_succ_false]
    simp [law_false_succ n]

theorem tailProb_eq (n : ℕ) : flow.tailProb n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [FlowData.tailProb, FlowData.law_zero_false, flow]
  | succ n => simp [FlowData.tailProb, law_false_succ]

/-- **The bound of `theo:sampling_theorem` can be strict**: here `E(τ) = 1` while
`F⋆_out(𝒮)/F_init(𝒮) + 1 = 41`. The occupation measure is the *minimal* solution of its
recursion, and `F_term + F⋆_out` is merely *a* solution. -/
theorem strict : flow.expectedTau = 1 ∧
    (∑ x, flow.fout x) / (∑ x, flow.finit x) + 1 = 41 := by
  constructor
  · unfold FlowData.expectedTau
    rw [tsum_eq_single 0 fun n hn => by rw [tailProb_eq, if_neg hn], tailProb_eq, if_pos rfl]
  · simp [flow]; norm_num

/-- **`theo:sampling_theorem` is inhabited** (kb `0025`): the parked flow meets every hypothesis,
so the theorem applies to it, with a strict bound (`strict`). -/
theorem inhabited :
    (∑ x, flow.finit x = ∑ x, flow.fterm x) ∧
    Summable flow.tailProb ∧
    flow.expectedTau ≤ (∑ x, flow.fout x) / (∑ x, flow.finit x) + 1 ∧
    Tendsto flow.tailProb atTop (𝓝 0) ∧
    Tendsto (fun n => ∑ y, flow.law n (y, true)) atTop (𝓝 1) ∧
    ∀ y, Tendsto (fun n => flow.law n (y, true)) atTop (𝓝 (flow.fterm y / ∑ x, flow.fterm x)) :=
  FlowData.sampling_theorem isGenFlow fterm_ne flowMatching

end Parked
end GFNBounds.Core.Sampling
