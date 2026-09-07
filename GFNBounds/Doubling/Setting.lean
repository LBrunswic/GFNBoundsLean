import Mathlib

/-!
# The doubling graph: state space, backward policy, and invariant sequences

**`def:doubling_setting`** — `app_doubling.tex:13–84` (Definition 88 of the ICLR build).

Formalizes the standing setting of Appendix H of *Universality and Convergence of Generative
Flows*: the ladder graph carrying the source `s₀`, the states `1, 2, 3, …`, the sink `s_f` and
the forward edges `s₀→1`, `j→j+1`, `2j→j`, `j→s_f`, so that the *backward* chain at `j` either
decrements to `j−1` or doubles to `2j`; the loop closure adds the wrap `s_f→s₀`.

## The three modelling decisions

**`s₀` is the integer `0`.** `St.src` is a `@[match_pattern] abbrev` for `St.lad 0`, which is the
paper's own convention (`def:doubling_setting`: "`j−1 = 0` read as `s₀`", and again in
`lem:doubling_supersolution`, "`h(s_0) := 0`"). It makes the decrement uniformly
`lad (j+1) → lad j`, so the source is not a separate case in `prop:doubling_drift`,
`lem:doubling_supersolution`, the six-case identity of `lem:doubling_percut` or `lem:doubling_ramp`.
The sink keeps its own constructor: it genuinely has different dynamics (it fires the target row)
and it is a state of `λ`, of `L^p(λ)`, and of the `L^∞` ramp argument.

**`ε` stays a free function.** `lem:doubling_percut`, `theo:doubling_unbounded`, `lem:doubling_ramp`
and `prop:doubling_unsolvable` hypothesize `ε` abstractly — `ε(j) > 0` and `sup ε < 1` — and are
*not* confined to the standing range, which `def:doubling_setting` says in as many words at
`app_doubling.tex:36–39`. The family `ε_{c,s}(j) = c/(j+1)^s` of `eq:doubling_family` is therefore
one instance, supplied in `GFNBounds.Doubling.Range`, and never baked in here.

**`pstar` is total and in closed form**, not `∑' y, kern x y * f y`. It is the *function* action
`(P⋆ f)(x) = E(f(X₁) | X₀ = x)` of `lem:adjoint`(3), and writing it as a match means it carries no
integrability side condition: every proof that touches it is a case analysis on `St`. The `cap`
parameter carries the loop closure (`none`) and the truncation at `K` (`some K`) at once, which is
how the paper states `lem:doubling_excursion`, `lem:doubling_supersolution`, `prop:doubling_cut`
and `lem:doubling_percut` — each of them "on the loop closure and the truncation alike".

## SCOPE (disclosed)

This file is definitions only; it asserts no mathematics. Two things it deliberately does **not**
model. First, the *density* action `P` of `def:doubling_setting` is not defined here — only the
function action `P⋆`; they are mutually adjoint on `L²(λ)` by `lem:adjoint`(3), and that identity
belongs to `LpLayer`. Second, `Stat` carries positivity of `λ` as a **field** rather than deriving
it: `lem:doubling_irreducible` and `lem:doubling_truncation_irreducible` supply it, but every
downstream statement of the appendix quantifies over "an invariant probability", so positivity
belongs in the hypothesis and not in a global theorem.

Note that `Stat` is *not* the hypothesis of the decay results. `prop:doubling_cut`,
`theo:doubling_decay` and `theo:doubling_sharp` are stated for an arbitrary positive real sequence
satisfying the cut-balance recursion — no invariance, no normalisation, no positive recurrence —
and `cor:doubling_truncation` Step 4 relies on that, feeding them `λ^K` extended past the cap by
`1`. See `GFNBounds.Doubling.CutBalance` for the predicate those results actually use.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

/-- The states of the doubling graph `eq:counterexample_graph`.

`lad 0` **is** the source `s₀` (see `St.src`); `lad j` for `j ≥ 1` is the ladder state `j`;
`sink` is `s_f`. -/
inductive St where
  | lad : ℕ → St
  | sink : St
  deriving DecidableEq, Repr

namespace St

/-- The source `s₀`, which is the ladder index `0`. A `match_pattern` so that it may be used on
the left of the defining equations of `pstar`. -/
@[match_pattern] abbrev src : St := St.lad 0

/-- `St` is countable: `lad j ↦ j + 1` and `sink ↦ 0` is injective into `ℕ`. -/
instance : Countable St :=
  Function.Injective.countable (f := fun s => match s with | .lad j => j + 1 | .sink => 0)
    (by rintro (a | _) (b | _) h <;> simp_all)

instance : Inhabited St := ⟨.sink⟩

end St

/-- Whether the doubling edge out of the ladder state `j` is present.

`cap = none` is the loop closure, where every doubling edge is present. `cap = some K` is the
truncation at `K` of `def:doubling_setting`: the edge `j → 2j` is deleted when `2j > K`, the
decrement out of such a state then carrying probability `1`. -/
def HasDouble : Option ℕ → ℕ → Prop
  | none, _ => True
  | some K, j => 2 * j ≤ K

instance : ∀ (cap : Option ℕ) (j : ℕ), Decidable (HasDouble cap j)
  | none, _ => .isTrue trivial
  | some K, j => inferInstanceAs (Decidable (2 * j ≤ K))

@[simp] theorem hasDouble_none (j : ℕ) : HasDouble none j := trivial

@[simp] theorem hasDouble_some (K j : ℕ) : HasDouble (some K) j ↔ 2 * j ≤ K := Iff.rfl

/-- The doubling edge survives downward: if it is present at `m` it is present at every `j ≤ m`.
On the truncation this is `2j ≤ 2m ≤ K`. It is why `lem:doubling_percut`'s single hypothesis
`2m ≤ K` (the paper's `m ≤ K/2`) covers the whole window `W(m)` as well as `m` itself. -/
theorem hasDouble_mono {cap : Option ℕ} {m j : ℕ} (h : HasDouble cap m) (hj : j ≤ m) :
    HasDouble cap j := by
  cases cap with
  | none => trivial
  | some K =>
      have h' : 2 * m ≤ K := h
      show 2 * j ≤ K
      omega

/-- The states of the chain in play.

On the loop closure (`cap = none`) every state of `St`. On the truncation at `K` the `K + 2`
states `{s₀, 1, …, K, s_f}` of `lem:doubling_truncation_irreducible`: the ladder states above `K`
carry no incoming edge from within the chain — a decrement from `j ≤ K` lands at most at `K − 1`
and a doubling that survives lands at `2j ≤ K` — so they are unreachable, and the invariant
probability vanishes on them.

This is why `Stat` below carries positivity only **on chain** and vanishing off it, rather than
global positivity: `St` is one type serving two chains, and the truncation genuinely does not live
on all of it. -/
def OnChain : Option ℕ → St → Prop
  | none, _ => True
  | some K, .lad j => j ≤ K
  | some _, .sink => True

instance : ∀ (cap : Option ℕ) (x : St), Decidable (OnChain cap x)
  | none, _ => .isTrue trivial
  | some K, .lad j => inferInstanceAs (Decidable (j ≤ K))
  | some _, .sink => .isTrue trivial

@[simp] theorem onChain_none (x : St) : OnChain none x := trivial
@[simp] theorem onChain_sink (cap : Option ℕ) : OnChain cap .sink := by cases cap <;> trivial
@[simp] theorem onChain_some_lad (K j : ℕ) : OnChain (some K) (.lad j) ↔ j ≤ K := Iff.rfl

/-- Where a surviving doubling edge lands is on the chain: on the truncation that is exactly the
content of `HasDouble`, `2j ≤ K`. -/
theorem onChain_double {cap : Option ℕ} {j : ℕ} (h : HasDouble cap j) :
    OnChain cap (.lad (2 * j)) := by
  cases cap with
  | none => trivial
  | some K => exact (h : 2 * j ≤ K)

/-- A ladder state at or below a state carrying its doubling edge is on the chain. -/
theorem onChain_lad_of_hasDouble {cap : Option ℕ} {m j : ℕ} (h : HasDouble cap m) (hj : j ≤ m) :
    OnChain cap (.lad j) := by
  cases cap with
  | none => trivial
  | some K =>
      have h' : 2 * m ≤ K := h
      show j ≤ K
      omega

/-- The cut window `W(m) = {⌈m/2⌉, …, m−1}` of `eq:doubling_window`.

It is the set of ladder states whose doubling edge lands at or above `m` while the state itself
lies below `m` — the states that carry mass across the cut at `m`. Shared by
`lem:doubling_percut` and `def:doubling_decay_notation`, which use the same window. -/
def window (m : ℕ) : Finset ℕ := Finset.Ico ((m + 1) / 2) m

theorem mem_window {m j : ℕ} : j ∈ window m ↔ (m + 1) / 2 ≤ j ∧ j < m := Finset.mem_Ico

theorem window_lt {m j : ℕ} (h : j ∈ window m) : j < m := (mem_window.mp h).2

/-- The standing hypotheses of `def:doubling_setting`, minus the family.

The target row `P̂_B(s_f → ·)` is finitely supported **by hypothesis** (`row_supp`), so every
expression involving it is a `Finset.sum` and never a `tsum`; that kills a class of summability
side conditions before it appears.

`epsMax` is a field rather than `⨆ j, eps j` because the appendix only ever uses
`ε(j) ≤ ε_max < 1`, and an `iSup` in `ℝ` would drag `BddAbove` bookkeeping through every proof.
`lem:doubling_range` supplies `ε_max = c·2^(-s)` for the family. -/
structure Setting where
  /-- The target row is supported in `{1, …, d}`. -/
  d : ℕ
  d_pos : 1 ≤ d
  /-- `ε(j)`, the doubling probability out of the ladder state `j`. Used only at `j ≥ 1`. -/
  eps : ℕ → ℝ
  eps_pos : ∀ ⦃j⦄, 1 ≤ j → 0 < eps j
  /-- An upper bound for `ε`, strictly below `1`. -/
  epsMax : ℝ
  eps_le : ∀ ⦃j⦄, 1 ≤ j → eps j ≤ epsMax
  epsMax_lt_one : epsMax < 1
  /-- The target row `P̂_B(s_f → ·)`, a probability supported in `{1, …, d}`. -/
  row : ℕ → ℝ
  row_nonneg : ∀ j, 0 ≤ row j
  row_supp : ∀ ⦃j⦄, row j ≠ 0 → 1 ≤ j ∧ j ≤ d
  row_sum : ∑ j ∈ Finset.Icc 1 d, row j = 1

namespace Setting

variable (S : Setting)

/-- `j̄`, the mean of the target row (`def:doubling_setting`). -/
noncomputable def jbar : ℝ := ∑ j ∈ Finset.Icc 1 S.d, (j : ℝ) * S.row j

theorem epsMax_pos : 0 < S.epsMax := lt_of_lt_of_le (S.eps_pos S.d_pos) (S.eps_le S.d_pos)

theorem eps_lt_one ⦃j : ℕ⦄ (hj : 1 ≤ j) : S.eps j < 1 :=
  lt_of_le_of_lt (S.eps_le hj) S.epsMax_lt_one

theorem one_sub_eps_pos ⦃j : ℕ⦄ (hj : 1 ≤ j) : 0 < 1 - S.eps j := by
  have := S.eps_lt_one hj; linarith

end Setting

/-- The function action `(P⋆ f)(x) = E(f(X₁) | X₀ = x)` of the backward kernel, in closed form.

This is `P⋆` of `def:doubling_setting`, which `lem:adjoint`(3) identifies as the function action
of the backward kernel `T` — the density action of the forward policy of the balanced flow.

The three cases are the three kinds of state. From the source the chain wraps to the sink with
probability one. From a ladder state `j ≥ 1` it doubles with probability `ε(j)` when that edge is
present and decrements otherwise, the decrement carrying the whole mass when the doubling edge has
been truncated away. From the sink it fires the target row. -/
noncomputable def pstar (S : Setting) (cap : Option ℕ) (f : St → ℝ) : St → ℝ
  | .lad 0 => f .sink
  | .lad (j + 1) =>
      if HasDouble cap (j + 1) then
        S.eps (j + 1) * f (.lad (2 * (j + 1))) + (1 - S.eps (j + 1)) * f (.lad j)
      else
        f (.lad j)
  | .sink => ∑ k ∈ Finset.Icc 1 S.d, S.row k * f (.lad k)

variable {S : Setting} {cap : Option ℕ} {f g : St → ℝ}

@[simp] theorem pstar_src : pstar S cap f .src = f .sink := rfl

@[simp] theorem pstar_sink :
    pstar S cap f .sink = ∑ k ∈ Finset.Icc 1 S.d, S.row k * f (.lad k) := rfl

theorem pstar_lad_succ (j : ℕ) :
    pstar S cap f (.lad (j + 1)) =
      if HasDouble cap (j + 1) then
        S.eps (j + 1) * f (.lad (2 * (j + 1))) + (1 - S.eps (j + 1)) * f (.lad j)
      else f (.lad j) := rfl

/-- The doubling case of `pstar`, stated at a ladder index `j ≥ 1` rather than at `j + 1`. -/
theorem pstar_lad_of_hasDouble {j : ℕ} (hj : 1 ≤ j) (h : HasDouble cap j) :
    pstar S cap f (.lad j) =
      S.eps j * f (.lad (2 * j)) + (1 - S.eps j) * f (.lad (j - 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, (Nat.succ_pred_eq_of_pos hj).symm⟩
  simp [pstar_lad_succ, h]

/-- The truncated case of `pstar`: with the doubling edge deleted, the decrement carries `1`. -/
theorem pstar_lad_of_not_hasDouble {j : ℕ} (hj : 1 ≤ j) (h : ¬ HasDouble cap j) :
    pstar S cap f (.lad j) = f (.lad (j - 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, (Nat.succ_pred_eq_of_pos hj).symm⟩
  simp [pstar_lad_succ, h]

theorem pstar_add : pstar S cap (f + g) = pstar S cap f + pstar S cap g := by
  funext x
  rcases x with (_ | j) | _
  · rfl
  · by_cases h : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, h, if_true, Pi.add_apply]; ring
    · simp only [pstar_lad_succ, h, if_false, Pi.add_apply]
  · simp only [pstar_sink, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pstar_smul (c : ℝ) : pstar S cap (c • f) = c • pstar S cap f := by
  funext x
  rcases x with (_ | j) | _
  · rfl
  · by_cases h : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, h, if_true, Pi.smul_apply, smul_eq_mul]; ring
    · simp only [pstar_lad_succ, h, if_false, Pi.smul_apply, smul_eq_mul]
  · simp only [pstar_sink, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- `P⋆` preserves non-negativity: it is an average over the one-step law. -/
theorem pstar_nonneg (hf : ∀ x, 0 ≤ f x) (x : St) : 0 ≤ pstar S cap f x := by
  rcases x with (_ | j) | _
  · exact hf _
  · by_cases h : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, h, if_true]
      have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
      have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
      exact add_nonneg (mul_nonneg h1 (hf _)) (mul_nonneg h2 (hf _))
    · simp only [pstar_lad_succ, h, if_false]; exact hf _
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (S.row_nonneg k) (hf _)

/-- `P⋆` is a contraction of the sup norm: it is an average, so it cannot enlarge the range.
This is the `p = ∞` case of `lem:doubling_operator`(1), which is all the `tsum` manipulations
below need. -/
theorem pstar_bounded {C : ℝ} (hC : ∀ x, |f x| ≤ C) (x : St) : |pstar S cap f x| ≤ C := by
  rcases x with (_ | j) | _
  · exact hC _
  · by_cases h : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, h, if_true]
      have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
      have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
      calc |S.eps (j+1) * f (.lad (2*(j+1))) + (1 - S.eps (j+1)) * f (.lad j)|
          ≤ |S.eps (j+1) * f (.lad (2*(j+1)))| + |(1 - S.eps (j+1)) * f (.lad j)| :=
            abs_add_le _ _
        _ ≤ S.eps (j+1) * C + (1 - S.eps (j+1)) * C := by
            rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
            gcongr <;> [exact hC _; exact hC _]
        _ = C := by ring
    · simp only [pstar_lad_succ, h, if_false]; exact hC _
  · simp only [pstar_sink]
    calc |∑ k ∈ Finset.Icc 1 S.d, S.row k * f (.lad k)|
        ≤ ∑ k ∈ Finset.Icc 1 S.d, |S.row k * f (.lad k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 S.d, S.row k * C := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (S.row_nonneg k)]
          exact mul_le_mul_of_nonneg_left (hC _) (S.row_nonneg k)
      _ = C := by rw [← Finset.sum_mul, S.row_sum, one_mul]

/-- `P⋆` fixes the constants: the rows are probabilities. This is the statement that the constants
are `0`-flows, and it is what makes `Π` commute with `P⋆`. -/
@[simp] theorem pstar_const (c : ℝ) : pstar S cap (fun _ => c) = fun _ => c := by
  funext x
  rcases x with (_ | j) | _
  · rfl
  · by_cases h : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, h, if_true]; ring
    · simp only [pstar_lad_succ, h, if_false]
  · simp [← Finset.sum_mul, S.row_sum]


/-- An invariant probability of the chain in play — `λ` of `def:doubling_setting`.

Positivity is **on chain**, and `λ` vanishes off it; see `OnChain`. On the loop closure
`OnChain` is vacuous and this is the paper's "positive at every state".

Invariance is carried in the **integral** form `∫ P⋆f dλ = ∫ f dλ` against bounded `f`, which is
the form every downstream use consumes (`prop:doubling_cut` tests it against `1_A`) and which
needs no summability side condition at the point of use. The pointwise form `λT = λ` is
equivalent on a countable space; that bridge is `Stat.of_pointwise`, and nothing below is blocked
while it is open.

Positivity is a field rather than a theorem because every statement of the appendix downstream of
`lem:doubling_irreducible` quantifies over "an invariant probability" — the existence question is
`prop:doubling_phase`, which is separate and, for the family, hard. -/
structure Stat (S : Setting) (cap : Option ℕ) where
  lam : St → ℝ
  nonneg : ∀ x, 0 ≤ lam x
  pos : ∀ ⦃x⦄, OnChain cap x → 0 < lam x
  vanish : ∀ ⦃x⦄, ¬ OnChain cap x → lam x = 0
  summable : Summable lam
  total : ∑' x, lam x = 1
  inv : ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) →
          ∑' x, lam x * pstar S cap f x = ∑' x, lam x * f x

namespace Stat

variable {S : Setting} {cap : Option ℕ} (L : Stat S cap)

/-- `λ · f` is summable whenever `f` is bounded — the workhorse behind every `tsum` manipulation
in the norm estimates. -/
theorem summable_mul {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) : Summable (fun x => L.lam x * f x) := by
  obtain ⟨C, hC⟩ := hf
  refine Summable.of_norm_bounded (g := fun x => C * L.lam x) (L.summable.mul_left C) ?_
  intro x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (L.nonneg x)]
  exact mul_le_mul_of_nonneg_left (hC x) (L.nonneg x) |>.trans_eq (by ring)

/-- The invariance identity, rearranged: the `λ`-integral of the flow-matching defect
`(Id − P⋆)f` vanishes for every bounded `f`. This is the form `prop:doubling_cut` uses. -/
theorem tsum_sub_pstar {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) :
    ∑' x, L.lam x * (f x - pstar S cap f x) = 0 := by
  have hb : ∃ C, ∀ x, |pstar S cap f x| ≤ C := by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, fun x => pstar_bounded hC x⟩
  have := L.inv f hf
  have hs1 := L.summable_mul hf
  have hs2 := L.summable_mul hb
  simp only [mul_sub]
  rw [Summable.tsum_sub hs1 hs2, this, sub_self]

end Stat

end GFNBounds.Doubling
