import GFNBounds.Silva.PathSpaceMarkov

/-!
# `rem:path_space` on every marked graph: `sup_{p_F} M' = +∞` over full-support Markov policies

**`rem:path_space`** — `silva_comparison.tex` (a remark; no proof environment; the label is the
anchor, kb 0036). Quoted from the working tree of 2026-09-19, which was being reworded the same
night through `/writer`:

> When a cycle lies on the trajectories into a state `x`, these are infinitely many, and, for a
> backward policy of full support, both `inf_τ p_B(τ|x) = 0` and `sup_{p_F} M' = +∞` follow from
> that. The infimum vanishes because `p_B(·|x)` is a probability charging each of them. The
> supremum is infinite because `p_B(·|x)` is summable: along the trajectories `τ_n` that wind `n`
> times around the cycle, `liminf_{n→∞} n p_B(τ_n|x) = 0`, while for each `n` some full-support
> forward policy, leaving the cycle with probability `1/(n+2)` at the state where `τ_n` leaves it,
> has `p_F(τ_n) ≥ c/(n+2)`, with `c > 0` depending on the graph, the cycle and `x` but not on `n`
> — `M'` being read with the formula of Proposition `prop:silva_explicit`. The infimum alone would
> not give the supremum, since every forward policy has `p_F(τ_n) ≤ 1/(n+1)`.

`Silva/PathSpaceMarkov.lean` certifies `sup_{p_F} M' = +∞` on `𝒞_N` over full-support Markov
forward policies, and `Silva/Remarks.lean` on every graph over full-support **trajectory laws**
(`exists_ratio_gt_walksInto`). This file certifies it **on every finite marked graph over
full-support Markov forward policies**, for a backward law `p_B(·|x)` that is summable and positive
on the walks into `x` — in particular the law of any full-support Markov backward policy — together
with every step of the mechanism the remark states.

## What is proved

| paper | here |
|---|---|
| a closed walk on the trajectories into `x` yields a simple cycle on them (a shortest closed walk among the states reachable from `s₀` and reaching `x`; not in general a sub-cycle of the given one) | `closedIn_of_list`, `exists_simpleCycle` (a closed walk of minimal length visits no state twice) |
| "the trajectories `τ_n` that wind `n` times around the cycle" | `exists_pumped_of_simpleCycle` (around any given simple cycle), `exists_pumped`: enter the simple cycle at the first state of it met from `s₀` (`first_entry`), wind, leave at the last state of it met before `x` (`last_exit`); an injective family of walks into `x` |
| `liminf_n n p_B(τ_n|x) = 0`, from summability | `exists_pumped_liminf` (via `frequently_succ_mul_lt`), for every summable non-negative `p_B(·|x)` |
| "some full-support forward policy, leaving the cycle with probability `1/(n+2)` …, has `p_F(τ_n) ≥ c/(n+2)`" | `exists_pumped` / `exists_pumped_liminf`: `cycPolicy G C a` with `a = (m+1)/(m+2)`, `m` the number of cycle steps of `τ_k`; `p_F(τ_k) > c₀/(k+1)`, `c₀ > 0` independent of `k` (`one_div_three_lt`) |
| "every forward policy has `p_F(τ_n) ≤ 1/(n+1)`" | `exists_pumped` / `exists_pumped_liminf`: every full-support Markov policy has `p_F(τ_k) ≤ 1/(k+1)` (`pow_mul_one_sub_le`, `cnt_ge_mul`, `fsm_pair`) |
| **`sup_{p_F} M' = +∞`** over full-support Markov forward policies | **`exists_markov_ratio_gt`**, `markov_ratio_not_bddAbove`; in Silva's setting (`p_B` from a full-support Markov backward policy) **`exists_markov_ratio_gt_backward`**, `markov_ratio_not_bddAbove_backward` |
| a full-support backward policy: `p_B(·|x)` charges each trajectory, and is summable | `backProb_pos`, `summable_backProb` (backward mass `≤ 1`, `sum_backProb_le_one`) |
| `inf_τ p_B(τ|x) = 0`, for a full-support Markov backward policy | `iInf_backProb_eq_zero` (for an arbitrary probability: `Remarks.iInf_pB_walksInto_eq_zero`) |
| the policy class is inhabited, and so are the hypotheses | `cycPolicy_isFullSupportMarkov`, `exists_isFullSupportMarkovBackward`; `inhabit_markov_general` on `𝒞₂` |

## SCOPE (disclosed)

* **Finite graphs.** The state space is a `Fintype`, as in the framework of `silvageneralization`
  that the remark discusses; the graph is a `MarkedGraph` (`s₀` receives no edge, `s_f` emits
  none). Nothing else is assumed of it: no acyclicity (the point of the sentence), no
  path-connectedness.
* **Trajectories into `x`** are walks `τ` from `s₀` to `x` (`Remarks.walksInto`), and
  `p_F(τ) := pathProb pol (τ ++ [s_f])`, the probability that `pol` samples `τ` and then
  terminates at `x`; the edge `x → s_f` is the hypothesis `hxs`. "A cycle lies on the trajectories
  into `x`" is read as in `Remarks.walksInto_infinite`: some walk from `s₀` to `x` visits a state
  `v` carrying a closed walk `v :: c`.
* **Full-support Markov forward policy** (`IsFullSupportMarkov`): positive on every edge, zero off
  the edges, and a probability on the out-edges of every state that has one. The class does not
  assert that the induced law on complete trajectories has mass `1` (not used; on a graph with
  dead ends it need not). The same holds of `IsFullSupportMarkovBackward` on the in-edges.
* **`p_B(·|x)`.** `exists_markov_ratio_gt` asks only that `p_B` be positive on every walk into `x`
  and summable over them — weaker than the paper's "a probability charging each of them", which it
  contains. `exists_markov_ratio_gt_backward` takes Silva's Markov backward policy and derives
  both properties; `summable_backProb` proves the backward mass `≤ 1` (that it equals `1` is not
  proved and not used).
* **`= +∞` is delivered as unboundedness of the ratio** `p_F(τ)/p_B(τ|x)` over the policies and
  the trajectories into `x`, as in `Remarks.exists_ratio_gt_walksInto`: `M' ≥ M ≥` that ratio, and
  on an infinite trajectory set `M'` is only "read with the formula of `prop:silva_explicit`" — the
  paper says so itself.
* **The winding index.** The paper's `τ_n` "wind `n` times around the cycle" through a cycle it
  does not fix; here it is any **simple** cycle on the trajectories into `x`
  (`exists_pumped_of_simpleCycle`); from a given closed walk, `exists_simpleCycle` supplies one of
  minimal length, which need not be a sub-cycle of it. For a non-simple closed walk the paper's
  lower bound fails under Markov policies (a figure-eight at `v` forces `p_F ≤ 4^{-n}`), so the
  paper's cycle is read as simple; `τ_k` winds `k` full extra turns, and the constants read
  `c₀/(k+1)` and `1/(k+1)` for the paper's
  `c/(n+2)` and `1/(n+1)`. The policy of the lower bound leaves the cycle with probability at least
  `(1 − a)/|𝒱|`, `1 − a = 1/(m+2)`, where `m` is the number of cycle steps of `τ_k`, not exactly
  `1/(n+2)`: the paper's phrase is a description of the construction, and the certified content is
  the bound `p_F(τ_k) > c₀/(k+1)` with `c₀` independent of `k`.
* **The upper bound `≤ 1/(k+1)`** is over full-support Markov policies (the paper's "every forward
  policy" in this sentence means Markov: over trajectory laws it is false: a law may put mass
  arbitrarily close to 1 on `τ_k`). It is stated over **full-support** Markov policies, the class
  the supremum runs over. The proof uses only non-negativity and row sums (`fsm_nonneg`,
  `fsm_le_one`, `fsm_pair`), so it extends to every Markov policy, but that extension is not
  stated.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| a finite graph (the framework of `silvageneralization`) | ✓ `[Fintype V]`, `G : MarkedGraph V` |
| a cycle lies on the trajectories into `x` | ✓ `hw`, `hv`, `hcE`, `hc` |
| `x` is a terminal state | ✓ `hxs : G.Edge x G.snk` |
| a backward policy of full support; `p_B(·|x)` a probability charging each trajectory into `x` | ✓ `IsFullSupportMarkovBackward G pb` (`…_backward`); ⚠ weakened to "positive and summable" in `exists_markov_ratio_gt` (a more general statement) |
| `p_F` a full-support forward policy | ✓ `IsFullSupportMarkov G pol`, Markov |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Silva.PathSpaceMarkovGeneral

open GFNBounds.Graph GFNBounds.Silva.Remarks Finset

/-! ## Path probabilities along concatenations -/

section Lists

variable {S : Type*}

/-- `pathProb` is multiplicative at a shared state. -/
theorem pathProb_append_cons (pol : S → S → ℝ) :
    ∀ (l : List S) (b : S) (r : List S),
      pathProb pol (l ++ b :: r) = pathProb pol (l ++ [b]) * pathProb pol (b :: r)
  | [], b, r => by simp only [List.nil_append, pathProb, one_mul]
  | [a], b, r => by simp only [List.cons_append, List.nil_append, pathProb, mul_one]
  | a :: a' :: l, b, r => by
      have ih := pathProb_append_cons pol (a' :: l) b r
      simp only [List.cons_append] at ih ⊢
      rw [pathProb, ih, pathProb, mul_assoc]

/-- **A walk whose states before the last all lie off `P`** has probability at least `β^{#steps}`
under a policy giving every edge out of a state off `P` at least `β`. -/
theorem pathProb_ge_pow {pol : S → S → ℝ} {E : S → S → Prop} {β : ℝ} (hβ : 0 ≤ β)
    {P : S → Prop} (hstep : ∀ s s', E s s' → ¬ P s → β ≤ pol s s') :
    ∀ (l : List S) (b : S), (l ++ [b]).IsChain E → (∀ y ∈ l, ¬ P y) →
      β ^ l.length ≤ pathProb pol (l ++ [b])
  | [], b, _, _ => by simp only [List.nil_append, pathProb, List.length_nil, pow_zero, le_refl]
  | [a], b, h, hP => by
      simp only [List.cons_append, List.nil_append, List.isChain_cons_cons] at h
      simp only [List.cons_append, List.nil_append, pathProb, mul_one, List.length_singleton,
        pow_one]
      exact hstep a b h.1 (hP a List.mem_cons_self)
  | a :: c :: l, b, h, hP => by
      simp only [List.cons_append, List.isChain_cons_cons] at h
      have ih := pathProb_ge_pow hβ hstep (c :: l) b (by simpa only [List.cons_append] using h.2)
        (fun y hy => hP y (List.mem_cons_of_mem _ hy))
      have hac : β ≤ pol a c := hstep a c h.1 (hP a List.mem_cons_self)
      simp only [List.cons_append] at ih ⊢
      rw [pathProb, List.length_cons, pow_succ']
      exact mul_le_mul hac ih (pow_nonneg hβ _) (hβ.trans hac)

/-- The walk `q j → q (j+1) → ⋯ → q (j+n)` along a sequence of states. -/
def cycW (q : ℕ → S) : ℕ → ℕ → List S
  | j, 0 => [q j]
  | j, n + 1 => q j :: cycW q (j + 1) n

theorem cycW_eq_cons (q : ℕ → S) (j n : ℕ) : ∃ r, cycW q j n = q j :: r := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n => exact ⟨cycW q (j + 1) n, rfl⟩

theorem cycW_eq_append (q : ℕ → S) (j n : ℕ) : ∃ r, cycW q j n = r ++ [q (j + n)] := by
  induction n generalizing j with
  | zero => exact ⟨[], by simp only [cycW, add_zero, List.nil_append]⟩
  | succ n ih =>
      obtain ⟨r, hr⟩ := ih (j + 1)
      refine ⟨q j :: r, ?_⟩
      rw [cycW, hr, show j + 1 + n = j + (n + 1) by omega, List.cons_append]

theorem length_cycW (q : ℕ → S) (j n : ℕ) : (cycW q j n).length = n + 1 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => rw [cycW, List.length_cons, ih]

theorem isChain_cycW {E : S → S → Prop} {q : ℕ → S} (hq : ∀ m, E (q m) (q (m + 1))) (j n : ℕ) :
    (cycW q j n).IsChain E := by
  induction n generalizing j with
  | zero => exact List.IsChain.singleton _
  | succ n ih =>
      obtain ⟨r, hr⟩ := cycW_eq_cons q (j + 1) n
      have h := ih (j + 1)
      rw [cycW, hr]
      rw [hr] at h
      exact List.IsChain.cons_cons (hq j) h

theorem pathProb_cycW_ge {pol : S → S → ℝ} {q : ℕ → S} {a : ℝ} (ha : 0 ≤ a)
    (hq : ∀ m, a ≤ pol (q m) (q (m + 1))) (j n : ℕ) : a ^ n ≤ pathProb pol (cycW q j n) := by
  induction n generalizing j with
  | zero => simp only [cycW, pathProb, pow_zero, le_refl]
  | succ n ih =>
      obtain ⟨r, hr⟩ := cycW_eq_cons q (j + 1) n
      have h := ih (j + 1)
      rw [cycW, hr]
      rw [hr] at h
      rw [pathProb, pow_succ']
      exact mul_le_mul (hq j) h (pow_nonneg ha _) (ha.trans (hq j))


/-- **The exit step**: a walk `f → t₁ → ⋯ → t_s → z` whose first step has probability at least `γ`
and whose states `t_i` lie off `P` has probability at least `γ β^s`. -/
theorem pathProb_exit_ge {pol : S → S → ℝ} {E : S → S → Prop} {β γ : ℝ} (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) {P : S → Prop} (hstep : ∀ s s', E s s' → ¬ P s → β ≤ pol s s') {f z : S}
    (hexit : ∀ s', E f s' → γ ≤ pol f s') :
    ∀ T : List S, (f :: (T ++ [z])).IsChain E → (∀ y ∈ T, ¬ P y) →
      γ * β ^ T.length ≤ pathProb pol (f :: (T ++ [z]))
  | [], h, _ => by
      simp only [List.nil_append, List.isChain_cons_cons] at h
      simp only [List.nil_append, pathProb, List.length_nil, pow_zero, mul_one]
      exact hexit z h.1
  | t :: T, h, hoff => by
      simp only [List.cons_append, List.isChain_cons_cons] at h
      have ih := pathProb_ge_pow hβ hstep (t :: T) z (by simpa only [List.cons_append] using h.2)
        hoff
      have hft := hexit t h.1
      simp only [List.cons_append] at ih ⊢
      rw [pathProb]
      exact mul_le_mul hft ih (pow_nonneg hβ _) (hγ.trans hft)

/-- `pathProb` of a walk `P ++ Z ++ T ++ [z]` through a middle segment `Z = e :: ⋯ = ⋯ ++ [f]`. -/
theorem pathProb_concat (pol : S → S → ℝ) (P T : List S) {Z r₁ r₂ : List S} {e f : S} (z : S)
    (h₁ : Z = e :: r₁) (h₂ : Z = r₂ ++ [f]) :
    pathProb pol (P ++ Z ++ T ++ [z]) =
      pathProb pol (P ++ [e]) * pathProb pol Z * pathProb pol (f :: (T ++ [z])) := by
  have e1 : P ++ Z ++ T ++ [z] = P ++ e :: (r₁ ++ (T ++ [z])) := by
    rw [h₁]; simp only [List.append_assoc, List.cons_append]
  have e2 : e :: (r₁ ++ (T ++ [z])) = r₂ ++ f :: (T ++ [z]) := by
    rw [← List.cons_append, ← h₁, h₂, List.append_assoc, List.singleton_append]
  rw [e1, pathProb_append_cons pol P e, e2, pathProb_append_cons pol r₂ f, ← h₂, mul_assoc]

/-- **The concatenation is a walk from `s` to `x`.** -/
theorem mem_walksInto_concat {E : S → S → Prop} {s x : S} {P T Z r₁ r₂ : List S} {e f : S}
    (hP : (P ++ [e]).IsChain E) (hPh : (P ++ [e]).head? = some s) (hZ : Z.IsChain E)
    (h₁ : Z = e :: r₁) (h₂ : Z = r₂ ++ [f]) (hT : (f :: T).IsChain E)
    (hTl : (f :: T).getLast? = some x) : P ++ Z ++ T ∈ walksInto E s x := by
  have e1 : P ++ Z ++ T = P ++ e :: (r₁ ++ T) := by
    rw [h₁]; simp only [List.append_assoc, List.cons_append]
  have e2 : P ++ Z ++ T = (P ++ r₂) ++ f :: T := by
    rw [h₂]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  have e3 : e :: (r₁ ++ T) = r₂ ++ f :: T := by
    rw [← List.cons_append, ← h₁, h₂, List.append_assoc, List.singleton_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    rw [List.head?_append] at hPh ⊢
    simpa only [List.head?_cons] using hPh
  · rw [e2, List.getLast?_append, hTl, Option.some_or]
  · rw [e1, List.isChain_split, e3]
    refine ⟨hP, ?_⟩
    rw [List.isChain_split, ← h₂]
    exact ⟨hZ, hT⟩

end Lists

/-! ## Reachability, first entry and last exit -/

section Reach

variable {S : Type*} {E : S → S → Prop}

/-- Every state of a walk is reachable from its head. -/
theorem reach_of_mem_of_head :
    ∀ {l : List S} {a b : S}, l.IsChain E → l.head? = some a → b ∈ l →
      Relation.ReflTransGen E a b
  | [], _, _, _, h, _ => by simp only [List.head?_nil, reduceCtorEq] at h
  | [c], a, b, _, h, hb => by
      simp only [List.head?_cons, Option.some.injEq] at h
      rw [List.mem_singleton] at hb
      subst h hb
      exact Relation.ReflTransGen.refl
  | c :: d :: l, a, b, hch, h, hb => by
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      rw [List.isChain_cons_cons] at hch
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head hch.1
          (reach_of_mem_of_head hch.2 (List.head?_cons ..) hb')

/-- Every state of a walk reaches its last state. -/
theorem reach_of_mem_of_getLast :
    ∀ {l : List S} {b z : S}, l.IsChain E → l.getLast? = some z → b ∈ l →
      Relation.ReflTransGen E b z
  | [], _, _, _, h, _ => by simp only [List.getLast?_nil, reduceCtorEq] at h
  | [c], b, z, _, h, hb => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      rw [List.mem_singleton] at hb
      subst h hb
      exact Relation.ReflTransGen.refl
  | c :: d :: l, b, z, hch, h, hb => by
      rw [List.getLast?_cons_cons] at h
      rw [List.isChain_cons_cons] at hch
      have hd : Relation.ReflTransGen E d z := reach_of_mem_of_getLast hch.2 h List.mem_cons_self
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact Relation.ReflTransGen.head hch.1 hd
      · exact reach_of_mem_of_getLast hch.2 h hb'

/-- **First entry into `Q`**: a walk from `a` to a state of `Q` has a prefix `P ++ [e]` ending at
its first state `e` in `Q`. -/
theorem first_entry {Q : S → Prop} {a b : S} (h : Relation.ReflTransGen E a b) (hb : Q b) :
    ∃ P : List S, ∃ e, Q e ∧ (P ++ [e]).IsChain E ∧ (P ++ [e]).head? = some a ∧
      ∀ y ∈ P, ¬ Q y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], b, hb, List.IsChain.singleton _, rfl, fun y hy => absurd hy List.not_mem_nil⟩
  | @head a c hac _ ih =>
      by_cases hQa : Q a
      · exact ⟨[], a, hQa, List.IsChain.singleton _, rfl,
          fun y hy => absurd hy List.not_mem_nil⟩
      · obtain ⟨P, e, hQe, hch, hhead, hoff⟩ := ih
        refine ⟨a :: P, e, hQe, ?_, rfl, ?_⟩
        · rw [List.cons_append, List.isChain_cons]
          refine ⟨fun y hy => ?_, hch⟩
          rw [hhead, Option.mem_def, Option.some.injEq] at hy
          exact hy ▸ hac
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hQa
          · exact hoff y hy'

/-- **Last exit from `Q`**, the dichotomy form: a walk from `a` to `z` either has a suffix
`f :: T` from its last state `f` in `Q`, or avoids `Q` entirely. -/
theorem last_exit_or {Q : S → Prop} {a z : S} (h : Relation.ReflTransGen E a z) :
    (∃ f, Q f ∧ ∃ T : List S, (f :: T).IsChain E ∧ (f :: T).getLast? = some z ∧
      ∀ y ∈ T, ¬ Q y) ∨
    (∃ T : List S, (a :: T).IsChain E ∧ (a :: T).getLast? = some z ∧ ∀ y ∈ a :: T, ¬ Q y) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      by_cases hQ : Q z
      · exact Or.inl ⟨z, hQ, [], List.IsChain.singleton _, rfl,
          fun y hy => absurd hy List.not_mem_nil⟩
      · refine Or.inr ⟨[], List.IsChain.singleton _, rfl, fun y hy => ?_⟩
        rw [List.mem_singleton] at hy
        exact hy ▸ hQ
  | @head a c hac _ ih =>
      rcases ih with hl | ⟨T, hch, hlast, hoff⟩
      · exact Or.inl hl
      · have hch' : (a :: c :: T).IsChain E := List.IsChain.cons_cons hac hch
        have hlast' : (a :: c :: T).getLast? = some z := by
          rw [List.getLast?_cons_cons]; exact hlast
        by_cases hQa : Q a
        · exact Or.inl ⟨a, hQa, c :: T, hch', hlast', hoff⟩
        · refine Or.inr ⟨c :: T, hch', hlast', fun y hy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hQa
          · exact hoff y hy'

/-- **Last exit from `Q`**: a walk from a state of `Q` to `z` has a suffix `f :: T` from its last
state `f` in `Q`. -/
theorem last_exit {Q : S → Prop} {a z : S} (h : Relation.ReflTransGen E a z) (ha : Q a) :
    ∃ f, Q f ∧ ∃ T : List S, (f :: T).IsChain E ∧ (f :: T).getLast? = some z ∧
      ∀ y ∈ T, ¬ Q y := by
  rcases last_exit_or (Q := Q) h with hl | ⟨_, _, _, hoff⟩
  · exact hl
  · exact absurd ha (hoff a List.mem_cons_self)

end Reach

/-! ## Simple cycles, and their extraction from a closed walk -/

section Cycle

variable {S : Type*}

/-- **A simple cycle** `q 0 → q 1 → ⋯ → q (L−1) → q 0` of length `L ≥ 1`: an `L`-periodic sequence
of states, injective on one period, each state joined to the next by an edge. -/
structure SimpleCycle (E : S → S → Prop) where
  /-- The states, read periodically. -/
  q : ℕ → S
  /-- The length. -/
  L : ℕ
  L_pos : 0 < L
  periodic : ∀ m, q (m + L) = q m
  inj : ∀ i j, i < L → j < L → q i = q j → i = j
  edge : ∀ m, E (q m) (q (m + 1))

namespace SimpleCycle

variable {E : S → S → Prop} (C : SimpleCycle E)

theorem q_add_mul (m k : ℕ) : C.q (m + k * C.L) = C.q m := by
  induction k with
  | zero => rw [zero_mul, add_zero]
  | succ k ih => rw [Nat.succ_mul, ← add_assoc, C.periodic, ih]

theorem q_mod (m : ℕ) : C.q m = C.q (m % C.L) := by
  conv_lhs => rw [← Nat.mod_add_div m C.L, mul_comm]
  exact C.q_add_mul _ _

theorem q_eq_q_iff (i j : ℕ) : C.q i = C.q j ↔ i % C.L = j % C.L := by
  constructor
  · intro h
    rw [C.q_mod i, C.q_mod j] at h
    exact C.inj _ _ (Nat.mod_lt _ C.L_pos) (Nat.mod_lt _ C.L_pos) h
  · intro h
    rw [C.q_mod i, C.q_mod j, h]

open Classical in
/-- The successor of a state on the cycle (and the state itself off the cycle). -/
noncomputable def nxt (s : S) : S :=
  if h : ∃ m, C.q m = s then C.q (Classical.choose h + 1) else s

theorem nxt_q (m : ℕ) : C.nxt (C.q m) = C.q (m + 1) := by
  have h : ∃ n, C.q n = C.q m := ⟨m, rfl⟩
  rw [nxt, dif_pos h]
  have hs := Classical.choose_spec h
  rw [C.q_eq_q_iff] at hs ⊢
  rw [Nat.add_mod, hs, ← Nat.add_mod]

/-- Every state of the cycle is met within one period from any starting index. -/
theorem exists_lt_eq (j m : ℕ) : ∃ i < C.L, C.q (j + i) = C.q m := by
  have hr : j % C.L < C.L := Nat.mod_lt _ C.L_pos
  have hf : m % C.L < C.L := Nat.mod_lt _ C.L_pos
  have hj : j / C.L * C.L + j % C.L = j := Nat.div_add_mod' j C.L
  rw [C.q_mod m]
  by_cases hle : j % C.L ≤ m % C.L
  · refine ⟨m % C.L - j % C.L, by omega, ?_⟩
    rw [show j + (m % C.L - j % C.L) = m % C.L + j / C.L * C.L by omega, C.q_add_mul]
  · refine ⟨m % C.L + C.L - j % C.L, by omega, ?_⟩
    rw [show j + (m % C.L + C.L - j % C.L) = m % C.L + (j / C.L + 1) * C.L by
      rw [Nat.succ_mul]; omega, C.q_add_mul]

end SimpleCycle

/-- A closed walk `p 0 → p 1 → ⋯ → p n = p 0` of length `n ≥ 1` whose states all satisfy `R`. -/
def ClosedIn (E : S → S → Prop) (R : S → Prop) (n : ℕ) : Prop :=
  0 < n ∧ ∃ p : ℕ → S, p n = p 0 ∧ (∀ i < n, E (p i) (p (i + 1))) ∧ ∀ i, R (p i)

/-- **A closed walk in `R` yields a simple cycle in `R`**: a closed walk of minimal length among all
those staying in `R` visits no state twice. It is not in general a sub-cycle of the given walk. -/
theorem exists_simpleCycle {E : S → S → Prop} {R : S → Prop} {n : ℕ} (h : ClosedIn E R n) :
    ∃ C : SimpleCycle E, ∀ m, R (C.q m) := by
  classical
  have hex : ∃ n, ClosedIn E R n := ⟨n, h⟩
  obtain ⟨hLpos, p, hp0, hpE, hpR⟩ := Nat.find_spec hex
  set L := Nat.find hex with hL
  have hmin : ∀ m < L, ¬ ClosedIn E R m := fun m hm => Nat.find_min hex hm
  have key : ∀ i j, i < j → j < L → p i = p j → False := by
    intro i j hij hj hpij
    refine hmin (j - i) (by omega) ⟨by omega, fun t => p (i + t), ?_, fun t ht => ?_,
      fun t => hpR _⟩
    · simp only [add_zero, Nat.add_sub_cancel' hij.le, hpij]
    · exact hpE (i + t) (by omega)
  have hinj : ∀ i j, i < L → j < L → p i = p j → i = j := by
    intro i j hi hj hpij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (key i j hlt hj hpij).elim
    · exact heq
    · exact (key j i hgt hi hpij.symm).elim
  refine ⟨⟨fun m => p (m % L), L, hLpos, fun m => ?_, fun i j hi hj hij => ?_, fun m => ?_⟩,
    fun m => hpR _⟩
  · simp only [Nat.add_mod_right]
  · simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hij
    exact hinj i j hi hj hij
  have hi : m % L < L := Nat.mod_lt _ hLpos
  have hm1 : (m + 1) % L = (m % L + 1) % L := (Nat.mod_add_mod m L 1).symm
  show E (p (m % L)) (p ((m + 1) % L))
  rw [hm1]
  rcases Nat.lt_or_ge (m % L + 1) L with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
    exact hpE _ hi
  · have heq : m % L + 1 = L := by omega
    have hE := hpE _ hi
    rw [heq, hp0] at hE
    rw [heq, Nat.mod_self]
    exact hE

/-- A closed walk given as a list `v :: c` (`c` ending at `v`) is a `ClosedIn` walk. -/
theorem closedIn_of_list {E : S → S → Prop} {R : S → Prop} {v : S} {c : List S}
    (hcE : (v :: c).IsChain E) (hc : c.getLast? = some v) (hR : ∀ y ∈ v :: c, R y) :
    ClosedIn E R c.length := by
  obtain ⟨k, hk⟩ : ∃ k, c.length = k + 1 := by
    cases c with
    | nil => simp only [List.getLast?_nil, reduceCtorEq] at hc
    | cons a l => exact ⟨l.length, rfl⟩
  refine ⟨by omega, fun t => (v :: c).getD t v, ?_, fun i hi => ?_, fun t => ?_⟩
  · rw [List.getLast?_eq_getElem?, hk, Nat.add_sub_cancel] at hc
    simp only [List.getD_eq_getElem?_getD, hk, List.getElem?_cons_succ, hc,
      List.getElem?_cons_zero, Option.getD_some]
  · have hlen : i + 1 < (v :: c).length := by rw [List.length_cons]; omega
    beta_reduce
    rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ (by omega)]
    exact List.isChain_iff_getElem.mp hcE i hlen
  · beta_reduce
    by_cases ht : t < (v :: c).length
    · rw [List.getD_eq_getElem _ _ ht]
      exact hR _ (List.getElem_mem ht)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact hR _ List.mem_cons_self

end Cycle


/-! ## The loop-weighted Markov forward policy -/

section Policy

variable {V : Type*} [Fintype V] [DecidableEq V] (G : MarkedGraph V) [DecidableRel G.Edge]

omit [DecidableEq V] in
/-- The out-degree of `s` in `G`. -/
def outDeg (s : V) : ℕ := (univ.filter (G.Edge s)).card

omit [DecidableEq V] [DecidableRel G.Edge] in
/-- **A full-support Markov forward policy on `G`**: positive on every edge, zero off the edges,
and a probability on the successors of every state that has one. -/
def IsFullSupportMarkov (pol : V → V → ℝ) : Prop :=
  (∀ u v, G.Edge u v → 0 < pol u v) ∧ (∀ u v, ¬ G.Edge u v → pol u v = 0) ∧
    ∀ u, (∃ v, G.Edge u v) → ∑ v, pol u v = 1

variable {G}

omit [DecidableEq V] in
theorem outDeg_pos {s s' : V} (h : G.Edge s s') : (0 : ℝ) < (outDeg G s : ℝ) :=
  Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨s', Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)

omit [DecidableEq V] in
theorem outDeg_le (s : V) : (outDeg G s : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_univ (α := V)).le

variable (G)

open Classical in
/-- **The loop-weighted policy** `cycPolicy G C a`: at a state of the simple cycle `C` it takes the
cycle edge with extra weight `a` and spreads `1 − a` uniformly over all out-edges; off the cycle it
is uniform over the out-edges. It plays on an arbitrary graph the role `PathSpaceMarkov.cycPol`
plays on `𝒞_N` (it does not reduce to it: on `𝒞_N` it continues with `a + (1 − a)/2`). -/
noncomputable def cycPolicy (C : SimpleCycle G.Edge) (a : ℝ) (s s' : V) : ℝ :=
  if G.Edge s s' then
    (if ∃ m, C.q m = s then a * (if s' = C.nxt s then 1 else 0) + (1 - a) / (outDeg G s : ℝ)
      else 1 / (outDeg G s : ℝ))
  else 0

variable {G}

/-- **`cycPolicy G C a` is a full-support Markov forward policy** for `0 ≤ a < 1`. -/
theorem cycPolicy_isFullSupportMarkov (C : SimpleCycle G.Edge) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < 1) : IsFullSupportMarkov G (cycPolicy G C a) := by
  refine ⟨fun u v h => ?_, fun u v h => by rw [cycPolicy, if_neg h], fun u ⟨v, hv⟩ => ?_⟩
  · have hd := outDeg_pos h
    rw [cycPolicy, if_pos h]
    by_cases hQ : ∃ m, C.q m = u
    · rw [if_pos hQ]
      have : 0 ≤ a * (if v = C.nxt u then (1 : ℝ) else 0) :=
        mul_nonneg ha0 (by split_ifs <;> norm_num)
      have : 0 < (1 - a) / (outDeg G u : ℝ) := div_pos (by linarith) hd
      linarith
    · rw [if_neg hQ]
      exact div_pos one_pos hd
  · have hd := outDeg_pos hv
    have hdne : (outDeg G u : ℝ) ≠ 0 := hd.ne'
    simp only [cycPolicy]
    rw [← Finset.sum_filter]
    by_cases hQ : ∃ m, C.q m = u
    · simp only [hQ, if_true]
      obtain ⟨m, rfl⟩ := hQ
      have hmem : C.nxt (C.q m) ∈ univ.filter (G.Edge (C.q m)) := by
        rw [C.nxt_q]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.edge m⟩
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' _ _ (fun _ => (1 : ℝ)),
        if_pos hmem, Finset.sum_const, nsmul_eq_mul]
      change a * 1 + (outDeg G (C.q m) : ℝ) * ((1 - a) / (outDeg G (C.q m) : ℝ)) = 1
      field_simp
      ring
    · simp only [hQ, if_false]
      rw [Finset.sum_const, nsmul_eq_mul]
      change (outDeg G u : ℝ) * (1 / (outDeg G u : ℝ)) = 1
      field_simp

/-- Off the cycle, every edge has probability at least `1/|𝒱|`. -/
theorem cycPolicy_ge_off (C : SimpleCycle G.Edge) (a : ℝ) {s s' : V} (h : G.Edge s s')
    (hQ : ¬ ∃ m, C.q m = s) : 1 / (Fintype.card V : ℝ) ≤ cycPolicy G C a s s' := by
  rw [cycPolicy, if_pos h, if_neg hQ]
  exact one_div_le_one_div_of_le (outDeg_pos h) (outDeg_le s)

/-- Every edge has probability at least `(1 − a)/|𝒱|`. -/
theorem cycPolicy_ge_exit (C : SimpleCycle G.Edge) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {s s' : V} (h : G.Edge s s') : (1 - a) / (Fintype.card V : ℝ) ≤ cycPolicy G C a s s' := by
  have hd := outDeg_pos h
  have hle : (1 - a) / (Fintype.card V : ℝ) ≤ (1 - a) / (outDeg G s : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) hd (outDeg_le s)
  rw [cycPolicy, if_pos h]
  by_cases hQ : ∃ m, C.q m = s
  · rw [if_pos hQ]
    have : 0 ≤ a * (if s' = C.nxt s then (1 : ℝ) else 0) :=
      mul_nonneg ha0 (by split_ifs <;> norm_num)
    linarith
  · rw [if_neg hQ]
    have : (1 - a) / (outDeg G s : ℝ) ≤ 1 / (outDeg G s : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hd.le
    linarith

/-- Along the cycle, every step has probability at least `a`. -/
theorem cycPolicy_ge_cyc (C : SimpleCycle G.Edge) {a : ℝ} (ha1 : a ≤ 1) (m : ℕ) :
    a ≤ cycPolicy G C a (C.q m) (C.q (m + 1)) := by
  have hd := outDeg_pos (C.edge m)
  rw [cycPolicy, if_pos (C.edge m), if_pos ⟨m, rfl⟩, C.nxt_q, if_pos rfl, mul_one]
  have : 0 ≤ (1 - a) / (outDeg G (C.q m) : ℝ) := div_nonneg (by linarith) hd.le
  linarith

end Policy


/-! ## A Markov backward policy: `p_B(·|x)` is positive and summable on the walks into `x` -/

section Backward

variable {V : Type*} [Fintype V] (G : MarkedGraph V)

/-- **A full-support Markov backward policy on `G`**: `pb y z` is the probability of the backward
step from `y` to its parent `z`; positive on every edge `z → y`, zero off the edges, and a
probability on the parents of every state that has one. -/
def IsFullSupportMarkovBackward (pb : V → V → ℝ) : Prop :=
  (∀ y z, G.Edge z y → 0 < pb y z) ∧ (∀ y z, ¬ G.Edge z y → pb y z = 0) ∧
    ∀ y, (∃ z, G.Edge z y) → ∑ z, pb y z = 1

omit [Fintype V] in
/-- **The backward probability of a walk** `s₀ → s₁ → ⋯ → s_n`: the product over its steps of
`pb(s_{i+1} → s_i)`. For a Markov backward policy this is `p_B(τ|s_n)`. -/
noncomputable def backProb (pb : V → V → ℝ) : List V → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: l => pb b a * backProb pb (b :: l)

omit [Fintype V] in
theorem backProb_nonneg {pb : V → V → ℝ} (hpb : ∀ y z, 0 ≤ pb y z) :
    ∀ l : List V, 0 ≤ backProb pb l
  | [] => by rw [backProb]; exact zero_le_one
  | [_] => by rw [backProb]; exact zero_le_one
  | a :: b :: l => by rw [backProb]; exact mul_nonneg (hpb b a) (backProb_nonneg hpb (b :: l))

omit [Fintype V] in
/-- A full-support backward policy charges every walk. -/
theorem backProb_pos {pb : V → V → ℝ} (hpb : ∀ y z, G.Edge z y → 0 < pb y z) :
    ∀ l : List V, l.IsChain G.Edge → 0 < backProb pb l
  | [], _ => by rw [backProb]; exact one_pos
  | [_], _ => by rw [backProb]; exact one_pos
  | a :: b :: l, h => by
      rw [List.isChain_cons_cons] at h
      rw [backProb]
      exact mul_pos (hpb b a h.1) (backProb_pos hpb (b :: l) h.2)

omit [Fintype V] in
theorem backProb_concat (pb : V → V → ℝ) (y : V) :
    ∀ (l : List V) (h : l ≠ []), backProb pb (l ++ [y]) = backProb pb l * pb y (l.getLast h)
  | [], h => absurd rfl h
  | [a], _ => by
      simp only [List.cons_append, List.nil_append, backProb, List.getLast_singleton, one_mul,
        mul_one]
  | a :: b :: l, _ => by
      have ih := backProb_concat pb y (b :: l) (List.cons_ne_nil _ _)
      simp only [List.cons_append] at ih ⊢
      rw [backProb, ih, backProb, List.getLast_cons_cons, mul_assoc]

omit [Fintype V] in
/-- The only walk from `s₀` to `s₀` is `[s₀]`: `s₀` has no incoming edge. -/
theorem eq_singleton_src {l : List V} (hl : l ∈ walksInto G.Edge G.src G.src) : l = [G.src] := by
  obtain ⟨hh, hlast, hch⟩ := hl
  cases l with
  | nil => simp only [List.head?_nil, reduceCtorEq] at hh
  | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      cases l with
      | nil => rfl
      | cons b l =>
          exfalso
          have hne : b :: l ≠ [] := List.cons_ne_nil _ _
          have hmem : (b :: l).getLast hne ∈ G.src :: b :: l :=
            List.mem_cons_of_mem _ (List.getLast_mem hne)
          rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast hne,
            Option.some.injEq] at hlast
          -- the last step enters `s₀`
          have hsplit : G.src :: b :: l = (G.src :: b :: l).dropLast ++ [G.src] := by
            have := List.dropLast_append_getLast (l := G.src :: b :: l) (List.cons_ne_nil _ _)
            rw [List.getLast_cons_cons, hlast] at this
            exact this.symm
          have hdne : (G.src :: b :: l).dropLast ≠ [] := by
            simp only [List.dropLast_cons_cons, ne_eq, reduceCtorEq, not_false_eq_true]
          rw [hsplit, List.isChain_append] at hch
          exact G.no_edge_into_src _ (hch.2.2 _ (List.getLast?_eq_some_getLast hdne) _ rfl)

/-- **The backward mass of the walks from `s₀` to `y` of length at most `n+1` is at most `1`.** -/
theorem sum_backProb_le_one {pb : V → V → ℝ} (hpb : IsFullSupportMarkovBackward G pb) :
    ∀ (n : ℕ) (y : V) (F : Finset (List V)),
      (∀ l ∈ F, l ∈ walksInto G.Edge G.src y ∧ l.length ≤ n + 1) →
      ∑ l ∈ F, backProb pb l ≤ 1 := by
  classical
  obtain ⟨hpos, hzero, hsum⟩ := hpb
  have hnn : ∀ y z, 0 ≤ pb y z := fun y z => by
    by_cases h : G.Edge z y
    · exact (hpos y z h).le
    · exact (hzero y z h).ge
  have hsum_le : ∀ y, ∑ z, pb y z ≤ 1 := fun y => by
    by_cases h : ∃ z, G.Edge z y
    · exact (hsum y h).le
    · push Not at h
      rw [Finset.sum_eq_zero fun z _ => hzero y z (h z)]
      exact zero_le_one
  intro n
  induction n with
  | zero =>
      intro y F hF
      have hsub : F ⊆ {[G.src]} := by
        intro l hl
        obtain ⟨⟨hh, hlast, _⟩, hlen⟩ := hF l hl
        rw [Finset.mem_singleton]
        cases l with
        | nil => simp only [List.head?_nil, reduceCtorEq] at hh
        | cons a l =>
            cases l with
            | nil =>
                simp only [List.head?_cons, Option.some.injEq] at hh
                rw [hh]
            | cons b l => simp only [List.length_cons] at hlen; omega
      calc ∑ l ∈ F, backProb pb l ≤ ∑ l ∈ {[G.src]}, backProb pb l :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ => backProb_nonneg hnn l
        _ = 1 := by rw [Finset.sum_singleton, backProb]
  | succ n ih =>
      intro y F hF
      by_cases hy : y = G.src
      · subst hy
        have hsub : F ⊆ {[G.src]} := fun l hl =>
          Finset.mem_singleton.mpr (eq_singleton_src G (hF l hl).1)
        calc ∑ l ∈ F, backProb pb l ≤ ∑ l ∈ {[G.src]}, backProb pb l :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ => backProb_nonneg hnn l
          _ = 1 := by rw [Finset.sum_singleton, backProb]
      -- every walk in `F` is `l' ++ [y]` with `l'` a walk from `s₀` to a parent of `y`
      have hdec : ∀ l ∈ F, ∃ l' : List V, ∃ h : l' ≠ [], l = l' ++ [y] ∧
          l' ∈ walksInto G.Edge G.src (l'.getLast h) ∧ G.Edge (l'.getLast h) y ∧
          l'.length ≤ n + 1 := by
        intro l hl
        obtain ⟨⟨hh, hlast, hch⟩, hlen⟩ := hF l hl
        obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.mp hlast
        have hne : l' ≠ [] := by
          rintro rfl
          simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hh
          exact hy hh
        rw [List.isChain_append] at hch
        refine ⟨l', hne, rfl, ⟨?_, List.getLast?_eq_some_getLast hne, hch.1⟩,
          hch.2.2 _ (List.getLast?_eq_some_getLast hne) _ rfl, ?_⟩
        · rw [List.head?_append] at hh
          obtain ⟨a, l'', rfl⟩ := List.exists_cons_of_ne_nil hne
          simpa only [List.head?_cons, Option.some_or] using hh
        · simp only [List.length_append, List.length_singleton] at hlen
          omega
      let key : List V → V := fun l => l.dropLast.getLast?.getD G.src
      have hkey : ∀ l ∈ F, ∀ (l' : List V) (h : l' ≠ []), l = l' ++ [y] → key l = l'.getLast h := by
        intro l _ l' h hl
        simp only [key, hl, List.dropLast_concat, List.getLast?_eq_some_getLast h, Option.getD_some]
      rw [← Finset.sum_fiberwise F key]
      calc ∑ z, ∑ l ∈ F with key l = z, backProb pb l
          ≤ ∑ z, pb y z := by
            refine Finset.sum_le_sum fun z _ => ?_
            -- the fiber over `z`
            have hfib : ∑ l ∈ F with key l = z, backProb pb l =
                pb y z * ∑ l' ∈ (F.filter fun l => key l = z).image List.dropLast,
                  backProb pb l' := by
              rw [Finset.sum_image, Finset.mul_sum]
              · refine Finset.sum_congr rfl fun l hl => ?_
                obtain ⟨hlF, hkz⟩ := Finset.mem_filter.mp hl
                obtain ⟨l', h, rfl, -, -, -⟩ := hdec l hlF
                rw [backProb_concat pb y l' h, List.dropLast_concat, ← hkey _ hlF l' h rfl, hkz,
                  mul_comm]
              · intro l₁ h₁ l₂ h₂ he
                obtain ⟨l₁', -, rfl, -⟩ := hdec l₁ (Finset.mem_filter.mp h₁).1
                obtain ⟨l₂', -, rfl, -⟩ := hdec l₂ (Finset.mem_filter.mp h₂).1
                simp only [List.dropLast_concat] at he
                rw [he]
            rw [hfib]
            have hin : ∑ l' ∈ (F.filter fun l => key l = z).image List.dropLast,
                backProb pb l' ≤ 1 := by
              refine ih z _ fun l' hl' => ?_
              obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hl'
              obtain ⟨hlF, hkz⟩ := Finset.mem_filter.mp hl
              obtain ⟨l', h, rfl, hw', -, hlen'⟩ := hdec l hlF
              rw [List.dropLast_concat]
              rw [← hkey _ hlF l' h rfl, hkz] at hw'
              exact ⟨hw', hlen'⟩
            calc pb y z * _ ≤ pb y z * 1 := mul_le_mul_of_nonneg_left hin (hnn y z)
              _ = pb y z := mul_one _
        _ ≤ 1 := hsum_le y

/-- **`p_B(·|x)` of a full-support Markov backward policy is summable over the walks into `x`.** -/
theorem summable_backProb {pb : V → V → ℝ} (hpb : IsFullSupportMarkovBackward G pb) (x : V) :
    Summable fun τ : walksInto G.Edge G.src x => backProb pb τ.1 := by
  have hnn : ∀ y z, 0 ≤ pb y z := fun y z => by
    by_cases h : G.Edge z y
    · exact (hpb.1 y z h).le
    · exact (hpb.2.1 y z h).ge
  refine summable_of_sum_le (c := 1) (fun τ => backProb_nonneg hnn τ.1) fun u => ?_
  classical
  let n := u.sup fun τ => τ.1.length
  have h := sum_backProb_le_one G hpb n x (u.map (Function.Embedding.subtype _)) fun l hl => by
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_map.mp hl
    exact ⟨τ.2, (Finset.le_sup (f := fun τ : walksInto G.Edge G.src x => τ.1.length) hτ).trans
      (Nat.le_succ _)⟩
  rwa [Finset.sum_map] at h

end Backward

/-- `p^k (1 − p) ≤ 1/(k+1)` on `[0,1]`: a Markov policy cannot both continue `k` times around a
cycle and leave it with large probability. -/
theorem pow_mul_one_sub_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    p ^ k * (1 - p) ≤ 1 / ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hgeom := geom_sum_mul_neg p (k + 1)
  have hsum : ((k : ℝ) + 1) * p ^ k ≤ ∑ i ∈ range (k + 1), p ^ i := by
    have h := Finset.card_nsmul_le_sum (range (k + 1)) (fun i => p ^ i) (p ^ k)
      fun i hi => pow_le_pow_of_le_one hp0 hp1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    rw [Finset.card_range, nsmul_eq_mul] at h
    push_cast at h
    exact h
  rw [le_div_iff₀ hk1]
  have h1p : 0 ≤ 1 - p := by linarith
  have hpk : 0 ≤ p ^ (k + 1) := pow_nonneg hp0 _
  calc p ^ k * (1 - p) * ((k : ℝ) + 1) = ((k : ℝ) + 1) * p ^ k * (1 - p) := by ring
    _ ≤ (∑ i ∈ range (k + 1), p ^ i) * (1 - p) := mul_le_mul_of_nonneg_right hsum h1p
    _ = 1 - p ^ (k + 1) := hgeom
    _ ≤ 1 := by linarith

theorem pathProb_nonneg {S : Type*} {pol : S → S → ℝ} (hnn : ∀ u v, 0 ≤ pol u v) :
    ∀ l : List S, 0 ≤ pathProb pol l
  | [] => by rw [pathProb]; exact zero_le_one
  | [_] => by rw [pathProb]; exact zero_le_one
  | a :: b :: l => by rw [pathProb]; exact mul_nonneg (hnn a b) (pathProb_nonneg hnn (b :: l))

/-! ### Full-support Markov policies are sub-stochastic along walks -/

section FSM

variable {V : Type*} [Fintype V] {G : MarkedGraph V} {pol : V → V → ℝ}

theorem fsm_nonneg (h : IsFullSupportMarkov G pol) (u v : V) : 0 ≤ pol u v := by
  by_cases he : G.Edge u v
  · exact (h.1 u v he).le
  · exact (h.2.1 u v he).ge

theorem fsm_le_one (h : IsFullSupportMarkov G pol) {u v : V} (he : G.Edge u v) :
    pol u v ≤ 1 := by
  rw [← h.2.2 u ⟨v, he⟩]
  exact Finset.single_le_sum (fun y _ => fsm_nonneg h u y) (Finset.mem_univ v)

/-- Two distinct out-edges share at most the whole mass. -/
theorem fsm_pair (h : IsFullSupportMarkov G pol) {u v v' : V} (he : G.Edge u v)
    (hne : v ≠ v') : pol u v + pol u v' ≤ 1 := by
  classical
  rw [← h.2.2 u ⟨v, he⟩, ← Finset.sum_pair hne]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun y _ _ => fsm_nonneg h u y

theorem pathProb_fsm_Icc (h : IsFullSupportMarkov G pol) :
    ∀ l : List V, l.IsChain G.Edge → 0 ≤ pathProb pol l ∧ pathProb pol l ≤ 1
  | [], _ => by rw [pathProb]; exact ⟨zero_le_one, le_rfl⟩
  | [_], _ => by rw [pathProb]; exact ⟨zero_le_one, le_rfl⟩
  | a :: b :: l, hc => by
      rw [List.isChain_cons_cons] at hc
      obtain ⟨h0, h1⟩ := pathProb_fsm_Icc h (b :: l) hc.2
      rw [pathProb]
      exact ⟨mul_nonneg (fsm_nonneg h a b) h0,
        mul_le_one₀ (fsm_le_one h hc.1) h0 h1⟩

end FSM

/-! ### Counting the passages through a state along the cycle -/

section Count

variable {S : Type*}

open Classical in
/-- `cnt q f j n`: the number of `i < n` with `q (j + i) = f`, i.e. of the steps of `cycW q j n`
taken from `f`. -/
noncomputable def cnt (q : ℕ → S) (f : S) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | j, n + 1 => (if q j = f then 1 else 0) + cnt q f (j + 1) n

theorem cnt_add (q : ℕ → S) (f : S) (j a b : ℕ) :
    cnt q f j (a + b) = cnt q f j a + cnt q f (j + a) b := by
  induction a generalizing j with
  | zero => simp only [cnt, zero_add, add_zero]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega, cnt, cnt, ih (j + 1),
        show j + 1 + a = j + (a + 1) by omega, add_assoc]

theorem one_le_cnt (q : ℕ → S) (f : S) :
    ∀ (n j i : ℕ), i < n → q (j + i) = f → 1 ≤ cnt q f j n
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, j, 0, _, hq => by
      rw [cnt, if_pos (by simpa only [add_zero] using hq)]
      exact Nat.le_add_right _ _
  | n + 1, j, i + 1, hi, hq => by
      rw [cnt]
      exact (one_le_cnt q f n (j + 1) i (by omega)
        (by rw [show j + 1 + i = j + (i + 1) by omega]; exact hq)).trans (Nat.le_add_left _ _)

theorem cnt_ge_mul (q : ℕ → S) (L : ℕ) (f : S) (hf : ∀ j, ∃ i < L, q (j + i) = f) (j k : ℕ) :
    k ≤ cnt q f j (k * L) := by
  induction k generalizing j with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      rw [Nat.succ_mul, add_comm (k * L) L, cnt_add]
      obtain ⟨i, hi, hq⟩ := hf j
      have h1 := one_le_cnt q f L j i hi hq
      have h2 := ih (j + L)
      omega

/-- **Along the cycle, only the passages through `f` cost**: if every cycle step has probability
in `[0,1]` and a step from `f` at most `p`, then `cycW q j n` has probability at most
`p^{cnt q f j n}`. -/
theorem pathProb_cycW_le {pol : S → S → ℝ} {q : ℕ → S} {f : S} {p : ℝ} (hp0 : 0 ≤ p)
    (h0 : ∀ m, 0 ≤ pol (q m) (q (m + 1))) (h1 : ∀ m, pol (q m) (q (m + 1)) ≤ 1)
    (hf : ∀ m, q m = f → pol (q m) (q (m + 1)) ≤ p) (j n : ℕ) :
    pathProb pol (cycW q j n) ≤ p ^ cnt q f j n := by
  induction n generalizing j with
  | zero => simp only [cycW, pathProb, cnt, pow_zero, le_refl]
  | succ n ih =>
      obtain ⟨r, hr⟩ := cycW_eq_cons q (j + 1) n
      have hX0 : 0 ≤ pathProb pol (cycW q (j + 1) n) :=
        (pow_nonneg le_rfl _).trans (pathProb_cycW_ge le_rfl h0 _ _)
      have hih := ih (j + 1)
      rw [cycW, hr, pathProb, ← hr, cnt]
      by_cases hq : q j = f
      · rw [if_pos hq, pow_add, pow_one]
        exact mul_le_mul (hf j hq) hih hX0 hp0
      · rw [if_neg hq, zero_add]
        exact (mul_le_of_le_one_left hX0 (h1 j)).trans hih

end Count

/-! ## `sup_{p_F} M' = +∞` over full-support Markov policies, on every marked graph -/

section Main

/-- `((n+1)/(n+2))ⁿ · (1 − (n+1)/(n+2)) > 1/(3(n+2))`: the continuation weight
`a = (n+1)/(n+2)` keeps a length-`n` loop at probability of order `1/n`. -/
theorem one_div_three_lt (n : ℕ) :
    1 / (3 * ((n : ℝ) + 2)) <
      (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ n * (1 - ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
  set a : ℝ := ((n : ℝ) + 1) / ((n : ℝ) + 2) with ha
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have ha0 : 0 < a := div_pos hn1 hn2
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hn2]; linarith
  have h1a : 1 - a = 1 / ((n : ℝ) + 2) := by rw [ha]; field_simp; ring
  have hinv : 1 / a = 1 / ((n : ℝ) + 1) + 1 := by rw [ha]; field_simp; ring
  have hexp : (1 / a) ^ (n + 1) ≤ Real.exp 1 := by
    rw [hinv]
    calc (1 / ((n : ℝ) + 1) + 1) ^ (n + 1)
        ≤ (Real.exp (1 / ((n : ℝ) + 1))) ^ (n + 1) :=
          pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hpow : 1 / 3 < a ^ (n + 1) := by
    have hpos : 0 < (1 / a) ^ (n + 1) := by positivity
    have : a ^ (n + 1) = 1 / (1 / a) ^ (n + 1) := by rw [one_div_pow, one_div_one_div]
    rw [this, one_div_lt_one_div (by norm_num) hpos]
    exact lt_of_le_of_lt hexp Real.exp_one_lt_three
  have hle : a ^ (n + 1) ≤ a ^ n := pow_le_pow_of_le_one ha0.le ha1 (Nat.le_succ n)
  rw [h1a]
  calc 1 / (3 * ((n : ℝ) + 2)) = 1 / 3 * (1 / ((n : ℝ) + 2)) := by field_simp
    _ < a ^ n * (1 / ((n : ℝ) + 2)) :=
        mul_lt_mul_of_pos_right (lt_of_lt_of_le hpow hle) (by positivity)

/-- **Summability forces `liminf (k+1) f(k) = 0`**: a summable real sequence has
`(k+1) f(k) < δ` for some `k`, else it would dominate a harmonic series. -/
theorem exists_succ_mul_lt {f : ℕ → ℝ} (hf : Summable f) {δ : ℝ}
    (hδ : 0 < δ) : ∃ k : ℕ, ((k : ℝ) + 1) * f k < δ := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ k : ℕ, ((k : ℝ) + 1)⁻¹ ≤ δ⁻¹ * f k := by
    intro k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [inv_eq_one_div, div_le_iff₀ hk1]
    calc (1 : ℝ) = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
      _ ≤ δ⁻¹ * (((k : ℝ) + 1) * f k) := mul_le_mul_of_nonneg_left (hcon k) (inv_nonneg.2 hδ.le)
      _ = δ⁻¹ * f k * ((k : ℝ) + 1) := by ring
  have hsum : Summable fun k : ℕ => ((k : ℝ) + 1)⁻¹ :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle (hf.mul_left _)
  have hsum' : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsum
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).1 hsum')

/-- **`liminf_k (k+1) f(k) = 0`** for a summable non-negative sequence, in the form
"frequently `(k+1) f(k) < δ`" for every `δ > 0`. -/
theorem frequently_succ_mul_lt {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hf : Summable f) {δ : ℝ}
    (hδ : 0 < δ) : ∃ᶠ k : ℕ in Filter.atTop, ((k : ℝ) + 1) * f k < δ := by
  rw [Filter.frequently_atTop]
  intro K
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  obtain ⟨j, hj⟩ := exists_succ_mul_lt ((summable_nat_add_iff K).2 hf) (div_pos hδ hK)
  refine ⟨j + K, Nat.le_add_left _ _, ?_⟩
  rw [lt_div_iff₀ hK] at hj
  have h0 := hf0 (j + K)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_nonneg hj0 hK0, mul_nonneg (mul_nonneg hj0 hK0) h0, mul_nonneg hK0 h0]

variable {V : Type*} [Fintype V] {G : MarkedGraph V}

/-- **`rem:path_space`, the trajectories `τ_n` that wind `n` times around the cycle.** The
certificate of the mechanism around a **given** simple cycle `C` on the trajectories into `x`
(every state of `C` reachable from `s₀` and reaching `x`), with `x → s_f` an edge. There is an
injective family `τ k` of walks from `s₀` to `x` of the form `P ++ cycW C.q i (n₀ + k·L) ++ T` —
enter `C`, wind `k` further full turns around it, leave it at the state where it is left for the
last time — such that
* **some** full-support Markov policy, leaving the cycle with probability of order `1/k`, samples
  `τ k` (and terminates at `x`) with probability `> c/(k+1)`, with `c > 0` independent of `k`;
* **every** full-support Markov policy samples it with probability `≤ 1/(k+1)`. -/
theorem exists_pumped_of_simpleCycle {x : V} (C : SimpleCycle G.Edge)
    (hC : ∀ m, Relation.ReflTransGen G.Edge G.src (C.q m) ∧ Relation.ReflTransGen G.Edge (C.q m) x)
    (hxs : G.Edge x G.snk) :
    ∃ τ : ℕ → walksInto G.Edge G.src x, Function.Injective τ ∧
      (∃ P T : List V, ∃ i n₀ : ℕ, ∀ k, (τ k).1 = P ++ cycW C.q i (n₀ + k * C.L) ++ T) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k : ℕ, ∃ pol : V → V → ℝ, IsFullSupportMarkov G pol ∧
        c₀ / ((k : ℝ) + 1) < pathProb pol ((τ k).1 ++ [G.snk])) ∧
      ∀ pol : V → V → ℝ, IsFullSupportMarkov G pol → ∀ k : ℕ,
        pathProb pol ((τ k).1 ++ [G.snk]) ≤ 1 / ((k : ℝ) + 1) := by
  classical
  -- first entry into the cycle, last exit from it
  obtain ⟨P, e, ⟨ie0, rfl⟩, hPch, hPh, hPoff⟩ :=
    first_entry (Q := fun s => ∃ m, C.q m = s) (hC 0).1 ⟨0, rfl⟩
  obtain ⟨f, ⟨jf0, rfl⟩, T, hTch, hTl, hToff⟩ :=
    last_exit (Q := fun s => ∃ m, C.q m = s) (hC 0).2 ⟨0, rfl⟩
  have hLpos := C.L_pos
  have hie : ie0 % C.L < C.L := Nat.mod_lt _ hLpos
  have hjf : jf0 % C.L < C.L := Nat.mod_lt _ hLpos
  have hqie : C.q (ie0 % C.L) = C.q ie0 := (C.q_mod ie0).symm
  -- the pumped trajectories `τ k`: enter, run `k` extra loops, exit
  let nk : ℕ → ℕ := fun k => (jf0 % C.L + C.L - ie0 % C.L) + k * C.L
  have hend : ∀ k, C.q (ie0 % C.L + nk k) = C.q jf0 := by
    intro k
    have : ie0 % C.L + nk k = jf0 % C.L + (k + 1) * C.L := by
      simp only [nk, Nat.succ_mul]
      omega
    rw [this, C.q_add_mul, ← C.q_mod]
  let τ : ℕ → List V := fun k => P ++ cycW C.q (ie0 % C.L) (nk k) ++ T
  have hseg : ∀ k, (∃ r₁, cycW C.q (ie0 % C.L) (nk k) = C.q ie0 :: r₁) ∧
      ∃ r₂, cycW C.q (ie0 % C.L) (nk k) = r₂ ++ [C.q jf0] := by
    intro k
    obtain ⟨r₁, hr₁⟩ := cycW_eq_cons C.q (ie0 % C.L) (nk k)
    obtain ⟨r₂, hr₂⟩ := cycW_eq_append C.q (ie0 % C.L) (nk k)
    rw [hqie] at hr₁
    rw [hend k] at hr₂
    exact ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩
  have hmem : ∀ k, τ k ∈ walksInto G.Edge G.src x := by
    intro k
    obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := hseg k
    exact mem_walksInto_concat hPch hPh (isChain_cycW C.edge _ _) hr₁ hr₂ hTch hTl
  -- the probability of `τ k` under the loop-weighted policy with `a = (n+1)/(n+2)`
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨G.src⟩)
  set β : ℝ := 1 / (Fintype.card V : ℝ) with hβdef
  have hβ : 0 < β := div_pos one_pos hcard
  set K : ℝ := β ^ P.length * (β * β ^ T.length) with hKdef
  have hK : 0 < K := by positivity
  let a : ℕ → ℝ := fun k => ((nk k : ℝ) + 1) / ((nk k : ℝ) + 2)
  have hpF : ∀ k, K / (3 * ((nk k : ℝ) + 2)) <
      pathProb (cycPolicy G C (a k)) (τ k ++ [G.snk]) := by
    intro k
    have hn2 : (0 : ℝ) < (nk k : ℝ) + 2 := by positivity
    have ha0 : 0 ≤ a k := div_nonneg (by positivity) hn2.le
    have ha1 : a k ≤ 1 := by
      simp only [a]; rw [div_le_one hn2]; linarith
    obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := hseg k
    have hsplit := pathProb_concat (cycPolicy G C (a k)) P T G.snk hr₁ hr₂
    have hA : β ^ P.length ≤ pathProb (cycPolicy G C (a k)) (P ++ [C.q ie0]) :=
      pathProb_ge_pow hβ.le (P := fun s => ∃ m, C.q m = s)
        (fun s s' h hQ => cycPolicy_ge_off C (a k) h hQ) P _ hPch hPoff
    have hB : a k ^ nk k ≤ pathProb (cycPolicy G C (a k)) (cycW C.q (ie0 % C.L) (nk k)) :=
      pathProb_cycW_ge ha0 (cycPolicy_ge_cyc C ha1) _ _
    have hTch' : (C.q jf0 :: (T ++ [G.snk])).IsChain G.Edge := by
      rw [← List.cons_append]
      refine hTch.append (List.IsChain.singleton _) fun y hy z hz => ?_
      rw [hTl, Option.mem_def, Option.some.injEq] at hy
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hy hz
      exact hxs
    have hγ : 0 ≤ (1 - a k) / (Fintype.card V : ℝ) := div_nonneg (by linarith) hcard.le
    have hCc : (1 - a k) / (Fintype.card V : ℝ) * β ^ T.length ≤
        pathProb (cycPolicy G C (a k)) (C.q jf0 :: (T ++ [G.snk])) :=
      pathProb_exit_ge hβ.le hγ (P := fun s => ∃ m, C.q m = s)
        (fun s s' h hQ => cycPolicy_ge_off C (a k) h hQ)
        (fun s' h => cycPolicy_ge_exit C ha0 ha1 h) T hTch' hToff
    have hprod : β ^ P.length * a k ^ nk k * ((1 - a k) / (Fintype.card V : ℝ) * β ^ T.length)
        ≤ pathProb (cycPolicy G C (a k)) (τ k ++ [G.snk]) := by
      rw [show τ k ++ [G.snk] = P ++ cycW C.q (ie0 % C.L) (nk k) ++ T ++ [G.snk] from rfl, hsplit]
      have hA0 := (pow_nonneg hβ.le P.length).trans hA
      have hB0 := (pow_nonneg ha0 (nk k)).trans hB
      exact mul_le_mul (mul_le_mul hA hB (pow_nonneg ha0 _) hA0) hCc
        (mul_nonneg hγ (pow_nonneg hβ.le _)) (mul_nonneg hA0 hB0)
    have hkey := one_div_three_lt (nk k)
    have heq : β ^ P.length * a k ^ nk k * ((1 - a k) / (Fintype.card V : ℝ) * β ^ T.length)
        = K * (a k ^ nk k * (1 - a k)) := by
      rw [hKdef, hβdef]; ring
    have hlt : K / (3 * ((nk k : ℝ) + 2)) < K * (a k ^ nk k * (1 - a k)) := by
      rw [div_eq_mul_one_div]
      exact mul_lt_mul_of_pos_left hkey hK
    linarith
  have hinj : Function.Injective fun k : ℕ => (⟨τ k, hmem k⟩ : walksInto G.Edge G.src x) := by
    intro k k' hkk
    have hlen := congrArg (fun t : walksInto G.Edge G.src x => t.1.length) hkk
    simp only [τ, List.length_append, length_cycW, nk] at hlen
    have : k * C.L = k' * C.L := by omega
    exact Nat.eq_of_mul_eq_mul_right hLpos this
  set n0 : ℕ := jf0 % C.L + C.L - ie0 % C.L with hn0
  set D : ℝ := K / (3 * ((n0 : ℝ) + (C.L : ℝ) + 2)) with hD
  have hDpos : 0 < D := by positivity
  refine ⟨fun k => ⟨τ k, hmem k⟩, hinj,
    ⟨P, T, ie0 % C.L, jf0 % C.L + C.L - ie0 % C.L, fun k => rfl⟩, ⟨D, hDpos, fun k => ⟨cycPolicy G C (a k),
    cycPolicy_isFullSupportMarkov C (div_nonneg (by positivity) (by positivity))
      ((div_lt_one (by positivity)).2 (by linarith)), ?_⟩⟩, fun pol hpol k => ?_⟩
  · -- `D/(k+1) ≤ K/(3(n_k+2)) < p_F`
    have hnk : ((nk k : ℕ) : ℝ) = (n0 : ℝ) + (k : ℝ) * (C.L : ℝ) := by
      simp only [nk, hn0]; push_cast; ring
    have hDle : D / ((k : ℝ) + 1) ≤ K / (3 * ((nk k : ℝ) + 2)) := by
      rw [hD, div_div, hnk]
      apply div_le_div_of_nonneg_left hK.le (by positivity)
      have h0 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
      have hL0 : (0 : ℝ) ≤ C.L := Nat.cast_nonneg _
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith
    exact lt_of_le_of_lt hDle (hpF k)
  · -- every full-support Markov policy: `p_F(τ k) ≤ p^k (1 − p) ≤ 1/(k+1)`
    obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := hseg k
    show pathProb pol (τ k ++ [G.snk]) ≤ 1 / ((k : ℝ) + 1)
    rw [show τ k ++ [G.snk] = P ++ cycW C.q (ie0 % C.L) (nk k) ++ T ++ [G.snk] from rfl,
      pathProb_concat pol P T G.snk hr₁ hr₂]
    have hnn := fsm_nonneg hpol
    set p : ℝ := pol (C.q jf0) (C.nxt (C.q jf0)) with hp
    have hp0 : 0 ≤ p := hnn _ _
    have hnxt : G.Edge (C.q jf0) (C.nxt (C.q jf0)) := by rw [C.nxt_q]; exact C.edge jf0
    have hp1 : p ≤ 1 := fsm_le_one hpol hnxt
    have hA := pathProb_fsm_Icc hpol (P ++ [C.q ie0]) hPch
    -- the cycle segment passes `k` times through the exit state along the cycle edge
    have hcnt : k ≤ cnt C.q (C.q jf0) (ie0 % C.L) (nk k) := by
      have hsplit : nk k = (jf0 % C.L + C.L - ie0 % C.L) + k * C.L := rfl
      rw [hsplit, cnt_add]
      exact le_add_left (cnt_ge_mul C.q C.L (C.q jf0) (fun j => C.exists_lt_eq j jf0) _ k)
    have hB : pathProb pol (cycW C.q (ie0 % C.L) (nk k)) ≤ p ^ k := by
      refine (pathProb_cycW_le hp0 (fun m => hnn _ _) (fun m => fsm_le_one hpol (C.edge m))
        (fun m hm => ?_) _ _).trans (pow_le_pow_of_le_one hp0 hp1 hcnt)
      rw [hp, ← hm, C.nxt_q]
    have hB0 : 0 ≤ pathProb pol (cycW C.q (ie0 % C.L) (nk k)) := pathProb_nonneg hnn _
    -- the exit step goes off the cycle, so it has probability at most `1 − p`
    have hTch' : (C.q jf0 :: (T ++ [G.snk])).IsChain G.Edge := by
      rw [← List.cons_append]
      refine hTch.append (List.IsChain.singleton _) fun y hy z hz => ?_
      rw [hTl, Option.mem_def, Option.some.injEq] at hy
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hy hz
      exact hxs
    obtain ⟨g, rest, hgr, hgoff⟩ : ∃ g rest, T ++ [G.snk] = g :: rest ∧ ¬ ∃ m, C.q m = g := by
      cases T with
      | nil =>
          refine ⟨G.snk, [], rfl, ?_⟩
          rintro ⟨m, hm⟩
          exact G.no_edge_out_of_snk _ (hm ▸ C.edge m)
      | cons t T' => exact ⟨t, T' ++ [G.snk], rfl, hToff t List.mem_cons_self⟩
    rw [hgr] at hTch' ⊢
    rw [List.isChain_cons_cons] at hTch'
    have hne : g ≠ C.nxt (C.q jf0) := by
      rintro rfl
      exact hgoff ⟨jf0 + 1, (C.nxt_q jf0).symm⟩
    have hexit : pol (C.q jf0) g ≤ 1 - p := by
      have := fsm_pair hpol hTch'.1 hne
      linarith
    have hrest := pathProb_fsm_Icc hpol (g :: rest) hTch'.2
    rw [pathProb]
    have hCc : pol (C.q jf0) g * pathProb pol (g :: rest) ≤ 1 - p :=
      (mul_le_of_le_one_right (hnn _ _) hrest.2).trans hexit
    have hCc0 : 0 ≤ pol (C.q jf0) g * pathProb pol (g :: rest) := mul_nonneg (hnn _ _) hrest.1
    calc pathProb pol (P ++ [C.q ie0]) * pathProb pol (cycW C.q (ie0 % C.L) (nk k)) *
          (pol (C.q jf0) g * pathProb pol (g :: rest))
        ≤ 1 * p ^ k * (1 - p) :=
          mul_le_mul (mul_le_mul hA.2 hB hB0 zero_le_one) hCc hCc0
            (mul_nonneg zero_le_one (pow_nonneg hp0 _))
      _ = p ^ k * (1 - p) := by ring
      _ ≤ 1 / ((k : ℝ) + 1) := pow_mul_one_sub_le hp0 hp1 k

/-- **`rem:path_space`, the pumped trajectories.** Let a walk `w` from `s₀` to `x` visit a
state `v` carrying a closed walk `v :: c`, and let `x → s_f` be an edge. There is an injective
family `τ k` of walks from `s₀` to `x` — enter a simple cycle, wind `k` further times around it,
leave it at the state where it is left for the last time — such that
* **some** full-support Markov policy, leaving the cycle with probability of order `1/k`, samples
  `τ k` (and terminates at `x`) with probability `> c/(k+1)`, with `c > 0` independent of `k`;
* **every** full-support Markov policy samples it with probability `≤ 1/(k+1)`.
The second item is why `inf_τ p_B(τ|x) = 0` alone does not give `sup_{p_F} M' = +∞`. -/
theorem exists_pumped {x v : V} {w : List V} (hw : w ∈ walksInto G.Edge G.src x)
    (hv : v ∈ w) {c : List V} (hcE : (v :: c).IsChain G.Edge) (hc : c.getLast? = some v)
    (hxs : G.Edge x G.snk) :
    ∃ τ : ℕ → walksInto G.Edge G.src x, Function.Injective τ ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k : ℕ, ∃ pol : V → V → ℝ, IsFullSupportMarkov G pol ∧
        c₀ / ((k : ℝ) + 1) < pathProb pol ((τ k).1 ++ [G.snk])) ∧
      ∀ pol : V → V → ℝ, IsFullSupportMarkov G pol → ∀ k : ℕ,
        pathProb pol ((τ k).1 ++ [G.snk]) ≤ 1 / ((k : ℝ) + 1) := by
  classical
  obtain ⟨hhead, hlast, hchain⟩ := hw
  have hsv := reach_of_mem_of_head hchain hhead hv
  have hvx := reach_of_mem_of_getLast hchain hlast hv
  have hcl : (v :: c).getLast? = some v := getLast?_cons_self_of hc
  -- a simple cycle on the trajectories into `x`
  have hclosed : ClosedIn G.Edge (fun y => Relation.ReflTransGen G.Edge G.src y ∧
      Relation.ReflTransGen G.Edge y x) c.length :=
    closedIn_of_list hcE hc fun y hy =>
      ⟨hsv.trans (reach_of_mem_of_head hcE rfl hy), (reach_of_mem_of_getLast hcE hcl hy).trans hvx⟩
  obtain ⟨C, hC⟩ := exists_simpleCycle hclosed
  obtain ⟨τ, hinj, -, hlow, hup⟩ := exists_pumped_of_simpleCycle C hC hxs
  exact ⟨τ, hinj, hlow, hup⟩

/-- **`rem:path_space`, `sup_{p_F} M' = +∞`, over full-support Markov forward policies, on every
finite marked graph.** Let a walk `w` from `s₀` to `x` visit a state `v` carrying a closed walk
`v :: c` (so a cycle lies on the trajectories into `x`), let `x → s_f` be an edge, and let
`p_B(·|x)` be positive on every walk from `s₀` to `x` and summable over them (for instance a
probability charging each trajectory into `x`). For every `R` there is a full-support Markov
forward policy `pol` and a walk `τ` from `s₀` to `x` with `p_F(τ → s_f)/p_B(τ|x) > R`, where
`p_F(τ → s_f) = pathProb pol (τ ++ [s_f])` is the probability that `pol` samples the trajectory
`τ` and terminates at `x` — so `M' ≥ M > R`. -/
theorem exists_markov_ratio_gt {x v : V} {w : List V} (hw : w ∈ walksInto G.Edge G.src x)
    (hv : v ∈ w) {c : List V} (hcE : (v :: c).IsChain G.Edge) (hc : c.getLast? = some v)
    (hxs : G.Edge x G.snk) {pB : walksInto G.Edge G.src x → ℝ} (hBpos : ∀ τ, 0 < pB τ)
    (hBs : Summable pB) (R : ℝ) :
    ∃ pol : V → V → ℝ, IsFullSupportMarkov G pol ∧
      ∃ τ : walksInto G.Edge G.src x, 0 < pB τ ∧ R < pathProb pol (τ.1 ++ [G.snk]) / pB τ := by
  obtain ⟨τ, hinj, ⟨c₀, hc₀, hlow⟩, -⟩ := exists_pumped hw hv hcE hc hxs
  have hgs : Summable fun k : ℕ => pB (τ k) := hBs.comp_injective hinj
  have hδ : 0 < c₀ / (|R| + 1) := by positivity
  obtain ⟨k, hk⟩ := exists_succ_mul_lt hgs hδ
  obtain ⟨pol, hpol, hpF'⟩ := hlow k
  have hp := hBpos (τ k)
  refine ⟨pol, hpol, τ k, hp, ?_⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- `R < c₀/((k+1) p_B) ≤ p_F/p_B`
  have hRlt : R < c₀ / (((k : ℝ) + 1) * pB (τ k)) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hk
    have hR : R ≤ |R| := le_abs_self R
    have hpos : 0 ≤ ((k : ℝ) + 1) * pB (τ k) := by positivity
    nlinarith [abs_nonneg R]
  calc R < c₀ / (((k : ℝ) + 1) * pB (τ k)) := hRlt
    _ = c₀ / ((k : ℝ) + 1) / pB (τ k) := (div_div _ _ _).symm
    _ ≤ pathProb pol ((τ k).1 ++ [G.snk]) / pB (τ k) := div_le_div_of_nonneg_right hpF'.le hp.le

/-- **`rem:path_space`, the mechanism, in one statement.** Along the pumped trajectories `τ k`
into `x` (`exists_pumped`): `liminf_k (k+1) p_B(τ_k|x) = 0` for every summable non-negative
`p_B(·|x)`; some full-support Markov policy has `p_F(τ_k) > c₀/(k+1)`; every full-support Markov
policy has `p_F(τ_k) ≤ 1/(k+1)`. -/
theorem exists_pumped_liminf {x v : V} {w : List V} (hw : w ∈ walksInto G.Edge G.src x)
    (hv : v ∈ w) {c : List V} (hcE : (v :: c).IsChain G.Edge) (hc : c.getLast? = some v)
    (hxs : G.Edge x G.snk) {pB : walksInto G.Edge G.src x → ℝ} (hB0 : ∀ τ, 0 ≤ pB τ)
    (hBs : Summable pB) :
    ∃ τ : ℕ → walksInto G.Edge G.src x, Function.Injective τ ∧
      (∀ δ : ℝ, 0 < δ → ∃ᶠ k : ℕ in Filter.atTop, ((k : ℝ) + 1) * pB (τ k) < δ) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k : ℕ, ∃ pol : V → V → ℝ, IsFullSupportMarkov G pol ∧
        c₀ / ((k : ℝ) + 1) < pathProb pol ((τ k).1 ++ [G.snk])) ∧
      ∀ pol : V → V → ℝ, IsFullSupportMarkov G pol → ∀ k : ℕ,
        pathProb pol ((τ k).1 ++ [G.snk]) ≤ 1 / ((k : ℝ) + 1) := by
  obtain ⟨τ, hinj, hlow, hup⟩ := exists_pumped hw hv hcE hc hxs
  exact ⟨τ, hinj, fun δ hδ =>
    frequently_succ_mul_lt (fun k => hB0 (τ k)) (hBs.comp_injective hinj) hδ, hlow, hup⟩

/-- **`rem:path_space`, `inf_τ p_B(τ|x) = 0`, in Silva's setting**: for a full-support Markov
backward policy, `p_B(·|x)` has infimum `0` over the (infinitely many) walks into `x`. -/
theorem iInf_backProb_eq_zero {x v : V} {w : List V} (hw : w ∈ walksInto G.Edge G.src x)
    (hv : v ∈ w) {c : List V} (hcE : (v :: c).IsChain G.Edge) (hc : c.getLast? = some v)
    {pb : V → V → ℝ} (hpb : IsFullSupportMarkovBackward G pb) :
    ⨅ τ : walksInto G.Edge G.src x, backProb pb τ.1 = 0 := by
  have hcne : c ≠ [] := by
    rintro rfl
    simp only [List.getLast?_nil, reduceCtorEq] at hc
  haveI := (walksInto_infinite hw hv hcne hcE hc).to_subtype
  exact iInf_eq_zero_of_summable (fun τ => (backProb_pos G hpb.1 τ.1 τ.2.2.2).le)
    (summable_backProb G hpb x)

/-- **`rem:path_space`, the same, as unboundedness**: the ratios `p_F(τ → s_f)/p_B(τ|x)` over
full-support Markov forward policies and walks `τ` from `s₀` to `x` are not bounded above. -/
theorem markov_ratio_not_bddAbove {x v : V} {w : List V} (hw : w ∈ walksInto G.Edge G.src x)
    (hv : v ∈ w) {c : List V} (hcE : (v :: c).IsChain G.Edge) (hc : c.getLast? = some v)
    (hxs : G.Edge x G.snk) {pB : walksInto G.Edge G.src x → ℝ} (hBpos : ∀ τ, 0 < pB τ)
    (hBs : Summable pB) :
    ¬ BddAbove {r : ℝ | ∃ pol : V → V → ℝ, IsFullSupportMarkov G pol ∧
      ∃ τ : walksInto G.Edge G.src x, 0 < pB τ ∧ r = pathProb pol (τ.1 ++ [G.snk]) / pB τ} := by
  rintro ⟨R, hR⟩
  obtain ⟨pol, hpol, τ, hp, hlt⟩ := exists_markov_ratio_gt hw hv hcE hc hxs hBpos hBs R
  exact absurd (hR ⟨pol, hpol, τ, hp, rfl⟩) (not_le.2 hlt)

/-- **`rem:path_space` in Silva's setting**: the backward law `p_B(·|x)` is that of a full-support
Markov backward policy `pb`, `p_B(τ|x) = backProb pb τ`. It charges every walk into `x` and is
summable over them (`summable_backProb`), so `exists_markov_ratio_gt` applies. -/
theorem exists_markov_ratio_gt_backward {x v : V} {w : List V}
    (hw : w ∈ walksInto G.Edge G.src x) (hv : v ∈ w) {c : List V}
    (hcE : (v :: c).IsChain G.Edge) (hc : c.getLast? = some v) (hxs : G.Edge x G.snk)
    {pb : V → V → ℝ} (hpb : IsFullSupportMarkovBackward G pb) (R : ℝ) :
    ∃ pol : V → V → ℝ, IsFullSupportMarkov G pol ∧
      ∃ τ : walksInto G.Edge G.src x, 0 < backProb pb τ.1 ∧
        R < pathProb pol (τ.1 ++ [G.snk]) / backProb pb τ.1 :=
  exists_markov_ratio_gt hw hv hcE hc hxs (fun τ => backProb_pos G hpb.1 τ.1 τ.2.2.2)
    (summable_backProb G hpb x) R

/-- **`rem:path_space`, the same, as unboundedness**, in Silva's setting. -/
theorem markov_ratio_not_bddAbove_backward {x v : V} {w : List V}
    (hw : w ∈ walksInto G.Edge G.src x) (hv : v ∈ w) {c : List V}
    (hcE : (v :: c).IsChain G.Edge) (hc : c.getLast? = some v) (hxs : G.Edge x G.snk)
    {pb : V → V → ℝ} (hpb : IsFullSupportMarkovBackward G pb) :
    ¬ BddAbove {r : ℝ | ∃ pol : V → V → ℝ, IsFullSupportMarkov G pol ∧
      ∃ τ : walksInto G.Edge G.src x, 0 < backProb pb τ.1 ∧
        r = pathProb pol (τ.1 ++ [G.snk]) / backProb pb τ.1} :=
  markov_ratio_not_bddAbove (pB := fun τ => backProb pb τ.1) hw hv hcE hc hxs
    (fun τ => backProb_pos G hpb.1 τ.1 τ.2.2.2) (summable_backProb G hpb x)

variable (G) in
/-- **The uniform backward policy** `pb(y → z) = 1/#parents(y)` is a full-support Markov backward
policy: the class of `exists_markov_ratio_gt_backward` is inhabited on every finite graph. -/
theorem exists_isFullSupportMarkovBackward :
    ∃ pb : V → V → ℝ, IsFullSupportMarkovBackward G pb := by
  classical
  let deg : V → ℝ := fun y => ((univ.filter fun z => G.Edge z y).card : ℝ)
  have hdeg : ∀ y z, G.Edge z y → 0 < deg y := fun y z h =>
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)
  refine ⟨fun y z => if G.Edge z y then 1 / deg y else 0, fun y z h => ?_, fun y z h => ?_,
    fun y ⟨z, hz⟩ => ?_⟩
  · simp only [if_pos h]
    exact div_pos one_pos (hdeg y z h)
  · simp only [if_neg h]
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    change deg y * (1 / deg y) = 1
    field_simp [(hdeg y z hz).ne']

end Main

/-! ## The hypotheses are inhabited -/

section Inhabit

open GFNBounds.Graph.CycleDivergence

/-- **`rem:path_space`: the hypotheses of `exists_markov_ratio_gt_backward` are inhabited**
(kb 0025): on `𝒞₂`, the walk `s₀ → x₁ → x₂` into `x₂` visits `x₁`, which carries the cycle
`x₁ → x₂ → x₁`; `x₂ → s_f` is an edge; and a full-support Markov backward policy exists. So every `R` is exceeded by a ratio
`p_F/p_B` with `p_F` a full-support Markov policy of `𝒞₂`. -/
theorem inhabit_markov_general :
    ∃ pb : cycV 0 → cycV 0 → ℝ, IsFullSupportMarkovBackward (cycGraph 0) pb ∧
      ∀ R : ℝ, ∃ pol : cycV 0 → cycV 0 → ℝ, IsFullSupportMarkov (cycGraph 0) pol ∧
        ∃ τ : walksInto (cycGraph 0).Edge (cycGraph 0).src (xC 0 1), 0 < backProb pb τ.1 ∧
          R < pathProb pol (τ.1 ++ [(cycGraph 0).snk]) / backProb pb τ.1 := by
  have e1 : (cycGraph 0).Edge (srcC 0) (xC 0 0) := Or.inl ⟨rfl, rfl⟩
  have e2 : (cycGraph 0).Edge (xC 0 0) (xC 0 1) := Or.inr (Or.inr ⟨0, rfl, rfl⟩)
  have e3 : (cycGraph 0).Edge (xC 0 1) (xC 0 0) := Or.inr (Or.inr ⟨1, rfl, rfl⟩)
  have e4 : (cycGraph 0).Edge (xC 0 1) (cycGraph 0).snk := Or.inr (Or.inl ⟨1, rfl, rfl⟩)
  have hw : [srcC 0, xC 0 0, xC 0 1] ∈ walksInto (cycGraph 0).Edge (cycGraph 0).src (xC 0 1) := by
    refine ⟨rfl, rfl, ?_⟩
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨e1, e2⟩
  have hv : xC 0 0 ∈ [srcC 0, xC 0 0, xC 0 1] := List.mem_cons_of_mem _ List.mem_cons_self
  have hcE : [xC 0 0, xC 0 1, xC 0 0].IsChain (cycGraph 0).Edge := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨e2, e3⟩
  obtain ⟨pb, hpb⟩ := exists_isFullSupportMarkovBackward (cycGraph 0)
  exact ⟨pb, hpb, fun R => exists_markov_ratio_gt_backward hw hv hcE rfl e4 hpb R⟩

end Inhabit

end GFNBounds.Silva.PathSpaceMarkovGeneral
