import GFNBounds.Silva.Remarks

/-!
# `rem:path_space` on `𝒞_N`: `sup_{p_F} M' = +∞` over full-support Markov forward policies

**`rem:path_space`** — `silva_comparison.tex:110–116` (a remark; no proof environment; the label
is the anchor, kb 0036).

> When a cycle lies on the trajectories into a state `x`, these are infinitely many, so
> `inf_τ p_B(τ|x) = 0` and `sup_{p_F} M' = +∞`. Let `𝒞_N` be the directed cycle on states
> `x₁,…,x_N` of Lemma `lem:cycle_counterexample`, entered at `x₁` and terminal at every state: …

with the supremum "running over full-support forward policies". `Silva/Remarks.lean` certifies
`sup_{p_F} M' = +∞` over full-support **trajectory laws** (`exists_ratio_gt_walksInto`). This file
certifies it on `𝒞_N` over full-support **Markov** forward policies — the class the paper's
"forward policy" names — for every backward law `p_B(·|x)` charging each trajectory into `x`.

## What is proved

| paper | here |
|---|---|
| the trajectories of `𝒞_N`: `s₀ → x₁ → x₂ → ⋯ → x_{n+1 mod N} → s_f` | `cycTraj`; `isChain_cycTraj`, `cycTraj_injective`, and **`eq_cycTraj`**: every walk from `s₀` to `s_f` is one of them |
| the trajectory `cycTraj n` runs into `x_{n+1 mod N}` | `cycTraj_eq_append` |
| a full-support Markov forward policy | `cycPol a`, `0 < a < 1`: `cycPol_pos_of_edge`, `cycPol_supp`, `cycPol_row_sum`, `cycPol_nonneg` |
| its trajectory law | `pathProb_cycTraj`: `p_F(cycTraj n) = aⁿ(1 − a)`, and `hasSum_cycTraj`: a probability on the trajectories |
| **`sup_{p_F} M' = +∞`**, Markov | **`cycle_exists_ratio_gt_markov`**: for every `R`, some `a ∈ (0,1)` and some trajectory `τ` into `x` with `p_B(τ|x) > 0` and `p_F(τ)/p_B(τ|x) > R`; `cycle_ratio_not_bddAbove_markov`, the same as unboundedness of the set of ratios |
| the hypotheses are inhabited | `inhabit_markov_cycle` |

## SCOPE (disclosed)

* **`𝒞_N`, not every graph with a cycle.** The paper's sentence is general ("when a cycle lies on
  the trajectories into a state `x`"); over Markov policies it is certified here on `𝒞_N`, the
  instance the remark names next. On a general graph the Markov form is **not** formalized (a
  pumped walk may revisit the states of its prefix, so a single Markov policy does not follow it
  with a controlled probability); the general sentence stays certified over trajectory laws only
  (`exists_ratio_gt_walksInto`).
* **Trajectories are indexed by their length.** `cycTraj M n` is the list
  `s₀, x₁, …, x_{n+1 mod N}, s_f`, and `eq_cycTraj` / `cycTraj_injective` prove that `n ↦ cycTraj
  M n` is a bijection onto the walks of `𝒞_N` from `s₀` to `s_f`; `p_B(·|x)` is therefore a
  function `pB : ℕ → ℝ` of the trajectory index. The theorem asks only `pB ≥ 0`, summable, and
  positive on every trajectory into `x` — weaker than "`p_B(·|x)` is a probability charging each
  trajectory into `x`", which it contains (`inhabit_markov_cycle` exhibits one).
* **`= +∞` is delivered as unboundedness of the ratio** `p_F(τ)/p_B(τ|x)` over the policies and the
  charged trajectories into `x`, as in `exists_ratio_gt_walksInto`: `M' ≥ M ≥` that ratio, and `M'`
  has no value on an infinite trajectory set.
* **The step `inf_τ p_B = 0 ⇒ sup M' = +∞` is not what the proof uses.** A Markov policy cannot put
  mass near `1` on a long trajectory of `𝒞_N`: with `a_x` its continuation probability at `x`,
  the length-`n` trajectory into `x` visits `x` `k = ⌊n/N⌋ + 1` times, so
  `p_F ≤ a_x^{k−1}(1 − a_x) ≤ 1/k ≤ N/(n+1)` (for the homogeneous `cycPol a`,
  `p_F = aⁿ(1 − a) < 1/(n+1)`). What gives `+∞` is summability of `p_B(·|x)`:
  `liminf_n n · p_B(τ_n|x) = 0` along the trajectories into `x` (`exists_mul_lt`), else
  `p_B(·|x)` would dominate a harmonic series. With `a = (n+1)/(n+2)`,
  `p_F(τ_n) > 1/(3(n+2))` (`pathProb_cycTraj_ge`; in fact `≥ e^{−1}/(n+2)`). This is a proof-level observation, not a
  correction to the remark: its conclusion holds.
* **`N ≥ 2`** is `N = M + 2`, as throughout `Graph/CycleDivergence.lean`; the paper's `x₁` is
  `xC M 0`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒞_N`, entered at `x₁`, terminal at every state | ✓ `cycGraph M` (`Graph/CycleDivergence.lean`) |
| `p_B(·|x)` of full support on the trajectories into `x` | ✓ `hBpos` (on the trajectories into `x`), `hB0`, `hBs` |
| `p_F` a full-support forward policy | ✓ `cycPol a`, `0 < a < 1`, Markov, positive on every edge, supported on edges, stochastic |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Silva.PathSpaceMarkov

open GFNBounds.Graph GFNBounds.Graph.CycleDivergence GFNBounds.Silva.Remarks Finset Filter
open Fin.NatCast

variable {M : ℕ}

/-! ## The trajectories of `𝒞_N` -/

/-- The tail `x_{j+1}, x_{j+2}, …, x_{j+n+1}, s_f` (indices mod `N`) of a trajectory: `n` cycle
steps from `x_{j+1}`, then the terminating edge. -/
def cycTail (M : ℕ) : ℕ → ℕ → List (cycV M)
  | j, 0 => [xC M (j : Fin (M + 2)), snkC M]
  | j, n + 1 => xC M (j : Fin (M + 2)) :: cycTail M (j + 1) n

/-- **The trajectory `cycTraj M n` of `𝒞_N`**: `s₀ → x₁ → ⋯ → x_{n+1 mod N} → s_f`. -/
def cycTraj (M : ℕ) (n : ℕ) : List (cycV M) := srcC M :: cycTail M 0 n

theorem cycTail_succ (j n : ℕ) :
    cycTail M j (n + 1) = xC M (j : Fin (M + 2)) :: cycTail M (j + 1) n :=
  rfl

theorem cycTail_eq_cons (j n : ℕ) : ∃ r, cycTail M j n = xC M (j : Fin (M + 2)) :: r := by
  cases n with
  | zero => exact ⟨[snkC M], rfl⟩
  | succ n => exact ⟨cycTail M (j + 1) n, rfl⟩

theorem length_cycTail (j n : ℕ) : (cycTail M j n).length = n + 2 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => rw [cycTail_succ, List.length_cons, ih]

/-- The tail ends `x_{j+n+1}, s_f`. -/
theorem cycTail_eq_append (j n : ℕ) :
    ∃ l, cycTail M j n = l ++ [xC M ((j + n : ℕ) : Fin (M + 2)), snkC M] := by
  induction n generalizing j with
  | zero => exact ⟨[], by simp only [cycTail, add_zero, List.nil_append]⟩
  | succ n ih =>
      obtain ⟨l, hl⟩ := ih (j + 1)
      refine ⟨xC M (j : Fin (M + 2)) :: l, ?_⟩
      rw [cycTail_succ, hl, show j + 1 + n = j + (n + 1) by omega, List.cons_append]

/-- **`cycTraj M n` is a trajectory into `x_{n+1 mod N}`**: it ends `x_{n+1}, s_f`. -/
theorem cycTraj_eq_append (n : ℕ) :
    ∃ l, cycTraj M n = l ++ [xC M (n : Fin (M + 2)), snkC M] := by
  obtain ⟨l, hl⟩ := cycTail_eq_append (M := M) 0 n
  refine ⟨srcC M :: l, ?_⟩
  rw [cycTraj, hl, zero_add, List.cons_append]

theorem cycTraj_injective (M : ℕ) : Function.Injective (cycTraj M) := by
  intro n m h
  have := congrArg List.length h
  simp only [cycTraj, List.length_cons, length_cycTail] at this
  omega

theorem edge_xC_iff {i : Fin (M + 2)} {v : cycV M} :
    (cycGraph M).Edge (xC M i) v ↔ v = snkC M ∨ v = xC M (i + 1) := by
  rw [cycGraph_edge_iff, cycEdge]
  constructor
  · rintro (⟨h, -⟩ | ⟨k, hk, hv⟩ | ⟨k, hk, hv⟩)
    · exact absurd h (xC_ne_srcC i)
    · exact Or.inl hv
    · rw [xC_inj] at hk
      subst hk
      exact Or.inr hv
  · rintro (hv | hv)
    · exact Or.inr (Or.inl ⟨i, rfl, hv⟩)
    · exact Or.inr (Or.inr ⟨i, rfl, hv⟩)

theorem edge_srcC_iff {v : cycV M} : (cycGraph M).Edge (srcC M) v ↔ v = xC M 0 := by
  rw [cycGraph_edge_iff, cycEdge]
  constructor
  · rintro (⟨-, hv⟩ | ⟨k, hk, -⟩ | ⟨k, hk, -⟩)
    · exact hv
    · exact absurd hk.symm (xC_ne_srcC k)
    · exact absurd hk.symm (xC_ne_srcC k)
  · intro hv
    exact Or.inl ⟨rfl, hv⟩

theorem natCast_succ_fin (j : ℕ) : ((j + 1 : ℕ) : Fin (M + 2)) = (j : Fin (M + 2)) + 1 := by
  push_cast
  rfl

theorem isChain_cycTail (j n : ℕ) : (cycTail M j n).IsChain (cycGraph M).Edge := by
  induction n generalizing j with
  | zero =>
      simp only [cycTail]
      exact List.IsChain.cons_cons (edge_xC_iff.2 (Or.inl rfl)) (List.IsChain.singleton _)
  | succ n ih =>
      rw [cycTail_succ]
      obtain ⟨r, hr⟩ := cycTail_eq_cons (M := M) (j + 1) n
      have h := ih (j + 1)
      rw [hr] at h ⊢
      exact List.IsChain.cons_cons (edge_xC_iff.2 (Or.inr (by rw [natCast_succ_fin]))) h

/-- **Every `cycTraj M n` is a walk of `𝒞_N`.** -/
theorem isChain_cycTraj (n : ℕ) : (cycTraj M n).IsChain (cycGraph M).Edge := by
  obtain ⟨r, hr⟩ := cycTail_eq_cons (M := M) 0 n
  have h := isChain_cycTail (M := M) 0 n
  rw [cycTraj, hr]
  rw [hr] at h
  exact List.IsChain.cons_cons (edge_srcC_iff.2 (by simp only [Nat.cast_zero])) h

theorem eq_cycTail_of_walk :
    ∀ (l : List (cycV M)) (j : ℕ), (xC M (j : Fin (M + 2)) :: l).IsChain (cycGraph M).Edge →
      (xC M (j : Fin (M + 2)) :: l).getLast? = some (snkC M) →
      ∃ n, xC M (j : Fin (M + 2)) :: l = cycTail M j n
  | [], j, _, hlast => by
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      exact absurd hlast (xC_ne_snkC _)
  | b :: l, j, hch, hlast => by
      rw [List.isChain_cons_cons] at hch
      rcases edge_xC_iff.1 hch.1 with hb | hb
      · subst hb
        cases l with
        | nil => exact ⟨0, rfl⟩
        | cons c l =>
            rw [List.isChain_cons_cons] at hch
            exact absurd hch.2.1 (by
              simpa only [cycGraph_snk] using (cycGraph M).no_edge_out_of_snk c)
      · rw [← natCast_succ_fin] at hb
        subst hb
        have hlast' : (xC M ((j + 1 : ℕ) : Fin (M + 2)) :: l).getLast? = some (snkC M) := by
          rw [List.getLast?_cons_cons] at hlast
          exact hlast
        obtain ⟨n, hn⟩ := eq_cycTail_of_walk l (j + 1) hch.2 hlast'
        exact ⟨n + 1, by rw [cycTail_succ, ← hn]⟩

/-- **The trajectories of `𝒞_N` are exactly the `cycTraj M n`**: every walk from `s₀` to `s_f`
is one of them. -/
theorem eq_cycTraj {l : List (cycV M)} (hch : l.IsChain (cycGraph M).Edge)
    (hhead : l.head? = some (srcC M)) (hlast : l.getLast? = some (snkC M)) :
    ∃ n, l = cycTraj M n := by
  cases l with
  | nil => simp only [List.head?_nil, reduceCtorEq] at hhead
  | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      cases l with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          exact absurd hlast srcC_ne_snkC
      | cons b l =>
          rw [List.isChain_cons_cons] at hch
          have hb := edge_srcC_iff.1 hch.1
          subst hb
          have h0 : xC M 0 = xC M ((0 : ℕ) : Fin (M + 2)) := by simp only [Nat.cast_zero]
          rw [List.getLast?_cons_cons] at hlast
          rw [h0] at hch hlast ⊢
          obtain ⟨n, hn⟩ := eq_cycTail_of_walk l 0 hch.2 hlast
          exact ⟨n, by rw [cycTraj, hn]⟩

/-! ## A full-support Markov forward policy on `𝒞_N` -/

/-- **The Markov forward policy `cycPol M a`**: `s₀ → x₁` with probability `1`; from every `xᵢ`,
continue to `x_{i+1}` with probability `a`, terminate with probability `1 − a`. -/
noncomputable def cycPol (M : ℕ) (a : ℝ) : cycV M → cycV M → ℝ
  | none, v => if v = xC M 0 then 1 else 0
  | some none, _ => 0
  | some (some _), none => 0
  | some (some _), some none => 1 - a
  | some (some i), some (some j) => if j = i + 1 then a else 0

theorem cycPol_src (a : ℝ) (v : cycV M) : cycPol M a (srcC M) v = if v = xC M 0 then 1 else 0 :=
  rfl

theorem cycPol_x_snk (a : ℝ) (i : Fin (M + 2)) : cycPol M a (xC M i) (snkC M) = 1 - a := rfl

theorem cycPol_x_x (a : ℝ) (i j : Fin (M + 2)) :
    cycPol M a (xC M i) (xC M j) = if j = i + 1 then a else 0 := rfl

theorem cycPol_x_src (a : ℝ) (i : Fin (M + 2)) : cycPol M a (xC M i) (srcC M) = 0 := rfl

theorem cycPol_snk (a : ℝ) (v : cycV M) : cycPol M a (snkC M) v = 0 := rfl

theorem cycPol_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (u v : cycV M) : 0 ≤ cycPol M a u v := by
  rcases u with _ | _ | i
  · change 0 ≤ cycPol M a (srcC M) v
    rw [cycPol_src]; split_ifs <;> norm_num
  · exact le_rfl
  · rcases v with _ | _ | j
    · exact le_rfl
    · change 0 ≤ 1 - a; linarith
    · change 0 ≤ cycPol M a (xC M i) (xC M j)
      rw [cycPol_x_x]; split_ifs <;> linarith

/-- **Full support**: `cycPol M a` is positive on every edge of `𝒞_N`. -/
theorem cycPol_pos_of_edge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {u v : cycV M}
    (h : (cycGraph M).Edge u v) : 0 < cycPol M a u v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩
  · rw [cycPol_src, if_pos rfl]; exact one_pos
  · rw [cycPol_x_snk]; linarith
  · rw [cycPol_x_x, if_pos rfl]; exact ha0

/-- `cycPol M a` is carried by the edges of `𝒞_N`. -/
theorem cycPol_supp {a : ℝ} {u v : cycV M} (h : cycPol M a u v ≠ 0) : (cycGraph M).Edge u v := by
  rcases u with _ | _ | i
  · change cycPol M a (srcC M) v ≠ 0 at h
    rw [cycPol_src] at h
    split_ifs at h with hv
    · exact edge_srcC_iff.2 hv
    · exact absurd rfl h
  · exact absurd rfl h
  · rcases v with _ | _ | j
    · exact absurd rfl h
    · exact edge_xC_iff.2 (Or.inl rfl)
    · change cycPol M a (xC M i) (xC M j) ≠ 0 at h
      rw [cycPol_x_x] at h
      split_ifs at h with hj
      · exact edge_xC_iff.2 (Or.inr (by rw [hj]; rfl))
      · exact absurd rfl h

/-- `cycPol M a` is a probability at every state but the sink. -/
theorem cycPol_row_sum (a : ℝ) {u : cycV M} (hu : u ≠ snkC M) : ∑ v, cycPol M a u v = 1 := by
  rw [sum_cycV]
  rcases u with _ | _ | i
  · change cycPol M a (srcC M) (srcC M) + (cycPol M a (srcC M) (snkC M)
      + ∑ j, cycPol M a (srcC M) (xC M j)) = 1
    simp only [cycPol_src, srcC_ne_xC, snkC_ne_xC, if_false, xC_inj]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (M + 2)), if_pos (mem_univ _)]
    ring
  · exact absurd rfl hu
  · change cycPol M a (xC M i) (srcC M) + (cycPol M a (xC M i) (snkC M)
      + ∑ j, cycPol M a (xC M i) (xC M j)) = 1
    simp only [cycPol_x_src, cycPol_x_snk, cycPol_x_x]
    rw [Finset.sum_ite_eq' Finset.univ (i + 1), if_pos (mem_univ _)]
    ring

/-! ## Its trajectory law -/

theorem pathProb_cycTail (a : ℝ) (j n : ℕ) :
    pathProb (cycPol M a) (cycTail M j n) = a ^ n * (1 - a) := by
  induction n generalizing j with
  | zero =>
      simp only [cycTail, pathProb, cycPol_x_snk, pow_zero, one_mul, mul_one]
  | succ n ih =>
      rw [cycTail_succ]
      obtain ⟨r, hr⟩ := cycTail_eq_cons (M := M) (j + 1) n
      have h := ih (j + 1)
      rw [hr] at h ⊢
      rw [pathProb, h, cycPol_x_x, if_pos (natCast_succ_fin j), pow_succ]
      ring

/-- **The trajectory law of `cycPol M a`**: `p_F(cycTraj n) = aⁿ(1 − a)`. -/
theorem pathProb_cycTraj (a : ℝ) (n : ℕ) :
    pathProb (cycPol M a) (cycTraj M n) = a ^ n * (1 - a) := by
  obtain ⟨r, hr⟩ := cycTail_eq_cons (M := M) 0 n
  have h := pathProb_cycTail (M := M) a 0 n
  rw [hr] at h
  rw [cycTraj, hr, pathProb, h, cycPol_src, if_pos (by simp only [Nat.cast_zero]), one_mul]

/-- **It is a probability on the trajectories**, for `0 ≤ a < 1`. -/
theorem hasSum_cycTraj {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun n => pathProb (cycPol M a) (cycTraj M n)) 1 := by
  simp only [pathProb_cycTraj]
  have h := (hasSum_geometric_of_lt_one ha0 ha1).mul_right (1 - a)
  rwa [inv_mul_cancel₀ (by linarith)] at h

/-- With `a = (n+1)/(n+2)` the trajectory of length index `n` has
`p_F ≥ e^{−1}/(n+2) > 1/(3(n+2))`. -/
theorem pathProb_cycTraj_ge (n : ℕ) :
    1 / (3 * ((n : ℝ) + 2))
      < pathProb (cycPol M (((n : ℝ) + 1) / ((n : ℝ) + 2))) (cycTraj M n) := by
  rw [pathProb_cycTraj]
  set a : ℝ := ((n : ℝ) + 1) / ((n : ℝ) + 2) with ha
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have ha0 : 0 < a := div_pos hn1 hn2
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hn2]; linarith
  have h1a : 1 - a = 1 / ((n : ℝ) + 2) := by rw [ha]; field_simp; ring
  -- `(1/a)^{n+1} = (1 + 1/(n+1))^{n+1} ≤ e`
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

/-! ## `sup_{p_F} M' = +∞` over Markov forward policies -/

theorem natCast_fin_add_mul (i : Fin (M + 2)) (k : ℕ) :
    ((i.val + k * (M + 2) : ℕ) : Fin (M + 2)) = i := by
  ext
  rw [Fin.val_natCast, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

/-- **Summability forces `liminf (n+2) p_B(τ_n|x) = 0` along the trajectories into `x`.** -/
theorem exists_mul_lt (i : Fin (M + 2)) {pB : ℕ → ℝ} (hB0 : ∀ n, 0 ≤ pB n) (hBs : Summable pB)
    {δ : ℝ} (hδ : 0 < δ) : ∃ n : ℕ, (n : Fin (M + 2)) = i ∧ ((n : ℝ) + 2) * pB n < δ := by
  by_contra hcon
  push Not at hcon
  let f : ℕ → ℝ := fun k => pB (i.val + k * (M + 2))
  have hinj : Function.Injective fun k : ℕ => i.val + k * (M + 2) := by
    intro k k' h
    have : k * (M + 2) = k' * (M + 2) := by simpa only [Nat.add_left_cancel_iff] using h
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  have hf : Summable f := hBs.comp_injective hinj
  have hC : (0 : ℝ) < 2 * ((M : ℝ) + 2) / δ := by positivity
  -- `1/(k+1) ≤ (2N/δ) f k`
  have hle : ∀ k : ℕ, ((k : ℝ) + 1)⁻¹ ≤ (2 * ((M : ℝ) + 2) / δ) * f k := by
    intro k
    have hk := hcon (i.val + k * (M + 2)) (natCast_fin_add_mul i k)
    have hi : (i.val : ℝ) + 1 ≤ (M : ℝ) + 2 := by
      have := i.isLt; exact_mod_cast this
    have hfk : 0 ≤ f k := hB0 _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hden : ((i.val + k * (M + 2) : ℕ) : ℝ) + 2 ≤ 2 * ((M : ℝ) + 2) * ((k : ℝ) + 1) := by
      push_cast
      nlinarith
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h1 : δ ≤ 2 * ((M : ℝ) + 2) * ((k : ℝ) + 1) * f k :=
      le_trans hk (mul_le_mul_of_nonneg_right hden hfk)
    rw [inv_le_iff_one_le_mul₀ hk1, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hδ,
      one_mul]
    linarith
  have hsum : Summable fun k : ℕ => ((k : ℝ) + 1)⁻¹ :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle (hf.mul_left _)
  have hsum' : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsum
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).1 hsum')

/-- **`rem:path_space`, `sup_{p_F} M' = +∞` on `𝒞_N`, over full-support Markov forward
policies.** Let `x = x_{i+1}` and let `p_B(·|x)`, a function of the trajectory index, be
non-negative, summable and positive on every trajectory into `x`. For every `R` there is a
full-support Markov forward policy `cycPol M a`, `0 < a < 1`, and a trajectory `cycTraj M n` into
`x` with `p_B > 0` there and `p_F(τ)/p_B(τ|x) > R` — so `M' ≥ M > R`. -/
theorem cycle_exists_ratio_gt_markov (i : Fin (M + 2)) {pB : ℕ → ℝ} (hB0 : ∀ n, 0 ≤ pB n)
    (hBs : Summable pB) (hBpos : ∀ n : ℕ, (n : Fin (M + 2)) = i → 0 < pB n) (R : ℝ) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∃ n : ℕ, (n : Fin (M + 2)) = i ∧ 0 < pB n ∧
      R < pathProb (cycPol M a) (cycTraj M n) / pB n := by
  have hR1 : (0 : ℝ) < |R| + 1 := by positivity
  have hδ : (0 : ℝ) < 1 / (3 * (|R| + 1)) := by positivity
  obtain ⟨n, hni, hlt⟩ := exists_mul_lt i hB0 hBs hδ
  have hp := hBpos n hni
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine ⟨((n : ℝ) + 1) / ((n : ℝ) + 2), div_pos (by positivity) hn2,
    (div_lt_one hn2).2 (by linarith), n, hni, hp, ?_⟩
  have hge := pathProb_cycTraj_ge (M := M) n
  -- `R < 1/(3 (n+2) pB) < p_F/pB`
  have hq : 0 < 3 * ((n : ℝ) + 2) := by positivity
  have hkey : R < 1 / (3 * ((n : ℝ) + 2)) / pB n := by
    rw [div_div, lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hlt
    have hRle : R ≤ |R| := le_abs_self R
    have hpos : 0 ≤ 3 * ((n : ℝ) + 2) * pB n := by positivity
    nlinarith
  exact hkey.trans (div_lt_div_of_pos_right hge hp)

/-- **The same, as unboundedness**: the ratios `p_F(τ)/p_B(τ|x)` over full-support Markov policies
`cycPol M a` and trajectories `τ` into `x` charged by `p_B` are not bounded above. -/
theorem cycle_ratio_not_bddAbove_markov (i : Fin (M + 2)) {pB : ℕ → ℝ} (hB0 : ∀ n, 0 ≤ pB n)
    (hBs : Summable pB) (hBpos : ∀ n : ℕ, (n : Fin (M + 2)) = i → 0 < pB n) :
    ¬ BddAbove {r : ℝ | ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∃ n : ℕ, (n : Fin (M + 2)) = i ∧ 0 < pB n ∧
      r = pathProb (cycPol M a) (cycTraj M n) / pB n} := by
  rintro ⟨R, hR⟩
  obtain ⟨a, ha0, ha1, n, hni, hp, hlt⟩ := cycle_exists_ratio_gt_markov i hB0 hBs hBpos R
  exact absurd (hR ⟨a, ha0, ha1, n, hni, hp, rfl⟩) (not_le.2 hlt)

/-! ## Inhabitation -/

/-- **The hypotheses are inhabited** (kb 0025): for every `x = x_{i+1}`, the law
`p_B(cycTraj n|x) = 2^{-(n+1)} / Z` on the trajectories into `x` (and `0` elsewhere), with `Z` its
mass, is a probability charging each trajectory into `x`, and `cycPol M ½` is a full-support
Markov policy whose trajectory law is a probability. -/
theorem inhabit_markov_cycle (i : Fin (M + 2)) :
    ∃ pB : ℕ → ℝ, (∀ n, 0 ≤ pB n) ∧ Summable pB ∧ (∀ n : ℕ, (n : Fin (M + 2)) = i → 0 < pB n) ∧
      (∀ n : ℕ, (n : Fin (M + 2)) ≠ i → pB n = 0) ∧
      (∀ u v, (cycGraph M).Edge u v → 0 < cycPol M (1 / 2) u v) ∧
      HasSum (fun n => pathProb (cycPol M (1 / 2)) (cycTraj M n)) 1 := by
  classical
  let g : ℕ → ℝ := fun n => if (n : Fin (M + 2)) = i then (1 / 2 : ℝ) ^ (n + 1) else 0
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [g]; split_ifs <;> positivity
  have hgs : Summable g :=
    Summable.of_nonneg_of_le hg0 (fun n => by
      simp only [g]; split_ifs
      · exact le_rfl
      · positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left
        (1 / 2) |>.congr fun n => by rw [pow_succ]; ring)
  have hgpos : ∀ n : ℕ, (n : Fin (M + 2)) = i → 0 < g n := fun n hn => by
    simp only [g, hn, if_true]; positivity
  have hZ : 0 < ∑' n, g n :=
    hgs.tsum_pos hg0 i.val (hgpos _ (by ext; simp only [Fin.val_natCast, Nat.mod_eq_of_lt i.isLt]))
  refine ⟨fun n => g n / ∑' n, g n, fun n => div_nonneg (hg0 n) hZ.le, hgs.div_const _,
    fun n hn => div_pos (hgpos n hn) hZ, fun n hn => by simp only [g, hn, if_false, zero_div],
    fun u v h => cycPol_pos_of_edge (by norm_num) (by norm_num) h,
    hasSum_cycTraj (by norm_num) (by norm_num)⟩

end GFNBounds.Silva.PathSpaceMarkov
