import GFNBounds.Doubling.Weight
import GFNBounds.Doubling.DescentStatement

/-!
# `lem:doubling_weight` in the paper's form: `E(|Z_ℓ − 1| | Y_0 = m) ≤ c₃/ℓ`

**`lem:doubling_weight`** — `app_doubling.tex:1357–1369` (statement), `1371–1397` (proof).

> In the setting of Definitions `def:doubling_setting` and `def:doubling_decay_notation`, with the
> constant `c₄` of `lem:doubling_descent` and `γ`, `c₅` and `ℓ₂` of `lem:doubling_escape`, put
> `c₃ := 8c₅c₄` and `ℓ₃ := max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)`, which depend on `c` and `d`
> alone. Let `ℓ ≥ ℓ₃` be an integer, let `(Y_n)_{n≥0}` and `N_ℓ` be the descent chain of
> `lem:doubling_descent` at the level `ℓ` and its exit time, and let `Z_ℓ := ∏_{n<N_ℓ} R₀(Y_n)` be
> the weight of `lem:doubling_descent`(3). Then, for every integer `m ≥ 2ℓ`,
> `E(|Z_ℓ − 1| | Y_0 = m) ≤ c₃/ℓ`.   `(eq:doubling_weight)`

## What was missing, and what this file adds

`GFNBounds/Doubling/Weight.lean` proves the lemma's *consequence* — for `g` bounded by `B`,
`|E(Z_ℓ g(Y_{N_ℓ})) − E(g(Y_{N_ℓ}))| ≤ B·c₃/ℓ` (`Decay.weight_bound`) — because `E(|Z_ℓ − 1|)` is
not a recursion in the state alone: `|R₀(y)·Z' − 1|` does not factor through `Z'`. It never states
`eq:doubling_weight`, and it uses its own sharper constants. This file states the lemma itself.

**The running product is carried as a second state variable.** The joint recursion

  `descJoint ℓ G y w = if y < 2ℓ then G(y, w) else Σ_{j∈W(y)} k_y(j) · descJoint ℓ G j (w·R₀(y))`,

`k_y(j) = w_y(j)/R₀(y)` the transition law of `lem:doubling_descent`, is
`E(G(Y_{N_ℓ}, w·Z_ℓ) | Y_0 = y)`, and `E(|Z_ℓ − 1| | Y_0 = m)` is `weightDev ℓ m :=
descJoint ℓ (·, v ↦ |v − 1|) m 1`. Three facts tie it to what the library already has and to the
paper's reading of the expectation:

* **It is an honest finite expectation** (`descJoint_eq_sum_paths`, `weightDev_eq_sum_paths`): it
  equals `Σ_{l ∈ descPaths ℓ y} pathProb l · G(pathExit l, w·pathZ l)`, a sum over the finite set
  of stopped trajectories `l = (Y_0, …, Y_N)` with probabilities `∏_{n<N} k_{Y_n}(Y_{n+1})`, which
  are positive (`pathProb_pos`) and sum to `1` (`sum_pathProb`), and with `pathZ l =
  ∏_{n<N} R₀(Y_n)`. `mem_descPaths_iff` says the set is exactly the trajectories with `Y_0 = y`,
  `Y_n ≥ 2ℓ` and `Y_{n+1} ∈ W(Y_n)` for `n < N`, and `Y_N < 2ℓ`; `trajOf_mem_descPaths` and
  `exists_descentPath_of_mem` say these are exactly the trajectories `(Y_0, …, Y_{N_ℓ})` of the
  allowed paths of `DescentStatement.lean` (`IsDescentPath`, `exitTime`), with `pathZ` the very
  product `∏_{n<N_ℓ} R₀(Y_n)` of its `item3_Z_pos`.
* **Its marginals are the existing recursions**: `descJoint_mul_eq_descZ` (the `Z`-weighted exit
  law, hence `descW`), `descJoint_const_eq_descP` (the exit law), `descJoint_id_eq_descOne`
  (`E(Z_ℓ)`).
* **The paper's use of the lemma follows from it** (`abs_descW_sub_descP_le_weightDev`,
  `doubling_weight_transform`), and Jensen `|E(Z_ℓ) − 1| ≤ E|Z_ℓ − 1|` holds
  (`abs_descOne_sub_one_le_weightDev`).

**The proof.** The paper bounds `|Z_ℓ − 1| ≤ ∏_{n<N_ℓ}(1 + b̃(Y_n)) − 1` pathwise, with
`b̃(y) = e^{2c₄/y} − 1`, and applies `eq:doubling_product` at `H = 4c₄`. Here the pathwise step is
the invariant of a running pair (`descJoint_absDev_le_prodW`): if `|w − 1| ≤ v − 1` and
`|R₀(y) − 1| ≤ b(y)`, then `|w·R₀(y) − 1| ≤ v·(1 + b(y)) − 1`, because `|w| ≤ v`; carried through the
recursion it gives `E(|Z_ℓ − 1|) ≤ E(∏(1 + b(Y_n))) − 1` at any `b ≥ |R₀ − 1|`. At `b(y) = c₄/y`
(`eq:doubling_R0`), `H = c₄`, `Product.lean`'s `prodW_two_sided` and `e^x − 1 ≤ 2x` give
`E(|Z_ℓ − 1|) ≤ 2c₅c₄/ℓ`, which is `Weight.lean`'s `c₃ = 32c₅cτ` and is at most the paper's
`8c₅c₄/ℓ`.

## SCOPE (disclosed)

* **`E(· | Y_0 = m)` is the expectation against the finite law of the stopped trajectory**, the
  law in which a trajectory `(Y_0, …, Y_N)` has probability `∏_{n<N} k_{Y_n}(Y_{n+1})`. No Markov
  chain on a probability space is constructed: the horizon is bounded (every trajectory from `m`
  has at most `m + 1` states), so the law is a finite sum and none is needed; that this finite law is
  the law of `(Y_0, …, Y_{N_ℓ})` under a chain with kernel `k` is the definition of such a chain
  and is not a theorem here. The recursion `descJoint` is **not** the definition the statement
  rests on alone: `weightDev_eq_sum_paths` identifies it with the finite sum, and
  `doubling_weight_paths` states the bound on the sum directly. (Ruling R17 accepts a
  recursion-defined `E`; this file needs less.)
* **The constants are the paper's, made effective through the library's**: `c₄ = 16cτ`
  (`DescentStatement.lean`), `γ = √τ/(2(√τ+1))` (`Escape.lean`), `c₅ = 6/γ²` (`Sojourn.lean`),
  `ℓ₂ = ell2 d = max(d+1, ⌈16cτ⌉)` (`Escape.lean`, which discloses that its `ℓ₂` is not `≥ 2ℓ₁`).
  `c3Paper = 8c₅c₄` and `ell3Paper d = max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)` are the paper's
  formulas verbatim over those. **The bound does not depend on the choice of `ℓ₂`**:
  `doubling_weight_of_ceils` needs only `ℓ ≥ ⌈2c₄⌉` and `ℓ ≥ ⌈24c₄/γ²⌉`, so it holds at the
  paper's `ℓ₃` for any `ℓ₂` the escape lemma may be proved with, the paper's `ℓ₂ ≥ 2ℓ₁` included.
* **`m ≥ 2ℓ` is carried and unused**: `doubling_weight_of_ceils` holds at every state (below `2ℓ`
  the weight is the empty product and the deviation is `0`).
* **The paper's requirements `⌈24c₄/γ²⌉` and `⌈4c₄c₅⌉` coincide** (`twentyfour_c4_div_eq`:
  `24c₄/γ² = 4c₄c₅` since `c₅ = 6/γ²`). Harmless redundancy in the paper's `ℓ₃`, not an error.
* A **stronger** statement is also proved, `weightDev_le_c3`: `E(|Z_ℓ − 1|) ≤ c₃'/ℓ` at the
  library's `c₃' = 2c₅c₄ ≤ c₃` and `ℓ₃' = max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉) ≤ ℓ₃` (`c3_le_c3Paper`,
  `ell3_le_ell3Paper`).
* "Which depend on `c` and `d` alone": `c3Paper` and `ell3Paper` are functions of `(D, d)`, `D`
  bundling `c` and its Cramér root `p_*`; as in `DescentStatement.lean`, no further dependence
  clause is stated.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| setting, `s = 1`, `0 < c < 1`, `p = p_*`, `τ = 2^{p_*}` | ✓ carried by `Decay` |
| `c₄` of `lem:doubling_descent` | ✓ `Decay.c4 = 16cτ` |
| `γ`, `c₅`, `ℓ₂` of `lem:doubling_escape` | ✓ `Decay.gam`, `Decay.c5 = 6/γ²`, `Decay.ell2 d` |
| `c₃ := 8c₅c₄` | ✓ `Decay.c3Paper`, verbatim |
| `ℓ₃ := max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)` | ✓ `Decay.ell3Paper d`, verbatim; `ℓ₃ ≥ ℓ₁` (`ell1_le_ell3Paper`) so the chain is defined |
| `ℓ ≥ ℓ₃` an integer | ✓ carried (`hℓ`); weakened to two ceilings in `doubling_weight_of_ceils` |
| `(Y_n)`, `N_ℓ` the descent chain at level `ℓ` | ✓ its stopped trajectories `descPaths ℓ m` with their law `pathProb`, identified with `IsDescentPath`/`exitTime` |
| `Z_ℓ := ∏_{n<N_ℓ} R₀(Y_n)` | ✓ `pathZ`, equal to `DescentStatement.lean`'s product on every allowed path |
| `m ≥ 2ℓ` an integer | ✓ carried (`_hm`), unused |
| `E(|Z_ℓ − 1| ∣ Y_0 = m) ≤ c₃/ℓ` | ✓ `doubling_weight` (via `weightDev`) and `doubling_weight_paths` (the finite sum) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

variable (D : Decay)

/-- **`E(G(Y_{N_ℓ}, w·Z_ℓ) | Y_0 = y)`, with the running weight `w` as a second state variable.**
Below `2ℓ` the descent has exited and the weight is the empty product; above it, one step of the
transition law `k_y(j) = w_y(j)/R₀(y)` multiplies the running weight by `R₀(y)`.
`descJoint_eq_sum_paths` identifies it with the finite sum over stopped trajectories.

Well-founded because every `j ∈ W(y)` has `j < y` — `lem:doubling_descent`(1). -/
noncomputable def descJoint (D : Decay) (ℓ : ℕ) (G : ℕ → ℝ → ℝ) (y : ℕ) (w : ℝ) : ℝ :=
  if y < 2 * ℓ then G y w
  else ∑ j ∈ (window y).attach, D.kern y j.1 * descJoint D ℓ G j.1 (w * D.R0 y)
termination_by y
decreasing_by exact window_lt j.2

theorem descJoint_of_lt {ℓ : ℕ} (G : ℕ → ℝ → ℝ) {y : ℕ} (h : y < 2 * ℓ) (w : ℝ) :
    D.descJoint ℓ G y w = G y w := by
  rw [descJoint, if_pos h]

theorem descJoint_of_ge {ℓ : ℕ} (G : ℕ → ℝ → ℝ) {y : ℕ} (h : ¬ y < 2 * ℓ) (w : ℝ) :
    D.descJoint ℓ G y w = ∑ j ∈ window y, D.kern y j * D.descJoint ℓ G j (w * D.R0 y) := by
  rw [descJoint, if_neg h]
  exact Finset.sum_attach (window y) fun j => D.kern y j * D.descJoint ℓ G j (w * D.R0 y)

/-! ## The two marginals: the joint recursion restricts to the existing ones -/

/-- **The weighted marginal.** `E(w·Z_ℓ·g(Y_{N_ℓ}) | Y_0 = y) = w·E(Z_ℓ g(Y_{N_ℓ}) | Y_0 = y)`. -/
theorem descJoint_mul_eq_descZ {ℓ : ℕ} (g : ℕ → ℝ) :
    ∀ (y : ℕ) (w : ℝ), D.descJoint ℓ (fun j v => v * g j) y w = w * D.descZ ℓ g y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro w
    by_cases hlt : y < 2 * ℓ
    · rw [D.descJoint_of_lt _ hlt, D.descZ_of_lt _ hlt]
    · rw [D.descJoint_of_ge _ hlt, D.descZ_of_ge _ hlt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ih j (window_lt hj)]
      ring

/-- **The exit marginal.** `E(g(Y_{N_ℓ}) | Y_0 = y)` read off the joint recursion is `descP`. -/
theorem descJoint_const_eq_descP {ℓ : ℕ} (g : ℕ → ℝ) :
    ∀ (y : ℕ) (w : ℝ), D.descJoint ℓ (fun j _ => g j) y w = D.descP ℓ g y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro w
    by_cases hlt : y < 2 * ℓ
    · rw [D.descJoint_of_lt _ hlt, D.descP_of_lt _ hlt]
    · rw [D.descJoint_of_ge _ hlt, D.descP_of_ge _ hlt]
      exact Finset.sum_congr rfl fun j hj => by rw [ih j (window_lt hj)]

/-- **The expected weight.** `E(Z_ℓ | Y_0 = y)` read off the joint recursion is `descOne`. -/
theorem descJoint_id_eq_descOne {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y : ℕ) :
    D.descJoint ℓ (fun _ v => v) y 1 = D.descOne ℓ y := by
  have h := D.descJoint_mul_eq_descZ (ℓ := ℓ) (fun _ => 1) y 1
  simp only [mul_one, one_mul] at h
  rw [h, D.descZ_eq_descW hℓ]
  rfl

/-- The joint recursion is additive in the integrand. -/
theorem descJoint_sub {ℓ : ℕ} (F G : ℕ → ℝ → ℝ) :
    ∀ (y : ℕ) (w : ℝ), D.descJoint ℓ (fun j v => F j v - G j v) y w
      = D.descJoint ℓ F y w - D.descJoint ℓ G y w := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro w
    by_cases hlt : y < 2 * ℓ
    · rw [D.descJoint_of_lt _ hlt, D.descJoint_of_lt _ hlt, D.descJoint_of_lt _ hlt]
    · rw [D.descJoint_of_ge _ hlt, D.descJoint_of_ge _ hlt, D.descJoint_of_ge _ hlt,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ih j (window_lt hj)]
      ring

/-- **The joint recursion is an average.** If `|F| ≤ B·G` pointwise then
`|E(F(Y_{N_ℓ}, wZ_ℓ))| ≤ B·E(G(Y_{N_ℓ}, wZ_ℓ))`. -/
theorem abs_descJoint_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {F G : ℕ → ℝ → ℝ} {B : ℝ}
    (hFG : ∀ j v, |F j v| ≤ B * G j v) :
    ∀ (y : ℕ) (w : ℝ), |D.descJoint ℓ F y w| ≤ B * D.descJoint ℓ G y w := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro w
    by_cases hlt : y < 2 * ℓ
    · rw [D.descJoint_of_lt _ hlt, D.descJoint_of_lt _ hlt]
      exact hFG y w
    · have hy2 : 2 ≤ y := by omega
      rw [D.descJoint_of_ge _ hlt, D.descJoint_of_ge _ hlt, Finset.mul_sum]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j hj => ?_)
      have hk := D.kern_nonneg hy2 hj
      rw [abs_mul, abs_of_nonneg hk]
      calc D.kern y j * |D.descJoint ℓ F j (w * D.R0 y)|
          ≤ D.kern y j * (B * D.descJoint ℓ G j (w * D.R0 y)) :=
            mul_le_mul_of_nonneg_left (ih j (window_lt hj) _) hk
        _ = B * (D.kern y j * D.descJoint ℓ G j (w * D.R0 y)) := by ring

/-! ## The finite law of the trajectory: the recursion is an honest expectation -/

/-- **The trajectories `(Y_0, …, Y_{N_ℓ})` of the descent chain at the level `ℓ` from `y`**, as a
finite set of lists: `[y]` below `2ℓ`, and `y` prepended to a trajectory from some `j ∈ W(y)`
above it. -/
def descPaths (ℓ y : ℕ) : Finset (List ℕ) :=
  if y < 2 * ℓ then {[y]}
  else (window y).attach.biUnion fun j => (descPaths ℓ j.1).image (List.cons y)
termination_by y
decreasing_by exact window_lt j.2

theorem descPaths_of_lt {ℓ y : ℕ} (h : y < 2 * ℓ) : descPaths ℓ y = {[y]} := by
  rw [descPaths, if_pos h]

theorem descPaths_of_ge {ℓ y : ℕ} (h : ¬ y < 2 * ℓ) :
    descPaths ℓ y = (window y).biUnion fun j => (descPaths ℓ j).image (List.cons y) := by
  rw [descPaths, if_neg h]
  ext l
  simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, exists_prop]

/-- `Z_ℓ = ∏_{n<N_ℓ} R₀(Y_n)` of a trajectory `(Y_0, …, Y_N)`. -/
noncomputable def pathZ (D : Decay) (l : List ℕ) : ℝ :=
  ∏ n ∈ Finset.range (l.length - 1), D.R0 (l.getD n 0)

/-- The probability `∏_{n<N} k_{Y_n}(Y_{n+1})` of a trajectory `(Y_0, …, Y_N)` under the transition
law `k_y(j) = w_y(j)/R₀(y)` of `lem:doubling_descent`. -/
noncomputable def pathProb (D : Decay) (l : List ℕ) : ℝ :=
  ∏ n ∈ Finset.range (l.length - 1), D.kern (l.getD n 0) (l.getD (n + 1) 0)

/-- The last state `Y_N` of a trajectory `(Y_0, …, Y_N)`. -/
def pathExit (l : List ℕ) : ℕ := l.getD (l.length - 1) 0

/-- **A trajectory from `y` stopped at its exit below `2ℓ`**: `Y_0 = y`, `Y_n ≥ 2ℓ` and
`Y_{n+1} ∈ W(Y_n)` for every `n < N`, and `Y_N < 2ℓ`. -/
def IsExitTraj (ℓ y : ℕ) (l : List ℕ) : Prop :=
  l ≠ [] ∧ l.getD 0 0 = y ∧
    (∀ n, n + 1 < l.length → 2 * ℓ ≤ l.getD n 0 ∧ l.getD (n + 1) 0 ∈ window (l.getD n 0)) ∧
    pathExit l < 2 * ℓ

theorem pathZ_cons (y : ℕ) {l : List ℕ} (hl : l ≠ []) :
    D.pathZ (y :: l) = D.R0 y * D.pathZ l := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [pathZ, List.length_cons, Nat.add_sub_cancel]
  rw [Finset.prod_range_succ', mul_comm]
  simp only [List.getD_cons_succ, List.getD_cons_zero]

theorem pathProb_cons (y : ℕ) {l : List ℕ} (hl : l ≠ []) :
    D.pathProb (y :: l) = D.kern y (l.getD 0 0) * D.pathProb l := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [pathProb, List.length_cons, Nat.add_sub_cancel]
  rw [Finset.prod_range_succ', mul_comm]
  simp only [List.getD_cons_succ, List.getD_cons_zero]

theorem pathExit_cons (y : ℕ) {l : List ℕ} (hl : l ≠ []) : pathExit (y :: l) = pathExit l := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [pathExit, List.length_cons, Nat.add_sub_cancel, List.getD_cons_succ]

theorem head_of_mem_descPaths {ℓ : ℕ} :
    ∀ (y : ℕ) {l : List ℕ}, l ∈ descPaths ℓ y → l ≠ [] ∧ l.getD 0 0 = y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y _ =>
    intro l hl
    by_cases hlt : y < 2 * ℓ
    · rw [descPaths_of_lt hlt, Finset.mem_singleton] at hl
      subst hl
      exact ⟨List.cons_ne_nil _ _, List.getD_cons_zero⟩
    · rw [descPaths_of_ge hlt, Finset.mem_biUnion] at hl
      obtain ⟨j, _, hl⟩ := hl
      rw [Finset.mem_image] at hl
      obtain ⟨l', _, rfl⟩ := hl
      exact ⟨List.cons_ne_nil _ _, List.getD_cons_zero⟩

/-- **The finite set of lists is exactly the set of stopped trajectories.** -/
theorem mem_descPaths_iff {ℓ : ℕ} :
    ∀ (y : ℕ) (l : List ℕ), l ∈ descPaths ℓ y ↔ IsExitTraj ℓ y l := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro l
    by_cases hlt : y < 2 * ℓ
    · rw [descPaths_of_lt hlt, Finset.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨List.cons_ne_nil _ _, List.getD_cons_zero, fun n hn => ?_, ?_⟩
        · simp only [List.length_cons, List.length_nil] at hn; omega
        · simp only [pathExit, List.length_cons, List.length_nil, Nat.sub_self,
            List.getD_cons_zero]
          exact hlt
      · rintro ⟨hne, h0, hstep, _⟩
        obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
        rw [List.getD_cons_zero] at h0
        subst h0
        rcases t with _ | ⟨b, t⟩
        · rfl
        · have h := (hstep 0 (by simp only [List.length_cons]; omega)).1
          rw [List.getD_cons_zero] at h
          omega
    · rw [descPaths_of_ge hlt, Finset.mem_biUnion]
      constructor
      · rintro ⟨j, hj, hl⟩
        rw [Finset.mem_image] at hl
        obtain ⟨l', hl', rfl⟩ := hl
        obtain ⟨hne', h0', hstep', hexit'⟩ := (ih j (window_lt hj) l').mp hl'
        refine ⟨List.cons_ne_nil _ _, List.getD_cons_zero, fun n hn => ?_, ?_⟩
        · rcases n with _ | k
          · simp only [List.getD_cons_zero, List.getD_cons_succ, h0']
            exact ⟨by omega, hj⟩
          · simp only [List.getD_cons_succ]
            exact hstep' k (by simp only [List.length_cons] at hn; omega)
        · rw [pathExit_cons y hne']; exact hexit'
      · rintro ⟨hne, h0, hstep, hexit⟩
        obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
        rw [List.getD_cons_zero] at h0
        subst h0
        rcases t with _ | ⟨b, t⟩
        · simp only [pathExit, List.length_cons, List.length_nil, Nat.sub_self,
            List.getD_cons_zero] at hexit
          exact absurd hexit hlt
        · have h1 := hstep 0 (by simp only [List.length_cons]; omega)
          simp only [List.getD_cons_zero, List.getD_cons_succ] at h1
          refine ⟨b, h1.2, Finset.mem_image.mpr ⟨b :: t, ?_, rfl⟩⟩
          refine (ih b (window_lt h1.2) (b :: t)).mpr
            ⟨List.cons_ne_nil _ _, List.getD_cons_zero, fun n hn => ?_, ?_⟩
          · have h := hstep (n + 1) (by simp only [List.length_cons] at hn ⊢; omega)
            simp only [List.getD_cons_succ] at h
            exact h
          · rw [pathExit_cons a (List.cons_ne_nil b t)] at hexit; exact hexit

/-- Every trajectory has positive probability: the finite law charges exactly `descPaths`. -/
theorem pathProb_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y : ℕ} {l : List ℕ} (hl : l ∈ descPaths ℓ y) :
    0 < D.pathProb l := by
  obtain ⟨_, _, hstep, _⟩ := (mem_descPaths_iff y l).mp hl
  refine Finset.prod_pos fun n hn => ?_
  have hn' : n + 1 < l.length := by rw [Finset.mem_range] at hn; omega
  obtain ⟨h2, hw⟩ := hstep n hn'
  have hy2 : 2 ≤ l.getD n 0 := by omega
  exact div_pos (D.wm_pos (by omega) (one_le_of_mem_window' (by omega) hw)) (D.R0_pos hy2)

/-- **The recursion is the expectation against the finite law of the trajectory.**
`descJoint ℓ G y w = Σ_{(Y_0,…,Y_N) ∈ descPaths ℓ y} P(Y_0,…,Y_N) · G(Y_N, w·∏_{n<N} R₀(Y_n))`. -/
theorem descJoint_eq_sum_paths {ℓ : ℕ} (G : ℕ → ℝ → ℝ) :
    ∀ (y : ℕ) (w : ℝ), D.descJoint ℓ G y w
      = ∑ l ∈ descPaths ℓ y, D.pathProb l * G (pathExit l) (w * D.pathZ l) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro w
    by_cases hlt : y < 2 * ℓ
    · rw [D.descJoint_of_lt _ hlt, descPaths_of_lt hlt, Finset.sum_singleton]
      simp only [pathProb, pathZ, pathExit, List.length_cons, List.length_nil, Nat.sub_self,
        Finset.range_zero, Finset.prod_empty, List.getD_cons_zero, one_mul, mul_one]
    · have hdisj : (↑(window y) : Set ℕ).PairwiseDisjoint
          fun j => (descPaths ℓ j).image (List.cons y) := by
        intro j₁ _ j₂ _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro l hl₁ hl₂
        rw [Finset.mem_image] at hl₁ hl₂
        obtain ⟨a, ha, rfl⟩ := hl₁
        obtain ⟨b, hb, hab⟩ := hl₂
        have hba : b = a := List.cons_injective hab
        subst hba
        exact hne ((head_of_mem_descPaths j₁ ha).2.symm.trans (head_of_mem_descPaths j₂ hb).2)
      rw [D.descJoint_of_ge _ hlt, descPaths_of_ge hlt, Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.sum_image (fun a _ b _ h => List.cons_injective h), ih j (window_lt hj),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      obtain ⟨hne, hhead⟩ := head_of_mem_descPaths j hl
      rw [D.pathProb_cons y hne, D.pathZ_cons y hne, pathExit_cons y hne, hhead,
        ← mul_assoc w (D.R0 y) (D.pathZ l)]
      ring

/-! ### The lists are the trajectories of `DescentStatement.lean`'s allowed paths -/

/-- The trajectory `(Y_0, …, Y_{N_ℓ})` of a path `Y`, with `N_ℓ = exitTime ℓ Y`. -/
noncomputable def trajOf (ℓ : ℕ) (Y : ℕ → ℕ) : List ℕ := (List.range (exitTime ℓ Y + 1)).map Y

theorem length_trajOf (ℓ : ℕ) (Y : ℕ → ℕ) : (trajOf ℓ Y).length = exitTime ℓ Y + 1 := by
  rw [trajOf, List.length_map, List.length_range]

theorem getD_trajOf {ℓ : ℕ} {Y : ℕ → ℕ} {n : ℕ} (hn : n ≤ exitTime ℓ Y) :
    (trajOf ℓ Y).getD n 0 = Y n := by
  rw [List.getD_eq_getElem _ _ (by rw [length_trajOf]; omega)]
  simp only [trajOf, List.getElem_map, List.getElem_range]

/-- **Every allowed path from `m ≥ 2ℓ` is counted, with its own `Z_ℓ`, its own exit state and the
product of its transition probabilities.** `Z_ℓ = ∏_{n<N_ℓ} R₀(Y_n)` is verbatim the product
`DescentStatement.lean`'s `item3_Z_pos` speaks of. -/
theorem trajOf_mem_descPaths {ℓ m : ℕ} {Y : ℕ → ℕ} (hY : IsDescentPath ℓ Y) (h0 : Y 0 = m)
    (hm : 2 * ℓ ≤ m) :
    trajOf ℓ Y ∈ descPaths ℓ m ∧
      D.pathZ (trajOf ℓ Y) = ∏ n ∈ Finset.range (exitTime ℓ Y), D.R0 (Y n) ∧
      D.pathProb (trajOf ℓ Y) = ∏ n ∈ Finset.range (exitTime ℓ Y), D.kern (Y n) (Y (n + 1)) ∧
      pathExit (trajOf ℓ Y) = Y (exitTime ℓ Y) := by
  obtain ⟨-, hN, hbefore, -⟩ := exitTime_spec hY h0 hm
  have hlen : (trajOf ℓ Y).length - 1 = exitTime ℓ Y := by rw [length_trajOf]; omega
  have hexit : pathExit (trajOf ℓ Y) = Y (exitTime ℓ Y) := by
    rw [pathExit, hlen, getD_trajOf le_rfl]
  refine ⟨(mem_descPaths_iff m _).mpr ⟨?_, ?_, fun n hn => ?_, ?_⟩, ?_, ?_, hexit⟩
  · rw [← List.length_pos_iff, length_trajOf]; omega
  · rw [getD_trajOf (Nat.zero_le _), h0]
  · rw [length_trajOf] at hn
    rw [getD_trajOf (by omega), getD_trajOf (by omega)]
    have h2 := hbefore n (by omega)
    exact ⟨h2, (hY n).1 h2⟩
  · rw [hexit]; exact hN
  · rw [pathZ, hlen]
    exact Finset.prod_congr rfl fun n hn => by
      rw [getD_trajOf (by rw [Finset.mem_range] at hn; omega)]
  · rw [pathProb, hlen]
    exact Finset.prod_congr rfl fun n hn => by
      rw [Finset.mem_range] at hn
      rw [getD_trajOf (by omega), getD_trajOf (by omega)]

/-- **Every counted list is the trajectory of an allowed path.** Extend it by its exit state. -/
theorem exists_descentPath_of_mem {ℓ m : ℕ} {l : List ℕ} (hl : l ∈ descPaths ℓ m) :
    ∃ Y : ℕ → ℕ, IsDescentPath ℓ Y ∧ Y 0 = m ∧ trajOf ℓ Y = l := by
  obtain ⟨hne, h0, hstep, hexit⟩ := (mem_descPaths_iff m l).mp hl
  have hlen : 1 ≤ l.length := List.length_pos_iff.mpr hne
  set Y : ℕ → ℕ := fun n => l.getD (min n (l.length - 1)) 0 with hYdef
  have hYlt : ∀ n, n + 1 < l.length → Y n = l.getD n 0 := fun n hn => by
    rw [hYdef]; simp only; rw [Nat.min_eq_left (by omega)]
  have hYge : ∀ n, l.length - 1 ≤ n → Y n = pathExit l := fun n hn => by
    rw [hYdef, pathExit]; simp only; rw [Nat.min_eq_right hn]
  have hpath : IsDescentPath ℓ Y := by
    intro n
    by_cases hn : n + 1 < l.length
    · obtain ⟨h2, hw⟩ := hstep n hn
      rw [hYlt n hn]
      refine ⟨fun _ => ?_, fun h => absurd h2 (by omega)⟩
      by_cases hn' : n + 2 < l.length
      · rw [hYlt (n + 1) hn']; exact hw
      · rw [hYge (n + 1) (by omega)]
        have hidx : l.length - 1 = n + 1 := by omega
        rw [pathExit, hidx]; exact hw
    · rw [hYge n (by omega), hYge (n + 1) (by omega)]
      exact ⟨fun h => absurd hexit (by omega), fun _ => rfl⟩
  have hY0 : Y 0 = m := by
    rw [hYdef]; simp only; rw [Nat.zero_min]; exact h0
  have hexitY : Y (l.length - 1) < 2 * ℓ := by rw [hYge _ le_rfl]; exact hexit
  have hN : exitTime ℓ Y = l.length - 1 := by
    have hmem : l.length - 1 ∈ {n | Y n < 2 * ℓ} := hexitY
    refine le_antisymm (Nat.sInf_le hmem) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hin : Y (exitTime ℓ Y) < 2 * ℓ := Nat.sInf_mem ⟨_, hmem⟩
    rw [hYlt (exitTime ℓ Y) (by omega)] at hin
    exact absurd (hstep (exitTime ℓ Y) (by omega)).1 (by omega)
  refine ⟨Y, hpath, hY0, List.ext_getElem (by rw [length_trajOf, hN]; omega) fun n h₁ h₂ => ?_⟩
  rw [← List.getD_eq_getElem _ 0 h₁, ← List.getD_eq_getElem _ 0 h₂,
    getD_trajOf (by rw [length_trajOf] at h₁; omega)]
  by_cases hn : n + 1 < l.length
  · exact hYlt n hn
  · rw [hYge n (by omega), pathExit]
    congr 1
    omega

/-- The finite law is a probability: its masses sum to `1` from every state `y ≥ ℓ`. -/
theorem sum_pathProb {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y : ℕ} (hy : ℓ ≤ y) :
    ∑ l ∈ descPaths ℓ y, D.pathProb l = 1 := by
  have h := D.descJoint_eq_sum_paths (ℓ := ℓ) (fun _ _ => (1 : ℝ)) y 1
  rw [D.descJoint_const_eq_descP (ℓ := ℓ) (fun _ => 1) y 1, D.descP_one hℓ y hy] at h
  simp only [mul_one] at h
  exact h.symm

/-! ## The weight deviation -/

/-- **`E(|Z_ℓ − 1| | Y_0 = m)`**, the left side of `eq:doubling_weight`: the joint recursion at
the integrand `(j, v) ↦ |v − 1|`, started with running weight `1`. -/
noncomputable def weightDev (D : Decay) (ℓ m : ℕ) : ℝ :=
  D.descJoint ℓ (fun _ v => |v - 1|) m 1

/-- **`E(|Z_ℓ − 1| | Y_0 = m)` is the finite sum over trajectories.** -/
theorem weightDev_eq_sum_paths (ℓ m : ℕ) :
    D.weightDev ℓ m = ∑ l ∈ descPaths ℓ m, D.pathProb l * |D.pathZ l - 1| := by
  rw [weightDev, D.descJoint_eq_sum_paths]
  simp only [one_mul]

/-- **The running-pair invariant.** If `|R₀ − 1| ≤ b` above `2ℓ`, then from a running weight `w`
and a running product `v` with `|w − 1| ≤ v − 1`, the deviation at exit is at most
`v · E(∏_{n<N_ℓ}(1 + b(Y_n)) | Y_0 = y) − 1`. -/
theorem descJoint_absDev_le_prodW {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℕ → ℝ}
    (hbR : ∀ y : ℕ, 2 * ℓ ≤ y → |D.R0 y - 1| ≤ b y) :
    ∀ (y : ℕ) (w v : ℝ), |w - 1| ≤ v - 1 →
      D.descJoint ℓ (fun _ u => |u - 1|) y w ≤ v * D.prodW ℓ b y - 1 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro w v hwv
    by_cases hlt : y < 2 * ℓ
    · rw [D.descJoint_of_lt _ hlt, D.prodW_of_lt b hlt, mul_one]
      exact hwv
    · have hy2l : 2 * ℓ ≤ y := by omega
      have hy2 : 2 ≤ y := by omega
      have hb := hbR y hy2l
      have hb0 : 0 ≤ b y := le_trans (abs_nonneg _) hb
      -- the running pair after one step
      have hwv' : |w * D.R0 y - 1| ≤ v * (1 + b y) - 1 := by
        have hw : |w| ≤ v := by
          rcases abs_le.mp (show |w - 1| ≤ v - 1 from hwv) with ⟨h1, h2⟩
          rw [abs_le]; constructor <;> linarith
        have hsplit : w * D.R0 y - 1 = w * (D.R0 y - 1) + (w - 1) := by ring
        rw [hsplit]
        calc |w * (D.R0 y - 1) + (w - 1)| ≤ |w * (D.R0 y - 1)| + |w - 1| := abs_add_le _ _
          _ = |w| * |D.R0 y - 1| + |w - 1| := by rw [abs_mul]
          _ ≤ v * b y + (v - 1) := by
              exact add_le_add (mul_le_mul hw hb (abs_nonneg _) (le_trans (abs_nonneg _) hw))
                hwv
          _ = v * (1 + b y) - 1 := by ring
      rw [D.descJoint_of_ge _ hlt, D.prodW_of_ge b hlt]
      calc ∑ j ∈ window y, D.kern y j * D.descJoint ℓ (fun _ u => |u - 1|) j (w * D.R0 y)
          ≤ ∑ j ∈ window y, D.kern y j * (v * (1 + b y) * D.prodW ℓ b j - 1) :=
            Finset.sum_le_sum fun j hj =>
              mul_le_mul_of_nonneg_left (ih j (window_lt hj) _ _ hwv') (D.kern_nonneg hy2 hj)
        _ = v * (1 + b y) * (∑ j ∈ window y, D.kern y j * D.prodW ℓ b j)
              - ∑ j ∈ window y, D.kern y j := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = v * ((1 + b y) * ∑ j ∈ window y, D.pk y j * D.prodW ℓ b j) - 1 := by
            rw [D.sum_kern hy2]
            simp only [Decay.kern_eq_pk]
            ring

/-- **The paper's use of the lemma, as a consequence.** For `g` bounded by `B`,
`|E(Z_ℓ g(Y_{N_ℓ})) − E(g(Y_{N_ℓ}))| = |E((Z_ℓ − 1) g(Y_{N_ℓ}))| ≤ B·E(|Z_ℓ − 1|)`. -/
theorem abs_descW_sub_descP_le_weightDev {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {B : ℝ} {g : ℕ → ℝ}
    (hg : ∀ j, |g j| ≤ B) (y : ℕ) :
    |D.descW ℓ g y - D.descP ℓ g y| ≤ B * D.weightDev ℓ y := by
  have hW := D.descJoint_mul_eq_descZ (ℓ := ℓ) g y 1
  have hP := D.descJoint_const_eq_descP (ℓ := ℓ) g y 1
  have hS := D.descJoint_sub (ℓ := ℓ) (fun j v => v * g j) (fun j _ => g j) y 1
  rw [hW, hP, one_mul, D.descZ_eq_descW hℓ] at hS
  rw [← hS, weightDev]
  refine D.abs_descJoint_le hℓ (fun j v => ?_) y 1
  have hsub : v * g j - g j = (v - 1) * g j := by ring
  rw [hsub, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hg j) (abs_nonneg _)

/-- **Jensen, as a consistency check.** `|E(Z_ℓ) − 1| ≤ E(|Z_ℓ − 1|)`. -/
theorem abs_descOne_sub_one_le_weightDev {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y : ℕ} (hy : ℓ ≤ y) :
    |D.descOne ℓ y - 1| ≤ D.weightDev ℓ y := by
  have h := D.abs_descW_sub_descP_le_weightDev hℓ (B := 1) (g := fun _ => 1)
    (fun _ => by simp only [abs_one, le_refl]) y
  rw [D.descP_one hℓ y hy, one_mul] at h
  exact h

/-- **`E(|Z_ℓ − 1|) ≤ E(∏(1 + b(Y_n))) − 1`**, the running-pair invariant started at `w = v = 1`. -/
theorem weightDev_le_prodW {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℕ → ℝ}
    (hbR : ∀ y : ℕ, 2 * ℓ ≤ y → |D.R0 y - 1| ≤ b y) (m : ℕ) :
    D.weightDev ℓ m ≤ D.prodW ℓ b m - 1 := by
  have h := D.descJoint_absDev_le_prodW hℓ hbR m 1 1 (by simp only [sub_self, abs_zero, le_refl])
  rw [one_mul] at h
  exact h

/-- **The bound at a level, from the three requirements it consumes.** With `c₄ = 16cτ`: if
`32cτ ≤ 2ℓ`, `c₄ ≤ γ²ℓ/6` and `c₅c₄/ℓ ≤ 1`, then `E(|Z_ℓ − 1| | Y_0 = m) ≤ 2c₅c₄/ℓ` at every
`m`. -/
theorem weightDev_le_of_level {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hthr : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ))
    (hH : D.c4 ≤ D.gam ^ 2 * (ℓ : ℝ) / 6) (hx1 : D.c5 * D.c4 / (ℓ : ℝ) ≤ 1) (m : ℕ) :
    D.weightDev ℓ m ≤ 2 * D.c5 * D.c4 / (ℓ : ℝ) := by
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hH0 : 0 ≤ D.c4 := D.c4_pos.le
  set b : ℕ → ℝ := fun w => D.c4 / (w : ℝ) with hbdef
  have hbR : ∀ w : ℕ, 2 * ℓ ≤ w → |D.R0 w - 1| ≤ b w := by
    intro w hw
    have h := D.R0_sub_one_le (by omega : 1 ≤ w)
    simpa only [hbdef, c4] using h
  have hbb : ∀ w : ℕ, ℓ ≤ w → |b w| ≤ D.c4 / (w : ℝ) := by
    intro w hw
    have hw1 : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (le_trans hℓ1 hw)
    rw [hbdef, abs_of_nonneg (div_nonneg hH0 hw1.le)]
  have hprod : D.prodW ℓ b m ≤ Real.exp (D.c5 * D.c4 / (ℓ : ℝ)) :=
    (D.prodW_two_sided hthr hH0 hH hbb m).2
  have hx0 : 0 ≤ D.c5 * D.c4 / (ℓ : ℝ) := div_nonneg (mul_nonneg D.c5_pos.le hH0) hℓpos.le
  have hexp := exp_sub_one_le_two_mul hx0 hx1
  have h2 : 2 * (D.c5 * D.c4 / (ℓ : ℝ)) = 2 * D.c5 * D.c4 / (ℓ : ℝ) := by ring
  linarith [D.weightDev_le_prodW hℓ1 hbR m]

/-! ## The constants -/

/-- **`c₃`, as the paper puts it.** `c₃ := 8c₅c₄`, with `c₄ = 16cτ` of `lem:doubling_descent` and
`c₅ = 6/γ²` of `lem:doubling_escape`. -/
noncomputable def c3Paper (D : Decay) : ℝ := 8 * D.c5 * D.c4

/-- **`ℓ₃`, as the paper puts it.** `ℓ₃ := max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)`. -/
noncomputable def ell3Paper (D : Decay) (d : ℕ) : ℕ :=
  max (D.ell2 d) (max ⌈2 * D.c4⌉₊ (max ⌈24 * D.c4 / D.gam ^ 2⌉₊ ⌈4 * D.c4 * D.c5⌉₊))

theorem c3Paper_pos : 0 < D.c3Paper := by
  have := D.c5_pos; have := D.c4_pos
  rw [c3Paper]; positivity

theorem ell2_le_ell3Paper (d : ℕ) : D.ell2 d ≤ D.ell3Paper d := le_max_left _ _

/-- `ℓ₃ ≥ ℓ₁`: the descent chain of `lem:doubling_descent` is defined at every level `ℓ ≥ ℓ₃`. -/
theorem ell1_le_ell3Paper (d : ℕ) : D.ell1 d ≤ D.ell3Paper d := by
  have h1 : d + 1 ≤ D.ell2 d := le_max_left _ _
  have h2 : ⌈32 * D.c * D.tau⌉₊ ≤ ⌈2 * D.c4⌉₊ := by
    refine Nat.ceil_mono (le_of_eq ?_)
    rw [c4]; ring
  rw [ell1, ell3Paper]
  exact max_le (le_trans h1 (le_max_left _ _))
    (le_trans h2 (le_trans (le_max_left _ _) (le_max_right _ _)))

/-- The library's sharper `c₃ = 32c₅cτ = 2c₅c₄` is at most the paper's `8c₅c₄`. -/
theorem c3_le_c3Paper : D.c3 ≤ D.c3Paper := by
  have h := mul_pos D.c5_pos D.c4_pos
  have hc3 : D.c3 = 2 * (D.c5 * D.c4) := by rw [c3, c4]; ring
  have hc3P : D.c3Paper = 8 * (D.c5 * D.c4) := by rw [c3Paper]; ring
  rw [hc3, hc3P]; linarith

/-- **The paper's two requirements `⌈24c₄/γ²⌉` and `⌈4c₄c₅⌉` on `ℓ₃` are one number**:
`24c₄/γ² = 4c₄c₅`, since `c₅ = 6/γ²`. -/
theorem twentyfour_c4_div_eq : 24 * D.c4 / D.gam ^ 2 = 4 * D.c4 * D.c5 := by
  have hg2 : D.gam ^ 2 ≠ 0 := by have := D.gam_pos; positivity
  rw [c5]; field_simp; ring

/-- **The library's `ℓ₃` is reached by two of the paper's requirements alone**, `ℓ ≥ ⌈2c₄⌉` and
`ℓ ≥ ⌈24c₄/γ²⌉`; no property of `ℓ₂` is used. -/
theorem ell3_le_of_ceils {ℓ : ℕ} (h2 : ⌈2 * D.c4⌉₊ ≤ ℓ) (h24 : ⌈24 * D.c4 / D.gam ^ 2⌉₊ ≤ ℓ) :
    D.ell3 ≤ ℓ := by
  have hct := D.ctau_pos
  have hg2 : (0 : ℝ) < D.gam ^ 2 := by have := D.gam_pos; positivity
  have h1 : 1 ≤ ⌈2 * D.c4⌉₊ := Nat.ceil_pos.mpr (by have := D.c4_pos; linarith)
  have h16 : ⌈16 * D.c * D.tau⌉₊ ≤ ⌈2 * D.c4⌉₊ := by
    refine Nat.ceil_mono ?_
    rw [c4]; nlinarith
  have h96 : ⌈96 * D.c * D.tau / D.gam ^ 2⌉₊ ≤ ⌈24 * D.c4 / D.gam ^ 2⌉₊ := by
    refine Nat.ceil_mono (div_le_div_of_nonneg_right ?_ hg2.le)
    rw [c4]; nlinarith
  rw [ell3]
  exact max_le (le_trans h1 h2) (max_le (le_trans h16 h2) (le_trans h96 h24))

/-- The library's sharper `ℓ₃ = max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉)` is at most the paper's. -/
theorem ell3_le_ell3Paper (d : ℕ) : D.ell3 ≤ D.ell3Paper d :=
  D.ell3_le_of_ceils (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

/-! ## `lem:doubling_weight` -/

/-- **`lem:doubling_weight`, at the library's sharper constants**, at every state:
`E(|Z_ℓ − 1| | Y_0 = m) ≤ c₃/ℓ` for `ℓ ≥ ℓ₃`, with `c₃ = 32c₅cτ` and
`ℓ₃ = max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉)` of `Weight.lean`. -/
theorem weightDev_le_c3 {ℓ : ℕ} (hℓ : D.ell3 ≤ ℓ) (m : ℕ) :
    D.weightDev ℓ m ≤ D.c3 / (ℓ : ℝ) := by
  have hgp := D.gam_pos
  have hg2 : (0 : ℝ) < D.gam ^ 2 := by positivity
  have hct := D.ctau_pos
  have hℓ1 : 1 ≤ ℓ := le_trans D.one_le_ell3 hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have h16 : (16 : ℝ) * D.c * D.tau ≤ (ℓ : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hℓ
  have h96 : (96 : ℝ) * D.c * D.tau / D.gam ^ 2 ≤ (ℓ : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hℓ
  have h96' : (96 : ℝ) * D.c * D.tau ≤ D.gam ^ 2 * (ℓ : ℝ) := by
    rw [div_le_iff₀ hg2] at h96; linarith
  have hthr : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ) := by linarith
  have hH : D.c4 ≤ D.gam ^ 2 * (ℓ : ℝ) / 6 := by rw [c4]; linarith
  have hx1 : D.c5 * D.c4 / (ℓ : ℝ) ≤ 1 := by
    have hxdef : D.c5 * D.c4 = 96 * D.c * D.tau / D.gam ^ 2 := by
      rw [c5, c4]; field_simp; ring
    rw [hxdef, div_le_one hℓpos]; exact h96
  have h := D.weightDev_le_of_level hℓ1 hthr hH hx1 m
  have hc3 : 2 * D.c5 * D.c4 = D.c3 := by rw [c3, c4]; ring
  rw [hc3] at h
  exact h

/-- **`lem:doubling_weight`, whatever `ℓ₂` is.** The bound `E(|Z_ℓ − 1| | Y_0 = m) ≤ c₃/ℓ`, with
the paper's `c₃ = 8c₅c₄`, holds at every level `ℓ ≥ ⌈2c₄⌉` with `ℓ ≥ ⌈24c₄/γ²⌉`, and at every
state `m`. -/
theorem doubling_weight_of_ceils {ℓ : ℕ} (h2 : ⌈2 * D.c4⌉₊ ≤ ℓ)
    (h24 : ⌈24 * D.c4 / D.gam ^ 2⌉₊ ≤ ℓ) (m : ℕ) :
    D.weightDev ℓ m ≤ D.c3Paper / (ℓ : ℝ) := by
  have hℓ3 := D.ell3_le_of_ceils h2 h24
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by
    have : 1 ≤ ℓ := le_trans D.one_le_ell3 hℓ3
    exact_mod_cast this
  calc D.weightDev ℓ m ≤ D.c3 / (ℓ : ℝ) := D.weightDev_le_c3 hℓ3 m
    _ ≤ D.c3Paper / (ℓ : ℝ) := div_le_div_of_nonneg_right D.c3_le_c3Paper hℓpos.le

/-- **`lem:doubling_weight`** (`eq:doubling_weight`), in the paper's shape and at the paper's
constants: with `c₃ := 8c₅c₄` and `ℓ₃ := max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)`, for every integer
`ℓ ≥ ℓ₃` and every integer `m ≥ 2ℓ`, `E(|Z_ℓ − 1| | Y_0 = m) ≤ c₃/ℓ`. -/
theorem doubling_weight (d : ℕ) {ℓ : ℕ} (hℓ : D.ell3Paper d ≤ ℓ) {m : ℕ} (_hm : 2 * ℓ ≤ m) :
    D.weightDev ℓ m ≤ D.c3Paper / (ℓ : ℝ) :=
  D.doubling_weight_of_ceils (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hℓ)
    (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hℓ) m

/-- **`lem:doubling_weight`, as the finite sum it is.** Over the trajectories `(Y_0, …, Y_{N_ℓ})`
of the descent chain from `m ≥ 2ℓ`, weighted by their probabilities,
`Σ P(Y_0,…,Y_{N_ℓ}) · |∏_{n<N_ℓ} R₀(Y_n) − 1| ≤ c₃/ℓ`. -/
theorem doubling_weight_paths (d : ℕ) {ℓ : ℕ} (hℓ : D.ell3Paper d ≤ ℓ) {m : ℕ}
    (hm : 2 * ℓ ≤ m) :
    ∑ l ∈ descPaths ℓ m, D.pathProb l * |D.pathZ l - 1| ≤ D.c3Paper / (ℓ : ℝ) := by
  rw [← D.weightDev_eq_sum_paths]
  exact D.doubling_weight d hℓ hm

/-- **The paper's use of `lem:doubling_weight`**, derived from it: for `g` bounded by `B`,
`|E(Z_ℓ g(Y_{N_ℓ})) − E(g(Y_{N_ℓ}))| ≤ B c₃/ℓ`, at the paper's constants. -/
theorem doubling_weight_transform (d : ℕ) {ℓ : ℕ} (hℓ : D.ell3Paper d ≤ ℓ) {m : ℕ}
    (hm : 2 * ℓ ≤ m) {B : ℝ} {g : ℕ → ℝ} (hg : ∀ j, |g j| ≤ B) :
    |D.descW ℓ g m - D.descP ℓ g m| ≤ B * D.c3Paper / (ℓ : ℝ) := by
  have hℓ1 : 1 ≤ ℓ := le_trans (le_trans (D.one_le_ell3) (D.ell3_le_ell3Paper d)) hℓ
  have hB : 0 ≤ B := le_trans (abs_nonneg (g 0)) (hg 0)
  calc |D.descW ℓ g m - D.descP ℓ g m| ≤ B * D.weightDev ℓ m :=
        D.abs_descW_sub_descP_le_weightDev hℓ1 hg m
    _ ≤ B * (D.c3Paper / (ℓ : ℝ)) := mul_le_mul_of_nonneg_left (D.doubling_weight d hℓ hm) hB
    _ = B * D.c3Paper / (ℓ : ℝ) := by ring

end Decay

end GFNBounds.Doubling
