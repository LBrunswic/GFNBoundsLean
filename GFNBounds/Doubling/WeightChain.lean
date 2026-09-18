import GFNBounds.Doubling.WeightFull

/-!
# `lem:doubling_weight` on a Markov chain: `E(|Z_ℓ − 1| | Y_0 = m) ≤ c₃/ℓ` as an integral

**`lem:doubling_weight`** — `app_doubling.tex`, the lemma "the weight of a descent deviates from
`1` by `O(1/ℓ)` in mean" (line citations drift, kb `0036`; the label is the anchor).

> Let `ℓ ≥ ℓ₃` be an integer, let `(Y_n)_{n≥0}` and `N_ℓ` be the descent chain of
> `lem:doubling_descent` at the level `ℓ` and its exit time, and let `Z_ℓ := ∏_{n<N_ℓ} R₀(Y_n)`.
> Then, for every integer `m ≥ 2ℓ`, `E(|Z_ℓ − 1| | Y_0 = m) ≤ c₃/ℓ`.   `(eq:doubling_weight)`

## What was missing, and what this file adds

`GFNBounds/Doubling/WeightFull.lean` states `eq:doubling_weight` at the paper's constants, with
`E(· | Y_0 = m)` read as the expectation against the **finite law of the stopped trajectory**
(`weightDev = Σ_{l ∈ descPaths} pathProb l · |pathZ l − 1|`). Its SCOPE says what that leaves:
*"that this finite law is the law of `(Y_0, …, Y_{N_ℓ})` under a chain with kernel `k` is the
definition of such a chain and is not a theorem here."* This file makes it a theorem.

`lem:doubling_descent` defines the chain by its transition law: from `y ≥ 2ℓ`, `Y_{n+1} = j` with
probability `w_y(j)/R₀(y)` for `j ∈ W(y)`; from `y < 2ℓ`, `Y_{n+1} = Y_n`. That is the matrix
`descStep ℓ y j`. A process `Y : ℕ → Ω → ℕ` on a probability space **is the descent chain at the
level `ℓ` from `m`** (`IsDescentChain`) when its finite-dimensional laws are those of that matrix
from `δ_m`:

  `P(Y_0 = a_0, …, Y_n = a_n) = 1[a_0 = m] · ∏_{i<n} descStep ℓ a_i a_{i+1}`

for every finite sequence `(a_0, …, a_n)` — the definition of a time-homogeneous Markov chain on a
countable state space by its cylinder probabilities. Nothing else is assumed: no filtration, no
strong Markov property, no particular `Ω`. On such a process, with `N_ℓ(ω) = inf{n : Y_n(ω) < 2ℓ}`
(`exitTime`, the library's `N_ℓ`) and `Z_ℓ(ω) = ∏_{n<N_ℓ(ω)} R₀(Y_n(ω))` (`chainZ`):

* `integrable_chainDev`: `ω ↦ |Z_ℓ(ω) − 1|` is `P`-integrable;
* `integral_chainDev`: `∫ |Z_ℓ − 1| dP = weightDev ℓ m`, the recursion `WeightFull.lean` bounds;
* `doubling_weight_chain`: **`∫ |Z_ℓ − 1| dP ≤ c₃/ℓ`** at the paper's `c₃ = 8c₅c₄`, for every
  `ℓ ≥ ℓ₃` (the paper's formula) and `m ≥ 2ℓ` — `eq:doubling_weight` verbatim, with `E` the
  Lebesgue integral against `P`.

**The hypothesis is inhabited** (kb `0025`, `0027`): `exists_descentChain` builds, for every
`ℓ ≥ 1` and `m ≥ ℓ`, a probability measure on the path space `ℕ → ℕ` under which the coordinate
process is the descent chain from `m` — the finite mixture of Dirac masses at the stopped
trajectories, extended by their exit state, weighted by `pathProb`. Every finite-dimensional law is
checked, not only those of stopped trajectories (`sum_pathProb_matches`).

**The proof.** The cylinders `C_l = {Y_0 = l_0, …, Y_N = l_N}` of the stopped trajectories
`l ∈ descPaths ℓ m` are pairwise disjoint (a path determines its own stopped trajectory,
`matches_descPaths_unique`), have probabilities `pathProb l` (`cylProb_of_mem_descPaths`), summing to
`1`, so they cover `Ω` up to a null set; on `C_l`, `N_ℓ = N` and `Z_ℓ = pathZ l`
(`exitTime_of_matches`, `chainZ_of_matches`). Hence `|Z_ℓ − 1|` agrees a.e. with the simple function
`Σ_l 1_{C_l} |pathZ l − 1|`, whose integral is `weightDev_eq_sum_paths`' sum.

## SCOPE (disclosed)

* **`E(· | Y_0 = m)` is the integral against a probability `P` under which `Y_0 = m` a.s.** — the
  conditioning is realised by the initial law `δ_m`, the standard reading of `E(· | Y_0 = m)` for a
  Markov chain (`E_m`). No conditional expectation `μ[· | σ(Y_0)]` is formed. The result holds for
  **every** such `(Ω, P, Y)`, so it does not depend on a choice of construction.
* **The chain is defined by its finite-dimensional laws** (`IsDescentChain`), not by
  `ProbabilityTheory.Kernel.traj`; any chain with this transition matrix started at `m` satisfies
  them, and `exists_descentChain` shows one exists. The expectation is **not** defined by a
  recursion here: `weightDev` enters only as the value `integral_chainDev` computes.
* **States below `ℓ`** are never reached from `m ≥ ℓ`; the matrix `descStep` is defined on all of
  `ℕ` (a Dirac below `2ℓ`), which is the paper's chain restricted to the integers `≥ ℓ`.
* **Constants** are `WeightFull.lean`'s: `c3Paper = 8c₅c₄`, `ell3Paper d` the paper's `ℓ₃` over the
  library's `c₄ = 16cτ`, `γ`, `c₅ = 6/γ²`, `ℓ₂ = ell2 d` (see that file's SCOPE, which this inherits,
  including that `c₄` is certified at a value where the paper asserts existence).
* **`m ≥ 2ℓ`** is used only for `m ≥ ℓ` (the stopped law summing to `1`); the bound itself holds at
  every state, as in `WeightFull.lean`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| setting, `s = 1`, `0 < c < 1` | ✓ carried by `Decay` |
| `c₃ := 8c₅c₄`, `ℓ₃ := max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)` | ✓ `c3Paper`, `ell3Paper d` |
| `ℓ ≥ ℓ₃` an integer | ✓ `hℓ` |
| `(Y_n)` the descent chain at level `ℓ` | ✓ `IsDescentChain D P ℓ m Y`, its transition law verbatim (`descStep`) |
| `N_ℓ`, `Z_ℓ := ∏_{n<N_ℓ} R₀(Y_n)` | ✓ `exitTime ℓ (Y · ω)`, `chainZ` |
| `Y_0 = m`, `m ≥ 2ℓ` an integer | ✓ initial law `δ_m` in `IsDescentChain`; `hm` |
| `E(|Z_ℓ − 1| | Y_0 = m) ≤ c₃/ℓ` | ✓ `doubling_weight_chain`: integrable, and `∫ |Z_ℓ − 1| dP ≤ c₃/ℓ` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory

namespace Decay

variable (D : Decay)

/-! ## The transition matrix and the finite-dimensional laws -/

/-- **The transition law of the descent chain at the level `ℓ`** (`lem:doubling_descent`):
`P(Y_{n+1} = j | Y_n = y) = w_y(j)/R₀(y)` on `W(y)` when `y ≥ 2ℓ`, and `Y_{n+1} = y` when
`y < 2ℓ`. -/
noncomputable def descStep (ℓ y j : ℕ) : ℝ :=
  if y < 2 * ℓ then (if j = y then 1 else 0) else (if j ∈ window y then D.kern y j else 0)

/-- `chainProb ℓ y [a_1, …, a_n] = ∏_{i<n} descStep ℓ a_i a_{i+1}` with `a_0 = y`: the probability,
from `Y_0 = y`, that `Y_1 = a_1, …, Y_n = a_n`. -/
noncomputable def chainProb (ℓ : ℕ) : ℕ → List ℕ → ℝ
  | _, [] => 1
  | y, j :: t => D.descStep ℓ y j * chainProb ℓ j t

/-- **The finite-dimensional law of the chain from `δ_m`**:
`cylProb ℓ m [a_0, …, a_n] = 1[a_0 = m] · ∏_{i<n} descStep ℓ a_i a_{i+1}`. -/
noncomputable def cylProb (ℓ m : ℕ) : List ℕ → ℝ
  | [] => 1
  | a :: t => (if a = m then 1 else 0) * D.chainProb ℓ a t

end Decay

/-- `Matches f [a_0, …, a_n]`: the path `f` starts `f 0 = a_0, …, f n = a_n`. -/
def Matches : (ℕ → ℕ) → List ℕ → Prop
  | _, [] => True
  | f, a :: t => f 0 = a ∧ Matches (fun n => f (n + 1)) t

theorem matches_iff : ∀ (c : List ℕ) (f : ℕ → ℕ), Matches f c ↔ ∀ i < c.length, f i = c.getD i 0
  | [], f => by simp only [Matches, List.length_nil, Nat.not_lt_zero, false_imp_iff, imp_true_iff]
  | a :: t, f => by
    rw [Matches, matches_iff t]
    constructor
    · rintro ⟨h0, ht⟩ i hi
      rcases i with _ | i
      · simpa only [List.getD_cons_zero] using h0
      · simp only [List.getD_cons_succ]
        exact ht i (by simp only [List.length_cons] at hi; omega)
    · intro h
      refine ⟨by simpa only [List.getD_cons_zero] using h 0 (by simp), fun i hi => ?_⟩
      have := h (i + 1) (by simp only [List.length_cons]; omega)
      simpa only [List.getD_cons_succ] using this

/-- The cylinder `{Y_0 = a_0, …, Y_n = a_n}`. -/
def cyl {Ω : Type*} (Y : ℕ → Ω → ℕ) (c : List ℕ) : Set Ω := {ω | Matches (fun n => Y n ω) c}

theorem measurableSet_cyl {Ω : Type*} [MeasurableSpace Ω] :
    ∀ (c : List ℕ) (Y : ℕ → Ω → ℕ), (∀ n, Measurable (Y n)) → MeasurableSet (cyl Y c)
  | [], _, _ => by
    simp only [cyl, Matches, Set.setOf_true, MeasurableSet.univ]
  | a :: t, Y, hY => by
    have h : cyl Y (a :: t) = Y 0 ⁻¹' {a} ∩ cyl (fun n => Y (n + 1)) t := by
      ext ω
      simp only [cyl, Matches, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
    rw [h]
    exact ((hY 0) (measurableSet_singleton a)).inter
      (measurableSet_cyl t _ fun n => hY (n + 1))

namespace Decay

variable (D : Decay)

/-- **`Y` is the descent chain at the level `ℓ` started at `m`**: each `Y_n` is measurable and the
finite-dimensional laws are `cylProb ℓ m`, those of the transition law of `lem:doubling_descent`
from `δ_m`. -/
structure IsDescentChain {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ℓ m : ℕ)
    (Y : ℕ → Ω → ℕ) : Prop where
  measurable : ∀ n, Measurable (Y n)
  fdd : ∀ c : List ℕ, P (cyl Y c) = ENNReal.ofReal (D.cylProb ℓ m c)

/-- **`Z_ℓ(ω) = ∏_{n<N_ℓ(ω)} R₀(Y_n(ω))`**, `N_ℓ = exitTime ℓ`. -/
noncomputable def chainZ {Ω : Type*} (ℓ : ℕ) (Y : ℕ → Ω → ℕ) (ω : Ω) : ℝ :=
  ∏ n ∈ Finset.range (exitTime ℓ fun k => Y k ω), D.R0 (Y n ω)

/-! ## The stopped trajectories under the chain -/

/-- On a stopped trajectory the chain's transition law is `k`: `chainProb` is `pathProb`. -/
theorem chainProb_of_mem_descPaths {ℓ : ℕ} :
    ∀ (y : ℕ) {l : List ℕ}, l ∈ descPaths ℓ y → D.chainProb ℓ y l.tail = D.pathProb l := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro l hl
    by_cases hlt : y < 2 * ℓ
    · rw [descPaths_of_lt hlt, Finset.mem_singleton] at hl
      subst hl
      simp only [List.tail_cons, chainProb, pathProb, List.length_cons, List.length_nil,
        Nat.sub_self, Finset.range_zero, Finset.prod_empty]
    · rw [descPaths_of_ge hlt, Finset.mem_biUnion] at hl
      obtain ⟨j, hj, hl⟩ := hl
      rw [Finset.mem_image] at hl
      obtain ⟨l', hl', rfl⟩ := hl
      obtain ⟨hne, hhead⟩ := head_of_mem_descPaths j hl'
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [List.getD_cons_zero] at hhead
      subst hhead
      rw [List.tail_cons, chainProb, D.pathProb_cons y hne, List.getD_cons_zero,
        ← ih a (window_lt hj) hl', List.tail_cons, descStep, if_neg hlt, if_pos hj]

/-- **The cylinder of a stopped trajectory has probability `pathProb`.** -/
theorem cylProb_of_mem_descPaths {ℓ m : ℕ} {l : List ℕ} (hl : l ∈ descPaths ℓ m) :
    D.cylProb ℓ m l = D.pathProb l := by
  obtain ⟨hne, hhead⟩ := head_of_mem_descPaths m hl
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.getD_cons_zero] at hhead
  subst hhead
  have h := D.chainProb_of_mem_descPaths a hl
  rw [List.tail_cons] at h
  rw [cylProb, if_pos rfl, one_mul, h]

/-- A path matching a stopped trajectory `l` exits at `N = |l| − 1`. -/
theorem exitTime_of_matches {ℓ m : ℕ} {l : List ℕ} (hl : l ∈ descPaths ℓ m) {f : ℕ → ℕ}
    (hf : Matches f l) : exitTime ℓ f = l.length - 1 := by
  obtain ⟨hne, -, hstep, hexit⟩ := (mem_descPaths_iff m l).mp hl
  have hlen : 1 ≤ l.length := List.length_pos_iff.mpr hne
  rw [matches_iff] at hf
  have hlast : f (l.length - 1) < 2 * ℓ := by
    rw [hf _ (by omega)]; exact hexit
  have hmem : l.length - 1 ∈ {n | f n < 2 * ℓ} := hlast
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hin : f (exitTime ℓ f) < 2 * ℓ := Nat.sInf_mem ⟨_, hmem⟩
  rw [hf _ (by omega)] at hin
  exact absurd (hstep (exitTime ℓ f) (by omega)).1 (by omega)

/-- On the cylinder of a stopped trajectory `l`, `Z_ℓ = pathZ l`. -/
theorem prod_R0_of_matches {ℓ m : ℕ} {l : List ℕ} (hl : l ∈ descPaths ℓ m) {f : ℕ → ℕ}
    (hf : Matches f l) :
    ∏ n ∈ Finset.range (exitTime ℓ f), D.R0 (f n) = D.pathZ l := by
  rw [exitTime_of_matches hl hf, pathZ]
  rw [matches_iff] at hf
  exact Finset.prod_congr rfl fun n hn => by
    rw [Finset.mem_range] at hn
    rw [hf n (by omega)]

/-- **A path determines its stopped trajectory**: two stopped trajectories from `m` matched by the
same path are equal. -/
theorem matches_descPaths_unique {ℓ m : ℕ} {l l' : List ℕ} (hl : l ∈ descPaths ℓ m)
    (hl' : l' ∈ descPaths ℓ m) {f : ℕ → ℕ} (hf : Matches f l) (hf' : Matches f l') : l = l' := by
  have hN := exitTime_of_matches hl hf
  have hN' := exitTime_of_matches hl' hf'
  have hne := (head_of_mem_descPaths m hl).1
  have hne' := (head_of_mem_descPaths m hl').1
  have h1 : 1 ≤ l.length := List.length_pos_iff.mpr hne
  have h1' : 1 ≤ l'.length := List.length_pos_iff.mpr hne'
  have hlen : l.length = l'.length := by omega
  rw [matches_iff] at hf hf'
  refine List.ext_getElem hlen fun n h₁ h₂ => ?_
  rw [← List.getD_eq_getElem _ 0 h₁, ← List.getD_eq_getElem _ 0 h₂, ← hf n h₁, ← hf' n h₂]

/-! ## The expectation over the chain -/

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ℓ m : ℕ}
  {Y : ℕ → Ω → ℕ}

omit [MeasurableSpace Ω] in
/-- On the cylinder of a stopped trajectory `l`, `Z_ℓ = pathZ l`. -/
theorem chainZ_of_matches {l : List ℕ} (hl : l ∈ descPaths ℓ m) {ω : Ω} (hω : ω ∈ cyl Y l) :
    D.chainZ ℓ Y ω = D.pathZ l :=
  D.prod_R0_of_matches hl hω

omit [MeasurableSpace Ω] in
/-- The cylinders of the stopped trajectories are pairwise disjoint. -/
theorem pairwiseDisjoint_cyl :
    (↑(descPaths ℓ m) : Set (List ℕ)).PairwiseDisjoint fun l => cyl Y l := by
  intro l hl l' hl' hne
  rw [Function.onFun, Set.disjoint_left]
  intro ω h h'
  exact hne (matches_descPaths_unique hl hl' h h')

/-- **The stopped trajectories exhaust the chain**: their cylinders cover `Ω` up to a `P`-null
set. -/
theorem ae_mem_iUnion_cyl (hY : D.IsDescentChain P ℓ m Y) (hℓ : 1 ≤ ℓ) (hm : ℓ ≤ m) :
    ∀ᵐ ω ∂P, ω ∈ ⋃ l ∈ descPaths ℓ m, cyl Y l := by
  have hmeas : ∀ l ∈ descPaths ℓ m, MeasurableSet (cyl Y l) :=
    fun l _ => measurableSet_cyl l Y hY.measurable
  have hU : P (⋃ l ∈ descPaths ℓ m, cyl Y l) = 1 := by
    rw [measure_biUnion_finset pairwiseDisjoint_cyl hmeas]
    have hterm : ∀ l ∈ descPaths ℓ m, P (cyl Y l) = ENNReal.ofReal (D.pathProb l) := fun l hl => by
      rw [hY.fdd l, D.cylProb_of_mem_descPaths hl]
    rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg
      (fun l hl => (D.pathProb_pos hℓ hl).le), D.sum_pathProb hℓ hm, ENNReal.ofReal_one]
  have hUm : MeasurableSet (⋃ l ∈ descPaths ℓ m, cyl Y l) :=
    Finset.measurableSet_biUnion _ hmeas
  rw [ae_iff]
  have hc : {a | ¬ a ∈ ⋃ l ∈ descPaths ℓ m, cyl Y l} = (⋃ l ∈ descPaths ℓ m, cyl Y l)ᶜ := rfl
  rw [hc, prob_compl_eq_zero_iff hUm, hU]

/-- `|Z_ℓ − 1|` agrees `P`-a.e. with the simple function `Σ_l 1_{C_l} |pathZ l − 1|`. -/
theorem chainDev_ae_eq (hY : D.IsDescentChain P ℓ m Y) (hℓ : 1 ≤ ℓ) (hm : ℓ ≤ m) :
    (fun ω => |D.chainZ ℓ Y ω - 1|) =ᵐ[P]
      fun ω => ∑ l ∈ descPaths ℓ m, (cyl Y l).indicator (fun _ => |D.pathZ l - 1|) ω := by
  filter_upwards [D.ae_mem_iUnion_cyl hY hℓ hm] with ω hω
  rw [Set.mem_iUnion₂] at hω
  obtain ⟨l, hl, hωl⟩ := hω
  rw [Finset.sum_eq_single_of_mem l hl, Set.indicator_of_mem hωl, D.chainZ_of_matches hl hωl]
  intro l' hl' hne
  refine Set.indicator_of_notMem (fun h' => hne ?_) _
  exact matches_descPaths_unique hl' hl h' hωl

/-- **`|Z_ℓ − 1|` is integrable** under the chain. -/
theorem integrable_chainDev (hY : D.IsDescentChain P ℓ m Y) (hℓ : 1 ≤ ℓ) (hm : ℓ ≤ m) :
    Integrable (fun ω => |D.chainZ ℓ Y ω - 1|) P := by
  refine (integrable_congr (D.chainDev_ae_eq hY hℓ hm)).mpr ?_
  refine integrable_finsetSum _ fun l _ => ?_
  exact (integrable_const _).indicator (measurableSet_cyl l Y hY.measurable)

/-- **`E(|Z_ℓ − 1| | Y_0 = m)` over the chain is `weightDev ℓ m`.** -/
theorem integral_chainDev (hY : D.IsDescentChain P ℓ m Y) (hℓ : 1 ≤ ℓ) (hm : ℓ ≤ m) :
    ∫ ω, |D.chainZ ℓ Y ω - 1| ∂P = D.weightDev ℓ m := by
  rw [integral_congr_ae (D.chainDev_ae_eq hY hℓ hm), D.weightDev_eq_sum_paths,
    integral_finsetSum _ fun l _ =>
      (integrable_const _).indicator (measurableSet_cyl l Y hY.measurable)]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [integral_indicator_const _ (measurableSet_cyl l Y hY.measurable), smul_eq_mul,
    measureReal_def, hY.fdd l, D.cylProb_of_mem_descPaths hl,
    ENNReal.toReal_ofReal (D.pathProb_pos hℓ hl).le]

/-- **`lem:doubling_weight`** (`eq:doubling_weight`) **on the descent chain**: for every
probability space carrying the descent chain `(Y_n)` of `lem:doubling_descent` at the level `ℓ`
from `Y_0 = m`, with `c₃ := 8c₅c₄` and `ℓ₃ := max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)`, every integer
`ℓ ≥ ℓ₃` and every integer `m ≥ 2ℓ`, `|Z_ℓ − 1|` is integrable and
`E(|Z_ℓ − 1| | Y_0 = m) = ∫ |Z_ℓ − 1| dP ≤ c₃/ℓ`. -/
theorem doubling_weight_chain (d : ℕ) (hℓ : D.ell3Paper d ≤ ℓ) (hm : 2 * ℓ ≤ m)
    (hY : D.IsDescentChain P ℓ m Y) :
    Integrable (fun ω => |D.chainZ ℓ Y ω - 1|) P ∧
      ∫ ω, |D.chainZ ℓ Y ω - 1| ∂P ≤ D.c3Paper / (ℓ : ℝ) := by
  have hℓ1 : 1 ≤ ℓ := le_trans (le_trans D.one_le_ell3 (D.ell3_le_ell3Paper d)) hℓ
  have hm' : ℓ ≤ m := by omega
  refine ⟨D.integrable_chainDev hY hℓ1 hm', ?_⟩
  rw [D.integral_chainDev hY hℓ1 hm']
  exact D.doubling_weight d hℓ hm

end Chain

/-! ## The hypothesis is inhabited: the descent chain exists -/

/-- A stopped trajectory `(Y_0, …, Y_N)` extended by its exit state, as a path `ℕ → ℕ`. -/
def extPath (l : List ℕ) : ℕ → ℕ := fun n => l.getD (min n (l.length - 1)) 0

theorem extPath_zero (l : List ℕ) : extPath l 0 = l.getD 0 0 := by
  simp only [extPath, Nat.zero_min]

theorem extPath_single (y : ℕ) : extPath [y] = fun _ => y := by
  funext n
  simp only [extPath, List.length_cons, List.length_nil, Nat.sub_self, Nat.min_zero,
    List.getD_cons_zero]

theorem extPath_cons_succ (y : ℕ) {l : List ℕ} (hl : l ≠ []) :
    (fun n => extPath (y :: l) (n + 1)) = extPath l := by
  have h1 : 1 ≤ l.length := List.length_pos_iff.mpr hl
  funext n
  simp only [extPath, List.length_cons, Nat.add_sub_cancel]
  have hmin : min (n + 1) l.length = min n (l.length - 1) + 1 := by omega
  rw [hmin, List.getD_cons_succ]

open Classical in
/-- Below `2ℓ` the chain stays put: `chainProb ℓ y t = 1` if `t` is constantly `y`, else `0`. -/
theorem chainProb_of_lt {ℓ y : ℕ} (hy : y < 2 * ℓ) :
    ∀ t : List ℕ, D.chainProb ℓ y t = if Matches (fun _ => y) t then 1 else 0 := by
  intro t
  induction t with
  | nil => simp only [chainProb, Matches, if_true]
  | cons j t ih =>
    rw [chainProb, descStep, if_pos hy]
    by_cases hj : j = y
    · subst hj
      simp only [if_true, one_mul, Matches, true_and]
      exact ih
    · have hj' : ¬ y = j := fun h => hj h.symm
      simp only [hj, if_false, zero_mul, Matches, hj', false_and]

open Classical in
/-- **Every finite-dimensional law of the mixture is the chain's.** For the finite law on the
stopped trajectories from `y ≥ ℓ`, each extended by its exit state, the probability that the path
starts `a_0, …, a_n` is `1[a_0 = y] ∏_{i<n} descStep ℓ a_i a_{i+1}`. -/
theorem sum_pathProb_matches {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∀ (y : ℕ), ℓ ≤ y → ∀ c : List ℕ,
      ∑ l ∈ descPaths ℓ y, D.pathProb l * (if Matches (extPath l) c then 1 else 0)
        = D.cylProb ℓ y c := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy c
    rcases c with _ | ⟨a, t⟩
    · simp only [Matches, if_true, mul_one, cylProb]
      exact D.sum_pathProb hℓ hy
    · by_cases hay : a = y
      swap
      · rw [cylProb, if_neg hay, zero_mul]
        refine Finset.sum_eq_zero fun l hl => ?_
        have h0 : extPath l 0 = y := by
          rw [extPath_zero]; exact (head_of_mem_descPaths y hl).2
        have : ¬ Matches (extPath l) (a :: t) := fun h => hay (h.1.symm.trans h0)
        rw [if_neg this, mul_zero]
      subst hay
      rw [cylProb, if_pos rfl, one_mul]
      by_cases hlt : a < 2 * ℓ
      · rw [descPaths_of_lt hlt, Finset.sum_singleton, D.chainProb_of_lt hlt t]
        have hp : D.pathProb [a] = 1 := by
          simp only [pathProb, List.length_cons, List.length_nil, Nat.sub_self,
            Finset.range_zero, Finset.prod_empty]
        rw [hp, one_mul, extPath_single]
        simp only [Matches, true_and]
      · have hge : 2 * ℓ ≤ a := by omega
        have ha2 : 2 ≤ a := by omega
        have hdisj : (↑(window a) : Set ℕ).PairwiseDisjoint
            fun j => (descPaths ℓ j).image (List.cons a) := by
          intro j₁ _ j₂ _ hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro l hl₁ hl₂
          rw [Finset.mem_image] at hl₁ hl₂
          obtain ⟨u, hu, rfl⟩ := hl₁
          obtain ⟨v, hv, huv⟩ := hl₂
          have hvu : v = u := List.cons_injective huv
          subst hvu
          exact hne ((head_of_mem_descPaths j₁ hu).2.symm.trans (head_of_mem_descPaths j₂ hv).2)
        rw [descPaths_of_ge hlt, Finset.sum_biUnion hdisj]
        have hstep : ∀ j ∈ window a,
            ∑ l ∈ (descPaths ℓ j).image (List.cons a),
                D.pathProb l * (if Matches (extPath l) (a :: t) then 1 else 0)
              = D.kern a j * D.cylProb ℓ j t := by
          intro j hj
          rw [Finset.sum_image (fun u _ v _ h => List.cons_injective h),
            ← ih j (window_lt hj) (le_of_mem_window_of_ge hge hj) t, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l hl => ?_
          obtain ⟨hne, hhead⟩ := head_of_mem_descPaths j hl
          have hM : Matches (extPath (a :: l)) (a :: t) ↔ Matches (extPath l) t := by
            simp only [Matches, extPath_zero, List.getD_cons_zero, true_and]
            rw [extPath_cons_succ a hne]
          rw [D.pathProb_cons a hne, hhead]
          simp only [hM]
          ring
        rw [Finset.sum_congr rfl hstep]
        rcases t with _ | ⟨b, t⟩
        · simp only [cylProb, mul_one, chainProb]
          exact D.sum_kern ha2
        · simp only [cylProb, chainProb, descStep, if_neg hlt]
          have hterm : ∀ j ∈ window a,
              D.kern a j * ((if b = j then 1 else 0) * D.chainProb ℓ b t)
                = if b = j then D.kern a b * D.chainProb ℓ b t else 0 := by
            intro j _
            by_cases hbj : b = j
            · subst hbj; simp only [if_true, one_mul]
            · simp only [hbj, if_false, zero_mul, mul_zero]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
          by_cases hb : b ∈ window a
          · simp only [hb, if_true]
          · simp only [hb, if_false, zero_mul]

/-- **The descent chain exists** (so `IsDescentChain` is not vacuous): for every `ℓ ≥ 1` and
`m ≥ ℓ`, the mixture `Σ_{l ∈ descPaths ℓ m} pathProb l · δ_{extPath l}` is a probability on the
path space `ℕ → ℕ` under which the coordinate process is the descent chain at the level `ℓ` from
`m`. -/
theorem exists_descentChain {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (hm : ℓ ≤ m) :
    ∃ P : Measure (ℕ → ℕ), IsProbabilityMeasure P ∧
      D.IsDescentChain P ℓ m (fun n ω => ω n) := by
  classical
  set P : Measure (ℕ → ℕ) :=
    ∑ l ∈ descPaths ℓ m, ENNReal.ofReal (D.pathProb l) • Measure.dirac (extPath l) with hP
  have hmeas : ∀ n, Measurable fun ω : ℕ → ℕ => ω n := fun n => measurable_pi_apply n
  have hfdd : ∀ c : List ℕ, P (cyl (fun n ω => ω n) c) = ENNReal.ofReal (D.cylProb ℓ m c) := by
    intro c
    have hS := measurableSet_cyl c (fun n (ω : ℕ → ℕ) => ω n) hmeas
    rw [hP, Measure.coe_finsetSum, Finset.sum_apply, ← D.sum_pathProb_matches hℓ m hm c,
      ENNReal.ofReal_sum_of_nonneg fun l hl =>
        mul_nonneg (D.pathProb_pos hℓ hl).le (by split_ifs <;> norm_num)]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
    have hmem : extPath l ∈ cyl (fun n (ω : ℕ → ℕ) => ω n) c ↔ Matches (extPath l) c := Iff.rfl
    by_cases h : Matches (extPath l) c
    · rw [Set.indicator_of_mem (hmem.mpr h), if_pos h, mul_one, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h')), if_neg h, mul_zero, mul_zero,
        ENNReal.ofReal_zero]
  refine ⟨P, ⟨?_⟩, ⟨hmeas, hfdd⟩⟩
  have h := hfdd []
  simp only [cyl, Matches, Set.setOf_true, cylProb, ENNReal.ofReal_one] at h
  exact h

end Decay

end GFNBounds.Doubling
