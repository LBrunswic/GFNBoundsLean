import GFNBounds.Balance.Lift
import GFNBounds.Balance.WeightedL2Norm
import GFNBounds.Balance.TrainingSpeed

/-!
# The edge lift transfers mixing and coercivity: `β̂_n = β_{n−1}`, and `C` lifts to `1 + C`

**`lem:lift_mixing`** — statement `proofs.tex:560–562`, proof `proofs.tex:564–570`.
**`lem:lift_coercivity`** — statement `proofs.tex:572–577`, proof `proofs.tex:579–587`.
(Draft commit `3194054`. The bold-backtick form of each label is what `scripts/trace_check.py` and
the paper-side ledger machine-read.)

> (`lem:lift_mixing`, mixing transfer) In the setting of Definition `def:edge_lift`, let
> `β_n := ‖π_←^n − Π‖_{L²(λ)}` and `β̂_n := ‖K₂^n − Π₂‖_{L²(λ₂)}` be the `L²`-mixing coefficients
> of the density actions of `π_←` and of its edge lift `K₂`, where `Π` and `Π₂` are the mean
> projections against `λ` and `λ₂`. Then `β̂_n = β_{n−1}` for every `n ≥ 1`.

> (`lem:lift_coercivity`, coercivity transfer) In the setting of Definition `def:edge_lift`, let
> `P` and `P₂` be the density actions `φ ↦ d((φλ)π_←)/dλ` of `π_←` on `L²(λ)` and
> `h ↦ d((hλ₂)K₂)/dλ₂` of its edge lift `K₂` on `L²(λ₂)`, and let `Π` and `Π₂` be the mean
> projections against `λ` and `λ₂`. If `C ≥ 0` satisfies `‖φ − Πφ‖_{L²(λ)} ≤ C‖(I − P)φ‖_{L²(λ)}`
> for every `φ ∈ L²(λ)`, then `‖h − Π₂h‖_{L²(λ₂)} ≤ (1 + C)‖(I − P₂)h‖_{L²(λ₂)}` for every
> `h ∈ L²(λ₂)`.

This file finishes, on a finite state space, what `GFNBounds/Balance/Lift.lean` left of
`lem:lift_mixing` — which the draft now states as an **equality** — and proves
`lem:lift_coercivity`, which had no Lean. It builds on `Lift.lean`'s objects (`edgeKernel`,
`edgeMeasure`, `deviation`, `edgeDeviation`, `opNorm`, `opNorm₂`, `lift_mixing`,
`pushEdge_density`) and on `Core/Adjoint.lean`'s adjoint calculus; nothing there is re-proved.

## What is proved

| | |
|---|---|
| `opBound_opNorm` | the infimum of the bounds of an operator on a finite `L²(w)` is a bound, once one exists — **`Lift.lift_mixing_opNorm_le`'s `hattained`, discharged** |
| `opBound_of_adjoint`, `opNorm_eq_of_adjoint` | an operator and its `L²(w)`-adjoint have the same bounds, hence the same `opNorm` — no spectral theorem, `‖Au‖² = ⟪u, BAu⟫` and Cauchy–Schwarz |
| `densDeviation`, `ipL2_densDeviation`, `opNorm_densDeviation` | `P^n − Π` on densities is the adjoint of `(P†)^n − Π` on functions, so the two deviation norms agree — **the "density- and function-action norms agree" step of `proofs.tex:565`, proved** (it was an assumption of `Lift.lean`) |
| `opBound_deviation_two` | `2` bounds `(P†)^n − Π`, so the set of bounds is non-empty |
| `lift_mixing_ge` | **the `≥` half** (`proofs.tex:569`, "Conversely"): a bound of `K₂^{n+1} − Π₂` bounds `P^n − Π`, tested on `f(z,s') = φ(s')` |
| **`lift_mixing_opNorm_eq`** | `opNorm₂(K₂^{n+1} − Π₂) = opNorm(P^n − Π)` on `Lift.lean`'s function actions, with no `hattained` (still under `htot`) |
| `pairKernel`, `pairMeasure`, `opNorm_pair` | `K₂`, `λ₂` on `V × V` uncurried; `Lift.lean`'s curried `β̂_n` is the uncurried one |
| **`lift_mixing_dens`** | **`lem:lift_mixing` verbatim**: `β̂_{n+1} = β_n`, both the operator norms of the **density** actions |
| `opNorm_densDeviation_eq_beta`, `opNorm_densDeviation_restrict` | on a positive weight `opNorm` is `Core.Mixing.beta`, the Mathlib operator norm through `WeightedL2.wtL2`; and `β` does not change on restriction to the support of the weight |
| **`lift_mixing_beta`** | `lem:lift_mixing` in `Core.Mixing.beta`'s norm, `K₂` and `λ₂` on the edge set `E` where `λ₂ > 0` |
| `condFwdPair`, `densAct_pair`, `meanL2_pair`, `nrmL2_condFwdPair_le`, `nrmL2_pair_snd`, `Aop_condFwdPair` | the proof's five facts: `P₂h = k_h ∘ pr₂`, `Π₂h = Πk_h`, Jensen `‖k_h‖ ≤ ‖h‖`, the second marginal is `λ`, `(I − P)k_h = k_{(I−P₂)h}` |
| **`lift_coercivity_finite`** | **`lem:lift_coercivity`** on `V × V` |
| `coercive_restrict`, **`lift_coercivity_edgeSupport`** | coercivity restricts to the support with the same constant; the lemma on `E`, definitionally the shape `C3Wrappers.local_convergence_full_DB`'s `hcoer` takes |
| **`lift_coercivity_graph`** | on the loop closure of a finite marked graph at `C := B̂_σ` — the detailed-balance half of `prop:morozov_rate`*(3)* (`proofs.tex:969`) |
| `lift_coercivity_twoState`, `twoState_lift_beta_one` | inhabitation: both hypothesis bundles on the uniform two-state chain, with `C = 1` attained, and `β̂₁ = β₀ = 1` (`WeightedL2Norm.twoState_beta_zero`), so the equality is not `0 = 0` |

## SCOPE (disclosed)

* **Finite state space.** As in `Lift.lean`: `(𝒮, λ)` is a `Fintype` with `λ : V → ℝ`, `𝒮²` is
  `V × V` (or `V → V → ℝ` curried, for `Lift.lean`'s objects), integrals are finite sums, and
  "`λ`-almost everywhere" is "at every point of positive weight". `L²(λ)` is not a quotient type:
  norms are the weighted seminorms `Graph.nrmL2`/`Lift.l2norm`, which do not see a null point
  (`Core.nrmL2_congr`), and an operator norm is the infimum of the bounds over all functions —
  the operator norm on the quotient. The general measure-space version is `CLAUDE.md`'s
  obstruction 2; every Lean-side consumer (`prop:morozov_rate`*(3)*, the DB instance of
  `theo:local_convergence_full`) is finite.
* **`λ` is a probability where `Π` is at stake.** The paper's `Π` is `h ↦ λ(𝒮)^{−1}∫h dλ` for a
  finite `λ`; the library's `Graph.meanL2`/`perpL2`/`deviation` are the unnormalized `∫h dλ`, which
  is the paper's `Π` exactly when `∑λ = 1`. `lift_mixing_*` carry `htot : ∑ x, lam x = 1`.
  `lift_coercivity_finite` carries no `htot`, but it **is in effect the probability case**: with the
  unnormalized `perpL2`, testing `hcoer` at `φ ≡ 1` gives `|1 − c|√c ≤ 0` for `c = ∑λ`, so its
  hypothesis can hold only at mass `0` or `1`; for a `λ` of other positive mass the paper's statement follows by
  rescaling (`P`, `P₂` are unchanged, both norms scale by the same factor, `Π` becomes the
  normalized mean), which is **not formalized**.
* **`λ ≥ 0`, not `λ > 0`**, in `lift_coercivity_finite`, `lift_mixing_opNorm_eq` and
  `lift_mixing_dens`: the forward policy of the paper's proof is `Core.reversal lam pb`, a Markov
  kernel `λ`-a.e. only, and every identity is used at points of positive weight. `λ > 0` is
  asked only by `lift_mixing_beta`, whose `EuclideanSpace` norm needs `WeightedL2.wtL2` to be a
  bijection, and by the graph instance, where `IsInvProb.pos` supplies it.
* **Sign convention.** The library's `Aop K w h = Ph − h` is `−(I − P)h`; `‖Aop‖ = ‖(I − P)h‖`
  (`nrmL2_neg`), so the coercivity inequalities are the paper's.
* **Two readings of `β̂_n`**, both proved equal to `β_{n−1}`: `lift_mixing_dens` on `V × V` with
  the seminorm operator norm `opNorm`, and `lift_mixing_beta` on the edge set `E` with
  `Core.Mixing.beta`'s `‖·‖` on `EuclideanSpace`. They agree
  (`opNorm_densDeviation_restrict`, `opNorm_densDeviation_eq_beta`). The edge set is the
  support of `λ₂` when `λ > 0`.
* **The sentence after `lem:lift_coercivity`** (`proofs.tex:589`, "the constant `C = ∑β_n` … lifts
  to `1 + C`, which is also the value of the edge-lifted mixing sum") is not a labelled statement
  and is not formalized here; `lift_mixing_beta` together with `β̂₀ = 1` is what it needs.
* **`Lift.lean`'s module docstring is stale on `lem:lift_mixing`**: it quotes the old
  `β̂_n ≤ β_{n−1}` with a window-lift half, and its SCOPE records the `hattained` and
  "density- and function-action norms agree" assumptions this file discharges.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, λ)`, `π_←` a Markov kernel with `λ` invariant (`def:edge_lift`) | ⚠ finite `V`; `Core.IsMarkov pb` (coercivity) or `hnn`, `hrow` (mixing); `Core.IsInvariant lam pb` or `hlam : 0 ≤ λ`, `Invariant pb lam` |
| `λ` a finite measure, `Π = λ(𝒮)^{−1}∫· dλ` | ⚠ `∑λ = 1` (`htot`) for mixing; coercivity proved for any `λ ≥ 0` and is the paper's reading at `∑λ = 1`. See SCOPE |
| `K₂`, `λ₂` the edge lift and edge measure | ✓ `pairKernel pb`, `pairMeasure pb lam` — `Lift.edgeKernel`, `Lift.edgeMeasure` on pairs, proved Markov and invariant (`pairKernel_isMarkov`, `pairMeasure_isInvariant`) |
| `β_n`, `β̂_n` operator norms of the density actions | ✓ `opNorm lam (densDeviation pb lam n)`, `opNorm (pairMeasure pb lam) (densDeviation (pairKernel pb) (pairMeasure pb lam) n)`; and `Core.Mixing.beta` on `EuclideanSpace` for `λ > 0` |
| `n ≥ 1` | ✓ `n + 1` in the type |
| `P`, `P₂` density actions | ✓ `Core.densAct lam pb`, `Core.densAct (pairMeasure pb lam) (pairKernel pb)`, inside `Aop` |
| `C ≥ 0` | ✓ `hC` |
| `‖φ − Πφ‖ ≤ C‖(I − P)φ‖` for every `φ` | ✓ `hcoer`, the library's shape (`TrainingSpeed.hcoer_of_graph`, `C3Wrappers`) |
| for every `h ∈ L²(λ₂)` | ✓ `∀ h : V × V → ℝ`; on `E`, `∀ f : {q // 0 < pb q.2 q.1} → ℝ` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

/-! ### Operator norms on a weighted finite `L²`: attainment and adjoints -/

section Generic

variable {α : Type*} [Fintype α]

/-- `Lift.l2norm` is `Graph.nrmL2`: the two spellings of `‖·‖_{L²(w)}` agree. -/
theorem l2norm_eq_nrmL2 (w f : α → ℝ) : l2norm w f = Graph.nrmL2 w f := by
  simp only [l2norm, l2sq, Graph.nrmL2, Graph.ipL2, sq]

/-- **The operator norm is attained in finite dimension**: if `A` has some bound on `L²(w)`,
then `opNorm w A`, the infimum of its bounds, is itself a bound. The set of bounds is closed. -/
theorem opBound_opNorm {w : α → ℝ} {A : (α → ℝ) → (α → ℝ)} (hne : ∃ b, OpBound w A b) :
    OpBound w A (opNorm w A) := by
  have hset : {b | OpBound w A b}
      = {b : ℝ | 0 ≤ b} ∩ ⋂ g : α → ℝ, {b : ℝ | l2norm w (A g) ≤ b * l2norm w g} := by
    ext b
    simp only [OpBound, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  have hclosed : IsClosed {b | OpBound w A b} := by
    rw [hset]
    exact (isClosed_le continuous_const continuous_id).inter
      (isClosed_iInter fun g => isClosed_le continuous_const
        (continuous_id.mul continuous_const))
  exact hclosed.csInf_mem hne ⟨0, fun _ hb => hb.1⟩

/-- **A bound of an adjoint is a bound**: if `⟪Au, v⟫_w = ⟪u, Bv⟫_w` for all `u, v`, every
bound of `B` on `L²(w)` bounds `A`. `‖Au‖² = ⟪u, BAu⟫ ≤ ‖u‖·b‖Au‖`. -/
theorem opBound_of_adjoint {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) {A B : (α → ℝ) → (α → ℝ)}
    (hadj : ∀ u v, Graph.ipL2 w (A u) v = Graph.ipL2 w u (B v)) {b : ℝ}
    (hb : OpBound w B b) : OpBound w A b := by
  refine ⟨hb.1, fun u => ?_⟩
  rw [l2norm_eq_nrmL2, l2norm_eq_nrmL2]
  have hB := hb.2 (A u)
  rw [l2norm_eq_nrmL2, l2norm_eq_nrmL2] at hB
  have h1 : Graph.nrmL2 w (A u) ^ 2 ≤ Graph.nrmL2 w u * (b * Graph.nrmL2 w (A u)) := by
    rw [Graph.sq_nrmL2 hw, hadj]
    exact (Graph.ipL2_le_mul_nrmL2 hw u (B (A u))).trans
      (mul_le_mul_of_nonneg_left hB (Graph.nrmL2_nonneg _ _))
  have hA0 := Graph.nrmL2_nonneg w (A u)
  have hbu : 0 ≤ b * Graph.nrmL2 w u := mul_nonneg hb.1 (Graph.nrmL2_nonneg _ _)
  by_contra hcon
  have hlt := not_le.mp hcon
  nlinarith

/-- **Adjoint operators have the same operator norm** on a weighted finite `L²` — the step
"`β_n` and `β̂_n` are also the norms of the function actions" of `proofs.tex:565`, with no
spectral theorem: the two sets of bounds coincide. -/
theorem opNorm_eq_of_adjoint {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) {A B : (α → ℝ) → (α → ℝ)}
    (hadj : ∀ u v, Graph.ipL2 w (A u) v = Graph.ipL2 w u (B v)) :
    opNorm w A = opNorm w B := by
  have hadj' : ∀ u v, Graph.ipL2 w (B u) v = Graph.ipL2 w u (A v) := fun u v => by
    rw [ipL2_comm, ← hadj v u, ipL2_comm]
  have hset : {b | OpBound w A b} = {b | OpBound w B b} :=
    Set.ext fun _ => ⟨fun h => opBound_of_adjoint hw hadj' h, fun h => opBound_of_adjoint hw hadj h⟩
  simp only [opNorm, hset]

/-- The **density-action deviation** `P^n − Π` on `L²(w)`, with `P = Core.densAct w K` the action
`u ↦ d((uw)K)/dw` — the operator whose norm is the paper's mixing coefficient
(`lem:lift_mixing`, "`β_n := ‖π_←^n − Π‖_{L²(λ)}` […] of the density actions"). Same argument
order as `Lift.deviation`, its function-action twin. -/
noncomputable def densDeviation (K : α → α → ℝ) (w : α → ℝ) (n : ℕ) (u : α → ℝ) : α → ℝ :=
  fun y => (Core.densAct w K)^[n] u y - ∑ x, w x * u x

/-- The unapplied form of `densDeviation` (kb `0021`). -/
theorem densDeviation_eq (K : α → α → ℝ) (w : α → ℝ) (n : ℕ) (u : α → ℝ) :
    densDeviation K w n u = fun y => (Core.densAct w K)^[n] u y - ∑ x, w x * u x := rfl

theorem densDeviation_apply_eq (K : α → α → ℝ) (w : α → ℝ) (n : ℕ) (u : α → ℝ) (y : α) :
    densDeviation K w n u y = (Core.densAct w K)^[n] u y - ∑ x, w x * u x := rfl

/-- The unapplied form of `Lift.deviation` (kb `0021`). -/
theorem deviation_eq (K : α → α → ℝ) (w : α → ℝ) (n : ℕ) (g : α → ℝ) :
    deviation K w n g = fun x => (funAct K)^[n] g x - ∑ y, w y * g y := rfl

/-- `⟪P^n u, v⟫_w = ⟪u, (P†)^n v⟫_w`: `Core.ipL2_densAct_funAct` iterated. -/
theorem ipL2_densAct_iterate {K : α → α → ℝ} {w : α → ℝ} (hinv : Core.IsInvariant w K)
    (hK : ∀ x y, 0 ≤ K x y) (n : ℕ) (u v : α → ℝ) :
    Graph.ipL2 w ((Core.densAct w K)^[n] u) v = Graph.ipL2 w u ((funAct K)^[n] v) := by
  induction n generalizing u with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply']
      exact Core.ipL2_densAct_funAct hinv hK u _

/-- `⟪a − c, b⟫_w = ⟪a, b⟫_w − c·∫b dw`. -/
theorem ipL2_sub_const_left (w a b : α → ℝ) (c : ℝ) :
    Graph.ipL2 w (fun x => a x - c) b = Graph.ipL2 w a b - c * ∑ x, w x * b x := by
  simp only [Graph.ipL2]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **The density deviation is the `L²(w)`-adjoint of the function deviation**:
`⟪(P^n − Π)u, v⟫_w = ⟪u, ((P†)^n − Π)v⟫_w`. -/
theorem ipL2_densDeviation {K : α → α → ℝ} {w : α → ℝ} (hinv : Core.IsInvariant w K)
    (hK : ∀ x y, 0 ≤ K x y) (n : ℕ) (u v : α → ℝ) :
    Graph.ipL2 w (densDeviation K w n u) v = Graph.ipL2 w u (deviation K w n v) := by
  have hR : Graph.ipL2 w u (deviation K w n v)
      = Graph.ipL2 w u ((funAct K)^[n] v) - (∑ x, w x * v x) * ∑ x, w x * u x := by
    rw [ipL2_comm, deviation_eq, ipL2_sub_const_left, ipL2_comm]
  rw [densDeviation_eq, ipL2_sub_const_left, ipL2_densAct_iterate hinv hK, hR, mul_comm]

/-- **`β_n` read on the density action equals `β_n` read on the function action**, on any finite
`L²(w)` with `w` a non-negative `K`-invariant weight: `‖P^n − Π‖ = ‖(P†)^n − Π‖`. -/
theorem opNorm_densDeviation {K : α → α → ℝ} {w : α → ℝ} (hinv : Core.IsInvariant w K)
    (hK : ∀ x y, 0 ≤ K x y) (n : ℕ) :
    opNorm w (densDeviation K w n) = opNorm w (deviation K w n) :=
  opNorm_eq_of_adjoint hinv.nonneg (ipL2_densDeviation hinv hK n)

/-- `‖(P†)^n g‖ ≤ ‖g‖`: the function action iterated is still a contraction. -/
theorem nrmL2_funAct_iterate_le {K : α → α → ℝ} {w : α → ℝ} (hK : Core.IsMarkovOn w K)
    (hinv : Core.IsInvariant w K) (n : ℕ) (g : α → ℝ) :
    Graph.nrmL2 w ((funAct K)^[n] g) ≤ Graph.nrmL2 w g := by
  induction n with
  | zero => exact le_rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (nrmL2_funAct_le hK hinv _).trans ih

/-- **`2` bounds `(P†)^n − Π`** on `L²(w)` for a `w`-a.e. Markov kernel and an invariant
probability `w` — what makes the set of bounds non-empty, hence `opNorm` attained. -/
theorem opBound_deviation_two {K : α → α → ℝ} {w : α → ℝ} (hK : Core.IsMarkovOn w K)
    (hinv : Core.IsInvariant w K) (htot : ∑ x, w x = 1) (n : ℕ) :
    OpBound w (deviation K w n) 2 := by
  refine ⟨by norm_num, fun g => ?_⟩
  rw [l2norm_eq_nrmL2, l2norm_eq_nrmL2]
  have hc : Graph.nrmL2 w (fun _ => ∑ y, w y * g y) = |∑ y, w y * g y| := by
    have h1 := nrmL2_smul w (fun _ => (1:ℝ)) (∑ y, w y * g y)
    have h2 : Graph.nrmL2 w (fun _ => (1:ℝ)) = 1 := by
      simp only [Graph.nrmL2, Graph.ipL2, mul_one, htot, Real.sqrt_one]
    simpa only [mul_one, h2] using h1
  have hm : |∑ y, w y * g y| ≤ Graph.nrmL2 w g := abs_meanL2_le_nrmL2 hinv.nonneg htot g
  have hsub := nrmL2_sub_le hinv.nonneg ((funAct K)^[n] g) (fun _ => ∑ y, w y * g y)
  have hit := nrmL2_funAct_iterate_le hK hinv n g
  rw [deviation_eq]
  rw [hc] at hsub
  linarith

end Generic

/-! ### `lem:lift_mixing`, the `≥` half, and the equality on the function actions -/

section Mixing

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- `g_f = φ` for `f(z,s') := φ(s')` (`proofs.tex:569`: "`g_f = φ`, `π_←(s' → ·)` being a
probability"). -/
theorem condBack_snd {pb : V → V → ℝ} (hrow : ∀ x, ∑ y, pb x y = 1) (φ : V → ℝ) :
    condBack pb (fun _ s' => φ s') = φ := by
  funext x
  simp only [condBack]
  rw [← Finset.sum_mul, hrow x, one_mul]

omit [DecidableEq V] in
/-- `‖f‖_{L²(λ₂)} = ‖φ‖_{L²(λ)}` for `f(z,s') := φ(s')` (`proofs.tex:569`: "the second marginal
of `λ₂` being `λ`"). Row-stochasticity alone. -/
theorem l2sq₂_of_snd {pb : V → V → ℝ} {lam : V → ℝ} (hrow : ∀ x, ∑ y, pb x y = 1) (φ : V → ℝ) :
    l2sq₂ (edgeMeasure pb lam) (fun _ s' => φ s') = l2sq lam φ := by
  rw [l2sq₂, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  have h : ∀ s : V, edgeMeasure pb lam s s' * φ s' ^ 2 = pb s' s * (lam s' * φ s' ^ 2) :=
    fun s => by simp only [edgeMeasure]; ring
  rw [Finset.sum_congr rfl fun s (_ : s ∈ (univ : Finset V)) => h s, ← Finset.sum_mul, hrow s',
    one_mul]

/-- `K₂^{n+1} − Π₂` applied to `f` is `P^n − Π` applied to `g_f`, read at the first coordinate
(`eq:lift_mixing_identity` before the norms are taken). -/
theorem edgeDeviation_succ (pb : V → V → ℝ) (lam : V → ℝ) (n : ℕ) (f : V → V → ℝ) :
    edgeDeviation pb lam (n + 1) f = fun s _ => deviation pb lam n (condBack pb f) s := by
  funext s s'
  rw [edgeDeviation, funActEdge_iterate, deviation, edgeMean]

/-- **`lem:lift_mixing`, the `≥` half** (`proofs.tex:569`, "Conversely, …"): every bound of
`K₂^{n+1} − Π₂` on `L²(λ₂)` is a bound of `P^n − Π` on `L²(λ)`, tested on `f(z,s') := φ(s')`. -/
theorem lift_mixing_ge {pb : V → V → ℝ} {lam : V → ℝ} (hrow : ∀ x, ∑ y, pb x y = 1)
    (hinv : Invariant pb lam) {b : ℝ} {n : ℕ}
    (hb : OpBound₂ (edgeMeasure pb lam) (edgeDeviation pb lam (n + 1)) b) :
    OpBound lam (deviation pb lam n) b := by
  refine ⟨hb.1, fun φ => ?_⟩
  have h := hb.2 (fun _ s' => φ s')
  rw [edgeDeviation_succ, condBack_snd hrow, l2norm₂, l2norm₂, l2sq₂_of_fst hinv,
    l2sq₂_of_snd hrow] at h
  exact h

/-- **`lem:lift_mixing` on the function actions, as an equality**: `β̂_{n+1} = β_n`, i.e. the
paper's `β̂_n = β_{n−1}` for `n ≥ 1`, with both sides the operator norms (`opNorm`, the infimum
of the bounds, as Mathlib defines `‖·‖` on `→L`). No attainment hypothesis: the infimum is
attained (`opBound_opNorm`), `2` being a bound (`opBound_deviation_two`). -/
theorem lift_mixing_opNorm_eq {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) (hlam : ∀ x, 0 ≤ lam x) (hinv : Invariant pb lam)
    (htot : ∑ x, lam x = 1) (n : ℕ) :
    opNorm₂ (edgeMeasure pb lam) (edgeDeviation pb lam (n + 1))
      = opNorm lam (deviation pb lam n) := by
  have hbd : OpBound lam (deviation pb lam n) 2 :=
    opBound_deviation_two ⟨hnn, fun {x} _ => hrow x⟩ ⟨hlam, hinv⟩ htot n
  have hatt := opBound_opNorm ⟨2, hbd⟩
  refine le_antisymm (lift_mixing_opNorm_le hnn hrow hlam hinv hatt) ?_
  refine le_csInf ⟨2, hbd.1, fun f => lift_mixing hnn hrow hlam hinv hbd.1 hbd.2 f⟩ ?_
  intro b hb
  exact csInf_le ⟨0, fun _ h => h.1⟩ (lift_mixing_ge hrow hinv hb)

/-! ### The edge lift on `𝒮 × 𝒮`, uncurried

`Lift.lean` carries functions on `𝒮²` curried, `V → V → ℝ`. The density action, the mean
projection and the coercivity of the library (`Core.densAct`, `Graph.meanL2`, `perpL2`, `Aop`)
are stated for functions on one `Fintype`; on `V × V` they apply verbatim. `pairKernel` and
`pairMeasure` are `edgeKernel` and `edgeMeasure` read on pairs, and are definitionally what the
edge-subtype objects of the DB instance restrict. -/

/-- `K₂` on pairs: `K₂(p → q) = edgeKernel pb p.1 p.2 q.1 q.2`. -/
def pairKernel (pb : V → V → ℝ) (p q : V × V) : ℝ := edgeKernel pb p.1 p.2 q.1 q.2

/-- `λ₂` on pairs: `λ₂(p) = π_←(p.2 → p.1)·λ(p.2)`. -/
def pairMeasure (pb : V → V → ℝ) (lam : V → ℝ) (p : V × V) : ℝ := edgeMeasure pb lam p.1 p.2

/-- `K₂` is a Markov kernel on `V × V`. -/
theorem pairKernel_isMarkov {pb : V → V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) : Core.IsMarkov (pairKernel pb) := by
  refine ⟨fun p q => edgeKernel_nonneg hnn _ _ _ _, fun p => ?_⟩
  simp only [pairKernel]
  rw [Fintype.sum_prod_type]
  exact edgeKernel_total hrow p.1 p.2

/-- **`λ₂` is `K₂`-invariant, on pairs** (`lem:lift_wellposed`'s invariance, `Lift.pushEdge_edgeMeasure`
uncurried): `λ₂` is a non-negative `K₂`-invariant measure on `V × V`. -/
theorem pairMeasure_isInvariant {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hlam : ∀ x, 0 ≤ lam x) (hinv : Invariant pb lam) :
    Core.IsInvariant (pairMeasure pb lam) (pairKernel pb) := by
  refine ⟨fun p => edgeMeasure_nonneg hnn hlam _ _, fun q => ?_⟩
  have h := congrFun (congrFun (pushEdge_edgeMeasure hinv) q.1) q.2
  simp only [pushEdge] at h
  simp only [pairMeasure, pairKernel]
  rw [Fintype.sum_prod_type]
  exact h

omit [DecidableEq V] in
/-- `λ₂` is a probability on `V × V`. -/
theorem pairMeasure_total {pb : V → V → ℝ} {lam : V → ℝ} (hrow : ∀ x, ∑ y, pb x y = 1)
    (htot : ∑ x, lam x = 1) : ∑ p, pairMeasure pb lam p = 1 := by
  simp only [pairMeasure]
  rw [Fintype.sum_prod_type]
  exact edgeMeasure_total hrow htot

/-- `K₂`'s function action commutes with uncurrying. -/
theorem funAct_pairKernel (pb : V → V → ℝ) (f : V → V → ℝ) :
    funAct (pairKernel pb) (Function.uncurry f) = Function.uncurry (funActEdge pb f) := by
  funext p
  simp only [funAct, pairKernel, funActEdge, Function.uncurry]
  rw [Fintype.sum_prod_type]

/-- … and so do its iterates. -/
theorem funAct_pairKernel_iterate (pb : V → V → ℝ) (n : ℕ) (f : V → V → ℝ) :
    (funAct (pairKernel pb))^[n] (Function.uncurry f)
      = Function.uncurry ((funActEdge pb)^[n] f) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, funAct_pairKernel,
      Function.iterate_succ_apply']

/-- The function deviation of `K₂` on pairs is `edgeDeviation`, uncurried. -/
theorem deviation_pair (pb : V → V → ℝ) (lam : V → ℝ) (n : ℕ) (f : V → V → ℝ) :
    deviation (pairKernel pb) (pairMeasure pb lam) n (Function.uncurry f)
      = Function.uncurry (edgeDeviation pb lam n f) := by
  funext p
  rw [deviation_eq, funAct_pairKernel_iterate]
  simp only [Function.uncurry, edgeDeviation, pairMeasure]
  rw [edgeMean_eq_integral, Fintype.sum_prod_type]

omit [DecidableEq V] in
/-- `‖f‖_{L²(λ₂)}` curried or uncurried. -/
theorem l2norm_pair (pb : V → V → ℝ) (lam : V → ℝ) (f : V → V → ℝ) :
    l2norm (pairMeasure pb lam) (Function.uncurry f) = l2norm₂ (edgeMeasure pb lam) f := by
  simp only [l2norm, l2norm₂, l2sq, l2sq₂, pairMeasure, Function.uncurry]
  rw [Fintype.sum_prod_type]

/-- `β̂_n` curried (`opNorm₂` of `Lift.lean`) is `β̂_n` uncurried. -/
theorem opNorm_pair (pb : V → V → ℝ) (lam : V → ℝ) (n : ℕ) :
    opNorm (pairMeasure pb lam) (deviation (pairKernel pb) (pairMeasure pb lam) n)
      = opNorm₂ (edgeMeasure pb lam) (edgeDeviation pb lam n) := by
  have hset : {b | OpBound (pairMeasure pb lam) (deviation (pairKernel pb) (pairMeasure pb lam) n) b}
      = {b | OpBound₂ (edgeMeasure pb lam) (edgeDeviation pb lam n) b} := by
    ext b
    simp only [OpBound, OpBound₂, Set.mem_setOf_eq]
    refine and_congr_right fun _ => ⟨fun h f => ?_, fun h g => ?_⟩
    · have := h (Function.uncurry f)
      rwa [deviation_pair, l2norm_pair, l2norm_pair] at this
    · have := h (Function.curry g)
      rwa [← l2norm_pair, ← l2norm_pair, ← deviation_pair, Function.uncurry_curry] at this
  simp only [opNorm, opNorm₂, hset]

/-- **`lem:lift_mixing`** (`proofs.tex:560–562`, proof `proofs.tex:564–570`) **as the paper
states it**, on a finite state space: with `β_n := ‖π_←^n − Π‖_{L²(λ)}` and
`β̂_n := ‖K₂^n − Π₂‖_{L²(λ₂)}` the operator norms of the **density actions**,
`β̂_n = β_{n−1}` for every `n ≥ 1` (written `n + 1`, `n`).

Assembled from the three steps of the paper's proof: density and function actions have the same
deviation norms (`opNorm_densDeviation`, on `V` and on `V × V`); uncurrying (`opNorm_pair`); and
the two inequalities of `lift_mixing_opNorm_eq`. -/
theorem lift_mixing_dens {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) (hlam : ∀ x, 0 ≤ lam x) (hinv : Invariant pb lam)
    (htot : ∑ x, lam x = 1) (n : ℕ) :
    opNorm (pairMeasure pb lam) (densDeviation (pairKernel pb) (pairMeasure pb lam) (n + 1))
      = opNorm lam (densDeviation pb lam n) := by
  rw [opNorm_densDeviation (pairMeasure_isInvariant hnn hlam hinv)
      (pairKernel_isMarkov hnn hrow).nonneg, opNorm_pair,
    lift_mixing_opNorm_eq hnn hrow hlam hinv htot, opNorm_densDeviation ⟨hlam, hinv⟩ hnn]

end Mixing

/-! ### `lem:lift_coercivity`: coercivity transfers from `P` to `P₂` with constant `1 + C` -/

section Coercivity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's `k_h(s) := ∫ h(s,z) π_→^λ(s → dz)` (`proofs.tex:580`), for `h` a function on
pairs and `pf` the dual forward policy. `Lift.condFwd`, uncurried. -/
def condFwdPair (pf : V → V → ℝ) (h : V × V → ℝ) : V → ℝ := fun s => ∑ z, pf s z * h (s, z)

omit [DecidableEq V] in
/-- `λ₂(s,z) = λ(s)·π_→^λ(s → z)` (`proofs.tex:580`, "`λ₂(ds dz) = λ(ds)π_→^λ(s → dz)`"), for
the `λ`-reversal `π_→^λ = Core.reversal lam pb`. -/
theorem pairMeasure_eq_reversal {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam pb)
    (hnn : ∀ x y, 0 ≤ pb x y) (s z : V) :
    pairMeasure pb lam (s, z) = lam s * Core.reversal lam pb s z := by
  rw [hinv.isReversalPair_reversal hnn s z]
  simp only [pairMeasure, edgeMeasure]
  ring

/-- **`P₂h = k_h ∘ pr₂`** (`proofs.tex:580`, from `eq:muK2_density`): the density action of `K₂`
against `λ₂` at every pair carrying `λ₂`-mass. `Lift.pushEdge_density`, uncurried. -/
theorem densAct_pair {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam pb)
    (hnn : ∀ x y, 0 ≤ pb x y) (h : V × V → ℝ) {q : V × V} (hq : pairMeasure pb lam q ≠ 0) :
    Core.densAct (pairMeasure pb lam) (pairKernel pb) h q
      = condFwdPair (Core.reversal lam pb) h q.2 := by
  have hpd := pushEdge_density (hinv.isReversalPair_reversal hnn) (fun a b => h (a, b)) q.1 q.2
  have hnum : ∑ p, pairMeasure pb lam p * pairKernel pb p q * h p
      = pairMeasure pb lam q * condFwdPair (Core.reversal lam pb) h q.2 := by
    simp only [pushEdge] at hpd
    simp only [pairMeasure, pairKernel]
    rw [Fintype.sum_prod_type]
    refine (Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring).trans hpd
  rw [Core.densAct_apply, hnum, mul_div_cancel_left₀ _ hq]

omit [DecidableEq V] in
/-- **`Π₂h = Πk_h`** (`proofs.tex:580`, "`∫k_h dλ = ∫h dλ₂`"). -/
theorem meanL2_pair {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam pb)
    (hnn : ∀ x y, 0 ≤ pb x y) (h : V × V → ℝ) :
    Graph.meanL2 (pairMeasure pb lam) h = Graph.meanL2 lam (condFwdPair (Core.reversal lam pb) h) := by
  simp only [Graph.meanL2, condFwdPair]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by rw [pairMeasure_eq_reversal hinv hnn]; ring

omit [DecidableEq V] in
/-- **Jensen, `‖k_h‖_{L²(λ)} ≤ ‖h‖_{L²(λ₂)}`** (`proofs.tex:580`), against the probability
measures `π_→^λ(s → ·)` — which the reversal is at every `s` carrying `λ`-mass. -/
theorem nrmL2_condFwdPair_le {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam pb)
    (hnn : ∀ x y, 0 ≤ pb x y) (h : V × V → ℝ) :
    Graph.nrmL2 lam (condFwdPair (Core.reversal lam pb) h) ≤ Graph.nrmL2 (pairMeasure pb lam) h := by
  have hR := hinv.isMarkovOn_reversal hnn
  refine Real.sqrt_le_sqrt ?_
  simp only [Graph.ipL2]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun s _ => ?_
  have hrhs : ∑ z, pairMeasure pb lam (s, z) * (h (s, z) * h (s, z))
      = lam s * ∑ z, Core.reversal lam pb s z * (h (s, z) * h (s, z)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [pairMeasure_eq_reversal hinv hnn]; ring
  rw [hrhs]
  by_cases hs : lam s = 0
  · rw [hs, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (Core.funAct_mul_self_le hR hs (fun z => h (s, z)))
      (hinv.nonneg s)

omit [DecidableEq V] in
/-- `‖φ ∘ pr₂‖_{L²(λ₂)} = ‖φ‖_{L²(λ)}` (`proofs.tex:585`, "the second marginal of `λ₂` being
`λ`"). -/
theorem nrmL2_pair_snd {pb : V → V → ℝ} {lam : V → ℝ} (hrow : ∀ x, ∑ y, pb x y = 1)
    (φ : V → ℝ) : Graph.nrmL2 (pairMeasure pb lam) (fun q => φ q.2) = Graph.nrmL2 lam φ := by
  simp only [Graph.nrmL2, Graph.ipL2, pairMeasure, edgeMeasure]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s' _ => ?_
  have h : ∀ s : V, pb s' s * lam s' * (φ s' * φ s') = pb s' s * (lam s' * (φ s' * φ s')) :=
    fun s => by ring
  rw [Finset.sum_congr rfl fun s (_ : s ∈ (univ : Finset V)) => h s, ← Finset.sum_mul, hrow s',
    one_mul]

/-- **`k_v = (I − P)k_h` for `v := (I − P₂)h`**, in the library's sign convention
`Aop K w h = Ph − h`: `A k_h = k_{A₂ h}` at every state carrying `λ`-mass (`proofs.tex:582`). -/
theorem Aop_condFwdPair {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam pb)
    (hnn : ∀ x y, 0 ≤ pb x y) (h : V × V → ℝ) {s : V} (hs : lam s ≠ 0) :
    Aop pb lam (condFwdPair (Core.reversal lam pb) h) s
      = condFwdPair (Core.reversal lam pb) (Aop (pairKernel pb) (pairMeasure pb lam) h) s := by
  set R := Core.reversal lam pb with hRdef
  have hterm : ∀ z : V, R s z * Aop (pairKernel pb) (pairMeasure pb lam) h (s, z)
      = R s z * condFwdPair R h z - R s z * h (s, z) := by
    intro z
    rw [Aop_apply]
    by_cases hz : R s z = 0
    · rw [hz, zero_mul, zero_mul, zero_mul, sub_zero]
    · have hq : pairMeasure pb lam (s, z) ≠ 0 := by
        rw [pairMeasure_eq_reversal hinv hnn]
        exact mul_ne_zero hs hz
      rw [densAct_pair hinv hnn h hq]
      ring
  have hrow : ∑ z, R s z * h (s, z) = condFwdPair R h s := rfl
  rw [Aop_apply, Core.densAct_eq_funAct_reversal, ← hRdef]
  simp only [condFwdPair]
  rw [Finset.sum_congr rfl fun z (_ : z ∈ (univ : Finset V)) => hterm z, Finset.sum_sub_distrib]
  rfl

/-- **`lem:lift_coercivity`** (`proofs.tex:572–577`, proof `proofs.tex:579–587`) on a finite
state space: if `C ≥ 0` satisfies `‖φ − Πφ‖_{L²(λ)} ≤ C‖(I − P)φ‖_{L²(λ)}` for every `φ`, then
`‖h − Π₂h‖_{L²(λ₂)} ≤ (1 + C)‖(I − P₂)h‖_{L²(λ₂)}` for every `h`, where `P` and `P₂` are the
density actions of `π_←` against `λ` and of its edge lift `K₂` against `λ₂`.

In the library's spelling: `‖h^⊥‖ ≤ B̂‖Ah‖` with `A = Aop = P − I` (so `‖Ah‖ = ‖(I − P)h‖`,
`nrmL2_neg`) and `h^⊥ = perpL2`, which is `h − Πh` when the weight is a probability.

The proof is the paper's: `h − Π₂h = v + (k_h − Πk_h) ∘ pr₂` with `v = (I − P₂)h`, the second
summand has the `L²(λ)` norm of `k_h − Πk_h`, the hypothesis bounds that by `C‖(I − P)k_h‖`,
`(I − P)k_h = k_v`, Jensen gives `‖k_v‖ ≤ ‖v‖`, and the triangle inequality closes. Every
identity holds at the points carrying mass, which is all a weighted norm sees (`nrmL2_congr`). -/
theorem lift_coercivity_finite {pb : V → V → ℝ} {lam : V → ℝ} {C : ℝ}
    (hpb : Core.IsMarkov pb) (hinv : Core.IsInvariant lam pb) (hC : 0 ≤ C)
    (hcoer : ∀ φ : V → ℝ, Graph.nrmL2 lam (perpL2 lam φ) ≤ C * Graph.nrmL2 lam (Aop pb lam φ))
    (h : V × V → ℝ) :
    Graph.nrmL2 (pairMeasure pb lam) (perpL2 (pairMeasure pb lam) h)
      ≤ (1 + C) * Graph.nrmL2 (pairMeasure pb lam) (Aop (pairKernel pb) (pairMeasure pb lam) h) := by
  set W := pairMeasure pb lam with hW
  set R := Core.reversal lam pb with hR
  set k := condFwdPair R h with hk
  set Ah := Aop (pairKernel pb) W h with hAh
  have hWnn : ∀ q, 0 ≤ W q := (pairMeasure_isInvariant hpb.nonneg hinv.nonneg hinv.inv).nonneg
  -- `h − Π₂h = −A₂h + (k_h − Πk_h) ∘ pr₂`, at every pair carrying `λ₂`-mass
  have hsplit : Graph.nrmL2 W (perpL2 W h)
      = Graph.nrmL2 W (fun q => (fun q => -Ah q) q + (fun q => perpL2 lam k q.2) q) := by
    refine Core.nrmL2_congr fun q hq => ?_
    simp only [perpL2_apply, hAh, Aop_apply]
    rw [densAct_pair hinv hpb.nonneg h hq, meanL2_pair hinv hpb.nonneg]
    ring
  -- `‖(I − P)k_h‖_{L²(λ)} = ‖k_{(I − P₂)h}‖_{L²(λ)} ≤ ‖(I − P₂)h‖_{L²(λ₂)}`
  have hAk : Graph.nrmL2 lam (Aop pb lam k) ≤ Graph.nrmL2 W Ah := by
    have heq : Graph.nrmL2 lam (Aop pb lam k) = Graph.nrmL2 lam (condFwdPair R Ah) :=
      Core.nrmL2_congr fun s hs => Aop_condFwdPair hinv hpb.nonneg h hs
    rw [heq]
    exact nrmL2_condFwdPair_le hinv hpb.nonneg Ah
  have hperp : Graph.nrmL2 lam (perpL2 lam k) ≤ C * Graph.nrmL2 W Ah :=
    (hcoer k).trans (mul_le_mul_of_nonneg_left hAk hC)
  rw [hsplit]
  refine (nrmL2_add_le hWnn _ _).trans ?_
  rw [nrmL2_neg, nrmL2_pair_snd hpb.row_sum]
  linarith

end Coercivity

/-! ### Restriction to the support of the weight

The DB instance of the convergence theorems runs `K₂` on the edge set
`E = {(s,s') : π_←(s' → s) > 0}`, where `λ₂ > 0`, rather than on `V × V`, where `λ₂` vanishes off
`E`. A weighted norm does not see a null point, so coercivity on the whole type restricts to the
support with the same constant. Stated for any predicate containing the support of the weight. -/

section Restrict

variable {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p]

/-- Extension by `0` of a function on `{a // p a}`. -/
noncomputable def extSupp (f : {a // p a} → ℝ) : α → ℝ :=
  fun a => if hp : p a then f ⟨a, hp⟩ else 0

omit [Fintype α] in
theorem extSupp_val (f : {a // p a} → ℝ) (e : {a // p a}) : extSupp f e.1 = f e := by
  simp only [extSupp, dif_pos e.2]

/-- A sum over `{a // p a}` of a function vanishing off `p` is the sum over `α`. -/
theorem sum_subtype_of_vanish (g : α → ℝ) (hg : ∀ a, ¬ p a → g a = 0) :
    ∑ e : {a // p a}, g e.1 = ∑ a, g a := by
  rw [← Fintype.sum_subtype_add_sum_subtype p g]
  have h0 : ∑ i : {x // ¬ p x}, g i = 0 := Finset.sum_eq_zero fun i _ => hg i.1 i.2
  rw [h0, add_zero]

/-- `‖G ∘ val‖_{L²(w ∘ val)} = ‖G‖_{L²(w)}` when `w` vanishes off `p`. -/
theorem nrmL2_restrict {w : α → ℝ} (hw0 : ∀ a, ¬ p a → w a = 0) (G : α → ℝ) :
    Graph.nrmL2 (fun e : {a // p a} => w e.1) (fun e => G e.1) = Graph.nrmL2 w G := by
  simp only [Graph.nrmL2, Graph.ipL2]
  rw [sum_subtype_of_vanish (fun a => w a * (G a * G a))
    fun a ha => by rw [hw0 a ha, zero_mul]]

/-- `h − Πh` restricts. -/
theorem perpL2_restrict {w : α → ℝ} (hw0 : ∀ a, ¬ p a → w a = 0) (f : {a // p a} → ℝ) :
    perpL2 (fun e : {a // p a} => w e.1) f = fun e => perpL2 w (extSupp f) e.1 := by
  have hm : Graph.meanL2 (fun e : {a // p a} => w e.1) f = Graph.meanL2 w (extSupp f) := by
    simp only [Graph.meanL2]
    rw [← sum_subtype_of_vanish (fun a => w a * extSupp f a)
      fun a ha => by rw [hw0 a ha, zero_mul]]
    exact Finset.sum_congr rfl fun e _ => by rw [extSupp_val]
  funext e
  rw [perpL2_apply, perpL2_apply, hm, extSupp_val]

/-- `(P − I)h` restricts, the kernel read on the subtype. -/
theorem Aop_restrict {w : α → ℝ} (hw0 : ∀ a, ¬ p a → w a = 0) (K : α → α → ℝ)
    (f : {a // p a} → ℝ) :
    Aop (fun e e' : {a // p a} => K e.1 e'.1) (fun e => w e.1) f
      = fun e => Aop K w (extSupp f) e.1 := by
  funext e'
  have hnum : ∑ e : {a // p a}, w e.1 * K e.1 e'.1 * f e = ∑ a, w a * K a e'.1 * extSupp f a := by
    rw [← sum_subtype_of_vanish (fun a => w a * K a e'.1 * extSupp f a)
      fun a ha => by rw [hw0 a ha, zero_mul, zero_mul]]
    exact Finset.sum_congr rfl fun e _ => by rw [extSupp_val]
  rw [Aop_apply, Aop_apply, Core.densAct_apply, Core.densAct_apply, hnum, extSupp_val]

/-- **Coercivity restricts to the support**, with the same constant. -/
theorem coercive_restrict {w : α → ℝ} (hw0 : ∀ a, ¬ p a → w a = 0) {K : α → α → ℝ} {c : ℝ}
    (hco : ∀ h : α → ℝ, Graph.nrmL2 w (perpL2 w h) ≤ c * Graph.nrmL2 w (Aop K w h))
    (f : {a // p a} → ℝ) :
    Graph.nrmL2 (fun e : {a // p a} => w e.1) (perpL2 (fun e => w e.1) f)
      ≤ c * Graph.nrmL2 (fun e => w e.1) (Aop (fun e e' : {a // p a} => K e.1 e'.1)
          (fun e => w e.1) f) := by
  rw [perpL2_restrict hw0, Aop_restrict hw0, nrmL2_restrict hw0, nrmL2_restrict hw0]
  exact hco (extSupp f)

end Restrict

section Instances

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- `λ₂` vanishes off the edge set. -/
theorem pairMeasure_eq_zero_off {pb : V → V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y) (lam : V → ℝ)
    (q : V × V) (hq : ¬ 0 < pb q.2 q.1) : pairMeasure pb lam q = 0 := by
  have h0 : pb q.2 q.1 = 0 := le_antisymm (not_lt.mp hq) (hnn q.2 q.1)
  simp only [pairMeasure, edgeMeasure, h0, zero_mul]

/-- **`lem:lift_coercivity` on the edge set `E = {(s,s') : π_←(s' → s) > 0}`**, the setting of
the DB instance (`proofs.tex:666–668`): `K₂` and `λ₂` read on `E` — definitionally the objects
`fun e => edgeMeasure pb lam e.1.1 e.1.2` and `fun e e' => edgeKernel pb e.1.1 e.1.2 e'.1.1 e'.1.2`.
-/
theorem lift_coercivity_edgeSupport {pb : V → V → ℝ} {lam : V → ℝ} {C : ℝ}
    (hpb : Core.IsMarkov pb) (hinv : Core.IsInvariant lam pb) (hC : 0 ≤ C)
    (hcoer : ∀ φ : V → ℝ, Graph.nrmL2 lam (perpL2 lam φ) ≤ C * Graph.nrmL2 lam (Aop pb lam φ))
    (f : {q : V × V // 0 < pb q.2 q.1} → ℝ) :
    Graph.nrmL2 (fun e : {q : V × V // 0 < pb q.2 q.1} => pairMeasure pb lam e.1)
        (perpL2 (fun e => pairMeasure pb lam e.1) f)
      ≤ (1 + C) * Graph.nrmL2 (fun e => pairMeasure pb lam e.1)
          (Aop (fun e e' : {q : V × V // 0 < pb q.2 q.1} => pairKernel pb e.1 e'.1)
            (fun e => pairMeasure pb lam e.1) f) :=
  coercive_restrict (pairMeasure_eq_zero_off hpb.nonneg lam)
    (lift_coercivity_finite hpb hinv hC hcoer) f

/-- **`lem:lift_coercivity` on the loop closure of a finite marked graph, at `C := B̂_σ`** — the
coercivity part of the detailed-balance half of `prop:morozov_rate`*(3)* (`proofs.tex:969`):
`1 + B̂_σ` is a coercivity constant of `K₂` on `L²(λ₂)` over `V × V`, the hypothesis for `π̂_←`
being `hcoer_of_graph`. Not stated here: `1 + B̂_σ ≥ 1` (from `BhatSigma_pos`) and the
restriction to `E` (`lift_coercivity_edgeSupport`), each one line. -/
theorem lift_coercivity_graph {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH : V → ℝ} (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hhit : B.IsHitExp uH) (h : V × V → ℝ) :
    Graph.nrmL2 (pairMeasure B.phat lam) (perpL2 (pairMeasure B.phat lam) h)
      ≤ (1 + BhatSigma G uH lam)
          * Graph.nrmL2 (pairMeasure B.phat lam) (Aop (pairKernel B.phat) (pairMeasure B.phat lam) h) :=
  lift_coercivity_finite (Core.phat_isMarkov B) (Core.isInvariant_of_isInvProb B hl)
    (BhatSigma_pos hpc hpos hl hhit).le (hcoer_of_graph hpc hpos hl hhit) h

end Instances

/-! ### Inhabitation: the two-state uniform chain -/

section Witness

/-- `twoStateK` (uniform `1/2`) is a Markov kernel. -/
theorem twoStateK_isMarkov : Core.IsMarkov twoStateK :=
  ⟨fun _ _ => by norm_num [twoStateK],
    fun _ => by simp only [twoStateK, Fin.sum_univ_two]; norm_num⟩

/-- `twoStateLam` is a non-negative `twoStateK`-invariant measure. -/
theorem twoStateLam_isInvariant : Core.IsInvariant twoStateLam twoStateK :=
  ⟨fun x => (twoStateLam_pos x).le, twoStateK_invariant⟩

/-- **`lift_coercivity_finite`'s hypotheses are inhabited, non-trivially**: on the uniform chain on
two states, `C = 1` is a coercivity constant (`LocalEnergy.twoState_coercivity`, attained), and
the lemma yields `2` for the edge lift on the four pairs. -/
theorem lift_coercivity_twoState (h : Fin 2 × Fin 2 → ℝ) :
    Graph.nrmL2 (pairMeasure twoStateK twoStateLam) (perpL2 (pairMeasure twoStateK twoStateLam) h)
      ≤ (1 + 1) * Graph.nrmL2 (pairMeasure twoStateK twoStateLam)
          (Aop (pairKernel twoStateK) (pairMeasure twoStateK twoStateLam) h) :=
  lift_coercivity_finite twoStateK_isMarkov twoStateLam_isInvariant zero_le_one
    twoState_coercivity h

end Witness

/-! ### The mixing coefficients as Mathlib operator norms

`Core.Mixing.beta P Π n = ‖P ^ n − Π‖` is the operator norm on `EuclideanSpace` that
`theo:db_stable_frozen_full`'s Lean (`WeightedL2.stable_frozen_discrete_mixing`) sums. On a weight
`λ > 0`, conjugation by the weighting isometry `wtL2` identifies it with `opNorm` of the density
deviation; on the pair space, where `λ₂` vanishes off the edge set, the identification runs
through the restriction to the support. -/

section MathlibNorm

variable {α : Type*} [Fintype α]

/-- `P^n` conjugated by the weighting. -/
theorem densOp_pow_wtL2 {lam : α → ℝ} (hlam : ∀ x, 0 < lam x) (K : α → α → ℝ) (n : ℕ)
    (a : α → ℝ) :
    (densOp lam K ^ n) (wtL2 lam a) = wtL2 lam ((Core.densAct lam K)^[n] a) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Function.iterate_succ_apply', ← densOp_wtL2 hlam, ← ih]
      rfl

/-- `P^n − Π` conjugated by the weighting is `densDeviation`. -/
theorem densDeviation_wtL2 {lam : α → ℝ} (hlam : ∀ x, 0 < lam x) (K : α → α → ℝ) (n : ℕ)
    (a : α → ℝ) :
    (densOp lam K ^ n - meanOp lam) (wtL2 lam a) = wtL2 lam (densDeviation K lam n a) := by
  rw [sub_apply, densOp_pow_wtL2 hlam, meanOp_wtL2 hlam, densDeviation_eq,
    ← wtL2_sub]
  rfl

/-- `opNorm` is the Mathlib operator norm of the conjugated operator: both are the infimum of the
same set of bounds, `wtL2` being a norm-preserving bijection. -/
theorem opNorm_eq_norm {lam : α → ℝ} (hlam : ∀ x, 0 < lam x) {A : (α → ℝ) → (α → ℝ)}
    {T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α} (hT : ∀ a, T (wtL2 lam a) = wtL2 lam (A a)) :
    opNorm lam A = ‖T‖ := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  rw [ContinuousLinearMap.norm_def, opNorm]
  congr 1
  ext b
  simp only [OpBound, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h v => ?_, fun h a => ?_⟩
  · obtain ⟨a, rfl⟩ := exists_wtL2 hlam v
    rw [hT, norm_wtL2 hnn, norm_wtL2 hnn, ← l2norm_eq_nrmL2, ← l2norm_eq_nrmL2]
    exact h a
  · have := h (wtL2 lam a)
    rwa [hT, norm_wtL2 hnn, norm_wtL2 hnn, ← l2norm_eq_nrmL2, ← l2norm_eq_nrmL2] at this

/-- **`opNorm` of the density deviation is `Core.Mixing.beta`**, on a positive weight. -/
theorem opNorm_densDeviation_eq_beta {lam : α → ℝ} (hlam : ∀ x, 0 < lam x) (K : α → α → ℝ)
    (n : ℕ) : opNorm lam (densDeviation K lam n) = Core.Mixing.beta (densOp lam K) (meanOp lam) n :=
  opNorm_eq_norm hlam fun a => densDeviation_wtL2 hlam K n a

variable {p : α → Prop} [DecidablePred p]

/-- A kernel's density action does not see a change of its argument off the support of the weight
(`w x = 0` kills the term). -/
theorem densAct_congr_supp {w : α → ℝ} (K : α → α → ℝ) {u u' : α → ℝ}
    (h : ∀ x, w x ≠ 0 → u x = u' x) : Core.densAct w K u = Core.densAct w K u' := by
  funext y
  rw [Core.densAct_apply, Core.densAct_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : w x = 0
  · simp only [hx, zero_mul]
  · rw [h x hx]

/-- … and its iterates agree on the support. -/
theorem densAct_iterate_congr_supp {w : α → ℝ} (K : α → α → ℝ) {u u' : α → ℝ}
    (h : ∀ x, w x ≠ 0 → u x = u' x) (n : ℕ) :
    ∀ x, w x ≠ 0 → (Core.densAct w K)^[n] u x = (Core.densAct w K)^[n] u' x := by
  induction n with
  | zero => exact h
  | succ k ih =>
      intro x _
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', densAct_congr_supp K ih]

/-- The density action restricts to the support. -/
theorem densAct_restrict {w : α → ℝ} (hw0 : ∀ a, ¬ p a → w a = 0) (K : α → α → ℝ)
    (f : {a // p a} → ℝ) :
    Core.densAct (fun e : {a // p a} => w e.1) (fun e e' => K e.1 e'.1) f
      = fun e => Core.densAct w K (extSupp f) e.1 := by
  funext e'
  have hnum : ∑ e : {a // p a}, w e.1 * K e.1 e'.1 * f e = ∑ a, w a * K a e'.1 * extSupp f a := by
    rw [← sum_subtype_of_vanish (fun a => w a * K a e'.1 * extSupp f a)
      fun a ha => by rw [hw0 a ha, zero_mul, zero_mul]]
    exact Finset.sum_congr rfl fun e _ => by rw [extSupp_val]
  rw [Core.densAct_apply, Core.densAct_apply, hnum]

/-- … and so do its iterates, read on the support. -/
theorem densAct_iterate_restrict {w : α → ℝ} (hw0 : ∀ a, ¬ p a → w a = 0) (K : α → α → ℝ)
    (n : ℕ) (f : {a // p a} → ℝ) :
    (Core.densAct (fun e : {a // p a} => w e.1) (fun e e' => K e.1 e'.1))^[n] f
      = fun e => (Core.densAct w K)^[n] (extSupp f) e.1 := by
  induction n with
  | zero => exact funext fun e => (extSupp_val f e).symm
  | succ k ih =>
      funext e
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', densAct_restrict hw0, ih]
      refine congrFun (densAct_congr_supp K fun x hx => ?_) e.1
      have hpx : p x := by
        by_contra hnp
        exact hx (hw0 x hnp)
      rw [show x = (⟨x, hpx⟩ : {a // p a}).1 from rfl, extSupp_val]

/-- The density deviation restricts to the support. -/
theorem densDeviation_restrict {w : α → ℝ} (hw0 : ∀ a, ¬ p a → w a = 0) (K : α → α → ℝ)
    (n : ℕ) (f : {a // p a} → ℝ) :
    densDeviation (fun e e' : {a // p a} => K e.1 e'.1) (fun e => w e.1) n f
      = fun e => densDeviation K w n (extSupp f) e.1 := by
  have hm : ∑ e : {a // p a}, w e.1 * f e = ∑ a, w a * extSupp f a := by
    rw [← sum_subtype_of_vanish (fun a => w a * extSupp f a)
      fun a ha => by rw [hw0 a ha, zero_mul]]
    exact Finset.sum_congr rfl fun e _ => by rw [extSupp_val]
  rw [densDeviation_eq, densAct_iterate_restrict hw0, hm]
  rfl

/-- **`β_n` is unchanged by restriction to the support of the weight.** -/
theorem opNorm_densDeviation_restrict {w : α → ℝ} (hw0 : ∀ a, ¬ p a → w a = 0)
    (K : α → α → ℝ) (n : ℕ) :
    opNorm (fun e : {a // p a} => w e.1) (densDeviation (fun e e' => K e.1 e'.1) (fun e => w e.1) n)
      = opNorm w (densDeviation K w n) := by
  have hf : ∀ f : {a // p a} → ℝ, (fun e : {a // p a} => extSupp f e.1) = f :=
    fun f => funext fun e => extSupp_val f e
  have hset : {b | OpBound (fun e : {a // p a} => w e.1)
        (densDeviation (fun e e' => K e.1 e'.1) (fun e => w e.1) n) b}
      = {b | OpBound w (densDeviation K w n) b} := by
    ext b
    simp only [OpBound, Set.mem_setOf_eq, l2norm_eq_nrmL2]
    refine and_congr_right fun _ => ⟨fun h u => ?_, fun h f => ?_⟩
    · have hu := h (fun e => u e.1)
      rw [densDeviation_restrict hw0, nrmL2_restrict hw0, nrmL2_restrict hw0] at hu
      have hagree : ∀ x, w x ≠ 0 → extSupp (fun e : {a // p a} => u e.1) x = u x := by
        intro x hx
        have hpx : p x := by
          by_contra hnp
          exact hx (hw0 x hnp)
        exact extSupp_val (fun e : {a // p a} => u e.1) ⟨x, hpx⟩
      have hdev : Graph.nrmL2 w (densDeviation K w n (extSupp fun e : {a // p a} => u e.1))
          = Graph.nrmL2 w (densDeviation K w n u) := by
        refine Core.nrmL2_congr fun x hx => ?_
        rw [densDeviation_apply_eq, densDeviation_apply_eq,
          densAct_iterate_congr_supp K hagree n x hx]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : w y = 0
        · rw [hy, zero_mul, zero_mul]
        · rw [hagree y hy]
      rwa [hdev] at hu
    · have hu := h (extSupp f)
      rw [densDeviation_restrict hw0, nrmL2_restrict hw0]
      rw [← nrmL2_restrict hw0 (extSupp f), hf] at hu
      exact hu
  simp only [opNorm, hset]

end MathlibNorm

/-! ### `lem:lift_mixing` on the edge set, in `Core.Mixing`'s norm -/

section MixingBeta

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:lift_mixing` in the norm `Core.Mixing` sums**: for `λ > 0`, on the edge set
`E = {(s,s') : π_←(s' → s) > 0}` where `λ₂ > 0`,
`β̂_{n+1} = ‖P₂^{n+1} − Π₂‖ = ‖P^n − Π‖ = β_n` as operator norms on `EuclideanSpace`, `P`, `P₂`
the density actions conjugated by the weighting (`WeightedL2.densOp`). -/
theorem lift_mixing_beta {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) (hlam : ∀ x, 0 < lam x) (hinv : Invariant pb lam)
    (htot : ∑ x, lam x = 1) (n : ℕ) :
    Core.Mixing.beta
        (densOp (fun e : {q : V × V // 0 < pb q.2 q.1} => pairMeasure pb lam e.1)
          (fun e e' => pairKernel pb e.1 e'.1))
        (meanOp (fun e : {q : V × V // 0 < pb q.2 q.1} => pairMeasure pb lam e.1)) (n + 1)
      = Core.Mixing.beta (densOp lam pb) (meanOp lam) n := by
  have hpos : ∀ e : {q : V × V // 0 < pb q.2 q.1}, 0 < pairMeasure pb lam e.1 :=
    fun e => mul_pos e.2 (hlam e.1.2)
  rw [← opNorm_densDeviation_eq_beta hpos, ← opNorm_densDeviation_eq_beta hlam,
    opNorm_densDeviation_restrict (pairMeasure_eq_zero_off hnn lam),
    lift_mixing_dens hnn hrow (fun x => (hlam x).le) hinv htot]

end MixingBeta

/-! ### `lem:lift_mixing` is not `0 = 0`: `β̂₁ = β₀ = 1` on the two-state chain -/

section MixingWitness

/-- **`lift_mixing_dens` at `n = 0` on the two-state chain**: `β̂₁ = β₀ = 1`, the right-hand side
being `WeightedL2Norm.twoState_beta_zero` read back through `opNorm_densDeviation_eq_beta`. -/
theorem twoState_lift_beta_one :
    opNorm (pairMeasure twoStateK twoStateLam)
      (densDeviation (pairKernel twoStateK) (pairMeasure twoStateK twoStateLam) 1) = 1 := by
  rw [lift_mixing_dens twoStateK_isMarkov.nonneg twoStateK_isMarkov.row_sum
    twoStateLam_isInvariant.nonneg twoStateK_invariant twoStateLam_sum 0,
    opNorm_densDeviation_eq_beta twoStateLam_pos, twoState_beta_zero]

end MixingWitness

end GFNBounds.Balance
