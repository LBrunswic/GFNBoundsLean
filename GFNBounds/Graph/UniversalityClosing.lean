import GFNBounds.Core.FamilyUniversality

/-!
# The closing paragraph of the finite-graph universality theorem: a frozen family matches every full-support target exactly, at every `p`

**`theo:universality_graphs`** — statement `proofs.tex:1125–1141`, **the closing paragraph at
`:1140`**, its proof at `:1170`; also a finding on item *(3)* (`:1136–1138`) when `G` has an edge
`s₀ → s_f`. Items *(1)*–*(3)* are `GFNBounds/Graph/Setting.lean`'s and
`GFNBounds/Graph/Universality.lean`'s; the sampler clause of item *(3)* and "samples `R` exactly"
are `GFNBounds/Graph/SamplerWiring.lean`'s, downstream of this file.

(Line citations to `proofs.tex` drift, `kb/entries/0036`.)

> (`theo:universality_graphs`, item *(3)* and the closing paragraph) *(3)* for `c = Z/λ(s₀)`,
> cutting the wrap edge turns this element into a generative flow on `G` satisfying the
> flow-matching constraint exactly, with initial flow of total mass `Z` carried by the edges out of
> `s₀` and terminal flow `F_term = R := Z π_←(s_f → ·)`, positive on every terminating state; in
> particular its sampler satisfies `s_τ ∼ R/Z` by Theorem `theo:sampling_theorem`.
>
> Consequently, for every target distribution `R` with full support on the terminating states of
> `G`, freezing `π_←(s_f → ·) := R` produces a frozen-backward family whose unique balanced flow
> samples `R` exactly: the universality infimum vanishes and is attained, simultaneously for every
> `p ∈ [1,+∞]` — the family is strongly universal over terminal targets.

> (proof, `:1170`) For the final statement, given a target `R` with full support on the terminating
> states, the backward policy with `π_←(s_f → ·) = R` is positive on every termination edge, so
> *(3)* applies: the balanced flow matches the target exactly, every reasonable loss vanishes on it,
> and all residuals `δF_init`, `δF_term` are zero — in every `L^p` norm at once, the state space
> being finite.

## Findings (reported, not worked around)

1. **The closing paragraph's derivation fails when `G` has an edge `s₀ → s_f`; its conclusion does
   not.** A target on `𝒮` does not charge `s₀`, so freezing sets `π_←(s_f → s₀) = 0` on the edge
   `s₀ → s_f`, and the frozen policy is positive on every edge — the hypothesis under which the
   proof at `:1170` invokes *(3)* — **iff** there is no such edge
   (`freezeSink_positiveOnEdges_iff`; on the triangle `0 → 1 → 2`, `0 → 2`, `triSrcSnk_check`). The
   conclusion is nevertheless proved here **with no hypothesis on that edge**
   (`universality_graphs_closing`): irreducibility, positivity and uniqueness of `λ`, and the ray
   of item *(2)*, need positivity only off `s₀ → s_f` (`breach_all_off`, `invProb_unique_off`,
   `frozenBalance_eq_off`), and item *(3)*'s flow-matching identity needs none. The repair the
   author may choose: ask positivity "on every edge except `s₀ → s_f`" in the theorem, or exclude
   the edge.
2. **Item *(3)* read on `𝒮` holds iff `G` has no edge `s₀ → s_f`.** Under the theorem's own
   hypotheses, *(3)*'s flow has initial and terminal mass `Z(1 − π_←(s_f → s₀))` on `𝒮`, and
   `R := Zπ_←(s_f → ·)` charges `s₀ ∉ 𝒮` by `Zπ_←(s_f → s₀) > 0` (`item_three_masses_on_internal`;
   instance `triSrcSnk_check`). So "initial flow of total mass `Z`" and "`F_term = R`", as
   distributions on `𝒮`, and with them `s_τ ∼ R/Z`, fail exactly when the edge is present — for the
   sampler, read literally as "the law of `s_τ` is `R/Z`" (`SamplerWiring.universality_graphs_sampler_iff`);
   in `app:notation`'s normalized sense, `R` read on `𝒮`, the sampler clause holds with the edge too,
   `s_τ` having law `R|_𝒮/R(𝒮)` (`SamplerWiring.universality_graphs_sampler`). This is
   the pointer `Core/FamilyUniversality.lean`'s SCOPE records for this row.
3. **A notation point, not an error: the letter `R`.** In item *(3)* `R := Zπ_←(s_f → ·)` carries
   mass `Z`; two lines later `R` is a "target distribution" and the sink row is frozen to `R`. A
   probability row needs `R/Z`; at `Z = 1` the two readings agree. `freezeSink` freezes to `R/Z`
   and the terminal flow is then `R` (`Graph.BackwardPolicy.termFlow_eq_target`). For the author.
4. **For the author: what is a "terminating state"?** Read here as internal (`x ∈ 𝒮` with an edge
   `x → s_f`). The paper does not define it; flows and targets live on `𝒮 = 𝒱 ∖ {s₀, s_f}`
   (`introduction.tex:84–86`, `proofs.tex:1162`), but the proof of *(3)* says `R` "is positive on
   every terminating state since `π_←` is positive on every edge `x → s_f`" (`proofs.tex:1162`),
   which read literally counts `s₀` when `s₀ → s_f` is an edge. Under that reading a full-support
   `R` charges `s₀ ∉ 𝒮`, and the closing conclusion on `𝒮` fails: the reading decides whether the
   paragraph is true.
5. **For the author: `F_init` is not free.** "Strongly universal over terminal targets" holds with
   `F_init` forced by the frozen family (see SCOPE), not for an arbitrary `F_init`.

## What is proved

| | |
|---|---|
| `IsFullTarget`, `IsFullTarget.isTarget`, `IsFullTarget.eq_zero_of_not_mem` | a target of mass `Z` with full support on the terminating states; it is a `PartialSupport.IsTarget` |
| `freezeSink`, `freezeSink_pb_snk`, `freezeSink_pb_of_ne` | the frozen policy: sink row `R/Z`, every other row `B`'s |
| `PositiveOffDirect`, `positiveOffDirect_of_positiveOnEdges`, `freezeSink_positiveOffDirect`, **`freezeSink_positiveOnEdges_iff`** | positivity off `s₀ → s_f`; freezing keeps it; full positivity iff no edge `s₀ → s_f` (finding 1) |
| `breach_of_reach_ne_snk`, `breach_of_reach_ne_src`, `breach_snk_src`, **`breach_all_off`**, `invProb_pos_off`, **`invProb_unique_off`**, **`frozenBalance_eq_off`** | item *(1)*'s irreducibility, positivity, uniqueness and item *(2)*'s ray, under positivity off `s₀ → s_f` (each docstring names the strict lemma it generalizes) |
| `frozenFamily`, `frozenUnion_eq_iUnion`, `balancedMember`, `memberFlow_balancedMember` | `Θ_{π_←}`; `PartialSupport.FrozenUnion` is `⋃` of it over the policies positive on the edges; the balanced member and its edge flow, item *(3)*'s |
| `graphResidual_eq_zero_of_defect` | a defect vanishing on `𝒮` gives `PartialSupport.graphResidual = 0` at **every** `p`, `p = 0` included |
| **`universality_graphs_closing`** | **the closing paragraph** — see its docstring |
| **`universality_graphs_strongly_universal`** | "strongly universal over terminal targets": for every full target, a member of the frozen family realizing residual `0` at every `p` for (its initial flow, `R`), both of mass `Z` on `𝒮` |
| **`item_three_masses_on_internal`** | finding 2 |
| `triangle_pathConnected`, `triangle_edge_src_snk`, `triSrcSnkPol`, `triSrcSnkPol_positiveOnEdges`, `triangleTarget_full`, **`triSrcSnk_check`** | inhabitation in the edge case, on `PartialSupport.triangle` and `PartialSupport.triangleTarget`: every hypothesis above inhabited, finding 2 exhibited, freezing not positive on every edge, and the closing conclusion delivered |

## Hypothesis checklist — the closing paragraph (`universality_graphs_closing`)

| paper | here |
|---|---|
| `G` finite, path-connected; `π_←` positive on every edge | ✓ `[Fintype V]`, `hpc`, `hB : B.PositiveOnEdges` (the rows `freezeSink` keeps) |
| total mass `Z > 0` | ✓ `hZ` |
| "target distribution `R` with full support on the terminating states" | ✓ `IsFullTarget G R Z`: `R ≥ 0`, mass `Z`, carried by internal states with an edge to `s_f`, positive on each — the internal reading of "terminating state", see SCOPE |
| "freezing `π_←(s_f → ·) := R`" | ⚠ frozen to `R/Z` (finding 3; `= R` at `Z = 1`); every other row `B`'s |
| (implicit in `:1170`) the frozen policy is positive on every edge | ✗ **false with an edge `s₀ → s_f`** (finding 1); replaced by `PositiveOffDirect`, which freezing provides, so **no hypothesis on that edge is added** |
| "frozen-backward family" | ✓ `frozenFamily`: `π_→` Markov, `f_out ≥ 0`, `FrozenBalance` |
| "unique balanced flow" | ✓ the balanced member of initial mass `Z` is in the family, non-trivial, and the only non-trivial member of initial mass `Z` |
| "samples `R` exactly" | ✓ downstream: `SamplerWiring.universality_graphs_closing_sampler` — the balanced flow's sampler terminates with `s_τ ∼ R/Z`, no hypothesis on `s₀ → s_f`; here, its terminal flow is `R`, its initial flow a distribution on `𝒮` of mass `Z`, and flow matching is exact on `𝒮` |
| "the universality infimum vanishes and is attained, simultaneously for every `p ∈ [1,+∞]`" | ✓ the balanced member's residual `graphResidual` is `0` for every `p : ℝ≥0∞` (one member for all `p`), and `⨅_{θ ∈ Θ} graphResidual = 0` for every `p` |
| "strongly universal over terminal targets" | ✓ `universality_graphs_strongly_universal` |

## SCOPE (disclosed)

* **Certified per pair.** The pair is (the balanced member's initial flow `e(s₀ → ·)`, `R`); the
  statement proves that initial flow is a distribution carried by `𝒮` of mass `Z`, as `R` is. The
  residual is `Core/FamilyUniversality.lean`'s `graphResidual`, `def:universality`'s
  `‖δf_init‖_p + ‖δf_term‖_p` for the counting measure on `𝒮` with each member's defect
  `fmDefectE` taken against **its own** initial flow `e(s₀ → ·)` — the reading
  `Graph/Universality.lean` and `Core/FamilyUniversality.lean` record ("`F_init` is not free").
  Nothing is lost against `def:universality`'s fixed pair: the residual is `≥ 0`, and at the pair
  (`e_bal(s₀ → ·)`, `R`) the balanced member's own-init residual **is** the fixed-pair residual, so
  the fixed-pair infimum is `0` and attained by the same member. For an **arbitrary** `F_init` the
  claim is false, not merely unstated: each frozen family is a ray whose `F_init` is forced by the
  policy (on `s₀ → a, b → s_f` it is `F_init = R`), so "strongly universal over terminal targets"
  holds with `F_init` determined by the family, and `Θ` depends on `R` — the reading
  `Graph/Universality.lean` records ("`F_init` is not free") and `Core/FamilyUniversality.lean`
  per pair (ruling R6). Flagged for the author (finding 5). Every
  `p : ℝ≥0∞` is covered, a superset of `[1,∞]`; `[MeasurableSpace V] [MeasurableSingletonClass V]`
  are carried. No quantification over arbitrary admissible pairs, as in `Graph/Universality.lean`.
* **The sink row is frozen to `R/Z`**, which is `R` at `Z = 1` (finding 3, a notation point for
  the author, not an error).
* **The conclusion is proved with no hypothesis on the edge `s₀ → s_f`.** The theorem's
  `B.PositiveOnEdges` is kept (it is the paper's), and the frozen policy is shown to satisfy only
  `PositiveOffDirect`; items *(1)*–*(2)*'s lemmas are re-proved under that hypothesis here rather
  than widened in the strict `Graph/Setting.lean` and `Graph/Universality.lean`.
* **"Samples `R` exactly" and `s_τ ∼ R/Z` are certified downstream**, in
  `GFNBounds/Graph/SamplerWiring.lean`, which imports this file and the finite sampling theorem
  (`GFNBounds.Core.Sampling`): `universality_graphs_closing_sampler` (the balanced flow of the
  family frozen at `R` samples `R/Z`, no hypothesis on `s₀ → s_f`, since the frozen sink row
  vanishes at `s₀`) and, for finding 2, `universality_graphs_sampler_iff` (item *(3)*'s
  "the law of `s_τ` is `R/Z`" iff no edge `s₀ → s_f`; `universality_graphs_sampler` gives the law
  `R|_𝒮/R(𝒮)` in every case), inhabited in the edge case by `sampler_check_triangle`. No
  sampler is modelled in this file.
* **"Terminating state" is read as internal** (finding 4, an author question), as
  `Core/FamilyUniversality.lean`'s SCOPE reads it. The paper does not define the term: flows and
  targets live on `𝒮 = 𝒱 ∖ {s₀, s_f}` (`introduction.tex:84–86`, `proofs.tex:1162`), but the proof
  of *(3)* says `R` "is positive on every terminating state since `π_←` is positive on every edge
  `x → s_f`" (`proofs.tex:1162`), which read literally counts `s₀` when `s₀ → s_f` is an edge.
  `PartialSupport.IsTarget` is wider (it admits `R(s₀) ≠ 0`); `IsFullTarget.isTarget` places the
  targets here inside it.
* **A member is read on `𝒮` through its edge flow** `memberFlow θ`: `fwdStarE` is Lean's junk
  `x/0 = 0` where the star outflow vanishes, and the defect consumes only the product
  `outStar · fwdStarE`, which is the edge flow there too (`PartialSupport.outStar_mul_fwdStarE`).
  The `L^p` boundedness of `π_→⋆` that `def:universality` asks is automatic on a finite space and
  not stated.

**`sorry`-free.** `#print axioms` on `universality_graphs_closing`,
`universality_graphs_strongly_universal`, `freezeSink_positiveOnEdges_iff`,
`item_three_masses_on_internal` and `triSrcSnk_check` returns `[propext, Classical.choice,
Quot.sound]`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph.UniversalityClosing

open Finset MeasureTheory
open scoped ENNReal
open GFNBounds.Graph.PartialSupport

variable {V : Type*} [Fintype V] [DecidableEq V] {G : MarkedGraph V}

/-! ### Targets, and freezing the sink row -/

/-- **A target of mass `Z` with full support on the terminating states** (`proofs.tex:1140`). The
flows of `theo:universality_graphs` live on the internal state space `𝒮 = 𝒱 ∖ {s₀, s_f}`, and a
*terminating state* is an internal state `x` with an edge `x → s_f`: `R ≥ 0`, `R(𝒮) = Z`, `R`
charges terminating states only, and charges every one of them. -/
structure IsFullTarget (G : MarkedGraph V) (R : V → ℝ) (Z : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ R x
  mass : ∑ x, R x = Z
  supp : ∀ ⦃x⦄, R x ≠ 0 → x ∈ G.internal ∧ G.Edge x G.snk
  full : ∀ ⦃x⦄, x ∈ G.internal → G.Edge x G.snk → 0 < R x

/-- A full target is a target in `Core/FamilyUniversality.lean`'s (wider) sense. -/
theorem IsFullTarget.isTarget {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z) : IsTarget G R :=
  ⟨hR.nonneg, fun _ h => (hR.supp h).2⟩

/-- A target on `𝒮` vanishes at both marks. -/
theorem IsFullTarget.eq_zero_of_not_mem {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z) {x : V}
    (hx : x ∉ G.internal) : R x = 0 := by
  by_contra h
  exact hx (hR.supp h).1

/-- **"freezing `π_←(s_f → ·) := R`"** (`proofs.tex:1140`), with the row normalized:
`π_←(s_f → ·) := R/Z`, every other row that of `B`. At `Z = 1` this is the printed `:= R`. -/
noncomputable def freezeSink (B : BackwardPolicy G) {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z)
    (hZ : 0 < Z) : BackwardPolicy G where
  pb s s' := if s = G.snk then R s' / Z else B.pb s s'
  nonneg s s' := by
    by_cases h : s = G.snk
    · simp only [h, if_true]; exact div_nonneg (hR.nonneg s') hZ.le
    · simp only [h, if_false]; exact B.nonneg s s'
  row_sum s hs := by
    by_cases h : s = G.snk
    · simp only [h, if_true]; rw [← Finset.sum_div, hR.mass, div_self hZ.ne']
    · simp only [h, if_false]; exact B.row_sum hs
  supp s s' hs hne := by
    by_cases h : s = G.snk
    · simp only [h, if_true] at hne
      have hR0 : R s' ≠ 0 := fun h0 => hne (by rw [h0, zero_div])
      rw [h]; exact (hR.supp hR0).2
    · simp only [h, if_false] at hne
      exact B.supp hs hne

theorem freezeSink_pb_snk (B : BackwardPolicy G) {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z)
    (hZ : 0 < Z) (x : V) : (freezeSink B hR hZ).pb G.snk x = R x / Z := by
  simp only [freezeSink, if_true]

theorem freezeSink_pb_of_ne (B : BackwardPolicy G) {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z)
    (hZ : 0 < Z) {s : V} (hs : s ≠ G.snk) (x : V) : (freezeSink B hR hZ).pb s x = B.pb s x := by
  simp only [freezeSink, hs, if_false]

/-- **Positivity on every edge but the direct one `s₀ → s_f`.** The hypothesis the closing
paragraph actually has at its disposal after freezing: a target on `𝒮` gives `π_←(s_f → s₀) = 0`. -/
def PositiveOffDirect (B : BackwardPolicy G) : Prop :=
  ∀ ⦃s s'⦄, G.Edge s' s → s' ≠ G.src ∨ s ≠ G.snk → 0 < B.pb s s'

omit [DecidableEq V] in
theorem positiveOffDirect_of_positiveOnEdges {B : BackwardPolicy G} (hB : B.PositiveOnEdges) :
    PositiveOffDirect B := fun _ _ h _ => hB h

/-- **The frozen policy is positive on every edge but `s₀ → s_f`.** -/
theorem freezeSink_positiveOffDirect {B : BackwardPolicy G} (hB : B.PositiveOnEdges) {R : V → ℝ}
    {Z : ℝ} (hR : IsFullTarget G R Z) (hZ : 0 < Z) : PositiveOffDirect (freezeSink B hR hZ) := by
  intro s s' he hor
  by_cases hs : s = G.snk
  · subst hs
    rw [freezeSink_pb_snk]
    have hsrc : s' ≠ G.src := by
      rcases hor with h | h
      · exact h
      · exact absurd rfl h
    have hsnk : s' ≠ G.snk := fun e => G.no_edge_out_of_snk G.snk (e ▸ he)
    exact div_pos (hR.full (MarkedGraph.mem_internal.mpr ⟨hsrc, hsnk⟩) he) hZ
  · rw [freezeSink_pb_of_ne B hR hZ hs]
    exact hB he

/-- **FINDING (`proofs.tex:1140`): the closing paragraph cannot invoke item *(3)* when `s₀ → s_f`
is an edge.** The frozen policy is positive on every edge of `G` — the hypothesis of
`theo:universality_graphs` — **iff** `G` has no edge `s₀ → s_f`: a target on `𝒮` does not charge
`s₀`, so freezing sets `π_←(s_f → s₀) = 0`. -/
theorem freezeSink_positiveOnEdges_iff {B : BackwardPolicy G} (hB : B.PositiveOnEdges) {R : V → ℝ}
    {Z : ℝ} (hR : IsFullTarget G R Z) (hZ : 0 < Z) :
    (freezeSink B hR hZ).PositiveOnEdges ↔ ¬ G.Edge G.src G.snk := by
  constructor
  · intro hpos he
    have h := hpos he
    rw [freezeSink_pb_snk, hR.eq_zero_of_not_mem (fun hm => (MarkedGraph.mem_internal.mp hm).1 rfl),
      zero_div] at h
    exact lt_irrefl _ h
  · intro hno s s' he
    refine freezeSink_positiveOffDirect hB hR hZ he ?_
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    exact hno (h1 ▸ h2 ▸ he)

/-! ### Irreducibility, positivity and uniqueness under positivity off `s₀ → s_f`

Each lemma of this section re-proves a strict lemma of `Graph/Setting.lean` or
`Graph/Universality.lean` under `PositiveOffDirect` in place of `PositiveOnEdges`. Widening the
graduated files is out of this file's scope; the pairing is named in each docstring. -/

variable {B : BackwardPolicy G}

/-- A walk of `G` ending off `s_f` is reversed by the backward chain. Generalizes
`BackwardPolicy.breach_of_reach` (`Graph/Setting.lean`) from `PositiveOnEdges` to
`PositiveOffDirect`, for walks ending off `s_f`. -/
theorem breach_of_reach_ne_snk (hP : PositiveOffDirect B) {a b : V} (h : G.Reach a b)
    (hb : b ≠ G.snk) : B.BReach b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b' c _ hbc ih =>
    have hb' : b' ≠ G.snk := fun e => G.no_edge_out_of_snk c (e ▸ hbc)
    have hc : c ≠ G.src := fun e => G.no_edge_into_src b' (e ▸ hbc)
    have hstep : B.BStep c b' := by
      show 0 < B.phat c b'
      rw [B.phat_of_ne_src hc]
      exact hP hbc (Or.inr hb)
    exact Relation.ReflTransGen.head hstep (ih hb')

/-- A walk of `G` starting off `s₀` is reversed by the backward chain. Generalizes
`BackwardPolicy.breach_of_reach` (`Graph/Setting.lean`) from `PositiveOnEdges` to
`PositiveOffDirect`, for walks starting off `s₀`. -/
theorem breach_of_reach_ne_src (hP : PositiveOffDirect B) {a b : V} (h : G.Reach a b)
    (ha : a ≠ G.src) : B.BReach b a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a' c hac _ ih =>
    have hc : c ≠ G.src := fun e => G.no_edge_into_src a' (e ▸ hac)
    have hstep : B.BStep c a' := by
      show 0 < B.phat c a'
      rw [B.phat_of_ne_src hc]
      exact hP hac (Or.inl ha)
    exact (ih hc).tail hstep

/-- `s_f` reaches `s₀` backwards: its row charges some in-neighbour. (A helper for
`breach_all_off`; under `PositiveOnEdges` it is a case of `BackwardPolicy.breach_all`.) -/
theorem breach_snk_src (hpc : G.PathConnected) (hP : PositiveOffDirect B) :
    B.BReach G.snk G.src := by
  have hsnk : G.snk ≠ G.src := G.src_ne_snk.symm
  obtain ⟨y, -, hy⟩ : ∃ y ∈ Finset.univ, 0 < B.pb G.snk y := by
    by_contra hc
    push Not at hc
    have h0 : ∑ y, B.pb G.snk y = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (hc y (Finset.mem_univ y)) (B.nonneg _ _)
    rw [B.row_sum hsnk] at h0
    exact one_ne_zero h0
  have hedge : G.Edge y G.snk := B.supp hsnk hy.ne'
  have hstep : B.BStep G.snk y := by
    show 0 < B.phat G.snk y
    rw [B.phat_of_ne_src hsnk]; exact hy
  by_cases hys : y = G.src
  · rw [hys] at hstep; exact Relation.ReflTransGen.single hstep
  · have hy' : y ≠ G.snk := fun e => G.no_edge_out_of_snk G.snk (e ▸ hedge)
    exact Relation.ReflTransGen.head hstep (breach_of_reach_ne_snk hP (hpc.from_src y) hy')

/-- **Irreducibility of the backward chain under positivity off `s₀ → s_f`.** Generalizes
`BackwardPolicy.breach_all` (`Graph/Setting.lean`, `theo:universality_graphs`*(1)*). -/
theorem breach_all_off (hpc : G.PathConnected) (hP : PositiveOffDirect B) (x y : V) :
    B.BReach x y := by
  have h1 : B.BReach x G.src := by
    by_cases hx : x = G.snk
    · rw [hx]; exact breach_snk_src hpc hP
    · exact breach_of_reach_ne_snk hP (hpc.from_src x) hx
  have h2 : B.BReach G.snk y := by
    by_cases hy : y = G.src
    · rw [hy]; exact breach_snk_src hpc hP
    · exact breach_of_reach_ne_src hP (hpc.to_snk y) hy
  exact (h1.tail B.bstep_wrap).trans h2

/-- Positivity of the invariant probability. Generalizes `BackwardPolicy.IsInvProb.pos`
(`Graph/Setting.lean`). -/
theorem invProb_pos_off (hpc : G.PathConnected) (hP : PositiveOffDirect B) {lam : V → ℝ}
    (h : B.IsInvProb lam) (y : V) : 0 < lam y := by
  obtain ⟨x, hx⟩ := h.exists_pos
  exact h.pos_of_breach (breach_all_off hpc hP x y) hx

/-- Uniqueness of the invariant probability, by the ratio maximum principle. Generalizes
`BackwardPolicy.invProb_unique` (`Graph/Setting.lean`). -/
theorem invProb_unique_off (hpc : G.PathConnected) (hP : PositiveOffDirect B) {lam lam' : V → ℝ}
    (h : B.IsInvProb lam) (h' : B.IsInvProb lam') : lam = lam' := by
  have hp' : ∀ x, 0 < lam' x := fun x => invProb_pos_off hpc hP h' x
  obtain ⟨x0, -, hx0min⟩ := Finset.exists_min_image (Finset.univ : Finset V)
    (fun x => lam x / lam' x) ⟨G.src, Finset.mem_univ _⟩
  set t : ℝ := lam x0 / lam' x0 with ht
  have hnn : ∀ x, 0 ≤ lam x - t * lam' x := by
    intro x
    have hx : t ≤ lam x / lam' x := hx0min x (Finset.mem_univ x)
    have := (le_div_iff₀ (hp' x)).mp hx
    linarith
  have h0 : lam x0 - t * lam' x0 = 0 := by
    rw [ht, div_mul_cancel₀ _ (ne_of_gt (hp' x0)), sub_self]
  have hinv : ∀ y, ∑ x, (lam x - t * lam' x) * B.phat x y = lam y - t * lam' y := by
    intro y
    have hrw : ∀ x : V, (lam x - t * lam' x) * B.phat x y
        = lam x * B.phat x y - t * (lam' x * B.phat x y) := by
      intro x; ring
    rw [Finset.sum_congr rfl (fun x _ => hrw x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      h.inv y, h'.inv y]
  have hall : ∀ x, lam x - t * lam' x = 0 := fun x =>
    BackwardPolicy.eq_zero_of_breach hnn hinv h0 (breach_all_off hpc hP x x0)
  have ht1 : t = 1 := by
    have h1 : ∑ x, lam x = ∑ x, t * lam' x :=
      Finset.sum_congr rfl fun x _ => by have := hall x; linarith
    rw [h.total, ← Finset.mul_sum, h'.total, mul_one] at h1
    exact h1.symm
  funext x
  have := hall x
  rw [ht1, one_mul] at this
  linarith

/-- `theo:universality_graphs`*(2)*, the forward inclusion. Generalizes
`BackwardPolicy.frozenBalance_eq` (`Graph/Universality.lean`). -/
theorem frozenBalance_eq_off (hpc : G.PathConnected) (hP : PositiveOffDirect B) {lam : V → ℝ}
    (h : B.IsInvProb lam) {pf : V → V → ℝ} {fout : V → ℝ} (hrow : ∀ u, ∑ v, pf u v = 1)
    (hnn : ∀ x, 0 ≤ fout x) (hne : fout ≠ 0) (hfb : B.FrozenBalance pf fout) :
    0 < ∑ z, fout z ∧ (∀ x, fout x = (∑ z, fout z) * lam x) ∧ pf = B.reversal lam := by
  have hinv : ∀ y, ∑ x, fout x * B.phat x y = fout y := by
    intro u
    have h1 : ∑ v, fout u * pf u v = ∑ v, B.phat v u * fout v :=
      Finset.sum_congr rfl fun v _ => hfb u v
    rw [← Finset.mul_sum, hrow u, mul_one] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  obtain ⟨x₀, hx₀⟩ : ∃ x, fout x ≠ 0 := by
    by_contra hc
    exact hne (funext fun x => not_not.mp (not_exists.mp hc x))
  have hc : 0 < ∑ z, fout z :=
    Finset.sum_pos' (fun i _ => hnn i) ⟨x₀, Finset.mem_univ _, (hnn x₀).lt_of_ne (Ne.symm hx₀)⟩
  have heq := invProb_unique_off hpc hP (B.isInvProb_normalized hnn hc hinv) h
  have hray : ∀ x, fout x = (∑ z, fout z) * lam x := by
    intro x
    have hx : fout x / (∑ z, fout z) = lam x := congrFun heq x
    rw [div_eq_iff (ne_of_gt hc)] at hx
    rw [hx]; ring
  refine ⟨hc, hray, ?_⟩
  have hlam : ∀ x, 0 < lam x := fun x => invProb_pos_off hpc hP h x
  funext u v
  have key := hfb u v
  rw [hray u, hray v] at key
  simp only [BackwardPolicy.reversal]
  rw [eq_div_iff (hlam u).ne']
  refine mul_left_cancel₀ (ne_of_gt hc) ?_
  linear_combination key

/-! ### The family, its balanced member, and the residual -/

/-- **The frozen-backward family `Θ_{π_←}`** (`proofs.tex:1133`): pairs `(π_→, f_out)` with `π_→` a
Markov kernel, `f_out ≥ 0`, and `(f_out μ) ⊗ π_→ = π̂_← ⊗ (f_out μ)`. -/
def frozenFamily (B : BackwardPolicy G) : Set ((V → V → ℝ) × (V → ℝ)) :=
  {θ | (∀ u, ∑ v, θ.1 u v = 1) ∧ (∀ u v, 0 ≤ θ.1 u v) ∧ (∀ x, 0 ≤ θ.2 x) ∧
    B.FrozenBalance θ.1 θ.2}

/-- `Core/FamilyUniversality.lean`'s `FrozenUnion` **is** the union of the frozen-backward
families over the backward policies positive on the edges of `G`. -/
theorem frozenUnion_eq_iUnion :
    FrozenUnion G = ⋃ (B : BackwardPolicy G) (_ : B.PositiveOnEdges), frozenFamily B := by
  ext θ
  simp only [FrozenUnion, frozenFamily, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

/-- **The balanced flow of initial mass `Z`**: `(π̂_←^λ, (Z/λ(s₀))λ)`, item *(3)*'s element. -/
noncomputable def balancedMember (B : BackwardPolicy G) (lam : V → ℝ) (Z : ℝ) :
    (V → V → ℝ) × (V → ℝ) :=
  (B.reversal lam, fun x => Z / lam G.src * lam x)

/-- The balanced member's edge flow is item *(3)*'s `edgeFlow` at `c = Z/λ(s₀)`. -/
theorem memberFlow_balancedMember {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (Z : ℝ) :
    memberFlow (balancedMember B lam Z) = B.edgeFlow lam (Z / lam G.src) := by
  funext u v
  simp only [memberFlow, balancedMember, BackwardPolicy.reversal, BackwardPolicy.edgeFlow]
  have := (hlam u).ne'
  field_simp

/-- A defect vanishing on `𝒮` has `graphResidual` `0` at **every** `p` — `p = 0` included, where
`eLpNorm` is `0` by definition. -/
theorem graphResidual_eq_zero_of_defect [MeasurableSpace V] [MeasurableSingletonClass V]
    {e : V → V → ℝ} {T : V → ℝ} (h : ∀ v ∈ G.internal, fmDefectE G e T v = 0) (p : ℝ≥0∞) :
    graphResidual G p e T = 0 := by
  by_cases hp : p = 0
  · subst hp
    rw [graphResidual, eLpNorm_exponent_zero, eLpNorm_exponent_zero, add_zero]
  · exact (graphResidual_eq_zero_iff hp e T).mpr h

/-! ### The closing paragraph -/

/-- **`theo:universality_graphs`, the closing paragraph** (`proofs.tex:1140`, proof `:1170`):
*for every target `R` with full support on the terminating states of `G`, freezing
`π_←(s_f → ·) := R` produces a frozen-backward family whose unique balanced flow [matches] `R`
exactly: the universality infimum vanishes and is attained, simultaneously for every
`p ∈ [1,+∞]`.*

With `R` of mass `Z` and the row frozen to `R/Z` (`freezeSink`):

* the frozen policy has sink row `R/Z`, the other rows of `B`, and is positive on every edge but
  `s₀ → s_f` — on every edge iff there is no such edge (`freezeSink_positiveOnEdges_iff`);
* its backward chain has a unique invariant probability `λ`, positive everywhere;
* the balanced flow of initial mass `Z` lies in `Θ_{π_←}` and is the **unique** non-trivial member
  of initial mass `Z`;
* its terminal flow `e(· → s_f)` is `R`, its initial flow `e(s₀ → ·)` is a distribution carried by
  `𝒮` of mass `Z`, and so is `R`;
* flow matching holds exactly on `𝒮` (`fmDefectE = 0`), so its residual `graphResidual` is `0` at
  every `p`, and the infimum of the residual over `Θ_{π_←}` is `0` at every `p`, attained.

**No hypothesis on the edge `s₀ → s_f`**: the paragraph's own derivation through item *(3)* needs
positivity on every edge, which freezing destroys when `s₀ → s_f` is an edge; the conclusion is
proved here from positivity off that edge. -/
theorem universality_graphs_closing [MeasurableSpace V] [MeasurableSingletonClass V]
    (hpc : G.PathConnected) (hB : B.PositiveOnEdges) {R : V → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hR : IsFullTarget G R Z) :
    (∀ x, (freezeSink B hR hZ).pb G.snk x = R x / Z)
    ∧ (∀ s, s ≠ G.snk → ∀ x, (freezeSink B hR hZ).pb s x = B.pb s x)
    ∧ PositiveOffDirect (freezeSink B hR hZ)
    ∧ ((freezeSink B hR hZ).PositiveOnEdges ↔ ¬ G.Edge G.src G.snk)
    ∧ (∃ lam : V → ℝ, (freezeSink B hR hZ).IsInvProb lam)
    ∧ (∀ lam lam' : V → ℝ, (freezeSink B hR hZ).IsInvProb lam → (freezeSink B hR hZ).IsInvProb lam'
        → lam = lam')
    ∧ ∀ lam : V → ℝ, (freezeSink B hR hZ).IsInvProb lam →
        (∀ x, 0 < lam x)
        ∧ (balancedMember (freezeSink B hR hZ) lam Z) ∈ frozenFamily (freezeSink B hR hZ)
        ∧ (balancedMember (freezeSink B hR hZ) lam Z).2 ≠ 0
        ∧ (∀ θ ∈ frozenFamily (freezeSink B hR hZ), θ.2 ≠ 0 → (∑ v, memberFlow θ G.src v = Z ↔
            θ = (balancedMember (freezeSink B hR hZ) lam Z)))
        ∧ (∀ x, memberFlow (balancedMember (freezeSink B hR hZ) lam Z) x G.snk = R x)
        ∧ (∀ v, 0 ≤ memberFlow (balancedMember (freezeSink B hR hZ) lam Z) G.src v)
        ∧ (∀ v, v ∉ G.internal → memberFlow (balancedMember (freezeSink B hR hZ) lam Z) G.src v = 0)
        ∧ ∑ v ∈ G.internal, memberFlow (balancedMember (freezeSink B hR hZ) lam Z) G.src v = Z
        ∧ (∀ v, v ∉ G.internal → R v = 0)
        ∧ ∑ v ∈ G.internal, R v = Z
        ∧ (∀ v ∈ G.internal,
            fmDefectE G (memberFlow (balancedMember (freezeSink B hR hZ) lam Z)) R v = 0)
        ∧ (∀ p : ℝ≥0∞,
            graphResidual G p (memberFlow (balancedMember (freezeSink B hR hZ) lam Z)) R = 0)
        ∧ (∀ p : ℝ≥0∞,
            ⨅ θ ∈ frozenFamily (freezeSink B hR hZ), graphResidual G p (memberFlow θ) R = 0) := by
  set B' := freezeSink B hR hZ
  have hP : PositiveOffDirect B' := freezeSink_positiveOffDirect hB hR hZ
  refine ⟨freezeSink_pb_snk B hR hZ, fun s hs x => freezeSink_pb_of_ne B hR hZ hs x, hP,
    freezeSink_positiveOnEdges_iff hB hR hZ, B'.exists_invProb,
    fun _ _ h h' => invProb_unique_off hpc hP h h', fun lam hl => ?_⟩
  have hlam : ∀ x, 0 < lam x := fun x => invProb_pos_off hpc hP hl x
  have hs0 : 0 < lam G.src := hlam G.src
  set c := Z / lam G.src with hc
  have hcpos : 0 < c := div_pos hZ hs0
  have hcZ : c * lam G.src = Z := div_mul_cancel₀ Z hs0.ne'
  have hedge := memberFlow_balancedMember (B := B') hlam Z
  have hsnk_ne : G.snk ≠ G.src := G.src_ne_snk.symm
  -- the target vanishes off `𝒮`, and has mass `Z` on `𝒮`
  have hRoff : ∀ v, v ∉ G.internal → R v = 0 := fun v hv => hR.eq_zero_of_not_mem hv
  have hsplit : ∀ f : V → ℝ, (∑ v ∈ G.internal, f v) + f G.snk + f G.src = ∑ v, f v := by
    intro f
    have h1 : (∑ v ∈ (Finset.univ.erase G.src), f v) + f G.src = ∑ v, f v :=
      Finset.sum_erase_add _ _ (Finset.mem_univ _)
    have h2 : (∑ v ∈ G.internal, f v) + f G.snk = ∑ v ∈ Finset.univ.erase G.src, f v :=
      Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hsnk_ne, Finset.mem_univ _⟩)
    rw [← h1, ← h2]
  have hsrc_nm : G.src ∉ G.internal := fun hm => (MarkedGraph.mem_internal.mp hm).1 rfl
  have hsnk_nm : G.snk ∉ G.internal := fun hm => (MarkedGraph.mem_internal.mp hm).2 rfl
  have hRS : ∑ v ∈ G.internal, R v = Z := by
    have := hsplit R
    rw [hRoff _ hsnk_nm, hRoff _ hsrc_nm, hR.mass] at this
    linarith
  -- the initial flow
  have hinit : ∀ v, memberFlow (balancedMember B' lam Z) G.src v = B'.initFlow lam c v := by
    intro v; rw [hedge]; rfl
  have hinit_off : ∀ v, v ∉ G.internal → memberFlow (balancedMember B' lam Z) G.src v = 0 := by
    intro v hv
    rw [hinit]
    simp only [BackwardPolicy.initFlow, BackwardPolicy.edgeFlow]
    by_cases hvs : v = G.src
    · rw [hvs, B'.phat_src_of_ne hsnk_ne.symm, mul_zero]
    · have hvk : v = G.snk := by
        by_contra hk; exact hv (MarkedGraph.mem_internal.mpr ⟨hvs, hk⟩)
      rw [hvk, B'.phat_of_ne_src hsnk_ne, freezeSink_pb_snk, hRoff _ hsrc_nm, zero_div, mul_zero]
  have hterm : ∀ x, memberFlow (balancedMember B' lam Z) x G.snk = R x := by
    intro x
    have h := B'.termFlow_eq_target hl hcZ x
    rw [freezeSink_pb_snk] at h
    rw [hedge]
    change B'.termFlow lam c x = R x
    rw [h]; field_simp
  have hdef : ∀ v ∈ G.internal, fmDefectE G (memberFlow (balancedMember B' lam Z)) R v = 0 := by
    intro v hv
    have hT : R = B'.termFlow lam c :=
      funext fun x => (hterm x).symm.trans (by rw [hedge]; rfl)
    rw [hT, hedge, ← fmDefect_eq_fmDefectE B' hl c v]
    exact B'.fmDefect_eq_zero hl hcpos.le hv
  have hmem : balancedMember B' lam Z ∈ frozenFamily B' :=
    ⟨fun u => B'.sum_reversal hl (hlam u).ne', fun u v => B'.reversal_nonneg hl.nonneg u v,
      fun x => mul_nonneg hcpos.le (hlam x).le, B'.frozenBalance_reversal hlam c⟩
  have hres : ∀ p : ℝ≥0∞, graphResidual G p (memberFlow (balancedMember B' lam Z)) R = 0 :=
    graphResidual_eq_zero_of_defect hdef
  refine ⟨hlam, hmem, fun h0 => ?_, fun θ hθ hne => ?_, hterm,
    fun v => by rw [hinit]; exact B'.edgeFlow_nonneg hl.nonneg hcpos.le _ _, hinit_off, ?_, hRoff,
    hRS, hdef, hres, fun p => le_antisymm ((iInf₂_le _ hmem).trans (hres p).le) zero_le⟩
  · have := congrFun h0 G.src
    simp only [balancedMember, Pi.zero_apply] at this
    exact (mul_pos hcpos hs0).ne' this
  · obtain ⟨hrow, -, hnn, hfb⟩ := hθ
    obtain ⟨hc', hray, hpf⟩ := frozenBalance_eq_off hpc hP hl hrow hnn hne hfb
    have hmass : ∑ v, memberFlow θ G.src v = (∑ z, θ.2 z) * lam G.src := by
      simp only [memberFlow]
      rw [← Finset.mul_sum, hrow, mul_one, hray]
    rw [hmass]
    constructor
    · intro hZ'
      have hcc : (∑ z, θ.2 z) = c := by
        rw [hc, eq_div_iff hs0.ne']; exact hZ'
      refine Prod.ext hpf (funext fun x => ?_)
      simp only [balancedMember]
      rw [hray x, hcc]
    · intro hθeq
      rw [hθeq]
      simp only [balancedMember]
      rw [← Finset.mul_sum, hl.total, mul_one]
      exact hcZ
  · have := hsplit (memberFlow (balancedMember B' lam Z) G.src)
    rw [hinit_off _ hsnk_nm, hinit_off _ hsrc_nm] at this
    have hall : ∑ v, memberFlow (balancedMember B' lam Z) G.src v = Z := by
      simp only [hinit]; rw [B'.sum_initFlow hl c, hcZ]
    linarith

/-- **"The family is strongly universal over terminal targets"** (`proofs.tex:1140`): for every
target `R` of mass `Z > 0` with full support on the terminating states, the family frozen at `R`
contains a flow whose initial flow is a distribution on `𝒮` of mass `Z` and whose residual for the
pair (that initial flow, `R`) is `0` at every `p` at once. -/
theorem universality_graphs_strongly_universal [MeasurableSpace V] [MeasurableSingletonClass V]
    (hpc : G.PathConnected) (hB : B.PositiveOnEdges) :
    ∀ (R : V → ℝ) (Z : ℝ) (hZ : 0 < Z) (hR : IsFullTarget G R Z),
      ∃ θ ∈ frozenFamily (freezeSink B hR hZ),
        (∀ v, 0 ≤ memberFlow θ G.src v) ∧ (∀ v, v ∉ G.internal → memberFlow θ G.src v = 0)
        ∧ ∑ v ∈ G.internal, memberFlow θ G.src v = Z ∧ ∑ v ∈ G.internal, R v = Z
        ∧ ∀ p : ℝ≥0∞, graphResidual G p (memberFlow θ) R = 0 := by
  intro R Z hZ hR
  obtain ⟨-, -, -, -, ⟨lam, hl⟩, -, hall⟩ := universality_graphs_closing hpc hB hZ hR
  obtain ⟨-, hmem, -, -, -, hnn, hoff, hmass, -, hRS, -, hres, -⟩ := hall lam hl
  exact ⟨_, hmem, hnn, hoff, hmass, hRS, hres⟩

/-! ### FINDING: item *(3)* on `𝒮` when `s₀ → s_f` is an edge -/

/-- **FINDING (`proofs.tex:1136–1138`, item *(3)*).** Under the theorem's own hypotheses, item
*(3)*'s flow at `c = Z/λ(s₀)` has, on `𝒮`, initial and terminal mass `Z(1 − π_←(s_f → s₀))`, and its
terminal flow `F_term = Z π_←(s_f → ·)` charges `s₀ ∉ 𝒮` by `Z π_←(s_f → s₀)`. So *"initial flow of
total mass `Z`"*, *"terminal flow `F_term = R := Zπ_←(s_f → ·)`"* read on `𝒮`, and hence
`s_τ ∼ R/Z`, hold **iff** `G` has no edge `s₀ → s_f`. -/
theorem item_three_masses_on_internal (hpc : G.PathConnected) (hB : B.PositiveOnEdges)
    {lam : V → ℝ} (hl : B.IsInvProb lam) {Z c : ℝ} (hZ : 0 < Z) (hc : c = Z / lam G.src) :
    B.termFlow lam c G.src = Z * B.pb G.snk G.src
    ∧ ∑ v ∈ G.internal, B.termFlow lam c v = Z * (1 - B.pb G.snk G.src)
    ∧ ∑ v ∈ G.internal, B.initFlow lam c v = Z * (1 - B.pb G.snk G.src)
    ∧ (0 < B.pb G.snk G.src ↔ G.Edge G.src G.snk)
    ∧ (∑ v ∈ G.internal, B.termFlow lam c v = Z ↔ ¬ G.Edge G.src G.snk)
    ∧ (∑ v ∈ G.internal, B.initFlow lam c v = Z ↔ ¬ G.Edge G.src G.snk) := by
  obtain ⟨-, hcZ, -, hinit, hterm, -, -, -⟩ := B.universality_graphs_three hpc hB hl hZ hc
  have hsnk_ne : G.snk ≠ G.src := G.src_ne_snk.symm
  have hsplit : ∀ f : V → ℝ, (∑ v ∈ G.internal, f v) + f G.snk + f G.src = ∑ v, f v := by
    intro f
    have h1 : (∑ v ∈ (Finset.univ.erase G.src), f v) + f G.src = ∑ v, f v :=
      Finset.sum_erase_add _ _ (Finset.mem_univ _)
    have h2 : (∑ v ∈ G.internal, f v) + f G.snk = ∑ v ∈ Finset.univ.erase G.src, f v :=
      Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hsnk_ne, Finset.mem_univ _⟩)
    rw [← h1, ← h2]
  have hpbsnk : B.pb G.snk G.snk = 0 := by
    by_contra h
    exact G.no_edge_out_of_snk G.snk (B.supp hsnk_ne h)
  have hiff : 0 < B.pb G.snk G.src ↔ G.Edge G.src G.snk :=
    ⟨fun h => B.supp hsnk_ne h.ne', fun h => hB h⟩
  have hT : ∑ v ∈ G.internal, B.termFlow lam c v = Z * (1 - B.pb G.snk G.src) := by
    have h := hsplit (B.termFlow lam c)
    have htot : ∑ v, B.termFlow lam c v = Z := by
      simp only [hterm]; rw [← Finset.mul_sum, B.row_sum hsnk_ne, mul_one]
    rw [hterm G.snk, hterm G.src, hpbsnk, htot] at h
    linarith
  have hI : ∑ v ∈ G.internal, B.initFlow lam c v = Z * (1 - B.pb G.snk G.src) := by
    have h := hsplit (B.initFlow lam c)
    have hsrc0 : B.initFlow lam c G.src = 0 := by
      simp only [BackwardPolicy.initFlow, BackwardPolicy.edgeFlow,
        B.phat_src_of_ne hsnk_ne.symm, mul_zero]
    have hsnk0 : B.initFlow lam c G.snk = Z * B.pb G.snk G.src := by
      simp only [BackwardPolicy.initFlow, BackwardPolicy.edgeFlow, B.phat_of_ne_src hsnk_ne,
        hl.lam_snk_eq_src, hcZ]
    rw [hsrc0, hsnk0, hinit] at h
    linarith
  refine ⟨hterm G.src, hT, hI, hiff, ?_, ?_⟩
  · rw [hT, ← hiff]
    have h0 := B.nonneg G.snk G.src
    constructor
    · intro h hpos; nlinarith [mul_pos hZ hpos]
    · intro h; have : B.pb G.snk G.src = 0 := le_antisymm (not_lt.mp h) h0
      rw [this]; ring
  · rw [hI, ← hiff]
    have h0 := B.nonneg G.snk G.src
    constructor
    · intro h hpos; nlinarith [mul_pos hZ hpos]
    · intro h; have : B.pb G.snk G.src = 0 := le_antisymm (not_lt.mp h) h0
      rw [this]; ring

/-! ### Inhabitation on the triangle `s₀ = 0 → 1 → 2 = s_f`, `0 → 2`: the edge case itself

The graph and the target are `Core/FamilyUniversality.lean`'s `PartialSupport.triangle` and
`PartialSupport.triangleTarget` (`δ₁`). -/

section TriSrcSnk

theorem triangle_pathConnected : triangle.PathConnected := by
  have e01 : triangle.Edge 0 1 := Or.inl ⟨rfl, rfl⟩
  have e12 : triangle.Edge 1 2 := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have e02 : triangle.Edge 0 2 := Or.inr (Or.inr ⟨rfl, rfl⟩)
  intro s
  fin_cases s
  · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.single e02⟩
  · exact ⟨Relation.ReflTransGen.single e01, Relation.ReflTransGen.single e12⟩
  · exact ⟨Relation.ReflTransGen.single e02, Relation.ReflTransGen.refl⟩

theorem triangle_edge_src_snk : triangle.Edge triangle.src triangle.snk :=
  Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- The backward policy `π_←(1 → 0) = 1`, `π_←(2 → 1) = π_←(2 → 0) = 1/2` on the triangle. -/
noncomputable def triSrcSnkPol : BackwardPolicy triangle where
  pb s s' := !![0, 0, 0; 1, 0, 0; 1/2, 1/2, 0] s s'
  nonneg s s' := by fin_cases s <;> fin_cases s' <;> norm_num
  row_sum s hs := by
    fin_cases s
    · exact absurd rfl hs
    · norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    · norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  supp s s' _ hne := by
    revert hne
    fin_cases s <;> fin_cases s' <;> simp [triangle]

theorem triSrcSnkPol_positiveOnEdges : triSrcSnkPol.PositiveOnEdges := by
  intro s s' he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [triSrcSnkPol]

/-- The target `δ₁`, of mass `1`: full support on the one (internal) terminating state. -/
theorem triangleTarget_full : IsFullTarget triangle triangleTarget 1 := by
  refine ⟨fun x => ?_, ?_, fun x hx => ?_, fun x hx _ => ?_⟩
  · simp only [triangleTarget]; split_ifs <;> norm_num
  · simp [triangleTarget]
  · have h1 : x = 1 := by
      by_contra hc; exact hx (by simp only [triangleTarget, hc, if_false])
    subst h1
    exact ⟨MarkedGraph.mem_internal.mpr ⟨by decide, by decide⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · obtain ⟨h0, h2⟩ := MarkedGraph.mem_internal.mp hx
    have h1 : x = 1 := by
      fin_cases x
      · exact absurd rfl h0
      · rfl
      · exact absurd rfl h2
    subst h1; simp [triangleTarget]

/-- **The hypotheses of both findings and of the closing theorem are inhabited, in the edge case.**
On the triangle with `π_←` positive on every edge: item *(3)*'s terminal flow charges `s₀` and its
`𝒮`-mass falls short of `Z`; freezing at the full target `δ₁` is **not** positive on every edge; and
yet the closing paragraph's conclusion holds — the residual for `(F_init, δ₁)` is `0` at every `p`,
with `F_init` of mass `1` on `𝒮`. -/
theorem triSrcSnk_check :
    triangle.PathConnected ∧ triSrcSnkPol.PositiveOnEdges ∧ triangle.Edge triangle.src triangle.snk
    ∧ (∃ lam : Fin 3 → ℝ, triSrcSnkPol.IsInvProb lam
        ∧ 0 < triSrcSnkPol.termFlow lam (1 / lam triangle.src) triangle.src
        ∧ ∑ v ∈ triangle.internal, triSrcSnkPol.termFlow lam (1 / lam triangle.src) v < 1)
    ∧ ¬ (freezeSink triSrcSnkPol triangleTarget_full one_pos).PositiveOnEdges
    ∧ ∃ θ ∈ frozenFamily (freezeSink triSrcSnkPol triangleTarget_full one_pos),
        ∑ v ∈ triangle.internal, memberFlow θ triangle.src v = 1
        ∧ ∀ p : ℝ≥0∞, graphResidual triangle p (memberFlow θ) triangleTarget = 0 := by
  have hpc := triangle_pathConnected
  have hB := triSrcSnkPol_positiveOnEdges
  have he := triangle_edge_src_snk
  obtain ⟨lam, hl⟩ := triSrcSnkPol.exists_invProb
  refine ⟨hpc, hB, he, ⟨lam, hl, ?_⟩, fun h => (freezeSink_positiveOnEdges_iff hB
    triangleTarget_full one_pos).mp h he, ?_⟩
  · obtain ⟨h1, h2, -, hiff, -, -⟩ :=
      item_three_masses_on_internal (Z := 1) (c := 1 / lam triangle.src) hpc hB hl one_pos rfl
    have hpb : 0 < triSrcSnkPol.pb triangle.snk triangle.src := hiff.mpr he
    refine ⟨?_, ?_⟩
    · rw [h1]; linarith
    · rw [h2]; nlinarith
  · obtain ⟨θ, hθ, -, -, hmass, -, hres⟩ :=
      universality_graphs_strongly_universal hpc hB triangleTarget 1 one_pos triangleTarget_full
    exact ⟨θ, hθ, hmass, hres⟩

end TriSrcSnk

end GFNBounds.Graph.UniversalityClosing
