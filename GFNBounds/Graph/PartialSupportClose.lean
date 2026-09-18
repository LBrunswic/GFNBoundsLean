import GFNBounds.Core.FamilyUniversality

/-!
# `rem:partial_support` on the paper's terminating states, with or without an edge `s₀ → s_f`

**`rem:partial_support`** — `proofs.tex:1181–1183` (a remark, no proof environment; the label is
the anchor, kb 0036). The statement is quoted in full in `GFNBounds/Core/FamilyUniversality.lean`.

`Core/FamilyUniversality.lean` (namespace `GFNBounds.Graph.PartialSupport`) certifies the remark
with one disclosed divergence: **when `s₀ → s_f` is an edge of `G`**, its `subGraph` deletes that
edge (it deletes `y → s_f` for *every* `y` with `R(y) = 0`, `s₀` included) and its `unif` charges
`s₀`. In the paper terminating states are internal (`𝒮 = 𝒱 ∖ {s₀, s_f}`, `introduction.tex:84–86`,
`proofs.tex:1162`), so the paper's `G′` **keeps** the edge `s₀ → s_f`, and the paper's `unif` is
uniform on the internal terminating states. This file certifies the remark on the paper's objects
in every case, and reduces to the strict file's objects when `s₀ → s_f` is not an edge.

## What is proved

| paper | here |
|---|---|
| a target on the terminating states | `IsTargetI`: `R ≥ 0`, charging only internal states with an edge to `s_f` |
| `G′`: induced on `s₀`, `s_f`, the states reaching `supp R`; terminating edges `y → s_f`, `R(y) = 0`, deleted | `subGraphI` (`Deleted`: `y` internal and `R(y) = 0`); `subGraphI_edge_iff_of_not_edge`: the strict `subGraph` when `s₀ ↛ s_f` |
| `G′` is again path-connected | `subGraphI_pathConnected` |
| a policy positive on the edges of `G` restricts to one on `G′`, only its sink row renormalized | `restrict_policyI` (`restrictWithI`, `renormRowI`) |
| theorem on `G′`, extended by zero: `equ:FM_const` on `G` exactly, terminal flow `R` | `partial_support_exactI` |
| … in the frozen-backward family of `G′` | the `FrozenBalance` conjunct of `partial_support_exactI` |
| … not in that of `G` | `partial_support_not_in_GI` |
| `(1−ε)R + εZ unif`, full-support targets, realize `R` as a limit of exactly matched flows | `unifI`, `epsTargetI`, `isTargetI_epsTargetI`, `epsTargetI_pos`, `sum_epsTargetI`, `member_epsTargetI` |
| the infimum over the union vanishes, and is not attained | `iInf_graphResidual_eq_zeroI`, `graphResidual_ne_zeroI` (the strict statements, on `IsTargetI`) |
| inhabitation of the edge case | `diamondE_check`, `diamondE_partial_support` (a graph with `s₀ → s_f`, a target vanishing on an internal terminating state) |

## SCOPE (disclosed)

* **The sink row in the edge case.** `theo:universality_graphs` applied to `G′` freezes
  `π_←(s_f → ·)`; with an edge `s₀ → s_f` in `G′` the frozen row must keep weight `α > 0` on `s₀`
  to stay positive on that edge (freezing it to `R/Z` breaks positivity, the pointer recorded on
  row `theo:universality_graphs`). `partial_support_exactI` takes the row
  `q_α = (1−α) R/Z + α δ_{s₀}`, `α ∈ [0,1)`, `α > 0` iff `s₀ → s_f` is an edge, and the constant
  `c = Z/((1−α) λ′(s₀))`; theorem (3)'s terminal flow `Z/(1−α) · q_α` is then `R` **on `𝒮`**, and
  the mass `αZ/(1−α)` it sends along `s₀ → s_f` is invisible to `equ:FM_const`, which lives on
  `𝒮`. With no edge, `α = 0` and this is the strict file's row `R/Z`. The remark claims exactly
  "flow-matching on `G` exactly, with terminal flow `R`", both on `𝒮`. The source's total outflow is
  `Z/(1−α)` (the `∑ v, extend … G.src v` conjunct); `αZ/(1−α)` of it leaves along `s₀ → s_f`, so
  the initial flow on `𝒮` has mass `Z`, as in theorem (3), by conservation (not a separate
  conjunct).
* **The restriction sentence** is certified as written: rows off the sink are `π_←`'s, the sink row
  is `π_←(s_f → ·)` restricted to the in-neighbours of `s_f` in `G′` and renormalized
  (`restrict_policyI`). As in the strict file, the flow of the next sentence uses theorem (3)'s
  frozen row, not the renormalized one — the wording finding already recorded on the row.
* **Terminating states are internal.** `IsTargetI` asks `R(x) ≠ 0 → x ∈ 𝒮 ∧ x → s_f`, which is
  the paper's "target on the terminating states"; it implies the strict `IsTarget`
  (`IsTargetI.isTarget`), so the strict vanishing/non-attainment theorems apply verbatim.
  "`R` vanishes on some terminating state" is `∃ y ∈ 𝒮, y → s_f ∧ R(y) = 0`.
* **Residual reading.** As in the strict file: the residual on a graph is taken against the flow's
  own initial flow (`graphResidual`, counting measure on `𝒮`).
* Everything `Core/FamilyUniversality.lean` discloses for the remark otherwise is inherited.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `G` finite, path-connected | ✓ `[Fintype V]`, `hpc` |
| `π_←` positive on the edges of `G` | ✓ `hB : B.PositiveOnEdges` |
| `R` a target of mass `Z > 0` on the terminating states | ✓ `IsTargetI G R`, `0 < ∑ R` |
| `R` vanishes on some terminating state | ✓ `hvan`, where used |
| an edge `s₀ → s_f` may or may not exist | ✓ both cases; `α` carries the choice |
| `ε ∈ (0, 1]` | ✓ |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph.PartialSupportClose

open Finset GFNBounds.Graph.PartialSupport

variable {V : Type*} [Fintype V] [DecidableEq V] {G : MarkedGraph V}

/-! ## Targets and the deleted edges, on the paper's terminating states -/

/-- A **target on the terminating states** (internal states with an edge to `s_f`). -/
structure IsTargetI (G : MarkedGraph V) (R : V → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ R x
  supp : ∀ ⦃x⦄, R x ≠ 0 → x ∈ G.internal ∧ G.Edge x G.snk

theorem IsTargetI.isTarget {R : V → ℝ} (h : IsTargetI G R) : IsTarget G R :=
  ⟨h.nonneg, fun _ hx => (h.supp hx).2⟩

/-- The terminating edge `y → s_f` is **deleted** from `G′`: `y` is a terminating state (internal)
where `R` vanishes. -/
def Deleted (G : MarkedGraph V) (R : V → ℝ) (y : V) : Prop := y ∈ G.internal ∧ R y = 0

/-- **`G′`** on the paper's reading: induced on `subVerts G R`, with the terminating edges
`y → s_f`, `y ∈ 𝒮`, `R(y) = 0`, deleted. An edge `s₀ → s_f` is kept. -/
def subGraphI (G : MarkedGraph V) (R : V → ℝ) : MarkedGraph {v // v ∈ subVerts G R} where
  Edge x y := G.Edge x.1 y.1 ∧ ¬ (y.1 = G.snk ∧ Deleted G R x.1)
  src := ⟨G.src, src_mem_subVerts R⟩
  snk := ⟨G.snk, snk_mem_subVerts R⟩
  src_ne_snk h := G.src_ne_snk (congrArg Subtype.val h)
  no_edge_into_src x h := G.no_edge_into_src x.1 h.1
  no_edge_out_of_snk y h := G.no_edge_out_of_snk y.1 h.1

/-- **Without an edge `s₀ → s_f`, `subGraphI` is the strict file's `subGraph`.** -/
theorem subGraphI_edge_iff_of_not_edge (hsrc : ¬ G.Edge G.src G.snk) {R : V → ℝ}
    (x y : {v // v ∈ subVerts G R}) : (subGraphI G R).Edge x y ↔ (subGraph G R).Edge x y := by
  constructor
  · rintro ⟨he, hd⟩
    refine ⟨he, fun ⟨hy, hR⟩ => hd ⟨hy, ?_, hR⟩⟩
    rw [hy] at he
    exact mem_internal_of_edge_snk hsrc he
  · rintro ⟨he, hd⟩
    exact ⟨he, fun ⟨hy, _, hR⟩ => hd ⟨hy, hR⟩⟩

theorem subGraph_edge_imp {R : V → ℝ} {x y : {v // v ∈ subVerts G R}}
    (h : (subGraph G R).Edge x y) : (subGraphI G R).Edge x y :=
  ⟨h.1, fun ⟨hy, _, hR⟩ => h.2 ⟨hy, hR⟩⟩

/-- **`G′` is again path-connected** (`rem:partial_support`), as soon as `R ≠ 0`. -/
theorem subGraphI_pathConnected (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTargetI G R)
    (hne : ∃ y, R y ≠ 0) : (subGraphI G R).PathConnected := by
  have h := subGraph_pathConnected hpc hR.isTarget hne
  intro s
  exact ⟨Relation.ReflTransGen.mono (fun _ _ => subGraph_edge_imp) (h s).1,
    Relation.ReflTransGen.mono (fun _ _ => subGraph_edge_imp) (h s).2⟩

/-- A state with a surviving terminating edge is a state of `G′`. -/
theorem mem_subVerts_of_not_deleted {R : V → ℝ} {y : V} (he : G.Edge y G.snk)
    (hd : ¬ Deleted G R y) : y ∈ subVerts G R := by
  by_cases hy : y = G.src
  · rw [hy]; exact src_mem_subVerts R
  · have hyi : y ∈ G.internal := MarkedGraph.mem_internal.2
      ⟨hy, fun h => G.no_edge_out_of_snk G.snk (h ▸ he)⟩
    have hRy : R y ≠ 0 := fun h => hd ⟨hyi, h⟩
    exact mem_subVerts.2 (Or.inr (Or.inr ⟨y, hRy, Relation.ReflTransGen.refl⟩))

/-! ## Restricting a backward policy to `G′` -/

/-- A **sink row for `G′`**: a probability on the in-neighbours of `s_f` in `G′`, positive on each
of them. -/
structure IsSinkRowI (G : MarkedGraph V) (R : V → ℝ) (q : V → ℝ) : Prop where
  nonneg : ∀ y, 0 ≤ q y
  supp : ∀ ⦃y⦄, q y ≠ 0 → G.Edge y G.snk ∧ ¬ Deleted G R y
  sum : ∑ y, q y = 1
  pos : ∀ ⦃y⦄, G.Edge y G.snk → ¬ Deleted G R y → 0 < q y

/-- **The restriction of `π_←` to `G′`**, with sink row `q`. -/
noncomputable def restrictWithI (B : BackwardPolicy G) {R : V → ℝ} (q : V → ℝ)
    (hq : IsSinkRowI G R q) : BackwardPolicy (subGraphI G R) where
  pb s s' := if s.1 = G.snk then q s'.1 else B.pb s.1 s'.1
  nonneg s s' := by
    by_cases h : s.1 = G.snk
    · simp only [h, if_true]; exact hq.nonneg _
    · simp only [h, if_false]; exact B.nonneg _ _
  row_sum s hs := by
    have hsrc : s.1 ≠ G.src := fun h => hs (Subtype.ext h)
    by_cases h : s.1 = G.snk
    · simp only [h, if_true]
      rw [sum_subtype_eq q fun v hv => ?_]
      · exact hq.sum
      · by_contra hc
        obtain ⟨he, hd⟩ := hq.supp hc
        exact hv (mem_subVerts_of_not_deleted he hd)
    · simp only [h, if_false]
      rw [sum_subtype_eq (fun v => B.pb s.1 v) fun v hv => ?_]
      · exact B.row_sum hsrc
      · by_contra hc
        exact hv (mem_subVerts_of_edge s.2 hsrc h (B.supp hsrc hc))
  supp s s' hs hne := by
    have hsrc : s.1 ≠ G.src := fun h => hs (Subtype.ext h)
    by_cases h : s.1 = G.snk
    · simp only [h, if_true] at hne
      obtain ⟨he, hd⟩ := hq.supp hne
      exact ⟨h ▸ he, fun h' => hd h'.2⟩
    · simp only [h, if_false] at hne
      exact ⟨B.supp hsrc hne, fun h' => h h'.1⟩

theorem restrictWithI_pb_of_ne_snk (B : BackwardPolicy G) {R q : V → ℝ} (hq : IsSinkRowI G R q)
    {s s' : {v // v ∈ subVerts G R}} (hs : s ≠ (subGraphI G R).snk) :
    (restrictWithI B q hq).pb s s' = B.pb s.1 s'.1 := by
  have h : s.1 ≠ G.snk := fun h => hs (Subtype.ext h)
  simp only [restrictWithI, h, if_false]

theorem restrictWithI_pb_snk (B : BackwardPolicy G) {R q : V → ℝ} (hq : IsSinkRowI G R q)
    (s' : {v // v ∈ subVerts G R}) :
    (restrictWithI B q hq).pb (subGraphI G R).snk s' = q s'.1 := by
  simp only [restrictWithI, subGraphI, if_true]

/-- The restriction is positive on every edge of `G′`. -/
theorem restrictWithI_positiveOnEdges (B : BackwardPolicy G) (hB : B.PositiveOnEdges)
    {R q : V → ℝ} (hq : IsSinkRowI G R q) : (restrictWithI B q hq).PositiveOnEdges := by
  intro s s' he
  by_cases h : s.1 = G.snk
  · simp only [restrictWithI, h, if_true]
    exact hq.pos (h ▸ he.1) (fun h' => he.2 ⟨h, h'⟩)
  · simp only [restrictWithI, h, if_false]
    exact hB he.1

/-- The normalizer of the renormalized sink row. -/
noncomputable def sinkMassI (B : BackwardPolicy G) (R : V → ℝ) : ℝ := by
  classical exact ∑ y, if Deleted G R y then 0 else B.pb G.snk y

/-- **`π_←`'s sink row, restricted to the in-neighbours of `s_f` in `G′` and renormalized.** -/
noncomputable def renormRowI (B : BackwardPolicy G) (R : V → ℝ) (y : V) : ℝ := by
  classical exact if Deleted G R y then 0 else B.pb G.snk y / sinkMassI B R

theorem sinkMassI_pos (B : BackwardPolicy G) (hB : B.PositiveOnEdges) {R : V → ℝ}
    (hR : IsTargetI G R) (hne : ∃ y, R y ≠ 0) : 0 < sinkMassI B R := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  unfold sinkMassI
  refine Finset.sum_pos' (fun y _ => ?_) ⟨y₀, mem_univ _, ?_⟩
  · split_ifs
    · exact le_rfl
    · exact B.nonneg _ _
  · rw [if_neg (fun h => hy₀ h.2)]
    exact hB (hR.supp hy₀).2

theorem isSinkRowI_renormRowI (B : BackwardPolicy G) (hB : B.PositiveOnEdges) {R : V → ℝ}
    (hR : IsTargetI G R) (hne : ∃ y, R y ≠ 0) : IsSinkRowI G R (renormRowI B R) := by
  classical
  have hZ := sinkMassI_pos B hB hR hne
  have hsnk : G.snk ≠ G.src := G.src_ne_snk.symm
  refine ⟨fun y => ?_, fun y hy => ?_, ?_, fun y he hd => ?_⟩
  · unfold renormRowI; split_ifs
    · exact le_rfl
    · exact div_nonneg (B.nonneg _ _) hZ.le
  · unfold renormRowI at hy
    by_cases h : Deleted G R y
    · rw [if_pos h] at hy; exact absurd rfl hy
    · rw [if_neg h] at hy
      exact ⟨B.supp hsnk (fun h0 => hy (by rw [h0, zero_div])), h⟩
  · unfold renormRowI
    have : ∀ y, (if Deleted G R y then (0 : ℝ) else B.pb G.snk y / sinkMassI B R)
        = (if Deleted G R y then 0 else B.pb G.snk y) / sinkMassI B R := by
      intro y; split_ifs <;> simp only [zero_div]
    simp only [this]
    rw [← Finset.sum_div]
    unfold sinkMassI at hZ ⊢
    exact div_self hZ.ne'
  · unfold renormRowI
    rw [if_neg hd]
    exact div_pos (hB he) hZ

/-- **`rem:partial_support`, the restriction claim**, on the paper's `G′`: a backward policy on
`G` positive on its edges restricts to one on `G′` positive on the edges of `G′`, with only its
sink row renormalized. -/
theorem restrict_policyI (B : BackwardPolicy G) (hB : B.PositiveOnEdges) {R : V → ℝ}
    (hR : IsTargetI G R) (hne : ∃ y, R y ≠ 0) :
    ∃ B' : BackwardPolicy (subGraphI G R), B'.PositiveOnEdges ∧
      (∀ s s', s ≠ (subGraphI G R).snk → B'.pb s s' = B.pb s.1 s'.1) ∧
      (∀ s', B'.pb (subGraphI G R).snk s' = renormRowI B R s'.1) :=
  ⟨restrictWithI B (renormRowI B R) (isSinkRowI_renormRowI B hB hR hne),
    restrictWithI_positiveOnEdges B hB _, fun _ _ hs => restrictWithI_pb_of_ne_snk B _ hs,
    fun s' => restrictWithI_pb_snk B _ s'⟩

/-! ## Claim (a): the flow of `G′`, extended by zero, matches `R` exactly on `G` -/

section Exact

variable {R : V → ℝ}

/-- **The frozen sink row** `q_α = (1−α) R/Z + α δ_{s₀}`. -/
noncomputable def frozenRow (G : MarkedGraph V) (R : V → ℝ) (α : ℝ) (y : V) : ℝ :=
  (1 - α) * (R y / ∑ z, R z) + if y = G.src then α else 0

/-- The admissible weights on `s₀`: `α ∈ [0, 1)`, positive iff `s₀ → s_f` is an edge. -/
structure IsSrcWeight (G : MarkedGraph V) (α : ℝ) : Prop where
  nonneg : 0 ≤ α
  lt_one : α < 1
  pos_of_edge : G.Edge G.src G.snk → 0 < α
  zero_of_not_edge : ¬ G.Edge G.src G.snk → α = 0

omit [Fintype V] [DecidableEq V] in
/-- Such a weight exists. -/
theorem exists_srcWeight (G : MarkedGraph V) : ∃ α, IsSrcWeight G α := by
  classical
  by_cases h : G.Edge G.src G.snk
  · exact ⟨1 / 2, ⟨by norm_num, by norm_num, fun _ => by norm_num, fun h' => absurd h h'⟩⟩
  · exact ⟨0, ⟨le_rfl, one_pos, fun h' => absurd h' h, fun _ => rfl⟩⟩

theorem frozenRow_of_ne_src {α : ℝ} {y : V} (hy : y ≠ G.src) :
    frozenRow G R α y = (1 - α) * (R y / ∑ z, R z) := by
  simp only [frozenRow, hy, if_false, add_zero]

theorem isSinkRowI_frozenRow (hR : IsTargetI G R) (hZ : 0 < ∑ y, R y) {α : ℝ}
    (hα : IsSrcWeight G α) : IsSinkRowI G R (frozenRow G R α) := by
  have h1α : 0 < 1 - α := by linarith [hα.lt_one]
  have hsrcI : G.src ∉ G.internal := fun h => (MarkedGraph.mem_internal.1 h).1 rfl
  have hRsrc : R G.src = 0 := by
    by_contra h; exact hsrcI (hR.supp h).1
  refine ⟨fun y => ?_, fun y hy => ?_, ?_, fun y he hd => ?_⟩
  · unfold frozenRow
    have := div_nonneg (hR.nonneg y) hZ.le
    have : 0 ≤ (if y = G.src then α else 0) := by split_ifs; exacts [hα.nonneg, le_rfl]
    positivity
  · by_cases hys : y = G.src
    · subst hys
      simp only [frozenRow, if_true, hRsrc, zero_div, mul_zero, zero_add] at hy
      have he : G.Edge G.src G.snk := by
        by_contra hc; exact hy (hα.zero_of_not_edge hc)
      exact ⟨he, fun h => hsrcI h.1⟩
    · rw [frozenRow_of_ne_src hys] at hy
      have hRy : R y ≠ 0 := fun h => hy (by rw [h, zero_div, mul_zero])
      exact ⟨(hR.supp hRy).2, fun h => hRy h.2⟩
  · unfold frozenRow
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, div_self hZ.ne',
      Finset.sum_ite_eq' univ G.src, if_pos (mem_univ _)]
    ring
  · by_cases hys : y = G.src
    · subst hys
      simp only [frozenRow, if_true, hRsrc, zero_div, mul_zero, zero_add]
      exact hα.pos_of_edge he
    · rw [frozenRow_of_ne_src hys]
      have hyi : y ∈ G.internal := MarkedGraph.mem_internal.2
        ⟨hys, fun h => G.no_edge_out_of_snk G.snk (h ▸ he)⟩
      have hRy : 0 < R y := (hR.nonneg y).lt_of_ne (fun h => hd ⟨hyi, h.symm⟩)
      exact mul_pos h1α (div_pos hRy hZ)

/-- **`rem:partial_support`, claim (a), on the paper's `G′`.** Let `G` be path-connected, `π_←` a
backward policy on `G` positive on its edges, `R` a target of mass `Z > 0` on the terminating
states, and `α` a source weight (`0` without an edge `s₀ → s_f`). On `G′`, the backward policy
with `π_←`'s rows and sink row `q_α` is positive on the edges of `G′`, and
`theo:universality_graphs` applies to it: with `λ′` its invariant probability and
`c = Z/((1−α)λ′(s₀))`, the element `(π̂′^{λ′}, cλ′)` lies in the frozen-backward family of `G′`,
and its edge flow extended by zero to `G` is non-negative, has terminal flow exactly `R` on every
terminating state (every internal state), and satisfies `equ:FM_const` at every internal state
of `G`. -/
theorem partial_support_exactI (hpc : G.PathConnected) (B : BackwardPolicy G)
    (hB : B.PositiveOnEdges) (hR : IsTargetI G R) (hZ : 0 < ∑ y, R y) {α : ℝ}
    (hα : IsSrcWeight G α) :
    ∃ hq : IsSinkRowI G R (frozenRow G R α),
      (restrictWithI B _ hq).PositiveOnEdges ∧ (subGraphI G R).PathConnected ∧
      (∃ lam, (restrictWithI B _ hq).IsInvProb lam) ∧
      ∀ lam : {v // v ∈ subVerts G R} → ℝ, (restrictWithI B _ hq).IsInvProb lam →
        let c := (∑ y, R y) / ((1 - α) * lam (subGraphI G R).src)
        let B' := restrictWithI B _ hq
        B'.FrozenBalance (B'.reversal lam) (fun x => c * lam x) ∧
        (∀ u v, 0 ≤ B'.reversal lam u v) ∧ (∀ u, ∑ v, B'.reversal lam u v = 1) ∧
        (∀ u v, 0 ≤ extend (B'.edgeFlow lam c) u v) ∧
        (∑ v, extend (B'.edgeFlow lam c) G.src v) = (∑ y, R y) / (1 - α) ∧
        (∀ x ∈ G.internal, extend (B'.edgeFlow lam c) x G.snk = R x) ∧
        (∀ v ∈ G.internal, fmDefectE G (extend (B'.edgeFlow lam c)) R v = 0) := by
  set Z := ∑ y, R y with hZdef
  have hne : ∃ y, R y ≠ 0 := by
    by_contra hc
    push Not at hc
    simp only [hc, Finset.sum_const_zero] at hZdef
    rw [hZdef] at hZ; exact lt_irrefl _ hZ
  have h1α : 0 < 1 - α := by linarith [hα.lt_one]
  have hq := isSinkRowI_frozenRow hR hZ hα
  refine ⟨hq, restrictWithI_positiveOnEdges B hB hq, subGraphI_pathConnected hpc hR hne,
    (restrictWithI B _ hq).exists_invProb, fun lam hlam => ?_⟩
  intro c B'
  have hpc' := subGraphI_pathConnected hpc hR hne
  have hB' : B'.PositiveOnEdges := restrictWithI_positiveOnEdges B hB hq
  have hlpos : ∀ x, 0 < lam x := fun x => hlam.pos hpc' hB' x
  have hc : 0 < c := div_pos hZ (mul_pos h1α (hlpos _))
  have hcZ : c * lam (subGraphI G R).src = Z / (1 - α) := by
    change Z / ((1 - α) * lam (subGraphI G R).src) * lam (subGraphI G R).src = Z / (1 - α)
    have hl0 := (hlpos (subGraphI G R).src).ne'
    field_simp
  have hnn : ∀ u v, 0 ≤ extend (B'.edgeFlow lam c) u v := by
    intro u v
    by_cases h : u ∈ subVerts G R ∧ v ∈ subVerts G R
    · simp only [extend, h, and_self, dif_pos]
      exact B'.edgeFlow_nonneg hlam.nonneg hc.le _ _
    · simp only [extend, h, dif_neg, not_false_eq_true, le_refl]
  have hterm : ∀ x ∈ G.internal, extend (B'.edgeFlow lam c) x G.snk = R x := by
    intro x hxi
    have hxs : x ≠ G.src := (MarkedGraph.mem_internal.1 hxi).1
    by_cases hx : x ∈ subVerts G R
    · have h1 := extend_of_mem (e' := B'.edgeFlow lam c) ⟨x, hx⟩ (subGraphI G R).snk
      have h2 := B'.termFlow_eq_target hlam hcZ ⟨x, hx⟩
      simp only [BackwardPolicy.termFlow] at h2
      change extend (B'.edgeFlow lam c) x G.snk = _ at h1
      rw [h1, h2, restrictWithI_pb_snk, frozenRow_of_ne_src hxs, ← hZdef]
      field_simp
    · rw [extend_of_not_mem_left hx]
      by_contra hc'
      exact hx (mem_subVerts.2 (Or.inr (Or.inr ⟨x, Ne.symm hc', Relation.ReflTransGen.refl⟩)))
  refine ⟨B'.frozenBalance_reversal hlpos c, B'.reversal_nonneg (fun x => (hlpos x).le),
    fun u => B'.sum_reversal hlam (hlpos u).ne', hnn, ?_, hterm, fun v hv => ?_⟩
  · have h := sum_extend_out (B'.edgeFlow lam c) (subGraphI G R).src
    change ∑ v, extend (B'.edgeFlow lam c) G.src v = _ at h
    rw [h]
    have := B'.sum_initFlow hlam c
    simp only [BackwardPolicy.initFlow] at this
    rw [this, hcZ]
  · rw [fmDefectE_eq hnn R hv, hterm v hv]
    obtain ⟨hvsrc, -⟩ := MarkedGraph.mem_internal.1 hv
    by_cases hvm : v ∈ subVerts G R
    · have hin := sum_extend_in (B'.edgeFlow lam c) ⟨v, hvm⟩
      have hout := sum_extend_out (B'.edgeFlow lam c) ⟨v, hvm⟩
      rw [B'.sum_edgeFlow_in lam c] at hin
      rw [B'.sum_edgeFlow_out hlam c] at hout
      have hs : extend (B'.edgeFlow lam c) G.snk v = 0 := by
        have h1 := extend_of_mem (e' := B'.edgeFlow lam c) (subGraphI G R).snk ⟨v, hvm⟩
        change extend (B'.edgeFlow lam c) G.snk v = _ at h1
        rw [h1]
        exact B'.edgeFlow_snk_out lam c (fun h => hvsrc (congrArg Subtype.val h))
      simp only at hin hout
      rw [hin, hout, hs]
      ring
    · have hin : ∑ u, extend (B'.edgeFlow lam c) u v = 0 :=
        Finset.sum_eq_zero fun u _ => extend_of_not_mem_right u hvm
      have hout : ∑ w, extend (B'.edgeFlow lam c) v w = 0 :=
        Finset.sum_eq_zero fun w _ => extend_of_not_mem_left hvm w
      rw [hin, hout, extend_of_not_mem_right _ hvm]
      ring

/-- **`rem:partial_support`, claim (a), "not to that of `G`"**, on the paper's `G′`: when `R`
vanishes on a terminating state, the extended flow of `partial_support_exactI` is the edge flow of
no element of the union of the frozen-backward families of `G`. -/
theorem partial_support_not_in_GI (hpc : G.PathConnected) (B : BackwardPolicy G)
    (hB : B.PositiveOnEdges) (hR : IsTargetI G R) (hZ : 0 < ∑ y, R y) {α : ℝ}
    (hα : IsSrcWeight G α) (hvan : ∃ y ∈ G.internal, G.Edge y G.snk ∧ R y = 0) :
    ∃ hq : IsSinkRowI G R (frozenRow G R α),
      ∀ lam : {v // v ∈ subVerts G R} → ℝ, (restrictWithI B _ hq).IsInvProb lam →
        ∀ θ ∈ FrozenUnion G, memberFlow θ
          ≠ extend ((restrictWithI B _ hq).edgeFlow lam
              ((∑ y, R y) / ((1 - α) * lam (subGraphI G R).src))) := by
  obtain ⟨hq, -, -, -, hall⟩ := partial_support_exactI hpc B hB hR hZ hα
  refine ⟨hq, fun lam hlam θ hθ heq => ?_⟩
  obtain ⟨-, -, -, -, hmass, hterm, -⟩ := hall lam hlam
  have h1α : 0 < 1 - α := by linarith [hα.lt_one]
  rcases member_dichotomy hpc hθ with h0 | ⟨B₁, -, -, -, hpos⟩
  · have : ∑ v, memberFlow θ G.src v = 0 := by
      simp only [memberFlow, h0, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rw [heq, hmass] at this
    exact (div_pos hZ h1α).ne' this
  · obtain ⟨y, hyi, hy, hRy⟩ := hvan
    have := hpos y hy
    rw [heq, hterm y hyi, hRy] at this
    exact lt_irrefl _ this

end Exact

/-! ## Claim (b): the full-support targets `(1−ε)R + εZ unif`, `unif` on the terminating states -/

section Union

/-- `unif`: the uniform probability on the terminating states, the internal `y` with `y → s_f`. -/
noncomputable def unifI (G : MarkedGraph V) (y : V) : ℝ := by
  classical exact
    if y ∈ G.internal ∧ G.Edge y G.snk then
      1 / ((univ.filter fun z => z ∈ G.internal ∧ G.Edge z G.snk).card : ℝ) else 0

/-- **The full-support targets** `R_ε := (1 − ε) R + ε Z unif`. -/
noncomputable def epsTargetI (G : MarkedGraph V) (R : V → ℝ) (ε : ℝ) (y : V) : ℝ :=
  (1 - ε) * R y + ε * (∑ z, R z) * unifI G y

theorem unifI_nonneg (y : V) : 0 ≤ unifI G y := by
  classical
  simp only [unifI]
  split_ifs <;> first | exact le_rfl | positivity

open Classical in
theorem card_terminating_pos {y : V} (hy : y ∈ G.internal ∧ G.Edge y G.snk) :
    0 < (univ.filter fun z => z ∈ G.internal ∧ G.Edge z G.snk).card := by
  classical
  exact Finset.card_pos.2 ⟨y, by simp only [mem_filter, mem_univ, true_and]; exact hy⟩

theorem unifI_le_one (y : V) : unifI G y ≤ 1 := by
  classical
  simp only [unifI]
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ (univ.filter fun z => z ∈ G.internal ∧ G.Edge z G.snk).card := by
      exact_mod_cast card_terminating_pos h
    rw [div_le_one (by linarith)]; exact h1
  · exact zero_le_one

theorem unifI_pos {y : V} (hy : y ∈ G.internal ∧ G.Edge y G.snk) : 0 < unifI G y := by
  classical
  have hpos := card_terminating_pos hy
  simp only [unifI, hy, and_self, if_true]
  positivity

theorem unifI_eq_zero {y : V} (hy : ¬ (y ∈ G.internal ∧ G.Edge y G.snk)) : unifI G y = 0 := by
  classical
  simp only [unifI, hy, if_false]

/-- `unif` is a probability, as soon as there is a terminating state. -/
theorem sum_unifI {y₀ : V} (hy₀ : y₀ ∈ G.internal ∧ G.Edge y₀ G.snk) : ∑ y, unifI G y = 1 := by
  classical
  have hne : ((univ.filter fun z => z ∈ G.internal ∧ G.Edge z G.snk).card : ℝ) ≠ 0 := by
    exact_mod_cast (card_terminating_pos hy₀).ne'
  simp only [unifI]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem exists_terminatingI {R : V → ℝ} (hR : IsTargetI G R) (hZ : 0 < ∑ z, R z) :
    ∃ y, y ∈ G.internal ∧ G.Edge y G.snk := by
  by_contra hc
  push Not at hc
  have : ∑ z, R z = 0 := Finset.sum_eq_zero fun z _ => by
    by_contra h; exact hc z (hR.supp h).1 (hR.supp h).2
  rw [this] at hZ; exact lt_irrefl _ hZ

/-- `R_ε` is a target on the terminating states. -/
theorem isTargetI_epsTargetI {R : V → ℝ} (hR : IsTargetI G R) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) : IsTargetI G (epsTargetI G R ε) := by
  have hZ : 0 ≤ ∑ z, R z := Finset.sum_nonneg fun z _ => hR.nonneg z
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · have := hR.nonneg y; have := unifI_nonneg (G := G) y
    have : 0 ≤ 1 - ε := by linarith
    simp only [epsTargetI]; positivity
  · by_contra hc
    apply hy
    have hRy : R y = 0 := by by_contra h; exact hc (hR.supp h)
    simp only [epsTargetI, hRy, unifI_eq_zero hc, mul_zero, add_zero]

/-- `R_ε` has full support on the terminating states, for `ε ∈ (0, 1]` and `Z > 0`. -/
theorem epsTargetI_pos {R : V → ℝ} (hR : IsTargetI G R) (hZ : 0 < ∑ z, R z) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) {y : V} (hy : y ∈ G.internal ∧ G.Edge y G.snk) :
    0 < epsTargetI G R ε y := by
  have := hR.nonneg y
  have : 0 ≤ 1 - ε := by linarith
  have h1 : 0 ≤ (1 - ε) * R y := by positivity
  have h2 : 0 < ε * (∑ z, R z) * unifI G y := by have := unifI_pos hy; positivity
  simp only [epsTargetI]; linarith

/-- `R_ε` has the mass `Z` of `R`. -/
theorem sum_epsTargetI {R : V → ℝ} (hR : IsTargetI G R) (hZ : 0 < ∑ z, R z) (ε : ℝ) :
    ∑ y, epsTargetI G R ε y = ∑ y, R y := by
  obtain ⟨y₀, hy₀⟩ := exists_terminatingI hR hZ
  simp only [epsTargetI]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_unifI hy₀]
  ring

/-- **`rem:partial_support`, claim (b), on the paper's `unif`: `R_ε` is exactly matched in the
union, within `εZ` of `R`.** For `ε ∈ (0, 1]` some element of the union of the frozen-backward
families of `G` is exactly matched to `R_ε` at every internal state, and its defect against `R` is
at most `εZ` there — with or without an edge `s₀ → s_f`. -/
theorem member_epsTargetI (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTargetI G R)
    (hZ : 0 < ∑ y, R y) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ θ ∈ FrozenUnion G,
      (∀ v ∈ G.internal, fmDefectE G (memberFlow θ) (epsTargetI G R ε) v = 0) ∧
      ∀ v ∈ G.internal, |fmDefectE G (memberFlow θ) R v| ≤ ε * ∑ y, R y := by
  set Z := ∑ y, R y with hZdef
  have hRε := isTargetI_epsTargetI hR hε0.le hε1
  have hZε : ∑ y, epsTargetI G R ε y = Z := sum_epsTargetI hR hZ ε
  obtain ⟨α, hα⟩ := exists_srcWeight G
  have h1α : 0 < 1 - α := by linarith [hα.lt_one]
  -- the sink row `q_α` of `R_ε`
  have hq := isSinkRowI_frozenRow (R := epsTargetI G R ε) hRε (by rw [hZε]; exact hZ) hα
  let q := frozenRow G (epsTargetI G R ε) α
  have hqsupp : ∀ ⦃y⦄, q y ≠ 0 → G.Edge y G.snk := fun y hy => (hq.supp hy).1
  obtain ⟨B₀, hB₀⟩ := exists_positive_policy hpc
  let B := withSinkRow B₀ q hq.nonneg hq.sum hqsupp
  have hBsnk : ∀ x, B.pb G.snk x = q x := fun x => by simp only [B, withSinkRow, if_true]
  have hB : B.PositiveOnEdges := by
    intro s s' he
    by_cases hs : s = G.snk
    · subst hs
      rw [hBsnk]
      refine hq.pos he fun ⟨hi, h0⟩ => ?_
      exact (epsTargetI_pos hR hZ hε0 hε1 ⟨hi, he⟩).ne' h0
    · simp only [B, withSinkRow, hs, if_false]; exact hB₀ he
  obtain ⟨lam, hlam⟩ := B.exists_invProb
  have hlpos : ∀ x, 0 < lam x := fun x => hlam.pos hpc hB x
  set c := Z / ((1 - α) * lam G.src) with hc
  have hc0 : 0 < c := div_pos hZ (mul_pos h1α (hlpos _))
  have hcZ : c * lam G.snk = Z / (1 - α) := by
    have hl0 := (hlpos G.src).ne'
    rw [hlam.lam_snk_eq_src, hc]; field_simp
  let θ : (V → V → ℝ) × (V → ℝ) := (B.reversal lam, fun x => c * lam x)
  have hmem : θ ∈ FrozenUnion G :=
    ⟨B, hB, fun u => B.sum_reversal hlam (hlpos u).ne',
      fun u v => B.reversal_nonneg (fun x => (hlpos x).le) u v,
      fun x => mul_nonneg hc0.le (hlpos x).le, B.frozenBalance_reversal hlpos c⟩
  have hterm : ∀ x ∈ G.internal, memberFlow θ x G.snk = epsTargetI G R ε x := by
    intro x hxi
    have hxs : x ≠ G.src := (MarkedGraph.mem_internal.1 hxi).1
    have h := B.frozenBalance_reversal hlpos c x G.snk
    simp only [memberFlow, θ]
    rw [h, B.phat_of_ne_src G.src_ne_snk.symm, hBsnk]
    show frozenRow G (epsTargetI G R ε) α x * (c * lam G.snk) = epsTargetI G R ε x
    rw [hcZ, frozenRow_of_ne_src hxs, hZε]
    field_simp
  refine ⟨θ, hmem, fun v hv => ?_, fun v hv => ?_⟩
  · rw [fmDefectE_member hmem _ hv, hterm v hv, sub_self]
  · rw [fmDefectE_member hmem _ hv, hterm v hv]
    have hRle : R v ≤ Z := Finset.single_le_sum (fun y _ => hR.nonneg y) (mem_univ v)
    have hRnn := hR.nonneg v
    have hu := unifI_nonneg (G := G) v
    have hu1 := unifI_le_one (G := G) v
    have hexp : epsTargetI G R ε v - R v = ε * (Z * unifI G v - R v) := by
      simp only [epsTargetI, hZdef]; ring
    rw [hexp, abs_mul, abs_of_pos hε0]
    have hab : |Z * unifI G v - R v| ≤ Z := by
      rw [abs_le]
      constructor
      · have : 0 ≤ Z * unifI G v := mul_nonneg hZ.le hu
        linarith
      · have : Z * unifI G v ≤ Z := by
          calc Z * unifI G v ≤ Z * 1 := by gcongr
            _ = Z := mul_one Z
        linarith
    exact mul_le_mul_of_nonneg_left hab hε0.le

section Norms

open MeasureTheory
open scoped ENNReal

variable [MeasurableSpace V] [MeasurableSingletonClass V]

omit [MeasurableSingletonClass V] in
/-- **`rem:partial_support`, claim (b), in `L^p`, on the paper's targets**: the infimum over the
union vanishes, at every `p` (the strict `iInf_graphResidual_eq_zero`, applied to `IsTargetI`). -/
theorem iInf_graphResidual_eq_zeroI (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTargetI G R)
    (hZ : 0 < ∑ y, R y) (p : ℝ≥0∞) :
    ⨅ θ ∈ FrozenUnion G, graphResidual G p (memberFlow θ) R = 0 :=
  iInf_graphResidual_eq_zero hpc hR.isTarget hZ p

/-- **`rem:partial_support`, claim (b), in `L^p`, on the paper's targets**: not attained, at any
`p ≠ 0`, when `R` vanishes on some terminating state. -/
theorem graphResidual_ne_zeroI (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTargetI G R)
    (hZ : 0 < ∑ y, R y) (hvan : ∃ y ∈ G.internal, G.Edge y G.snk ∧ R y = 0) {p : ℝ≥0∞}
    (hp : p ≠ 0) {θ : (V → V → ℝ) × (V → ℝ)} (hθ : θ ∈ FrozenUnion G) :
    graphResidual G p (memberFlow θ) R ≠ 0 := by
  have hne : ∃ x ∈ G.internal, R x ≠ 0 := by
    by_contra hc
    push Not at hc
    have : ∑ z, R z = 0 := Finset.sum_eq_zero fun z _ => by
      by_contra h; exact h (hc z (hR.supp h).1)
    rw [this] at hZ; exact lt_irrefl _ hZ
  exact graphResidual_ne_zero hpc hne hvan hp hθ

end Norms

end Union

/-! ## Inhabitation: the edge case -/

section Check

/-- The graph `s₀ = 0 → 1, 2`, `1, 2 → 3 = s_f`, **and `s₀ → s_f`**. -/
def diamondE : MarkedGraph (Fin 4) where
  Edge x y := (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3)) ∨ ((x = 1 ∨ x = 2) ∧ y = 3)
  src := 0
  snk := 3
  src_ne_snk := by decide
  no_edge_into_src x h := by
    rcases h with ⟨-, h | h | h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  no_edge_out_of_snk y h := by
    rcases h with ⟨h, -⟩ | ⟨h | h, -⟩ <;> exact absurd h (by decide)

/-- The target `δ₁`, which vanishes on the terminating state `2`. -/
noncomputable def diamondETarget : Fin 4 → ℝ := fun x => if x = 1 then 1 else 0

/-- **The edge case is inhabited** (kb 0025): `diamondE` is path-connected, has the edge
`s₀ → s_f`, `δ₁` is a target of positive mass on its terminating states vanishing on the
terminating state `2`, so the hypotheses of `partial_support_exactI` and
`partial_support_not_in_GI` hold; they are applied in `diamondE_partial_support`. -/
theorem diamondE_check :
    diamondE.PathConnected ∧ diamondE.Edge diamondE.src diamondE.snk ∧
      IsTargetI diamondE diamondETarget ∧ 0 < ∑ y, diamondETarget y ∧
      (∃ y ∈ diamondE.internal, diamondE.Edge y diamondE.snk ∧ diamondETarget y = 0) := by
  have e01 : diamondE.Edge 0 1 := Or.inl ⟨rfl, Or.inl rfl⟩
  have e02 : diamondE.Edge 0 2 := Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩
  have e03 : diamondE.Edge 0 3 := Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩
  have e13 : diamondE.Edge 1 3 := Or.inr ⟨Or.inl rfl, rfl⟩
  have e23 : diamondE.Edge 2 3 := Or.inr ⟨Or.inr rfl, rfl⟩
  have h1 : (1 : Fin 4) ∈ diamondE.internal :=
    MarkedGraph.mem_internal.2 ⟨show (1 : Fin 4) ≠ 0 by decide, show (1 : Fin 4) ≠ 3 by decide⟩
  have h2 : (2 : Fin 4) ∈ diamondE.internal :=
    MarkedGraph.mem_internal.2 ⟨show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 3 by decide⟩
  refine ⟨fun s => ?_, e03, ⟨fun x => ?_, fun x hx => ?_⟩, ?_, ⟨2, h2, e23, if_neg (by decide)⟩⟩
  · fin_cases s
    · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.single e03⟩
    · exact ⟨Relation.ReflTransGen.single e01, Relation.ReflTransGen.single e13⟩
    · exact ⟨Relation.ReflTransGen.single e02, Relation.ReflTransGen.single e23⟩
    · exact ⟨Relation.ReflTransGen.single e03, Relation.ReflTransGen.refl⟩
  · simp only [diamondETarget]; split_ifs <;> norm_num
  · have hx1 : x = 1 := by
      by_contra hc; exact hx (by simp only [diamondETarget, hc, if_false])
    subst hx1; exact ⟨h1, e13⟩
  · rw [Fin.sum_univ_four]
    unfold diamondETarget
    rw [if_neg (by decide), if_pos rfl, if_neg (by decide), if_neg (by decide)]
    norm_num

/-- On `diamondE`, with the edge `s₀ → s_f`, claim (a) on the paper's `G′` holds non-vacuously:
for some backward policy positive on the edges, the extended flow matches `δ₁` exactly on `𝒮` and is not the
edge flow of any element of the union. -/
theorem diamondE_partial_support :
    ∃ B : BackwardPolicy diamondE, B.PositiveOnEdges ∧
      ∃ α, IsSrcWeight diamondE α ∧ 0 < α ∧
      ∃ hq : IsSinkRowI diamondE diamondETarget (frozenRow diamondE diamondETarget α),
        ∃ lam, (restrictWithI B _ hq).IsInvProb lam ∧
          let c := (∑ y, diamondETarget y) / ((1 - α) * lam (subGraphI diamondE diamondETarget).src)
          (∀ v ∈ diamondE.internal,
            fmDefectE diamondE (extend ((restrictWithI B _ hq).edgeFlow lam c)) diamondETarget v
              = 0) ∧
          ∀ θ ∈ FrozenUnion diamondE,
            memberFlow θ ≠ extend ((restrictWithI B _ hq).edgeFlow lam c) := by
  obtain ⟨hpc, hedge, hR, hZ, hvan⟩ := diamondE_check
  obtain ⟨B, hB⟩ := exists_positive_policy hpc
  obtain ⟨α, hα⟩ := exists_srcWeight diamondE
  obtain ⟨hq, -, -, ⟨lam, hlam⟩, hall⟩ := partial_support_exactI hpc B hB hR hZ hα
  obtain ⟨hq', hnot⟩ := partial_support_not_in_GI hpc B hB hR hZ hα hvan
  obtain ⟨-, -, -, -, -, -, hfm⟩ := hall lam hlam
  exact ⟨B, hB, α, hα, hα.pos_of_edge hedge, hq, lam, hlam, hfm, hnot lam hlam⟩

end Check

end GFNBounds.Graph.PartialSupportClose
