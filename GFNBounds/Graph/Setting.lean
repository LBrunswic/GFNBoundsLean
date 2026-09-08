import Mathlib

/-!
# Finite marked graphs, their loop closure, and the invariant measure of the backward chain

**`def:path_connected`** — `proofs.tex:951–953`, **`def:loop_closure`** — `proofs.tex:955–957`,
and **`theo:universality_graphs`** **item (1)** — statement `proofs.tex:967–969`, proof
`proofs.tex:985`. (The bold-backtick form of each label is what
`formalization_ledger.py`'s docstring scan and `scripts/trace_check.py` read; a label mentioned
only in prose is not a claim to certify it.) The standing prose that defines *marked graph* and *backward policy* is
`proofs.tex:949` and is part of the specification.

> Throughout, a *marked graph* `G = (𝒱, ℰ)` is a finite directed graph with two distinguished
> vertices: a source `s₀` with no incoming edge and a sink `s_f` with no outgoing edge. A
> *backward policy* on `G` is a collection of probability distributions `π_←(s → ·)`, one for
> each `s ∈ 𝒱 ∖ {s₀}`, supported on the in-neighbours of `s`: `π_←(s → s') > 0` only if
> `s' → s ∈ ℰ`.

> (`def:path_connected`) A marked graph `G` is *path-connected* if for any `s ∈ 𝒱` there exists a
> path `s₀ → s₁ → ⋯ → s → ⋯ → s_f` from `s₀` to `s_f` via `s`.

> (`def:loop_closure`) The *loop closure* of a marked graph `G` is `Ĝ := (𝒱, ℰ ∪ {s_f → s₀})`. A
> backward policy `π_←` on `G` extends uniquely to a backward policy `π̂_←` on `Ĝ` by
> `π̂_←(s₀ → s_f) := 1`, the wrap edge `s_f → s₀` being the only incoming edge of `s₀` in `Ĝ`. The
> *backward chain* of `(G, π_←)` is the Markov chain on `𝒱` with kernel `π̂_←`.

> (`theo:universality_graphs`) Let `G = (𝒱, ℰ)` be a finite path-connected marked graph endowed
> with the counting measure `μ`, let `π_←` be a backward policy on `G` such that
> `π_←(s → s') > 0` for every edge `s' → s` of `G`, and let `π̂_←` be its loop closure. Fix a
> total mass `Z > 0`. Then:
> *(1)* the backward chain `π̂_←` is irreducible on `𝒱` and admits a unique invariant probability
> measure `λ`; moreover `λ > 0` everywhere and `λ(s₀) = λ(s_f)`;

and its proof, which this file follows line by line:

> *(1)* Every vertex of `Ĝ` has an incoming edge: internal vertices and `s_f` lie on
> source-to-sink paths, and the wrap edge feeds `s₀`; so `π̂_←` is a genuine Markov kernel on `𝒱`.
> For irreducibility, let `s, s' ∈ 𝒱` and choose paths `p : s₀ → ⋯ → s` and `p' : s' → ⋯ → s_f` in
> `G` (path-connectedness). The backward chain started at `s` realizes the reversal of `p` (from
> `s` down to `s₀`) with positive probability, each reversed edge carrying `π_← > 0` by
> hypothesis; it then moves `s₀ → s_f` with probability `1`, and realizes the reversal of `p'`
> (from `s_f` down to `s'`) with positive probability. Hence `s'` is accessible from `s`: the
> chain is irreducible. A finite irreducible Markov chain admits a unique invariant probability
> measure, which is everywhere positive; note that aperiodicity is not needed. Finally, the only
> backward transition into `s_f` is from `s₀` (the wrap edge is the only edge out of `s_f` in
> `Ĝ`) and it has probability `1`, so stationarity at `s_f` reads
> `λ(s_f) = λ(s₀) π̂_←(s₀ → s_f) = λ(s₀)`.

## The modelling decisions

**The edge relation is a bare `V → V → Prop`, with no decidability.** Nothing in item *(1)* ever
decides an edge: the path arguments are `Relation.ReflTransGen` and the analytic content lives in
`phat`, which is real-valued. Carrying a `DecidableRel` would be dead weight in every signature.
`DecidableEq V` *is* carried, because `phat` is defined by a case split on `s = s₀`.

**"Path" is read as "walk"** — `Relation.ReflTransGen G.Edge`, the reflexive-transitive closure of
the edge relation. `PathConnected` is `∀ s, Reach s₀ s ∧ Reach s s_f`, which is the paper's "there
exists a path from `s₀` to `s_f` via `s`" split at `s`: the two halves concatenate by
`ReflTransGen.trans` (`PathConnected.reach_src_snk`) and a walk through `s` restricts to the two
halves. The paper's proof uses only that a walk can be reversed, never that it is simple.

**The backward policy is a total function `V → V → ℝ` with the structure in hypotheses**, in the
style of `GFNBounds.Doubling.Setting`'s `pstar`: `pb s s'` is `π_←(s → s')`, non-negative
everywhere, summing to `1` at every `s ≠ s₀`, and supported on the in-neighbours of `s`. Its
values at `s₀`, where the paper leaves `π_←` undefined, are unconstrained and are *overwritten* by
the loop closure `phat`, so no downstream statement can read them. `phat` is the genuine Markov
kernel of `def:loop_closure`: `phat_row_sum` holds at **every** state, `s₀` included.

**The invariant probability is a `Prop`-valued structure `IsInvProb`, not a bundled term.** Item
*(1)* asserts existence, uniqueness, positivity and `λ(s₀) = λ(s_f)`; three of the four are
statements *about an arbitrary* invariant probability, so the predicate — not a chosen
representative — is what they quantify over.

## What was reused, and what was redone

Mathlib v4.31.0 has **no** stationary-distribution theory: `Probability/Kernel/Invariance.lean`
defines `Invariant` and reversibility and proves nothing about existence;
`Probability/Kernel/Irreducible.lean` defines `φ`-irreducibility only; there is no
Perron–Frobenius eigenvector theorem — `LinearAlgebra/Matrix/Irreducible/Defs.lean` tags itself
"perron-frobenius" but carries only `Matrix.IsIrreducible` and its path characterization
`isIrreducible_iff_exists_pow_pos`, which would mean re-presenting `phat` as a `Matrix V V ℝ` to
buy the one assertion of item *(1)* that is not the difficulty. This is `CLAUDE.md`'s obstruction
1, and the paper's citation of Levin–Peres for "a finite irreducible Markov chain admits a unique
invariant probability measure, which is everywhere positive" therefore has to be **proved
here**. It is proved by the three
elementary arguments `GFNBounds/Doubling/TruncationStat.lean` uses for the truncated doubling
chain, transplanted to a finite `V`:

* **existence** — the density action is an endomorphism of `V → ℝ` preserving total mass, so
  `densMap − id` misses the constant `1`, is not surjective, hence (finite dimension) not
  injective; a non-zero fixed vector exists, and `|·|` of it is a supersolution of equal total
  mass, hence a solution;
* **positivity** — mass travels along a positive transition, hence along a walk of the backward
  chain, and irreducibility carries it everywhere;
* **uniqueness** — the ratio maximum principle: `ν := λ − tλ'` with `t = min λ/λ'` is
  non-negative, invariant and vanishes at the minimizer, and invariance propagates the vanishing
  backwards along `Reach`.

Those three arguments could not be *imported*: every declaration in `TruncationStat.lean` is
stated over `Setting`, `St` and `pstar`, and `docs/REPO-MAP.md` lists `exists_fixed`,
`exists_stationary` and `sum_densMap` on the general-purpose shelf only because the shelf's filter
is textual — `densMap S K` hides a `Setting`. **They are general, and they are in the wrong
place**; relocating a `Doubling`-independent core of them is the master session's call, not this
file's, and until then this file carries its own copies. `Irreducible.lean`'s `Edge`/`Reach`
skeleton and `PreStat.toStat` pattern were reused as a *shape*, not as code.

## SCOPE (disclosed)

* **Only item *(1)*.** Items *(2)* (the frozen-backward family is the ray `f_out μ = cλ` with the
  `λ`-reversal as forward policy) and *(3)* (cutting the wrap edge gives an exactly flow-matching
  generative flow with `F_term = ρ`) are not stated here. The setting is built so they can be:
  `phat`, `IsInvProb` and `invProb_pos` are the three objects their statements need.
* **`Z > 0` is not carried.** The total mass of `theo:universality_graphs` enters only in items
  *(2)*–*(3)*; item *(1)* is scale-free.
* **The counting measure `μ` is not modelled.** On a finite `V` it is `Finset.univ.sum`, which is
  what every sum below is; no `MeasureTheory` layer is introduced.
* **The chain itself is not modelled.** There is no `Kernel`, no trajectory space and no
  `E(·|X₀=x)`: "irreducible" is `∀ x y, BReach x y` with `BReach` the reflexive-transitive closure
  of `0 < phat`, and "invariant probability" is `λ P̂ = λ` as a finite sum. This is the same
  route `Doubling/Irreducible.lean` and `Doubling/Kac.lean` take, and for the same reason.
* **`hatEdge` is defined and used only where the paper uses it** — to say that the extension of
  `π_←` to `Ĝ` is a backward policy (`phat_supp`), that it is unique (`src_row_unique`,
  `phat_unique_extension`), and that every vertex of `Ĝ` has an in-edge (`exists_hatEdge_into`). It is not equipped with its own
  reachability relation, `BReach` being the object the proof actually walks along.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒱` finite | ✓ carried (`[Fintype V]`); `[DecidableEq V]` added for the case split defining `phat` |
| `G` directed, `s₀` with no incoming edge, `s_f` with no outgoing edge | ✓ carried (`MarkedGraph.no_edge_into_src`, `no_edge_out_of_snk`) |
| `s₀ ≠ s_f` | ⚠ **carried as a field** (`src_ne_snk`). The paper says "two distinguished vertices", which is where it is implied; item *(1)* never uses it, and it is recorded rather than dropped |
| `G` path-connected | ✓ carried (`MarkedGraph.PathConnected`), read as walks |
| `π_←(s → ·)` a probability for each `s ≠ s₀` | ✓ carried (`BackwardPolicy.nonneg`, `row_sum`) |
| `π_←(s → s') > 0` only if `s' → s ∈ ℰ` | ✓ carried (`BackwardPolicy.supp`) |
| `π_←(s → s') > 0` for **every** edge `s' → s` | ✓ carried as a hypothesis (`PositiveOnEdges`), not a field: `def:loop_closure` and the Markov-kernel half of the proof do not need it |
| `π̂_←(s₀ → s_f) := 1` | ✓ `BackwardPolicy.phat`, by construction |
| total mass `Z > 0` | not needed by item *(1)*; see SCOPE |
| aperiodicity | ✓ not assumed, as the paper insists |

## What the paper's item (1) claims and this file delivers

| paper | here |
|---|---|
| `π̂_←` is a genuine Markov kernel on `𝒱` | `phat_nonneg`, `phat_row_sum`, `phat_supp`, `exists_hatEdge_into` |
| the extension to `Ĝ` is unique | `src_row_unique`, `phat_unique_extension` |
| the backward chain is irreducible | `breach_all` |
| an invariant probability exists | `exists_invProb` |
| it is unique | `invProb_unique` |
| it is positive everywhere | `IsInvProb.pos` |
| `λ(s₀) = λ(s_f)` | `IsInvProb.lam_snk_eq_src` |
| all four at once | `universality_graphs_one` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

/-! ### Marked graphs -/

/-- A **marked graph** `G = (𝒱, ℰ)` (`proofs.tex:949`): a directed graph on `V` with a source
`s₀` carrying no incoming edge and a sink `s_f` carrying no outgoing edge.

Finiteness of `𝒱` is *not* a field: it is the instance `[Fintype V]`, required only where a sum
over the vertices is taken. -/
structure MarkedGraph (V : Type*) where
  /-- The edge relation: `Edge x y` is the paper's `x → y ∈ ℰ`. -/
  Edge : V → V → Prop
  /-- The source `s₀`. -/
  src : V
  /-- The sink `s_f`. -/
  snk : V
  /-- The two marks are distinct. -/
  src_ne_snk : src ≠ snk
  /-- `s₀` has no incoming edge. -/
  no_edge_into_src : ∀ x, ¬ Edge x src
  /-- `s_f` has no outgoing edge. -/
  no_edge_out_of_snk : ∀ y, ¬ Edge snk y

namespace MarkedGraph

variable {V : Type*} (G : MarkedGraph V)

/-- Walks in `G`: the reflexive-transitive closure of the edge relation. The paper's *path*. -/
abbrev Reach : V → V → Prop := Relation.ReflTransGen G.Edge

/-- **`def:path_connected`** (`proofs.tex:951–953`): every vertex lies on a walk from the source
to the sink, split at that vertex. -/
def PathConnected : Prop := ∀ s : V, G.Reach G.src s ∧ G.Reach s G.snk

/-- **`def:loop_closure`** (`proofs.tex:955–957`), the graph half: the edges of
`Ĝ = (𝒱, ℰ ∪ {s_f → s₀})`. -/
def hatEdge (x y : V) : Prop := G.Edge x y ∨ (x = G.snk ∧ y = G.src)

variable {G}

/-- The wrap edge `s_f → s₀` of `Ĝ`. -/
theorem hatEdge_wrap : G.hatEdge G.snk G.src := Or.inr ⟨rfl, rfl⟩

/-- In `Ĝ` the wrap edge is the only incoming edge of `s₀`, because `s₀` had none in `G`. -/
theorem eq_snk_of_hatEdge_into_src {x : V} (h : G.hatEdge x G.src) : x = G.snk := by
  rcases h with h | ⟨h, -⟩
  · exact absurd h (G.no_edge_into_src x)
  · exact h

/-- The source half of path-connectedness. -/
theorem PathConnected.from_src (h : G.PathConnected) (s : V) : G.Reach G.src s := (h s).1

/-- The sink half of path-connectedness. -/
theorem PathConnected.to_snk (h : G.PathConnected) (s : V) : G.Reach s G.snk := (h s).2

/-- The two halves of `def:path_connected` concatenate at `s` into one walk `s₀ ⤳ s_f`, which is
the form the definition is stated in. -/
theorem PathConnected.reach_src_snk (h : G.PathConnected) (s : V) : G.Reach G.src G.snk :=
  (h.from_src s).trans (h.to_snk s)

/-- **Every vertex of `Ĝ` has an incoming edge** — the first sentence of the proof of
`theo:universality_graphs`*(1)*. Off the source this is the last edge of a walk from `s₀`; at the
source it is the wrap edge. -/
theorem exists_hatEdge_into (h : G.PathConnected) (x : V) : ∃ y, G.hatEdge y x := by
  by_cases hx : x = G.src
  · exact ⟨G.snk, hx ▸ hatEdge_wrap⟩
  · rcases Relation.ReflTransGen.cases_tail (h.from_src x) with hxs | ⟨y, -, hy⟩
    · exact absurd hxs hx
    · exact ⟨y, Or.inl hy⟩

end MarkedGraph

/-! ### Backward policies, and the loop closure of one -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **backward policy** on a marked graph (`proofs.tex:949`): probability distributions
`π_←(s → ·)` for each `s ≠ s₀`, supported on the in-neighbours of `s`.

`pb` is total, as `pstar` is in `GFNBounds.Doubling.Setting`; the paper leaves `π_←(s₀ → ·)`
undefined, and the fields say nothing about it. Nothing downstream reads it: `phat` overwrites the
source row with the point mass at `s_f`. -/
structure BackwardPolicy (G : MarkedGraph V) where
  /-- `pb s s'` is `π_←(s → s')`. -/
  pb : V → V → ℝ
  /-- `π_←` is non-negative. -/
  nonneg : ∀ s s', 0 ≤ pb s s'
  /-- `π_←(s → ·)` is a probability distribution at every `s ≠ s₀`. -/
  row_sum : ∀ ⦃s⦄, s ≠ G.src → ∑ s', pb s s' = 1
  /-- `π_←(s → s') > 0` only if `s' → s` is an edge of `G`. -/
  supp : ∀ ⦃s s'⦄, s ≠ G.src → pb s s' ≠ 0 → G.Edge s' s

namespace BackwardPolicy

variable {G : MarkedGraph V} (B : BackwardPolicy G)

/-- **`def:loop_closure`** (`proofs.tex:955–957`), the policy half: the unique extension `π̂_←` of
`π_←` to `Ĝ`, given by `π̂_←(s₀ → s_f) := 1` and `π̂_← = π_←` elsewhere.

This is the kernel of the *backward chain* of `(G, π_←)`, and it is a genuine Markov kernel on all
of `V`: see `phat_nonneg` and `phat_row_sum`. -/
noncomputable def phat : V → V → ℝ :=
  fun s s' => if s = G.src then (if s' = G.snk then 1 else 0) else B.pb s s'

@[simp] theorem phat_src_snk : B.phat G.src G.snk = 1 := by simp [phat]

theorem phat_src_of_ne {s' : V} (h : s' ≠ G.snk) : B.phat G.src s' = 0 := by simp [phat, h]

theorem phat_of_ne_src {s s' : V} (h : s ≠ G.src) : B.phat s s' = B.pb s s' := by simp [phat, h]

/-- `π̂_←` is non-negative. -/
theorem phat_nonneg (s s' : V) : 0 ≤ B.phat s s' := by
  by_cases h : s = G.src
  · subst h
    by_cases h' : s' = G.snk
    · subst h'; rw [B.phat_src_snk]; norm_num
    · rw [B.phat_src_of_ne h']
  · rw [B.phat_of_ne_src h]; exact B.nonneg s s'

/-- **`π̂_←` is a genuine Markov kernel on `𝒱`**: its rows sum to `1` at *every* state, the source
included, where the wrap edge carries the whole mass. -/
theorem phat_row_sum (s : V) : ∑ s', B.phat s s' = 1 := by
  by_cases h : s = G.src
  · subst h
    have hsingle : ∑ s', B.phat G.src s' = B.phat G.src G.snk :=
      Finset.sum_eq_single G.snk (fun b _ hb => B.phat_src_of_ne hb)
        (fun hn => absurd (Finset.mem_univ G.snk) hn)
    rw [hsingle, B.phat_src_snk]
  · simp only [B.phat_of_ne_src h]
    exact B.row_sum h

/-- `π̂_←` is a backward policy on `Ĝ`: it is supported on the in-neighbours of `s` in `Ĝ`. -/
theorem phat_supp {s s' : V} (h : B.phat s s' ≠ 0) : G.hatEdge s' s := by
  by_cases hs : s = G.src
  · subst hs
    by_cases hs' : s' = G.snk
    · subst hs'; exact MarkedGraph.hatEdge_wrap
    · exact absurd (B.phat_src_of_ne hs') h
  · exact Or.inl (B.supp hs (by rwa [B.phat_of_ne_src hs] at h))

/-- **`def:loop_closure`, the source row.** A row summing to `1` and supported on the
in-neighbours of `s₀` in `Ĝ` is the point mass at `s_f`, the wrap edge being the only one.

The policy plays no part — this is a statement about `Ĝ` alone — and non-negativity, which the
paper's "probability distribution" carries, is not used either: the support condition kills every
entry off `s_f` and the total mass fixes the one that is left. Both are strengthenings in the safe
direction; the paper's statement is the case `q ≥ 0`. -/
theorem src_row_unique (q : V → ℝ) (htot : ∑ s', q s' = 1)
    (hsupp : ∀ s', q s' ≠ 0 → G.hatEdge s' G.src) :
    q = fun s' => if s' = G.snk then 1 else 0 := by
  have hoff : ∀ s', s' ≠ G.snk → q s' = 0 := by
    intro s' hs'
    by_contra hc
    exact hs' (MarkedGraph.eq_snk_of_hatEdge_into_src (hsupp s' hc))
  have hsingle : ∑ s', q s' = q G.snk :=
    Finset.sum_eq_single G.snk (fun b _ hb => hoff b hb)
      (fun hn => absurd (Finset.mem_univ G.snk) hn)
  rw [hsingle] at htot
  funext s'
  by_cases hs' : s' = G.snk
  · subst hs'; simpa using htot
  · rw [hoff s' hs']; simp [hs']

/-- **`def:loop_closure`: the extension is unique.** A backward policy `Q` on `Ĝ` — rows summing
to `1`, supported on the in-neighbours in `Ĝ` — that agrees with `π_←` at every state other than
`s₀` is `π̂_←`. This is the definition's "extends uniquely", in full: `phat` is not merely *an*
extension but the only one. -/
theorem phat_unique_extension (Q : V → V → ℝ) (hrow : ∀ s, ∑ s', Q s s' = 1)
    (hsupp : ∀ s s', Q s s' ≠ 0 → G.hatEdge s' s) (hoff : ∀ ⦃s⦄, s ≠ G.src → Q s = B.pb s) :
    Q = B.phat := by
  funext s s'
  by_cases hs : s = G.src
  · subst hs
    rw [congrFun (src_row_unique (Q G.src) (hrow G.src) (fun t ht => hsupp G.src t ht)) s']
    by_cases hs' : s' = G.snk
    · subst hs'; rw [B.phat_src_snk]; simp
    · rw [B.phat_src_of_ne hs']; simp [hs']
  · rw [B.phat_of_ne_src hs, hoff hs]

/-- The hypothesis of `theo:universality_graphs`: `π_←(s → s') > 0` for **every** edge `s' → s`
of `G`. Carried as a hypothesis rather than a field of `BackwardPolicy`, since neither
`def:loop_closure` nor the Markov-kernel half of the proof uses it. -/
def PositiveOnEdges : Prop := ∀ ⦃s s'⦄, G.Edge s' s → 0 < B.pb s s'

/-- Reversing an edge of `G` gives a positive transition of the backward chain. -/
theorem phat_pos_of_edge (hpos : B.PositiveOnEdges) {x y : V} (h : G.Edge x y) :
    0 < B.phat y x := by
  have hy : y ≠ G.src := by rintro rfl; exact G.no_edge_into_src x h
  rw [B.phat_of_ne_src hy]
  exact hpos h

/-! ### Irreducibility of the backward chain -/

/-- A positive one-step transition of the backward chain. -/
def BStep (x y : V) : Prop := 0 < B.phat x y

/-- Accessibility in the backward chain: the reflexive-transitive closure of `BStep`. -/
abbrev BReach : V → V → Prop := Relation.ReflTransGen B.BStep

theorem bstep_wrap : B.BStep G.src G.snk := by
  show (0 : ℝ) < B.phat G.src G.snk
  rw [B.phat_src_snk]; norm_num

theorem bstep_of_edge (hpos : B.PositiveOnEdges) {x y : V} (h : G.Edge x y) : B.BStep y x :=
  B.phat_pos_of_edge hpos h

/-- **The backward chain reverses walks of `G`**, each reversed edge carrying `π_← > 0`. -/
theorem breach_of_reach (hpos : B.PositiveOnEdges) {a b : V} (h : G.Reach a b) :
    B.BReach b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (B.bstep_of_edge hpos hstep) ih

/-- **`theo:universality_graphs`*(1)*, irreducibility.** From `s`, reverse a walk `s₀ ⤳ s` down to
`s₀`, take the wrap edge to `s_f`, then reverse a walk `s' ⤳ s_f` down to `s'`. -/
theorem breach_all (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (x y : V) :
    B.BReach x y :=
  ((B.breach_of_reach hpos (hpc.from_src x)).tail B.bstep_wrap).trans
    (B.breach_of_reach hpos (hpc.to_snk y))

/-! ### The invariant probability -/

/-- An **invariant probability** of the backward chain: `λ ≥ 0`, `λ(𝒱) = 1` and `λ π̂_← = λ`.

The counting measure of `theo:universality_graphs` is `Finset.univ.sum`; no measure-theoretic
layer is introduced. -/
structure IsInvProb (lam : V → ℝ) : Prop where
  /-- `λ ≥ 0`. -/
  nonneg : ∀ x, 0 ≤ lam x
  /-- `λ` is a probability. -/
  total : ∑ x, lam x = 1
  /-- `λ π̂_← = λ`. -/
  inv : ∀ y, ∑ x, lam x * B.phat x y = lam y

/-- The density action `l ↦ l π̂_←` on measures, a linear endomorphism of the finite-dimensional
space `V → ℝ`. -/
noncomputable def densMap : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun l := fun y => ∑ x, l x * B.phat x y
  map_add' l l' := by
    funext y; simp only [Pi.add_apply, add_mul]; exact Finset.sum_add_distrib
  map_smul' c l := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem densMap_apply (l : V → ℝ) (y : V) : B.densMap l y = ∑ x, l x * B.phat x y := rfl

/-- The density action preserves total mass: the rows of `π̂_←` sum to `1`. -/
theorem sum_densMap (l : V → ℝ) : ∑ y, B.densMap l y = ∑ x, l x := by
  simp only [densMap_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, B.phat_row_sum, mul_one]

/-- `densMap − id` is not injective: its range lies in the mass-zero hyperplane, so it misses the
constant `1` and is not surjective, and `V → ℝ` is finite-dimensional. -/
theorem exists_fixed : ∃ l : V → ℝ, l ≠ 0 ∧ B.densMap l = l := by
  classical
  set g : (V → ℝ) →ₗ[ℝ] (V → ℝ) := B.densMap - LinearMap.id with hg
  have hns : ¬ Function.Surjective g := by
    intro hsurj
    obtain ⟨l, hl⟩ := hsurj (fun _ => (1 : ℝ))
    have hpt : ∀ y, g l y = B.densMap l y - l y := fun _ => rfl
    have h0 : ∑ y, g l y = 0 := by
      simp only [hpt, Finset.sum_sub_distrib, B.sum_densMap, sub_self]
    rw [hl] at h0
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h0
    have hcard : 0 < (Finset.univ : Finset V).card :=
      Finset.card_pos.mpr ⟨G.src, Finset.mem_univ _⟩
    have hR : (0 : ℝ) < (Finset.univ : Finset V).card := by exact_mod_cast hcard
    rw [h0] at hR
    exact lt_irrefl _ hR
  have hni : ¬ Function.Injective g := fun h => hns (LinearMap.injective_iff_surjective.mp h)
  have hker : LinearMap.ker g ≠ ⊥ := fun h => hni (LinearMap.ker_eq_bot.mp h)
  obtain ⟨l, hlmem, hlne⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨l, hlne, ?_⟩
  have hz : B.densMap l - l = 0 := hlmem
  funext y
  have hy := congrFun hz y
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hy
  exact hy

/-- **`theo:universality_graphs`*(1)*, existence.** `|l|` of a non-zero fixed vector is a
supersolution of the same total mass, hence a solution; normalizing gives a probability. -/
theorem exists_invProb : ∃ lam : V → ℝ, B.IsInvProb lam := by
  classical
  obtain ⟨l, hlne, hlfix⟩ := B.exists_fixed
  set m : V → ℝ := fun y => |l y| with hm
  have hmnn : ∀ y, 0 ≤ m y := fun y => abs_nonneg _
  have hsuper : ∀ y, m y ≤ B.densMap m y := by
    intro y
    have h1 : m y = |B.densMap l y| := by rw [hlfix]
    rw [h1, densMap_apply, densMap_apply]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_mul, abs_of_nonneg (B.phat_nonneg x y)]
  have hsum : ∑ y, m y = ∑ y, B.densMap m y := (B.sum_densMap m).symm
  have hfix : ∀ y, m y = B.densMap m y :=
    fun y => (Finset.sum_eq_sum_iff_of_le (fun i _ => hsuper i)).mp hsum y (Finset.mem_univ y)
  have hZpos : 0 < ∑ y, m y := by
    obtain ⟨y0, hy0⟩ : ∃ y0, l y0 ≠ 0 := by
      by_contra hc
      exact hlne (funext fun y => by simpa using not_not.mp (not_exists.mp hc y))
    exact Finset.sum_pos' (fun i _ => hmnn i) ⟨y0, Finset.mem_univ _, abs_pos.mpr hy0⟩
  refine ⟨fun y => m y / (∑ z, m z), ?_, ?_, ?_⟩
  · exact fun y => div_nonneg (hmnn y) hZpos.le
  · rw [← Finset.sum_div, div_self (ne_of_gt hZpos)]
  · intro y
    have hrw : ∀ x : V, m x / (∑ z, m z) * B.phat x y
        = (∑ z, m z)⁻¹ * (m x * B.phat x y) := by
      intro x; rw [div_eq_inv_mul]; ring
    rw [Finset.sum_congr rfl (fun x _ => hrw x), ← Finset.mul_sum, ← densMap_apply, ← hfix y,
      div_eq_inv_mul]

/-! ### Positivity, uniqueness, and the two marks -/

variable {B}

/-- Mass travels along a positive transition of the backward chain. -/
theorem IsInvProb.pos_of_bstep {lam : V → ℝ} (h : B.IsInvProb lam) {x y : V}
    (hs : B.BStep x y) (hx : 0 < lam x) : 0 < lam y := by
  have hs' : 0 < B.phat x y := hs
  have hle : lam x * B.phat x y ≤ ∑ z, lam z * B.phat z y :=
    Finset.single_le_sum (f := fun z => lam z * B.phat z y)
      (fun z _ => mul_nonneg (h.nonneg z) (B.phat_nonneg z y)) (Finset.mem_univ x)
  rw [h.inv y] at hle
  exact lt_of_lt_of_le (mul_pos hx hs') hle

/-- Mass travels along a walk of the backward chain. -/
theorem IsInvProb.pos_of_breach {lam : V → ℝ} (h : B.IsInvProb lam) {x y : V}
    (hr : B.BReach x y) (hx : 0 < lam x) : 0 < lam y := by
  induction hr with
  | refl => exact hx
  | tail _ hstep ih => exact h.pos_of_bstep hstep ih

/-- A probability charges some state. -/
theorem IsInvProb.exists_pos {lam : V → ℝ} (h : B.IsInvProb lam) : ∃ x, 0 < lam x := by
  by_contra hc
  have hz : ∀ x, lam x = 0 := by
    intro x
    rcases lt_or_eq_of_le (h.nonneg x) with hlt | heq
    · exact absurd ⟨x, hlt⟩ hc
    · exact heq.symm
  have h1 : ∑ x, lam x = 0 := by simp [hz]
  rw [h.total] at h1
  exact one_ne_zero h1

/-- **`theo:universality_graphs`*(1)*, positivity.** An invariant probability of an irreducible
chain is positive at every state. -/
theorem IsInvProb.pos (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (h : B.IsInvProb lam) (y : V) : 0 < lam y := by
  obtain ⟨x, hx⟩ := h.exists_pos
  exact h.pos_of_breach (B.breach_all hpc hpos x y) hx

/-- A non-negative invariant vector that vanishes at `x₀` vanishes at every state that reaches
`x₀`: invariance at a state where it vanishes forces it to vanish at every state carrying a
positive transition into that state. -/
theorem eq_zero_of_breach {nu : V → ℝ} (hnn : ∀ x, 0 ≤ nu x)
    (hinv : ∀ y, ∑ x, nu x * B.phat x y = nu y) {x0 : V} (h0 : nu x0 = 0) {x : V}
    (hr : B.BReach x x0) : nu x = 0 := by
  have hstep : ∀ {a c : V}, B.BStep a c → nu c = 0 → nu a = 0 := by
    intro a c hac hcz
    have hsum := hinv c
    rw [hcz] at hsum
    have hle : nu a * B.phat a c ≤ 0 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun z => nu z * B.phat z c)
        (fun z _ => mul_nonneg (hnn z) (B.phat_nonneg z c)) (Finset.mem_univ a)
    have hge : 0 ≤ nu a * B.phat a c := mul_nonneg (hnn a) (B.phat_nonneg a c)
    rcases mul_eq_zero.mp (le_antisymm hle hge) with hh | hh
    · exact hh
    · exact absurd hh (ne_of_gt (show (0 : ℝ) < B.phat a c from hac))
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact h0
  | head h' _ ih => exact hstep h' ih

/-- **`theo:universality_graphs`*(1)*, uniqueness.** The ratio maximum principle: if `λ` and `λ'`
are invariant probabilities and `t` minimizes `λ/λ'`, then `ν = λ − tλ'` is non-negative,
invariant and vanishes at the minimizer, hence everywhere; both being probabilities gives
`t = 1`. -/
theorem invProb_unique (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam lam' : V → ℝ}
    (h : B.IsInvProb lam) (h' : B.IsInvProb lam') : lam = lam' := by
  classical
  have hp' : ∀ x, 0 < lam' x := fun x => h'.pos hpc hpos x
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
    eq_zero_of_breach hnn hinv h0 (B.breach_all hpc hpos x x0)
  have ht1 : t = 1 := by
    have h1 : ∑ x, lam x = ∑ x, t * lam' x :=
      Finset.sum_congr rfl fun x _ => by have := hall x; linarith
    rw [h.total, ← Finset.mul_sum, h'.total, mul_one] at h1
    exact h1.symm
  funext x
  have := hall x
  rw [ht1, one_mul] at this
  linarith

/-- **`theo:universality_graphs`*(1)*, `λ(s₀) = λ(s_f)`.** The wrap edge is the only edge out of
`s_f` in `Ĝ`, so the only backward transition into `s_f` is from `s₀`, and it has probability `1`:
stationarity at `s_f` reads `λ(s_f) = λ(s₀) π̂_←(s₀ → s_f) = λ(s₀)`. -/
theorem IsInvProb.lam_snk_eq_src {lam : V → ℝ} (h : B.IsInvProb lam) :
    lam G.snk = lam G.src := by
  have h1 := h.inv G.snk
  have hoff : ∀ x ∈ (Finset.univ : Finset V), x ≠ G.src → lam x * B.phat x G.snk = 0 := by
    intro x _ hx
    have hzero : B.phat x G.snk = 0 := by
      rw [B.phat_of_ne_src hx]
      by_contra hc
      exact G.no_edge_out_of_snk x (B.supp hx hc)
    rw [hzero, mul_zero]
  rw [Finset.sum_eq_single G.src hoff (fun hn => absurd (Finset.mem_univ G.src) hn),
    B.phat_src_snk, mul_one] at h1
  exact h1.symm

/-! ### Item (1) of `theo:universality_graphs`, in one statement -/

variable (B)

/-- **`theo:universality_graphs`*(1)*** (`proofs.tex:967–969`, proof `proofs.tex:985`).

On a finite path-connected marked graph with a backward policy positive on every edge, the
backward chain of the loop closure is irreducible and admits a unique invariant probability `λ`;
moreover `λ > 0` everywhere and `λ(s₀) = λ(s_f)`.

The four conjuncts are the paper's four assertions, in its order. `Z > 0` and the counting measure
`μ` play no part in item *(1)*; see the module SCOPE. -/
theorem universality_graphs_one (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) :
    (∀ x y : V, B.BReach x y) ∧
      (∃ lam : V → ℝ, B.IsInvProb lam) ∧
      (∀ lam lam' : V → ℝ, B.IsInvProb lam → B.IsInvProb lam' → lam = lam') ∧
      (∀ lam : V → ℝ, B.IsInvProb lam →
        (∀ x, 0 < lam x) ∧ lam G.snk = lam G.src) :=
  ⟨B.breach_all hpc hpos, B.exists_invProb,
    fun _ _ h h' => invProb_unique hpc hpos h h',
    fun _ h => ⟨fun x => h.pos hpc hpos x, h.lam_snk_eq_src⟩⟩

end BackwardPolicy

end GFNBounds.Graph
