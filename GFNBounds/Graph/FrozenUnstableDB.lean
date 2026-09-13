import GFNBounds.Graph.FrozenUnstable
import GFNBounds.Balance.Lift

/-!
# Freezing the backward policy does not restore stability of the detailed-balance loss either

**`prop:frozen_unstable_full`** — statement `proofs.tex:680–690`, proof `proofs.tex:692–704`;
this file certifies the **DB half** (the paper's *The DB case* paragraph, `proofs.tex:701`) and the
closing claim that both losses are unstable *in the sense of* `eq:def_stability`
(`cv_divergence.tex:183–185`), which it states as a formal predicate `Stable`. The FM half is
`GFNBounds.Graph.BackwardPolicy.frozen_unstable_full_fm`, imported and not restated.

The stability being negated, `eq:def_stability`, with the sentence that introduces it:

> […] `brunswic2024theory`, whose Definition 3 calls a loss *stable* when adding a `0`-flow never
> decreases it, `𝓛(F + F₀) ≥ 𝓛(F)` for every `0`-flow `F₀` that is a subflow of `F`.

The proposition's conclusion and the proof paragraph this file consumes:

> Then for every training measure `ν` of positive density and every
> `0 < ε ≤ ½ min_{(u→v)∈γ} F*(u→v)`, the edgeflow `F := F* − ε1_γ` and the `0`-flow
> `F₀ := ε1_γ` satisfy `0 ≤ F₀ ≤ F` and `𝓛_{g,ν}(F + F₀) = 0 < 𝓛_{g,ν}(F)`. Hence the FM and DB
> losses with frozen backward policy remain *unstable* in the sense of `eq:def_stability`, on
> every such graph and for every such generator and training measure.

> *The DB case.* Read on edge flows, the DB loss vanishes iff every edge satisfies
> `F(u→v) = μ_F(v) π̂_←(v→u)` (Proposition `prop:db_lift`). At `F + F₀ = F*` this holds by
> construction, so the DB loss is `0` there. At `F` it fails on a set of positive `ν̂`-measure:
> edge-level balance would give, summing over `v` at each `u` (`F` being conservative, its
> outflow equals its inflow `μ_F`), `μ_F π̂_← = μ_F`, contradicting the previous paragraph — and
> `g > 0` off `1` turns the failure into a positive DB loss. The same pair `(F, F₀)` therefore
> witnesses DB instability.

The words *flow*, *`0`-flow* and *subflow* are not defined in the paper; they are those of the
source `eq:def_stability` cites, `brunswic2024theory` (arXiv 2312.15246, §2), on a graph with
states `𝒮 = 𝒮* ∪ {s₀, s_f}`:

> An edgeflow on `G` is an assignment `F` of a non-negative value on each edge,
> `∀ s → s′, F(s → s′) ≥ 0`. **Definition 1.** A flow is an edgeflow `F` satisfying the so-called
> flow-matching constraint (1) [`∀ s ∈ 𝒮*, ∑_{s′} F(s′ → s) = ∑_{s′} F(s → s′)`]. Given a reward
> `R : 𝒮* → ℝ₊`, an edgeflow is a `R`-edgeflow if it satisfies the reward constraint (2)
> [`∀ s ∈ 𝒮*, F(s → s_f) = R(s)`]. […] **Definition 2.** A `0`-flow is a flow satisfying the
> reward constraint (2) for the null reward `R = 0`. […] define an edgeflow `F₀` as a subflow of
> an edgeflow `F` with `F₀ ≤ F` as functions defined on edges. **Definition 3 (Stability).** A loss
> `L` acting on families of flows `(F₁, ⋯, F_p)` is stable if adding a `0`-flow does not decrease
> the loss. More formally: if for any `0`-flow `F₀`, `L(F₁ + F₀, ⋯, F_p + F₀) ≥ L(F₁, ⋯, F_p)`,
> for all `0`-flow `F₀` which is a subflow of each `F_i`.

## The modelling decisions

**The DB loss is `prop:db_lift`'s left-hand side, on the loop closure.** An edgeflow `F` is read
as a measure on `𝒮²` (`F u v` the mass of `u → v`), and
`dbLoss g ν̂ F := ∑_{u,v} ν̂(u,v) g((F K₂)(u,v) / F(u,v))` with `K₂` the edge lift of `π̂_←`
(`Balance.pushEdge`). `dbLoss_eq_edgeRatio` is `Balance.db_lift_loss` read here: the same sum
with the detailed-balance edge ratio `F(v) π̂_←(v→u) / (F(u) π_→^F(u→v))`, `F(·)` the first
marginal and `π_→^F` the disintegration. `(F K₂)(u,v) = π̂_←(v→u) · ∑_w F(v→w)` carries the
**outflow** at `v` where the paper's sentence writes the inflow `μ_F(v)`; the two agree for a
conservative `F`, which is the only case the proof uses, and the proof below passes between them
through `isCirculation_perturbedFlow`.

**`eq:def_stability` as a predicate, with the source's Definitions 1–3 transported to `Ĝ`.**
The paper's flows live on the loop closure `Ĝ` (`F*` charges the wrap edge `s_f → s₀`), while
the source's live on `G`. The transport is the loop closure itself: a flow `F` of `G` in the sense
of Definition 1 becomes the edgeflow of `Ĝ` carrying `F_in(s_f)` on the wrap edge. Since `G` has
no edge into `s₀` and none out of `s_f`, flow matching on `𝒮*` gives `F_out(s₀) = F_in(s_f)` by
summing (1) over `𝒮*`, so this edgeflow is conserved at `s₀` and `s_f` too; conversely a
conservative edgeflow of `Ĝ` restricts to a flow of `G`. Hence:
* *edgeflow* (`IsEdgeflow`): `F : V → V → ℝ` with `F ≥ 0` and `F = 0` off the edges of `Ĝ`;
* *flow*, Definition 1 (`IsFlow`): an edgeflow that is a circulation (`IsCirculation`);
* *`0`-flow*, Definition 2 (`IsZeroFlow`): a flow with zero inflow at `s_f`, the reward constraint
  (2) at `R = 0`;
* *subflow*, before Definition 3: `F₀ ≤ F` edgewise (`F₀ ≥ 0` is part of `F₀` being a flow);
* *stable*, Definition 3 read at `p = 1` as `eq:def_stability` states it (`Stable`): for every flow
  `F` and every `0`-flow `F₀` that is a subflow of `F`, `𝓛(F) ≤ 𝓛(F + F₀)`.

## What is proved

| | |
|---|---|
| `IsEdgeflow`, `IsFlow`, `IsZeroFlow`, `Stable` | the source's edgeflow and Definitions 1–3, on `Ĝ`; `Stable` is `eq:def_stability`, its `0`-flows narrowed at a possible edge `s₀ → s_f` (safe for `¬ Stable`, see SCOPE) |
| `not_stable_of_witness` | a pair `(F, F₀)` with `𝓛(F + F₀) < 𝓛(F)` refutes `Stable` |
| `edgeFlow_one_eq_edgeMeasure` | `F* = λ₂`: the balanced edgeflow is the edge measure of `Balance.Lift` |
| `phat_pos_of_hatEdge`, `phat_eq_zero_of_not_hatEdge` | `π̂_←(v→u) > 0` on the edges of `Ĝ`, `= 0` off them |
| `edgeMeasure_pos_iff_hatEdge` | `λ₂ > 0` exactly on the edges of `Ĝ` — the support `ν̂` is asked to have |
| `circ_eq_zero_of_not_hatEdge` | an admissible `ε > 0` forces `1_γ` onto the edges of `Ĝ` |
| `perturbedFlow_pos_of_hatEdge`, `perturbedFlow_eq_zero_of_not_hatEdge` | `F > 0` on the edges of `Ĝ`, `F = 0` off them |
| `perturbedFlow_isEdgeflow`, `perturbedFlow_isFlow`, `epsCirc_isZeroFlow` | *Admissibility*: "`F` is a flow and `F₀` is a `0`-subflow of it" |
| `invariant_edgeInflow_of_pushEdge_eq` | edge-level balance of a circulation makes its inflow `π̂_←`-invariant — "summing over `v` at each `u`" |
| `pushEdge_perturbedFlow_ne` | `F K₂ ≠ F`: edge-level balance fails at `F` |
| `dbLoss`, `dbLoss_eq_edgeRatio` | the DB loss, and its identity with the edge-ratio form (`prop:db_lift`) |
| `dbLoss_eq_zero_of`, `dbLoss_pos_of` | `g(1) = 0` at balance; `g > 0` off `1` at a single unbalanced edge |
| `dbLoss_sub_eq_of_support` | between two edgeflows of `Ĝ`, the DB loss difference sees `ν̂` only on the edges |
| `dbRatio_edgeFlow_eq_one`, `dbRatio_perturbedFlow_pos` | the ratio is `1` at `F*` and positive at `F`, on every edge of `Ĝ` |
| `frozen_unstable_full_db` | **the DB half**, in the four-part form of `frozen_unstable_full_fm` |
| `frozen_not_stable_fm`, `frozen_not_stable_db` | "**Hence** the FM and DB losses […] remain unstable in the sense of `eq:def_stability`" |

## SCOPE (disclosed)

* **`ν̂` has positive density against `λ₂`.** The paper names no hypothesis on the DB training
  measure `ν̂` in this proposition; its "training measure `ν` of positive density" is a measure on
  states, and the DB loss `∫ g(d(FK₂)/dF) dν̂` of `prop:db_lift` lives on `𝒮²`, where the
  reference measure is the edge measure `λ₂(u,v) = π̂_←(v→u) λ(v)`. `λ₂` is positive **exactly**
  on the edges of `Ĝ` (`edgeMeasure_pos_iff_hatEdge`), so "`ν̂` of positive density against `λ₂`"
  is `hnupos : ν̂ > 0` on the edges of `Ĝ` together with `hnu0 : ν̂ = 0` off them. The two are
  consumed differently:
  - `hnupos` is what makes the failure of balance at `F` cost something (`dbLoss_pos_of`).
  - `hnu0` is used **only** for the `= 0` conjunct of `frozen_unstable_full_db`. Off the edges
    both `FK₂` and `F` vanish, the ratio is Lean's `0/0 = 0`, and `g(0)` is unconstrained (`g > 0`
    is only asked on `ℝ_{>0}`), so a `ν̂` charging a non-edge adds the constant `ν̂ · g(0)` to the
    loss of every edgeflow of `Ĝ`. That constant cancels in `𝓛(F + F₀) < 𝓛(F)`
    (`dbLoss_sub_eq_of_support`), so **`frozen_not_stable_db` does not carry `hnu0`**.
* **Transport of the source's definitions to `Ĝ`**, as in the modelling decisions. Two points
  where the Lean predicate and a literal reading of the source could differ, both in the safe
  direction for the negations proved here:
  - The source's reward constraint (2) is quantified over `s ∈ 𝒮*`, so a literal `0`-flow may
    charge an edge `s₀ → s_f` if `G` has one; `IsZeroFlow` asks zero inflow at `s_f` from every
    vertex. That narrows the `0`-flows `Stable` quantifies over, so `Stable` is implied by the
    source's stability, and `¬ Stable` implies the source's instability.
  - Definition 3 is for families `(F₁, ⋯, F_p)`; `eq:def_stability` states `p = 1`, and so does
    `Stable`.
* **Continuity of `g` is not carried**, exactly as in the FM half: only `g(1) = 0` and `g > 0`
  on `ℝ_{>0} ∖ {1}` enter.
* **`1_γ` is a `MarkedCirculation`**, as in the FM half (a strengthening, disclosed there). The
  two `¬ Stable` theorems, which quantify no `ε`, also ask that `1_γ` ride on the edges of `Ĝ`
  (`hsupp`), which is what makes an admissible `ε` exist (`exists_admissibleEps`); every directed
  cycle of `𝒢` satisfies it. They take `λ` from `exists_invProb` rather than as a hypothesis,
  since neither loss depends on `λ`.
* **The loss is a definition, not derived** from `brunswic2024theory`; its tie to the paper's DB
  ratio is `prop:db_lift`, which is `Balance.db_lift_loss`, reused.
* **No `sorry`.**

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒢` a finite path-connected marked graph | ✓ `[Fintype V] [DecidableEq V]`, `hpc : G.PathConnected` |
| a directed cycle `γ` disjoint from `{s₀, s_f}` | ⚠ **strengthened statement** (weaker hypothesis): `γ : MarkedCirculation G`, as in the FM half; `hsupp` (on `Ĝ`'s edges) added only where no `ε` is given |
| `π̂_←` everywhere positive, frozen, on the loop closure | ✓ `B : BackwardPolicy G`, `hbpos : B.PositiveOnEdges`, `B.phat` |
| `λ` the associated balanced flow | ✓ `h : B.IsInvProb lam` in `frozen_unstable_full_db`; obtained by `exists_invProb` in the `¬ Stable` theorems |
| `g` continuous | ✗ **not carried** — unused |
| `g(1) = 0`, `g > 0` elsewhere | ✓ `hg1`, `hgpos` on `ℝ_{>0}` |
| training measure of positive density (FM) | ✓ `hnu : ∀ x, 0 < nu x` |
| training measure `ν̂` for DB | ⚠ **made explicit**: positive density against `λ₂`, i.e. `hnupos` and `hnu0`; `frozen_not_stable_db` needs only `hnupos`. See SCOPE |
| `0 < ε ≤ ½ min_γ F*` | ✓ `heps`, `hadm : B.AdmissibleEps lam eps γ.circ`, as in the FM half |
| `eq:def_stability`, via the source's Definitions 1–3 | ✓ `Stable`, `IsFlow`, `IsZeroFlow`, transported to `Ĝ`; `0`-flows narrowed at a possible edge `s₀ → s_f`, the safe direction. See SCOPE |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

variable {V : Type*} [Fintype V]

/-! ### `eq:def_stability`, through Definitions 1–3 of `brunswic2024theory` -/

/-- **An edgeflow of the loop closure `Ĝ`** (`brunswic2024theory` §2: "an assignment `F` of a
non-negative value on each edge"): `F ≥ 0`, and `F = 0` off the edges of `Ĝ`. -/
def IsEdgeflow (G : MarkedGraph V) (F : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ F u v) ∧ ∀ u v, ¬ G.hatEdge u v → F u v = 0

/-- **A flow**, Definition 1 of `brunswic2024theory` transported to `Ĝ`: an edgeflow satisfying
flow matching, which on the loop closure is conservation at every vertex. -/
def IsFlow (G : MarkedGraph V) (F : V → V → ℝ) : Prop :=
  IsEdgeflow G F ∧ IsCirculation F

/-- **A `0`-flow**, Definition 2 of `brunswic2024theory`: a flow satisfying the reward constraint
for the null reward, i.e. with zero inflow at `s_f`. -/
def IsZeroFlow (G : MarkedGraph V) (F₀ : V → V → ℝ) : Prop :=
  IsFlow G F₀ ∧ edgeInflow F₀ G.snk = 0

/-- **`eq:def_stability`** (`cv_divergence.tex:183–185`), Definition 3 of `brunswic2024theory` at
`p = 1`: a loss `𝓛` on edgeflows is *stable* when `𝓛(F + F₀) ≥ 𝓛(F)` for every flow `F` and
every `0`-flow `F₀` that is a subflow of `F` (`F₀ ≤ F` edgewise). `IsZeroFlow` forbids mass on a
possible edge `s₀ → s_f`, which Definition 2 allows; fewer `F₀` are checked, so the source's
stability implies `Stable` and `¬ Stable` implies the source's instability, but a *positive*
`Stable` result certifies less than the source's stability. -/
def Stable (G : MarkedGraph V) (L : (V → V → ℝ) → ℝ) : Prop :=
  ∀ F F₀ : V → V → ℝ, IsFlow G F → IsZeroFlow G F₀ → (∀ u v, F₀ u v ≤ F u v) → L F ≤ L (F + F₀)

/-- A single flow strictly improved by adding a `0`-subflow refutes `eq:def_stability`. -/
theorem not_stable_of_witness {G : MarkedGraph V} {L : (V → V → ℝ) → ℝ} {F F₀ : V → V → ℝ}
    (hF : IsFlow G F) (hF₀ : IsZeroFlow G F₀) (hsub : ∀ u v, F₀ u v ≤ F u v)
    (hlt : L (F + F₀) < L F) : ¬ Stable G L :=
  fun hs => (not_le.mpr hlt) (hs F F₀ hF hF₀ hsub)

variable [DecidableEq V]

namespace BackwardPolicy

variable {G : MarkedGraph V} (B : BackwardPolicy G)

/-! ### The balanced edgeflow is the edge measure, and the support of `F` -/

/-- **`F* = λ₂`**: the balanced edgeflow `F*(u→v) = λ(v) π̂_←(v→u)` of `Graph.Universality` is the
edge measure `λ₂(u,v) = π̂_←(v→u) λ(v)` of `Balance.Lift`. -/
theorem edgeFlow_one_eq_edgeMeasure (lam : V → ℝ) :
    B.edgeFlow lam 1 = Balance.edgeMeasure B.phat lam := by
  funext u v
  simp only [edgeFlow, Balance.edgeMeasure]
  ring

/-- `π̂_←(v → u) > 0` on every edge `u → v` of `Ĝ`. -/
theorem phat_pos_of_hatEdge (hbpos : B.PositiveOnEdges) {u v : V} (he : G.hatEdge u v) :
    0 < B.phat v u := by
  rcases he with he | ⟨hu, hv⟩
  · exact B.phat_pos_of_edge hbpos he
  · subst hu; subst hv; rw [B.phat_src_snk]; norm_num

/-- `π̂_←(v → u) = 0` off the edges of `Ĝ`. -/
theorem phat_eq_zero_of_not_hatEdge {u v : V} (he : ¬ G.hatEdge u v) : B.phat v u = 0 := by
  by_contra hne
  exact he (B.phat_supp hne)

/-- `F* = 0` off the edges of `Ĝ`. -/
theorem edgeFlow_eq_zero_of_not_hatEdge (lam : V → ℝ) (c : ℝ) {u v : V}
    (he : ¬ G.hatEdge u v) : B.edgeFlow lam c u v = 0 := by
  simp only [edgeFlow, B.phat_eq_zero_of_not_hatEdge he, mul_zero]

/-- An admissible `ε > 0` forces `1_γ = 0` off the edges of `Ĝ`: there `2ε1_γ ≤ F* = 0`. -/
theorem circ_eq_zero_of_not_hatEdge {lam : V → ℝ} (γ : MarkedCirculation G) {eps : ℝ}
    (heps : 0 < eps) (hadm : B.AdmissibleEps lam eps γ.circ) {u v : V}
    (he : ¬ G.hatEdge u v) : γ.circ u v = 0 := by
  have h1 := hadm u v
  rw [B.edgeFlow_eq_zero_of_not_hatEdge lam 1 he, epsCirc_apply] at h1
  by_contra hne
  have hpos : 0 < γ.circ u v := (γ.nonneg u v).lt_of_ne (Ne.symm hne)
  have := mul_pos heps hpos
  linarith

/-- **`F = F* − ε1_γ` vanishes off the edges of `Ĝ`.** -/
theorem perturbedFlow_eq_zero_of_not_hatEdge {lam : V → ℝ} (γ : MarkedCirculation G) {eps : ℝ}
    (heps : 0 < eps) (hadm : B.AdmissibleEps lam eps γ.circ) {u v : V}
    (he : ¬ G.hatEdge u v) : B.perturbedFlow lam eps γ.circ u v = 0 := by
  simp only [perturbedFlow, epsCirc_apply, B.edgeFlow_eq_zero_of_not_hatEdge lam 1 he,
    B.circ_eq_zero_of_not_hatEdge γ heps hadm he, mul_zero, sub_zero]

/-- **`F = F* − ε1_γ` is positive on every edge of `Ĝ`**: `2ε1_γ ≤ F*` gives `F ≥ F*/2 > 0`. -/
theorem perturbedFlow_pos_of_hatEdge (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) {eps : ℝ} {c : V → V → ℝ}
    (hadm : B.AdmissibleEps lam eps c) {u v : V} (he : G.hatEdge u v) :
    0 < B.perturbedFlow lam eps c u v := by
  have hpos := B.edgeFlow_pos_of_hatEdge hbpos (h.pos hpc hbpos) one_pos he
  have h1 := hadm u v
  simp only [perturbedFlow]
  linarith

/-- **`prop:frozen_unstable_full`, *Admissibility*** (`proofs.tex:695`): "`F` is a flow". -/
theorem perturbedFlow_isEdgeflow {lam : V → ℝ} (γ : MarkedCirculation G) {eps : ℝ}
    (heps : 0 < eps) (hadm : B.AdmissibleEps lam eps γ.circ) :
    IsEdgeflow G (B.perturbedFlow lam eps γ.circ) :=
  ⟨fun u v => (epsCirc_nonneg heps.le γ.nonneg u v).trans (B.epsCirc_le_perturbedFlow hadm u v),
    fun _ _ he => B.perturbedFlow_eq_zero_of_not_hatEdge γ heps hadm he⟩

/-! ### Edge-level balance fails at `F` -/

/-- **"Summing over `v` at each `u`"** (`proofs.tex:701`): if a circulation `F` is in edge-level
balance, `F K₂ = F`, then its inflow is `π̂_←`-invariant. `(F K₂)(u,v) = π̂_←(v→u) · ∑_w F(v→w)`
summed over `v` is `∑_v F(v) π̂_←(v→u)` with `F(v)` the outflow, which the circulation property
turns into the inflow. -/
theorem invariant_edgeInflow_of_pushEdge_eq {F : V → V → ℝ} (hcirc : IsCirculation F)
    (heq : Balance.pushEdge B.phat F = F) :
    ∀ y, ∑ x, edgeInflow F x * B.phat x y = edgeInflow F y := by
  intro u
  have hrow : ∑ v, Balance.pushEdge B.phat F u v = ∑ v, F u v := by rw [heq]
  simp only [Balance.pushEdge_apply] at hrow
  calc ∑ x, edgeInflow F x * B.phat x u = ∑ x, B.phat x u * Balance.marg₁ F x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        show edgeInflow F x * B.phat x u = B.phat x u * edgeOutflow F x
        rw [hcirc x, mul_comm]
    _ = ∑ v, F u v := hrow
    _ = edgeOutflow F u := rfl
    _ = edgeInflow F u := hcirc u

/-- **Edge-level balance fails at `F`** (`proofs.tex:701`): `F K₂ ≠ F`, since otherwise
`μ_F π̂_← = μ_F`, contradicting `not_invariant_perturbedFlow`. -/
theorem pushEdge_perturbedFlow_ne (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) (γ : MarkedCirculation G) {eps : ℝ} (heps : 0 < eps)
    (hadm : B.AdmissibleEps lam eps γ.circ) :
    Balance.pushEdge B.phat (B.perturbedFlow lam eps γ.circ) ≠ B.perturbedFlow lam eps γ.circ :=
  fun heq => B.not_invariant_perturbedFlow hpc hbpos h γ heps hadm
    (B.invariant_edgeInflow_of_pushEdge_eq (B.isCirculation_perturbedFlow h eps γ.isCirculation)
      heq)

/-! ### The witness pair is a flow and a `0`-subflow, and the support of `λ₂` -/

/-- **`prop:frozen_unstable_full`, *Admissibility*** (`proofs.tex:695`): "`F` is a flow", in the
sense of Definition 1 — an edgeflow of `Ĝ` that is conserved at every vertex. -/
theorem perturbedFlow_isFlow {lam : V → ℝ} (h : B.IsInvProb lam) (γ : MarkedCirculation G)
    {eps : ℝ} (heps : 0 < eps) (hadm : B.AdmissibleEps lam eps γ.circ) :
    IsFlow G (B.perturbedFlow lam eps γ.circ) :=
  ⟨B.perturbedFlow_isEdgeflow γ heps hadm, B.isCirculation_perturbedFlow h eps γ.isCirculation⟩

/-- **`prop:frozen_unstable_full`, *Admissibility*** (`proofs.tex:695`): "`F₀` is a `0`-subflow",
in the sense of Definition 2 — a flow with zero inflow at `s_f`, because `γ` avoids `s_f`. -/
theorem epsCirc_isZeroFlow {lam : V → ℝ} (γ : MarkedCirculation G) {eps : ℝ} (heps : 0 < eps)
    (hadm : B.AdmissibleEps lam eps γ.circ) : IsZeroFlow G (epsCirc eps γ.circ) := by
  refine ⟨⟨⟨epsCirc_nonneg heps.le γ.nonneg, fun u v he => ?_⟩,
    isCirculation_epsCirc eps γ.isCirculation⟩, ?_⟩
  · rw [epsCirc_apply, B.circ_eq_zero_of_not_hatEdge γ heps hadm he, mul_zero]
  · rw [edgeInflow_epsCirc, γ.inflow_snk, mul_zero]

/-- **`λ₂` is positive exactly on the edges of `Ĝ`**: `λ₂(u,v) = π̂_←(v→u) λ(v)` with `λ > 0`.
This is why "`ν̂` of positive density against `λ₂`" means `ν̂ > 0` on the edges of `Ĝ` and
`ν̂ = 0` off them. -/
theorem edgeMeasure_pos_iff_hatEdge (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) (u v : V) :
    0 < Balance.edgeMeasure B.phat lam u v ↔ G.hatEdge u v := by
  rw [← B.edgeFlow_one_eq_edgeMeasure]
  constructor
  · intro hpos
    by_contra he
    rw [B.edgeFlow_eq_zero_of_not_hatEdge lam 1 he] at hpos
    exact lt_irrefl 0 hpos
  · exact fun he => B.edgeFlow_pos_of_hatEdge hbpos (h.pos hpc hbpos) one_pos he

/-! ### The DB loss with a frozen backward policy, read on edgeflows -/

/-- **`prop:frozen_unstable_full`, the DB loss with frozen backward policy, read on edgeflows**
(`proofs.tex:701`, through `prop:db_lift`, `proofs.tex:524–531`):
`𝓛_{DB,g,ν̂}(F) = ∫ g(d(FK₂)/dF) dν̂ = ∑_{u,v} ν̂(u,v) g((FK₂)(u,v) / F(u,v))`, with `K₂` the edge
lift of `π̂_←`. A definition; `dbLoss_eq_edgeRatio` is its identity with the edge-ratio form. -/
noncomputable def dbLoss (g : ℝ → ℝ) (nuHat F : V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, nuHat u v * g (Balance.pushEdge B.phat F u v / F u v)

/-- **`prop:db_lift`, read here**: for a non-negative edgeflow the DB loss is the `g`-divergence
of the detailed-balance edge ratio `F(v) π̂_←(v→u) / (F(u) π_→^F(u→v))`, with `F(·)` the first
marginal and `π_→^F` the disintegration. `Balance.db_lift_loss`, unchanged. -/
theorem dbLoss_eq_edgeRatio {F : V → V → ℝ} (hF : ∀ u v, 0 ≤ F u v) (g : ℝ → ℝ)
    (nuHat : V → V → ℝ) :
    B.dbLoss g nuHat F = ∑ u, ∑ v, nuHat u v *
      g (Balance.marg₁ F v * B.phat v u / (Balance.marg₁ F u * Balance.disint F u v)) :=
  Balance.db_lift_loss hF g nuHat

/-- **Between two edgeflows of `Ĝ`, the DB loss difference sees `ν̂` only on the edges.** Off the
edges both ratios are `0/0 = 0`, so the terms `ν̂(u,v) g(0)` cancel; any `ν̂'` agreeing with `ν̂` on
the edges gives the same difference. This is what lets `frozen_not_stable_db` drop `hnu0`. -/
theorem dbLoss_sub_eq_of_support {g : ℝ → ℝ} {nuHat nuHat' F F' : V → V → ℝ}
    (hnu : ∀ u v, G.hatEdge u v → nuHat' u v = nuHat u v)
    (hF : ∀ u v, ¬ G.hatEdge u v → F u v = 0) (hF' : ∀ u v, ¬ G.hatEdge u v → F' u v = 0) :
    B.dbLoss g nuHat F' - B.dbLoss g nuHat F = B.dbLoss g nuHat' F' - B.dbLoss g nuHat' F := by
  simp only [dbLoss, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  by_cases he : G.hatEdge u v
  · rw [hnu u v he]
  · rw [hF u v he, hF' u v he, div_zero, div_zero, sub_self, sub_self]

/-- **The DB loss vanishes at edge-level balance**: ratio `1` on every edge of `Ĝ`, `ν̂ = 0` off
them, and `g(1) = 0`. -/
theorem dbLoss_eq_zero_of {g : ℝ → ℝ} (hg1 : g 1 = 0) {nuHat F : V → V → ℝ}
    (hnu0 : ∀ u v, ¬ G.hatEdge u v → nuHat u v = 0)
    (hr : ∀ u v, G.hatEdge u v → Balance.pushEdge B.phat F u v / F u v = 1) :
    B.dbLoss g nuHat F = 0 := by
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
  by_cases he : G.hatEdge u v
  · rw [hr u v he, hg1, mul_zero]
  · rw [hnu0 u v he, zero_mul]

/-- **The DB loss is positive at one unbalanced edge**: `ν̂ > 0` on the edges of `Ĝ` and `0` off
them, positive ratios on the edges, and one edge whose ratio is not `1`; `g > 0` off `1` does the
rest. -/
theorem dbLoss_pos_of {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x)
    {nuHat F : V → V → ℝ} (hnupos : ∀ u v, G.hatEdge u v → 0 < nuHat u v)
    (hnu0 : ∀ u v, ¬ G.hatEdge u v → nuHat u v = 0)
    (hrpos : ∀ u v, G.hatEdge u v → 0 < Balance.pushEdge B.phat F u v / F u v)
    {u₀ v₀ : V} (he₀ : G.hatEdge u₀ v₀)
    (hne : Balance.pushEdge B.phat F u₀ v₀ / F u₀ v₀ ≠ 1) :
    0 < B.dbLoss g nuHat F := by
  have hterm : ∀ u v, 0 ≤ nuHat u v * g (Balance.pushEdge B.phat F u v / F u v) := by
    intro u v
    by_cases he : G.hatEdge u v
    · rcases eq_or_ne (Balance.pushEdge B.phat F u v / F u v) 1 with h1 | h1
      · rw [h1, hg1, mul_zero]
      · exact (mul_pos (hnupos u v he) (hgpos _ (hrpos u v he) h1)).le
    · rw [hnu0 u v he, zero_mul]
  unfold dbLoss
  refine Finset.sum_pos' (fun u _ => Finset.sum_nonneg fun v _ => hterm u v)
    ⟨u₀, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun v _ => hterm u₀ v)
    ⟨v₀, Finset.mem_univ _, mul_pos (hnupos u₀ v₀ he₀) (hgpos _ (hrpos u₀ v₀ he₀) hne)⟩

/-- **At `F + F₀ = F*` the DB ratio is `1` on every edge of `Ĝ`** (`proofs.tex:701`, "this holds by
construction"): `F* = λ₂` is `K₂`-invariant (`Balance.pushEdge_edgeMeasure_graph`) and `F* > 0`
on the edges. -/
theorem dbRatio_edgeFlow_eq_one (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) {u v : V} (he : G.hatEdge u v) :
    Balance.pushEdge B.phat (B.edgeFlow lam 1) u v / B.edgeFlow lam 1 u v = 1 := by
  have hfix : Balance.pushEdge B.phat (B.edgeFlow lam 1) = B.edgeFlow lam 1 := by
    rw [B.edgeFlow_one_eq_edgeMeasure]
    exact Balance.pushEdge_edgeMeasure_graph h
  rw [hfix]
  exact div_self (B.edgeFlow_pos_of_hatEdge hbpos (h.pos hpc hbpos) one_pos he).ne'

/-- **At `F` the DB ratio is positive on every edge of `Ĝ`** — what `g > 0` on `ℝ_{>0}` needs:
`π̂_←(v→u) > 0`, the outflow of `F` at `v` equals its inflow, which is `≥ λ(v)/2 > 0`, and
`F(u→v) > 0`. -/
theorem dbRatio_perturbedFlow_pos (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) (γ : MarkedCirculation G) {eps : ℝ}
    (hadm : B.AdmissibleEps lam eps γ.circ) {u v : V} (he : G.hatEdge u v) :
    0 < Balance.pushEdge B.phat (B.perturbedFlow lam eps γ.circ) u v
      / B.perturbedFlow lam eps γ.circ u v := by
  have hlam := h.pos hpc hbpos
  have hcirc := B.isCirculation_perturbedFlow h eps γ.isCirculation
  rw [Balance.pushEdge_apply]
  refine div_pos (mul_pos (B.phat_pos_of_hatEdge hbpos he) ?_)
    (B.perturbedFlow_pos_of_hatEdge hpc hbpos h hadm he)
  show 0 < edgeOutflow (B.perturbedFlow lam eps γ.circ) v
  rw [hcirc v]
  linarith [hlam v, B.edgeInflow_perturbedFlow_ge hadm v]

/-! ### `prop:frozen_unstable_full`, the DB half -/

/-- **`prop:frozen_unstable_full`, the DB half** (statement `proofs.tex:680–690`, *The DB case*
`proofs.tex:701`), in the four-part form of `frozen_unstable_full_fm`.

With the FM half's hypotheses, and `ν̂` positive on the edges of `Ĝ` and zero off them:
`0 ≤ F₀`, `F₀ ≤ F`, and `𝓛_{DB,g,ν̂}(F + F₀) = 0 < 𝓛_{DB,g,ν̂}(F)` — the same pair `(F, F₀)`
witnesses DB instability. -/
theorem frozen_unstable_full_db (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) (γ : MarkedCirculation G) {g : ℝ → ℝ} (hg1 : g 1 = 0)
    (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) {nuHat : V → V → ℝ}
    (hnupos : ∀ u v, G.hatEdge u v → 0 < nuHat u v)
    (hnu0 : ∀ u v, ¬ G.hatEdge u v → nuHat u v = 0) {eps : ℝ} (heps : 0 < eps)
    (hadm : B.AdmissibleEps lam eps γ.circ) :
    (∀ u v, 0 ≤ epsCirc eps γ.circ u v) ∧
      (∀ u v, epsCirc eps γ.circ u v ≤ B.perturbedFlow lam eps γ.circ u v) ∧
      B.dbLoss g nuHat (B.perturbedFlow lam eps γ.circ + epsCirc eps γ.circ) = 0 ∧
      0 < B.dbLoss g nuHat (B.perturbedFlow lam eps γ.circ) := by
  refine ⟨epsCirc_nonneg heps.le γ.nonneg, B.epsCirc_le_perturbedFlow hadm, ?_, ?_⟩
  · rw [B.perturbedFlow_add_epsCirc]
    exact B.dbLoss_eq_zero_of hg1 hnu0 fun u v he => B.dbRatio_edgeFlow_eq_one hpc hbpos h he
  · obtain ⟨u₀, v₀, he₀, hne⟩ : ∃ u v, G.hatEdge u v ∧
        Balance.pushEdge B.phat (B.perturbedFlow lam eps γ.circ) u v
          / B.perturbedFlow lam eps γ.circ u v ≠ 1 := by
      by_contra hc
      push Not at hc
      apply B.pushEdge_perturbedFlow_ne hpc hbpos h γ heps hadm
      funext u v
      by_cases he : G.hatEdge u v
      · exact (div_eq_one_iff_eq (B.perturbedFlow_pos_of_hatEdge hpc hbpos h hadm he).ne').mp
          (hc u v he)
      · rw [Balance.pushEdge_apply, B.phat_eq_zero_of_not_hatEdge he, zero_mul,
          B.perturbedFlow_eq_zero_of_not_hatEdge γ heps hadm he]
    exact B.dbLoss_pos_of hg1 hgpos hnupos hnu0
      (fun u v he => B.dbRatio_perturbedFlow_pos hpc hbpos h γ hadm he) he₀ hne


/-! ### "Hence […] unstable in the sense of `eq:def_stability`" -/

/-- **`prop:frozen_unstable_full`, the FM loss is unstable in the sense of `eq:def_stability`**
(`proofs.tex:689`). -/
theorem frozen_not_stable_fm (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    (γ : MarkedCirculation G) (hsupp : ∀ u v, γ.circ u v ≠ 0 → G.hatEdge u v) {g : ℝ → ℝ}
    (hg1 : g 1 = 0) (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) {nu : V → ℝ}
    (hnu : ∀ x, 0 < nu x) :
    ¬ Stable G (fun F => B.fmLoss g nu (edgeInflow F)) := by
  obtain ⟨lam, h⟩ := B.exists_invProb
  obtain ⟨eps, heps, hadm⟩ := B.exists_admissibleEps hbpos (h.pos hpc hbpos) γ hsupp
  obtain ⟨-, hle, hzero, hpos⟩ := B.frozen_unstable_full_fm hpc hbpos h γ hg1 hgpos hnu heps hadm
  exact not_stable_of_witness (B.perturbedFlow_isFlow h γ heps hadm)
    (B.epsCirc_isZeroFlow γ heps hadm) hle (hzero.trans_lt hpos)

/-- **`prop:frozen_unstable_full`, the DB loss is unstable in the sense of `eq:def_stability`**
(`proofs.tex:689`, and "the same pair `(F, F₀)` therefore witnesses DB instability",
`proofs.tex:701`).

Only `ν̂ > 0` on the edges of `Ĝ` is asked: what `ν̂` does off them adds the same constant to
`𝓛(F + F₀)` and to `𝓛(F)` (`dbLoss_sub_eq_of_support`), so the comparison is made at the
restriction of `ν̂` to the edges, where `frozen_unstable_full_db` applies. -/
theorem frozen_not_stable_db (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    (γ : MarkedCirculation G) (hsupp : ∀ u v, γ.circ u v ≠ 0 → G.hatEdge u v) {g : ℝ → ℝ}
    (hg1 : g 1 = 0) (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) {nuHat : V → V → ℝ}
    (hnupos : ∀ u v, G.hatEdge u v → 0 < nuHat u v) :
    ¬ Stable G (B.dbLoss g nuHat) := by
  classical
  obtain ⟨lam, h⟩ := B.exists_invProb
  obtain ⟨eps, heps, hadm⟩ := B.exists_admissibleEps hbpos (h.pos hpc hbpos) γ hsupp
  let nuE : V → V → ℝ := fun u v => if G.hatEdge u v then nuHat u v else 0
  have hEon : ∀ u v, G.hatEdge u v → nuE u v = nuHat u v := fun u v he => if_pos he
  have hEpos : ∀ u v, G.hatEdge u v → 0 < nuE u v := fun u v he => (hEon u v he).symm ▸ hnupos u v he
  have hE0 : ∀ u v, ¬ G.hatEdge u v → nuE u v = 0 := fun u v he => if_neg he
  obtain ⟨-, hle, hzero, hpos⟩ :=
    B.frozen_unstable_full_db hpc hbpos h γ hg1 hgpos hEpos hE0 heps hadm
  have hsum0 : ∀ u v, ¬ G.hatEdge u v →
      (B.perturbedFlow lam eps γ.circ + epsCirc eps γ.circ) u v = 0 := by
    intro u v he
    rw [B.perturbedFlow_add_epsCirc]
    exact B.edgeFlow_eq_zero_of_not_hatEdge lam 1 he
  have hdiff := B.dbLoss_sub_eq_of_support (g := g) hEon
    (fun u v he => B.perturbedFlow_eq_zero_of_not_hatEdge γ heps hadm he) hsum0
  refine not_stable_of_witness (B.perturbedFlow_isFlow h γ heps hadm)
    (B.epsCirc_isZeroFlow γ heps hadm) hle ?_
  linarith

end BackwardPolicy

end GFNBounds.Graph
