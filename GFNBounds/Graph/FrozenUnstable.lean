import GFNBounds.Balance.MassIdentity
import GFNBounds.Graph.Universality

/-!
# Freezing the backward policy does not restore stability, and the loop closure is what makes the frozen family nonempty

**`prop:frozen_unstable_full`** — statement `proofs.tex:659–669`, proof `proofs.tex:671–683`.

**`rem:loop_closure_necessary`** — `proofs.tex:1014–1016`.

(The bold-backtick form of each label, each alone on its line, is what `scripts/trace_check.py`
and the paper-side ledger machine-read; a label mentioned only in prose is not a claim to
certify it.) The standing prose defining *marked graph* and *backward policy* is
`proofs.tex:949`, and the stability being negated is `eq:def_stability`
(`cv_divergence.tex:179–181`):

> `𝓛(F + F₀) ≥ 𝓛(F)` for every `0`-flow `F₀` that is a subflow of `F`.

> (`prop:frozen_unstable_full`) Let `𝒢` be a finite path-connected marked graph carrying a
> directed cycle `γ` disjoint from `{s₀, s_f}`, let `π̂_←` be an everywhere-positive frozen
> backward policy on its loop closure, let `λ` be the associated balanced flow and let `g` be
> continuous with `g(1) = 0` and `g > 0` elsewhere. Write `F*(u→v) := λ(v) π̂_←(v→u)` for the
> balanced edgeflow and `1_γ` for the unit circulation along `γ`. Then for every training
> measure `ν` of positive density and every `0 < ε ≤ ½ min_{(u→v)∈γ} F*(u→v)`, the edgeflow
> `F := F* − ε1_γ` and the `0`-flow `F₀ := ε1_γ` satisfy `0 ≤ F₀ ≤ F` and
> `𝓛_{g,ν}(F + F₀) = 0 < 𝓛_{g,ν}(F)`.

and its proof, whose three steps this file follows:

> With a frozen backward policy the FM loss is a function of the state flow alone,
> `𝓛_{g,ν}(μ) = ∫ g(r) dν` with `r = d(μ π̂_←)/dμ`; read on edgeflows […] it is
> `F ↦ 𝓛_{g,ν}(μ_F)`, where `μ_F(v) := ∑_u F(u→v)` is the inflow. Since the rows of `π̂_←` sum
> to `1`, `μ_{F*} = λ`, and `μ_{1_γ} = ∂γ := ∑_{v ∈ γ} δ_v`.
>
> *Admissibility.* `λ > 0` and `π̂_← > 0` give `F* > 0` on every edge, so `ε` is well defined and
> positive, and `2ε1_γ ≤ F*` edgewise; hence `F = F* − ε1_γ ≥ ε1_γ = F₀ ≥ 0`.
>
> *`𝓛_{g,ν}(F) > 0`.* We have `μ_F = λ − ε ∂γ`. As `γ` avoids `s_f`, `∂γ(s_f) = 0 < λ(s_f)`
> while `∂γ ≠ 0`, so `∂γ` is not proportional to `λ` and neither is `μ_F`. The loop-closed chain
> being ergodic, its invariant measures are exactly the multiples of `λ`, so `μ_F π̂_← ≠ μ_F`:
> the ratio `r` differs from `1` on a set of positive `ν`-measure, and `g > 0` off `1` gives
> `𝓛_{g,ν}(F) > 0`.
>
> *`𝓛_{g,ν}(F + F₀) = 0`.* `F + F₀ = F*`, whose state flow `λ` is `π̂_←`-invariant, so `r ≡ 1`
> and `g(1) = 0`.

> (`rem:loop_closure_necessary`) On `G` itself, i.e. without the wrap edge, the frozen-backward
> family is trivial. Indeed the marginal argument of *(2)* forces `f_out(s₀) = 0` (`π_←` being
> undefined at `s₀`) and `f_out μ` to be invariant under the backward kernel restricted to
> `𝒱 ∖ {s₀}`, which is substochastic: from every vertex, the backward chain leaks to `s₀` within
> `#𝒱` steps with probability bounded below, by reversing a source-to-vertex path as in the
> proof of *(1)*. Iterating the invariance identity gives `f_out = 0`. The loop closure is
> therefore not a convenience of the proof: it is the mechanism that makes the frozen-backward
> parameterization nonempty […].

## The modelling decisions

**The loss is a definition, and that is why this proposition is reachable.** `fmLoss` is
`𝓛_{g,ν}(μ) = ∑_x ν(x) g(r(x))` with `r` the ratio `d(μ π̂_←)/dμ` of `GFNBounds.Balance`, and
`fmLoss g ν (edgeInflow F)` is the paper's "read on edgeflows". Nothing here differentiates
anything: `prop:frozen_unstable_full` is a statement about two *values* of the loss, not about
its gradient, so `theo:first_variation_full` — the missing storey under
`GFNBounds.Balance.MassIdentity` — is not needed and is not used. That is the whole reason this
label is closable while its neighbours in `app:divergence` are not.

**`1_γ` is hypothesized, not constructed — a strengthening.** The paper exhibits a directed
cycle `γ` avoiding both marks and takes `1_γ` to be its indicator. What its proof consumes of
`1_γ` is only that it is non-negative, non-zero, and has zero inflow at `s_f`; and what makes
`F₀ = ε1_γ` a *`0`-flow* in the sense of `eq:def_stability` is that it is a circulation. So the
hypothesis carried here is `MarkedCirculation`: a non-negative circulation, not identically
zero, with zero inflow at both marks. Every `1_γ` of the paper is one, so the proposition proved
is the paper's; it is stated for more circulations than the paper's, which is the safe
direction. `exists_admissibleEps` shows the interval of admissible `ε` is non-empty, which is
the paper's *Admissibility* sentence "`ε` is well defined and positive"; it is there, and only
there, that `1_γ` is asked to ride on the edges of `Ĝ`, since a circulation supported off them
sits where `F*` vanishes and admits no positive `ε` at all.

**The `ε` hypothesis is the edgewise one.** The paper's `0 < ε ≤ ½ min_{(u→v)∈γ} F*(u→v)` is,
for a `{0,1}`-valued `1_γ`, exactly `AdmissibleEps`: `2 ε 1_γ ≤ F*` edgewise — which is the form
its own proof uses one line later, and the form that survives a circulation taking values other
than `0` and `1`.

**`rem:loop_closure_necessary` reads "`π_←` undefined at `s₀`" as an emptied row** (`pcut`), and
keeps `π_→` a Markov kernel at every state, exactly as `FrozenBalance` does in item *(2)*. Both
halves of that reading are load-bearing; see SCOPE.

## What is proved

| | |
|---|---|
| `edgeInflow`, `edgeOutflow`, `IsCirculation` | the marginals of an edgeflow, and what a `0`-flow is |
| `MarkedCirculation` | the hypothesis bundle standing for `1_γ` |
| `sum_edgeInflow_pos` | `∂γ ≠ 0`, in the form the last step needs: `∑_v ∂γ(v) > 0` |
| `stateRatio`, `fmLoss` | `r = d(μπ̂_←)/dμ` via `GFNBounds.Balance.ratio`, and `∫ g(r) dν` |
| `stateRatio_eq_one_iff` | `r ≡ 1 ↔ μ π̂_← = μ`, via `GFNBounds.Balance.ratio_eq_one_iff_balanced` |
| `stateRatio_pos` | `r > 0` at every state flow of positive density — what `g > 0` on `ℝ_{>0}` needs |
| `edgeFlow_pos_of_hatEdge` | *Admissibility*, first half: `F* > 0` on every edge of `Ĝ` |
| `exists_admissibleEps` | *Admissibility*, second half: an admissible `ε > 0` exists |
| `epsCirc_le_perturbedFlow`, `perturbedFlow_add_epsCirc` | `0 ≤ F₀ ≤ F` and `F + F₀ = F*` |
| `edgeInflow_perturbedFlow` | `μ_F = λ − ε ∂γ` |
| `edgeInflow_perturbedFlow_ge` | `μ_F ≥ λ/2 > 0` — the non-negativity `eq_smul_invProb` needs |
| `sum_edgeInflow_perturbedFlow` | `∑ μ_F = 1 − ε ∑ ∂γ` |
| `not_invariant_perturbedFlow` | `μ_F π̂_← ≠ μ_F`, by `eq_smul_invProb` and `∂γ(s_f) = 0` |
| `fmLoss_eq_zero`, `fmLoss_pos` | `g(1) = 0` at balance; `g > 0` off `1` away from it |
| `frozen_unstable_full_fm` | the proposition's FM half, in its own four-part form |
| `isCirculation_epsCirc`, `isCirculation_perturbedFlow` | `F₀` and `F` really are `0`-flows |
| `pcut`, `CutBalance` | the backward kernel of `G` itself, and the frozen family on `G` |
| `cutBalance_zero` | `f_out ≡ 0` is in the family, whatever `π_→` |
| `cutBalance_invariant` | the marginal argument: `f_out μ` is `π_←`-invariant |
| `cutBalance_src_eq_zero` | the marginal argument, at the source: `f_out(s₀) = 0` |
| `cutInvariant_step`, `cutInvariant_eq_zero_of_reach` | zero propagates along the edges of `G` |
| `loop_closure_necessary` | `rem:loop_closure_necessary`: the family on `G` is `{f_out ≡ 0}` |

## SCOPE (disclosed)

* **Only the FM half of `prop:frozen_unstable_full`.** The paper's *DB case* paragraph
  (`proofs.tex:680`) reads the DB loss on edgeflows through `prop:db_lift`
  (`proofs.tex:524–535`), which is **not formalized** — it is `bucket C` and unassigned in
  `paper-map.json`. Nothing below mentions the DB loss, and the sentence "the same pair
  `(F, F₀)` therefore witnesses DB instability" is not certified here.
* **The loss is defined, not derived.** `fmLoss` is `∑_x ν(x) g(r(x))`; that this is the FM loss
  of Definition 3 of `brunswic2024theory` read on edgeflows is the paper's first proof
  paragraph, and it is taken as the definition. Neither the edgeflow FM loss nor
  `eq:def_stability` is defined in this library, so "unstable in the sense of
  `eq:def_stability`" is delivered as the four conjuncts of `frozen_unstable_full_fm` — `F₀` a
  non-negative subflow of `F` (and, by `isCirculation_epsCirc`, a circulation), and
  `𝓛(F + F₀) = 0 < 𝓛(F)` — and not as a negation of a formal `Stable` predicate.
* **Continuity of `g` is not carried**, because the proof never uses it: only `g(1) = 0` and
  `g > 0` elsewhere enter, and only at the finitely many values `r(x)`. `hgpos` is stated on
  `ℝ_{>0}`, the domain the generator lives on, matching `GFNBounds.Balance`'s
  `StrictlyUnimodal`; the ratios are proved positive (`stateRatio_pos`) rather than assumed so.
* **`ν` is a positive density, not a probability.** "Training measure of positive density" is
  `∀ x, 0 < ν x`; no normalization is imposed, and none is used.
* **The proposition is stated at an arbitrary invariant probability `λ`**, quantified over as
  `IsInvProb`, rather than at a chosen one. `theo:universality_graphs`*(1)* — imported, not
  restated — supplies existence and uniqueness, so this is the paper's "the associated balanced
  flow".
* **Two fields of `MarkedCirculation` are carried but unconsumed by the FM half.**
  `isCirculation` and `inflow_src` are what make `F₀` a `0`-flow and what "disjoint from
  `{s₀, s_f}`" says at the source; the three steps of the proof use only `nonneg`, `ne_zero` and
  `inflow_snk`. They are kept because dropping them would leave `F₀` a subflow that is not a
  `0`-flow, which is not the paper's statement; `isCirculation_epsCirc` and
  `isCirculation_perturbedFlow` are where `isCirculation` is spent.
* **`rem:loop_closure_necessary` is proved by a different route than the paper's, on the same
  hypotheses.** The paper leaks to `s₀` within `#𝒱` steps with probability bounded below and
  iterates the invariance identity — a Doeblin argument needing powers of the substochastic
  kernel. Here the marginal argument gives `f_out(s₀) = 0` directly, and invariance then
  propagates that zero **forwards along the edges of `G`** (`cutInvariant_eq_zero_of_reach`):
  `f_out(u) = ∑_v f_out(v) π_←(v→u)` with `f_out ≥ 0` forces `f_out(v) = 0` at every
  out-neighbour `v` of a vertex `u` where `f_out` vanishes, because `π_←(v→u) > 0` there. Path
  connectedness then reaches every vertex from `s₀`. No kernel powers, no minorization, and no
  hypothesis beyond `PathConnected` and `PositiveOnEdges`, which the paper also uses.
* **The remark's truth depends on reading `π_→` as a Markov kernel at every state**, which is
  what item *(2)*'s `Θ` does and what `FrozenBalance` carries. It is not a harmless choice: with
  the row of `π_→` at `s_f` emptied as well — the reading in which `G` has no edge out of `s_f`
  — the conclusion is **false**. On `G = (s₀ → s_f)` with `π_←(s_f → s₀) = 1`,
  `π_→(s₀ → s_f) = 1` and `π_→(s_f → ·) = 0`, every pair `f_out(s₀) = f_out(s_f) = c` satisfies
  the constraint, and the family is a ray rather than `{0}`. This is recorded, not fixed: the
  paper's own `Θ` is item *(2)*'s, and on `Ĝ` every vertex has an outgoing edge, so the question
  does not arise there. It is what "the loop closure is the mechanism that makes the
  parameterization nonempty" costs when the wrap edge is removed from one side only.
* **`f_out ≥ 0` is a hypothesis of `loop_closure_necessary`**, as it is of `frozenBalance_eq`:
  `f_out` is the density of a measure. The signed statement — that the substochastic kernel has
  no non-zero fixed density at all — is true but needs the Doeblin route the paper takes, and is
  not proved here.
* **No `sorry`.** Every declaration below is closed.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒢` a finite marked graph | ✓ `[Fintype V]`, `MarkedGraph V`; `[DecidableEq V]` as in `Setting` |
| `𝒢` path-connected | ✓ `G.PathConnected` |
| `𝒢` carries a directed cycle `γ` disjoint from `{s₀, s_f}` | ⚠ **weakened to a hypothesis** `MarkedCirculation G`: a non-negative circulation, non-zero, with zero inflow at both marks. Every such cycle gives one; the converse fails, so the statement proved is more general. See the modelling decisions |
| `π̂_←` an everywhere-positive frozen backward policy on the loop closure | ✓ `BackwardPolicy G` with `B.PositiveOnEdges`; `phat` is the loop closure |
| `λ` the associated balanced flow | ✓ `B.IsInvProb lam`, quantified over — existence and uniqueness are `theo:universality_graphs`*(1)* |
| `g` continuous | ✗ **not carried** — unused; see SCOPE |
| `g(1) = 0` | ✓ `hg1` |
| `g > 0` elsewhere | ✓ `hgpos : ∀ x, 0 < x → x ≠ 1 → 0 < g x`, on the generator's domain |
| `ν` a training measure of positive density | ✓ `hnu : ∀ x, 0 < nu x`; not required to be a probability |
| `0 < ε ≤ ½ min_{(u→v)∈γ} F*(u→v)` | ✓ `0 < eps` and `B.AdmissibleEps lam eps γ.circ`, i.e. `2ε1_γ ≤ F*` edgewise — the paper's own next line, and equivalent to its display for a `{0,1}`-valued `1_γ`. Non-vacuity is `exists_admissibleEps` |
| `F* (u→v) = λ(v) π̂_←(v→u)` | ✓ `B.edgeFlow lam 1`, imported from `Universality` |
| (`rem`) `π_←` undefined at `s₀` | ✓ modelled as the emptied row `pcut`; `pcut G.src = 0`, `pcut s = pb s` off `s₀` |
| (`rem`) `π_→` a forward policy | ⚠ read as `∀ u, ∑ v, π_→(u→v) = 1`, as in `FrozenBalance`; **load-bearing**, see SCOPE |
| (`rem`) `f_out` a density | ✓ `hnn : ∀ x, 0 ≤ fout x` |
| (`rem`) the substochastic kernel leaks to `s₀` | ✗ **not used**; replaced by forward propagation of the zero along `G.Reach`. See SCOPE |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

variable {V : Type*} [Fintype V]

/-! ### Edgeflows, their marginals, and `0`-flows -/

/-- **`prop:frozen_unstable_full`, the inflow of an edgeflow** (`proofs.tex:673`):
`μ_F(v) := ∑_u F(u → v)`. This is the state flow the FM loss with a frozen backward policy is a
function of. -/
def edgeInflow (F : V → V → ℝ) : V → ℝ := fun v => ∑ u, F u v

/-- The outflow of an edgeflow, `∑_v F(u → v)`. -/
def edgeOutflow (F : V → V → ℝ) : V → ℝ := fun u => ∑ v, F u v

/-- **A `0`-flow**, in the sense `eq:def_stability` quantifies over
(`cv_divergence.tex:179–181`): an edgeflow that neither creates nor destroys mass at any vertex,
i.e. a circulation. -/
def IsCirculation (F : V → V → ℝ) : Prop := ∀ x, edgeOutflow F x = edgeInflow F x

/-- **`prop:frozen_unstable_full`, the unit circulation `1_γ`** (`proofs.tex:663`), as the
hypothesis bundle its proof consumes: a non-negative circulation, not identically zero, with
zero inflow at both marks.

The indicator of a directed cycle disjoint from `{s₀, s_f}` is one of these; carrying the
properties rather than the cycle is a strengthening, disclosed in the module's SCOPE. -/
structure MarkedCirculation (G : MarkedGraph V) where
  /-- The edgeflow `1_γ` itself. -/
  circ : V → V → ℝ
  /-- `1_γ ≥ 0`. -/
  nonneg : ∀ u v, 0 ≤ circ u v
  /-- `1_γ` is a circulation: it is a `0`-flow. -/
  isCirculation : IsCirculation circ
  /-- `1_γ ≠ 0`: the cycle is not empty. -/
  ne_zero : circ ≠ 0
  /-- `γ` avoids `s₀`: `∂γ(s₀) = 0`. -/
  inflow_src : edgeInflow circ G.src = 0
  /-- `γ` avoids `s_f`: `∂γ(s_f) = 0`. -/
  inflow_snk : edgeInflow circ G.snk = 0

omit [Fintype V] in
/-- A non-zero edgeflow is non-zero at some transition, in the form the sums below want. -/
theorem exists_apply_ne_zero {c : V → V → ℝ} (hne : c ≠ 0) : ∃ u v, c u v ≠ 0 := by
  obtain ⟨u, hu⟩ := Function.ne_iff.mp hne
  simp only [Pi.zero_apply] at hu
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hu
  simp only [Pi.zero_apply] at hv
  exact ⟨u, v, hv⟩

/-- `1_γ` is somewhere non-zero. -/
theorem MarkedCirculation.exists_ne_zero {G : MarkedGraph V} (γ : MarkedCirculation G) :
    ∃ u v, γ.circ u v ≠ 0 :=
  exists_apply_ne_zero γ.ne_zero

/-- **`prop:frozen_unstable_full`, the `0`-flow `F₀ := ε 1_γ`** (`proofs.tex:665`). -/
def epsCirc (eps : ℝ) (c : V → V → ℝ) : V → V → ℝ := fun u v => eps * c u v

omit [Fintype V] in
/-- `ε 1_γ`, evaluated. -/
theorem epsCirc_apply (eps : ℝ) (c : V → V → ℝ) (u v : V) : epsCirc eps c u v = eps * c u v := rfl

omit [Fintype V] in
/-- `F₀ = ε 1_γ ≥ 0` for `ε ≥ 0` — the first conjunct of the proposition's display. -/
theorem epsCirc_nonneg {eps : ℝ} (heps : 0 ≤ eps) {c : V → V → ℝ} (hc : ∀ u v, 0 ≤ c u v)
    (u v : V) : 0 ≤ epsCirc eps c u v :=
  mul_nonneg heps (hc u v)

/-- The inflow of `ε 1_γ` is `ε ∂γ`. -/
theorem edgeInflow_epsCirc (eps : ℝ) (c : V → V → ℝ) (v : V) :
    edgeInflow (epsCirc eps c) v = eps * edgeInflow c v := by
  simp only [edgeInflow, epsCirc, ← Finset.mul_sum]

/-- The outflow of `ε 1_γ` is `ε` times that of `1_γ`. -/
theorem edgeOutflow_epsCirc (eps : ℝ) (c : V → V → ℝ) (u : V) :
    edgeOutflow (epsCirc eps c) u = eps * edgeOutflow c u := by
  simp only [edgeOutflow, epsCirc, ← Finset.mul_sum]

/-- **`F₀ = ε1_γ` is a `0`-flow**: scaling a circulation gives a circulation. This is what makes
the pair `(F, F₀)` a witness against `eq:def_stability` rather than against a weaker statement
about subflows. -/
theorem isCirculation_epsCirc (eps : ℝ) {c : V → V → ℝ} (hc : IsCirculation c) :
    IsCirculation (epsCirc eps c) := by
  intro x
  rw [edgeOutflow_epsCirc, edgeInflow_epsCirc, hc x]

/-- **`∂γ ≠ 0`** in the only form the proof of `𝓛_{g,ν}(F) > 0` needs: the total mass of the
inflow of a non-negative, non-zero edgeflow is positive. -/
theorem sum_edgeInflow_pos {c : V → V → ℝ} (hnn : ∀ u v, 0 ≤ c u v) (hne : c ≠ 0) :
    0 < ∑ v, edgeInflow c v := by
  obtain ⟨u0, v0, h0⟩ := exists_apply_ne_zero hne
  refine Finset.sum_pos' (fun v _ => Finset.sum_nonneg fun u _ => hnn u v)
    ⟨v0, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun u _ => hnn u v0)
    ⟨u0, Finset.mem_univ _, (hnn u0 v0).lt_of_ne (Ne.symm h0)⟩

variable [DecidableEq V]

namespace BackwardPolicy

variable {G : MarkedGraph V} (B : BackwardPolicy G)

/-! ### The FM loss with a frozen backward policy, read on state flows -/

/-- **`prop:frozen_unstable_full`, the ratio `r = d(μ π̂_←)/dμ`** (`proofs.tex:673`), in the
coordinates of `GFNBounds.Balance`: `μ = u λ` at `λ := μ` and `u := 1`, so that
`ratio π̂_← μ 1 = (μ π̂_←)/μ`. -/
noncomputable def stateRatio (mu : V → ℝ) : V → ℝ := Balance.ratio B.phat mu 1

theorem stateRatio_apply (mu : V → ℝ) (y : V) :
    B.stateRatio mu y = (∑ x, mu x * B.phat x y) / mu y := by
  simp [stateRatio, Balance.ratio, Balance.pushMass]

/-- `GFNBounds.Balance`'s `Balanced` at these coordinates is invariance of the state flow. -/
theorem balanced_iff (mu : V → ℝ) :
    Balance.Balanced B.phat mu 1 ↔ ∀ y, ∑ x, mu x * B.phat x y = mu y := by
  simp [Balance.Balanced, Balance.pushMass]

/-- **`r ≡ 1` if and only if the state flow is `π̂_←`-invariant** — `ratio_eq_one_iff_balanced`
of `GFNBounds.Balance`, read here. -/
theorem stateRatio_eq_one_iff {mu : V → ℝ} (hmu : ∀ y, 0 < mu y) :
    (∀ y, B.stateRatio mu y = 1) ↔ ∀ y, ∑ x, mu x * B.phat x y = mu y := by
  have hpos : ∀ y, 0 < mu y * (1 : V → ℝ) y := fun y => by simpa using hmu y
  simpa only [stateRatio, B.balanced_iff mu] using
    Balance.ratio_eq_one_iff_balanced (K := B.phat) (lam := mu) (u := 1) hpos

/-- **`prop:frozen_unstable_full`, the FM loss with a frozen backward policy**
(`proofs.tex:673`): `𝓛_{g,ν}(μ) = ∫ g(r) dν = ∑_x ν(x) g(r(x))`, a function of the state flow
alone. Read on an edgeflow `F` it is `fmLoss g ν (edgeInflow F)`.

A definition, not a derivation: see the module SCOPE. -/
noncomputable def fmLoss (g : ℝ → ℝ) (nu mu : V → ℝ) : ℝ := ∑ x, nu x * g (B.stateRatio mu x)

/-- Every state receives mass from somewhere under `π̂_←`: an invariant probability that is
positive somewhere is positive at `y`, so some term of `∑_x λ(x) π̂_←(x → y) = λ(y) > 0` is. -/
theorem exists_phat_pos_into {lam : V → ℝ} (h : B.IsInvProb lam) (hlam : ∀ x, 0 < lam x) (y : V) :
    ∃ x, 0 < B.phat x y := by
  by_contra hc
  have hc' : ∀ x : V, B.phat x y ≤ 0 := fun x => not_lt.mp fun hx => hc ⟨x, hx⟩
  have hz : ∀ x : V, lam x * B.phat x y = 0 := by
    intro x
    rw [le_antisymm (hc' x) (B.phat_nonneg x y), mul_zero]
  have hsum := h.inv y
  rw [Finset.sum_congr rfl fun x _ => hz x, Finset.sum_const_zero] at hsum
  exact (hlam y).ne' hsum.symm

/-- **The ratio is positive at every state flow of positive density.** The paper's `g > 0`
elsewhere is a statement on `ℝ_{>0}`, so this is what lets it be applied. -/
theorem stateRatio_pos {lam : V → ℝ} (h : B.IsInvProb lam) (hlam : ∀ x, 0 < lam x)
    {mu : V → ℝ} (hmu : ∀ x, 0 < mu x) (y : V) : 0 < B.stateRatio mu y := by
  obtain ⟨x0, hx0⟩ := B.exists_phat_pos_into h hlam y
  rw [B.stateRatio_apply]
  refine div_pos (Finset.sum_pos' (fun x _ => mul_nonneg (hmu x).le (B.phat_nonneg x y))
    ⟨x0, Finset.mem_univ _, mul_pos (hmu x0) hx0⟩) (hmu y)

/-- **`𝓛_{g,ν}(F + F₀) = 0`** (`proofs.tex:678`), in its general form: at a state flow that is
`π̂_←`-invariant the ratio is `≡ 1` and `g(1) = 0`. -/
theorem fmLoss_eq_zero {mu : V → ℝ} (hmu : ∀ y, 0 < mu y)
    (hinv : ∀ y, ∑ x, mu x * B.phat x y = mu y) {g : ℝ → ℝ} (hg1 : g 1 = 0) (nu : V → ℝ) :
    B.fmLoss g nu mu = 0 := by
  have hone := (B.stateRatio_eq_one_iff hmu).mpr hinv
  simp only [fmLoss, hone, hg1, mul_zero, Finset.sum_const_zero]

/-- **`𝓛_{g,ν}(F) > 0`** (`proofs.tex:676`), in its general form: `ν > 0`, `g ≥ 0` on the ratios
and `g > 0` at one of them. -/
theorem fmLoss_pos {mu : V → ℝ} (hr : ∀ y, 0 < B.stateRatio mu y) {g : ℝ → ℝ} (hg1 : g 1 = 0)
    (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) {nu : V → ℝ} (hnu : ∀ x, 0 < nu x) {y : V}
    (hy : B.stateRatio mu y ≠ 1) : 0 < B.fmLoss g nu mu := by
  simp only [fmLoss]
  refine Finset.sum_pos' (fun x _ => ?_) ⟨y, Finset.mem_univ _, mul_pos (hnu y) (hgpos _ (hr y) hy)⟩
  rcases eq_or_ne (B.stateRatio mu x) 1 with hx | hx
  · rw [hx, hg1, mul_zero]
  · exact (mul_pos (hnu x) (hgpos _ (hr x) hx)).le

/-! ### Admissibility: `F* > 0` on the edges of `Ĝ`, and an admissible `ε` exists -/

/-- **`prop:frozen_unstable_full`, the admissible `ε`** (`proofs.tex:664`): `2 ε 1_γ ≤ F*`
edgewise, which is the form the *Admissibility* step uses and, for a `{0,1}`-valued `1_γ`, is
the statement's `ε ≤ ½ min_{(u→v)∈γ} F*(u→v)`. -/
def AdmissibleEps (lam : V → ℝ) (eps : ℝ) (c : V → V → ℝ) : Prop :=
  ∀ u v, 2 * epsCirc eps c u v ≤ B.edgeFlow lam 1 u v

/-- **`prop:frozen_unstable_full`, the perturbed edgeflow `F := F* − ε1_γ`**
(`proofs.tex:665`). -/
noncomputable def perturbedFlow (lam : V → ℝ) (eps : ℝ) (c : V → V → ℝ) : V → V → ℝ :=
  fun u v => B.edgeFlow lam 1 u v - epsCirc eps c u v

/-- **`prop:frozen_unstable_full`, *Admissibility*, first half** (`proofs.tex:675`): `λ > 0` and
`π̂_← > 0` give `F* > 0` on every edge of `Ĝ` — on an edge of `G` by `PositiveOnEdges`, on the
wrap edge because `π̂_←(s₀ → s_f) = 1`. -/
theorem edgeFlow_pos_of_hatEdge (hbpos : B.PositiveOnEdges) {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    {c : ℝ} (hc : 0 < c) {u v : V} (he : G.hatEdge u v) : 0 < B.edgeFlow lam c u v := by
  have hp : 0 < B.phat v u := by
    rcases he with he | ⟨hu, hv⟩
    · exact B.phat_pos_of_edge hbpos he
    · subst hu; subst hv; rw [B.phat_src_snk]; norm_num
  simp only [edgeFlow]
  exact mul_pos (mul_pos hc (hlam v)) hp

/-- **`prop:frozen_unstable_full`, *Admissibility*, second half** (`proofs.tex:675`): "`ε` is
well defined and positive". For a `1_γ` supported on the edges of `Ĝ` the witness is
`ε := ½ min_{1_γ(u→v) ≠ 0} F*(u→v)/1_γ(u→v)`, which is the statement's
`½ min_{(u→v)∈γ} F*(u→v)` when `1_γ` is `{0,1}`-valued.

The support hypothesis is where "`γ` is a directed cycle *of the graph*" enters: a circulation
riding on non-edges, where `F*` vanishes, admits no positive `ε` at all. -/
theorem exists_admissibleEps (hbpos : B.PositiveOnEdges) {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    (γ : MarkedCirculation G) (hsupp : ∀ u v, γ.circ u v ≠ 0 → G.hatEdge u v) :
    ∃ eps : ℝ, 0 < eps ∧ B.AdmissibleEps lam eps γ.circ := by
  classical
  set S : Finset (V × V) := Finset.univ.filter (fun p => γ.circ p.1 p.2 ≠ 0) with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨u0, v0, h0⟩ := γ.exists_ne_zero
    exact ⟨(u0, v0), by simp [hSdef, h0]⟩
  have hmemS : ∀ {p : V × V}, p ∈ S → γ.circ p.1 p.2 ≠ 0 := by
    intro p hp; simpa [hSdef] using hp
  set m : ℝ := S.inf' hSne (fun p => B.edgeFlow lam 1 p.1 p.2 / γ.circ p.1 p.2) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef, Finset.lt_inf'_iff]
    intro p hp
    have hne := hmemS hp
    exact div_pos (B.edgeFlow_pos_of_hatEdge hbpos hlam one_pos (hsupp _ _ hne))
      ((γ.nonneg p.1 p.2).lt_of_ne (Ne.symm hne))
  refine ⟨m / 2, by linarith, fun u v => ?_⟩
  rcases eq_or_ne (γ.circ u v) 0 with hc | hc
  · simp only [epsCirc, hc, mul_zero]
    exact B.edgeFlow_nonneg (fun x => (hlam x).le) zero_le_one u v
  · have hcpos : 0 < γ.circ u v := (γ.nonneg u v).lt_of_ne (Ne.symm hc)
    have hmem : (u, v) ∈ S := by simp [hSdef, hc]
    have hle : m ≤ B.edgeFlow lam 1 u v / γ.circ u v :=
      Finset.inf'_le (fun p => B.edgeFlow lam 1 p.1 p.2 / γ.circ p.1 p.2) hmem
    rw [le_div_iff₀ hcpos] at hle
    have heq : 2 * epsCirc (m / 2) γ.circ u v = m * γ.circ u v := by
      simp only [epsCirc]; ring
    rw [heq]
    exact hle

/-! ### The pair `(F, F₀)`: admissibility, the two marginals, and `F + F₀ = F*` -/

/-- **`prop:frozen_unstable_full`, *Admissibility*** (`proofs.tex:675`): `2ε1_γ ≤ F*` edgewise
gives `F₀ = ε1_γ ≤ F* − ε1_γ = F`. -/
theorem epsCirc_le_perturbedFlow {lam : V → ℝ} {eps : ℝ} {c : V → V → ℝ}
    (hadm : B.AdmissibleEps lam eps c) (u v : V) :
    epsCirc eps c u v ≤ B.perturbedFlow lam eps c u v := by
  have := hadm u v
  simp only [perturbedFlow]
  linarith

/-- **`F + F₀ = F*`** (`proofs.tex:678`). -/
theorem perturbedFlow_add_epsCirc (lam : V → ℝ) (eps : ℝ) (c : V → V → ℝ) :
    B.perturbedFlow lam eps c + epsCirc eps c = B.edgeFlow lam 1 := by
  funext u v
  simp only [Pi.add_apply, perturbedFlow, sub_add_cancel]

/-- **`μ_{F*} = λ`** (`proofs.tex:673`), "since the rows of `π̂_←` sum to `1`". -/
theorem edgeInflow_edgeFlow_one (lam : V → ℝ) : edgeInflow (B.edgeFlow lam 1) = lam := by
  funext v
  simpa [edgeInflow] using B.sum_edgeFlow_in lam 1 v

/-- **`μ_F = λ − ε ∂γ`** (`proofs.tex:676`). -/
theorem edgeInflow_perturbedFlow (lam : V → ℝ) (eps : ℝ) (c : V → V → ℝ) (v : V) :
    edgeInflow (B.perturbedFlow lam eps c) v = lam v - eps * edgeInflow c v := by
  have hsplit : edgeInflow (B.perturbedFlow lam eps c) v
      = edgeInflow (B.edgeFlow lam 1) v - edgeInflow (epsCirc eps c) v := by
    simp only [edgeInflow, perturbedFlow, Finset.sum_sub_distrib]
  rw [hsplit, edgeInflow_epsCirc, B.edgeInflow_edgeFlow_one]

/-- **The perturbed state flow is at least `λ/2`, hence positive.**

This is the point at which `eq_smul_invProb` — uniqueness of the invariant measure among
*non-negative* vectors — becomes applicable to `μ_F`, and the paper's `ε` hypothesis is exactly
what buys it: summing `ε 1_γ(u→v) ≤ ½ F*(u→v)` over `u` against `∑_u F*(u→v) = λ(v)` gives
`ε ∂γ(v) ≤ ½ λ(v)`. No circulation property and no sign condition on `ε` are used. -/
theorem edgeInflow_perturbedFlow_ge {lam : V → ℝ} {eps : ℝ} {c : V → V → ℝ}
    (hadm : B.AdmissibleEps lam eps c) (v : V) :
    lam v / 2 ≤ edgeInflow (B.perturbedFlow lam eps c) v := by
  have key : eps * edgeInflow c v ≤ lam v / 2 := by
    have h1 : ∀ u ∈ (Finset.univ : Finset V),
        epsCirc eps c u v ≤ B.edgeFlow lam 1 u v / 2 := by
      intro u _
      have := hadm u v
      linarith
    calc eps * edgeInflow c v = ∑ u, epsCirc eps c u v := (edgeInflow_epsCirc eps c v).symm
      _ ≤ ∑ u, B.edgeFlow lam 1 u v / 2 := Finset.sum_le_sum h1
      _ = (∑ u, B.edgeFlow lam 1 u v) / 2 := by rw [Finset.sum_div]
      _ = lam v / 2 := by rw [B.sum_edgeFlow_in lam 1 v, one_mul]
  rw [B.edgeInflow_perturbedFlow]
  linarith

/-- The total mass of the perturbed state flow, `∑ μ_F = 1 − ε ∑_v ∂γ(v)`. -/
theorem sum_edgeInflow_perturbedFlow {lam : V → ℝ} (h : B.IsInvProb lam) (eps : ℝ)
    (c : V → V → ℝ) :
    ∑ v, edgeInflow (B.perturbedFlow lam eps c) v = 1 - eps * ∑ v, edgeInflow c v := by
  simp only [B.edgeInflow_perturbedFlow, Finset.sum_sub_distrib, h.total, ← Finset.mul_sum]

/-- **`F = F* − ε1_γ` is again a `0`-flow**: `F*` is a circulation
(`theo:universality_graphs`*(3)*, `proofs.tex:995–996`) and so is `ε1_γ`. -/
theorem isCirculation_perturbedFlow {lam : V → ℝ} (h : B.IsInvProb lam) (eps : ℝ)
    {c : V → V → ℝ} (hc : IsCirculation c) : IsCirculation (B.perturbedFlow lam eps c) := by
  intro x
  have hout : edgeOutflow (B.perturbedFlow lam eps c) x
      = 1 * lam x - edgeOutflow (epsCirc eps c) x := by
    simp only [edgeOutflow, perturbedFlow, Finset.sum_sub_distrib, B.sum_edgeFlow_out h 1 x]
  have hin : edgeInflow (B.perturbedFlow lam eps c) x
      = 1 * lam x - edgeInflow (epsCirc eps c) x := by
    simp only [edgeInflow, perturbedFlow, Finset.sum_sub_distrib, B.sum_edgeFlow_in lam 1 x]
  rw [hout, hin, isCirculation_epsCirc eps hc x]

/-! ### The heart of the proposition: `μ_F` is not `π̂_←`-invariant -/

/-- **`prop:frozen_unstable_full`, the step `𝓛_{g,ν}(F) > 0` rests on** (`proofs.tex:676`):
`μ_F π̂_← ≠ μ_F`.

The paper argues that `∂γ` is not proportional to `λ` because it vanishes at `s_f` where `λ` does
not, so neither is `μ_F`, and the loop-closed chain being ergodic its invariant measures are the
multiples of `λ`. Here that uniqueness is `eq_smul_invProb`
(`theo:universality_graphs`*(2)*): were `μ_F` invariant it would be `(∑ μ_F) λ`, which at `s_f`
reads `λ(s_f) = (∑ μ_F) λ(s_f)` — because `∂γ(s_f) = 0` — hence `∑ μ_F = 1`, while
`∑ μ_F = 1 − ε ∑ ∂γ < 1`. -/
theorem not_invariant_perturbedFlow (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) (γ : MarkedCirculation G) {eps : ℝ} (heps : 0 < eps)
    (hadm : B.AdmissibleEps lam eps γ.circ) :
    ¬ ∀ y, ∑ x, edgeInflow (B.perturbedFlow lam eps γ.circ) x * B.phat x y
        = edgeInflow (B.perturbedFlow lam eps γ.circ) y := by
  intro hinv
  have hlam : ∀ x, 0 < lam x := fun x => h.pos hpc hbpos x
  set mu : V → ℝ := edgeInflow (B.perturbedFlow lam eps γ.circ) with hmu
  have hmupos : ∀ x, 0 < mu x := fun x =>
    lt_of_lt_of_le (by linarith [hlam x]) (B.edgeInflow_perturbedFlow_ge hadm x)
  have hne : mu ≠ 0 := fun hz => (hmupos G.src).ne' (congrFun hz G.src)
  obtain ⟨hsum, hray⟩ :=
    B.eq_smul_invProb hpc hbpos h (fun x => (hmupos x).le) hne hinv
  -- at the sink, `∂γ` vanishes, so `μ_F(s_f) = λ(s_f)` and the ray constant is `1`
  have hsnk : mu G.snk = lam G.snk := by
    rw [hmu, B.edgeInflow_perturbedFlow, γ.inflow_snk, mul_zero, sub_zero]
  have hone : ∑ z, mu z = 1 := by
    have := hray G.snk
    rw [hsnk] at this
    have hcancel : lam G.snk * (1 - ∑ z, mu z) = 0 := by linarith [this]
    rcases mul_eq_zero.mp hcancel with hz | hz
    · exact absurd hz (hlam G.snk).ne'
    · linarith
  -- but the total mass has dropped by `ε ∑ ∂γ > 0`
  have hdrop : ∑ z, mu z = 1 - eps * ∑ v, edgeInflow γ.circ v :=
    B.sum_edgeInflow_perturbedFlow h eps γ.circ
  have hpos : 0 < eps * ∑ v, edgeInflow γ.circ v :=
    mul_pos heps (sum_edgeInflow_pos γ.nonneg γ.ne_zero)
  rw [hone] at hdrop
  linarith

/-! ### `prop:frozen_unstable_full`, the FM half -/

/-- **`prop:frozen_unstable_full`, the FM half** (statement `proofs.tex:659–669`, proof
`proofs.tex:671–683`), in one statement.

On a finite path-connected marked graph carrying a `0`-flow `1_γ` that avoids both marks, with an
everywhere-positive frozen backward policy, `λ` an invariant probability of the loop closure, `g`
vanishing at `1` and positive elsewhere, `ν` of positive density, and `ε > 0` with `2ε1_γ ≤ F*`
edgewise:

`0 ≤ F₀`, `F₀ ≤ F`, and `𝓛_{g,ν}(F + F₀) = 0 < 𝓛_{g,ν}(F)` — so adding the `0`-subflow `F₀`
strictly *decreases* the loss, which is the failure of `eq:def_stability`.

The four conjuncts are the paper's, in its order. The DB half is not here; see the module SCOPE.
-/
theorem frozen_unstable_full_fm (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) (γ : MarkedCirculation G) {g : ℝ → ℝ} (hg1 : g 1 = 0)
    (hgpos : ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < g x) {nu : V → ℝ} (hnu : ∀ x, 0 < nu x) {eps : ℝ}
    (heps : 0 < eps) (hadm : B.AdmissibleEps lam eps γ.circ) :
    (∀ u v, 0 ≤ epsCirc eps γ.circ u v) ∧
      (∀ u v, epsCirc eps γ.circ u v ≤ B.perturbedFlow lam eps γ.circ u v) ∧
      B.fmLoss g nu
          (edgeInflow (B.perturbedFlow lam eps γ.circ + epsCirc eps γ.circ)) = 0 ∧
      0 < B.fmLoss g nu (edgeInflow (B.perturbedFlow lam eps γ.circ)) := by
  have hlam : ∀ x, 0 < lam x := fun x => h.pos hpc hbpos x
  refine ⟨epsCirc_nonneg heps.le γ.nonneg, B.epsCirc_le_perturbedFlow hadm, ?_, ?_⟩
  · rw [B.perturbedFlow_add_epsCirc, B.edgeInflow_edgeFlow_one]
    exact B.fmLoss_eq_zero hlam h.inv hg1 nu
  · set mu : V → ℝ := edgeInflow (B.perturbedFlow lam eps γ.circ) with hmu
    have hmupos : ∀ x, 0 < mu x := fun x =>
      lt_of_lt_of_le (by linarith [hlam x]) (B.edgeInflow_perturbedFlow_ge hadm x)
    obtain ⟨y, hy⟩ : ∃ y, B.stateRatio mu y ≠ 1 := by
      by_contra hc
      exact B.not_invariant_perturbedFlow hpc hbpos h γ heps hadm
        ((B.stateRatio_eq_one_iff hmupos).mp fun y => not_not.mp fun hy => hc ⟨y, hy⟩)
    exact B.fmLoss_pos (B.stateRatio_pos h hlam hmupos) hg1 hgpos hnu hy

/-! ### `rem:loop_closure_necessary`: on `G` itself the frozen family is trivial -/

/-- **`rem:loop_closure_necessary`, the backward kernel of `G` itself** (`proofs.tex:1014`):
`π_←` with the row at `s₀` emptied. `s₀` has no in-neighbour in `G`, so the paper's "`π_←` being
undefined at `s₀`" is the absence of that row; the kernel is substochastic, its rows summing to
`1` off `s₀` and to `0` at `s₀`.

This is `phat` with the wrap edge removed rather than redirected: `phat` overwrites the source
row by the point mass at `s_f`, `pcut` deletes it. -/
noncomputable def pcut : V → V → ℝ := fun s s' => if s = G.src then 0 else B.pb s s'

@[simp] theorem pcut_src (s' : V) : B.pcut G.src s' = 0 := by simp [pcut]

theorem pcut_of_ne_src {s : V} (hs : s ≠ G.src) (s' : V) : B.pcut s s' = B.pb s s' := by
  simp [pcut, hs]

theorem pcut_nonneg (s s' : V) : 0 ≤ B.pcut s s' := by
  by_cases hs : s = G.src
  · subst hs; simp
  · rw [B.pcut_of_ne_src hs]; exact B.nonneg s s'

/-- Off the source, `π_←` is a probability: `pcut` inherits `row_sum`. -/
theorem pcut_row_sum_of_ne_src {s : V} (hs : s ≠ G.src) : ∑ s', B.pcut s s' = 1 := by
  simp only [B.pcut_of_ne_src hs]
  exact B.row_sum hs

/-- At the source the row is empty: this is the deficit the marginal argument reads off. -/
theorem pcut_row_sum_src : ∑ s', B.pcut G.src s' = 0 := by simp

/-- **`rem:loop_closure_necessary`, the frozen-backward family on `G`** (`proofs.tex:1014`): the
family `Θ_{π_←}` of `theo:universality_graphs`*(2)* with `π̂_←` replaced by the kernel of `G`
itself, in the same coordinates —
`f_out(u) π_→(u → v) = π_←(v → u) f_out(v)` at every transition. -/
def CutBalance (pf : V → V → ℝ) (fout : V → ℝ) : Prop :=
  ∀ u v, fout u * pf u v = B.pcut v u * fout v

/-- The family is not empty: `f_out ≡ 0` is in it, whatever the forward policy. Together with
`loop_closure_necessary` this says the family *is* `{f_out ≡ 0}`. -/
theorem cutBalance_zero (pf : V → V → ℝ) : B.CutBalance pf 0 := by
  intro u v
  simp

/-- **`rem:loop_closure_necessary`, the marginal argument** (`proofs.tex:1014`): summing the
constraint over `v` at fixed `u`, the rows of `π_→` summing to `1`, makes `f_out μ` invariant
under `π_←`. -/
theorem cutBalance_invariant {pf : V → V → ℝ} {fout : V → ℝ} (hrow : ∀ u, ∑ v, pf u v = 1)
    (hcb : B.CutBalance pf fout) (u : V) : ∑ v, fout v * B.pcut v u = fout u := by
  have h1 : ∑ v, fout u * pf u v = ∑ v, B.pcut v u * fout v :=
    Finset.sum_congr rfl fun v _ => hcb u v
  rw [← Finset.mul_sum, hrow u, mul_one] at h1
  calc ∑ v, fout v * B.pcut v u = ∑ v, B.pcut v u * fout v :=
        Finset.sum_congr rfl fun v _ => mul_comm _ _
    _ = fout u := h1.symm

/-- **`rem:loop_closure_necessary`: the marginal argument forces `f_out(s₀) = 0`**
(`proofs.tex:1014`).

Summing the invariance identity over `u` moves the row sums of `π_←` outside: they are `1` at
every state but `s₀`, where the row is empty. So `∑_u f_out(u) = ∑_v f_out(v) − f_out(s₀)`. No
sign condition on `f_out` is used. -/
theorem cutBalance_src_eq_zero {pf : V → V → ℝ} {fout : V → ℝ} (hrow : ∀ u, ∑ v, pf u v = 1)
    (hcb : B.CutBalance pf fout) : fout G.src = 0 := by
  have hinv := B.cutBalance_invariant hrow hcb
  have key : ∑ u, fout u = ∑ v, fout v * ∑ u, B.pcut v u := by
    have h1 : ∑ u, fout u = ∑ u, ∑ v, fout v * B.pcut v u :=
      Finset.sum_congr rfl fun u _ => (hinv u).symm
    rw [h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => by rw [← Finset.mul_sum]
  have hterm : ∀ v : V,
      fout v * (∑ u, B.pcut v u) = fout v - (if v = G.src then fout v else 0) := by
    intro v
    by_cases hv : v = G.src
    · subst hv; rw [B.pcut_row_sum_src]; simp
    · rw [B.pcut_row_sum_of_ne_src hv, mul_one]; simp [hv]
  have hsplit : ∑ v, fout v * ∑ u, B.pcut v u = ∑ v, fout v - fout G.src := by
    rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_sub_distrib]
    simp
  have := key.trans hsplit
  linarith

/-- **`rem:loop_closure_necessary`: the zero propagates along the edges of `G`.**

Invariance under `π_←` reads `f_out(u) = ∑_v f_out(v) π_←(v → u)` with every term non-negative,
so `f_out(u) = 0` kills every term; and `π_←(v → u) > 0` at every out-neighbour `v` of `u`, by
`PositiveOnEdges` and because such a `v` is not the source. Induction along a walk of `G` then
carries a single zero to everything the walk reaches.

This replaces the paper's Doeblin route — leaking to `s₀` within `#𝒱` steps and iterating — on
the same hypotheses; see the module SCOPE. -/
theorem cutInvariant_step (hbpos : B.PositiveOnEdges) {fout : V → ℝ} (hnn : ∀ x, 0 ≤ fout x)
    (hinv : ∀ u, ∑ v, fout v * B.pcut v u = fout u) {u v : V} (he : G.Edge u v)
    (hu : fout u = 0) : fout v = 0 := by
  have hvsrc : v ≠ G.src := fun hvs => G.no_edge_into_src u (hvs ▸ he)
  have hppos : 0 < B.pcut v u := by
    rw [B.pcut_of_ne_src hvsrc]
    exact hbpos he
  have hz : ∑ w, fout w * B.pcut w u = 0 := by rw [hinv u, hu]
  have hle : fout v * B.pcut v u ≤ 0 := by
    rw [← hz]
    exact Finset.single_le_sum (f := fun w => fout w * B.pcut w u)
      (fun w _ => mul_nonneg (hnn w) (B.pcut_nonneg w u)) (Finset.mem_univ v)
  rcases mul_eq_zero.mp (le_antisymm hle (mul_nonneg (hnn v) (B.pcut_nonneg v u))) with h' | h'
  · exact h'
  · exact absurd h' hppos.ne'

/-- **`rem:loop_closure_necessary`: the zero propagates along a walk of `G`** — the one-step
lemma iterated along `Relation.ReflTransGen`. -/
theorem cutInvariant_eq_zero_of_reach (hbpos : B.PositiveOnEdges) {fout : V → ℝ}
    (hnn : ∀ x, 0 ≤ fout x) (hinv : ∀ u, ∑ v, fout v * B.pcut v u = fout u) {a b : V}
    (hr : G.Reach a b) (ha : fout a = 0) : fout b = 0 := by
  induction hr with
  | refl => exact ha
  | tail _ he ih => exact B.cutInvariant_step hbpos hnn hinv he ih

/-- **`rem:loop_closure_necessary`** (`proofs.tex:1014–1016`): *on `G` itself, i.e. without the
wrap edge, the frozen-backward family is trivial.*

Every member of `Θ_{π_←}` on `G` — a forward policy `π_→` with rows summing to `1`, a
non-negative outflow `f_out`, and the balance constraint against the emptied kernel `pcut` — has
`f_out ≡ 0`. With `cutBalance_zero`, the family is exactly `{f_out ≡ 0}`.

This is what makes the loop closure load-bearing: on `Ĝ` the same family is the ray
`f_out = cλ`, `c > 0` (`theo:universality_graphs`*(2)*), and the wrap edge is the only
difference. -/
theorem loop_closure_necessary (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {pf : V → V → ℝ} {fout : V → ℝ} (hrow : ∀ u, ∑ v, pf u v = 1) (hnn : ∀ x, 0 ≤ fout x)
    (hcb : B.CutBalance pf fout) : fout = 0 := by
  have hinv := B.cutBalance_invariant hrow hcb
  have hsrc := B.cutBalance_src_eq_zero hrow hcb
  funext x
  show fout x = 0
  exact B.cutInvariant_eq_zero_of_reach hbpos hnn hinv (hpc.from_src x) hsrc

end BackwardPolicy

end GFNBounds.Graph
