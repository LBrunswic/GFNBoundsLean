import GFNBounds.Balance.MassIdentity
import GFNBounds.Graph.Universality

/-!
# The edge lift: detailed balance is flow matching one step up

**`def:edge_lift`** — `proofs.tex:504–510`.
**`lem:lift_wellposed`** — statement `proofs.tex:512–513`, proof `proofs.tex:516–522`.
**`prop:db_lift`** — statement `proofs.tex:524–531`, proof `proofs.tex:533–535`.
**`lem:lift_mixing`** — statement `proofs.tex:550–551`, proof `proofs.tex:554–561`.
(The bold-backtick form of each label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (`def:edge_lift`) Let `π_←` be a backward policy on `(𝒮, λ)` with `λ` `π_←`-invariant. The
> *edge lift* of `π_←` is the Markov kernel `K₂` on `𝒮²` given by `K₂ : (s,s') ↦ (π_←(s), s)`,
> i.e. the current edge is shifted one `π_←`-step backward along the trajectory. The *edge
> measure* is `λ₂(ds ds') := π_←(s' → ds) λ(ds')`.

> (`lem:lift_wellposed`) `λ₂` is `K₂`-invariant, `K₂` is a contraction of `𝓜²(λ₂)`, and the
> `𝓜²(λ₂)`-dual of `K₂` is the edge lift `(s,s') ↦ (s', π_→^λ(s'))` of the dual forward policy
> `π_→^λ = π_←^λ`.

> (`prop:db_lift`) Let `μ ∈ 𝓜²(λ₂)` be an edge flow, let `F := m₁μ` and let `π_→^μ` be the
> disintegration `μ = F ⊗ π_→^μ`. Then for any `g` and any training distribution `ν̂` on `𝒮²`,
> `∫ g(d(μK₂)/dμ) dν̂ = ∫ g( F(ds')π_←(s'→ds) / (F(ds)π_→^μ(s→ds')) ) dν̂`, the `g`-divergence
> detailed-balance loss with frozen backward policy. In particular `μK₂ = μ` if and only if
> `(F, π_→^μ)` satisfies detailed balance with respect to `π_←`.

> (`lem:lift_mixing`) For all `n ≥ 1`, `β̂_n ≤ β_{n−1}`; for the window lift `K_ℓ`,
> `β̂_n ≤ β_{n−ℓ+1}` for `n ≥ ℓ−1`.

The engine of the whole block is one identity, `eq:muK2_density` (`proofs.tex:518–520`),

    d(μK₂)/dλ₂ (s,s') = d(m₁μ)/dλ (s'),

and it is proved first, in the division-free form `pushEdge_apply`. Everything else falls out of
it: invariance by taking `μ = λ₂`, the detailed-balance rewriting by dividing by `dμ/dλ₂`, and
the contraction by summing its square.

## Conventions

`pb x y` is `π_←(x → y)`, matching `GFNBounds.Graph.BackwardPolicy.phat`; `pf x y` is
`π_→^λ(x → y)`. The edge measure is therefore `λ₂(s,s') = pb s' s · λ(s')` — **the backward
policy is read at the second coordinate**, because `λ₂` is the law of a *backward* pair
`(s, s')` in which `s` was drawn from `s'`. The first marginal `m₁μ(s) = ∑_{s'} μ(s,s')` is the
marginal in the *first* coordinate, as `μ = F ⊗ π_→^μ` requires.

Measures on `𝒮²` and functions on `𝒮²` are both `V → V → ℝ`; which one a declaration means is
said in its docstring. `𝓜²(λ₂)` and `L²(λ₂)` are not separate types: the norms are the two
explicit sums `l2sq₂` (on densities/functions against `λ₂`) and `l2sq` (against `λ`), and the
identification of a measure with its `λ₂`-density is carried by hand, `f ↦ f · λ₂`.

## What is proved

| | |
|---|---|
| `edgeKernel`, `edgeMeasure` | `def:edge_lift` on a finite space: `K₂((s,s') → (z,w)) = [w = s]·π_←(s → z)` and `λ₂` |
| `edgeKernel_nonneg`, `edgeKernel_total` | `K₂` is a Markov kernel on `𝒮²` |
| `edgeMeasure_nonneg`, `edgeMeasure_total` | `λ₂` is a probability measure on `𝒮²` |
| `marg₁_edgeMeasure`, `marg₂_edgeMeasure` | "both marginals of `λ₂` equal `λ`" (`proofs.tex:521`) — the first needs invariance, the second only row-stochasticity |
| `pushEdge_apply` | **`eq:muK2_density`**, division-free: `(μK₂)(s,s') = π_←(s'→s)·(m₁μ)(s')` |
| `pushEdge_eq_edgeMeasure_mul` | the same as a density: `(μK₂) = λ₂ · (d(m₁μ)/dλ)(s')` wherever `λ(s') ≠ 0` |
| `pushEdge_edgeMeasure` | **`lem:lift_wellposed`, invariance**: `λ₂ K₂ = λ₂` |
| `edgeKernel_dual` | **`lem:lift_wellposed`, duality**: `λ₂ ⊗ K₂ = K₂* ⊗ λ₂` pointwise, with `K₂*((s,s') → (z,w)) = [z = s']·π_→^λ(s' → w)` |
| `inner_funActEdge` | its consequence: `⟨K₂f, g⟩_{λ₂} = ⟨f, K₂*g⟩_{λ₂}`, so `K₂*` *is* the `L²(λ₂)`-adjoint |
| `marg₁_mul_disint` | the disintegration reassembles: `F(s)·π_→^μ(s→s') = μ(s,s')`, **everywhere**, `F(s) = 0` included |
| `db_lift_ratio`, `db_lift_loss` | **`prop:db_lift`**: the lifted balance ratio *is* the edge ratio, pointwise and under `∫ · dν̂` for every `g` |
| `db_lift_iff` | **`prop:db_lift`, the "in particular"**: `μK₂ = μ ↔ (F, π_→^μ)` is in detailed balance with `π_←` |
| `pushEdge_density`, `l2sq_condFwd_le`, `edgeDensAct_contraction` | **`lem:lift_wellposed`, contraction**: the `λ₂`-density action of `K₂` is `f ↦ ((s,s') ↦ E[f(s,·) ∣ s])`, and it is an `L²(λ₂)` contraction |
| `funActEdge_apply`, `funActEdge_iterate` | `(K₂^n f)(s,s') = (P^{n−1} g_f)(s)` with `g_f(x) = ∫ f(z,x) π_←(x→dz)` (`proofs.tex:555`) |
| `edgeMean_eq_integral` | `Π₂ f = ∫ g_f dλ = ∫ f dλ₂`: `Π₂` is the mean projection of `L²(λ₂)` |
| `l2sq_condBack_le` | Jensen: `‖g_f‖_{L²(λ)} ≤ ‖f‖_{L²(λ₂)}` (`proofs.tex:555`) |
| `lift_mixing` | **`lem:lift_mixing`** as a *transfer*: every bound for `P^n − Π` on `L²(λ)` is a bound for `K₂^{n+1} − Π₂` on `L²(λ₂)` |
| `lift_mixing_opNorm`, `lift_mixing_opNorm_le` | the same read on operator norms: `β̂_{n+1} ≤ b` for every such `b`, hence `β̂_{n+1} ≤ β_n` |
| `*_graph` | all of it on the loop closure of a finite marked graph, with `π_→^λ` **reused** from `Graph.Universality.reversal` |

## SCOPE (disclosed)

* **Finite state space.** The paper states the whole block on a general `(𝒮, λ)` with `π_←` a
  Markov kernel; everything below is on a `Fintype`, with `∫ · dλ` read as `∑ x, λ x * ·`, `𝒮²`
  as `V → V → ℝ`, and `a.e.` as `∀`. This is a `⚠` row of the checklist, not a silent
  substitution. The general version needs disintegration of kernels on standard Borel spaces and
  the `L²` adjoint layer — `CLAUDE.md`'s obstruction 2, which this library has not built — while
  **every downstream consumer of the block in the paper is on a finite graph**
  (`prop:frozen_unstable_full`, `prop:morozov_rate`, `theo:global_dichotomy_full`). On a finite
  space the disintegration `π_→^μ` is the elementary quotient `μ(s,s')/F(s)`.
* **The window lift `K_ℓ`, `ℓ ≥ 3`, is not formalized.** `def:edge_lift`'s second sentence, the
  "the same holds for `K_ℓ`" of `lem:lift_wellposed`, and the second half of `lem:lift_mixing`
  (`β̂_n ≤ β_{n−ℓ+1}` for `n ≥ ℓ−1`) are **absent**. The paper defines `λ_ℓ` as "the stationary
  backward path measure of length `ℓ`", which needs a path-measure construction on `𝒮^ℓ` that
  nothing here has; the `ℓ = 2` case is what every use in the paper needs. All three labels are
  therefore **partial**, and this is the reason for two of them.
* **`lem:lift_mixing` is stated as a transfer of bounds, not as an inequality between two
  operator norms — and then as both.** The paper's `β̂_n` and `β_n` are operator norms on
  `L²(λ₂)` and `L²(λ)`; `GFNBounds.Core.Mixing.beta` defines `β_n = ‖P^n − Π‖` for a bounded
  operator on a Banach space, which is not the finite weighted-`L²` setting used here, and
  building a normed-space instance for `(V → ℝ, l2norm lam)` would be a layer of its own. What
  `lift_mixing` proves is the content of the lemma: *any* `b ≥ 0` bounding `P^n − Π` on `L²(λ)`
  bounds `K₂^{n+1} − Π₂` on `L²(λ₂)`. `opNorm` and `opNorm₂` are then defined as the infimum of
  the bounds — the operator norm, when the operator has one — and `lift_mixing_opNorm` gives
  `β̂_{n+1} ≤ b` for each such `b`. `lift_mixing_opNorm_le` gives the paper's inequality
  `β̂_{n+1} ≤ β_n` verbatim, **under the hypothesis that `β_n` is itself a bound**, i.e. that the
  infimum is attained. That is true in finite dimension and false for no reason the paper cares
  about, but it is not proved here: proving it needs a Hilbert-space structure on `(V → ℝ)` with
  the `λ`-weighted inner product, which is exactly the layer this file declines to build.
* **`β` is read on the *function* action, as the paper's own proof reads it — and the step that
  licenses that is not formalized.** `lem:lift_mixing`'s proof opens "*we work with the function
  actions, whose deviation norms coincide with those of the dual density actions*"
  (`proofs.tex:555`), and `deviation` below is accordingly `P^n − Π` for the function action
  `funAct` — `GFNBounds.Balance.MassIdentity`'s `P†`, reused. The paper's `β_n` of
  `equ:mixing_coefficients` is the operator norm of the *density* action, and the two agree
  because an operator and its `L²(λ)`-adjoint have the same norm. **That identification is
  assumed, not proved here**: it needs the Hilbert-space structure on `(V → ℝ, l2norm lam)`,
  the same layer `lift_mixing_opNorm_le` declines to build. `inner_funActEdge` is the one place
  an adjoint is actually exhibited, and it is exhibited on `𝒮²`, not on `𝒮`.
* **`cor:db_gradient` (`proofs.tex:537–548`) is not attempted.** It is a specialization of
  `theo:first_variation_full`, bucket `D` and unformalized; the same boundary
  `GFNBounds/Balance/MassIdentity.lean` records.
* **`λ > 0` is used only where it is needed, and where it is not needed it is not assumed.** The
  invariance, duality, detailed-balance and mixing results ask nothing of `λ` beyond
  `λ ≥ 0`, `λ π_← = λ` and — for `Π₂` — `∑ λ = 1`. The *density* form of `eq:muK2_density`
  (`pushEdge_eq_edgeMeasure_mul`) asks `λ(s') ≠ 0` at the point where it divides, and the
  identification of `pf` with the `λ`-reversal asks `λ > 0`, which `IsInvProb.pos` supplies.
* **`𝓜²(λ₂)`, `L²(λ₂)` and integrability carry no content.** On a `Fintype` every function is
  square-summable, so the paper's hypothesis `μ ∈ 𝓜²(λ₂)` is not carried anywhere: `μ` is an
  arbitrary `V → V → ℝ`, non-negative where non-negativity is used and unconstrained otherwise.
  The two norms below are *definitions made here*, not instances of a Mathlib norm.
* **`g` is opaque.** `db_lift_loss` holds for every `g : ℝ → ℝ` with no hypothesis at all,
  because on a finite space the two ratio expressions are equal *pointwise* before `g` is
  applied. The paper's parenthesis about the orientation of the ratio and the symmetry of `g` is
  a remark about a *different* loss and is not formalized.

## A discrepancy in the paper's proof of the contraction, recorded not repaired

`proofs.tex:521` argues the contraction as: "*since under `λ₂` the conditional law of `s` given
`s'` is `π_←(s' → ·)`, the map `dμ/dλ₂ ↦ d(m₁μ)/dλ` is a conditional expectation*". Both halves
of that sentence are true, but they are about **different conditionals**. Under `λ₂` the law of
`s` given `s'` is indeed `π_←(s' → ·)`, and averaging `dμ/dλ₂` against it produces
`d(m₂μ)/dλ` — the *second* marginal. The map that `eq:muK2_density` actually needs is
`dμ/dλ₂ ↦ d(m₁μ)/dλ`, and

    d(m₁μ)/dλ (x) = ∑_w (dμ/dλ₂)(x,w) · π_→^λ(x → w),

the conditional expectation given the **first** coordinate, taken against the **forward**
conditional `π_→^λ` — the very object the same lemma introduces one sentence later, and the one
`marg₁_smul_edgeMeasure` below computes. The conclusion is unaffected: both conditional
expectations are `L²` contractions, and the step "both marginals of `λ₂` equal `λ`", which the
paper does state, is what closes either route. The formalization takes the forward route
(`l2sq_condFwd_le`), so `edgeDensAct_contraction` carries `π_→^λ` as a hypothesis where the
paper's sentence would suggest `π_←`. Nothing in the draft is edited from here; this is a note
for the author.

The *function*-action Jensen of `lem:lift_mixing` (`proofs.tex:555`) is the other conditional and
is exactly as the paper writes it: `g_f(x) = ∫ f(z,x) π_←(x → dz)`, averaged against the backward
policy. `l2sq_condBack_le` is that step, unchanged.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, λ)` a measurable space with a finite measure | ⚠ **finite** (`[Fintype V] [DecidableEq V]`); `λ : V → ℝ`. See SCOPE |
| `π_←` a Markov kernel on `𝒮` | ✓ `hnn : ∀ x y, 0 ≤ pb x y`, `hrow : ∀ x, ∑ y, pb x y = 1`; each result carries only the half it uses |
| `λ` is `π_←`-invariant | ✓ `Invariant pb lam`, reused verbatim from `GFNBounds.Balance.MassIdentity` |
| `λ` a probability | ⚠ carried only where `Π₂` or `λ₂(𝒮²) = 1` is at stake (`edgeMeasure_total`, `edgeMean_eq_integral`); elsewhere unused |
| `K₂` the edge lift | ✓ `edgeKernel`, defined from `π_←` and proved Markov |
| `λ₂` the edge measure | ✓ `edgeMeasure`, proved a probability with both marginals `λ` |
| `μ ∈ 𝓜²(λ₂)` | ⚠ **not carried** — vacuous on a `Fintype`; `μ : V → V → ℝ` arbitrary |
| `μ ≥ 0` (an edge *flow*) | ✓ `hmu : ∀ s s', 0 ≤ μ s s'`, and it is what makes the disintegration reassemble at `F(s) = 0` |
| `F := m₁μ`, `μ = F ⊗ π_→^μ` | ✓ `marg₁`, `disint`; `marg₁_mul_disint` proves the factorization *everywhere*, junk value included |
| `π_→^λ = π_←^λ` the dual forward policy | ✓ hypothesised abstractly as `hpf : ∀ u v, λ(u)·π_→^λ(u→v) = λ(v)·π_←(v→u)` — the paper's `λ ⊗ π_→^λ = π_← ⊗ λ` — and **discharged** in the graph section by `Graph.Universality.reversal`, which is not rebuilt |
| `g` admissible / symmetric | ✗ **not carried**: `db_lift_loss` needs nothing of `g` |
| `ν̂` a training distribution on `𝒮²` | ⚠ weakened to an arbitrary `nu : V → V → ℝ`: the identity is pointwise, so no property of `ν̂` is used |
| `β_n = ‖P^n − Π‖_{L²(λ)}` an operator norm | ⚠ **a hypothesised bound** (`lift_mixing`), then an `sInf` of bounds (`opNorm`). See SCOPE |
| the window lift `K_ℓ`, `ℓ ≥ 3` | ✗ **absent**. See SCOPE |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### A rotation of three summation indices

Used once, to match the two sides of the adjoint identity after both have been expanded. -/

omit [DecidableEq V] in
/-- Moving the outermost of three summation indices to the innermost position. -/
theorem sum_rotate (F : V → V → V → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ b, ∑ c, ∑ a, F a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-! ### Marginals of a measure on `𝒮²` -/

/-- The **first marginal** `m₁μ(s) = ∑_{s'} μ(s,s')` — the marginal in the *first* coordinate,
which is what `μ = F ⊗ π_→^μ` (`proofs.tex:525`) means by `F := m₁μ`. -/
def marg₁ (mu : V → V → ℝ) : V → ℝ := fun s => ∑ s', mu s s'

/-- The **second marginal** `m₂μ(s') = ∑_s μ(s,s')`. It appears only in
`marg₂_edgeMeasure`, the second half of "both marginals of `λ₂` equal `λ`"
(`proofs.tex:521`). -/
def marg₂ (mu : V → V → ℝ) : V → ℝ := fun s' => ∑ s, mu s s'

/-! ### `def:edge_lift`: the edge lift `K₂` and the edge measure `λ₂` -/

/-- **`def:edge_lift`, the kernel** (`proofs.tex:505–508`). `K₂ : (s,s') ↦ (π_←(s), s)` is, on a
finite space, the transition matrix

    K₂((s,s') → (z,w)) = [w = s] · π_←(s → z) :

the second coordinate of the new edge is deterministically the old first coordinate, and the new
first coordinate is drawn from `π_←(s → ·)`. `pb x y` is `π_←(x → y)`. -/
def edgeKernel (pb : V → V → ℝ) (s _s' z w : V) : ℝ := if w = s then pb s z else 0

omit [Fintype V] in
/-- `K₂` is non-negative. -/
theorem edgeKernel_nonneg {pb : V → V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y) (s s' z w : V) :
    0 ≤ edgeKernel pb s s' z w := by
  unfold edgeKernel
  split
  · exact hnn s z
  · exact le_rfl

/-- `K₂` is a Markov kernel on `𝒮²`: each row sums to `1`. -/
theorem edgeKernel_total {pb : V → V → ℝ} (hrow : ∀ x, ∑ y, pb x y = 1) (s s' : V) :
    ∑ z, ∑ w, edgeKernel pb s s' z w = 1 := by
  have h : ∀ z : V, ∑ w, edgeKernel pb s s' z w = pb s z := by
    intro z
    simp [edgeKernel]
  rw [Finset.sum_congr rfl fun z _ => h z, hrow s]

/-- **`def:edge_lift`, the edge measure** (`proofs.tex:509`):
`λ₂(ds ds') := π_←(s' → ds) λ(ds')`, i.e. `λ₂(s,s') = π_←(s' → s) · λ(s')`.

The backward policy is read at the **second** coordinate: `λ₂` is the law of a backward pair, in
which `s` was drawn from `s'`. -/
def edgeMeasure (pb : V → V → ℝ) (lam : V → ℝ) : V → V → ℝ := fun s s' => pb s' s * lam s'

omit [Fintype V] [DecidableEq V] in
/-- `λ₂ ≥ 0`. -/
theorem edgeMeasure_nonneg {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hlam : ∀ x, 0 ≤ lam x) (s s' : V) : 0 ≤ edgeMeasure pb lam s s' :=
  mul_nonneg (hnn s' s) (hlam s')

omit [DecidableEq V] in
/-- **`λ₂` has second marginal `λ`** (`proofs.tex:521`, "both marginals of `λ₂` equal `λ`"). This
half is row-stochasticity of `π_←` alone; invariance is not used. -/
theorem marg₂_edgeMeasure {pb : V → V → ℝ} {lam : V → ℝ} (hrow : ∀ x, ∑ y, pb x y = 1) :
    marg₂ (edgeMeasure pb lam) = lam := by
  funext s'
  simp only [marg₂, edgeMeasure, ← Finset.sum_mul, hrow s', one_mul]

omit [DecidableEq V] in
/-- **`λ₂` has first marginal `λ`** (`proofs.tex:521`, and the "`λπ_← = λ`" of the invariance
step). This half is invariance of `λ`, and row-stochasticity is not used. -/
theorem marg₁_edgeMeasure {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Invariant pb lam) :
    marg₁ (edgeMeasure pb lam) = lam := by
  funext s
  have h : ∀ s' : V, edgeMeasure pb lam s s' = lam s' * pb s' s := fun s' => mul_comm _ _
  simp only [marg₁, Finset.sum_congr rfl fun s' (_ : s' ∈ (univ : Finset V)) => h s', hinv s]

omit [DecidableEq V] in
/-- `λ₂` is a probability measure on `𝒮²` when `λ` is one on `𝒮`. -/
theorem edgeMeasure_total {pb : V → V → ℝ} {lam : V → ℝ} (hrow : ∀ x, ∑ y, pb x y = 1)
    (htot : ∑ x, lam x = 1) : ∑ s, ∑ s', edgeMeasure pb lam s s' = 1 := by
  rw [Finset.sum_comm]
  have h : ∀ s' : V, ∑ s, edgeMeasure pb lam s s' = lam s' :=
    fun s' => congrFun (marg₂_edgeMeasure (lam := lam) hrow) s'
  rw [Finset.sum_congr rfl fun s' _ => h s', htot]

/-! ### `eq:muK2_density`: the density of `μK₂` -/

/-- The action of `K₂` on measures: `μ ↦ μK₂`, written out as
`(μK₂)(z,w) = ∑_{s,s'} μ(s,s') K₂((s,s') → (z,w))`.

`mu` here is a **measure** on `𝒮²`, given by its values against the counting structure. -/
def pushEdge (pb : V → V → ℝ) (mu : V → V → ℝ) : V → V → ℝ :=
  fun z w => ∑ s, ∑ s', mu s s' * edgeKernel pb s s' z w

/-- **`eq:muK2_density`** (`proofs.tex:517–520`), in its division-free form:

    (μK₂)(s,s') = π_←(s' → s) · (m₁μ)(s'),

which is the paper's `μK₂(ds ds') = π_←(s' → ds)(m₁μ)(ds')`. Everything in this file is a
consequence of this one line. -/
theorem pushEdge_apply (pb : V → V → ℝ) (mu : V → V → ℝ) (z w : V) :
    pushEdge pb mu z w = pb w z * marg₁ mu w := by
  have hin : ∀ s : V, ∑ s', mu s s' * edgeKernel pb s s' z w
      = (if w = s then pb s z else 0) * marg₁ mu s := by
    intro s
    simp only [edgeKernel, marg₁]
    rw [← Finset.sum_mul, mul_comm]
  rw [pushEdge, Finset.sum_congr rfl fun s (_ : s ∈ (univ : Finset V)) => hin s]
  simp

/-- **`eq:muK2_density`** as the paper writes it, as a density against `λ₂`:

    d(μK₂)/dλ₂ (s,s') = d(m₁μ)/dλ (s').

Stated multiplicatively so that no division by `λ₂(s,s')` — which may vanish — occurs; the only
hypothesis is that `λ` does not vanish at the point where `d(m₁μ)/dλ` is read. -/
theorem pushEdge_eq_edgeMeasure_mul (pb : V → V → ℝ) (lam : V → ℝ) (mu : V → V → ℝ) {s s' : V}
    (h : lam s' ≠ 0) :
    pushEdge pb mu s s' = edgeMeasure pb lam s s' * (marg₁ mu s' / lam s') := by
  rw [pushEdge_apply, edgeMeasure]
  field_simp

/-! ### `lem:lift_wellposed`, first clause: `λ₂` is `K₂`-invariant -/

/-- **`lem:lift_wellposed`, invariance** (`proofs.tex:512`, proved at `proofs.tex:521`: "taking
`μ = λ₂`, whose first marginal is `λπ_← = λ`, yields invariance"). -/
theorem pushEdge_edgeMeasure {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Invariant pb lam) :
    pushEdge pb (edgeMeasure pb lam) = edgeMeasure pb lam := by
  funext s s'
  rw [pushEdge_apply, marg₁_edgeMeasure hinv]
  rfl

/-! ### `lem:lift_wellposed`, third clause: the dual is the forward edge lift -/

/-- **`lem:lift_wellposed`, the dual kernel** (`proofs.tex:513`): the edge lift
`(s,s') ↦ (s', π_→^λ(s'))` of the dual forward policy, i.e.

    K₂*((s,s') → (z,w)) = [z = s'] · π_→^λ(s' → w).

`pf x y` is `π_→^λ(x → y)`. -/
def dualEdgeKernel (pf : V → V → ℝ) (_s s' z w : V) : ℝ := if z = s' then pf s' w else 0

omit [Fintype V] in
/-- **`lem:lift_wellposed`, the duality identity** `λ₂ ⊗ K₂* = K₂ ⊗ λ₂` (`proofs.tex:521`), read
pointwise on a finite space:

    λ₂(s,s') · K₂((s,s') → (z,w)) = λ₂(z,w) · K₂*((z,w) → (s,s')).

Its only input is the defining identity `λ ⊗ π_→^λ = π_← ⊗ λ` of the dual forward policy, which
`hpf` states in coordinates. Both sides vanish unless `w = s`, and there it is `hpf` at `(s,s')`
multiplied by `π_←(s → z)`. -/
theorem edgeKernel_dual {pb pf : V → V → ℝ} {lam : V → ℝ}
    (hpf : ∀ u v, lam u * pf u v = lam v * pb v u) (s s' z w : V) :
    edgeMeasure pb lam s s' * edgeKernel pb s s' z w
      = edgeMeasure pb lam z w * dualEdgeKernel pf z w s s' := by
  by_cases h : w = s
  · subst h
    simp only [edgeKernel, dualEdgeKernel, edgeMeasure, if_true]
    rw [show pb s' w * lam s' * pb w z = pb w z * (lam s' * pb s' w) by ring, ← hpf w s']
    ring
  · have h' : ¬ s = w := fun hc => h hc.symm
    simp [edgeKernel, dualEdgeKernel, h, h']

/-- The action of `K₂` on **functions**: `(K₂f)(s,s') = ∑_{z,w} K₂((s,s') → (z,w)) f(z,w)`. -/
def funActEdge (pb : V → V → ℝ) (f : V → V → ℝ) : V → V → ℝ :=
  fun s s' => ∑ z, ∑ w, edgeKernel pb s s' z w * f z w

/-- `(K₂f)(s,s') = ∫ f(z,s) π_←(s → dz)`: the value depends on `s` alone, the new second
coordinate being the old first one. -/
theorem funActEdge_apply (pb : V → V → ℝ) (f : V → V → ℝ) (s s' : V) :
    funActEdge pb f s s' = ∑ z, pb s z * f z s := by
  refine Finset.sum_congr rfl fun z _ => ?_
  have h : ∀ w : V, edgeKernel pb s s' z w * f z w = if w = s then pb s z * f z w else 0 := by
    intro w; unfold edgeKernel; split <;> simp
  rw [Finset.sum_congr rfl fun w (_ : w ∈ (univ : Finset V)) => h w]
  simp

/-- The action of `K₂*` on functions. -/
def dualFunActEdge (pf : V → V → ℝ) (f : V → V → ℝ) : V → V → ℝ :=
  fun s s' => ∑ z, ∑ w, dualEdgeKernel pf s s' z w * f z w

/-- `(K₂*f)(s,s') = ∫ f(s',w) π_→^λ(s' → dw)`. -/
theorem dualFunActEdge_apply (pf : V → V → ℝ) (f : V → V → ℝ) (s s' : V) :
    dualFunActEdge pf f s s' = ∑ w, pf s' w * f s' w := by
  have h : ∀ z : V, ∑ w, dualEdgeKernel pf s s' z w * f z w
      = if z = s' then ∑ w, pf s' w * f z w else 0 := by
    intro z
    unfold dualEdgeKernel
    split
    · rfl
    · simp
  rw [dualFunActEdge, Finset.sum_congr rfl fun z (_ : z ∈ (univ : Finset V)) => h z]
  simp

/-- **`lem:lift_wellposed`, the dual clause in its `L²(λ₂)` form**:
`⟨K₂ f, g⟩_{λ₂} = ⟨f, K₂* g⟩_{λ₂}`, so the edge lift of the dual forward policy *is* the
adjoint. It is `edgeKernel_dual` summed, after both sides are expanded by `funActEdge_apply`
and `dualFunActEdge_apply` and the three surviving indices are rotated. -/
theorem inner_funActEdge {pb pf : V → V → ℝ} {lam : V → ℝ}
    (hpf : ∀ u v, lam u * pf u v = lam v * pb v u) (f g : V → V → ℝ) :
    ∑ s, ∑ s', edgeMeasure pb lam s s' * funActEdge pb f s s' * g s s'
      = ∑ s, ∑ s', edgeMeasure pb lam s s' * f s s' * dualFunActEdge pf g s s' := by
  have hL : ∀ s s' : V, edgeMeasure pb lam s s' * funActEdge pb f s s' * g s s'
      = ∑ z, lam s' * pb s' s * pb s z * f z s * g s s' := by
    intro s s'
    rw [funActEdge_apply, edgeMeasure, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hR : ∀ s s' : V, edgeMeasure pb lam s s' * f s s' * dualFunActEdge pf g s s'
      = ∑ w, lam w * pb w s' * pb s' s * f s s' * g s' w := by
    intro s s'
    rw [dualFunActEdge_apply, edgeMeasure, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [show pb s' s * lam s' * f s s' * (pf s' w * g s' w)
        = lam s' * pf s' w * (pb s' s * f s s' * g s' w) by ring, hpf s' w]
    ring
  simp only [Finset.sum_congr rfl fun s (_ : s ∈ (univ : Finset V)) =>
    Finset.sum_congr rfl fun s' (_ : s' ∈ (univ : Finset V)) => hL s s',
    Finset.sum_congr rfl fun s (_ : s ∈ (univ : Finset V)) =>
    Finset.sum_congr rfl fun s' (_ : s' ∈ (univ : Finset V)) => hR s s']
  exact (sum_rotate (fun x y z => lam z * pb z y * pb y x * f x y * g y z)).symm

/-! ### `prop:db_lift`: the disintegration, and detailed balance -/

/-- The **disintegration** `π_→^μ` of an edge flow: `π_→^μ(s → s') = μ(s,s')/F(s)` with
`F = m₁μ` (`proofs.tex:525`). Where `F(s) = 0` this is Lean's `x/0 = 0`; `marg₁_mul_disint`
shows the junk value is harmless. -/
noncomputable def disint (mu : V → V → ℝ) : V → V → ℝ := fun s s' => mu s s' / marg₁ mu s

omit [DecidableEq V] in
/-- **The disintegration reassembles, everywhere**: `F(s) · π_→^μ(s → s') = μ(s,s')` for every
`(s,s')`, with no positivity hypothesis on `F`.

This is how the file handles `F(s) = 0`, which the paper does not discuss: at such an `s` a
non-negative `μ` has `∑_{s'} μ(s,s') = 0`, hence `μ(s,s') = 0` for every `s'`, and both sides
vanish. So `μ = F ⊗ π_→^μ` holds as an identity of functions and no statement below has to
exclude the null part of `F`. -/
theorem marg₁_mul_disint {mu : V → V → ℝ} (hmu : ∀ s s', 0 ≤ mu s s') (s s' : V) :
    marg₁ mu s * disint mu s s' = mu s s' := by
  by_cases h : marg₁ mu s = 0
  · have hz : mu s s' = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun x (_ : x ∈ (univ : Finset V)) =>
        hmu s x).mp h s' (mem_univ s')
      exact this
    rw [h, hz, zero_mul]
  · rw [disint, mul_div_cancel₀ _ h]

/-- **Detailed balance of `(F, π_→)` with respect to `π_←`** (`proofs.tex:530`):
`F(s) π_→(s → s') = F(s') π_←(s' → s)` at every pair. -/
def DetailedBalance (pb : V → V → ℝ) (F : V → ℝ) (pf : V → V → ℝ) : Prop :=
  ∀ s s', F s * pf s s' = F s' * pb s' s

/-- **`prop:db_lift`, the ratio identity** (`proofs.tex:534`): the lifted balance ratio
`d(μK₂)/dμ` *is* the detailed-balance edge ratio

    F(s') π_←(s' → s) / (F(s) π_→^μ(s → s')).

Pointwise, before any `g` or any `ν̂`: on a finite space the numerators and the denominators
agree term by term, `pushEdge_apply` giving the one and `marg₁_mul_disint` the other. -/
theorem db_lift_ratio {pb : V → V → ℝ} {mu : V → V → ℝ} (hmu : ∀ s s', 0 ≤ mu s s') (s s' : V) :
    pushEdge pb mu s s' / mu s s'
      = marg₁ mu s' * pb s' s / (marg₁ mu s * disint mu s s') := by
  rw [pushEdge_apply, marg₁_mul_disint hmu, mul_comm (pb s' s) (marg₁ mu s')]

/-- **`prop:db_lift`, the loss identity** (`proofs.tex:526–529`): for **any** `g` and any
training distribution `ν̂` on `𝒮²`,

    ∫ g(d(μK₂)/dμ) dν̂ = ∫ g( F(ds')π_←(s'→ds) / (F(ds)π_→^μ(s→ds')) ) dν̂,

the `g`-divergence detailed-balance loss with frozen backward policy. No hypothesis on `g` and
none on `ν̂`: `db_lift_ratio` equates the arguments pointwise. -/
theorem db_lift_loss {pb : V → V → ℝ} {mu : V → V → ℝ} (hmu : ∀ s s', 0 ≤ mu s s')
    (g : ℝ → ℝ) (nu : V → V → ℝ) :
    ∑ s, ∑ s', nu s s' * g (pushEdge pb mu s s' / mu s s')
      = ∑ s, ∑ s', nu s s' * g (marg₁ mu s' * pb s' s / (marg₁ mu s * disint mu s s')) :=
  Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by
    rw [db_lift_ratio hmu s s']

/-- **`prop:db_lift`, the "in particular"** (`proofs.tex:530`): `μK₂ = μ` if and only if
`(F, π_→^μ)` satisfies detailed balance with respect to `π_←`.

Both sides are the same pair of pointwise equations: `μK₂ = μ` reads
`π_←(s'→s)·F(s') = μ(s,s')`, and `μ(s,s') = F(s)·π_→^μ(s→s')` by `marg₁_mul_disint`. -/
theorem db_lift_iff {pb : V → V → ℝ} {mu : V → V → ℝ} (hmu : ∀ s s', 0 ≤ mu s s') :
    pushEdge pb mu = mu ↔ DetailedBalance pb (marg₁ mu) (disint mu) := by
  constructor
  · intro h s s'
    have hss := congrFun (congrFun h s) s'
    rw [pushEdge_apply] at hss
    rw [marg₁_mul_disint hmu, ← hss]
    ring
  · intro h
    funext s s'
    rw [pushEdge_apply, ← marg₁_mul_disint hmu s s', h s s']
    ring

/-! ### The two weighted `L²` norms -/

/-- `‖f‖²_{L²(λ)} = ∑_x λ(x) f(x)²`, the finite-space reading of the paper's `L²(λ)` norm. A
definition made here: no Mathlib norm instance is involved. -/
def l2sq (w f : V → ℝ) : ℝ := ∑ x, w x * f x ^ 2

/-- `‖f‖²_{L²(λ₂)} = ∑_{s,s'} λ₂(s,s') f(s,s')²`. -/
def l2sq₂ (w f : V → V → ℝ) : ℝ := ∑ s, ∑ s', w s s' * f s s' ^ 2

/-- `‖f‖_{L²(λ)}`. -/
noncomputable def l2norm (w f : V → ℝ) : ℝ := Real.sqrt (l2sq w f)

/-- `‖f‖_{L²(λ₂)}`. -/
noncomputable def l2norm₂ (w f : V → V → ℝ) : ℝ := Real.sqrt (l2sq₂ w f)

omit [DecidableEq V] in
/-- **Jensen against a probability weight**: `(∑ p φ)² ≤ ∑ p φ²` when `p ≥ 0` and `∑ p = 1`.
This is the one inequality both contraction arguments run on. -/
theorem sq_sum_le_sum_sq {p φ : V → ℝ} (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) :
    (∑ z, p z * φ z) ^ 2 ≤ ∑ z, p z * φ z ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset V)
    (r := fun z => p z * φ z) (f := p) (g := fun z => p z * φ z ^ 2)
    (fun z _ => hp z) (fun z _ => mul_nonneg (hp z) (sq_nonneg _))
    (fun z _ => le_of_eq (by ring))
  rwa [hp1, one_mul] at h

/-! ### `lem:lift_wellposed`, second clause: `K₂` is a contraction of `𝓜²(λ₂)` -/

/-- The **forward** conditional expectation `(E f)(x) = ∫ f(x,w) π_→^λ(x → dw)`, the average of
`f` over the second coordinate given the first, under `λ₂`. -/
def condFwd (pf : V → V → ℝ) (f : V → V → ℝ) : V → ℝ := fun x => ∑ w, pf x w * f x w

omit [DecidableEq V] in
/-- `d(m₁(f λ₂))/dλ = E f` — the first marginal of the measure with `λ₂`-density `f` is
`λ · (E f)`, the average of `f` against the **forward** conditional. This is the computation the
paper's contraction step needs; see the module's note on the discrepancy. -/
theorem marg₁_smul_edgeMeasure {pb pf : V → V → ℝ} {lam : V → ℝ}
    (hpf : ∀ u v, lam u * pf u v = lam v * pb v u) (f : V → V → ℝ) (x : V) :
    marg₁ (fun s s' => f s s' * edgeMeasure pb lam s s') x = lam x * condFwd pf f x := by
  rw [marg₁, condFwd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [edgeMeasure]
  rw [show f x w * (pb w x * lam w) = lam w * pb w x * f x w by ring, ← hpf x w]
  ring

/-- **The `λ₂`-density action of `K₂`**: if `μ = f λ₂` then `μK₂ = ((s,s') ↦ (E f)(s')) λ₂`.
This is `eq:muK2_density` written on densities, and it is what the contraction is about. -/
theorem pushEdge_density {pb pf : V → V → ℝ} {lam : V → ℝ}
    (hpf : ∀ u v, lam u * pf u v = lam v * pb v u) (f : V → V → ℝ) (s s' : V) :
    pushEdge pb (fun a b => f a b * edgeMeasure pb lam a b) s s'
      = edgeMeasure pb lam s s' * condFwd pf f s' := by
  rw [pushEdge_apply, marg₁_smul_edgeMeasure hpf, edgeMeasure]
  ring

omit [DecidableEq V] in
/-- **Jensen for the forward conditional**: `‖E f‖_{L²(λ)} ≤ ‖f‖_{L²(λ₂)}`, squared. -/
theorem l2sq_condFwd_le {pb pf : V → V → ℝ} {lam : V → ℝ}
    (hpfnn : ∀ u v, 0 ≤ pf u v) (hpfrow : ∀ u, ∑ v, pf u v = 1)
    (hpf : ∀ u v, lam u * pf u v = lam v * pb v u) (hlam : ∀ x, 0 ≤ lam x) (f : V → V → ℝ) :
    l2sq lam (condFwd pf f) ≤ l2sq₂ (edgeMeasure pb lam) f := by
  have step : ∀ x : V, lam x * condFwd pf f x ^ 2 ≤ ∑ w, edgeMeasure pb lam x w * f x w ^ 2 := by
    intro x
    have hj : condFwd pf f x ^ 2 ≤ ∑ w, pf x w * f x w ^ 2 :=
      sq_sum_le_sum_sq (fun z => hpfnn x z) (hpfrow x)
    have h1 : lam x * condFwd pf f x ^ 2 ≤ lam x * ∑ w, pf x w * f x w ^ 2 :=
      mul_le_mul_of_nonneg_left hj (hlam x)
    refine h1.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have := hpf x w
    simp only [edgeMeasure]
    nlinarith [this]
  calc l2sq lam (condFwd pf f) ≤ ∑ x, ∑ w, edgeMeasure pb lam x w * f x w ^ 2 :=
        Finset.sum_le_sum fun x _ => step x
    _ = l2sq₂ (edgeMeasure pb lam) f := rfl

omit [DecidableEq V] in
/-- **`lem:lift_wellposed`, the contraction** (`proofs.tex:512`, proved at `proofs.tex:521`):
`‖μK₂‖_{𝓜²(λ₂)} ≤ ‖μ‖_{𝓜²(λ₂)}`, read on `λ₂`-densities and squared.

The two ingredients are the paper's: the second marginal of `λ₂` is `λ`, which collapses the
`λ₂`-norm of a function of the second coordinate to a `λ`-norm; and Jensen for the conditional
expectation, `l2sq_condFwd_le`. -/
theorem edgeDensAct_contraction {pb pf : V → V → ℝ} {lam : V → ℝ}
    (hrow : ∀ x, ∑ y, pb x y = 1) (hpfnn : ∀ u v, 0 ≤ pf u v) (hpfrow : ∀ u, ∑ v, pf u v = 1)
    (hpf : ∀ u v, lam u * pf u v = lam v * pb v u) (hlam : ∀ x, 0 ≤ lam x) (f : V → V → ℝ) :
    l2sq₂ (edgeMeasure pb lam) (fun _ s' => condFwd pf f s')
      ≤ l2sq₂ (edgeMeasure pb lam) f := by
  have hcollapse : l2sq₂ (edgeMeasure pb lam) (fun _ s' => condFwd pf f s')
      = l2sq lam (condFwd pf f) := by
    rw [l2sq₂, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    have h : ∀ s : V, edgeMeasure pb lam s s' * condFwd pf f s' ^ 2
        = pb s' s * (lam s' * condFwd pf f s' ^ 2) := fun s => by
      simp only [edgeMeasure]; ring
    rw [Finset.sum_congr rfl fun s (_ : s ∈ (univ : Finset V)) => h s, ← Finset.sum_mul,
      hrow s', one_mul]
  rw [hcollapse]
  exact l2sq_condFwd_le hpfnn hpfrow hpf hlam f

omit [DecidableEq V] in
/-- The contraction in norm form: `‖K₂ f‖_{L²(λ₂)} ≤ ‖f‖_{L²(λ₂)}`. -/
theorem edgeDensAct_contraction_norm {pb pf : V → V → ℝ} {lam : V → ℝ}
    (hrow : ∀ x, ∑ y, pb x y = 1) (hpfnn : ∀ u v, 0 ≤ pf u v) (hpfrow : ∀ u, ∑ v, pf u v = 1)
    (hpf : ∀ u v, lam u * pf u v = lam v * pb v u) (hlam : ∀ x, 0 ≤ lam x) (f : V → V → ℝ) :
    l2norm₂ (edgeMeasure pb lam) (fun _ s' => condFwd pf f s')
      ≤ l2norm₂ (edgeMeasure pb lam) f :=
  Real.sqrt_le_sqrt (edgeDensAct_contraction hrow hpfnn hpfrow hpf hlam f)

/-! ### `lem:lift_mixing`: the mixing transfer -/

/-- The **backward** conditional `g_f(x) := ∫ f(z,x) π_←(x → dz)` of `proofs.tex:555`. -/
def condBack (pb : V → V → ℝ) (f : V → V → ℝ) : V → ℝ := fun x => ∑ z, pb x z * f z x

/-- `(K₂ f)(s,s') = g_f(s)`, the `n = 1` case of `proofs.tex:555`. -/
theorem funActEdge_eq_condBack (pb : V → V → ℝ) (f : V → V → ℝ) :
    funActEdge pb f = fun s _ => condBack pb f s := by
  funext s s'
  rw [funActEdge_apply]
  rfl

/-- **`(K₂^n f)(s,s') = (P^{n−1} g_f)(s)`** (`proofs.tex:555`), where `P` is the function action
of `π_←` — `GFNBounds.Balance.funAct`, reused from `MassIdentity`. Written with `n = m + 1` so
that `n ≥ 1` is carried by the type. -/
theorem funActEdge_iterate (pb : V → V → ℝ) (f : V → V → ℝ) (m : ℕ) :
    (funActEdge pb)^[m + 1] f = fun s _ => (funAct pb)^[m] (condBack pb f) s := by
  induction m with
  | zero => simpa using funActEdge_eq_condBack pb f
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext s s'
      rw [funActEdge_apply, Function.iterate_succ_apply']
      rfl

/-- `Π₂ f = ∫ g_f dλ` (`proofs.tex:555`), the mean projection of `L²(λ₂)`. -/
def edgeMean (pb : V → V → ℝ) (lam : V → ℝ) (f : V → V → ℝ) : ℝ :=
  ∑ x, lam x * condBack pb f x

omit [DecidableEq V] in
/-- `Π₂ f = ∫ f dλ₂`: the paper's `∫ g_f dλ` really is the mean of `f` against the edge
measure. -/
theorem edgeMean_eq_integral (pb : V → V → ℝ) (lam : V → ℝ) (f : V → V → ℝ) :
    edgeMean pb lam f = ∑ s, ∑ s', edgeMeasure pb lam s s' * f s s' := by
  rw [edgeMean, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [condBack, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by simp only [edgeMeasure]; ring

omit [DecidableEq V] in
/-- A function of the **first** coordinate has the same `L²(λ₂)` norm as its `L²(λ)` norm: the
first marginal of `λ₂` is `λ` (`marg₁_edgeMeasure`, which is where invariance enters). -/
theorem l2sq₂_of_fst {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Invariant pb lam) (G : V → ℝ) :
    l2sq₂ (edgeMeasure pb lam) (fun s _ => G s) = l2sq lam G := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_mul]
  exact congrArg (· * G s ^ 2) (congrFun (marg₁_edgeMeasure hinv) s)

omit [DecidableEq V] in
/-- **Jensen for the backward conditional** (`proofs.tex:555`):
`‖g_f‖_{L²(λ)} ≤ ‖f‖_{L²(λ₂)}`, squared. This is the paper's step verbatim. -/
theorem l2sq_condBack_le {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) (hlam : ∀ x, 0 ≤ lam x) (f : V → V → ℝ) :
    l2sq lam (condBack pb f) ≤ l2sq₂ (edgeMeasure pb lam) f := by
  have hle : ∀ x : V, lam x * condBack pb f x ^ 2 ≤ ∑ z, edgeMeasure pb lam z x * f z x ^ 2 := by
    intro x
    simp only [condBack]
    have hj : (∑ z, pb x z * f z x) ^ 2 ≤ ∑ z, pb x z * f z x ^ 2 :=
      sq_sum_le_sum_sq (fun z => hnn x z) (hrow x)
    have h1 : lam x * (∑ z, pb x z * f z x) ^ 2 ≤ lam x * ∑ z, pb x z * f z x ^ 2 :=
      mul_le_mul_of_nonneg_left hj (hlam x)
    refine h1.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by simp only [edgeMeasure]; ring
  calc l2sq lam (condBack pb f) ≤ ∑ x, ∑ z, edgeMeasure pb lam z x * f z x ^ 2 :=
        Finset.sum_le_sum fun x _ => hle x
    _ = l2sq₂ (edgeMeasure pb lam) f := Finset.sum_comm

/-- `K₂^n − Π₂` on `L²(λ₂)`, whose operator norm is the paper's `β̂_n`. -/
noncomputable def edgeDeviation (pb : V → V → ℝ) (lam : V → ℝ) (n : ℕ) (f : V → V → ℝ) :
    V → V → ℝ :=
  fun s s' => (funActEdge pb)^[n] f s s' - edgeMean pb lam f

/-- `P^n − Π` on `L²(λ)`, whose operator norm is the paper's `β_n`. -/
noncomputable def deviation (pb : V → V → ℝ) (lam : V → ℝ) (n : ℕ) (g : V → ℝ) : V → ℝ :=
  fun x => (funAct pb)^[n] g x - ∑ y, lam y * g y

/-- **`lem:lift_mixing`** (`proofs.tex:550–551`, proof `proofs.tex:554–561`), as the transfer of
bounds it is:

> every `b ≥ 0` with `‖(P^n − Π) g‖_{L²(λ)} ≤ b ‖g‖_{L²(λ)}` for all `g` also satisfies
> `‖(K₂^{n+1} − Π₂) f‖_{L²(λ₂)} ≤ b ‖f‖_{L²(λ₂)}` for all `f`,

which read on the least such `b` is `β̂_{n+1} ≤ β_n`, i.e. the paper's `β̂_n ≤ β_{n−1}` for
`n ≥ 1`. See the module SCOPE for why the operator norms are not the primitive here.

The proof is the paper's three steps: `funActEdge_iterate` turns `K₂^{n+1} f − Π₂ f` into a
function of the first coordinate alone; `l2sq₂_of_fst` moves that to `L²(λ)`, the first marginal
of `λ₂` being `λ`; and `l2sq_condBack_le` is Jensen. -/
theorem lift_mixing {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) (hlam : ∀ x, 0 ≤ lam x) (hinv : Invariant pb lam)
    {b : ℝ} (hb : 0 ≤ b) {n : ℕ}
    (hbeta : ∀ g : V → ℝ, l2norm lam (deviation pb lam n g) ≤ b * l2norm lam g)
    (f : V → V → ℝ) :
    l2norm₂ (edgeMeasure pb lam) (edgeDeviation pb lam (n + 1) f)
      ≤ b * l2norm₂ (edgeMeasure pb lam) f := by
  set G : V → ℝ := condBack pb f with hG
  have hshape : edgeDeviation pb lam (n + 1) f = fun s _ => deviation pb lam n G s := by
    funext s s'
    rw [edgeDeviation, funActEdge_iterate, deviation, edgeMean]
  have hnorm : l2norm₂ (edgeMeasure pb lam) (edgeDeviation pb lam (n + 1) f)
      = l2norm lam (deviation pb lam n G) := by
    rw [hshape, l2norm₂, l2norm, l2sq₂_of_fst hinv]
  have hjensen : l2norm lam G ≤ l2norm₂ (edgeMeasure pb lam) f :=
    Real.sqrt_le_sqrt (l2sq_condBack_le hnn hrow hlam f)
  rw [hnorm]
  exact (hbeta G).trans (mul_le_mul_of_nonneg_left hjensen hb)

/-! ### The same, read on operator norms -/

/-- `b` is an operator-norm bound for `A` on `L²(λ)`. -/
def OpBound (w : V → ℝ) (A : (V → ℝ) → (V → ℝ)) (b : ℝ) : Prop :=
  0 ≤ b ∧ ∀ g, l2norm w (A g) ≤ b * l2norm w g

/-- `b` is an operator-norm bound for `A` on `L²(λ₂)`. -/
def OpBound₂ (w : V → V → ℝ) (A : (V → V → ℝ) → (V → V → ℝ)) (b : ℝ) : Prop :=
  0 ≤ b ∧ ∀ f, l2norm₂ w (A f) ≤ b * l2norm₂ w f

/-- The operator norm on `L²(λ)`, as the infimum of the bounds. -/
noncomputable def opNorm (w : V → ℝ) (A : (V → ℝ) → (V → ℝ)) : ℝ := sInf {b | OpBound w A b}

/-- The operator norm on `L²(λ₂)`, as the infimum of the bounds — the paper's `β̂_n` at
`A = K₂^n − Π₂`. -/
noncomputable def opNorm₂ (w : V → V → ℝ) (A : (V → V → ℝ) → (V → V → ℝ)) : ℝ :=
  sInf {b | OpBound₂ w A b}

omit [DecidableEq V] in
/-- The set of bounds is bounded below by `0`, which is all `csInf_le` needs. -/
theorem bddBelow_opBound₂ (w : V → V → ℝ) (A : (V → V → ℝ) → (V → V → ℝ)) :
    BddBelow {b | OpBound₂ w A b} := ⟨0, fun _ hb => hb.1⟩

/-- **`lem:lift_mixing` on the operator norm**: `β̂_{n+1} ≤ b` for every bound `b` of
`P^n − Π`. -/
theorem lift_mixing_opNorm {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) (hlam : ∀ x, 0 ≤ lam x) (hinv : Invariant pb lam)
    {b : ℝ} {n : ℕ} (hbeta : OpBound lam (deviation pb lam n) b) :
    opNorm₂ (edgeMeasure pb lam) (edgeDeviation pb lam (n + 1)) ≤ b :=
  csInf_le (bddBelow_opBound₂ _ _)
    ⟨hbeta.1, fun f => lift_mixing hnn hrow hlam hinv hbeta.1 hbeta.2 f⟩

/-- **`lem:lift_mixing` verbatim**: `β̂_{n+1} ≤ β_n`, i.e. the paper's `β̂_n ≤ β_{n−1}` for
`n ≥ 1`.

The one hypothesis beyond the paper's is `hattained`: that `β_n`, defined as the infimum of the
bounds, is itself a bound. In finite dimension it is — the infimum of a non-empty closed set of
bounds is attained — but proving that needs the Hilbert-space structure on `(V → ℝ, l2norm lam)`
that this file declines to build; see the module SCOPE. -/
theorem lift_mixing_opNorm_le {pb : V → V → ℝ} {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y)
    (hrow : ∀ x, ∑ y, pb x y = 1) (hlam : ∀ x, 0 ≤ lam x) (hinv : Invariant pb lam) {n : ℕ}
    (hattained : OpBound lam (deviation pb lam n) (opNorm lam (deviation pb lam n))) :
    opNorm₂ (edgeMeasure pb lam) (edgeDeviation pb lam (n + 1))
      ≤ opNorm lam (deviation pb lam n) :=
  lift_mixing_opNorm hnn hrow hlam hinv hattained

/-! ### On the loop closure of a finite marked graph

Everything above is stated for an abstract kernel `pb` with an invariant `lam` and an abstract
dual `pf` satisfying `λ ⊗ π_→^λ = π_← ⊗ λ`. This section discharges all three on the backward
chain of a finite path-connected marked graph, taking `π_→^λ` to be
`GFNBounds.Graph.BackwardPolicy.reversal` — **the paper's `π_→^λ = π_←^λ` of
`theo:universality_graphs`*(2)*, already built and already proved a Markov kernel there.** It is
not rebuilt here; only the defining identity is checked against it. -/

section MarkedGraph

open GFNBounds.Graph

variable {G : MarkedGraph V} {B : BackwardPolicy G}

/-- **`Graph.Universality.reversal` is the paper's dual forward policy**: `λ ⊗ π_→^λ = π_← ⊗ λ`
in coordinates, `λ(u)·π_→^λ(u → v) = λ(v)·π̂_←(v → u)`.

This is the only thing the abstract results above ask of `pf`, and it is the definition of
`reversal` cleared of its denominator — legitimate because `λ > 0`, which `IsInvProb.pos`
supplies from path-connectedness and positivity on edges. -/
theorem lam_mul_reversal {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (u v : V) :
    lam u * B.reversal lam u v = lam v * B.phat v u := by
  rw [BackwardPolicy.reversal, mul_div_cancel₀ _ (hlam u).ne']

/-- **`lem:lift_wellposed`, invariance, on a marked graph.** -/
theorem pushEdge_edgeMeasure_graph {lam : V → ℝ} (h : B.IsInvProb lam) :
    pushEdge B.phat (edgeMeasure B.phat lam) = edgeMeasure B.phat lam :=
  pushEdge_edgeMeasure (invariant_of_isInvProb h)

/-- **`lem:lift_wellposed`, the duality identity, on a marked graph**, with the dual kernel built
from `Graph.Universality.reversal`. -/
theorem edgeKernel_dual_graph (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (h : B.IsInvProb lam) (s s' z w : V) :
    edgeMeasure B.phat lam s s' * edgeKernel B.phat s s' z w
      = edgeMeasure B.phat lam z w * dualEdgeKernel (B.reversal lam) z w s s' :=
  edgeKernel_dual (lam_mul_reversal (h.pos hpc hpos)) s s' z w

/-- **`lem:lift_wellposed`, the adjoint, on a marked graph**: the edge lift of the `λ`-reversal
is the `L²(λ₂)`-adjoint of `K₂`. -/
theorem inner_funActEdge_graph (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (h : B.IsInvProb lam) (f g : V → V → ℝ) :
    ∑ s, ∑ s', edgeMeasure B.phat lam s s' * funActEdge B.phat f s s' * g s s'
      = ∑ s, ∑ s', edgeMeasure B.phat lam s s' * f s s'
          * dualFunActEdge (B.reversal lam) g s s' :=
  inner_funActEdge (lam_mul_reversal (h.pos hpc hpos)) f g

/-- **`lem:lift_wellposed`, the contraction, on a marked graph.** The three properties of the
reversal it needs — non-negativity, row sums `1`, and the defining identity — are
`reversal_nonneg`, `sum_reversal` and `lam_mul_reversal`; none is rebuilt. -/
theorem edgeDensAct_contraction_graph (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) (f : V → V → ℝ) :
    l2sq₂ (edgeMeasure B.phat lam) (fun _ s' => condFwd (B.reversal lam) f s')
      ≤ l2sq₂ (edgeMeasure B.phat lam) f :=
  edgeDensAct_contraction B.phat_row_sum
    (B.reversal_nonneg fun x => (h.pos hpc hpos x).le)
    (fun u => B.sum_reversal h (h.pos hpc hpos u).ne')
    (lam_mul_reversal (h.pos hpc hpos)) (fun x => h.nonneg x) f

/-- **`prop:db_lift`, the "in particular", on a marked graph**: an edge flow is `K₂`-invariant
exactly when its first marginal and its disintegration are in detailed balance with the frozen
backward policy. -/
theorem db_lift_iff_graph {mu : V → V → ℝ} (hmu : ∀ s s', 0 ≤ mu s s') :
    pushEdge B.phat mu = mu ↔ DetailedBalance B.phat (marg₁ mu) (disint mu) :=
  db_lift_iff hmu

/-- **`lem:lift_mixing` on a marked graph.** -/
theorem lift_mixing_graph {lam : V → ℝ} (h : B.IsInvProb lam) {b : ℝ} (hb : 0 ≤ b) {n : ℕ}
    (hbeta : ∀ g : V → ℝ, l2norm lam (deviation B.phat lam n g) ≤ b * l2norm lam g)
    (f : V → V → ℝ) :
    l2norm₂ (edgeMeasure B.phat lam) (edgeDeviation B.phat lam (n + 1) f)
      ≤ b * l2norm₂ (edgeMeasure B.phat lam) f :=
  lift_mixing B.phat_nonneg B.phat_row_sum (fun x => h.nonneg x) (invariant_of_isInvProb h)
    hb hbeta f

end MarkedGraph

end GFNBounds.Balance
