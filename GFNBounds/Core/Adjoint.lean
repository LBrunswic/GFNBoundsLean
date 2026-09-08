import GFNBounds.Graph.Morozov
import GFNBounds.Graph.Universality

/-!
# The `λ`-reversal of a Markov kernel, and the `L²(λ)`-adjointness it carries

**`lem:adjoint`** — statement `proofs.tex:402–410`, proof `proofs.tex:412–445`.

> Let `𝒮` be Polish, let `ν_B ∈ 𝓜⁺(𝒮)`, let `T` be a Markov kernel on `𝒮`, and let
> `λ ∈ 𝓜⁺(𝒮, ν_B)` be non-zero, finite and `T`-invariant. Then:
> *(1)* the measure `T ⊗ λ` on `𝒮²` disintegrates over its first marginal — which is `λT = λ` —
> into a `λ`-almost everywhere unique Markov kernel `T^λ`, the *`λ`-reversal* of `T`,
> characterized by `λ ⊗ T^λ = T ⊗ λ`;
> *(2)* `λ` is `T^λ`-invariant and `T^λ ⊗ λ = λ ⊗ T`, so that `T` is in turn the `λ`-reversal of
> `T^λ`: reversal is an involution, `λ`-almost everywhere, on the Markov kernels leaving `λ`
> invariant;
> *(3)* the density actions `μ ↦ μT` and `μ ↦ μT^λ` are mutually adjoint contractions of
> `𝓜²(λ)`, each of operator norm `1`: `⟪μT ∣ ν⟫_λ = ⟪μ ∣ νT^λ⟫_λ` for all `μ, ν ∈ 𝓜²(λ)`; under
> `μ ↦ dμ/dλ` the density action of each of `T` and `T^λ` on `𝓜²(λ)` is the function action of
> the other on `L²(λ)`;
> *(4)* when `T = π_←` is a backward policy — which on a finite marked graph is the loop closure
> `π̂_←` of Definition `def:loop_closure` and not `π_←` itself — its reversal, written
> `π_→^λ := π_←^λ`, is the forward policy that the *balanced* flow of inflow `λ` pairs with
> `π_←`, and `(π_→^λ)^λ = π_←` […]. On a finite marked graph with `λ > 0` everywhere,
> `π_→^λ(s → s') = λ(s') π̂_←(s' → s)/λ(s)` is supported on the edges of the loop closure `Ĝ`,
> wrap edge included, so `π_→^λ(s_f → s₀) = 1` and `s_f` is not terminal for it.

## SCOPE (disclosed)

**This file proves the lemma on a *finite* state space, not on a Polish one.** That is a
disclosed restriction of the paper's hypothesis, not a substitution for it, and everything below
is stated over a `Fintype`. Four further boundaries:

* **The disintegration is elementary here.** On a finite space `T ⊗ λ` is a matrix and its
  disintegration over the first marginal is the division `T^λ(x→y) = λ(y)T(y→x)/λ(x)`; no
  standard-Borel machinery, no `ProbabilityTheory.Kernel.condKernel`, no `𝒮` at all. The paper's
  item *(1)* rests on the disintegration theorem for a finite measure on a standard Borel space
  and **that theorem is not what is used, nor what is proved**. What survives of item *(1)* is
  its content — existence, `λ`-a.e. uniqueness, and the characterizing identity `λ ⊗ T^λ =
  T ⊗ λ` — in the finite instance where the identity can be read entrywise.
* **`𝓜²(λ)` and `L²(λ)` are weighted sums, not `MeasureTheory` spaces.** `Graph.ipL2`,
  `Graph.nrmL2` of `GFNBounds/Graph/Morozov.lean` are reused verbatim rather than redefined; they
  are a `Finset` sum and a `Real.sqrt`, and no `InnerProductSpace` instance is built. A measure
  is carried by its `λ`-density throughout: `μ ↔ u` with `μ(x) = λ(x)u(x)`, so the isometry
  `μ ↦ dμ/dλ` of the paper's item *(3)* is the identification itself and is not a theorem here.
  Consequently `⟪μT ∣ ν⟫_λ = ⟪μ ∣ νT^λ⟫_λ` is `ipL2_densAct_densAct` read on densities. The
  absolute continuity `μT ≪ λ` that the paper establishes first (`proofs.tex:422`) is likewise
  not a separate statement: `μT` is *given* by its density `densAct`, so it is `≪ λ` by
  construction. What the paper's argument for it does carry over, and is used, is the reason the
  construction is harmless where `λ` vanishes — `λT(X) = 0` forces `T(y → X) = 0` for
  `λ`-almost every `y`, which is `IsInvariant.mul_eq_zero` here.
* **"Operator norm `1`" is `IsLeast`, not `‖·‖`.** No continuous-linear-map object is formed, so
  `‖·‖` is unavailable; `isLeast_opNorm_funAct` and `isLeast_opNorm_densAct` state instead that
  `1` is the least `c` with `‖Au‖ ≤ c‖u‖` for all `u`, which is the same assertion. The paper's
  "the adjoint is unique, being the adjoint of a map on a space with a non-degenerate inner
  product" is `IsReversalPair.eq_reversal` — uniqueness of the reversal, from which uniqueness of
  the adjoint follows — and the Riesz-representation step is not formalized.
* **Item *(4)*'s first half is already certified elsewhere and is not restated.** "The reversal is
  the forward policy that the balanced flow of inflow `λ` pairs with `π̂_←`" is
  `theo:universality_graphs`*(2)*, closed in `GFNBounds/Graph/Universality.lean`
  (`frozenBalance_reversal`, `frozenBalance_eq`). What this file adds for item *(4)* is the
  identification of that graph-specific reversal with the general finite one
  (`graph_reversal_eq`), the involution and the adjointness *through* that identification, and
  the support half — `reversal_hatEdge` and `reversal_snk_src`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒮` Polish | ⚠ **restricted to a `Fintype`** — see SCOPE; this is the whole of the disclosure |
| `ν_B ∈ 𝓜⁺(𝒮)` a reference measure | ✓ not needed: on a finite space every measure is `≪` the counting measure, and `𝓜⁺(𝒮, ν_B)` is every non-negative `lam : V → ℝ` |
| `T` a Markov kernel on `𝒮` | ✓ carried (`IsMarkov`: non-negative, rows summing to `1`) |
| `λ` non-negative | ✓ carried (`IsInvariant.nonneg`) |
| `λ` finite | ✓ automatic — a finite sum |
| `λ` non-zero | ⚠ **carried where it is used, not as a field**: only "operator norm exactly `1`" needs it, as `∃ x, 0 < lam x`. Items *(1)*, *(2)* and the adjointness identity hold for `λ = 0` (vacuously) |
| `λ` is `T`-invariant | ✓ carried (`IsInvariant.inv`) |
| `λ > 0`, for the entrywise formula of item *(4)* | ✓ carried where item *(4)* needs it, and *only* there |

**The `λ`-a.e. qualifications are taken seriously and are not silently upgraded.** The paper says
the reversal is `λ`-a.e. unique and the involution `λ`-a.e.; on a finite space "`λ`-a.e." is
"at every `x` with `λ(x) ≠ 0`", and that is the hypothesis every uniqueness and involution
statement below carries. It is *not* assumed that `λ > 0` everywhere, which would make them
unconditional. Two consequences are visible in the statements:

* `reversal lam A` is a Markov kernel only `λ`-a.e. (`IsMarkovOn`, not `IsMarkov`): where
  `λ(x) = 0` the division by `λ(x)` returns `0` and the row is the zero row, not a probability.
  `IsMarkovOn.toIsMarkov` upgrades it under `λ > 0`.
* the involution `reversal lam (reversal lam A) x y = A x y` needs `λ(x) ≠ 0` — and *only* that,
  because invariance forces `A x y = 0` when `λ(x) ≠ 0 = λ(y)` (`IsInvariant.eq_zero_of_ne_zero`).

## What the paper claims and this file delivers

| paper | here |
|---|---|
| *(1)* `T^λ` exists, is Markov, and satisfies `λ ⊗ T^λ = T ⊗ λ` | `reversal`, `IsInvariant.isMarkovOn_reversal`, `IsInvariant.isReversalPair_reversal` |
| *(1)* `T^λ` is `λ`-a.e. unique | `IsReversalPair.eq_reversal`, `IsReversalPair.eq_of_ne_zero` |
| *(2)* `λ` is `T^λ`-invariant | `IsReversalPair.isInvariant` |
| *(2)* `T^λ ⊗ λ = λ ⊗ T`, the flip identity `eq:reversal_flip` | `IsReversalPair.symm` — the relation is symmetric by inspection |
| *(2)* reversal is a `λ`-a.e. involution | `reversal_reversal` |
| *(3)* `⟪μT ∣ ν⟫_λ = ⟪μ ∣ νT^λ⟫_λ` | `ipL2_densAct_densAct`; `ipL2_densAct_funAct` is its density/function form |
| *(3)* the density action of `T` is the function action of `T^λ` | `densAct_eq_funAct_reversal` (unconditional) |
| *(3)* … and the density action of `T^λ` is the function action of `T` | `funAct_eq_densAct_reversal` (`λ`-a.e.) |
| *(3)* both are contractions — `eq:reversal_contraction`, the paper's Jensen step | `nrmL2_funAct_le`, `nrmL2_densAct_le` |
| *(3)* … of operator norm exactly `1`, attained at `λ` itself | `isLeast_opNorm_funAct`, `isLeast_opNorm_densAct` |
| *(1)*–*(3)* in one statement | `adjoint_finite` |
| *(4)* `π_→^λ(s→s') = λ(s')π̂_←(s'→s)/λ(s)` is the general reversal | `graph_reversal_eq` (definitional) |
| *(4)* it is the balanced flow's forward policy | `theo:universality_graphs`*(2)* — not restated, see SCOPE |
| *(4)* it is supported on the edges of `Ĝ` | `reversal_hatEdge` |
| *(4)* `π_→^λ(s_f → s₀) = 1`, so `s_f` is not terminal for it | `reversal_snk_src` |

Reuse, rather than redefinition, of the `L²(λ)` layer built for `prop:morozov_rate`:
`Graph.ipL2`, `Graph.nrmL2`, `Graph.sq_nrmL2` and `Graph.ipL2_le_mul_nrmL2` are imported and used
as they stand — the last is the discrete Cauchy–Schwarz that supplies the paper's Jensen step,
applied to the *row* `A(x → ·)` as the weight rather than to `λ`. Conversely
`Graph.BackwardPolicy.pdens` and `Graph.BackwardPolicy.qact` are shown to be `densAct` and
`funAct` of `π̂_←` (`graph_pdens_eq`, `graph_qact_eq`), so `Graph.ipL2_pdens_qact` — the pointwise
adjointness `prop:morozov_rate` was given — and `ipL2_densAct_funAct` are the same identity under
two *different* sufficient hypotheses: `λ > 0` there, `λ` invariant here. Neither implies the
other and neither is redundant; on the loop closure of a path-connected marked graph both hold,
so the two agree there.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

variable {V : Type*} [Fintype V]

/-! ### Markov kernels and invariant measures on a finite state space

The paper's `T` is a Markov kernel on `𝒮` and its `λ` a non-negative finite invariant measure.
On a finite `V` both are matrices, and `𝓜⁺(𝒮, ν_B)` is every non-negative `V → ℝ`: no reference
measure is needed. -/

/-- A **Markov kernel** on the finite state space `V`: non-negative, with every row summing to
`1`. The paper's `T` (`proofs.tex:403`). -/
structure IsMarkov (A : V → V → ℝ) : Prop where
  /-- `T(x → y) ≥ 0`. -/
  nonneg : ∀ x y, 0 ≤ A x y
  /-- `T(x → ·)` is a probability distribution. -/
  row_sum : ∀ x, ∑ y, A x y = 1

/-- A **`λ`-almost-everywhere Markov kernel**: non-negative, with the row at `x` summing to `1`
whenever `λ(x) ≠ 0`. This is what the `λ`-reversal is in general — where `λ` vanishes its row is
the zero row — and it is the honest reading of the paper's "`λ`-almost everywhere unique Markov
kernel" (`proofs.tex:405`). -/
structure IsMarkovOn (lam : V → ℝ) (A : V → V → ℝ) : Prop where
  /-- `T(x → y) ≥ 0`. -/
  nonneg : ∀ x y, 0 ≤ A x y
  /-- `T(x → ·)` is a probability distribution at every `x` carrying `λ`-mass. -/
  row_sum : ∀ ⦃x⦄, lam x ≠ 0 → ∑ y, A x y = 1

/-- A **non-negative invariant measure** `λ`: `λ ≥ 0` and `λT = λ` (`proofs.tex:403`).

Finiteness is automatic on a `Fintype`, and non-zeroness is *not* a field: only "operator norm
exactly `1`" consumes it, and it is carried there as `∃ x, 0 < lam x`. -/
structure IsInvariant (lam : V → ℝ) (A : V → V → ℝ) : Prop where
  /-- `λ ≥ 0`. -/
  nonneg : ∀ x, 0 ≤ lam x
  /-- `λT = λ`. -/
  inv : ∀ y, ∑ x, lam x * A x y = lam y

theorem IsMarkov.toIsMarkovOn {A : V → V → ℝ} (h : IsMarkov A) (lam : V → ℝ) :
    IsMarkovOn lam A :=
  ⟨h.nonneg, fun {x} _ => h.row_sum x⟩

theorem IsMarkovOn.toIsMarkov {lam : V → ℝ} {A : V → V → ℝ} (h : IsMarkovOn lam A)
    (hp : ∀ x, 0 < lam x) : IsMarkov A :=
  ⟨h.nonneg, fun x => h.row_sum (hp x).ne'⟩

/-- **A `λ`-null state is unreachable**: if `λ(y) = 0` then every term of `λT(y) = 0` vanishes.
The one consequence of invariance that the `λ`-a.e. statements below all lean on. -/
theorem IsInvariant.mul_eq_zero {lam : V → ℝ} {A : V → V → ℝ} (h : IsInvariant lam A)
    (hA : ∀ x y, 0 ≤ A x y) {y : V} (hy : lam y = 0) (x : V) : lam x * A x y = 0 := by
  have hsum : ∑ z, lam z * A z y = 0 := by rw [h.inv y, hy]
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun z _ => mul_nonneg (h.nonneg z) (hA z y))).1 hsum x (Finset.mem_univ x)

/-- **No transition from a `λ`-charged state to a `λ`-null one**: `λ(x) ≠ 0 = λ(y)` forces
`T(x → y) = 0`. This is why the involution of item *(2)* needs only `λ(x) ≠ 0`. -/
theorem IsInvariant.eq_zero_of_ne_zero {lam : V → ℝ} {A : V → V → ℝ} (h : IsInvariant lam A)
    (hA : ∀ x y, 0 ≤ A x y) {x y : V} (hx : lam x ≠ 0) (hy : lam y = 0) : A x y = 0 := by
  rcases _root_.mul_eq_zero.1 (h.mul_eq_zero hA hy x) with h' | h'
  · exact absurd h' hx
  · exact h'

/-! ### Item *(1)*: the `λ`-reversal, and the identity that characterizes it -/

/-- **`lem:adjoint`*(1)*, the `λ`-reversal `T^λ`** (`proofs.tex:405`, entrywise form at
`proofs.tex:408`): `T^λ(x → y) = λ(y) T(y → x)/λ(x)`, the disintegration of `T ⊗ λ` over its
first marginal `λ`, done by division on a finite space.

Where `λ(x) = 0` the Lean convention `a / 0 = 0` makes the row vanish; that is exactly the
`λ`-negligible set on which the paper leaves `T^λ` undetermined. -/
noncomputable def reversal (lam : V → ℝ) (A : V → V → ℝ) : V → V → ℝ :=
  fun x y => lam y * A y x / lam x

omit [Fintype V] in
theorem reversal_apply (lam : V → ℝ) (A : V → V → ℝ) (x y : V) :
    reversal lam A x y = lam y * A y x / lam x := rfl

omit [Fintype V] in
/-- Off the support of `λ` the reversal is the zero row — the `λ`-negligible set of
`proofs.tex:405`, made visible. -/
theorem reversal_of_eq_zero {lam : V → ℝ} {A : V → V → ℝ} {x : V} (hx : lam x = 0) (y : V) :
    reversal lam A x y = 0 := by simp [reversal, hx]

omit [Fintype V] in
theorem reversal_nonneg {lam : V → ℝ} {A : V → V → ℝ} (hlam : ∀ x, 0 ≤ lam x)
    (hA : ∀ x y, 0 ≤ A x y) (x y : V) : 0 ≤ reversal lam A x y :=
  div_nonneg (mul_nonneg (hlam y) (hA y x)) (hlam x)

/-- **`lem:adjoint`*(1)*, the characterizing identity** `λ ⊗ R = A ⊗ λ` (`proofs.tex:405`), read
entrywise on a finite space: `(λ ⊗ R)(x,y) = λ(x)R(x→y)` and `(A ⊗ λ)(x,y) = A(y→x)λ(y)`
(`proofs.tex:412`).

The relation is **symmetric in `A` and `R`** — swapping the two arguments of the identity swaps
the roles of the kernels — and that symmetry *is* item *(2)*'s flip identity `eq:reversal_flip`;
see `IsReversalPair.symm`. -/
def IsReversalPair (lam : V → ℝ) (A R : V → V → ℝ) : Prop :=
  ∀ x y, lam x * R x y = lam y * A y x

omit [Fintype V] in
/-- **`lem:adjoint`*(2)*, the flip identity `eq:reversal_flip`** (`proofs.tex:418`):
`T^λ ⊗ λ = λ ⊗ T`. On a finite space it is the symmetry of the characterizing identity, obtained
by reading it at `(y,x)` instead of `(x,y)`. -/
theorem IsReversalPair.symm {lam : V → ℝ} {A R : V → V → ℝ} (h : IsReversalPair lam A R) :
    IsReversalPair lam R A := fun x y => (h y x).symm

omit [Fintype V] in
theorem isReversalPair_comm {lam : V → ℝ} {A R : V → V → ℝ} :
    IsReversalPair lam A R ↔ IsReversalPair lam R A :=
  ⟨IsReversalPair.symm, IsReversalPair.symm⟩

/-- **`lem:adjoint`*(1)*, existence**: the reversal satisfies the characterizing identity — at
*every* state, including where `λ` vanishes, because there invariance kills both sides. -/
theorem IsInvariant.isReversalPair_reversal {lam : V → ℝ} {A : V → V → ℝ}
    (h : IsInvariant lam A) (hA : ∀ x y, 0 ≤ A x y) :
    IsReversalPair lam A (reversal lam A) := by
  intro x y
  by_cases hx : lam x = 0
  · rw [hx, zero_mul]
    exact (h.mul_eq_zero hA hx y).symm
  · rw [reversal_apply, mul_div_cancel₀ _ hx]

omit [Fintype V] in
/-- **`lem:adjoint`*(1)*, `λ`-a.e. uniqueness** (`proofs.tex:405`, "unique up to a
`λ`-negligible set"): any solution of the characterizing identity is the reversal at every state
carrying `λ`-mass. -/
theorem IsReversalPair.eq_reversal {lam : V → ℝ} {A R : V → V → ℝ} (h : IsReversalPair lam A R)
    {x : V} (hx : lam x ≠ 0) (y : V) : R x y = reversal lam A x y := by
  rw [reversal_apply, eq_div_iff hx, mul_comm]
  exact h x y

omit [Fintype V] in
/-- **`lem:adjoint`*(1)*, `λ`-a.e. uniqueness**, in the two-solutions form. -/
theorem IsReversalPair.eq_of_ne_zero {lam : V → ℝ} {A R R' : V → V → ℝ}
    (h : IsReversalPair lam A R) (h' : IsReversalPair lam A R') {x : V} (hx : lam x ≠ 0) (y : V) :
    R x y = R' x y := by rw [h.eq_reversal hx y, ← h'.eq_reversal hx y]

/-- **`lem:adjoint`*(1)*, the reversal is a Markov kernel** — `λ`-almost everywhere, its rows
summing to `1` by stationarity of `λ` exactly where `λ` does not vanish. -/
theorem IsInvariant.isMarkovOn_reversal {lam : V → ℝ} {A : V → V → ℝ} (h : IsInvariant lam A)
    (hA : ∀ x y, 0 ≤ A x y) : IsMarkovOn lam (reversal lam A) := by
  refine ⟨reversal_nonneg h.nonneg hA, fun {x} hx => ?_⟩
  simp only [reversal_apply]
  rw [← Finset.sum_div, h.inv x, div_self hx]

/-! ### Item *(2)*: invariance of `λ` under the reversal, and the involution -/

/-- **`lem:adjoint`*(2)*, `λ` is `T^λ`-invariant** (`proofs.tex:416`): `λT^λ` is the second
marginal of `λ ⊗ T^λ = T ⊗ λ`, which is `λ`. It needs only that `A` is row-stochastic — not that
`λ` is `A`-invariant. -/
theorem IsReversalPair.isInvariant {lam : V → ℝ} {A R : V → V → ℝ} (hlam : ∀ x, 0 ≤ lam x)
    (hA : IsMarkov A) (h : IsReversalPair lam A R) : IsInvariant lam R := by
  refine ⟨hlam, fun y => ?_⟩
  calc ∑ x, lam x * R x y = ∑ x, lam y * A y x := Finset.sum_congr rfl fun x _ => h x y
    _ = lam y := by rw [← Finset.mul_sum, hA.row_sum y, mul_one]

/-- **`lem:adjoint`*(2)*, reversal is an involution `λ`-almost everywhere** (`proofs.tex:406`):
`(T^λ)^λ = T` at every state carrying `λ`-mass.

`λ(x) ≠ 0` is the *only* hypothesis: if `λ(y) = 0` as well, both sides vanish — the left by the
convention `a/0 = 0` and the right by `IsInvariant.eq_zero_of_ne_zero`. -/
theorem reversal_reversal {lam : V → ℝ} {A : V → V → ℝ} (h : IsInvariant lam A)
    (hA : ∀ x y, 0 ≤ A x y) {x : V} (hx : lam x ≠ 0) (y : V) :
    reversal lam (reversal lam A) x y = A x y := by
  by_cases hy : lam y = 0
  · rw [reversal_apply, reversal_of_eq_zero hy, mul_zero, zero_div,
      h.eq_zero_of_ne_zero hA hx hy]
  · rw [reversal_apply, reversal_apply, mul_div_cancel₀ _ hy, mul_comm, mul_div_assoc,
      div_self hx, mul_one]

/-! ### The two actions of a kernel, and item *(3)*

A measure `μ ∈ 𝓜²(λ)` is carried by its density `u = dμ/dλ`, so that `μ(x) = λ(x)u(x)`; the
paper's isometry `μ ↦ dμ/dλ` is that identification and is not a theorem here (SCOPE). -/

/-- The **function action** `(Au)(x) = ∑_y A(x→y)u(y)` of a kernel on `L²(λ)` — the paper's `Af`
of `proofs.tex:422`, and `Graph.BackwardPolicy.qact` for `π̂_←`. -/
def funAct (A : V → V → ℝ) (u : V → ℝ) : V → ℝ := fun x => ∑ y, A x y * u y

theorem funAct_apply (A : V → V → ℝ) (u : V → ℝ) (x : V) :
    funAct A u x = ∑ y, A x y * u y := rfl

/-- The **density action** `μ ↦ μA` of a kernel on `𝓜²(λ)`, read on densities:
`(d(μA)/dλ)(y) = (∑_x λ(x)A(x→y)u(x))/λ(y)` for `u = dμ/dλ`. This is
`Graph.BackwardPolicy.pdens` for `π̂_←`. -/
noncomputable def densAct (lam : V → ℝ) (A : V → V → ℝ) (u : V → ℝ) : V → ℝ :=
  fun y => (∑ x, lam x * A x y * u x) / lam y

theorem densAct_apply (lam : V → ℝ) (A : V → V → ℝ) (u : V → ℝ) (y : V) :
    densAct lam A u y = (∑ x, lam x * A x y * u x) / lam y := rfl

/-- **`lem:adjoint`*(3)*, half of "the density action of each is the function action of the
other"** (`proofs.tex:407`): `d(μT)/dλ = T^λ u`. It holds at every state, no hypothesis at all,
both sides vanishing together where `λ` does. -/
theorem densAct_eq_funAct_reversal (lam : V → ℝ) (A : V → V → ℝ) (u : V → ℝ) :
    densAct lam A u = funAct (reversal lam A) u := by
  funext y
  simp only [densAct_apply, funAct_apply, reversal_apply, div_mul_eq_mul_div]
  rw [← Finset.sum_div]

/-- **`lem:adjoint`*(3)*, the other half** (`proofs.tex:442`, "exchanging the roles of `T` and
`T^λ`, legitimate by `eq:reversal_flip`"): `d(μT^λ)/dλ = Tu`, `λ`-almost everywhere. -/
theorem funAct_eq_densAct_reversal {lam : V → ℝ} {A R : V → V → ℝ} (h : IsReversalPair lam A R)
    (u : V → ℝ) {y : V} (hy : lam y ≠ 0) : densAct lam R u y = funAct A u y := by
  simp only [densAct_apply, funAct_apply]
  rw [show ∑ x, lam x * R x y * u x = ∑ x, lam y * (A y x * u x) from
      Finset.sum_congr rfl fun x _ => by rw [h x y]; ring,
    ← Finset.mul_sum, mul_comm, mul_div_assoc, div_self hy, mul_one]

/-- `⟪a ∣ ·⟫_λ` does not see a change off the support of `λ`. The bookkeeping lemma that lets the
`λ`-a.e. identities above be used inside an inner product. -/
theorem ipL2_congr_right {lam : V → ℝ} {a b b' : V → ℝ} (h : ∀ x, lam x ≠ 0 → b x = b' x) :
    Graph.ipL2 lam a b = Graph.ipL2 lam a b' := by
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : lam x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

/-- `⟪· ∣ b⟫_λ` does not see a change off the support of `λ`. -/
theorem ipL2_congr_left {lam : V → ℝ} {a a' b : V → ℝ} (h : ∀ x, lam x ≠ 0 → a x = a' x) :
    Graph.ipL2 lam a b = Graph.ipL2 lam a' b := by
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : lam x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

theorem nrmL2_congr {lam : V → ℝ} {a a' : V → ℝ} (h : ∀ x, lam x ≠ 0 → a x = a' x) :
    Graph.nrmL2 lam a = Graph.nrmL2 lam a' := by
  simp only [Graph.nrmL2]
  rw [ipL2_congr_left h, ipL2_congr_right h]

/-- **`lem:adjoint`*(3)*, the adjointness identity in density/function form**
(`proofs.tex:433–441`): `⟪μT ∣ ν⟫_λ = ∫ v · (Tv-side) dλ`, here `⟪d(μT)/dλ ∣ v⟫_λ =
⟪u ∣ Tv⟫_λ`. Two finite sums swapped, as `Graph.ipL2_pdens_qact` does for `π̂_←` —
**without that lemma's `λ > 0` hypothesis**, invariance supplying what positivity supplied
there. -/
theorem ipL2_densAct_funAct {lam : V → ℝ} {A : V → V → ℝ} (h : IsInvariant lam A)
    (hA : ∀ x y, 0 ≤ A x y) (u v : V → ℝ) :
    Graph.ipL2 lam (densAct lam A u) v = Graph.ipL2 lam u (funAct A v) := by
  have hleft : Graph.ipL2 lam (densAct lam A u) v = ∑ y, ∑ x, lam x * A x y * u x * v y := by
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : lam y = 0
    · rw [hy, zero_mul]
      refine (Finset.sum_eq_zero fun x _ => ?_).symm
      rw [h.mul_eq_zero hA hy x, zero_mul, zero_mul]
    · simp only [densAct_apply]
      rw [div_mul_eq_mul_div, mul_div_assoc', mul_comm (lam y), mul_div_assoc,
        div_self hy, mul_one, Finset.sum_mul]
  have hright : Graph.ipL2 lam u (funAct A v) = ∑ x, ∑ y, lam x * A x y * u x * v y := by
    simp only [Graph.ipL2, funAct_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hleft, hright, Finset.sum_comm]

/-- **`lem:adjoint`*(3)*, the adjointness of the two density actions** (`proofs.tex:407`):
`⟪μT ∣ ν⟫_λ = ⟪μ ∣ νT^λ⟫_λ` for `μ, ν ∈ 𝓜²(λ)`, carried by their densities `u, v`. -/
theorem ipL2_densAct_densAct {lam : V → ℝ} {A R : V → V → ℝ} (h : IsInvariant lam A)
    (hA : ∀ x y, 0 ≤ A x y) (hR : IsReversalPair lam A R) (u v : V → ℝ) :
    Graph.ipL2 lam (densAct lam A u) v = Graph.ipL2 lam u (densAct lam R v) := by
  rw [ipL2_densAct_funAct h hA u v]
  exact ipL2_congr_right fun x hx => (funAct_eq_densAct_reversal hR v hx).symm

/-! ### Item *(3)*, the contraction `eq:reversal_contraction`

The paper's step is Jensen against the probability measures `T^λ(x → ·)` (`proofs.tex:422`).
Here it is the discrete Cauchy–Schwarz `Graph.ipL2_le_mul_nrmL2` of `GFNBounds/Graph/Morozov.lean`
applied with the **row** `A(x → ·)` as the weight — the same inequality, reused rather than
reproved. -/

/-- **`eq:reversal_contraction` pointwise** (`proofs.tex:424`): `(Au)(x)² ≤ A(u²)(x)`, Jensen at
one state, for a row that is a probability distribution. -/
theorem funAct_mul_self_le {lam : V → ℝ} {A : V → V → ℝ} (hA : IsMarkovOn lam A) {x : V}
    (hx : lam x ≠ 0) (u : V → ℝ) :
    funAct A u x * funAct A u x ≤ ∑ y, A x y * (u y * u y) := by
  have hnn : ∀ y, 0 ≤ A x y := fun y => hA.nonneg x y
  have hone : Graph.nrmL2 (A x) (fun _ => (1:ℝ)) = 1 := by
    simp only [Graph.nrmL2, Graph.ipL2, mul_one]
    rw [hA.row_sum hx, Real.sqrt_one]
  have hip : ∀ w : V → ℝ, Graph.ipL2 (A x) w (fun _ => (1:ℝ)) = funAct A w x := by
    intro w
    simp only [Graph.ipL2, funAct_apply, mul_one]
  have hplus : funAct A u x ≤ Graph.nrmL2 (A x) u := by
    have := Graph.ipL2_le_mul_nrmL2 hnn u (fun _ => (1:ℝ))
    rwa [hip u, hone, mul_one] at this
  have hminus : -funAct A u x ≤ Graph.nrmL2 (A x) u := by
    have hneg : funAct A (fun z => -u z) x = -funAct A u x := by
      simp only [funAct_apply, mul_neg, Finset.sum_neg_distrib]
    have hnrm : Graph.nrmL2 (A x) (fun z => -u z) = Graph.nrmL2 (A x) u := by
      simp only [Graph.nrmL2, Graph.ipL2, neg_mul_neg]
    have := Graph.ipL2_le_mul_nrmL2 hnn (fun z => -u z) (fun _ => (1:ℝ))
    rwa [hip (fun z => -u z), hneg, hone, mul_one, hnrm] at this
  have habs : |funAct A u x| ≤ Graph.nrmL2 (A x) u := abs_le.2 ⟨neg_le.1 hminus, hplus⟩
  calc funAct A u x * funAct A u x = |funAct A u x| * |funAct A u x| :=
        (abs_mul_abs_self _).symm
    _ ≤ Graph.nrmL2 (A x) u * Graph.nrmL2 (A x) u :=
        mul_self_le_mul_self (abs_nonneg _) habs
    _ = Graph.nrmL2 (A x) u ^ 2 := (sq _).symm
    _ = ∑ y, A x y * (u y * u y) := Graph.sq_nrmL2 hnn u

/-- **`eq:reversal_contraction`** (`proofs.tex:424–425`): the function action of a kernel leaving
`λ` invariant is a contraction of `L²(λ)`. -/
theorem ipL2_funAct_self_le {lam : V → ℝ} {A : V → V → ℝ} (hA : IsMarkovOn lam A)
    (h : IsInvariant lam A) (u : V → ℝ) :
    Graph.ipL2 lam (funAct A u) (funAct A u) ≤ Graph.ipL2 lam u u := by
  have step : ∀ x : V, lam x * (funAct A u x * funAct A u x)
      ≤ ∑ y, lam x * A x y * (u y * u y) := by
    intro x
    by_cases hx : lam x = 0
    · rw [hx, zero_mul]
      refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_).symm
      rw [zero_mul, zero_mul]
    · have := funAct_mul_self_le hA hx u
      calc lam x * (funAct A u x * funAct A u x)
          ≤ lam x * ∑ y, A x y * (u y * u y) := by
            exact mul_le_mul_of_nonneg_left this (h.nonneg x)
        _ = ∑ y, lam x * A x y * (u y * u y) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
  calc Graph.ipL2 lam (funAct A u) (funAct A u)
      ≤ ∑ x, ∑ y, lam x * A x y * (u y * u y) := Finset.sum_le_sum fun x _ => step x
    _ = ∑ y, ∑ x, lam x * A x y * (u y * u y) := Finset.sum_comm
    _ = ∑ y, lam y * (u y * u y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, h.inv y]
    _ = Graph.ipL2 lam u u := rfl

/-- **`lem:adjoint`*(3)*, the function action is a contraction of `L²(λ)`**. -/
theorem nrmL2_funAct_le {lam : V → ℝ} {A : V → V → ℝ} (hA : IsMarkovOn lam A)
    (h : IsInvariant lam A) (u : V → ℝ) :
    Graph.nrmL2 lam (funAct A u) ≤ Graph.nrmL2 lam u :=
  Real.sqrt_le_sqrt (ipL2_funAct_self_le hA h u)

/-- **`lem:adjoint`*(3)*, the density action is a contraction of `𝓜²(λ)`** — the paper's own
route, through `d(μT)/dλ = T^λ u` and the contraction of the reversal's function action. -/
theorem nrmL2_densAct_le {lam : V → ℝ} {A : V → V → ℝ} (hA : IsMarkov A) (h : IsInvariant lam A)
    (u : V → ℝ) : Graph.nrmL2 lam (densAct lam A u) ≤ Graph.nrmL2 lam u := by
  rw [densAct_eq_funAct_reversal]
  exact nrmL2_funAct_le (h.isMarkovOn_reversal hA.nonneg)
    ((h.isReversalPair_reversal hA.nonneg).isInvariant h.nonneg hA) u

/-! ### Item *(3)*, "of operator norm `1`"

`1` is attained at `λ` itself — `dλ/dλ ≡ 1` and `λT = λT^λ = λ` (`proofs.tex:442`). No
`ContinuousLinearMap` is built, so the assertion is stated as `IsLeast`: see SCOPE. -/

/-- `‖λ‖_{𝓜²(λ)} > 0`: `λ` is non-zero and finite, so its own density `1` has positive norm.
The paper's reason why the two contractions have norm exactly `1`. -/
theorem nrmL2_one_pos {lam : V → ℝ} (hlam : ∀ x, 0 ≤ lam x) (hne : ∃ x, 0 < lam x) :
    0 < Graph.nrmL2 lam (fun _ => (1:ℝ)) := by
  obtain ⟨x₀, hx₀⟩ := hne
  simp only [Graph.nrmL2]
  refine Real.sqrt_pos.2 ?_
  have hterm : ∀ x ∈ (Finset.univ : Finset V), 0 ≤ lam x * ((1:ℝ) * 1) := fun x _ => by
    simpa using hlam x
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm (Finset.mem_univ x₀))
  simpa using hx₀

/-- **`lem:adjoint`*(3)*, the function action has operator norm exactly `1`**: `1` is the least
constant `c` with `‖Au‖_{L²(λ)} ≤ c‖u‖_{L²(λ)}` for every `u`. Membership is the contraction;
minimality is attainment at the constant density `1`, i.e. at the measure `λ`. -/
theorem isLeast_opNorm_funAct {lam : V → ℝ} {A : V → V → ℝ} (hA : IsMarkovOn lam A)
    (h : IsInvariant lam A) (hne : ∃ x, 0 < lam x) :
    IsLeast {c : ℝ | ∀ u, Graph.nrmL2 lam (funAct A u) ≤ c * Graph.nrmL2 lam u} 1 := by
  have hfix : Graph.nrmL2 lam (funAct A fun _ => (1:ℝ)) = Graph.nrmL2 lam (fun _ => (1:ℝ)) := by
    refine nrmL2_congr fun x hx => ?_
    simp only [funAct_apply, mul_one]
    exact hA.row_sum hx
  refine ⟨fun u => by rw [one_mul]; exact nrmL2_funAct_le hA h u, fun c hc => ?_⟩
  have := hc (fun _ => (1:ℝ))
  rw [hfix] at this
  exact le_of_mul_le_mul_right (by linarith) (nrmL2_one_pos h.nonneg hne)

/-- **`lem:adjoint`*(3)*, the density action has operator norm exactly `1`**. -/
theorem isLeast_opNorm_densAct {lam : V → ℝ} {A : V → V → ℝ} (hA : IsMarkov A)
    (h : IsInvariant lam A) (hne : ∃ x, 0 < lam x) :
    IsLeast {c : ℝ | ∀ u, Graph.nrmL2 lam (densAct lam A u) ≤ c * Graph.nrmL2 lam u} 1 := by
  have hrew : ∀ u : V → ℝ, densAct lam A u = funAct (reversal lam A) u := fun u => by
    rw [densAct_eq_funAct_reversal]
  constructor
  · intro u
    rw [one_mul]
    exact nrmL2_densAct_le hA h u
  · intro c hc
    refine (isLeast_opNorm_funAct (h.isMarkovOn_reversal hA.nonneg)
      ((h.isReversalPair_reversal hA.nonneg).isInvariant h.nonneg hA) hne).2 fun u => ?_
    rw [← hrew u]
    exact hc u

/-! ### Items *(1)*–*(3)* in one statement -/

/-- **`lem:adjoint`*(1)*–*(3)* on a finite state space** (`proofs.tex:402–410`), with the
paper's `λ`-almost-everywhere qualifications read as "at every state carrying `λ`-mass".

The Polish hypothesis is **restricted to a `Fintype`**; see the module SCOPE. Item *(4)* is the
graph section below, together with `theo:universality_graphs`*(2)*. -/
theorem adjoint_finite {lam : V → ℝ} {A : V → V → ℝ} (hA : IsMarkov A) (h : IsInvariant lam A)
    (hne : ∃ x, 0 < lam x) :
    -- *(1)* existence, Markov `λ`-a.e., and the characterizing identity `λ ⊗ T^λ = T ⊗ λ`
    (IsMarkovOn lam (reversal lam A) ∧ IsReversalPair lam A (reversal lam A))
    -- *(1)* `λ`-a.e. uniqueness
    ∧ (∀ R, IsReversalPair lam A R → ∀ x, lam x ≠ 0 → ∀ y, R x y = reversal lam A x y)
    -- *(2)* `λ` is `T^λ`-invariant, the flip identity, and the `λ`-a.e. involution
    ∧ (IsInvariant lam (reversal lam A) ∧ IsReversalPair lam (reversal lam A) A
        ∧ ∀ x, lam x ≠ 0 → ∀ y, reversal lam (reversal lam A) x y = A x y)
    -- *(3)* mutual adjointness on `𝓜²(λ)`
    ∧ (∀ u v, Graph.ipL2 lam (densAct lam A u) v
        = Graph.ipL2 lam u (densAct lam (reversal lam A) v))
    -- *(3)* each density action is the other's function action
    ∧ (densAct lam A = funAct (reversal lam A)
        ∧ ∀ u x, lam x ≠ 0 → densAct lam (reversal lam A) u x = funAct A u x)
    -- *(3)* both are contractions of operator norm exactly `1`
    ∧ IsLeast {c : ℝ | ∀ u, Graph.nrmL2 lam (densAct lam A u) ≤ c * Graph.nrmL2 lam u} 1 := by
  have hrev : IsReversalPair lam A (reversal lam A) := h.isReversalPair_reversal hA.nonneg
  refine ⟨⟨h.isMarkovOn_reversal hA.nonneg, hrev⟩,
    fun R hR x hx y => hR.eq_reversal hx y,
    ⟨hrev.isInvariant h.nonneg hA, hrev.symm,
      fun x hx y => reversal_reversal h hA.nonneg hx y⟩,
    fun u v => ipL2_densAct_densAct h hA.nonneg hrev u v,
    ⟨funext fun u => densAct_eq_funAct_reversal lam A u,
      fun u x hx => funAct_eq_densAct_reversal hrev u hx⟩,
    isLeast_opNorm_densAct hA h hne⟩

/-! ### Item *(4)*: the finite marked graph

`Graph.BackwardPolicy.reversal`, `Graph.BackwardPolicy.pdens` and `Graph.BackwardPolicy.qact` of
`GFNBounds/Graph/` are the loop-closed backward policy's instances of `reversal`, `densAct` and
`funAct` — definitionally, so every theorem above applies to them verbatim. What is *not*
restated here is that the reversal is the balanced flow's forward policy: that is
`theo:universality_graphs`*(2)*, already closed in `GFNBounds/Graph/Universality.lean`. -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Graph.MarkedGraph V}
  (B : Graph.BackwardPolicy G)

/-- **`lem:adjoint`*(4)*, `T = π̂_←`**: the loop closure is a Markov kernel on `𝒱`
(`proofs.tex:408`, "which on a finite marked graph is the loop closure `π̂_←` […] and not `π_←`
itself"). -/
theorem phat_isMarkov : IsMarkov B.phat := ⟨B.phat_nonneg, B.phat_row_sum⟩

/-- An invariant probability of the backward chain is an invariant measure in the sense of this
file. -/
theorem isInvariant_of_isInvProb {lam : V → ℝ} (h : B.IsInvProb lam) :
    IsInvariant lam B.phat := ⟨h.nonneg, h.inv⟩

/-- **`lem:adjoint`*(4)*, the entrywise formula** (`proofs.tex:408`):
`π_→^λ(s → s') = λ(s') π̂_←(s' → s)/λ(s)` is the general finite `λ`-reversal of `π̂_←`, so
`theo:universality_graphs`*(2)*'s `Graph.BackwardPolicy.reversal` **is** `reversal`. -/
theorem graph_reversal_eq (lam : V → ℝ) : B.reversal lam = reversal lam B.phat := rfl

/-- `Graph.BackwardPolicy.pdens`, the density action of `prop:morozov_rate`, is `densAct` of
`π̂_←`. -/
theorem graph_pdens_eq (lam : V → ℝ) : B.pdens lam = densAct lam B.phat := rfl

/-- `Graph.BackwardPolicy.qact`, the function action of `prop:morozov_rate`, is `funAct` of
`π̂_←`. -/
theorem graph_qact_eq : B.qact = funAct B.phat := rfl

/-- **`lem:adjoint`*(4)*, the support** (`proofs.tex:444`, "it is positive only where
`π̂_←(s'→s) > 0`, hence only on edges `s → s'` of `Ĝ`"). -/
theorem reversal_hatEdge {lam : V → ℝ} {u v : V} (h : reversal lam B.phat u v ≠ 0) :
    G.hatEdge u v := by
  refine B.phat_supp (s := v) (s' := u) fun hz => h ?_
  rw [reversal_apply, hz, mul_zero, zero_div]

/-- **`lem:adjoint`*(4)*, the wrap edge** (`proofs.tex:444`): `π_→^λ(s_f → s₀) = 1`, so `s_f` is
not terminal for the forward policy. The wrap edge is the only edge out of `s_f` in `Ĝ`, hence
the only in-edge of `s_f` the backward policy can use, so the reversal's row at `s_f` — a
probability row where `λ > 0` — is the point mass at `s₀`. -/
theorem reversal_snk_src {lam : V → ℝ} (h : B.IsInvProb lam) (hp : ∀ x, 0 < lam x) :
    reversal lam B.phat G.snk G.src = 1 := by
  have hinv : IsInvariant lam B.phat := isInvariant_of_isInvProb B h
  have hrow : ∑ v, reversal lam B.phat G.snk v = 1 :=
    (hinv.isMarkovOn_reversal B.phat_nonneg).row_sum (hp G.snk).ne'
  have hsingle : ∀ v ∈ (Finset.univ : Finset V), v ≠ G.src →
      reversal lam B.phat G.snk v = 0 := by
    intro v _ hv
    have hz : B.phat v G.snk = 0 := by
      by_contra hne
      rcases B.phat_supp hne with hedge | ⟨-, hsrc⟩
      · exact G.no_edge_out_of_snk v hedge
      · exact hv hsrc
    rw [reversal_apply, hz, mul_zero, zero_div]
  rw [Finset.sum_eq_single G.src hsingle (fun hn => absurd (Finset.mem_univ G.src) hn)] at hrow
  exact hrow

end Graph

end GFNBounds.Core
