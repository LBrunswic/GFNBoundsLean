import GFNBounds.Graph.Setting

/-!
# The frozen-backward family: the balanced ray, and the flow left by cutting the wrap edge

**`theo:universality_graphs`** — items *(2)* and *(3)*. Statement `proofs.tex:966–982`
(item *(2)* at `:970–974`, item *(3)* at `:975–979`, the concluding paragraph at `:981`);
proof `proofs.tex:984–1012` (item *(2)* at `:987–991`, item *(3)* at `:993–1009`). Item *(1)*
is `GFNBounds.Graph.Setting`'s `BackwardPolicy.universality_graphs_one`; it is imported, not
restated. The standing prose defining *marked graph* and *backward policy* is `proofs.tex:949`
and is part of the specification.

> *(2)* the frozen-backward family on the loop closure,
> `Θ_{π_←} := { (π_→, f_out) : (f_out μ) ⊗ π_→ = π̂_← ⊗ (f_out μ) }`,
> is, apart from the trivial element `f_out ≡ 0`, exactly the ray `f_out μ = c λ`, `c > 0`, with
> `π_→ = π̂_←^λ` the `λ`-reversal of `π̂_←` (Lemma `lem:adjoint`), given on edges by
> `π_→(s → s') = λ(s') π̂_←(s' → s) / λ(s)`;
>
> *(3)* for `c = Z/λ(s₀)`, cutting the wrap edge turns this element into a generative flow on
> `G` satisfying the flow-matching constraint exactly, with initial flow of total mass `Z`
> carried by the edges out of `s₀` and terminal flow `F_term = κ := Z π_←(s_f → ·)`, positive on
> every terminating state; in particular its sampler satisfies `s_τ ∼ κ/Z` by Theorem
> `theo:sampling_theorem`.

and the two proofs, which this file follows line by line:

> *(2)* The constraint is an equality of measures on `𝒱²`: in coordinates `(u,v)` standing for a
> transition `u → v`, it reads `f_out(u) π_→(u → v) = π̂_←(v → u) f_out(v)`. Summing over `v`
> gives, at every `u ∈ 𝒱`, `f_out(u) = ∑_v f_out(v) π̂_←(v → u)`, i.e. `f_out μ` is invariant
> under the backward chain, whence `f_out μ = c λ` for some `c > 0` by *(1)*. The constraint then
> becomes `(cλ) ⊗ π_→ = π̂_← ⊗ (cλ)`, whose unique solution is the `λ`-reversal of Lemma
> `lem:adjoint`; on a finite space the disintegration is the elementary formula displayed in the
> statement, well-defined since `λ > 0`. Conversely this pair satisfies the constraint by
> definition of the reversal.

> *(3)* Define the edge flow `e(u → v) := c λ(v) π̂_←(v → u)` … `∑_v e(u→v) = c λ(u)` by
> stationarity of `λ`, `∑_u e(u→v) = c λ(v)` because `π̂_←(v→·)` is a probability: `e` is a
> circulation, with throughput `cλ(u)` at every vertex `u`. The wrap edge carries
> `e(s_f → s₀) = c λ(s₀) π̂_←(s₀ → s_f) = c λ(s₀) = Z`. Cut it … the initial flow is
> `F_init(v) = e(s₀ → v)`, of total mass `Z`, and the terminal flow is
> `F_term(x) = e(x → s_f) = Z π_←(s_f → x) = κ(x)` … positive on every terminating state since
> `π_←` is positive on every edge `x → s_f`. Explicitly, on the internal state space
> `𝒮 := 𝒱 ∖ {s₀, s_f}` the generative flow has star outflow `f_out^*(u) = cλ(u) − e(u → s_f)`
> and star forward policy `π_→^*(u → v) := e(u → v)/f_out^*(u)` (at states where `f_out^*`
> vanishes the trajectory terminates almost surely and the policy is immaterial), so that
> `f_out^*(u) π_→^*(u → v) = e(u → v)` and, at every `v ∈ 𝒮`,
> `F_init(v) + ((f_out^* μ) π_→^*)(v) = c λ(v) = F_term(v) + f_out^*(v)`, which is the
> flow-matching constraint.

## The modelling decisions

**The internal state space `𝒮 = 𝒱 ∖ {s₀, s_f}` is a `Finset V`, not a subtype**
(`MarkedGraph.internal`). The counting measure `μ` is `Finset.sum`, so "restrict to `𝒮`" is
"sum over a sub-`Finset`"; a subtype would buy nothing here and would cost a coercion in every
statement. It is `(univ.erase s₀).erase s_f`, and `internal_eq_erase_src` records that the two
erasures commute — both orders are used, one for the inflow split, one for the row sum of the
star policy.

**The family `Θ_{π_←}` is its balance equation.** `FrozenBalance pf fout` is exactly
`∀ u v, f_out(u) π_→(u → v) = π̂_←(v → u) f_out(v)`, the paper's "equality of measures on `𝒱²`
in coordinates". That `π_→` is a Markov kernel and `f_out ≥ 0` are what *makes a pair a member*
of `Θ`; they are carried as named hypotheses at each statement rather than bundled, so that the
reader can see which half of *(2)* consumes which. **Only `∑_v π_→(u → v) = 1` is used** in the
forward direction — non-negativity of `π_→` is never needed to identify the ray — and the
converse *produces* a non-negative kernel (`reversal_nonneg`, `sum_reversal`). Dropping an
unused hypothesis is a strengthening in the safe direction, as in `Setting.lean`'s
`src_row_unique`.

**Division by zero is `0`, twice, and both are harmless.** `reversal lam u v` divides by
`λ(u)`, which the theorem's hypotheses make positive (`IsInvProb.pos`); every statement about it
carries that positivity, so the junk value is never in the range of any claim.
`fwdStar lam c u v := e(u → v)/f_out^*(u)` divides by an outflow the paper itself allows to
vanish. There the junk value is not avoided but *proved harmless*: `outflowStar_eq_sum` shows
`f_out^*(u) = ∑_{v ≠ s_f} e(u → v)`, a sum of non-negative terms, so `f_out^*(u) = 0` forces
`e(u → v) = 0` for every `v ≠ s_f` (`edgeFlow_eq_zero_of_outflowStar`), and the identity the
flow-matching computation actually uses,
`f_out^*(u) π_→^*(u → v) = e(u → v)` for `v ≠ s_f` (`outflowStar_mul_fwdStar`), holds
unconditionally. This is the Lean reading of "the policy is immaterial": the *product* is
determined even where the *quotient* is not, and only the product is ever summed.

**`c` is not existentially quantified.** Item *(3)* fixes `c = Z/λ(s₀)`; the umbrella theorem
carries that as the hypothesis `hc : c = Z / lam G.src`, so the constant is an explicit formula
in the statement rather than a witness produced by the proof.

## SCOPE (disclosed)

* **The sampler is not formalized, and `theo:sampling_theorem` is not assumed.** The last clause
  of item *(3)* — "in particular its sampler satisfies `s_τ ∼ κ/Z` by Theorem
  `theo:sampling_theorem`" — and the last sentence of the proof rest on a theorem the paper
  **quotes from `bengio2021flow` and does not prove**. There is no trajectory space, no stopping
  time and no `s_τ` anywhere in this file, and nothing here is stated conditionally on that
  theorem either: the honest boundary is the flow-matching identity, which is finite algebra,
  and this file stops at it. A conditional statement was considered and rejected as empty — with
  `theo:sampling_theorem` as a hypothesis and no model of the sampler, the conclusion would be a
  rewriting of the hypothesis.
* **The bridge to `GFNBounds.Core.StronglyUniversalAt` is not built.** `Core`'s predicate lives
  on a Banach lattice (`[NormedAddCommGroup] [Lattice] [HasSolidNorm] [IsOrderedAddMonoid]`), and
  Mathlib `v4.31.0` carries **no `HasSolidNorm` instance for a `Pi` type** — the only instances
  are `ℝ`, `ℚ`, `ℤ`, `α →ᵇ β` and `Lp`. Instantiating it at `𝒮 → ℝ` would mean declaring a global
  order-lattice-norm instance from a scaffold file, which is an invasive change for a statement
  that is *weaker* than what is proved here: `fmDefect_eq_zero` says the flow-matching defect is
  **identically zero, pointwise**, on `𝒮`, whence `residuals_eq_zero` gives `δf_init = δf_term = 0`
  pointwise. Pointwise vanishing implies vanishing in every norm, so the paper's "simultaneously
  for every `p ∈ [1,+∞]`" is subsumed; but the *predicate* `StronglyUniversalAt` is not the one
  discharged, and this file does not claim it.
* **`def:universality`'s quantifier is not closed.** The concluding paragraph reads "for every
  target `κ` with full support on the terminating states … the universality infimum vanishes and
  is attained". What is proved here is the pair-level statement item *(3)* delivers: for the pair
  `(F_init, F_term)` **that the construction produces**, the defect is zero. `F_init` is not free,
  and no statement here quantifies over arbitrary admissible pairs.
* **The concluding paragraph's "freeze `π_←(s_f → ·) := κ`" is read backwards.** Rather than
  building a backward policy from a target, `termFlow_eq_target` records the equivalent fact that
  the constructed terminal flow *is* `Z π_←(s_f → ·)`, so a policy whose sink row is `κ/Z` gives
  `F_term = κ` — and `termFlow_pos_of_edge` is the paper's "positive on every terminating state",
  which is exactly the hypothesis `PositiveOnEdges` read at the edges into `s_f`.
* **`π_→^*` is checked to be a Markov kernel on `𝒮`** (`sum_fwdStar_internal`) where the outflow
  does not vanish. The paper does not state this; it is implied by calling `π_→^*` a policy, and
  it is included as a consistency check on the construction, not as a claim of the paper.
* **`rem:loop_closure_necessary`** (`proofs.tex:1014–1015`) is not formalized. It is the reason
  every definition below is written against `phat` (the loop closure) rather than `pb`, and it was
  used as a sanity check: the wrap edge is what makes `FrozenBalance` non-trivial.
* **The chain is not modelled**, as in `Setting.lean`: invariance is a finite sum identity and
  irreducibility is reflexive-transitive closure of a positive transition.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒱` finite | ✓ carried (`[Fintype V]`); `[DecidableEq V]` for `phat`'s case split and for `Finset.erase` |
| `G` path-connected | ✓ carried (`MarkedGraph.PathConnected`), used only through `IsInvProb.pos` |
| `π_←(s → s') > 0` for every edge `s' → s` | ✓ carried (`PositiveOnEdges`); used for `λ > 0` and for `κ > 0` on terminating states |
| `λ` an invariant probability of `π̂_←` | ✓ carried as `B.IsInvProb lam`, the predicate of item *(1)* |
| total mass `Z > 0` | ✓ carried (`hZ : 0 < Z`), and `c = Z/λ(s₀)` is a hypothesis, not an existential |
| `π_→` a Markov kernel | ⚠ **weakened**: only `∑_v π_→(u → v) = 1` is assumed in the forward half; the converse proves both halves for the reversal |
| `f_out ≥ 0` | ✓ carried (`hnn`), and `f_out ≠ 0` is the paper's "apart from the trivial element" |
| the counting measure `μ` | ✓ `Finset.sum`; no measure-theoretic layer |
| `theo:sampling_theorem` | ✗ **not used and not assumed**; see SCOPE |
| `equ:FM_const` at every `v ∈ 𝒮` | ✓ `fmDefect_eq_zero`, exactly (pointwise `= 0`, not a norm bound) |

## What items (2) and (3) claim and this file delivers

| paper | here |
|---|---|
| summing the constraint makes `f_out μ` invariant | `FrozenBalance.invariant` |
| a non-negative non-zero invariant vector is `cλ`, `c > 0` | `eq_smul_invProb` |
| the family is the ray, and `π_→` is the `λ`-reversal | `frozenBalance_eq` |
| the reversal is a Markov kernel and lies in the family | `reversal_nonneg`, `sum_reversal`, `frozenBalance_reversal` |
| item *(2)*, both directions | `universality_graphs_two` |
| `e` is a circulation with throughput `cλ` | `sum_edgeFlow_out`, `sum_edgeFlow_in` |
| the wrap edge carries `Z` | `edgeFlow_wrap` |
| the initial flow has total mass `Z` | `sum_initFlow` |
| `F_term = κ = Z π_←(s_f → ·)`, positive on terminating states | `termFlow_eq_target`, `termFlow_pos_of_edge` |
| `f_out^* ≥ 0`, and `f_out^* π_→^* = e` even where `f_out^*` vanishes | `outflowStar_nonneg`, `outflowStar_mul_fwdStar` |
| flow matching holds **exactly** at every `v ∈ 𝒮` | `fmDefect_eq_zero`, `flow_matching` |
| the residuals vanish, hence in every `L^p` at once | `residuals_eq_zero` |
| item *(3)*, in one statement | `universality_graphs_three` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The internal state space -/

namespace MarkedGraph

variable (G : MarkedGraph V)

/-- **`theo:universality_graphs`*(3)*, the internal state space** `𝒮 := 𝒱 ∖ {s₀, s_f}`
(`proofs.tex:1003`), as a `Finset` of `V`. The counting measure is `Finset.sum`, so this is all
that "restrict to `𝒮`" needs. -/
def internal : Finset V := (Finset.univ.erase G.src).erase G.snk

variable {G}

/-- Membership in `𝒮`: the internal states are the vertices that are neither mark. -/
theorem mem_internal {v : V} : v ∈ G.internal ↔ v ≠ G.src ∧ v ≠ G.snk := by
  simp only [internal, Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-- The two erasures commute. Both orders occur below: the first splits the inflow at `v`, the
second sums the star forward policy over `𝒮`. -/
theorem internal_eq_erase_src : G.internal = (Finset.univ.erase G.snk).erase G.src := by
  ext v
  simp only [mem_internal, Finset.mem_erase, Finset.mem_univ, and_true]

end MarkedGraph

namespace BackwardPolicy

variable {G : MarkedGraph V} (B : BackwardPolicy G)

/-! ### Un-normalized uniqueness of the invariant measure -/

/-- Normalizing a non-negative invariant vector of positive total mass gives an invariant
probability of the backward chain. -/
theorem isInvProb_normalized {f : V → ℝ} (hnn : ∀ x, 0 ≤ f x) (hpos : 0 < ∑ z, f z)
    (hinv : ∀ y, ∑ x, f x * B.phat x y = f y) :
    B.IsInvProb (fun x => f x / ∑ z, f z) := by
  refine ⟨fun y => div_nonneg (hnn y) hpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self (ne_of_gt hpos)]
  · intro y
    have hrw : ∀ x : V, f x / (∑ z, f z) * B.phat x y = (∑ z, f z)⁻¹ * (f x * B.phat x y) := by
      intro x; rw [div_eq_inv_mul]; ring
    rw [Finset.sum_congr rfl fun x _ => hrw x, ← Finset.mul_sum, hinv y, div_eq_inv_mul]

/-- **`theo:universality_graphs`*(2)*, un-normalized uniqueness.** A non-negative, non-zero
vector invariant under the backward chain is `c λ` with `c = ∑ f > 0` — the step the paper takes
in the words "whence `f_out μ = c λ` for some `c > 0` by *(1)*", where *(1)* delivers uniqueness
only among *probabilities*. It is `invProb_unique` applied to `f / ∑ f`. -/
theorem eq_smul_invProb (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges) {lam f : V → ℝ}
    (h : B.IsInvProb lam) (hnn : ∀ x, 0 ≤ f x) (hne : f ≠ 0)
    (hinv : ∀ y, ∑ x, f x * B.phat x y = f y) :
    0 < ∑ z, f z ∧ ∀ x, f x = (∑ z, f z) * lam x := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
    by_contra hc
    exact hne (funext fun x => not_not.mp (not_exists.mp hc x))
  have hpos : 0 < ∑ z, f z :=
    Finset.sum_pos' (fun i _ => hnn i) ⟨x₀, Finset.mem_univ _, (hnn x₀).lt_of_ne (Ne.symm hx₀)⟩
  refine ⟨hpos, fun x => ?_⟩
  have heq := invProb_unique hpc hbpos (B.isInvProb_normalized hnn hpos hinv) h
  have hx : f x / (∑ z, f z) = lam x := congrFun heq x
  rw [div_eq_iff (ne_of_gt hpos)] at hx
  rw [hx]; ring

/-! ### Item (2): the frozen-backward family is the balanced ray -/

/-- **`theo:universality_graphs`*(2)*, the family `Θ_{π_←}`** (`proofs.tex:970–974`), in the
coordinates its proof uses (`proofs.tex:987`): the pair `(π_→, f_out)` satisfies
`(f_out μ) ⊗ π_→ = π̂_← ⊗ (f_out μ)` iff `f_out(u) π_→(u → v) = π̂_←(v → u) f_out(v)` at every
transition `u → v`.

Membership in `Θ` also asks that `π_→` be a forward policy and `f_out` a non-negative density;
those are carried as hypotheses at each statement, not as fields — see the module's modelling
decisions. -/
def FrozenBalance (pf : V → V → ℝ) (fout : V → ℝ) : Prop :=
  ∀ u v, fout u * pf u v = B.phat v u * fout v

/-- **`theo:universality_graphs`*(2)*, the `λ`-reversal `π̂_←^λ`** (`proofs.tex:974`):
`π_→(s → s') = λ(s') π̂_←(s' → s) / λ(s)`, the elementary finite-space form of the disintegration
of Lemma `lem:adjoint`. Well-defined wherever `λ > 0`, which item *(1)* supplies. -/
noncomputable def reversal (lam : V → ℝ) (u v : V) : ℝ := lam v * B.phat v u / lam u

/-- The `λ`-reversal is non-negative. -/
theorem reversal_nonneg {lam : V → ℝ} (hlam : ∀ x, 0 ≤ lam x) (u v : V) :
    0 ≤ B.reversal lam u v :=
  div_nonneg (mul_nonneg (hlam v) (B.phat_nonneg v u)) (hlam u)

/-- The `λ`-reversal is a Markov kernel: its rows sum to `1`, by stationarity of `λ`. -/
theorem sum_reversal {lam : V → ℝ} (h : B.IsInvProb lam) {u : V} (hu : lam u ≠ 0) :
    ∑ v, B.reversal lam u v = 1 := by
  simp only [reversal]
  rw [← Finset.sum_div, h.inv u, div_self hu]

/-- **`theo:universality_graphs`*(2)*, the converse inclusion** (`proofs.tex:991`, "Conversely
this pair satisfies the constraint by definition of the reversal"): every point `c λ`, `c` real,
of the ray lies in `Θ_{π_←}` with the `λ`-reversal as forward policy. -/
theorem frozenBalance_reversal {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (c : ℝ) :
    B.FrozenBalance (B.reversal lam) (fun x => c * lam x) := by
  intro u v
  have hu : lam u ≠ 0 := (hlam u).ne'
  simp only [reversal]
  field_simp

/-- **`theo:universality_graphs`*(2)*, the forward inclusion** (`proofs.tex:987–991`): a member
of `Θ_{π_←}` with a non-zero non-negative outflow has `f_out = c λ` with `c = ∑ f_out > 0`, and
its forward policy is the `λ`-reversal at **every** transition — `f_out` being positive
everywhere, the disintegration is pinned everywhere. -/
theorem frozenBalance_eq (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges) {lam : V → ℝ}
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
  obtain ⟨hc, hray⟩ := B.eq_smul_invProb hpc hbpos h hnn hne hinv
  refine ⟨hc, hray, ?_⟩
  have hlam : ∀ x, 0 < lam x := fun x => h.pos hpc hbpos x
  funext u v
  have key := hfb u v
  rw [hray u, hray v] at key
  simp only [reversal]
  rw [eq_div_iff (hlam u).ne']
  refine mul_left_cancel₀ (ne_of_gt hc) ?_
  linear_combination key

/-- **`theo:universality_graphs`*(2)*** (`proofs.tex:970–974`, proof `proofs.tex:987–991`), in
one statement: apart from `f_out ≡ 0`, the frozen-backward family on the loop closure is exactly
the ray `f_out = c λ`, `c > 0`, carrying the `λ`-reversal — and the `λ`-reversal is a genuine
Markov kernel.

The first conjunct assumes of `π_→` only that its rows sum to `1`; the second and third *prove*
that the reversal is a non-negative kernel, so no member of the family is lost by the weakening.
See the module's modelling decisions. -/
theorem universality_graphs_two (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) :
    (∀ (pf : V → V → ℝ) (fout : V → ℝ), (∀ u, ∑ v, pf u v = 1) → (∀ x, 0 ≤ fout x) →
        fout ≠ 0 → B.FrozenBalance pf fout →
        ∃ c : ℝ, 0 < c ∧ (∀ x, fout x = c * lam x) ∧ pf = B.reversal lam) ∧
      (∀ c : ℝ, 0 < c → B.FrozenBalance (B.reversal lam) (fun x => c * lam x)) ∧
      (∀ u v, 0 ≤ B.reversal lam u v) ∧ (∀ u, ∑ v, B.reversal lam u v = 1) := by
  have hlam : ∀ x, 0 < lam x := fun x => h.pos hpc hbpos x
  refine ⟨fun pf fout hrow hnn hne hfb => ?_, fun c _ => B.frozenBalance_reversal hlam c,
    fun u v => B.reversal_nonneg (fun x => (hlam x).le) u v,
    fun u => B.sum_reversal h (hlam u).ne'⟩
  obtain ⟨hc, hray, hpf⟩ := B.frozenBalance_eq hpc hbpos h hrow hnn hne hfb
  exact ⟨∑ z, fout z, hc, hray, hpf⟩

/-! ### Item (3): cutting the wrap edge -/

/-- **`theo:universality_graphs`*(3)*, the edge flow** (`proofs.tex:993`):
`e(u → v) := c λ(v) π̂_←(v → u)`, the edge measure of the flow of item *(2)*. -/
noncomputable def edgeFlow (lam : V → ℝ) (c : ℝ) (u v : V) : ℝ := c * lam v * B.phat v u

/-- **`theo:universality_graphs`*(3)*, the initial flow**: `F_init(v) = e(s₀ → v)`. -/
noncomputable def initFlow (lam : V → ℝ) (c : ℝ) (v : V) : ℝ := B.edgeFlow lam c G.src v

/-- **`theo:universality_graphs`*(3)*, the terminal flow**: `F_term(x) = e(x → s_f)`. -/
noncomputable def termFlow (lam : V → ℝ) (c : ℝ) (x : V) : ℝ := B.edgeFlow lam c x G.snk

/-- **`theo:universality_graphs`*(3)*, the star outflow**:
`f_out^*(u) = c λ(u) − e(u → s_f)` (`proofs.tex:1003`). -/
noncomputable def outflowStar (lam : V → ℝ) (c : ℝ) (u : V) : ℝ :=
  c * lam u - B.edgeFlow lam c u G.snk

/-- **`theo:universality_graphs`*(3)*, the star forward policy**:
`π_→^*(u → v) := e(u → v)/f_out^*(u)` (`proofs.tex:1003`). Where `f_out^*` vanishes this is
Lean's `x/0 = 0`; the paper's "the policy is immaterial" is `outflowStar_mul_fwdStar`, which
holds there too. -/
noncomputable def fwdStar (lam : V → ℝ) (c : ℝ) (u v : V) : ℝ :=
  B.edgeFlow lam c u v / B.outflowStar lam c u

/-- **`equ:FM_const` on `𝒮`, as a defect**: the two sides of the flow-matching constraint
`F_init + (f_out^* μ) π_→^* = F_term + f_out^*`, subtracted. Item *(3)* claims it is `0` at every
internal state — exactly, not in norm. -/
noncomputable def fmDefect (lam : V → ℝ) (c : ℝ) (v : V) : ℝ :=
  B.initFlow lam c v + (∑ u ∈ G.internal, B.outflowStar lam c u * B.fwdStar lam c u v)
    - B.termFlow lam c v - B.outflowStar lam c v

/-- The only backward transition into `s_f` is from `s₀`: `π̂_←(v → s_f) = 0` for `v ≠ s₀`,
because `s_f` has no outgoing edge in `G`. -/
theorem phat_snk_of_ne_src {v : V} (hv : v ≠ G.src) : B.phat v G.snk = 0 := by
  rw [B.phat_of_ne_src hv]
  by_contra hc
  exact G.no_edge_out_of_snk v (B.supp hv hc)

/-- The edge flow is non-negative. -/
theorem edgeFlow_nonneg {lam : V → ℝ} (hlam : ∀ x, 0 ≤ lam x) {c : ℝ} (hc : 0 ≤ c) (u v : V) :
    0 ≤ B.edgeFlow lam c u v :=
  mul_nonneg (mul_nonneg hc (hlam v)) (B.phat_nonneg v u)

/-- **`e` is a circulation, outgoing half** (`proofs.tex:995`): `∑_v e(u → v) = c λ(u)`, by
stationarity of `λ`. -/
theorem sum_edgeFlow_out {lam : V → ℝ} (h : B.IsInvProb lam) (c : ℝ) (u : V) :
    ∑ v, B.edgeFlow lam c u v = c * lam u := by
  have hrw : ∀ v : V, B.edgeFlow lam c u v = c * (lam v * B.phat v u) := by
    intro v; simp only [edgeFlow, mul_assoc]
  rw [Finset.sum_congr rfl fun v _ => hrw v, ← Finset.mul_sum, h.inv u]

/-- **`e` is a circulation, incoming half** (`proofs.tex:996`): `∑_u e(u → v) = c λ(v)`, because
`π̂_←(v → ·)` is a probability. -/
theorem sum_edgeFlow_in (lam : V → ℝ) (c : ℝ) (v : V) :
    ∑ u, B.edgeFlow lam c u v = c * lam v := by
  have hrw : ∀ u : V, B.edgeFlow lam c u v = (c * lam v) * B.phat v u := fun _ => rfl
  rw [Finset.sum_congr rfl fun u _ => hrw u, ← Finset.mul_sum, B.phat_row_sum, mul_one]

/-- **The wrap edge carries `c λ(s₀)`** (`proofs.tex:998`):
`e(s_f → s₀) = c λ(s₀) π̂_←(s₀ → s_f) = c λ(s₀)`, which is `Z` at `c = Z/λ(s₀)`. -/
theorem edgeFlow_wrap (lam : V → ℝ) (c : ℝ) : B.edgeFlow lam c G.snk G.src = c * lam G.src := by
  simp only [edgeFlow, B.phat_src_snk, mul_one]

/-- Off the wrap edge, `s_f` emits nothing: `e(s_f → v) = 0` for `v ≠ s₀`. This is what makes
cutting the wrap edge leave conservation untouched at every internal vertex. -/
theorem edgeFlow_snk_out (lam : V → ℝ) (c : ℝ) {v : V} (hv : v ≠ G.src) :
    B.edgeFlow lam c G.snk v = 0 := by
  simp only [edgeFlow, B.phat_snk_of_ne_src hv, mul_zero]

/-- Nothing but the wrap edge enters `s₀`: `e(u → s₀) = 0` for `u ≠ s_f`. -/
theorem edgeFlow_to_src (lam : V → ℝ) (c : ℝ) {u : V} (hu : u ≠ G.snk) :
    B.edgeFlow lam c u G.src = 0 := by
  simp only [edgeFlow, B.phat_src_of_ne hu, mul_zero]

/-- **The star outflow is the flow out of `u` along every edge but the terminating one**:
`f_out^*(u) = ∑_{v ≠ s_f} e(u → v)`. This is the circulation identity with the term at `s_f`
removed, and it is what makes `f_out^* ≥ 0` and the vanishing analysis below elementary. -/
theorem outflowStar_eq_sum {lam : V → ℝ} (h : B.IsInvProb lam) (c : ℝ) (u : V) :
    B.outflowStar lam c u = ∑ v ∈ Finset.univ.erase G.snk, B.edgeFlow lam c u v := by
  have htot := B.sum_edgeFlow_out h c u
  have hsplit : (∑ v ∈ Finset.univ.erase G.snk, B.edgeFlow lam c u v)
      + B.edgeFlow lam c u G.snk = ∑ v, B.edgeFlow lam c u v :=
    Finset.sum_erase_add _ _ (Finset.mem_univ G.snk)
  simp only [outflowStar]
  linarith

/-- **`f_out^* ≥ 0`**: a sum of non-negative edge flows. -/
theorem outflowStar_nonneg {lam : V → ℝ} (h : B.IsInvProb lam) {c : ℝ} (hc : 0 ≤ c) (u : V) :
    0 ≤ B.outflowStar lam c u := by
  rw [B.outflowStar_eq_sum h c u]
  exact Finset.sum_nonneg fun v _ => B.edgeFlow_nonneg h.nonneg hc u v

/-- **Where the star outflow vanishes, no non-terminating edge carries flow.** This is the
content of the paper's parenthesis "at states where `f_out^*` vanishes the trajectory terminates
almost surely and the policy is immaterial". -/
theorem edgeFlow_eq_zero_of_outflowStar {lam : V → ℝ} (h : B.IsInvProb lam) {c : ℝ} (hc : 0 ≤ c)
    {u : V} (hu : B.outflowStar lam c u = 0) {v : V} (hv : v ≠ G.snk) :
    B.edgeFlow lam c u v = 0 := by
  rw [B.outflowStar_eq_sum h c u] at hu
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun w _ => B.edgeFlow_nonneg h.nonneg hc u w)).mp hu v
    (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)

/-- **`f_out^*(u) π_→^*(u → v) = e(u → v)`** (`proofs.tex:1003`) at every `u` and every
`v ≠ s_f` — including the states where `f_out^*(u) = 0` and the quotient defining `π_→^*` is
Lean's junk value, since there both sides are `0`. Only this product is ever summed. -/
theorem outflowStar_mul_fwdStar {lam : V → ℝ} (h : B.IsInvProb lam) {c : ℝ} (hc : 0 ≤ c) (u : V)
    {v : V} (hv : v ≠ G.snk) :
    B.outflowStar lam c u * B.fwdStar lam c u v = B.edgeFlow lam c u v := by
  by_cases hu : B.outflowStar lam c u = 0
  · rw [hu, zero_mul, B.edgeFlow_eq_zero_of_outflowStar h hc hu hv]
  · simp only [fwdStar]
    field_simp

/-- Where the star outflow does not vanish, `π_→^*(u → ·)` is a probability on `𝒱 ∖ {s_f}`. -/
theorem sum_fwdStar {lam : V → ℝ} (h : B.IsInvProb lam) (c : ℝ) {u : V}
    (hu : B.outflowStar lam c u ≠ 0) :
    ∑ v ∈ Finset.univ.erase G.snk, B.fwdStar lam c u v = 1 := by
  simp only [fwdStar]
  rw [← Finset.sum_div, ← B.outflowStar_eq_sum h c u, div_self hu]

/-- **`π_→^*` is a Markov kernel on `𝒮`** where the star outflow does not vanish: nothing leaves
an internal state towards `s₀`, so the row already summing to `1` over `𝒱 ∖ {s_f}` sums to `1`
over `𝒮`. Not a claim of the paper — a consistency check on calling `π_→^*` a policy. -/
theorem sum_fwdStar_internal {lam : V → ℝ} (h : B.IsInvProb lam) (c : ℝ) {u : V}
    (husnk : u ≠ G.snk) (hu : B.outflowStar lam c u ≠ 0) :
    ∑ v ∈ G.internal, B.fwdStar lam c u v = 1 := by
  have hsrc : B.fwdStar lam c u G.src = 0 := by
    simp only [fwdStar, B.edgeFlow_to_src lam c husnk, zero_div]
  have hsplit : (∑ v ∈ (Finset.univ.erase G.snk).erase G.src, B.fwdStar lam c u v)
      + B.fwdStar lam c u G.src = ∑ v ∈ Finset.univ.erase G.snk, B.fwdStar lam c u v :=
    Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨G.src_ne_snk, Finset.mem_univ _⟩)
  rw [MarkedGraph.internal_eq_erase_src]
  rw [B.sum_fwdStar h c hu] at hsplit
  rw [hsrc, add_zero] at hsplit
  exact hsplit

/-- **The initial flow has total mass `c λ(s₀)`** (`proofs.tex:998`), which is `Z` at
`c = Z/λ(s₀)`. -/
theorem sum_initFlow {lam : V → ℝ} (h : B.IsInvProb lam) (c : ℝ) :
    ∑ v, B.initFlow lam c v = c * lam G.src :=
  B.sum_edgeFlow_out h c G.src

/-- **`F_term = κ := Z π_←(s_f → ·)`** (`proofs.tex:999–1003`), using `λ(s_f) = λ(s₀)`. -/
theorem termFlow_eq_target {lam : V → ℝ} (h : B.IsInvProb lam) {c Z : ℝ}
    (hcZ : c * lam G.src = Z) (x : V) : B.termFlow lam c x = Z * B.pb G.snk x := by
  have hsnk : B.phat G.snk x = B.pb G.snk x := B.phat_of_ne_src (Ne.symm G.src_ne_snk)
  simp only [termFlow, edgeFlow, h.lam_snk_eq_src, hsnk, hcZ]

/-- **`κ` is positive on every terminating state** (`proofs.tex:1003`): `π_←` is positive on
every edge `x → s_f`. -/
theorem termFlow_pos_of_edge (hbpos : B.PositiveOnEdges) {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    {c : ℝ} (hc : 0 < c) {x : V} (hx : G.Edge x G.snk) : 0 < B.termFlow lam c x := by
  have hsnk : B.phat G.snk x = B.pb G.snk x := B.phat_of_ne_src (Ne.symm G.src_ne_snk)
  simp only [termFlow, edgeFlow, hsnk]
  exact mul_pos (mul_pos hc (hlam G.snk)) (hbpos hx)

/-- **`theo:universality_graphs`*(3)*, flow matching, exactly** (`proofs.tex:1004–1009`): at
every internal state the defect of `equ:FM_const` is `0`. -/
theorem fmDefect_eq_zero {lam : V → ℝ} (h : B.IsInvProb lam) {c : ℝ} (hc : 0 ≤ c) {v : V}
    (hv : v ∈ G.internal) : B.fmDefect lam c v = 0 := by
  obtain ⟨hvsrc, hvsnk⟩ := MarkedGraph.mem_internal.mp hv
  have hsum : ∑ u ∈ G.internal, B.outflowStar lam c u * B.fwdStar lam c u v
      = ∑ u ∈ G.internal, B.edgeFlow lam c u v :=
    Finset.sum_congr rfl fun u _ => B.outflowStar_mul_fwdStar h hc u hvsnk
  have hrw : B.fmDefect lam c v
      = B.initFlow lam c v + (∑ u ∈ G.internal, B.edgeFlow lam c u v)
        - B.termFlow lam c v - B.outflowStar lam c v := by
    simp only [fmDefect, hsum]
  have h1 : (∑ u ∈ Finset.univ.erase G.src, B.edgeFlow lam c u v) + B.edgeFlow lam c G.src v
      = ∑ u, B.edgeFlow lam c u v :=
    Finset.sum_erase_add _ _ (Finset.mem_univ G.src)
  have h2 : (∑ u ∈ G.internal, B.edgeFlow lam c u v) + B.edgeFlow lam c G.snk v
      = ∑ u ∈ Finset.univ.erase G.src, B.edgeFlow lam c u v :=
    Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm G.src_ne_snk, Finset.mem_univ _⟩)
  have h3 := B.sum_edgeFlow_in lam c v
  have h4 := B.edgeFlow_snk_out lam c hvsrc
  rw [hrw]
  simp only [initFlow, termFlow, outflowStar]
  linarith

/-- **`theo:universality_graphs`*(3)*, flow matching**, in the paper's own form
(`proofs.tex:1004–1009`): `F_init(v) + ((f_out^* μ) π_→^*)(v) = F_term(v) + f_out^*(v)` at every
`v ∈ 𝒮`. -/
theorem flow_matching {lam : V → ℝ} (h : B.IsInvProb lam) {c : ℝ} (hc : 0 ≤ c) {v : V}
    (hv : v ∈ G.internal) :
    B.initFlow lam c v + (∑ u ∈ G.internal, B.outflowStar lam c u * B.fwdStar lam c u v)
      = B.termFlow lam c v + B.outflowStar lam c v := by
  have := B.fmDefect_eq_zero h hc hv
  simp only [fmDefect] at this
  linarith

/-- **The residuals vanish** (`proofs.tex:981`, "all residuals `δF_init`, `δF_term` are zero").
Pointwise on `𝒮`, hence in every `L^p` at once, the state space being finite — the `p`-uniformity
of the paper's closing sentence is subsumed by a pointwise identity. `δf_init = D⁻` and
`δf_term = D⁺` is the sign convention of `theo:universality_L2_full` and of
`GFNBounds.Core.resInit` / `resTerm`. -/
theorem residuals_eq_zero {lam : V → ℝ} (h : B.IsInvProb lam) {c : ℝ} (hc : 0 ≤ c) {v : V}
    (hv : v ∈ G.internal) : (B.fmDefect lam c v)⁻ = 0 ∧ (B.fmDefect lam c v)⁺ = 0 := by
  rw [B.fmDefect_eq_zero h hc hv]
  exact ⟨negPart_zero, posPart_zero⟩

/-- **`theo:universality_graphs`*(3)*** (`proofs.tex:975–979`, proof `proofs.tex:993–1009`), in
one statement. At `c = Z/λ(s₀)`, the flow of item *(2)* with its wrap edge cut is a generative
flow on `G`: the wrap edge carried `Z`, the initial flow has total mass `Z`, the terminal flow is
`κ = Z π_←(s_f → ·)` and is positive on every terminating state, the star outflow is
non-negative, and the flow-matching constraint holds **exactly** at every internal state.

The sampler clause of item *(3)* is not here; it rests on `theo:sampling_theorem`, which the
paper cites and does not prove. See the module SCOPE. -/
theorem universality_graphs_three (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam : V → ℝ} (h : B.IsInvProb lam) {Z c : ℝ} (hZ : 0 < Z) (hc : c = Z / lam G.src) :
    0 < c ∧ c * lam G.src = Z ∧
      B.edgeFlow lam c G.snk G.src = Z ∧
      (∑ v, B.initFlow lam c v) = Z ∧
      (∀ x, B.termFlow lam c x = Z * B.pb G.snk x) ∧
      (∀ x, G.Edge x G.snk → 0 < B.termFlow lam c x) ∧
      (∀ u, 0 ≤ B.outflowStar lam c u) ∧
      (∀ v ∈ G.internal, B.fmDefect lam c v = 0) := by
  have hlam : ∀ x, 0 < lam x := fun x => h.pos hpc hbpos x
  have hcpos : 0 < c := by rw [hc]; exact div_pos hZ (hlam G.src)
  have hcZ : c * lam G.src = Z := by
    rw [hc]; exact div_mul_cancel₀ Z (hlam G.src).ne'
  refine ⟨hcpos, hcZ, ?_, ?_, fun x => B.termFlow_eq_target h hcZ x,
    fun x hx => B.termFlow_pos_of_edge hbpos hlam hcpos hx,
    fun u => B.outflowStar_nonneg h hcpos.le u, fun v hv => B.fmDefect_eq_zero h hcpos.le hv⟩
  · rw [B.edgeFlow_wrap lam c, hcZ]
  · rw [B.sum_initFlow h c, hcZ]

end BackwardPolicy

end GFNBounds.Graph
