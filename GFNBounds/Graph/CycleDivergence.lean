import GFNBounds.Graph.FrozenUnstable
import GFNBounds.Balance.Freezing
import GFNBounds.Core.StableBound

/-!
# No bound on the sampling error can hold for a divergence-based FM loss: the cyclic counter-example

**`theo:no_bound_divergence`** — statement `cv_divergence.tex:7–19`, proof `proofs.tex:385–400`.

(The bold-backtick form of the label, alone on its line, is what the paper-side ledger
machine-reads. **This label has no `paper-map.json` row and none can be added here**: its
`\label` lives in `cv_divergence.tex`, which is not among `scripts/paper.py`'s `SOURCES`
(`proofs.tex`, `silva_comparison.tex`, `app_doubling.tex`), so `scripts/trace_check.py`'s
invariant *(c)* does not fire on it and citing it is safe — `GFNBounds/Graph/CycleExample.lean:24`
already does. Widening the charter is the author's decision, not this file's; the paper-side
`FORMALIZATION-LEDGER.md` is where `theo:no_bound_divergence` should record that it is
formalized, in the scaffold, under this module.)

> (`theo:no_bound_divergence`) Let `𝓛(F)` be a divergence-based FM-loss on a directed graph
> `𝒢`, depending on a target `target` and on a training distribution `ν_train`; the supremum
> below ranges over the pairs `(𝒢, target)` with `#𝒢 = N`.
>
> `∀ N ≥ 2, ∀ ε > 0 : inf_{ν_train} sup_{#𝒢 = N} sup_{F : 𝓛(F) ≤ ε} TV(s_τ ‖ target) = 1`.

and its proof, whose four steps this file follows:

> Consider the cyclic graph `𝒞_N` with states `x₁,…,x_N`, cycle edges `xᵢ → x_{i+1 mod N}`,
> initial edge `s₀ → x₁` and a terminal edge `xᵢ → s_f` for every `i`; for `δ ∈ (0,1)` let
> `target(x₁) = 1 − δ` and `target(xᵢ) = δ/(N−1)` otherwise.
>
> Let `F̂` be the unit-mass flow routed `s₀ → x₁ → x₂ → s_f`: it satisfies the flow-matching
> constraint `equ:FM_const` with terminal flow `μ := δ_{x₂}`, so by Theorem
> `theo:sampling_theorem` its sampler satisfies `s_τ ∼ μ`. Let `γ` be the unit circulation on the
> cycle (`γ = 1` on each edge `xᵢ → x_{i+1}`): `γ` is a `0`-flow in the sense of
> `brunswic2024theory`, so `F_k := F̂ + kγ` remains flow-matching with the same terminal flow
> `μ`, and `s_τ(F_k) ∼ μ` for every `k`. Hence
> `TV(s_τ(F_k) ‖ target) = TV(μ, target) = 1 − target(x₂) = 1 − δ/(N−1)`.
>
> A divergence-based FM loss evaluates a function `g`, continuous at `1` with `g(1) = 0` and
> `g > 0` elsewhere, of the ratio of the two sides of the flow-matching constraint
> `equ:FM_const`. At every state both sides gain `k` from the circulation:
> `ρ_k(xᵢ) = (F_init + f^k_←)(xᵢ) / (target + f^k_→)(xᵢ) = (aᵢ + k)/(bᵢ + k) ⟶ 1`
> uniformly on the finite graph — including at `x₁`, where the target mismatch
> `target(x₁) = 1 − δ` is drowned by the circulation. Hence `𝓛(F_k) = ∫ g(ρ_k) dν_train → 0` for
> *every* finite `ν_train`, and `𝓛(F_k) ≤ ε` for `k` large.
>
> Therefore `sup_{#𝒢=N} sup_{𝓛≤ε} TV ≥ 1 − δ/(N−1)` for every `δ > 0`, so it equals `1`; the
> construction being independent of `ν_train`, the infimum over `ν_train` is also `1`.

## The modelling decisions

**The denominator carries the target, not the flow's own terminal flow, and that is forced.**
`fmRatio` is `(F_init + f_←)/(target + f_→)`, which is the paper's display verbatim. The
alternative reading — the model's own terminal flow in the denominator — makes the statement
true but empty: `F_k` is *exactly* flow-matching to its own terminal flow `δ_{x₂}`, so every
ratio would be `1`, the loss would be `0` for every `k`, and the circulation would play no part.
What the theorem says is that the loss is measured against the **target** while the sampler emits
the flow's **own** terminal flow, and that a circulation drives the first to zero without moving
the second. Nothing in `cv_divergence.tex:7–19` or `proofs.tex:385–400` says in words which
terminal flow the loss compares against; the display at `proofs.tex:395` is the only place it is
fixed, and it fixes it as the target. See SCOPE for the clarifying clause this file suggests.

**The `aᵢ` and `bᵢ`, which the paper leaves abstract, are computed here.** On `𝒞_N` with `F̂`
routed `s₀ → x₁ → x₂ → s_f`, `F_init = δ_{x₁}`, `f_←(x₂) = 1` and `f_→(x₁) = 1` with everything
else `0`, so the circulation gives

  `a₁ = a₂ = 1`, `aᵢ = 0` for `i ≥ 3`; `b₁ = 2 − δ`, `bᵢ = δ/(N−1)` for `i ≥ 2`

(`aC`, `bC`, `fmRatio_Fk`). `b₁ = (1 − δ) + 1` is the target mismatch *plus* the outflow `F̂`
already carries along `x₁ → x₂` — this is the `x₁` the paper singles out.

**`N ≥ 2` is carried as `N = M + 2`.** It is used twice and only twice: `x₁ ≠ x₂`, without which
the routed flow is not defined, and `N − 1 ≠ 0`, without which the target is not. Writing the
vertex index set as `Fin (M+2)` supplies both as instances, and `exists_cycle_of_size` recovers
the paper's quantifier `∀ N ≥ 2`.

**The vertex type is `Option (Option (Fin N))`, not `Fin (N+2)`.** `none` is `s₀`, `some none` is
`s_f`, `some (some i)` is `xᵢ₊₁`. This is a bookkeeping choice with no mathematical content: it
makes `Fintype.sum_option` split every sum into the two marks and the `N` internal states
(`sum_cycV`), and it keeps the cycle's wrap-around `x_N → x₁` as `Fin N`'s own `i + 1`, rather
than as a `Fin.val` case split inside `Fin (N+2)`.

**Flow matching is conservation at the internal states.** On a marked graph, `equ:FM_const` at
`v ∈ 𝒮` reads `F_init(v) + f_←(v) = F_term(v) + f_→(v)`; since `s_f` emits nothing and `s₀`
receives nothing, its two sides are the total inflow `∑_u F(u→v)` and the total outflow
`∑_w F(v→w)`. So `Fk_flowMatching` states `edgeInflow = edgeOutflow` on `𝒮`, in the vocabulary
`GFNBounds/Graph/FrozenUnstable.lean` already uses for `0`-flows.

## What is proved

| | |
|---|---|
| `cycV`, `srcC`, `snkC`, `xC`, `sum_cycV` | the vertex set of `𝒞_N` and the splitting of a sum over it |
| `cycEdge`, `cycGraph` | `𝒞_N` as a `MarkedGraph`, all three fields discharged |
| `internal_eq`, `sum_internal`, `mem_internal_iff` | `𝒮 = {x₁,…,x_N}` |
| `card_internal`, `exists_cycle_of_size` | `#𝒢 = N`, for every `N ≥ 2` |
| `unitEdge` and its marginals | the single-edge flows every flow here is a finite sum of |
| `Fhat`, `gammaC` | `F̂` and `γ` |
| `isCirculation_gammaC`, `gammaMC` | `γ` is a `0`-flow, packaged as the `MarkedCirculation` of `GFNBounds.Graph` |
| `Fk`, `Fk_nonneg`, `Fk_supp` | `F_k = F̂ + kγ`, non-negative and carried by the edges |
| `Fk_flowMatching` | `F_k` satisfies `equ:FM_const` at every internal state, for every `k` |
| `targetC`, `sum_targetC` | the target, and that it is a probability on `𝒮` |
| `fmRatio`, `fmLossTarget` | `ρ` and `𝓛_{g,ν}(F) = ∫ g(ρ) dν` |
| `aC`, `bC`, `edgeInflow_Fk_x`, `foutC_Fk_x`, `fmRatio_Fk` | the closed form `ρ_k(xᵢ) = (aᵢ+k)/(bᵢ+k)` |
| `tendsto_affine_ratio`, `fmRatio_Fk_tendsto_one` | `ρ_k → 1` |
| `fmLossTarget_Fk_tendsto_zero`, `exists_Fk_loss_le` | `𝓛(F_k) → 0`, hence `≤ ε` for some `k ≥ 0` |
| `termLaw`, `sum_termFlow_Fk`, `termLaw_Fk` | the normalized terminal flow of `F_k` is `δ_{x₂}`, for every `k` |
| `tvFin`, `tvFin_termLaw_Fk` | `TV(δ_{x₂} ‖ target) = 1 − δ/(N−1)` |
| `no_bound_divergence` | the five conjuncts at one flow |
| `no_bound_divergence_sup` | the `= 1` reading: `∀ η < 1` some `δ` beats `η` |
| `ratio_eq_fmRatio`, `fmLossTarget_eq_loss` | the loss here **is** `GFNBounds.Balance.loss`, not a new notion |
| `Fk_snk_row`, `foutC_Fk_srcC`, `Fk_lam_ne_zero` | that identification's one hypothesis holds at every `F_k` |
| `tvFin_eq_tvD_count` | `tvFin` is `GFNBounds.Core.tvD` against the counting measure |

## SCOPE (disclosed)

* **The sampler is not formalized, and `s_τ` is not what is measured here.** `tvFin_termLaw_Fk`
  measures the target against the **normalized terminal flow** `F(·→s_f)/F(𝒮→s_f)`. Identifying
  that with the law of `s_τ` is `theo:sampling_theorem`, which the paper restates from
  `bengio2021flow, brunswic2024theory` and does **not** prove; no Markov chain, no sampling time
  and no `τ` appears below. That step is cited, never discharged — and, per `CLAUDE.md` rule 1,
  not smuggled in as an axiom either.
* **The DB and TB variants are not stated.** The proof's last sentence covers them by citing
  Theorem 3 of `brunswic2024theory`; nothing here mentions a DB or a TB loss.
* **`sup_{#𝒢 = N}` is read as "on `𝒞_N`".** A supremum over graphs is bounded below by its value
  at one graph, which is all the proof uses; `exists_cycle_of_size` supplies a graph of the right
  size for every `N ≥ 2`. Formalizing the supremum itself would need a type of finite marked
  graphs of given size, which nothing in this library has.
* **`inf_{ν_train}` is read as "for every `ν`".** `nu` is universally quantified and the
  construction does not mention it — the paper's own "the construction being independent of
  `ν_train`". This is the stronger reading: it bounds the sup below at every `ν`, hence bounds
  the inf of the sups. No positivity, normalization or finiteness is asked of `ν`.
* **`= 1` is delivered as a supremum, not as a value.** No single flow attains `1`:
  `tvFin_termLaw_Fk` is exactly `1 − δ/(N−1) < 1` for `δ > 0`, and `δ = 0` is outside the
  paper's `δ ∈ (0,1)` (at `δ = 0` the target is `δ_{x₁}` and the statement still holds, with TV
  exactly `1`, but that is not the paper's construction). `no_bound_divergence_sup` gives the
  `∀ η < 1, ∃ δ` form, which is what "`= 1`" means for a supremum that is not attained.
* **`g > 0` off `1` is not carried, because this direction does not use it.** Only `g(1) = 0`
  and continuity of `g` at `1` enter, and only through `fmLossTarget_Fk_tendsto_zero`. The
  hypothesis is what makes `𝓛` a *divergence* — what forces `𝓛(F) = 0` to mean flow matching —
  and it is needed for the converse reading of the loss, not for the upper bound `𝓛(F_k) ≤ ε`.
  Continuity is asked only **at `1`**, as the paper asks it.
* **The loss is a definition, not a derivation.** `fmLossTarget` is `∑_{x ∈ 𝒮} ν(x) g(ρ(x))`;
  that this is "a divergence-based FM-loss" in the sense of `brunswic2024theory` is the paper's
  own sentence at `proofs.tex:393`, taken here as the definition. `fmLossTarget_eq_loss` shows it
  is `GFNBounds.Balance.loss` at `λ := target + f_→`, `u := 1` and the row-normalized kernel
  `T(x→y) := F(x→y)/λ(x)`, so it is not a notion invented for this file; the hypothesis that
  identification needs — the row of `F` is empty wherever `λ` vanishes — is discharged for every
  `F_k` with `k ≥ 0`, `δ ∈ (0,1)` by `Fk_lam_ne_zero`.
* **A clarifying clause the paper may want.** `proofs.tex:388` says `F̂` "satisfies the
  flow-matching constraint `equ:FM_const` with terminal flow `μ := δ_{x₂}`" while
  `proofs.tex:395` evaluates the ratio of the two sides of that same constraint with `target` in
  the denominator. Both are right, but they are two different readings of `equ:FM_const` — one
  with the flow's own `F_term`, one with the target — a sentence apart, and only the second makes
  the theorem non-trivial. One clause saying that the loss holds `F_term := target` fixed while
  the sampler uses the flow's own terminal flow would remove the ambiguity. Recorded, not
  applied: nothing in this repository edits the draft.
* **No `sorry`.** Every declaration below is closed.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N ≥ 2` | ✓ carried, as `N = M + 2`; `exists_cycle_of_size` restores `∀ N ≥ 2` |
| `ε > 0` | ✓ `heps` |
| the supremum ranges over graphs with `#𝒢 = N` | ⚠ **read as "on `𝒞_N`"**, with `card_internal` witnessing `#𝒢 = N`; see SCOPE |
| the infimum ranges over training distributions | ⚠ **read as "for every `ν`"** — stronger, and what the construction delivers; see SCOPE |
| `𝒞_N`: cycle edges, initial edge, a terminal edge at every state | ✓ `cycEdge`, `cycGraph` |
| `δ ∈ (0,1)`, `target(x₁) = 1−δ`, `target(xᵢ) = δ/(N−1)` | ✓ `targetC`, `hd0`, `hd1`; `sum_targetC` checks it is a probability |
| `F̂` the unit flow routed `s₀ → x₁ → x₂ → s_f` | ✓ `Fhat` |
| `γ` the unit circulation on the cycle, a `0`-flow | ✓ `gammaC`, `isCirculation_gammaC`, `gammaMC` |
| `F_k := F̂ + kγ` flow-matching for every `k` | ✓ `Fk_flowMatching`, at every internal state and exactly |
| `g` continuous at `1` | ✓ `ContinuousAt g 1` |
| `g(1) = 0` | ✓ `hg1` |
| `g > 0` elsewhere | ✗ **not carried** — unused in this direction; see SCOPE |
| `𝓛(F) = ∫ g(ρ) dν_train` | ✓ `fmLossTarget`, identified with `Balance.loss` by `fmLossTarget_eq_loss` |
| `ρ = (F_init + f_←)/(target + f_→)` | ✓ `fmRatio`, with the **target** in the denominator; see the modelling decisions |
| `s_τ ∼ μ` by `theo:sampling_theorem` | ✗ **not certified** — TV is measured against the normalized terminal flow; see SCOPE |
| `TV` the `½`-convention total variation | ✓ `tvFin`, bridged to `GFNBounds.Core.tvD` by `tvFin_eq_tvD_count` |
| the DB and TB variants | ✗ **not stated** — they rest on a cited theorem; see SCOPE |
| the conclusion `= 1` | ⚠ delivered as `∀ η < 1, ∃ δ, TV > η` (`no_bound_divergence_sup`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
namespace GFNBounds.Graph
namespace CycleDivergence

/-! ### The vertex set of `C_N` -/

/-- The vertices of the cyclic graph `C_N`, `N = M + 2`: `none` is `s₀`, `some none` is `s_f`,
and `some (some i)` is the internal state `x_{i+1}`. Writing `N` as `M + 2` is how `N ≥ 2` is
carried: it makes `0` and `1` available in `Fin N` and `N − 1 = M + 1` non-zero. -/
abbrev cycV (M : ℕ) := Option (Option (Fin (M + 2)))

/-- The source `s₀`. -/
def srcC (M : ℕ) : cycV M := none

/-- The sink `s_f`. -/
def snkC (M : ℕ) : cycV M := some none

/-- The internal state `x_{i+1}`; `xC M 0` is the paper's `x₁` and `xC M 1` its `x₂`. -/
def xC (M : ℕ) (i : Fin (M + 2)) : cycV M := some (some i)

variable {M : ℕ}

@[simp] theorem xC_inj {i j : Fin (M + 2)} : xC M i = xC M j ↔ i = j := by
  simp [xC]

theorem xC_injective (M : ℕ) : Function.Injective (xC M) := fun _ _ h => xC_inj.mp h

@[simp] theorem xC_ne_srcC (i : Fin (M + 2)) : xC M i ≠ srcC M := by simp [xC, srcC]

@[simp] theorem xC_ne_snkC (i : Fin (M + 2)) : xC M i ≠ snkC M := by simp [xC, snkC]

@[simp] theorem srcC_ne_xC (i : Fin (M + 2)) : srcC M ≠ xC M i := by simp [xC, srcC]

@[simp] theorem snkC_ne_xC (i : Fin (M + 2)) : snkC M ≠ xC M i := by simp [xC, snkC]

@[simp] theorem srcC_ne_snkC : srcC M ≠ snkC M := by simp [srcC, snkC]

@[simp] theorem snkC_ne_srcC : snkC M ≠ srcC M := by simp [srcC, snkC]

/-- Case analysis on a vertex, in the paper's names. -/
theorem cycV_cases {p : cycV M → Prop} (hs : p (srcC M)) (ht : p (snkC M))
    (hx : ∀ i, p (xC M i)) : ∀ v, p v := by
  rintro (_ | (_ | i))
  · exact hs
  · exact ht
  · exact hx i

/-- Every sum over the vertices splits into the two marks and the `N` internal states. -/
theorem sum_cycV (f : cycV M → ℝ) :
    ∑ v, f v = f (srcC M) + (f (snkC M) + ∑ i, f (xC M i)) := by
  rw [Fintype.sum_option, Fintype.sum_option]
  rfl

/-! ### The graph `C_N` -/

/-- **`theo:no_bound_divergence`, the graph `𝒞_N`** (`proofs.tex:387`): the initial edge
`s₀ → x₁`, a terminal edge `xᵢ → s_f` for every `i`, and the cycle edges `xᵢ → x_{i+1 mod N}`.
The wrap-around is `Fin N`'s own arithmetic: `(N−1) + 1 = 0`. -/
def cycEdge (M : ℕ) (u v : cycV M) : Prop :=
  (u = srcC M ∧ v = xC M 0) ∨ (∃ i, u = xC M i ∧ v = snkC M) ∨
    (∃ i, u = xC M i ∧ v = xC M (i + 1))

/-- **`theo:no_bound_divergence`, the marked graph `𝒞_N`**: `s₀` receives no edge (the three
edge families all end at an internal state or at `s_f`) and `s_f` emits none. -/
def cycGraph (M : ℕ) : MarkedGraph (cycV M) where
  Edge := cycEdge M
  src := srcC M
  snk := snkC M
  src_ne_snk := srcC_ne_snkC
  no_edge_into_src := by
    intro x h
    rcases h with ⟨-, h⟩ | ⟨i, -, h⟩ | ⟨i, -, h⟩ <;> simp [srcC, snkC, xC] at h
  no_edge_out_of_snk := by
    intro y h
    rcases h with ⟨h, -⟩ | ⟨i, h, -⟩ | ⟨i, h, -⟩ <;> simp [srcC, snkC, xC] at h

@[simp] theorem cycGraph_src : (cycGraph M).src = srcC M := rfl

@[simp] theorem cycGraph_snk : (cycGraph M).snk = snkC M := rfl

theorem cycGraph_edge_iff {u v : cycV M} : (cycGraph M).Edge u v ↔ cycEdge M u v := Iff.rfl

/-- The internal state space `𝒮 = 𝒱 ∖ {s₀, s_f}` is exactly the `N` states `x₁,…,x_N`. -/
theorem internal_eq (M : ℕ) :
    (cycGraph M).internal = Finset.univ.map ⟨xC M, xC_injective M⟩ := by
  ext v
  rw [MarkedGraph.mem_internal]
  refine cycV_cases (p := fun v => (v ≠ (cycGraph M).src ∧ v ≠ (cycGraph M).snk) ↔
    v ∈ Finset.univ.map ⟨xC M, xC_injective M⟩) ?_ ?_ ?_ v
  · simp
  · simp
  · intro i
    simp only [cycGraph_src, cycGraph_snk, xC_ne_srcC, xC_ne_snkC, ne_eq, not_false_eq_true,
      and_self, true_iff, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk]
    exact ⟨i, trivial, rfl⟩

/-- A sum over `𝒮` is a sum over the `N` internal indices. -/
theorem sum_internal (f : cycV M → ℝ) :
    ∑ x ∈ (cycGraph M).internal, f x = ∑ i, f (xC M i) := by
  rw [internal_eq, Finset.sum_map]
  rfl

/-- Membership in `𝒮`, in the paper's names. -/
theorem mem_internal_iff {v : cycV M} : v ∈ (cycGraph M).internal ↔ ∃ i, v = xC M i := by
  rw [internal_eq]
  simp [Finset.mem_map, eq_comm]

/-- **`#𝒞_N = N`**: the graph has exactly `N = M + 2` internal states, which is what the
supremum of `theo:no_bound_divergence` ranges over. -/
theorem card_internal (M : ℕ) : (cycGraph M).internal.card = M + 2 := by
  rw [internal_eq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-! ### Unit edges -/

variable {V : Type*}

/-- The edgeflow carrying mass `1` on the single transition `a → b` and nothing elsewhere. Every
flow below is a finite sum of these. -/
def unitEdge [DecidableEq V] (a b : V) : V → V → ℝ := fun u v => if u = a ∧ v = b then 1 else 0

variable [DecidableEq V]

theorem unitEdge_nonneg (a b u v : V) : 0 ≤ unitEdge a b u v := by
  unfold unitEdge; split <;> norm_num

theorem unitEdge_eq_zero_of_ne {a b u v : V} (h : ¬ (u = a ∧ v = b)) : unitEdge a b u v = 0 :=
  if_neg h

theorem unitEdge_of_ne_zero {a b u v : V} (h : unitEdge a b u v ≠ 0) : u = a ∧ v = b := by
  by_contra hc
  exact h (unitEdge_eq_zero_of_ne hc)

variable [Fintype V]

theorem edgeInflow_unitEdge (a b v : V) :
    edgeInflow (unitEdge a b) v = if v = b then 1 else 0 := by
  by_cases hv : v = b <;> simp [edgeInflow, unitEdge, hv]

theorem edgeOutflow_unitEdge (a b u : V) :
    edgeOutflow (unitEdge a b) u = if u = a then 1 else 0 := by
  by_cases hu : u = a <;> simp [edgeOutflow, unitEdge, hu]

omit [DecidableEq V] in
theorem edgeInflow_add (F G : V → V → ℝ) (v : V) :
    edgeInflow (F + G) v = edgeInflow F v + edgeInflow G v := by
  simp only [edgeInflow, Pi.add_apply, Finset.sum_add_distrib]

omit [DecidableEq V] in
theorem edgeOutflow_add (F G : V → V → ℝ) (u : V) :
    edgeOutflow (F + G) u = edgeOutflow F u + edgeOutflow G u := by
  simp only [edgeOutflow, Pi.add_apply, Finset.sum_add_distrib]

omit [Fintype V] in
theorem unitEdge_eq_zero_of_ne_left {a b u : V} (h : u ≠ a) (v : V) : unitEdge a b u v = 0 :=
  unitEdge_eq_zero_of_ne fun hc => h hc.1

omit [Fintype V] in
theorem unitEdge_eq_zero_of_ne_right {a b v : V} (h : v ≠ b) (u : V) : unitEdge a b u v = 0 :=
  unitEdge_eq_zero_of_ne fun hc => h hc.2

omit [Fintype V] in
theorem unitEdge_left (a b v : V) : unitEdge a b a v = if v = b then 1 else 0 := by
  by_cases hv : v = b <;> simp [unitEdge, hv]

omit [Fintype V] in
theorem unitEdge_right (a b u : V) : unitEdge a b u b = if u = a then 1 else 0 := by
  by_cases hu : u = a <;> simp [unitEdge, hu]

/-! ### The two flows: the routed unit flow `F̂` and the unit circulation `γ` -/

/-- **`theo:no_bound_divergence`, the flow `F̂`** (`proofs.tex:388`): the unit-mass flow routed
`s₀ → x₁ → x₂ → s_f`. -/
noncomputable def Fhat (M : ℕ) : cycV M → cycV M → ℝ :=
  unitEdge (srcC M) (xC M 0) + unitEdge (xC M 0) (xC M 1) + unitEdge (xC M 1) (snkC M)

theorem Fhat_apply (u v : cycV M) :
    Fhat M u v = unitEdge (srcC M) (xC M 0) u v + unitEdge (xC M 0) (xC M 1) u v
      + unitEdge (xC M 1) (snkC M) u v := rfl

/-- **`theo:no_bound_divergence`, the unit circulation `γ`** (`proofs.tex:388`): `γ = 1` on each
cycle edge `xᵢ → x_{i+1}`, `0` elsewhere. -/
noncomputable def gammaC (M : ℕ) : cycV M → cycV M → ℝ :=
  ∑ i, unitEdge (xC M i) (xC M (i + 1))

theorem gammaC_apply (u v : cycV M) :
    gammaC M u v = ∑ i, unitEdge (xC M i) (xC M (i + 1)) u v := by
  simp only [gammaC, Finset.sum_apply]

theorem Fhat_nonneg (u v : cycV M) : 0 ≤ Fhat M u v := by
  rw [Fhat_apply]
  have h1 := unitEdge_nonneg (srcC M) (xC M 0) u v
  have h2 := unitEdge_nonneg (xC M 0) (xC M 1) u v
  have h3 := unitEdge_nonneg (xC M 1) (snkC M) u v
  linarith

theorem gammaC_nonneg (u v : cycV M) : 0 ≤ gammaC M u v := by
  rw [gammaC_apply]
  exact Finset.sum_nonneg fun i _ => unitEdge_nonneg _ _ _ _

theorem gammaC_srcC (u : cycV M) : gammaC M u (srcC M) = 0 := by
  rw [gammaC_apply]
  exact Finset.sum_eq_zero fun i _ => unitEdge_eq_zero_of_ne_right (srcC_ne_xC (i + 1)) u

theorem gammaC_snkC (u : cycV M) : gammaC M u (snkC M) = 0 := by
  rw [gammaC_apply]
  exact Finset.sum_eq_zero fun i _ => unitEdge_eq_zero_of_ne_right (snkC_ne_xC (i + 1)) u

theorem Fhat_srcC (u : cycV M) : Fhat M u (srcC M) = 0 := by
  rw [Fhat_apply, unitEdge_eq_zero_of_ne_right (srcC_ne_xC (M := M) 0) u,
    unitEdge_eq_zero_of_ne_right (srcC_ne_xC (M := M) 1) u,
    unitEdge_eq_zero_of_ne_right (srcC_ne_snkC (M := M)) u, add_zero, add_zero]

theorem Fhat_snkC (u : cycV M) : Fhat M u (snkC M) = if u = xC M 1 then 1 else 0 := by
  rw [Fhat_apply, unitEdge_eq_zero_of_ne_right (snkC_ne_xC (M := M) 0) u,
    unitEdge_eq_zero_of_ne_right (snkC_ne_xC (M := M) 1) u, unitEdge_right, zero_add, zero_add]

/-! ### The marginals of `F̂` and of `γ` -/

theorem edgeInflow_Fhat (v : cycV M) :
    edgeInflow (Fhat M) v = (if v = xC M 0 then 1 else 0) + (if v = xC M 1 then 1 else 0)
      + (if v = snkC M then 1 else 0) := by
  simp only [Fhat, edgeInflow_add, edgeInflow_unitEdge]

theorem edgeOutflow_Fhat (u : cycV M) :
    edgeOutflow (Fhat M) u = (if u = srcC M then 1 else 0) + (if u = xC M 0 then 1 else 0)
      + (if u = xC M 1 then 1 else 0) := by
  simp only [Fhat, edgeOutflow_add, edgeOutflow_unitEdge]

theorem edgeInflow_gammaC (v : cycV M) :
    edgeInflow (gammaC M) v = ∑ i, (if v = xC M (i + 1) then (1 : ℝ) else 0) := by
  simp only [edgeInflow, gammaC_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => edgeInflow_unitEdge _ _ v

theorem edgeOutflow_gammaC (u : cycV M) :
    edgeOutflow (gammaC M) u = ∑ i, (if u = xC M i then (1 : ℝ) else 0) := by
  simp only [edgeOutflow, gammaC_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => edgeOutflow_unitEdge _ _ u

theorem edgeInflow_gammaC_x (j : Fin (M + 2)) : edgeInflow (gammaC M) (xC M j) = 1 := by
  rw [edgeInflow_gammaC]
  have h : ∀ i : Fin (M + 2),
      (if xC M j = xC M (i + 1) then (1 : ℝ) else 0) = if i = j - 1 then 1 else 0 := by
    intro i
    have hiff : (j = i + 1) ↔ (i = j - 1) :=
      ⟨fun h => eq_sub_of_add_eq h.symm, fun h => by rw [h, sub_add_cancel]⟩
    simp only [xC_inj, hiff]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem edgeOutflow_gammaC_x (i : Fin (M + 2)) : edgeOutflow (gammaC M) (xC M i) = 1 := by
  rw [edgeOutflow_gammaC]
  simp

theorem edgeInflow_gammaC_srcC : edgeInflow (gammaC M) (srcC M) = 0 := by
  rw [edgeInflow_gammaC]; simp

theorem edgeInflow_gammaC_snkC : edgeInflow (gammaC M) (snkC M) = 0 := by
  rw [edgeInflow_gammaC]; simp

theorem edgeOutflow_gammaC_srcC : edgeOutflow (gammaC M) (srcC M) = 0 := by
  rw [edgeOutflow_gammaC]; simp

theorem edgeOutflow_gammaC_snkC : edgeOutflow (gammaC M) (snkC M) = 0 := by
  rw [edgeOutflow_gammaC]; simp

/-- **`γ` is a `0`-flow** (`proofs.tex:388`): every internal state gains `1` and loses `1`, and
the cycle touches neither mark. -/
theorem isCirculation_gammaC (M : ℕ) : IsCirculation (gammaC M) := by
  show ∀ x : cycV M, edgeOutflow (gammaC M) x = edgeInflow (gammaC M) x
  refine cycV_cases ?_ ?_ ?_
  · rw [edgeOutflow_gammaC_srcC, edgeInflow_gammaC_srcC]
  · rw [edgeOutflow_gammaC_snkC, edgeInflow_gammaC_snkC]
  · intro i; rw [edgeOutflow_gammaC_x, edgeInflow_gammaC_x]

/-- **`γ` as the `MarkedCirculation` of `GFNBounds.Graph`** — the hypothesis bundle
`prop:frozen_unstable_full` consumes of its own `1_γ`, here discharged rather than assumed. -/
noncomputable def gammaMC (M : ℕ) : MarkedCirculation (cycGraph M) where
  circ := gammaC M
  nonneg := gammaC_nonneg
  isCirculation := isCirculation_gammaC M
  ne_zero := by
    intro h
    have h1 : edgeOutflow (gammaC M) (xC M 0) = 1 := edgeOutflow_gammaC_x 0
    rw [h] at h1
    simp [edgeOutflow] at h1
  inflow_src := edgeInflow_gammaC_srcC
  inflow_snk := edgeInflow_gammaC_snkC

/-! ### The family `F_k = F̂ + kγ` -/

/-- **`theo:no_bound_divergence`, the family `F_k := F̂ + kγ`** (`proofs.tex:388`). -/
noncomputable def Fk (M : ℕ) (k : ℝ) : cycV M → cycV M → ℝ :=
  fun u v => Fhat M u v + k * gammaC M u v

theorem edgeInflow_Fk (k : ℝ) (v : cycV M) :
    edgeInflow (Fk M k) v = edgeInflow (Fhat M) v + k * edgeInflow (gammaC M) v := by
  simp only [edgeInflow, Fk, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem edgeOutflow_Fk (k : ℝ) (u : cycV M) :
    edgeOutflow (Fk M k) u = edgeOutflow (Fhat M) u + k * edgeOutflow (gammaC M) u := by
  simp only [edgeOutflow, Fk, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem Fk_nonneg {k : ℝ} (hk : 0 ≤ k) (u v : cycV M) : 0 ≤ Fk M k u v :=
  add_nonneg (Fhat_nonneg u v) (mul_nonneg hk (gammaC_nonneg u v))

theorem Fk_srcC (k : ℝ) (u : cycV M) : Fk M k u (srcC M) = 0 := by
  simp only [Fk, Fhat_srcC, gammaC_srcC, mul_zero, add_zero]

theorem Fk_snkC (k : ℝ) (u : cycV M) : Fk M k u (snkC M) = if u = xC M 1 then 1 else 0 := by
  simp only [Fk, Fhat_snkC, gammaC_snkC, mul_zero, add_zero]

/-- Every transition `F_k` charges is an edge of `𝒞_N`: `F̂` rides on the initial edge, one
cycle edge and one terminal edge, and `γ` on the cycle. -/
theorem Fk_supp {k : ℝ} {u v : cycV M} (h : Fk M k u v ≠ 0) : (cycGraph M).Edge u v := by
  by_cases hg : gammaC M u v = 0
  · have hF : Fhat M u v ≠ 0 := by
      simp only [Fk, hg, mul_zero, add_zero] at h
      exact h
    rw [Fhat_apply] at hF
    by_cases e1 : unitEdge (srcC M) (xC M 0) u v = 0
    · by_cases e2 : unitEdge (xC M 0) (xC M 1) u v = 0
      · have e3 : unitEdge (xC M 1) (snkC M) u v ≠ 0 := by
          rw [e1, e2, zero_add, zero_add] at hF
          exact hF
        obtain ⟨hu, hv⟩ := unitEdge_of_ne_zero e3
        exact Or.inr (Or.inl ⟨1, hu, hv⟩)
      · obtain ⟨hu, hv⟩ := unitEdge_of_ne_zero e2
        refine Or.inr (Or.inr ⟨0, hu, ?_⟩)
        rw [hv, zero_add]
    · exact Or.inl (unitEdge_of_ne_zero e1)
  · rw [gammaC_apply] at hg
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
    exact Or.inr (Or.inr ⟨i, unitEdge_of_ne_zero hi⟩)

/-- **`F_k` is flow-matching for every `k`** (`proofs.tex:388`): the circulation adds `k` to the
inflow and `k` to the outflow of every internal state, so the constraint `equ:FM_const` at `𝒮`
— which on a marked graph is conservation at the internal states — is untouched. -/
theorem Fk_flowMatching (k : ℝ) :
    ∀ x ∈ (cycGraph M).internal, edgeInflow (Fk M k) x = edgeOutflow (Fk M k) x := by
  intro x hx
  obtain ⟨j, rfl⟩ := mem_internal_iff.mp hx
  rw [edgeInflow_Fk, edgeOutflow_Fk, edgeInflow_Fhat, edgeOutflow_Fhat,
    edgeInflow_gammaC_x, edgeOutflow_gammaC_x]
  simp

/-! ### Two index sums on `Fin N` -/

theorem zero_ne_one_fin (M : ℕ) : (0 : Fin (M + 2)) ≠ 1 := zero_ne_one

theorem sum_fin_ite_zero (A B : ℝ) :
    ∑ i : Fin (M + 2), (if i = 0 then A else B) = A + ((M : ℝ) + 1) * B := by
  have h : ∀ i : Fin (M + 2), (if i = 0 then A else B) = B + (if i = 0 then A - B else 0) := by
    intro i; by_cases hi : i = 0 <;> simp [hi]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h i, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_ite_eq' Finset.univ (0 : Fin (M + 2)) (fun _ => A - B),
    if_pos (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem sum_fin_ite_two (A B C : ℝ) :
    ∑ i : Fin (M + 2), (if i = 0 then A else if i = 1 then B else C) = A + B + (M : ℝ) * C := by
  have h : ∀ i : Fin (M + 2), (if i = 0 then A else if i = 1 then B else C)
      = C + ((if i = 0 then A - C else 0) + (if i = 1 then B - C else 0)) := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [if_pos rfl, if_pos rfl, if_neg (zero_ne_one_fin M)]; ring
    · by_cases hj : i = 1
      · subst hj; rw [if_neg hi, if_pos rfl, if_neg hi, if_pos rfl]; ring
      · rw [if_neg hi, if_neg hj, if_neg hi, if_neg hj]; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h i, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (M + 2)) (fun _ => A - C),
    Finset.sum_ite_eq' Finset.univ (1 : Fin (M + 2)) (fun _ => B - C),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

/-! ### The target -/

/-- **`theo:no_bound_divergence`, the target** (`proofs.tex:387`): `target(x₁) = 1 − δ` and
`target(xᵢ) = δ/(N−1)` for `i ≥ 2`, with `N − 1 = M + 1`. The two marks carry no target mass —
the target is a measure on the internal state space `𝒮`. -/
noncomputable def targetC (M : ℕ) (delta : ℝ) : cycV M → ℝ
  | none => 0
  | some none => 0
  | some (some i) => if i = 0 then 1 - delta else delta / ((M : ℝ) + 1)

@[simp] theorem targetC_srcC (delta : ℝ) : targetC M delta (srcC M) = 0 := rfl

@[simp] theorem targetC_snkC (delta : ℝ) : targetC M delta (snkC M) = 0 := rfl

@[simp] theorem targetC_x (delta : ℝ) (i : Fin (M + 2)) :
    targetC M delta (xC M i) = if i = 0 then 1 - delta else delta / ((M : ℝ) + 1) := rfl

/-- **The target is a probability measure on `𝒮`**: `(1 − δ) + (N − 1)·δ/(N − 1) = 1`. -/
theorem sum_targetC (delta : ℝ) : ∑ v, targetC M delta v = 1 := by
  have hM : ((M : ℝ) + 1) ≠ 0 := by positivity
  rw [sum_cycV, targetC_srcC, targetC_snkC]
  simp only [targetC_x]
  rw [sum_fin_ite_zero]
  field_simp
  ring

/-! ### The flow-matching ratio against the target, and the divergence loss -/

/-- **`theo:no_bound_divergence`, the ratio of the two sides of `equ:FM_const`**
(`proofs.tex:393`): `ρ(x) = (F_init + f_←)(x)/(target + f_→)(x)`, with the **target** in the
denominator in place of the flow's own terminal flow. On a marked graph `F_init + f_←` is the
total inflow `∑_u F(u → x)` — `s_f` emits nothing — and `f_→` is the outflow along the internal
edges, `∑_{v ∈ 𝒮} F(x → v)`. See the module SCOPE for why the denominator carries the target. -/
noncomputable def fmRatio (G : MarkedGraph V) (target : V → ℝ) (F : V → V → ℝ) (x : V) : ℝ :=
  edgeInflow F x / (target x + ∑ v ∈ G.internal, F x v)

/-- **`theo:no_bound_divergence`, a divergence-based FM loss** (`proofs.tex:393`):
`𝓛(F) = ∫ g(ρ) dν_train`, the integral over the internal states of a generator `g` of the ratio
of the two sides of the flow-matching constraint. -/
noncomputable def fmLossTarget (G : MarkedGraph V) (g : ℝ → ℝ) (nu target : V → ℝ)
    (F : V → V → ℝ) : ℝ :=
  ∑ x ∈ G.internal, nu x * g (fmRatio G target F x)

/-! ### The closed forms `ρ_k(xᵢ) = (aᵢ + k)/(bᵢ + k)` -/

/-- **The numerators `aᵢ` of `proofs.tex:395`**: `a₁ = a₂ = 1`, `aᵢ = 0` for `i ≥ 3`. -/
noncomputable def aC (M : ℕ) (i : Fin (M + 2)) : ℝ := if i = 0 then 1 else if i = 1 then 1 else 0

/-- **The denominators `bᵢ` of `proofs.tex:395`**: `b₁ = 2 − δ`, `bᵢ = δ/(N−1)` for `i ≥ 2`. -/
noncomputable def bC (M : ℕ) (delta : ℝ) (i : Fin (M + 2)) : ℝ :=
  if i = 0 then 2 - delta else delta / ((M : ℝ) + 1)

theorem sum_internal_row (F : cycV M → cycV M → ℝ) (u : cycV M) :
    ∑ v ∈ (cycGraph M).internal, F u v = edgeOutflow F u - F u (srcC M) - F u (snkC M) := by
  rw [sum_internal]
  have h : ∑ v, F u v = F u (srcC M) + (F u (snkC M) + ∑ i, F u (xC M i)) := sum_cycV _
  simp only [edgeOutflow]
  linarith

/-- `aᵢ` is the sum of the two indicators `F̂` contributes to the inflow at `xᵢ`. -/
theorem indicator_add (j : Fin (M + 2)) :
    (if j = 0 then (1 : ℝ) else 0) + (if j = 1 then (1 : ℝ) else 0) = aC M j := by
  rw [aC]
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h1 : j = 1 <;> simp [h0, h1]

/-- **The numerator of `ρ_k` at an internal state**: `(F_init + f^k_←)(xᵢ) = aᵢ + k`. -/
theorem edgeInflow_Fk_x (k : ℝ) (j : Fin (M + 2)) :
    edgeInflow (Fk M k) (xC M j) = aC M j + k := by
  rw [edgeInflow_Fk, edgeInflow_Fhat, edgeInflow_gammaC_x, mul_one, if_neg (xC_ne_snkC j)]
  simp only [xC_inj]
  rw [add_zero, indicator_add]

/-- **The outflow half of the denominator**: `f^k_→(xᵢ) = 1_{i=1} + k`, the circulation adding
`k` at every internal state. -/
theorem foutC_Fk_x (k : ℝ) (j : Fin (M + 2)) :
    ∑ v ∈ (cycGraph M).internal, Fk M k (xC M j) v = (if j = 0 then 1 else 0) + k := by
  rw [sum_internal_row, edgeOutflow_Fk, edgeOutflow_Fhat, edgeOutflow_gammaC_x, mul_one,
    Fk_srcC, Fk_snkC, if_neg (xC_ne_srcC j)]
  simp only [xC_inj]
  split_ifs <;> ring

/-- **`theo:no_bound_divergence`, the closed form of the ratio** (`proofs.tex:395`):
`ρ_k(xᵢ) = (aᵢ + k)/(bᵢ + k)`, with `a₁ = a₂ = 1`, `aᵢ = 0` for `i ≥ 3`, `b₁ = 2 − δ` and
`bᵢ = δ/(N−1)` for `i ≥ 2`. At `x₁` the target mismatch `1 − δ` sits in `b₁ = 2 − δ`: it is what
the circulation drowns. -/
theorem fmRatio_Fk (k delta : ℝ) (j : Fin (M + 2)) :
    fmRatio (cycGraph M) (targetC M delta) (Fk M k) (xC M j)
      = (aC M j + k) / (bC M delta j + k) := by
  rw [fmRatio, edgeInflow_Fk_x, foutC_Fk_x, targetC_x, bC]
  by_cases h0 : j = 0
  · subst h0; rw [if_pos rfl, if_pos rfl, if_pos rfl]; ring_nf
  · rw [if_neg h0, if_neg h0, if_neg h0]; ring_nf

/-! ### The ratios tend to `1`, so the loss tends to `0` -/

/-- **`ρ_k → 1`** (`proofs.tex:395`): a quotient of two affine functions of `k` with the same
slope tends to `1`, whatever the intercepts — this is the scale invariance along `0`-flows. -/
theorem tendsto_affine_ratio (a b : ℝ) :
    Filter.Tendsto (fun k : ℝ => (a + k) / (b + k)) Filter.atTop (nhds 1) := by
  have hb : Filter.Tendsto (fun k : ℝ => b + k) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ b Filter.tendsto_id
  have h1 : Filter.Tendsto (fun k : ℝ => 1 + (a - b) / (b + k)) Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add (hb.const_div_atTop _)
  rw [add_zero] at h1
  refine Filter.Tendsto.congr' ?_ h1
  filter_upwards [Filter.eventually_gt_atTop |b|] with k hk
  have hbk : b + k ≠ 0 := by
    have hba : -|b| ≤ b := neg_abs_le b
    intro hc
    have : |b| < -b := by linarith
    linarith [neg_abs_le b, le_abs_self b]
  field_simp
  ring

theorem fmRatio_Fk_tendsto_one (delta : ℝ) (j : Fin (M + 2)) :
    Filter.Tendsto (fun k : ℝ => fmRatio (cycGraph M) (targetC M delta) (Fk M k) (xC M j))
      Filter.atTop (nhds 1) := by
  simp only [fmRatio_Fk]
  exact tendsto_affine_ratio _ _

/-- **`𝓛(F_k) → 0`** (`proofs.tex:396`): a finite sum of terms `ν(x) g(ρ_k(x))`, each tending to
`ν(x) g(1) = 0` by continuity of `g` at `1`. Only `g(1) = 0` and continuity at `1` are used;
`g > 0` off `1` is not. -/
theorem fmLossTarget_Fk_tendsto_zero (g : ℝ → ℝ) (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (nu : cycV M → ℝ) (delta : ℝ) :
    Filter.Tendsto (fun k : ℝ => fmLossTarget (cycGraph M) g nu (targetC M delta) (Fk M k))
      Filter.atTop (nhds 0) := by
  have hterm : ∀ x ∈ (cycGraph M).internal,
      Filter.Tendsto (fun k : ℝ => nu x * g (fmRatio (cycGraph M) (targetC M delta) (Fk M k) x))
        Filter.atTop (nhds (nu x * g 1)) := by
    intro x hx
    obtain ⟨j, rfl⟩ := mem_internal_iff.mp hx
    exact (hgc.tendsto.comp (fmRatio_Fk_tendsto_one delta j)).const_mul (nu (xC M j))
  have hsum := tendsto_finsetSum (cycGraph M).internal hterm
  simp only [hg1, mul_zero, Finset.sum_const_zero] at hsum
  exact hsum

/-- **`𝓛(F_k) ≤ ε` for `k` large** (`proofs.tex:396`). -/
theorem exists_Fk_loss_le (g : ℝ → ℝ) (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (nu : cycV M → ℝ) (delta : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ k : ℝ, 0 ≤ k ∧ fmLossTarget (cycGraph M) g nu (targetC M delta) (Fk M k) ≤ eps := by
  have h := fmLossTarget_Fk_tendsto_zero g hg1 hgc nu delta
  have h2 : ∀ᶠ k : ℝ in Filter.atTop,
      fmLossTarget (cycGraph M) g nu (targetC M delta) (Fk M k) < eps := h (Iio_mem_nhds heps)
  obtain ⟨k, hk1, hk2⟩ := (h2.and (Filter.eventually_ge_atTop 0)).exists
  exact ⟨k, hk2, hk1.le⟩

/-! ### The terminal law, and its distance to the target -/

/-- The **normalized terminal flow** of an edgeflow, `F(·→s_f)/F(𝒮→s_f)`. This is the law
`theo:sampling_theorem` identifies with `s_τ`; that identification is cited, not proved — see the
module SCOPE. -/
noncomputable def termLaw (G : MarkedGraph V) (F : V → V → ℝ) : V → ℝ :=
  fun x => F x G.snk / ∑ y, F y G.snk

/-- The `½`-convention total variation of `app:notation` between two densities on a finite state
space, `TV(p‖q) = ½ ∑ |p − q|`. -/
noncomputable def tvFin (p q : V → ℝ) : ℝ := (1 / 2) * ∑ x, |p x - q x|

theorem sum_termFlow_Fk (k : ℝ) : ∑ y, Fk M k y (snkC M) = 1 := by
  simp only [Fk_snkC, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **`theo:no_bound_divergence`, the terminal law is `δ_{x₂}` for every `k`**
(`proofs.tex:388`): the circulation charges no terminal edge, so `F_k` and `F̂` have the same
terminal flow `μ = δ_{x₂}`, of mass `1`. -/
theorem termLaw_Fk (k : ℝ) (x : cycV M) :
    termLaw (cycGraph M) (Fk M k) x = if x = xC M 1 then 1 else 0 := by
  show Fk M k x (cycGraph M).snk / ∑ y, Fk M k y (cycGraph M).snk = _
  rw [cycGraph_snk, sum_termFlow_Fk, div_one, Fk_snkC]

/-- **`theo:no_bound_divergence`, the total variation is `1 − δ/(N−1)`** (`proofs.tex:390`):
`TV(δ_{x₂} ‖ target) = 1 − target(x₂)`. -/
theorem tvFin_termLaw_Fk (k : ℝ) {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    tvFin (termLaw (cycGraph M) (Fk M k)) (targetC M delta) = 1 - delta / ((M : ℝ) + 1) := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hdnn : 0 ≤ delta / ((M : ℝ) + 1) := div_nonneg h0 hM.le
  have hdle : delta / ((M : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hM]
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hsrc : |(if srcC M = xC M 1 then (1 : ℝ) else 0) - targetC M delta (srcC M)| = 0 := by
    rw [if_neg (srcC_ne_xC 1), targetC_srcC, sub_zero, abs_zero]
  have hsnk : |(if snkC M = xC M 1 then (1 : ℝ) else 0) - targetC M delta (snkC M)| = 0 := by
    rw [if_neg (snkC_ne_xC 1), targetC_snkC, sub_zero, abs_zero]
  have hterm : ∀ i : Fin (M + 2),
      |(if xC M i = xC M 1 then (1 : ℝ) else 0) - targetC M delta (xC M i)|
        = if i = 0 then 1 - delta else
            if i = 1 then 1 - delta / ((M : ℝ) + 1) else delta / ((M : ℝ) + 1) := by
    intro i
    simp only [xC_inj, targetC_x]
    by_cases hi : i = 0
    · subst hi
      rw [if_neg (zero_ne_one_fin M), if_pos rfl, if_pos rfl, zero_sub, abs_neg,
        abs_of_nonneg (by linarith)]
    · by_cases hj : i = 1
      · subst hj
        rw [if_pos rfl, if_neg hi, if_neg hi, if_pos rfl, abs_of_nonneg (by linarith)]
      · rw [if_neg hj, if_neg hi, if_neg hi, if_neg hj, zero_sub, abs_neg,
          abs_of_nonneg hdnn]
  simp only [tvFin, termLaw_Fk]
  rw [sum_cycV, hsrc, hsnk, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i,
    sum_fin_ite_two]
  field_simp
  ring

/-! ### The theorem -/

/-- **`theo:no_bound_divergence`** — `cv_divergence.tex:7–19`, proof `proofs.tex:385–400` — on
the cyclic graph `𝒞_N`, `N = M + 2`.

For every generator `g` continuous at `1` with `g(1) = 0`, every training distribution `ν`, every
`δ ∈ (0,1)` and every `ε > 0` there is an edgeflow `F` on `𝒞_N` which is non-negative, rides on
the edges, is **exactly** flow-matching at every internal state, has FM loss at most `ε`, and
whose normalized terminal flow is at total variation `1 − δ/(N−1)` from the target. Letting
`δ → 0` (`no_bound_divergence_sup`) pushes that distance above every `η < 1`.

The construction does not depend on `ν`, which is the paper's "the construction being
independent of `ν_train`, the infimum over `ν_train` is also `1`". -/
theorem no_bound_divergence (M : ℕ) (g : ℝ → ℝ) (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (nu : cycV M → ℝ) {delta eps : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) (heps : 0 < eps) :
    ∃ F : cycV M → cycV M → ℝ,
      (∀ u v, 0 ≤ F u v) ∧
      (∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v) ∧
      (∀ x ∈ (cycGraph M).internal, edgeInflow F x = edgeOutflow F x) ∧
      fmLossTarget (cycGraph M) g nu (targetC M delta) F ≤ eps ∧
      tvFin (termLaw (cycGraph M) F) (targetC M delta) = 1 - delta / ((M : ℝ) + 1) := by
  obtain ⟨k, hk0, hk⟩ := exists_Fk_loss_le g hg1 hgc nu delta heps
  exact ⟨Fk M k, Fk_nonneg hk0, fun _ _ h => Fk_supp h, Fk_flowMatching k, hk,
    tvFin_termLaw_Fk k hd0.le hd1.le⟩

/-- **`theo:no_bound_divergence`, the `= 1` reading**: the supremum is not attained but is `1`,
because `δ` is free. For every `η < 1` some `δ ∈ (0,1)` puts a flow of loss `≤ ε` at total
variation more than `η` from its target. -/
theorem no_bound_divergence_sup (M : ℕ) (g : ℝ → ℝ) (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (nu : cycV M → ℝ) {eps : ℝ} (heps : 0 < eps) {eta : ℝ} (heta : eta < 1) :
    ∃ (delta : ℝ) (F : cycV M → cycV M → ℝ), 0 < delta ∧ delta < 1 ∧
      (∀ u v, 0 ≤ F u v) ∧
      (∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v) ∧
      (∀ x ∈ (cycGraph M).internal, edgeInflow F x = edgeOutflow F x) ∧
      fmLossTarget (cycGraph M) g nu (targetC M delta) F ≤ eps ∧
      eta < tvFin (termLaw (cycGraph M) F) (targetC M delta) := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  set delta : ℝ := min (1 / 2) ((1 - eta) * ((M : ℝ) + 1) / 2) with hdef
  have hd0 : 0 < delta := lt_min (by norm_num) (by positivity)
  have hd1 : delta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  obtain ⟨F, h1, h2, h3, h4, h5⟩ := no_bound_divergence M g hg1 hgc nu hd0 hd1 heps
  refine ⟨delta, F, hd0, hd1, h1, h2, h3, h4, ?_⟩
  rw [h5]
  have hle : delta ≤ (1 - eta) * ((M : ℝ) + 1) / 2 := min_le_right _ _
  have : delta / ((M : ℝ) + 1) < 1 - eta := by
    rw [div_lt_iff₀ hM]
    nlinarith
  linarith

/-- **The supremum ranges over graphs of size `N`**: for every `N ≥ 2` the family above contains
a graph with exactly `N` internal states, which is what `#𝒢 = N` asks. -/
theorem exists_cycle_of_size (N : ℕ) (hN : 2 ≤ N) : ∃ M : ℕ, (cycGraph M).internal.card = N :=
  ⟨N - 2, by rw [card_internal]; omega⟩

/-! ### The loss is the library's own `𝓛_{g,ν}`, at a kernel read off the flow -/

/-- **The ratio `ρ` is `GFNBounds.Balance`'s `r = d(μT)/dμ`** at `λ := target + f_→`, `u := 1`
and the kernel `T(x→y) := F(x→y)/λ(x)` normalising each row of the flow. The hypothesis is the
only thing that can go wrong: where `λ` vanishes the kernel is Lean's `x/0 = 0` and the row is
lost, so the row of `F` there must already be empty. -/
theorem ratio_eq_fmRatio (G : MarkedGraph V) (target : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ x, target x + (∑ v ∈ G.internal, F x v) = 0 → ∀ y, F x y = 0) (y : V) :
    Balance.ratio (fun x y => F x y / (target x + ∑ v ∈ G.internal, F x v))
        (fun x => target x + ∑ v ∈ G.internal, F x v) 1 y = fmRatio G target F y := by
  simp only [Balance.ratio, Balance.pushMass, fmRatio, Pi.one_apply, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : target x + ∑ v ∈ G.internal, F x v = 0
  · rw [hx, zero_mul, hF x hx y]
  · field_simp

/-- **`fmLossTarget` is `GFNBounds.Balance.loss`**, not a new notion: the divergence FM loss of
`theo:no_bound_divergence` is the library's `𝓛_{g,ν}(μ) = ∑_x ν(x) g(r(x))` at the kernel and
reference measure above, with `ν` extended by `0` off the internal states. -/
theorem fmLossTarget_eq_loss (G : MarkedGraph V) (g : ℝ → ℝ) (nu target : V → ℝ)
    (F : V → V → ℝ) (hF : ∀ x, target x + (∑ v ∈ G.internal, F x v) = 0 → ∀ y, F x y = 0) :
    fmLossTarget G g nu target F
      = Balance.loss (fun x y => F x y / (target x + ∑ v ∈ G.internal, F x v))
          (fun x => target x + ∑ v ∈ G.internal, F x v)
          (fun x => if x ∈ G.internal then nu x else 0) 1 g := by
  rw [Balance.loss, ← Finset.sum_subset (Finset.subset_univ G.internal)
    (fun x _ hx => by rw [if_neg hx, zero_mul])]
  exact Finset.sum_congr rfl fun x hx => by
    rw [if_pos hx, ratio_eq_fmRatio G target F hF x]

/-! ### The hypothesis of `fmLossTarget_eq_loss` holds for `F_k` -/

/-- `s_f` emits nothing under `F_k` — it emits nothing in `𝒞_N`. -/
theorem Fk_snk_row (k : ℝ) (y : cycV M) : Fk M k (snkC M) y = 0 := by
  by_contra h
  exact (cycGraph M).no_edge_out_of_snk y (Fk_supp h)

/-- `F_k` sends unit mass out of `s₀`, along the initial edge: `F_init(𝒮) = 1`. -/
theorem foutC_Fk_srcC (k : ℝ) : ∑ v ∈ (cycGraph M).internal, Fk M k (srcC M) v = 1 := by
  rw [sum_internal_row, edgeOutflow_Fk, edgeOutflow_Fhat, edgeOutflow_gammaC_srcC, mul_zero,
    Fk_srcC, Fk_snkC]
  simp

theorem Fk_lam_ne_zero {k delta : ℝ} (hk : 0 ≤ k) (hd0 : 0 < delta) (hd1 : delta < 1) :
    ∀ x, targetC M delta x + (∑ v ∈ (cycGraph M).internal, Fk M k x v) = 0 →
      ∀ y, Fk M k x y = 0 := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  refine cycV_cases ?_ ?_ ?_
  · intro h
    rw [targetC_srcC, foutC_Fk_srcC, zero_add] at h
    exact absurd h one_ne_zero
  · intro _ y; exact Fk_snk_row k y
  · intro j h
    rw [targetC_x, foutC_Fk_x] at h
    by_cases h0 : j = 0
    · rw [if_pos h0, if_pos h0] at h; linarith
    · rw [if_neg h0, if_neg h0] at h
      have : 0 < delta / ((M : ℝ) + 1) := div_pos hd0 hM
      linarith

/-! ### The finite total variation is the library's measure-theoretic one -/

omit [DecidableEq V] in
/-- **`tvFin` is `GFNBounds.Core.tvD` against the counting measure** — the `½`-convention TV of
`app:notation` read on a finite state space, so the value `1 − δ/(N−1)` above is the paper's
`TV(s_τ ‖ target)` and not a separate notion. -/
theorem tvFin_eq_tvD_count [MeasurableSpace V] [MeasurableSingletonClass V] (p q : V → ℝ) :
    tvFin p q = Core.tvD MeasureTheory.Measure.count p q := by
  rw [Core.tvD, tvFin, MeasureTheory.integral_count]

end CycleDivergence
end GFNBounds.Graph
