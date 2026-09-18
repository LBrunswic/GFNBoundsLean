import GFNBounds.Core.StrongUniversality
import GFNBounds.Graph.Universality

/-!
# Universality of an arbitrary family of generative flows, and targets without full support

**`def:universality`** — `universality.tex:10–19` (draft commit `3194054`).

**`rem:partial_support`** — `proofs.tex:1181–1183` (draft commit `3194054`; a remark, no proof
environment — every sentence is certified as a claim).

(The bold-backtick form of each label is what `formalization_ledger.py`'s docstring scan and
`scripts/trace_check.py` read. Line citations to `proofs.tex` drift, `kb/entries/0036`.)

> (`def:universality`) Let `Θ` be a family of generative flows on a statespace `(𝒮, ν_B)` with
> `ν_B` finite and let `p ∈ [1,∞]`. The family `Θ` is weakly `L^p`-universal if its `π⋆`
> component is bounded as an operator from `L^p(ν_B)` to `L^p(ν_B)` and for any distributions
> `F_init, F_term ≪ ν_B` of equal total mass whose densities lie in `L^p(ν_B)` (equal masses are
> forced: the defect integrates to `F_init(𝒮) − F_term(𝒮)`, so unequal masses floor the infimum
> away from `0`)
> `inf_{(π⋆, f_out⋆) ∈ Θ} (‖δf_init‖_{L^p(ν_B)} + ‖δf_term‖_{L^p(ν_B)}) = 0`
> for `(π⋆, f_out⋆)` as a generative flow from `F_init` to `F_term`.
> The family `Θ` is strongly universal if the zero infimum is realized (a flow realizing it for
> `(F_init, F_term)` has almost-everywhere-zero residuals, so realizes it for that pair at every
> `r ∈ [1,p]`).

> (`rem:partial_support`, targets without full support) If the target `R` vanishes on some
> terminating states, let `G'` be the marked subgraph of `G` induced on `s₀`, `s_f` and the states
> from which a directed path of `G` reaches `supp R`, `supp R` included, with the terminating edges
> `y → s_f`, `R(y) = 0`, deleted. It is again path-connected, and a backward policy on `G` positive
> on its edges restricts to one on `G'` with only its sink row renormalized. Theorem
> `theo:universality_graphs` applied to `G'` gives a flow which, extended by zero, satisfies the
> flow-matching constraint `equ:FM_const` on `G` exactly, with terminal flow `R`; it belongs to the
> frozen-backward family of `G'`, not to that of `G`. Alternatively, if `R` has mass `Z` and `unif`
> is the uniform probability on the terminating states, the full-support targets
> `(1−ε)R + εZ unif` realize `R` as a limit of exactly matched flows: the universality infimum
> over the union of the frozen-backward families of `G`, one for each backward policy positive on
> its edges, still vanishes, and it is not attained, every element of that union being either the
> trivial element or a flow whose terminal flow `Z' π_←(s_f → ·)`, `Z' > 0`, is positive on every
> terminating state.

The notation `δF_term = (F_init + F⋆_in − F⋆_out − F_term)⁺`, `δF_init = (…)⁻` is
`proofs.tex:45–51`; a generative flow is a Markov kernel `π⋆` with an integrable outflow
`f_out⋆ ≥ 0`, and `‖π⋆‖_{L^p(ν_B)} = sup ‖f π⋆‖_{L^p}/‖f‖_{L^p}` is `proofs.tex:16–21`.

## What is proved — `def:universality`

| | |
|---|---|
| `IsGenerativeFlow`, `IsFlowFamily` | the objects: `π⋆` Markov, `f_out⋆ ≥ 0` integrable |
| `defectFn`, `resInitFn`, `resTermFn`, `residual` | `D = f_init + P⋆f_out − f_out − f_term`, `δf_init = D⁻`, `δf_term = D⁺`, and `‖δf_init‖_p + ‖δf_term‖_p ∈ [0, ∞]` |
| `IsAdmissiblePair`, `IsBoundedPolicy` | the pairs quantified over, and the boundedness requirement |
| `WeaklyUniversal`, `StronglyUniversal` | **the definition, for an arbitrary family `Θ`** |
| `iInf_eq_zero_iff` | the infimum read as an `ε`-statement |
| `StronglyUniversal.weaklyUniversal` | strong ⇒ weak |
| `ae_eq_zero_of_residual_eq_zero`, `realizes_of_le`, `StronglyUniversal.realizes_of_le` | **the second parenthetical (ruling R6)**: a realizing flow has a.e.-zero residuals, and realizes the pair at every `r ≤ p` |
| `integral_defectFn`, `ofReal_abs_mass_le_residual`, `mass_gap_div_le_iInf`, `iInf_pos_of_mass_ne` | **the first parenthetical**: `∫ D = F_init(𝒮) − F_term(𝒮)`, and the explicit floor `|F_init(𝒮) − F_term(𝒮)| / ν(𝒮)^{1−1/p}` |
| `fixedPolicyFamily`, `weaklyUniversal_fixedPolicyFamily_iff`, `stronglyUniversal_fixedPolicyFamily_iff` | **the bridge**: at `Θ = {π⋆} × L^p_+` the definition is *equivalent* to the library's `Core.WeaklyUniversal` / `Core.StronglyUniversal` |
| `weaklyUniversal_fixedPolicyFamily_of_kernel`, `stronglyUniversal_fixedPolicyFamily_top` | `theo:universality_L2_full`'s two conclusions, in the definition's own terms |
| `weaklyUniversal_const_kernel`, `stronglyUniversal_const_kernel_top` | **inhabitation**: the i.i.d. resampling policy `π⋆(x) = ν` is weakly universal at every finite `p` and strongly universal at `p = ∞` |

## What is proved — `rem:partial_support`

| paper | here |
|---|---|
| `G'` | `subVerts`, `subGraph` |
| `G'` is path-connected | `subGraph_pathConnected` |
| a policy on `G` restricts to `G'`, only its sink row renormalized | `restrict_policy` (via `restrictWith`, `renormRow`) |
| theorem on `G'`, extended by zero: exact flow matching on `G`, terminal flow `R`, in `Θ` of `G'` | `partial_support_exact` — with the sink row frozen to `R/Z`, see SCOPE |
| … not in the frozen-backward family of `G` | `not_memberFlow`, `partial_support_not_in_G` |
| `(1−ε)R + εZ unif` realize `R` as a limit of exactly matched flows | `epsTarget`, `isTarget_epsTarget`, `epsTarget_pos`, `sum_epsTarget`, `member_epsTarget` |
| the infimum over the union vanishes | `iInf_graphResidual_eq_zero`, at every `p` |
| every element is trivial or has terminal flow `Z'π_←(s_f → ·)`, `Z' > 0`, positive on terminating states | `member_dichotomy` |
| the infimum is not attained | `not_attained`, `graphResidual_ne_zero` (terminating states internal, as in the paper); corollaries `not_attained_of_not_edge_src_snk`, `graphResidual_ne_zero_of_not_edge_src_snk` |
| (the constraint on `G`, and the library's) | `fmDefectE`, `fmDefect_eq_fmDefectE`, `graphResidual` |
| inhabitation | `diamond_check`, `diamond_partial_support` |
| the reading of "terminating state" matters | `triangle_attained` |

## SCOPE (disclosed)

**`def:universality`.**

* **Densities, not measures.** `F_init`, `F_term` are carried by densities `f_init, f_term : α → ℝ`
  (Radon–Nikodym gives one for every `F ≪ ν_B`), a.e. non-negative; "equal total mass" is
  `∫ f_init = ∫ f_term`, which is the total mass because `L^p ⊆ L¹` on a finite measure for
  `p ≥ 1`. The definitions take any measure and any `p`; finiteness of `ν` and `1 ≤ p` are carried
  by the theorems that use them.
* **The residual lives in `[0, ∞]`.** `residual` is `eLpNorm δf_init + eLpNorm δf_term` in `ℝ≥0∞`
  and the infimum is `⨅ θ ∈ Θ` there: a member whose residual is not in `L^p` counts `∞`, and the
  empty family has infimum `∞ ≠ 0`. A real-valued `sInf` would make the empty family universal.
* **`F⋆_out π⋆` is `densityAction`**, the `ν`-density of `(f_out ν) π⋆`, i.e. the Radon–Nikodym
  derivative of its absolutely continuous part. **`IsBoundedPolicy` therefore asks
  `ν π⋆ ≪ ν` besides `IsBoundedDensityAction`**: the paper's operator norm of `f ↦ f π⋆` is finite
  only if `(f ν) π⋆` has an `L^p` density, so it forces `ν π⋆ ≪ ν` (take `f = 𝟏`); conversely
  `ν π⋆ ≪ ν` gives `(f ν) π⋆ ≪ ν` for every `f` (`bind_withDensity_ac`), and then
  `densityAction` is the whole density. Without the `≪` clause a singular kernel (`π⋆(x) = δ₀` on
  `[0,1]`) would pass `IsBoundedDensityAction` with `C = 0`. The equivalence with the paper's norm
  is this argument, not a Lean theorem: the paper's norm on measures has no Lean counterpart.
* **"Its `π⋆` component is bounded" is read member by member** (`∀ θ ∈ Θ`), each with its own
  constant, which the `∃ C` of `IsBoundedPolicy` is — the definition of *bounded*, not a theorem
  constant (rule 3 does not apply). A uniform bound over `Θ` would be a different, stronger
  requirement; the paper's metrization of `Θ` by the operator norm (`proofs.tex:17–21`)
  supports the per-member reading.
* **Strong universality carries the same two standing conjuncts** (flow family, bounded policies)
  and replaces the infimum by a realizing member; `StronglyUniversal.weaklyUniversal` proves the
  implication the word "realized" presupposes.
* **R6 is per pair.** `realizes_of_le` proves exactly the parenthetical: the realizing member, the
  pair, `r ≤ p`. It is not a family-level transfer — `StronglyUniversal ν p Θ` does not give
  `StronglyUniversal ν r Θ`, since pairs in `L^r ∖ L^p` are admissible at `r` and boundedness at
  `r` is not implied — and the paper does not claim one.
* **The floor needs `ν π⋆ ≪ ν` of each member** (the first conjunct of `IsBoundedPolicy`) and
  integrable densities; the constant is explicit, `ν(𝒮)^{1 − 1/p}`.
* **The bridge is at invariant kernels.** `weaklyUniversal_fixedPolicyFamily_iff` needs
  `ν π⋆ = ν` and `IsBoundedDensityAction`, the hypotheses under which the library's
  `densityActionCLM` exists. `Core.WeaklyUniversal` quantifies over *every* `θ ∈ L^p` with
  `Π θ = 0`; the iff shows nothing is lost, since such a `θ` is `θ⁺ − θ⁻` for the admissible pair
  `(θ⁻, θ⁺)` (`isAdmissiblePair_parts`).

**`rem:partial_support`.**

* **"Only its sink row renormalized": the claim is true, one word is not.** `restrict_policy`
  certifies the restriction sentence as written (rows off the sink are `π_←`'s, the sink row is
  the renormalized restriction). `partial_support_exact` certifies the next sentence as the paper
  obtains it: `theo:universality_graphs`' concluding freeze applied to `G'`, where `R` has full
  support on the terminating states of `G'`, i.e. the restriction with sink row set to `R/Z`.
  Both halves are certified separately and faithfully; what is wrong is only the word
  "renormalized" — with the renormalized row the theorem's terminal flow is `Z · renormRow`,
  which is `R` only when `π_←(s_f → ·)` is proportional to `R` on `supp R`. Relatedly,
  `proofs.tex:1140` freezes `π_←(s_f → ·) := R` where the probability row `R/Z` is needed
  (`termFlow_eq_target`: the terminal flow is `Z π_←(s_f → ·)`).
* **"Not to that of `G`" is read on edge flows.** The flow of `G'` lives on another vertex type;
  `not_memberFlow` proves that its extension by zero (indeed any edge flow of positive initial mass
  with terminal flow `R`, `R` vanishing on a terminating state) is the edge flow
  `f_out(u) π_→(u → v)` of **no** element of the union over **all** backward policies positive on
  the edges of `G` — stronger than the family of the given `π_←`.
* **The residual on a graph is taken against the flow's own initial flow.** `fmDefectE G e T` is
  `equ:FM_const` on `𝒮 = 𝒱 ∖ {s₀, s_f}` with `F_init(v) = e(s₀ → v)` and terminal flow `T`, and
  `graphResidual` its `‖D⁻‖_p + ‖D⁺‖_p` for the counting measure on `𝒮` (`[MeasurableSpace V]`
  with measurable singletons). This is the reading `Graph/Universality.lean`'s SCOPE records for
  `theo:universality_graphs` ("`F_init` is not free"); with `F_init` fixed in advance the infimum
  would not vanish in general, and no statement here takes that reading.
  `fmDefect_eq_fmDefectE` shows `fmDefectE` is the library's `fmDefect` on the flow of item (3).
* **Terminating states are internal, as in the paper.** Initial and terminal flows and targets
  live on `𝒮 = 𝒱 ∖ {s₀, s_f}` (`introduction.tex:84–86`, `proofs.tex:1162`, `s_τ ∈ 𝒮`), so a
  terminating state is an internal state with an edge to `s_f`. `not_attained` and
  `graphResidual_ne_zero` take their two witnesses (`R ≠ 0` somewhere, `R = 0` on a terminating
  state) in `G.internal` and need **no** edge condition and no `IsTarget`. The older forms, with
  `¬ (s₀ → s_f)` and unrestricted witnesses, are kept as corollaries.
  `triangle_attained` shows only that the *reading* matters: if `s₀` is counted as a terminating
  state (which `IsTarget` and an unrestricted witness allow when `s₀ → s_f` is an edge), `R = δ₁` on
  the triangle `0 → 1 → 2`, `0 → 2` "vanishes on a terminating state" and is nonetheless attained
  on `𝒮`. Under the paper's reading its only terminating state is `1`, where `R ≠ 0`, so the
  remark's hypothesis fails there: it is not a refutation of the remark.
  `IsTarget` itself is wider than the paper's targets (it lets `R(s₀) ≠ 0` when `s₀ → s_f`); where
  it is used (claim (a), the vanishing half) this only enlarges the class of targets covered.
  When `s₀ → s_f` is an edge, `subGraph` and `unif` also count `s₀` as a terminating state (the
  edge is deleted from `G′` when `R(s₀) = 0`); that case is the one the `theo:universality_graphs`
  pointer below flags as inconsistent in the paper.
* **Pointer, not a claim of this file (row `theo:universality_graphs`).** With an edge `s₀ → s_f`,
  `theo:universality_graphs`(3) and its concluding "freeze `π_←(s_f → ·) := R`" are inconsistent
  on `𝒮`: the terminal flow `Z π_←(s_f → ·)` charges `s₀ ∉ 𝒮` (mass leaks to `s₀`), and a target on
  `𝒮` frozen into the sink row makes `π_←(s_f → s₀) = 0` on an edge of `G`, breaking positivity on
  that edge.
* **Implicit hypotheses made explicit**: `R ≠ 0` for path-connectedness of `G'` (with `R = 0`,
  `G'` is `{s₀, s_f}` with no edge), and `R` carried by the terminating states (`IsTarget`), which
  "target" means (`theo:universality_graphs`(3)).
* **Everything `Graph/Setting.lean` and `Graph/Universality.lean` disclose is inherited**: no
  chain, no sampler, `theo:sampling_theorem` not assumed; nothing here certifies `s_τ ∼ R/Z`.
  The sampler clause is certified downstream, in `GFNBounds.Graph.SamplerWiring`
  (`universality_graphs_sampler_iff`: the law of `s_τ` is `R/Z` iff no edge `s₀ → s_f`;
  `universality_graphs_sampler`: it is `R|_𝒮/R(𝒮)` in every case;
  `universality_graphs_closing_sampler`: the balanced flow of a frozen family samples `R/Z`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)`, `ν_B` finite | ✓ `[IsFiniteMeasure ν]` where used; Polish not used |
| `p ∈ [1, ∞]` | ✓ `1 ≤ p` where used (`[Fact (1 ≤ p)]` on `L^p`) |
| `Θ` a family of generative flows | ✓ `IsFlowFamily`, a conjunct of both predicates |
| `π⋆` bounded on `L^p(ν_B)` | ✓ `IsBoundedPolicy` (per member; `≪` clause explained in SCOPE) |
| `F_init, F_term ≪ ν_B`, equal mass, densities in `L^p` | ✓ `IsAdmissiblePair` |
| residuals `δf_init = D⁻`, `δf_term = D⁺` | ✓ `resInitFn`, `resTermFn` |
| `G` finite, path-connected | ✓ `[Fintype V]`, `hpc` |
| `π_←` positive on the edges of `G` | ✓ `hB : B.PositiveOnEdges` |
| `R` a target of mass `Z` | ✓ `IsTarget G R`, `0 < ∑ R` |
| `R` vanishes on some terminating state | ✓ `hvan`, only where used (claim (b), "not in `G`") |
| terminating states are internal (`𝒮 = 𝒱 ∖ {s₀, s_f}`) | ✓ the witnesses of `not_attained` are taken in `G.internal`; no edge condition |
| `ε ∈ (0, 1]` | ✓ `0 < ε`, `ε ≤ 1` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core.Family

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

/-! ## The objects of `def:universality` -/

/-- **`def:universality`, the objects**: a generative flow `(π⋆, f_out⋆)` on `(𝒮, ν_B)`
(`proofs.tex:16`) — `π⋆` a Markov kernel and `f_out⋆ : 𝒮 → ℝ₊` integrable. -/
structure IsGenerativeFlow (ν : Measure α) (θ : Kernel α α × (α → ℝ)) : Prop where
  markov : IsMarkovKernel θ.1
  nonneg : ∀ x, 0 ≤ θ.2 x
  integrable : Integrable θ.2 ν

/-- **`def:universality`**: `Θ` is a family of generative flows. -/
def IsFlowFamily (ν : Measure α) (Θ : Set (Kernel α α × (α → ℝ))) : Prop :=
  ∀ θ ∈ Θ, IsGenerativeFlow ν θ

/-- **The flow-matching defect** `D = F_init + F⋆_out π⋆ − F⋆_out − F_term`, as a `ν`-density
(`proofs.tex:45–51`, `proofs.tex:79`). -/
noncomputable def defectFn (ν : Measure α) (θ : Kernel α α × (α → ℝ)) (f_init f_term : α → ℝ) :
    α → ℝ :=
  fun x => f_init x + densityAction θ.1 ν θ.2 x - θ.2 x - f_term x

/-- **`δf_init = D⁻`**. -/
noncomputable def resInitFn (ν : Measure α) (θ : Kernel α α × (α → ℝ)) (f_init f_term : α → ℝ) :
    α → ℝ :=
  fun x => (defectFn ν θ f_init f_term x)⁻

/-- **`δf_term = D⁺`**. -/
noncomputable def resTermFn (ν : Measure α) (θ : Kernel α α × (α → ℝ)) (f_init f_term : α → ℝ) :
    α → ℝ :=
  fun x => (defectFn ν θ f_init f_term x)⁺

/-- **`def:universality`, the quantity infimized**: `‖δf_init‖_{L^p(ν)} + ‖δf_term‖_{L^p(ν)}`, in
`[0, ∞]`. -/
noncomputable def residual (ν : Measure α) (p : ℝ≥0∞) (θ : Kernel α α × (α → ℝ))
    (f_init f_term : α → ℝ) : ℝ≥0∞ :=
  eLpNorm (resInitFn ν θ f_init f_term) p ν + eLpNorm (resTermFn ν θ f_init f_term) p ν

/-- **`def:universality`, the pairs**: densities of distributions `F_init, F_term ≪ ν`, in
`L^p(ν)`, of equal total mass. -/
structure IsAdmissiblePair (ν : Measure α) (p : ℝ≥0∞) (f_init f_term : α → ℝ) : Prop where
  nonneg_init : ∀ᵐ x ∂ν, 0 ≤ f_init x
  nonneg_term : ∀ᵐ x ∂ν, 0 ≤ f_term x
  memLp_init : MemLp f_init p ν
  memLp_term : MemLp f_term p ν
  mass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν

/-- **`def:universality`, the boundedness requirement**: `f ↦ f π⋆` is bounded on `L^p(ν)` —
`(f ν) π⋆` has a density (`ν π⋆ ≪ ν`) and it is bounded in `L^p`. See SCOPE. -/
def IsBoundedPolicy (ν : Measure α) (p : ℝ≥0∞) (κ : Kernel α α) : Prop :=
  ν.bind ⇑κ ≪ ν ∧ ∃ C : ℝ, IsBoundedDensityAction κ ν p C

/-- **`def:universality`, weak form, for an arbitrary family `Θ`.** -/
def WeaklyUniversal (ν : Measure α) (p : ℝ≥0∞) (Θ : Set (Kernel α α × (α → ℝ))) : Prop :=
  IsFlowFamily ν Θ ∧ (∀ θ ∈ Θ, IsBoundedPolicy ν p θ.1) ∧
    ∀ f_init f_term : α → ℝ, IsAdmissiblePair ν p f_init f_term →
      ⨅ θ ∈ Θ, residual ν p θ f_init f_term = 0

/-- **`def:universality`, strong form, for an arbitrary family `Θ`**: the zero infimum is realized
at every admissible pair. -/
def StronglyUniversal (ν : Measure α) (p : ℝ≥0∞) (Θ : Set (Kernel α α × (α → ℝ))) : Prop :=
  IsFlowFamily ν Θ ∧ (∀ θ ∈ Θ, IsBoundedPolicy ν p θ.1) ∧
    ∀ f_init f_term : α → ℝ, IsAdmissiblePair ν p f_init f_term →
      ∃ θ ∈ Θ, residual ν p θ f_init f_term = 0

/-! ## The infimum, read as an `ε`-statement -/

/-- An infimum in `[0, ∞]` over a set vanishes iff it is approached by elements of the set. -/
theorem iInf_eq_zero_iff {ι : Type*} (s : Set ι) (r : ι → ℝ≥0∞) :
    (⨅ i ∈ s, r i) = 0 ↔ ∀ ε : ℝ, 0 < ε → ∃ i ∈ s, r i < ENNReal.ofReal ε := by
  constructor
  · intro h ε hε
    have hlt : (⨅ i ∈ s, r i) < ENNReal.ofReal ε := by
      rw [h]; exact ENNReal.ofReal_pos.2 hε
    obtain ⟨i, hi⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hs, his⟩ := iInf_lt_iff.1 hi
    exact ⟨i, hs, his⟩
  · intro h
    refine le_antisymm ?_ zero_le
    by_contra hc
    obtain ⟨b, -, hb, hb'⟩ := ENNReal.lt_iff_exists_real_btwn.1 (not_le.1 hc)
    obtain ⟨i, hs, hi⟩ := h b (ENNReal.ofReal_pos.1 hb)
    have hle : (⨅ i ∈ s, r i) ≤ r i := iInf₂_le i hs
    exact absurd (hle.trans_lt hi) (not_lt.2 hb'.le)

/-- **`def:universality`**: strong universality implies weak universality. -/
theorem StronglyUniversal.weaklyUniversal {ν : Measure α} {p : ℝ≥0∞}
    {Θ : Set (Kernel α α × (α → ℝ))} (h : StronglyUniversal ν p Θ) : WeaklyUniversal ν p Θ := by
  obtain ⟨hfam, hb, hreal⟩ := h
  refine ⟨hfam, hb, fun f_init f_term hpair => ?_⟩
  obtain ⟨θ, hθ, h0⟩ := hreal f_init f_term hpair
  exact le_antisymm ((iInf₂_le θ hθ).trans h0.le) zero_le


/-! ## Measurability of the residuals -/

section Measurability

variable {ν : Measure α} {θ : Kernel α α × (α → ℝ)} {f_init f_term : α → ℝ}

theorem aestronglyMeasurable_defectFn (hθ : AEStronglyMeasurable θ.2 ν)
    (hi : AEStronglyMeasurable f_init ν) (ht : AEStronglyMeasurable f_term ν) :
    AEStronglyMeasurable (defectFn ν θ f_init f_term) ν :=
  ((hi.add (measurable_densityAction θ.1 ν θ.2).aestronglyMeasurable).sub hθ).sub ht

theorem aestronglyMeasurable_resInitFn (hθ : AEStronglyMeasurable θ.2 ν)
    (hi : AEStronglyMeasurable f_init ν) (ht : AEStronglyMeasurable f_term ν) :
    AEStronglyMeasurable (resInitFn ν θ f_init f_term) ν :=
  continuous_negPart.comp_aestronglyMeasurable (aestronglyMeasurable_defectFn hθ hi ht)

theorem aestronglyMeasurable_resTermFn (hθ : AEStronglyMeasurable θ.2 ν)
    (hi : AEStronglyMeasurable f_init ν) (ht : AEStronglyMeasurable f_term ν) :
    AEStronglyMeasurable (resTermFn ν θ f_init f_term) ν :=
  continuous_posPart.comp_aestronglyMeasurable (aestronglyMeasurable_defectFn hθ hi ht)

/-- `D = δf_term − δf_init`, pointwise. -/
theorem defectFn_eq_sub (x : α) :
    defectFn ν θ f_init f_term x = resTermFn ν θ f_init f_term x - resInitFn ν θ f_init f_term x :=
  (posPart_sub_negPart _).symm

end Measurability

/-! ## `def:universality`'s parenthetical: a realized pair is realized at every `r ∈ [1, p]` -/

section Realization

variable {ν : Measure α} {θ : Kernel α α × (α → ℝ)} {f_init f_term : α → ℝ} {p r : ℝ≥0∞}

/-- A flow realizing the zero infimum for a pair has almost-everywhere-zero residuals. -/
theorem ae_eq_zero_of_residual_eq_zero (hp : p ≠ 0) (hθ : AEStronglyMeasurable θ.2 ν)
    (hi : AEStronglyMeasurable f_init ν) (ht : AEStronglyMeasurable f_term ν)
    (h : residual ν p θ f_init f_term = 0) :
    resInitFn ν θ f_init f_term =ᵐ[ν] 0 ∧ resTermFn ν θ f_init f_term =ᵐ[ν] 0 := by
  obtain ⟨h1, h2⟩ := add_eq_zero.1 h
  exact ⟨(eLpNorm_eq_zero_iff (aestronglyMeasurable_resInitFn hθ hi ht) hp).1 h1,
    (eLpNorm_eq_zero_iff (aestronglyMeasurable_resTermFn hθ hi ht) hp).1 h2⟩

/-- Almost-everywhere-zero residuals have zero norm at every exponent. -/
theorem residual_eq_zero_of_ae (h : resInitFn ν θ f_init f_term =ᵐ[ν] 0 ∧
    resTermFn ν θ f_init f_term =ᵐ[ν] 0) (r : ℝ≥0∞) : residual ν r θ f_init f_term = 0 := by
  simp only [residual, eLpNorm_congr_ae h.1, eLpNorm_congr_ae h.2, eLpNorm_zero, add_zero]

/-- On a finite measure an `L^p`-admissible pair is `L^r`-admissible for `r ≤ p`. -/
theorem IsAdmissiblePair.mono [IsFiniteMeasure ν] (h : IsAdmissiblePair ν p f_init f_term)
    (hrp : r ≤ p) : IsAdmissiblePair ν r f_init f_term :=
  ⟨h.nonneg_init, h.nonneg_term, h.memLp_init.mono_exponent hrp, h.memLp_term.mono_exponent hrp,
    h.mass⟩

/-- **`def:universality`'s parenthetical** (ruling R6): a flow realizing the zero infimum for an
`L^p`-admissible pair realizes it for that pair at every `r ∈ [1, p]`. -/
theorem realizes_of_le [IsFiniteMeasure ν] (hθ : IsGenerativeFlow ν θ)
    (hpair : IsAdmissiblePair ν p f_init f_term) (hp : 1 ≤ p)
    (h : residual ν p θ f_init f_term = 0) (hrp : r ≤ p) :
    IsAdmissiblePair ν r f_init f_term ∧ residual ν r θ f_init f_term = 0 :=
  ⟨hpair.mono hrp, residual_eq_zero_of_ae (ae_eq_zero_of_residual_eq_zero
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hθ.integrable.1 hpair.memLp_init.1
    hpair.memLp_term.1 h) r⟩

/-- The same at family level, pair by pair. -/
theorem StronglyUniversal.realizes_of_le [IsFiniteMeasure ν] {Θ : Set (Kernel α α × (α → ℝ))}
    (h : StronglyUniversal ν p Θ) (hp : 1 ≤ p) (hrp : r ≤ p)
    (hpair : IsAdmissiblePair ν p f_init f_term) :
    ∃ θ ∈ Θ, IsAdmissiblePair ν r f_init f_term ∧ residual ν r θ f_init f_term = 0 := by
  obtain ⟨hfam, -, hreal⟩ := h
  obtain ⟨θ, hθ, h0⟩ := hreal f_init f_term hpair
  exact ⟨θ, hθ, GFNBounds.Core.Family.realizes_of_le (hfam θ hθ) hpair hp h0 hrp⟩

end Realization

/-! ## `def:universality`'s first parenthetical: unequal masses floor the infimum -/

section Mass

variable {ν : Measure α}

theorem bind_withDensity_ac (κ : Kernel α α) (hac : ν.bind ⇑κ ≪ ν) (f : α → ℝ≥0∞) :
    (ν.withDensity f).bind ⇑κ ≪ ν :=
  (bind_absolutelyContinuous_bind κ (withDensity_absolutelyContinuous ν f)).trans hac

theorem lintegral_bindDensity_of_ac (κ : Kernel α α) [IsMarkovKernel κ] [SigmaFinite ν]
    (hac : ν.bind ⇑κ ≪ ν) (f : α → ℝ≥0∞) :
    ∫⁻ x, bindDensity κ ν f x ∂ν = ∫⁻ x, f x ∂ν := by
  calc ∫⁻ x, bindDensity κ ν f x ∂ν
      = (ν.withDensity (bindDensity κ ν f)) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = ((ν.withDensity f).bind ⇑κ) Set.univ := by
        rw [bindDensity, Measure.withDensity_rnDeriv_eq _ _ (bind_withDensity_ac κ hac f)]
    _ = ∫⁻ x, f x ∂ν := bind_withDensity_univ κ ν f

theorem integrable_toReal_bindDensity_of_ac (κ : Kernel α α) [IsMarkovKernel κ] [SigmaFinite ν]
    (hac : ν.bind ⇑κ ≪ ν) {f : α → ℝ} (hf : Integrable f ν) :
    Integrable (fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (measurable_bindDensity κ ν _).aemeasurable
    (by rw [lintegral_bindDensity_of_ac κ hac]; exact lintegral_ofReal_ne_top hf)

theorem integral_toReal_bindDensity_of_ac (κ : Kernel α α) [IsMarkovKernel κ] [SigmaFinite ν]
    (hac : ν.bind ⇑κ ≪ ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∫ x, (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal ∂ν
      = (∫⁻ x, ENNReal.ofReal (f x) ∂ν).toReal := by
  have hlt : ∀ᵐ x ∂ν, bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x < ⊤ :=
    ae_lt_top (measurable_bindDensity κ ν _)
      (by rw [lintegral_bindDensity_of_ac κ hac]; exact lintegral_ofReal_ne_top hf)
  rw [integral_toReal (measurable_bindDensity κ ν _).aemeasurable hlt,
    lintegral_bindDensity_of_ac κ hac]

/-- `P⋆ f` is integrable, with no invariance: absolute continuity `ν π⋆ ≪ ν` suffices. -/
theorem integrable_densityAction_of_ac (κ : Kernel α α) [IsMarkovKernel κ] [SigmaFinite ν]
    (hac : ν.bind ⇑κ ≪ ν) {f : α → ℝ} (hf : Integrable f ν) :
    Integrable (densityAction κ ν f) ν :=
  (integrable_toReal_bindDensity_of_ac κ hac hf).sub
    (integrable_toReal_bindDensity_of_ac κ hac hf.neg)

/-- `∫ P⋆ f dν = ∫ f dν`, from stochasticity and `ν π⋆ ≪ ν`, with no invariance. -/
theorem integral_densityAction_of_ac (κ : Kernel α α) [IsMarkovKernel κ] [SigmaFinite ν]
    (hac : ν.bind ⇑κ ≪ ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∫ x, densityAction κ ν f x ∂ν = ∫ x, f x ∂ν := by
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  simp only [densityAction]
  rw [integral_sub (integrable_toReal_bindDensity_of_ac κ hac hf)
      (integrable_toReal_bindDensity_of_ac κ hac hfn),
    integral_toReal_bindDensity_of_ac κ hac hf, integral_toReal_bindDensity_of_ac κ hac hfn]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm

variable {θ : Kernel α α × (α → ℝ)} {f_init f_term : α → ℝ}

/-- **The defect integrates to `F_init(𝒮) − F_term(𝒮)`** (`universality.tex:11`). -/
theorem integral_defectFn [SigmaFinite ν] (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν)
    (hi : Integrable f_init ν) (ht : Integrable f_term ν) :
    ∫ x, defectFn ν θ f_init f_term x ∂ν = ∫ x, f_init x ∂ν - ∫ x, f_term x ∂ν := by
  haveI := hθ.markov
  have hP := integrable_densityAction_of_ac θ.1 hac hθ.integrable
  have e1 : ∫ x, defectFn ν θ f_init f_term x ∂ν
      = ∫ x, (f_init x + densityAction θ.1 ν θ.2 x - θ.2 x) ∂ν - ∫ x, f_term x ∂ν :=
    integral_sub (f := fun x => f_init x + densityAction θ.1 ν θ.2 x - θ.2 x)
      ((hi.add hP).sub hθ.integrable) ht
  have e2 : ∫ x, (f_init x + densityAction θ.1 ν θ.2 x - θ.2 x) ∂ν
      = ∫ x, (f_init x + densityAction θ.1 ν θ.2 x) ∂ν - ∫ x, θ.2 x ∂ν :=
    integral_sub (f := fun x => f_init x + densityAction θ.1 ν θ.2 x) (hi.add hP) hθ.integrable
  have e3 : ∫ x, (f_init x + densityAction θ.1 ν θ.2 x) ∂ν
      = ∫ x, f_init x ∂ν + ∫ x, densityAction θ.1 ν θ.2 x ∂ν := integral_add hi hP
  rw [e1, e2, e3, integral_densityAction_of_ac θ.1 hac hθ.integrable]
  ring

/-- The mass gap is bounded by the `L¹` residuals. -/
theorem ofReal_abs_mass_le_residual_one [SigmaFinite ν] (hθ : IsGenerativeFlow ν θ)
    (hac : ν.bind ⇑θ.1 ≪ ν) (hi : Integrable f_init ν) (ht : Integrable f_term ν) :
    ENNReal.ofReal |∫ x, f_init x ∂ν - ∫ x, f_term x ∂ν| ≤ residual ν 1 θ f_init f_term := by
  have hD := aestronglyMeasurable_defectFn (θ := θ) hθ.integrable.1 hi.1 ht.1
  have hI := aestronglyMeasurable_resInitFn (θ := θ) hθ.integrable.1 hi.1 ht.1
  have hT := aestronglyMeasurable_resTermFn (θ := θ) hθ.integrable.1 hi.1 ht.1
  rw [← integral_defectFn hθ hac hi ht, ← Real.enorm_eq_ofReal_abs]
  calc ‖∫ x, defectFn ν θ f_init f_term x ∂ν‖ₑ
      ≤ ∫⁻ x, ‖defectFn ν θ f_init f_term x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (defectFn ν θ f_init f_term) 1 ν := (eLpNorm_one_eq_lintegral_enorm).symm
    _ = eLpNorm (resTermFn ν θ f_init f_term - resInitFn ν θ f_init f_term) 1 ν := by
        congr 1; funext x; exact defectFn_eq_sub x
    _ ≤ eLpNorm (resTermFn ν θ f_init f_term) 1 ν + eLpNorm (resInitFn ν θ f_init f_term) 1 ν :=
        eLpNorm_sub_le hT hI le_rfl
    _ = residual ν 1 θ f_init f_term := add_comm _ _

/-- **Unequal masses floor the residuals away from `0`**, at every exponent `p ≥ 1`, with the
explicit constant `ν(𝒮)^{1 − 1/p}`. -/
theorem ofReal_abs_mass_le_residual [IsFiniteMeasure ν] (hθ : IsGenerativeFlow ν θ)
    (hac : ν.bind ⇑θ.1 ≪ ν) (hi : Integrable f_init ν) (ht : Integrable f_term ν)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ENNReal.ofReal |∫ x, f_init x ∂ν - ∫ x, f_term x ∂ν|
      ≤ residual ν p θ f_init f_term * ν Set.univ ^ (1 - 1 / p.toReal) := by
  have hI := aestronglyMeasurable_resInitFn (θ := θ) hθ.integrable.1 hi.1 ht.1
  have hT := aestronglyMeasurable_resTermFn (θ := θ) hθ.integrable.1 hi.1 ht.1
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hI
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hT
  simp only [ENNReal.toReal_one, div_one] at h1 h2
  refine (ofReal_abs_mass_le_residual_one hθ hac hi ht).trans ?_
  simp only [residual, add_mul]
  exact add_le_add h1 h2

/-- **`def:universality`'s first parenthetical, at family level**: the infimum is at least
`|F_init(𝒮) − F_term(𝒮)| / ν(𝒮)^{1 − 1/p}`. -/
theorem mass_gap_div_le_iInf [IsFiniteMeasure ν] {Θ : Set (Kernel α α × (α → ℝ))}
    (hfam : IsFlowFamily ν Θ) (hac : ∀ θ ∈ Θ, ν.bind ⇑θ.1 ≪ ν) (hi : Integrable f_init ν)
    (ht : Integrable f_term ν) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ENNReal.ofReal |∫ x, f_init x ∂ν - ∫ x, f_term x ∂ν| / ν Set.univ ^ (1 - 1 / p.toReal)
      ≤ ⨅ θ ∈ Θ, residual ν p θ f_init f_term :=
  le_iInf₂ fun θ hθ =>
    ENNReal.div_le_of_le_mul (ofReal_abs_mass_le_residual (hfam θ hθ) (hac θ hθ) hi ht hp)

/-- Unequal masses: the infimum is not `0`. -/
theorem iInf_pos_of_mass_ne [IsFiniteMeasure ν] {Θ : Set (Kernel α α × (α → ℝ))}
    (hfam : IsFlowFamily ν Θ) (hac : ∀ θ ∈ Θ, ν.bind ⇑θ.1 ≪ ν) (hi : Integrable f_init ν)
    (ht : Integrable f_term ν) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hmass : ∫ x, f_init x ∂ν ≠ ∫ x, f_term x ∂ν) :
    0 < ⨅ θ ∈ Θ, residual ν p θ f_init f_term := by
  refine lt_of_lt_of_le ?_ (mass_gap_div_le_iInf hfam hac hi ht hp)
  refine ENNReal.div_pos_iff.2 ⟨?_, ?_⟩
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (sub_ne_zero.2 hmass)
  · have hexp : 0 ≤ 1 - 1 / p.toReal := by
      rcases eq_or_ne p ⊤ with rfl | hpt
      · simp only [ENNReal.toReal_top, div_zero, sub_zero, zero_le_one]
      · have : 1 ≤ p.toReal := by
          have := ENNReal.toReal_mono hpt hp
          simpa using this
        have : 1 / p.toReal ≤ 1 := by
          rw [div_le_one (by linarith)]; exact this
        linarith
    exact (ENNReal.rpow_lt_top_of_nonneg hexp (measure_ne_top ν Set.univ)).ne

end Mass

/-! ## The bridge to the library's fixed-policy predicates -/

section Bridge

variable {ν : Measure α} [IsFiniteMeasure ν] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The family `Θ := {π⋆} × L^p_+(𝒮, ν_B)` of `theo:universality_L2_full`**: one policy, and a
free non-negative outflow in `L^p(ν)`. -/
def fixedPolicyFamily (ν : Measure α) (p : ℝ≥0∞) (κ : Kernel α α) :
    Set (Kernel α α × (α → ℝ)) :=
  {θ | θ.1 = κ ∧ (∀ x, 0 ≤ θ.2 x) ∧ MemLp θ.2 p ν}

omit [IsFiniteMeasure ν] [Fact (1 ≤ p)] in
theorem coeFn_negPart_Lp (a : Lp ℝ p ν) : ⇑(a⁻) =ᵐ[ν] fun x => (a x)⁻ := by
  rw [negPart_def]
  filter_upwards [Lp.coeFn_sup (-a) 0, Lp.coeFn_neg a, Lp.coeFn_zero ℝ p ν] with x h1 h2 h3
  rw [h1, Pi.sup_apply, h2, h3, negPart_def]
  rfl

omit [IsFiniteMeasure ν] [Fact (1 ≤ p)] in
theorem coeFn_posPart_Lp (a : Lp ℝ p ν) : ⇑(a⁺) =ᵐ[ν] fun x => (a x)⁺ := by
  rw [posPart_def]
  filter_upwards [Lp.coeFn_sup a 0, Lp.coeFn_zero ℝ p ν] with x h1 h3
  rw [h1, Pi.sup_apply, h3, posPart_def]
  rfl

omit [IsFiniteMeasure ν] [Fact (1 ≤ p)] in
theorem eLpNorm_eq_ofReal_norm {g : α → ℝ} {a : Lp ℝ p ν} (h : g =ᵐ[ν] ⇑a) :
    eLpNorm g p ν = ENNReal.ofReal ‖a‖ := by
  rw [eLpNorm_congr_ae h, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top a)]

/-- **The family residual is the library's**, for a member of the fixed-policy family whose
outflow represents `f_out ∈ L^p(ν)` and a pair whose difference represents `θ`. -/
theorem residual_eq_ofReal (κ : Kernel α α) [IsMarkovKernel κ] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) {fout θL : Lp ℝ p ν} {g f_init f_term : α → ℝ}
    (hg : g =ᵐ[ν] ⇑fout) (hθ : (fun x => f_term x - f_init x) =ᵐ[ν] ⇑θL) :
    residual ν p (κ, g) f_init f_term
      = ENNReal.ofReal (‖resInit (densityActionCLM κ ν p hinv hb) θL fout‖
          + ‖resTerm (densityActionCLM κ ν p hinv hb) θL fout‖) := by
  set P := densityActionCLM κ ν p hinv hb
  have hD : defectFn ν (κ, g) f_init f_term =ᵐ[ν] ⇑(defect P θL fout) := by
    have hP := coeFn_densityActionCLM κ ν p hinv hb fout
    have hcong : densityAction κ ν g = densityAction κ ν ⇑fout := densityAction_congr κ ν hg
    filter_upwards [coeFn_defect P θL fout, hP, hg, hθ] with x e1 e2 e3 e4
    rw [e1, e2]
    simp only [defectFn, hcong]
    rw [e3, ← e4]
    ring
  have hI : resInitFn ν (κ, g) f_init f_term =ᵐ[ν] ⇑(resInit P θL fout) := by
    filter_upwards [hD, coeFn_negPart_Lp (defect P θL fout)] with x e1 e2
    simp only [resInitFn, resInit]
    rw [e2, e1]
  have hT : resTermFn ν (κ, g) f_init f_term =ᵐ[ν] ⇑(resTerm P θL fout) := by
    filter_upwards [hD, coeFn_posPart_Lp (defect P θL fout)] with x e1 e2
    simp only [resTermFn, resTerm]
    rw [e2, e1]
  rw [residual, eLpNorm_eq_ofReal_norm hI, eLpNorm_eq_ofReal_norm hT,
    ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]

/-- Members of the fixed-policy family are generative flows. -/
theorem isFlowFamily_fixedPolicyFamily (κ : Kernel α α) [IsMarkovKernel κ] :
    IsFlowFamily ν (fixedPolicyFamily ν p κ) := by
  rintro ⟨κ', g⟩ ⟨hκ, hnn, hmem⟩
  simp only at hκ hnn hmem
  subst hκ
  exact ⟨inferInstance, hnn, hmem.integrable Fact.out⟩

omit [IsFiniteMeasure ν] [Fact (1 ≤ p)] in
/-- Under invariance, the paper's boundedness requirement is `IsBoundedDensityAction`. -/
theorem isBoundedPolicy_of_inv {κ : Kernel α α} {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) : IsBoundedPolicy ν p κ :=
  ⟨by rw [hinv], C, hb⟩

/-- A mean-zero `L^p` element has zero integral. -/
theorem integral_eq_zero_of_meanProj {θL : Lp ℝ p ν} (h : meanProj ν p θL = 0) :
    ∫ x, θL x ∂ν = 0 := by
  by_cases hν : ν Set.univ = 0
  · refine integral_eq_zero_of_ae ?_
    show ∀ᵐ x ∂ν, θL x = (0 : α → ℝ) x
    rw [ae_iff]
    exact measure_mono_null (Set.subset_univ _) hν
  · have h1 := congrArg (integralCLM ν p) h
    rw [meanProj_apply, map_smul, map_zero, integralCLM_apply, integral_constOne,
      smul_eq_mul] at h1
    have hne : (ν Set.univ).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨hν, measure_ne_top ν Set.univ⟩
    field_simp at h1
    exact h1

/-- The admissible pair `(θ⁻, θ⁺)` of a mean-zero element. -/
theorem isAdmissiblePair_parts {θL : Lp ℝ p ν} (h : meanProj ν p θL = 0) :
    IsAdmissiblePair ν p (fun x => max (-θL x) 0) (fun x => max (θL x) 0) := by
  have hmem := Lp.memLp θL
  refine ⟨Eventually.of_forall fun x => le_max_right _ _,
    Eventually.of_forall fun x => le_max_right _ _, hmem.neg_part, hmem.pos_part, ?_⟩
  have hint : Integrable (⇑θL) ν := hmem.integrable Fact.out
  have hsplit : ∫ x, θL x ∂ν = ∫ x, max (θL x) 0 ∂ν - ∫ x, max (-θL x) 0 ∂ν := by
    rw [← integral_sub hint.pos_part hint.neg_part]
    congr 1
    funext x
    rcases le_total 0 (θL x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  have h0 := integral_eq_zero_of_meanProj h
  linarith

omit [IsFiniteMeasure ν] [Fact (1 ≤ p)] in
/-- The pair `(θ⁻, θ⁺)` has difference `θ`. -/
theorem parts_sub_eq (θL : Lp ℝ p ν) :
    (fun x => max (θL x) 0 - max (-θL x) 0) =ᵐ[ν] ⇑θL := by
  refine Eventually.of_forall fun x => ?_
  rcases le_total 0 (θL x) with hx | hx
  · simp only [max_eq_left hx, max_eq_right (show -θL x ≤ 0 by linarith), sub_zero]
  · simp only [max_eq_right hx, max_eq_left (show 0 ≤ -θL x by linarith)]; ring

omit [IsFiniteMeasure ν] [Fact (1 ≤ p)] in
/-- A pair's densities, read in `L^p(ν)`, give the library's `θ = f_term − f_init`. -/
theorem pair_sub_eq {f_init f_term : α → ℝ} (h : IsAdmissiblePair ν p f_init f_term) :
    (fun x => f_term x - f_init x)
      =ᵐ[ν] ⇑(h.memLp_term.toLp f_term - h.memLp_init.toLp f_init) := by
  filter_upwards [Lp.coeFn_sub (h.memLp_term.toLp f_term) (h.memLp_init.toLp f_init),
    h.memLp_term.coeFn_toLp, h.memLp_init.coeFn_toLp] with x e1 e2 e3
  rw [e1, Pi.sub_apply, e2, e3]

theorem meanProj_pair_eq_zero {f_init f_term : α → ℝ} (h : IsAdmissiblePair ν p f_init f_term) :
    meanProj ν p (h.memLp_term.toLp f_term - h.memLp_init.toLp f_init) = 0 := by
  refine meanProj_sub_eq_zero ?_
  rw [integral_congr_ae h.memLp_init.coeFn_toLp, integral_congr_ae h.memLp_term.coeFn_toLp]
  exact h.mass

omit [IsFiniteMeasure ν] [Fact (1 ≤ p)] in
/-- An a.e.-non-negative `L^p` element has a pointwise non-negative representative. -/
theorem nonneg_rep {fout : Lp ℝ p ν} (h : 0 ≤ fout) :
    (fun x => max (fout x) 0) =ᵐ[ν] ⇑fout := by
  filter_upwards [(Lp.coeFn_nonneg fout).2 h] with x hx
  exact max_eq_left hx

/-- **`def:universality` and the library agree on the fixed-policy family, weak form.**
`WeaklyUniversal ν p ({π⋆} × L^p_+)` — the paper's definition, for an arbitrary family, read at
the family of `theo:universality_L2_full` — holds iff the library's `Core.WeaklyUniversal`
holds for the density action of `π⋆` and the mean projection. -/
theorem weaklyUniversal_fixedPolicyFamily_iff (κ : Kernel α α) [IsMarkovKernel κ] {C : ℝ}
    (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν p C) :
    WeaklyUniversal ν p (fixedPolicyFamily ν p κ)
      ↔ GFNBounds.Core.WeaklyUniversal (densityActionCLM κ ν p hinv hb) (meanProj ν p) := by
  constructor
  · rintro ⟨-, -, hinf⟩ θL hθL ε hε
    have hpair := isAdmissiblePair_parts hθL
    obtain ⟨⟨κ', g⟩, ⟨hκ, hnn, hmem⟩, hlt⟩ :=
      (iInf_eq_zero_iff _ _).1 (hinf _ _ hpair) ε hε
    simp only at hκ hnn hmem
    subst hκ
    refine ⟨hmem.toLp g, ?_, ?_⟩
    · rw [← Lp.coeFn_nonneg]
      filter_upwards [hmem.coeFn_toLp] with x hx
      rw [hx]; exact hnn x
    · rw [residual_eq_ofReal κ' hinv hb hmem.coeFn_toLp.symm (parts_sub_eq θL)] at hlt
      exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hlt
  · intro hW
    refine ⟨isFlowFamily_fixedPolicyFamily κ, ?_, fun f_init f_term hpair => ?_⟩
    · rintro ⟨κ', g⟩ ⟨hκ, -, -⟩
      simp only at hκ
      subst hκ
      exact isBoundedPolicy_of_inv hinv hb
    · refine (iInf_eq_zero_iff _ _).2 fun ε hε => ?_
      obtain ⟨fout, hnn, hlt⟩ := hW _ (meanProj_pair_eq_zero hpair) ε hε
      have hrep := nonneg_rep hnn
      refine ⟨(κ, fun x => max (fout x) 0), ⟨rfl, fun x => le_max_right _ _,
        (Lp.memLp fout).ae_eq hrep.symm⟩, ?_⟩
      rw [residual_eq_ofReal κ hinv hb hrep (pair_sub_eq hpair)]
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hlt

/-- **`def:universality` and the library agree on the fixed-policy family, strong form.** -/
theorem stronglyUniversal_fixedPolicyFamily_iff (κ : Kernel α α) [IsMarkovKernel κ] {C : ℝ}
    (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν p C) :
    StronglyUniversal ν p (fixedPolicyFamily ν p κ)
      ↔ GFNBounds.Core.StronglyUniversal (densityActionCLM κ ν p hinv hb) (meanProj ν p) := by
  set P := densityActionCLM κ ν p hinv hb
  have hzero : ∀ θL fout : Lp ℝ p ν,
      ‖resInit P θL fout‖ + ‖resTerm P θL fout‖ = 0 ↔ defect P θL fout = 0 := by
    intro θL fout
    constructor
    · intro h
      have h1 : ‖resInit P θL fout‖ = 0 := by
        have := norm_nonneg (resInit P θL fout); have := norm_nonneg (resTerm P θL fout)
        linarith
      have h2 : ‖resTerm P θL fout‖ = 0 := by
        have := norm_nonneg (resInit P θL fout); have := norm_nonneg (resTerm P θL fout)
        linarith
      rw [norm_eq_zero] at h1 h2
      rw [← posPart_sub_negPart (defect P θL fout)]
      simp only [resInit, resTerm] at h1 h2
      rw [h1, h2, sub_zero]
    · intro h
      simp only [resInit, resTerm, h, negPart_zero, posPart_zero, norm_zero, add_zero]
  constructor
  · rintro ⟨-, -, hreal⟩ θL hθL
    obtain ⟨⟨κ', g⟩, ⟨hκ, hnn, hmem⟩, h0⟩ := hreal _ _ (isAdmissiblePair_parts hθL)
    simp only at hκ hnn hmem
    subst hκ
    refine ⟨hmem.toLp g, ?_, ?_⟩
    · rw [← Lp.coeFn_nonneg]
      filter_upwards [hmem.coeFn_toLp] with x hx
      rw [hx]; exact hnn x
    · rw [residual_eq_ofReal κ' hinv hb hmem.coeFn_toLp.symm (parts_sub_eq θL),
        ENNReal.ofReal_eq_zero] at h0
      exact (hzero _ _).1 (le_antisymm h0 (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  · intro hS
    refine ⟨isFlowFamily_fixedPolicyFamily κ, ?_, fun f_init f_term hpair => ?_⟩
    · rintro ⟨κ', g⟩ ⟨hκ, -, -⟩
      simp only at hκ
      subst hκ
      exact isBoundedPolicy_of_inv hinv hb
    · obtain ⟨fout, hnn, hD⟩ := hS _ (meanProj_pair_eq_zero hpair)
      have hrep := nonneg_rep hnn
      refine ⟨(κ, fun x => max (fout x) 0), ⟨rfl, fun x => le_max_right _ _,
        (Lp.memLp fout).ae_eq hrep.symm⟩, ?_⟩
      rw [residual_eq_ofReal κ hinv hb hrep (pair_sub_eq hpair), (hzero _ _).2 hD,
        ENNReal.ofReal_zero]

/-- **`theo:universality_L2_full`, weak half, in `def:universality`'s own terms**: the family
`{π⋆} × L^p_+(ν)` is weakly `L^p`-universal for `p < ∞`. -/
theorem weaklyUniversal_fixedPolicyFamily_of_kernel (κ : Kernel α α) [IsMarkovKernel κ] {C : ℝ}
    (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν p C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν p hinv hb) ^ n - meanProj ν p‖)
    (hp : p ≠ ⊤) : WeaklyUniversal ν p (fixedPolicyFamily ν p κ) :=
  (weaklyUniversal_fixedPolicyFamily_iff κ hinv hb).2
    (weaklyUniversal_of_kernel κ ν p hinv hb hsum hp)

end Bridge

section BridgeTop

variable {ν : Measure α} [IsFiniteMeasure ν]

/-- **`theo:universality_L2_full`, `p = +∞` clause, in `def:universality`'s own terms.** -/
theorem stronglyUniversal_fixedPolicyFamily_top (κ : Kernel α α) [IsMarkovKernel κ] {C : ℝ}
    (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν ⊤ C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν ⊤ hinv hb) ^ n - meanProj ν ⊤‖) :
    StronglyUniversal ν ⊤ (fixedPolicyFamily ν ⊤ κ) :=
  (stronglyUniversal_fixedPolicyFamily_iff κ hinv hb).2
    (stronglyUniversal_of_kernel_top κ ν hinv hb hsum)

end BridgeTop

/-! ## Inhabitation: the i.i.d. resampling policy -/

section Witness

variable {ν : Measure α} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem coe_const_kernel : ⇑(Kernel.const α ν) = fun _ => ν := funext (Kernel.const_apply ν)

/-- The i.i.d. resampling policy `π⋆(x) := ν` leaves `ν` invariant. -/
theorem bind_const_kernel : ν.bind ⇑(Kernel.const α ν) = ν := by
  rw [coe_const_kernel, Measure.bind_const, measure_univ, one_smul]

theorem bindDensity_const_kernel {g : α → ℝ≥0∞} (hg : ∫⁻ x, g x ∂ν ≠ ⊤) :
    bindDensity (Kernel.const α ν) ν g =ᵐ[ν] fun _ => ∫⁻ x, g x ∂ν := by
  have hpush : (ν.withDensity g).bind ⇑(Kernel.const α ν) = (∫⁻ x, g x ∂ν) • ν := by
    rw [coe_const_kernel, Measure.bind_const, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  rw [bindDensity, hpush]
  filter_upwards [Measure.rnDeriv_smul_left_of_ne_top ν ν hg, Measure.rnDeriv_self ν]
    with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, mul_one]

/-- The density action of the resampling policy is the mean: `P⋆ f = ∫ f dν`, a.e. -/
theorem densityAction_const_kernel {f : α → ℝ} (hf : Integrable f ν) :
    densityAction (Kernel.const α ν) ν f =ᵐ[ν] fun _ => ∫ x, f x ∂ν := by
  filter_upwards [bindDensity_const_kernel (lintegral_ofReal_ne_top hf),
    bindDensity_const_kernel (g := fun y => ENNReal.ofReal (-f y))
      (lintegral_ofReal_ne_top hf.neg)] with x h1 h2
  simp only [densityAction]
  rw [h1, h2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm

/-- The resampling policy is bounded on every `L^p(ν)`, `p ≥ 1`, with constant `1`. -/
theorem isBoundedDensityAction_const_kernel {p : ℝ≥0∞} (hp : 1 ≤ p) :
    IsBoundedDensityAction (Kernel.const α ν) ν p 1 where
  nonneg := zero_le_one
  memLp f hf := (memLp_const (∫ x, f x ∂ν)).ae_eq
    (densityAction_const_kernel (hf.integrable hp)).symm
  eLpNorm_le f hf := by
    have hint := hf.integrable hp
    rw [eLpNorm_congr_ae (densityAction_const_kernel hint), ENNReal.ofReal_one, one_mul]
    have hb : ∀ᵐ _x ∂ν, ‖∫ x, f x ∂ν‖ ≤ ∫ x, ‖f x‖ ∂ν :=
      Eventually.of_forall fun _ => norm_integral_le_integral_norm f
    refine (eLpNorm_le_of_ae_bound hb).trans ?_
    rw [measure_univ, ENNReal.one_rpow, one_mul,
      ofReal_integral_norm_eq_lintegral_enorm hint, ← eLpNorm_one_eq_lintegral_enorm]
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hint.1
    rwa [measure_univ, ENNReal.one_rpow, mul_one] at h

/-- On `L^p(ν)` the density action of the resampling policy **is** the mean projection. -/
theorem densityActionCLM_const_kernel {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    densityActionCLM (Kernel.const α ν) ν p bind_const_kernel
        (isBoundedDensityAction_const_kernel Fact.out) = meanProj ν p := by
  ext1 F
  refine Lp.ext ?_
  have h1 := coeFn_densityActionCLM (Kernel.const α ν) ν p bind_const_kernel
    (isBoundedDensityAction_const_kernel Fact.out) F
  refine (h1.trans (densityAction_const_kernel ((Lp.memLp F).integrable Fact.out))).trans ?_
  rw [meanProj_apply, measure_univ, ENNReal.toReal_one, div_one]
  filter_upwards [Lp.coeFn_smul (∫ x, F x ∂ν) (constOne ν p),
    coeFn_constOne (ν := ν) (p := p)] with x e1 e2
  rw [e1, Pi.smul_apply, e2, smul_eq_mul, mul_one]

/-- The mixing coefficients of the resampling policy vanish from `n = 1` on. -/
theorem summable_const_kernel {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Summable fun n : ℕ => ‖(densityActionCLM (Kernel.const α ν) ν p bind_const_kernel
        (isBoundedDensityAction_const_kernel Fact.out)) ^ n - meanProj ν p‖ := by
  rw [densityActionCLM_const_kernel]
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  have hn0 : n ≠ 0 := by simpa using hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hidem : ∀ k : ℕ, (meanProj ν p) ^ (k + 1) = meanProj ν p := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one]
    | succ k ih =>
        rw [pow_succ, ih]
        exact meanProj_idem (by rw [measure_univ]; exact one_ne_zero)
  rw [hidem k, sub_self, norm_zero]

/-- **Inhabitation of `def:universality`'s weak predicate**: on any probability space the family
`{π⋆} × L^p_+(ν)` of the i.i.d. resampling policy `π⋆(x) = ν` is weakly `L^p`-universal for every
`p ∈ [1, ∞)`. -/
theorem weaklyUniversal_const_kernel {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    WeaklyUniversal ν p (fixedPolicyFamily ν p (Kernel.const α ν)) :=
  weaklyUniversal_fixedPolicyFamily_of_kernel (Kernel.const α ν) bind_const_kernel
    (isBoundedDensityAction_const_kernel Fact.out) summable_const_kernel hp

/-- **Inhabitation of `def:universality`'s strong predicate**: the same family at `p = +∞` is
strongly universal — every pair of bounded densities of equal mass is joined exactly. -/
theorem stronglyUniversal_const_kernel_top :
    StronglyUniversal ν ⊤ (fixedPolicyFamily ν ⊤ (Kernel.const α ν)) :=
  stronglyUniversal_fixedPolicyFamily_top (Kernel.const α ν) bind_const_kernel
    (isBoundedDensityAction_const_kernel le_top) summable_const_kernel

end Witness

end GFNBounds.Core.Family


/-! # `rem:partial_support`: targets without full support -/

namespace GFNBounds.Graph.PartialSupport

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : MarkedGraph V}

/-- A **target** on the terminating states of `G`: `R ≥ 0`, charging only states `x` with an
edge `x → s_f`. -/
structure IsTarget (G : MarkedGraph V) (R : V → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ R x
  supp : ∀ ⦃x⦄, R x ≠ 0 → G.Edge x G.snk

/-- The vertex set of `G'`: `s₀`, `s_f`, and the states from which a directed path of `G`
reaches `supp R`, `supp R` included. -/
def InSub (G : MarkedGraph V) (R : V → ℝ) (v : V) : Prop :=
  v = G.src ∨ v = G.snk ∨ ∃ y, R y ≠ 0 ∧ G.Reach v y

/-- `InSub` as a `Finset`. -/
noncomputable def subVerts (G : MarkedGraph V) (R : V → ℝ) : Finset V := by
  classical exact univ.filter (InSub G R)

omit [DecidableEq V] in
theorem mem_subVerts {R : V → ℝ} {v : V} : v ∈ subVerts G R ↔ InSub G R v := by
  classical
  simp only [subVerts, mem_filter, mem_univ, true_and]

omit [DecidableEq V] in
theorem src_mem_subVerts (R : V → ℝ) : G.src ∈ subVerts G R := mem_subVerts.2 (Or.inl rfl)

omit [DecidableEq V] in
theorem snk_mem_subVerts (R : V → ℝ) : G.snk ∈ subVerts G R :=
  mem_subVerts.2 (Or.inr (Or.inl rfl))

/-- **`G'`** (`rem:partial_support`): the marked subgraph of `G` induced on `subVerts G R`, with
the terminating edges `y → s_f`, `R(y) = 0`, deleted. -/
def subGraph (G : MarkedGraph V) (R : V → ℝ) : MarkedGraph {v // v ∈ subVerts G R} where
  Edge x y := G.Edge x.1 y.1 ∧ ¬ (y.1 = G.snk ∧ R x.1 = 0)
  src := ⟨G.src, src_mem_subVerts R⟩
  snk := ⟨G.snk, snk_mem_subVerts R⟩
  src_ne_snk h := G.src_ne_snk (congrArg Subtype.val h)
  no_edge_into_src x h := G.no_edge_into_src x.1 h.1
  no_edge_out_of_snk y h := G.no_edge_out_of_snk y.1 h.1

omit [Fintype V] [DecidableEq V] in
theorem eq_snk_of_reach_snk {b : V} (h : G.Reach G.snk b) : b = G.snk := by
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, hc, -⟩
  · exact h'.symm
  · exact absurd hc (G.no_edge_out_of_snk c)

omit [DecidableEq V] in
/-- A walk of `G` ending at a state that reaches `supp R` and is not `s_f` is a walk of `G'`. -/
theorem sub_reach {R : V → ℝ} {a b : V} (hab : G.Reach a b) (hb : b ≠ G.snk)
    (hbR : ∃ y, R y ≠ 0 ∧ G.Reach b y) :
    ∃ (ha' : a ∈ subVerts G R) (hb' : b ∈ subVerts G R),
      (subGraph G R).Reach ⟨a, ha'⟩ ⟨b, hb'⟩ := by
  obtain ⟨y, hy, hby⟩ := hbR
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl =>
      have hm : b ∈ subVerts G R := mem_subVerts.2 (Or.inr (Or.inr ⟨y, hy, hby⟩))
      exact ⟨hm, hm, Relation.ReflTransGen.refl⟩
  | head hac hcb ih =>
      rename_i a c
      obtain ⟨hc', hb', hreach⟩ := ih
      have ha' : a ∈ subVerts G R :=
        mem_subVerts.2 (Or.inr (Or.inr ⟨y, hy, (Relation.ReflTransGen.head hac hcb).trans hby⟩))
      have hcsnk : c ≠ G.snk := by
        rintro rfl
        exact hb (eq_snk_of_reach_snk hcb)
      refine ⟨ha', hb', Relation.ReflTransGen.head (b := ⟨c, hc'⟩) ⟨hac, fun h => hcsnk h.1⟩ hreach⟩

omit [Fintype V] [DecidableEq V] in
theorem ne_snk_of_ne_zero {R : V → ℝ} (hR : IsTarget G R) {y : V} (hy : R y ≠ 0) :
    y ≠ G.snk := by
  rintro rfl
  exact G.no_edge_out_of_snk G.snk (hR.supp hy)

omit [DecidableEq V] in
/-- **`G'` is again path-connected** (`rem:partial_support`), as soon as the target is not `0`. -/
theorem subGraph_pathConnected (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTarget G R)
    (hne : ∃ y, R y ≠ 0) : (subGraph G R).PathConnected := by
  obtain ⟨y₀, hy₀⟩ := hne
  have hy₀snk := ne_snk_of_ne_zero hR hy₀
  -- the last edge `y₀ → s_f` survives the deletion
  have hlast : ∀ (hm : y₀ ∈ subVerts G R),
      (subGraph G R).Edge ⟨y₀, hm⟩ (subGraph G R).snk :=
    fun _ => ⟨hR.supp hy₀, fun h => hy₀ h.2⟩
  -- every state that reaches `supp R` reaches `s_f` in `G'`
  have hto : ∀ (b : V) (hbm : b ∈ subVerts G R), b ≠ G.snk → (∃ y, R y ≠ 0 ∧ G.Reach b y) →
      (subGraph G R).Reach ⟨b, hbm⟩ (subGraph G R).snk := by
    intro b hbm _ ⟨y, hy, hby⟩
    obtain ⟨hb'', hy', hr⟩ := sub_reach (R := R) hby (ne_snk_of_ne_zero hR hy)
      ⟨y, hy, Relation.ReflTransGen.refl⟩
    exact hr.tail ⟨hR.supp hy, fun h => hy h.2⟩
  have hsrc_snk : (subGraph G R).Reach (subGraph G R).src (subGraph G R).snk := by
    obtain ⟨hs0, hy', hr⟩ := sub_reach (R := R) (hpc.from_src y₀) hy₀snk
      ⟨y₀, hy₀, Relation.ReflTransGen.refl⟩
    exact hr.tail (hlast hy')
  rintro ⟨s, hs⟩
  rcases mem_subVerts.1 hs with rfl | rfl | ⟨y, hy, hsy⟩
  · exact ⟨Relation.ReflTransGen.refl, hsrc_snk⟩
  · exact ⟨hsrc_snk, Relation.ReflTransGen.refl⟩
  · have hssnk : s ≠ G.snk := by
      rintro rfl
      exact ne_snk_of_ne_zero hR hy (eq_snk_of_reach_snk hsy)
    obtain ⟨hs0, hs', hr⟩ := sub_reach (R := R) (hpc.from_src s) hssnk ⟨y, hy, hsy⟩
    exact ⟨hr, hto s hs hssnk ⟨y, hy, hsy⟩⟩

/-! ## Restricting a backward policy to `G'` -/

omit [DecidableEq V] in
/-- A sum over `V` of a function vanishing off `subVerts G R` is a sum over the subtype. -/
theorem sum_subtype_eq {R : V → ℝ} (f : V → ℝ) (hf : ∀ v, v ∉ subVerts G R → f v = 0) :
    ∑ v : {v // v ∈ subVerts G R}, f v.1 = ∑ v, f v := by
  rw [Finset.sum_coe_sort (subVerts G R) f]
  exact Finset.sum_subset (subset_univ _) fun v _ hv => hf v hv

/-- A **sink row for `G'`**: a probability on the in-neighbours of `s_f` in `G'`, positive on each
of them. -/
structure IsSinkRow (G : MarkedGraph V) (R : V → ℝ) (q : V → ℝ) : Prop where
  nonneg : ∀ y, 0 ≤ q y
  supp : ∀ ⦃y⦄, q y ≠ 0 → G.Edge y G.snk ∧ R y ≠ 0
  sum : ∑ y, q y = 1
  pos : ∀ ⦃y⦄, G.Edge y G.snk → R y ≠ 0 → 0 < q y

omit [DecidableEq V] in
/-- A predecessor of a state of `G'` other than a mark is a state of `G'`. -/
theorem mem_subVerts_of_edge {R : V → ℝ} {s s' : V} (hs : s ∈ subVerts G R) (hsrc : s ≠ G.src)
    (hsnk : s ≠ G.snk) (he : G.Edge s' s) : s' ∈ subVerts G R := by
  rcases mem_subVerts.1 hs with h | h | ⟨y, hy, hsy⟩
  · exact absurd h hsrc
  · exact absurd h hsnk
  · exact mem_subVerts.2 (Or.inr (Or.inr ⟨y, hy, Relation.ReflTransGen.head he hsy⟩))

/-- **The restriction of `π_←` to `G'`**, with sink row `q`: every row but the sink's is `π_←`'s,
read on `G'`. -/
noncomputable def restrictWith (B : BackwardPolicy G) {R : V → ℝ} (q : V → ℝ)
    (hq : IsSinkRow G R q) :
    BackwardPolicy (subGraph G R) where
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
        exact hv (mem_subVerts.2 (Or.inr (Or.inr ⟨v, (hq.supp hc).2, Relation.ReflTransGen.refl⟩)))
    · simp only [h, if_false]
      rw [sum_subtype_eq (fun v => B.pb s.1 v) fun v hv => ?_]
      · exact B.row_sum hsrc
      · by_contra hc
        exact hv (mem_subVerts_of_edge s.2 hsrc h (B.supp hsrc hc))
  supp s s' hs hne := by
    have hsrc : s.1 ≠ G.src := fun h => hs (Subtype.ext h)
    by_cases h : s.1 = G.snk
    · simp only [h, if_true] at hne
      obtain ⟨he, hR⟩ := hq.supp hne
      exact ⟨h ▸ he, fun h' => hR h'.2⟩
    · simp only [h, if_false] at hne
      exact ⟨B.supp hsrc hne, fun h' => h h'.1⟩

theorem restrictWith_pb_of_ne_snk (B : BackwardPolicy G) {R q : V → ℝ} (hq : IsSinkRow G R q)
    {s s' : {v // v ∈ subVerts G R}} (hs : s ≠ (subGraph G R).snk) :
    (restrictWith B q hq).pb s s' = B.pb s.1 s'.1 := by
  have h : s.1 ≠ G.snk := fun h => hs (Subtype.ext h)
  simp only [restrictWith, h, if_false]

theorem restrictWith_pb_snk (B : BackwardPolicy G) {R q : V → ℝ} (hq : IsSinkRow G R q)
    (s' : {v // v ∈ subVerts G R}) :
    (restrictWith B q hq).pb (subGraph G R).snk s' = q s'.1 := by
  simp only [restrictWith, subGraph, if_true]

/-- The restriction is positive on every edge of `G'`. -/
theorem restrictWith_positiveOnEdges (B : BackwardPolicy G) (hB : B.PositiveOnEdges)
    {R q : V → ℝ} (hq : IsSinkRow G R q) : (restrictWith B q hq).PositiveOnEdges := by
  intro s s' he
  by_cases h : s.1 = G.snk
  · simp only [restrictWith, h, if_true]
    exact hq.pos (h ▸ he.1) (fun h' => he.2 ⟨h, h'⟩)
  · simp only [restrictWith, h, if_false]
    exact hB he.1

/-- The normalizer of the renormalized sink row: `π_←`'s sink row summed over the in-neighbours
of `s_f` in `G'`. -/
noncomputable def sinkMass (B : BackwardPolicy G) (R : V → ℝ) : ℝ :=
  ∑ y, if R y = 0 then 0 else B.pb G.snk y

/-- **`π_←`'s sink row, restricted to `G'` and renormalized.** -/
noncomputable def renormRow (B : BackwardPolicy G) (R : V → ℝ) (y : V) : ℝ :=
  if R y = 0 then 0 else B.pb G.snk y / sinkMass B R

omit [DecidableEq V] in
theorem sinkMass_pos (B : BackwardPolicy G) (hB : B.PositiveOnEdges) {R : V → ℝ}
    (hR : IsTarget G R) (hne : ∃ y, R y ≠ 0) : 0 < sinkMass B R := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  refine Finset.sum_pos' (fun y _ => ?_) ⟨y₀, mem_univ _, ?_⟩
  · split_ifs
    · exact le_rfl
    · exact B.nonneg _ _
  · simp only [hy₀, if_false]
    exact hB (hR.supp hy₀)

omit [DecidableEq V] in
theorem isSinkRow_renormRow (B : BackwardPolicy G) (hB : B.PositiveOnEdges) {R : V → ℝ}
    (hR : IsTarget G R) (hne : ∃ y, R y ≠ 0) : IsSinkRow G R (renormRow B R) := by
  have hZ := sinkMass_pos B hB hR hne
  have hsnk : G.snk ≠ G.src := G.src_ne_snk.symm
  refine ⟨fun y => ?_, fun y hy => ?_, ?_, fun y he hRy => ?_⟩
  · unfold renormRow; split_ifs
    · exact le_rfl
    · exact div_nonneg (B.nonneg _ _) hZ.le
  · unfold renormRow at hy
    by_cases h : R y = 0
    · simp only [h, if_true, ne_eq, not_true_eq_false] at hy
    · simp only [h, if_false] at hy
      exact ⟨B.supp hsnk (fun h0 => hy (by rw [h0, zero_div])), h⟩
  · unfold renormRow
    have : ∀ y, (if R y = 0 then (0 : ℝ) else B.pb G.snk y / sinkMass B R)
        = (if R y = 0 then 0 else B.pb G.snk y) / sinkMass B R := by
      intro y; split_ifs <;> simp only [zero_div]
    simp only [this]
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  · unfold renormRow
    simp only [hRy, if_false]
    exact div_pos (hB he) hZ

/-- **`rem:partial_support`, the restriction claim**: a backward policy on `G` positive on its
edges restricts to one on `G'` positive on the edges of `G'`, with only its sink row renormalized
— every other row is `π_←`'s. -/
theorem restrict_policy (B : BackwardPolicy G) (hB : B.PositiveOnEdges) {R : V → ℝ}
    (hR : IsTarget G R) (hne : ∃ y, R y ≠ 0) :
    ∃ B' : BackwardPolicy (subGraph G R), B'.PositiveOnEdges ∧
      (∀ s s', s ≠ (subGraph G R).snk → B'.pb s s' = B.pb s.1 s'.1) ∧
      (∀ s', B'.pb (subGraph G R).snk s' = renormRow B R s'.1) :=
  ⟨restrictWith B (renormRow B R) (isSinkRow_renormRow B hB hR hne),
    restrictWith_positiveOnEdges B hB _, fun _ _ hs => restrictWith_pb_of_ne_snk B _ hs,
    fun s' => restrictWith_pb_snk B _ s'⟩

/-! ## The flow-matching constraint on `G`, for an edge flow -/

/-- The star outflow of an edge flow `e`: the flow out of `u` along every edge but the
terminating one. -/
noncomputable def outStar (G : MarkedGraph V) (e : V → V → ℝ) (u : V) : ℝ :=
  ∑ w ∈ univ.erase G.snk, e u w

/-- The star forward policy of an edge flow, `e(u → v)/f_out⋆(u)`. -/
noncomputable def fwdStarE (G : MarkedGraph V) (e : V → V → ℝ) (u v : V) : ℝ :=
  e u v / outStar G e u

/-- **`equ:FM_const` on `𝒮 = 𝒱 ∖ {s₀, s_f}` for an edge flow `e` and a terminal flow `T`**:
`F_init(v) + ((f_out⋆ μ) π⋆)(v) − T(v) − f_out⋆(v)`, with `F_init(v) = e(s₀ → v)`. The same shape
as `BackwardPolicy.fmDefect`, with the terminal flow a free argument. -/
noncomputable def fmDefectE (G : MarkedGraph V) (e : V → V → ℝ) (T : V → ℝ) (v : V) : ℝ :=
  e G.src v + (∑ u ∈ G.internal, outStar G e u * fwdStarE G e u v) - T v - outStar G e v

/-- On the flow of `theo:universality_graphs`(3), `fmDefectE` **is** the library's `fmDefect`. -/
theorem fmDefect_eq_fmDefectE (B : BackwardPolicy G) {lam : V → ℝ} (h : B.IsInvProb lam)
    (c : ℝ) (v : V) :
    B.fmDefect lam c v = fmDefectE G (B.edgeFlow lam c) (B.termFlow lam c) v := by
  have hout : ∀ u, B.outflowStar lam c u = outStar G (B.edgeFlow lam c) u :=
    fun u => B.outflowStar_eq_sum h c u
  simp only [BackwardPolicy.fmDefect, fmDefectE, BackwardPolicy.initFlow, BackwardPolicy.fwdStar,
    fwdStarE, hout]

theorem outStar_mul_fwdStarE {e : V → V → ℝ} (he : ∀ u v, 0 ≤ e u v) (u : V) {v : V}
    (hv : v ≠ G.snk) : outStar G e u * fwdStarE G e u v = e u v := by
  by_cases hu : outStar G e u = 0
  · have h0 : e u v = 0 := by
      unfold outStar at hu
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => he u w)).1 hu v
        (mem_erase.2 ⟨hv, mem_univ v⟩)
    rw [hu, zero_mul, h0]
  · simp only [fwdStarE]
    field_simp

/-- For a non-negative edge flow, the defect at an internal state is conservation plus the
terminal mismatch: `D(v) = (in − out)(v) − e(s_f → v) + e(v → s_f) − T(v)`. -/
theorem fmDefectE_eq {e : V → V → ℝ} (he : ∀ u v, 0 ≤ e u v) (T : V → ℝ) {v : V}
    (hv : v ∈ G.internal) :
    fmDefectE G e T v
      = (∑ u, e u v) - (∑ w, e v w) - e G.snk v + e v G.snk - T v := by
  obtain ⟨-, hvsnk⟩ := MarkedGraph.mem_internal.1 hv
  have hsum : ∑ u ∈ G.internal, outStar G e u * fwdStarE G e u v = ∑ u ∈ G.internal, e u v :=
    Finset.sum_congr rfl fun u _ => outStar_mul_fwdStarE he u hvsnk
  have h1 : (∑ u ∈ univ.erase G.src, e u v) + e G.src v = ∑ u, e u v :=
    Finset.sum_erase_add _ _ (mem_univ _)
  have h2 : (∑ u ∈ G.internal, e u v) + e G.snk v = ∑ u ∈ univ.erase G.src, e u v :=
    Finset.sum_erase_add _ _ (mem_erase.2 ⟨G.src_ne_snk.symm, mem_univ _⟩)
  have h3 : (∑ w ∈ univ.erase G.snk, e v w) + e v G.snk = ∑ w, e v w :=
    Finset.sum_erase_add _ _ (mem_univ _)
  simp only [fmDefectE]
  rw [hsum]
  simp only [outStar]
  linarith

/-! ## Claim (a): the flow of `G'`, extended by zero, matches `R` exactly on `G` -/

section Extension

variable {R : V → ℝ}

/-- Extension by zero of an edge flow of `G'` to `G`. -/
noncomputable def extend (e' : {v // v ∈ subVerts G R} → {v // v ∈ subVerts G R} → ℝ)
    (u v : V) : ℝ :=
  if h : u ∈ subVerts G R ∧ v ∈ subVerts G R then e' ⟨u, h.1⟩ ⟨v, h.2⟩ else 0

theorem extend_of_mem {e' : {v // v ∈ subVerts G R} → {v // v ∈ subVerts G R} → ℝ}
    (u v : {v // v ∈ subVerts G R}) : extend e' u.1 v.1 = e' u v := by
  simp only [extend, u.2, v.2, and_self, dif_pos]

theorem extend_of_not_mem_left {e' : {v // v ∈ subVerts G R} → {v // v ∈ subVerts G R} → ℝ}
    {u : V} (hu : u ∉ subVerts G R) (v : V) : extend e' u v = 0 := by
  simp only [extend, hu, false_and, dif_neg, not_false_eq_true]

theorem extend_of_not_mem_right {e' : {v // v ∈ subVerts G R} → {v // v ∈ subVerts G R} → ℝ}
    (u : V) {v : V} (hv : v ∉ subVerts G R) : extend e' u v = 0 := by
  simp only [extend, hv, and_false, dif_neg, not_false_eq_true]

theorem sum_extend_in (e' : {v // v ∈ subVerts G R} → {v // v ∈ subVerts G R} → ℝ)
    (v : {v // v ∈ subVerts G R}) : ∑ u, extend e' u v.1 = ∑ u, e' u v := by
  rw [← sum_subtype_eq (R := R) (fun u => extend e' u v.1)
    fun u hu => extend_of_not_mem_left hu _]
  exact Finset.sum_congr rfl fun u _ => extend_of_mem u v

theorem sum_extend_out (e' : {v // v ∈ subVerts G R} → {v // v ∈ subVerts G R} → ℝ)
    (u : {v // v ∈ subVerts G R}) : ∑ v, extend e' u.1 v = ∑ v, e' u v := by
  rw [← sum_subtype_eq (R := R) (fun v => extend e' u.1 v)
    fun v hv => extend_of_not_mem_right _ hv]
  exact Finset.sum_congr rfl fun v _ => extend_of_mem u v

/-- **`rem:partial_support`, claim (a).** Let `G` be path-connected, `π_←` a backward policy on `G`
positive on its edges, and `R` a target of mass `Z > 0` on the terminating states. On `G'`, the
backward policy with `π_←`'s rows and sink row `R/Z` is positive on the edges of `G'`, and
`theo:universality_graphs` applies to it: with `λ'` its invariant probability and
`c = Z/λ'(s₀)`, the element `(π̂'^{λ'}, c λ')` lies in the frozen-backward family of `G'`, and its
edge flow extended by zero to `G` is non-negative, carries initial mass `Z`, has terminal flow
exactly `R`, and satisfies the flow-matching constraint of `G` at every internal state. -/
theorem partial_support_exact (hpc : G.PathConnected) (B : BackwardPolicy G)
    (hB : B.PositiveOnEdges) (hR : IsTarget G R) (hZ : 0 < ∑ y, R y) :
    ∃ hq : IsSinkRow G R (fun y => R y / ∑ z, R z),
      (restrictWith B _ hq).PositiveOnEdges ∧ (subGraph G R).PathConnected ∧
      (∃ lam, (restrictWith B _ hq).IsInvProb lam) ∧
      ∀ lam : {v // v ∈ subVerts G R} → ℝ, (restrictWith B _ hq).IsInvProb lam →
        let c := (∑ y, R y) / lam (subGraph G R).src
        let B' := restrictWith B _ hq
        B'.FrozenBalance (B'.reversal lam) (fun x => c * lam x) ∧
        (∀ u v, 0 ≤ B'.reversal lam u v) ∧ (∀ u, ∑ v, B'.reversal lam u v = 1) ∧
        (∀ u v, 0 ≤ extend (B'.edgeFlow lam c) u v) ∧
        (∑ v, extend (B'.edgeFlow lam c) G.src v) = ∑ y, R y ∧
        (∀ x, extend (B'.edgeFlow lam c) x G.snk = R x) ∧
        (∀ v ∈ G.internal, fmDefectE G (extend (B'.edgeFlow lam c)) R v = 0) := by
  set Z := ∑ y, R y with hZdef
  have hne : ∃ y, R y ≠ 0 := by
    by_contra hc
    push Not at hc
    simp only [hc, Finset.sum_const_zero] at hZdef
    rw [hZdef] at hZ; exact lt_irrefl _ hZ
  have hq : IsSinkRow G R (fun y => R y / Z) := by
    refine ⟨fun y => div_nonneg (hR.nonneg y) hZ.le, fun y hy => ?_, ?_, fun y _ hRy => ?_⟩
    · have hRy : R y ≠ 0 := fun h => hy (by simp only [h, zero_div])
      exact ⟨hR.supp hRy, hRy⟩
    · rw [← Finset.sum_div]; exact div_self hZ.ne'
    · exact div_pos ((hR.nonneg y).lt_of_ne (Ne.symm hRy)) hZ
  refine ⟨hq, restrictWith_positiveOnEdges B hB hq, subGraph_pathConnected hpc hR hne,
    (restrictWith B _ hq).exists_invProb, fun lam hlam => ?_⟩
  intro c B'
  have hpc' := subGraph_pathConnected hpc hR hne
  have hB' : B'.PositiveOnEdges := restrictWith_positiveOnEdges B hB hq
  have hlpos : ∀ x, 0 < lam x := fun x => hlam.pos hpc' hB' x
  have hc : 0 < c := div_pos hZ (hlpos _)
  have hcZ : c * lam (subGraph G R).src = Z := div_mul_cancel₀ Z (hlpos _).ne'
  have hnn : ∀ u v, 0 ≤ extend (B'.edgeFlow lam c) u v := by
    intro u v
    by_cases h : u ∈ subVerts G R ∧ v ∈ subVerts G R
    · simp only [extend, h, and_self, dif_pos]
      exact B'.edgeFlow_nonneg hlam.nonneg hc.le _ _
    · simp only [extend, h, dif_neg, not_false_eq_true, le_refl]
  have hterm : ∀ x, extend (B'.edgeFlow lam c) x G.snk = R x := by
    intro x
    by_cases hx : x ∈ subVerts G R
    · have h1 := extend_of_mem (e' := B'.edgeFlow lam c) ⟨x, hx⟩ (subGraph G R).snk
      have h2 := B'.termFlow_eq_target hlam hcZ ⟨x, hx⟩
      simp only [BackwardPolicy.termFlow] at h2
      change extend (B'.edgeFlow lam c) x G.snk = _ at h1
      rw [h1, h2, restrictWith_pb_snk]
      field_simp
    · rw [extend_of_not_mem_left hx]
      by_contra hc'
      exact hx (mem_subVerts.2 (Or.inr (Or.inr ⟨x, Ne.symm hc', Relation.ReflTransGen.refl⟩)))
  refine ⟨B'.frozenBalance_reversal hlpos c, B'.reversal_nonneg (fun x => (hlpos x).le),
    fun u => B'.sum_reversal hlam (hlpos u).ne', hnn, ?_, hterm, fun v hv => ?_⟩
  · have h := sum_extend_out (B'.edgeFlow lam c) (subGraph G R).src
    change ∑ v, extend (B'.edgeFlow lam c) G.src v = _ at h
    rw [h]
    have := B'.sum_initFlow hlam c
    simp only [BackwardPolicy.initFlow] at this
    rw [this, hcZ]
  · rw [fmDefectE_eq hnn R hv, hterm v]
    obtain ⟨hvsrc, -⟩ := MarkedGraph.mem_internal.1 hv
    by_cases hvm : v ∈ subVerts G R
    · have hin := sum_extend_in (B'.edgeFlow lam c) ⟨v, hvm⟩
      have hout := sum_extend_out (B'.edgeFlow lam c) ⟨v, hvm⟩
      rw [B'.sum_edgeFlow_in lam c] at hin
      rw [B'.sum_edgeFlow_out hlam c] at hout
      have hs : extend (B'.edgeFlow lam c) G.snk v = 0 := by
        have h1 := extend_of_mem (e' := B'.edgeFlow lam c) (subGraph G R).snk ⟨v, hvm⟩
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

end Extension

/-! ## Claim (b): over the union of the frozen-backward families of `G` -/

section Union

/-- **The union of the frozen-backward families of `G`**, one for each backward policy positive
on its edges: pairs `(π_→, f_out)` with `π_→` a Markov kernel, `f_out ≥ 0`, and
`(f_out μ) ⊗ π_→ = π̂_← ⊗ (f_out μ)` for some such `π_←` (`theo:universality_graphs`(2)). -/
def FrozenUnion (G : MarkedGraph V) : Set ((V → V → ℝ) × (V → ℝ)) :=
  {θ | ∃ B : BackwardPolicy G, B.PositiveOnEdges ∧ (∀ u, ∑ v, θ.1 u v = 1) ∧
    (∀ u v, 0 ≤ θ.1 u v) ∧ (∀ x, 0 ≤ θ.2 x) ∧ B.FrozenBalance θ.1 θ.2}

/-- The edge flow of a pair: `e(u → v) = f_out(u) π_→(u → v)`. -/
def memberFlow (θ : (V → V → ℝ) × (V → ℝ)) (u v : V) : ℝ := θ.2 u * θ.1 u v

/-- **Every element of the union is the trivial element or has terminal flow `Z' π_←(s_f → ·)`,
`Z' > 0`, positive on every terminating state** (`rem:partial_support`, last clause). -/
theorem member_dichotomy (hpc : G.PathConnected) {θ : (V → V → ℝ) × (V → ℝ)}
    (hθ : θ ∈ FrozenUnion G) :
    θ.2 = 0 ∨ ∃ B : BackwardPolicy G, B.PositiveOnEdges ∧ 0 < θ.2 G.snk ∧
      (∀ x, memberFlow θ x G.snk = θ.2 G.snk * B.pb G.snk x) ∧
      ∀ x, G.Edge x G.snk → 0 < memberFlow θ x G.snk := by
  obtain ⟨B, hB, hrow, -, hnn, hfb⟩ := hθ
  by_cases h0 : θ.2 = 0
  · exact Or.inl h0
  · right
    obtain ⟨lam, hlam⟩ := B.exists_invProb
    obtain ⟨hc, hray, -⟩ := B.frozenBalance_eq hpc hB hlam hrow hnn h0 hfb
    have hsnk : 0 < θ.2 G.snk := by
      rw [hray]; exact mul_pos hc (hlam.pos hpc hB _)
    have hterm : ∀ x, memberFlow θ x G.snk = θ.2 G.snk * B.pb G.snk x := by
      intro x
      simp only [memberFlow]
      rw [hfb x G.snk, B.phat_of_ne_src G.src_ne_snk.symm, mul_comm]
    refine ⟨B, hB, hsnk, hterm, fun x hx => ?_⟩
    rw [hterm]
    exact mul_pos hsnk (hB hx)

/-- **The defect of an element of the union against a target `R`** is its terminal mismatch:
`D(v) = f_out(v) π_→(v → s_f) − R(v)` at every internal state. -/
theorem fmDefectE_member {θ : (V → V → ℝ) × (V → ℝ)} (hθ : θ ∈ FrozenUnion G) (R : V → ℝ)
    {v : V} (hv : v ∈ G.internal) :
    fmDefectE G (memberFlow θ) R v = memberFlow θ v G.snk - R v := by
  obtain ⟨B, -, hrow, -, hnn, hfb⟩ := hθ
  have he : ∀ u w, 0 ≤ memberFlow θ u w := by
    intro u w
    simp only [memberFlow]
    rw [hfb u w]
    exact mul_nonneg (B.phat_nonneg _ _) (hnn _)
  obtain ⟨hvsrc, -⟩ := MarkedGraph.mem_internal.1 hv
  have hin : ∑ u, memberFlow θ u v = θ.2 v := by
    simp only [memberFlow]
    rw [Finset.sum_congr rfl fun u _ => hfb u v, ← Finset.sum_mul, B.phat_row_sum, one_mul]
  have hout : ∑ w, memberFlow θ v w = θ.2 v := by
    simp only [memberFlow]
    rw [← Finset.mul_sum, hrow v, mul_one]
  have hs : memberFlow θ G.snk v = 0 := by
    simp only [memberFlow]
    rw [hfb G.snk v, B.phat_snk_of_ne_src hvsrc, zero_mul]
  rw [fmDefectE_eq he R hv, hin, hout, hs]
  ring

omit [Fintype V] [DecidableEq V] in
/-- A path-connected marked graph has a terminating state. -/
theorem exists_terminating (hpc : G.PathConnected) : ∃ y, G.Edge y G.snk := by
  rcases Relation.ReflTransGen.cases_tail (hpc.reach_src_snk G.src) with h | ⟨y, -, hy⟩
  · exact absurd h.symm G.src_ne_snk
  · exact ⟨y, hy⟩

/-- **A backward policy positive on the edges exists** on a path-connected marked graph: the
uniform law on the in-neighbours. -/
theorem exists_positive_policy (hpc : G.PathConnected) :
    ∃ B : BackwardPolicy G, B.PositiveOnEdges := by
  classical
  let N : V → Finset V := fun s => univ.filter fun s' => G.Edge s' s
  have hN : ∀ s, s ≠ G.src → 0 < (N s).card := by
    intro s hs
    obtain ⟨y, hy⟩ := MarkedGraph.exists_hatEdge_into hpc s
    rcases hy with hy | ⟨-, h⟩
    · exact Finset.card_pos.2 ⟨y, by simp only [N, mem_filter, mem_univ, true_and]; exact hy⟩
    · exact absurd h hs
  refine ⟨⟨fun s s' => if s = G.src then 0 else if G.Edge s' s then 1 / (N s).card else 0,
    fun s s' => ?_, fun s hs => ?_, fun s s' hs hne => ?_⟩, fun s s' he => ?_⟩
  · split_ifs <;> first | exact le_rfl | positivity
  · simp only [hs, if_false]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    change ((N s).card : ℝ) * (1 / ((N s).card : ℝ)) = 1
    have : ((N s).card : ℝ) ≠ 0 := by exact_mod_cast (hN s hs).ne'
    field_simp
  · simp only [hs, if_false] at hne
    by_contra hc
    simp only [hc, if_false, ne_eq, not_true_eq_false] at hne
  · have hs : s ≠ G.src := by rintro rfl; exact G.no_edge_into_src s' he
    simp only [hs, he, if_false, if_true]
    have := hN s hs
    positivity

/-- A backward policy with its sink row replaced by a probability `q` on the in-neighbours of
`s_f`. -/
noncomputable def withSinkRow (B : BackwardPolicy G) (q : V → ℝ) (hnn : ∀ y, 0 ≤ q y)
    (hsum : ∑ y, q y = 1) (hsupp : ∀ ⦃y⦄, q y ≠ 0 → G.Edge y G.snk) : BackwardPolicy G where
  pb s s' := if s = G.snk then q s' else B.pb s s'
  nonneg s s' := by split_ifs; exacts [hnn _, B.nonneg _ _]
  row_sum s hs := by split_ifs; exacts [hsum, B.row_sum hs]
  supp s s' hs hne := by
    split_ifs at hne with h
    · exact h ▸ hsupp hne
    · exact B.supp hs hne

/-- `unif`: the uniform probability on the terminating states `{y | y → s_f}`. -/
noncomputable def unif (G : MarkedGraph V) (y : V) : ℝ := by
  classical exact
    if G.Edge y G.snk then 1 / ((univ.filter fun z => G.Edge z G.snk).card : ℝ) else 0

/-- **The full-support targets** `R_ε := (1 − ε) R + ε Z unif` of `rem:partial_support`, with
`Z = ∑ R`. -/
noncomputable def epsTarget (G : MarkedGraph V) (R : V → ℝ) (ε : ℝ) (y : V) : ℝ :=
  (1 - ε) * R y + ε * (∑ z, R z) * unif G y

omit [DecidableEq V] in
theorem unif_nonneg (y : V) : 0 ≤ unif G y := by
  classical
  simp only [unif]
  split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq V] in
theorem unif_le_one (y : V) : unif G y ≤ 1 := by
  classical
  simp only [unif]
  split_ifs with h
  · have hpos : 0 < (univ.filter fun z => G.Edge z G.snk).card :=
      Finset.card_pos.2 ⟨y, by simp only [mem_filter, mem_univ, true_and]; exact h⟩
    have h1 : (1 : ℝ) ≤ (univ.filter fun z => G.Edge z G.snk).card := by exact_mod_cast hpos
    rw [div_le_one (by linarith)]; exact h1
  · exact zero_le_one

omit [DecidableEq V] in
theorem unif_pos {y : V} (hy : G.Edge y G.snk) : 0 < unif G y := by
  classical
  have hpos : 0 < (univ.filter fun z => G.Edge z G.snk).card :=
    Finset.card_pos.2 ⟨y, by simp only [mem_filter, mem_univ, true_and]; exact hy⟩
  simp only [unif, hy, if_true]
  positivity

omit [DecidableEq V] in
theorem sum_unif (hpc : G.PathConnected) : ∑ y, unif G y = 1 := by
  classical
  obtain ⟨y₀, hy₀⟩ := exists_terminating hpc
  have hpos : 0 < (univ.filter fun z => G.Edge z G.snk).card :=
    Finset.card_pos.2 ⟨y₀, by simp only [mem_filter, mem_univ, true_and]; exact hy₀⟩
  have hne : ((univ.filter fun z => G.Edge z G.snk).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [unif]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  field_simp

omit [DecidableEq V] in
theorem unif_eq_zero {y : V} (hy : ¬ G.Edge y G.snk) : unif G y = 0 := by
  classical
  simp only [unif, hy, if_false]

omit [DecidableEq V] in
/-- `R_ε` is a target: non-negative and carried by the terminating states. -/
theorem isTarget_epsTarget {R : V → ℝ} (hR : IsTarget G R) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsTarget G (epsTarget G R ε) := by
  have hZ : 0 ≤ ∑ z, R z := Finset.sum_nonneg fun z _ => hR.nonneg z
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · have := hR.nonneg y; have := unif_nonneg (G := G) y
    have : 0 ≤ 1 - ε := by linarith
    simp only [epsTarget]; positivity
  · by_contra hc
    apply hy
    have hRy : R y = 0 := by by_contra h; exact hc (hR.supp h)
    simp only [epsTarget, hRy, unif_eq_zero hc, mul_zero, add_zero]

omit [DecidableEq V] in
/-- `R_ε` has full support on the terminating states, for `ε ∈ (0, 1]` and `Z > 0`. -/
theorem epsTarget_pos {R : V → ℝ} (hR : IsTarget G R) (hZ : 0 < ∑ z, R z) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) {y : V} (hy : G.Edge y G.snk) : 0 < epsTarget G R ε y := by
  have := hR.nonneg y
  have : 0 ≤ 1 - ε := by linarith
  have h1 : 0 ≤ (1 - ε) * R y := by positivity
  have h2 : 0 < ε * (∑ z, R z) * unif G y := by have := unif_pos hy; positivity
  simp only [epsTarget]; linarith

omit [DecidableEq V] in
/-- `R_ε` has the mass `Z` of `R`. -/
theorem sum_epsTarget (hpc : G.PathConnected) (R : V → ℝ) (ε : ℝ) :
    ∑ y, epsTarget G R ε y = ∑ y, R y := by
  simp only [epsTarget]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_unif hpc]
  ring

/-- **`rem:partial_support`, claim (b): `R_ε` is exactly matched in the union, within `εZ` of
`R`.** For `ε ∈ (0, 1]`, the balanced flow of `theo:universality_graphs` for the backward policy
whose sink row is `R_ε/Z` lies in the union of the frozen-backward families of `G`, is exactly
matched to `R_ε`, and its defect against `R` is at most `εZ` at every internal state. -/
theorem member_epsTarget (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTarget G R)
    (hZ : 0 < ∑ y, R y) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ θ ∈ FrozenUnion G,
      (∀ v ∈ G.internal, fmDefectE G (memberFlow θ) (epsTarget G R ε) v = 0) ∧
      ∀ v ∈ G.internal, |fmDefectE G (memberFlow θ) R v| ≤ ε * ∑ y, R y := by
  set Z := ∑ y, R y with hZdef
  have hRε := isTarget_epsTarget hR hε0.le hε1
  let q : V → ℝ := fun y => epsTarget G R ε y / Z
  have hqnn : ∀ y, 0 ≤ q y := fun y => div_nonneg (hRε.nonneg y) hZ.le
  have hqsum : ∑ y, q y = 1 := by
    simp only [q]
    rw [← Finset.sum_div, sum_epsTarget hpc, div_self hZ.ne']
  have hqsupp : ∀ ⦃y⦄, q y ≠ 0 → G.Edge y G.snk := by
    intro y hy
    exact hRε.supp fun h => hy (by simp only [q, h, zero_div])
  obtain ⟨B₀, hB₀⟩ := exists_positive_policy hpc
  let B := withSinkRow B₀ q hqnn hqsum hqsupp
  have hBsnk : ∀ x, B.pb G.snk x = q x := fun x => by simp only [B, withSinkRow, if_true]
  have hB : B.PositiveOnEdges := by
    intro s s' he
    by_cases hs : s = G.snk
    · subst hs; rw [hBsnk]; exact div_pos (epsTarget_pos hR hZ hε0 hε1 he) hZ
    · simp only [B, withSinkRow, hs, if_false]; exact hB₀ he
  obtain ⟨lam, hlam⟩ := B.exists_invProb
  have hlpos : ∀ x, 0 < lam x := fun x => hlam.pos hpc hB x
  set c := Z / lam G.src with hc
  have hcZ : c * lam G.snk = Z := by
    rw [hlam.lam_snk_eq_src, hc]; exact div_mul_cancel₀ Z (hlpos _).ne'
  let θ : (V → V → ℝ) × (V → ℝ) := (B.reversal lam, fun x => c * lam x)
  have hmem : θ ∈ FrozenUnion G :=
    ⟨B, hB, fun u => B.sum_reversal hlam (hlpos u).ne',
      fun u v => B.reversal_nonneg (fun x => (hlpos x).le) u v,
      fun x => mul_nonneg (div_pos hZ (hlpos _)).le (hlpos x).le,
      B.frozenBalance_reversal hlpos c⟩
  have hterm : ∀ x, memberFlow θ x G.snk = epsTarget G R ε x := by
    intro x
    have h := B.frozenBalance_reversal hlpos c x G.snk
    simp only [memberFlow, θ]
    rw [h, B.phat_of_ne_src G.src_ne_snk.symm, hBsnk]
    show epsTarget G R ε x / Z * (c * lam G.snk) = epsTarget G R ε x
    rw [hcZ, div_mul_cancel₀ _ hZ.ne']
  refine ⟨θ, hmem, fun v hv => ?_, fun v hv => ?_⟩
  · rw [fmDefectE_member hmem _ hv, hterm, sub_self]
  · rw [fmDefectE_member hmem _ hv, hterm]
    have hRle : R v ≤ Z := Finset.single_le_sum (fun y _ => hR.nonneg y) (mem_univ v)
    have hRnn := hR.nonneg v
    have hu := unif_nonneg (G := G) v
    have hu1 := unif_le_one (G := G) v
    have hexp : epsTarget G R ε v - R v = ε * (Z * unif G v - R v) := by
      simp only [epsTarget, hZdef]; ring
    rw [hexp, abs_mul, abs_of_pos hε0]
    have hab : |Z * unif G v - R v| ≤ Z := by
      rw [abs_le]
      constructor
      · have : 0 ≤ Z * unif G v := mul_nonneg hZ.le hu
        linarith
      · have : Z * unif G v ≤ Z := by
          calc Z * unif G v ≤ Z * 1 := by gcongr
            _ = Z := mul_one Z
        linarith
    exact mul_le_mul_of_nonneg_left hab hε0.le

/-- The vanishing half with a prescribed accuracy `δ`: take `ε = min 1 (δ/Z)`. -/
theorem exists_member_close (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTarget G R)
    (hZ : 0 < ∑ y, R y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ ∈ FrozenUnion G, ∀ v ∈ G.internal, |fmDefectE G (memberFlow θ) R v| ≤ δ := by
  set ε : ℝ := min 1 (δ / ∑ y, R y) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (div_pos hδ hZ)
  obtain ⟨θ, hθ, -, hclose⟩ := member_epsTarget hpc hR hZ hε0 (min_le_left _ _)
  refine ⟨θ, hθ, fun v hv => (hclose v hv).trans ?_⟩
  calc ε * ∑ y, R y ≤ δ / (∑ y, R y) * ∑ y, R y := by gcongr; exact min_le_right _ _
    _ = δ := div_mul_cancel₀ δ hZ.ne'

/-- **`rem:partial_support`, claim (b), the non-attainment half.** If `R` is non-zero at some
internal state and vanishes at some terminating state — an internal state with an edge to `s_f` —
then no element of the union is exactly matched to `R`: some internal state carries a non-zero
defect. No edge condition is needed. -/
theorem not_attained (hpc : G.PathConnected) {R : V → ℝ} (hne : ∃ x ∈ G.internal, R x ≠ 0)
    (hvan : ∃ y ∈ G.internal, G.Edge y G.snk ∧ R y = 0)
    {θ : (V → V → ℝ) × (V → ℝ)} (hθ : θ ∈ FrozenUnion G) :
    ∃ v ∈ G.internal, fmDefectE G (memberFlow θ) R v ≠ 0 := by
  rcases member_dichotomy hpc hθ with h0 | ⟨B, -, -, -, hpos⟩
  · obtain ⟨x, hxi, hx⟩ := hne
    refine ⟨x, hxi, ?_⟩
    rw [fmDefectE_member hθ R hxi]
    simp only [memberFlow, h0, Pi.zero_apply, zero_mul, zero_sub, neg_ne_zero]
    exact hx
  · obtain ⟨y, hyi, hy, hRy⟩ := hvan
    refine ⟨y, hyi, ?_⟩
    rw [fmDefectE_member hθ R hyi, hRy, sub_zero]
    exact (hpos y hy).ne'

/-- Without an edge `s₀ → s_f`, every state with an edge to `s_f` is internal. -/
theorem mem_internal_of_edge_snk (hsrc : ¬ G.Edge G.src G.snk)
    {x : V} (hx : G.Edge x G.snk) : x ∈ G.internal := by
  refine MarkedGraph.mem_internal.2 ⟨?_, ?_⟩
  · rintro rfl; exact hsrc hx
  · rintro rfl; exact G.no_edge_out_of_snk G.snk hx

/-- `not_attained` with unrestricted witnesses, under `¬ (s₀ → s_f)`: a corollary. -/
theorem not_attained_of_not_edge_src_snk (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTarget G R)
    (hsrc : ¬ G.Edge G.src G.snk) (hne : ∃ x, R x ≠ 0) (hvan : ∃ y, G.Edge y G.snk ∧ R y = 0)
    {θ : (V → V → ℝ) × (V → ℝ)} (hθ : θ ∈ FrozenUnion G) :
    ∃ v ∈ G.internal, fmDefectE G (memberFlow θ) R v ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hRy⟩ := hvan
  exact not_attained hpc ⟨x, mem_internal_of_edge_snk hsrc (hR.supp hx), hx⟩
    ⟨y, mem_internal_of_edge_snk hsrc hy, hy, hRy⟩ hθ

/-- **`rem:partial_support`, "not to that of `G`"**: an edge flow with positive initial mass whose
terminal flow is `R`, where `R` vanishes on some terminating state, is the edge flow of no element
of the union of the frozen-backward families of `G`. -/
theorem not_memberFlow (hpc : G.PathConnected) {R : V → ℝ}
    (hvan : ∃ y, G.Edge y G.snk ∧ R y = 0) {e : V → V → ℝ} (hterm : ∀ x, e x G.snk = R x)
    (hmass : 0 < ∑ v, e G.src v) {θ : (V → V → ℝ) × (V → ℝ)} (hθ : θ ∈ FrozenUnion G) :
    memberFlow θ ≠ e := by
  intro heq
  rcases member_dichotomy hpc hθ with h0 | ⟨B, -, -, -, hpos⟩
  · have : ∑ v, e G.src v = 0 := by
      rw [← heq]
      simp only [memberFlow, h0, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rw [this] at hmass
    exact lt_irrefl _ hmass
  · obtain ⟨y, hy, hRy⟩ := hvan
    have := hpos y hy
    rw [heq, hterm, hRy] at this
    exact lt_irrefl _ this

/-- **`rem:partial_support`, claim (a), "not to that of `G`"**: when `R` vanishes on a terminating
state, the flow of `partial_support_exact`, extended by zero, is the edge flow of no element of
the union of the frozen-backward families of `G`. -/
theorem partial_support_not_in_G (hpc : G.PathConnected) (B : BackwardPolicy G)
    (hB : B.PositiveOnEdges) {R : V → ℝ} (hR : IsTarget G R) (hZ : 0 < ∑ y, R y)
    (hvan : ∃ y, G.Edge y G.snk ∧ R y = 0) :
    ∃ hq : IsSinkRow G R (fun y => R y / ∑ z, R z),
      ∀ lam : {v // v ∈ subVerts G R} → ℝ, (restrictWith B _ hq).IsInvProb lam →
        ∀ θ ∈ FrozenUnion G, memberFlow θ
          ≠ extend ((restrictWith B _ hq).edgeFlow lam ((∑ y, R y) / lam (subGraph G R).src)) := by
  obtain ⟨hq, -, -, -, hall⟩ := partial_support_exact hpc B hB hR hZ
  refine ⟨hq, fun lam hlam θ hθ => ?_⟩
  obtain ⟨-, -, -, -, hmass, hterm, -⟩ := hall lam hlam
  exact not_memberFlow hpc hvan hterm (by rw [hmass]; exact hZ) hθ

end Union

/-! ## The residuals in `L^p` of the counting measure on `𝒮` -/

section Norms

open MeasureTheory
open scoped ENNReal

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **The universality residual on a graph**: `‖δf_init‖_{L^p(μ)} + ‖δf_term‖_{L^p(μ)}`, `μ` the
counting measure on the internal state space `𝒮`, with `δf_init = D⁻`, `δf_term = D⁺` for the
defect `D = fmDefectE G e T` of `equ:FM_const`. -/
noncomputable def graphResidual (G : MarkedGraph V) (p : ℝ≥0∞) (e : V → V → ℝ) (T : V → ℝ) :
    ℝ≥0∞ :=
  eLpNorm (fun v => if v ∈ G.internal then (fmDefectE G e T v)⁻ else 0) p Measure.count
    + eLpNorm (fun v => if v ∈ G.internal then (fmDefectE G e T v)⁺ else 0) p Measure.count

/-- The residual vanishes, at any `p ≠ 0`, iff the flow-matching constraint holds exactly. -/
theorem graphResidual_eq_zero_iff {p : ℝ≥0∞} (hp : p ≠ 0) (e : V → V → ℝ) (T : V → ℝ) :
    graphResidual G p e T = 0 ↔ ∀ v ∈ G.internal, fmDefectE G e T v = 0 := by
  simp only [graphResidual, add_eq_zero]
  rw [eLpNorm_eq_zero_iff (measurable_of_finite _).aestronglyMeasurable hp,
    eLpNorm_eq_zero_iff (measurable_of_finite _).aestronglyMeasurable hp,
    Filter.EventuallyEq, Filter.EventuallyEq, Measure.ae_count_iff, Measure.ae_count_iff]
  constructor
  · rintro ⟨h1, h2⟩ v hv
    have e1 := h1 v
    have e2 := h2 v
    simp only [hv, if_true, Pi.zero_apply] at e1 e2
    rw [← posPart_sub_negPart (fmDefectE G e T v), e1, e2, sub_zero]
  · intro h
    refine ⟨fun v => ?_, fun v => ?_⟩ <;> by_cases hv : v ∈ G.internal <;>
      simp only [hv, h v, if_true, if_false, negPart_zero, posPart_zero, Pi.zero_apply]

omit [MeasurableSingletonClass V] in
/-- A uniform bound on the defect bounds the residual, at every `p`. -/
theorem graphResidual_le {p : ℝ≥0∞} {e : V → V → ℝ} {T : V → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v ∈ G.internal, |fmDefectE G e T v| ≤ C) :
    graphResidual G p e T
      ≤ 2 * ((Measure.count (Set.univ : Set V)) ^ p.toReal⁻¹ * ENNReal.ofReal C) := by
  have hb1 : ∀ᵐ v ∂(Measure.count : Measure V),
      ‖(if v ∈ G.internal then (fmDefectE G e T v)⁻ else 0)‖ ≤ C := by
    refine Filter.Eventually.of_forall fun v => ?_
    by_cases hv : v ∈ G.internal
    · simp only [hv, if_true, Real.norm_eq_abs, abs_of_nonneg (negPart_nonneg _)]
      have h := posPart_add_negPart (fmDefectE G e T v)
      have := posPart_nonneg (fmDefectE G e T v)
      have := hC v hv
      linarith
    · simp only [hv, if_false, norm_zero]; exact hC0
  have hb2 : ∀ᵐ v ∂(Measure.count : Measure V),
      ‖(if v ∈ G.internal then (fmDefectE G e T v)⁺ else 0)‖ ≤ C := by
    refine Filter.Eventually.of_forall fun v => ?_
    by_cases hv : v ∈ G.internal
    · simp only [hv, if_true, Real.norm_eq_abs, abs_of_nonneg (posPart_nonneg _)]
      have h := posPart_add_negPart (fmDefectE G e T v)
      have := negPart_nonneg (fmDefectE G e T v)
      have := hC v hv
      linarith
    · simp only [hv, if_false, norm_zero]; exact hC0
  rw [graphResidual, two_mul]
  exact add_le_add (eLpNorm_le_of_ae_bound hb1) (eLpNorm_le_of_ae_bound hb2)

omit [MeasurableSingletonClass V] in
/-- **`rem:partial_support`, claim (b), in `L^p`**: the universality infimum over the union of
the frozen-backward families of `G` vanishes, at every `p`. -/
theorem iInf_graphResidual_eq_zero (hpc : G.PathConnected) {R : V → ℝ} (hR : IsTarget G R)
    (hZ : 0 < ∑ y, R y) (p : ℝ≥0∞) :
    ⨅ θ ∈ FrozenUnion G, graphResidual G p (memberFlow θ) R = 0 := by
  refine (GFNBounds.Core.Family.iInf_eq_zero_iff _ _).2 fun ε hε => ?_
  set K : ℝ≥0∞ := (Measure.count (Set.univ : Set V)) ^ p.toReal⁻¹ with hKdef
  have hKtop : K ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (measure_ne_top _ _)).ne
  set k := K.toReal with hk
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  set δ := ε / (2 * (k + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨θ, hθ, hclose⟩ := exists_member_close hpc hR hZ hδ0
  refine ⟨θ, hθ, lt_of_le_of_lt (graphResidual_le hδ0.le hclose) ?_⟩
  rw [← hKdef, ← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by rw [ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_lt_ofReal_iff hε, ← hk]
  have hlt : 2 * (k * δ) = ε * (k / (k + 1)) := by
    rw [hδ]; field_simp
  rw [hlt]
  have : k / (k + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  nlinarith

/-- **`rem:partial_support`, claim (b), in `L^p`**: the infimum is not attained, at any `p ≠ 0`,
for `R` non-zero at an internal state and vanishing at an internal terminating state. -/
theorem graphResidual_ne_zero (hpc : G.PathConnected) {R : V → ℝ}
    (hne : ∃ x ∈ G.internal, R x ≠ 0) (hvan : ∃ y ∈ G.internal, G.Edge y G.snk ∧ R y = 0)
    {p : ℝ≥0∞} (hp : p ≠ 0) {θ : (V → V → ℝ) × (V → ℝ)} (hθ : θ ∈ FrozenUnion G) :
    graphResidual G p (memberFlow θ) R ≠ 0 := by
  rw [ne_eq, graphResidual_eq_zero_iff hp]
  intro h
  obtain ⟨v, hv, hD⟩ := not_attained hpc hne hvan hθ
  exact hD (h v hv)

/-- `graphResidual_ne_zero` with unrestricted witnesses, under `¬ (s₀ → s_f)`: a corollary. -/
theorem graphResidual_ne_zero_of_not_edge_src_snk (hpc : G.PathConnected) {R : V → ℝ}
    (hR : IsTarget G R) (hsrc : ¬ G.Edge G.src G.snk) (hne : ∃ x, R x ≠ 0)
    (hvan : ∃ y, G.Edge y G.snk ∧ R y = 0) {p : ℝ≥0∞} (hp : p ≠ 0)
    {θ : (V → V → ℝ) × (V → ℝ)} (hθ : θ ∈ FrozenUnion G) :
    graphResidual G p (memberFlow θ) R ≠ 0 := by
  rw [ne_eq, graphResidual_eq_zero_iff hp]
  intro h
  obtain ⟨v, hv, hD⟩ := not_attained_of_not_edge_src_snk hpc hR hsrc hne hvan hθ
  exact hD (h v hv)

end Norms

/-! ## Inhabitation: a four-state instance -/

section Check

open scoped ENNReal

/-- The diamond `s₀ = 0 → 1, 2 → 3 = s_f`. -/
def diamond : MarkedGraph (Fin 4) where
  Edge x y := (x = 0 ∧ (y = 1 ∨ y = 2)) ∨ ((x = 1 ∨ x = 2) ∧ y = 3)
  src := 0
  snk := 3
  src_ne_snk := by decide
  no_edge_into_src x h := by
    rcases h with ⟨-, h | h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  no_edge_out_of_snk y h := by
    rcases h with ⟨h, -⟩ | ⟨h | h, -⟩ <;> exact absurd h (by decide)

/-- The target `δ₁`, which vanishes on the terminating state `2`. -/
noncomputable def diamondTarget : Fin 4 → ℝ := fun x => if x = 1 then 1 else 0

/-- **The hypotheses of claims (a) and (b) are inhabited**, on the diamond with target `δ₁`:
path-connected, a target of positive mass on the terminating states, vanishing on the terminating
state `2`, and no edge `s₀ → s_f`. -/
theorem diamond_check :
    diamond.PathConnected ∧ IsTarget diamond diamondTarget ∧ ¬ diamond.Edge diamond.src diamond.snk
      ∧ (∃ x, diamondTarget x ≠ 0) ∧ (∃ y, diamond.Edge y diamond.snk ∧ diamondTarget y = 0)
      ∧ 0 < ∑ y, diamondTarget y := by
  have e01 : diamond.Edge 0 1 := Or.inl ⟨rfl, Or.inl rfl⟩
  have e02 : diamond.Edge 0 2 := Or.inl ⟨rfl, Or.inr rfl⟩
  have e13 : diamond.Edge 1 3 := Or.inr ⟨Or.inl rfl, rfl⟩
  have e23 : diamond.Edge 2 3 := Or.inr ⟨Or.inr rfl, rfl⟩
  have r03 : diamond.Reach 0 3 :=
    Relation.ReflTransGen.head e01 (Relation.ReflTransGen.single e13)
  refine ⟨fun s => ?_, ⟨fun x => ?_, fun x hx => ?_⟩, fun h => ?_,
    ⟨1, by simp only [diamondTarget, if_true]; norm_num⟩,
    ⟨2, e23, if_neg (by decide)⟩, ?_⟩
  · fin_cases s
    · exact ⟨Relation.ReflTransGen.refl, r03⟩
    · exact ⟨Relation.ReflTransGen.single e01, Relation.ReflTransGen.single e13⟩
    · exact ⟨Relation.ReflTransGen.single e02, Relation.ReflTransGen.single e23⟩
    · exact ⟨r03, Relation.ReflTransGen.refl⟩
  · simp only [diamondTarget]; split_ifs <;> norm_num
  · have h1 : x = 1 := by
      by_contra hc; exact hx (by simp only [diamondTarget, hc, if_false])
    subst h1; exact e13
  · rcases h with ⟨-, h | h⟩ | ⟨h | h, -⟩ <;> exact absurd h (by decide)
  · rw [Fin.sum_univ_four]
    unfold diamondTarget
    rw [if_neg (by decide), if_pos rfl, if_neg (by decide), if_neg (by decide)]
    norm_num

/-- On the diamond, claim (b) in `L^p` holds non-vacuously: the infimum is `0` and every element of
the union has a non-zero residual. -/
theorem diamond_partial_support (p : ℝ≥0∞) (hp : p ≠ 0) :
    (⨅ θ ∈ FrozenUnion diamond, graphResidual diamond p (memberFlow θ) diamondTarget = 0) ∧
      ∀ θ ∈ FrozenUnion diamond, graphResidual diamond p (memberFlow θ) diamondTarget ≠ 0 := by
  obtain ⟨hpc, hR, -, -, -, hZ⟩ := diamond_check
  have h1 : (1 : Fin 4) ∈ diamond.internal :=
    MarkedGraph.mem_internal.2 ⟨show (1 : Fin 4) ≠ 0 by decide, show (1 : Fin 4) ≠ 3 by decide⟩
  have h2 : (2 : Fin 4) ∈ diamond.internal :=
    MarkedGraph.mem_internal.2 ⟨show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 3 by decide⟩
  exact ⟨iInf_graphResidual_eq_zero hpc hR hZ p,
    fun θ hθ => graphResidual_ne_zero hpc
      ⟨1, h1, by simp only [diamondTarget, if_true]; norm_num⟩
      ⟨2, h2, Or.inr ⟨Or.inr rfl, rfl⟩, if_neg (by decide)⟩ hp hθ⟩

end Check

/-! ## The reading of "terminating state" matters -/

section Triangle

open scoped ENNReal

/-- The triangle `s₀ = 0 → 1 → 2 = s_f` with the extra edge `s₀ → s_f`. -/
def triangle : MarkedGraph (Fin 3) where
  Edge x y := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 0 ∧ y = 2)
  src := 0
  snk := 2
  src_ne_snk := by decide
  no_edge_into_src x h := by
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  no_edge_out_of_snk y h := by
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

/-- The target `δ₁`: it vanishes at `s₀`, which has an edge to `s_f` but is not internal. -/
noncomputable def triangleTarget : Fin 3 → ℝ := fun x => if x = 1 then 1 else 0

/-- **The reading of "terminating state" matters — not a refutation of `rem:partial_support`.**
On the triangle, *if* `s₀` is counted as a terminating state (it has an edge to `s_f`), `δ₁`
"vanishes on a terminating state", and yet an element of the union of the frozen-backward families
is exactly matched to it on `𝒮 = {1}`: its residual is `0` at every `p`, the mass sent along
`s₀ → s_f` being invisible to `equ:FM_const`, which lives on `𝒮`. In the paper terminating states
are internal; the only one here is `1`, where `δ₁ ≠ 0`, so the remark's hypothesis is not met and
`not_attained` does not apply. -/
theorem triangle_attained :
    triangle.PathConnected ∧ IsTarget triangle triangleTarget ∧
      triangle.Edge triangle.src triangle.snk ∧ (∃ x, triangleTarget x ≠ 0) ∧
      (∃ y, triangle.Edge y triangle.snk ∧ triangleTarget y = 0) ∧
      ∃ θ ∈ FrozenUnion triangle,
        ∀ p : ℝ≥0∞, graphResidual triangle p (memberFlow θ) triangleTarget = 0 := by
  have e01 : triangle.Edge 0 1 := Or.inl ⟨rfl, rfl⟩
  have e12 : triangle.Edge 1 2 := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have e02 : triangle.Edge 0 2 := Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hpc : triangle.PathConnected := by
    intro s
    fin_cases s
    · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.single e02⟩
    · exact ⟨Relation.ReflTransGen.single e01, Relation.ReflTransGen.single e12⟩
    · exact ⟨Relation.ReflTransGen.single e02, Relation.ReflTransGen.refl⟩
  have hR : IsTarget triangle triangleTarget := by
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · simp only [triangleTarget]; split_ifs <;> norm_num
    · have h1 : x = 1 := by
        by_contra hc; exact hx (by simp only [triangleTarget, hc, if_false])
      subst h1; exact e12
  refine ⟨hpc, hR, e02, ⟨1, by simp only [triangleTarget, if_true]; norm_num⟩,
    ⟨0, e02, if_neg (by decide)⟩, ?_⟩
  obtain ⟨B, hB⟩ := exists_positive_policy hpc
  obtain ⟨lam, hlam⟩ := B.exists_invProb
  have hlpos : ∀ x, 0 < lam x := fun x => hlam.pos hpc hB x
  have hb : 0 < B.pb 2 1 := hB e12
  set c := 1 / (lam 2 * B.pb 2 1) with hc
  have hcpos : 0 < c := by rw [hc]; exact div_pos one_pos (mul_pos (hlpos 2) hb)
  let θ : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → ℝ) := (B.reversal lam, fun x => c * lam x)
  have hmem : θ ∈ FrozenUnion triangle :=
    ⟨B, hB, fun u => B.sum_reversal hlam (hlpos u).ne',
      fun u v => B.reversal_nonneg (fun x => (hlpos x).le) u v,
      fun x => mul_nonneg hcpos.le (hlpos x).le, B.frozenBalance_reversal hlpos c⟩
  refine ⟨θ, hmem, fun p => ?_⟩
  by_cases hp : p = 0
  · subst hp
    rw [graphResidual, MeasureTheory.eLpNorm_exponent_zero, MeasureTheory.eLpNorm_exponent_zero,
      add_zero]
  · rw [graphResidual_eq_zero_iff hp]
    intro v hv
    obtain ⟨hv0, hv2⟩ := MarkedGraph.mem_internal.1 hv
    have hv1 : v = 1 := by
      fin_cases v
      · exact absurd rfl hv0
      · rfl
      · exact absurd rfl hv2
    subst hv1
    rw [fmDefectE_member hmem _ hv]
    have h := B.frozenBalance_reversal hlpos c 1 2
    have hphat : B.phat 2 1 = B.pb 2 1 := B.phat_of_ne_src (by decide)
    simp only [memberFlow, θ, triangleTarget, if_true]
    change c * lam 1 * B.reversal lam 1 2 - 1 = 0
    have hl2 := (hlpos 2).ne'
    rw [h, hphat, hc]
    field_simp
    norm_num

end Triangle

end GFNBounds.Graph.PartialSupport
