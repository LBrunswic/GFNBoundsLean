import GFNBounds.Graph.Sampling
import GFNBounds.Graph.CycleRemarks
import GFNBounds.Graph.UniversalityClosing
import GFNBounds.Silva.Remarks

/-!
# The sampler, wired into the rows that cite `theo:sampling_theorem`

**`lem:cycle_counterexample`** (`proofs.tex`), item *(1)*'s sampler clause and its total variation.

**`theo:no_bound_divergence`** (`cv_divergence.tex`, proof in `proofs.tex`), the sampler step and the
upper half `TV ≤ 1` of `= 1`.

**`rem:silva_model_constant`** and **`rem:path_space`** (`silva_comparison.tex`), their cycle
sentence read on the sampler.

**`theo:universality_graphs`** (`proofs.tex`), item *(3)*'s sampler clause `s_τ ∼ R/Z` and the
closing paragraph's "samples `R` exactly".

(Line citations drift, kb `0036`; the labels are the anchors.)

Each of these rows cites `theo:sampling_theorem` for one step — "its sampler satisfies
`s_τ ∼ …`" — and until now measured total variation against the **normalized terminal flow**
`CycleDivergence.termLaw` or stopped at the flow-matching identity, recording in its SCOPE that
the step to the sampler was cited, not certified. `GFNBounds.Graph.Sampling` certifies the
finite-state sampling theorem on a marked graph (`sampler_law`, `sampler_termLaw`, `sampler_Fk`);
this file takes the step in each row.

## What "`s_τ ∼ μ`" is here

`IsSamplerLaw G F μ` — the sampler of the generative flow of the edgeflow `F`
(`Graph.Sampling.graphFlow`: `F_init = F(s₀ → ·)`, `F_term = F(· → s_f)`, `F⋆_out` and `P⋆` the
internal outflow and its normalization) has `P(τ ≤ n, s_τ = x) → μ(x)` at every internal state,
and `μ` vanishes off `𝒮`, where the sampler never stands. The limit is `P(τ < ∞, s_τ = x)`, so
with `Terminates G F` (`P(τ > n) → 0`) it is the law of `s_τ`, and limits being unique it is
determined by `F` (`IsSamplerLaw.unique`). This is `GFNBounds.Core.Sampling`'s reading of
`s_τ ∼ F_term`, unchanged. `TV(s_τ ‖ κ)` is then `tvFin μ κ` for the `μ` with
`IsSamplerLaw G F μ`: every statement below quantifies over such `μ`, so it is a statement about
the sampler and not about a chosen normalization of the terminal flow.

## What is proved

| | |
|---|---|
| `IsSamplerLaw`, `Terminates`, `IsSamplerLaw.unique`, `samplerLaw` | `s_τ ∼ μ` and termination, for the sampler of an edgeflow |
| **`sampler_general`** | any non-negative edge-carried flow-matching edgeflow with `F_term(𝒮) > 0`: `𝔼(τ)` bound, termination, `s_τ ∼ F(·→s_f)/F(𝒮→s_f)` on `𝒮`, no hypothesis on `s₀ → s_f` |
| `samplerLaw_nonneg`, `sum_samplerLaw`, `isSamplerLaw_prob` | the law of `s_τ` is a probability on `𝒱`, carried by `𝒮` |
| `isSamplerLaw_termLaw` | under `F(s₀ → s_f) = 0`, `s_τ ∼ termLaw G F` |
| `tvFin_le_one`, **`samplerTV_le_one`** | `TV ≤ 1` between probabilities; so `TV(s_τ ‖ κ) ≤ 1` on **every** marked graph |
| `isSamplerLaw_subprob`, **`samplerTV_le_one_general`** | for any non-negative edgeflow with `F_init(𝒮) > 0`, flow-matching or not, the law of `s_τ` is a sub-probability and `TV(s_τ ‖ κ) ≤ 1` |
| `cyc_no_edge_src_snk`, **`cycle_sampler`** | `𝒞_N` has no edge `s₀ → s_f`; every admissible flow on it samples its `termLaw` |
| **`Fk_sampler`**, `Fk_sampler_tv` | `s_τ(F_k) ∼ δ_{x₂}`, `F_k` terminates, `TV(s_τ(F_k) ‖ κ) = 1 − κ(x₂)` |
| **`cycle_counterexample_full`** | `lem:cycle_counterexample`, items *(1)*–*(2)*, the sampler clause included |
| **`no_bound_divergence_sampler`** | `theo:no_bound_divergence` at one flow, `TV(s_τ ‖ target)` on the sampler |
| `targetC_eq_extT`, `tvSet`, **`sSup_tvSet`**, **`no_bound_divergence_minimax`** | `inf_ν sup_{(𝒞_N, κ)} sup_{𝓛(F) ≤ ε} TV(s_τ ‖ κ) = 1`, as a real supremum and infimum; `samplerTV_le_one` bounds every other graph |
| **`cycle_flows_target_sampler`**, **`cycle_no_model_free_bound_sampler`**, **`cycle_no_bound_along_Fk_sampler`**, **`cycle_no_bound_punctured_sampler`** | the cycle sentence of `rem:path_space` and `rem:silva_model_constant`, on `s_τ` |
| `cutFlow`, `cutFlow_nonneg`, `cutFlow_supp`, `cutFlow_cons`, `graphFlow_cutFlow` | item *(3)*'s edge flow with the wrap edge cut is an admissible edgeflow on `G`, with the same sampler |
| `graphFlow_edgeFlow_finit`, `_fterm`, `_fout`, `_P` | that sampler **is** the sampler of item *(3)*'s generative flow `(F_init, F_term, f⋆_out, π⋆_→)` |
| `sum_internal_termFlow`, `pb_snk_src_lt_one` | `F_term(𝒮) = cλ(s₀)(1 − π_←(s_f → s₀))`, positive once `𝒮 ≠ ∅` |
| **`edgeFlow_sampler`** | the sampler of item *(3)*'s flow at any `c ≥ 0` with `F_term(𝒮) > 0` |
| **`universality_graphs_sampler`** | item *(3)*: the sampler terminates with `s_τ ∼ F_term|_𝒮/F_term(𝒮) = π_←(s_f → ·)/(1 − π_←(s_f → s₀))` on `𝒮`, with or without an edge `s₀ → s_f` — `s_τ ∼ R/Z` in `app:notation`'s normalized sense |
| **`universality_graphs_sampler_iff`** | item *(3)*'s clause read literally, *the law of `s_τ` is `R/Z`*, holds **iff** `G` has no edge `s₀ → s_f` |
| **`universality_graphs_closing_sampler`** | the closing paragraph: the balanced flow of the family frozen at `R` samples `R` exactly, `s_τ ∼ R/Z`, with no hypothesis on `s₀ → s_f` |
| `sampler_check_triangle` | inhabitation of the edge case (kb `0025`): on the triangle `0 → 1 → 2`, `0 → 2`, item *(3)*'s sampler emits `δ₁` while `R/Z = ½δ₀ + ½δ₁` |
| `closing_sampler_check_triangle` | inhabitation of the closing theorem in the edge case: the balanced flow of the family frozen at `δ₁` samples `δ₁` |
| `cycle_counterexample_full_check` | inhabitation at `N = 2`, uniform target: `s_τ(F_k) ∼ δ_{x₂}` at TV `½` |
| `sum_internal_snk`, `extT_nonneg`, `sum_extT`, `outflowStar_eq_sum_internal`, `reach_src_eq` | bookkeeping |

## SCOPE (disclosed)

* **Everything `GFNBounds.Graph.Sampling` and `GFNBounds.Core.Sampling` disclose applies**: the
  sampler is modelled by its time-`n` marginals; "`s_τ ∼ μ`" is delivered as a limit together with
  termination. The graphs are finite in the paper too, so the finite-state narrowing of
  `theo:sampling_theorem` does not narrow any row here.
* **`theo:no_bound_divergence`: the minimax identity is stated on `𝒞_N`.** `sSup_tvSet` is the
  supremum over probability targets `κ` on `𝒞_N`'s internal states and flows of loss `≤ ε` of
  `TV(s_τ ‖ κ)`, the flows being the non-negative edge-carried edgeflows with `F_init(𝒮) > 0` —
  the ones whose sampler can draw `s₁` — **flow-matching or not**, as the paper's
  `sup_{F : 𝓛(F) ≤ ε}` does not ask it; a flow contributes the `TV` of every `μ` with
  `IsSamplerLaw` (the limits exist, `P(τ ≤ n, s_τ = x)` being non-decreasing in `n`, but that is
  not needed and not proved: a flow without a limit law contributes nothing, and the lower bound
  is attained along the flow-matching `F_k`, whose law is certified). `no_bound_divergence_minimax`
  takes the infimum over every real weight `ν`. The paper's supremum over all graphs with
  `#𝒢 = N` is bounded below by the value at `𝒞_N` (`card_internal`) and above by `1` on every
  marked graph (`samplerTV_le_one_general`); a type of all marked graphs of size `N` is not
  formed, so the supremum over graphs is not itself a Lean term. The infimum over `ν` ranges over all real weights, a superset of the training
  distributions; the value is `1` for each `ν`, so any non-empty sub-range gives `1` too.
* **`theo:universality_graphs` item *(3)*, with an edge `s₀ → s_f`: two readings of
  "`s_τ ∼ R/Z`", `R = Zπ_←(s_f → ·)`.** Read as *the law of `s_τ` is `R/Z`*, with `R` the
  printed function on `𝒱`, it holds **iff** there is no such edge
  (`universality_graphs_sampler_iff`): with the edge `R/Z` charges `s₀`, which the sampler of `Graph.Sampling` —
  started in `𝒮`, `F_init = F(s₀ → ·)` on `𝒮` — never emits; a sampler that let the trajectory
  `s₀ → s_f` emit `s₀`, which counting `s₀` a terminating state would suggest, is a different
  model and is not formalized. Read through
  `app:notation`'s convention (`x ∼ μ` means the law of `x` is `μ/μ(𝒮)`) with `R` restricted to
  `𝒮`, it holds **with or without the edge** (`universality_graphs_sampler`, second clause): the
  sampler emits `R|_𝒮/R(𝒮) = π_←(s_f → ·)/(1 − π_←(s_f → s₀))` on `𝒮`. The two differ exactly by
  the mass `Zπ_←(s_f → s₀)` that item *(3)*'s `F_term` puts on `s₀` (finding 2 of
  `UniversalityClosing.lean`, `item_three_masses_on_internal`). Which reading the paper
  means, and whether the edge is excluded, is the author's question recorded in
  `GFNBounds/Graph/UniversalityClosing.lean` (findings 2 and 4); this file states what holds
  under each and resolves neither. `universality_graphs_sampler` asks `𝒮 ≠ ∅` (`hne`) in
  every case; without an edge `s₀ → s_f` path-connectedness already forces it, so it narrows only
  the edge case, where `pb_snk_src_lt_one` needs it for `F_term(𝒮) > 0`.
* **The closing paragraph's "samples `R` exactly"** is `s_τ ∼ R/Z` for the balanced member
  (`universality_graphs_closing_sampler`), read through `app:notation`'s "`x ∼ μ` for the law of
  `x` is `μ/μ(𝒮)`" — `R` has mass `Z` on `𝒮`. It holds **with no hypothesis on `s₀ → s_f`**,
  because the frozen sink row `R/Z` vanishes at `s₀` (a target lives on `𝒮`), so the balanced
  flow carries nothing on that edge. The internal reading of "terminating state" is
  `IsFullTarget`'s, as in `UniversalityClosing.lean`.
* **The sampler is the paper's.** The sampler is built from the edge flow of item *(3)* with the
  wrap edge cut (`cutFlow`); `graphFlow_cutFlow` shows the cut changes nothing the sampler reads,
  and `graphFlow_edgeFlow_*` identify its `F_init`, `F_term`, `F⋆_out` and — where `F⋆_out ≠ 0`,
  the only states the sampler leaves — `P⋆` with `Graph.Universality`'s `initFlow`, `termFlow`,
  `outflowStar` and `fwdStar`.
* **Not formalized here: `sup_{p_F} M' = +∞` over Markov forward policies** (`rem:path_space`).
  It needs the trajectory law of a Markov forward policy on the infinite set of walks of `𝒞_N`,
  and a policy that cannot tell visits of `x` apart gives each winding walk mass at most of order
  `1/k` after `k` windings; the ratio `p_F/p_B` is unbounded only through `liminf_k k·p_B(τ_k) = 0`
  for a summable `p_B`. That is a separate construction, not a sampler identification; it stays
  open, certified over trajectory laws only (`Silva.Remarks.exists_ratio_gt_walksInto`).
* **No `sorry`.**

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph.SamplerWiring

open Finset Filter Topology GFNBounds.Core.Sampling GFNBounds.Graph.Sampling
  GFNBounds.Graph.CycleDivergence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### `s_τ ∼ μ`, for the sampler of an edgeflow -/

/-- **`s_τ ∼ μ`** for the sampler of the generative flow of the edgeflow `F`
(`Graph.Sampling.graphFlow`): `P(τ ≤ n, s_τ = x) → μ(x)` at every internal state, and `μ`
vanishes off `𝒮 = 𝒱 ∖ {s₀, s_f}`, where the sampler never stands. -/
def IsSamplerLaw (G : MarkedGraph V) (F : V → V → ℝ) (μ : V → ℝ) : Prop :=
  (∀ x : G.internal,
    Tendsto (fun n => (graphFlow G F).law n (x, true)) atTop (𝓝 (μ x))) ∧
  ∀ x, x ∉ G.internal → μ x = 0

/-- **The sampler terminates almost surely**: `P(τ > n) → 0`. -/
def Terminates (G : MarkedGraph V) (F : V → V → ℝ) : Prop :=
  Tendsto (graphFlow G F).tailProb atTop (𝓝 0)

variable {G : MarkedGraph V} {F : V → V → ℝ}

/-- The law of `s_τ` is determined by the flow. -/
theorem IsSamplerLaw.unique {μ μ' : V → ℝ} (h : IsSamplerLaw G F μ) (h' : IsSamplerLaw G F μ') :
    μ = μ' := by
  funext x
  by_cases hx : x ∈ G.internal
  · exact tendsto_nhds_unique (h.1 ⟨x, hx⟩) (h'.1 ⟨x, hx⟩)
  · rw [h.2 x hx, h'.2 x hx]

/-- The normalized terminal flow **on `𝒮`**: `F(x → s_f)/∑_{y ∈ 𝒮} F(y → s_f)` at internal `x`,
`0` at the marks. -/
noncomputable def samplerLaw (G : MarkedGraph V) (F : V → V → ℝ) : V → ℝ :=
  fun x => if x ∈ G.internal then F x G.snk / ∑ y ∈ G.internal, F y G.snk else 0

/-- **`theo:sampling_theorem` for an edgeflow, with no hypothesis on `s₀ → s_f`**: the sampler
obeys the `𝔼(τ)` bound, terminates, and `s_τ ∼ F(· → s_f)/F(𝒮 → s_f)` on `𝒮`. -/
theorem sampler_general (hnn : ∀ u v, 0 ≤ F u v) (hsupp : ∀ u v, F u v ≠ 0 → G.Edge u v)
    (hcons : ∀ x ∈ G.internal, edgeInflow F x = edgeOutflow F x)
    (hpos : 0 < ∑ y ∈ G.internal, F y G.snk) :
    Summable (graphFlow G F).tailProb ∧
    (graphFlow G F).expectedTau
      ≤ (∑ x, (graphFlow G F).fout x) / (∑ x, (graphFlow G F).finit x) + 1 ∧
    Terminates G F ∧ IsSamplerLaw G F (samplerLaw G F) := by
  have hpos' : 0 < ∑ y : G.internal, F y G.snk := by
    rwa [Finset.sum_coe_sort G.internal (fun y => F y G.snk)]
  have hterm : (graphFlow G F).fterm ≠ 0 := by
    intro h
    have : ∑ y : G.internal, F y G.snk = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      simpa only [graphFlow, Pi.zero_apply] using congrFun h y
    linarith
  obtain ⟨-, hs, hE, ht, -, -⟩ :=
    FlowData.sampling_theorem (isGenFlow hnn) hterm (flowMatching hnn hsupp hcons)
  refine ⟨hs, hE, ht, fun x => ?_, fun x hx => by simp only [samplerLaw, if_neg hx]⟩
  have h := sampler_law hnn hsupp hcons hpos' x
  rw [Finset.sum_coe_sort G.internal (fun y => F y G.snk)] at h
  simpa only [samplerLaw, if_pos x.2] using h

theorem samplerLaw_nonneg (hnn : ∀ u v, 0 ≤ F u v) (x : V) : 0 ≤ samplerLaw G F x := by
  unfold samplerLaw
  split_ifs
  · exact div_nonneg (hnn _ _) (Finset.sum_nonneg fun y _ => hnn _ _)
  · exact le_rfl

theorem sum_samplerLaw (hpos : 0 < ∑ y ∈ G.internal, F y G.snk) : ∑ x, samplerLaw G F x = 1 := by
  unfold samplerLaw
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div,
    div_self hpos.ne']

/-- **The law of `s_τ` is a probability on `𝒱`, carried by `𝒮`.** -/
theorem isSamplerLaw_prob (hnn : ∀ u v, 0 ≤ F u v) (hsupp : ∀ u v, F u v ≠ 0 → G.Edge u v)
    (hcons : ∀ x ∈ G.internal, edgeInflow F x = edgeOutflow F x)
    (hpos : 0 < ∑ y ∈ G.internal, F y G.snk) {μ : V → ℝ} (hμ : IsSamplerLaw G F μ) :
    (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1 := by
  rw [hμ.unique (sampler_general hnn hsupp hcons hpos).2.2.2]
  exact ⟨samplerLaw_nonneg hnn, sum_samplerLaw hpos⟩

/-- With no flow on `s₀ → s_f`, the sampler emits `termLaw G F`, the normalized terminal flow the
rows citing `theo:sampling_theorem` measured against. -/
theorem isSamplerLaw_termLaw (hnn : ∀ u v, 0 ≤ F u v) (hsupp : ∀ u v, F u v ≠ 0 → G.Edge u v)
    (hcons : ∀ x ∈ G.internal, edgeInflow F x = edgeOutflow F x)
    (hss : F G.src G.snk = 0) (hpos : 0 < ∑ y, F y G.snk) :
    IsSamplerLaw G F (termLaw G F) := by
  refine ⟨(sampler_termLaw hnn hsupp hcons hss hpos).2.2.2, fun x hx => ?_⟩
  have hsnk : F G.snk G.snk = 0 := by
    by_contra hc; exact G.no_edge_out_of_snk _ (hsupp _ _ hc)
  have hx' : x = G.src ∨ x = G.snk := by
    by_contra hc
    push Not at hc
    exact hx (MarkedGraph.mem_internal.mpr hc)
  rcases hx' with rfl | rfl
  · simp only [termLaw, hss, zero_div]
  · simp only [termLaw, hsnk, zero_div]

omit [DecidableEq V] in
/-- `TV ≤ 1` between two probabilities. -/
theorem tvFin_le_one {p q : V → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) : tvFin p q ≤ 1 := by
  have h : ∑ x, |p x - q x| ≤ ∑ x, (p x + q x) :=
    Finset.sum_le_sum fun x _ => by
      rw [abs_le]; constructor <;> linarith [hp0 x, hq0 x]
  rw [Finset.sum_add_distrib, hp1, hq1] at h
  unfold tvFin
  linarith

/-- **`TV(s_τ ‖ κ) ≤ 1` on every marked graph**, for every probability target `κ` and every flow
with a sampler — the upper half of `theo:no_bound_divergence`'s `= 1`, which holds whatever the
graph, the loss and the training distribution. -/
theorem samplerTV_le_one (hnn : ∀ u v, 0 ≤ F u v) (hsupp : ∀ u v, F u v ≠ 0 → G.Edge u v)
    (hcons : ∀ x ∈ G.internal, edgeInflow F x = edgeOutflow F x)
    (hpos : 0 < ∑ y ∈ G.internal, F y G.snk) {κ : V → ℝ} (hκ0 : ∀ x, 0 ≤ κ x)
    (hκ1 : ∑ x, κ x = 1) {μ : V → ℝ} (hμ : IsSamplerLaw G F μ) : tvFin μ κ ≤ 1 := by
  obtain ⟨h0, h1⟩ := isSamplerLaw_prob hnn hsupp hcons hpos hμ
  exact tvFin_le_one h0 hκ0 h1 hκ1

/-- **For any non-negative edgeflow with a sampler, flow-matching or not**, the law of `s_τ` is a
sub-probability: `P(τ < ∞, s_τ = x) ≥ 0` and `P(τ < ∞) ≤ 1`. The sampler needs only
`F_init(𝒮) > 0`, to draw `s₁`. -/
theorem isSamplerLaw_subprob (hnn : ∀ u v, 0 ≤ F u v)
    (hZ : 0 < ∑ v ∈ G.internal, F G.src v) {μ : V → ℝ} (hμ : IsSamplerLaw G F μ) :
    (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x ≤ 1 := by
  have hgen := isGenFlow (G := G) hnn
  have hZ' : 0 < ∑ x, (graphFlow G F).finit x := by
    show 0 < ∑ x : G.internal, F G.src x
    rwa [Finset.sum_coe_sort G.internal (fun v => F G.src v)]
  refine ⟨fun x => ?_, ?_⟩
  · by_cases hx : x ∈ G.internal
    · exact ge_of_tendsto' (hμ.1 ⟨x, hx⟩) fun n => FlowData.law_nonneg hgen n _
    · rw [hμ.2 x hx]
  · have hsplit := sum_split G μ
    rw [hμ.2 G.src (fun h => (MarkedGraph.mem_internal.mp h).1 rfl),
      hμ.2 G.snk (fun h => (MarkedGraph.mem_internal.mp h).2 rfl), zero_add, zero_add] at hsplit
    rw [hsplit]
    refine le_of_tendsto' (tendsto_finsetSum Finset.univ fun x _ => hμ.1 x) fun n => ?_
    have h1 := FlowData.law_sum hgen hZ' n
    rw [Fintype.sum_prod_type] at h1
    rw [← h1]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Fintype.sum_bool]
    linarith [FlowData.law_nonneg hgen n (x, false)]

/-- **`TV(s_τ ‖ κ) ≤ 1` for every non-negative edgeflow with a sampler** on every marked graph,
flow-matching or not: the law of `s_τ` is a sub-probability. -/
theorem samplerTV_le_one_general (hnn : ∀ u v, 0 ≤ F u v)
    (hZ : 0 < ∑ v ∈ G.internal, F G.src v) {κ : V → ℝ} (hκ0 : ∀ x, 0 ≤ κ x)
    (hκ1 : ∑ x, κ x = 1) {μ : V → ℝ} (hμ : IsSamplerLaw G F μ) : tvFin μ κ ≤ 1 := by
  obtain ⟨h0, h1⟩ := isSamplerLaw_subprob hnn hZ hμ
  have h : ∑ x, |μ x - κ x| ≤ ∑ x, (μ x + κ x) :=
    Finset.sum_le_sum fun x _ => by
      rw [abs_le]; constructor <;> linarith [h0 x, hκ0 x]
  rw [Finset.sum_add_distrib, hκ1] at h
  unfold tvFin
  linarith

/-- The terminal mass on `𝒮` is the whole terminal mass when `s₀ → s_f` carries nothing. -/
theorem sum_internal_snk (hsupp : ∀ u v, F u v ≠ 0 → G.Edge u v) (hss : F G.src G.snk = 0) :
    ∑ y ∈ G.internal, F y G.snk = ∑ y, F y G.snk := by
  have hsnk : F G.snk G.snk = 0 := by
    by_contra hc; exact G.no_edge_out_of_snk _ (hsupp _ _ hc)
  rw [sum_split G (fun y => F y G.snk), hss, hsnk, zero_add, zero_add,
    Finset.sum_coe_sort G.internal (fun y => F y G.snk)]

/-! ### The cyclic counter-example `𝒞_N` -/

section Cycle

open GFNBounds.Graph.CycleRemarks

variable {M : ℕ}

/-- **`𝒞_N` has no edge `s₀ → s_f`**: its only edge out of `s₀` is `s₀ → x₁`. -/
theorem cyc_no_edge_src_snk : ¬ (cycGraph M).Edge (cycGraph M).src (cycGraph M).snk := by
  rintro (⟨-, h⟩ | ⟨i, h, -⟩ | ⟨i, h, -⟩)
  · exact snkC_ne_xC 0 h
  · exact srcC_ne_xC i h
  · exact srcC_ne_xC i h

theorem cyc_hss {F : cycV M → cycV M → ℝ} (hsupp : ∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v) :
    F (cycGraph M).src (cycGraph M).snk = 0 := by
  by_contra h
  exact cyc_no_edge_src_snk (hsupp _ _ h)

/-- **`theo:sampling_theorem` on `𝒞_N`**: every non-negative, edge-carried, flow-matching edgeflow
of positive terminal mass has a sampler that obeys the `𝔼(τ)` bound, terminates, and emits the
normalized terminal flow `termLaw`. -/
theorem cycle_sampler {F : cycV M → cycV M → ℝ} (hnn : ∀ u v, 0 ≤ F u v)
    (hsupp : ∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v)
    (hcons : ∀ x ∈ (cycGraph M).internal, edgeInflow F x = edgeOutflow F x)
    (hpos : 0 < ∑ y, F y (cycGraph M).snk) :
    Summable (graphFlow (cycGraph M) F).tailProb ∧
    (graphFlow (cycGraph M) F).expectedTau
      ≤ (∑ x, (graphFlow (cycGraph M) F).fout x) / (∑ x, (graphFlow (cycGraph M) F).finit x) + 1 ∧
    Terminates (cycGraph M) F ∧ IsSamplerLaw (cycGraph M) F (termLaw (cycGraph M) F) := by
  obtain ⟨hs, hE, ht, -⟩ := sampler_termLaw hnn hsupp hcons (cyc_hss hsupp) hpos
  exact ⟨hs, hE, ht, isSamplerLaw_termLaw hnn hsupp hcons (cyc_hss hsupp) hpos⟩

theorem Fk_termMass_pos (k : ℝ) : 0 < ∑ y, Fk M k y (cycGraph M).snk := by
  rw [cycGraph_snk, sum_termFlow_Fk]; exact one_pos

/-- **`s_τ(F_k) ∼ δ_{x₂}`**, and the sampler of `F_k` terminates, for every `k ≥ 0`. -/
theorem Fk_sampler {k : ℝ} (hk : 0 ≤ k) :
    Terminates (cycGraph M) (Fk M k) ∧
    IsSamplerLaw (cycGraph M) (Fk M k) (fun v => if v = xC M 1 then 1 else 0) := by
  obtain ⟨-, -, ht, hlaw⟩ :=
    cycle_sampler (Fk_nonneg hk) (fun _ _ h => Fk_supp h) (Fk_flowMatching k) (Fk_termMass_pos k)
  refine ⟨ht, ?_⟩
  have e : termLaw (cycGraph M) (Fk M k) = fun v => if v = xC M 1 then 1 else 0 :=
    funext (termLaw_Fk k)
  rwa [e] at hlaw

/-- **`TV(s_τ(F_k) ‖ κ) = 1 − κ(x₂)`** for every probability `κ` on `{x₁,…,x_N}`. -/
theorem Fk_sampler_tv {k : ℝ} (hk : 0 ≤ k) {t : Fin (M + 2) → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hsum : ∑ i, t i = 1) {μ : cycV M → ℝ} (hμ : IsSamplerLaw (cycGraph M) (Fk M k) μ) :
    tvFin μ (extT M t) = 1 - t 1 := by
  rw [hμ.unique (cycle_sampler (Fk_nonneg hk) (fun _ _ h => Fk_supp h) (Fk_flowMatching k)
    (Fk_termMass_pos k)).2.2.2]
  exact tvFin_termLaw_Fk_gen k ht hsum

/-- **`lem:cycle_counterexample`, in full**: items *(1)* and *(2)* for every `N ≥ 2`
(`N = M + 2`), every integer `k ≥ 0`, every probability target and every weight — the statement
of `CycleRemarks.cycle_counterexample` with item *(1)*'s sampler clause added: the sampler of
`F_k` terminates, `s_τ(F_k) ∼ δ_{x₂}`, and `TV(s_τ(F_k) ‖ κ) = 1 − κ(x₂)` is a statement about
`s_τ`. -/
theorem cycle_counterexample_full (M : ℕ) :
    (∀ k : ℕ,
      (∀ u v, 0 ≤ Fk M k u v) ∧ (∀ u v, Fk M k u v ≠ 0 → (cycGraph M).Edge u v)
      ∧ (∀ i, Fk M k (srcC M) (xC M i) + ∑ j, Fk M k (xC M j) (xC M i)
          = Fk M k (xC M i) (snkC M) + ∑ j, Fk M k (xC M i) (xC M j))
      ∧ (∀ i, Fk M k (srcC M) (xC M i) = if i = 0 then 1 else 0)
      ∧ (∀ i, Fk M k (xC M i) (snkC M) = if i = 1 then 1 else 0)
      ∧ Terminates (cycGraph M) (Fk M k)
      ∧ IsSamplerLaw (cycGraph M) (Fk M k) (fun v => if v = xC M 1 then 1 else 0)
      ∧ ∀ t : Fin (M + 2) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i = 1 →
          ∀ μ, IsSamplerLaw (cycGraph M) (Fk M k) μ → tvFin μ (extT M t) = 1 - t 1)
    ∧ ∀ t : Fin (M + 2) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i = 1 →
      ∀ (nu : cycV M → ℝ) (g : ℝ → ℝ), g 1 = 0 → ContinuousAt g 1 →
        (∀ k : ℕ, 1 ≤ k → ∀ i,
          0 < extT M t (xC M i) + ∑ v ∈ (cycGraph M).internal, Fk M k (xC M i) v
          ∧ 0 < fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M i)
          ∧ |fmRatio (cycGraph M) (extT M t) (Fk M k) (xC M i) - 1| ≤ 1 / k)
        ∧ Tendsto (fun k : ℕ => fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := cycle_counterexample M
  refine ⟨fun k => ?_, h2⟩
  obtain ⟨a, b, c, d, e, -, -⟩ := h1 k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨ht, hlaw⟩ := Fk_sampler (M := M) hk
  exact ⟨a, b, c, d, e, ht, hlaw, fun t h0 hs μ hμ => Fk_sampler_tv hk h0 hs hμ⟩

/-- **Inhabitation of `cycle_counterexample_full`** at `N = 2`, uniform target: the sampler of
every `F_k` emits `δ_{x₂}`, at total variation `½` from the target. -/
theorem cycle_counterexample_full_check (k : ℕ) :
    IsSamplerLaw (cycGraph 0) (Fk 0 k) (fun v => if v = xC 0 1 then 1 else 0)
      ∧ tvFin (fun v => if v = xC 0 1 then 1 else 0) (extT 0 fun _ => 1 / 2) = 1 / 2 := by
  have ht : ∀ i : Fin 2, (0 : ℝ) ≤ (fun _ => 1 / 2) i := fun _ => by norm_num
  have hsum : ∑ i : Fin 2, (fun _ => (1 : ℝ) / 2) i = 1 := by
    simp only [Fin.sum_univ_two]; norm_num
  obtain ⟨-, hlaw⟩ := Fk_sampler (M := 0) (Nat.cast_nonneg k)
  refine ⟨hlaw, ?_⟩
  rw [((cycle_counterexample_full 0).1 k).2.2.2.2.2.2.2 _ ht hsum _ hlaw]
  norm_num

end Cycle

/-! ### `theo:no_bound_divergence`, on the sampler -/

section NoBound

open GFNBounds.Graph.CycleRemarks

variable {M : ℕ}

/-- **`theo:no_bound_divergence` at one flow, on the sampler**: for every generator `g` continuous
at `1` with `g(1) = 0`, every weight `ν`, every `δ ∈ (0,1)` and every `ε > 0` there is an edgeflow
on `𝒞_N`, non-negative, edge-carried and exactly flow-matching, of FM loss `≤ ε`, whose sampler
terminates and satisfies `TV(s_τ ‖ target) = 1 − δ/(N−1)`. -/
theorem no_bound_divergence_sampler (M : ℕ) (g : ℝ → ℝ) (hg1 : g 1 = 0)
    (hgc : ContinuousAt g 1) (nu : cycV M → ℝ) {delta eps : ℝ} (hd0 : 0 < delta)
    (hd1 : delta < 1) (heps : 0 < eps) :
    ∃ F : cycV M → cycV M → ℝ,
      (∀ u v, 0 ≤ F u v) ∧
      (∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v) ∧
      (∀ x ∈ (cycGraph M).internal, edgeInflow F x = edgeOutflow F x) ∧
      fmLossTarget (cycGraph M) g nu (targetC M delta) F ≤ eps ∧
      0 < ∑ y, F y (cycGraph M).snk ∧
      Terminates (cycGraph M) F ∧
      IsSamplerLaw (cycGraph M) F (termLaw (cycGraph M) F) ∧
      ∀ μ, IsSamplerLaw (cycGraph M) F μ →
        tvFin μ (targetC M delta) = 1 - delta / ((M : ℝ) + 1) := by
  obtain ⟨k, hk0, hk⟩ := exists_Fk_loss_le g hg1 hgc nu delta heps
  obtain ⟨-, -, ht, hlaw⟩ := cycle_sampler (Fk_nonneg hk0) (fun _ _ h => Fk_supp h)
    (Fk_flowMatching k) (Fk_termMass_pos (M := M) k)
  refine ⟨Fk M k, Fk_nonneg hk0, fun _ _ h => Fk_supp h, Fk_flowMatching k, hk,
    Fk_termMass_pos k, ht, hlaw,
    fun μ hμ => ?_⟩
  rw [hμ.unique hlaw]
  exact tvFin_termLaw_Fk k hd0.le hd1.le

/-- `theo:no_bound_divergence`'s target is a probability on `{x₁,…,x_N}`, extended by `0`. -/
theorem targetC_eq_extT (delta : ℝ) :
    targetC M delta = extT M (fun i => if i = 0 then 1 - delta else delta / ((M : ℝ) + 1)) := by
  funext v
  rcases v with _ | _ | i <;> rfl

/-- **The set whose supremum `theo:no_bound_divergence` computes, on `𝒞_N`**: the values of
`TV(s_τ ‖ κ)` over probability targets `κ` on `{x₁,…,x_N}` and flows with a sampler — non-negative,
edge-carried, with `F_init(𝒮) > 0`; flow matching is **not** asked — whose FM loss against `κ` is
at most `ε`. -/
def tvSet (M : ℕ) (g : ℝ → ℝ) (nu : cycV M → ℝ) (eps : ℝ) : Set ℝ :=
  {r | ∃ t : Fin (M + 2) → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧
    ∃ F : cycV M → cycV M → ℝ, (∀ u v, 0 ≤ F u v) ∧
      (∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v) ∧
      0 < ∑ v ∈ (cycGraph M).internal, F (cycGraph M).src v ∧
      fmLossTarget (cycGraph M) g nu (extT M t) F ≤ eps ∧
      ∃ μ, IsSamplerLaw (cycGraph M) F μ ∧ r = tvFin μ (extT M t)}

theorem extT_nonneg {t : Fin (M + 2) → ℝ} (ht : ∀ i, 0 ≤ t i) (v : cycV M) : 0 ≤ extT M t v := by
  rcases v with _ | _ | i
  · exact le_rfl
  · exact le_rfl
  · exact ht i

theorem sum_extT (t : Fin (M + 2) → ℝ) : ∑ v, extT M t v = ∑ i, t i := by
  rw [sum_cycV, extT_srcC, extT_snkC, zero_add, zero_add]
  rfl

/-- **`theo:no_bound_divergence`, the supremum over targets and flows on `𝒞_N` is `1`**, for every
weight `ν` and every `ε > 0`: bounded by `1` (`samplerTV_le_one_general`), and exceeding every
`η < 1` along the flow-matching flows `F_k`. -/
theorem sSup_tvSet (M : ℕ) (g : ℝ → ℝ) (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (nu : cycV M → ℝ) {eps : ℝ} (heps : 0 < eps) : sSup (tvSet M g nu eps) = 1 := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hlow : ∀ w : ℝ, w < 1 → ∃ r ∈ tvSet M g nu eps, w < r := by
    intro w hw
    set delta : ℝ := min (1 / 2) ((1 - w) * ((M : ℝ) + 1) / 2) with hdef
    have hd0 : 0 < delta := lt_min (by norm_num) (by nlinarith)
    have hd1 : delta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    obtain ⟨k, hk0, hk⟩ := exists_Fk_loss_le g hg1 hgc nu delta heps
    obtain ⟨-, -, -, hlaw⟩ := cycle_sampler (Fk_nonneg hk0) (fun _ _ h => Fk_supp h)
      (Fk_flowMatching k) (Fk_termMass_pos (M := M) k)
    set t : Fin (M + 2) → ℝ := fun i => if i = 0 then 1 - delta else delta / ((M : ℝ) + 1)
    have ht0 : ∀ i, 0 ≤ t i := fun i => by
      simp only [t]; split_ifs
      · linarith
      · exact div_nonneg hd0.le hM.le
    have hts : ∑ i, t i = 1 := by
      have h := sum_targetC (M := M) delta
      rwa [targetC_eq_extT, sum_extT] at h
    have hinit : 0 < ∑ v ∈ (cycGraph M).internal, Fk M k (cycGraph M).src v := by
      rw [cycGraph_src, foutC_Fk_srcC]; exact one_pos
    refine ⟨tvFin (termLaw (cycGraph M) (Fk M k)) (extT M t),
      ⟨t, ht0, hts, Fk M k, Fk_nonneg hk0, fun _ _ h => Fk_supp h, hinit, ?_, _, hlaw, rfl⟩, ?_⟩
    · rwa [← targetC_eq_extT]
    · rw [← targetC_eq_extT, tvFin_termLaw_Fk k hd0.le hd1.le]
      have hle : delta ≤ (1 - w) * ((M : ℝ) + 1) / 2 := min_le_right _ _
      have : delta / ((M : ℝ) + 1) < 1 - w := by
        rw [div_lt_iff₀ hM]
        nlinarith
      linarith
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ hlow
  · obtain ⟨r, hr, -⟩ := hlow 0 one_pos
    exact ⟨r, hr⟩
  · rintro r ⟨t, ht0, hts, F, hnn, -, hZ, -, μ, hμ, rfl⟩
    exact samplerTV_le_one_general hnn hZ (extT_nonneg ht0) (by rw [sum_extT, hts]) hμ

/-- **`theo:no_bound_divergence`, the minimax identity on `𝒞_N`**:
`inf_ν sup_{κ} sup_{F : 𝓛(F) ≤ ε} TV(s_τ ‖ κ) = 1`, for every generator continuous at `1` with
`g(1) = 0` and every `ε > 0`. The infimum runs over every real weight `ν`. -/
theorem no_bound_divergence_minimax (M : ℕ) (g : ℝ → ℝ) (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    {eps : ℝ} (heps : 0 < eps) : ⨅ nu : cycV M → ℝ, sSup (tvSet M g nu eps) = 1 := by
  simp only [sSup_tvSet M g hg1 hgc _ heps, ciInf_const]

end NoBound

/-! ### `rem:path_space` and `rem:silva_model_constant`: the cycle sentence on the sampler -/

section Silva

open GFNBounds.Graph.CycleRemarks GFNBounds.Silva.Remarks

variable {M : ℕ}

/-- **`rem:path_space`, the flows of `lem:cycle_counterexample`, on the sampler**: for a
probability `κ ≠ δ_{x₂}` on `{x₁,…,x_N}`, the sampler of every `F_k` terminates with
`s_τ(F_k) ∼ δ_{x₂}`, at total variation `1 − κ(x₂) > 0` from `κ`, while the loss of `F_k` tends to
`0` for every weight (`Silva.Remarks.cycle_flows_target`). -/
theorem cycle_flows_target_sampler {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) :
    (∀ k : ℕ, Terminates (cycGraph M) (Fk M k) ∧
      IsSamplerLaw (cycGraph M) (Fk M k) (fun v => if v = xC M 1 then 1 else 0) ∧
      ∀ μ, IsSamplerLaw (cycGraph M) (Fk M k) μ → tvFin μ (extT M t) = 1 - t 1) ∧
    (∀ nu : cycV M → ℝ,
      Tendsto (fun k : ℕ => fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) atTop (𝓝 0)) ∧
    0 < 1 - t 1 := by
  obtain ⟨-, -, -, -, -, hloss, -, -, hgap⟩ := cycle_flows_target hg1 hgc ht0 hsum ht
  refine ⟨fun k => ?_, hloss, hgap⟩
  obtain ⟨hT, hL⟩ := Fk_sampler (M := M) (Nat.cast_nonneg k)
  exact ⟨hT, hL, fun μ hμ => Fk_sampler_tv (Nat.cast_nonneg k) ht0 hsum hμ⟩

/-- **`rem:path_space` / `rem:silva_model_constant`, "no model-free bound tending to `0` with the
loss", on the sampler**: over the non-negative, edge-carried, flow-matching flows on `𝒞_N` with
every denominator positive and positive terminal mass, no `Φ` with `Φ(L) → 0` as `L → 0⁺`
(through `L ≥ 0`) bounds `TV(s_τ ‖ κ) ≤ Φ(𝓛(F))`. -/
theorem cycle_no_model_free_bound_sampler {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (hg0 : ∀ r, 0 < r → 0 ≤ g r) {nu : cycV M → ℝ} (hnu : ∀ v, 0 ≤ nu v)
    {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) :
    ¬ ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ F : cycV M → cycV M → ℝ, (∀ u v, 0 ≤ F u v) →
        (∀ u v, F u v ≠ 0 → (cycGraph M).Edge u v) →
        (∀ x ∈ (cycGraph M).internal, edgeInflow F x = edgeOutflow F x) →
        (∀ x ∈ (cycGraph M).internal, 0 < extT M t x + ∑ v ∈ (cycGraph M).internal, F x v) →
        0 < ∑ y, F y (cycGraph M).snk →
        ∀ μ, IsSamplerLaw (cycGraph M) F μ →
          tvFin μ (extT M t) ≤ Φ (fmLossTarget (cycGraph M) g nu (extT M t) F) := by
  rintro ⟨Φ, hΦ, hb⟩
  exact cycle_no_model_free_bound hg1 hgc hg0 hnu ht0 hsum ht ⟨Φ, hΦ,
    fun F hnn hsupp hcons hden hpos => hb F hnn hsupp hcons hden hpos _
      (cycle_sampler hnn hsupp hcons hpos).2.2.2⟩

/-- **The same, along `(F_k)_{k≥1}`, on the sampler.** -/
theorem cycle_no_bound_along_Fk_sampler {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (hg0 : ∀ r, 0 < r → 0 ≤ g r) {nu : cycV M → ℝ} (hnu : ∀ v, 0 ≤ nu v)
    {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) :
    ¬ ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ μ, IsSamplerLaw (cycGraph M) (Fk M k) μ →
        tvFin μ (extT M t) ≤ Φ (fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) := by
  rintro ⟨Φ, hΦ, hb⟩
  exact cycle_no_bound_along_Fk hg1 hgc hg0 hnu ht0 hsum ht ⟨Φ, hΦ, fun k hk => hb k hk _
    (cycle_sampler (Fk_nonneg (Nat.cast_nonneg k)) (fun _ _ h => Fk_supp h) (Fk_flowMatching _)
      (Fk_termMass_pos _)).2.2.2⟩

/-- **The punctured reading, on the sampler** (`ν(x₂) > 0`, `g > 0` off `1`). -/
theorem cycle_no_bound_punctured_sampler {g : ℝ → ℝ} (hg1 : g 1 = 0) (hgc : ContinuousAt g 1)
    (hg0 : ∀ r, 0 < r → 0 ≤ g r) (hgpos : ∀ r, 0 < r → r ≠ 1 → 0 < g r)
    {nu : cycV M → ℝ} (hnu : ∀ v, 0 ≤ nu v) (hnu2 : 0 < nu (xC M 1))
    {t : Fin (M + 2) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = 1)
    (ht : t ≠ fun i => if i = 1 then 1 else 0) :
    ¬ ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[>] 0) (𝓝 0) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ μ, IsSamplerLaw (cycGraph M) (Fk M k) μ →
        tvFin μ (extT M t) ≤ Φ (fmLossTarget (cycGraph M) g nu (extT M t) (Fk M k)) := by
  rintro ⟨Φ, hΦ, hb⟩
  exact cycle_no_bound_punctured hg1 hgc hg0 hgpos hnu hnu2 ht0 hsum ht ⟨Φ, hΦ, fun k hk => hb k hk _
    (cycle_sampler (Fk_nonneg (Nat.cast_nonneg k)) (fun _ _ h => Fk_supp h) (Fk_flowMatching _)
      (Fk_termMass_pos _)).2.2.2⟩

end Silva

/-! ### `theo:universality_graphs`: item *(3)*'s sampler and the closing paragraph -/

section Universality

variable (B : BackwardPolicy G)

/-- **Item *(3)*'s edge flow with the wrap edge cut** (`proofs.tex`, "cut it, declaring its flow to
be an initial flow `Z` injected at `s₀` and a terminal flow `Z` collected at `s_f`"): `e(u → v)`
everywhere but on `s_f → s₀`. -/
noncomputable def cutFlow (lam : V → ℝ) (c : ℝ) : V → V → ℝ :=
  fun u v => if u = G.snk ∧ v = G.src then 0 else B.edgeFlow lam c u v

theorem cutFlow_nonneg {lam : V → ℝ} (hl : B.IsInvProb lam) {c : ℝ} (hc : 0 ≤ c) (u v : V) :
    0 ≤ cutFlow B lam c u v := by
  unfold cutFlow
  split_ifs
  · exact le_rfl
  · exact B.edgeFlow_nonneg hl.nonneg hc u v

/-- The cut flow rides on the edges of `G`: off the wrap edge, `e(u → v) ≠ 0` needs
`π̂_←(v → u) ≠ 0`, an edge `u → v` of the loop closure other than the wrap edge. -/
theorem cutFlow_supp (lam : V → ℝ) (c : ℝ) (u v : V) (h : cutFlow B lam c u v ≠ 0) :
    G.Edge u v := by
  unfold cutFlow at h
  split_ifs at h with hw
  · exact absurd rfl h
  · have hp : B.phat v u ≠ 0 := by
      intro h0; exact h (by simp only [BackwardPolicy.edgeFlow, h0, mul_zero])
    by_cases hv : v = G.src
    · subst hv
      by_cases hu : u = G.snk
      · exact absurd ⟨hu, rfl⟩ hw
      · exact absurd (B.phat_src_of_ne hu) hp
    · rw [B.phat_of_ne_src hv] at hp
      exact B.supp hv hp

/-- **Cutting the wrap edge leaves conservation untouched at every internal state.** -/
theorem cutFlow_cons {lam : V → ℝ} (hl : B.IsInvProb lam) (c : ℝ) :
    ∀ x ∈ G.internal, edgeInflow (cutFlow B lam c) x = edgeOutflow (cutFlow B lam c) x := by
  intro x hx
  obtain ⟨hxs, hxk⟩ := MarkedGraph.mem_internal.mp hx
  have hin : ∀ u, cutFlow B lam c u x = B.edgeFlow lam c u x := fun u => by
    simp only [cutFlow, hxs, and_false, if_false]
  have hout : ∀ w, cutFlow B lam c x w = B.edgeFlow lam c x w := fun w => by
    simp only [cutFlow, hxk, false_and, if_false]
  simp only [edgeInflow, edgeOutflow, hin, hout]
  rw [B.sum_edgeFlow_in lam c x, B.sum_edgeFlow_out hl c x]

/-- **The cut changes nothing the sampler reads**: the generative flow of the cut edge flow is
that of the uncut one — the sampler reads only `e(s₀ → ·)`, `e(· → s_f)` and `e` inside `𝒮`. -/
theorem graphFlow_cutFlow (lam : V → ℝ) (c : ℝ) :
    graphFlow G (cutFlow B lam c) = graphFlow G (B.edgeFlow lam c) := by
  have hrow : ∀ (v : G.internal) (w : V), cutFlow B lam c v w = B.edgeFlow lam c v w := by
    intro v w
    have := (MarkedGraph.mem_internal.mp v.2).2
    simp only [cutFlow, this, false_and, if_false]
  have hsrc : ∀ w, cutFlow B lam c G.src w = B.edgeFlow lam c G.src w := fun w => by
    simp only [cutFlow, G.src_ne_snk, false_and, if_false]
  have hout : outInt G (cutFlow B lam c) = outInt G (B.edgeFlow lam c) := by
    funext v; simp only [outInt, hrow]
  simp only [graphFlow, hsrc, hrow, hout]

/-- **The sampler is the paper's: `F_init = e(s₀ → ·)`**, item *(3)*'s `initFlow`. -/
theorem graphFlow_edgeFlow_finit (lam : V → ℝ) (c : ℝ) (v : G.internal) :
    (graphFlow G (B.edgeFlow lam c)).finit v = B.initFlow lam c v := rfl

/-- `F_term = e(· → s_f)`, item *(3)*'s `termFlow`. -/
theorem graphFlow_edgeFlow_fterm (lam : V → ℝ) (c : ℝ) (v : G.internal) :
    (graphFlow G (B.edgeFlow lam c)).fterm v = B.termFlow lam c v := rfl

/-- The star outflow of item *(3)* is the flow into `𝒮`: `f⋆_out(u) = ∑_{w ∈ 𝒮} e(u → w)` for
`u ≠ s_f`, nothing leaving `u` towards `s₀`. -/
theorem outflowStar_eq_sum_internal {lam : V → ℝ} (hl : B.IsInvProb lam) (c : ℝ) {x : V}
    (hxk : x ≠ G.snk) : B.outflowStar lam c x = ∑ w ∈ G.internal, B.edgeFlow lam c x w := by
  have h1 := B.outflowStar_eq_sum hl c x
  have h2 : (∑ w ∈ (Finset.univ.erase G.snk).erase G.src, B.edgeFlow lam c x w)
      + B.edgeFlow lam c x G.src = ∑ w ∈ Finset.univ.erase G.snk, B.edgeFlow lam c x w :=
    Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨G.src_ne_snk, Finset.mem_univ _⟩)
  rw [B.edgeFlow_to_src lam c hxk, add_zero, ← MarkedGraph.internal_eq_erase_src] at h2
  rw [h1, h2]

/-- `F⋆_out` is item *(3)*'s star outflow `f⋆_out(u) = cλ(u) − e(u → s_f)`. -/
theorem graphFlow_edgeFlow_fout {lam : V → ℝ} (hl : B.IsInvProb lam) (c : ℝ) (v : G.internal) :
    (graphFlow G (B.edgeFlow lam c)).fout v = B.outflowStar lam c v := by
  rw [outflowStar_eq_sum_internal B hl c (MarkedGraph.mem_internal.mp v.2).2]
  show outInt G (B.edgeFlow lam c) v = _
  rw [outInt, Finset.sum_coe_sort G.internal (fun w => B.edgeFlow lam c v w)]

/-- `P⋆` is item *(3)*'s star forward policy `π⋆_→ = e/f⋆_out` wherever `f⋆_out ≠ 0` — the only
states the sampler leaves; where it vanishes the sampler stops surely and the row is immaterial,
as the paper says. -/
theorem graphFlow_edgeFlow_P {lam : V → ℝ} (hl : B.IsInvProb lam) (c : ℝ) (v w : G.internal)
    (hv : B.outflowStar lam c v ≠ 0) :
    (graphFlow G (B.edgeFlow lam c)).P v w = B.fwdStar lam c v w := by
  have hf := graphFlow_edgeFlow_fout B hl c v
  have hne : outInt G (B.edgeFlow lam c) v ≠ 0 := by
    change (graphFlow G (B.edgeFlow lam c)).fout v ≠ 0
    rwa [hf]
  change (if outInt G (B.edgeFlow lam c) v = 0 then _ else _) = _
  rw [if_neg hne]
  change B.edgeFlow lam c v w / (graphFlow G (B.edgeFlow lam c)).fout v = _
  rw [hf]
  rfl

/-- **The terminal mass on `𝒮`**: `F_term(𝒮) = cλ(s₀)(1 − π_←(s_f → s₀))`. -/
theorem sum_internal_termFlow {lam : V → ℝ} (hl : B.IsInvProb lam) (c : ℝ) :
    ∑ y ∈ G.internal, B.termFlow lam c y = c * lam G.src * (1 - B.pb G.snk G.src) := by
  have hsnk_ne : G.snk ≠ G.src := G.src_ne_snk.symm
  have hpbsnk : B.pb G.snk G.snk = 0 := by
    by_contra h
    exact G.no_edge_out_of_snk G.snk (B.supp hsnk_ne h)
  have hterm : ∀ y, B.termFlow lam c y = c * lam G.src * B.pb G.snk y := fun y => by
    simp only [BackwardPolicy.termFlow, BackwardPolicy.edgeFlow, hl.lam_snk_eq_src,
      B.phat_of_ne_src hsnk_ne]
  have hrow : ∑ y ∈ G.internal, B.pb G.snk y = 1 - B.pb G.snk G.src := by
    have h := sum_split G (fun y => B.pb G.snk y)
    rw [B.row_sum hsnk_ne, hpbsnk, Finset.sum_coe_sort G.internal (fun y => B.pb G.snk y)] at h
    linarith
  simp only [hterm]
  rw [← Finset.mul_sum, hrow]

omit [Fintype V] [DecidableEq V] in
/-- A walk into `s₀` starts at `s₀`: nothing enters it. -/
theorem reach_src_eq {a : V} (h : G.Reach a G.src) : a = G.src := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, -, hb⟩
  · exact h.symm
  · exact absurd hb (G.no_edge_into_src b)

/-- **Once `𝒮 ≠ ∅`, some internal state has an edge to `s_f`**, so on a path-connected graph with
`π_←` positive on its edges `π_←(s_f → s₀) < 1`. -/
theorem pb_snk_src_lt_one (hpc : G.PathConnected) (hB : B.PositiveOnEdges)
    (hne : G.internal.Nonempty) : B.pb G.snk G.src < 1 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxs, hxk⟩ := MarkedGraph.mem_internal.mp hx
  obtain ⟨y, hy, hyk⟩ : ∃ y, y ≠ G.src ∧ G.Edge y G.snk := by
    rcases Relation.ReflTransGen.cases_tail (hpc.to_snk x) with h | ⟨y, hxy, hy⟩
    · exact absurd h.symm hxk
    · refine ⟨y, fun hys => ?_, hy⟩
      subst hys
      exact hxs (reach_src_eq hxy)
  have hpos : 0 < B.pb G.snk y := hB hyk
  have hsnk_ne : G.snk ≠ G.src := G.src_ne_snk.symm
  have hsub : ({G.src, y} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => B.nonneg G.snk i)
  rw [Finset.sum_pair (Ne.symm hy), B.row_sum hsnk_ne] at hle
  linarith

/-- **`theo:sampling_theorem` for item *(3)*'s flow**, at any `c ≥ 0` with `F_term(𝒮) > 0`: the
sampler obeys the `𝔼(τ)` bound, terminates, and emits `F_term` restricted to `𝒮`, normalized. -/
theorem edgeFlow_sampler {lam : V → ℝ} (hl : B.IsInvProb lam) {c : ℝ} (hc : 0 ≤ c)
    (hpos : 0 < ∑ y ∈ G.internal, B.termFlow lam c y) :
    Summable (graphFlow G (B.edgeFlow lam c)).tailProb ∧
    (graphFlow G (B.edgeFlow lam c)).expectedTau
      ≤ (∑ x, (graphFlow G (B.edgeFlow lam c)).fout x)
          / (∑ x, (graphFlow G (B.edgeFlow lam c)).finit x) + 1 ∧
    Terminates G (B.edgeFlow lam c) ∧
    IsSamplerLaw G (B.edgeFlow lam c) (fun x => if x ∈ G.internal then
      B.termFlow lam c x / ∑ y ∈ G.internal, B.termFlow lam c y else 0) := by
  have hsnk : ∀ y, cutFlow B lam c y G.snk = B.termFlow lam c y := fun y => by
    simp only [cutFlow, G.src_ne_snk.symm, and_false, if_false, BackwardPolicy.termFlow]
  have hpos' : 0 < ∑ y ∈ G.internal, cutFlow B lam c y G.snk := by simpa only [hsnk] using hpos
  have h := sampler_general (cutFlow_nonneg B hl hc) (cutFlow_supp B lam c) (cutFlow_cons B hl c)
    hpos'
  have hlaw : samplerLaw G (cutFlow B lam c) = fun x => if x ∈ G.internal then
      B.termFlow lam c x / ∑ y ∈ G.internal, B.termFlow lam c y else 0 := by
    funext x; simp only [samplerLaw, hsnk]
  rw [hlaw] at h
  simp only [IsSamplerLaw, Terminates, graphFlow_cutFlow] at h ⊢
  exact h

/-- **`theo:universality_graphs`*(3)*, the sampler clause, with or without an edge `s₀ → s_f`**:
at `c = Z/λ(s₀)` the sampler of the generative flow of item *(3)* terminates and emits
`F_term|_𝒮/F_term(𝒮)` — which is `s_τ ∼ F_term` in `app:notation`'s normalized sense, `F_term`
read as a distribution on `𝒮` — and that law is `π_←(s_f → ·)/(1 − π_←(s_f → s₀))` on `𝒮`,
`R = Zπ_←(s_f → ·)` restricted to `𝒮` and normalized. `𝒮 ≠ ∅` is what makes `F_term(𝒮) > 0`
when the edge is present. -/
theorem universality_graphs_sampler (hpc : G.PathConnected) (hB : B.PositiveOnEdges)
    {lam : V → ℝ} (hl : B.IsInvProb lam) {Z c : ℝ} (hZ : 0 < Z) (hc : c = Z / lam G.src)
    (hne : G.internal.Nonempty) :
    Summable (graphFlow G (B.edgeFlow lam c)).tailProb ∧
    (graphFlow G (B.edgeFlow lam c)).expectedTau
      ≤ (∑ x, (graphFlow G (B.edgeFlow lam c)).fout x)
          / (∑ x, (graphFlow G (B.edgeFlow lam c)).finit x) + 1 ∧
    Terminates G (B.edgeFlow lam c) ∧
    IsSamplerLaw G (B.edgeFlow lam c) (fun x => if x ∈ G.internal then
      B.termFlow lam c x / ∑ y ∈ G.internal, B.termFlow lam c y else 0) ∧
    IsSamplerLaw G (B.edgeFlow lam c) (fun x => if x ∈ G.internal then
      B.pb G.snk x / (1 - B.pb G.snk G.src) else 0) := by
  obtain ⟨hcpos, hcZ, -, -, hterm, -, -, -⟩ := B.universality_graphs_three hpc hB hl hZ hc
  have hlt := pb_snk_src_lt_one B hpc hB hne
  have hsum := sum_internal_termFlow B hl c
  rw [hcZ] at hsum
  have hpos : 0 < ∑ y ∈ G.internal, B.termFlow lam c y := by
    rw [hsum]; exact mul_pos hZ (by linarith)
  obtain ⟨h1, h2, h3, h4⟩ := edgeFlow_sampler B hl hcpos.le hpos
  refine ⟨h1, h2, h3, h4, ?_⟩
  have e : (fun x => if x ∈ G.internal then
      B.termFlow lam c x / ∑ y ∈ G.internal, B.termFlow lam c y else 0)
      = fun x => if x ∈ G.internal then B.pb G.snk x / (1 - B.pb G.snk G.src) else 0 := by
    funext x
    rw [hsum, hterm x, mul_div_mul_left _ _ hZ.ne']
  rwa [e] at h4

/-- **`theo:universality_graphs`*(3)*, the printed clause `s_τ ∼ R/Z`, `R = Zπ_←(s_f → ·)`,
holds iff `G` has no edge `s₀ → s_f`.** With the edge, `R/Z` charges `s₀`, which the sampler —
started in `𝒮` — never emits; without it, the sampler terminates and emits exactly `R/Z`. -/
theorem universality_graphs_sampler_iff (hpc : G.PathConnected) (hB : B.PositiveOnEdges)
    {lam : V → ℝ} (hl : B.IsInvProb lam) {Z c : ℝ} (hZ : 0 < Z) (hc : c = Z / lam G.src) :
    (IsSamplerLaw G (B.edgeFlow lam c) (fun x => B.termFlow lam c x / Z) ↔
      ¬ G.Edge G.src G.snk) ∧
    (¬ G.Edge G.src G.snk → Terminates G (B.edgeFlow lam c)) := by
  obtain ⟨hcpos, hcZ, -, -, hterm, -, -, -⟩ := B.universality_graphs_three hpc hB hl hZ hc
  have hsrc_nm : G.src ∉ G.internal := fun hm => (MarkedGraph.mem_internal.mp hm).1 rfl
  have hRZ : ∀ x, B.termFlow lam c x / Z = B.pb G.snk x := fun x => by
    rw [hterm x, mul_div_cancel_left₀ _ hZ.ne']
  have hno : ¬ G.Edge G.src G.snk → B.pb G.snk G.src = 0 := fun h => by
    by_contra h0; exact h (B.supp G.src_ne_snk.symm h0)
  have hsum := sum_internal_termFlow B hl c
  rw [hcZ] at hsum
  have key : ¬ G.Edge G.src G.snk →
      Terminates G (B.edgeFlow lam c) ∧
      IsSamplerLaw G (B.edgeFlow lam c) (fun x => B.termFlow lam c x / Z) := by
    intro h
    have h0 := hno h
    rw [h0, sub_zero, mul_one] at hsum
    obtain ⟨-, -, hT, hL⟩ := edgeFlow_sampler B hl hcpos.le (by rw [hsum]; exact hZ)
    refine ⟨hT, ?_⟩
    have e : (fun x => if x ∈ G.internal then
        B.termFlow lam c x / ∑ y ∈ G.internal, B.termFlow lam c y else 0)
        = fun x => B.termFlow lam c x / Z := by
      funext x
      rw [hsum]
      split_ifs with hx
      · rfl
      · have hx' : x = G.src ∨ x = G.snk := by
          by_contra hc'
          push Not at hc'
          exact hx (MarkedGraph.mem_internal.mpr hc')
        rw [hRZ]
        rcases hx' with rfl | rfl
        · exact h0.symm
        · by_contra h'
          exact G.no_edge_out_of_snk G.snk (B.supp G.src_ne_snk.symm (Ne.symm h'))
    rwa [e] at hL
  refine ⟨⟨fun hL he => ?_, fun h => (key h).2⟩, fun h => (key h).1⟩
  have : B.termFlow lam c G.src / Z = 0 := hL.2 G.src hsrc_nm
  rw [hRZ] at this
  exact (hB he).ne' this

/-- **`theo:universality_graphs`, the closing paragraph's "samples `R` exactly"**: for every
target `R` of mass `Z` with full support on the terminating states, the balanced flow of initial
mass `Z` of the family frozen at `R` (`UniversalityClosing.balancedMember`) has a sampler
with summable tail (so `𝔼(τ) < ∞`) that terminates and satisfies `s_τ ∼ R/Z` — **with no
hypothesis on the edge `s₀ → s_f`**: the frozen sink row `R/Z` vanishes at `s₀`, so the balanced flow carries nothing on
that edge. -/
theorem universality_graphs_closing_sampler [MeasurableSpace V] [MeasurableSingletonClass V]
    (hpc : G.PathConnected) (hB : B.PositiveOnEdges) {R : V → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hR : UniversalityClosing.IsFullTarget G R Z) {lam : V → ℝ}
    (hl : (UniversalityClosing.freezeSink B hR hZ).IsInvProb lam) :
    Summable (graphFlow G (PartialSupport.memberFlow
      (UniversalityClosing.balancedMember (UniversalityClosing.freezeSink B hR hZ) lam Z))).tailProb
    ∧ Terminates G (PartialSupport.memberFlow
      (UniversalityClosing.balancedMember (UniversalityClosing.freezeSink B hR hZ) lam Z))
    ∧ IsSamplerLaw G (PartialSupport.memberFlow
      (UniversalityClosing.balancedMember (UniversalityClosing.freezeSink B hR hZ) lam Z))
      (fun x => R x / Z) := by
  set B' := UniversalityClosing.freezeSink B hR hZ
  obtain ⟨-, -, -, -, -, -, hall⟩ := UniversalityClosing.universality_graphs_closing hpc hB hZ hR
  obtain ⟨hlam, -⟩ := hall lam hl
  rw [UniversalityClosing.memberFlow_balancedMember hlam Z]
  set c := Z / lam G.src with hc
  have hs0 := hlam G.src
  have hcpos : 0 < c := div_pos hZ hs0
  have hcZ : c * lam G.src = Z := div_mul_cancel₀ Z hs0.ne'
  have hsrc_nm : G.src ∉ G.internal := fun hm => (MarkedGraph.mem_internal.mp hm).1 rfl
  have hpb0 : B'.pb G.snk G.src = 0 := by
    rw [UniversalityClosing.freezeSink_pb_snk, hR.eq_zero_of_not_mem hsrc_nm, zero_div]
  have hsum := sum_internal_termFlow B' hl c
  rw [hcZ, hpb0, sub_zero, mul_one] at hsum
  have hterm : ∀ x, B'.termFlow lam c x = R x := fun x => by
    rw [B'.termFlow_eq_target hl hcZ x, UniversalityClosing.freezeSink_pb_snk]
    field_simp
  obtain ⟨h1, -, h3, h4⟩ := edgeFlow_sampler B' hl hcpos.le (by rw [hsum]; exact hZ)
  refine ⟨h1, h3, ?_⟩
  have e : (fun x => if x ∈ G.internal then
      B'.termFlow lam c x / ∑ y ∈ G.internal, B'.termFlow lam c y else 0)
      = fun x => R x / Z := by
    funext x
    rw [hsum, hterm]
    split_ifs with hx
    · rfl
    · rw [hR.eq_zero_of_not_mem hx, zero_div]
  rwa [e] at h4

/-- **Inhabitation of the edge case (kb `0025`)**: on the triangle `s₀ = 0 → 1 → 2 = s_f`,
`0 → 2`, with `π_←(2 → 1) = π_←(2 → 0) = ½` (`UniversalityClosing.triSrcSnkPol`, positive on every
edge), item *(3)*'s sampler at `Z = 1` terminates and emits `δ₁`, while `R/Z = π_←(2 → ·)` is
`½δ₀ + ½δ₁`: the printed `s_τ ∼ R/Z` fails. -/
theorem sampler_check_triangle :
    ∃ lam : Fin 3 → ℝ, UniversalityClosing.triSrcSnkPol.IsInvProb lam ∧
      Terminates PartialSupport.triangle
        (UniversalityClosing.triSrcSnkPol.edgeFlow lam (1 / lam PartialSupport.triangle.src)) ∧
      IsSamplerLaw PartialSupport.triangle
        (UniversalityClosing.triSrcSnkPol.edgeFlow lam (1 / lam PartialSupport.triangle.src))
        (fun x => if x = 1 then 1 else 0) ∧
      ¬ IsSamplerLaw PartialSupport.triangle
        (UniversalityClosing.triSrcSnkPol.edgeFlow lam (1 / lam PartialSupport.triangle.src))
        (fun x => UniversalityClosing.triSrcSnkPol.termFlow lam
          (1 / lam PartialSupport.triangle.src) x / 1) := by
  obtain ⟨lam, hl⟩ := UniversalityClosing.triSrcSnkPol.exists_invProb
  have hpc := UniversalityClosing.triangle_pathConnected
  have hB := UniversalityClosing.triSrcSnkPol_positiveOnEdges
  have hmem : (1 : Fin 3) ∈ PartialSupport.triangle.internal :=
    MarkedGraph.mem_internal.mpr ⟨by decide, by decide⟩
  obtain ⟨-, -, hT, -, hL⟩ := universality_graphs_sampler UniversalityClosing.triSrcSnkPol hpc hB hl
    (Z := 1) one_pos rfl ⟨1, hmem⟩
  refine ⟨lam, hl, hT, ?_, fun h => ((universality_graphs_sampler_iff
    UniversalityClosing.triSrcSnkPol hpc hB hl (Z := 1) one_pos rfl).1.mp h)
    UniversalityClosing.triangle_edge_src_snk⟩
  have e : (fun x => if x ∈ PartialSupport.triangle.internal then
      UniversalityClosing.triSrcSnkPol.pb PartialSupport.triangle.snk x
        / (1 - UniversalityClosing.triSrcSnkPol.pb PartialSupport.triangle.snk
          PartialSupport.triangle.src) else 0) = fun x => if x = 1 then 1 else 0 := by
    funext x
    fin_cases x
    · have h0 : (0 : Fin 3) ∉ PartialSupport.triangle.internal :=
        fun h => (MarkedGraph.mem_internal.mp h).1 rfl
      simp only [Fin.zero_eta, Fin.isValue, h0, if_false]
      rw [if_neg (by decide)]
    · simp only [Fin.mk_one, Fin.isValue, hmem, if_true]
      simp [UniversalityClosing.triSrcSnkPol, PartialSupport.triangle]
      norm_num
    · have h2 : (2 : Fin 3) ∉ PartialSupport.triangle.internal :=
        fun h => (MarkedGraph.mem_internal.mp h).2 rfl
      simp only [Fin.reduceFinMk, Fin.isValue, h2, if_false]
      rw [if_neg (by decide)]
  rwa [e] at hL

/-- **Inhabitation of `universality_graphs_closing_sampler` in the edge case**: on the same
triangle, the family frozen at the full target `δ₁` — not positive on the edge `0 → 2` — has a
balanced flow whose sampler terminates with `s_τ ∼ δ₁`. -/
theorem closing_sampler_check_triangle :
    ∃ lam : Fin 3 → ℝ,
      (UniversalityClosing.freezeSink UniversalityClosing.triSrcSnkPol
        UniversalityClosing.triangleTarget_full one_pos).IsInvProb lam ∧
      Terminates PartialSupport.triangle (PartialSupport.memberFlow
        (UniversalityClosing.balancedMember (UniversalityClosing.freezeSink
          UniversalityClosing.triSrcSnkPol UniversalityClosing.triangleTarget_full one_pos) lam 1)) ∧
      IsSamplerLaw PartialSupport.triangle (PartialSupport.memberFlow
        (UniversalityClosing.balancedMember (UniversalityClosing.freezeSink
          UniversalityClosing.triSrcSnkPol UniversalityClosing.triangleTarget_full one_pos) lam 1))
        (fun x => PartialSupport.triangleTarget x / 1) := by
  obtain ⟨lam, hl⟩ := (UniversalityClosing.freezeSink UniversalityClosing.triSrcSnkPol
    UniversalityClosing.triangleTarget_full one_pos).exists_invProb
  letI : MeasurableSpace (Fin 3) := ⊤
  haveI : MeasurableSingletonClass (Fin 3) := ⟨fun _ => trivial⟩
  obtain ⟨-, h2, h3⟩ := universality_graphs_closing_sampler UniversalityClosing.triSrcSnkPol
    UniversalityClosing.triangle_pathConnected UniversalityClosing.triSrcSnkPol_positiveOnEdges
    one_pos UniversalityClosing.triangleTarget_full hl
  exact ⟨lam, hl, h2, h3⟩

end Universality

end GFNBounds.Graph.SamplerWiring
