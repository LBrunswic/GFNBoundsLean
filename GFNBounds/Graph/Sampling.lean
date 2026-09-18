import GFNBounds.Core.Sampling
import GFNBounds.Graph.CycleDivergence

/-!
# The sampler of a flow-matching marked-graph flow emits its normalized terminal flow

**`theo:sampling_theorem`** — `proofs.tex`, the marked-graph corollary of
`GFNBoundsScaffold.Core.Sampling`, stated in the vocabulary its downstream rows use. Line numbers
drift (kb `0036`); the label is the anchor.

> If the flow-matching constraint `F_init + F⋆_out π⋆_→ = F_term + F⋆_out` is satisfied then
> `F_init(𝒮) = F_term(𝒮)` and `𝔼(τ) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1`, `s_τ ∼ F_term`.

`theo:no_bound_divergence` (`GFNBounds.Graph.CycleDivergence`), `lem:cycle_counterexample`
(`GFNBounds.Graph.CycleRemarks`) and `rem:silva_model_constant` (`GFNBounds.Silva.Remarks`) all
measure total variation against `CycleDivergence.termLaw G F = F(·→s_f)/F(𝒱→s_f)`, the
**normalized terminal flow** of an edgeflow, and each records in its SCOPE that identifying it
with the law of `s_τ` is this theorem, cited and not certified. This file certifies it.

## The generative flow of an edgeflow

On a marked graph `G` with edgeflow `F`, the sampler runs on the internal states `𝒮 = 𝒱 ∖ {s₀,s_f}`
(`G.internal`, as a subtype) with (`graphFlow`)

* `F_init(v) = F(s₀ → v)`, `F_term(v) = F(v → s_f)`,
* `F⋆_out(v) = ∑_{w ∈ 𝒮} F(v → w)` and `P⋆(v → w) = F(v → w)/F⋆_out(v)`.

Conservation `edgeInflow F = edgeOutflow F` on `𝒮`, the form the downstream files state flow
matching in, is exactly `equ:FM_const` for this flow (`flowMatching`): `s_f` emits nothing and
`s₀` receives nothing, by the support hypothesis and the two axioms of `MarkedGraph`.

## What is proved

| | |
|---|---|
| `sum_split` | a sum over `𝒱` is the two marks plus the sum over `𝒮` |
| `graphFlow`, `isGenFlow`, `flowMatching` | the generative flow of an edgeflow, and conservation as `equ:FM_const` |
| **`sampler_law`** | with no hypothesis on `s₀ → s_f`: `P(τ ≤ n, s_τ = x) → F(x→s_f)/∑_{y∈𝒮} F(y→s_f)` |
| **`sampler_termLaw`** | the sampler terminates, `𝔼(τ) ≤ F⋆_out(𝒮)/F_init(𝒮) + 1`, and `P(τ ≤ n, s_τ = x) → termLaw G F x` |
| **`sampler_Fk`** | inhabitation (kb `0025`): on the cycle `𝒞_N`, the sampler of `F_k = F̂ + kγ` emits `δ_{x₂}` for every `k ≥ 0` — the clause `s_τ(F_k) ∼ δ_{x₂}` downstream |

## Hypothesis checklist

| `sampler_termLaw` | |
|---|---|
| `F ≥ 0`, carried by the edges | ✓ `hnn`, `hsupp` — the downstream files' own hypotheses |
| flow matching on `𝒮` | ✓ `hcons`, in the downstream vocabulary |
| `F_term ≠ 0` | ✓ `hpos : 0 < ∑_y F(y → s_f)` together with `hss` |
| `F(s₀ → s_f) = 0` | ⚠ **added**; see SCOPE. It holds on `𝒞_N`, which has no edge `s₀ → s_f` |

## SCOPE (disclosed)

* **Everything `GFNBoundsScaffold.Core.Sampling` discloses** — finite state space, the sampler
  modelled by its time-`n` marginals, `s_τ ∼ F_term` delivered as a limit — applies here.
* **`hss : F(s₀ → s_f) = 0` is a hypothesis of the identification with `termLaw`, not of the
  theorem.** `termLaw G F` normalizes over all of `𝒱`, so a flow on an edge `s₀ → s_f` puts mass
  on `s₀` there, while the sampler, which starts in `𝒮`, never emits `s₀`: the two laws differ
  and `termLaw` is then *not* the law of `s_τ`. Without `hss` the sampler's law is still
  `F(x → s_f)/∑_{y ∈ 𝒮} F(y → s_f)` on `𝒮` (`sampler_law`); `hss` is what
  makes it `termLaw`. No downstream use is affected: `𝒞_N` has no edge `s₀ → s_f`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph.Sampling

open Finset Filter Topology GFNBounds.Core.Sampling GFNBounds.Graph.CycleDivergence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A sum over the vertices splits into the two marks and the internal states. -/
theorem sum_split (G : MarkedGraph V) (f : V → ℝ) :
    ∑ u, f u = f G.src + f G.snk + ∑ u : G.internal, f u := by
  rw [Finset.sum_coe_sort, MarkedGraph.internal]
  have hsnk : G.snk ∈ Finset.univ.erase G.src :=
    Finset.mem_erase.mpr ⟨G.src_ne_snk.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ G.src),
    ← Finset.add_sum_erase _ _ hsnk]
  ring

/-- The internal outflow of an edgeflow at `v`, `F⋆_out(v) = ∑_{w ∈ 𝒮} F(v → w)`. -/
noncomputable def outInt (G : MarkedGraph V) (F : V → V → ℝ) (v : G.internal) : ℝ :=
  ∑ w : G.internal, F v w

/-- **The generative flow of an edgeflow on a marked graph**, on the internal states `𝒮`:
`F_init(v) = F(s₀ → v)`, `F_term(v) = F(v → s_f)`, `F⋆_out(v) = ∑_{w ∈ 𝒮} F(v → w)` and
`P⋆(v → w) = F(v → w)/F⋆_out(v)` (a Dirac mass at `v` where `F⋆_out(v) = 0`, a state the sampler
leaves with probability `0` whatever the row says). -/
noncomputable def graphFlow (G : MarkedGraph V) (F : V → V → ℝ) : FlowData G.internal where
  finit v := F G.src v
  fterm v := F v G.snk
  fout v := outInt G F v
  P v w := if outInt G F v = 0 then (if v = w then 1 else 0) else F v w / outInt G F v

variable {G : MarkedGraph V} {F : V → V → ℝ}

theorem outInt_nonneg (hnn : ∀ u v, 0 ≤ F u v) (v : G.internal) : 0 ≤ outInt G F v :=
  Finset.sum_nonneg fun w _ => hnn v w

theorem fout_mul_P (hnn : ∀ u v, 0 ≤ F u v) (v w : G.internal) :
    (graphFlow G F).fout v * (graphFlow G F).P v w = F v w := by
  simp only [graphFlow]
  by_cases h : outInt G F v = 0
  · have hw : F v w = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun (w : G.internal) _ => hnn (v : V) (w : V))).mp h w
        (Finset.mem_univ _)
    rw [if_pos h, h, zero_mul, hw]
  · rw [if_neg h]
    field_simp

theorem isGenFlow (hnn : ∀ u v, 0 ≤ F u v) : (graphFlow G F).IsGenFlow where
  finit_nonneg v := hnn _ _
  fterm_nonneg v := hnn _ _
  fout_nonneg v := outInt_nonneg hnn v
  P_nonneg v w := by
    simp only [graphFlow]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact div_nonneg (hnn _ _) (outInt_nonneg hnn v)
  P_row v := by
    simp only [graphFlow]
    split_ifs with h
    · simp
    · rw [← Finset.sum_div]; exact div_self h

/-- **Conservation at the internal states is the flow-matching constraint** `equ:FM_const` of
the graph's generative flow. -/
theorem flowMatching (hnn : ∀ u v, 0 ≤ F u v) (hsupp : ∀ u v, F u v ≠ 0 → G.Edge u v)
    (hcons : ∀ x ∈ G.internal, edgeInflow F x = edgeOutflow F x) :
    (graphFlow G F).FlowMatching := by
  intro y
  have h := hcons y y.2
  simp only [edgeInflow, edgeOutflow] at h
  rw [sum_split G (fun u => F u y), sum_split G (fun w => F y w)] at h
  have h1 : F G.snk y = 0 := by
    by_contra hc; exact G.no_edge_out_of_snk _ (hsupp _ _ hc)
  have h2 : F y G.src = 0 := by
    by_contra hc; exact G.no_edge_into_src _ (hsupp _ _ hc)
  simp only [Finset.sum_congr rfl fun x _ => fout_mul_P (G := G) hnn x y]
  simp only [graphFlow, outInt]
  linarith

/-- **`theo:sampling_theorem`, on a marked graph, with no hypothesis on `s₀ → s_f`**: the
sampler emits `F(x → s_f)/∑_{y ∈ 𝒮} F(y → s_f)` on `𝒮`. -/
theorem sampler_law (hnn : ∀ u v, 0 ≤ F u v) (hsupp : ∀ u v, F u v ≠ 0 → G.Edge u v)
    (hcons : ∀ x ∈ G.internal, edgeInflow F x = edgeOutflow F x)
    (hpos : 0 < ∑ y : G.internal, F y G.snk) (x : G.internal) :
    Tendsto (fun n => (graphFlow G F).law n (x, true)) atTop
      (𝓝 (F x G.snk / ∑ y : G.internal, F y G.snk)) := by
  have hterm : (graphFlow G F).fterm ≠ 0 := by
    intro h
    have : ∑ y : G.internal, F y G.snk = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      simpa only [graphFlow, Pi.zero_apply] using congrFun h y
    linarith
  exact (FlowData.sampling_theorem (isGenFlow hnn) hterm (flowMatching hnn hsupp hcons)).2.2.2.2.2 x

/-- **`theo:sampling_theorem`, on a marked graph**: the sampler of a flow-matching edgeflow
terminates, obeys the `𝔼(τ)` bound, and emits its normalized terminal flow.
Its terminal law is `termLaw G F` of `GFNBounds.Graph.CycleDivergence`, the object
`theo:no_bound_divergence`, `lem:cycle_counterexample` and the Silva remarks measure TV against. -/
theorem sampler_termLaw (hnn : ∀ u v, 0 ≤ F u v) (hsupp : ∀ u v, F u v ≠ 0 → G.Edge u v)
    (hcons : ∀ x ∈ G.internal, edgeInflow F x = edgeOutflow F x)
    (hss : F G.src G.snk = 0) (hpos : 0 < ∑ y, F y G.snk) :
    Summable (graphFlow G F).tailProb ∧
    (graphFlow G F).expectedTau
      ≤ (∑ x, (graphFlow G F).fout x) / (∑ x, (graphFlow G F).finit x) + 1 ∧
    Tendsto (graphFlow G F).tailProb atTop (𝓝 0) ∧
    ∀ x : G.internal,
      Tendsto (fun n => (graphFlow G F).law n (x, true)) atTop (𝓝 (termLaw G F x)) := by
  have hsnk : F G.snk G.snk = 0 := by
    by_contra hc; exact G.no_edge_out_of_snk _ (hsupp _ _ hc)
  have hsum : ∑ y, F y G.snk = ∑ x, (graphFlow G F).fterm x := by
    rw [sum_split G (fun y => F y G.snk), hss, hsnk, zero_add, zero_add]
    rfl
  have hterm : (graphFlow G F).fterm ≠ 0 := by
    intro h
    rw [h] at hsum
    simp only [Pi.zero_apply, Finset.sum_const_zero] at hsum
    linarith
  obtain ⟨-, hs, hE, ht, -, hlaw⟩ :=
    FlowData.sampling_theorem (isGenFlow hnn) hterm (flowMatching hnn hsupp hcons)
  refine ⟨hs, hE, ht, fun x => ?_⟩
  have := hlaw x
  rwa [← hsum] at this

/-! ### Inhabitation: the cyclic counter-example -/

/-- **`theo:sampling_theorem`, inhabited on the cyclic counter-example**: the sampler of `F_k`
emits `δ_{x₂}` for every `k ≥ 0` — the sampler clause
`s_τ(F_k) ∼ δ_{x₂}` of `theo:no_bound_divergence` and `lem:cycle_counterexample`, now certified. -/
theorem sampler_Fk (M : ℕ) {k : ℝ} (hk : 0 ≤ k) (x : (cycGraph M).internal) :
    Tendsto (fun n => (graphFlow (cycGraph M) (Fk M k)).law n (x, true)) atTop
      (𝓝 (if (x : cycV M) = xC M 1 then 1 else 0)) := by
  have h := (sampler_termLaw (Fk_nonneg hk) (fun _ _ => Fk_supp) (Fk_flowMatching k)
    (by simp only [cycGraph_src, cycGraph_snk, Fk_snkC, if_neg (srcC_ne_xC 1)])
    (by rw [cycGraph_snk, sum_termFlow_Fk]; exact one_pos)).2.2.2 x
  rwa [termLaw_Fk] at h

end GFNBounds.Graph.Sampling
