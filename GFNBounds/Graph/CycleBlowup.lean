import GFNBounds.Graph.MorozovConsume

/-!
# On the five-vertex cycle, `B̂_σ` blows up as the leak closes

**`rem:cycle_no_stalemate`** — `proofs.tex:837–839`; this file certifies the `B̂_σ` clause of its
closing sentence, `proofs.tex:838`.

**What the rest of the remark has, and where.** `GFNBounds/Graph/CycleExample.lean` certifies, in
its own file and on the same `cyc`, `pol`, `hitExp`, `lam`: the backward-trajectory length
`σ̄ = 3/(1−p)` (`sigmaBar_eq`); the invariant measure `q, q, q, (1−p)q, (1−p)q`
(`invProb_paper`, unique by `invProb_eq`); the ratios of the over-inflated flow, exactly as now
printed, `r(x₁) = r(x₂) = r(s_f) = 1`, `r(x₃) = p + (1−p)/M`, `r(s₀) = M` (`ratio_x1`, `ratio_x2`,
`ratio_snk`, `ratio_x3`, `ratio_src`); the force `2 log r(s₀) = 2 log M` and its growth
(`inflation_force`, `inflation_force_tendsto`); and the absence of a stalemate, as a strictly
negative gradient mass (`no_stalemate`). **Its module docstring quotes an older version of the
remark** — with `r(s₀) ∼ M(1−p)`, ratios as limits in `M`, and an `M/log M` transient — and its
cited span `proofs.tex:816–818` is stale; the certificates above match the current text.
**In neither file**: the clause that at `p ∈ {0,1}` an edge carries no backward probability, the
loop-closed chain no longer mixes and `B̂ = +∞`; the `M²` transient from the degree `−1`
homogeneity of the gradient field, and the handover to `theo:local_convergence`; `B̂ → +∞` as
`p → 1`; and "every rate the theorems certify degenerates".

> As `p → 1` the cycle closes, the backward-length bound `3/(1−p)`, `B̂` and `B̂_σ` blow up, and
> every rate the theorems certify degenerates.

The constant, as `prop:morozov_rate`*(2)* defines it (`proofs.tex:869`), and as its proof
rewrites it (`proofs.tex:893`):

> `B̂_σ := σ_* √((2+σ̄)/min_x N(x))` … `B̂_σ = σ_* λ_min^{-1/2}`.

"Blow up as `p → 1`" is read as a limit, `→ +∞` along `p → 1⁻` inside `(0,1)`, the only side on
which the remark's policy is defined. That is stronger than unboundedness, which is all
`CycleExample.sigmaBar_unbounded` gave for the backward-length bound.

## What is proved

| | |
|---|---|
| `bhatSigma_cycle_tendsto` | **`B̂_σ → +∞` as `p → 1⁻`**, for `Balance.BhatSigma = σ_*/√λ_min` evaluated at the cycle's `E(σ ∣ X₀ = ·)` and `λ` |
| `bhatSigma_blowup_paper_form` | the same limit with the **explicit** threshold `p > 1 − 3/(|C|+3)` ⇒ `B̂_σ > C`, in the **defining form** `σ_*√((2+σ̄)/min N)`, for *every* solution of the hitting-time system and of the renewal equation of `pol p` — solutions that exist (`CycleExample.isHitExp`, `CycleExample.isGreen`) and are unique |
| `three_div_le_bhatSigma` | the comparison it rests on: `3/(1−p) ≤ B̂_σ` on `(0,1)` |
| `three_div_one_sub_tendsto_atTop`, `sigmaBar_blowup` | the backward-length bound `3/(1−p) → +∞`, and `σ̄ → +∞` with the same explicit threshold |
| `blowupDelta_pos`, `lt_three_div_of_blowupDelta` | `δ(C) = 3/(|C|+3) > 0`, and `1 − δ(C) < p < 1 ⇒ C < 3/(1−p)` |
| `inv_one_sub_tendsto_atTop`, `eventually_mem_Ioo_zero_one` | the filter plumbing |

The route: `B̂_σ = ((4−p)/(1−p))·√((5−2p)/(1−p))` on `(0,1)` (`MorozovConsume.cycle_morozov_consume_check`),
the square root is `≥ 1` since `5−2p ≥ 1−p`, and `4−p ≥ 3`; so `B̂_σ ≥ 3/(1−p)`, and
`1/(1−p) → +∞` is `tendsto_inv_nhdsGT_zero` composed with `p ↦ 1−p`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the five-vertex marked graph, loop-closed | ✓ carried — `CycleExample.cyc`, `CycleExample.pol` |
| `π_←(x₁→x₃) = p`, `π_←(x₁→s₀) = 1−p`, `p ∈ (0,1)` | ✓ carried — explicit `hp0`, `hp1` in the two explicit-threshold forms; in `bhatSigma_cycle_tendsto` the filter `𝓝[<] 1` is eventually inside `(0,1)` (`eventually_mem_Ioo_zero_one`), so values at `p ∉ (0,1)` play no role |
| `p → 1` | ✓ read as `p → 1⁻`, the only approach inside `(0,1)` |
| `σ_*`, `σ̄` from `E(σ ∣ X₀ = ·)` | ✓ in the defining form, for *any* `uH` solving `IsHitExp` — one exists, `CycleExample.isHitExp`, and it is unique, `hitExp_unique`; `bhatSigma_cycle_tendsto` uses that solution, `hitExp p`, directly |
| `N(x)` | ✓ for *any* `gr` solving `IsGreen`, through `visits` — one exists, `CycleExample.isGreen`, and it is unique, `BackwardPolicy.IsGreen.unique` |
| `λ` the invariant probability | ✓ `lam p` in `bhatSigma_cycle_tendsto`, which is *the* invariant probability (`isInvProb`, `invProb_eq`) |
| `B̂_σ` defined as `σ_*√((2+σ̄)/min N)` | ✓ `bhatSigma_blowup_paper_form` states it in that form; `Balance.BhatSigma` is the `σ_*/√λ_min` form, equal by `MorozovConsume.bhatSigma_eq_visits` |
| "blow up" | ✓ read as `Tendsto … atTop`, not mere unboundedness |

## SCOPE (disclosed)

* **Only the `B̂_σ` clause is certified** (and, as a by-product, the backward-length bound
  `3/(1−p)` and `σ̄` tending to `+∞`). **`B̂ → +∞` is not stated.** The object exists:
  `Core.Mixing.B (Balance.densOp λ K) (Balance.meanOp λ)` is the mixing sum `∑ₙ β̂ₙ`,
  `β̂ₙ = ‖Pⁿ − Π‖` on `L²(λ)`, and it is typeable on this chain. What is missing is (a) a
  `Core.Mixing` instance for this chain's `densOp` at each `p ∈ (0,1)` — summability of `β̂ₙ`,
  i.e. geometric decay of `‖Pⁿ − Π‖`, which needs a spectral-gap or aperiodicity argument for the
  loop-closed kernel that nothing in the library supplies — without which `B` is a `tsum` of
  junk value `0`; and (b) a lower bound on `β̂ₙ` that grows as `p → 1`, e.g. from a slowly mixing
  test function concentrated on the cycle. The blow-up of `B̂_σ` does not transfer either:
  `B̂_σ` and `B̂` both bound `‖S‖` from above (`proofs.tex:1018`), and `B̂_σ` is no lower bound
  for `B̂`.
* **"Every rate the theorems certify degenerates" is not stated.** It quantifies over the rates of
  several theorems. Its `ϱ_σ = g''(1)w_min/B̂_σ² → 0` instance would follow in one line from
  `bhatSigma_cycle_tendsto`, but the sentence is wider than that one rate and is not certified.
* **`E(σ ∣ X₀ = ·)` and `N` are characterized, not constructed**, as in
  `GFNBounds/Graph/CycleExample.lean`'s SCOPE: they are the unique real solutions of their
  linear systems, and reading them as a hitting-time expectation and a visit count is taken on
  the paper's authority.
* The closing "interpolates smoothly toward the instability regime" is interpretation and is not
  stated.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph
namespace CycleExample

open Filter Topology

/-- `1/(1−p) → +∞` as `p → 1⁻`. -/
theorem inv_one_sub_tendsto_atTop :
    Tendsto (fun p : ℝ => (1 - p)⁻¹) (𝓝[<] 1) atTop := by
  have hsub : Tendsto (fun p : ℝ => 1 - p) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun p : ℝ => 1 - p) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Iio.mp hp))
  exact tendsto_inv_nhdsGT_zero.comp hsub

/-- `p ∈ (0,1)` eventually as `p → 1⁻`. -/
theorem eventually_mem_Ioo_zero_one : ∀ᶠ p : ℝ in 𝓝[<] 1, 0 < p ∧ p < 1 := by
  have h : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [h] with p hp
  exact hp

/-- **The backward-length bound blows up**: `3/(1−p) → +∞` as `p → 1⁻` (`proofs.tex:838`). -/
theorem three_div_one_sub_tendsto_atTop :
    Tendsto (fun p : ℝ => 3 / (1 - p)) (𝓝[<] 1) atTop := by
  have h := inv_one_sub_tendsto_atTop.const_mul_atTop (show (0:ℝ) < 3 by norm_num)
  refine h.congr fun p => ?_
  rw [div_eq_mul_inv]

/-- `B̂_σ ≥ 3/(1−p)` on the cycle, for every `p ∈ (0,1)`: in the closed form
`((4−p)/(1−p))·√((5−2p)/(1−p))`, `4−p ≥ 3` and the square root is at least `1`. -/
theorem three_div_le_bhatSigma {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    3 / (1 - p) ≤ Balance.BhatSigma cyc (hitExp p) (lam p) := by
  have h1 : (0:ℝ) < 1 - p := by linarith
  rw [(cycle_morozov_consume_check hp0 hp1).2.1]
  have hq : (1:ℝ) ≤ (5 - 2 * p) / (1 - p) := by
    rw [le_div_iff₀ h1]
    linarith
  have hs : (1:ℝ) ≤ Real.sqrt ((5 - 2 * p) / (1 - p)) := Real.one_le_sqrt.mpr hq
  have h3 : 3 / (1 - p) ≤ (4 - p) / (1 - p) := by
    gcongr
    linarith
  have hnn : (0:ℝ) ≤ (4 - p) / (1 - p) := by
    have : (0:ℝ) < 4 - p := by linarith
    positivity
  calc 3 / (1 - p) ≤ (4 - p) / (1 - p) := h3
    _ = (4 - p) / (1 - p) * 1 := (mul_one _).symm
    _ ≤ (4 - p) / (1 - p) * Real.sqrt ((5 - 2 * p) / (1 - p)) :=
        mul_le_mul_of_nonneg_left hs hnn

/-- **`rem:cycle_no_stalemate`, the `B̂_σ` clause**: on the five-vertex cycle,
`B̂_σ = σ_*/√λ_min → +∞` as `p → 1⁻`. The function is evaluated at the closed-form hitting
expectations `hitExp p` and invariant probability `lam p`, which are the paper's objects on
`(0,1)` (`isHitExp`, `hitExp_unique`, `isInvProb`, `invProb_eq`); the filter never sees
`p ∉ (0,1)`. -/
theorem bhatSigma_cycle_tendsto :
    Tendsto (fun p => Balance.BhatSigma cyc (hitExp p) (lam p)) (𝓝[<] 1) atTop := by
  refine tendsto_atTop_mono' _ ?_ three_div_one_sub_tendsto_atTop
  filter_upwards [eventually_mem_Ioo_zero_one] with p hp
  exact three_div_le_bhatSigma hp.1 hp.2

/-- The explicit threshold `δ(C) = 3/(|C|+3) ∈ (0,1]`: `0 < δ(C)`. -/
theorem blowupDelta_pos (C : ℝ) : 0 < 3 / (|C| + 3) := by
  have : (0:ℝ) ≤ |C| := abs_nonneg C
  positivity

/-- **The explicit threshold works**: `1 − 3/(|C|+3) < p < 1` gives `C < 3/(1−p)`. Indeed
`(1−p)(|C|+3) < 3`, so `C(1−p) ≤ |C|(1−p) < 3 − 3(1−p) ≤ 3`. -/
theorem lt_three_div_of_blowupDelta {C p : ℝ} (hp1 : p < 1) (hpδ : 1 - 3 / (|C| + 3) < p) :
    C < 3 / (1 - p) := by
  have h1 : (0:ℝ) < 1 - p := by linarith
  have hc : (0:ℝ) < |C| + 3 := by linarith [abs_nonneg C]
  have hlt : (1 - p) * (|C| + 3) < 3 := (lt_div_iff₀ hc).mp (by linarith)
  have hCle : C * (1 - p) ≤ |C| * (1 - p) := mul_le_mul_of_nonneg_right (le_abs_self C) h1.le
  rw [lt_div_iff₀ h1]
  nlinarith

/-- **`rem:cycle_no_stalemate`, the `B̂_σ` clause, in `prop:morozov_rate`'s defining form**
`B̂_σ = σ_*√((2+σ̄)/min_x N(x))`, with the explicit threshold `δ(C) = 3/(|C|+3)`
(`blowupDelta_pos`): at every `p ∈ (0,1)` with `p > 1 − 3/(|C|+3)`, and for every solution `uH` of
the hitting-time system and `gr` of the renewal equation of the policy `pol p`, `B̂_σ > C`. No
closed form enters the statement. **The quantifiers are not vacuous**: a solution of each system
exists at every `p ∈ (0,1)` — `CycleExample.isHitExp` exhibits `hitExp p`, `CycleExample.isGreen`
exhibits `green p` — and it is the only one (`hitExp_unique`, `BackwardPolicy.IsGreen.unique`). -/
theorem bhatSigma_blowup_paper_form (C : ℝ) :
    ∀ (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1), 1 - 3 / (|C| + 3) < p →
      ∀ uH gr : Fin 5 → ℝ, (pol hp0 hp1).IsHitExp uH → (pol hp0 hp1).IsGreen gr →
        C < sigmaStar cyc uH
          * Real.sqrt ((2 + (pol hp0 hp1).sigmaBar uH) / minOver cyc (visits cyc gr)) := by
  intro p hp0 hp1 hpδ uH gr hu hg
  rw [hitExp_unique hp0 hp1 hu,
    BackwardPolicy.IsGreen.unique pathConnected (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1)
      hg (isGreen hp0 hp1),
    ← (cycle_morozov_consume_check hp0 hp1).1]
  exact lt_of_lt_of_le (lt_three_div_of_blowupDelta hp1 hpδ) (three_div_le_bhatSigma hp0 hp1)

/-- **`σ̄ → +∞` as `p → 1⁻`**, in the same form with the same explicit threshold
`δ(C) = 3/(|C|+3)`: the limit strengthening of `CycleExample.sigmaBar_unbounded`, for every
solution of the hitting-time system — which exists, `CycleExample.isHitExp`, and is unique,
`hitExp_unique`, so the quantifier is not vacuous. -/
theorem sigmaBar_blowup (C : ℝ) :
    ∀ (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1), 1 - 3 / (|C| + 3) < p →
      ∀ uH : Fin 5 → ℝ, (pol hp0 hp1).IsHitExp uH → C < (pol hp0 hp1).sigmaBar uH := by
  intro p hp0 hp1 hpδ uH hu
  rw [hitExp_unique hp0 hp1 hu, sigmaBar_eq hp0 hp1]
  exact lt_three_div_of_blowupDelta hp1 hpδ

end CycleExample
end GFNBounds.Graph
