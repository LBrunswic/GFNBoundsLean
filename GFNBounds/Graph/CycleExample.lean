import GFNBounds.Graph.Morozov
import GFNBounds.Balance.MassIdentity

/-!
# A five-vertex cycle: the frozen policy and the inflation force never deadlock

**`rem:cycle_no_stalemate`** — `proofs.tex:816–818`.

> Take the marked graph with vertices `{s₀,x₁,x₂,x₃,s_f}`, edges `s₀ → x₁`, the cycle
> `x₁ → x₂ → x₃ → x₁`, and `x₃ → s_f`, loop-closed as in Definition `def:loop_closure`; freeze
> the backward policy `π_←(x₁ → x₃) = p`, `π_←(x₁ → s₀) = 1 − p`, all other rows being
> deterministic. The expected backward-trajectory length is `(1+2p)/(1−p) < ∞`: the condition of
> Morozov et al. holds and the circulation cannot explode. The invariant measure gives equal mass
> `q` to the three cycle states and `(1−p)q` to `s₀` and `s_f`. Over-inflate the cycle: `u = M` on
> `{x₁,x₂,x₃}` and `u = 1` elsewhere, `M` large. Then, as `M → ∞`, the ratios tend to
> `r(x₁), r(x₂), r(s_f) → 1`, `r(x₃) → p` and `r(s₀) ∼ M(1−p)`: the frozen-policy constraint
> appears as the persistent leak-ratio `p` at the junction `x₃`, and the inflation force
> concentrates at the starved source, with magnitude `|g'(r)r| = 2 log r(s₀) ∼ 2 log M` for
> `g = (log x)²` — *growing*, not vanishing, with the imbalance. The candidate stalemate between
> the two forces therefore never forms (consistently with the mass identity); the source refills
> at logarithmic speed, giving a transient of order `M/log M`, after which the exponential phase
> of Theorem `theo:local_convergence` takes over. As `p → 1` the cycle closes, the backward-length
> bound `(1+2p)/(1−p)` and `B̂` blow up, and every rate degenerates: the construction interpolates
> smoothly toward the instability regime of Theorem `theo:no_bound_divergence`.

The vertices are `Fin 5`, in the paper's order: `0 = s₀`, `1 = x₁`, `2 = x₂`, `3 = x₃`, `4 = s_f`.
Everything below is a closed form in `p` and `M`; the limits `M → ∞` are corollaries of the closed
forms, which is the stronger statement.

## One correction to the remark, and one reading of an `∼`

**The expected backward-trajectory length is `3/(1−p)`, not `(1+2p)/(1−p)`.** `σ̄` is
`prop:morozov_rate`'s `E_{x ∼ π̂_←(s_f→·)} E(σ ∣ X₀ = x)`; here the target row is the point mass
at `x₃`, so `σ̄ = E(σ ∣ X₀ = x₃) = 3/(1−p)` (`sigmaBar_eq`). The number `(1+2p)/(1−p)` the remark
prints is `E(σ ∣ X₀ = x₁)` (`hitExp_x1`), the hitting time from the *other* end of the cycle. The
two differ at every `p < 1` (`sigmaBar_ne_paper_value`), and the remark's own second claim decides
between them: `prop:morozov_rate`*(1)* gives `λ(s₀) = 1/(2+σ̄)`, and the invariant measure the
remark states — which is correct, `invProb_paper` — forces `2 + σ̄ = (5−2p)/(1−p)`, i.e.
`σ̄ = 3/(1−p)` (`lam_src_eq_inv_two_add_sigmaBar`). **Nothing the remark concludes changes**: both
numbers are finite for `p < 1`, both blow up as `p → 1`, and neither enters claims 2–4.

**`r(s₀) ∼ M(1−p)` is the counting-measure reading.** `prop:no_distant_equilibrium` sets
`u := dμ/dλ` against the invariant probability `λ`, and on that reading `r(s₀) = M` *exactly*
(`ratio_src`) — the factor `(1−p)` cancels, because `λ(s₀)` already carries it. Reading `u`
instead as the density against the counting measure gives `r(s₀) = M(1−p)` exactly
(`ratio_counting_src`), which is the remark's number. Both readings are certified here, both give
`r(s₀) → ∞` linearly in `M`, and the four other ratios agree to their stated limits under both.

## SCOPE (disclosed)

* **`E(σ ∣ X₀ = ·)` is characterized, not constructed.** As in `GFNBounds/Graph/Morozov.lean`,
  `IsHitExp` is the linear system `u(s₀) = 0`, `u = 1 + Qu` off `s₀`, and reading its unique
  solution as a hitting-time expectation is a modelling step taken on the paper's authority.
  "*The expected backward-trajectory length is finite*" is delivered here as *the linear system
  has a (unique) real solution, with these values* — over `ℝ` there is nothing else to say.
* **"The circulation cannot explode" is not a dynamical theorem here.** What is certified is the
  static statement the remark reasons from: the mass of the gradient density is strictly negative
  at the inflated configuration (`no_stalemate`), so the two forces do not cancel. `B̂_σ` is
  exhibited in closed form (`bSigma_eq`) as the finite constant `prop:morozov_rate`*(2)*
  attaches to this graph.
* **The transient `M/log M`, the handover to `theo:local_convergence`, the blow-up of `B̂` as
  `p → 1`, and the interpolation toward `theo:no_bound_divergence` are not stated.** They are the
  remark's interpretation of the computation, not consequences of it: the first two need the
  gradient *flow* (no ODE layer exists here), and `B̂` is an operator norm — `CLAUDE.md`'s
  obstruction 2. What is certified of the `p → 1` clause is that `σ̄` is unbounded on `(0,1)`
  (`sigmaBar_unbounded`).
* **`g` never appears; only `g' = 2 log x / x`.** As in `GFNBounds/Balance/MassIdentity.lean`,
  the generator enters only through its derivative, and `lossGradDensity` is a definition rather
  than a derived gradient (`theo:first_variation_full` is not formalized).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the five-vertex marked graph, loop-closed | ✓ carried — `cyc`, closed by `BackwardPolicy.phat`; `phat_eq` prints the kernel |
| path-connected (needed by every cited result) | ✓ proved, not assumed — `pathConnected` |
| `π_←(x₁→x₃) = p`, `π_←(x₁→s₀) = 1−p`, other rows deterministic | ✓ carried — `pbFun`, and `pol` is the `BackwardPolicy` it defines |
| `0 < p` | ✓ carried; used **only** for `π_←(x₁→x₃) > 0`, i.e. the edge `x₃ → x₁` of `PositiveOnEdges` |
| `p < 1` | ✓ carried; used for `π_←(x₁→s₀) > 0` (the edge `s₀ → x₁`), and for `1 − p ≠ 0` in every closed form |
| `M` large | ✓ weakened to `0 < M`; the closed forms hold there, and `1 < M` is used only where a *strict* inequality is claimed |
| `g = (log x)²` | ⚠ only `g'` — `Balance.strictlyUnimodal_logSqDeriv` |
| the training measure `ν` | ✓ arbitrary with `w = dν/dμ > 0`, as in `prop:no_distant_equilibrium`*(1)* |

## What the remark claims and this file delivers

| remark | here |
|---|---|
| the expected backward-trajectory length is `(1+2p)/(1−p)` | ⚠ **`3/(1−p)`** — `sigmaBar_eq`, `sigmaBar_ne_paper_value`; the printed number is `hitExp_x1` |
| … `< ∞`, so Morozov's condition holds | `isHitExp` (the system is solved), `bSigma_eq` (the constant of `prop:morozov_rate`*(2)*) |
| `λ` gives `q` to `x₁,x₂,x₃` and `(1−p)q` to `s₀,s_f` | ✓ `invProb_paper`, with `q = 1/(5−2p)`; unique by `invProb_eq` |
| `r(x₁), r(x₂), r(s_f) → 1` | ✓ **exactly** `1` at every `M` — `ratio_x1`, `ratio_x2`, `ratio_snk` |
| `r(x₃) → p` | ✓ `ratio_x3 : = p + (1−p)/M`, limit `ratio_x3_tendsto` |
| `r(s₀) ∼ M(1−p)` | ⚠ `= M` on the paper's `u = dμ/dλ` reading (`ratio_src`); `= M(1−p)` against the counting measure (`ratio_counting_src`) |
| the force at the source is `2 log r(s₀) ∼ 2 log M`, growing | ✓ `inflation_force`, `inflation_force_tendsto` |
| the candidate stalemate never forms | ✓ `no_stalemate` — the gradient mass is *strictly* negative |
| the transient `M/log M`, the handover, `B̂ → ∞` | not stated — see SCOPE |
| all four claims at once | `cycle_no_stalemate` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph
namespace CycleExample

/-! ### The graph

`0 = s₀`, `1 = x₁`, `2 = x₂`, `3 = x₃`, `4 = s_f`. -/

/-- The edges of the remark's graph: `s₀ → x₁`, the cycle `x₁ → x₂ → x₃ → x₁`, and `x₃ → s_f`. -/
def edgeB : Fin 5 → Fin 5 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 3, 1 => true
  | 3, 4 => true
  | _, _ => false

/-- The edge relation of the remark's graph, as a decidable `Prop`. -/
def Edge (x y : Fin 5) : Prop := edgeB x y = true

instance : DecidableRel Edge := fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- **`rem:cycle_no_stalemate`, the graph**: `𝒱 = {s₀,x₁,x₂,x₃,s_f}` with `s₀ → x₁`, the cycle
`x₁ → x₂ → x₃ → x₁` and `x₃ → s_f`. The two marks `s₀ = 0` and `s_f = 4` carry no incoming resp.
outgoing edge, which `decide` settles. -/
def cyc : MarkedGraph (Fin 5) where
  Edge := Edge
  src := 0
  snk := 4
  src_ne_snk := by decide
  no_edge_into_src := by decide
  no_edge_out_of_snk := by decide

/-- **`rem:cycle_no_stalemate` is path-connected** (`def:path_connected`), the hypothesis every
result cited below carries. The single walk `s₀ → x₁ → x₂ → x₃ → s_f` passes through all five
vertices, so each vertex is split off it. -/
theorem pathConnected : cyc.PathConnected := by
  have e01 : cyc.Edge 0 1 := rfl
  have e12 : cyc.Edge 1 2 := rfl
  have e23 : cyc.Edge 2 3 := rfl
  have e34 : cyc.Edge 3 4 := rfl
  have r34 : cyc.Reach 3 4 := Relation.ReflTransGen.single e34
  have r24 : cyc.Reach 2 4 := Relation.ReflTransGen.head e23 r34
  have r14 : cyc.Reach 1 4 := Relation.ReflTransGen.head e12 r24
  have r04 : cyc.Reach 0 4 := Relation.ReflTransGen.head e01 r14
  have r01 : cyc.Reach 0 1 := Relation.ReflTransGen.single e01
  have r02 : cyc.Reach 0 2 := Relation.ReflTransGen.tail r01 e12
  have r03 : cyc.Reach 0 3 := Relation.ReflTransGen.tail r02 e23
  intro s
  fin_cases s
  · exact ⟨Relation.ReflTransGen.refl, r04⟩
  · exact ⟨r01, r14⟩
  · exact ⟨r02, r24⟩
  · exact ⟨r03, r34⟩
  · exact ⟨r04, Relation.ReflTransGen.refl⟩

/-! ### The frozen backward policy -/

/-- **`rem:cycle_no_stalemate`, the frozen policy**: `π_←(x₁→x₃) = p`, `π_←(x₁→s₀) = 1−p`, and
the three remaining rows deterministic — `π_←(x₂→x₁) = π_←(x₃→x₂) = π_←(s_f→x₃) = 1`. The `s₀`
row is left at `0`, the paper leaving `π_←(s₀→·)` undefined; `phat` overwrites it. -/
noncomputable def pbFun (p : ℝ) : Fin 5 → Fin 5 → ℝ
  | 1, 0 => 1 - p
  | 1, 3 => p
  | 2, 1 => 1
  | 3, 2 => 1
  | 4, 3 => 1
  | _, _ => 0

/-- **`rem:cycle_no_stalemate`, the frozen policy as a `BackwardPolicy`.** Of the three fields
only non-negativity constrains `p`, and it asks for `0 ≤ p` and `p ≤ 1`; the row sum
`(1−p) + p = 1` at `x₁` and the support condition are identities. The *strict* halves are the
binders because every statement below consumes one of them — `0 < p` for `PositiveOnEdges` at the
edge `x₃ → x₁`, `p < 1` for it at `s₀ → x₁` and for `1 − p ≠ 0` in every closed form. -/
noncomputable def pol {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : BackwardPolicy cyc where
  pb := pbFun p
  nonneg := by
    intro s s'
    have h0 : 0 ≤ p := hp0.le
    have h1 : 0 ≤ 1 - p := by linarith
    fin_cases s <;> fin_cases s' <;> simp [pbFun] <;> linarith
  row_sum := by
    intro s hs
    fin_cases s <;> simp_all [Fin.sum_univ_five, pbFun, cyc]
  supp := by
    intro s s' hs hne
    fin_cases s <;> fin_cases s' <;> simp_all [pbFun, cyc, Edge, edgeB]

/-- **`rem:cycle_no_stalemate`, the frozen policy is positive on the edges** — the hypothesis of
`theo:universality_graphs` and of `prop:morozov_rate`. This is where `0 < p` (the edge `x₃ → x₁`)
and `p < 1` (the edge `s₀ → x₁`) are consumed; the other three edges carry probability `1`. -/
theorem positiveOnEdges {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : (pol hp0 hp1).PositiveOnEdges := by
  intro s s' h
  have h1 : 0 < 1 - p := by linarith
  fin_cases s <;> fin_cases s' <;>
    simp_all [pol, pbFun, cyc, Edge, edgeB]

/-- The loop-closed kernel `π̂_←` of the remark, written out: the wrap row `π̂_←(s₀→s_f) = 1`
(`def:loop_closure`) on top of `pbFun`. -/
noncomputable def kern (p : ℝ) : Fin 5 → Fin 5 → ℝ
  | 0, 4 => 1
  | 1, 0 => 1 - p
  | 1, 3 => p
  | 2, 1 => 1
  | 3, 2 => 1
  | 4, 3 => 1
  | _, _ => 0

/-- **`def:loop_closure` on this graph**: `π̂_←` is `kern p`. -/
theorem phat_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : (pol hp0 hp1).phat = kern p := by
  funext s s'
  fin_cases s <;> fin_cases s' <;> rfl

/-! ### Claim 1: the expected backward-trajectory length -/

/-- `E(σ ∣ X₀ = ·)`, the hitting time of `s₀` by the backward chain, in closed form: `0` at `s₀`,
`(1+2p)/(1−p)` at `x₁`, `(2+p)/(1−p)` at `x₂`, `3/(1−p)` at `x₃` and `(4−p)/(1−p)` at `s_f`.
Characterized, not constructed — see the module SCOPE. -/
noncomputable def hitExp (p : ℝ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => (1 + 2 * p) / (1 - p)
  | 2 => (2 + p) / (1 - p)
  | 3 => 3 / (1 - p)
  | 4 => (4 - p) / (1 - p)

/-- **`rem:cycle_no_stalemate`, the backward-trajectory length**: `hitExp p` solves the linear
system `IsHitExp` of `prop:morozov_rate` — `u(s₀) = 0` and `u = 1 + Qu` off `s₀`. Each row is one
`field_simp`; the cycle closes at `x₁`, where `u(x₁) = 1 + p·u(x₃)` and `1 − p ≠ 0` is what makes
the system solvable. -/
theorem isHitExp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : (pol hp0 hp1).IsHitExp (hitExp p) := by
  have hne : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  refine ⟨rfl, ?_⟩
  intro x hx
  fin_cases x
  · exact absurd rfl hx
  · show hitExp p 1 = 1 + (pol hp0 hp1).qact (hitExp p) 1
    rw [BackwardPolicy.qact_apply, phat_eq, Fin.sum_univ_five]
    simp only [kern, hitExp]
    field_simp
    ring
  · show hitExp p 2 = 1 + (pol hp0 hp1).qact (hitExp p) 2
    rw [BackwardPolicy.qact_apply, phat_eq, Fin.sum_univ_five]
    simp only [kern, hitExp]
    field_simp
    ring
  · show hitExp p 3 = 1 + (pol hp0 hp1).qact (hitExp p) 3
    rw [BackwardPolicy.qact_apply, phat_eq, Fin.sum_univ_five]
    simp only [kern, hitExp]
    field_simp
    ring
  · show hitExp p 4 = 1 + (pol hp0 hp1).qact (hitExp p) 4
    rw [BackwardPolicy.qact_apply, phat_eq, Fin.sum_univ_five]
    simp only [kern, hitExp]
    field_simp
    ring

/-- `hitExp p` is *the* solution: `prop:morozov_rate`'s system has at most one. -/
theorem hitExp_unique {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {u : Fin 5 → ℝ}
    (hu : (pol hp0 hp1).IsHitExp u) : u = hitExp p :=
  BackwardPolicy.IsHitExp.unique pathConnected (positiveOnEdges hp0 hp1) hu (isHitExp hp0 hp1)

/-- **The number the remark prints**, `(1+2p)/(1−p)`, is `E(σ ∣ X₀ = x₁)` — the expected hitting
time of `s₀` from the far end of the cycle, not the backward-trajectory length. -/
theorem hitExp_x1 (p : ℝ) : hitExp p 1 = (1 + 2 * p) / (1 - p) := rfl

/-- **`rem:cycle_no_stalemate`, claim 1, corrected.** The expected backward-trajectory length
`σ̄ = E_{x ∼ π̂_←(s_f→·)} E(σ ∣ X₀ = x)` of `prop:morozov_rate` is `3/(1−p)`: the target row
`π̂_←(s_f→·)` is the point mass at `x₃`, so `σ̄ = E(σ ∣ X₀ = x₃)`, and a backward excursion runs
`x₃ → x₂ → x₁` and leaves to `s₀` with probability `1 − p` each lap. -/
theorem sigmaBar_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (pol hp0 hp1).sigmaBar (hitExp p) = 3 / (1 - p) := by
  show (pol hp0 hp1).qact (hitExp p) 4 = 3 / (1 - p)
  rw [BackwardPolicy.qact_apply, phat_eq, Fin.sum_univ_five]
  simp [kern, hitExp]

/-- **The remark's value for `σ̄` is not `σ̄`.** `3/(1−p) = (1+2p)/(1−p)` forces `p = 1`, which the
hypothesis excludes, so the two disagree at *every* `p ∈ (0,1)`. Both are finite and both diverge
as `p → 1`, which is all the remark uses the number for. -/
theorem sigmaBar_ne_paper_value {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (pol hp0 hp1).sigmaBar (hitExp p) ≠ (1 + 2 * p) / (1 - p) := by
  have hne : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  rw [sigmaBar_eq]
  intro h
  field_simp at h
  linarith

/-- **`σ̄` is unbounded on `(0,1)`** — the certified half of the remark's closing clause "as
`p → 1` the backward-length bound blows up". The witness is explicit: `p = 1 − 3/(|C|+4)`. That
`B̂` blows up too is an operator-norm statement and is not stated; see the module SCOPE. -/
theorem sigmaBar_unbounded (C : ℝ) : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ C < 3 / (1 - p) := by
  have habs : (0 : ℝ) ≤ |C| := abs_nonneg C
  have hd : (0 : ℝ) < |C| + 4 := by linarith
  have hlt : 3 / (|C| + 4) < 1 := (div_lt_one hd).mpr (by linarith)
  have hpos : (0 : ℝ) < 3 / (|C| + 4) := by positivity
  refine ⟨1 - 3 / (|C| + 4), by linarith, by linarith, ?_⟩
  have hrw : (1 : ℝ) - (1 - 3 / (|C| + 4)) = 3 / (|C| + 4) := by ring
  rw [hrw, div_div_eq_mul_div]
  linarith [le_abs_self C]

/-- `σ_* = max_x E(σ ∣ X₀ = x) = (4−p)/(1−p)`, attained at `s_f`. -/
theorem sigmaStar_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    sigmaStar cyc (hitExp p) = (4 - p) / (1 - p) := by
  have h1 : (0 : ℝ) < 1 - p := by linarith
  refine le_antisymm (maxOver_le fun x => ?_) (le_maxOver (hitExp p) 4)
  fin_cases x <;> simp only [hitExp]
  · exact div_nonneg (by linarith) (by linarith)
  · gcongr
    linarith
  · gcongr
    linarith
  · gcongr
    linarith
  · exact le_rfl

/-! ### Claim 2: the invariant measure -/

/-- The invariant probability of the backward chain: `q = 1/(5−2p)` at each of `x₁, x₂, x₃` and
`(1−p)q` at `s₀` and `s_f`. Normalization fixes `q`, which the remark leaves free. -/
noncomputable def lam (p : ℝ) : Fin 5 → ℝ
  | 0 => (1 - p) / (5 - 2 * p)
  | 1 => 1 / (5 - 2 * p)
  | 2 => 1 / (5 - 2 * p)
  | 3 => 1 / (5 - 2 * p)
  | 4 => (1 - p) / (5 - 2 * p)

/-- **`rem:cycle_no_stalemate`, claim 2**: `lam p` is an invariant probability of the loop-closed
backward chain. Stationarity at `x₃` is the one row the cycle enters — `q = qp + (1−p)q` — and at
`s₀` it is the leak `(1−p)q`. -/
theorem isInvProb {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : (pol hp0 hp1).IsInvProb (lam p) := by
  have hd : (0 : ℝ) < 5 - 2 * p := by linarith
  have hdne : (5 : ℝ) - 2 * p ≠ 0 := ne_of_gt hd
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp only [lam] <;> apply div_nonneg <;> linarith
  · rw [Fin.sum_univ_five]
    simp only [lam]
    have hnum : (1 - p) + 1 + 1 + 1 + (1 - p) = 5 - 2 * p := by ring
    rw [← add_div, ← add_div, ← add_div, ← add_div, hnum, div_self hdne]
  · intro y
    fin_cases y
    · show ∑ x, lam p x * (pol hp0 hp1).phat x 0 = lam p 0
      rw [Fin.sum_univ_five, phat_eq]
      simp only [kern, lam]
      ring
    · show ∑ x, lam p x * (pol hp0 hp1).phat x 1 = lam p 1
      rw [Fin.sum_univ_five, phat_eq]
      simp only [kern, lam]
      ring
    · show ∑ x, lam p x * (pol hp0 hp1).phat x 2 = lam p 2
      rw [Fin.sum_univ_five, phat_eq]
      simp only [kern, lam]
      ring
    · show ∑ x, lam p x * (pol hp0 hp1).phat x 3 = lam p 3
      rw [Fin.sum_univ_five, phat_eq]
      simp only [kern, lam]
      ring
    · show ∑ x, lam p x * (pol hp0 hp1).phat x 4 = lam p 4
      rw [Fin.sum_univ_five, phat_eq]
      simp only [kern, lam]
      ring

/-- **`theo:universality_graphs`*(1)* on this graph**: `lam p` is *the* invariant probability. -/
theorem invProb_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {l : Fin 5 → ℝ}
    (hl : (pol hp0 hp1).IsInvProb l) : l = lam p :=
  BackwardPolicy.invProb_unique pathConnected (positiveOnEdges hp0 hp1) hl (isInvProb hp0 hp1)

/-- **`rem:cycle_no_stalemate`, claim 2 in the remark's own words**: there is a `q > 0` with mass
`q` at each of the three cycle states and `(1−p)q` at `s₀` and at `s_f`. Here `q = 1/(5−2p)`. -/
theorem invProb_paper {p : ℝ} (hp1 : p < 1) :
    ∃ q : ℝ, 0 < q ∧ lam p 1 = q ∧ lam p 2 = q ∧ lam p 3 = q
      ∧ lam p 0 = (1 - p) * q ∧ lam p 4 = (1 - p) * q := by
  have hd : (0 : ℝ) < 5 - 2 * p := by linarith
  refine ⟨1 / (5 - 2 * p), by positivity, rfl, rfl, rfl, ?_, ?_⟩
  · show (1 - p) / (5 - 2 * p) = (1 - p) * (1 / (5 - 2 * p)); ring
  · show (1 - p) / (5 - 2 * p) = (1 - p) * (1 / (5 - 2 * p)); ring

/-! ### The two claims are inconsistent with each other, and claim 2 is the one that stands

`prop:morozov_rate`*(1)* reads `λ(s₀) = 1/(2+σ̄)` — proved for every finite path-connected marked
graph in `GFNBounds/Graph/Morozov.lean`, and instantiated here. The remark's own claim 2 therefore
determines `σ̄`, and what it determines is `3/(1−p)`. -/

/-- The occupation measure `N` of `prop:morozov_rate`, killed at `s₀`: `g ≡ 1/(1−p)` on the cycle
and `0` at the two marks. Characterized by the renewal equation `IsGreen`, not constructed. -/
noncomputable def green (p : ℝ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => 1 / (1 - p)
  | 2 => 1 / (1 - p)
  | 3 => 1 / (1 - p)
  | 4 => 0

/-- **`green p` solves `prop:morozov_rate`'s renewal equation** `g(s₀) = 0`,
`g = π̂_←(s_f→·) + gP̂` off `s₀`. The source term lands at `x₃`, the only in-neighbour of `s_f`. -/
theorem isGreen {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : (pol hp0 hp1).IsGreen (green p) := by
  have hne : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  refine ⟨rfl, ?_⟩
  intro y hy
  fin_cases y
  · exact absurd rfl hy
  · show green p 1 = (pol hp0 hp1).phat 4 1 + (pol hp0 hp1).densMap (green p) 1
    rw [BackwardPolicy.densMap_apply, Fin.sum_univ_five, phat_eq]
    simp only [kern, green]
    ring
  · show green p 2 = (pol hp0 hp1).phat 4 2 + (pol hp0 hp1).densMap (green p) 2
    rw [BackwardPolicy.densMap_apply, Fin.sum_univ_five, phat_eq]
    simp only [kern, green]
    ring
  · show green p 3 = (pol hp0 hp1).phat 4 3 + (pol hp0 hp1).densMap (green p) 3
    rw [BackwardPolicy.densMap_apply, Fin.sum_univ_five, phat_eq]
    simp only [kern, green]
    field_simp
    ring
  · show green p 4 = (pol hp0 hp1).phat 4 4 + (pol hp0 hp1).densMap (green p) 4
    rw [BackwardPolicy.densMap_apply, Fin.sum_univ_five, phat_eq]
    simp only [kern, green]
    ring

/-- `2 + σ̄ = (5−2p)/(1−p)`, the expected length of one loop-closed excursion. -/
theorem two_add_sigmaBar_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 + (pol hp0 hp1).sigmaBar (hitExp p) = (5 - 2 * p) / (1 - p) := by
  have hne : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  rw [sigmaBar_eq]
  field_simp
  ring

/-- **`prop:morozov_rate`*(1)* at `s₀`, on this graph**: `λ(s₀) = 1/(2+σ̄)`. Read backwards with
claim 2's `λ(s₀) = (1−p)/(5−2p)`, this *forces* `σ̄ = 3/(1−p)`; the remark's `(1+2p)/(1−p)` would
give `λ(s₀) = (1−p)/3`, which is claim 2 only at `p = 1`. -/
theorem lam_src_eq_inv_two_add_sigmaBar {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    lam p 0 = 1 / (2 + (pol hp0 hp1).sigmaBar (hitExp p)) := by
  have hne : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  have hd : (5 : ℝ) - 2 * p ≠ 0 := ne_of_gt (by linarith)
  rw [two_add_sigmaBar_eq]
  show (1 - p) / (5 - 2 * p) = 1 / ((5 - 2 * p) / (1 - p))
  field_simp

/-- `N ≡ 1/(1−p)` on the cycle and `N(s₀) = N(s_f) = 1`, so `min_x N(x) = 1`. -/
theorem minOver_visits_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    minOver cyc (visits cyc (green p)) = 1 := by
  have h1 : (0 : ℝ) < 1 - p := by linarith
  have hipos : (0 : ℝ) < (1 - p)⁻¹ := inv_pos.mpr h1
  have hmul : (1 - p) * (1 - p)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h1)
  have hge : (1 : ℝ) ≤ (1 - p)⁻¹ := by nlinarith [mul_pos hp0 hipos]
  refine le_antisymm ?_ (le_minOver fun x => ?_)
  · exact le_of_le_of_eq (minOver_le _ 0) (by simp [visits, green, cyc])
  · fin_cases x <;> simp [visits, green, cyc] <;> linarith

/-- **`prop:morozov_rate`*(2)* on this graph, with the constant computed**:
`B̂_σ = σ_*√((2+σ̄)/min N) = ((4−p)/(1−p))·√((5−2p)/(1−p))`, finite at every `p ∈ (0,1)`. This is
what "*the condition of Morozov et al. holds and the circulation cannot explode*" buys in the
paper's own variables; the dynamical reading of that sentence is not stated (see SCOPE). -/
theorem bSigma_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    sigmaStar cyc (hitExp p)
        * Real.sqrt ((2 + (pol hp0 hp1).sigmaBar (hitExp p))
          / minOver cyc (visits cyc (green p)))
      = (4 - p) / (1 - p) * Real.sqrt ((5 - 2 * p) / (1 - p)) := by
  rw [sigmaStar_eq hp0 hp1, minOver_visits_eq hp0 hp1, two_add_sigmaBar_eq hp0 hp1, div_one]

/-! ### Claim 3: the ratios of the over-inflated flow -/

/-- The over-inflated density of the remark: `u = M` on the cycle `{x₁,x₂,x₃}` and `u = 1` at the
two marks. It is `dμ/dλ`, as in `prop:no_distant_equilibrium`. -/
noncomputable def uInfl (M : ℝ) : Fin 5 → ℝ
  | 0 => 1
  | 1 => M
  | 2 => M
  | 3 => M
  | 4 => 1

theorem lam_pos {p : ℝ} (hp1 : p < 1) (x : Fin 5) : 0 < lam p x := by
  have hd : (0 : ℝ) < 5 - 2 * p := by linarith
  fin_cases x <;> simp only [lam] <;> apply div_pos <;> linarith

theorem uInfl_pos {M : ℝ} (hM : 0 < M) (x : Fin 5) : 0 < uInfl M x := by
  fin_cases x <;> simp only [uInfl] <;> linarith

private theorem den_ne {p M : ℝ} (hp1 : p < 1) (hM : 0 < M) (y : Fin 5) :
    lam p y * uInfl M y ≠ 0 :=
  ne_of_gt (mul_pos (lam_pos hp1 y) (uInfl_pos hM y))

/-- **`rem:cycle_no_stalemate`, claim 3 at `x₁`**: `r(x₁) = 1` *exactly*, at every `M` — the
remark's `→ 1` is attained, not approached. Mass enters `x₁` only from `x₂`, and `λ(x₁) = λ(x₂)`,
`u(x₁) = u(x₂)`. -/
theorem ratio_x1 {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 1 = 1 := by
  show (∑ x, lam p x * uInfl M x * (pol hp0 hp1).phat x 1) / (lam p 1 * uInfl M 1) = 1
  rw [div_eq_iff (den_ne hp1 hM 1), one_mul, Fin.sum_univ_five, phat_eq]
  simp only [kern, lam, uInfl]
  ring

/-- **`rem:cycle_no_stalemate`, claim 3 at `x₂`**: `r(x₂) = 1` exactly. -/
theorem ratio_x2 {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 2 = 1 := by
  show (∑ x, lam p x * uInfl M x * (pol hp0 hp1).phat x 2) / (lam p 2 * uInfl M 2) = 1
  rw [div_eq_iff (den_ne hp1 hM 2), one_mul, Fin.sum_univ_five, phat_eq]
  simp only [kern, lam, uInfl]
  ring

/-- **`rem:cycle_no_stalemate`, claim 3 at `s_f`**: `r(s_f) = 1` exactly. The wrap edge carries
`λ(s₀)u(s₀)` into `s_f`, and `λ(s_f) = λ(s₀)`, `u(s_f) = u(s₀) = 1`. -/
theorem ratio_snk {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 4 = 1 := by
  show (∑ x, lam p x * uInfl M x * (pol hp0 hp1).phat x 4) / (lam p 4 * uInfl M 4) = 1
  rw [div_eq_iff (den_ne hp1 hM 4), one_mul, Fin.sum_univ_five, phat_eq]
  simp only [kern, lam, uInfl]
  ring

/-- **`rem:cycle_no_stalemate`, claim 3 at `x₃`**: `r(x₃) = p + (1−p)/M` exactly, hence `→ p`.
This is the remark's *persistent leak-ratio at the junction*: the cycle feeds `x₃` with the
fraction `p` of the inflated mass, and the un-inflated `s_f` supplies the rest. -/
theorem ratio_x3 {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 3 = p + (1 - p) / M := by
  have hMne : M ≠ 0 := ne_of_gt hM
  have hd : (5 : ℝ) - 2 * p ≠ 0 := ne_of_gt (by linarith)
  show (∑ x, lam p x * uInfl M x * (pol hp0 hp1).phat x 3) / (lam p 3 * uInfl M 3)
    = p + (1 - p) / M
  rw [div_eq_iff (den_ne hp1 hM 3), Fin.sum_univ_five, phat_eq]
  simp only [kern, lam, uInfl]
  field_simp
  ring

/-- **`rem:cycle_no_stalemate`, claim 3 at `s₀`**: on the paper's own convention `u = dμ/dλ`
(`prop:no_distant_equilibrium`), `r(s₀) = M` *exactly*. The remark's `M(1−p)` is the counting
reading — see `ratio_counting_src` — the factor `(1−p)` being already carried by `λ(s₀)`. -/
theorem ratio_src {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0 = M := by
  have hd : (5 : ℝ) - 2 * p ≠ 0 := ne_of_gt (by linarith)
  show (∑ x, lam p x * uInfl M x * (pol hp0 hp1).phat x 0) / (lam p 0 * uInfl M 0) = M
  rw [div_eq_iff (den_ne hp1 hM 0), Fin.sum_univ_five, phat_eq]
  simp only [kern, lam, uInfl]
  ring

/-! #### The same five ratios read against the counting measure

Replacing `λ` by the counting measure — i.e. taking `u` itself as the measure `μ` — leaves
`r(x₁), r(x₂), r(s_f)` at `1` and moves the two `p`-dependent values to exactly the remark's:
`r(s₀) = M(1−p)` and `r(x₃) = p + 1/M`. -/

private theorem den_one_ne {M : ℝ} (hM : 0 < M) (y : Fin 5) :
    (1 : ℝ) * uInfl M y ≠ 0 := by
  rw [one_mul]; exact ne_of_gt (uInfl_pos hM y)

/-- **`r(s₀) = M(1−p)`, the remark's own value**, obtained by reading `u` as the density against
the counting measure rather than against `λ`. -/
theorem ratio_counting_src {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    Balance.ratio (pol hp0 hp1).phat (fun _ => 1) (uInfl M) 0 = M * (1 - p) := by
  show (∑ x, (1 : ℝ) * uInfl M x * (pol hp0 hp1).phat x 0) / ((1 : ℝ) * uInfl M 0) = M * (1 - p)
  rw [div_eq_iff (den_one_ne hM 0), Fin.sum_univ_five, phat_eq]
  simp only [kern, uInfl]
  ring

/-- `r(x₃) = p + 1/M` against the counting measure — the same limit `p`. -/
theorem ratio_counting_x3 {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    Balance.ratio (pol hp0 hp1).phat (fun _ => 1) (uInfl M) 3 = p + 1 / M := by
  have hMne : M ≠ 0 := ne_of_gt hM
  show (∑ x, (1 : ℝ) * uInfl M x * (pol hp0 hp1).phat x 3) / ((1 : ℝ) * uInfl M 3) = p + 1 / M
  rw [div_eq_iff (den_one_ne hM 3), Fin.sum_univ_five, phat_eq]
  simp only [kern, uInfl]
  field_simp
  ring

/-- `r(x₁) = r(x₂) = r(s_f) = 1` against the counting measure too. -/
theorem ratio_counting_ones {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    Balance.ratio (pol hp0 hp1).phat (fun _ => 1) (uInfl M) 1 = 1
      ∧ Balance.ratio (pol hp0 hp1).phat (fun _ => 1) (uInfl M) 2 = 1
      ∧ Balance.ratio (pol hp0 hp1).phat (fun _ => 1) (uInfl M) 4 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · show (∑ x, (1 : ℝ) * uInfl M x * (pol hp0 hp1).phat x 1) / ((1 : ℝ) * uInfl M 1) = 1
    rw [div_eq_iff (den_one_ne hM 1), one_mul, Fin.sum_univ_five, phat_eq]
    simp only [kern, uInfl]
    ring
  · show (∑ x, (1 : ℝ) * uInfl M x * (pol hp0 hp1).phat x 2) / ((1 : ℝ) * uInfl M 2) = 1
    rw [div_eq_iff (den_one_ne hM 2), one_mul, Fin.sum_univ_five, phat_eq]
    simp only [kern, uInfl]
    ring
  · show (∑ x, (1 : ℝ) * uInfl M x * (pol hp0 hp1).phat x 4) / ((1 : ℝ) * uInfl M 4) = 1
    rw [div_eq_iff (den_one_ne hM 4), one_mul, Fin.sum_univ_five, phat_eq]
    simp only [kern, uInfl]
    ring

/-! #### The limits `M → ∞`, as corollaries of the closed forms -/

/-- **`r(x₃) → p`** as `M → ∞` (`rem:cycle_no_stalemate`, claim 3). -/
theorem ratio_x3_tendsto {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun M : ℝ => Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 3)
      Filter.atTop (nhds p) := by
  have hcongr : (fun M : ℝ => Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 3)
      =ᶠ[Filter.atTop] fun M : ℝ => p + (1 - p) / M := by
    filter_upwards [Filter.eventually_gt_atTop 0] with M hM using ratio_x3 hp0 hp1 hM
  rw [Filter.tendsto_congr' hcongr]
  have h0 : Filter.Tendsto (fun M : ℝ => (1 - p) / M) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  simpa using tendsto_const_nhds.add h0

/-- **`r(s₀) → ∞`** as `M → ∞`, linearly — the starved source of the remark. -/
theorem ratio_src_tendsto {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun M : ℝ => Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0)
      Filter.atTop Filter.atTop := by
  have hcongr : (fun M : ℝ => Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0)
      =ᶠ[Filter.atTop] fun M : ℝ => M := by
    filter_upwards [Filter.eventually_gt_atTop 0] with M hM using ratio_src hp0 hp1 hM
  rw [Filter.tendsto_congr' hcongr]
  exact Filter.tendsto_id

/-! ### Claim 4: the inflation force grows, and the two forces do not cancel

The remark's closing move has two halves. The computable half is the *magnitude* of the force at
the starved source, `|g'(r)r| = 2 log r(s₀)`, and that it grows with `M`. The half that is a
reading rather than a claim — the transient `M/log M`, the handover to `theo:local_convergence`
— is not stated; see the module SCOPE. What *is* stated in place of "the candidate stalemate never
forms" is the mass identity's own verdict at this configuration: `no_stalemate`. -/

/-- **`rem:cycle_no_stalemate`, claim 4, the magnitude**: for `g = (log x)²`, so
`g'(x) = 2 log x / x`, the force at the starved source is `|g'(r)r| = 2 log r(s₀) = 2 log M`
exactly (on the counting reading it is `2 log(M(1−p))`, the same to leading order). -/
theorem inflation_force {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 < M) :
    2 * Real.log (Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0)
        / Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0
        * Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0
      = 2 * Real.log M := by
  rw [ratio_src hp0 hp1 hM]
  field_simp

/-- **… and it *grows*, not vanishes, with the imbalance**: `2 log M → ∞`. This is the whole of
the remark's "*growing, not vanishing*"; the *rate* at which the source refills is a statement
about the gradient flow and is not stated. -/
theorem inflation_force_tendsto :
    Filter.Tendsto (fun M : ℝ => 2 * Real.log M) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.const_mul_atTop (by norm_num)

/-- **`rem:cycle_no_stalemate`, claim 4**: at the over-inflated configuration the total mass of
the gradient density is *strictly* negative, for every training measure of positive density. So
the frozen-policy constraint and the inflation force do not cancel — "*the candidate stalemate
between the two forces never forms (consistently with the mass identity)*".

The proof is the remark's own: `prop:no_distant_equilibrium`*(1)* makes the mass `≤ 0` with
equality only at balance, and `ratio_x3` shows this configuration is not balanced — `r(x₃)` is
`p + (1−p)/M < 1` at every `M > 1`. The generator enters only through
`g' = 2 log x / x`, strictly unimodal by `Balance.strictlyUnimodal_logSqDeriv`. -/
theorem no_stalemate {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 1 < M)
    {w : Fin 5 → ℝ} (hw : ∀ x, 0 < w x) :
    Balance.gradMass (pol hp0 hp1).phat (lam p) (uInfl M) w (fun x => 2 * Real.log x / x) < 0 := by
  have hM0 : (0 : ℝ) < M := by linarith
  obtain ⟨-, hle, hiff⟩ := Balance.no_distant_equilibrium_one_graph pathConnected
    (positiveOnEdges hp0 hp1) (isInvProb hp0 hp1) (uInfl_pos hM0) hw
    Balance.strictlyUnimodal_logSqDeriv
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have hbal := hiff.mp h
    have h1 := (Balance.ratio_eq_one_iff_balanced
      (fun y => mul_pos (lam_pos hp1 y) (uInfl_pos hM0 y))).mpr hbal 3
    rw [ratio_x3 hp0 hp1 hM0] at h1
    have hlt : (1 - p) / M < 1 - p := div_lt_self (by linarith) hM
    linarith

/-! ### The remark in one statement -/

/-- **`rem:cycle_no_stalemate`** (`proofs.tex:816–818`), its four claims at once, on the graph
`cyc` with the frozen policy `pol` and the over-inflated density `uInfl M`.

Two departures from the printed text, both disclosed in the module docstring and neither touching
what the remark concludes. Claim 1 is stated with the **corrected** backward-trajectory length
`σ̄ = 3/(1−p)` — the printed `(1+2p)/(1−p)` is `E(σ ∣ X₀ = x₁)`, `hitExp_x1` — and claim 3's
`r(s₀)` is stated on the paper's own convention `u = dμ/dλ`, where it is exactly `M`; the printed
`M(1−p)` is the counting reading, `ratio_counting_src`. Claim 4 is stated as what the mass
identity delivers: the two forces do not cancel, the gradient mass being *strictly* negative.
The remark's dynamical readings — the `M/log M` transient, the handover to
`theo:local_convergence`, `B̂ → ∞` as `p → 1` — are not stated; see the module SCOPE. -/
theorem cycle_no_stalemate {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 1 < M)
    {w : Fin 5 → ℝ} (hw : ∀ x, 0 < w x) :
    (pol hp0 hp1).sigmaBar (hitExp p) = 3 / (1 - p)
      ∧ (∃ q : ℝ, 0 < q ∧ lam p 1 = q ∧ lam p 2 = q ∧ lam p 3 = q
          ∧ lam p 0 = (1 - p) * q ∧ lam p 4 = (1 - p) * q)
      ∧ (Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 1 = 1
          ∧ Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 2 = 1
          ∧ Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 4 = 1
          ∧ Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 3 = p + (1 - p) / M
          ∧ Balance.ratio (pol hp0 hp1).phat (lam p) (uInfl M) 0 = M)
      ∧ Balance.gradMass (pol hp0 hp1).phat (lam p) (uInfl M) w
          (fun x => 2 * Real.log x / x) < 0 :=
  ⟨sigmaBar_eq hp0 hp1, invProb_paper hp1,
    ⟨ratio_x1 hp0 hp1 (by linarith), ratio_x2 hp0 hp1 (by linarith),
      ratio_snk hp0 hp1 (by linarith), ratio_x3 hp0 hp1 (by linarith),
      ratio_src hp0 hp1 (by linarith)⟩,
    no_stalemate hp0 hp1 hM hw⟩

end CycleExample
end GFNBounds.Graph
