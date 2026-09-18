import GFNBounds.Balance.GlobalConvergence
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The gradient flow exists, stays positive, and is unique

**`prop:no_distant_equilibrium`** — `proofs.tex:874–908` (statement `874–885`, item *(3)* at
`879–883`; proof `887–908`, the existence paragraph `900–907`). What is formalized here is item
*(3)*'s **existence and uniqueness clause**, for both generators the item names, and — for
`g = (log x)²` on marked-graph loop closures — its convergence clause **from `u₀` alone**, with
the flow hypothesis of `GlobalConvergence.no_distant_equilibrium_three_converges` discharged.

> (`prop:no_distant_equilibrium`*(3)*) Let `𝒮̂` be finite, let `λ` be a probability with
> `λ_min := min_x λ(x) > 0`, let `g = (log x)²` or `g = (x−1)²`, and let `ν = wλ` with
> `w ≥ w_min > 0`. […] the gradient flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` from any `μ₀ ∼ λ`, with
> `u₀ := dμ₀/dλ`, has a unique solution `(μ_t)_{t≥0}` with `μ_t ∼ λ`, which converges to the
> balanced flow of the sphere `{‖u‖_{L²(λ)} = ‖u₀‖_{L²(λ)}}` […]

> (`prop:no_distant_equilibrium`, preamble) Let `g` be admissible and differentiable with
> `sign g'(x) = sign(x−1)` for `x ≠ 1` […], let `(𝒮̂, λ, T)` be ergodic, and write `u := dμ/dλ`
> and `r := d(μT)/dμ`.

> (proof, existence) […] The chain `T` is irreducible: if the set `C` of states accessible from
> some state were a proper subset of `𝒮̂`, […] `𝟏_Cλ` would be a `T`-invariant measure that is
> not a multiple of `λ` […] against ergodicity. […] `r(u)`, `𝓛(u)` and the gradient density
> `D(u) = P†φ − rφ`, `φ = g'(r)w/u`, are `C^∞` functions of `u ∈ 𝒰`. By the Cauchy–Lipschitz
> theorem the equation `u̇ = −D(u)`, which is the gradient flow in densities, has a unique
> maximal solution `(u_t)_{t∈[0,t_max)}` in `𝒰`. Along it: `‖u_t‖ = ‖u₀‖`; `𝓛(u_t) ≤ 𝓛₀` and
> `Πu_t ≥ m₀`; `r(u_t) ≤ R_max`, where `R_max := e^M` with `M := max(1, √(𝓛₀/(w_min λ_min)))`
> for `g = (log x)²`, and `R_max := 1 + √(𝓛₀/(w_min λ_min))` for `g = (x−1)²`;
> `u_t ≥ u_min := m₀(λ_min p_min/R_max)^{#𝒮̂−1}` at every state. […] Hence the solution never
> leaves `𝒦 := {‖u‖ = ‖u₀‖, u ≥ u_min}`, a compact subset of `𝒰`; a maximal solution of a locally
> Lipschitz equation that remains in a compact subset of its open domain is defined for all
> times, so `t_max = +∞`.

## What is proved

| clause | declaration |
|---|---|
| "`D(u)` is a `C^∞` function of `u ∈ 𝒰`" (`C¹` is what is used) | `contDiffAt_lossGrad`, hence `exists_lipschitzOnWith_lossGrad` on every box `[a,b]^V`, `a > 0` |
| Cauchy–Lipschitz, global form for a bounded globally Lipschitz field | `exists_forall_hasDerivAt_of_lipschitzWith` |
| the four a priori bullets, on a set of times where the ODE holds | `loss_antitoneOn_of_on`, `mass_monotoneOn_of_on`, `nrmL2_eq_of_on`, `FlowGenerator.ratio_le`, `edge_drop_of_ratio_le`, `floor_of_edge_drop`, `FlowGenerator.floor` |
| the generator facts the proof consumes, and the two generators | `FlowGenerator`; `logSqFlowGenerator` (`R_max = e^M`), `sqFlowGenerator` (`R_max = 1 + √·`) |
| **existence, with `u_t ≥ u_min` at the paper's constant** | **`FlowGenerator.exists_flow`**; `uFloor_logSq_eq_uMin` identifies `u_min` with `BoundaryBlowup.uMin` |
| **uniqueness among positive solutions** | **`isGradientFlow_unique`** (any `gd` that is `C¹` on `(0,∞)`) |
| irreducibility from ergodicity | **`reach_of_uniqueInvariant`** |
| **item *(3)*, existence and uniqueness, in the paper's hypotheses** | **`existsUnique_flow_logSq_of_ergodic`**, **`existsUnique_flow_sq_of_ergodic`**; irreducible-kernel forms `existsUnique_flow_logSq`, `existsUnique_flow_sq`, `FlowGenerator.existsUnique_flow`; marked-graph forms `existsUnique_flow_logSq_graph`, `existsUnique_flow_sq_graph` |
| **item *(3)*, "has a unique solution … which converges to the balanced flow of the sphere"**, `(log x)²`, from `u₀` alone | **`no_distant_equilibrium_three_of_init`** |
| inhabitation (kb 0025) | `twoState_uniqueInvariant`, `twoState_flow_exists_check`, `twoState_flow_exists_check_sq`, `cycle_flow_converges_check` |

## The route

The paper's own sentence uses a *maximal* solution and the escape-from-compacts theorem; Mathlib
v4.31.0 has Picard–Lindelöf on a compact time interval (`IsPicardLindelof`) and Grönwall
uniqueness (`ODE_solution_unique_of_mem_Icc_right`), and neither of the other two. The proof
therefore packages the same mathematics differently:

1. **Clamp.** On `𝒦' := [u_min/2, ‖u₀‖λ_min^{−1/2} + 2u_min]^V`, a compact convex subset of the
   open cone, `D` is `C¹`, hence Lipschitz and bounded (`ContDiffOn.exists_lipschitzOnWith`).
   The field `F(v) := −D(clamp_{𝒦'} v)` is then globally Lipschitz and bounded.
2. **Solve globally.** Picard–Lindelöf on `[−(n+1), n+1]` for every `n`, glued by uniqueness.
3. **The clamp is never active on `[0,∞)`.** A continuity bootstrap
   (`L2Toolkit.bootstrap_of_continuous`, the tool `BoundaryBlowup.flow_pos_of_pos` uses): while
   the solution is in `𝒦'` it solves the true ODE, so the paper's four bullets hold there — the
   sphere, the loss budget, the mass, the ratio cap and the floor — and they place it in the
   strictly smaller box `[u_min, ‖u₀‖λ_min^{−1/2}]^V`.
4. **Uniqueness.** Two positive solutions are continuous on `[0,T]`, hence both lie in a common
   box `[a,b]^V` with `a > 0`, where `D` is Lipschitz; Grönwall.

## Hypothesis checklist — `prop:no_distant_equilibrium`*(3)*, existence and uniqueness

| paper hypothesis | here |
|---|---|
| `𝒮̂` finite | ✓ `[Fintype V]` |
| `λ` a probability, `λ_min > 0` | ✓ `hlam : ∀ x, 0 < lam x`, `htot : ∑ x, lam x = 1`; `λ_min` is taken as the minimum inside the proof. ⚠ `FlowGenerator.exists_flow` takes `lamMin` with `hlmin : ∀ x, lamMin ≤ lam x` as a parameter, as `BoundaryBlowup` does |
| `(𝒮̂, λ, T)` ergodic, `T` a Markov kernel, `λ` its invariant measure | ✓ `_of_ergodic` forms: `hK : 0 ≤ K`, `hrow : ∑_y K x y = 1`, `hinv : Invariant K lam`, and `herg : UniqueInvariant K lam` — every non-negative invariant vector is a multiple of `λ`, the reading of "ergodic" the paper's proof spends ("not a multiple of `λ` … against ergodicity"). ⚠ The other forms take irreducibility `hreach` in its place (derived from ergodicity by `reach_of_uniqueInvariant`, the paper's argument) and no row sums; the marked-graph forms take the loop closure (`hpc`, `hpos`, `hl`), irreducibility being `breach_all` |
| `p_min := min{T(y→z) : T(y→z) > 0}` | ✓ inside the proof, `BoundaryBlowup.exists_edgeFloor` (`min(1, ·)` of the minimum). ⚠ a parameter with `hpmin` / `CrossingFloor` in `FlowGenerator.exists_flow` |
| `g = (log x)²` | ✓ `logSq`, `logSqDeriv`; ⚠ `logSqDeriv` is the definition `2 log x/x`, tied to `logSq` by `Flow.hasDerivAt_logSq` (the field `logSqFlowGenerator.hasDerivAt`), as throughout `GFNBounds.Balance` |
| `g = (x−1)²` | ✓ `sqGen` for `g`, `fun x => 2 * (x - 1)` for `g'` — the lambda `MassIdentity.strictlyUnimodal_sqDeriv` and `SqGenerator.lean` use; here tied to `sqGen` by `sqFlowGenerator.hasDerivAt` |
| `ν = wλ`, `w ≥ w_min > 0` | ✓ `nu = fun x => lam x * wf x`, `hwmin`, `hw` |
| "the gradient flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)`", "the equation `u̇ = −D(u)`, which is the gradient flow in densities" | ✓ `IsGradientFlow K lam nu gd u` (`Flow.lean`): the ODE in `ℝ^V` at every `t ≥ 0`, two-sided derivative at `0`. `D = lossGrad` is the library's definition of the field; its identification with `∇^λ𝓛` is `FirstVariation.lean`'s, inherited |
| "from any `μ₀ ∼ λ`" | ✓ `hu0 : ∀ x, 0 < u0 x` |
| "has a solution `(μ_t)_{t≥0}` with `μ_t ∼ λ`" | ✓ `∃ u, u 0 = u0 ∧ IsGradientFlow … u ∧ ∀ t ≥ 0, ∀ x, 0 < u t x` |
| "unique" | ✓ `∀ v, v 0 = u0 → IsGradientFlow … v → (∀ t ≥ 0, ∀ x, 0 < v t x) → ∀ t ≥ 0, v t = u t`. ⚠ the competitor is asked `IsGradientFlow`, i.e. a two-sided derivative at `0`; a solution with only a right derivative there becomes one by extending it linearly to `t < 0`, which changes nothing on `[0,∞)` (not formalized) |
| "which converges to the balanced flow of the sphere" | ✓ for `(log x)²` on marked-graph loop closures: `no_distant_equilibrium_three_of_init`. ✗ otherwise in this file; both generators on every finite ergodic chain: `GlobalConvergenceFinite.no_distant_equilibrium_three_{logSq,sq}_of_ergodic` |
| `R_max`, `u_min` | ✓ `capR` of the two instances **is** the paper's `R_max` at `C = 𝓛₀/(w_min λ_min)`, `uFloor` **is** `u_min`, and `FlowGenerator.exists_flow` delivers `u_t ≥ u_min` |

## SCOPE (disclosed)

* **This file certifies convergence only where `GlobalConvergence.lean` does**: `g = (log x)²`
  on the loop closure of a finite path-connected marked graph. This file removes that theorem's
  flow hypothesis (`no_distant_equilibrium_three_of_init`) and nothing else. The convergence of
  the `(x−1)²` flow and on a general finite ergodic kernel are closed in
  `GlobalConvergenceFinite.lean` (2026-09-18); **existence and uniqueness** are proved at the full
  generality of item *(3)*: a
  finite ergodic chain, both generators.
* **The route is not the paper's word for word** (see *The route*): no maximal solution and no
  escape-from-compacts theorem, which Mathlib v4.31.0 lacks; a clamped field, a global solution
  and a bootstrap instead. The mathematical content consumed — `C¹` field, sphere, loss budget,
  mass, ratio cap, floor — is the paper's, bullet for bullet.
* **`C¹`, not `C^∞`.** The paper asserts `C^∞`; only `C¹` is proved, and only `C¹` is used.
* **Below `t = 0` the constructed curve is the clamped flow's**, not a gradient flow. The
  predicate asks nothing there.
* **Re-proved rather than reused.** `MassAscent.lossVal_antitoneOn`, `mass_monotoneOn` and
  `Flow.nrmL2_const_on_Ici` hypothesise `IsGradientFlow` on all of `[0,∞)`, which the clamped
  curve satisfies only where the clamp is inactive; `loss_antitoneOn_of_on`,
  `mass_monotoneOn_of_on` and `nrmL2_eq_of_on` are the same proofs with the ODE asked on the set
  of times (`IsGradientFlowOn`), and are generic in `g`. `floor_of_edge_drop` is
  `BoundaryBlowup.pos_of_loss_le`'s level-set argument with the one-edge drop as a hypothesis, so
  that it serves both generators. The master may route the strict lemmas through these.
* **Not restated**: "along the flow `‖u_t‖ = ‖u₀‖` and `μ_t(𝒮̂)` is non-decreasing" are
  `Flow.nrmL2_const_of_flow` and `MassAscent.mass_monotone_flow`, which now apply to a curve
  that exists; the gradient lower bound and the entry time are `Lojasiewicz.lean`,
  `SqGenerator.lean` and `MassAscent.entry_time`; the coercivity clause (`μ_t = m_t(1+h)λ`,
  `‖h‖ ≤ ε₀` at the entry time) is `RatioBridge.exists_delta_for_radius`.
* **Two constants are existential, and neither is the paper's.** The Lipschitz constant of `D`
  on a box and the bound on `D` there come from compactness (`exists_lipschitzOnWith_lossGrad`,
  `IsCompact.exists_bound_of_continuousOn`); they serve only the qualitative existence and
  uniqueness clause, which names no constant. The constants the paper does name, `R_max` and
  `u_min`, are explicit formulas (`capR`, `uFloor`), kb 0007.
* **Ergodicity is `UniqueInvariant`**: every non-negative invariant vector is a multiple of `λ`.
  This is the literal finite-space instance of the paper's definition (`universality.tex:22–24`:
  the kernel is ergodic if "the only `μ ≪ ν_B` it fixes are the multiples of `ν_B`"; with `λ > 0`
  every non-negative vector is `≪ λ`), and the convention at `proofs.tex:22`. The
  irreducible-kernel forms (`existsUnique_flow_logSq`, `existsUnique_flow_sq`) take irreducibility
  instead, which every usual reading of ergodicity implies (`reach_of_uniqueInvariant` is the
  paper's accessible-set argument), so the invariant-set definition is covered too.

## Inhabitation (kb 0025)

`twoState_flow_exists_check` and `twoState_flow_exists_check_sq` exhibit, on the two-state chain
`T(i→j) = 1/2`, `λ = (1/2,1/2)`, `w ≡ 1`, a positive curve satisfying `IsGradientFlow` from the
**non-balanced** `u₀ = (3/2, 1/2)` (`r(1) = 2`), for each generator, through the paper-hypothesis
forms `existsUnique_flow_*_of_ergodic` — whose `UniqueInvariant` is inhabited there by
`twoState_uniqueInvariant`, and `FlowGenerator` by the two instances. `cycle_flow_converges_check`
does the same on the five-vertex cycle of `rem:cycle_no_stalemate` at `p = 1/2` from the
over-inflated `uInfl 2` (`r(s₀) = 2`), and applies `no_distant_equilibrium_three_converges` to it.
More generally, `existsUnique_flow_logSq` and `existsUnique_flow_sq` show that a hypothesis
`IsGradientFlow K lam (fun x => lam x * wf x) gd u` with `hu0 : ∀ x, 0 < u 0 x`, for `gd` either
generator, `K ≥ 0` irreducible, `λ > 0` a `K`-invariant probability and `w ≥ w_min > 0`, is met by
a curve that exists from **every** positive start: the theorems of `GFNBounds.Balance` carrying it
are not vacuous on that setting (their other hypotheses are theirs to inhabit).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset Filter Topology Set
open scoped NNReal

/-! ### The field is `C¹` on the open cone, hence Lipschitz on every box inside it -/

section Smooth

variable {V : Type*} [Fintype V]

/-- The ratio `r(u)(y) = (μT)(y)/(λ(y)u(y))` is `C¹` in `u` wherever its denominator is not `0`. -/
theorem contDiffAt_ratio {K : V → V → ℝ} {lam : V → ℝ} {u : V → ℝ} (y : V)
    (hy : lam y * u y ≠ 0) :
    ContDiffAt ℝ 1 (fun v : V → ℝ => ratio K lam v y) u := by
  simp only [ratio, pushMass]
  refine ContDiffAt.div ?_ ?_ hy
  · exact (ContDiff.sum fun x _ => ((contDiff_const.mul (contDiff_apply ℝ ℝ x)).mul
      contDiff_const)).contDiffAt
  · exact (contDiff_const.mul (contDiff_apply ℝ ℝ y)).contDiffAt

/-- **`D(u) = P†φ − rφ`, `φ = g'(r)w/u`, is a `C¹` function of `u` on the open cone**
(`proofs.tex:900`, "are `C^∞` functions of `u ∈ 𝒰`"), for any `g'` that is `C¹` on `(0,∞)`:
`r > 0` there (`MassIdentity.ratio_pos`), so `g'` is only ever evaluated where it is smooth. -/
theorem contDiffAt_lossGrad {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hgd : ∀ y : ℝ, 0 < y → ContDiffAt ℝ 1 gd y) :
    ContDiffAt ℝ 1 (fun v : V → ℝ => lossGrad K lam nu gd v) u := by
  have hden : ∀ y, lam y * u y ≠ 0 := fun y => (mul_pos (hlam y) (hu y)).ne'
  have hr : ∀ y, ContDiffAt ℝ 1 (fun v : V → ℝ => ratio K lam v y) u :=
    fun y => contDiffAt_ratio y (hden y)
  have hphi : ∀ y, ContDiffAt ℝ 1
      (fun v : V → ℝ => gd (ratio K lam v y) * (nu y / (lam y * v y))) u := by
    intro y
    refine ContDiffAt.mul ?_ ?_
    · exact (hgd _ (ratio_pos hinv hK hlam hu y)).comp u (hr y)
    · exact contDiffAt_const.div (contDiff_const.mul (contDiff_apply ℝ ℝ y)).contDiffAt (hden y)
  refine contDiffAt_pi.2 fun x => ?_
  simp only [lossGrad, lossGradDensity, gradDensity, funAct]
  refine ContDiffAt.sub ?_ ((hr x).mul (hphi x))
  exact ContDiffAt.sum fun y _ => contDiffAt_const.mul (hphi y)

/-- The box `[a,b]^V` in the space of densities. -/
def densityBox (V : Type*) (a b : ℝ) : Set (V → ℝ) := Set.pi univ fun _ => Icc a b

omit [Fintype V] in
/-- Membership in the box, coordinate by coordinate. -/
theorem mem_densityBox {a b : ℝ} {u : V → ℝ} :
    u ∈ densityBox V a b ↔ ∀ x, a ≤ u x ∧ u x ≤ b := by
  simp only [densityBox, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_imp_iff]

omit [Fintype V] in
/-- The box is convex. -/
theorem convex_densityBox (a b : ℝ) : Convex ℝ (densityBox V a b) :=
  convex_pi fun _ _ => convex_Icc a b

omit [Fintype V] in
/-- The box is compact. -/
theorem isCompact_densityBox (a b : ℝ) : IsCompact (densityBox V a b) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- The field `D` is Lipschitz on every box `[a,b]^V` with `a > 0`: `C¹` on a compact convex set
(`ContDiffOn.exists_lipschitzOnWith`). -/
theorem exists_lipschitzOnWith_lossGrad {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hgd : ∀ y : ℝ, 0 < y → ContDiffAt ℝ 1 gd y) {a b : ℝ} (ha : 0 < a) :
    ∃ L, LipschitzOnWith L (fun v : V → ℝ => lossGrad K lam nu gd v) (densityBox V a b) := by
  have hC : ContDiffOn ℝ 1 (fun v : V → ℝ => lossGrad K lam nu gd v) (densityBox V a b) :=
    fun u hu => (contDiffAt_lossGrad hinv hK hlam
      (fun x => lt_of_lt_of_le ha ((mem_densityBox.1 hu) x).1) hgd).contDiffWithinAt
  exact hC.exists_lipschitzOnWith one_ne_zero (convex_densityBox a b) (isCompact_densityBox a b)

/-- The clamp onto `[a,b]^V`, coordinate by coordinate: `max a (min b ·)`. -/
def clampBox (a b : ℝ) (u : V → ℝ) : V → ℝ := fun x => max a (min b (u x))

omit [Fintype V] in
/-- The clamp lands in the box. -/
theorem clampBox_mem {a b : ℝ} (hab : a ≤ b) (u : V → ℝ) : clampBox a b u ∈ densityBox V a b :=
  mem_densityBox.2 fun _ => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

omit [Fintype V] in
/-- The clamp is the identity on the box. -/
theorem clampBox_eq {a b : ℝ} {u : V → ℝ} (hu : u ∈ densityBox V a b) : clampBox a b u = u := by
  funext x
  obtain ⟨h1, h2⟩ := (mem_densityBox.1 hu) x
  simp only [clampBox, min_eq_right h2, max_eq_right h1]

/-- The clamp is `1`-Lipschitz for the sup distance on `V → ℝ`. -/
theorem lipschitzWith_clampBox (a b : ℝ) : LipschitzWith 1 (clampBox (V := V) a b) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro x
  rw [Real.dist_eq]
  have h1 : |max a (min b (u x)) - max a (min b (v x))| ≤ |min b (u x) - min b (v x)| := by
    rw [max_comm a, max_comm a]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : |min b (u x) - min b (v x)| ≤ |u x - v x| := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    simp only [sub_self, abs_zero]
    exact max_le (abs_nonneg _) le_rfl
  have h3 : |u x - v x| ≤ dist u v := by
    rw [← Real.dist_eq]; exact dist_le_pi_dist u v x
  exact h1.trans (h2.trans h3)

end Smooth

/-! ### The paper's four a priori bullets, on a set of times where the ODE holds

The clamped curve of the existence proof solves the true ODE only where the clamp is inactive,
so the a priori estimates are needed with the ODE asked on a set of times, not on `[0,∞)`. -/

section Apriori

variable {V : Type*} [Fintype V]

/-- The gradient-flow ODE asked on a set `D` of times only. -/
def IsGradientFlowOn (K : V → V → ℝ) (lam nu : V → ℝ) (gd : ℝ → ℝ) (u : ℝ → V → ℝ)
    (D : Set ℝ) : Prop :=
  ∀ s ∈ D, ∀ x : V, HasDerivAt (fun r : ℝ => u r x) (-lossGrad K lam nu gd (u s) x) s

/-- A gradient flow is a gradient flow on `[0,∞)`. -/
theorem IsGradientFlow.isGradientFlowOn {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ}
    {u : ℝ → V → ℝ} (h : IsGradientFlow K lam nu gd u) :
    IsGradientFlowOn K lam nu gd u (Ici 0) := fun s hs => h s hs

/-- **`𝓛(u_t) ≤ 𝓛₀`** (`proofs.tex:903`), on a convex set of times where the ODE holds and
`u > 0`: `MassAscent.loss_antitoneOn` with the ODE asked on `D` only. -/
theorem loss_antitoneOn_of_on {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    {D : Set ℝ} (hD : Convex ℝ D)
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hupos : ∀ s ∈ D, ∀ x, 0 < u s x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hflow : IsGradientFlowOn K lam nu gd u D) :
    AntitoneOn (fun s : ℝ => loss K lam nu (u s) g) D := by
  have hderiv : ∀ s ∈ D, HasDerivAt (fun z : ℝ => loss K lam nu (u z) g)
      (-(Graph.nrmL2 lam (lossGrad K lam nu gd (u s)) ^ 2)) s :=
    fun s hs => hasDerivAt_loss_flow_at hinv hK hlam (hupos s hs) hg (hflow s hs)
  refine antitoneOn_of_deriv_nonpos hD
    (fun s hs => ((hderiv s hs).continuousAt).continuousWithinAt)
    (fun s hs => ((hderiv s (interior_subset hs)).differentiableAt).differentiableWithinAt)
    fun s hs => ?_
  rw [(hderiv s (interior_subset hs)).deriv]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- **`Πu_t ≥ m₀`** (`proofs.tex:903`), on a convex set of times where the ODE holds and `u > 0`:
`MassAscent.mass_monotoneOn` with the ODE asked on `D` only. -/
theorem mass_monotoneOn_of_on {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    {D : Set ℝ} (hD : Convex ℝ D)
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hupos : ∀ s ∈ D, ∀ x, 0 < u s x) (hnu : ∀ x, 0 < nu x) (hg : StrictlyUnimodal gd)
    (hflow : IsGradientFlowOn K lam nu gd u D) :
    MonotoneOn (fun s : ℝ => Graph.meanL2 lam (u s)) D := by
  have hderiv : ∀ s ∈ D, HasDerivAt (fun z : ℝ => Graph.meanL2 lam (u z))
      (-(gradMass K lam (u s) (rnWeight lam nu (u s)) gd)) s := by
    intro s hs
    have hsum : HasDerivAt (fun z : ℝ => ∑ x, lam x * u z x)
        (∑ x, lam x * -lossGrad K lam nu gd (u s) x) s :=
      HasDerivAt.fun_sum fun x _ => (hflow s hs x).const_mul (lam x)
    have hval : (∑ x, lam x * -lossGrad K lam nu gd (u s) x)
        = -(gradMass K lam (u s) (rnWeight lam nu (u s)) gd) := by
      simp only [gradMass, lossGrad_eq_lossGradDensity, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hval] at hsum
    exact hsum
  refine monotoneOn_of_deriv_nonneg hD
    (fun s hs => ((hderiv s hs).continuousAt).continuousWithinAt)
    (fun s hs => ((hderiv s (interior_subset hs)).differentiableAt).differentiableWithinAt)
    fun s hs => ?_
  rw [(hderiv s (interior_subset hs)).deriv]
  obtain ⟨-, hle, -⟩ := no_distant_equilibrium_one hinv hK hlam
    (hupos s (interior_subset hs)) (rnWeight_pos hlam hnu (hupos s (interior_subset hs))) hg
  exact neg_nonneg.mpr hle

/-- **`‖u_t‖ = ‖u₀‖`** (`proofs.tex:902`), on a convex set of times where the ODE holds and
`u > 0`: `Flow.nrmL2_const_on_Ici` with the ODE asked on `D` only. -/
theorem nrmL2_eq_of_on {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    {D : Set ℝ} (hD : Convex ℝ D) (hlam : ∀ x, 0 < lam x)
    (hupos : ∀ s ∈ D, ∀ x, 0 < u s x) (hflow : IsGradientFlowOn K lam nu gd u D)
    {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≤ b) :
    Graph.nrmL2 lam (u b) = Graph.nrmL2 lam (u a) := by
  have hN : ∀ s ∈ D, HasDerivAt (fun z : ℝ => ∑ x, lam x * (u z x * u z x)) 0 s := by
    intro s hs
    have hsum : HasDerivAt (fun z : ℝ => ∑ x, lam x * (u z x * u z x))
        (∑ x, lam x * (-lossGrad K lam nu gd (u s) x * u s x
          + u s x * -lossGrad K lam nu gd (u s) x)) s :=
      HasDerivAt.fun_sum fun x _ =>
        HasDerivAt.const_mul (lam x) ((hflow s hs x).fun_mul (hflow s hs x))
    have hrw : ∀ x : V, lam x * (-lossGrad K lam nu gd (u s) x * u s x
        + u s x * -lossGrad K lam nu gd (u s) x)
        = -2 * (lam x * (lossGrad K lam nu gd (u s) x * u s x)) := fun x => by ring
    have hzero : (∑ x, lam x * (-lossGrad K lam nu gd (u s) x * u s x
        + u s x * -lossGrad K lam nu gd (u s) x)) = 0 := by
      rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hrw x, ← Finset.mul_sum]
      have h := ipL2_lossGrad_self (K := K) (lam := lam) (u := u s) nu gd hlam (hupos s hs)
      simp only [Graph.ipL2] at h
      rw [h, mul_zero]
    rwa [hzero] at hsum
  have hconst := eq_of_hasDerivAt_zero_on hD hN ha hb hab
  simp only [Graph.nrmL2, Graph.ipL2]
  rw [hconst]

/-- **The one-edge drop from a ratio cap** (`proofs.tex:905`, "`R_max u_t(z) ≥ r(u_t)(z)u_t(z)
= (Pu_t)(z) ≥ … ≥ λ_min p_min u_t(y)`"): if `r ≤ R` everywhere, then across an edge `y → z` with
`K(y,z) ≥ p_min`, `(λ_min p_min/R) u(y) ≤ u(z)`. -/
theorem edge_drop_of_ratio_le {K : V → V → ℝ} {lam u : V → ℝ} {lamMin pmin R : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin) (hpmin0 : 0 < pmin) (hR : 0 < R)
    (hr : ∀ x, ratio K lam u x ≤ R) {y z : V} (hyz : pmin ≤ K y z) :
    lamMin * pmin / R * u y ≤ u z := by
  have hden : 0 < lam z * u z := mul_pos (hlam z) (hu z)
  have hpush : pushMass K lam u z ≤ R * (lam z * u z) := by
    have := (div_le_iff₀ hden).mp (by simpa only [ratio] using hr z)
    linarith
  have hsingle : lam y * u y * K y z ≤ pushMass K lam u z :=
    Finset.single_le_sum (f := fun x => lam x * u x * K x z)
      (fun x _ => mul_nonneg (mul_nonneg (hlam x).le (hu x).le) (hK x z)) (Finset.mem_univ y)
  have hlamz : lam z ≤ 1 := by
    rw [← htot]
    exact Finset.single_le_sum (f := lam) (fun i _ => (hlam i).le) (Finset.mem_univ z)
  have hlow : lamMin * pmin * u y ≤ lam y * u y * K y z := by
    have h1 : lamMin * pmin ≤ lam y * K y z :=
      mul_le_mul (hlmin y) hyz hpmin0.le (le_trans hlmin0.le (hlmin y))
    have h2 := mul_le_mul_of_nonneg_right h1 (hu y).le
    calc lamMin * pmin * u y ≤ lam y * K y z * u y := h2
      _ = lam y * u y * K y z := by ring
  have hup : R * (lam z * u z) ≤ R * u z := by
    have : lam z * u z ≤ u z := by nlinarith [(hu z).le]
    exact mul_le_mul_of_nonneg_left this hR.le
  have hchain : lamMin * pmin * u y ≤ R * u z := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hR]
  linarith

/-- **Propagation of a one-edge drop across the state space** (`proofs.tex:905`, "by
irreducibility every state is reached from `y₀` along at most `#𝒮̂ − 1` transitions"): if
`c·u(y) ≤ u(z)` across every edge with `K(y,z) ≥ p_min`, `0 < c ≤ 1`, and the mass is at least
`m₀`, then `u ≥ m₀ c^{|V|−1}`.
`BoundaryBlowup.pos_of_loss_le`'s level-set argument, with the drop as a hypothesis. -/
theorem floor_of_edge_drop {K : V → V → ℝ} {lam u : V → ℝ} {pmin c m0 : ℝ}
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hcross : CrossingFloor K pmin) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hdrop : ∀ y z : V, pmin ≤ K y z → c * u y ≤ u z)
    (hm0 : m0 ≤ Graph.meanL2 lam u) (x : V) :
    m0 * c ^ (Fintype.card V - 1) ≤ u x := by
  classical
  obtain ⟨xM, -, hxM⟩ := Finset.exists_max_image (Finset.univ : Finset V) u ⟨x, Finset.mem_univ x⟩
  have humax0 : 0 < u xM := hu xM
  have hmean_le : Graph.meanL2 lam u ≤ u xM := by
    calc Graph.meanL2 lam u = ∑ y, lam y * u y := rfl
      _ ≤ ∑ y, lam y * u xM :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hxM y (Finset.mem_univ y)) (hlam y).le
      _ = u xM := by rw [← Finset.sum_mul, htot, one_mul]
  set A : ℕ → Finset V := fun j => Finset.univ.filter (fun y => c ^ j * u xM ≤ u y) with hAdef
  have hmemA : ∀ (j : ℕ) (y : V), y ∈ A j ↔ c ^ j * u xM ≤ u y := by
    intro j y; simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
  have hA0 : xM ∈ A 0 := by rw [hmemA, pow_zero, one_mul]
  have hmono : ∀ j : ℕ, A j ⊆ A (j + 1) := by
    intro j y hy
    rw [hmemA] at hy ⊢
    refine le_trans ?_ hy
    have hpj : (0:ℝ) ≤ c ^ j := (pow_pos hc0 j).le
    have h1 : c ^ (j + 1) * u xM = c ^ j * c * u xM := by ring
    have h2 : c ^ j * c ≤ c ^ j * 1 := mul_le_mul_of_nonneg_left hc1 hpj
    have h3 : c ^ j * c * u xM ≤ c ^ j * 1 * u xM :=
      mul_le_mul_of_nonneg_right h2 humax0.le
    rw [h1, mul_one] at *
    exact h3
  have hxMmem : ∀ j : ℕ, xM ∈ A j := by
    intro j
    induction j with
    | zero => exact hA0
    | succ k ih => exact hmono k ih
  have hgrow : ∀ j : ℕ, A j ≠ Finset.univ → (A j).card < (A (j + 1)).card := by
    intro j hj
    obtain ⟨y, hy, z, hz, hyz⟩ := hcross (A j) ⟨xM, hxMmem j⟩ hj
    have hzA : z ∈ A (j + 1) := by
      rw [hmemA]
      have h1 : c ^ j * u xM ≤ u y := (hmemA j y).mp hy
      have h2 : c * u y ≤ u z := hdrop y z hyz
      have : c ^ (j + 1) * u xM = c * (c ^ j * u xM) := by ring
      rw [this]
      exact le_trans (mul_le_mul_of_nonneg_left h1 hc0.le) h2
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset (hmono j)).mpr ⟨z, hzA, hz⟩)
  have hcard : ∀ j : ℕ, min (j + 1) (Fintype.card V) ≤ (A j).card := by
    intro j
    induction j with
    | zero =>
        refine le_trans (min_le_left _ _) ?_
        exact Finset.card_pos.mpr ⟨xM, hA0⟩
    | succ k ih =>
        by_cases hk : A k = Finset.univ
        · have hsub : (Finset.univ : Finset V) ⊆ A (k + 1) := by
            rw [← hk]; exact hmono k
          have huniv : A (k + 1) = Finset.univ := Finset.univ_subset_iff.mp hsub
          rw [huniv, Finset.card_univ]
          exact min_le_right _ _
        · have := hgrow k hk
          have hle : min (k + 1) (Fintype.card V) + 1 ≤ (A (k + 1)).card := by omega
          have hub : (A (k + 1)).card ≤ Fintype.card V := Finset.card_le_univ (A (k + 1))
          omega
  have huniv : A (Fintype.card V - 1) = Finset.univ := by
    have hcardpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
    refine Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) ?_)
    have := hcard (Fintype.card V - 1)
    have hmin : min (Fintype.card V - 1 + 1) (Fintype.card V) = Fintype.card V := by omega
    rw [hmin] at this
    exact this
  have hkey : c ^ (Fintype.card V - 1) * u xM ≤ u x := by
    have : x ∈ A (Fintype.card V - 1) := by rw [huniv]; exact Finset.mem_univ x
    exact (hmemA _ x).mp this
  have hpow : (0:ℝ) ≤ c ^ (Fintype.card V - 1) := (pow_pos hc0 _).le
  calc m0 * c ^ (Fintype.card V - 1) ≤ u xM * c ^ (Fintype.card V - 1) :=
        mul_le_mul_of_nonneg_right (le_trans hm0 hmean_le) hpow
    _ = c ^ (Fintype.card V - 1) * u xM := by ring
    _ ≤ u x := hkey

end Apriori

section Generator

/-- **The facts about a generator `g` (with `g' = gd`) that the existence proof consumes**
(kb 0034): its derivative on `(0,∞)`, `C¹` of `g'` there, strict unimodality, `g ≥ 0`, and an
explicit cap on its sublevel sets — the paper's `R_max` is `capR(𝓛₀/(w_min λ_min))`. Inhabited by
`logSqFlowGenerator` and `sqFlowGenerator`. -/
structure FlowGenerator (g gd : ℝ → ℝ) where
  /-- The cap on the sublevel sets of `g`, as a formula in the level. -/
  capR : ℝ → ℝ
  /-- `g' = gd` on `(0,∞)`. -/
  hasDerivAt : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y
  /-- `g'` is `C¹` on `(0,∞)`. -/
  contDiffAt : ∀ y : ℝ, 0 < y → ContDiffAt ℝ 1 gd y
  /-- `sign g'(x) = sign(x − 1)`. -/
  unimodal : StrictlyUnimodal gd
  /-- `g ≥ 0`. -/
  nonneg : ∀ y : ℝ, 0 ≤ g y
  /-- `capR ≥ 1`. -/
  one_le_capR : ∀ C : ℝ, 1 ≤ capR C
  /-- `g(y) ≤ C` forces `y ≤ capR C`. -/
  le_capR : ∀ C y : ℝ, 0 < y → g y ≤ C → y ≤ capR C

variable {V : Type*} [Fintype V]

/-- **The ratio cap** (`proofs.tex:904`): `𝓛 ≤ L₀` forces `r ≤ R_max := capR(L₀/(w_min λ_min))`
at every state. -/
theorem FlowGenerator.ratio_le {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf u : V → ℝ} {lamMin wmin L0 : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hL : loss K lam (fun x => lam x * wf x) u g ≤ L0) (x : V) :
    ratio K lam u x ≤ G.capR (L0 / (wmin * lamMin)) := by
  refine G.le_capR _ _ (ratio_pos hinv hK hlam hu x) ?_
  have hterm : lam x * wf x * g (ratio K lam u x) ≤ L0 := by
    refine le_trans ?_ hL
    exact Finset.single_le_sum (f := fun z => lam z * wf z * g (ratio K lam u z))
      (fun z _ => mul_nonneg (mul_nonneg (hlam z).le (le_trans hwmin.le (hw z))) (G.nonneg _))
      (Finset.mem_univ x)
  have hlow : wmin * lamMin * g (ratio K lam u x) ≤ lam x * wf x * g (ratio K lam u x) := by
    refine mul_le_mul_of_nonneg_right ?_ (G.nonneg _)
    rw [mul_comm wmin]
    exact mul_le_mul (hlmin x) (hw x) hwmin.le (hlam x).le
  rw [le_div_iff₀ (mul_pos hwmin hlmin0), mul_comm]
  linarith

/-- **`u_min := m₀ (λ_min p_min / R_max)^{#𝒮̂−1}`** (`proofs.tex:905`), with `R` standing for
`R_max`. -/
noncomputable def uFloor (V : Type*) [Fintype V] (R lamMin pmin m0 : ℝ) : ℝ :=
  m0 * (lamMin * pmin / R) ^ (Fintype.card V - 1)

/-- **The static floor** (`proofs.tex:904–905`): loss at most `L₀` and mass at least `m₀` give
`u ≥ u_min` at every state, with `R_max = capR(L₀/(w_min λ_min))`. -/
theorem FlowGenerator.floor {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf u : V → ℝ} {lamMin pmin wmin L0 m0 : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hL : loss K lam (fun x => lam x * wf x) u g ≤ L0)
    (hm0 : m0 ≤ Graph.meanL2 lam u) (x : V) :
    uFloor V (G.capR (L0 / (wmin * lamMin))) lamMin pmin m0 ≤ u x := by
  set R := G.capR (L0 / (wmin * lamMin)) with hRdef
  have hR1 : 1 ≤ R := G.one_le_capR _
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hlmin1 : lamMin ≤ 1 := by
    refine le_trans (hlmin x) ?_
    rw [← htot]
    exact Finset.single_le_sum (f := lam) (fun i _ => (hlam i).le) (Finset.mem_univ x)
  have hc0 : 0 < lamMin * pmin / R := by positivity
  have hc1 : lamMin * pmin / R ≤ 1 := by
    rw [div_le_one hR0]
    calc lamMin * pmin ≤ 1 * 1 := mul_le_mul hlmin1 hpmin1 hpmin0.le zero_le_one
      _ = 1 := one_mul 1
      _ ≤ R := hR1
  have hr := G.ratio_le hinv hK hlam hu hlmin hlmin0 hwmin hw hL
  exact floor_of_edge_drop hlam htot hu hcross hc0 hc1
    (fun y z hyz => edge_drop_of_ratio_le hK hlam htot hu hlmin hlmin0 hpmin0 hR0 hr hyz) hm0 x

end Generator

/-! ### Cauchy–Lipschitz, global form -/

section Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Global existence for a bounded, globally Lipschitz autonomous field on a Banach space:
Picard–Lindelöf on `[−(n+1), n+1]` for every `n`, glued by uniqueness. Not a paper statement. -/
theorem exists_forall_hasDerivAt_of_lipschitzWith {f : E → E} {L : ℝ≥0} {M : ℝ≥0}
    (hf : LipschitzWith L f) (hM : ∀ x, ‖f x‖ ≤ M) (x₀ : E) :
    ∃ α : ℝ → E, α 0 = x₀ ∧ ∀ t, HasDerivAt α (f (α t)) t := by
  -- a solution on `[−(n+1), n+1]`
  have hloc : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        HasDerivWithinAt α (f (α t)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t := by
    intro n
    have hT : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have h0 : (0 : ℝ) ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := ⟨by linarith, hT⟩
    have hpl : IsPicardLindelof (fun _ => f) (⟨0, h0⟩ : Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) x₀
        (M * ⟨(n : ℝ) + 1, hT⟩) 0 M L := by
      refine ⟨fun _ _ => hf.lipschitzOnWith, fun _ _ => continuousOn_const,
        fun _ _ x _ => hM x, ?_⟩
      simp only [NNReal.coe_mul, NNReal.coe_zero, sub_zero, zero_sub, neg_neg,
        max_self]
      exact le_rfl
    obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨α, hα0, hα⟩
  choose α hα0 hα using hloc
  -- any two agree on the smaller interval
  have hagree : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1), α m t = α n t := by
    intro m n hmn
    have hsub : Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1) ⊆ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact Icc_subset_Icc (by linarith) (by linarith)
    have hLip : ∀ t ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1),
        LipschitzOnWith L ((fun _ => f) t) ((fun _ => univ) t) := fun _ _ => hf.lipschitzOnWith
    have hm0 : (0 : ℝ) ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) := by
      have : (0 : ℝ) ≤ m := by positivity
      exact ⟨by linarith, by linarith⟩
    refine ODE_solution_unique_of_mem_Icc hLip hm0
      (fun t ht => (hα m t ht).continuousWithinAt)
      (fun t ht => (hα m t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (fun _ _ => mem_univ _)
      (fun t ht => ((hα n t (hsub ht)).mono hsub).continuousWithinAt)
      (fun t ht => (hα n t (hsub (Ioo_subset_Icc_self ht))).hasDerivAt
        (mem_of_superset (Icc_mem_nhds ht.1 ht.2) hsub))
      (fun _ _ => mem_univ _) (by rw [hα0, hα0])
  refine ⟨fun t => α ⌈|t|⌉₊ t, hα0 _, fun t => ?_⟩
  set N : ℕ := ⌈|t|⌉₊ + 1 with hN
  have hNt : |t| < (N : ℝ) := by
    rw [hN, Nat.cast_add, Nat.cast_one]
    linarith [Nat.le_ceil |t|]
  have hmem : t ∈ Ioo (-((N : ℝ) + 1)) ((N : ℝ) + 1) := by
    constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
  have hd : HasDerivAt (α N) (f (α N t)) t :=
    (hα N t (Ioo_subset_Icc_self hmem)).hasDerivAt (Icc_mem_nhds hmem.1 hmem.2)
  have hev : (fun s => α ⌈|s|⌉₊ s) =ᶠ[𝓝 t] α N := by
    have hball : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hball] with s hs
    have hsN : ⌈|s|⌉₊ ≤ N := by
      rw [hN]
      have : |s| ≤ |t| + 1 := by
        have := abs_sub_abs_le_abs_sub s t
        have h2 : |s - t| < 1 := abs_sub_lt_iff.2 ⟨by linarith [hs.2], by linarith [hs.1]⟩
        linarith
      calc ⌈|s|⌉₊ ≤ ⌈|t| + 1⌉₊ := Nat.ceil_mono this
        _ ≤ ⌈|t|⌉₊ + 1 := by
          rw [Nat.ceil_add_one (abs_nonneg t)]
    refine hagree _ _ hsN s ⟨?_, ?_⟩
    · linarith [neg_abs_le s, Nat.le_ceil |s|]
    · linarith [le_abs_self s, Nat.le_ceil |s|]
  have hval : (fun s => α ⌈|s|⌉₊ s) t = α N t := hev.eq_of_nhds
  rw [hval]
  exact hd.congr_of_eventuallyEq hev

end Global

/-! ### Existence -/

section Existence

variable {V : Type*} [Fintype V]

/-- `|max 0 (max p q)| ≤ e ↔ p ≤ e ∧ q ≤ e` for `e ≥ 0`: the bootstrap's window, unfolded. -/
theorem abs_max_zero_max_le_iff {p q e : ℝ} (he : 0 ≤ e) :
    |max 0 (max p q)| ≤ e ↔ p ≤ e ∧ q ≤ e := by
  rw [abs_of_nonneg (le_max_left _ _), max_le_iff, max_le_iff]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

/-- **`prop:no_distant_equilibrium`*(3)*, existence, for any `FlowGenerator`, with the paper's
floor** (`proofs.tex:900–907`): from `u₀ > 0` a gradient flow exists, and it stays at density at
least `u_min = m₀(λ_min p_min/R_max)^{#𝒮̂−1}`, `R_max = capR(𝓛₀/(w_min λ_min))`,
`𝓛₀ = 𝓛(u₀)`, `m₀ = Πu₀`, at every `t ≥ 0` and every state.

`K` need not be row-stochastic; irreducibility enters through `CrossingFloor K p_min`. -/
theorem FlowGenerator.exists_flow {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin pmin wmin : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) gd u ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x,
        uFloor V (G.capR (loss K lam (fun x => lam x * wf x) u0 g / (wmin * lamMin)))
          lamMin pmin (Graph.meanL2 lam u0) ≤ u t x := by
  haveI : Nonempty V := nonempty_of_total htot
  set nu : V → ℝ := fun x => lam x * wf x with hnudef
  have hnu : ∀ x, 0 < nu x := fun x => mul_pos (hlam x) (lt_of_lt_of_le hwmin (hw x))
  set L0 := loss K lam nu u0 g with hL0def
  set m0 := Graph.meanL2 lam u0 with hm0def
  set n0 := Graph.nrmL2 lam u0 with hn0def
  set R := G.capR (L0 / (wmin * lamMin)) with hRdef
  set um := uFloor V R lamMin pmin m0 with humdef
  have hm0pos : 0 < m0 :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (G.one_le_capR _)
  have hum0 : 0 < um := by
    simp only [humdef, uFloor]
    positivity
  set N := n0 / Real.sqrt lamMin with hNdef
  have hsqrt : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
  have hN0 : 0 ≤ N := div_nonneg (Graph.nrmL2_nonneg _ _) hsqrt.le
  set a := um / 2 with hadef
  set b := N + 2 * um with hbdef
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by linarith
  -- the static bounds
  have hstatic : ∀ v : V → ℝ, (∀ x, 0 < v x) → loss K lam nu v g ≤ L0 →
      m0 ≤ Graph.meanL2 lam v → Graph.nrmL2 lam v = n0 → ∀ x, um ≤ v x ∧ v x ≤ N := by
    intro v hv hL hm hn x
    refine ⟨G.floor hinv hK hlam htot hv hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hL hm x, ?_⟩
    have h1 := abs_le_nrmL2_div_sqrt hlmin0 hlmin v x
    rw [hn] at h1
    rw [hNdef, le_div_iff₀ hsqrt]
    nlinarith [le_abs_self (v x)]
  -- the clamped field
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_lossGrad (nu := nu) hinv hK hlam G.contDiffAt
    (V := V) (b := b) ha0
  set F : (V → ℝ) → (V → ℝ) := fun v => -lossGrad K lam nu gd (clampBox a b v) with hFdef
  have hFlip : LipschitzWith L F := by
    have h1 : LipschitzOnWith (L * 1) ((fun v => lossGrad K lam nu gd v) ∘ clampBox a b) univ :=
      hL.comp (lipschitzWith_clampBox a b).lipschitzOnWith (fun v _ => clampBox_mem hab v)
    rw [mul_one, lipschitzOnWith_univ] at h1
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [hFdef]
    simp only
    rw [dist_neg_neg]
    exact h1.dist_le_mul v w
  have hLc : ContinuousOn (fun v : V → ℝ => lossGrad K lam nu gd v) (densityBox V a b) :=
    hL.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_densityBox (V := V) a b).exists_bound_of_continuousOn hLc
  have hM : ∀ v, ‖F v‖ ≤ (⟨max C 0, le_max_right _ _⟩ : ℝ≥0) := by
    intro v
    rw [hFdef]
    simp only [norm_neg]
    exact (hC _ (clampBox_mem hab v)).trans (le_max_left _ _)
  obtain ⟨α, hα0, hα⟩ := exists_forall_hasDerivAt_of_lipschitzWith hFlip hM u0
  have hαx : ∀ t x, HasDerivAt (fun s => α s x) (F (α t) x) t :=
    fun t x => hasDerivAt_pi.1 (hα t) x
  have hcont : ∀ x, Continuous fun t => α t x :=
    fun x => continuous_iff_continuousAt.2 fun t => (hαx t x).continuousAt
  have hon_of_box : ∀ D : Set ℝ, (∀ s ∈ D, α s ∈ densityBox V a b) →
      IsGradientFlowOn K lam nu gd α D := by
    intro D hD s hs y
    have h := hαx s y
    rw [hFdef] at h
    simp only [Pi.neg_apply, clampBox_eq (hD s hs)] at h
    exact h
  -- the bootstrap
  have hkey := bootstrap_of_continuous
    (h := fun t x => max 0 (max (3 * um / 2 - α t x) (α t x - (N + um)))) (eps := um) hum0
    (fun x => continuous_const.max
      ((continuous_const.sub (hcont x)).max ((hcont x).sub continuous_const)))
    (fun x => by
      rw [abs_max_zero_max_le_iff (by linarith), hα0]
      obtain ⟨h1, h2⟩ := hstatic u0 hu0 le_rfl le_rfl rfl x
      constructor <;> linarith)
    (fun t ht hwin x => by
      have hbox : ∀ s ∈ Icc (0 : ℝ) t, α s ∈ densityBox V a b := by
        intro s hs
        refine mem_densityBox.2 fun y => ?_
        have h := (abs_max_zero_max_le_iff hum0.le).1 (hwin s hs y)
        constructor <;> linarith [h.1, h.2]
      have hon := hon_of_box _ hbox
      have hpos : ∀ s ∈ Icc (0 : ℝ) t, ∀ y, 0 < α s y :=
        fun s hs y => lt_of_lt_of_le ha0 ((mem_densityBox.1 (hbox s hs)) y).1
      have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
      have htmem : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
      have hLt : loss K lam nu (α t) g ≤ L0 := by
        have := loss_antitoneOn_of_on (convex_Icc 0 t) hinv hK hlam hpos G.hasDerivAt hon
          h0mem htmem ht
        simpa only [hα0] using this
      have hmt : m0 ≤ Graph.meanL2 lam (α t) := by
        have := mass_monotoneOn_of_on (convex_Icc 0 t) hinv hK hlam hpos hnu G.unimodal hon
          h0mem htmem ht
        simpa only [hα0] using this
      have hnt : Graph.nrmL2 lam (α t) = n0 := by
        have := nrmL2_eq_of_on (convex_Icc 0 t) hlam hpos hon h0mem htmem ht
        simpa only [hα0] using this
      obtain ⟨h1, h2⟩ := hstatic (α t) (hpos t htmem) hLt hmt hnt x
      rw [abs_max_zero_max_le_iff (by linarith)]
      constructor <;> linarith)
  have hboxAll : ∀ t : ℝ, 0 ≤ t → α t ∈ densityBox V a b ∧ ∀ x, um ≤ α t x := by
    intro t ht
    have h := fun x => (abs_max_zero_max_le_iff (by linarith)).1 (hkey t ht x)
    refine ⟨mem_densityBox.2 fun y => ?_, fun x => ?_⟩
    · constructor <;> linarith [(h y).1, (h y).2]
    · linarith [(h x).1]
  refine ⟨α, hα0, fun t ht x => ?_, fun t ht x => (hboxAll t ht).2 x⟩
  exact hon_of_box (Ici 0) (fun s hs => (hboxAll s hs).1) t ht x

end Existence

/-! ### Uniqueness -/

section Uniqueness

variable {V : Type*} [Fintype V]

/-- A curve continuous and positive on a compact set of times stays in a box `[a,b]^V`, `a > 0`. -/
theorem exists_densityBox_of_continuousOn [Nonempty V] {u : ℝ → V → ℝ} {S : Set ℝ}
    (hS : IsCompact S)
    (hc : ∀ x, ContinuousOn (fun s => u s x) S) (hpos : ∀ s ∈ S, ∀ x, 0 < u s x) :
    ∃ a b : ℝ, 0 < a ∧ ∀ s ∈ S, u s ∈ densityBox V a b := by
  rcases S.eq_empty_or_nonempty with hSe | hSn
  · exact ⟨1, 1, one_pos, fun s hs => by simp only [hSe, mem_empty_iff_false] at hs⟩
  have hmin : ∀ x, ∃ a : ℝ, 0 < a ∧ ∀ s ∈ S, a ≤ u s x := by
    intro x
    obtain ⟨s0, hs0, hmin0⟩ := hS.exists_isMinOn hSn (hc x)
    exact ⟨u s0 x, hpos s0 hs0 x, fun s hs => hmin0 hs⟩
  have hmax : ∀ x, ∃ b : ℝ, ∀ s ∈ S, u s x ≤ b := by
    intro x
    obtain ⟨s0, -, hmax0⟩ := hS.exists_isMaxOn hSn (hc x)
    exact ⟨u s0 x, fun s hs => hmax0 hs⟩
  choose aF haF hle using hmin
  choose bF hbF using hmax
  refine ⟨Finset.univ.inf' Finset.univ_nonempty aF, Finset.univ.sup' Finset.univ_nonempty bF,
    (Finset.lt_inf'_iff _).2 fun x _ => haF x, fun s hs => mem_densityBox.2 fun x => ⟨?_, ?_⟩⟩
  · exact (Finset.inf'_le _ (Finset.mem_univ x)).trans (hle x s hs)
  · exact (hbF x s hs).trans (Finset.le_sup' _ (Finset.mem_univ x))

omit [Fintype V] in
/-- Boxes are monotone in their bounds. -/
theorem densityBox_mono {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    densityBox V a b ⊆ densityBox V a' b' :=
  fun _ hu => mem_densityBox.2 fun x =>
    ⟨ha.trans ((mem_densityBox.1 hu) x).1, ((mem_densityBox.1 hu) x).2.trans hb⟩

/-- **`prop:no_distant_equilibrium`*(3)*, uniqueness** (`proofs.tex:900`, "has a unique … solution
in `𝒰`"): two gradient flows positive on `[0,∞)` with the same initial density agree on `[0,∞)`.
Any `g'` that is `C¹` on `(0,∞)`; only `λ`-invariance, `K ≥ 0` and `λ > 0` are used — no
irreducibility, no normalization, no weight bound. -/
theorem isGradientFlow_unique {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hgd : ∀ y : ℝ, 0 < y → ContDiffAt ℝ 1 gd y) {u v : ℝ → V → ℝ}
    (hu : IsGradientFlow K lam nu gd u) (hv : IsGradientFlow K lam nu gd v)
    (hupos : ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x) (hvpos : ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x)
    (h0 : u 0 = v 0) : ∀ t : ℝ, 0 ≤ t → u t = v t := by
  intro T hT
  rcases isEmpty_or_nonempty V with hV | hV
  · funext x; exact isEmptyElim x
  have hu' := (isGradientFlow_iff K lam nu gd u).1 hu
  have hv' := (isGradientFlow_iff K lam nu gd v).1 hv
  obtain ⟨a1, b1, ha1, hb1⟩ := exists_densityBox_of_continuousOn (V := V) (u := u) isCompact_Icc
    (fun x s hs => (hu s hs.1 x).continuousAt.continuousWithinAt) (fun s hs => hupos s hs.1)
  obtain ⟨a2, b2, ha2, hb2⟩ := exists_densityBox_of_continuousOn (V := V) (u := v) isCompact_Icc
    (fun x s hs => (hv s hs.1 x).continuousAt.continuousWithinAt) (fun s hs => hvpos s hs.1)
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_lossGrad (nu := nu) hinv hK hlam hgd
    (V := V) (b := max b1 b2) (lt_min ha1 ha2)
  have hLn : LipschitzOnWith L (fun w : V → ℝ => fun x => -lossGrad K lam nu gd w x)
      (densityBox V (min a1 a2) (max b1 b2)) := by
    refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_
    show dist (-lossGrad K lam nu gd w) (-lossGrad K lam nu gd w') ≤ _
    rw [dist_neg_neg]
    exact hL.dist_le_mul w hw w' hw'
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ w => fun x => -lossGrad K lam nu gd w x)
    (s := fun _ => densityBox V (min a1 a2) (max b1 b2)) (K := L) (a := 0) (b := T)
    (fun _ _ => hLn)
    (fun s hs => (hu' s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hu' s hs.1).hasDerivWithinAt)
    (fun s hs => densityBox_mono (min_le_left _ _) (le_max_left _ _)
      (hb1 s (Ico_subset_Icc_self hs)))
    (fun s hs => (hv' s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hv' s hs.1).hasDerivWithinAt)
    (fun s hs => densityBox_mono (min_le_right _ _) (le_max_right _ _)
      (hb2 s (Ico_subset_Icc_self hs)))
    h0
  exact heq ⟨hT, le_rfl⟩

end Uniqueness

/-! ### The two generators of item *(3)* -/

section Instances

/-- `g(y) = (y − 1)²`, the second generator of item *(3)*. -/
noncomputable def sqGen (y : ℝ) : ℝ := (y - 1) ^ 2

/-- **`g = (log x)²` is a `FlowGenerator`**, with `R_max = e^{max(1,√C)}` — the paper's
`e^M`, `M = max(1, √(𝓛₀/(w_min λ_min)))`. -/
noncomputable def logSqFlowGenerator : FlowGenerator logSq logSqDeriv where
  capR C := Real.exp (max 1 (Real.sqrt C))
  hasDerivAt _ hy := hasDerivAt_logSq hy
  contDiffAt y hy := by
    show ContDiffAt ℝ 1 (fun x : ℝ => 2 * Real.log x / x) y
    exact (contDiffAt_const.mul (Real.contDiffAt_log.2 hy.ne')).div contDiffAt_id hy.ne'
  unimodal := logSqDeriv_strictlyUnimodal
  nonneg := logSq_nonneg
  one_le_capR C := Real.one_le_exp (le_trans zero_le_one (le_max_left _ _))
  le_capR C y hy hg := by
    rcases le_or_gt y 1 with h1 | h1
    · exact h1.trans (Real.one_le_exp (le_trans zero_le_one (le_max_left _ _)))
    · have hlog : Real.log y ≤ Real.sqrt C := by
        have := Real.abs_le_sqrt (show Real.log y ^ 2 ≤ C from hg)
        exact (le_abs_self _).trans this
      calc y = Real.exp (Real.log y) := (Real.exp_log hy).symm
        _ ≤ Real.exp (max 1 (Real.sqrt C)) :=
          Real.exp_le_exp.2 (hlog.trans (le_max_right _ _))

/-- **`g = (x − 1)²` is a `FlowGenerator`**, with `R_max = 1 + √C` — the paper's. -/
noncomputable def sqFlowGenerator : FlowGenerator sqGen (fun x : ℝ => 2 * (x - 1)) where
  capR C := 1 + Real.sqrt C
  hasDerivAt y _ := by
    have h := ((hasDerivAt_id y).sub_const 1).fun_pow 2
    have hv : (2 : ℕ) * (id y - 1) ^ (2 - 1) * 1 = 2 * (y - 1) := by
      simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    rw [hv] at h
    exact h
  contDiffAt _ _ := contDiffAt_const.mul (contDiffAt_id.sub contDiffAt_const)
  unimodal := strictlyUnimodal_sqDeriv
  nonneg _ := sq_nonneg _
  one_le_capR C := le_add_of_nonneg_right (Real.sqrt_nonneg C)
  le_capR C y _ hg := by
    have := Real.abs_le_sqrt (show (y - 1) ^ 2 ≤ C from hg)
    linarith [le_abs_self (y - 1)]

/-- On `g = (log x)²` the floor `u_min` is `BoundaryBlowup.uMin`, the constant `flow_pos_of_pos`
already delivers: `λ_min p_min/e^M = λ_min p_min e^{−M}`. -/
theorem uFloor_logSq_eq_uMin (V : Type*) [Fintype V] (lamMin pmin wmin L0 m0 : ℝ) :
    uFloor V (logSqFlowGenerator.capR (L0 / (wmin * lamMin))) lamMin pmin m0
      = uMin V lamMin pmin wmin L0 m0 := by
  simp only [uFloor, uMin, edgeDrop, ratioCap, logSqFlowGenerator, Real.exp_neg, div_eq_mul_inv]

end Instances

/-! ### Item *(3)*, existence and uniqueness, assembled -/

section Headline

variable {V : Type*} [Fintype V]

/-- **`prop:no_distant_equilibrium`*(3)*, existence and uniqueness, for any `FlowGenerator`**, on
a finite irreducible kernel with a positive invariant probability: from any `u₀ > 0` the gradient
flow has a solution positive on `[0,∞)`, and every such solution agrees with it on `[0,∞)`.
`λ_min` and `p_min` are taken inside the proof. -/
theorem FlowGenerator.existsUnique_flow {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hreach : ∀ x y : V, Relation.ReflTransGen (fun a b => 0 < K a b) x y)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) gd u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ∀ v : ℝ → V → ℝ, v 0 = u0 → IsGradientFlow K lam (fun x => lam x * wf x) gd v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t := by
  haveI : Nonempty V := nonempty_of_total htot
  obtain ⟨xm, -, hxm⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  obtain ⟨pmin, hp0, hp1, hp⟩ := exists_edgeFloor K
  have hcross : CrossingFloor K pmin := crossingFloor_of_reach hreach hp
  obtain ⟨u, hu0', hflow, hfloor⟩ := G.exists_flow hinv hK hlam htot
    (lamMin := lam xm) (fun x => hxm x (Finset.mem_univ x)) (hlam xm) hp0 hp1 hcross hwmin hw hu0
  have hm0 : 0 < Graph.meanL2 lam u0 :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  have hR0 : 0 < G.capR (loss K lam (fun x => lam x * wf x) u0 g / (wmin * lam xm)) :=
    lt_of_lt_of_le one_pos (G.one_le_capR _)
  have hfl0 : 0 < uFloor V (G.capR (loss K lam (fun x => lam x * wf x) u0 g / (wmin * lam xm)))
      (lam xm) pmin (Graph.meanL2 lam u0) := by
    have := hlam xm
    simp only [uFloor]
    positivity
  have hpos : ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x := fun t ht x => hfl0.trans_le (hfloor t ht x)
  refine ⟨u, hu0', hflow, hpos, fun v hv0 hv hvpos t ht => ?_⟩
  exact isGradientFlow_unique hinv hK hlam G.contDiffAt hv hflow hvpos hpos
    (hv0.trans hu0'.symm) t ht

/-- **`prop:no_distant_equilibrium`*(3)*, existence and uniqueness, `g = (log x)²`**, on a
finite irreducible kernel: `FlowGenerator.existsUnique_flow` at `logSqFlowGenerator`. -/
theorem existsUnique_flow_logSq {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hreach : ∀ x y : V, Relation.ReflTransGen (fun a b => 0 < K a b) x y)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ∀ v : ℝ → V → ℝ, v 0 = u0 → IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t :=
  logSqFlowGenerator.existsUnique_flow hinv hK hlam htot hreach hwmin hw hu0

/-- **`prop:no_distant_equilibrium`*(3)*, existence and uniqueness, `g = (x − 1)²`**, on a
finite irreducible kernel: `FlowGenerator.existsUnique_flow` at `sqFlowGenerator`. -/
theorem existsUnique_flow_sq {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hreach : ∀ x y : V, Relation.ReflTransGen (fun a b => 0 < K a b) x y)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ,
      u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ∀ v : ℝ → V → ℝ, v 0 = u0 →
          IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t :=
  sqFlowGenerator.existsUnique_flow hinv hK hlam htot hreach hwmin hw hu0

/-- **Ergodicity, in the reading the paper's proof uses**: every non-negative `K`-invariant
vector is a scalar multiple of `λ`. -/
def UniqueInvariant (K : V → V → ℝ) (lam : V → ℝ) : Prop :=
  ∀ m : V → ℝ, (∀ x, 0 ≤ m x) → Invariant K m → ∃ c : ℝ, ∀ x, m x = c * lam x

/-- **Ergodicity gives irreducibility** (`proofs.tex:900`, "The chain `T` is irreducible: …"):
the states accessible from one state carry the invariant measure `𝟏_Cλ`, which ergodicity forces
to be a multiple of `λ`, hence `C` is everything. Row-stochasticity is used for `T(x→C) = 1` on
`C`, as in the paper. -/
theorem reach_of_uniqueInvariant {K : V → V → ℝ} {lam : V → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (herg : UniqueInvariant K lam) :
    ∀ x y : V, Relation.ReflTransGen (fun a b => 0 < K a b) x y := by
  classical
  intro x0 y0
  by_contra hne
  set C : Finset V :=
    Finset.univ.filter (fun y => Relation.ReflTransGen (fun a b => 0 < K a b) x0 y) with hCdef
  have hmemC : ∀ y, y ∈ C ↔ Relation.ReflTransGen (fun a b => 0 < K a b) x0 y := by
    intro y; simp only [hCdef, Finset.mem_filter, Finset.mem_univ, true_and]
  have hx0 : x0 ∈ C := (hmemC x0).2 Relation.ReflTransGen.refl
  have hy0 : y0 ∉ C := fun h => hne ((hmemC y0).1 h)
  -- `C` is closed
  have hclosed : ∀ z ∈ C, ∀ w, w ∉ C → K z w = 0 := by
    intro z hz w hw
    by_contra hK0
    exact hw ((hmemC w).2 (((hmemC z).1 hz).tail (lt_of_le_of_ne (hK z w) (Ne.symm hK0))))
  -- rows inside `C` sum to one on `C`
  have hrowC : ∀ z ∈ C, ∑ w ∈ C, K z w = 1 := by
    intro z hz
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ C) (K z)
    have hout : ∑ w ∈ Finset.univ.filter (fun w => w ∉ C), K z w = 0 :=
      Finset.sum_eq_zero fun w hw => hclosed z hz w (Finset.mem_filter.1 hw).2
    have hin : Finset.univ.filter (fun w => w ∈ C) = C := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hout, add_zero, hin, hrow z] at hsplit
    exact hsplit
  -- no mass enters `C` from outside
  have hnoin : ∀ x, x ∉ C → ∀ w ∈ C, K x w = 0 := by
    have hmass : ∑ w ∈ C, lam w = ∑ x, lam x * ∑ w ∈ C, K x w := by
      calc ∑ w ∈ C, lam w = ∑ w ∈ C, ∑ x, lam x * K x w :=
            Finset.sum_congr rfl fun w _ => (hinv w).symm
        _ = ∑ x, ∑ w ∈ C, lam x * K x w := Finset.sum_comm
        _ = ∑ x, lam x * ∑ w ∈ C, K x w :=
            Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x ∈ C)
      (fun x => lam x * ∑ w ∈ C, K x w)
    have hin : ∑ x ∈ Finset.univ.filter (fun x => x ∈ C), lam x * ∑ w ∈ C, K x w
        = ∑ w ∈ C, lam w := by
      have hf : Finset.univ.filter (fun x => x ∈ C) = C := by
        ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hf]
      exact Finset.sum_congr rfl fun x hx => by rw [hrowC x hx, mul_one]
    rw [hin, ← hmass] at hsplit
    have hzero : ∑ x ∈ Finset.univ.filter (fun x => x ∉ C), lam x * ∑ w ∈ C, K x w = 0 := by
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (hlam x).le
      (Finset.sum_nonneg fun w _ => hK x w))).1 hzero
    intro x hx w hw
    have h1 := hterm x (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)
    have h2 : ∑ w ∈ C, K x w = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h (hlam x).ne'
      · exact h
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hK x w)).1 h2 w hw
  -- the restriction of `λ` to `C` is invariant
  set m : V → ℝ := fun x => if x ∈ C then lam x else 0 with hmdef
  have hmnn : ∀ x, 0 ≤ m x := fun x => by
    simp only [hmdef]; split_ifs <;> [exact (hlam x).le; exact le_rfl]
  have hminv : Invariant K m := by
    intro w
    have hsum : ∑ x, m x * K x w = ∑ x, (if x ∈ C then lam x * K x w else 0) :=
      Finset.sum_congr rfl fun x _ => by simp only [hmdef]; split_ifs <;> ring
    rw [hsum]
    by_cases hw : w ∈ C
    · have : ∀ x, (if x ∈ C then lam x * K x w else 0) = lam x * K x w := by
        intro x; split_ifs with hx
        · rfl
        · rw [hnoin x hx w hw, mul_zero]
      rw [Finset.sum_congr rfl fun x _ => this x, hinv w]
      simp only [hmdef, if_pos hw]
    · have : ∀ x, (if x ∈ C then lam x * K x w else 0) = 0 := by
        intro x; split_ifs with hx
        · rw [hclosed x hx w hw, mul_zero]
        · rfl
      rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_const_zero]
      simp only [hmdef, if_neg hw]
  obtain ⟨c, hc⟩ := herg m hmnn hminv
  have hc1 : c = 1 := by
    have h := hc x0
    simp only [hmdef, if_pos hx0] at h
    have hl := (hlam x0).ne'
    field_simp at h
    linarith
  have h := hc y0
  simp only [hmdef, if_neg hy0, hc1, one_mul] at h
  exact (hlam y0).ne' h.symm

/-- **`prop:no_distant_equilibrium`*(3)*, existence and uniqueness, `g = (log x)²`, in the
paper's hypotheses**: `(𝒮̂, λ, T)` ergodic on a finite state space, `λ` a positive probability,
`ν = wλ` with `w ≥ w_min > 0`, `g = (log x)²` — the gradient flow from any `u₀ > 0` exists,
stays positive, and is unique among positive solutions. -/
theorem existsUnique_flow_logSq_of_ergodic {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ∀ v : ℝ → V → ℝ, v 0 = u0 → IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t :=
  existsUnique_flow_logSq hinv hK hlam htot (reach_of_uniqueInvariant hK hrow hinv hlam herg)
    hwmin hw hu0

/-- **`prop:no_distant_equilibrium`*(3)*, existence and uniqueness, `g = (x − 1)²`, in the
paper's hypotheses**: as `existsUnique_flow_logSq_of_ergodic`. -/
theorem existsUnique_flow_sq_of_ergodic {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ,
      u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ∀ v : ℝ → V → ℝ, v 0 = u0 →
          IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t :=
  existsUnique_flow_sq hinv hK hlam htot (reach_of_uniqueInvariant hK hrow hinv hlam herg)
    hwmin hw hu0

end Headline

/-! ### On the loop closure of a finite marked graph, and the convergence clause from `u₀` -/

section GraphSetting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Graph.MarkedGraph V}
  {B : Graph.BackwardPolicy G}

/-- **`prop:no_distant_equilibrium`*(3)*, existence and uniqueness, `g = (log x)²`, on the loop
closure of a finite path-connected marked graph** — the setting of
`no_distant_equilibrium_three_converges`; irreducibility is `breach_all`. -/
theorem existsUnique_flow_logSq_graph {lam wf : V → ℝ} {wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ∀ v : ℝ → V → ℝ, v 0 = u0 → IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t :=
  existsUnique_flow_logSq (invariant_of_isInvProb hl) B.phat_nonneg (hl.pos hpc hpos) hl.total
    (fun x y => B.breach_all hpc hpos x y) hwmin hw hu0

/-- **`prop:no_distant_equilibrium`*(3)*, existence and uniqueness, `g = (x − 1)²`, on the loop
closure of a finite path-connected marked graph.** -/
theorem existsUnique_flow_sq_graph {lam wf : V → ℝ} {wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ,
      u 0 = u0 ∧ IsGradientFlow B.phat lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ∀ v : ℝ → V → ℝ, v 0 = u0 →
          IsGradientFlow B.phat lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t :=
  existsUnique_flow_sq (invariant_of_isInvProb hl) B.phat_nonneg (hl.pos hpc hpos) hl.total
    (fun x y => B.breach_all hpc hpos x y) hwmin hw hu0

/-- **`prop:no_distant_equilibrium`*(3)*, from `u₀` alone, for `g = (log x)²` on the loop closure
of a finite path-connected marked graph**: the gradient
flow from any `μ₀ ∼ λ` has a unique positive solution, and it converges to the balanced flow of
its sphere `‖·‖_{L²(λ)} = ‖u₀‖_{L²(λ)}` — the constant density `‖u₀‖_{L²(λ)}`, balanced, and the
only positive balanced density on that sphere. No flow hypothesis:
`no_distant_equilibrium_three_converges` applied to the solution `existsUnique_flow_logSq_graph`
provides. -/
theorem no_distant_equilibrium_three_of_init {lam wf : V → ℝ} {wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ (∀ v : ℝ → V → ℝ, v 0 = u0 →
          IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t)
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam u0)
      ∧ Balanced B.phat lam (fun _ => Graph.nrmL2 lam u0)
      ∧ ∀ w : V → ℝ, (∀ x, 0 < w x) → Balanced B.phat lam w →
          Graph.nrmL2 lam w = Graph.nrmL2 lam u0 → w = fun _ => Graph.nrmL2 lam u0 := by
  obtain ⟨u, hu0', hflow, hupos, huniq⟩ := existsUnique_flow_logSq_graph hpc hpos hl hwmin hw hu0
  have hu0'' : ∀ x, 0 < u 0 x := fun x => by rw [hu0']; exact hu0 x
  obtain ⟨hconv, hbal, -, hone⟩ :=
    no_distant_equilibrium_three_converges hpc hpos hl hwmin hw hu0'' hflow
  rw [hu0'] at hconv hbal hone
  exact ⟨u, hu0', hflow, hupos, huniq, hconv, hbal, hone⟩

end GraphSetting

/-! ### Inhabitation -/

section Checks

/-- The two-state chain is ergodic in the sense of `UniqueInvariant`: an invariant `m` has
`m(0) = m(1) = (m(0) + m(1))/2`. -/
theorem twoState_uniqueInvariant : UniqueInvariant twoStateK twoStateLam := by
  intro m _ hm
  refine ⟨2 * m 0, fun x => ?_⟩
  have h0 := hm 0
  have h1 := hm 1
  simp only [twoStateK, Fin.sum_univ_two] at h0 h1
  fin_cases x
  · simp only [twoStateLam, Fin.zero_eta]
    ring
  · simp only [twoStateLam, Fin.mk_one]
    linarith

/-- The two-state kernel is row-stochastic. -/
theorem twoStateK_row : ∀ x, ∑ y, twoStateK x y = 1 := fun _ => by
  simp only [twoStateK, Fin.sum_univ_two]
  norm_num

/-- **The two-state chain, `g = (log x)²`, from the non-balanced `u₀ = (3/2, 1/2)`**, through the
paper-hypothesis form `existsUnique_flow_logSq_of_ergodic`: a positive gradient flow exists.
`IsGradientFlow` and `UniqueInvariant` are inhabited off balance. -/
theorem twoState_flow_exists_check :
    ∃ u : ℝ → Fin 2 → ℝ, u 0 = blowupU
      ∧ IsGradientFlow twoStateK twoStateLam (fun x => twoStateLam x * 1) logSqDeriv u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ¬ Balanced twoStateK twoStateLam (u 0) := by
  obtain ⟨u, hu0, hflow, hpos, -⟩ := existsUnique_flow_logSq_of_ergodic (K := twoStateK)
    (lam := twoStateLam) (wf := fun _ => (1 : ℝ)) (wmin := 1)
    (fun _ _ => by norm_num [twoStateK]) twoStateK_row twoStateK_invariant twoStateLam_pos
    (by norm_num [twoStateLam, Fin.sum_univ_two]) twoState_uniqueInvariant
    one_pos (fun _ => le_rfl) blowupU_pos
  refine ⟨u, hu0, hflow, hpos, ?_⟩
  rw [hu0, ← ratio_eq_one_iff_balanced (fun y => mul_pos (twoStateLam_pos y) (blowupU_pos y))]
  intro h
  have h1 := h 1
  rw [twoState_blowup_ratio.2] at h1
  norm_num at h1

/-- **The two-state chain, `g = (x − 1)²`, from the non-balanced `u₀ = (3/2, 1/2)`**, through
`existsUnique_flow_sq_of_ergodic`: a positive gradient flow exists. -/
theorem twoState_flow_exists_check_sq :
    ∃ u : ℝ → Fin 2 → ℝ, u 0 = blowupU
      ∧ IsGradientFlow twoStateK twoStateLam (fun x => twoStateLam x * 1) (fun x => 2 * (x - 1)) u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ¬ Balanced twoStateK twoStateLam (u 0) := by
  obtain ⟨u, hu0, hflow, hpos, -⟩ := existsUnique_flow_sq_of_ergodic (K := twoStateK)
    (lam := twoStateLam) (wf := fun _ => (1 : ℝ)) (wmin := 1)
    (fun _ _ => by norm_num [twoStateK]) twoStateK_row twoStateK_invariant twoStateLam_pos
    (by norm_num [twoStateLam, Fin.sum_univ_two]) twoState_uniqueInvariant
    one_pos (fun _ => le_rfl) blowupU_pos
  refine ⟨u, hu0, hflow, hpos, ?_⟩
  rw [hu0, ← ratio_eq_one_iff_balanced (fun y => mul_pos (twoStateLam_pos y) (blowupU_pos y))]
  intro h
  have h1 := h 1
  rw [twoState_blowup_ratio.2] at h1
  norm_num at h1

open Graph.CycleExample in
/-- **The five-vertex cycle of `rem:cycle_no_stalemate`, at `p = 1/2`, from the over-inflated
density `uInfl 2`** (`r(s₀) = 2`): the flow exists, is unique, and converges to the balanced
flow of its sphere — `no_distant_equilibrium_three_converges` applied to a curve that exists. -/
theorem cycle_flow_converges_check :
    ∃ u : ℝ → Fin 5 → ℝ, u 0 = uInfl 2
      ∧ IsGradientFlow (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2))
          (fun x => lam (1 / 2) x * 1) logSqDeriv u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ¬ Balanced (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2)) (u 0)
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 (lam (1 / 2)) (uInfl 2)) := by
  obtain ⟨u, hu0, hflow, hpos, -, hconv, -, -⟩ := no_distant_equilibrium_three_of_init
    (G := cyc) (B := pol (p := 1 / 2) (by norm_num) (by norm_num)) (wf := fun _ => (1 : ℝ))
    (wmin := 1) pathConnected (positiveOnEdges _ _) (isInvProb _ _) one_pos (fun _ => le_rfl)
    (uInfl_pos (M := 2) (by norm_num))
  refine ⟨u, hu0, hflow, hpos, ?_, hconv⟩
  rw [hu0, ← ratio_eq_one_iff_balanced
    (fun y => mul_pos (lam_pos (p := 1 / 2) (by norm_num) y) (uInfl_pos (M := 2) (by norm_num) y))]
  intro h
  have h0 := h 0
  rw [ratio_src (by norm_num) (by norm_num) (by norm_num)] at h0
  norm_num at h0

end Checks

end GFNBounds.Balance
