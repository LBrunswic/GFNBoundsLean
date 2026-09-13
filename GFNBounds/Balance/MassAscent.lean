import GFNBounds.Balance.Flow
import GFNBounds.Graph.Universality

/-!
# The mass is the Lyapunov function: monotone ascent on the sphere, and the entry time

**`prop:no_distant_equilibrium`** **item *(2)***, its **Lyapunov half** — statement
`proofs.tex:791`, proof `proofs.tex:807`; `GFNBounds/Balance/Flow.lean` proves the *first* half
(scale invariance and the invariant sphere) and discloses this one as missing. See SCOPE.
**`cor:global_lojasiewicz`** — statement `proofs.tex:875–886`, proof `proofs.tex:887–898`;
**both displays with two hypotheses discharged**, see `global_lojasiewicz_flow'`.
(The bold-backtick form of each label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (`prop:no_distant_equilibrium`*(2)*) **The inflation is the algorithm.** For fixed `ν = wλ` the
> loss is scale-invariant, so the gradient flow preserves `‖u_t‖_{L²(λ)}`, while by *(1)* the
> total mass `μ_t(𝒮̂)` strictly increases off balance: training is a monotone ascent of the mass
> on a sphere of `𝓜²(λ)`, whose unique maximizer (Cauchy–Schwarz) is the balanced flow. The
> circulation-inflating force is the mass component of the gradient, and it is extinguished
> exactly at flow-matching: no stalemate with the frozen-policy constraint can occur.

> (proof of *(2)*) For fixed `ν`, `r(cμ) = r(μ)` gives `𝓛_{g,ν}(cμ) = 𝓛_{g,ν}(μ)`, whence
> `0 = d/dc 𝓛(cμ)|_{c=1} = ⟨∇𝓛, μ⟩_{𝓜²(λ)} = ∫ Du dλ`: the gradient is orthogonal to the radial
> direction, so `d/dt ‖u_t‖²_{L²(λ)} = −2∫ Du dλ = 0`. Meanwhile `d/dt μ_t(𝒮̂) = −∫ D dλ > 0` off
> balance by *(1)*. On the sphere `‖u‖ = ‖u₀‖`, Cauchy–Schwarz gives `∫ u dλ ≤ ‖u‖_{L²(λ)}` with
> equality if and only if `u` is constant, i.e. `μ` is balanced: the mass is a strict Lyapunov
> function whose unique maximizer on the sphere is the balanced flow.

> (proof of *(3)*, the entry time, `proofs.tex:813`) […] while `sup|r−1| ≥ δ` one has
> `λ(|r−1| ≥ δ) ≥ λ_min`, so `d𝓛/dt = −‖D‖² ≤ −c(δ)²` with
> `c(δ) := w_min λ_min^{3/2} δ²/(2‖u₀‖)`: after time at most `𝓛(μ₀)/c(δ)²` all ratios are within
> `δ` of `1`. […] the rescaling `μ ↦ μ/m` changes the gradient field by the factor `1/m`, hence
> only the time scale.

## Why this file exists

`Flow.lean`'s SCOPE says it in as many words: *"Of item (2) only the first half is proved […]
the total mass strictly increases off balance, the mass is a strict Lyapunov function, and its
unique maximizer on the sphere is the balanced flow is **not** stated.
`MassIdentity.no_distant_equilibrium_one` has the ingredient (`∫ D dλ ≤ 0`, `= 0` iff balanced)
but the monotonicity and the maximizer are not assembled"*. They are assembled here, out of the two files
as they stand: the flow ODE differentiates the mass term by term (`hasDerivAt_mass_flow`), the
sign of `∫ D dλ` is `no_distant_equilibrium_one`, and the maximizer is Cauchy–Schwarz against
`𝟏` with its equality case (`mean_le_nrmL2_iff_const`).

The second half of the file serves `theo:training_speed_full`, which this file does **not**
certify: the crossover time `T₀ = 𝓛(μ₀)/c(δ₀)²` of `proofs.tex:928` is `entry_time` evaluated at
the paper's `δ₀`, and the homogeneity that turns the entry point's rescaling into a time change
is `lossGrad_smul` and `flow_rescale`. Assembling those into the theorem needs
`theo:local_convergence_full`, which is `closed` since 2026-09-12.

## What is proved

| | |
|---|---|
| `rnWeight` | `dν/dμ = ν/(λu)`, the weight `Flow.lossGrad` substitutes, named so the mass can be spoken of |
| `hasDerivAt_mass_flow` | `d/dt μ_t(𝒮̂) = −∫ D dλ` — the flow differentiates the mass state by state |
| `mass_monotoneOn`, `mass_monotone_flow` | **the monotone ascent**: `t ↦ μ_t(𝒮̂)` is monotone on any convex set of times where the trajectory is positive, hence on `[0,∞)`. `hasDerivAt_mass_flow` and `no_distant_equilibrium_one` ask positivity at **one** time, so the general form is available inside `BoundaryBlowup`'s continuation |
| `mass_deriv_pos_off_balance` | **strictly** increases off balance, which is the word the paper uses |
| `ipL2_sub_mean`, `mean_le_nrmL2_iff_const` | **the maximizer**: `∫u dλ ≤ ‖u‖_{L²(λ)}`, with equality iff `u` is constant — Cauchy–Schwarz against `𝟏` and its equality case |
| `balanced_const` | a constant density is balanced, on any kernel with an invariant `λ` |
| `const_of_balanced_graph` | its converse, **and it is ergodicity**: available on a path-connected marked graph through `Graph.eq_smul_invProb`, and false for an abstract `K`. See SCOPE |
| `mass_ascent_lyapunov` | item *(2)*'s sentences read together, for an abstract `K`, at every `t ≥ 0`: the sphere is preserved, the mass ascends, it is bounded by `‖u₀‖`, and the bound is attained only at a constant density, which is balanced |
| `mass_ascent_lyapunov_graph` | the same on a marked graph, where the bound is attained **exactly** at the balanced flows — the paper's "whose unique maximizer is the balanced flow", with the word *unique* earned |
| `loss_antitoneOn`, `loss_antitone_flow`, `lossVal_antitoneOn`, `lossVal_antitone_flow` | `𝓛` decreases along the flow — the fact `Flow.lean` carries as the hypothesis `hL0` — on any convex set of times where the trajectory is positive, hence on `[0,∞)`. `Flow.hasDerivAt_loss_flow_at` asks positivity at **one** time, which is what breaks the circularity in `BoundaryBlowup`'s continuation |
| `lossVal_eq_zero_iff_balanced` | `𝓛 = 0 ↔` balanced, for `g = (log x)²` and positive weights |
| `lojasiewicz_integrated_nonneg` | `lojasiewicz_integrated` with its positivity hypothesis removed; like it, every hypothesis ranges over `[0,∞)` |
| `global_lojasiewicz_flow'` | **`cor:global_lojasiewicz`** with `hL0` and `hpos` both discharged: `L₀` is literally `𝓛(μ₀)`, as in the paper |
| `ratio_smul`, `lossGrad_smul` | scale invariance of `r` and the homogeneity `D(cμ) = c^{-1}D(μ)` |
| `flow_rescale` | the rescaling `μ ↦ μ/c` is a time change by `c²` (`proofs.tex:813`) |
| `cDelta` | `c(δ) = w_min λ_min^{3/2}δ²/(2‖u₀‖)`, an explicit formula (`proofs.tex:813`) |
| `entry_time` | **after `𝓛(μ₀)/c(δ)²` every ratio is within `δ` of `1`** — item *(3)*'s entry time, which `theo:training_speed_full` reads at `δ₀` to get `T₀` |

## SCOPE (disclosed)

* **"Balanced ⇒ constant" is ergodicity, and it is not available for an abstract `K`.** The
  paper's item *(2)* concludes "whose unique maximizer (Cauchy–Schwarz) is the balanced flow",
  and the paper is entitled to it: `prop:no_distant_equilibrium` hypothesises `(𝒮̂, λ, T)`
  **ergodic**. This library's finite layer does not: `MassIdentity.lean` carries only
  `Invariant K lam`, which is strictly weaker, and under it the implication is **false** — take
  `K = Id` on two states, where every `λ` is invariant and every `u` is balanced, so the balanced
  set is all of `𝓜²(λ)` and not the constants. So the file states the two directions separately:
  `balanced_const` (constant ⇒ balanced) for any invariant `K`, and `const_of_balanced_graph`
  (balanced ⇒ constant) **only** on the loop closure of a path-connected marked graph with a
  backward policy positive on its edges, where it is `Graph.eq_smul_invProb`, i.e.
  `theo:universality_graphs`*(2)*'s uniqueness. `mass_ascent_lyapunov` is the abstract reading
  and stops at "the maximizer is the constant density"; `mass_ascent_lyapunov_graph` is the
  paper's, and names the balanced flow.
* **No existence theorem**, inherited from `Flow.lean`: every statement quantifies over a curve
  satisfying `IsGradientFlow`, and none produces one.
* **Finite state space**, inherited from the whole of `GFNBounds.Balance`.
* **The maximizer statement needs `u ≥ 0`, which the paper's `u = dμ/dλ` has and its sentence
  does not name.** `∫ u dλ ≤ ‖u‖_{L²(λ)}` holds for every `u`, but *equality iff constant* does
  not: at `u ≡ −1` the two sides are `−1` and `1`. `mean_le_nrmL2_iff_const` therefore carries
  `hv : ∀ x, 0 ≤ v x`. This is a gap in the sentence, not in the paper: densities are
  non-negative, and the flow's are positive.
* **`entry_time` is item *(3)*'s entry time, not item *(3)*.** The proposition's convergence half
  — the trajectory stays in a compact subset of the open sphere, LaSalle's principle, the
  `ω`-limit is the single balanced point — is **not** here. LaSalle needs `ω`-limit sets of an
  ODE with no solution theory in Mathlib v4.31.0, and the compactness step needs the boundary
  blow-up of `𝓛`, which is not stated anywhere in this library. What `entry_time` delivers is
  the *quantitative* sentence of the proof: after `𝓛(μ₀)/c(δ)²` all ratios are within `δ` of `1`.
* **`entry_time` concludes at a time `t₁ ≤ T₀`, not at `T₀`.** The paper says "after time at most
  `𝓛(μ₀)/c(δ)²` all ratios are within `δ`", which reads as a statement about every later time;
  the proof gives exactly one time in `[0, T₀]` at which it holds, because the argument is a
  contradiction against the loss budget and says nothing about what happens afterwards. Staying
  inside the band is `theo:local_convergence_full`'s job, and it is `closed`. The `∃ t₁ ∈ [0,T₀]`
  form is what the argument proves and what `theo:training_speed_full` consumes as the crossover.
  What the budget really bounds is the **total time spent off the band**, `T₀` being the loss
  divided by the burn rate `c(δ)²`; the flow may in principle leave the band and return, and only
  the local theorem forbids it. `entry_time` states the weakest form of this that the assembly
  needs, and states it unconditionally.
* **`theo:training_speed_full` is not certified here**, and the label is deliberately not in
  bold-backtick form: `flow_rescale`, `lossGrad_smul` and `entry_time` are three of its
  ingredients, and the theorem itself needs `theo:local_convergence_full`.
* **`global_lojasiewicz_flow'` drops two hypotheses and adds none.** `Flow.global_lojasiewicz_flow`
  carries `hL0 : ∀ t ≥ 0, 𝓛(μ_t) ≤ L₀` and `hpos : ∀ t ≥ 0, 0 < 𝓛(μ_t)`. The first is discharged
  by `lossVal_antitone_flow` with `L₀ := 𝓛(μ₀)` — which is what the paper writes — and the second
  by `lojasiewicz_integrated_nonneg`, which needs only `0 ≤ 𝓛(μ₀)`. It re-derives the statement
  rather than applying `global_lojasiewicz_flow`, because the route through
  `lojasiewicz_integrated_nonneg` is a different integration and not a specialization.
* **Every trajectory hypothesis of this file is ranged over `[0,∞)`.** `hu` reads
  `∀ t, 0 ≤ t → ∀ x, 0 < u t x` and `lojasiewicz_integrated_nonneg`'s `hderiv` reads
  `∀ t, 0 ≤ t → HasDerivAt L (L' t) t`; both read `∀ t` until 2026-09-13, which is kb `0022` and
  made them undischargeable from `BoundaryBlowup.flow_pos_graph`. Two conclusions moved with the
  hypothesis: `mass_ascent_lyapunov`'s three `∀ t` conjuncts and `mass_ascent_lyapunov_graph`'s
  one are now guarded by `0 ≤ t`, since positivity below `0` is exactly what is no longer
  assumed. Neither theorem is used anywhere in this library, at a negative time or otherwise.
* **`sorry`-free.** Nothing below is open. Graduated into the strict library on 2026-09-12.

## Hypothesis checklist — `prop:no_distant_equilibrium`*(2)*, the Lyapunov half

| paper hypothesis | here |
|---|---|
| `g` admissible, differentiable | ✗ **not carried**: `gd : ℝ → ℝ` opaque, as in `MassIdentity.lean` |
| `sign g'(x) = sign(x − 1)` for `x ≠ 1` | ✓ `StrictlyUnimodal gd`, and it is what makes the ascent strict |
| `(𝒮̂, λ, T)` **ergodic** | ⚠ **weakened to `Invariant K lam`** for the ascent, which does not use it; **carried in full** for the maximizer, in the marked-graph form `PathConnected` + `PositiveOnEdges` + `IsInvProb`. See SCOPE — the two are not interchangeable here |
| `𝒮̂` a general measurable space | ⚠ **finite** (`[Fintype V]`) |
| `λ` a probability | ✓ `htot : ∑ x, lam x = 1`, spent in Cauchy–Schwarz against `𝟏` |
| `ν = wλ` fixed | ✓ `nu` a fixed function; `rnWeight lam nu u` is `dν/dμ` |
| `dν/dμ > 0` `μ`-a.e. | ✓ derived from `hnu : ∀ x, 0 < nu x`, `hlam`, `hu` |
| `μ ∼ λ`, `u = dμ/dλ` | ✓ `hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x`, **discharged** from `0 < u₀` by `BoundaryBlowup.flow_pos_graph` |
| the gradient flow `μ̇ = −∇𝓛` | ✓ `IsGradientFlow`, hypothesised of a curve |
| the loss is scale-invariant, `‖u_t‖` preserved | ✓ **imported**, `Flow.nrmL2_const_of_flow` — not reproved |
| `d/dt μ_t(𝒮̂) = −∫ D dλ` | ✓ `hasDerivAt_mass_flow` |
| the mass **strictly increases** off balance | ✓ `mass_deriv_pos_off_balance` (the derivative), `mass_monotone_flow` (the ascent) |
| Cauchy–Schwarz: `∫u dλ ≤ ‖u‖`, equality iff `u` constant | ⚠ `mean_le_nrmL2_iff_const`, **with `u ≥ 0` added**. See SCOPE |
| the unique maximizer is **the balanced flow** | ⚠ **split**: `balanced_const` on any invariant `K`; the converse only on a marked graph (`const_of_balanced_graph`). See SCOPE |
| "no stalemate with the frozen-policy constraint" | ✗ not stated — it is the reading of the identity, and `rem:cycle_no_stalemate` is its instance |

## Hypothesis checklist — `prop:no_distant_equilibrium`*(3)*, the entry time only

| paper hypothesis | here |
|---|---|
| finite state space, `g = (log x)²`, `ν = wλ`, `w ≥ w_min > 0` | ✓ inherited from `Lojasiewicz.no_distant_equilibrium_three`, whose checklist governs |
| `λ_min := min_x λ(x)` | ⚠ a parameter `lamMin` with `∀ x, lamMin ≤ lam x`, `0 < lamMin` — inherited |
| `δ ∈ (0, ½]` | ✓ `hδ0`, `hδ1` |
| `c(δ) = w_min λ_min^{3/2}δ²/(2‖u₀‖)` | ✓ `cDelta`, an **explicit formula**; `λ_min^{3/2}` is `lamMin * √lamMin` |
| `‖u_t‖ = ‖u₀‖` on the sphere | ✓ **derived**, `Flow.nrmL2_const_of_flow`; not a hypothesis |
| `d𝓛/dt = −‖D‖²` | ✓ `Flow.hasDerivAt_loss_flow` |
| `λ(|r−1| ≥ δ) ≥ λ_min` while some ratio is far | ✓ `Finset.single_le_sum` over `farSet`, one term |
| "after time at most `𝓛(μ₀)/c(δ)²` all ratios are within `δ`" | ⚠ `∃ t₁ ∈ [0, 𝓛(μ₀)/c(δ)²]` with all ratios within `δ`. See SCOPE |
| the trajectory stays in a compact subset; LaSalle | ✗ not stated. See SCOPE |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

/-! ### The mass along the flow

`proofs.tex:807`: `d/dt μ_t(𝒮̂) = −∫ D dλ > 0` off balance. The mass `μ_t(𝒮̂) = ∫ u_t dλ` is
`Graph.meanL2 lam (u t)`, which is also the left-hand side of the Cauchy–Schwarz step below. -/

section MassAscent

variable {V : Type*} [Fintype V]

/-- **`dν/dμ = ν/(λu)`**, the Radon–Nikodym weight `Flow.lossGrad` substitutes for `w` — named
here because the mass identity of `MassIdentity.lean` is stated in `w`, and the flow's `w` is
this function of the flow. -/
noncomputable def rnWeight (lam nu u : V → ℝ) : V → ℝ := fun z => nu z / (lam z * u z)

theorem lossGrad_eq_lossGradDensity (K : V → V → ℝ) (lam nu : V → ℝ) (gd : ℝ → ℝ) (u : V → ℝ) :
    lossGrad K lam nu gd u = lossGradDensity K lam u (rnWeight lam nu u) gd := rfl

omit [Fintype V] in
/-- `dν/dμ > 0` wherever `ν`, `λ` and `u` are. -/
theorem rnWeight_pos {lam nu u : V → ℝ} (hlam : ∀ x, 0 < lam x) (hnu : ∀ x, 0 < nu x)
    (hu : ∀ x, 0 < u x) (x : V) : 0 < rnWeight lam nu u x :=
  div_pos (hnu x) (mul_pos (hlam x) (hu x))

/-- **`d/dt μ_t(𝒮̂) = −∫ D dλ`** (`proofs.tex:807`): along the gradient flow the total mass moves
at minus the mass of the gradient.

The flow is an ODE in `ℝ^V`, so the mass `∑_x λ(x)u_t(x)` differentiates state by state; the sum
of the velocities is `−∫ D dλ` by definition of `gradMass`. -/
theorem hasDerivAt_mass_flow {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd u) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Graph.meanL2 lam (u s))
      (-(gradMass K lam (u t) (rnWeight lam nu (u t)) gd)) t := by
  have hsum : HasDerivAt (fun s : ℝ => ∑ x, lam x * u s x)
      (∑ x, lam x * -lossGrad K lam nu gd (u t) x) t :=
    HasDerivAt.fun_sum fun x _ => (hflow t x).const_mul (lam x)
  have hval : (∑ x, lam x * -lossGrad K lam nu gd (u t) x)
      = -(gradMass K lam (u t) (rnWeight lam nu (u t)) gd) := by
    simp only [gradMass, lossGrad_eq_lossGradDensity, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hval] at hsum
  exact hsum

/-- **The mass strictly increases off balance** (`proofs.tex:791`, `:807`): its velocity
`−∫ D dλ` is positive wherever `μ_t` is not balanced.

This is the `≤ 0` and the `= 0 ↔ balanced` conjuncts of `MassIdentity.
no_distant_equilibrium_one` read together, at the flow's own weight `dν/dμ = ν/(λu_t)`. -/
theorem mass_deriv_pos_off_balance {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hnu : ∀ x, 0 < nu x) (hg : StrictlyUnimodal gd)
    (hbal : ¬ Balanced K lam u) :
    0 < -(gradMass K lam u (rnWeight lam nu u) gd) := by
  obtain ⟨-, hle, hiff⟩ := no_distant_equilibrium_one hinv hK hlam hu
    (rnWeight_pos hlam hnu hu) hg
  have hne : gradMass K lam u (rnWeight lam nu u) gd ≠ 0 := fun h => hbal (hiff.mp h)
  exact neg_pos.mpr (lt_of_le_of_ne hle hne)

/-- **The mass ascends, on any convex set of times where the trajectory is positive**
(`proofs.tex:791`).

`hasDerivAt_mass_flow` and `no_distant_equilibrium_one` each ask positivity **at one time only**,
so the ascent is available on the bootstrap window `[0,t]` of a continuation and not merely on a
trajectory already known to be positive: that is what
`BoundaryBlowup.flow_pos_of_pos` consumes, and it is why this and not
`mass_monotone_flow` is the primitive. -/
theorem mass_monotoneOn {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    {D : Set ℝ} (hD : Convex ℝ D)
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hupos : ∀ s ∈ D, ∀ x, 0 < u s x) (hnu : ∀ x, 0 < nu x) (hg : StrictlyUnimodal gd)
    (hflow : IsGradientFlow K lam nu gd u) :
    MonotoneOn (fun s : ℝ => Graph.meanL2 lam (u s)) D := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun z : ℝ => Graph.meanL2 lam (u z))
      (-(gradMass K lam (u s) (rnWeight lam nu (u s)) gd)) s := hasDerivAt_mass_flow hflow
  refine monotoneOn_of_deriv_nonneg hD
    (fun s _ => ((hderiv s).continuousAt).continuousWithinAt)
    (fun s _ => ((hderiv s).differentiableAt).differentiableWithinAt) fun s hs => ?_
  rw [(hderiv s).deriv]
  obtain ⟨-, hle, -⟩ := no_distant_equilibrium_one hinv hK hlam
    (hupos s (interior_subset hs)) (rnWeight_pos hlam hnu (hupos s (interior_subset hs))) hg
  simpa using neg_nonneg.mpr hle

/-- **The monotone ascent** (`proofs.tex:791`: "training is a monotone ascent of the mass"): along
the gradient flow `t ↦ μ_t(𝒮̂)` is monotone on `[0,∞)`.

`mass_monotoneOn` at `D = [0,∞)`, which is where the paper's trajectory lives and where
`BoundaryBlowup.flow_pos_graph` discharges `hu` — kb `0022`. -/
theorem mass_monotone_flow {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x) (hnu : ∀ x, 0 < nu x) (hg : StrictlyUnimodal gd)
    (hflow : IsGradientFlow K lam nu gd u) :
    MonotoneOn (fun s : ℝ => Graph.meanL2 lam (u s)) (Set.Ici 0) :=
  mass_monotoneOn (convex_Ici 0) hinv hK hlam (fun s hs => hu s hs) hnu hg hflow

/-! ### The maximizer on the sphere: Cauchy–Schwarz against `𝟏`, with its equality case -/

/-- **`∫(v − Πv)² dλ = ‖v‖²_{L²(λ)} − (Πv)²`**, the variance decomposition, on a probability `λ`.
The equality case of Cauchy–Schwarz against `𝟏` is exactly the vanishing of the left side. -/
theorem ipL2_sub_mean {lam : V → ℝ} (htot : ∑ x, lam x = 1) (v : V → ℝ) :
    ∑ x, lam x * (v x - Graph.meanL2 lam v) ^ 2
      = Graph.ipL2 lam v v - Graph.meanL2 lam v ^ 2 := by
  simp only [Graph.ipL2, Graph.meanL2]
  set m : ℝ := ∑ x, lam x * v x with hm
  have hexp : ∀ x : V, lam x * (v x - m) ^ 2
      = lam x * (v x * v x) - 2 * m * (lam x * v x) + m ^ 2 * lam x := fun x => by ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hm, htot]
  ring

/-- **`∫ u dλ ≤ ‖u‖_{L²(λ)}`, with equality if and only if `u` is constant** (`proofs.tex:807`) —
Cauchy–Schwarz against `𝟏` on the probability `λ`, and its equality case.

The non-negativity hypothesis is not in the paper's sentence and is needed: at `v ≡ −1` the two
sides are `−1` and `1`, so *equality iff constant* is false without it. Densities have it. -/
theorem mean_le_nrmL2_iff_const {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1)
    {v : V → ℝ} (hv : ∀ x, 0 ≤ v x) :
    Graph.meanL2 lam v ≤ Graph.nrmL2 lam v
      ∧ (Graph.meanL2 lam v = Graph.nrmL2 lam v ↔ ∀ x, v x = Graph.meanL2 lam v) := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hmnn : 0 ≤ Graph.meanL2 lam v :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hnn x) (hv x)
  have hle : Graph.meanL2 lam v ≤ Graph.nrmL2 lam v :=
    le_trans (le_abs_self _) (abs_mass_le_nrmL2 hnn htot v)
  refine ⟨hle, ?_, ?_⟩
  · intro heq
    have hsq : Graph.nrmL2 lam v ^ 2 = Graph.ipL2 lam v v := Graph.sq_nrmL2 hnn v
    have hzero : ∑ x, lam x * (v x - Graph.meanL2 lam v) ^ 2 = 0 := by
      rw [ipL2_sub_mean htot v, ← hsq, ← heq]; ring
    intro x
    have hterm : lam x * (v x - Graph.meanL2 lam v) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => mul_nonneg (hnn z) (sq_nonneg _))).mp hzero x (mem_univ x)
    have h2 : (v x - Graph.meanL2 lam v) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with h | h
      · exact absurd h (hlam x).ne'
      · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith [this]
  · intro hconst
    have hip : Graph.ipL2 lam v v = Graph.meanL2 lam v ^ 2 := by
      have hzero : ∑ x, lam x * (v x - Graph.meanL2 lam v) ^ 2 = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [hconst x]; ring
      rw [ipL2_sub_mean htot v] at hzero
      linarith
    rw [Graph.nrmL2, hip, Real.sqrt_sq hmnn]

/-! ### The maximizer is the balanced flow — and the converse is ergodicity -/

/-- **A constant density is balanced**, on any kernel with an invariant `λ`: `μ = cλ` and
`λK = λ` give `μK = μ`. One half of "the unique maximizer is the balanced flow". -/
theorem balanced_const {K : V → V → ℝ} {lam : V → ℝ} (hinv : Invariant K lam) (c : ℝ) :
    Balanced K lam (fun _ => c) := by
  intro y
  simp only [pushMass]
  have hexp : ∀ x : V, lam x * c * K x y = c * (lam x * K x y) := fun x => by ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x, ← Finset.mul_sum, hinv y]
  ring

/-- **`prop:no_distant_equilibrium`*(2)*, the Lyapunov half, for an abstract kernel.**

Along the gradient flow: the sphere `‖u_t‖_{L²(λ)} = ‖u₀‖` is preserved, the mass ascends, it is
bounded by `‖u₀‖`, and the bound is attained exactly at a constant density — which is balanced.

The missing word is *only*: that a **balanced** density is constant is ergodicity, is false for a
general invariant `K`, and is `mass_ascent_lyapunov_graph` below. See the module SCOPE. -/
theorem mass_ascent_lyapunov {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x) (hnu : ∀ x, 0 < nu x)
    (hg : StrictlyUnimodal gd) (hflow : IsGradientFlow K lam nu gd u) :
    (∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (u t) = Graph.nrmL2 lam (u 0))
      ∧ MonotoneOn (fun s : ℝ => Graph.meanL2 lam (u s)) (Set.Ici 0)
      ∧ (∀ t : ℝ, 0 ≤ t → Graph.meanL2 lam (u t) ≤ Graph.nrmL2 lam (u 0))
      ∧ (∀ t : ℝ, 0 ≤ t → Graph.meanL2 lam (u t) = Graph.nrmL2 lam (u 0)
          → (∀ x, u t x = Graph.meanL2 lam (u t)) ∧ Balanced K lam (u t)) := by
  have hsph : ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (u t) = Graph.nrmL2 lam (u 0) :=
    fun t ht => nrmL2_const_of_flow hlam hu hflow t ht
  refine ⟨hsph, mass_monotone_flow hinv hK hlam hu hnu hg hflow, fun t ht => ?_,
    fun t ht heq => ?_⟩
  · rw [← hsph t ht]
    exact (mean_le_nrmL2_iff_const hlam htot (fun x => (hu t ht x).le)).1
  · have hconst := (mean_le_nrmL2_iff_const hlam htot (fun x => (hu t ht x).le)).2.mp
      (by rw [heq, hsph t ht])
    refine ⟨hconst, ?_⟩
    have hfun : u t = fun _ => Graph.meanL2 lam (u t) := funext hconst
    rw [hfun]
    exact balanced_const hinv _

end MassAscent

/-! ### On a marked graph, the maximizer *is* the balanced flow

`proofs.tex:791` says "whose unique maximizer (Cauchy–Schwarz) is the balanced flow", and the
word *unique* is ergodicity: Cauchy–Schwarz delivers **constant**, and only an irreducible chain
turns *balanced* back into *constant*. The loop closure of a path-connected marked graph with a
backward policy positive on its edges is such a chain, by `theo:universality_graphs`*(1)–(2)*. -/

section MarkedGraphAscent

open GFNBounds.Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : MarkedGraph V} {B : BackwardPolicy G}

/-- **Balanced ⇒ constant, and this is ergodicity** (`proofs.tex:807`).

`λu` is a non-negative non-zero vector invariant under the backward chain, so it is `cλ` by
`Graph.eq_smul_invProb` — `theo:universality_graphs`*(2)*'s un-normalized uniqueness — and `u ≡ c`
follows from `λ > 0`. There is **no** abstract-kernel version: see the module SCOPE. -/
theorem const_of_balanced_graph (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam u : V → ℝ} (h : B.IsInvProb lam) (hu : ∀ x, 0 < u x)
    (hbal : Balanced B.phat lam u) (x : V) :
    u x = Graph.meanL2 lam u := by
  have hlam : ∀ z, 0 < lam z := h.pos hpc hbpos
  have hnn : ∀ z, 0 ≤ lam z * u z := fun z => (mul_pos (hlam z) (hu z)).le
  have hne : (fun z => lam z * u z) ≠ 0 := fun hc => by
    have h0 : lam G.src * u G.src = 0 := by
      have := congrFun hc G.src
      simpa using this
    exact (mul_pos (hlam G.src) (hu G.src)).ne' h0
  have hinv' : ∀ y, ∑ z, lam z * u z * B.phat z y = lam y * u y := by
    intro y
    simpa only [pushMass] using hbal y
  obtain ⟨-, heq⟩ := B.eq_smul_invProb hpc hbpos h hnn hne hinv'
  have hx : lam x * u x = (∑ z, lam z * u z) * lam x := heq x
  have hcancel : lam x * u x = lam x * ∑ z, lam z * u z := by rw [hx]; ring
  simpa only [Graph.meanL2] using mul_left_cancel₀ (hlam x).ne' hcancel

/-- **`prop:no_distant_equilibrium`*(2)*, the Lyapunov half, in full** — on the backward chain of
a finite path-connected marked graph, where the paper's ergodicity hypothesis is available.

The mass is bounded on the sphere by `‖u₀‖_{L²(λ)}`, and the bound is attained **exactly** at the
balanced flows: this is the sentence "training is a monotone ascent of the mass on a sphere of
`𝓜²(λ)`, whose unique maximizer (Cauchy–Schwarz) is the balanced flow", with `mass_monotone_flow`
supplying the ascent. -/
theorem mass_ascent_lyapunov_graph (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (h : B.IsInvProb lam) (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x) (hnu : ∀ x, 0 < nu x)
    (hg : StrictlyUnimodal gd) (hflow : IsGradientFlow B.phat lam nu gd u) :
    MonotoneOn (fun s : ℝ => Graph.meanL2 lam (u s)) (Set.Ici 0)
      ∧ ∀ t : ℝ, 0 ≤ t → Graph.meanL2 lam (u t) ≤ Graph.nrmL2 lam (u 0)
          ∧ (Graph.meanL2 lam (u t) = Graph.nrmL2 lam (u 0) ↔ Balanced B.phat lam (u t)) := by
  have hlam : ∀ z, 0 < lam z := h.pos hpc hbpos
  have hinv : Invariant B.phat lam := invariant_of_isInvProb h
  have hsph : ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (u t) = Graph.nrmL2 lam (u 0) :=
    fun t ht => nrmL2_const_of_flow hlam hu hflow t ht
  refine ⟨mass_monotone_flow hinv B.phat_nonneg hlam hu hnu hg hflow, fun t ht => ?_⟩
  obtain ⟨hle, hiff⟩ := mean_le_nrmL2_iff_const hlam h.total (fun x => (hu t ht x).le)
  refine ⟨by rw [← hsph t ht]; exact hle, ?_, ?_⟩
  · intro heq
    have hfun : u t = fun _ => Graph.meanL2 lam (u t) := funext (hiff.mp (by rw [heq, hsph t ht]))
    rw [hfun]
    exact balanced_const hinv _
  · intro hbal
    rw [← hsph t ht]
    exact hiff.mpr fun x => const_of_balanced_graph hpc hbpos h (hu t ht) hbal x

end MarkedGraphAscent

/-! ### The loss decreases, and `cor:global_lojasiewicz` with its hypotheses discharged

`proofs.tex:811`: "`𝓛` decreases along the flow". `Flow.lean` carries that as the hypothesis
`hL0 : ∀ t, 𝓛(μ_t) ≤ L₀`; here it is a conclusion, and with it the corollary's `L₀` becomes the
paper's own `𝓛(μ₀)`. -/

section LossDecay

variable {V : Type*} [Fintype V]

/-- **`𝓛` decreases along the flow, on any convex set of times where the trajectory is positive**
(`proofs.tex:811`), from the flow identity `−𝓛̇ = ‖D‖² ≥ 0`.

`Flow.hasDerivAt_loss_flow_at` asks positivity **at one time only**, so the descent is available
on the bootstrap window `[0,t]` of a continuation: that is what
`BoundaryBlowup.flow_pos_of_pos` consumes. -/
theorem loss_antitoneOn {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    {D : Set ℝ} (hD : Convex ℝ D)
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hupos : ∀ s ∈ D, ∀ x, 0 < u s x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hflow : IsGradientFlow K lam nu gd u) :
    AntitoneOn (fun s : ℝ => loss K lam nu (u s) g) D := by
  have hderiv : ∀ s ∈ D, HasDerivAt (fun z : ℝ => loss K lam nu (u z) g)
      (-(Graph.nrmL2 lam (lossGrad K lam nu gd (u s)) ^ 2)) s :=
    fun s hs => hasDerivAt_loss_flow_at hinv hK hlam (hupos s hs) hg (hflow s)
  refine antitoneOn_of_deriv_nonpos hD
    (fun s hs => ((hderiv s hs).continuousAt).continuousWithinAt)
    (fun s hs => ((hderiv s (interior_subset hs)).differentiableAt).differentiableWithinAt)
    fun s hs => ?_
  rw [(hderiv s (interior_subset hs)).deriv]
  simpa using neg_nonpos.mpr (sq_nonneg (Graph.nrmL2 lam (lossGrad K lam nu gd (u s))))

/-- **`𝓛` decreases along the gradient flow** (`proofs.tex:811`): `loss_antitoneOn` at
`D = [0,∞)`. -/
theorem loss_antitone_flow {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hflow : IsGradientFlow K lam nu gd u) :
    AntitoneOn (fun s : ℝ => loss K lam nu (u s) g) (Set.Ici 0) :=
  loss_antitoneOn (convex_Ici 0) hinv hK hlam (fun s hs => hu s hs) hg hflow

/-- **`𝓛` decreases along the flow, for `g = (log x)²`, on any convex set of times where the
trajectory is positive** (`proofs.tex:811`, `:813`) — `loss_antitoneOn` in `Lojasiewicz.lean`'s
variables, where `ν = wλ`. This is the form `BoundaryBlowup.flow_pos_of_pos` consumes. -/
theorem lossVal_antitoneOn {K : V → V → ℝ} {lam wf : V → ℝ} {u : ℝ → V → ℝ}
    {D : Set ℝ} (hD : Convex ℝ D)
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hupos : ∀ s ∈ D, ∀ x, 0 < u s x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    AntitoneOn (fun s : ℝ => lossVal lam wf logSq (ratio K lam (u s))) D := by
  have h := loss_antitoneOn (g := logSq) (gd := logSqDeriv) hD hinv hK hlam hupos
    (fun _ hy => hasDerivAt_logSq hy) hflow
  simpa only [loss_eq_lossVal] using h

/-- The same on `[0,∞)`: `lossVal_antitoneOn` at `D = [0,∞)`. -/
theorem lossVal_antitone_flow {K : V → V → ℝ} {lam wf : V → ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    AntitoneOn (fun s : ℝ => lossVal lam wf logSq (ratio K lam (u s))) (Set.Ici 0) :=
  lossVal_antitoneOn (convex_Ici 0) hinv hK hlam (fun s hs => hu s hs) hflow

/-- **`𝓛_{g,ν}(μ) = 0` if and only if `μ` is balanced**, for `g = (log x)²` and a positive weight:
`(log r)² = 0` state by state is `r ≡ 1`, which is `ratio_eq_one_iff_balanced`.

This is what turns the loss budget of `entry_time` into a statement about the ratios. -/
theorem lossVal_eq_zero_iff_balanced {K : V → V → ℝ} {lam u wf : V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hw : ∀ x, 0 < wf x) :
    lossVal lam wf logSq (ratio K lam u) = 0 ↔ Balanced K lam u := by
  have hr : ∀ y, 0 < ratio K lam u y := ratio_pos hinv hK hlam hu
  rw [← ratio_eq_one_iff_balanced (fun y => mul_pos (hlam y) (hu y))]
  constructor
  · intro h y
    simp only [lossVal] at h
    have hterm : lam y * (wf y * logSq (ratio K lam u y)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun z _ =>
        mul_nonneg (hlam z).le (mul_nonneg (hw z).le (logSq_nonneg _)))).mp h y (mem_univ y)
    have hlog : logSq (ratio K lam u y) = 0 := by
      rcases mul_eq_zero.mp hterm with h1 | h1
      · exact absurd h1 (hlam y).ne'
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (hw y).ne'
        · exact h2
    have hz : Real.log (ratio K lam u y) = 0 := by
      simp only [logSq] at hlog
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hlog
    have hexp := Real.exp_log (hr y)
    rw [hz, Real.exp_zero] at hexp
    exact hexp.symm
  · intro h
    simp only [lossVal]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [h x]
    simp only [logSq, Real.log_one]
    ring

/-- **`lojasiewicz_integrated` without its positivity hypothesis** (`proofs.tex:884`).

`Flow.lojasiewicz_integrated` asks `0 < L t` at every `t ≥ 0`, which the paper never states and a
consumer cannot discharge: `𝓛` vanishes exactly at balance, and nothing forbids the flow from
reaching it. Only `0 ≤ L 0` is needed. The route: `−L' ≥ κ²L² ≥ 0` makes `L` antitone on `[0,∞)`,
so if `L t > 0` then `L > 0` on all of `[0,t]` and the monotonicity of `1/L − κ²s` runs there;
and if `L t ≤ 0` the bound is trivial, the right-hand side being non-negative. -/
theorem lojasiewicz_integrated_nonneg {L L' : ℝ → ℝ} {kappa : ℝ}
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt L (L' t) t)
    (hL0 : 0 ≤ L 0)
    (hineq : ∀ t : ℝ, 0 ≤ t → kappa ^ 2 * L t ^ 2 ≤ -L' t) :
    ∀ t : ℝ, 0 ≤ t → L t ≤ ((L 0)⁻¹ + kappa ^ 2 * t)⁻¹ := by
  have hanti : AntitoneOn L (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := L')
      (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hderiv s (interior_subset hs)).hasDerivWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    have h := hineq s (le_of_lt hs)
    nlinarith [mul_nonneg (sq_nonneg kappa) (sq_nonneg (L s))]
  intro t ht
  have hinv0 : 0 ≤ (L 0)⁻¹ := inv_nonneg.mpr hL0
  have hkt : 0 ≤ kappa ^ 2 * t := mul_nonneg (sq_nonneg _) ht
  have hden : 0 ≤ (L 0)⁻¹ + kappa ^ 2 * t := by linarith
  rcases le_or_gt (L t) 0 with hLt | hLt
  · exact le_trans hLt (inv_nonneg.mpr hden)
  · have hpos : ∀ s ∈ Set.Icc (0:ℝ) t, 0 < L s := fun s hs =>
      lt_of_lt_of_le hLt (hanti (Set.mem_Ici.mpr hs.1) (Set.mem_Ici.mpr ht) hs.2)
    have hyd : ∀ s ∈ Set.Icc (0:ℝ) t,
        HasDerivAt (fun z : ℝ => (L z)⁻¹ - kappa ^ 2 * z) (-L' s / L s ^ 2 - kappa ^ 2) s := by
      intro s hs
      have h1 : HasDerivAt (fun z : ℝ => (L z)⁻¹) (-L' s / L s ^ 2) s :=
        (hderiv s hs.1).inv (hpos s hs).ne'
      have h2 : HasDerivAt (fun z : ℝ => kappa ^ 2 * z) (kappa ^ 2) s := by
        simpa using (hasDerivAt_id' s).const_mul (kappa ^ 2)
      exact h1.sub h2
    have hmono : MonotoneOn (fun z : ℝ => (L z)⁻¹ - kappa ^ 2 * z) (Set.Icc 0 t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) (fun s hs => ?_) (fun s hs => ?_)
        (fun s hs => ?_)
      · exact ((hyd s hs).continuousAt).continuousWithinAt
      · rw [interior_Icc] at hs
        exact ((hyd s (Set.mem_Icc.mpr ⟨hs.1.le, hs.2.le⟩)).differentiableAt).differentiableWithinAt
      · rw [interior_Icc] at hs
        have hs' : s ∈ Set.Icc (0:ℝ) t := Set.mem_Icc.mpr ⟨hs.1.le, hs.2.le⟩
        rw [(hyd s hs').deriv, sub_nonneg, le_div_iff₀ (pow_pos (hpos s hs') 2)]
        exact hineq s hs.1.le
    have hle := hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
    simp only [mul_zero, sub_zero] at hle
    have h0 : (L 0)⁻¹ + kappa ^ 2 * t ≤ (L t)⁻¹ := by linarith
    have hkey : L t * ((L 0)⁻¹ + kappa ^ 2 * t) ≤ 1 := by
      have h1 : L t * ((L 0)⁻¹ + kappa ^ 2 * t) ≤ L t * (L t)⁻¹ :=
        mul_le_mul_of_nonneg_left h0 hLt.le
      rwa [mul_inv_cancel₀ hLt.ne'] at h1
    rcases eq_or_lt_of_le hden with hz | hz
    · exfalso
      have hL00 : L 0 = 0 := inv_eq_zero.mp (by linarith)
      have hmono0 : L t ≤ L 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
      rw [hL00] at hmono0
      linarith
    · have hfin : L t ≤ 1 / ((L 0)⁻¹ + kappa ^ 2 * t) := (le_div_iff₀ hz).2 hkey
      rwa [one_div] at hfin

/-- **`cor:global_lojasiewicz`, both displays, with `L₀ = 𝓛(μ₀)` and no positivity hypothesis**
(statement `proofs.tex:875–886`, proof `proofs.tex:887–898`).

`Flow.global_lojasiewicz_flow` is this statement with two extra hypotheses — a standing bound
`𝓛(μ_t) ≤ L₀` at **every** real time, and `𝓛(μ_t) > 0` for `t ≥ 0`. The first is discharged by
`lossVal_antitone_flow` at `L₀ := 𝓛(μ₀)`, which is what the paper writes; the second by
`lojasiewicz_integrated_nonneg`. The constant is unchanged and still explicit. -/
theorem global_lojasiewicz_flow'
    {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin wmin wsup : ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hu0 : 0 < Graph.nrmL2 lam (u 0))
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    ∀ t : ℝ, 0 ≤ t →
      lossVal lam wf logSq (ratio K lam (u t))
        ≤ ((lossVal lam wf logSq (ratio K lam (u 0)))⁻¹
            + (wmin * Real.sqrt lamMin
                / (Graph.nrmL2 lam (u 0) * wsup
                    * max 1 (Real.sqrt (lossVal lam wf logSq (ratio K lam (u 0))
                        / (wmin * lamMin))))) ^ 2 * t)⁻¹ := by
  have hanti := lossVal_antitone_flow hinv hK hlam hu hflow
  refine lojasiewicz_integrated_nonneg
    (L := fun s => lossVal lam wf logSq (ratio K lam (u s)))
    (L' := fun s => -(Graph.nrmL2 lam
      (lossGradDensity K lam (u s) (fun x => wf x / u s x) logSqDeriv) ^ 2))
    (fun s hs => ?_) (lossVal_nonneg (fun x => (hlam x).le) fun x => le_trans hwmin.le (hw x))
    fun s hs => ?_
  · have h := hasDerivAt_loss_flow (K := K) (lam := lam) (nu := fun x => lam x * wf x)
      (g := logSq) (gd := logSqDeriv) hinv hK hlam hu (fun _ hy => hasDerivAt_logSq hy) hflow s hs
    rw [lossGrad_of_weight hlam] at h
    simpa only [loss_eq_lossVal] using h
  · rw [neg_neg]
    exact global_lojasiewicz_sq hinv hK hlam htot (hu s hs) hlmin hlmin0 hwmin hw hwsup
      (nrmL2_const_of_flow hlam hu hflow s hs) hu0
      (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs)

end LossDecay

/-! ### Homogeneity: the rescaling `μ ↦ μ/m` is a change of time scale

`proofs.tex:813`: "the rescaling `μ ↦ μ/m` changes the gradient field by the factor `1/m`, hence
only the time scale". This is what `theo:training_speed_full` spends to read the local phase's
rate at the entry point rescaled to unit mass (`proofs.tex:928`). -/

section Homogeneity

variable {V : Type*} [Fintype V]

/-- **`r(cμ) = r(μ)`**: the ratio is scale-invariant, for any `c ≠ 0` — the first words of the
proof of item *(2)* (`proofs.tex:807`). Neither `λ > 0` nor `u > 0` is used: both sides divide by
the same vanishing denominator where there is one. -/
theorem ratio_smul {K : V → V → ℝ} {lam u : V → ℝ} {c : ℝ} (hc : c ≠ 0) :
    ratio K lam (fun x => c * u x) = ratio K lam u := by
  funext y
  have hpush : pushMass K lam (fun x => c * u x) y = c * pushMass K lam u y := by
    simp only [pushMass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hden : lam y * (c * u y) = c * (lam y * u y) := by ring
  simp only [ratio, hpush, hden]
  exact mul_div_mul_left _ _ hc

/-- **`D(cμ) = c^{-1} D(μ)`**, the homogeneity of the gradient field (`proofs.tex:813`).

Two cancellations: `r` does not see `c` (`ratio_smul`), and the weight `dν/dμ = ν/(λu)` scales by
`c^{-1}`, which passes through the linear expression `D = Qφ − rφ`. -/
theorem lossGrad_smul {K : V → V → ℝ} {lam nu u : V → ℝ} {gd : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0) :
    lossGrad K lam nu gd (fun x => c * u x) = fun x => c⁻¹ * lossGrad K lam nu gd u x := by
  have hw : ∀ z, nu z / (lam z * (c * u z)) = c⁻¹ * (nu z / (lam z * u z)) := by
    intro z
    rw [inv_mul_eq_div, div_div]
    congr 1
    ring
  funext x
  simp only [lossGrad, lossGradDensity, gradDensity, funAct, ratio_smul hc, hw]
  have hsum : ∑ y, K x y * (gd (ratio K lam u y) * (c⁻¹ * (nu y / (lam y * u y))))
      = c⁻¹ * ∑ y, K x y * (gd (ratio K lam u y) * (nu y / (lam y * u y))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hsum]
  ring

/-- **The rescaled flow is a flow, run at speed `c²`** (`proofs.tex:813`): if `t ↦ μ_t` solves
`μ̇ = −∇𝓛`, so does `s ↦ μ_{t₁ + c²s}/c`.

By `lossGrad_smul` the gradient field at `μ/c` is `c` times the field at `μ`, and the affine time
change contributes `c²`; dividing by `c` for the state leaves exactly `c`. Rescaling the entry
point to unit mass therefore dilates time by `m₁²`, which is the `m₁`-factor of
`theo:training_speed_full`'s local rate. -/
theorem flow_rescale {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hflow : IsGradientFlow K lam nu gd u) {c : ℝ} (hc : 0 < c) (t₁ : ℝ) :
    IsGradientFlow K lam nu gd (fun s x => c⁻¹ * u (t₁ + c ^ 2 * s) x) := by
  intro t x
  have hτ : HasDerivAt (fun s : ℝ => t₁ + c ^ 2 * s) (c ^ 2) t := by
    simpa using ((hasDerivAt_id' t).const_mul (c ^ 2)).const_add t₁
  have hcomp0 := (hflow (t₁ + c ^ 2 * t) x).comp t hτ
  have hcomp : HasDerivAt (fun s : ℝ => u (t₁ + c ^ 2 * s) x)
      (-lossGrad K lam nu gd (u (t₁ + c ^ 2 * t)) x * c ^ 2) t := hcomp0
  have hres := hcomp.const_mul c⁻¹
  have hval : c⁻¹ * (-lossGrad K lam nu gd (u (t₁ + c ^ 2 * t)) x * c ^ 2)
      = -lossGrad K lam nu gd (fun y => c⁻¹ * u (t₁ + c ^ 2 * t) y) x := by
    simp only [lossGrad_smul (inv_ne_zero hc.ne'), inv_inv]
    field_simp
  rwa [hval] at hres

end Homogeneity

/-! ### The entry time into the band `|r − 1| < δ`

`proofs.tex:813`, and `proofs.tex:928` where `theo:training_speed_full` reads it at
`δ₀ = ε₀m₀/(B̂_σ‖u₀‖)` to get `T₀ = 4𝓛(μ₀)‖u₀‖⁶σ_*⁴/(w_min²ε₀⁴m₀⁴λ_min⁵)`. -/

section EntryTime

/-- **`c(δ) = w_min λ_min^{3/2} δ²/(2‖u₀‖)`** (`proofs.tex:813`), the off-band lower bound on
`‖D‖` — an explicit formula, not an `∃ C`. `λ_min^{3/2}` is `lamMin * √lamMin`. -/
noncomputable def cDelta (wmin lamMin u0nrm δ : ℝ) : ℝ :=
  wmin * lamMin * Real.sqrt lamMin * δ ^ 2 / (2 * u0nrm)

variable {V : Type*} [Fintype V]

/-- **The entry time** (`proofs.tex:813`: "after time at most `𝓛(μ₀)/c(δ)²` all ratios are within
`δ` of `1`"): along the gradient flow of `𝓛_{g,ν}` with `g = (log x)²` and `ν = wλ`, `w ≥ w_min`,
there is a time `t₁ ≤ 𝓛(μ₀)/c(δ)²` at which every ratio satisfies `|r(x) − 1| < δ`.

The argument is the paper's, by contradiction on the loss budget. If at every `t ≤ T₀` some ratio
is `δ`-far then `λ(|r−1| ≥ δ) ≥ λ_min` there, so `‖D_t‖ ≥ c(δ)` by
`Lojasiewicz.no_distant_equilibrium_three` — whose sphere hypothesis is `Flow.nrmL2_const_of_flow`
— so `t ↦ 𝓛(μ_t) + c(δ)²t` is antitone by the flow identity, so `𝓛(μ_{T₀}) ≤ 0`, so `𝓛(μ_{T₀})`
vanishes, so `μ_{T₀}` is balanced and *every* ratio there is `1`: a contradiction at `t = T₀`.

`∃ t₁ ∈ [0,T₀]` is what the argument delivers; that the flow stays in the band afterwards is
`theo:local_convergence_full`, and is not here. See the module SCOPE. -/
theorem entry_time {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin wmin δ : ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : 0 < Graph.nrmL2 lam (u 0))
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ t₁ ∈ Set.Icc (0:ℝ) (lossVal lam wf logSq (ratio K lam (u 0))
        / cDelta wmin lamMin (Graph.nrmL2 lam (u 0)) δ ^ 2),
      ∀ x, |ratio K lam (u t₁) x - 1| < δ := by
  have hu0ne : Graph.nrmL2 lam (u 0) ≠ 0 := hu0.ne'
  have hsqrt : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  set c := cDelta wmin lamMin (Graph.nrmL2 lam (u 0)) δ with hcdef
  have hcpos : 0 < c := by
    rw [hcdef, cDelta]
    exact div_pos (mul_pos (mul_pos (mul_pos hwmin hlmin0) hsqrt) (pow_pos hδ0 2)) (by linarith)
  set L0 := lossVal lam wf logSq (ratio K lam (u 0)) with hL0def
  have hL0nn : 0 ≤ L0 := lossVal_nonneg (fun x => (hlam x).le) fun x => (hwpos x).le
  set T := L0 / c ^ 2 with hTdef
  have hTnn : 0 ≤ T := div_nonneg hL0nn (sq_nonneg c)
  by_contra hcon
  push Not at hcon
  have hDlow : ∀ s ∈ Set.Icc (0:ℝ) T,
      c ≤ Graph.nrmL2 lam (lossGradDensity K lam (u s) (fun x => wf x / u s x) logSqDeriv) := by
    intro s hs
    obtain ⟨x0, hx0⟩ := hcon s hs
    have hfar : lamMin ≤ ∑ x ∈ farSet (ratio K lam (u s)) δ, lam x :=
      le_trans (hlmin x0)
        (Finset.single_le_sum (f := lam) (fun i _ => (hlam i).le) (mem_farSet.mpr hx0))
    have h3 := no_distant_equilibrium_three (u0 := u 0) hinv hK hlam htot (hu s hs.1) hlmin hlmin0
      hwmin hw (nrmL2_const_of_flow hlam hu hflow s hs.1) hu0 hδ0 hδ1
    refine le_trans ?_ h3
    have hcoef : 0 ≤ wmin * Real.sqrt lamMin / Graph.nrmL2 lam (u 0) * (δ ^ 2 / 2) :=
      mul_nonneg (div_nonneg (mul_nonneg hwmin.le hsqrt.le) hu0.le) (by positivity)
    have hstep : c = wmin * Real.sqrt lamMin / Graph.nrmL2 lam (u 0) * (δ ^ 2 / 2) * lamMin := by
      rw [hcdef, cDelta]
      field_simp
    rw [hstep]
    exact mul_le_mul_of_nonneg_left hfar hcoef
  have hderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt
      (fun z : ℝ => lossVal lam wf logSq (ratio K lam (u z)) + c ^ 2 * z)
      (-(Graph.nrmL2 lam (lossGradDensity K lam (u s) (fun x => wf x / u s x) logSqDeriv) ^ 2)
        + c ^ 2) s := by
    intro s hs
    have h := hasDerivAt_loss_flow (K := K) (lam := lam) (nu := fun x => lam x * wf x)
      (g := logSq) (gd := logSqDeriv) hinv hK hlam hu (fun _ hy => hasDerivAt_logSq hy) hflow s hs
    rw [lossGrad_of_weight hlam] at h
    have h2 : HasDerivAt (fun z : ℝ => c ^ 2 * z) (c ^ 2) s := by
      simpa using (hasDerivAt_id' s).const_mul (c ^ 2)
    have h' : HasDerivAt (fun z : ℝ => lossVal lam wf logSq (ratio K lam (u z)))
        (-(Graph.nrmL2 lam
          (lossGradDensity K lam (u s) (fun x => wf x / u s x) logSqDeriv) ^ 2)) s := by
      simpa only [loss_eq_lossVal] using h
    exact h'.add h2
  have hFanti : AntitoneOn
      (fun z : ℝ => lossVal lam wf logSq (ratio K lam (u z)) + c ^ 2 * z) (Set.Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun s => -(Graph.nrmL2 lam
        (lossGradDensity K lam (u s) (fun x => wf x / u s x) logSqDeriv) ^ 2) + c ^ 2)
      (fun s hs => (hderiv s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hderiv s (interior_subset hs).1).hasDerivWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    have hD := hDlow s (Set.mem_Icc.mpr ⟨hs.1.le, hs.2.le⟩)
    nlinarith [mul_self_le_mul_self hcpos.le hD]
  have hFle := hFanti (Set.left_mem_Icc.mpr hTnn) (Set.right_mem_Icc.mpr hTnn) hTnn
  simp only [mul_zero, add_zero] at hFle
  rw [← hL0def] at hFle
  have hc2 : c ^ 2 * T = L0 := by
    rw [hTdef]
    field_simp
  have hLT : lossVal lam wf logSq (ratio K lam (u T)) ≤ 0 := by
    rw [hc2] at hFle
    linarith
  have hbal : Balanced K lam (u T) :=
    (lossVal_eq_zero_iff_balanced hinv hK hlam (hu T hTnn) hwpos).mp
      (le_antisymm hLT (lossVal_nonneg (fun x => (hlam x).le) fun x => (hwpos x).le))
  obtain ⟨x1, hx1⟩ := hcon T (Set.right_mem_Icc.mpr hTnn)
  rw [(ratio_eq_one_iff_balanced (fun y => mul_pos (hlam y) (hu T hTnn y))).mpr hbal x1] at hx1
  simp only [sub_self, abs_zero] at hx1
  linarith

end EntryTime

end GFNBounds.Balance
