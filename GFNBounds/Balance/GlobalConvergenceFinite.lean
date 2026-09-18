import GFNBounds.Balance.FlowExistence
import GFNBounds.Balance.SqGenerator

/-!
# On every finite ergodic chain, both gradient flows of item (3) converge to the balanced flow of their sphere

**`prop:no_distant_equilibrium`** — `proofs.tex:874–908` (statement `874–885`, item *(3)* at
`879–883`; proof `887–908`, the existence and convergence paragraphs at the end). Here: item
*(3)*'s **convergence clause** for **both** generators it names, on a **general** finite ergodic
chain, and its **explicit-time clause** for `g = (x − 1)²`.
**`theo:global_dichotomy_full`** — `proofs.tex:914–924`; item *1*'s convergence sentence, both
generators, a general finite ergodic chain.
**`rem:freezing`** — `proofs.tex:870–872`; item *(iv)*'s "global convergence is proved, on finite
state spaces, for `(log x)²` and `(x−1)²`", which is a pointer to the two rows above and closes
with them. (Line numbers drift, kb 0036; the labels are the anchors.)

> (`prop:no_distant_equilibrium`, preamble) Let `g` be admissible and differentiable with
> `sign g'(x) = sign(x−1)` for `x ≠ 1` […], let `(𝒮̂, λ, T)` be ergodic, and write `u := dμ/dλ`
> and `r := d(μT)/dμ`.

> (*(3)*) Let `𝒮̂` be finite, let `λ` be a probability with `λ_min := min_x λ(x) > 0`, let
> `g = (log x)²` or `g = (x−1)²`, and let `ν = wλ` with `w ≥ w_min > 0`. […] the gradient flow
> `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` from any `μ₀ ∼ λ`, with `u₀ := dμ₀/dλ`, has a unique solution
> `(μ_t)_{t≥0}` with `μ_t ∼ λ`, which converges to the balanced flow of the sphere
> `{‖u‖_{L²(λ)} = ‖u₀‖_{L²(λ)}}`, and whose ratios approach `1` in explicit time: for every
> `δ ∈ (0,½]` some `t ≤ 𝓛_{g,ν}(μ₀)/c(δ)²`, with `c(δ) := w_min λ_min^{3/2} δ²/(2‖u₀‖_{L²(λ)})`,
> has `|r_t − 1| < δ` at every state […]

> (proof, convergence) by LaSalle's principle, the trajectory staying in `𝒦`, its `ω`-limit is
> contained in `{d/dt mass = 0}`, which by *(1)* and *(2)* is the single balanced point of the
> sphere: the flow converges to it.

> (`theo:global_dichotomy_full`*(1)*, second sentence) On a finite state space with `ν = wλ`,
> `w ≥ w_min > 0`, and for `g = (log x)²` or `g = (x−1)²`, the gradient flow converges to a
> balanced flow from *every* initialization `μ₀ ∼ λ` (an explicit off-balance gradient lower bound).

> (`rem:freezing`*(iv)*) […] global convergence is proved, on finite state spaces, for
> `(log x)²` and `(x−1)²` only (Proposition `prop:no_distant_equilibrium`*(3)*), a bounded
> strictly unimodal generator not being covered; infinite state spaces are not addressed.

## What is proved

| clause | declaration |
|---|---|
| ergodicity makes a balanced density constant, and the balanced point of a sphere unique | `const_of_balanced_of_uniqueInvariant`, `eq_const_of_balanced_of_uniqueInvariant` |
| positivity of **any** solution from a positive start, any generator (the paper's floor `u_min`) | `FlowGenerator.flow_floor`, `FlowGenerator.flow_pos` |
| **convergence**, any `FlowGenerator`, given a positive solution | **`FlowGenerator.tendsto_of_flow`** |
| **convergence**, any `FlowGenerator`, given a solution from `u₀ > 0` (four conjuncts: limit, balanced, on the sphere, unique) | **`FlowGenerator.converges`** |
| **item *(3)*, "has a unique solution … which converges to the balanced flow of the sphere"**, from `u₀` alone | **`FlowGenerator.existsUnique_converges`**; instances **`no_distant_equilibrium_three_logSq_of_ergodic`**, **`no_distant_equilibrium_three_sq_of_ergodic`** |
| the same, for a given solution | `no_distant_equilibrium_three_converges_logSq_of_ergodic`, `no_distant_equilibrium_three_converges_sq_of_ergodic` |
| `theo:global_dichotomy_full`*(1)*, the convergence sentence, both generators | **`global_dichotomy_full_one_converges_of_ergodic`** |
| item *(3)*, "ratios approach `1` in explicit time", `g = (x − 1)²` | **`entry_time_sq`** (and `lossVal_sq_eq_zero_iff_balanced`) |
| inhabitation (kb 0025) | `twoState_sq_converges_check`, `lazyRot_converges_check` (with `lazyRot_uniqueInvariant`, `lazyRot_not_reversible`) |

Not restated: the existence/uniqueness clause at full generality (`FlowExistence.existsUnique_flow_*_of_ergodic`,
closed 2026-09-14), the display (`Lojasiewicz.no_distant_equilibrium_three`,
`SqGenerator.no_distant_equilibrium_three_sq`), the explicit time for `(log x)²`
(`MassAscent.entry_time`, already generic in the kernel), the coercivity clause at `δ₀`
(`RatioBridge.exists_delta_for_radius`, generic), "`‖u_t‖` constant and `μ_t(𝒮̂)` non-decreasing"
(`Flow.nrmL2_const_of_flow`, `MassAscent.mass_monotone_flow`).

## The route

The paper concludes by **LaSalle's principle**; Mathlib v4.31.0 has no `ω`-limit calculus, and
`GlobalConvergence.lean` went round it through the local exponential phase, which ties it to the
coercivity constant of a marked graph. Here the paper's own Lyapunov function — the mass of
item *(2)* — is used directly, which needs neither LaSalle nor any coercivity constant:

1. Along the flow: the sphere `‖u_t‖ = n₀ := ‖u₀‖`, the mass `m(t) = Πu_t` non-decreasing and
   `≤ n₀` (Cauchy–Schwarz), the floor `u_t ≥ u_min` (the paper's fourth bullet, `FlowGenerator.floor`
   fed by the loss and mass budgets), and the ceiling `u_t ≤ n₀λ_min^{−1/2}`.
2. If `m(t) < n₀ − ε` for all `t`, the trajectory stays in the compact
   `𝒦_ε := [u_min, n₀λ_min^{−1/2}]^V ∩ {‖v‖ = n₀} ∩ {Πv ≤ n₀ − ε}`, inside the open cone. The mass
   velocity `−∫ D dλ` is continuous there (`FlowExistence.contDiffAt_lossGrad`) and positive:
   by item *(1)* it vanishes only at a balanced point, and by ergodicity a balanced point of the
   sphere is the constant `n₀`, whose mass `n₀` is not `≤ n₀ − ε`. Its minimum `η > 0` gives
   `m(t) ≥ m(0) + ηt`, against `m ≤ n₀`. So `m(t) → n₀`.
3. Pythagoras on the sphere, `‖u_t − Πu_t‖² = n₀² − m(t)² → 0`, and `|·| ≤ ‖·‖/√λ_min` give
   `u_t → n₀` state by state.

This is LaSalle's argument specialised to a strict Lyapunov function whose maximum on the
invariant compact set is attained at one point — the content of the paper's sentence "by *(1)*
and *(2)* the single balanced point of the sphere" — carried out by hand.

## Hypothesis checklist — item *(3)*'s convergence and explicit-time clauses; `theo:global_dichotomy_full`*(1)*

| paper hypothesis | here |
|---|---|
| `𝒮̂` finite | ✓ `[Fintype V]` |
| `λ` a probability, `λ_min > 0` | ✓ `hlam : ∀ x, 0 < lam x`, `htot : ∑ x, lam x = 1` (the convention of `proofs.tex:22`: `λ` is an invariant probability); `λ_min` is the minimum, taken inside the proofs. ⚠ `entry_time_sq` takes a lower bound `lamMin ≤ λ` as a parameter, as `MassAscent.entry_time` does; the paper's constant is its value at `lamMin = min λ` |
| `(𝒮̂, λ, T)` ergodic, `T` a Markov kernel | ✓ `hK : 0 ≤ K`, `hrow : ∑_y K x y = 1`, `hinv : Invariant K lam`, `herg : UniqueInvariant K lam` — the reading of `FlowExistence` (every non-negative invariant vector is a multiple of `λ`, `universality.tex`'s definition on a finite space). ⚠ `entry_time_sq` needs only invariance, `K ≥ 0` and positivity of the solution (safe direction) |
| **no marked graph** | ✓ — the restriction of `GlobalConvergence.lean` is gone; `lazyRot_converges_check` is a non-reversible chain |
| `g = (log x)²` or `g = (x − 1)²` | ✓ `logSqFlowGenerator`, `sqFlowGenerator`; the generic theorems take any `FlowGenerator` (derivative `C¹` on `(0,∞)`, strictly unimodal, `g ≥ 0`, sublevel cap), which both inhabit |
| `ν = wλ`, `w ≥ w_min > 0` | ✓ `nu = fun x => lam x * wf x`, `hwmin`, `hw` |
| "from any `μ₀ ∼ λ`" | ✓ `hu0 : ∀ x, 0 < u0 x` (or `u 0`); positivity at later times is **derived** (`FlowGenerator.flow_pos`), not assumed, except in `tendsto_of_flow` (consumed by `FlowGenerator.converges` with it discharged) and `entry_time_sq` (which takes it as `MassAscent.entry_time` does; discharge it with `FlowGenerator.flow_pos`) |
| "the gradient flow" | ✓ `IsGradientFlow` (`t ≥ 0`), **inhabited**: existence and uniqueness are `FlowGenerator.existsUnique_flow`, and `existsUnique_converges` delivers the solution |
| "converges" | ✓ `Tendsto u atTop (𝓝 _)` in `V → ℝ` (every norm on a finite space) |
| "to the balanced flow of the sphere" | ✓ the limit is the explicit constant `‖u₀‖_{L²(λ)}`: balanced, on the sphere, the only positive balanced density there |
| "for every `δ ∈ (0,½]` some `t ≤ 𝓛(μ₀)/c(δ)²` has `\|r_t − 1\| < δ`" (`(x−1)²`) | ✓ `entry_time_sq`, with `δ ∈ (0,½]` **weakened** to `δ > 0` (the `(x−1)²` bound needs no upper limit, `SqGenerator`'s SCOPE) |

## SCOPE (disclosed)

* **LaSalle is not invoked**; the route above is its special case, proved. The limit is exhibited,
  not only located in an `ω`-limit set.
* **`D = lossGrad` is the library's definition of the field**, identified with `∇^λ𝓛_{g,ν}` by
  `FirstVariation.lean` on a finite state space, as throughout `GFNBounds.Balance`.
* **The generator is carried as a `FlowGenerator`**, i.e. the pair `(g, g')` tied by
  `HasDerivAt`; for `(x − 1)²` that is `sqGen` with `g' = 2(x−1)`, as in `FlowExistence`.
* **Items *(1)*–*(2)* in general (non-finite) state spaces are not here** — Phase 4, the general
  measure layer (obstruction 2). Nothing in this file speaks to infinite state spaces, which
  `rem:freezing`*(iv)* says are "not addressed".
* **`rem:freezing`*(iv)*'s first sentence** ("every critical point … is balanced") is
  `RemarksA.freezing_four_critical`; its "a bounded strictly unimodal generator not being covered"
  is a disclaimer with nothing to certify.
* **`η` is existential** (a minimum over a compact set): convergence carries no rate, as the paper's
  convergence clause names none. The constants the paper names — `u_min`, `R_max`, `c(δ)` — are
  explicit (`uFloor`, `capR`, `cDelta`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset Filter Topology Set

section Ergodic

variable {V : Type*} [Fintype V]

/-- **Under ergodicity a balanced density is constant**: `μ = vλ` balanced means `vλ` is
`K`-invariant, and `UniqueInvariant` makes it a multiple of `λ`. The constant is `Πv`. -/
theorem const_of_balanced_of_uniqueInvariant {K : V → V → ℝ} {lam v : V → ℝ}
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hv : ∀ x, 0 ≤ v x) (hbal : Balanced K lam v) (x : V) :
    v x = Graph.meanL2 lam v := by
  obtain ⟨c, hc⟩ := herg (fun x => lam x * v x) (fun x => mul_nonneg (hlam x).le (hv x))
    (fun y => by simpa only [pushMass] using hbal y)
  have hvc : ∀ z, v z = c := fun z => by
    have h := hc z
    have hl := (hlam z).ne'
    field_simp at h
    linarith
  have hmean : Graph.meanL2 lam v = c := by
    simp only [Graph.meanL2, hvc, ← Finset.sum_mul, htot, one_mul]
  rw [hmean, hvc x]

/-- **The balanced flow of a sphere is unique**, under ergodicity: a non-negative balanced
density `v` with `‖v‖_{L²(λ)} = n` is the constant `n`. -/
theorem eq_const_of_balanced_of_uniqueInvariant {K : V → V → ℝ} {lam v : V → ℝ} {n : ℝ}
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hv : ∀ x, 0 ≤ v x) (hbal : Balanced K lam v) (hn : Graph.nrmL2 lam v = n) :
    v = fun _ => n := by
  have hconst : v = fun _ => Graph.meanL2 lam v :=
    funext fun x => const_of_balanced_of_uniqueInvariant hlam htot herg hv hbal x
  have hmv : 0 ≤ Graph.meanL2 lam v :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hlam x).le (hv x)
  have hmeq : Graph.meanL2 lam v = n := by
    calc Graph.meanL2 lam v = |Graph.meanL2 lam v| := (abs_of_nonneg hmv).symm
      _ = Graph.nrmL2 lam (fun _ => Graph.meanL2 lam v) := (nrmL2_const htot _).symm
      _ = Graph.nrmL2 lam v := by rw [← hconst]
      _ = n := hn
  rw [hconst, hmeq]

end Ergodic

section Convergence

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- `v ↦ Πv = ∑ λ(x)v(x)` is continuous. -/
theorem continuous_meanL2 [Fintype V] (lam : V → ℝ) :
    Continuous fun v : V → ℝ => Graph.meanL2 lam v := by
  simp only [Graph.meanL2]
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_apply x)

/-- The mass velocity `−∫ D dλ` is continuous at every positive density. -/
theorem continuousAt_massVel {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {v : V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hv : ∀ x, 0 < v x) (hgd : ∀ y : ℝ, 0 < y → ContDiffAt ℝ 1 gd y) :
    ContinuousAt (fun z : V → ℝ => -(gradMass K lam z (rnWeight lam nu z) gd)) v := by
  have hD := (contDiffAt_lossGrad (nu := nu) hinv hK hlam hv hgd).continuousAt
  have heq : (fun z : V → ℝ => -(gradMass K lam z (rnWeight lam nu z) gd))
      = fun z => -(∑ x, lam x * lossGrad K lam nu gd z x) := by
    funext z
    simp only [gradMass, lossGrad_eq_lossGradDensity]
  rw [heq]
  refine ContinuousAt.neg ?_
  exact tendsto_finsetSum _ fun x _ =>
    (continuousAt_const.mul ((continuous_apply x).continuousAt.comp hD) :
      ContinuousAt (fun z : V → ℝ => lam x * lossGrad K lam nu gd z x) v)

/-- **`prop:no_distant_equilibrium`*(3)*, the convergence clause, for any `FlowGenerator`, on a
finite ergodic chain**: a positive gradient flow converges, state by state, to the constant
density `‖u₀‖_{L²(λ)}`.

The argument is the mass ascent of item *(2)* made quantitative by compactness, in place of the
paper's LaSalle sentence. The mass `m(t) = Πu_t` is non-decreasing and bounded by the invariant
norm `n₀ = ‖u₀‖`. If it stayed below `n₀ − ε`, the trajectory would stay in the compact set
`𝒦_ε = [a,b]^V ∩ {‖v‖ = n₀} ∩ {Πv ≤ n₀ − ε}` — `a = u_min > 0` the paper's floor, `b = n₀λ_min^{−1/2}`
— on which the mass velocity `−∫D dλ` is continuous and, by item *(1)* and ergodicity, positive
(a balanced point of the sphere is the constant `n₀`, whose mass is `n₀`); its minimum `η > 0`
makes `m(t) ≥ m(0) + ηt`, against `m ≤ n₀`. Hence `Πu_t → n₀`, and Pythagoras
`‖u_t − Πu_t‖² = n₀² − (Πu_t)²` sends the fluctuation to `0`. -/
theorem FlowGenerator.tendsto_of_flow {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ} {u : ℝ → V → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu : ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) gd u) :
    Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam (u 0)) := by
  haveI : Nonempty V := nonempty_of_total htot
  set nu : V → ℝ := fun x => lam x * wf x with hnudef
  have hnu : ∀ x, 0 < nu x := fun x => mul_pos (hlam x) (lt_of_lt_of_le hwmin (hw x))
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  obtain ⟨xm, -, hxm⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  set lamMin := lam xm with hlamMin
  have hlmin : ∀ x, lamMin ≤ lam x := fun x => hxm x (Finset.mem_univ x)
  have hlmin0 : 0 < lamMin := hlam xm
  obtain ⟨pmin, hp0, hp1, hp⟩ := exists_edgeFloor K
  have hcross : CrossingFloor K pmin :=
    crossingFloor_of_reach (reach_of_uniqueInvariant hK hrow hinv hlam herg) hp
  set n0 := Graph.nrmL2 lam (u 0) with hn0def
  set m : ℝ → ℝ := fun t => Graph.meanL2 lam (u t) with hmdef
  set L0 := loss K lam nu (u 0) g with hL0def
  set a := uFloor V (G.capR (L0 / (wmin * lamMin))) lamMin pmin (m 0) with hadef
  set b := n0 / Real.sqrt lamMin with hbdef
  set F : (V → ℝ) → ℝ := fun z => -(gradMass K lam z (rnWeight lam nu z) gd) with hFdef
  have hsqrt : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
  -- the a priori facts along the flow
  have hsph : ∀ t, 0 ≤ t → Graph.nrmL2 lam (u t) = n0 := fun t ht =>
    nrmL2_const_of_flow hlam hu hflow t ht
  have hmono : MonotoneOn m (Ici 0) :=
    mass_monotone_flow hinv hK hlam hu hnu G.unimodal hflow
  have hmle : ∀ t, 0 ≤ t → m t ≤ n0 := fun t ht => by
    have := abs_meanL2_le_nrmL2 hnn htot (u t)
    rw [hsph t ht] at this
    exact (le_abs_self _).trans this
  have hm0pos : 0 < m 0 :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu 0 le_rfl x)) Finset.univ_nonempty
  have hlossle : ∀ t, 0 ≤ t → loss K lam nu (u t) g ≤ L0 := fun t ht =>
    loss_antitone_flow hinv hK hlam hu G.hasDerivAt hflow (Set.mem_Ici.2 le_rfl)
      (Set.mem_Ici.2 ht) ht
  have hfloor : ∀ t, 0 ≤ t → ∀ x, a ≤ u t x := fun t ht x =>
    G.floor hinv hK hlam htot (hu t ht) hlmin hlmin0 hp0 hp1 hcross hwmin hw (hlossle t ht)
      (hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht) x
  have ha : 0 < a := by
    have hR0 : 0 < G.capR (L0 / (wmin * lamMin)) := lt_of_lt_of_le one_pos (G.one_le_capR _)
    simp only [hadef, uFloor]
    positivity
  have hceil : ∀ t, 0 ≤ t → ∀ x, u t x ≤ b := fun t ht x => by
    have h := abs_le_nrmL2_div_sqrt hlmin0 hlmin (u t) x
    rw [hsph t ht] at h
    rw [hbdef, le_div_iff₀ hsqrt, mul_comm]
    exact le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) hsqrt.le) h
  -- the mass reaches `n₀`
  have hreach : ∀ ε > 0, ∃ T, ∀ t, T ≤ t → n0 - ε ≤ m t := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hbelow : ∀ s, 0 ≤ s → m s < n0 - ε := by
      intro s hs
      obtain ⟨t, hts, ht⟩ := hcon s
      exact lt_of_le_of_lt (hmono (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hts)) hts) ht
    set Kset : Set (V → ℝ) := densityBox V a b ∩
      ({v | Graph.nrmL2 lam v = n0} ∩ {v | Graph.meanL2 lam v ≤ n0 - ε}) with hKdef
    have hKc : IsCompact Kset :=
      (isCompact_densityBox a b).inter_right
        ((isClosed_eq (continuous_nrmL2 lam) continuous_const).inter
          (isClosed_le (continuous_meanL2 lam) continuous_const))
    have hmemK : ∀ t, 0 ≤ t → u t ∈ Kset := fun t ht =>
      ⟨mem_densityBox.2 fun x => ⟨hfloor t ht x, hceil t ht x⟩, hsph t ht,
        (hbelow t ht).le⟩
    have hKpos : ∀ v ∈ Kset, ∀ x, 0 < v x := fun v hv x =>
      ha.trans_le (mem_densityBox.1 hv.1 x).1
    obtain ⟨vs, hvsK, hvsmin⟩ := hKc.exists_isMinOn ⟨u 0, hmemK 0 le_rfl⟩
      (fun v hv => (continuousAt_massVel hinv hK hlam (hKpos v hv) G.contDiffAt).continuousWithinAt)
    set η := F vs with hηdef
    have hη : 0 < η := by
      refine mass_deriv_pos_off_balance hinv hK hlam (hKpos vs hvsK) hnu G.unimodal fun hbal => ?_
      have hc := eq_const_of_balanced_of_uniqueInvariant hlam htot herg
        (fun x => (hKpos vs hvsK x).le) hbal hvsK.2.1
      have hmv : Graph.meanL2 lam vs ≤ n0 - ε := hvsK.2.2
      have : Graph.meanL2 lam vs = n0 := by
        rw [hc]; simp only [Graph.meanL2, ← Finset.sum_mul, htot, one_mul]
      linarith
    have hderiv : ∀ t, 0 ≤ t → HasDerivAt m (F (u t)) t := fun t ht =>
      hasDerivAt_mass_flow hflow t ht
    have hderiv2 : ∀ s, 0 ≤ s → HasDerivAt (fun t => m t - η * t) (F (u s) - η) s := by
      intro s hs
      have h := (hderiv s hs).fun_sub ((hasDerivAt_id' s).const_mul η)
      simpa only [mul_one] using h
    have hgrow : MonotoneOn (fun t => m t - η * t) (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun s hs => (hderiv2 s hs).continuousAt.continuousWithinAt)
        (fun s hs => (hderiv2 s (interior_subset hs)).differentiableAt.differentiableWithinAt)
        fun s hs => ?_
      have hs0 : 0 ≤ s := interior_subset hs
      rw [(hderiv2 s hs0).deriv]
      have : η ≤ F (u s) := hvsmin (hmemK s hs0)
      linarith
    set T := (n0 - m 0) / η + 1 with hTdef
    have hT0 : 0 ≤ T := by
      have : 0 ≤ (n0 - m 0) / η := div_nonneg (by linarith [hmle 0 le_rfl]) hη.le
      linarith
    have h1 := hgrow (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT0) hT0
    simp only [mul_zero, sub_zero] at h1
    have hηT : η * T = n0 - m 0 + η := by
      rw [hTdef, mul_add, mul_div_cancel₀ _ hη.ne', mul_one]
    have := hmle T hT0
    linarith
  -- `Πu_t → n₀`
  have hmt : Tendsto m atTop (𝓝 n0) := by
    rw [tendsto_order]
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨T, hT⟩ := hreach ((n0 - c) / 2) (by linarith)
      filter_upwards [eventually_ge_atTop T] with t ht
      linarith [hT t ht]
    · filter_upwards [eventually_ge_atTop 0] with t ht
      exact lt_of_le_of_lt (hmle t ht) hc
  -- the fluctuation `‖u_t − Πu_t‖` tends to `0`
  have hperp : Tendsto (fun t => Graph.nrmL2 lam (perpL2 lam (u t))) atTop (𝓝 0) := by
    have hsq : Tendsto (fun t => Real.sqrt (n0 ^ 2 - m t ^ 2)) atTop (𝓝 0) := by
      have := (((continuous_const (y := n0 ^ 2)).sub (continuous_pow 2)).tendsto n0).comp hmt
      have h2 := (Real.continuous_sqrt.tendsto _).comp this
      simpa only [Function.comp_def, sub_self, Real.sqrt_zero] using h2
    refine hsq.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have hpy := nrmL2_sq_eq_mean_sq_add_perp hnn htot (u t)
    rw [hsph t ht] at hpy
    rw [show n0 ^ 2 - m t ^ 2 = Graph.nrmL2 lam (perpL2 lam (u t)) ^ 2 by
      simp only [hmdef]; linarith]
    exact Real.sqrt_sq (Graph.nrmL2_nonneg _ _)
  -- pointwise convergence
  rw [tendsto_pi_nhds]
  intro x
  have hdev : Tendsto (fun t => u t x - m t) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
      (by simpa only [zero_div] using hperp.div_const (Real.sqrt lamMin))
    refine Eventually.of_forall fun t => ?_
    have h := abs_le_nrmL2_div_sqrt hlmin0 hlmin (perpL2 lam (u t)) x
    rw [perpL2_apply] at h
    rw [sub_zero, Real.norm_eq_abs, le_div_iff₀ hsqrt, mul_comm]
    exact h
  have := hdev.add hmt
  simpa only [zero_add, sub_add_cancel] using this

end Convergence

/-! ### Positivity of any solution from a positive start, for any `FlowGenerator` -/

section Positivity

variable {V : Type*} [Fintype V]

/-- **The floor along any solution, for any `FlowGenerator`** (`proofs.tex`, the fourth bullet of
the existence paragraph of `prop:no_distant_equilibrium`*(3)*): a gradient flow started at a
positive density stays at density at least `u_min = m₀(λ_min p_min/R_max)^{#𝒮̂−1}` on `[0,∞)`.

`BoundaryBlowup.flow_pos_of_pos`, whose continuation is hard-wired to `(log x)²`, with the static
floor `FlowGenerator.floor` in place of `pos_of_loss_le`: the same first-failure bootstrap, so
that it serves `(x − 1)²` too. -/
theorem FlowGenerator.flow_floor {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf : V → ℝ} {u : ℝ → V → ℝ} {lamMin pmin wmin : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) gd u) :
    ∀ t : ℝ, 0 ≤ t → ∀ x,
      uFloor V (G.capR (loss K lam (fun x => lam x * wf x) (u 0) g / (wmin * lamMin)))
        lamMin pmin (Graph.meanL2 lam (u 0)) ≤ u t x := by
  haveI : Nonempty V := nonempty_of_total htot
  have hnu : ∀ x, 0 < lam x * wf x := fun x => mul_pos (hlam x) (lt_of_lt_of_le hwmin (hw x))
  set L0 := loss K lam (fun x => lam x * wf x) (u 0) g with hL0def
  set m0 := Graph.meanL2 lam (u 0) with hm0def
  have hm0pos : 0 < m0 :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  set um := uFloor V (G.capR (L0 / (wmin * lamMin))) lamMin pmin m0 with humdef
  have hum0 : 0 < um := by
    have hR0 : 0 < G.capR (L0 / (wmin * lamMin)) := lt_of_lt_of_le one_pos (G.one_le_capR _)
    simp only [humdef, uFloor]
    positivity
  have hstatic : ∀ v : V → ℝ, (∀ x, 0 < v x) →
      loss K lam (fun x => lam x * wf x) v g ≤ L0 → m0 ≤ Graph.meanL2 lam v →
      ∀ x, um ≤ v x := fun v hv hL hm x =>
    G.floor hinv hK hlam htot hv hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hL hm x
  have hiff : ∀ (t : ℝ) (x : V) (b : ℝ), 0 ≤ b →
      (|max 0 (3 * um / 2 - u t x)| ≤ b ↔ 3 * um / 2 - b ≤ u t x) := by
    intro t x b hb
    rw [abs_of_nonneg (le_max_left (0:ℝ) (3 * um / 2 - u t x)), max_le_iff]
    exact ⟨fun hh => by linarith [hh.2], fun hh => ⟨hb, by linarith⟩⟩
  have hkey : ∀ t : ℝ, 0 ≤ t → ∀ x, |max 0 (3 * um / 2 - u (max t 0) x)| ≤ um / 2 := by
    refine bootstrap_of_continuous (h := fun t x => max 0 (3 * um / 2 - u (max t 0) x))
      (eps := um) hum0
      (fun x => continuous_const.max (continuous_const.sub
        (continuous_iff_continuousAt.2 fun s =>
          ContinuousAt.comp (g := fun r : ℝ => u r x) (f := fun r : ℝ => max r 0) (x := s)
            (continuous_flow hflow x _ (le_max_right s 0))
            (continuous_id.max continuous_const).continuousAt)))
      (fun x => ?_) fun t ht hwin' x => ?_
    · simp only [max_self]
      rw [hiff 0 x (um / 2) (by linarith)]
      have := hstatic (u 0) hu0 le_rfl le_rfl x
      linarith
    · simp only [max_eq_left ht]
      have hwin : ∀ s ∈ Set.Icc (0:ℝ) t, ∀ y, |max 0 (3 * um / 2 - u s y)| ≤ um :=
        fun s hs y => by simpa only [max_eq_left hs.1] using hwin' s hs y
      have hupos : ∀ s ∈ Set.Icc (0:ℝ) t, ∀ y, 0 < u s y := by
        intro s hs y
        have := (hiff s y um hum0.le).mp (hwin s hs y)
        linarith
      have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) t := ⟨le_rfl, ht⟩
      have htmem : t ∈ Set.Icc (0:ℝ) t := ⟨ht, le_rfl⟩
      have hL : loss K lam (fun x => lam x * wf x) (u t) g ≤ L0 :=
        loss_antitoneOn (convex_Icc 0 t) (fun _ hs => hs.1) hinv hK hlam hupos G.hasDerivAt
          hflow h0mem htmem ht
      have hm : m0 ≤ Graph.meanL2 lam (u t) :=
        mass_monotoneOn (convex_Icc 0 t) (fun _ hs => hs.1) hinv hK hlam hupos hnu
          G.unimodal hflow h0mem htmem ht
      rw [hiff t x (um / 2) (by linarith)]
      have := hstatic (u t) (hupos t htmem) hL hm x
      linarith
  intro t ht x
  have hb := hkey t ht x
  simp only [max_eq_left ht] at hb
  rw [hiff t x (um / 2) (by linarith)] at hb
  linarith

/-- **A solution from a positive start stays positive, for any `FlowGenerator`**, on a finite
irreducible kernel — so the positivity every convergence statement needs is discharged, for
`(x − 1)²` as `BoundaryBlowup.flow_pos` discharges it for `(log x)²`. -/
theorem FlowGenerator.flow_pos {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hreach : ∀ x y : V, Relation.ReflTransGen (fun a b => 0 < K a b) x y)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) gd u) :
    ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x := by
  haveI : Nonempty V := nonempty_of_total htot
  obtain ⟨xm, -, hxm⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  obtain ⟨pmin, hp0, hp1, hp⟩ := exists_edgeFloor K
  have hcross : CrossingFloor K pmin := crossingFloor_of_reach hreach hp
  have hm0 : 0 < Graph.meanL2 lam (u 0) :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  have hR0 : 0 < G.capR (loss K lam (fun x => lam x * wf x) (u 0) g / (wmin * lam xm)) :=
    lt_of_lt_of_le one_pos (G.one_le_capR _)
  have hfl0 : 0 < uFloor V (G.capR (loss K lam (fun x => lam x * wf x) (u 0) g / (wmin * lam xm)))
      (lam xm) pmin (Graph.meanL2 lam (u 0)) := by
    have := hlam xm
    simp only [uFloor]
    positivity
  intro t ht x
  exact hfl0.trans_le (G.flow_floor hinv hK hlam htot (lamMin := lam xm)
    (fun x => hxm x (Finset.mem_univ x)) (hlam xm) hp0 hp1 hcross hwmin hw hu0 hflow t ht x)

end Positivity

/-! ### Item *(3)* and the dichotomy's item *1*, convergence, assembled -/

section Headline

variable {V : Type*} [Fintype V]

/-- **`prop:no_distant_equilibrium`*(3)*, the convergence clause, for any `FlowGenerator`, on a
finite ergodic chain, for a given solution from a positive start.** Four conjuncts, as in
`GlobalConvergence.no_distant_equilibrium_three_converges`: `u_t → ‖u₀‖` (the constant density);
that constant is balanced; it lies on the sphere of `u₀`; it is the only positive balanced
density on that sphere. -/
theorem FlowGenerator.converges {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ} {u : ℝ → V → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) gd u) :
    Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam (u 0))
      ∧ Balanced K lam (fun _ => Graph.nrmL2 lam (u 0))
      ∧ Graph.nrmL2 lam (fun _ => Graph.nrmL2 lam (u 0)) = Graph.nrmL2 lam (u 0)
      ∧ ∀ v : V → ℝ, (∀ x, 0 < v x) → Balanced K lam v →
          Graph.nrmL2 lam v = Graph.nrmL2 lam (u 0) → v = fun _ => Graph.nrmL2 lam (u 0) := by
  have hu := G.flow_pos hinv hK hlam htot (reach_of_uniqueInvariant hK hrow hinv hlam herg)
    hwmin hw hu0 hflow
  refine ⟨G.tendsto_of_flow hK hrow hinv hlam htot herg hwmin hw hu hflow,
    balanced_const hinv _, ?_, fun v hv hbal hvn =>
      eq_const_of_balanced_of_uniqueInvariant hlam htot herg (fun x => (hv x).le) hbal hvn⟩
  rw [nrmL2_const htot, abs_of_nonneg (Graph.nrmL2_nonneg _ _)]

/-- **`prop:no_distant_equilibrium`*(3)*, existence, uniqueness and convergence, for any
`FlowGenerator`, from `u₀` alone**: the gradient flow from any `μ₀ ∼ λ` has a unique solution
with `μ_t ∼ λ`, which converges to the balanced flow of the sphere `{‖u‖ = ‖u₀‖}` — the constant
density `‖u₀‖`, balanced, and the only positive balanced density on that sphere. -/
theorem FlowGenerator.existsUnique_converges {g gd : ℝ → ℝ} (G : FlowGenerator g gd)
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) gd u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ (∀ v : ℝ → V → ℝ, v 0 = u0 → IsGradientFlow K lam (fun x => lam x * wf x) gd v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t)
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam u0)
      ∧ Balanced K lam (fun _ => Graph.nrmL2 lam u0)
      ∧ ∀ w : V → ℝ, (∀ x, 0 < w x) → Balanced K lam w →
          Graph.nrmL2 lam w = Graph.nrmL2 lam u0 → w = fun _ => Graph.nrmL2 lam u0 := by
  obtain ⟨u, hu0', hflow, hupos, huniq⟩ := G.existsUnique_flow hinv hK hlam htot
    (reach_of_uniqueInvariant hK hrow hinv hlam herg) hwmin hw hu0
  have hu0'' : ∀ x, 0 < u 0 x := fun x => by rw [hu0']; exact hu0 x
  obtain ⟨hconv, hbal, -, hone⟩ := G.converges hK hrow hinv hlam htot herg hwmin hw hu0'' hflow
  rw [hu0'] at hconv hbal hone
  exact ⟨u, hu0', hflow, hupos, huniq, hconv, hbal, hone⟩

/-- **`prop:no_distant_equilibrium`*(3)*, `g = (log x)²`, on a general finite ergodic chain**:
existence, uniqueness and convergence to the balanced flow of the sphere — the marked-graph
restriction of `FlowExistence.no_distant_equilibrium_three_of_init` removed. -/
theorem no_distant_equilibrium_three_logSq_of_ergodic
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ, u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ (∀ v : ℝ → V → ℝ, v 0 = u0 → IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t)
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam u0)
      ∧ Balanced K lam (fun _ => Graph.nrmL2 lam u0)
      ∧ ∀ w : V → ℝ, (∀ x, 0 < w x) → Balanced K lam w →
          Graph.nrmL2 lam w = Graph.nrmL2 lam u0 → w = fun _ => Graph.nrmL2 lam u0 :=
  logSqFlowGenerator.existsUnique_converges hK hrow hinv hlam htot herg hwmin hw hu0

/-- **`prop:no_distant_equilibrium`*(3)*, `g = (x − 1)²`, on a general finite ergodic chain**:
existence, uniqueness and convergence to the balanced flow of the sphere. -/
theorem no_distant_equilibrium_three_sq_of_ergodic
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ∃ u : ℝ → V → ℝ,
      u 0 = u0 ∧ IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ (∀ v : ℝ → V → ℝ, v 0 = u0 →
          IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) v →
          (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t)
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam u0)
      ∧ Balanced K lam (fun _ => Graph.nrmL2 lam u0)
      ∧ ∀ w : V → ℝ, (∀ x, 0 < w x) → Balanced K lam w →
          Graph.nrmL2 lam w = Graph.nrmL2 lam u0 → w = fun _ => Graph.nrmL2 lam u0 :=
  sqFlowGenerator.existsUnique_converges hK hrow hinv hlam htot herg hwmin hw hu0

/-- **`prop:no_distant_equilibrium`*(3)*, convergence, `g = (log x)²`, for a given solution on a
general finite ergodic chain** — `GlobalConvergence.no_distant_equilibrium_three_converges`
without the marked-graph restriction. -/
theorem no_distant_equilibrium_three_converges_logSq_of_ergodic
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ} {u : ℝ → V → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam (u 0))
      ∧ Balanced K lam (fun _ => Graph.nrmL2 lam (u 0))
      ∧ Graph.nrmL2 lam (fun _ => Graph.nrmL2 lam (u 0)) = Graph.nrmL2 lam (u 0)
      ∧ ∀ v : V → ℝ, (∀ x, 0 < v x) → Balanced K lam v →
          Graph.nrmL2 lam v = Graph.nrmL2 lam (u 0) → v = fun _ => Graph.nrmL2 lam (u 0) :=
  logSqFlowGenerator.converges hK hrow hinv hlam htot herg hwmin hw hu0 hflow

/-- **`prop:no_distant_equilibrium`*(3)*, convergence, `g = (x − 1)²`, for a given solution on a
general finite ergodic chain.** -/
theorem no_distant_equilibrium_three_converges_sq_of_ergodic
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ} {u : ℝ → V → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) u) :
    Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam (u 0))
      ∧ Balanced K lam (fun _ => Graph.nrmL2 lam (u 0))
      ∧ Graph.nrmL2 lam (fun _ => Graph.nrmL2 lam (u 0)) = Graph.nrmL2 lam (u 0)
      ∧ ∀ v : V → ℝ, (∀ x, 0 < v x) → Balanced K lam v →
          Graph.nrmL2 lam v = Graph.nrmL2 lam (u 0) → v = fun _ => Graph.nrmL2 lam (u 0) :=
  sqFlowGenerator.converges hK hrow hinv hlam htot herg hwmin hw hu0 hflow

/-- **`theo:global_dichotomy_full`*(1)*, the convergence sentence, both generators, on a finite
ergodic chain**: for `g = (log x)²` or `g = (x − 1)²`, `ν = wλ`, `w ≥ w_min > 0`, the gradient
flow converges to a balanced flow from every initialization `μ₀ ∼ λ` — explicitly, to the
constant density `‖u₀‖ > 0`. The flow exists and is unique (`FlowGenerator.existsUnique_flow`);
it is quantified here as "the" flow: every positive solution from `u₀`. -/
theorem global_dichotomy_full_one_converges_of_ergodic
    {K : V → V → ℝ} {lam wf : V → ℝ} {wmin : ℝ} {u : ℝ → V → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hinv : Invariant K lam)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (herg : UniqueInvariant K lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u
      ∨ IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) u) :
    0 < Graph.nrmL2 lam (u 0)
      ∧ Balanced K lam (fun _ => Graph.nrmL2 lam (u 0))
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam (u 0)) := by
  haveI : Nonempty V := nonempty_of_total htot
  have hmean0 : 0 < Graph.meanL2 lam (u 0) :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  have hpos : 0 < Graph.nrmL2 lam (u 0) :=
    lt_of_lt_of_le hmean0 (mean_le_nrmL2_iff_const hlam htot fun x => (hu0 x).le).1
  rcases hflow with hf | hf
  · obtain ⟨hconv, hbal, -, -⟩ :=
      no_distant_equilibrium_three_converges_logSq_of_ergodic hK hrow hinv hlam htot herg hwmin hw
        hu0 hf
    exact ⟨hpos, hbal, hconv⟩
  · obtain ⟨hconv, hbal, -, -⟩ :=
      no_distant_equilibrium_three_converges_sq_of_ergodic hK hrow hinv hlam htot herg hwmin hw
        hu0 hf
    exact ⟨hpos, hbal, hconv⟩

end Headline

/-! ### The entry time, for `(x − 1)²` -/

section EntryTimeSq

variable {V : Type*} [Fintype V]

/-- **`𝓛_{g,ν}(μ) = 0` iff `μ` is balanced, for `g = (x − 1)²`** and a positive weight. -/
theorem lossVal_sq_eq_zero_iff_balanced {K : V → V → ℝ} {lam u wf : V → ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x) (hw : ∀ x, 0 < wf x) :
    lossVal lam wf sqGen (ratio K lam u) = 0 ↔ Balanced K lam u := by
  rw [← ratio_eq_one_iff_balanced (fun y => mul_pos (hlam y) (hu y))]
  constructor
  · intro h y
    simp only [lossVal] at h
    have hterm : lam y * (wf y * sqGen (ratio K lam u y)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun z _ =>
        mul_nonneg (hlam z).le (mul_nonneg (hw z).le (sq_nonneg _)))).mp h y (mem_univ y)
    have hsq : sqGen (ratio K lam u y) = 0 := by
      rcases mul_eq_zero.mp hterm with h1 | h1
      · exact absurd h1 (hlam y).ne'
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (hw y).ne'
        · exact h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith
  · intro h
    simp only [lossVal]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [h x]
    simp only [sqGen]
    ring

/-- **`prop:no_distant_equilibrium`*(3)*, the explicit-time clause, `g = (x − 1)²`** ("for every
`δ ∈ (0,½]` some `t ≤ 𝓛(μ₀)/c(δ)²` … has `|r_t − 1| < δ` at every state"): the `(x − 1)²` twin of
`MassAscent.entry_time`, with the same constant `c(δ) = w_min λ_min^{3/2}δ²/(2‖u₀‖)` and the same
argument, the display being `SqGenerator.no_distant_equilibrium_three_sq`. -/
theorem entry_time_sq {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin wmin δ : ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : 0 < Graph.nrmL2 lam (u 0))
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) (fun x => 2 * (x - 1)) u)
    (hδ0 : 0 < δ) :
    ∃ t₁ ∈ Set.Icc (0:ℝ) (lossVal lam wf sqGen (ratio K lam (u 0))
        / cDelta wmin lamMin (Graph.nrmL2 lam (u 0)) δ ^ 2),
      ∀ x, |ratio K lam (u t₁) x - 1| < δ := by
  have hsqrt : 0 < Real.sqrt lamMin := Real.sqrt_pos.mpr hlmin0
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  set c := cDelta wmin lamMin (Graph.nrmL2 lam (u 0)) δ with hcdef
  have hcpos : 0 < c := by
    rw [hcdef, cDelta]
    exact div_pos (mul_pos (mul_pos (mul_pos hwmin hlmin0) hsqrt) (pow_pos hδ0 2)) (by linarith)
  set L0 := lossVal lam wf sqGen (ratio K lam (u 0)) with hL0def
  have hL0nn : 0 ≤ L0 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hlam x).le (mul_nonneg (hwpos x).le (sq_nonneg _))
  set T := L0 / c ^ 2 with hTdef
  have hTnn : 0 ≤ T := div_nonneg hL0nn (sq_nonneg c)
  by_contra hcon
  push Not at hcon
  have hDlow : ∀ s ∈ Set.Icc (0:ℝ) T, c ≤ Graph.nrmL2 lam
      (lossGradDensity K lam (u s) (fun x => wf x / u s x) fun x => 2 * (x - 1)) := by
    intro s hs
    obtain ⟨x0, hx0⟩ := hcon s hs
    have hfar : lamMin ≤ ∑ x ∈ farSet (ratio K lam (u s)) δ, lam x :=
      le_trans (hlmin x0)
        (Finset.single_le_sum (f := lam) (fun i _ => (hlam i).le) (mem_farSet.mpr hx0))
    have h3 := no_distant_equilibrium_three_sq (u0 := u 0) hinv hK hlam htot (hu s hs.1) hlmin
      hlmin0 hwmin hw (nrmL2_const_of_flow hlam hu hflow s hs.1) hu0 hδ0.le
    refine le_trans ?_ h3
    have hcoef : 0 ≤ wmin * Real.sqrt lamMin / Graph.nrmL2 lam (u 0) * (δ ^ 2 / 2) :=
      mul_nonneg (div_nonneg (mul_nonneg hwmin.le hsqrt.le) hu0.le) (by positivity)
    have hstep : c = wmin * Real.sqrt lamMin / Graph.nrmL2 lam (u 0) * (δ ^ 2 / 2) * lamMin := by
      rw [hcdef, cDelta]
      field_simp
    rw [hstep]
    exact mul_le_mul_of_nonneg_left hfar hcoef
  have hderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt
      (fun z : ℝ => lossVal lam wf sqGen (ratio K lam (u z)) + c ^ 2 * z)
      (-(Graph.nrmL2 lam (lossGradDensity K lam (u s) (fun x => wf x / u s x)
        fun x => 2 * (x - 1)) ^ 2) + c ^ 2) s := by
    intro s hs
    have h := hasDerivAt_loss_flow (K := K) (lam := lam) (nu := fun x => lam x * wf x)
      (g := sqGen) (gd := fun x => 2 * (x - 1)) hinv hK hlam hu sqFlowGenerator.hasDerivAt
      hflow s hs
    rw [lossGrad_of_weight hlam] at h
    have h2 : HasDerivAt (fun z : ℝ => c ^ 2 * z) (c ^ 2) s := by
      simpa using (hasDerivAt_id' s).const_mul (c ^ 2)
    have h' : HasDerivAt (fun z : ℝ => lossVal lam wf sqGen (ratio K lam (u z)))
        (-(Graph.nrmL2 lam (lossGradDensity K lam (u s) (fun x => wf x / u s x)
          fun x => 2 * (x - 1)) ^ 2)) s := by
      simpa only [loss_eq_lossVal] using h
    exact h'.add h2
  have hFanti : AntitoneOn
      (fun z : ℝ => lossVal lam wf sqGen (ratio K lam (u z)) + c ^ 2 * z) (Set.Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun s => -(Graph.nrmL2 lam (lossGradDensity K lam (u s) (fun x => wf x / u s x)
        fun x => 2 * (x - 1)) ^ 2) + c ^ 2)
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
  have hLT : lossVal lam wf sqGen (ratio K lam (u T)) ≤ 0 := by
    rw [hc2] at hFle
    linarith
  have hbal : Balanced K lam (u T) :=
    (lossVal_sq_eq_zero_iff_balanced hlam (hu T hTnn) hwpos).mp
      (le_antisymm hLT (Finset.sum_nonneg fun x _ =>
        mul_nonneg (hlam x).le (mul_nonneg (hwpos x).le (sq_nonneg _))))
  obtain ⟨x1, hx1⟩ := hcon T (Set.right_mem_Icc.mpr hTnn)
  rw [(ratio_eq_one_iff_balanced (fun y => mul_pos (hlam y) (hu T hTnn y))).mpr hbal x1] at hx1
  simp only [sub_self, abs_zero] at hx1
  linarith

end EntryTimeSq

/-! ### Inhabitation (kb 0025) -/

section Checks

/-- **The two-state chain, `g = (x − 1)²`, from the non-balanced `u₀ = (3/2, 1/2)`**: the flow
exists, is positive, and converges to the constant `‖u₀‖_{L²(λ)}`. -/
theorem twoState_sq_converges_check :
    ∃ u : ℝ → Fin 2 → ℝ, u 0 = blowupU
      ∧ IsGradientFlow twoStateK twoStateLam (fun x => twoStateLam x * 1) (fun x => 2 * (x - 1)) u
      ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
      ∧ ¬ Balanced twoStateK twoStateLam (u 0)
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 twoStateLam blowupU) := by
  obtain ⟨u, hu0, hflow, hpos, -, hconv, -, -⟩ := no_distant_equilibrium_three_sq_of_ergodic
    (K := twoStateK) (lam := twoStateLam) (wf := fun _ => (1 : ℝ)) (wmin := 1)
    (fun _ _ => by norm_num [twoStateK]) twoStateK_row twoStateK_invariant twoStateLam_pos
    (by norm_num [twoStateLam, Fin.sum_univ_two]) twoState_uniqueInvariant
    one_pos (fun _ => le_rfl) blowupU_pos
  refine ⟨u, hu0, hflow, hpos, ?_, hconv⟩
  rw [hu0, ← ratio_eq_one_iff_balanced (fun y => mul_pos (twoStateLam_pos y) (blowupU_pos y))]
  intro h
  have h1 := h 1
  rw [twoState_blowup_ratio.2] at h1
  norm_num at h1

/-- The lazy rotation on three states, `T(x → x) = T(x → x+1) = 1/2`: doubly stochastic,
**not reversible** for its uniform invariant law, and not presented as the loop closure of a
marked graph — a chain outside the setting of `GlobalConvergence.lean`. -/
noncomputable def lazyRotK : Fin 3 → Fin 3 → ℝ :=
  fun x y => if y = x ∨ y = x + 1 then 1 / 2 else 0

/-- The uniform law on three states. -/
noncomputable def lazyRotLam : Fin 3 → ℝ := fun _ => 1 / 3

/-- The over-weighted start `(2, 1, 1)`. -/
noncomputable def lazyRotU : Fin 3 → ℝ := fun x => if x = 0 then 2 else 1

theorem lazyRotK_nonneg : ∀ x y, 0 ≤ lazyRotK x y := by
  intro x y; unfold lazyRotK; split_ifs <;> norm_num

theorem lazyRotK_row : ∀ x, ∑ y, lazyRotK x y = 1 := by
  intro x; fin_cases x <;> simp [lazyRotK, Fin.sum_univ_three] <;> norm_num

theorem lazyRotK_invariant : Invariant lazyRotK lazyRotLam := by
  intro y; fin_cases y <;> simp [lazyRotK, lazyRotLam, Fin.sum_univ_three] <;> norm_num

theorem lazyRotLam_pos : ∀ x, 0 < lazyRotLam x := fun _ => by norm_num [lazyRotLam]

theorem lazyRotU_pos : ∀ x, 0 < lazyRotU x := by
  intro x; unfold lazyRotU; split_ifs <;> norm_num

/-- The lazy rotation is not reversible: `λ(0)T(0→1) = 1/6 ≠ 0 = λ(1)T(1→0)`. -/
theorem lazyRot_not_reversible : lazyRotLam 0 * lazyRotK 0 1 ≠ lazyRotLam 1 * lazyRotK 1 0 := by
  simp [lazyRotK, lazyRotLam]

/-- The lazy rotation is ergodic in the sense of `UniqueInvariant`: invariance forces
`m(y) = m(y − 1)`. -/
theorem lazyRot_uniqueInvariant : UniqueInvariant lazyRotK lazyRotLam := by
  intro m _ hm
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  simp [lazyRotK, Fin.sum_univ_three] at h0 h1 h2
  have e1 : m 1 = m 0 := by linarith
  have e2 : m 2 = m 0 := by linarith
  refine ⟨3 * m 0, fun x => ?_⟩
  fin_cases x
  · simp only [lazyRotLam, Fin.zero_eta]; ring
  · simp only [lazyRotLam, Fin.mk_one, e1]; ring
  · show m 2 = 3 * m 0 * lazyRotLam 2
    simp only [lazyRotLam, e2]; ring

/-- **Both generators, on the non-reversible lazy rotation, from the non-balanced `(2,1,1)`**
(`r(0) = 3/4`): each flow exists, is positive and converges to the constant `‖u₀‖_{L²(λ)}`. The
hypotheses of the `_of_ergodic` theorems are inhabited off the marked-graph setting. -/
theorem lazyRot_converges_check :
    ¬ Balanced lazyRotK lazyRotLam lazyRotU
      ∧ (∃ u : ℝ → Fin 3 → ℝ, u 0 = lazyRotU
          ∧ IsGradientFlow lazyRotK lazyRotLam (fun x => lazyRotLam x * 1) logSqDeriv u
          ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
          ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lazyRotLam lazyRotU))
      ∧ (∃ u : ℝ → Fin 3 → ℝ, u 0 = lazyRotU
          ∧ IsGradientFlow lazyRotK lazyRotLam (fun x => lazyRotLam x * 1)
              (fun x => 2 * (x - 1)) u
          ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
          ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lazyRotLam lazyRotU)) := by
  have htot : ∑ x, lazyRotLam x = 1 := by norm_num [lazyRotLam, Fin.sum_univ_three]
  refine ⟨?_, ?_, ?_⟩
  · rw [← ratio_eq_one_iff_balanced (fun y => mul_pos (lazyRotLam_pos y) (lazyRotU_pos y))]
    intro h
    have h0 := h 0
    simp [ratio, pushMass, Fin.sum_univ_three, lazyRotK, lazyRotLam, lazyRotU] at h0
    norm_num at h0
  · obtain ⟨u, hu0, hflow, hpos, -, hconv, -, -⟩ := no_distant_equilibrium_three_logSq_of_ergodic
      (wf := fun _ => (1 : ℝ)) (wmin := 1) lazyRotK_nonneg lazyRotK_row lazyRotK_invariant
      lazyRotLam_pos htot lazyRot_uniqueInvariant one_pos (fun _ => le_rfl) lazyRotU_pos
    exact ⟨u, hu0, hflow, hpos, hconv⟩
  · obtain ⟨u, hu0, hflow, hpos, -, hconv, -, -⟩ := no_distant_equilibrium_three_sq_of_ergodic
      (wf := fun _ => (1 : ℝ)) (wmin := 1) lazyRotK_nonneg lazyRotK_row lazyRotK_invariant
      lazyRotLam_pos htot lazyRot_uniqueInvariant one_pos (fun _ => le_rfl) lazyRotU_pos
    exact ⟨u, hu0, hflow, hpos, hconv⟩

end Checks

end GFNBounds.Balance
