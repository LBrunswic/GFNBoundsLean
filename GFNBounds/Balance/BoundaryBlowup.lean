import GFNBounds.Balance.LocalConvergence

/-!
# The boundary blow-up: the loss explodes where the density vanishes, so the flow stays positive

**`prop:no_distant_equilibrium`** — `proofs.tex:787–814`; statement `:787–798`, item *(3)* at
`:792–796`, proof `:800–814`. What is formalized here is **item *(3)*'s compactness half**, the
one sentence of the proof (`:813`) that keeps the trajectory off the boundary of the cone:

> Convergence: `𝓛` decreases along the flow, and it blows up at the boundary of the cone --- if
> `u(x) → 0` at some state while `‖u‖ = ‖u₀‖`, strong connectedness provides an edge from a
> non-vanishing state into the vanishing region, whose ratio explodes and `g(r)ν → ∞` --- so the
> trajectory stays in a compact subset of the open sphere. By LaSalle's principle its `ω`-limit
> is contained in `{d/dt mass = 0}`, which by *(1)* and *(2)* is the single balanced point of the
> sphere: the flow converges to it.

**Twelve declarations of the Appendix-A convergence block carry positivity of the trajectory as
a hypothesis** — `Flow.hasDerivAt_loss_flow`, `Flow.nrmL2_const_of_flow`,
`Flow.global_lojasiewicz_flow`; `MassAscent.mass_monotone_flow`, `.mass_ascent_lyapunov`,
`.mass_ascent_lyapunov_graph`, `.loss_antitone_flow`, `.lossVal_antitone_flow`,
`.global_lojasiewicz_flow'`, `.entry_time`; `TrainingSpeed.entry_and_rescale`,
`.training_speed_full` — each disclosing that it is the stand-in for this sentence. This file
proves it, in the quantitative form the sentence actually supports: a **static, explicit** lower
bound `u_min > 0` on the density at every state, valid at every flow whose loss is at most `L₀`
and whose mass is at least `m₀`, and then a continuation in `t` along the flow. Since 2026-09-13
those twelve read `hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x`, which is what `flow_pos_graph` proves, and
`TrainingSpeed.training_speed_full_of_pos` is the theorem with the hypothesis gone.

The blow-up is proved as a *quantitative* fact, in the paper's own order:

1. `ratio_blowup_of_small` — one edge into a small state makes its ratio large: `r(z) ≥ c/u(z)`.
2. `loss_lower_of_small` — hence `𝓛 ≥ λ_min w_min (log(c/u(z)))²`: the loss explodes.
3. `pos_of_loss_le` — the contrapositive, with `u_min` an explicit formula: strong connectedness
   propagates the one-edge drop across the whole state space, one state per power of `c`.
4. `flow_pos_of_pos` — the continuation: positive at `t = 0` implies positive, and in fact
   `≥ u_min`, at every `t ≥ 0`.

## The constant

`M := max(1, √(L₀/(w_min λ_min)))` — `Lojasiewicz.ratioCap`'s own exponent, reused verbatim —
and

    c := λ_min p_min e^{−M},        u_min := m₀ · c^{|V|−1}.

`c` is the worst per-edge drop of the density: across an edge `y → z` carrying `K(y,z) ≥ p_min`,
`u(z) ≥ c·u(y)`, because otherwise `r(z) = (μT)(z)/(λ(z)u(z))` would exceed `e^M` and the loss
would exceed `L₀`. Strong connectedness then reaches every state from the maximiser in at most
`|V|−1` edges, and the maximiser carries `u ≥ ∫u dλ ≥ m₀`.

## What is proved

| | |
|---|---|
| `ratioCap`, `edgeDrop`, `uMin` | the three constants, as formulas (kb 0007). `ratioCap` is `Lojasiewicz.ratio_le_exp`'s exponent, not a new object |
| `CrossingFloor` | **"strong connectedness provides an edge from a non-vanishing state into the vanishing region"**, with an explicit floor: every non-empty proper `A` has an edge `y → z`, `y ∈ A`, `z ∉ A`, `K(y,z) ≥ p_min` |
| `exists_cross_of_reflTransGen`, `crossingFloor_of_reach`, `crossingFloor_phat` | `CrossingFloor` **discharged** on the loop closure of a finite path-connected marked graph, from `Graph.BackwardPolicy.breach_all` — `theo:universality_graphs`*(1)*'s irreducibility |
| `exists_edgeFloor` | the floor always exists on a `Fintype`: the hypothesis is never vacuous |
| **`ratio_blowup_of_small`** | **the paper's "whose ratio explodes"**: `r(z) ≥ λ(y)u(y)K(y,z)/(λ(z)u(z))` |
| **`loss_lower_of_small`** | **the paper's "`g(r)ν → ∞`"**: `λ_min w_min (log(…))² ≤ 𝓛` |
| `edge_drop_of_loss_le` | the one-edge drop `c·u(y) ≤ u(z)`, the contrapositive of the two above |
| **`pos_of_loss_le`** | **the theorem**: `𝓛 ≤ L₀` and `∫u dλ ≥ m₀` force `u ≥ u_min` at every state |
| `continuous_flow` | a gradient flow is continuous in time, state by state — what `L2Toolkit.bootstrap_of_continuous` consumes |
| **`flow_pos_of_pos`**, `flow_pos`, **`flow_pos_graph`** | **the continuation**: `u_min ≤ u_t(x)` for every `t ≥ 0` and every `x`, hence `0 < u_t(x)`; and the same on the loop closure of a finite path-connected marked graph, which is the shape `theo:training_speed_full` consumes. `L2Toolkit.bootstrap_of_continuous` is the tool, `LocalConvergence.sup_global` the precedent |
| `mass_tendsto` | the mass converges — the half of the LaSalle sentence that does not need an `ω`-limit |
| `twoState_*`, **`twoState_boundary_blowup_check`** | the constants **evaluated** on the two-state chain at `u = (3/2, 1/2)`: `λ_min = p_min = 1/2`, `L₀ = 1/2`, `M = 1`, `u_min = e^{−1}/4 ≈ 0.0920`, against `min u = 1/2` |

## Hypothesis checklist — `prop:no_distant_equilibrium`*(3)*, the compactness half

| paper hypothesis | here |
|---|---|
| `g` admissible, differentiable, strictly unimodal | ⚠ **specialised to `g = (log x)²`**, which is what item *(3)* is stated for (`proofs.tex:792`). `logSq`, `logSqDeriv` are `Lojasiewicz.lean`'s, and ⚠ `logSqDeriv` is the *definition* `2 log x/x`, not a derivative — inherited |
| `(𝒮̂, λ, T)` ergodic | ⚠ **weakened to `Invariant K lam` with `λ > 0` and `∑λ = 1`**, as everywhere in `GFNBounds.Balance`. Ergodicity is not used; what replaces its dynamical content is `CrossingFloor` |
| a **finite** state space | ✓ `[Fintype V]`, and essentially: `u_min` carries `|V|` in its exponent |
| `w ≥ w_min > 0` | ✓ `hwmin : 0 < wmin`, `hw : ∀ x, wmin ≤ wf x`; `ν = wλ` |
| "**strong connectedness** provides an edge from a non-vanishing state into the vanishing region" | ⚠ **carried as `CrossingFloor K pmin`, with an explicit edge floor `p_min` the paper does not name.** Strong connectedness alone gives a crossing edge with `K(y,z) > 0`; a *quantitative* bound needs a floor on that entry. `crossingFloor_phat` discharges the connectedness half from `breach_all`, and `exists_edgeFloor` shows the floor half is always available; `p_min` is a parameter, as `λ_min`, `w_min` and `‖w‖_∞` are throughout this layer |
| `p_min ≤ 1` | ⚠ **added**: true of any transition probability, and needed only to make `c ≤ 1` so that the level sets nest. `K` is not assumed row-stochastic here, so it cannot be derived |
| "while `‖u‖ = ‖u₀‖`" — the invariant sphere | ⚠ **replaced by the mass**, `m₀ ≤ ∫u dλ`. Both are scale information and the argument cannot do without one of them — the loss is scale-invariant, so *no* absolute lower bound on `u` follows from a bound on it — and the mass is the one the flow supplies monotonically. The sphere is proved too (`Flow.nrmL2_const_on_Ici`) and is what bounds the mass from above in `mass_tendsto` |
| "`u(x) → 0` … the trajectory stays in a compact subset of the open sphere" | ⚠ **replaced by the explicit bound `u ≥ u_min`**, which is stronger and is what the downstream `hu` needs. No compactness, no `ω`-limit and no LaSalle principle is formed; see SCOPE |
| the gradient flow `μ̇ = −∇^λ𝓛_{g,ν}(μ)` | ⚠ `IsGradientFlow K lam (λw) logSqDeriv u`, hypothesised of a given curve; no existence theorem, as everywhere in `GFNBounds.Balance` |
| `μ₀ ∼ λ` | ✓ `hu0 : ∀ x, 0 < u 0 x`, the paper's "from any `μ₀ ∼ λ`" on a finite space |
| "By LaSalle's principle its `ω`-limit … the flow converges to it" | ✗ **not proved**; `mass_tendsto` delivers only that the mass converges. See SCOPE |

## SCOPE (disclosed)

* **`hu` is discharged on `[0,∞)`, and the twelve consumers now ask for it there.**
  `flow_pos` concludes `∀ t, 0 ≤ t → ∀ x, 0 < u t x`; until 2026-09-13 every declaration listed
  above took `hu : ∀ t x, 0 < u t x` and **the two did not meet** — kb `0022` in its pure form,
  since nothing about a flow on `[0,∞)` says anything at negative times. The twelve were
  re-ranged on 2026-09-13, the three proofs that had to be redone to do it moved up into
  `Flow.lean` and `MassAscent.lean` where they belong, and
  `TrainingSpeed.training_speed_full_of_pos` is the discharge.
* **What the rewiring costs.** Dropping `hu` is not free: `flow_pos` replaces it with
  `hu0 : ∀ x, 0 < u 0 x` — the paper's own "from *every* initialization `μ₀ ∼ λ`" — **plus** the
  edge floor `p_min` with `0 < p_min ≤ 1` and `CrossingFloor K p_min`. On the marked-graph
  setting `flow_pos_graph` reduces the second to `hpmin : ∀ y z, 0 < π̂_←(y→z) → p_min ≤ π̂_←(y→z)`,
  the connectedness half being `breach_all`; `exists_edgeFloor` says such a `p_min` always
  exists, at the cost of making the statement existential in it.
* **The trajectory's positivity is a continuation, and the continuation is genuine.** The
  circularity — `lossVal_antitone_flow` itself needs `hu` — is broken by
  `Flow.hasDerivAt_loss_flow_at`, which asks positivity **at one time only**.
  `MassAscent.lossVal_antitoneOn` and `MassAscent.mass_monotoneOn` are built from it on an
  arbitrary convex set of times, so the bootstrap window `[0,t]` supplies exactly what they
  consume. Nothing here is assumed at a time later than the one being proved.
* **What blows up in Lean is the loss, not the ratio at `u = 0`.** `ratio K lam u z` divides by
  `λ(z)u(z)`; at `u(z) = 0` Lean's division returns `0`, so `logSq` of it is `0` and the loss is
  *finite* on the boundary of the cone. The paper's `𝓛 = +∞` there is therefore **not** stated,
  and `pos_of_loss_le` hypothesises `u > 0` and concludes the quantitative `u ≥ u_min`. That is
  the honest reading: the statement is about the interior of the cone, and it is exactly the
  statement a continuation argument consumes. A Lean statement of the form "`u ≥ 0` and
  `𝓛 ≤ L₀` imply `u > 0`" would be **false** as the definitions stand, and the two-state chain
  already refutes it: at `u = (1,0)` one has `(μT) ≡ 1/4`, so `r(0) = 1/2` and `r(1) = 0` (the
  junk value), `𝓛 = ½(log 2)² = 0.2402 ≤ 1/4 =: L₀` and `∫u dλ = 1/2 =: m₀`, while
  `u_min = m₀c^{|V|−1} = e^{−1}/8 = 0.0460 > 0 = u(1)`.
* **`λ_min`, `w_min`, `p_min`, `m₀` are parameters, not minima over the vertex set**, as in
  `Lojasiewicz.lean` and `LocalConvergence.lean`. `Graph.minOver` would sharpen `u_min` and is not
  used, so that the general-kernel statements need no `MarkedGraph`.
* **LaSalle is not proved, and no `ω`-limit is formed.** Mathlib v4.31.0 has neither. What is
  delivered is `mass_tendsto`: the mass is monotone on `[0,∞)` and bounded above by
  `max_x u_0(x)`, hence converges. That its limit is the balanced point needs the `ω`-limit set,
  sequential compactness of the sphere and continuity of `u ↦ ∫D dλ` in the state — none of which
  is here. **The convergence half of item *(3)* remains unproved**, exactly as
  `TrainingSpeed.lean`'s SCOPE says; this file closes only the compactness half, and the paper's
  own assembly needs no more than that (`theo:training_speed_full` consumes item *(3)* through
  `hu` and nothing else).
* **`sorry`-free and axiom-clean.** Nothing below carries a `sorry`; `#print axioms` on
  `ratio_blowup_of_small`, `loss_lower_of_small`, `edge_drop_of_loss_le`, `pos_of_loss_le`,
  `crossingFloor_phat`, `exists_edgeFloor`, `continuous_flow`,
  `flow_pos_of_pos`, `flow_pos`, `flow_pos_graph`, `mass_tendsto` and
  `twoState_boundary_blowup_check` returns `[propext, Classical.choice, Quot.sound]`. Graduated
  into the strict library on 2026-09-13, together with the rewiring it enables.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### The three constants -/

/-- **`M := max(1, √(L₀/(w_min λ_min)))`** (`proofs.tex:892`), the exponent of
`Lojasiewicz.ratio_le_exp`. Named, not redefined: every use below is that lemma's own bound. -/
noncomputable def ratioCap (lamMin wmin L0 : ℝ) : ℝ :=
  max 1 (Real.sqrt (L0 / (wmin * lamMin)))

theorem one_le_ratioCap (lamMin wmin L0 : ℝ) : 1 ≤ ratioCap lamMin wmin L0 := le_max_left _ _

theorem ratioCap_pos (lamMin wmin L0 : ℝ) : 0 < ratioCap lamMin wmin L0 :=
  lt_of_lt_of_le one_pos (one_le_ratioCap _ _ _)

/-- **`c := λ_min p_min e^{−M}`**, the worst per-edge drop of the density (`proofs.tex:813`,
"strong connectedness provides an edge from a non-vanishing state into the vanishing region,
whose ratio explodes"). -/
noncomputable def edgeDrop (lamMin pmin wmin L0 : ℝ) : ℝ :=
  lamMin * pmin * Real.exp (-ratioCap lamMin wmin L0)

/-- **`u_min := m₀ · c^{|V|−1}`**, the floor on the density: `m₀` is a lower bound for the mass
`∫u dλ`, and `|V|−1` edges reach every state from the maximiser. -/
noncomputable def uMin (V : Type*) [Fintype V] (lamMin pmin wmin L0 m0 : ℝ) : ℝ :=
  m0 * edgeDrop lamMin pmin wmin L0 ^ (Fintype.card V - 1)

theorem edgeDrop_pos {lamMin pmin wmin L0 : ℝ} (hlmin0 : 0 < lamMin) (hpmin0 : 0 < pmin) :
    0 < edgeDrop lamMin pmin wmin L0 := by
  have := Real.exp_pos (-ratioCap lamMin wmin L0)
  simp only [edgeDrop]
  positivity

/-- `c ≤ 1`: `λ_min ≤ 1` on a probability, `p_min ≤ 1` on a transition floor, and `e^{−M} ≤ 1`
because `M ≥ 1`. -/
theorem edgeDrop_le_one {lamMin pmin wmin L0 : ℝ} (hlmin1 : lamMin ≤ 1)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) : edgeDrop lamMin pmin wmin L0 ≤ 1 := by
  have hexp : Real.exp (-ratioCap lamMin wmin L0) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [ratioCap_pos lamMin wmin L0])
  have hexp0 : 0 < Real.exp (-ratioCap lamMin wmin L0) := Real.exp_pos _
  have hprod : lamMin * pmin ≤ 1 := mul_le_one₀ hlmin1 hpmin0.le hpmin1
  calc edgeDrop lamMin pmin wmin L0 = lamMin * pmin * Real.exp (-ratioCap lamMin wmin L0) := rfl
    _ ≤ 1 * 1 := by
        exact mul_le_mul hprod hexp hexp0.le zero_le_one
    _ = 1 := by ring

theorem uMin_pos {lamMin pmin wmin L0 m0 : ℝ} (hlmin0 : 0 < lamMin) (hpmin0 : 0 < pmin)
    (hm0 : 0 < m0) : 0 < uMin V lamMin pmin wmin L0 m0 :=
  mul_pos hm0 (pow_pos (edgeDrop_pos hlmin0 hpmin0) _)

/-! ### Strong connectedness, with an explicit edge floor

The paper's "strong connectedness provides an edge from a non-vanishing state into the vanishing
region" is used on a *set* — the region where the density is small — and what it must deliver is
an edge leaving the complement of that set. That is the property below. The floor `p_min` on the
crossing entry is what turns the paper's qualitative sentence into a bound. -/

/-- **An edge from outside every non-empty proper set into it, carrying `K ≥ p_min`.** -/
def CrossingFloor (K : V → V → ℝ) (pmin : ℝ) : Prop :=
  ∀ A : Finset V, A.Nonempty → A ≠ Finset.univ → ∃ y ∈ A, ∃ z, z ∉ A ∧ pmin ≤ K y z

omit [Fintype V] in
/-- A walk from inside `A` to outside it crosses the boundary at some step. -/
theorem exists_cross_of_reflTransGen {R : V → V → Prop} {A : Finset V} {a b : V}
    (h : Relation.ReflTransGen R a b) (ha : a ∈ A) :
    b ∉ A → ∃ y ∈ A, ∃ z, z ∉ A ∧ R y z := by
  induction h with
  | refl => intro hb; exact absurd ha hb
  | @tail c d _ hcd ih =>
      intro hd
      by_cases hc : c ∈ A
      · exact ⟨c, hc, d, hd, hcd⟩
      · exact ih hc

/-- **`CrossingFloor` from irreducibility**: if every state reaches every state along positive
entries of `K`, and `p_min` floors the positive entries, the crossing edge is there. -/
theorem crossingFloor_of_reach {K : V → V → ℝ} {pmin : ℝ}
    (hreach : ∀ x y : V, Relation.ReflTransGen (fun a b => 0 < K a b) x y)
    (hpmin : ∀ y z : V, 0 < K y z → pmin ≤ K y z) : CrossingFloor K pmin := by
  intro A hA hne
  obtain ⟨y0, hy0⟩ := hA
  obtain ⟨z0, hz0⟩ : ∃ z : V, z ∉ A := by
    by_contra hc
    push Not at hc
    exact hne (Finset.eq_univ_iff_forall.mpr hc)
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_cross_of_reflTransGen (hreach y0 z0) hy0 hz0
  exact ⟨y, hy, z, hz, hpmin y z hyz⟩

/-- **A floor on the positive entries always exists**, on a finite state space: the hypothesis
`p_min` carries is never vacuous. Stated as an `∃` because it is an inhabitation lemma, not a
constant of the theorem (kb 0007). -/
theorem exists_edgeFloor (K : V → V → ℝ) :
    ∃ pmin : ℝ, 0 < pmin ∧ pmin ≤ 1 ∧ ∀ y z : V, 0 < K y z → pmin ≤ K y z := by
  classical
  set S : Finset (V × V) := Finset.univ.filter (fun p => 0 < K p.1 p.2) with hS
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, le_rfl, fun y z hyz => ?_⟩
    exact absurd (show (y, z) ∈ S from by simp [hS, hyz]) (by simp [hemp])
  · obtain ⟨p0, hp0S, hp0⟩ := S.exists_min_image (fun p => K p.1 p.2) hne
    have hp0pos : 0 < K p0.1 p0.2 := by
      have := hp0S
      rw [hS, Finset.mem_filter] at this
      exact this.2
    refine ⟨min 1 (K p0.1 p0.2), lt_min one_pos hp0pos, min_le_left _ _, fun y z hyz => ?_⟩
    have hmem : (y, z) ∈ S := by simp [hS, hyz]
    exact le_trans (min_le_right _ _) (hp0 (y, z) hmem)

section Graph

variable [DecidableEq V] {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}

/-- **`CrossingFloor` on the loop closure of a finite path-connected marked graph**, from
`Graph.BackwardPolicy.breach_all` — the irreducibility half of `theo:universality_graphs`*(1)*.
This is the paper's "strong connectedness", on the object the paper's own setting names. -/
theorem crossingFloor_phat {pmin : ℝ} (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges)
    (hpmin : ∀ y z : V, 0 < B.phat y z → pmin ≤ B.phat y z) : CrossingFloor B.phat pmin :=
  crossingFloor_of_reach (fun x y => B.breach_all hpc hbpos x y) hpmin

end Graph

/-! ### Item *(1)*: the ratio explodes at a small state -/

/-- **`r(z) ≥ λ(y)u(y)K(y,z)/(λ(z)u(z))`** (`proofs.tex:813`, "whose ratio explodes"): one edge
into `z` already forces the ratio there, and the bound is `∝ 1/u(z)`.

`pushMass` is a sum of non-negative terms and `r` is that sum over `λ(z)u(z)`. -/
theorem ratio_blowup_of_small {K : V → V → ℝ} {lam u : V → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x) (y z : V) :
    lam y * u y * K y z / (lam z * u z) ≤ ratio K lam u z := by
  have hden : 0 < lam z * u z := mul_pos (hlam z) (hu z)
  have hsingle : lam y * u y * K y z ≤ pushMass K lam u z :=
    Finset.single_le_sum (f := fun x => lam x * u x * K x z)
      (fun x _ => mul_nonneg (mul_nonneg (hlam x).le (hu x).le) (hK x z)) (Finset.mem_univ y)
  simpa only [ratio] using div_le_div_of_nonneg_right hsingle hden.le

/-! ### Item *(2)*: hence the loss explodes -/

/-- `logSq` is monotone above `1`. -/
theorem logSq_le_logSq_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : logSq a ≤ logSq b := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le one_pos ha
  have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hnn : 0 ≤ Real.log a := Real.log_nonneg ha
  simpa only [logSq] using pow_le_pow_left₀ hnn hlog 2

/-- **`λ_min w_min (log(λ(y)u(y)K(y,z)/(λ(z)u(z))))² ≤ 𝓛`** (`proofs.tex:813`, "`g(r)ν → ∞`"):
the loss blows up as `u(z) → 0`, at the logarithmic rate `g = (log x)²` gives it.

`Lojasiewicz.logSq_le_of_loss` read at the single state `z`, together with monotonicity of `g`
above `1`. The hypothesis `1 ≤ …` is what places the argument on the increasing branch; below it
the bound is vacuous, `g ≥ 0` being all one can say. -/
theorem loss_lower_of_small {K : V → V → ℝ} {lam u wf : V → ℝ} {lamMin wmin : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) {y z : V}
    (hone : 1 ≤ lam y * u y * K y z / (lam z * u z)) :
    lamMin * wmin * Real.log (lam y * u y * K y z / (lam z * u z)) ^ 2
      ≤ lossVal lam wf logSq (ratio K lam u) := by
  refine le_trans ?_ (logSq_le_of_loss (r := ratio K lam u)
    (fun x => (hlam x).le) hlmin hlmin0 hwmin hw z)
  have hmono : logSq (lam y * u y * K y z / (lam z * u z)) ≤ logSq (ratio K lam u z) :=
    logSq_le_logSq_of_one_le hone (ratio_blowup_of_small hK hlam hu y z)
  have hcoef : 0 ≤ lamMin * wmin := (mul_pos hlmin0 hwmin).le
  simpa only [logSq] using mul_le_mul_of_nonneg_left hmono hcoef

/-! ### Item *(3)*: the contrapositive, with an explicit floor -/

/-- **The one-edge drop**: if `𝓛 ≤ L₀` then `c·u(y) ≤ u(z)` across every edge `y → z` with
`K(y,z) ≥ p_min`. This is `ratio_blowup_of_small` and `loss_lower_of_small` read backwards,
through `Lojasiewicz.ratio_le_exp`. -/
theorem edge_drop_of_loss_le {K : V → V → ℝ} {lam u wf : V → ℝ} {lamMin pmin wmin L0 : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin) (hpmin0 : 0 < pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hL0 : lossVal lam wf logSq (ratio K lam u) ≤ L0) {y z : V} (hyz : pmin ≤ K y z) :
    edgeDrop lamMin pmin wmin L0 * u y ≤ u z := by
  have hr : ∀ x, 0 < ratio K lam u x := ratio_pos hinv hK hlam hu
  have hM : ratio K lam u z ≤ Real.exp (ratioCap lamMin wmin L0) :=
    ratio_le_exp (fun x => (hlam x).le) hlmin hlmin0 hwmin hw hr hL0 z
  have hden : 0 < lam z * u z := mul_pos (hlam z) (hu z)
  have hexp0 : 0 < Real.exp (ratioCap lamMin wmin L0) := Real.exp_pos _
  -- the numerator of `r(z)` is at most `e^M λ(z)u(z)`
  have hpush : pushMass K lam u z ≤ Real.exp (ratioCap lamMin wmin L0) * (lam z * u z) := by
    have := (div_le_iff₀ hden).mp (by simpa only [ratio] using hM)
    linarith
  have hsingle : lam y * u y * K y z ≤ pushMass K lam u z :=
    Finset.single_le_sum (f := fun x => lam x * u x * K x z)
      (fun x _ => mul_nonneg (mul_nonneg (hlam x).le (hu x).le) (hK x z)) (Finset.mem_univ y)
  -- and `λ(z) ≤ 1`, `λ(y) ≥ λ_min`, `K(y,z) ≥ p_min`
  have hlamz : lam z ≤ 1 := by
    rw [← htot]
    exact Finset.single_le_sum (f := lam) (fun i _ => (hlam i).le) (Finset.mem_univ z)
  have hlow : lamMin * pmin * u y ≤ lam y * u y * K y z := by
    have h1 : lamMin * pmin ≤ lam y * K y z :=
      mul_le_mul (hlmin y) hyz hpmin0.le (le_trans hlmin0.le (hlmin y))
    have h2 := mul_le_mul_of_nonneg_right h1 (hu y).le
    calc lamMin * pmin * u y ≤ lam y * K y z * u y := h2
      _ = lam y * u y * K y z := by ring
  have hup : Real.exp (ratioCap lamMin wmin L0) * (lam z * u z)
      ≤ Real.exp (ratioCap lamMin wmin L0) * u z := by
    have : lam z * u z ≤ u z := by nlinarith [(hu z).le]
    exact mul_le_mul_of_nonneg_left this hexp0.le
  have hchain : lamMin * pmin * u y ≤ Real.exp (ratioCap lamMin wmin L0) * u z := by
    linarith
  -- divide by `e^M`
  have hgoal : lamMin * pmin * Real.exp (-ratioCap lamMin wmin L0) * u y ≤ u z := by
    rw [Real.exp_neg]
    rw [show lamMin * pmin * (Real.exp (ratioCap lamMin wmin L0))⁻¹ * u y
        = (lamMin * pmin * u y) / Real.exp (ratioCap lamMin wmin L0) by ring]
    rw [div_le_iff₀ hexp0]
    linarith
  simpa only [edgeDrop] using hgoal

/-- **The theorem**: a flow whose loss is at most `L₀` and whose mass is at least `m₀` has density
at least `u_min = m₀ c^{|V|−1}` at **every** state.

This is `prop:no_distant_equilibrium`*(3)*'s "the trajectory stays in a compact subset of the open
sphere", quantified. The paper's sentence is the qualitative shadow of the chain below: from the
state where `u` is largest — where `u ≥ ∫u dλ ≥ m₀` — strong connectedness reaches every other
state, and each edge costs a factor `c`. The level sets `{u ≥ c^j u_max}` therefore gain at least
one state per step, so after `|V|−1` steps they are everything. -/
theorem pos_of_loss_le {K : V → V → ℝ} {lam u wf : V → ℝ} {lamMin pmin wmin L0 m0 : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 < u x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hL0 : lossVal lam wf logSq (ratio K lam u) ≤ L0)
    (hm0 : m0 ≤ Graph.meanL2 lam u) (x : V) :
    uMin V lamMin pmin wmin L0 m0 ≤ u x := by
  classical
  haveI : Nonempty V := nonempty_of_total htot
  set c := edgeDrop lamMin pmin wmin L0 with hcdef
  have hc0 : 0 < c := edgeDrop_pos hlmin0 hpmin0
  have hlmin1 : lamMin ≤ 1 := by
    obtain ⟨x0⟩ := ‹Nonempty V›
    refine le_trans (hlmin x0) ?_
    rw [← htot]
    exact Finset.single_le_sum (f := lam) (fun i _ => (hlam i).le) (Finset.mem_univ x0)
  have hc1 : c ≤ 1 := edgeDrop_le_one hlmin1 hpmin0 hpmin1
  have hdrop : ∀ y z : V, pmin ≤ K y z → c * u y ≤ u z := fun y z hyz =>
    edge_drop_of_loss_le hinv hK hlam htot hu hlmin hlmin0 hpmin0 hwmin hw hL0 hyz
  -- the maximiser, and the mass below it
  obtain ⟨xM, -, hxM⟩ := Finset.exists_max_image (Finset.univ : Finset V) u ⟨x, Finset.mem_univ x⟩
  have humax0 : 0 < u xM := hu xM
  have hmean_le : Graph.meanL2 lam u ≤ u xM := by
    calc Graph.meanL2 lam u = ∑ y, lam y * u y := rfl
      _ ≤ ∑ y, lam y * u xM :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hxM y (Finset.mem_univ y)) (hlam y).le
      _ = u xM := by rw [← Finset.sum_mul, htot, one_mul]
  -- the nested level sets
  set A : ℕ → Finset V := fun j => Finset.univ.filter (fun y => c ^ j * u xM ≤ u y) with hAdef
  have hmemA : ∀ (j : ℕ) (y : V), y ∈ A j ↔ c ^ j * u xM ≤ u y := by
    intro j y; simp [hAdef]
  have hA0 : xM ∈ A 0 := by rw [hmemA]; simp
  have hmono : ∀ j : ℕ, A j ⊆ A (j + 1) := by
    intro j y hy
    rw [hmemA] at hy ⊢
    refine le_trans ?_ hy
    have hpj : (0:ℝ) ≤ c ^ j := (pow_pos hc0 j).le
    have h1 : c ^ (j + 1) * u xM = c ^ j * c * u xM := by ring
    have h2 : c ^ j * c ≤ c ^ j * 1 := mul_le_mul_of_nonneg_left hc1 hpj
    have h3 : c ^ j * c * u xM ≤ c ^ j * 1 * u xM :=
      mul_le_mul_of_nonneg_right h2 humax0.le
    rw [h1]
    simpa using h3
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
          have hub : (A (k + 1)).card ≤ Fintype.card V := by
            simpa using Finset.card_le_univ (A (k + 1))
          omega
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos
  have huniv : A (Fintype.card V - 1) = Finset.univ := by
    refine Finset.eq_univ_of_card _ (le_antisymm (by simpa using Finset.card_le_univ _) ?_)
    have := hcard (Fintype.card V - 1)
    have hmin : min (Fintype.card V - 1 + 1) (Fintype.card V) = Fintype.card V := by omega
    rw [hmin] at this
    simpa using this
  have hkey : c ^ (Fintype.card V - 1) * u xM ≤ u x := by
    have : x ∈ A (Fintype.card V - 1) := by rw [huniv]; exact Finset.mem_univ x
    exact (hmemA _ x).mp this
  have hpow : (0:ℝ) ≤ c ^ (Fintype.card V - 1) := (pow_pos hc0 _).le
  calc uMin V lamMin pmin wmin L0 m0 = m0 * c ^ (Fintype.card V - 1) := rfl
    _ ≤ u xM * c ^ (Fintype.card V - 1) :=
        mul_le_mul_of_nonneg_right (le_trans hm0 hmean_le) hpow
    _ = c ^ (Fintype.card V - 1) * u xM := by ring
    _ ≤ u x := hkey


/-! ### Continuity in time, and where the localised flow lemmas live

Inside a continuation, positivity of the trajectory is exactly what is being proved, so a lemma
carrying it on all of `[0,∞)` cannot be used. `MassAscent.lossVal_antitoneOn`,
`MassAscent.mass_monotoneOn` and `Flow.nrmL2_const_on_Ici` are the forms that can be: they hold
on an arbitrary convex set `D` of times, from the pointwise-in-time derivative identities
`Flow.hasDerivAt_loss_flow_at` and `MassAscent.hasDerivAt_mass_flow`, **which ask positivity at
one time only**. That is what breaks the circularity. The three were written here and moved up
beside the theorems they generalise on 2026-09-13; what stays is the continuity
`L2Toolkit.bootstrap_of_continuous` consumes. -/

section Localised

variable {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}

/-- A gradient flow is continuous in time, state by state. -/
theorem continuous_flow (hflow : IsGradientFlow K lam nu gd u) (x : V) :
    Continuous fun t : ℝ => u t x :=
  continuous_iff_continuousAt.mpr fun t => (hflow t x).continuousAt

end Localised

/-! ### Item *(4)*: the continuation

The static bound reproduces itself at double strength — window `u ≥ u_min/2`, conclusion
`u ≥ u_min` — which is exactly the shape `L2Toolkit.bootstrap_of_continuous` propagates from
`t = 0` to all of `[0,∞)`. `LocalConvergence.sup_global` is the worked precedent. -/

/-- **`prop:no_distant_equilibrium`*(3)*'s compactness half, along the flow** (`proofs.tex:813`):
from a positive initial density the trajectory stays at density at least `u_min`, at every state
and every `t ≥ 0`, with `L₀ = 𝓛(μ₀)` and `m₀ = μ₀(𝒮̂)` — the paper's own budgets.

The continuation is genuine: `lossVal_antitoneOn` and `mass_monotoneOn` consume positivity only
on the window `[0,t]` that the bootstrap has already established. -/
theorem flow_pos_of_pos {K : V → V → ℝ} {lam wf : V → ℝ} {u : ℝ → V → ℝ}
    {lamMin pmin wmin : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    ∀ t : ℝ, 0 ≤ t → ∀ x,
      uMin V lamMin pmin wmin (lossVal lam wf logSq (ratio K lam (u 0)))
        (Graph.meanL2 lam (u 0)) ≤ u t x := by
  haveI : Nonempty V := nonempty_of_total htot
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  set L0 := lossVal lam wf logSq (ratio K lam (u 0)) with hL0def
  set m0 := Graph.meanL2 lam (u 0) with hm0def
  have hm0pos : 0 < m0 := by
    rw [hm0def]
    exact Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  set um := uMin V lamMin pmin wmin L0 m0 with humdef
  have hum0 : 0 < um := uMin_pos hlmin0 hpmin0 hm0pos
  have hstatic : ∀ v : V → ℝ, (∀ x, 0 < v x) →
      lossVal lam wf logSq (ratio K lam v) ≤ L0 → m0 ≤ Graph.meanL2 lam v →
      ∀ x, um ≤ v x := fun v hv hL hm x =>
    pos_of_loss_le hinv hK hlam htot hv hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hL hm x
  have hiff : ∀ (t : ℝ) (x : V) (b : ℝ), 0 ≤ b →
      (|max 0 (3 * um / 2 - u t x)| ≤ b ↔ 3 * um / 2 - b ≤ u t x) := by
    intro t x b hb
    rw [abs_of_nonneg (le_max_left (0:ℝ) (3 * um / 2 - u t x)), max_le_iff]
    exact ⟨fun hh => by linarith [hh.2], fun hh => ⟨hb, by linarith⟩⟩
  have hkey : ∀ t : ℝ, 0 ≤ t → ∀ x, |max 0 (3 * um / 2 - u t x)| ≤ um / 2 := by
    refine bootstrap_of_continuous (h := fun t x => max 0 (3 * um / 2 - u t x)) (eps := um)
      hum0 (fun x => continuous_const.max (continuous_const.sub (continuous_flow hflow x)))
      (fun x => ?_) fun t ht hwin x => ?_
    · rw [hiff 0 x (um / 2) (by linarith)]
      have := hstatic (u 0) hu0 le_rfl le_rfl x
      linarith
    · -- the window gives positivity on `[0,t]`, hence both budgets there
      have hupos : ∀ s ∈ Set.Icc (0:ℝ) t, ∀ y, 0 < u s y := by
        intro s hs y
        have := (hiff s y um hum0.le).mp (hwin s hs y)
        linarith
      have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) t := ⟨le_rfl, ht⟩
      have htmem : t ∈ Set.Icc (0:ℝ) t := ⟨ht, le_rfl⟩
      have hL : lossVal lam wf logSq (ratio K lam (u t)) ≤ L0 :=
        lossVal_antitoneOn (convex_Icc 0 t) hinv hK hlam hupos hflow h0mem htmem ht
      have hm : m0 ≤ Graph.meanL2 lam (u t) :=
        mass_monotoneOn (convex_Icc 0 t) hinv hK hlam hupos
          (fun y => mul_pos (hlam y) (hwpos y)) logSqDeriv_strictlyUnimodal hflow h0mem htmem ht
      rw [hiff t x (um / 2) (by linarith)]
      have := hstatic (u t) (hupos t htmem) hL hm x
      linarith
  intro t ht x
  have hb := hkey t ht x
  rw [hiff t x (um / 2) (by linarith)] at hb
  linarith

/-- **The hypothesis ten files carry, discharged on `[0,∞)`**: a gradient flow of `𝓛_{g,ν}` with
`g = (log x)²` started at a positive density stays positive.

Every consumer in `GFNBounds.Balance` states the hypothesis over **all** of `ℝ`; see the module
SCOPE, first bullet. -/
theorem flow_pos {K : V → V → ℝ} {lam wf : V → ℝ} {u : ℝ → V → ℝ} {lamMin pmin wmin : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x := by
  haveI : Nonempty V := nonempty_of_total htot
  have hm0pos : 0 < Graph.meanL2 lam (u 0) :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) Finset.univ_nonempty
  intro t ht x
  exact lt_of_lt_of_le (uMin_pos hlmin0 hpmin0 hm0pos)
    (flow_pos_of_pos hinv hK hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hu0 hflow t ht x)

/-! ### The same on the paper's own setting -/

section GraphFlow

variable [DecidableEq V] {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}

/-- **`hu`, discharged on the loop closure of a finite path-connected marked graph** — the
setting of `theo:training_speed_full` and of `prop:no_distant_equilibrium` itself. The invariant
probability is `theo:universality_graphs`*(1)*'s, and "strong connectedness" is `breach_all`.

This is precisely the hypothesis `TrainingSpeed.training_speed_full` carries, and
`TrainingSpeed.training_speed_full_of_pos` is that theorem with this in place of it. -/
theorem flow_pos_graph {lam wf : V → ℝ} {u : ℝ → V → ℝ} {lamMin pmin wmin : ℝ}
    (hpc : G.PathConnected) (hbpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (hpmin : ∀ y z : V, 0 < B.phat y z → pmin ≤ B.phat y z)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u) :
    ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x :=
  flow_pos (invariant_of_isInvProb hl) B.phat_nonneg (hl.pos hpc hbpos) hl.total
    hlmin hlmin0 hpmin0 hpmin1 (crossingFloor_phat hpc hbpos hpmin) hwmin hw hu0 hflow

end GraphFlow

/-! ### What of LaSalle can be had: the mass converges

Mathlib v4.31.0 has no `ω`-limit set and no LaSalle principle, and none is built here. What the
sentence's second half rests on that *is* available is that the mass is a bounded monotone
function of time: it converges. Its limit being the balanced point of the sphere is **not**
proved — see the module SCOPE. -/

section LaSalle

variable {K : V → V → ℝ} {lam nu wf : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}

/-- **The mass converges** — the half of the LaSalle sentence that needs no `ω`-limit: along the
flow from a positive initial density the mass is monotone on `[0,∞)` (`mass_monotoneOn`, using
`flow_pos`) and bounded above by `‖u₀‖_{L²(λ)}` (Cauchy–Schwarz on the invariant sphere), hence
convergent.

**That its limit is the balanced flow is not proved**, and is not implied by this: see the
module SCOPE. -/
theorem mass_tendsto {lamMin pmin wmin : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hpmin0 : 0 < pmin) (hpmin1 : pmin ≤ 1) (hcross : CrossingFloor K pmin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    ∃ minf : ℝ, Filter.Tendsto (fun t : ℝ => Graph.meanL2 lam (u t)) Filter.atTop (nhds minf) := by
  have hupos : ∀ s : ℝ, 0 ≤ s → ∀ x, 0 < u s x :=
    flow_pos hinv hK hlam htot hlmin hlmin0 hpmin0 hpmin1 hcross hwmin hw hu0 hflow
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  refine tendsto_atTop_of_monotoneOn_Ici
    (mass_monotoneOn (convex_Ici 0) hinv hK hlam (fun s hs => hupos s hs)
      (fun y => mul_pos (hlam y) (hwpos y)) logSqDeriv_strictlyUnimodal hflow)
    (C := Graph.nrmL2 lam (u 0)) fun τ hτ => ?_
  have hcs : Graph.meanL2 lam (u τ) ≤ Graph.nrmL2 lam (u τ) :=
    (mean_le_nrmL2_iff_const hlam htot (fun x => (hupos τ hτ x).le)).1
  rw [nrmL2_const_on_Ici hlam hupos hflow hτ] at hcs
  exact hcs

end LaSalle

/-! ### One instance, computed

The two-state chain of `prop:nonlinear_freezing`*(2)* — `T(i→j) = 1/2`, `λ = (1/2,1/2)` — at
`u = (3/2, 1/2)`, `w ≡ 1`, `g = (log x)²`.

**Computed by hand first.** `(μT)(y) = ∑_x λ(x)u(x)K(x,y) = 3/8 + 1/8 = 1/2` at both states, so
`r = (1/2)/(3/4), (1/2)/(1/4) = (2/3, 2)` and
`𝓛 = ½(log 3/2)² + ½(log 2)² ≈ 0.0822 + 0.2402 = 0.3224 ≤ 1/2 =: L₀`. The mass is
`½·3/2 + ½·1/2 = 1 =: m₀`, and `λ_min = p_min = 1/2`, `w_min = 1`. Then
`M = max(1, √(L₀/(w_min λ_min))) = max(1, √1) = 1`, `c = ½·½·e^{−1} = e^{−1}/4`, `|V| − 1 = 1`,
and

    u_min = m₀ c^{|V|−1} = e^{−1}/4 = 0.09196986…

against the true minimum `u(1) = 1/2`. The bound is non-vacuous and slack by a factor `5.4`. -/

section TwoStateCheck

/-- `u = (3/2, 1/2)` on the two-state chain. -/
noncomputable def blowupU : Fin 2 → ℝ := ![3 / 2, 1 / 2]

theorem blowupU_pos : ∀ x, 0 < blowupU x := by
  intro x; fin_cases x <;> norm_num [blowupU]

/-- Every entry of the two-state kernel is `1/2`, so `p_min = 1/2` floors every crossing. -/
theorem twoState_crossingFloor : CrossingFloor twoStateK (1 / 2 : ℝ) := by
  intro A hA hne
  obtain ⟨y, hy⟩ := hA
  obtain ⟨z, hz⟩ : ∃ z : Fin 2, z ∉ A := by
    by_contra hc
    push Not at hc
    exact hne (Finset.eq_univ_iff_forall.mpr hc)
  exact ⟨y, hy, z, hz, by norm_num [twoStateK]⟩

/-- **`r = (2/3, 2)`**, off `(μT) ≡ 1/2`. -/
theorem twoState_blowup_ratio :
    ratio twoStateK twoStateLam blowupU 0 = 2 / 3
      ∧ ratio twoStateK twoStateLam blowupU 1 = 2 := by
  constructor <;>
    · simp only [ratio, pushMass, Fin.sum_univ_two]
      norm_num [twoStateK, twoStateLam, blowupU]

/-- **The mass is `1`**. -/
theorem twoState_blowup_mean : Graph.meanL2 twoStateLam blowupU = 1 := by
  simp only [Graph.meanL2, Fin.sum_univ_two]
  norm_num [twoStateLam, blowupU]

/-- **`𝓛 ≤ 1/2`**: `(log 3/2)² ≤ 1/4` by `log x ≤ x − 1`, and `(log 2)² ≤ 3/4` by
`Real.log_two_lt_d9`. -/
theorem twoState_blowup_loss_le :
    lossVal twoStateLam (fun _ => (1 : ℝ)) logSq (ratio twoStateK twoStateLam blowupU)
      ≤ 1 / 2 := by
  have hA : logSq (2 / 3 : ℝ) ≤ 1 / 4 := by
    have hinv : ((2 : ℝ) / 3) = ((3 : ℝ) / 2)⁻¹ := by norm_num
    have hlog : Real.log ((2 : ℝ) / 3) = -Real.log (3 / 2) := by rw [hinv, Real.log_inv]
    have hle : Real.log ((3 : ℝ) / 2) ≤ 1 / 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
      linarith
    have hnn : 0 ≤ Real.log ((3 : ℝ) / 2) := Real.log_nonneg (by norm_num)
    simp only [logSq, hlog]
    nlinarith
  have hB : logSq (2 : ℝ) ≤ 3 / 4 := by
    have h1 := Real.log_two_lt_d9
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    simp only [logSq]
    nlinarith
  have hval : lossVal twoStateLam (fun _ => (1 : ℝ)) logSq (ratio twoStateK twoStateLam blowupU)
      = 1 / 2 * logSq (2 / 3) + 1 / 2 * logSq 2 := by
    simp only [lossVal, Fin.sum_univ_two, twoState_blowup_ratio.1, twoState_blowup_ratio.2]
    norm_num [twoStateLam]
  rw [hval]
  linarith

/-- **`M = 1`** on this instance: `L₀/(w_min λ_min) = 1`. -/
theorem twoState_ratioCap : ratioCap (1 / 2 : ℝ) 1 (1 / 2) = 1 := by
  simp only [ratioCap]
  norm_num

/-- **`u_min = e^{−1}/4`**, the constant evaluated. -/
theorem twoState_uMin : uMin (Fin 2) (1 / 2 : ℝ) (1 / 2) 1 (1 / 2) 1 = Real.exp (-1) / 4 := by
  simp only [uMin, edgeDrop, twoState_ratioCap, Fintype.card_fin]
  norm_num
  ring

/-- **The non-vacuity check**: `u_min = e^{−1}/4 ≈ 0.0920`, positive, at most the true minimum
`1/2`, and `pos_of_loss_le` delivers it at both states of the chain. -/
theorem twoState_boundary_blowup_check :
    uMin (Fin 2) (1 / 2 : ℝ) (1 / 2) 1 (1 / 2) 1 = Real.exp (-1) / 4
      ∧ 0 < Real.exp (-1) / 4
      ∧ Real.exp (-1) / 4 ≤ 1 / 2
      ∧ ∀ x, uMin (Fin 2) (1 / 2 : ℝ) (1 / 2) 1 (1 / 2) 1 ≤ blowupU x := by
  have hexp : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  refine ⟨twoState_uMin, by positivity, by linarith, fun x => ?_⟩
  refine pos_of_loss_le (K := twoStateK) (lam := twoStateLam) (u := blowupU)
    (wf := fun _ => (1 : ℝ)) twoStateK_invariant (fun _ _ => by norm_num [twoStateK])
    twoStateLam_pos (by norm_num [twoStateLam, Fin.sum_univ_two]) blowupU_pos
    (fun _ => by norm_num [twoStateLam]) (by norm_num) (by norm_num) (by norm_num)
    twoState_crossingFloor (by norm_num) (fun _ => le_rfl) twoState_blowup_loss_le ?_ x
  rw [twoState_blowup_mean]

end TwoStateCheck

end GFNBounds.Balance
