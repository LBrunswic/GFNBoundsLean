import GFNBounds.Balance.TrainingSpeed

/-!
# From every positive initialization, the `(log x)²` gradient flow converges to the balanced flow of its sphere

**`prop:no_distant_equilibrium`** — `proofs.tex:808–835` (statement `808–819`, proof `821–835`);
here item *(3)*'s convergence clause, `proofs.tex:813–818`, proof paragraph `830–834`.
**`theo:global_dichotomy_full`** — item *(1)*, the convergence clause, statement
`proofs.tex:841–847`, proof `proofs.tex:849–851`.

> (`prop:no_distant_equilibrium`*(3)*) *Global convergence, quantitatively.* On a finite state
> space, for `g = (log x)²` or `g = (x−1)²` and `w ≥ w_min > 0`: `|g'(x)(1−x)| ≥ δ²/2` whenever
> `|x−1| ≥ δ ∈ (0,½]`, whence
> `‖∇^λ𝓛_{g,ν}(μ)‖_{𝓜²(λ)} ≥ (w_min λ_min^{1/2}/‖u₀‖_{L²(λ)}) (δ²/2) λ(|r−1| ≥ δ)`,
> and the gradient flow from any `μ₀ ∼ λ` converges to the balanced flow of its sphere, entering
> the neighbourhood of Theorem `theo:local_convergence` in explicit time.

> (`theo:global_dichotomy_full`*(1)*, second sentence) On a finite state space with `ν = wλ`,
> `w ≥ w_min > 0`, and for `g = (log x)²` or `g = (x−1)²`, the gradient flow converges to a
> balanced flow from *every* initialization `μ₀ ∼ λ` (an explicit off-balance gradient lower
> bound; a bounded strictly unimodal generator can stall toward `r = ∞` and is not covered).

> (proof of *(3)*, convergence) […] the trajectory stays in a compact subset of the open sphere.
> By LaSalle's principle its `ω`-limit is contained in `{d/dt mass = 0}`, which by *(1)* and *(2)*
> is the single balanced point of the sphere: the flow converges to it. Quantitatively, […] after
> time at most `𝓛(μ₀)/c(δ)²` all ratios are within `δ` of `1` […] Choosing
> `δ₀ := ε₀m₀/(B̂‖u₀‖)` places the rescaled flow in the neighbourhood of Theorem
> `theo:local_convergence` […] whose exponential phase concludes.

> (proof of `theo:global_dichotomy_full`) Item *1* is Proposition `prop:no_distant_equilibrium`,
> items *(1)* and *(3)*; […]

## What is proved

| clause | declaration |
|---|---|
| continuity of `‖·‖_{L²(λ)}` (the constant's norm is `LocalConvergence.nrmL2_const`, reused) | `continuous_nrmL2` |
| *(3)*: "the gradient flow from any `μ₀ ∼ λ` converges to the balanced flow of its sphere" | **`no_distant_equilibrium_three_converges`**: `u_t → ‖u₀‖_{L²(λ)}` (the constant density) in `V → ℝ`; that constant is balanced; it lies on the sphere of `u₀`; and it is the **only** positive balanced density on that sphere |
| `theo:global_dichotomy_full`*(1)*: "converges to a balanced flow from every initialization `μ₀ ∼ λ`" | **`global_dichotomy_full_one_converges`**: `0 < ‖u₀‖`, the constant `‖u₀‖` is balanced, and `u_t` converges to it |

The mass-identity horn of `theo:global_dichotomy_full`*(1)* stays `MassIdentity.global_dichotomy_full_one`;
the gradient lower bound of *(3)* stays `Lojasiewicz.no_distant_equilibrium_three`; the entry
"in explicit time" stays `MassAscent.entry_time` and the fourth conjunct of
`TrainingSpeed.training_speed_full_of_init` (`∃ t₁ ∈ [0,T₀]`). None is restated here.

**The route.** The limit is not obtained by LaSalle (Mathlib v4.31.0 has no `ω`-limit set) but by
the proof's own *quantitative* sentence, already assembled in
`TrainingSpeed.training_speed_full_of_init`: after an entry time `t₁`,
`‖u_t/m₁ − c_∞‖_{L²(λ)} ≤ 2e^{−ϱ_σ(t−t₁)/(2m₁²)}‖(u_{t₁}/m₁ − 1)^⊥‖`. With `ϱ_σ > 0`
(`σ_* ≥ 1`, `λ_min > 0`) the right side tends to `0`; `L2Toolkit.abs_le_nrmL2_div_sqrt` turns the
`L²(λ)` bound into a pointwise one, so `u_t → m₁c_∞` state by state. The invariant sphere
(`Flow.nrmL2_const_of_flow`, positivity from `BoundaryBlowup.flow_pos_graph`) and continuity of
the norm put the limit on the sphere, `|m₁c_∞| = ‖u₀‖`, and positivity of the trajectory makes
`m₁c_∞ ≥ 0`; hence the limit is **the explicit constant `‖u₀‖_{L²(λ)}`**, not an existential one.

## Hypothesis checklist — `prop:no_distant_equilibrium`*(3)* and `theo:global_dichotomy_full`*(1)*, convergence clause

| paper hypothesis | here |
|---|---|
| `(𝒮̂, λ, T)` ergodic, on a finite state space | ⚠ **specialised**: the loop closure of a finite path-connected marked graph with a backward policy positive on its edges (`hpc`, `hpos`, `[Fintype V]`, kernel `B.phat`). A general finite ergodic chain is **not** covered. See SCOPE |
| `λ` the invariant probability | ✓ `hl : B.IsInvProb lam`; `λ > 0` is `IsInvProb.pos` |
| `g = (log x)²` | ✓ `logSqDeriv`, the gradient field of `IsGradientFlow`. ⚠ `logSqDeriv` is the definition `2 log x/x`, tied to `logSq` by `Flow.hasDerivAt_logSq`, as throughout `GFNBounds.Balance` |
| `g = (x−1)²` | ✗ **not covered**. See SCOPE |
| `ν = wλ`, `w ≥ w_min > 0` | ✓ `nu = fun x => lam x * wf x`, `hwmin`, `hw` |
| `‖w‖_{L^∞}` (not named by the clause, needed by the route) | ✓ **discharged**, not assumed: `∑_z \|w(z)\|` is used as the bound `training_speed_full_of_init` asks for |
| `σ(x)`, `N(x)` as linear systems (needed by the route, not by the clause) | ✓ **discharged**, not assumed: `Graph.BackwardPolicy.exists_isHitExp`, `exists_isGreen` |
| an edge floor `p_min` (needed by `flow_pos_graph`) | ✓ **discharged** by `BoundaryBlowup.exists_edgeFloor` |
| "from any `μ₀ ∼ λ`" | ✓ `hu0 : ∀ x, 0 < u 0 x`, and nothing about the trajectory at later times |
| "the gradient flow" | ⚠ `hflow : IsGradientFlow B.phat lam (λw) logSqDeriv u`, hypothesised of a given curve; its existence is not proved, as everywhere in `GFNBounds.Balance` |
| "converges" | ✓ `Tendsto u atTop (𝓝 _)` in `V → ℝ` (product topology). On a finite state space this is convergence of `μ_t = u_tλ` in every norm, in `𝓜²(λ)` included |
| "to **the** balanced flow **of its sphere**" | ✓ the limit is the constant density `‖u₀‖_{L²(λ)}`; it is `Balanced`, satisfies `‖·‖_{L²(λ)} = ‖u₀‖_{L²(λ)}`, and every positive balanced density on that sphere equals it (fourth conjunct, through `MassAscent.const_of_balanced_graph`) |
| "to a balanced flow" (`theo:global_dichotomy_full`*(1)*) | ✓ the same, with the limit's positivity `0 < ‖u₀‖` |
| "entering the neighbourhood of Theorem `theo:local_convergence` in explicit time" | not restated here: `training_speed_full_of_init`, fourth conjunct, and `MassAscent.entry_time` |

## SCOPE (disclosed)

* **Only `g = (log x)²`.** Both clauses also name `g = (x−1)²`. Its convergence needs the positivity
  of the trajectory, which `BoundaryBlowup.lean` proves for `logSq` only (the blow-up there is
  hard-wired to `(log x)²`), and the entry and local phases at `(x−1)²`'s constants. Scheduled as a
  separate target; nothing here speaks to it, and the map rows must keep the `(x−1)²` instance open.
* **Marked-graph loop closures only, not a general finite ergodic chain.** The route spends the
  coercivity constant `B̂_σ = σ_*/λ_min^{1/2}` from hitting times at `s₀`
  (`TrainingSpeed.hcoer_of_graph`, `prop:morozov_rate`), where the paper's proof spends `B̂` of
  Lemma `lem:sigma_mixing`, finite under ergodicity. Positivity of the trajectory
  (`flow_pos_graph`) and uniqueness of the balanced point (`const_of_balanced_graph`) are likewise
  stated on a marked graph. An abstract finite ergodic kernel is closer than that suggests:
  `flow_pos` and `MassAscent.entry_time` already hold for any invariant kernel, and
  `LocalConvergenceMixing.lean` states the local phase at summable mixing; what is missing is the
  assembly, and the uniqueness of the balanced point off a marked graph.
* **LaSalle is not proved and not used.** The convergence is the quantitative route of the same
  proof, which the paper gives beside the LaSalle sentence. Logically the Lean consumes
  `theo:local_convergence_full`, `MassAscent.entry_time`, `flow_pos_graph`, the invariant sphere and
  `prop:morozov_rate`'s coercivity, assembled in `TrainingSpeed.lean`; it does **not** consume any
  convergence statement of `theo:training_speed_full` that would itself cite this clause, so there
  is no circularity — but in the declaration DAG these two labels now sit downstream of
  `TrainingSpeed.lean`, whereas in the paper `theo:training_speed_full` cites them.
* **Existence of the gradient flow** is not proved: every statement is about a given curve
  satisfying `IsGradientFlow`, as throughout the layer.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Filter Topology

section GlobalConvergence

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- `a ↦ ‖a‖_{L²(λ)}` is continuous on `V → ℝ`. -/
theorem continuous_nrmL2 (lam : V → ℝ) : Continuous fun a : V → ℝ => Graph.nrmL2 lam a := by
  simp only [Graph.nrmL2, Graph.ipL2]
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun x _ =>
    continuous_const.mul ((continuous_apply x).mul (continuous_apply x)))

/-- **`prop:no_distant_equilibrium`*(3)*, the convergence clause, for `g = (log x)²`**: on the
loop closure of a finite path-connected marked graph, the gradient flow from any `μ₀ ∼ λ`
converges to the balanced flow of its sphere.

Four conjuncts: `u_t → ‖u₀‖_{L²(λ)}` (the constant density) in `V → ℝ`; that constant density is
balanced; it lies on the sphere `‖·‖_{L²(λ)} = ‖u₀‖_{L²(λ)}`; and it is the only positive
balanced density on that sphere. The hypotheses are the paper's: no edge floor, no `‖w‖_{L^∞}`,
no hitting-time or visit data — `training_speed_full_of_init` needs those, and they are
discharged here. -/
theorem no_distant_equilibrium_three_converges {G : Graph.MarkedGraph V}
    {B : Graph.BackwardPolicy G} {lam wf : V → ℝ} {wmin : ℝ} {u : ℝ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u) :
    Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam (u 0))
      ∧ Balanced B.phat lam (fun _ => Graph.nrmL2 lam (u 0))
      ∧ Graph.nrmL2 lam (fun _ => Graph.nrmL2 lam (u 0)) = Graph.nrmL2 lam (u 0)
      ∧ ∀ v : V → ℝ, (∀ x, 0 < v x) → Balanced B.phat lam v →
          Graph.nrmL2 lam v = Graph.nrmL2 lam (u 0) → v = fun _ => Graph.nrmL2 lam (u 0) := by
  obtain ⟨uH, hhit⟩ := Graph.BackwardPolicy.exists_isHitExp (B := B) hpc hpos
  obtain ⟨gr, hg⟩ := Graph.BackwardPolicy.exists_isGreen (B := B) hpc hpos hl
  have hwsup : ∀ x, wf x ≤ ∑ z, |wf z| := fun x =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun z => |wf z|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ x))
  obtain ⟨-, -, -, t₁, -, hm0, -, -, cinf, -, hdec⟩ :=
    training_speed_full_of_init hpc hpos hl hg hhit hwmin hw hwsup hu0 hflow
  have hlam : ∀ x, 0 < lam x := hl.pos hpc hpos
  have hinv : Invariant B.phat lam := invariant_of_isInvProb hl
  obtain ⟨pmin, hp0, hp1, hp⟩ := exists_edgeFloor B.phat
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hlam
  have hu : ∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x :=
    flow_pos_graph (lamMin := Graph.minOver G lam) hpc hpos hl
      (fun x => Graph.minOver_le lam x) hlmin0 hp0 hp1 hp hwmin hw hu0 hflow
  have hmean0 : 0 < Graph.meanL2 lam (u 0) :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) ⟨G.src, Finset.mem_univ _⟩
  set m₁ := Graph.meanL2 lam (u t₁) with hm₁_def
  have hm₁ : 0 < m₁ := lt_of_lt_of_le hmean0 hm0
  set ρ := rhoSigma 2 wmin (Graph.minOver G lam) (Graph.sigmaStar G uH) with hρ_def
  have hρ : 0 < ρ := by
    have h1 := one_le_sigmaStar hhit
    rw [hρ_def, rhoSigma]
    exact div_pos (by positivity) (pow_pos (by linarith) 2)
  set A := Graph.nrmL2 lam (perpL2 lam (fun x => u t₁ x / m₁ - 1)) with hA_def
  -- the exponential factor tends to zero
  have hlin : Tendsto (fun t : ℝ => ρ * (t - t₁) / (2 * m₁ ^ 2)) atTop atTop := by
    have hk : 0 < ρ / (2 * m₁ ^ 2) := by positivity
    have hsub : Tendsto (fun t : ℝ => t - t₁) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    refine (hsub.const_mul_atTop hk).congr fun t => ?_
    field_simp
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(ρ * (t - t₁) / (2 * m₁ ^ 2)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hbound : Tendsto
      (fun t : ℝ => m₁ * (2 * Real.exp (-(ρ * (t - t₁) / (2 * m₁ ^ 2))) * A)
        / Real.sqrt (Graph.minOver G lam)) atTop (𝓝 0) := by
    have := (((hexp.const_mul 2).mul_const A).const_mul m₁).div_const
      (Real.sqrt (Graph.minOver G lam))
    simpa only [mul_zero, zero_mul, zero_div] using this
  have hsqrt : 0 < Real.sqrt (Graph.minOver G lam) := Real.sqrt_pos.mpr hlmin0
  -- pointwise convergence to `m₁ c_∞`, from the `L²(λ)` bound
  have hconv : Tendsto u atTop (𝓝 fun _ => m₁ * cinf) := by
    rw [tendsto_pi_nhds]
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop t₁] with t ht
    have h1 := hdec t ht
    have h2 := abs_le_nrmL2_div_sqrt hlmin0 (fun z => Graph.minOver_le lam z)
      (fun z => u t z / m₁ - cinf) x
    have hsplit : u t x - m₁ * cinf = m₁ * (u t x / m₁ - cinf) := by
      field_simp
    rw [Real.norm_eq_abs, hsplit, abs_mul, abs_of_pos hm₁, le_div_iff₀ hsqrt]
    have h3 : Real.sqrt (Graph.minOver G lam) * |u t x / m₁ - cinf|
        ≤ 2 * Real.exp (-(ρ * (t - t₁) / (2 * m₁ ^ 2))) * A := h2.trans h1
    calc m₁ * |u t x / m₁ - cinf| * Real.sqrt (Graph.minOver G lam)
        = m₁ * (Real.sqrt (Graph.minOver G lam) * |u t x / m₁ - cinf|) := by ring
      _ ≤ m₁ * (2 * Real.exp (-(ρ * (t - t₁) / (2 * m₁ ^ 2))) * A) :=
        mul_le_mul_of_nonneg_left h3 hm₁.le
  -- the limit constant is nonnegative
  have hc0 : 0 ≤ m₁ * cinf :=
    ge_of_tendsto (tendsto_pi_nhds.mp hconv G.src)
      (by filter_upwards [eventually_ge_atTop 0] with t ht using (hu t ht G.src).le)
  -- the limit lies on the sphere of `u 0`
  have hsph : Graph.nrmL2 lam (fun _ => m₁ * cinf) = Graph.nrmL2 lam (u 0) := by
    have hn : Tendsto (fun t => Graph.nrmL2 lam (u t)) atTop
        (𝓝 (Graph.nrmL2 lam fun _ => m₁ * cinf)) :=
      ((continuous_nrmL2 lam).tendsto _).comp hconv
    have hn' : Tendsto (fun t => Graph.nrmL2 lam (u t)) atTop (𝓝 (Graph.nrmL2 lam (u 0))) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop 0] with t ht using
          (nrmL2_const_of_flow hlam hu hflow t ht).symm)
    exact tendsto_nhds_unique hn hn'
  have hceq : m₁ * cinf = Graph.nrmL2 lam (u 0) := by
    rw [← hsph, nrmL2_const hl.total, abs_of_nonneg hc0]
  rw [hceq] at hconv hsph
  refine ⟨hconv, balanced_const hinv _, hsph, fun v hv hbal hvn => ?_⟩
  -- uniqueness: a positive balanced density is constant, and the sphere fixes the constant
  have hconst : v = fun _ => Graph.meanL2 lam v :=
    funext fun x => const_of_balanced_graph hpc hpos hl hv hbal x
  have hmv : 0 ≤ Graph.meanL2 lam v :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hlam x).le (hv x).le
  have hmeq : Graph.meanL2 lam v = Graph.nrmL2 lam (u 0) :=
    calc Graph.meanL2 lam v = |Graph.meanL2 lam v| := (abs_of_nonneg hmv).symm
      _ = Graph.nrmL2 lam (fun _ => Graph.meanL2 lam v) :=
        (nrmL2_const hl.total _).symm
      _ = Graph.nrmL2 lam v := by rw [← hconst]
      _ = Graph.nrmL2 lam (u 0) := hvn
  rw [hconst, hmeq]

/-- **`theo:global_dichotomy_full`*(1)*, the convergence clause, for `g = (log x)²`**: on the loop
closure of a finite path-connected marked graph, with `ν = wλ` and `w ≥ w_min > 0`, the gradient
flow converges to a balanced flow from every initialization `μ₀ ∼ λ` — explicitly, to the
constant density `‖u₀‖_{L²(λ)} > 0`. The theorem's proof reads item *1* off
`prop:no_distant_equilibrium`*(1)* and *(3)*; so does this one, off
`no_distant_equilibrium_three_converges`. -/
theorem global_dichotomy_full_one_converges {G : Graph.MarkedGraph V}
    {B : Graph.BackwardPolicy G} {lam wf : V → ℝ} {wmin : ℝ} {u : ℝ → V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (hl : B.IsInvProb lam)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    (hu0 : ∀ x, 0 < u 0 x)
    (hflow : IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u) :
    0 < Graph.nrmL2 lam (u 0)
      ∧ Balanced B.phat lam (fun _ => Graph.nrmL2 lam (u 0))
      ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam (u 0)) := by
  obtain ⟨hconv, hbal, -, -⟩ :=
    no_distant_equilibrium_three_converges hpc hpos hl hwmin hw hu0 hflow
  have hlam : ∀ x, 0 < lam x := hl.pos hpc hpos
  have hmean0 : 0 < Graph.meanL2 lam (u 0) :=
    Finset.sum_pos (fun x _ => mul_pos (hlam x) (hu0 x)) ⟨G.src, Finset.mem_univ _⟩
  exact ⟨lt_of_lt_of_le hmean0
    (mean_le_nrmL2_iff_const hlam hl.total fun x => (hu0 x).le).1, hbal, hconv⟩

end GlobalConvergence

end GFNBounds.Balance
