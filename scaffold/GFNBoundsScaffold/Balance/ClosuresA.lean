import GFNBounds.Balance.DiscreteGlobal
import GFNBounds.Balance.TrainingSpeedAssembled
import GFNBounds.Graph.Universality

/-!
# Closures to bucket A: the training-speed theorem whole, and the closing paragraph of the finite-graph universality theorem

**`theo:training_speed_full`** — statement `proofs.tex:999–1035` (item *3* at `:1021–1033`), proof
`proofs.tex:1037–1093` (item *3* at `:1048–1090`); **item *3* with the balanced-start convention,
and the whole theorem assembled** (items *1*–*2* are `TrainingSpeedAssembled.lean`'s, item *3*'s
mathematics is `DiscreteGlobal.lean`'s).

**`theo:universality_graphs`** — statement `proofs.tex:1125–1141`, **the closing paragraph at
`:1140`** and its proof at `:1170`; also two findings on item *(3)* (`:1136–1138`) when `G` has an
edge `s₀ → s_f`. The sampler clause of item *(3)* is not here (Phase 3).

(Draft commit `3194054`. Line citations drift, `kb/entries/0036`.)

> (`theo:training_speed_full`, preamble) … from *every* initialization `μ₀ ∼ λ` — with
> `u₀ := dμ₀/dλ`, `m₀ := μ₀(𝒱)`, and `𝓛(μ₀)^{−1} := +∞` if `μ₀` is balanced — the gradient flow of
> `𝓛_{g,ν}` converges to the balanced flow of its sphere in the two phases *1* and *2*, and gradient
> descent with a step chosen from the initialization converges to a balanced flow as *3* states:
>
> *3.* **gradient descent** — write `‖·‖ := ‖·‖_{L²(λ)}`, write `D(u)` for the density against `λ`
> of `∇^λ𝓛_{g,ν}(uλ)` when `u > 0`, and set `u_min := m₀(λ_min p_min e^{−M})^{#𝒱−1}`. There is an
> explicit `γ_* > 0` such that, for every step `0 < γ ≤ γ_*`, there is an explicit integer `k₀(γ)`
> and the gradient descent `u_{k+1} := u_k − γD(u_k)` is well defined and satisfies:
> *(a)* for every `k ≥ 0`, `u_k ≥ u_min` pointwise, `𝓛(u_{k+1}λ) ≤ 𝓛(u_kλ) − (γ/2)‖D(u_k)‖²`,
> `Πu_{k+1} ≥ Πu_k` and `‖u_{k+1}‖² = ‖u_k‖² + γ²‖D(u_k)‖² ≤ 2‖u₀‖²`;
> *(b)* for every `k ≥ 0`, `𝓛(u_kλ) ≤ (𝓛(μ₀)^{−1} + kγκ²/4)^{−1}`;
> *(c)* for every `k ≥ k₀(γ)`, `‖u_k/Πu_k − 1‖ ≤ ε₀`, with `ε₀` as in *2*, and
> `‖u_{k+1} − Πu_{k+1}‖ ≤ (1 − γϱ_σ/(4(Πu_{k₀(γ)})²))‖u_k − Πu_k‖`, where
> `m₀ ≤ Πu_{k₀(γ)} ≤ √2‖u₀‖`;
> *(d)* `Πu_k` increases to some `m_∞ ≤ √2‖u₀‖`, `m_∞λ` is balanced, and for every `k ≥ k₀(γ)`,
> `m_∞ − Πu_k ≤ ‖u_k − Πu_k‖²/Πu_{k₀(γ)}` and `‖u_k − m_∞‖ ≤ (9/8)‖u_k − Πu_k‖`.
> No step bound independent of the initialization exists: for every `γ > 0` and every `μ₀ ∼ λ`
> that is not balanced, `su₀ − γD(su₀)` takes a negative value for every small enough `s > 0`.

> (proof, `:1051`) `γ_* := min(1/b₃, (‖u₀‖²/2)𝓛(μ₀)^{−1}, γ₀m₀²)`.

> (`theo:universality_graphs`, item *(3)* and the closing paragraph) *(3)* for `c = Z/λ(s₀)`,
> cutting the wrap edge turns this element into a generative flow on `G` satisfying the
> flow-matching constraint exactly, with initial flow of total mass `Z` carried by the edges out of
> `s₀` and terminal flow `F_term = R := Z π_←(s_f → ·)`, positive on every terminating state; in
> particular its sampler satisfies `s_τ ∼ R/Z` by Theorem `theo:sampling_theorem`.
>
> Consequently, for every target distribution `R` with full support on the terminating states of
> `G`, freezing `π_←(s_f → ·) := R` produces a frozen-backward family whose unique balanced flow
> samples `R` exactly: the universality infimum vanishes and is attained, simultaneously for every
> `p ∈ [1,+∞]` — the family is strongly universal over terminal targets.

> (proof, `:1170`) For the final statement, given a target `R` with full support on the terminating
> states, the backward policy with `π_←(s_f → ·) = R` is positive on every termination edge, so
> *(3)* applies: the balanced flow matches the target exactly, every reasonable loss vanishes on it,
> and all residuals `δF_init`, `δF_term` are zero — in every `L^p` norm at once, the state space
> being finite.

## Findings (reported, not worked around)

1. **The closing paragraph's derivation fails when `G` has an edge `s₀ → s_f`; its conclusion does
   not.** The flows and targets live on `𝒮 = 𝒱 ∖ {s₀, s_f}`, a terminating state being an internal
   state with an edge to `s_f`. A target on `𝒮` does not charge `s₀`, so freezing sets
   `π_←(s_f → s₀) = 0` on the edge `s₀ → s_f`, and the frozen policy is positive on every edge —
   the hypothesis under which the proof at `:1170` invokes *(3)* — **iff** there is no such edge
   (`freezeSink_positiveOnEdges_iff`; on the triangle `0 → 1 → 2`, `0 → 2`, `tri_check`). The
   conclusion is nevertheless proved here **with no hypothesis on that edge**
   (`universality_graphs_closing`): irreducibility, positivity and uniqueness of `λ`, and the ray of
   item *(2)*, need positivity only off `s₀ → s_f` (`breach_all_off`, `invProb_unique_off`,
   `frozenBalance_eq_off`), and item *(3)*'s flow-matching identity needs none. The repair the
   author may choose: ask positivity "on every edge except `s₀ → s_f`" in the theorem, or exclude
   the edge.
2. **Item *(3)* read on `𝒮` holds iff `G` has no edge `s₀ → s_f`.** Under the theorem's own
   hypotheses (positive on every edge), *(3)*'s flow has initial and terminal mass
   `Z(1 − π_←(s_f → s₀))` on `𝒮`, and `R := Zπ_←(s_f → ·)` charges `s₀ ∉ 𝒮` by `Zπ_←(s_f → s₀) > 0`
   (`item_three_masses_on_internal`; instance `tri_check`). So "initial flow of total mass `Z`" and
   "`F_term = R`", as distributions on `𝒮`, and with them `s_τ ∼ R/Z`, fail exactly when the edge is
   present.
3. **`:1140` freezes the sink row to `R` where `R/Z` is needed** if `R` has mass `Z` (item *(3)*'s
   `R` does); at `Z = 1` the two agree. `freezeSink` freezes to `R/Z`, and the terminal flow is `R`.

## What is proved — Part 1, `theo:training_speed_full`

| | |
|---|---|
| `ofReal_le_inv_display` | the display `L ≤ (L₀^{−1} + a)^{−1}` read in `[0,∞]`, where `0^{−1} = ∞` is the convention |
| `gammaStar_ofReal` | **`γ_*` is the printed three-term minimum in `[0,∞]`** with `𝓛(μ₀)^{−1} := +∞` — `DiscreteGlobal.gammaStar`'s case split is exactly the convention |
| `gamma0W_logSq_eq_gamma0At`, `eps0W_logSq_eq_eps0At` | item *3*'s `γ₀`, `ε₀` are Theorem 10's at `Γ₃ = sup|g'''|` (`eps0W`, `gamma0W`), the same `ε₀` as item *2* |
| **`training_speed_gd_exact`** | **item *3* as printed**, from `u₀` alone: `γ_* > 0`; `γ_*` in `[0,∞]`; balanced `↔ 𝓛(μ₀)^{−1} = ∞`; for every `0 < γ ≤ γ_*` the sequence exists and every such sequence is positive and satisfies *(a)*, *(b)* in `[0,∞]`, `𝓛(u_k) = 0` for all `k` at a balanced start, *(c)*, *(d)*; the necessity sentence for every non-balanced `μ₀` |
| **`training_speed_full_complete`** | **the whole theorem**: preamble and items *1*–*2* (`training_speed_full_paper`) and item *3* (`training_speed_gd_exact`) in one statement |
| `cycle_training_speed_complete_check` | inhabitation on the five-cycle from a non-balanced start |

## What is proved — Part 2, `theo:universality_graphs`

| | |
|---|---|
| `IsFullTarget`, `freezeSink`, `freezeSink_pb_snk`, `freezeSink_pb_of_ne` | a target of mass `Z` on the terminating states with full support; the frozen policy |
| `PositiveOffDirect`, `freezeSink_positiveOffDirect`, **`freezeSink_positiveOnEdges_iff`** | positivity off `s₀ → s_f`; freezing keeps it; full positivity iff no edge `s₀ → s_f` (finding 1) |
| `breach_of_reach_ne_snk`, `breach_of_reach_ne_src`, `breach_snk_src`, **`breach_all_off`**, `invProb_pos_off`, **`invProb_unique_off`**, **`frozenBalance_eq_off`** | item *(1)*'s irreducibility, positivity, uniqueness and item *(2)*'s ray, under positivity off `s₀ → s_f` |
| `frozenFamily`, `edgeOf`, `cutOut`, `cutPol`, `cutDefect`, `cutResidual`, `balancedMember` | `Θ_{π_←}`; a member as a generative flow on `𝒮`; `equ:FM_const`'s defect for a pair `(F_init, F_term)`; `def:universality`'s residual `‖δf_init‖_p + ‖δf_term‖_p` for the counting measure on `𝒮` |
| `edgeOf_balancedMember`, `cutDefect_edgeFlow`, `cutResidual_eq_zero` | the balanced member is *(3)*'s edge flow; `cutDefect` is the library's `fmDefect` there; zero defect on `𝒮` gives zero residual at every `p` |
| **`universality_graphs_closing`** | **the closing paragraph** — see its docstring |
| **`universality_graphs_strongly_universal`** | "strongly universal over terminal targets": for every full target, a member realizing residual `0` at every `p` for (its initial flow, `R`), both of mass `Z` on `𝒮` |
| **`item_three_masses_on_internal`** | finding 2 |
| `tri`, `triPol`, `triTarget`, **`tri_check`** | inhabitation, in the edge case: hypotheses of all of the above inhabited, finding 2 exhibited, freezing not positive on every edge, and the closing conclusion delivered |

## Hypothesis checklist — `theo:training_speed_full` (`training_speed_gd_exact`, `training_speed_full_complete`)

| paper | here |
|---|---|
| finite path-connected marked graph, backward policy positive on the loop closure's edges, `λ` its invariant probability | ✓ `[Fintype V]`, `hpc`, `hpos`, `hl` |
| `N`, `σ̄`, `σ_*` | ✓ `hg : B.IsGreen gr`, `hhit : B.IsHitExp uH` (`Graph.Morozov`'s linear-system reading, as throughout) |
| `g = (log x)²`, `ν = wλ`, `w ≥ w_min > 0`, `‖w‖_{L^∞}` | ✓ `logSq`/`logSqDeriv`, `hwmin`, `hw`; `‖w‖_{L^∞} = Graph.maxOver G wf` **exactly** |
| `p_min` the smallest positive transition probability, `λ_min`, `#𝒱` | ✓ `minPos B.phat`, `Graph.minOver G lam`, `Fintype.card V` (in `uMin`) |
| `μ₀ ∼ λ`, `u₀`, `m₀` | ✓ `hu0 : ∀ x, 0 < u0 x`, `Graph.meanL2 lam u0`; **no flow and no sequence hypothesised** |
| `𝓛(μ₀)^{−1} := +∞` at a balanced start | ✓ in `γ_*` (`gammaStar_ofReal`) and in *(b)*, both in `[0,∞]`; items *1*'s display likewise (`training_speed_full_paper`) |
| "there is an explicit `γ_* > 0` such that, for every step `0 < γ ≤ γ_*`" | ✓ `0 < γ_*` a conjunct, then `∀ γ, 0 < γ → γ ≤ γ_* → …`, `γ_*` the printed formula |
| "the gradient descent `u_{k+1} := u_k − γD(u_k)` is well defined" | ✓ the sequence exists, and every sequence with `u_0 = u₀` and the recursion has `u_k ≥ u_min > 0`; ⚠ `D` is `Flow.lossGrad`, total in Lean, its being the density of `∇^λ𝓛` is `theo:first_variation_full` |
| `ε₀`, `γ₀` of Theorem 10 at `a = 1/2`, `B̂_σ`, `C_∞ = λ_min^{−1/2}`, "`ε₀` as in *2*" | ✓ `eps0W logSq (1/2)`, `gamma0W logSq (1/2)`, the constants of `local_convergence_full_C3On`, `Γ₃ = Gamma3W logSq (1/2)`; the `ε₀` of item *2* literally |
| `ϱ_σ = g''(1)w_min λ_min/σ_*²` | ✓ `rhoSigma (deriv (deriv logSq) 1) …`, as in item *2* |
| `κ`, `M`, `u_min`, `b₃`, `k₀(γ)` | ✓ printed formulas (`kappa` expanded, `ratioCap`, `uMin`, `b3`, `k0`) |
| necessity: "for every `γ > 0` and every `μ₀ ∼ λ` that is not balanced" | ✓ `∀ γ > 0, ∀ v0 > 0, ¬ Balanced → ∃ y s₀ > 0, ∀ s ∈ (0,s₀), …`; one state `y` for all small `s`, slightly stronger |

## Hypothesis checklist — `theo:universality_graphs`, closing paragraph (`universality_graphs_closing`)

| paper | here |
|---|---|
| `G` finite, path-connected; `π_←` positive on every edge | ✓ `[Fintype V]`, `hpc`, `hB : B.PositiveOnEdges` (the rows `freezeSink` keeps) |
| total mass `Z > 0` | ✓ `hZ` |
| "target distribution `R` with full support on the terminating states" | ✓ `IsFullTarget G R Z`: `R ≥ 0`, mass `Z`, carried by internal states with an edge to `s_f`, positive on each |
| "freezing `π_←(s_f → ·) := R`" | ⚠ frozen to `R/Z` (finding 3); every other row `B`'s |
| (implicit in `:1170`) the frozen policy is positive on every edge | ✗ **false with an edge `s₀ → s_f`** (finding 1); replaced by `PositiveOffDirect`, which freezing provides, so **no hypothesis on that edge is added** |
| "frozen-backward family" | ✓ `frozenFamily`: `π_→` Markov, `f_out ≥ 0`, `FrozenBalance` |
| "unique balanced flow" | ✓ the balanced member of initial mass `Z` is in the family, non-trivial, and the only non-trivial member of initial mass `Z` |
| "samples `R` exactly" | ⚠ **not the sampler**: its terminal flow is `R` and its initial flow a distribution on `𝒮` of mass `Z`, and flow matching is exact on `𝒮`; `s_τ ∼ R/Z` is `theo:sampling_theorem`'s (Phase 3) |
| "the universality infimum vanishes and is attained, simultaneously for every `p ∈ [1,+∞]`" | ✓ for the pair `(F_init, R)`, `F_init` the balanced member's initial flow: its residual is `0` for every `p : ℝ≥0∞` (one member for all `p`), and `⨅_{θ ∈ Θ} residual = 0` for every `p` |
| "strongly universal over terminal targets" | ✓ `universality_graphs_strongly_universal` |

## SCOPE (disclosed)

**Part 1.**

* **Finite state space**, as throughout `GFNBounds.Balance`.
* **Nothing new is proved about the dynamics**: every inequality of item *3* is
  `DiscreteGlobal.training_speed_gd_minPos`'s; this part adds the quantifier structure, the exact
  `‖w‖_{L^∞}`, the identification of `ε₀`, `γ₀` with Theorem 10's at `Γ₃ = sup|g'''|`, and the
  `[0,∞]` reading of `γ_*` and *(b)*. Both displays are also available in `ℝ` (the real form of
  *(b)* for `𝓛(μ₀) > 0` is `training_speed_gd_minPos`'s).
* **`D` is `Flow.lossGrad`, a definition**, and the flow and descent are driven by it, as in
  `DiscreteGlobal.lean` and `TrainingSpeedAssembled.lean`.
* **"Every constant's dependence runs through `σ_*`, `σ̄`, `N_min` alone …"** is not a separate
  conjunct: every constant is an explicit formula whose arguments show the dependence, as in the
  source files.
* **The two printed forms of `k₀(γ)`** agree by `DiscreteGlobal.k0real_eq`; the statement uses the
  closed form.
* **"No mixing, spectral-gap or aperiodicity hypothesis is used"** holds of the signature.

**Part 2.**

* **Densities on `𝒱`, the counting measure restricted to `𝒮`.** `cutResidual` is
  `eLpNorm (D⁻) p (count.restrict 𝒮) + eLpNorm (D⁺) p (count.restrict 𝒮)` in `[0,∞]`, stated for
  every `p : ℝ≥0∞`, a superset of `[1,∞]`; `[MeasurableSpace V] [MeasurableSingletonClass V]` are
  carried.
* **The pair is fixed, the infimum runs over `Θ`.** `def:universality` fixes `(F_init, F_term)` and
  infimizes over the family; here `F_term = R` and `F_init` is the balanced member's initial flow
  `e(s₀ → ·)`, which the statement proves to be a distribution on `𝒮` of mass `Z`. The paragraph
  does not say which `F_init`; it is the only one for which a member can realize the infimum with
  terminal flow `R` and initial flow carried by the edges out of `s₀`.
* **A member is read on `𝒮` through its edge flow.** `π_→⋆(u → v) = e(u → v)/f_out⋆(u)` is Lean's
  junk `x/0 = 0` where `f_out⋆(u) = 0`; the defect consumes only the product `f_out⋆ π_→⋆`, which is
  `e` there too (the reading `Graph/Universality.lean` records). The `L^p` boundedness of `π_→⋆`
  that `def:universality` asks is automatic on a finite space and not stated.
* **The closing paragraph is proved without the hypothesis its proof needs.** The theorem's
  hypothesis `B.PositiveOnEdges` is kept (it is the paper's), and the frozen policy is shown to
  satisfy only `PositiveOffDirect`; item *(1)*–*(2)*'s lemmas are re-proved under that hypothesis
  here rather than widened in the strict `Graph/Setting.lean` and `Graph/Universality.lean`.
* **The sampler is not modelled**; `theo:sampling_theorem` is neither used nor assumed.
* **Duplication with `Core/FamilyUniversality.lean` (under audit, not imported):** `cutOut`,
  `cutPol` are its `outStar`, `fwdStarE`; `cutDefect G e (e s₀ ·) T` is its `fmDefectE G e T`;
  `cutResidual` at `F_init = e(s₀ → ·)` is its `graphResidual` (indicator on `count` versus
  `count.restrict 𝒮`); `edgeOf` is its `memberFlow`. To be merged at graduation.

**`sorry`-free.** `#print axioms` on `training_speed_gd_exact`, `training_speed_full_complete`,
`gammaStar_ofReal`, `cycle_training_speed_complete_check`, `universality_graphs_closing`,
`universality_graphs_strongly_universal`, `freezeSink_positiveOnEdges_iff`,
`item_three_masses_on_internal` and `tri_check` returns `[propext, Classical.choice, Quot.sound]`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

/-! ## Part 1 — `theo:training_speed_full`, item 3 with the balanced-start convention, and the
    whole theorem -/

namespace GFNBounds.Balance

open Finset Filter Topology
open GFNBounds.Balance.DiscreteGlobal

section Conventions

/-- **The paper's convention `𝓛(μ₀)^{−1} := +∞`, read in `[0,∞]`.** If `L_k ≤ (L₀^{−1} + a)^{−1}`
whenever `L₀ > 0`, and `L_k ≤ 0` whenever `L₀ = 0`, then
`ofReal L_k ≤ ((ofReal L₀)^{−1} + ofReal a)^{−1}` in `ℝ≥0∞`, where `0^{−1} = ∞` and `∞^{−1} = 0`. -/
theorem ofReal_le_inv_display {L0 Lk a : ℝ} (hL0 : 0 ≤ L0) (ha : 0 ≤ a)
    (hpos : 0 < L0 → Lk ≤ (L0⁻¹ + a)⁻¹) (hzero : L0 = 0 → Lk ≤ 0) :
    ENNReal.ofReal Lk ≤ ((ENNReal.ofReal L0)⁻¹ + ENNReal.ofReal a)⁻¹ := by
  rcases hL0.lt_or_eq with h | h
  · have hX : 0 < L0⁻¹ + a := by have := inv_pos.mpr h; linarith
    rw [← ENNReal.ofReal_inv_of_pos h, ← ENNReal.ofReal_add (inv_pos.mpr h).le ha,
      ← ENNReal.ofReal_inv_of_pos hX]
    exact ENNReal.ofReal_le_ofReal (hpos h)
  · rw [ENNReal.ofReal_of_nonpos (hzero h.symm)]
    exact zero_le

/-- **`γ_* := min(1/b₃, (‖u₀‖²/2)𝓛(μ₀)^{−1}, γ₀m₀²)` with `𝓛(μ₀)^{−1} := +∞`, exactly**
(`proofs.tex:1051`): `DiscreteGlobal.gammaStar`'s case split (the middle entry dropped at
`𝓛(μ₀) = 0`) is the printed minimum read in `[0,∞]`. -/
theorem gammaStar_ofReal {b3v U0 L0 γ0 m0 : ℝ} (hU0 : 0 < U0) (hL0 : 0 ≤ L0) :
    ENNReal.ofReal (gammaStar b3v U0 L0 γ0 m0)
      = min (min (ENNReal.ofReal (1 / b3v))
          (ENNReal.ofReal (U0 ^ 2 / 2) * (ENNReal.ofReal L0)⁻¹))
        (ENNReal.ofReal (γ0 * m0 ^ 2)) := by
  have hU : 0 < U0 ^ 2 / 2 := by positivity
  unfold gammaStar
  split_ifs with h
  · rw [h, ENNReal.ofReal_zero, ENNReal.inv_zero,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hU).ne', min_top_right, ENNReal.ofReal_min]
  · have hL : 0 < L0 := lt_of_le_of_ne hL0 (Ne.symm h)
    rw [ENNReal.ofReal_min, ENNReal.ofReal_min, ENNReal.ofReal_mul hU.le,
      ENNReal.ofReal_inv_of_pos hL]

/-- **Item *3*'s `γ₀` is Theorem 10's** for `g = (log x)²` at `a = 1/2`, with `Γ₃` the supremum of
`|g'''|` within the window (`TrainingSpeedAssembled.gamma0W`). -/
theorem gamma0W_logSq_eq_gamma0At (wmin W Bhat : ℝ) :
    gamma0W logSq (1/2) wmin W Bhat = gamma0At Gamma3Val wmin W Bhat := by
  simp only [gamma0W, gamma0At, logSq_deriv2_one, Gamma3W_logSq, Gamma3Val]

/-- **Item *3*'s `ε₀` is item *2*'s**, `TrainingSpeedAssembled.eps0W` at `g = (log x)²`,
`a = 1/2`. -/
theorem eps0W_logSq_eq_eps0At (wmin W Bhat lamMin : ℝ) :
    eps0W logSq (1/2) wmin W Bhat lamMin = eps0At Gamma3Val wmin W Bhat lamMin := by
  simp only [eps0W, eps0At, logSq_deriv2_one, Gamma3W_logSq, Gamma3Val]

end Conventions

section ItemThree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`theo:training_speed_full`, item *3*, as printed** (`proofs.tex:1021–1033`, proof
`:1045–1090`), from `u₀` alone, with the paper's quantifiers: *there is an explicit `γ_* > 0` such
that for every step `0 < γ ≤ γ_*` … the gradient descent `u_{k+1} := u_k − γD(u_k)` is well defined
and satisfies (a)–(d)*, and the closing necessity sentence.

Every constant is the printed formula at the paper's own values: `‖w‖_{L^∞} = max w`
(`Graph.maxOver`), `λ_min = min λ`, `p_min` the smallest positive transition probability
(`minPos`), `M = ratioCap`, `u_min`, `b₃`, `γ_*`, `κ`, `k₀(γ)`, `ϱ_σ = g''(1)w_min λ_min/σ_*²`, and
`ε₀`, `γ₀` those of `theo:local_convergence_full` for `g = (log x)²` at `a = 1/2`, `B̂_σ`,
`C_∞ = λ_min^{−1/2}`, with `Γ₃ = sup |g'''|` (`eps0W`, `gamma0W`: the same `ε₀` as item *2*).

The convention `𝓛(μ₀)^{−1} := +∞` at a balanced start is honoured twice: `γ_*` is stated in `[0,∞]`
as the printed three-term minimum, and *(b)* is stated in `[0,∞]`; `μ₀` balanced `↔`
`𝓛(μ₀)^{−1} = ∞`, and at a balanced start `𝓛(u_k) = 0` for every `k`. -/
theorem training_speed_gd_exact {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam uH wf : V → ℝ} {wmin : ℝ} {u0 : V → ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hu0 : ∀ x, 0 < u0 x) :
    0 < (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos B.phat) wmin
        (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap
        (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))) (Graph.nrmL2 lam
        u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin (Graph.maxOver G
        wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
    ∧ ENNReal.ofReal (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos
        B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap
        (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))) (Graph.nrmL2 lam
        u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin (Graph.maxOver G
        wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
        = min (min (ENNReal.ofReal (1 / b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam)
            (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam
            u0)) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam
            u0)))))
            (ENNReal.ofReal (Graph.nrmL2 lam u0 ^ 2 / 2) * (ENNReal.ofReal (lossVal lam wf logSq
                (ratio B.phat lam u0)))⁻¹))
          (ENNReal.ofReal (gamma0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam) *
              Graph.meanL2 lam u0 ^ 2))
    ∧ (Balanced B.phat lam u0 ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ = ⊤)
    ∧ (∀ γ : ℝ, 0 < γ → γ ≤ (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam)
        (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0))
        (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))))
        (Graph.nrmL2 lam u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin
        (Graph.maxOver G wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0)) →
        (∃ uk : ℕ → V → ℝ, uk 0 = u0 ∧ ∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad B.phat lam
            (fun z => lam z * wf z) logSqDeriv (uk k) x)
        ∧ ∀ uk : ℕ → V → ℝ, uk 0 = u0 →
          (∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad B.phat lam (fun z => lam z * wf z)
              logSqDeriv (uk k) x) →
          -- well defined
          0 < uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat
              lam u0)) (Graph.meanL2 lam u0) ∧ (∀ k x, 0 < uk k x)
          -- (a)
          ∧ (∀ k, (∀ x, uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq
              (ratio B.phat lam u0)) (Graph.meanL2 lam u0) ≤ uk k x)
              ∧ (lossVal lam wf logSq (ratio B.phat lam (uk (k + 1)))) ≤ (lossVal lam wf logSq
                  (ratio B.phat lam (uk k))) - γ / 2 * Graph.nrmL2 lam (lossGrad B.phat lam (fun z
                  => lam z * wf z) logSqDeriv (uk k)) ^ 2
              ∧ Graph.meanL2 lam (uk k) ≤ Graph.meanL2 lam (uk (k + 1))
              ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2
                  = Graph.nrmL2 lam (uk k) ^ 2 + γ ^ 2 * Graph.nrmL2 lam (lossGrad B.phat lam (fun
                      z => lam z * wf z) logSqDeriv (uk k)) ^ 2
              ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2 ≤ 2 * Graph.nrmL2 lam u0 ^ 2)
          -- (b), in `[0,∞]`
          ∧ (∀ k : ℕ, ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (uk k)))
              ≤ ((ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ + ENNReal.ofReal
                  (k * γ * (wmin * Real.sqrt (Graph.minOver G lam) / (Graph.nrmL2 lam u0 *
                  (Graph.maxOver G wf) * max 1 (Real.sqrt ((lossVal lam wf logSq (ratio B.phat lam
                  u0)) / (wmin * (Graph.minOver G lam)))))) ^ 2 / 4))⁻¹)
          ∧ (Balanced B.phat lam u0 → ∀ k, (lossVal lam wf logSq (ratio B.phat lam (uk k))) = 0)
          -- (c)
          ∧ Graph.meanL2 lam u0 ≤ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G
              wf) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam
              u0))) (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
              (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam
              u0)))
          ∧ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap
              (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))
              (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
              (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam
              u0))) ≤ Real.sqrt 2 * Graph.nrmL2 lam u0
          ∧ (∀ k : ℕ, (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver G
              lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH) wmin
              (Graph.minOver G lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH
              lam) (Graph.minOver G lam)) (Graph.meanL2 lam u0)) ≤ k →
              Graph.nrmL2 lam (fun x => uk k x / Graph.meanL2 lam (uk k) - 1) ≤ eps0W logSq (1/2)
                  wmin (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)
              ∧ Graph.nrmL2 lam (perpL2 lam (uk (k + 1)))
                ≤ (1 - γ * rhoSigma (deriv (deriv logSq) 1) wmin (Graph.minOver G lam)
                    (Graph.sigmaStar G uH) / (4 * Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0)
                    (Graph.maxOver G wf) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq
                    (ratio B.phat lam u0))) (Graph.sigmaStar G uH) wmin (Graph.minOver G lam)
                    (eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
                    (Graph.minOver G lam)) (Graph.meanL2 lam u0))) ^ 2))
                  * Graph.nrmL2 lam (perpL2 lam (uk k)))
          -- (d)
          ∧ Monotone (fun k => Graph.meanL2 lam (uk k))
          ∧ ∃ minf : ℝ, Tendsto (fun k => Graph.meanL2 lam (uk k)) atTop (𝓝 minf)
              ∧ minf ≤ Real.sqrt 2 * Graph.nrmL2 lam u0
              ∧ Balanced B.phat lam (fun _ => minf)
              ∧ (∀ k : ℕ, (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver
                  G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH)
                  wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf)
                  (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam u0)) ≤ k →
                  minf - Graph.meanL2 lam (uk k)
                      ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2 / Graph.meanL2 lam (uk (k0 γ
                          (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver G lam)
                          wmin (lossVal lam wf logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH)
                          wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf)
                          (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam u0)))
                  ∧ Graph.nrmL2 lam (fun x => uk k x - minf)
                      ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)))
              ∧ Tendsto (fun k => Graph.nrmL2 lam (fun x => uk k x - minf)) atTop (𝓝 0))
    -- no step bound independent of the initialization
    ∧ (∀ γ : ℝ, 0 < γ → ∀ v0 : V → ℝ, (∀ x, 0 < v0 x) → ¬ Balanced B.phat lam v0 →
        ∃ y : V, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s < s0 →
          s * v0 y - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (fun x => s * v0 x)
              y < 0) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hp x).le
  haveI := nonempty_of_total hl.total
  obtain ⟨x0⟩ := ‹Nonempty V›
  have hwsup : ∀ x, wf x ≤ Graph.maxOver G wf := fun x => Graph.le_maxOver wf x
  have hWpos : 0 < Graph.maxOver G wf := lt_of_lt_of_le hwmin (le_trans (hw x0) (hwsup x0))
  have hwpos : ∀ x, 0 < wf x := fun x => lt_of_lt_of_le hwmin (hw x)
  have hlmin0 : 0 < Graph.minOver G lam := Graph.minOver_pos hp
  have hm0 : 0 < Graph.meanL2 lam u0 :=
    Finset.sum_pos (fun x _ => mul_pos (hp x) (hu0 x)) Finset.univ_nonempty
  have hU0 : 0 < Graph.nrmL2 lam u0 :=
    lt_of_lt_of_le hm0 (mean_le_nrmL2_iff_const hp hl.total (fun x => (hu0 x).le)).1
  have hL0 : 0 ≤ (lossVal lam wf logSq (ratio B.phat lam u0)) := lossVal_nonneg hnn (fun x =>
      (hwpos x).le)
  have hum : 0 < uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq (ratio
      B.phat lam u0)) (Graph.meanL2 lam u0) := uMin_pos hlmin0 (minPos_pos _) hm0
  have hbr := (b3_bracket_ge (ratioCap_pos (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio
      B.phat lam u0))).le).2.2
  have hb3 : 0 < b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos B.phat) wmin
      (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap (Graph.minOver
      G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) := by
    rw [b3, mul_assoc]
    have := lt_of_lt_of_le (by norm_num : (0:ℝ) < 8) hbr
    positivity
  have hB := lt_of_lt_of_le zero_lt_one (one_le_BhatSigma hpc hpos hl hhit)
  have hGpos : 0 < (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos
      B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap
      (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))) (Graph.nrmL2 lam
      u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin (Graph.maxOver G
      wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0)) := by
    rw [gamma0W_logSq_eq_gamma0At]
    exact gammaStar_pos hb3 hU0 hL0
      (gamma0At_pos (le_trans (by norm_num) twentyfour_le_Gamma3Val) hwmin hWpos hB) hm0
  have hbal : Balanced B.phat lam u0 ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam
      u0)))⁻¹ = ⊤ := by
    rw [ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero,
      ← lossVal_eq_zero_iff_balanced hl.inv B.phat_nonneg hp hu0 hwpos]
    exact ⟨fun h => h.le, fun h => le_antisymm h hL0⟩
  refine ⟨hGpos, gammaStar_ofReal hU0 hL0, hbal, fun γ hγ hγs => ⟨exists_descent_seq _ _ _ _ _,
    fun uk huk0 hstep => ?_⟩, fun γ hγ v0 hv0 hnb => no_uniform_step_graph hpc hpos hl hwmin hw
      hv0 hnb hγ⟩
  subst huk0
  rw [gamma0W_logSq_eq_gamma0At] at hγs
  rw [eps0W_logSq_eq_eps0At, logSq_deriv2_one]
  obtain ⟨ha, hb, hc1, hc2, hc3, hd1, hd2⟩ :=
    training_speed_gd_minPos hpc hpos hl hhit hwmin hw hwsup hu0 hstep hγ hγs
  have hanti : ∀ k, (lossVal lam wf logSq (ratio B.phat lam (uk (k + 1)))) ≤ (lossVal lam wf logSq
      (ratio B.phat lam (uk k))) := fun k => by
    have := (ha k).2.1
    have hsq := sq_nonneg (Graph.nrmL2 lam (lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv
        (uk k)))
    nlinarith
  have hle0 : ∀ k, (lossVal lam wf logSq (ratio B.phat lam (uk k))) ≤ (lossVal lam wf logSq (ratio
      B.phat lam (uk 0))) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ n ih => exact le_trans (hanti n) ih
  have hbal0 : Balanced B.phat lam (uk 0) → ∀ k, (lossVal lam wf logSq (ratio B.phat lam (uk k))) =
      0 := by
    intro h k
    have h0 : (lossVal lam wf logSq (ratio B.phat lam (uk 0))) = 0 := (lossVal_eq_zero_iff_balanced
        hl.inv B.phat_nonneg hp hu0 hwpos).mpr h
    exact le_antisymm ((hle0 k).trans h0.le) (lossVal_nonneg hnn (fun x => (hwpos x).le))
  refine ⟨hum, fun k x => lt_of_lt_of_le hum ((ha k).1 x), ha, fun k => ?_, hbal0, hc1, hc2, hc3,
    hd1, hd2⟩
  refine ofReal_le_inv_display hL0 (by positivity) (fun _ => hb k) (fun h => ?_)
  exact (hle0 k).trans h.le

/-- **`theo:training_speed_full`, the whole statement** (`proofs.tex:999–1035`): the preamble and
items *1*–*2* (`TrainingSpeedAssembled.training_speed_full_paper`, the flow constructed, no flow
hypothesis) and item *3* (`training_speed_gd_exact`), from the paper's hypotheses and `u₀` alone,
with `𝓛(μ₀)^{−1} := +∞` at a balanced start honoured in both the flow's and the descent's
displays, and `ε₀` literally the same constant in items *2* and *3*. -/
theorem training_speed_full_complete {G : Graph.MarkedGraph V} {B : Graph.BackwardPolicy G}
    {lam gr uH wf : V → ℝ} {wmin : ℝ}
    (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    (hl : B.IsInvProb lam) (hg : B.IsGreen gr) (hhit : B.IsHitExp uH)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x)
    {u0 : V → ℝ} (hu0 : ∀ x, 0 < u0 x) :
    ((∀ x, lam x = Graph.visits G gr x / (2 + B.sigmaBar uH))
        ∧ Graph.minOver G lam = Graph.minOver G (Graph.visits G gr) / (2 + B.sigmaBar uH)
        ∧ rhoSigma (deriv (deriv logSq) 1) wmin (Graph.minOver G lam) (Graph.sigmaStar G uH)
            = 2 * wmin * Graph.minOver G (Graph.visits G gr)
                / (Graph.sigmaStar G uH ^ 2 * (2 + B.sigmaBar uH))
        ∧ ∃ u : ℝ → V → ℝ, u 0 = u0
          ∧ IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv u
          ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < u t x)
          ∧ (∀ v : ℝ → V → ℝ, v 0 = u0 →
              IsGradientFlow B.phat lam (fun x => lam x * wf x) logSqDeriv v →
              (∀ t : ℝ, 0 ≤ t → ∀ x, 0 < v t x) → ∀ t : ℝ, 0 ≤ t → v t = u t)
          ∧ Tendsto u atTop (𝓝 fun _ => Graph.nrmL2 lam u0)
          ∧ Balanced B.phat lam (fun _ => Graph.nrmL2 lam u0)
          -- item 1
          ∧ (∀ t : ℝ, 0 ≤ t →
              HasDerivAt (fun s => lossVal lam wf logSq (ratio B.phat lam (u s)))
                (-(Graph.nrmL2 lam (lossGrad B.phat lam (fun x => lam x * wf x) logSqDeriv (u t))
                  ^ 2)) t
              ∧ (wmin * Real.sqrt (Graph.minOver G lam)
                  / (Graph.nrmL2 lam u0 * Graph.maxOver G wf
                      * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam u0)
                          / (wmin * Graph.minOver G lam))))) ^ 2
                  * lossVal lam wf logSq (ratio B.phat lam (u t)) ^ 2
                ≤ Graph.nrmL2 lam (lossGrad B.phat lam (fun x => lam x * wf x) logSqDeriv (u t))
                  ^ 2)
          ∧ (∀ t : ℝ, 0 ≤ t →
              ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (u t)))
                ≤ ((ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹
                    + ENNReal.ofReal ((wmin * Real.sqrt (Graph.minOver G lam)
                        / (Graph.nrmL2 lam u0 * Graph.maxOver G wf
                            * max 1 (Real.sqrt (lossVal lam wf logSq (ratio B.phat lam u0)
                                / (wmin * Graph.minOver G lam))))) ^ 2 * t))⁻¹)
          ∧ (Balanced B.phat lam u0
              ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ = ⊤)
          -- item 2
          ∧ ∃ t₁ ∈ Set.Icc (0:ℝ)
              (4 * lossVal lam wf logSq (ratio B.phat lam u0) * Graph.nrmL2 lam u0 ^ 6
                  * Graph.sigmaStar G uH ^ 4
                / (wmin ^ 2
                    * eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
                        (Graph.minOver G lam) ^ 4
                    * Graph.meanL2 lam u0 ^ 4 * Graph.minOver G lam ^ 5)),
              Graph.meanL2 lam u0 ≤ Graph.meanL2 lam (u t₁)
                ∧ Graph.meanL2 lam (u t₁) ≤ Graph.nrmL2 lam u0
                ∧ Graph.nrmL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)
                    ≤ eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
                        (Graph.minOver G lam)
                ∧ ∃ cinf : ℝ, Balanced B.phat lam (fun _ => cinf) ∧ ∀ t : ℝ, t₁ ≤ t →
                    Graph.nrmL2 lam (fun x => u t x / Graph.meanL2 lam (u t₁) - cinf)
                      ≤ 2 * Real.exp (-(rhoSigma (deriv (deriv logSq) 1) wmin (Graph.minOver G lam)
                              (Graph.sigmaStar G uH) * (t - t₁)
                            / (2 * Graph.meanL2 lam (u t₁) ^ 2)))
                        * Graph.nrmL2 lam
                            (perpL2 lam (fun x => u t₁ x / Graph.meanL2 lam (u t₁) - 1)))
    ∧ (0 < (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos B.phat) wmin
        (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0)) (ratioCap
        (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))) (Graph.nrmL2 lam
        u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2) wmin (Graph.maxOver G
        wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
      ∧ ENNReal.ofReal (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam) (minPos
          B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0))
          (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))))
          (Graph.nrmL2 lam u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2)
          wmin (Graph.maxOver G wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0))
          = min (min (ENNReal.ofReal (1 / b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam)
              (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam
              u0)) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam
              u0)))))
              (ENNReal.ofReal (Graph.nrmL2 lam u0 ^ 2 / 2) * (ENNReal.ofReal (lossVal lam wf logSq
                  (ratio B.phat lam u0)))⁻¹))
            (ENNReal.ofReal (gamma0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam) *
                Graph.meanL2 lam u0 ^ 2))
      ∧ (Balanced B.phat lam u0 ↔ (ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ =
          ⊤)
      ∧ (∀ γ : ℝ, 0 < γ → γ ≤ (gammaStar (b3 (Graph.maxOver G wf) (uMin V (Graph.minOver G lam)
          (minPos B.phat) wmin (lossVal lam wf logSq (ratio B.phat lam u0)) (Graph.meanL2 lam u0))
          (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))))
          (Graph.nrmL2 lam u0) (lossVal lam wf logSq (ratio B.phat lam u0)) (gamma0W logSq (1/2)
          wmin (Graph.maxOver G wf) (BhatSigma G uH lam)) (Graph.meanL2 lam u0)) →
          (∃ uk : ℕ → V → ℝ, uk 0 = u0 ∧ ∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad B.phat
              lam (fun z => lam z * wf z) logSqDeriv (uk k) x)
          ∧ ∀ uk : ℕ → V → ℝ, uk 0 = u0 →
            (∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad B.phat lam (fun z => lam z * wf z)
                logSqDeriv (uk k) x) →
            -- well defined
            0 < uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq (ratio
                B.phat lam u0)) (Graph.meanL2 lam u0) ∧ (∀ k x, 0 < uk k x)
            -- (a)
            ∧ (∀ k, (∀ x, uMin V (Graph.minOver G lam) (minPos B.phat) wmin (lossVal lam wf logSq
                (ratio B.phat lam u0)) (Graph.meanL2 lam u0) ≤ uk k x)
                ∧ (lossVal lam wf logSq (ratio B.phat lam (uk (k + 1)))) ≤ (lossVal lam wf logSq
                    (ratio B.phat lam (uk k))) - γ / 2 * Graph.nrmL2 lam (lossGrad B.phat lam (fun
                    z => lam z * wf z) logSqDeriv (uk k)) ^ 2
                ∧ Graph.meanL2 lam (uk k) ≤ Graph.meanL2 lam (uk (k + 1))
                ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2
                    = Graph.nrmL2 lam (uk k) ^ 2 + γ ^ 2 * Graph.nrmL2 lam (lossGrad B.phat lam
                        (fun z => lam z * wf z) logSqDeriv (uk k)) ^ 2
                ∧ Graph.nrmL2 lam (uk (k + 1)) ^ 2 ≤ 2 * Graph.nrmL2 lam u0 ^ 2)
            -- (b), in `[0,∞]`
            ∧ (∀ k : ℕ, ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam (uk k)))
                ≤ ((ENNReal.ofReal (lossVal lam wf logSq (ratio B.phat lam u0)))⁻¹ + ENNReal.ofReal
                    (k * γ * (wmin * Real.sqrt (Graph.minOver G lam) / (Graph.nrmL2 lam u0 *
                    (Graph.maxOver G wf) * max 1 (Real.sqrt ((lossVal lam wf logSq (ratio B.phat
                    lam u0)) / (wmin * (Graph.minOver G lam)))))) ^ 2 / 4))⁻¹)
            ∧ (Balanced B.phat lam u0 → ∀ k, (lossVal lam wf logSq (ratio B.phat lam (uk k))) = 0)
            -- (c)
            ∧ Graph.meanL2 lam u0 ≤ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver
                G wf) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam
                u0))) (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
                (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam
                u0)))
            ∧ Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap
                (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))
                (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
                (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2 lam
                u0))) ≤ Real.sqrt 2 * Graph.nrmL2 lam u0
            ∧ (∀ k : ℕ, (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver G
                lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH) wmin
                (Graph.minOver G lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH
                lam) (Graph.minOver G lam)) (Graph.meanL2 lam u0)) ≤ k →
                Graph.nrmL2 lam (fun x => uk k x / Graph.meanL2 lam (uk k) - 1) ≤ eps0W logSq (1/2)
                    wmin (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)
                ∧ Graph.nrmL2 lam (perpL2 lam (uk (k + 1)))
                  ≤ (1 - γ * rhoSigma (deriv (deriv logSq) 1) wmin (Graph.minOver G lam)
                      (Graph.sigmaStar G uH) / (4 * Graph.meanL2 lam (uk (k0 γ (Graph.nrmL2 lam u0)
                      (Graph.maxOver G wf) (ratioCap (Graph.minOver G lam) wmin (lossVal lam wf
                      logSq (ratio B.phat lam u0))) (Graph.sigmaStar G uH) wmin (Graph.minOver G
                      lam) (eps0W logSq (1/2) wmin (Graph.maxOver G wf) (BhatSigma G uH lam)
                      (Graph.minOver G lam)) (Graph.meanL2 lam u0))) ^ 2))
                    * Graph.nrmL2 lam (perpL2 lam (uk k)))
            -- (d)
            ∧ Monotone (fun k => Graph.meanL2 lam (uk k))
            ∧ ∃ minf : ℝ, Tendsto (fun k => Graph.meanL2 lam (uk k)) atTop (𝓝 minf)
                ∧ minf ≤ Real.sqrt 2 * Graph.nrmL2 lam u0
                ∧ Balanced B.phat lam (fun _ => minf)
                ∧ (∀ k : ℕ, (k0 γ (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap
                    (Graph.minOver G lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))
                    (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2) wmin
                    (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam)) (Graph.meanL2
                    lam u0)) ≤ k →
                    minf - Graph.meanL2 lam (uk k)
                        ≤ Graph.nrmL2 lam (perpL2 lam (uk k)) ^ 2 / Graph.meanL2 lam (uk (k0 γ
                            (Graph.nrmL2 lam u0) (Graph.maxOver G wf) (ratioCap (Graph.minOver G
                            lam) wmin (lossVal lam wf logSq (ratio B.phat lam u0)))
                            (Graph.sigmaStar G uH) wmin (Graph.minOver G lam) (eps0W logSq (1/2)
                            wmin (Graph.maxOver G wf) (BhatSigma G uH lam) (Graph.minOver G lam))
                            (Graph.meanL2 lam u0)))
                    ∧ Graph.nrmL2 lam (fun x => uk k x - minf)
                        ≤ 9 / 8 * Graph.nrmL2 lam (perpL2 lam (uk k)))
                ∧ Tendsto (fun k => Graph.nrmL2 lam (fun x => uk k x - minf)) atTop (𝓝 0))
      -- no step bound independent of the initialization
      ∧ (∀ γ : ℝ, 0 < γ → ∀ v0 : V → ℝ, (∀ x, 0 < v0 x) → ¬ Balanced B.phat lam v0 →
          ∃ y : V, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s < s0 →
            s * v0 y - γ * lossGrad B.phat lam (fun z => lam z * wf z) logSqDeriv (fun x => s * v0
                x) y < 0)) :=
  ⟨training_speed_full_paper hpc hpos hl hg hhit hwmin hw hu0,
    training_speed_gd_exact hpc hpos hl hhit hwmin hw hu0⟩

open Graph.CycleExample in
/-- **Non-vacuity of `training_speed_full_complete`** (kb 0025) on the five-vertex cycle of
`rem:cycle_no_stalemate` at `p = 1/2`, `w ≡ 1`, from the over-inflated `uInfl 2`, which is **not**
balanced: the theorem applies with nothing hypothesised beyond the setting, `γ_* > 0`, and at
`γ = γ_*` the descent sequence exists and every iterate is positive. -/
theorem cycle_training_speed_complete_check :
    ¬ Balanced (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2)) (uInfl 2)
    ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ uk : ℕ → Fin 5 → ℝ, uk 0 = uInfl 2
        ∧ (∀ k, uk (k + 1) = fun x => uk k x - γ * lossGrad
            (pol (p := 1 / 2) (by norm_num) (by norm_num)).phat (lam (1 / 2))
            (fun z => lam (1 / 2) z * 1) logSqDeriv (uk k) x)
        ∧ ∀ k x, 0 < uk k x := by
  obtain ⟨-, hGS, -, -, hγ, -⟩ :=
    training_speed_full_complete (G := cyc) (B := pol (p := 1 / 2) (by norm_num) (by norm_num))
      (wf := fun _ => (1 : ℝ)) (wmin := 1) pathConnected (positiveOnEdges _ _) (isInvProb _ _)
      (isGreen _ _) (isHitExp _ _) one_pos (fun _ => le_rfl) (uInfl_pos (M := 2) (by norm_num))
  obtain ⟨⟨uk, h0, hrec⟩, hall⟩ := hγ _ hGS le_rfl
  obtain ⟨-, hpos, -⟩ := hall uk h0 hrec
  refine ⟨?_, _, hGS, uk, h0, hrec, hpos⟩
  rw [← ratio_eq_one_iff_balanced
    (fun y => mul_pos (lam_pos (p := 1 / 2) (by norm_num) y) (uInfl_pos (M := 2) (by norm_num) y))]
  intro h
  have h0' := h 0
  rw [ratio_src (by norm_num) (by norm_num) (by norm_num)] at h0'
  norm_num at h0'

end ItemThree

end GFNBounds.Balance

/-! ## Part 2 — `theo:universality_graphs`, the closing paragraph: attained for every `p` -/

namespace GFNBounds.Graph.ClosingClause

open Finset MeasureTheory
open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V] {G : MarkedGraph V}

/-! ### Targets, and freezing the sink row -/

/-- **A target of mass `Z` with full support on the terminating states** (`proofs.tex:1140`). The
flows of `theo:universality_graphs` live on the internal state space `𝒮 = 𝒱 ∖ {s₀, s_f}`, and a
*terminating state* is an internal state `x` with an edge `x → s_f`: `R ≥ 0`, `R(𝒮) = Z`, `R`
charges terminating states only, and charges every one of them. -/
structure IsFullTarget (G : MarkedGraph V) (R : V → ℝ) (Z : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ R x
  mass : ∑ x, R x = Z
  supp : ∀ ⦃x⦄, R x ≠ 0 → x ∈ G.internal ∧ G.Edge x G.snk
  full : ∀ ⦃x⦄, x ∈ G.internal → G.Edge x G.snk → 0 < R x

/-- **"freezing `π_←(s_f → ·) := R`"** (`proofs.tex:1140`), with the row normalized:
`π_←(s_f → ·) := R/Z`, every other row that of `B`. At `Z = 1` this is the printed `:= R`. -/
noncomputable def freezeSink (B : BackwardPolicy G) {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z)
    (hZ : 0 < Z) : BackwardPolicy G where
  pb s s' := if s = G.snk then R s' / Z else B.pb s s'
  nonneg s s' := by
    by_cases h : s = G.snk
    · simp only [h, if_true]; exact div_nonneg (hR.nonneg s') hZ.le
    · simp only [h, if_false]; exact B.nonneg s s'
  row_sum s hs := by
    by_cases h : s = G.snk
    · simp only [h, if_true]; rw [← Finset.sum_div, hR.mass, div_self hZ.ne']
    · simp only [h, if_false]; exact B.row_sum hs
  supp s s' hs hne := by
    by_cases h : s = G.snk
    · simp only [h, if_true] at hne
      have hR0 : R s' ≠ 0 := fun h0 => hne (by rw [h0, zero_div])
      rw [h]; exact (hR.supp hR0).2
    · simp only [h, if_false] at hne
      exact B.supp hs hne

theorem freezeSink_pb_snk (B : BackwardPolicy G) {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z)
    (hZ : 0 < Z) (x : V) : (freezeSink B hR hZ).pb G.snk x = R x / Z := by
  simp only [freezeSink, if_true]

theorem freezeSink_pb_of_ne (B : BackwardPolicy G) {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z)
    (hZ : 0 < Z) {s : V} (hs : s ≠ G.snk) (x : V) : (freezeSink B hR hZ).pb s x = B.pb s x := by
  simp only [freezeSink, hs, if_false]

/-- A target on `𝒮` vanishes at both marks. -/
theorem IsFullTarget.eq_zero_of_not_mem {R : V → ℝ} {Z : ℝ} (hR : IsFullTarget G R Z) {x : V}
    (hx : x ∉ G.internal) : R x = 0 := by
  by_contra h
  exact hx (hR.supp h).1

/-- **Positivity on every edge but the direct one `s₀ → s_f`.** The hypothesis the closing
paragraph actually has at its disposal after freezing: a target on `𝒮` gives `π_←(s_f → s₀) = 0`. -/
def PositiveOffDirect (B : BackwardPolicy G) : Prop :=
  ∀ ⦃s s'⦄, G.Edge s' s → s' ≠ G.src ∨ s ≠ G.snk → 0 < B.pb s s'

omit [DecidableEq V] in
theorem positiveOffDirect_of_positiveOnEdges {B : BackwardPolicy G} (hB : B.PositiveOnEdges) :
    PositiveOffDirect B := fun _ _ h _ => hB h

/-- **The frozen policy is positive on every edge but `s₀ → s_f`.** -/
theorem freezeSink_positiveOffDirect {B : BackwardPolicy G} (hB : B.PositiveOnEdges) {R : V → ℝ}
    {Z : ℝ} (hR : IsFullTarget G R Z) (hZ : 0 < Z) : PositiveOffDirect (freezeSink B hR hZ) := by
  intro s s' he hor
  by_cases hs : s = G.snk
  · subst hs
    rw [freezeSink_pb_snk]
    have hsrc : s' ≠ G.src := by
      rcases hor with h | h
      · exact h
      · exact absurd rfl h
    have hsnk : s' ≠ G.snk := fun e => G.no_edge_out_of_snk G.snk (e ▸ he)
    exact div_pos (hR.full (MarkedGraph.mem_internal.mpr ⟨hsrc, hsnk⟩) he) hZ
  · rw [freezeSink_pb_of_ne B hR hZ hs]
    exact hB he

/-- **FINDING (`proofs.tex:1140`): the closing paragraph cannot invoke item *(3)* when `s₀ → s_f`
is an edge.** The frozen policy is positive on every edge of `G` — the hypothesis of
`theo:universality_graphs` — **iff** `G` has no edge `s₀ → s_f`: a target on `𝒮` does not charge
`s₀`, so freezing sets `π_←(s_f → s₀) = 0`. -/
theorem freezeSink_positiveOnEdges_iff {B : BackwardPolicy G} (hB : B.PositiveOnEdges) {R : V → ℝ}
    {Z : ℝ} (hR : IsFullTarget G R Z) (hZ : 0 < Z) :
    (freezeSink B hR hZ).PositiveOnEdges ↔ ¬ G.Edge G.src G.snk := by
  constructor
  · intro hpos he
    have h := hpos he
    rw [freezeSink_pb_snk, hR.eq_zero_of_not_mem (fun hm => (MarkedGraph.mem_internal.mp hm).1 rfl),
      zero_div] at h
    exact lt_irrefl _ h
  · intro hno s s' he
    refine freezeSink_positiveOffDirect hB hR hZ he ?_
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    exact hno (h1 ▸ h2 ▸ he)

/-! ### Irreducibility, positivity and uniqueness under positivity off `s₀ → s_f` -/

variable {B : BackwardPolicy G}

/-- A walk of `G` ending off `s_f` is reversed by the backward chain. -/
theorem breach_of_reach_ne_snk (hP : PositiveOffDirect B) {a b : V} (h : G.Reach a b)
    (hb : b ≠ G.snk) : B.BReach b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b' c _ hbc ih =>
    have hb' : b' ≠ G.snk := fun e => G.no_edge_out_of_snk c (e ▸ hbc)
    have hc : c ≠ G.src := fun e => G.no_edge_into_src b' (e ▸ hbc)
    have hstep : B.BStep c b' := by
      show 0 < B.phat c b'
      rw [B.phat_of_ne_src hc]
      exact hP hbc (Or.inr hb)
    exact Relation.ReflTransGen.head hstep (ih hb')

/-- A walk of `G` starting off `s₀` is reversed by the backward chain. -/
theorem breach_of_reach_ne_src (hP : PositiveOffDirect B) {a b : V} (h : G.Reach a b)
    (ha : a ≠ G.src) : B.BReach b a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a' c hac _ ih =>
    have hc : c ≠ G.src := fun e => G.no_edge_into_src a' (e ▸ hac)
    have hstep : B.BStep c a' := by
      show 0 < B.phat c a'
      rw [B.phat_of_ne_src hc]
      exact hP hac (Or.inl ha)
    exact (ih hc).tail hstep

/-- `s_f` reaches `s₀` backwards: its row charges some in-neighbour. -/
theorem breach_snk_src (hpc : G.PathConnected) (hP : PositiveOffDirect B) :
    B.BReach G.snk G.src := by
  have hsnk : G.snk ≠ G.src := G.src_ne_snk.symm
  obtain ⟨y, -, hy⟩ : ∃ y ∈ Finset.univ, 0 < B.pb G.snk y := by
    by_contra hc
    push Not at hc
    have h0 : ∑ y, B.pb G.snk y = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (hc y (Finset.mem_univ y)) (B.nonneg _ _)
    rw [B.row_sum hsnk] at h0
    exact one_ne_zero h0
  have hedge : G.Edge y G.snk := B.supp hsnk hy.ne'
  have hstep : B.BStep G.snk y := by
    show 0 < B.phat G.snk y
    rw [B.phat_of_ne_src hsnk]; exact hy
  by_cases hys : y = G.src
  · rw [hys] at hstep; exact Relation.ReflTransGen.single hstep
  · have hy' : y ≠ G.snk := fun e => G.no_edge_out_of_snk G.snk (e ▸ hedge)
    exact Relation.ReflTransGen.head hstep (breach_of_reach_ne_snk hP (hpc.from_src y) hy')

/-- **Irreducibility of the backward chain under positivity off `s₀ → s_f`.** -/
theorem breach_all_off (hpc : G.PathConnected) (hP : PositiveOffDirect B) (x y : V) :
    B.BReach x y := by
  have h1 : B.BReach x G.src := by
    by_cases hx : x = G.snk
    · rw [hx]; exact breach_snk_src hpc hP
    · exact breach_of_reach_ne_snk hP (hpc.from_src x) hx
  have h2 : B.BReach G.snk y := by
    by_cases hy : y = G.src
    · rw [hy]; exact breach_snk_src hpc hP
    · exact breach_of_reach_ne_src hP (hpc.to_snk y) hy
  exact (h1.tail B.bstep_wrap).trans h2

theorem invProb_pos_off (hpc : G.PathConnected) (hP : PositiveOffDirect B) {lam : V → ℝ}
    (h : B.IsInvProb lam) (y : V) : 0 < lam y := by
  obtain ⟨x, hx⟩ := h.exists_pos
  exact h.pos_of_breach (breach_all_off hpc hP x y) hx

/-- Uniqueness of the invariant probability, `BackwardPolicy.invProb_unique`'s ratio maximum
principle under positivity off `s₀ → s_f`. -/
theorem invProb_unique_off (hpc : G.PathConnected) (hP : PositiveOffDirect B) {lam lam' : V → ℝ}
    (h : B.IsInvProb lam) (h' : B.IsInvProb lam') : lam = lam' := by
  have hp' : ∀ x, 0 < lam' x := fun x => invProb_pos_off hpc hP h' x
  obtain ⟨x0, -, hx0min⟩ := Finset.exists_min_image (Finset.univ : Finset V)
    (fun x => lam x / lam' x) ⟨G.src, Finset.mem_univ _⟩
  set t : ℝ := lam x0 / lam' x0 with ht
  have hnn : ∀ x, 0 ≤ lam x - t * lam' x := by
    intro x
    have hx : t ≤ lam x / lam' x := hx0min x (Finset.mem_univ x)
    have := (le_div_iff₀ (hp' x)).mp hx
    linarith
  have h0 : lam x0 - t * lam' x0 = 0 := by
    rw [ht, div_mul_cancel₀ _ (ne_of_gt (hp' x0)), sub_self]
  have hinv : ∀ y, ∑ x, (lam x - t * lam' x) * B.phat x y = lam y - t * lam' y := by
    intro y
    have hrw : ∀ x : V, (lam x - t * lam' x) * B.phat x y
        = lam x * B.phat x y - t * (lam' x * B.phat x y) := by
      intro x; ring
    rw [Finset.sum_congr rfl (fun x _ => hrw x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      h.inv y, h'.inv y]
  have hall : ∀ x, lam x - t * lam' x = 0 := fun x =>
    BackwardPolicy.eq_zero_of_breach hnn hinv h0 (breach_all_off hpc hP x x0)
  have ht1 : t = 1 := by
    have h1 : ∑ x, lam x = ∑ x, t * lam' x :=
      Finset.sum_congr rfl fun x _ => by have := hall x; linarith
    rw [h.total, ← Finset.mul_sum, h'.total, mul_one] at h1
    exact h1.symm
  funext x
  have := hall x
  rw [ht1, one_mul] at this
  linarith

/-- `theo:universality_graphs`*(2)*, the forward inclusion (`BackwardPolicy.frozenBalance_eq`),
under positivity off `s₀ → s_f`. -/
theorem frozenBalance_eq_off (hpc : G.PathConnected) (hP : PositiveOffDirect B) {lam : V → ℝ}
    (h : B.IsInvProb lam) {pf : V → V → ℝ} {fout : V → ℝ} (hrow : ∀ u, ∑ v, pf u v = 1)
    (hnn : ∀ x, 0 ≤ fout x) (hne : fout ≠ 0) (hfb : B.FrozenBalance pf fout) :
    0 < ∑ z, fout z ∧ (∀ x, fout x = (∑ z, fout z) * lam x) ∧ pf = B.reversal lam := by
  have hinv : ∀ y, ∑ x, fout x * B.phat x y = fout y := by
    intro u
    have h1 : ∑ v, fout u * pf u v = ∑ v, B.phat v u * fout v :=
      Finset.sum_congr rfl fun v _ => hfb u v
    rw [← Finset.mul_sum, hrow u, mul_one] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  obtain ⟨x₀, hx₀⟩ : ∃ x, fout x ≠ 0 := by
    by_contra hc
    exact hne (funext fun x => not_not.mp (not_exists.mp hc x))
  have hc : 0 < ∑ z, fout z :=
    Finset.sum_pos' (fun i _ => hnn i) ⟨x₀, Finset.mem_univ _, (hnn x₀).lt_of_ne (Ne.symm hx₀)⟩
  have heq := invProb_unique_off hpc hP (B.isInvProb_normalized hnn hc hinv) h
  have hray : ∀ x, fout x = (∑ z, fout z) * lam x := by
    intro x
    have hx : fout x / (∑ z, fout z) = lam x := congrFun heq x
    rw [div_eq_iff (ne_of_gt hc)] at hx
    rw [hx]; ring
  refine ⟨hc, hray, ?_⟩
  have hlam : ∀ x, 0 < lam x := fun x => invProb_pos_off hpc hP h x
  funext u v
  have key := hfb u v
  rw [hray u, hray v] at key
  simp only [BackwardPolicy.reversal]
  rw [eq_div_iff (hlam u).ne']
  refine mul_left_cancel₀ (ne_of_gt hc) ?_
  linear_combination key

/-! ### The family, its members as generative flows on `𝒮`, and the residual -/

/-- **The frozen-backward family `Θ_{π_←}`** (`proofs.tex:1133`): pairs `(π_→, f_out)` with `π_→` a
Markov kernel, `f_out ≥ 0`, and `(f_out μ) ⊗ π_→ = π̂_← ⊗ (f_out μ)`. -/
def frozenFamily (B : BackwardPolicy G) : Set ((V → V → ℝ) × (V → ℝ)) :=
  {θ | (∀ u, ∑ v, θ.1 u v = 1) ∧ (∀ u v, 0 ≤ θ.1 u v) ∧ (∀ x, 0 ≤ θ.2 x) ∧
    B.FrozenBalance θ.1 θ.2}

/-- The edge flow of a member, `e(u → v) = f_out(u) π_→(u → v)`; its initial flow, once the wrap
edge is cut, is `e(s₀ → ·)`. -/
def edgeOf (θ : (V → V → ℝ) × (V → ℝ)) (u v : V) : ℝ := θ.2 u * θ.1 u v

/-- The star outflow of an edge flow on `𝒮`: `f_out⋆(u) = ∑_{w ≠ s_f} e(u → w)`. -/
noncomputable def cutOut (G : MarkedGraph V) (e : V → V → ℝ) (u : V) : ℝ :=
  ∑ w ∈ univ.erase G.snk, e u w

/-- The star forward policy, `π_→⋆(u → v) = e(u → v)/f_out⋆(u)`. -/
noncomputable def cutPol (G : MarkedGraph V) (e : V → V → ℝ) (u v : V) : ℝ :=
  e u v / cutOut G e u

/-- **The defect of `equ:FM_const` on `𝒮` for the pair `(F_init, F_term)`**, the edge flow `e` read
as the generative flow `(π_→⋆, f_out⋆)` on `𝒮`:
`D(v) = F_init(v) + ((f_out⋆μ)π_→⋆)(v) − F_term(v) − f_out⋆(v)`. -/
noncomputable def cutDefect (G : MarkedGraph V) (e : V → V → ℝ) (fi ft : V → ℝ) (v : V) : ℝ :=
  fi v + (∑ u ∈ G.internal, cutOut G e u * cutPol G e u v) - ft v - cutOut G e v

/-- **`def:universality`'s residual for the pair `(F_init, F_term)`**:
`‖δf_init‖_{L^p(μ)} + ‖δf_term‖_{L^p(μ)}` in `[0,∞]`, `μ` the counting measure on `𝒮`,
`δf_init = D⁻`, `δf_term = D⁺`. -/
noncomputable def cutResidual [MeasurableSpace V] (G : MarkedGraph V) (p : ℝ≥0∞)
    (e : V → V → ℝ) (fi ft : V → ℝ) : ℝ≥0∞ :=
  eLpNorm (fun v => (cutDefect G e fi ft v)⁻) p (Measure.count.restrict (G.internal : Set V))
    + eLpNorm (fun v => (cutDefect G e fi ft v)⁺) p (Measure.count.restrict (G.internal : Set V))

/-- **The balanced flow of initial mass `Z`**: `(π̂_←^λ, (Z/λ(s₀))λ)`, item *(3)*'s element. -/
noncomputable def balancedMember (B : BackwardPolicy G) (lam : V → ℝ) (Z : ℝ) :
    (V → V → ℝ) × (V → ℝ) :=
  (B.reversal lam, fun x => Z / lam G.src * lam x)

/-- The balanced member's edge flow is item *(3)*'s `edgeFlow` at `c = Z/λ(s₀)`. -/
theorem edgeOf_balancedMember {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (Z : ℝ) :
    edgeOf (balancedMember B lam Z) = B.edgeFlow lam (Z / lam G.src) := by
  funext u v
  simp only [edgeOf, balancedMember, BackwardPolicy.reversal, BackwardPolicy.edgeFlow]
  have := (hlam u).ne'
  field_simp

/-- On item *(3)*'s flow, with its own initial flow and terminal flow, `cutDefect` **is**
`BackwardPolicy.fmDefect`. -/
theorem cutDefect_edgeFlow {lam : V → ℝ} (h : B.IsInvProb lam) (c : ℝ) (v : V) :
    cutDefect G (B.edgeFlow lam c) (B.initFlow lam c) (B.termFlow lam c) v = B.fmDefect lam c v :=
        by
  have hout : ∀ u, cutOut G (B.edgeFlow lam c) u = B.outflowStar lam c u :=
    fun u => (B.outflowStar_eq_sum h c u).symm
  simp only [cutDefect, cutPol, hout, BackwardPolicy.fmDefect, BackwardPolicy.fwdStar]

/-- A defect vanishing on `𝒮` has residual `0` at **every** `p`. -/
theorem cutResidual_eq_zero [MeasurableSpace V] [MeasurableSingletonClass V] {e : V → V → ℝ}
    {fi ft : V → ℝ} (h : ∀ v ∈ G.internal, cutDefect G e fi ft v = 0) (p : ℝ≥0∞) :
    cutResidual G p e fi ft = 0 := by
  have hneg : (fun v => (cutDefect G e fi ft v)⁻)
      =ᵐ[Measure.count.restrict (G.internal : Set V)] 0 := by
    refine (ae_restrict_iff' G.internal.measurableSet).mpr (Filter.Eventually.of_forall ?_)
    intro v hv
    simp only [Pi.zero_apply, h v hv, negPart_zero]
  have hpos : (fun v => (cutDefect G e fi ft v)⁺)
      =ᵐ[Measure.count.restrict (G.internal : Set V)] 0 := by
    refine (ae_restrict_iff' G.internal.measurableSet).mpr (Filter.Eventually.of_forall ?_)
    intro v hv
    simp only [Pi.zero_apply, h v hv, posPart_zero]
  rw [cutResidual, eLpNorm_congr_ae hneg, eLpNorm_congr_ae hpos, eLpNorm_zero, add_zero]

/-! ### The closing paragraph -/

/-- **`theo:universality_graphs`, the closing paragraph** (`proofs.tex:1140`, proof `:1167`):
*for every target `R` with full support on the terminating states of `G`, freezing
`π_←(s_f → ·) := R` produces a frozen-backward family whose unique balanced flow [matches] `R`
exactly: the universality infimum vanishes and is attained, simultaneously for every
`p ∈ [1,+∞]`.*

With `R` of mass `Z` and the row frozen to `R/Z` (`freezeSink`):

* the frozen policy has sink row `R/Z`, the other rows of `B`, and is positive on every edge but
  `s₀ → s_f` — on every edge iff there is no such edge (`freezeSink_positiveOnEdges_iff`);
* its backward chain has a unique invariant probability `λ`, positive everywhere;
* the balanced flow of initial mass `Z` lies in `Θ_{π_←}` and is the **unique** non-trivial member
  of initial mass `Z`;
* its terminal flow `e(· → s_f)` is `R`, its initial flow `e(s₀ → ·)` is a distribution carried by
  `𝒮` of mass `Z`, and so is `R`: the pair `(F_init, R)` is a pair of `def:universality`;
* flow matching holds exactly on `𝒮`, so its residual for that pair is `0` at every `p`, and the
  infimum of the residual over `Θ_{π_←}` for that pair is `0` at every `p`, attained.

**No hypothesis on the edge `s₀ → s_f`**: the paragraph's own derivation through item *(3)* needs
positivity on every edge, which freezing destroys when `s₀ → s_f` is an edge; the conclusion is
proved here from positivity off that edge. -/
theorem universality_graphs_closing [MeasurableSpace V] [MeasurableSingletonClass V]
    (hpc : G.PathConnected) (hB : B.PositiveOnEdges) {R : V → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hR : IsFullTarget G R Z) :
    (∀ x, (freezeSink B hR hZ).pb G.snk x = R x / Z)
    ∧ (∀ s, s ≠ G.snk → ∀ x, (freezeSink B hR hZ).pb s x = B.pb s x)
    ∧ PositiveOffDirect (freezeSink B hR hZ)
    ∧ ((freezeSink B hR hZ).PositiveOnEdges ↔ ¬ G.Edge G.src G.snk)
    ∧ (∃ lam : V → ℝ, (freezeSink B hR hZ).IsInvProb lam)
    ∧ (∀ lam lam' : V → ℝ, (freezeSink B hR hZ).IsInvProb lam → (freezeSink B hR hZ).IsInvProb lam'
        → lam = lam')
    ∧ ∀ lam : V → ℝ, (freezeSink B hR hZ).IsInvProb lam →
        (∀ x, 0 < lam x)
        ∧ (balancedMember (freezeSink B hR hZ) lam Z) ∈ frozenFamily (freezeSink B hR hZ)
        ∧ (balancedMember (freezeSink B hR hZ) lam Z).2 ≠ 0
        ∧ (∀ θ ∈ frozenFamily (freezeSink B hR hZ), θ.2 ≠ 0 → (∑ v, edgeOf θ G.src v = Z ↔ θ =
            (balancedMember (freezeSink B hR hZ) lam Z)))
        ∧ (∀ x, edgeOf (balancedMember (freezeSink B hR hZ) lam Z) x G.snk = R x)
        ∧ (∀ v, 0 ≤ edgeOf (balancedMember (freezeSink B hR hZ) lam Z) G.src v)
        ∧ (∀ v, v ∉ G.internal → edgeOf (balancedMember (freezeSink B hR hZ) lam Z) G.src v = 0)
        ∧ ∑ v ∈ G.internal, edgeOf (balancedMember (freezeSink B hR hZ) lam Z) G.src v = Z
        ∧ (∀ v, v ∉ G.internal → R v = 0)
        ∧ ∑ v ∈ G.internal, R v = Z
        ∧ (∀ v ∈ G.internal, cutDefect G (edgeOf (balancedMember (freezeSink B hR hZ) lam Z))
            (edgeOf (balancedMember (freezeSink B hR hZ) lam Z) G.src) R v = 0)
        ∧ (∀ p : ℝ≥0∞, cutResidual G p (edgeOf (balancedMember (freezeSink B hR hZ) lam Z)) (edgeOf
            (balancedMember (freezeSink B hR hZ) lam Z) G.src) R = 0)
        ∧ (∀ p : ℝ≥0∞,
            ⨅ θ ∈ frozenFamily (freezeSink B hR hZ), cutResidual G p (edgeOf θ) (edgeOf
                (balancedMember (freezeSink B hR hZ) lam Z) G.src) R = 0) := by
  set B' := freezeSink B hR hZ
  have hP : PositiveOffDirect B' := freezeSink_positiveOffDirect hB hR hZ
  refine ⟨freezeSink_pb_snk B hR hZ, fun s hs x => freezeSink_pb_of_ne B hR hZ hs x, hP,
    freezeSink_positiveOnEdges_iff hB hR hZ, B'.exists_invProb,
    fun _ _ h h' => invProb_unique_off hpc hP h h', fun lam hl => ?_⟩
  have hlam : ∀ x, 0 < lam x := fun x => invProb_pos_off hpc hP hl x
  have hs0 : 0 < lam G.src := hlam G.src
  set c := Z / lam G.src with hc
  have hcpos : 0 < c := div_pos hZ hs0
  have hcZ : c * lam G.src = Z := div_mul_cancel₀ Z hs0.ne'
  have hedge := edgeOf_balancedMember (B := B') hlam Z
  have hsnk_ne : G.snk ≠ G.src := G.src_ne_snk.symm
  -- the target vanishes off `𝒮`, and has mass `Z` on `𝒮`
  have hRoff : ∀ v, v ∉ G.internal → R v = 0 := fun v hv => hR.eq_zero_of_not_mem hv
  have hsplit : ∀ f : V → ℝ, (∑ v ∈ G.internal, f v) + f G.snk + f G.src = ∑ v, f v := by
    intro f
    have h1 : (∑ v ∈ (Finset.univ.erase G.src), f v) + f G.src = ∑ v, f v :=
      Finset.sum_erase_add _ _ (Finset.mem_univ _)
    have h2 : (∑ v ∈ G.internal, f v) + f G.snk = ∑ v ∈ Finset.univ.erase G.src, f v :=
      Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hsnk_ne, Finset.mem_univ _⟩)
    rw [← h1, ← h2]
  have hsrc_nm : G.src ∉ G.internal := fun hm => (MarkedGraph.mem_internal.mp hm).1 rfl
  have hsnk_nm : G.snk ∉ G.internal := fun hm => (MarkedGraph.mem_internal.mp hm).2 rfl
  have hRS : ∑ v ∈ G.internal, R v = Z := by
    have := hsplit R
    rw [hRoff _ hsnk_nm, hRoff _ hsrc_nm, hR.mass] at this
    linarith
  -- the initial flow
  have hinit : ∀ v, edgeOf (balancedMember B' lam Z) G.src v = B'.initFlow lam c v := by
    intro v; rw [hedge]; rfl
  have hinit_off : ∀ v, v ∉ G.internal → edgeOf (balancedMember B' lam Z) G.src v = 0 := by
    intro v hv
    rw [hinit]
    simp only [BackwardPolicy.initFlow, BackwardPolicy.edgeFlow]
    by_cases hvs : v = G.src
    · rw [hvs, B'.phat_src_of_ne hsnk_ne.symm, mul_zero]
    · have hvk : v = G.snk := by
        by_contra hk; exact hv (MarkedGraph.mem_internal.mpr ⟨hvs, hk⟩)
      rw [hvk, B'.phat_of_ne_src hsnk_ne, freezeSink_pb_snk, hRoff _ hsrc_nm, zero_div, mul_zero]
  have hterm : ∀ x, edgeOf (balancedMember B' lam Z) x G.snk = R x := by
    intro x
    have h := B'.termFlow_eq_target hl hcZ x
    rw [freezeSink_pb_snk] at h
    rw [hedge]
    change B'.termFlow lam c x = R x
    rw [h]; field_simp
  have hdef : ∀ v ∈ G.internal,
      cutDefect G (edgeOf (balancedMember B' lam Z)) (edgeOf (balancedMember B' lam Z) G.src) R v
        = 0 := by
    intro v hv
    have hT : R = B'.termFlow lam c := funext fun x => (hterm x).symm.trans (by rw [hedge]; rfl)
    have hI : edgeOf (balancedMember B' lam Z) G.src = B'.initFlow lam c := funext hinit
    rw [hI, hT, hedge, cutDefect_edgeFlow hl c v]
    exact B'.fmDefect_eq_zero hl hcpos.le hv
  have hmem : balancedMember B' lam Z ∈ frozenFamily B' :=
    ⟨fun u => B'.sum_reversal hl (hlam u).ne', fun u v => B'.reversal_nonneg hl.nonneg u v,
      fun x => mul_nonneg hcpos.le (hlam x).le, B'.frozenBalance_reversal hlam c⟩
  have hres : ∀ p : ℝ≥0∞,
      cutResidual G p (edgeOf (balancedMember B' lam Z)) (edgeOf (balancedMember B' lam Z) G.src) R
        = 0 := cutResidual_eq_zero hdef
  refine ⟨hlam, hmem, fun h0 => ?_, fun θ hθ hne => ?_, hterm,
    fun v => by rw [hinit]; exact B'.edgeFlow_nonneg hl.nonneg hcpos.le _ _, hinit_off, ?_, hRoff,
    hRS, hdef, hres, fun p => le_antisymm ((iInf₂_le _ hmem).trans (hres p).le) zero_le⟩
  · have := congrFun h0 G.src
    simp only [balancedMember, Pi.zero_apply] at this
    exact (mul_pos hcpos hs0).ne' this
  · obtain ⟨hrow, -, hnn, hfb⟩ := hθ
    obtain ⟨hc', hray, hpf⟩ := frozenBalance_eq_off hpc hP hl hrow hnn hne hfb
    have hmass : ∑ v, edgeOf θ G.src v = (∑ z, θ.2 z) * lam G.src := by
      simp only [edgeOf]
      rw [← Finset.mul_sum, hrow, mul_one, hray]
    rw [hmass]
    constructor
    · intro hZ'
      have hcc : (∑ z, θ.2 z) = c := by
        rw [hc, eq_div_iff hs0.ne']; exact hZ'
      refine Prod.ext hpf (funext fun x => ?_)
      simp only [balancedMember]
      rw [hray x, hcc]
    · intro hθeq
      rw [hθeq]
      simp only [balancedMember]
      rw [← Finset.mul_sum, hl.total, mul_one]
      exact hcZ
  · have := hsplit (edgeOf (balancedMember B' lam Z) G.src)
    rw [hinit_off _ hsnk_nm, hinit_off _ hsrc_nm] at this
    have hall : ∑ v, edgeOf (balancedMember B' lam Z) G.src v = Z := by
      simp only [hinit]; rw [B'.sum_initFlow hl c, hcZ]
    linarith

/-- **"The family is strongly universal over terminal targets"** (`proofs.tex:1140`): for every
target `R` of mass `Z > 0` with full support on the terminating states, the family frozen at `R`
contains a flow whose initial flow is a distribution on `𝒮` of mass `Z` and whose residual for the
pair (that initial flow, `R`) is `0` at every `p` at once. -/
theorem universality_graphs_strongly_universal [MeasurableSpace V] [MeasurableSingletonClass V]
    (hpc : G.PathConnected) (hB : B.PositiveOnEdges) :
    ∀ (R : V → ℝ) (Z : ℝ) (hZ : 0 < Z) (hR : IsFullTarget G R Z),
      ∃ θ ∈ frozenFamily (freezeSink B hR hZ),
        (∀ v, 0 ≤ edgeOf θ G.src v) ∧ (∀ v, v ∉ G.internal → edgeOf θ G.src v = 0)
        ∧ ∑ v ∈ G.internal, edgeOf θ G.src v = Z ∧ ∑ v ∈ G.internal, R v = Z
        ∧ ∀ p : ℝ≥0∞, cutResidual G p (edgeOf θ) (edgeOf θ G.src) R = 0 := by
  intro R Z hZ hR
  obtain ⟨-, -, -, -, ⟨lam, hl⟩, -, hall⟩ := universality_graphs_closing hpc hB hZ hR
  obtain ⟨-, hmem, -, -, -, hnn, hoff, hmass, -, hRS, -, hres, -⟩ := hall lam hl
  exact ⟨_, hmem, hnn, hoff, hmass, hRS, hres⟩

/-! ### FINDING: item *(3)* on `𝒮` when `s₀ → s_f` is an edge -/

/-- **FINDING (`proofs.tex:1136–1138`, item *(3)*).** Under the theorem's own hypotheses, item
*(3)*'s flow at `c = Z/λ(s₀)` has, on `𝒮`, initial and terminal mass `Z(1 − π_←(s_f → s₀))`, and its
terminal flow `F_term = Z π_←(s_f → ·)` charges `s₀ ∉ 𝒮` by `Z π_←(s_f → s₀)`. So *"initial flow of
total mass `Z`"*, *"terminal flow `F_term = R := Zπ_←(s_f → ·)`"* read on `𝒮`, and hence
`s_τ ∼ R/Z`, hold **iff** `G` has no edge `s₀ → s_f`. -/
theorem item_three_masses_on_internal (hpc : G.PathConnected) (hB : B.PositiveOnEdges)
    {lam : V → ℝ} (hl : B.IsInvProb lam) {Z c : ℝ} (hZ : 0 < Z) (hc : c = Z / lam G.src) :
    B.termFlow lam c G.src = Z * B.pb G.snk G.src
    ∧ ∑ v ∈ G.internal, B.termFlow lam c v = Z * (1 - B.pb G.snk G.src)
    ∧ ∑ v ∈ G.internal, B.initFlow lam c v = Z * (1 - B.pb G.snk G.src)
    ∧ (0 < B.pb G.snk G.src ↔ G.Edge G.src G.snk)
    ∧ (∑ v ∈ G.internal, B.termFlow lam c v = Z ↔ ¬ G.Edge G.src G.snk)
    ∧ (∑ v ∈ G.internal, B.initFlow lam c v = Z ↔ ¬ G.Edge G.src G.snk) := by
  obtain ⟨-, hcZ, -, hinit, hterm, -, -, -⟩ := B.universality_graphs_three hpc hB hl hZ hc
  have hsnk_ne : G.snk ≠ G.src := G.src_ne_snk.symm
  have hsplit : ∀ f : V → ℝ, (∑ v ∈ G.internal, f v) + f G.snk + f G.src = ∑ v, f v := by
    intro f
    have h1 : (∑ v ∈ (Finset.univ.erase G.src), f v) + f G.src = ∑ v, f v :=
      Finset.sum_erase_add _ _ (Finset.mem_univ _)
    have h2 : (∑ v ∈ G.internal, f v) + f G.snk = ∑ v ∈ Finset.univ.erase G.src, f v :=
      Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hsnk_ne, Finset.mem_univ _⟩)
    rw [← h1, ← h2]
  have hpbsnk : B.pb G.snk G.snk = 0 := by
    by_contra h
    exact G.no_edge_out_of_snk G.snk (B.supp hsnk_ne h)
  have hiff : 0 < B.pb G.snk G.src ↔ G.Edge G.src G.snk :=
    ⟨fun h => B.supp hsnk_ne h.ne', fun h => hB h⟩
  have hT : ∑ v ∈ G.internal, B.termFlow lam c v = Z * (1 - B.pb G.snk G.src) := by
    have h := hsplit (B.termFlow lam c)
    have htot : ∑ v, B.termFlow lam c v = Z := by
      simp only [hterm]; rw [← Finset.mul_sum, B.row_sum hsnk_ne, mul_one]
    rw [hterm G.snk, hterm G.src, hpbsnk, htot] at h
    linarith
  have hI : ∑ v ∈ G.internal, B.initFlow lam c v = Z * (1 - B.pb G.snk G.src) := by
    have h := hsplit (B.initFlow lam c)
    have hsrc0 : B.initFlow lam c G.src = 0 := by
      simp only [BackwardPolicy.initFlow, BackwardPolicy.edgeFlow,
        B.phat_src_of_ne hsnk_ne.symm, mul_zero]
    have hsnk0 : B.initFlow lam c G.snk = Z * B.pb G.snk G.src := by
      simp only [BackwardPolicy.initFlow, BackwardPolicy.edgeFlow, B.phat_of_ne_src hsnk_ne,
        hl.lam_snk_eq_src, hcZ]
    rw [hsrc0, hsnk0, hinit] at h
    linarith
  refine ⟨hterm G.src, hT, hI, hiff, ?_, ?_⟩
  · rw [hT, ← hiff]
    have h0 := B.nonneg G.snk G.src
    constructor
    · intro h hpos; nlinarith [mul_pos hZ hpos]
    · intro h; have : B.pb G.snk G.src = 0 := le_antisymm (not_lt.mp h) h0
      rw [this]; ring
  · rw [hI, ← hiff]
    have h0 := B.nonneg G.snk G.src
    constructor
    · intro h hpos; nlinarith [mul_pos hZ hpos]
    · intro h; have : B.pb G.snk G.src = 0 := le_antisymm (not_lt.mp h) h0
      rw [this]; ring

/-! ### Inhabitation on the triangle `s₀ = 0 → 1 → 2 = s_f`, `0 → 2`: the edge case itself -/

section Triangle

/-- The triangle `0 → 1 → 2`, `0 → 2`, with `s₀ = 0`, `s_f = 2`: the one internal state `1` is
terminating, and the direct edge `s₀ → s_f` is present. -/
def tri : MarkedGraph (Fin 3) where
  Edge x y := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 0 ∧ y = 2)
  src := 0
  snk := 2
  src_ne_snk := by decide
  no_edge_into_src x h := by
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  no_edge_out_of_snk y h := by
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

theorem tri_pathConnected : tri.PathConnected := by
  have e01 : tri.Edge 0 1 := Or.inl ⟨rfl, rfl⟩
  have e12 : tri.Edge 1 2 := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have e02 : tri.Edge 0 2 := Or.inr (Or.inr ⟨rfl, rfl⟩)
  intro s
  fin_cases s
  · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.single e02⟩
  · exact ⟨Relation.ReflTransGen.single e01, Relation.ReflTransGen.single e12⟩
  · exact ⟨Relation.ReflTransGen.single e02, Relation.ReflTransGen.refl⟩

theorem tri_edge_src_snk : tri.Edge tri.src tri.snk := Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- The backward policy `π_←(1 → 0) = 1`, `π_←(2 → 1) = π_←(2 → 0) = 1/2`. -/
noncomputable def triPol : BackwardPolicy tri where
  pb s s' := !![0, 0, 0; 1, 0, 0; 1/2, 1/2, 0] s s'
  nonneg s s' := by fin_cases s <;> fin_cases s' <;> norm_num
  row_sum s hs := by
    fin_cases s
    · exact absurd rfl hs
    · norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    · norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  supp s s' _ hne := by
    revert hne
    fin_cases s <;> fin_cases s' <;> simp [tri]

theorem triPol_positiveOnEdges : triPol.PositiveOnEdges := by
  intro s s' he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [triPol]

/-- The target `δ₁`, of mass `1`: full support on the one terminating state. -/
noncomputable def triTarget : Fin 3 → ℝ := fun x => if x = 1 then 1 else 0

theorem triTarget_full : IsFullTarget tri triTarget 1 := by
  refine ⟨fun x => ?_, ?_, fun x hx => ?_, fun x hx _ => ?_⟩
  · simp only [triTarget]; split_ifs <;> norm_num
  · simp [triTarget]
  · have h1 : x = 1 := by
      by_contra hc; exact hx (by simp only [triTarget, hc, if_false])
    subst h1
    exact ⟨MarkedGraph.mem_internal.mpr ⟨by decide, by decide⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · obtain ⟨h0, h2⟩ := MarkedGraph.mem_internal.mp hx
    have h1 : x = 1 := by
      fin_cases x
      · exact absurd rfl h0
      · rfl
      · exact absurd rfl h2
    subst h1; simp [triTarget]

/-- **The hypotheses of both findings and of the closing theorem are inhabited, in the edge case.**
On the triangle with `π_←` positive on every edge: item *(3)*'s terminal flow charges `s₀` and its
`𝒮`-mass falls short of `Z`; freezing at the full target `δ₁` is **not** positive on every edge; and
yet the closing paragraph's conclusion holds — the residual for `(F_init, δ₁)` is `0` at every `p`,
with `F_init` of mass `1` on `𝒮`. -/
theorem tri_check :
    tri.PathConnected ∧ triPol.PositiveOnEdges ∧ tri.Edge tri.src tri.snk
    ∧ (∃ lam : Fin 3 → ℝ, triPol.IsInvProb lam
        ∧ 0 < triPol.termFlow lam (1 / lam tri.src) tri.src
        ∧ ∑ v ∈ tri.internal, triPol.termFlow lam (1 / lam tri.src) v < 1)
    ∧ ¬ (freezeSink triPol triTarget_full one_pos).PositiveOnEdges
    ∧ ∃ θ ∈ frozenFamily (freezeSink triPol triTarget_full one_pos),
        ∑ v ∈ tri.internal, edgeOf θ tri.src v = 1
        ∧ ∀ p : ℝ≥0∞, cutResidual tri p (edgeOf θ) (edgeOf θ tri.src) triTarget = 0 := by
  have hpc := tri_pathConnected
  have hB := triPol_positiveOnEdges
  have he := tri_edge_src_snk
  obtain ⟨lam, hl⟩ := triPol.exists_invProb
  refine ⟨hpc, hB, he, ⟨lam, hl, ?_⟩, fun h => (freezeSink_positiveOnEdges_iff hB
    triTarget_full one_pos).mp h he, ?_⟩
  · obtain ⟨h1, h2, -, hiff, -, -⟩ :=
      item_three_masses_on_internal (Z := 1) (c := 1 / lam tri.src) hpc hB hl one_pos rfl
    have hpb : 0 < triPol.pb tri.snk tri.src := hiff.mpr he
    refine ⟨?_, ?_⟩
    · rw [h1]; linarith
    · rw [h2]; nlinarith
  · obtain ⟨θ, hθ, -, -, hmass, -, hres⟩ :=
      universality_graphs_strongly_universal hpc hB triTarget 1 one_pos triTarget_full
    exact ⟨θ, hθ, hmass, hres⟩

end Triangle

end GFNBounds.Graph.ClosingClause
