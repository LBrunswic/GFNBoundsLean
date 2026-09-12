import GFNBounds.Balance.MassAscent
import GFNBounds.Balance.LocalEnergy
import GFNBounds.Graph.Morozov

/-!
# From the ratio variable to the density variable: the local-phase rescaling step

**`theo:training_speed_full`** — statement `proofs.tex:900–920`, proof `proofs.tex:922–934`;
**the local-phase rescaling step only**, the one sentence of `proofs.tex:927` that reads "the
choice `δ₀ = ε₀m₀/(B̂_σ‖u₀‖)` places the rescaled flow inside the neighbourhood of Theorem
`theo:local_convergence`". Nothing else of the theorem is claimed here: not the two phases, not
the Łojasiewicz rate, not `T₀`, not the local exponential decay. See SCOPE.

The sentence the theorem quotes is written out one proof earlier, in the proof of
`prop:no_distant_equilibrium`*(3)* at `proofs.tex:813`, and that is the text formalized:

> Then `(P−I)u = (r−1)u` gives `‖(P−I)u‖ ≤ δ‖u₀‖`, and Lemma `lem:sigma_mixing` yields
> `‖u − Πu‖ ≤ B̂δ‖u₀‖`; since the mass `m_t := Πu_t` is nondecreasing, `m_t ≥ m₀ := μ₀(𝒮̂)`, and
> `h := u/m_t − 1` is mean-zero with `‖h‖ ≤ B̂δ‖u₀‖/m₀`. Choosing `δ₀ := ε₀m₀/(B̂‖u₀‖)` places the
> rescaled flow in the neighbourhood of Theorem `theo:local_convergence`.

## Why this file exists

`MassAscent.entry_time` closes the previous step and delivers its conclusion in the **ratio**
variable, `∀ x, |r(x) − 1| < δ`. Step 4 of `theo:local_convergence_full` wants a radius in the
**density** variable, `‖h‖ ≤ ε₀` for `h = u/m − 1`. The conversion is the sentence above and
nothing in the library performed it: `Expansion.ratio_one_add_sub_one` runs the other way, from
the density deviation to the ratio.

## What is proved

| | |
|---|---|
| `Aop_eq_ratio_sub_one_mul` | **`(P−I)u = (r−1)u`** pointwise — the load-bearing identity, with the side condition the paper does not state (see below) |
| `Aop_eq_ratio_sub_one` | the same, unapplied, for a positive density |
| `nrmL2_Aop_le_of_ratio_close` | **`‖(P−I)u‖ ≤ δ‖u‖`** from `∀ x, \|r(x) − 1\| ≤ δ` |
| `nrmL2_perpL2_le_of_ratio_close` | **`‖u − Πu‖ ≤ B̂δ‖u‖`**, the coercivity read at `u` |
| `dev_eq_smul_perpL2`, `meanL2_dev_eq_zero` | `h = m^{-1}(u − Πu)` pointwise, and `h` is mean-zero |
| `rescaled_dev_bound` | **`Πh = 0` and `‖h‖ ≤ B̂δ‖u₀‖/m₀`** — the payoff sentence |
| `mass_le_nrmL2` | `m₀ ≤ ‖u₀‖`, the one place `u ≥ 0` is spent — Cauchy–Schwarz behind the monotone ascent |
| `delta0`, `delta0_pos`, `delta0_le_eps0`, `delta0_le_half` | `δ₀ = ε₀m₀/(B̂‖u₀‖)`, an explicit formula, and the side condition `δ₀ ≤ 1/2` that `entry_time` needs and the paper never states |
| `exists_delta_for_radius` | the inversion: at `δ = δ₀` the payoff reads `‖h‖ ≤ ε₀` |
| `twoState_ratio_close`, `twoState_ratioBridge_check` | the whole chain **evaluated** on the two-state chain of `Freezing.lean`: `Au = (−1/2, 1/2)`, `m = 3/2`, `h = (1/3, −1/3)`, `‖h‖ = 1/3` against the bound `√(5/2)/3 ≈ 0.527`, and `δ₀ = 3/(4√(5/2)) ≈ 0.474 ≤ 1/2` |

## Hypothesis checklist — `theo:training_speed_full`, the local-phase rescaling step

| paper hypothesis | here |
|---|---|
| finite path-connected marked graph, backward policy positive on the loop closure | ⚠ **replaced by what the step consumes**: an abstract kernel `K` on a `Fintype`, `λ > 0`, `∑λ = 1`. The graph enters only through `hcoer`, whose inhabitant is `Graph.BackwardPolicy.coercivity_lamMin` |
| `λ` the invariant measure of the backward chain | ⚠ **not used by this step.** `Invariant K lam` appears nowhere below; the identity `(P−I)u = (r−1)u` is an algebraic identity and the rest is `L²` geometry |
| `g = (log x)²`, `ν = wλ`, `w ≥ w_min > 0` | ✗ **not carried** — no loss, no generator, no gradient appears in this step |
| the gradient flow `μ̇ = −∇𝓛` | ✗ **not carried**; `u` is a single density, not a curve. The flow enters through the two facts quoted as hypotheses below |
| `‖u_t‖ = ‖u₀‖` on the sphere (`prop:no_distant_equilibrium`*(2)*) | ⚠ **a hypothesis**, `hu0 : ‖u‖_{L²(λ)} = U0`. Its inhabitant is `Flow.nrmL2_const_of_flow` |
| `m_t ≥ m₀`, the mass being nondecreasing (`prop:no_distant_equilibrium`*(2)*) | ⚠ **a hypothesis**, `hmass : m0 ≤ Πu` with `0 < m0`. Its inhabitant is `MassAscent.mass_monotone_flow` |
| `∀ x, \|r(x) − 1\| ≤ δ` after the entry time | ⚠ **a hypothesis**, `hratio`. Its inhabitant is `MassAscent.entry_time`, which gives the strict `<` at one time `t₁ ≤ T₀` |
| Lemma `lem:sigma_mixing`, `‖h − Πh‖ ≤ B̂‖(I−P)h‖` | ⚠ **replaced by the finite hypothesis it produces**, `hcoer`, exactly as `LocalEnergy.lean` does. Inhabited by `Graph.BackwardPolicy.coercivity_lamMin` with `B̂ = σ_*/√λ_min`, and by `LocalEnergy.twoState_coercivity` with `B̂ = 1` |
| `u > 0`, `u = dμ/dλ` | ⚠ **weakened to `u x ≠ 0`** wherever that suffices, which is everywhere except the mass bound |
| `B̂ ≥ 1` | ⚠ **added, and not in the paper.** Needed by `delta0_le_eps0` and hence `delta0_le_half`, by nothing else. True of the paper's `B̂` (`β̂₀ = 1`) and of `B̂_σ`, and **not** derivable from `hcoer`: `hcoer` alone gives only `B̂ ≥ 1/2` on a Markov `K`. See SCOPE |
| `ε₀ ≤ 1/2` | ⚠ **added, and not in the paper.** Needed by `delta0_le_half` alone. See SCOPE |
| `δ₀ ≤ 1/2` | ✓ **proved**, `delta0_le_half` — the paper asserts `entry_time` at `δ₀` without checking `entry_time`'s own `δ ∈ (0,½]` |

## SCOPE (disclosed)

* **This is one step of `theo:training_speed_full` and the assembly is another file's.** The
  theorem has a global phase (`MassAscent.global_lojasiewicz_flow'`), an entry time
  (`MassAscent.entry_time`), a rescaling homogeneity (`MassAscent.flow_rescale`), a local
  exponential phase (`theo:local_convergence_full`, now `closed`; its Step 4 is `sup_global`) and the
  crossover time `T₀` of `proofs.tex:929`. **None of those is here.** What is here is the
  conversion between the two coordinates the two phases are written in. `theo:training_speed_full`
  must not be recorded as closed, or as partial in any sense wider than this, on the strength of
  this file.
* **The paper's `(P−I)u = (r−1)u` needs a side condition the paper does not print, and it is not
  the one about `λ`.** In Lean's total division the identity holds at every `y` with `u y ≠ 0`,
  and also — accidentally, both sides being `−u y` — at every `y` with `λ(y) = 0`. It **fails**
  exactly at a `y` with `λ(y) ≠ 0` and `u y = 0`: there the left side is `(μT)(y)/λ(y)`, the right
  side is `0`, and they differ whenever `y` receives mass. The paper is entitled to the identity
  because its `u = dμ/dλ` is positive (`μ ∼ λ`, hypothesised in `prop:no_distant_equilibrium`),
  but the hypothesis is `u ≠ 0`, not `λ ≠ 0`, and a reader porting the line to a flow allowed to
  vanish would be wrong. `Aop_eq_ratio_sub_one_mul` carries `u y ≠ 0`.
* **`B̂ ≥ 1` is a hypothesis, not a consequence.** `hcoer` says `‖f^⊥‖ ≤ B̂‖Af‖`, and the library
  already bounds the other direction: `L2Toolkit.Aop_perpL2` gives `Af = Af^⊥` off the null set of
  `λ` and `L2Toolkit.nrmL2_Aop_le_two` gives `‖Af^⊥‖ ≤ 2‖f^⊥‖` on a Markov `K` with invariant `λ`,
  so `hcoer` forces only `B̂ ≥ 1/2` and not `B̂ ≥ 1`. The
  paper's `B̂ = ∑_n β̂_n` has `β̂₀ = 1`, so `B̂ ≥ 1` there; `B̂_σ = σ_*/√λ_min ≥ 1` because
  `σ_* ≥ 1` and `λ_min ≤ 1`. Neither argument is formalized here, so the inequality is carried as
  a hypothesis on the two lemmas that use it and on no other.
* **`ε₀ ≤ 1/2` is a hypothesis too.** `δ₀ ≤ ε₀` is what `B̂ ≥ 1` and `m₀ ≤ ‖u₀‖` buy
  (`delta0_le_eps0`); turning that into `entry_time`'s `δ ≤ 1/2` needs `ε₀ ≤ 1/2`. The paper reads
  `entry_time` at `δ₀` without remarking that `entry_time` restricts `δ` to `(0,½]`; the
  restriction is real — `prop:no_distant_equilibrium`*(3)*'s pointwise bound `|g'(x)(1−x)| ≥ δ²/2`
  is proved only for `δ ≤ 1/2` — and `ε₀ ≤ 1/2` is the cheapest way to meet it. It costs nothing:
  `ε₀` is a neighbourhood radius for `‖h‖`, and `theo:local_convergence_full` already asks for
  `ε ≤ min(a,1)/4 ≤ 1/4`.
* **No flow, no time.** Every statement is about a single density `u`. The two facts the paper
  gets from the flow — the invariant sphere and the nondecreasing mass — are hypotheses
  `hu0` and `hmass`, each with a named inhabitant in `MassAscent.lean`.
* **`sorry`-free.** Nothing below is open. Graduated into the strict library on 2026-09-12.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

section RatioBridge

variable {V : Type*} [Fintype V]

/-! ### `(P − I)u = (r − 1)u`

`proofs.tex:813`. `Aop K lam u y = (μT)(y)/λ(y) − u(y)` and `ratio K lam u y = (μT)(y)/μ(y)`, so
multiplying the ratio by `u(y)` converts one denominator into the other. That conversion is where
`u y ≠ 0` is spent, and it is the only hypothesis the identity has. -/

/-- **`(P−I)u = (r−1)u` at a state** (`proofs.tex:813`): `Au y = (r(y) − 1)u(y)` whenever
`u y ≠ 0`.

The hypothesis is on `u`, not on `λ`. Where `λ(y) = 0` the identity holds anyway, both sides being
`−u(y)` under Lean's `x/0 = 0`; where `λ(y) ≠ 0` and `u(y) = 0` it **fails**, the left side being
`(μT)(y)/λ(y)` and the right side `0`. See the module SCOPE. -/
theorem Aop_eq_ratio_sub_one_mul {K : V → V → ℝ} {lam u : V → ℝ} {y : V} (hy : u y ≠ 0) :
    Aop K lam u y = (ratio K lam u y - 1) * u y := by
  have hsum : ∑ x, lam x * K x y * u x = ∑ x, lam x * u x * K x y :=
    Finset.sum_congr rfl fun x _ => by ring
  simp only [Aop_apply, Core.densAct_apply, ratio, pushMass, hsum]
  rcases eq_or_ne (lam y) 0 with hl | hl
  · rw [hl]
    simp
  · field_simp

/-- **`(P−I)u = (r−1)u`**, unapplied, for a nowhere-vanishing density — the form a norm consumes.
-/
theorem Aop_eq_ratio_sub_one {K : V → V → ℝ} {lam u : V → ℝ} (hu : ∀ x, u x ≠ 0) :
    Aop K lam u = fun y => (ratio K lam u y - 1) * u y := by
  funext y
  exact Aop_eq_ratio_sub_one_mul (hu y)

/-! ### `‖(P−I)u‖ ≤ δ‖u‖`, then `‖u − Πu‖ ≤ B̂δ‖u‖` -/

/-- **`‖(P−I)u‖_{L²(λ)} ≤ δ‖u‖_{L²(λ)}`** (`proofs.tex:813`): the ratios lying in the band
`|r − 1| ≤ δ` dominate `Au` by `δ|u|` state by state, and `L2Toolkit.nrmL2_le_of_abs_le` lifts
that to the norm. -/
theorem nrmL2_Aop_le_of_ratio_close {K : V → V → ℝ} {lam u : V → ℝ} {δ : ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (hu : ∀ x, u x ≠ 0) (hδ : 0 ≤ δ)
    (hratio : ∀ x, |ratio K lam u x - 1| ≤ δ) :
    Graph.nrmL2 lam (Aop K lam u) ≤ δ * Graph.nrmL2 lam u := by
  refine nrmL2_le_of_abs_le hnn hδ fun x => ?_
  rw [Aop_eq_ratio_sub_one_mul (hu x), abs_mul]
  exact mul_le_mul_of_nonneg_right (hratio x) (abs_nonneg _)

/-- **`‖u − Πu‖_{L²(λ)} ≤ B̂δ‖u‖_{L²(λ)}`** (`proofs.tex:813`, "Lemma `lem:sigma_mixing` yields
`‖u − Πu‖ ≤ B̂δ‖u₀‖`"): the coercivity read at `u` itself, composed with the previous bound.

`hcoer` is the finite face of `lem:sigma_mixing`, hypothesised rather than derived, exactly as in
`LocalEnergy.lean`. It is inhabited: `Graph.BackwardPolicy.coercivity_lamMin` gives it with
`B̂ = σ_*/√λ_min`, and `LocalEnergy.twoState_coercivity` with `B̂ = 1`. -/
theorem nrmL2_perpL2_le_of_ratio_close {K : V → V → ℝ} {lam u : V → ℝ} {Bhat δ : ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (hu : ∀ x, u x ≠ 0) (hδ : 0 ≤ δ) (hB0 : 0 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (hratio : ∀ x, |ratio K lam u x - 1| ≤ δ) :
    Graph.nrmL2 lam (perpL2 lam u) ≤ Bhat * δ * Graph.nrmL2 lam u := by
  calc Graph.nrmL2 lam (perpL2 lam u)
      ≤ Bhat * Graph.nrmL2 lam (Aop K lam u) := hcoer u
    _ ≤ Bhat * (δ * Graph.nrmL2 lam u) :=
        mul_le_mul_of_nonneg_left (nrmL2_Aop_le_of_ratio_close hnn hu hδ hratio) hB0
    _ = Bhat * δ * Graph.nrmL2 lam u := by ring

/-! ### The rescaled density deviation `h = u/m − 1` -/

/-- **`h = m^{-1}(u − Πu)`** (`proofs.tex:813`): the deviation of the rescaled density is the
orthogonal part of `u` divided by the mass, because `Πu` **is** `m`. -/
theorem dev_eq_smul_perpL2 {lam u : V → ℝ} {m : ℝ} (hm : m ≠ 0)
    (hmdef : Graph.meanL2 lam u = m) :
    (fun x => u x / m - 1) = fun x => m⁻¹ * perpL2 lam u x := by
  funext x
  rw [perpL2_apply, hmdef]
  field_simp

/-- **`Πh = 0`** (`proofs.tex:813`, "`h := u/m_t − 1` is mean-zero"), on a probability `λ`. -/
theorem meanL2_dev_eq_zero {lam u : V → ℝ} (htot : ∑ x, lam x = 1) {m : ℝ} (hm : m ≠ 0)
    (hmdef : Graph.meanL2 lam u = m) :
    Graph.meanL2 lam (fun x => u x / m - 1) = 0 := by
  have hdiv : ∑ x, lam x * (u x / m) = (∑ x, lam x * u x) / m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hmu : (∑ x, lam x * u x) = m := hmdef
  simp only [Graph.meanL2, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, htot, hdiv, hmu, div_self hm, sub_self]

/-- **The payoff sentence** (`proofs.tex:813`): with `m := Πu ≥ m₀ > 0` and `‖u‖ = U₀`, the
rescaled deviation `h := u/m − 1` is mean-zero and satisfies `‖h‖ ≤ B̂δU₀/m₀`.

Three steps, none of them about a flow: `h = m^{-1}(u − Πu)` (`dev_eq_smul_perpL2`), `‖·‖` is
absolutely homogeneous (`L2Toolkit.nrmL2_smul`), and `‖u − Πu‖ ≤ B̂δ‖u‖`
(`nrmL2_perpL2_le_of_ratio_close`); the mass is then dropped from `m` to `m₀`, which is where the
monotone ascent of `prop:no_distant_equilibrium`*(2)* is spent. -/
theorem rescaled_dev_bound {K : V → V → ℝ} {lam u : V → ℝ} {Bhat δ m0 U0 : ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1) (hu : ∀ x, u x ≠ 0)
    (hδ : 0 ≤ δ) (hB0 : 0 ≤ Bhat)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (hratio : ∀ x, |ratio K lam u x - 1| ≤ δ)
    (hm0 : 0 < m0) (hmass : m0 ≤ Graph.meanL2 lam u)
    (hu0 : Graph.nrmL2 lam u = U0) :
    Graph.meanL2 lam (fun x => u x / Graph.meanL2 lam u - 1) = 0
      ∧ Graph.nrmL2 lam (fun x => u x / Graph.meanL2 lam u - 1) ≤ Bhat * δ * U0 / m0 := by
  set m : ℝ := Graph.meanL2 lam u with hmdef
  have hmpos : 0 < m := lt_of_lt_of_le hm0 hmass
  have hU0nn : 0 ≤ U0 := hu0 ▸ Graph.nrmL2_nonneg lam u
  refine ⟨meanL2_dev_eq_zero htot hmpos.ne' rfl, ?_⟩
  have hrw : Graph.nrmL2 lam (fun x => u x / m - 1)
      = |m⁻¹| * Graph.nrmL2 lam (perpL2 lam u) := by
    rw [dev_eq_smul_perpL2 hmpos.ne' rfl, nrmL2_smul]
  have habs : |m⁻¹| = m⁻¹ := abs_of_pos (inv_pos.mpr hmpos)
  have hperp : Graph.nrmL2 lam (perpL2 lam u) ≤ Bhat * δ * U0 := by
    rw [← hu0]
    exact nrmL2_perpL2_le_of_ratio_close hnn hu hδ hB0 hcoer hratio
  have hprod : 0 ≤ Bhat * δ * U0 := mul_nonneg (mul_nonneg hB0 hδ) hU0nn
  rw [hrw, habs]
  calc m⁻¹ * Graph.nrmL2 lam (perpL2 lam u)
      ≤ m⁻¹ * (Bhat * δ * U0) :=
        mul_le_mul_of_nonneg_left hperp (inv_pos.mpr hmpos).le
    _ ≤ m0⁻¹ * (Bhat * δ * U0) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [one_div] using one_div_le_one_div_of_le hm0 hmass) hprod
    _ = Bhat * δ * U0 / m0 := by
        field_simp

/-! ### `δ₀ = ε₀m₀/(B̂‖u₀‖)`, and the side condition the paper does not state -/

/-- **`δ₀ := ε₀m₀/(B̂‖u₀‖)`** (`proofs.tex:813`, `:927`) — an explicit formula, not an `∃ δ`. -/
noncomputable def delta0 (eps0 m0 Bhat U0 : ℝ) : ℝ := eps0 * m0 / (Bhat * U0)

theorem delta0_pos {eps0 m0 Bhat U0 : ℝ} (heps0 : 0 < eps0) (hm0 : 0 < m0) (hB : 0 < Bhat)
    (hU0 : 0 < U0) : 0 < delta0 eps0 m0 Bhat U0 :=
  div_pos (mul_pos heps0 hm0) (mul_pos hB hU0)

/-- **`m₀ ≤ ‖u₀‖`**, the hypothesis `delta0_le_eps0` needs, discharged from the flow's own data:
`m₀ ≤ Πu` is the monotone ascent and `Πu ≤ ‖u‖` is Cauchy–Schwarz against `𝟏`
(`MassAscent.mean_le_nrmL2_iff_const`, whose `u ≥ 0` is what a density has).

It sits here rather than as a hypothesis of `rescaled_dev_bound` because that bound never needs
`u ≥ 0`, only `u ≠ 0`. -/
theorem mass_le_nrmL2 {V : Type*} [Fintype V] {lam u : V → ℝ} {m0 U0 : ℝ}
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) (hu : ∀ x, 0 ≤ u x)
    (hmass : m0 ≤ Graph.meanL2 lam u) (hu0 : Graph.nrmL2 lam u = U0) : m0 ≤ U0 :=
  le_trans hmass (hu0 ▸ (mean_le_nrmL2_iff_const hlam htot hu).1)

/-- **`δ₀ ≤ ε₀`**, from `m₀ ≤ ‖u₀‖` (`mass_le_nrmL2`, i.e. Cauchy–Schwarz) and
`B̂ ≥ 1`.

`B̂ ≥ 1` is a genuine hypothesis and not a consequence of the coercivity — see the module SCOPE.
It holds for the paper's `B̂ = ∑_n β̂_n` because `β̂₀ = 1`, and for `B̂_σ = σ_*/√λ_min`. -/
theorem delta0_le_eps0 {eps0 m0 Bhat U0 : ℝ} (heps0 : 0 ≤ eps0) (hm0 : 0 < m0)
    (hB1 : 1 ≤ Bhat) (hmU : m0 ≤ U0) : delta0 eps0 m0 Bhat U0 ≤ eps0 := by
  have hU0 : 0 < U0 := lt_of_lt_of_le hm0 hmU
  have hB0 : 0 < Bhat := lt_of_lt_of_le zero_lt_one hB1
  rw [delta0, div_le_iff₀ (mul_pos hB0 hU0)]
  nlinarith [mul_le_mul_of_nonneg_left hmU heps0,
    mul_le_mul_of_nonneg_left (le_trans hmU (le_mul_of_one_le_left hU0.le hB1)) heps0]

/-- **`δ₀ ≤ 1/2`**, the side condition `MassAscent.entry_time` requires of its `δ` and the paper
never states. It follows from `delta0_le_eps0` and `ε₀ ≤ 1/2`, which is itself an added
hypothesis; see the module SCOPE for why it costs nothing. -/
theorem delta0_le_half {eps0 m0 Bhat U0 : ℝ} (heps0 : 0 ≤ eps0) (heps1 : eps0 ≤ 1/2)
    (hm0 : 0 < m0) (hB1 : 1 ≤ Bhat) (hmU : m0 ≤ U0) : delta0 eps0 m0 Bhat U0 ≤ 1/2 :=
  le_trans (delta0_le_eps0 heps0 hm0 hB1 hmU) heps1

/-- **The inversion `theo:training_speed_full` quotes** (`proofs.tex:927`): at `δ = δ₀` the bound
of `rescaled_dev_bound` is exactly `ε₀`, so the rescaled flow sits inside the `ε₀`-neighbourhood
that `theo:local_convergence_full` asks for.

This states the placement and **not** what happens next: the exponential phase, the rate
`ϱ_σ/(2m₁²)` and the crossover time `T₀` are no part of it. -/
theorem exists_delta_for_radius {K : V → V → ℝ} {lam u : V → ℝ} {Bhat m0 U0 eps0 : ℝ}
    (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1) (hu : ∀ x, u x ≠ 0)
    (hB : 0 < Bhat) (hU0 : 0 < U0)
    (hcoer : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (heps0 : 0 < eps0) (hm0 : 0 < m0) (hmass : m0 ≤ Graph.meanL2 lam u)
    (hu0 : Graph.nrmL2 lam u = U0)
    (hratio : ∀ x, |ratio K lam u x - 1| ≤ delta0 eps0 m0 Bhat U0) :
    Graph.meanL2 lam (fun x => u x / Graph.meanL2 lam u - 1) = 0
      ∧ Graph.nrmL2 lam (fun x => u x / Graph.meanL2 lam u - 1) ≤ eps0 := by
  have hδ : 0 ≤ delta0 eps0 m0 Bhat U0 := (delta0_pos heps0 hm0 hB hU0).le
  obtain ⟨hmean, hbd⟩ :=
    rescaled_dev_bound hnn htot hu hδ hB.le hcoer hratio hm0 hmass hu0
  refine ⟨hmean, le_trans hbd (le_of_eq ?_)⟩
  rw [delta0]
  field_simp

end RatioBridge

/-! ### The two-state chain: the bridge evaluated

`Freezing.lean`'s chain, `T(i→j) = 1/2` on `Fin 2` with `λ = (1/2,1/2)` and `u = (2,1)`. By hand:
`μT = (3/4, 3/4)` as a vector, so `r = (3/4, 3/2)`; `Pu = (3/2, 3/2)` and `Au = (−1/2, 1/2)`,
which is `(r−1)u = (−1/4·2, 1/2·1)`. The mass is `m = 3/2`, so `h = u/m − 1 = (1/3, −1/3)` with
`Πh = 0` and `‖h‖ = 1/3`. The chain has `‖u‖ = √(5/2)`, and `LocalEnergy.twoState_coercivity`
gives `hcoer` with `B̂ = 1`, so at `δ = 1/2` the bound reads `1·½·√(5/2)/(3/2) = √(5/2)/3 ≈ 0.527`
against the realized `1/3`. At `ε₀ = 1/2` the choice `δ₀ = 3/(4√(5/2)) ≈ 0.474` is `≤ 1/2`, so
`entry_time`'s side condition is met with room. -/

section TwoState

/-- The band the two-state density sits in: `|r − 1| = (1/4, 1/2)`, so `δ = 1/2` is exact. -/
theorem twoState_ratio_close :
    ∀ x, |ratio twoStateK twoStateLam twoStateU x - 1| ≤ 1/2 := by
  have h0 : |ratio twoStateK twoStateLam twoStateU 0 - 1| ≤ 1/2 := by
    rw [twoState_ratio_zero, show (3:ℝ)/4 - 1 = -(1/4) by norm_num, abs_neg]
    norm_num
  have h1 : |ratio twoStateK twoStateLam twoStateU 1 - 1| ≤ 1/2 := by
    rw [twoState_ratio_one, show (3:ℝ)/2 - 1 = 1/2 by norm_num]
    norm_num
  intro x
  fin_cases x
  · exact h0
  · exact h1

theorem twoState_meanL2 : Graph.meanL2 twoStateLam twoStateU = 3/2 := by
  simp only [Graph.meanL2, Fin.sum_univ_two]
  norm_num [twoStateLam, twoStateU]

theorem twoState_nrmL2_u : Graph.nrmL2 twoStateLam twoStateU = Real.sqrt (5/2) := by
  simp only [Graph.nrmL2, Graph.ipL2, Fin.sum_univ_two]
  norm_num [twoStateLam, twoStateU]

/-- **The bridge evaluated on the two-state chain.** Every number was computed by hand first; the
last clause is `rescaled_dev_bound` applied, not recomputed. -/
theorem twoState_ratioBridge_check :
    Aop twoStateK twoStateLam twoStateU 0 = -(1/2)
      ∧ Aop twoStateK twoStateLam twoStateU 1 = 1/2
      ∧ Graph.meanL2 twoStateLam twoStateU = 3/2
      ∧ Graph.nrmL2 twoStateLam twoStateU = Real.sqrt (5/2)
      ∧ Graph.meanL2 twoStateLam
          (fun x => twoStateU x / Graph.meanL2 twoStateLam twoStateU - 1) = 0
      ∧ Graph.nrmL2 twoStateLam
          (fun x => twoStateU x / Graph.meanL2 twoStateLam twoStateU - 1) = 1/3
      ∧ Graph.nrmL2 twoStateLam
          (fun x => twoStateU x / Graph.meanL2 twoStateLam twoStateU - 1)
        ≤ 1 * (1/2) * Graph.nrmL2 twoStateLam twoStateU / (3/2)
      ∧ delta0 (1/2) (3/2) 1 (Real.sqrt (5/2)) ≤ 1/2 := by
  have hlamnn : ∀ x, (0:ℝ) ≤ twoStateLam x := fun x => (twoStateLam_pos x).le
  have hune : ∀ x, twoStateU x ≠ 0 := fun x => (twoStateU_pos x).ne'
  have htot : ∑ x, twoStateLam x = 1 := by
    simp only [Fin.sum_univ_two]
    norm_num [twoStateLam]
  have hA0 : Aop twoStateK twoStateLam twoStateU 0 = -(1/2) := by
    simp only [Aop_apply, Core.densAct_apply, Fin.sum_univ_two]
    norm_num [twoStateK, twoStateLam, twoStateU]
  have hA1 : Aop twoStateK twoStateLam twoStateU 1 = 1/2 := by
    simp only [Aop_apply, Core.densAct_apply, Fin.sum_univ_two]
    norm_num [twoStateK, twoStateLam, twoStateU]
  have hdev : Graph.nrmL2 twoStateLam
      (fun x => twoStateU x / Graph.meanL2 twoStateLam twoStateU - 1) = 1/3 := by
    rw [twoState_meanL2]
    simp only [Graph.nrmL2, Graph.ipL2, Fin.sum_univ_two]
    norm_num [twoStateLam, twoStateU]
  have hmU : (3:ℝ)/2 ≤ Real.sqrt (5/2) := by
    rw [show (3:ℝ)/2 = Real.sqrt ((3/2)^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  obtain ⟨hmean, hbd⟩ :=
    rescaled_dev_bound (K := twoStateK) (lam := twoStateLam) (u := twoStateU)
      (Bhat := 1) (δ := 1/2) (m0 := 3/2)
      (U0 := Graph.nrmL2 twoStateLam twoStateU)
      hlamnn htot hune (by norm_num) (by norm_num) twoState_coercivity
      twoState_ratio_close (by norm_num) (le_of_eq twoState_meanL2.symm) rfl
  exact ⟨hA0, hA1, twoState_meanL2, twoState_nrmL2_u, hmean, hdev, hbd,
    delta0_le_half (by norm_num) (by norm_num) (by norm_num) le_rfl hmU⟩

end TwoState

end GFNBounds.Balance
