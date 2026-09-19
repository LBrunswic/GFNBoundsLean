import GFNBounds.Balance.TBvsDB
import GFNBounds.Balance.LiftGeneralMixing
import GFNBounds.Doubling.OperatorGeneral

/-!
# TB against DB: the detailed-balance supply on the truncation, the complex Fejér kernel, the step cap on norms

**`rem:tb_vs_db`** — `proofs.tex`, the remark after `prop:tb_hessian` (the label is the anchor;
line citations drift, kb `0036`). This file closes the two items the map row left open (the DB
instance's supply, the complex Fejér form) and restates the step cap on operator norms; everything
else in the remark is certified in `TBvsDB.lean`.

> […] what is proved is one-sided, `0 ⪯ H_TB ⪯ ℓ(1+2B̂′)H_DB`, so a step cap derived from the norm
> of `H_DB` remains sufficient for TB once divided by `ℓ(1+2B̂′)`, and no TB rate is claimed. On an
> eigenfunction of `Q` with eigenvalue `e^{iθ}` the Rayleigh quotient of `Θ_ℓ` is the Fejér kernel
> `∑_{|m|<ℓ}(1 − |m|/ℓ)e^{imθ}`: […] At `c = 1/4`, […] the rate of Theorem
> `theo:db_stable_frozen_full` on the truncation at an even `K ≥ K₀` satisfies
> `ϱ_K ≤ g''(1)w_min/(c₈²K) → 0`, […] in the detailed-balance instance at the constant
> `1 + B̂_K` that Lemma `lem:lift_coercivity` supplies.

## What is proved

| | |
|---|---|
| `kerMeas`, **`ker`**, `isMarkovKernel_ker`, **`funAct_ker`** | (i) the chain in play (loop closure or truncation) as a Mathlib Markov kernel on the discrete `St`; its function action **is** `pstar`, for every function |
| `ker_apply_set`, **`mu_bind_ker`** | `π_←(x, A) = (P⋆1_A)(x)`; `λ` is invariant **as a measure**, `λπ_← = λ`, from `Stat.inv` against indicators |
| **`funActLp_ker`**, **`densityActionL2_ker`**, **`meanProj_mu`** | **the bridge**: the general layer's `P⋆`, `P` and `Π` on `L²(λ)` are `Stat.pstarL2`, `Stat.densL2`, `Stat.piL2` (the density actions agree as adjoints of the same function action) |
| `coercive_bhatK` | `eq:coercivity` of the truncation at `C = B̂_K`, on the general layer |
| **`lift_coercivity_truncation`** | **(i) the DB instance's supply**: `‖h − Π₂h‖ ≤ (1 + B̂_K)‖(I − P₂)h‖` on `L²(λ₂)` of the truncation's edge lift — `lem:lift_coercivity` (`LiftGeneral.lift_coercivity_general`) at `C = B̂_K` |
| **`truncation_rate_DB`** | the DB half of the truncation clause, assembled: at `0 < c < 1`, `K ≥ K₀`, `1 + B̂_K` is a coercivity constant of `K₂` **and** `g''(1)w_min/(1 + B̂_K)² ≤ g''(1)w_min/(c₈²K)` |
| `sum_Ioo_symm`, `fejerC`, **`fejerC_eq`** | (ii) **the Fejér kernel as printed**, `∑_{|m|<ℓ}(1 − |m|/ℓ)e^{imθ}` (sum over `m ∈ ℤ`), equal to the real form `fejer` for `ℓ ≥ 1` |
| `funActC`, `cplx`, `ipC`, `funActC_eq_cplx` | the complex function action of `K₂`, the complexification of a real operator, the inner product of `L²(λ₂; ℂ)` |
| **`rayleigh_fejerC`**, **`rayleigh_quotient_fejerC`** | **(ii) the Fejér clause in complex form**: `Q_ℂu = e^{iθ}u` gives `⟨u, Θ_ℓu⟩_ℂ = F_ℓ(θ)⟨u, u⟩_ℂ`, and the quotient is `F_ℓ(θ)` when `⟨u,u⟩_ℂ ≠ 0` |
| `RLin`, `ipL2_quad`, `form_cs`, `nrm_pow_four_le`, **`opBound_of_form`**, `nrm_sq_le_form`, **`step_nonexpansive`** | generic, on a weighted finite `L²`: for a linear, self-adjoint, `⪰ 0` operator a quadratic-form bound is an operator-norm bound, and a step `η` with `η‖H‖ ≤ 2` makes `h ↦ h − ηHh` non-expansive (no spectral theorem) |
| `rlin_funAct_iter`, `rlin_densAct_iter`, `rlin_Theta`, `rlin_HTB` | `Q^m`, `P^m`, `Θ_ℓ`, `H_TB` are linear |
| **`HTB_selfAdjoint`**, `HDB_eq` | (iii) **`H_TB` is self-adjoint** on `L²(λ₂)`; `H_DB = H_TB` at `ℓ = 1`, so it is too |
| `HDB_form_le_eight`, `opBound_HTB_of_form`, `opBound_HDB_opNorm` | `⟨h, H_DB h⟩ ≤ 8‖h‖²`, so `H_DB` has a bound and the infimum `opNorm λ₂ H_DB` is itself one (not a minimum over a named bound) |
| **`opNorm_HTB_le`** | (iii) **`‖H_TB‖ ≤ ℓ(1 + 2B̂′)‖H_DB‖`** on `L²(λ₂)` |
| **`stepCap_opNorm`** | (iii) **the sentence**: `η‖H_DB‖ ≤ c` gives `(η/(ℓ(1 + 2B̂′)))‖H_TB‖ ≤ c`, for every cap `c` |
| **`stepCap_stable`** | the cap read as stability: `η‖H_DB‖ ≤ 2` makes both `h ↦ h − ηH_DB h` and `h ↦ h − (η/(ℓ(1+2B̂′)))H_TB h` non-expansive |
| `stepCap_witness`, `fejerC_witness` | inhabitation (kb `0025`): the uniform two-state chain (`B = 1`) and the eigenfunction `u ≡ 1`, `θ = 0` |

## SCOPE (disclosed)

* **State space of the truncation.** The kernel lives on all of `St`, the type serving both chains;
  on the truncation `λ` vanishes off the `K + 2` on-chain states, so `λ₂ = λ ⊗ π_←` vanishes off
  the truncation's edges and `L²(λ)`, `L²(λ₂)` are the paper's spaces (as classes). Off-chain
  states carry `pstar`'s values, which no statement sees.
* **`Stat S (some K)` is empty at odd `K`** (kb `0027`): `lift_coercivity_truncation` and
  `truncation_rate_DB` hold vacuously there. The non-vacuous case, even `K ≥ K₀`, is inhabited by
  `TBvsDB.truncation_rate`'s `Nonempty` clause, and a `Setting` with `ε = ε_{1/4,1}` exists
  (`TBvsDB.exists_setting_six`). `RowOnChain` is `S.d ≤ K`, carried as `hdK`.
* **The rate `ϱ = g''(1)w_min/C²`** enters as a formula, as in `TBvsDB.lean`; that the linearized
  DB descent contracts at that rate is `theo:db_stable_frozen_full`'s own certificate.
* **"The norm of `H_DB`"** is `Balance.opNorm`, the infimum of the operator bounds on the weighted
  seminorm `Graph.nrmL2 λ₂`; with `λ₂ > 0` it is Mathlib's operator norm of the conjugated operator
  (`LiftFinite.opNorm_eq_norm`). **"A step cap derived from the norm"** is certified twice: as the
  norm inequality for every cap `c` (`stepCap_opNorm`), and at the classical cap `η‖H‖ ≤ 2` of the
  quadratic model `½⟨h, Hh⟩` as non-expansiveness of `h ↦ h − ηHh` (`stepCap_stable`). The remark
  names no specific cap; which descent a cap is for is not stated there.
* **`B̂′ = ∑_{m≥1}β̂_m`** enters through a real bound `B` of its partial sums (kb `0031`), as in
  `prop:tb_hessian`'s Lean; the statements are vacuous exactly at `B̂′ = +∞`, as the paper's are.
* **The complex Fejér clause.** `Q` acts on `E → ℂ` by its kernel (`funActC`, the natural action);
  `Θ_ℓ`, a real operator, acts by its real-linear extension (`cplx`), which is `Θ_ℓ` on
  `L²(λ₂; ℂ)`; the Rayleigh quotient is `⟨u, Θ_ℓu⟩_ℂ/⟨u, u⟩_ℂ` with `⟨u, v⟩_ℂ = ∑λ₂ ū v`. The
  kernel sum is over `m ∈ ℤ`, `|m| < ℓ`, and needs `ℓ ≥ 1` (at `ℓ = 0` the printed sum is empty).
* **Not formalized, by ruling**: the sentences marked "Heuristically" (author ruling (v)), and the
  recall sentences on `theo:universality_L2` at `p = 2` and on `prop:morozov_rate` (ruling of
  2026-09-18: a pointer sentence is recall, certified by its own row).
* **`sorry`-free**; no new axiom.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the truncation of the counter-example graph, `s = 1`, `0 < c < 1` | ✓ `Setting` with `ε = epsCS c 1`, `Stat S (some K)`, `hdK : S.d ≤ K` |
| even `K ≥ K₀`, `c₈`, `K₀` of `theo:doubling_main`(5) | ✓ `hK`, `Decay.c8Of`, `Decay.K0Of`; evenness via inhabitation (SCOPE) |
| `lem:lift_coercivity`'s setting: `π_←` Markov, `λ` finite invariant | ✓ `isMarkovKernel_ker`, `mu_bind_ker` (proved, not assumed) |
| `P`, `Π` of `eq:coercivity` on the truncation | ✓ `densityActionL2_ker`, `meanProj_mu` identify them with `Stat`'s |
| `prop:tb_hessian`'s setting (finite, `λ > 0` invariant probability) | ✓ `hnn`, `hrow`, `hlam`, `hinv`, `htot`, as in `TBHessian.lean` |
| an eigenfunction of `Q` with eigenvalue `e^{iθ}` | ✓ `hu : funActC u = e^{iθ}u`, `u : E → ℂ` |
| `ℓ ≥ 1` | ✓ `hℓ` where used |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling.TBvsDBClose

open MeasureTheory ProbabilityTheory GFNBounds.Core
open scoped ENNReal InnerProductSpace

/-! ### (i) The chain in play as a Markov kernel, and the bridge to `Stat`'s `L²` -/

section Kernel

variable (S : Setting) (cap : Option ℕ)

/-- The backward kernel of the chain in play, state by state: the three cases of `pstar`. -/
noncomputable def kerMeas : St → Measure St
  | .lad 0 => Measure.dirac .sink
  | .lad (j + 1) =>
      if HasDouble cap (j + 1) then
        ENNReal.ofReal (S.eps (j + 1)) • Measure.dirac (.lad (2 * (j + 1)))
          + ENNReal.ofReal (1 - S.eps (j + 1)) • Measure.dirac (.lad j)
      else Measure.dirac (.lad j)
  | .sink => ∑ k ∈ Finset.Icc 1 S.d, ENNReal.ofReal (S.row k) • Measure.dirac (.lad k)

/-- **The backward kernel `π_←` of the chain in play** (the loop closure at `cap = none`, the
truncation at `cap = some K`) as a Mathlib kernel on the discrete countable `St`. -/
noncomputable def ker : Kernel St St := Kernel.ofFunOfCountable (kerMeas S cap)

theorem ker_apply (x : St) : ker S cap x = kerMeas S cap x := rfl

theorem integrable_kerMeas (f : St → ℝ) (x : St) : Integrable f (kerMeas S cap x) := by
  have hd : ∀ a : St, Integrable f (Measure.dirac a) := fun a =>
    integrable_dirac (by simp)
  rcases x with (_ | j) | _
  · exact hd _
  · simp only [kerMeas]
    split_ifs
    · exact ((hd _).smul_measure ENNReal.ofReal_ne_top).add_measure
        ((hd _).smul_measure ENNReal.ofReal_ne_top)
    · exact hd _
  · simp only [kerMeas]
    exact integrable_finsetSum_measure.2 fun k _ => (hd _).smul_measure ENNReal.ofReal_ne_top

/-- **`∫ f dπ_←(x, ·) = (P⋆f)(x)`**: the function action of `ker` is `pstar`, for every `f`. -/
theorem integral_kerMeas (f : St → ℝ) (x : St) :
    ∫ y, f y ∂(kerMeas S cap x) = pstar S cap f x := by
  rcases x with (_ | j) | _
  · simp [kerMeas, integral_dirac]
  · by_cases h : HasDouble cap (j + 1)
    · have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.succ_pos j)).le
      have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.succ_pos j)).le
      simp only [kerMeas, h, if_true, pstar_lad_succ]
      rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
          ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
        integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
        ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2, smul_eq_mul, smul_eq_mul]
    · simp [kerMeas, h, pstar_lad_succ, integral_dirac]
  · simp only [kerMeas, pstar_sink]
    rw [integral_finsetSum_measure fun k _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (S.row_nonneg k),
      smul_eq_mul]

instance isMarkovKernel_ker : IsMarkovKernel (ker S cap) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have h := integral_kerMeas S cap (fun _ => 1) x
  rw [pstar_const, integral_const, smul_eq_mul, mul_one, measureReal_def] at h
  rw [ker_apply]
  have hfin : kerMeas S cap x Set.univ ≠ ∞ := by
    rcases x with (_ | j) | _
    · simp [kerMeas]
    · simp only [kerMeas]; split_ifs <;> simp
    · simp only [kerMeas]
      rw [Measure.coe_finsetSum, Finset.sum_apply]
      exact ENNReal.sum_ne_top.2 fun k _ => by simp
  rw [← ENNReal.ofReal_toReal hfin, h, ENNReal.ofReal_one]

/-- `General.funAct (ker S cap) = pstar S cap`, pointwise and for every function. -/
theorem funAct_ker (f : St → ℝ) : General.funAct (ker S cap) f = pstar S cap f :=
  funext fun x => integral_kerMeas S cap f x

end Kernel

section Bridge

variable {S : Setting} {cap : Option ℕ} (L : Stat S cap)

/-- `π_←(x, A) = (P⋆1_A)(x)`. -/
theorem ker_apply_set (x : St) (A : Set St) :
    ker S cap x A = ENNReal.ofReal (pstar S cap (A.indicator 1) x) := by
  rw [← integral_kerMeas, ← ker_apply,
    integral_indicator_one (DiscreteMeasurableSpace.forall_measurableSet A),
    measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **`λ` is `π_←`-invariant as a measure**: `L.mu.bind π_← = L.mu`, from `Stat.inv` tested
against indicators. -/
theorem mu_bind_ker : L.mu.bind (ker S cap) = L.mu := by
  ext A _
  rw [Measure.bind_apply (DiscreteMeasurableSpace.forall_measurableSet A)
    (ker S cap).aemeasurable, lintegral_countable']
  have hb : ∃ C, ∀ x, |A.indicator (1 : St → ℝ) x| ≤ C :=
    ⟨1, fun x => by by_cases hx : x ∈ A <;> simp [hx]⟩
  have hbP : ∃ C, ∀ x, |pstar S cap (A.indicator (1 : St → ℝ)) x| ≤ C := by
    obtain ⟨C, hC⟩ := hb; exact ⟨C, fun x => pstar_bounded hC x⟩
  have hnP : ∀ x, 0 ≤ pstar S cap (A.indicator (1 : St → ℝ)) x :=
    pstar_nonneg fun x => by by_cases hx : x ∈ A <;> simp [hx]
  have hnI : ∀ x, 0 ≤ A.indicator (1 : St → ℝ) x := fun x => by
    by_cases hx : x ∈ A <;> simp [hx]
  have hinv := L.inv _ hb
  have hA : L.mu A = ∑' x, ENNReal.ofReal (L.lam x * A.indicator 1 x) := by
    rw [← lintegral_indicator_one (DiscreteMeasurableSpace.forall_measurableSet A),
      lintegral_countable']
    refine tsum_congr fun x => ?_
    rw [L.mu_singleton, ENNReal.ofReal_mul (L.nonneg x)]
    by_cases hx : x ∈ A <;> simp [hx, mul_comm]
  rw [hA]
  have e1 : ∀ x, ker S cap x A * L.mu {x}
      = ENNReal.ofReal (L.lam x * pstar S cap (A.indicator 1) x) := by
    intro x
    rw [ker_apply_set, L.mu_singleton, ENNReal.ofReal_mul (L.nonneg x), mul_comm]
  simp only [e1]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (L.nonneg x) (hnP x))
      (L.summable_mul hbP),
    ← ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (L.nonneg x) (hnI x))
      (L.summable_mul hb), hinv]

/-- **`P⋆` of the general layer is `Stat.pstarL2`**, as operators of `L²(λ)`. -/
theorem funActLp_ker (hrow : RowOnChain S cap) :
    Doubling.General.funActLp (ker S cap) L.mu 2 (mu_bind_ker L) = L.pstarL2 hrow := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  refine (Doubling.General.coeFn_funActLp _ _ _ _ F).trans ?_
  rw [funAct_ker]
  exact (L.coeFn_pstarL2 hrow F).symm

/-- **The density action of the general layer is `Stat.densL2`**: both are the `L²(λ)`-adjoint
of the same function action. -/
theorem densityActionL2_ker (hrow : RowOnChain S cap) :
    densityActionL2 (ker S cap) L.mu (mu_bind_ker L) = L.densL2 hrow := by
  rw [← Doubling.General.adjoint_funActL2, funActLp_ker L hrow, L.adjoint_pstarL2]

/-- **The mean projection of the general layer is `Stat.piL2`**. -/
theorem meanProj_mu : meanProj L.mu 2 = L.piL2 := by
  refine ContinuousLinearMap.ext fun F => ?_
  rw [meanProj_apply, Stat.piL2_apply, measure_univ, ENNReal.toReal_one, div_one,
    L.integral_eq_tsum (Lp.memLp F), ← L.inner_oneLp]
  rfl

end Bridge

section DBInstance

open GFNBounds.Balance.LiftGeneral GFNBounds.Doubling.TBvsDB

variable {S : Setting} {K : ℕ} (L : Stat S (some K)) (hdK : S.d ≤ K)

/-- **`eq:coercivity` of the truncation at `C = B̂_K`, on the general layer**: `isLeast_bhatK`'s
coercivity read through the bridge (`densityActionL2_ker`, `meanProj_mu`). -/
theorem coercive_bhatK (φ : Lp ℝ 2 L.mu) :
    ‖φ - meanProj L.mu 2 φ‖
      ≤ L.bhatK hdK * ‖(1 - densityActionL2 (ker S (some K)) L.mu (mu_bind_ker L)) φ‖ := by
  rw [meanProj_mu, densityActionL2_ker L (rowOnChain_some hdK)]
  exact (isLeast_bhatK L hdK).1.2 φ

/-- **`rem:tb_vs_db`, the detailed-balance instance's supply**: `1 + B̂_K` is a coercivity
constant of the edge lift `K₂` of the truncation's backward kernel on `L²(λ₂)`,
`‖h − Π₂h‖ ≤ (1 + B̂_K)‖(I − P₂)h‖` — `lem:lift_coercivity` (`lift_coercivity_general`) applied
to `C = B̂_K`. -/
theorem lift_coercivity_truncation (h : Lp ℝ 2 (edgeMeasure (ker S (some K)) L.mu)) :
    ‖h - meanProj (edgeMeasure (ker S (some K)) L.mu) 2 h‖
      ≤ (1 + L.bhatK hdK) * ‖(1 - densityActionL2 (edgeLift (ker S (some K)))
          (edgeMeasure (ker S (some K)) L.mu)
          (edgeMeasure_invariant _ L.mu (mu_bind_ker L))) h‖ :=
  lift_coercivity_general _ L.mu (mu_bind_ker L) (isLeast_bhatK L hdK).1.1
    (coercive_bhatK L hdK) h

/-- **`rem:tb_vs_db`, the truncation clause, detailed-balance instance, with its supply.** At
`s = 1`, `0 < c < 1`, with `c₈`, `K₀` of `theo:doubling_main`(5): at every `K ≥ K₀` and every
invariant probability `λ^K` of the truncation (inhabited at every even `K ≥ K₀`,
`truncation_rate`), `1 + B̂_K` is a coercivity constant of the edge lift `K₂` of the truncation
(`lem:lift_coercivity`), and the rate `ϱ = g''(1)w_min/C²` of `theo:db_stable_frozen_full` at
that constant satisfies `ϱ ≤ g''(1)w_min/(c₈²K)`. -/
theorem truncation_rate_DB {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) (hK : (Decay.ofC hc0 hc1).K0Of S.d ≤ K) :
    ∀ g2w : ℝ, 0 ≤ g2w →
      (0 ≤ 1 + L.bhatK hdK ∧
        ∀ h : Lp ℝ 2 (edgeMeasure (ker S (some K)) L.mu),
          ‖h - meanProj (edgeMeasure (ker S (some K)) L.mu) 2 h‖
            ≤ (1 + L.bhatK hdK) * ‖(1 - densityActionL2 (edgeLift (ker S (some K)))
                (edgeMeasure (ker S (some K)) L.mu)
                (edgeMeasure_invariant _ L.mu (mu_bind_ker L))) h‖) ∧
      g2w / (1 + L.bhatK hdK) ^ 2
        ≤ g2w / ((Decay.ofC hc0 hc1).c8Of S.d S.jbar ^ 2 * K) := by
  intro g2w hg
  obtain ⟨-, -, -, -, hrate⟩ := truncation_rate (S := S) hc0 hc1 heps
  refine ⟨⟨by linarith [(isLeast_bhatK L hdK).1.1], lift_coercivity_truncation L hdK⟩, ?_⟩
  exact ((hrate K hK hdK L).2.2.2 g2w hg).2

end DBInstance

end GFNBounds.Doubling.TBvsDBClose

/-! ### (ii) The Fejér kernel in its complex form, and the complex Rayleigh quotient -/

namespace GFNBounds.Balance.TBHessian

open Finset Complex ComplexConjugate

section FejerC

/-- A sum over the symmetric window `(−n, n)` of `ℤ` pairs the terms `±k`. -/
theorem sum_Ioo_symm (f : ℤ → ℂ) : ∀ n : ℕ, 1 ≤ n →
    ∑ m ∈ Finset.Ioo (-(n : ℤ)) n, f m = f 0 + ∑ k ∈ Finset.Ico 1 n, (f k + f (-k))
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
      have : Finset.Ioo (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {0} := by decide
      rw [this]; simp
  | n + 2, _ => by
      have ih := sum_Ioo_symm f (n + 1) (by omega)
      have hset : Finset.Ioo (-((n + 2 : ℕ) : ℤ)) ((n + 2 : ℕ) : ℤ)
          = insert ((n + 1 : ℕ) : ℤ) (insert (-((n + 1 : ℕ) : ℤ))
              (Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ))) := by
        ext m; simp only [Finset.mem_Ioo, Finset.mem_insert]; push_cast; omega
      have h1 : ((n + 1 : ℕ) : ℤ) ∉ insert (-((n + 1 : ℕ) : ℤ))
          (Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Ioo]; push_cast; omega
      have h2 : -((n + 1 : ℕ) : ℤ) ∉ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) := by
        simp only [Finset.mem_Ioo]; push_cast; omega
      rw [hset, Finset.sum_insert h1, Finset.sum_insert h2, ih,
        Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
      push_cast
      ring

/-- **`rem:tb_vs_db`, the Fejér kernel as printed**: `∑_{|m|<ℓ}(1 − |m|/ℓ)e^{imθ}`. -/
noncomputable def fejerC (ℓ : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioo (-(ℓ : ℤ)) ℓ, (((1 - |(m : ℝ)| / ℓ : ℝ)) : ℂ) * Complex.exp (m * θ * I)

/-- **The complex and the real forms of the Fejér kernel agree** (`ℓ ≥ 1`):
`∑_{|m|<ℓ}(1 − |m|/ℓ)e^{imθ} = 1 + 2∑_{m=1}^{ℓ−1}(1 − m/ℓ)cos(mθ)`. -/
theorem fejerC_eq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (θ : ℝ) : fejerC ℓ θ = (fejer ℓ θ : ℂ) := by
  rw [fejerC, sum_Ioo_symm _ ℓ hℓ, fejer]
  have h0 : (((1 - |((0 : ℤ) : ℝ)| / ℓ : ℝ)) : ℂ) * Complex.exp (((0 : ℤ) : ℂ) * θ * I) = 1 := by
    simp
  rw [h0, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat,
    Complex.ofReal_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Int.cast_natCast, Int.cast_neg, abs_neg, Nat.abs_cast]
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  have e1 : -(k : ℂ) * θ * I = -((k : ℂ) * θ * I) := by ring
  rw [e1]
  ring_nf

end FejerC

section Complexified

variable {V : Type*} [Fintype V] [DecidableEq V] {pb : V → V → ℝ} {lam : V → ℝ}

/-- The complex function action `(Q_ℂu)(e) = ∑_{e'} K₂(e,e')u(e')` of `K₂` on `E → ℂ`. -/
noncomputable def funActC (u : EdgeSet pb → ℂ) : EdgeSet pb → ℂ :=
  fun e => ∑ e', (edgeKernelE pb e e' : ℂ) * u e'

/-- The real-linear extension `A_ℂ(f + ig) := Af + iAg` of a real operator to `E → ℂ`: how
`Θ_ℓ`, a real operator, acts on a complex eigenfunction. -/
noncomputable def cplx (A : (EdgeSet pb → ℝ) → (EdgeSet pb → ℝ)) (u : EdgeSet pb → ℂ) :
    EdgeSet pb → ℂ :=
  fun e => (A (fun e => (u e).re) e : ℂ) + (A (fun e => (u e).im) e : ℂ) * I

/-- The complex inner product of `L²(λ₂; ℂ)`, `⟨u, v⟩_ℂ = ∑_e λ₂(e) conj(u e) v(e)`. -/
noncomputable def ipC (w : EdgeSet pb → ℝ) (u v : EdgeSet pb → ℂ) : ℂ :=
  ∑ e, (w e : ℂ) * (conj (u e) * v e)

/-- `Q_ℂ` is the complexification of the real `Q = funAct K₂`. -/
theorem funActC_eq_cplx (u : EdgeSet pb → ℂ) : funActC u = cplx (funAct (edgeKernelE pb)) u := by
  funext e
  apply Complex.ext
  · simp [funActC, cplx, funAct, Complex.re_sum]
  · simp [funActC, cplx, funAct, Complex.im_sum]

/-- **`rem:tb_vs_db`, the Fejér clause in its printed complex form**: if `u : E → ℂ` is an
eigenfunction of `Q` with eigenvalue `e^{iθ}`, then `⟨u, Θ_ℓu⟩_ℂ = F_ℓ(θ)⟨u, u⟩_ℂ` with
`F_ℓ(θ) = ∑_{|m|<ℓ}(1 − |m|/ℓ)e^{imθ}` (`ℓ ≥ 1`). -/
theorem rayleigh_fejerC (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x)
    (hinv : Invariant pb lam) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (θ : ℝ) {u : EdgeSet pb → ℂ}
    (hu : funActC u = fun e => Complex.exp (θ * I) * u e) :
    ipC (edgeMeasureE pb lam) u (cplx (Theta pb lam ℓ) u)
      = fejerC ℓ θ * ipC (edgeMeasureE pb lam) u u := by
  set f : EdgeSet pb → ℝ := fun e => (u e).re
  set g : EdgeSet pb → ℝ := fun e => (u e).im
  have hu' := hu
  rw [funActC_eq_cplx] at hu'
  have hre : ∀ e, funAct (edgeKernelE pb) f e = Real.cos θ * f e - Real.sin θ * g e := by
    intro e
    have := congrArg Complex.re (congrFun hu' e)
    simpa [cplx, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, f, g] using this
  have him : ∀ e, funAct (edgeKernelE pb) g e = Real.sin θ * f e + Real.cos θ * g e := by
    intro e
    have := congrArg Complex.im (congrFun hu' e)
    simp [cplx, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at this
    linarith
  have hR := rayleigh_fejer hnn hlam hinv ℓ θ (funext hre) (funext him)
  have hsym : Graph.ipL2 (edgeMeasureE pb lam) f (Theta pb lam ℓ g)
      = Graph.ipL2 (edgeMeasureE pb lam) g (Theta pb lam ℓ f) := by
    rw [← Theta_selfAdjoint hnn hlam hinv, ipL2_comm]
  have hL : ipC (edgeMeasureE pb lam) u (cplx (Theta pb lam ℓ) u)
      = ((Graph.ipL2 (edgeMeasureE pb lam) f (Theta pb lam ℓ f)
          + Graph.ipL2 (edgeMeasureE pb lam) g (Theta pb lam ℓ g) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [ipC, cplx, Complex.re_sum, Graph.ipL2, Complex.ofReal_re]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [f, g]; ring
    · simp only [ipC, cplx, Complex.im_sum, Complex.ofReal_im]
      have : ∑ e, ((edgeMeasureE pb lam e : ℂ) * (conj (u e) *
          ((Theta pb lam ℓ f e : ℂ) + (Theta pb lam ℓ g e : ℂ) * I))).im
          = Graph.ipL2 (edgeMeasureE pb lam) f (Theta pb lam ℓ g)
            - Graph.ipL2 (edgeMeasureE pb lam) g (Theta pb lam ℓ f) := by
        simp only [Graph.ipL2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp [f, g]; ring
      rw [this, hsym, sub_self]
  have hU : ipC (edgeMeasureE pb lam) u u
      = ((Graph.ipL2 (edgeMeasureE pb lam) f f + Graph.ipL2 (edgeMeasureE pb lam) g g : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [ipC, Complex.re_sum, Graph.ipL2, Complex.ofReal_re]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [f, g]; ring
    · simp only [ipC, Complex.im_sum, Complex.ofReal_im]
      refine Finset.sum_eq_zero fun e _ => ?_
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im, Complex.mul_re]
      ring
  rw [hL, hU, hR, fejerC_eq hℓ]
  push_cast
  ring

/-- The same, as a Rayleigh quotient: `⟨u, Θ_ℓu⟩_ℂ / ⟨u, u⟩_ℂ = F_ℓ(θ)` for `u ≠ 0` in
`L²(λ₂; ℂ)`. -/
theorem rayleigh_quotient_fejerC (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 < lam x)
    (hinv : Invariant pb lam) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (θ : ℝ) {u : EdgeSet pb → ℂ}
    (hu : funActC u = fun e => Complex.exp (θ * I) * u e)
    (hne : ipC (edgeMeasureE pb lam) u u ≠ 0) :
    ipC (edgeMeasureE pb lam) u (cplx (Theta pb lam ℓ) u) / ipC (edgeMeasureE pb lam) u u
      = fejerC ℓ θ := by
  rw [rayleigh_fejerC hnn hlam hinv hℓ θ hu, mul_div_assoc, div_self hne, mul_one]

end Complexified

/-! ### (iii) `H_TB` self-adjoint, and the step cap on operator norms -/

section FormToNorm

variable {α : Type*} [Fintype α]

/-- Real-linearity of an operator on `α → ℝ`. -/
def RLin (H : (α → ℝ) → (α → ℝ)) : Prop :=
  ∀ (a b : α → ℝ) (t : ℝ), H (fun x => a x + t * b x) = fun x => H a x + t * H b x

theorem ipL2_quad (w a b c d : α → ℝ) (t : ℝ) :
    Graph.ipL2 w (fun x => a x + t * b x) (fun x => c x + t * d x)
      = Graph.ipL2 w a c + t * (Graph.ipL2 w a d + Graph.ipL2 w b c)
        + t ^ 2 * Graph.ipL2 w b d := by
  simp only [Graph.ipL2, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

variable {w : α → ℝ} {H : (α → ℝ) → (α → ℝ)}

/-- **Cauchy–Schwarz for the form `⟨a, Hb⟩`** of a linear, self-adjoint, positive
semi-definite `H` on `L²(w)`. -/
theorem form_cs (hlin : RLin H) (hsym : ∀ a b, Graph.ipL2 w (H a) b = Graph.ipL2 w a (H b))
    (hpsd : ∀ a, 0 ≤ Graph.ipL2 w a (H a)) (a b : α → ℝ) :
    Graph.ipL2 w a (H b) ^ 2 ≤ Graph.ipL2 w a (H a) * Graph.ipL2 w b (H b) := by
  have hs : Graph.ipL2 w b (H a) = Graph.ipL2 w a (H b) := by rw [ipL2_comm, hsym]
  have hq : ∀ t : ℝ, 0 ≤ Graph.ipL2 w b (H b) * (t * t) + 2 * Graph.ipL2 w a (H b) * t
      + Graph.ipL2 w a (H a) := by
    intro t
    have h := hpsd (fun x => a x + t * b x)
    rw [hlin, ipL2_quad, hs] at h
    nlinarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

/-- `‖Hh‖⁴ ≤ ⟨h, Hh⟩⟨Hh, H²h⟩`. -/
theorem nrm_pow_four_le (hw : ∀ x, 0 ≤ w x) (hlin : RLin H)
    (hsym : ∀ a b, Graph.ipL2 w (H a) b = Graph.ipL2 w a (H b))
    (hpsd : ∀ a, 0 ≤ Graph.ipL2 w a (H a)) (h : α → ℝ) :
    Graph.nrmL2 w (H h) ^ 4 ≤ Graph.ipL2 w h (H h) * Graph.ipL2 w (H h) (H (H h)) := by
  have hc := form_cs hlin hsym hpsd h (H h)
  have e : Graph.ipL2 w h (H (H h)) = Graph.nrmL2 w (H h) ^ 2 := by
    rw [← hsym, Graph.sq_nrmL2 hw]
  rw [e] at hc
  calc Graph.nrmL2 w (H h) ^ 4 = (Graph.nrmL2 w (H h) ^ 2) ^ 2 := by ring
    _ ≤ _ := hc

/-- **A quadratic-form bound is an operator-norm bound** for a linear, self-adjoint, positive
semi-definite operator: `⟨a, Ha⟩ ≤ L‖a‖²` for all `a` gives `‖Hh‖ ≤ L‖h‖`. No spectral theorem:
`form_cs` at `(h, Hh)`. -/
theorem opBound_of_form [DecidableEq α] (hw : ∀ x, 0 ≤ w x) (hlin : RLin H)
    (hsym : ∀ a b, Graph.ipL2 w (H a) b = Graph.ipL2 w a (H b))
    (hpsd : ∀ a, 0 ≤ Graph.ipL2 w a (H a)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ a, Graph.ipL2 w a (H a) ≤ L * Graph.ipL2 w a a) : OpBound w H L := by
  refine ⟨hL0, fun h => ?_⟩
  rw [l2norm_eq_nrmL2, l2norm_eq_nrmL2]
  have h4 := nrm_pow_four_le hw hlin hsym hpsd h
  set x := Graph.nrmL2 w (H h)
  set y := Graph.nrmL2 w h
  have hx : 0 ≤ x := Graph.nrmL2_nonneg _ _
  have hy : 0 ≤ y := Graph.nrmL2_nonneg _ _
  have a1 : Graph.ipL2 w h (H h) ≤ L * y ^ 2 := by rw [Graph.sq_nrmL2 hw]; exact hL h
  have a2 : Graph.ipL2 w (H h) (H (H h)) ≤ L * x ^ 2 := by rw [Graph.sq_nrmL2 hw]; exact hL _
  have p1 := hpsd h
  have p2 := hpsd (H h)
  have h4' : x ^ 4 ≤ (L * y ^ 2) * (L * x ^ 2) :=
    h4.trans (mul_le_mul a1 a2 p2 (by positivity))
  by_contra hcon
  push Not at hcon
  have hLy : 0 ≤ L * y := mul_nonneg hL0 hy
  have hxp : 0 < x := lt_of_le_of_lt hLy hcon
  have : (L * y) ^ 2 < x ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_right this (by positivity : (0 : ℝ) < x ^ 2)]

/-- `‖Hh‖² ≤ L⟨h, Hh⟩` for an operator-norm bound `L`. -/
theorem nrm_sq_le_form [DecidableEq α] (hw : ∀ x, 0 ≤ w x) (hlin : RLin H)
    (hsym : ∀ a b, Graph.ipL2 w (H a) b = Graph.ipL2 w a (H b))
    (hpsd : ∀ a, 0 ≤ Graph.ipL2 w a (H a)) {L : ℝ} (hb : OpBound w H L) (h : α → ℝ) :
    Graph.nrmL2 w (H h) ^ 2 ≤ L * Graph.ipL2 w h (H h) := by
  have h4 := nrm_pow_four_le hw hlin hsym hpsd h
  set x := Graph.nrmL2 w (H h)
  have hx : 0 ≤ x := Graph.nrmL2_nonneg _ _
  have hHH : Graph.nrmL2 w (H (H h)) ≤ L * x := by
    have := hb.2 (H h); rwa [l2norm_eq_nrmL2, l2norm_eq_nrmL2] at this
  have a2 : Graph.ipL2 w (H h) (H (H h)) ≤ L * x ^ 2 :=
    (Graph.ipL2_le_mul_nrmL2 hw _ _).trans (by nlinarith)
  have p1 := hpsd h
  have h4' : x ^ 2 * x ^ 2 ≤ (L * Graph.ipL2 w h (H h)) * x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left a2 p1]
  rcases hx.lt_or_eq with hxp | hx0
  · exact le_of_mul_le_mul_right h4' (by positivity)
  · rw [← hx0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hb.1 p1

/-- **A step below `2/‖H‖` is stable**: for an operator-norm bound `L` of a linear,
self-adjoint, positive semi-definite `H` and `0 ≤ η` with `ηL ≤ 2`, the linearized descent step
`h ↦ h − ηHh` does not expand `L²(w)`. -/
theorem step_nonexpansive [DecidableEq α] (hw : ∀ x, 0 ≤ w x) (hlin : RLin H)
    (hsym : ∀ a b, Graph.ipL2 w (H a) b = Graph.ipL2 w a (H b))
    (hpsd : ∀ a, 0 ≤ Graph.ipL2 w a (H a)) {L : ℝ} (hb : OpBound w H L) {η : ℝ} (hη : 0 ≤ η)
    (hηL : η * L ≤ 2) (h : α → ℝ) :
    Graph.nrmL2 w (fun x => h x - η * H h x) ≤ Graph.nrmL2 w h := by
  have hsq := nrm_sq_le_form hw hlin hsym hpsd hb h
  have e : (fun x => h x - η * H h x) = fun x => h x + (-η) * H h x := by funext x; ring
  have hq : Graph.ipL2 w (fun x => h x - η * H h x) (fun x => h x - η * H h x)
      = Graph.ipL2 w h h - 2 * η * Graph.ipL2 w h (H h) + η ^ 2 * Graph.nrmL2 w (H h) ^ 2 := by
    rw [e, ipL2_quad, Graph.sq_nrmL2 hw, ipL2_comm w (H h) h]; ring
  have p1 := hpsd h
  have hle : Graph.ipL2 w (fun x => h x - η * H h x) (fun x => h x - η * H h x)
      ≤ Graph.ipL2 w h h := by
    rw [hq]
    have : η ^ 2 * Graph.nrmL2 w (H h) ^ 2 ≤ η * (η * L) * Graph.ipL2 w h (H h) := by
      have := mul_le_mul_of_nonneg_left hsq (sq_nonneg η)
      nlinarith
    have : η * (η * L) * Graph.ipL2 w h (H h) ≤ η * 2 * Graph.ipL2 w h (H h) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηL hη) p1
    linarith
  exact Real.sqrt_le_sqrt hle

end FormToNorm

section TBOps

variable {V : Type*} [Fintype V] [DecidableEq V] {pb : V → V → ℝ} {lam : V → ℝ}

theorem rlin_funAct_iter {α : Type*} [Fintype α] [DecidableEq α] (K : α → α → ℝ) :
    ∀ m : ℕ, RLin (funAct K)^[m]
  | 0 => fun _ _ _ => rfl
  | m + 1 => fun a b t => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', rlin_funAct_iter K m a b t]
      funext x
      simp only [funAct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun y _ => by ring

theorem rlin_densAct_iter {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ)
    (K : α → α → ℝ) : ∀ m : ℕ, RLin (Core.densAct w K)^[m]
  | 0 => fun _ _ _ => rfl
  | m + 1 => fun a b t => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', rlin_densAct_iter w K m a b t]
      funext y
      simp only [Core.densAct_apply, mul_add, Finset.sum_add_distrib, add_div]
      congr 1
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring

theorem rlin_Theta (ℓ : ℕ) : RLin (Theta pb lam ℓ) := fun a b t => by
  funext e
  simp only [Theta, rlin_funAct_iter _ _ a b t, rlin_densAct_iter _ _ _ a b t]
  have : ∀ m ∈ Finset.Ico 1 ℓ, (1 - (m : ℝ) / ℓ)
      * (((funAct (edgeKernelE pb))^[m] a e + t * (funAct (edgeKernelE pb))^[m] b e)
        + ((Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] a e
          + t * (Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] b e))
      = (1 - (m : ℝ) / ℓ) * ((funAct (edgeKernelE pb))^[m] a e
          + (Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] a e)
        + t * ((1 - (m : ℝ) / ℓ) * ((funAct (edgeKernelE pb))^[m] b e
          + (Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[m] b e)) :=
    fun m _ => by ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem rlin_HTB (ℓ : ℕ) : RLin (HTB pb lam ℓ) := fun a b t => by
  have hA : Aop (edgeKernelE pb) (edgeMeasureE pb lam) (fun x => a x + t * b x)
      = fun x => Aop (edgeKernelE pb) (edgeMeasureE pb lam) a x
        + t * Aop (edgeKernelE pb) (edgeMeasureE pb lam) b x := by
    funext x
    simp only [Aop_apply]
    rw [show Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb) (fun x => a x + t * b x) x
        = (Core.densAct (edgeMeasureE pb lam) (edgeKernelE pb))^[1] (fun x => a x + t * b x) x
        from rfl, rlin_densAct_iter _ _ 1 a b t]
    simp only [Function.iterate_one]
    ring
  have hAdj : ∀ u v : EdgeSet pb → ℝ, Adj (edgeKernelE pb) (fun x => u x + t * v x)
      = fun x => Adj (edgeKernelE pb) u x + t * Adj (edgeKernelE pb) v x := by
    intro u v
    funext x
    simp only [Adj_apply]
    rw [show funAct (edgeKernelE pb) (fun x => u x + t * v x) x
        = (funAct (edgeKernelE pb))^[1] (fun x => u x + t * v x) x from rfl,
      rlin_funAct_iter _ 1 u v t]
    simp only [Function.iterate_one]
    ring
  funext e
  simp only [HTB, hA, rlin_Theta ℓ _ _ t, hAdj]
  ring

variable (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1) (hlam : ∀ x, 0 < lam x)
  (hinv : Invariant pb lam)
include hnn hlam hinv

/-- **`rem:tb_vs_db`, `H_TB` is self-adjoint** on `L²(λ₂)` (hence so is `H_DB = H_TB|_{ℓ=1}`). -/
theorem HTB_selfAdjoint (ℓ : ℕ) (a b : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) (HTB pb lam ℓ a) b
      = Graph.ipL2 (edgeMeasureE pb lam) a (HTB pb lam ℓ b) := by
  have hI := edgeMeasureE_isInvariant' hnn hlam hinv
  have hK : ∀ x y, 0 ≤ edgeKernelE pb x y := fun _ _ => edgeKernel_nonneg hnn _ _ _ _
  set c := (ℓ : ℝ) * deriv (deriv logSq) 1
  set A := Aop (edgeKernelE pb) (edgeMeasureE pb lam)
  have e1 : Graph.ipL2 (edgeMeasureE pb lam) (HTB pb lam ℓ a) b
      = c * Graph.ipL2 (edgeMeasureE pb lam) (Theta pb lam ℓ (A a)) (A b) := by
    rw [ipL2_comm, show HTB pb lam ℓ a = fun e => c * Adj (edgeKernelE pb) (Theta pb lam ℓ (A a)) e
      from rfl, Balance.ipL2_smul_right, ipL2_comm, ipL2_Adj_left hI hK]
  have e2 : Graph.ipL2 (edgeMeasureE pb lam) a (HTB pb lam ℓ b)
      = c * Graph.ipL2 (edgeMeasureE pb lam) (Theta pb lam ℓ (A b)) (A a) := by
    rw [show HTB pb lam ℓ b = fun e => c * Adj (edgeKernelE pb) (Theta pb lam ℓ (A b)) e
      from rfl, Balance.ipL2_smul_right, ipL2_comm, ipL2_Adj_left hI hK]
  rw [e1, e2, Theta_selfAdjoint hnn hlam hinv, ipL2_comm _ (A a)]

omit hnn hlam hinv in
theorem HDB_eq : HDB pb lam = HTB pb lam 1 := (HTB_one).symm

include hrow

/-- `⟨h, H_DB h⟩ ≤ 8‖h‖²` (`g''(1) = 2`, `‖A‖ ≤ 2`): `H_DB` is bounded. -/
theorem HDB_form_le_eight (h : EdgeSet pb → ℝ) :
    Graph.ipL2 (edgeMeasureE pb lam) h (HDB pb lam h)
      ≤ 8 * Graph.ipL2 (edgeMeasureE pb lam) h h := by
  have hw : ∀ e, 0 ≤ edgeMeasureE pb lam e := fun e => (edgeMeasureE_pos hlam e).le
  rw [ip_HDB hnn hlam hinv, logSq_deriv2_one, ← Graph.sq_nrmL2 hw, ← Graph.sq_nrmL2 hw]
  have := nrmL2_Aop_le_two (edgeKernelE_isMarkov hnn hrow)
    (edgeMeasureE_isInvariant' hnn hlam hinv) h
  have h0 := Graph.nrmL2_nonneg (edgeMeasureE pb lam) (Aop (edgeKernelE pb) (edgeMeasureE pb lam) h)
  nlinarith

theorem opBound_HTB_of_form (ℓ : ℕ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ a, Graph.ipL2 (edgeMeasureE pb lam) a (HTB pb lam ℓ a)
      ≤ L * Graph.ipL2 (edgeMeasureE pb lam) a a) :
    OpBound (edgeMeasureE pb lam) (HTB pb lam ℓ) L :=
  opBound_of_form (fun e => (edgeMeasureE_pos hlam e).le) (rlin_HTB ℓ)
    (HTB_selfAdjoint hnn hlam hinv ℓ) (HTB_nonneg hnn hrow hlam hinv ℓ) hL0 hL

/-- `‖H_DB‖` is attained: `opNorm λ₂ H_DB` is itself a bound. -/
theorem opBound_HDB_opNorm :
    OpBound (edgeMeasureE pb lam) (HDB pb lam) (opNorm (edgeMeasureE pb lam) (HDB pb lam)) := by
  refine opBound_opNorm ⟨8, ?_⟩
  rw [HDB_eq]
  refine opBound_HTB_of_form hnn hrow hlam hinv 1 (by norm_num) fun a => ?_
  rw [← HDB_eq]
  exact HDB_form_le_eight hnn hrow hlam hinv a

variable (htot : ∑ x, lam x = 1)
include htot

/-- **`rem:tb_vs_db`, the step cap on operator norms**: `‖H_TB‖ ≤ ℓ(1 + 2B̂′)‖H_DB‖` on
`L²(λ₂)`, for every real bound `B` of the partial sums of `B̂′` — the quadratic-form sandwich
`H_TB ⪯ ℓ(1 + 2B̂′)H_DB` read on norms, which needs `H_TB` self-adjoint and `⪰ 0`. -/
theorem opNorm_HTB_le (ℓ : ℕ) {B : ℝ} (hB : ∀ N, ∑ m ∈ range N, betaHat pb lam (m + 1) ≤ B) :
    opNorm (edgeMeasureE pb lam) (HTB pb lam ℓ)
      ≤ ℓ * (1 + 2 * B) * opNorm (edgeMeasureE pb lam) (HDB pb lam) := by
  have hw : ∀ e, 0 ≤ edgeMeasureE pb lam e := fun e => (edgeMeasureE_pos hlam e).le
  have hDB := opBound_HDB_opNorm hnn hrow hlam hinv
  set L := opNorm (edgeMeasureE pb lam) (HDB pb lam)
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hqDB : ∀ h, Graph.ipL2 (edgeMeasureE pb lam) h (HDB pb lam h)
      ≤ L * Graph.ipL2 (edgeMeasureE pb lam) h h := by
    intro h
    have h1 := Graph.ipL2_le_mul_nrmL2 hw h (HDB pb lam h)
    have h2 := hDB.2 h
    rw [l2norm_eq_nrmL2, l2norm_eq_nrmL2] at h2
    rw [← Graph.sq_nrmL2 hw]
    have := Graph.nrmL2_nonneg (edgeMeasureE pb lam) h
    nlinarith
  have hL0 : 0 ≤ L := hDB.1
  have hTB := opBound_HTB_of_form hnn hrow hlam hinv ℓ (by positivity : 0 ≤ ℓ * (1 + 2 * B) * L)
    (stepCap hnn hrow hlam hinv htot ℓ hB hqDB)
  exact csInf_le ⟨0, fun _ hb => hb.1⟩ hTB

/-- **`rem:tb_vs_db`, "a step cap derived from the norm of `H_DB` remains sufficient for TB once
divided by `ℓ(1 + 2B̂′)`"**, as a norm statement: every cap `c` with `η‖H_DB‖ ≤ c` gives
`(η/(ℓ(1 + 2B̂′)))‖H_TB‖ ≤ c` (`ℓ ≥ 1`). -/
theorem stepCap_opNorm {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {B : ℝ}
    (hB : ∀ N, ∑ m ∈ range N, betaHat pb lam (m + 1) ≤ B) {η c : ℝ} (hη : 0 ≤ η)
    (hc : η * opNorm (edgeMeasureE pb lam) (HDB pb lam) ≤ c) :
    η / (ℓ * (1 + 2 * B)) * opNorm (edgeMeasureE pb lam) (HTB pb lam ℓ) ≤ c := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hpos : 0 < (ℓ : ℝ) * (1 + 2 * B) := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    positivity
  have h := opNorm_HTB_le hnn hrow hlam hinv htot ℓ hB
  calc η / (ℓ * (1 + 2 * B)) * opNorm (edgeMeasureE pb lam) (HTB pb lam ℓ)
      ≤ η / (ℓ * (1 + 2 * B)) * (ℓ * (1 + 2 * B) * opNorm (edgeMeasureE pb lam) (HDB pb lam)) :=
        mul_le_mul_of_nonneg_left h (div_nonneg hη hpos.le)
    _ = η * opNorm (edgeMeasureE pb lam) (HDB pb lam) := by field_simp
    _ ≤ c := hc

/-- **The step cap, as stability of the linearized descent**: if `η‖H_DB‖ ≤ 2` — the classical
cap for the DB quadratic model — then with `η′ = η/(ℓ(1 + 2B̂′))` the TB step
`h ↦ h − η′H_TB h` does not expand `L²(λ₂)`; and the DB step `h ↦ h − ηH_DB h` does not either. -/
theorem stepCap_stable {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {B : ℝ}
    (hB : ∀ N, ∑ m ∈ range N, betaHat pb lam (m + 1) ≤ B) {η : ℝ} (hη : 0 ≤ η)
    (hc : η * opNorm (edgeMeasureE pb lam) (HDB pb lam) ≤ 2) (h : EdgeSet pb → ℝ) :
    Graph.nrmL2 (edgeMeasureE pb lam)
        (fun e => h e - η / (ℓ * (1 + 2 * B)) * HTB pb lam ℓ h e)
      ≤ Graph.nrmL2 (edgeMeasureE pb lam) h ∧
    Graph.nrmL2 (edgeMeasureE pb lam) (fun e => h e - η * HDB pb lam h e)
      ≤ Graph.nrmL2 (edgeMeasureE pb lam) h := by
  have hw : ∀ e, 0 ≤ edgeMeasureE pb lam e := fun e => (edgeMeasureE_pos hlam e).le
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hpos : 0 < (ℓ : ℝ) * (1 + 2 * B) := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    positivity
  have hTBb : OpBound (edgeMeasureE pb lam) (HTB pb lam ℓ)
      (opNorm (edgeMeasureE pb lam) (HTB pb lam ℓ)) := by
    refine opBound_opNorm ⟨ℓ * (1 + 2 * B) * 8, ?_⟩
    refine opBound_HTB_of_form hnn hrow hlam hinv ℓ (by positivity) fun a => ?_
    calc Graph.ipL2 (edgeMeasureE pb lam) a (HTB pb lam ℓ a)
        ≤ ℓ * (1 + 2 * B) * Graph.ipL2 (edgeMeasureE pb lam) a (HDB pb lam a) :=
          HTB_le hnn hrow hlam hinv htot ℓ hB a
      _ ≤ ℓ * (1 + 2 * B) * (8 * Graph.ipL2 (edgeMeasureE pb lam) a a) :=
          mul_le_mul_of_nonneg_left (HDB_form_le_eight hnn hrow hlam hinv a) hpos.le
      _ = _ := by ring
  refine ⟨step_nonexpansive hw (rlin_HTB ℓ) (HTB_selfAdjoint hnn hlam hinv ℓ)
    (HTB_nonneg hnn hrow hlam hinv ℓ) hTBb (div_nonneg hη hpos.le)
    (stepCap_opNorm hnn hrow hlam hinv htot hℓ hB hη hc) h, ?_⟩
  have hb1 : OpBound (edgeMeasureE pb lam) (HTB pb lam 1)
      (opNorm (edgeMeasureE pb lam) (HDB pb lam)) := by
    rw [← HDB_eq]; exact opBound_HDB_opNorm hnn hrow hlam hinv
  have := step_nonexpansive hw (rlin_HTB 1) (HTB_selfAdjoint hnn hlam hinv 1)
    (HTB_nonneg hnn hrow hlam hinv 1) hb1 hη hc h
  rwa [← HDB_eq] at this

end TBOps

section Witness

/-- **Inhabitation of the step-cap statements** (kb `0025`): on the uniform two-state chain,
`B = 1` bounds `B̂′`, so `opNorm_HTB_le` and `stepCap_stable` apply with `ℓ(1 + 2B̂′) = 3ℓ`. -/
theorem stepCap_witness {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {η : ℝ} (hη : 0 ≤ η)
    (hc : η * opNorm (edgeMeasureE pbU lamU) (HDB pbU lamU) ≤ 2) (h : EdgeSet pbU → ℝ) :
    opNorm (edgeMeasureE pbU lamU) (HTB pbU lamU ℓ)
        ≤ ℓ * (1 + 2 * 1) * opNorm (edgeMeasureE pbU lamU) (HDB pbU lamU) ∧
      Graph.nrmL2 (edgeMeasureE pbU lamU)
          (fun e => h e - η / (ℓ * (1 + 2 * 1)) * HTB pbU lamU ℓ h e)
        ≤ Graph.nrmL2 (edgeMeasureE pbU lamU) h := by
  obtain ⟨-, -, hB, -⟩ := witness ℓ h
  exact ⟨opNorm_HTB_le pbU_nonneg pbU_row lamU_pos lamU_inv lamU_tot ℓ hB,
    (stepCap_stable pbU_nonneg pbU_row lamU_pos lamU_inv lamU_tot hℓ hB hη hc h).1⟩

/-- **Inhabitation of the complex Fejér clause** (kb `0025`): on any chain meeting the
hypotheses, `u ≡ 1` is an eigenfunction of `Q` with eigenvalue `e^{i·0}`, so the hypothesis `hu`
of `rayleigh_fejerC` is inhabited. -/
theorem fejerC_witness {V : Type*} [Fintype V] [DecidableEq V] {pb : V → V → ℝ}
    (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1) :
    funActC (pb := pb) (fun _ => (1 : ℂ)) = fun _ => Complex.exp ((0 : ℝ) * I) * 1 := by
  funext e
  simp only [funActC, mul_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [← Complex.ofReal_sum, (edgeKernelE_isMarkov hnn hrow).row_sum e, Complex.ofReal_one]

end Witness

end GFNBounds.Balance.TBHessian
