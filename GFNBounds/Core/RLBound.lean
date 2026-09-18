import GFNBounds.Core.StableBound
import GFNBounds.Core.NegativeControl
import GFNBounds.Core.FamilyUniversality

/-!
# The stable-loss bound completed: `q = ∞`, Step 0, the two external inputs, and items (2)–(3)

**`theo:RL_CV_bound_full`** — `proofs.tex`, subsection `app:stable` (Theorem 17 of the ledger).
Line numbers drift (kb `0036`); the label is the anchor. `Core/StableBound.lean` proved item (1)
at finite `q` with three hypotheses standing for what it could not build (`hz`, `hNC`, `htri`);
this file finishes the row as far as the built layers reach. The body restatement
`theo:RL_CV_bound` (`cv_stable.tex`) is certified through this row.

> Let `(𝒮, ν_B)` be a Polish space endowed with a non-negative finite background measure, let
> `F_init ≪ ν_B` be a non-zero initial flow and let `κ ≪ ν_B` be a non-zero, possibly unnormalized
> target with known density with respect to `ν_B`. Let `q ∈ [1, +∞]` and let `ν_T` be a
> probability measure with `ν_B ≪ ν_T` and `dν_B/dν_T ∈ L^∞(ν_T)`. Write
> `C₀ := ν_B(𝒮)^{1−1/q} ‖dν_B/dν_T‖^{1/q}_{L^∞(ν_T)}`, `C := 2C₀/κ(𝒮)`. Let `(π⋆, f⋆_out)` be a
> generative flow trained on the target `F_term = κ` with loss `𝓛`, but using `F_term = κ̂ := E⁺`
> during inference, where `E := F_init + F⋆_← − F⋆_out`. Write `t := κ(𝒮)`. Then:
> (1) `TV(s_τ ‖ κ/t) ≤ C 𝓛` and `|F_init(𝒮) − κ(𝒮)| ≤ C₀ 𝓛`;
> (2) the infimum of the loss is `0` at an initial flow carrying the target's total mass. If `Θ`
> is a `L^p`-universal family of generative flows with `q ≤ p`, if `f_init` and `dκ/dν_B` lie in
> `L^p(ν_B)`, if the masses match, `κ(𝒮) = F_init(𝒮)`, and if `ν_T ≪ ν_B` with
> `dν_T/dν_B ∈ L^{q'}(ν_B)`, `q' = p/(p−q)` with `q' = 1` when `p = +∞` — only the domination
> being required when `q = p = +∞` — then `inf_{(π⋆, f⋆_out) ∈ Θ} 𝓛 = 0`;
> (3) the mass is the only obstruction over a trainable initial family. Call *initial family* a
> set `𝓘` of non-zero initial flows `F_init ≪ ν_B` and write `Z(𝓘) := {F_init(𝒮) : F_init ∈ 𝓘}`,
> `Z^p(𝓘) := {F_init(𝒮) : F_init ∈ 𝓘, f_init ∈ L^p(ν_B)}`. Under the hypotheses of (2) on `Θ`,
> on `dκ/dν_B` and on `ν_T`,
> `t ∈ closure Z^p(𝓘) ⟹ inf_{𝓘×Θ} 𝓛 = 0 ⟹ t ∈ closure Z(𝓘)`,
> the two conditions coinciding when every member of `𝓘` has its density in `L^p(ν_B)`.

## What is proved

| paper | here |
|---|---|
| Step 3 at every `q ∈ [1, ∞]` (the `q = ∞` lines included) | `lintegral_enorm_le_holderConst`, `integral_abs_le_holderConst`; `holderConst_top`: `C₀ = ν_B(𝒮)` at `q = ∞` |
| the loss `𝓛 = ‖e − k‖_{L^q(ν_T)}` | `(eLpNorm (e − k) q ν_T).toReal` in item (1), `eLpNorm (defectFn ν θ f_init k) q ν_T ∈ [0, ∞]` in items (2)–(3); `stableLoss_eq_toReal_eLpNorm` identifies it with `Core.stableLoss` at finite `q` |
| (1) both displays, every `q ∈ [1, ∞]`, general measurable space | `mass_floorE`, `stable_boundE` (with `hz`, `hNC`, `htri` as in `Core.stable_bound`) |
| Step 0 `E(𝒮) = F_init(𝒮)` for a kernel flow | `eFn`, `integral_eFn` (needs `ν_B π⋆ ≪ ν_B`, see SCOPE) |
| (1) `equ:mass_floor` for a kernel flow, nothing external | `mass_floor_kernel` |
| (1) `equ:stable_bound` for a kernel flow, `hz` discharged | `stable_bound_kernel` (`hNC`, `htri` remain) |
| (1) both displays, **all three hypotheses discharged**, finite `𝒮` | `stable_bound_finite` — `hNC` by `NegativeControl.negative_control_hNC`, `htri` by `Core.tvD_triangle`, `hz` by `negative_control_hNC` (its mass identity, via `integral_eDens` and `sum_emass`) |
| `q' = p/(p−q)`, `q' = 1` at `p = ∞` | `conjExp`; `holderConjugate_conjExp`: `1/q' + q/p = 1` |
| Step 4's Hölder transfer | `eLpNorm_le_transferConst`, constant `transferConst` explicit (rule 3) |
| `equ:defect_equivalence`, lower half, for a kernel flow | `eLpNorm_defectFn_le_residual` |
| (2) | `inf_loss_eq_zero`, every `1 ≤ q ≤ p ≤ ∞` |
| (2) at `p = ∞`, only `ν_T ≪ ν_B` | `inf_loss_eq_zero_top` (with `memLp_rho_top`) |
| (3) initial family, `Z`, `Z^p` | `IsInitialFamily`, `massSet`, `massSetLp` |
| (3) `equ:joint_infimum` | `joint_inf_eq_zero` (⟹ left), `mem_closure_of_joint_inf` (⟹ right), `joint_infimum` (both) |
| "the two conditions coinciding …" | `massSetLp_eq_massSet` |
| inhabitation of (2)'s hypotheses (kb `0025`, `0027`) | `inf_loss_eq_zero_const_kernel` |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` Polish, `ν_B` finite | ⚠ any `MeasurableSpace α` with `[IsFiniteMeasure ν]` (Polish used nowhere); `stable_bound_finite` on a finite `V` — see SCOPE |
| `F_init ≪ ν_B` non-zero | ✓ a density `f_init`, integrable; non-zero as `0 < ∫ f_init` (item 1), `¬ f =ᵐ 0` in `IsInitialFamily` (item 3). In `stable_bound_finite`, `F.finit ≠ 0` on atoms |
| `κ ≪ ν_B` non-zero, known density | ✓ `k`, `0 ≤ᵐ k`, `0 < ∫ k` |
| `q ∈ [1, +∞]` | ✓ `q : ℝ≥0∞`, `1 ≤ q` — **`q = ∞` now covered** |
| `ν_T` probability, `ν_B ≪ ν_T`, `dν_B/dν_T ∈ L^∞(ν_T)` | ✓ `hdom : ν ≤ M • ν_T` as in `Core.StableBound`; item (2) asks `[IsFiniteMeasure ν_T]` only; item (3)'s right implication also uses `hdom`, through `equ:mass_floor` |
| `(π⋆, f⋆_out)` a generative flow, `E := F_init + F⋆_← − F⋆_out` | ✓ `Family.IsGenerativeFlow` (Markov kernel, `f⋆_out ≥ 0` integrable), `E = eFn`; **plus `ν_B π⋆ ≪ ν_B`**, see SCOPE |
| inference at `κ̂ := E⁺`, sampler `s_τ` | general space: `hNC`/`htri` hypotheses; finite space: `NegativeControl.inference`, its limit law `p` |
| (2) `Θ` `L^p`-universal | ✓ `Family.WeaklyUniversal ν p Θ` (arbitrary `Θ`, `def:universality`) |
| (2) `f_init`, `dκ/dν_B ∈ L^p`, masses match | ✓ `Family.IsAdmissiblePair ν p f_init k` (also carries `f_init ≥ 0`, `k ≥ 0`) |
| (2) `ν_T ≪ ν_B`, `dν_T/dν_B ∈ L^{q'}(ν_B)` | ✓ `hac`, `hρ : MemLp (rho ν_T ν) (conjExp p q) ν` |
| (2) "only the domination when `q = p = ∞`" | ✓ `inf_loss_eq_zero_top` — and at `p = ∞` for every `q`, see SCOPE |
| (3) hypotheses of (2) on `Θ`, `dκ/dν_B`, `ν_T` | ✓ carried by `joint_infimum`; the right implication uses of `Θ` only `IsFlowFamily` and `ν_B π⋆ ≪ ν_B` (both inside `WeaklyUniversal`) |

## SCOPE (disclosed)

* **The TV display of item (1) is discharged only on a finite state space.** On a general
  measurable space `stable_boundE`/`stable_bound_kernel` keep `hNC` (`theo:negative_control`) and
  `htri` (the triangle inequality for the law of `s_τ`) as hypotheses: `theo:negative_control` is
  proved in `Core/NegativeControl.lean` on a finite space only, and the sampler as a sub-Markov
  kernel on a Polish space is the general measure layer (obstruction 2 of kb `0006`).
  `stable_bound_finite` closes both displays with nothing external, on a finite `V` with a
  background measure charging every atom (`NegativeControl`'s standing narrowing, which it
  inherits). **The row therefore stays in bucket `B`**: the paper's setting is Polish, not finite.
* **Everything else is on the paper's general setting.** `equ:mass_floor` (`mass_floor_kernel`),
  items (2) and (3), and the `q = ∞` case hold on any measurable space with `ν_B` finite, Polish
  never used.
* **`ν_B π⋆ ≪ ν_B` is asked where `E`'s density is formed** (`integral_eFn`, `mass_floor_kernel`,
  `stable_bound_kernel`, `ofReal_mass_gap_le`). The paper writes `e = dE/dν_B`, which exists only
  if `(f⋆_out ν_B) π⋆ ≪ ν_B`; it supplies this by the standing convention of `proofs.tex`'s notation
  paragraph ("in `app:universality` and `app:stable` … the star policy is assumed
  `ν_B`-invariant"), which is stronger than what is asked here. Item (2)–(3) take it from
  `Family.WeaklyUniversal` (`IsBoundedPolicy`'s first conjunct). Reported as a finding: item (1)'s
  statement does not itself carry it.
* **`q' = 1` at `p = ∞` makes the integrability hypothesis automatic there, at every `q`**
  (`memLp_rho_top`): a Radon–Nikodym derivative of a finite measure is integrable. The paper's
  "only the domination being required when `q = p = ∞`" is therefore true and also true at
  `q < p = ∞`; nothing is claimed beyond `inf_loss_eq_zero_top`.
* **At `q = p < ∞`, `q' = p/(p − q)` is `p/0 = ∞` in `ℝ≥0∞`** — the reading Step 4's Hölder at
  exponents `p/q = 1` and `q'` needs; the paper leaves the value at `q = p` to the convention.
* **The loss is carried in `[0, ∞]` in items (2)–(3)** (`eLpNorm`), so a member whose residual is not
  in `L^q(ν_T)` counts `∞` and the infimum is an honest infimum; in item (1) the loss is its real
  value under `MemLp (e − k) q ν_T` (the paper's tacit "the loss is finite", as in `Core.StableBound`;
  automatic on a finite space).
* **Measures are densities**, as in `Core/StableBound.lean` and `Core/FamilyUniversality.lean`:
  `F_init = f_init ν_B`, `κ = k ν_B`, and `F⋆_← = F⋆_out π⋆` has `ν_B`-density `densityAction`.
* **No `sorry`.**

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core.RLBound

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## Step 3 at every `q ∈ [1, ∞]` -/

theorem holderConst_nonneg (ν : Measure α) (M : ℝ≥0) (q : ℝ) : 0 ≤ holderConst ν M q := by
  unfold holderConst
  positivity

/-- At `q = ∞` the constant `C₀` of `equ:stable_constants` is `ν_B(𝒮)`: the real exponents
`1 − 1/q` and `1/q` read `1` and `0` at `q.toReal = 0`. -/
theorem holderConst_top (ν : Measure α) (M : ℝ≥0) :
    holderConst ν M (⊤ : ℝ≥0∞).toReal = ν.real Set.univ := by
  simp [holderConst]

theorem one_sub_inv_nonneg {q : ℝ≥0∞} (hq : 1 ≤ q) : 0 ≤ 1 - 1 / q.toReal := by
  rcases eq_or_ne q ⊤ with rfl | hqt
  · simp
  · have h1 : 1 ≤ q.toReal := by
      have := ENNReal.toReal_mono hqt hq
      simpa using this
    have : 1 / q.toReal ≤ 1 := by
      rw [div_le_one (by linarith)]; exact h1
    linarith

/-- **`theo:RL_CV_bound_full`, Step 3 at every `q ∈ [1, ∞]`, in `[0, ∞]`**:
`∫ |f| dν_B ≤ C₀ ‖f‖_{L^q(ν_T)}`, `C₀ = ν_B(𝒮)^{1−1/q} M^{1/q}` with `ν_B ≤ M ν_T`. At `q = ∞`
this is the paper's two extra lines, `Δ ≤ ν_B(𝒮)‖·‖_{L^∞(ν_B)} ≤ ν_B(𝒮)‖·‖_{L^∞(ν_T)}`. -/
theorem lintegral_enorm_le_holderConst {ν νT : Measure α} [IsFiniteMeasure ν] {M : ℝ≥0}
    (hdom : ν ≤ (M : ℝ≥0∞) • νT) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    ∫⁻ x, ‖f x‖ₑ ∂ν ≤ ENNReal.ofReal (holderConst ν M q.toReal) * eLpNorm f q νT := by
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hf
  simp only [ENNReal.toReal_one, div_one] at h1
  rw [← eLpNorm_one_eq_lintegral_enorm]
  have h2 : eLpNorm f q ν ≤ (M : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm f q νT := by
    refine (eLpNorm_mono_measure f hdom).trans ?_
    rcases eq_or_ne M 0 with hM | hM
    · subst hM
      simp
    · rw [eLpNorm_smul_measure_of_ne_zero (by exact_mod_cast hM), smul_eq_mul]
  have hexp := one_sub_inv_nonneg hq
  have hconst : ENNReal.ofReal (holderConst ν M q.toReal)
      = ν Set.univ ^ (1 - 1 / q.toReal) * (M : ℝ≥0∞) ^ (1 / q).toReal := by
    unfold holderConst
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg hexp,
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ENNReal.ofReal_coe_nnreal,
      measureReal_def, ENNReal.ofReal_toReal (measure_ne_top ν _), ENNReal.toReal_div,
      ENNReal.toReal_one]
  rw [hconst]
  calc eLpNorm f 1 ν ≤ eLpNorm f q ν * ν Set.univ ^ (1 - 1 / q.toReal) := h1
    _ ≤ (M : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm f q νT * ν Set.univ ^ (1 - 1 / q.toReal) := by
        gcongr
    _ = ν Set.univ ^ (1 - 1 / q.toReal) * (M : ℝ≥0∞) ^ (1 / q).toReal * eLpNorm f q νT := by
        ring

/-- **`theo:RL_CV_bound_full`, Step 3 in real form at every `q ∈ [1, ∞]`**: `Δ ≤ C₀ 𝓛`, with the loss
`𝓛 = ‖e − k‖_{L^q(ν_T)}` read as `(eLpNorm (e − k) q ν_T).toReal`. -/
theorem integral_abs_le_holderConst {ν νT : Measure α} [IsFiniteMeasure ν] {M : ℝ≥0}
    (hdom : ν ≤ (M : ℝ≥0∞) • νT) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) (hmem : MemLp f q νT) :
    ∫ x, |f x| ∂ν ≤ holderConst ν M q.toReal * (eLpNorm f q νT).toReal := by
  have h := lintegral_enorm_le_holderConst hdom hq hf
  have hfin : ENNReal.ofReal (holderConst ν M q.toReal) * eLpNorm f q νT ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmem.eLpNorm_ne_top
  have h' := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (holderConst_nonneg _ _ _),
    ← integral_norm_eq_lintegral_enorm hf] at h'
  simpa [Real.norm_eq_abs] using h'

/-- The real form of the loss agrees with `Core.stableLoss` at finite `q`. -/
theorem stableLoss_eq_toReal_eLpNorm {νT : Measure α} {q : ℝ} (hq : 1 ≤ q) {e k : α → ℝ}
    (hmem : MemLp (fun x => e x - k x) (ENNReal.ofReal q) νT) :
    stableLoss νT q e k = (eLpNorm (fun x => e x - k x) (ENNReal.ofReal q) νT).toReal := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  rw [hmem.eLpNorm_eq_integral_rpow_norm hq0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ =>
      Real.rpow_nonneg (norm_nonneg _) _) _), ENNReal.toReal_ofReal (by linarith)]
  simp only [stableLoss, Real.norm_eq_abs, one_div]

/-! ## Item (1) at every `q ∈ [1, ∞]` -/

section ItemOne

variable {ν νT : Measure α} {e k : α → ℝ}

/-- **`equ:mass_floor` at every `q ∈ [1, ∞]`**: `|F_init(𝒮) − κ(𝒮)| ≤ C₀ 𝓛`, `z` being
`F_init(𝒮)` through Step 0's `hz` (discharged in `mass_floor_kernel` and `stable_bound_finite`). -/
theorem mass_floorE [IsFiniteMeasure ν] {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hmem : MemLp (fun x => e x - k x) q νT) (he : Integrable e ν)
    (hk : Integrable k ν) {z t : ℝ} (hz : z = ∫ x, e x ∂ν) (ht : t = ∫ x, k x ∂ν) :
    |z - t| ≤ holderConst ν M q.toReal * (eLpNorm (fun x => e x - k x) q νT).toReal := by
  have h1 := mass_defect_le (e := e) (k := k) he hk
  rw [← hz, ← ht] at h1
  exact h1.trans (integral_abs_le_holderConst (f := fun x => e x - k x) hdom hq (he.sub hk).1 hmem)

/-- **`equ:stable_bound` at every `q ∈ [1, ∞]`**: `TV(s_τ ‖ κ/t) ≤ C 𝓛`, `C = 2C₀/t`. The
hypotheses `hNC` (`theo:negative_control`) and `htri` (the triangle inequality for the abstract
sampler) are those of `Core.stable_bound`; `stable_bound_finite` discharges both. At `q = ∞`
the constant is `2ν_B(𝒮)/t` (`holderConst_top`). -/
theorem stable_boundE [IsFiniteMeasure ν] {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hmem : MemLp (fun x => e x - k x) q νT) (he : Integrable e ν)
    (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k) {z t zhat tv tvNC : ℝ}
    (hz : z = ∫ x, e x ∂ν) (ht : t = ∫ x, k x ∂ν) (hzh : zhat = ∫ x, max (e x) 0 ∂ν)
    (hz0 : 0 < z) (ht0 : 0 < t)
    (hNC : tvNC ≤ (∫ x, max (-e x) 0 ∂ν) / zhat)
    (htri : tv ≤ tvNC + tvD ν (fun x => max (e x) 0 / zhat) (fun x => k x / t)) :
    tv ≤ stableConst ν M q.toReal t * (eLpNorm (fun x => e x - k x) q νT).toReal := by
  have h1 := tv_le_two_fmL1 he hk hk0 hz ht hzh hz0 ht0 hNC htri
  have h2 := integral_abs_le_holderConst (f := fun x => e x - k x) hdom hq (he.sub hk).1 hmem
  have h4 : 2 * (∫ x, |e x - k x| ∂ν) / t
      ≤ 2 * (holderConst ν M q.toReal * (eLpNorm (fun x => e x - k x) q νT).toReal) / t := by
    gcongr
  have h5 : 2 * (holderConst ν M q.toReal * (eLpNorm (fun x => e x - k x) q νT).toReal) / t
      = stableConst ν M q.toReal t * (eLpNorm (fun x => e x - k x) q νT).toReal := by
    rw [stableConst]; ring
  linarith

end ItemOne

/-! ## Step 0 for a kernel flow: `E(𝒮) = F_init(𝒮)`, on the general measurable space -/

section Kernel

open GFNBounds.Core.Family

variable {ν νT : Measure α} {θ : ProbabilityTheory.Kernel α α × (α → ℝ)} {f_init k : α → ℝ}

/-- `E = F_init + F⋆_out π⋆ − F⋆_out` as a `ν`-density: `densityAction` is the `ν`-density of
`(f⋆_out ν) π⋆` (`Family.defectFn` with `F_term = 0`). -/
noncomputable def eFn (ν : Measure α) (θ : ProbabilityTheory.Kernel α α × (α → ℝ))
    (f_init : α → ℝ) : α → ℝ :=
  fun x => f_init x + densityAction θ.1 ν θ.2 x - θ.2 x

theorem defectFn_eq_eFn_sub (x : α) : defectFn ν θ f_init k x = eFn ν θ f_init x - k x := rfl

theorem integrable_eFn [SigmaFinite ν] (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν)
    (hi : Integrable f_init ν) : Integrable (eFn ν θ f_init) ν := by
  haveI := hθ.markov
  exact (hi.add (integrable_densityAction_of_ac θ.1 hac hθ.integrable)).sub hθ.integrable

/-- **`equ:mass_identity`, Step 0's first half**, for a Markov kernel `π⋆` with
`ν π⋆ ≪ ν`: `E(𝒮) = F_init(𝒮)`, because `F⋆_←(𝒮) = F⋆_out(𝒮)`. This discharges the hypothesis
`hz` of `Core.stable_bound`/`Core.mass_floor`. -/
theorem integral_eFn [SigmaFinite ν] (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν)
    (hi : Integrable f_init ν) : ∫ x, eFn ν θ f_init x ∂ν = ∫ x, f_init x ∂ν := by
  have h := integral_defectFn (f_term := fun _ => (0 : ℝ)) hθ hac hi (integrable_zero _ _ _)
  simpa [defectFn, eFn] using h

/-- **`equ:mass_floor` for a kernel flow, nothing assumed beyond the paper**: on any measurable
space, for a generative flow `(π⋆, f⋆_out)` with `ν_B π⋆ ≪ ν_B`, at every `q ∈ [1, ∞]`,
`|F_init(𝒮) − κ(𝒮)| ≤ C₀ ‖e − k‖_{L^q(ν_T)}`. -/
theorem mass_floor_kernel [IsFiniteMeasure ν] {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν)
    (hi : Integrable f_init ν) (hk : Integrable k ν)
    (hmem : MemLp (defectFn ν θ f_init k) q νT) :
    |(∫ x, f_init x ∂ν) - ∫ x, k x ∂ν|
      ≤ holderConst ν M q.toReal * (eLpNorm (defectFn ν θ f_init k) q νT).toReal :=
  mass_floorE (e := eFn ν θ f_init) hdom hq hmem (integrable_eFn hθ hac hi) hk
    (integral_eFn hθ hac hi).symm rfl

/-- **`equ:stable_bound` for a kernel flow**: Step 0 (`hz`) discharged; `hNC`
(`theo:negative_control`, proved in this library only on a finite space) and `htri` (the
triangle inequality for a sampler this library does not build on a general space) remain
hypotheses. -/
theorem stable_bound_kernel [IsFiniteMeasure ν] {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν)
    (hi : Integrable f_init ν) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k)
    (hmem : MemLp (defectFn ν θ f_init k) q νT)
    (hz0 : 0 < ∫ x, f_init x ∂ν) (ht0 : 0 < ∫ x, k x ∂ν) {tv tvNC : ℝ}
    (hNC : tvNC ≤ (∫ x, max (-eFn ν θ f_init x) 0 ∂ν) / ∫ x, max (eFn ν θ f_init x) 0 ∂ν)
    (htri : tv ≤ tvNC + tvD ν (fun x => max (eFn ν θ f_init x) 0 /
      ∫ x, max (eFn ν θ f_init x) 0 ∂ν) (fun x => k x / ∫ x, k x ∂ν)) :
    tv ≤ stableConst ν M q.toReal (∫ x, k x ∂ν)
      * (eLpNorm (defectFn ν θ f_init k) q νT).toReal :=
  stable_boundE (e := eFn ν θ f_init) hdom hq hmem (integrable_eFn hθ hac hi) hk hk0
    (integral_eFn hθ hac hi).symm rfl rfl hz0 ht0 hNC htri

end Kernel

/-! ## Item (1) with nothing external, on a finite state space -/

section Finite

open GFNBounds.Core.Sampling GFNBounds.Core.NegativeControl

variable {V : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **`theo:RL_CV_bound_full`, item (1), both displays, with `hNC`, `htri` and `hz` all
discharged**, on a finite state space with a background measure `ν` charging every atom: the
sampler inferring at `κ̂ = E⁺` from `F_init` has a limit law `p` (`∑ p = 1`), and at every
`q ∈ [1, ∞]`

  `TV(s_τ ‖ κ/t) ≤ C 𝓛`,  `|F_init(𝒮) − κ(𝒮)| ≤ C₀ 𝓛`,

with `𝓛 = ‖e − k‖_{L^q(ν_T)}`, `e = dE/dν`, `C₀ = holderConst`, `C = stableConst`. -/
theorem stable_bound_finite (ν : Measure V) [IsFiniteMeasure ν] (hν : ∀ x, 0 < ν.real {x})
    {νT : Measure V} [IsFiniteMeasure νT] {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT)
    (F : FlowData V) (hfi : ∀ x, 0 ≤ F.finit x) (hfo : ∀ x, 0 ≤ F.fout x)
    (hP0 : ∀ x y, 0 ≤ F.P x y) (hP1 : ∀ x, ∑ y, F.P x y = 1) (hinit : F.finit ≠ 0)
    {k : V → ℝ} (hk0 : ∀ x, 0 ≤ k x) (ht0 : 0 < ∫ x, k x ∂ν) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ p : V → ℝ,
      (∀ y, Tendsto (fun n => (inference F).law n (y, true)) atTop (𝓝 (p y))) ∧
      ∑ y, p y = 1 ∧
      tvD ν (fun y => p y / ν.real {y}) (fun x => k x / ∫ x, k x ∂ν)
        ≤ stableConst ν M q.toReal (∫ x, k x ∂ν)
          * (eLpNorm (fun x => eDens ν F x - k x) q νT).toReal ∧
      |(∑ x, F.finit x) - ∫ x, k x ∂ν|
        ≤ holderConst ν M q.toReal * (eLpNorm (fun x => eDens ν F x - k x) q νT).toReal := by
  obtain ⟨p, hp, hp1, hz, -, hNC⟩ := negative_control_hNC ν hν F hfi hfo hP0 hP1 hinit
  have hmem : MemLp (fun x => eDens ν F x - k x) q νT := MemLp.of_discrete
  have hz0 : 0 < ∫ x, eDens ν F x ∂ν := by rw [hz]; exact sum_pos_of_ne_zero hfi hinit
  refine ⟨p, hp, hp1, ?_, ?_⟩
  · exact stable_boundE hdom hq hmem Integrable.of_finite Integrable.of_finite
      (Filter.Eventually.of_forall hk0) rfl rfl rfl hz0 ht0 hNC
      (tvD_triangle Integrable.of_finite Integrable.of_finite)
  · exact mass_floorE hdom hq hmem Integrable.of_finite Integrable.of_finite hz.symm rfl

end Finite

/-! ## Item (2): the second Hölder transfer, from `L^p(ν_B)` to the training measure -/

section Transfer

variable {ν νT : Measure α}

/-- **The exponent `q'` of item (2)**: `q' = p/(p − q)`, and `q' = 1` when `p = ∞`
(`proofs.tex`, `theo:RL_CV_bound_full`(2)). At `q = p < ∞` it is `p/0 = ∞`. -/
noncomputable def conjExp (p q : ℝ≥0∞) : ℝ≥0∞ := if p = ⊤ then 1 else p / (p - q)

/-- `q'` and `p/q` are Hölder conjugate: `1/q' + q/p = 1`, for `1 ≤ q < ∞`, `q ≤ p`. -/
theorem holderConjugate_conjExp {p q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ⊤) (hqp : q ≤ p) :
    ENNReal.HolderTriple (conjExp p q) (p / q) 1 := by
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
  refine ⟨?_⟩
  rcases eq_or_ne p ⊤ with rfl | hpt
  · simp [conjExp, ENNReal.top_div_of_ne_top hqt]
  · have hp0 : p ≠ 0 := (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hq) hqp).ne'
    simp only [conjExp, hpt, if_false, inv_one]
    rw [ENNReal.inv_div (Or.inl (ENNReal.sub_ne_top hpt)) (Or.inr hp0),
      ENNReal.inv_div (Or.inl hqt) (Or.inl hq0), ENNReal.div_add_div_same,
      tsub_add_cancel_of_le hqp, ENNReal.div_self hp0 hpt]

/-- `dν_T/dν_B`, as a real function. -/
noncomputable def rho (νT ν : Measure α) (x : α) : ℝ := (νT.rnDeriv ν x).toReal

/-- **The constant of the second Hölder transfer**: `‖dν_T/dν_B‖_{L^{q'}(ν_B)}^{1/q}` at
`q < ∞`, and `1` at `q = ∞` (where only the domination `ν_T ≪ ν_B` is used). -/
noncomputable def transferConst (νT ν : Measure α) (p q : ℝ≥0∞) : ℝ≥0∞ :=
  if q = ⊤ then 1 else eLpNorm (rho νT ν) (conjExp p q) ν ^ (1 / q.toReal)

theorem transferConst_ne_top {p q : ℝ≥0∞} (hρ : MemLp (rho νT ν) (conjExp p q) ν) :
    transferConst νT ν p q ≠ ⊤ := by
  unfold transferConst
  split_ifs
  · exact ENNReal.one_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hρ.eLpNorm_ne_top

/-- At `p = ∞` the integrability hypothesis on `dν_T/dν_B` is automatic: `q' = 1`, and a
Radon–Nikodym derivative of a finite measure is integrable. This is the paper's "only the
domination being required when `q = p = ∞`" — and, since `q' = 1` whenever `p = ∞`, at every
`q` when `p = ∞`. -/
theorem memLp_rho_top [IsFiniteMeasure νT] (q : ℝ≥0∞) :
    MemLp (rho νT ν) (conjExp ⊤ q) ν := by
  simp only [conjExp, if_true]
  exact memLp_one_iff_integrable.2 Measure.integrable_toReal_rnDeriv

/-- **`theo:RL_CV_bound_full`, Step 4's Hölder transfer**: for `ν_T ≪ ν_B`,
`1 ≤ q ≤ p`,

  `‖f‖_{L^q(ν_T)} ≤ ‖dν_T/dν_B‖^{1/q}_{L^{q'}(ν_B)} ‖f‖_{L^p(ν_B)}`,

by Hölder with the exponents `p/q` and `q'`; at `q = p = ∞`, `‖f‖_{L^∞(ν_T)} ≤ ‖f‖_{L^∞(ν_B)}`. -/
theorem eLpNorm_le_transferConst [SigmaFinite ν] [SigmaFinite νT] (hac : νT ≪ ν) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hqp : q ≤ p) {f : α → ℝ} (hf : AEStronglyMeasurable f ν) :
    eLpNorm f q νT ≤ transferConst νT ν p q * eLpNorm f p ν := by
  rcases eq_or_ne q ⊤ with rfl | hqt
  · have hp : p = ⊤ := top_le_iff.1 hqp
    subst hp
    simp only [transferConst, if_true, one_mul, eLpNorm_exponent_top]
    exact eLpNormEssSup_mono_measure f hac
  · have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
    haveI := holderConjugate_conjExp hq hqt hqp
    set r : ℝ := q.toReal with hr
    have hr0 : 0 < r := ENNReal.toReal_pos hq0 hqt
    simp only [transferConst, hqt, if_false]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt]
    set g : α → ℝ := fun x => ‖f x‖ ^ r with hg
    have hgm : AEStronglyMeasurable g ν := ((hf.aemeasurable.norm).pow_const r).aestronglyMeasurable
    have hρm : AEStronglyMeasurable (rho νT ν) ν :=
      (Measure.measurable_rnDeriv νT ν).ennreal_toReal.aestronglyMeasurable
    have hpq : p / q * ENNReal.ofReal r = p := by
      rw [hr, ENNReal.ofReal_toReal hqt, ENNReal.div_mul_cancel hq0 hqt]
    have hkey : ∫⁻ x, ‖f x‖ₑ ^ r ∂νT ≤ eLpNorm (rho νT ν) (conjExp p q) ν * eLpNorm f p ν ^ r := by
      rw [← lintegral_rnDeriv_mul hac (hf.enorm.pow_const r)]
      have hcongr : (fun x => νT.rnDeriv ν x * ‖f x‖ₑ ^ r) =ᵐ[ν] fun x => ‖(rho νT ν • g) x‖ₑ := by
        filter_upwards [Measure.rnDeriv_lt_top νT ν] with x hx
        show νT.rnDeriv ν x * ‖f x‖ₑ ^ r = ‖(νT.rnDeriv ν x).toReal * ‖f x‖ ^ r‖ₑ
        rw [enorm_mul, Real.enorm_eq_ofReal (ENNReal.toReal_nonneg : 0 ≤ (νT.rnDeriv ν x).toReal),
          ENNReal.ofReal_toReal hx.ne,
          Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg (f x)) r),
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le, ofReal_norm]
      rw [lintegral_congr_ae hcongr, ← eLpNorm_one_eq_lintegral_enorm]
      calc eLpNorm (rho νT ν • g) 1 ν ≤ eLpNorm (rho νT ν) (conjExp p q) ν * eLpNorm g (p / q) ν :=
            eLpNorm_smul_le_mul_eLpNorm hgm hρm
        _ = eLpNorm (rho νT ν) (conjExp p q) ν * eLpNorm f p ν ^ r := by
            rw [hg, eLpNorm_norm_rpow f hr0, hpq]
    have hinv : (1 / r) = r⁻¹ := one_div r
    calc (∫⁻ x, ‖f x‖ₑ ^ r ∂νT) ^ (1 / r)
        ≤ (eLpNorm (rho νT ν) (conjExp p q) ν * eLpNorm f p ν ^ r) ^ (1 / r) :=
          ENNReal.rpow_le_rpow hkey (by positivity)
      _ = eLpNorm (rho νT ν) (conjExp p q) ν ^ (1 / r) * eLpNorm f p ν := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hinv,
            ENNReal.rpow_rpow_inv hr0.ne']

end Transfer

section ItemsTwoThree

open GFNBounds.Core.Family

variable {ν νT : Measure α} {θ : ProbabilityTheory.Kernel α α × (α → ℝ)} {f_init k : α → ℝ}

/-- **`equ:defect_equivalence`, lower half, for a kernel flow**:
`‖D‖_{L^p} ≤ ‖δf_init‖_{L^p} + ‖δf_term‖_{L^p}`. -/
theorem eLpNorm_defectFn_le_residual {p : ℝ≥0∞} (hp : 1 ≤ p) {f_term : α → ℝ}
    (hθ : AEStronglyMeasurable θ.2 ν) (hi : AEStronglyMeasurable f_init ν)
    (ht : AEStronglyMeasurable f_term ν) :
    eLpNorm (defectFn ν θ f_init f_term) p ν ≤ residual ν p θ f_init f_term := by
  have hI := aestronglyMeasurable_resInitFn (θ := θ) hθ hi ht
  have hT := aestronglyMeasurable_resTermFn (θ := θ) hθ hi ht
  calc eLpNorm (defectFn ν θ f_init f_term) p ν
      = eLpNorm (resTermFn ν θ f_init f_term - resInitFn ν θ f_init f_term) p ν := by
        congr 1; funext x; exact defectFn_eq_sub x
    _ ≤ eLpNorm (resTermFn ν θ f_init f_term) p ν + eLpNorm (resInitFn ν θ f_init f_term) p ν :=
        eLpNorm_sub_le hT hI hp
    _ = residual ν p θ f_init f_term := add_comm _ _

/-- The training loss of a member, `𝓛 = ‖e − k‖_{L^q(ν_T)}`, is at most the transfer constant
times its `L^p(ν_B)` residuals for the pair `(F_init, κ)`. -/
theorem loss_le_transferConst_mul_residual [SigmaFinite ν] [SigmaFinite νT] (hac : νT ≪ ν)
    {p q : ℝ≥0∞} (hq : 1 ≤ q) (hqp : q ≤ p) (hθ : AEStronglyMeasurable θ.2 ν)
    (hi : AEStronglyMeasurable f_init ν) (hk : AEStronglyMeasurable k ν) :
    eLpNorm (defectFn ν θ f_init k) q νT ≤ transferConst νT ν p q * residual ν p θ f_init k :=
  (eLpNorm_le_transferConst hac hq hqp (aestronglyMeasurable_defectFn hθ hi hk)).trans
    (mul_le_mul_right (eLpNorm_defectFn_le_residual (hq.trans hqp) hθ hi hk) _)

/-- **`theo:RL_CV_bound_full`, item (2)**: over a weakly `L^p`-universal family `Θ`
(`def:universality`, arbitrary `Θ`), with `1 ≤ q ≤ p`, `f_init` and `dκ/dν_B` in `L^p(ν_B)` of
equal mass (`IsAdmissiblePair`), `ν_T ≪ ν_B` and `dν_T/dν_B ∈ L^{q'}(ν_B)`,

  `inf_{(π⋆, f⋆_out) ∈ Θ} ‖e − k‖_{L^q(ν_T)} = 0`,

every `q ∈ [1, ∞]` included. The loss of a member is `‖defectFn ν θ f_init k‖_{L^q(ν_T)}`, since
`defectFn ν θ f_init k = e − k` (`defectFn_eq_eFn_sub`). -/
theorem inf_loss_eq_zero [IsFiniteMeasure ν] [IsFiniteMeasure νT] {p q : ℝ≥0∞} (hq : 1 ≤ q)
    (hqp : q ≤ p) {Θ : Set (ProbabilityTheory.Kernel α α × (α → ℝ))}
    (hΘ : Family.WeaklyUniversal ν p Θ) (hpair : Family.IsAdmissiblePair ν p f_init k) (hac : νT ≪ ν)
    (hρ : MemLp (rho νT ν) (conjExp p q) ν) :
    ⨅ θ ∈ Θ, eLpNorm (defectFn ν θ f_init k) q νT = 0 := by
  have hres := hΘ.2.2 f_init k hpair
  set K := transferConst νT ν p q with hKdef
  have hK : K ≠ ⊤ := transferConst_ne_top hρ
  rw [Family.iInf_eq_zero_iff] at hres ⊢
  intro ε hε
  set Kr := K.toReal
  have hKr : 0 ≤ Kr := ENNReal.toReal_nonneg
  obtain ⟨θ, hθΘ, hθ⟩ := hres (ε / (Kr + 1)) (by positivity)
  refine ⟨θ, hθΘ, ?_⟩
  have hle := loss_le_transferConst_mul_residual (θ := θ) hac hq hqp
    (hΘ.1 θ hθΘ).integrable.1 hpair.memLp_init.1 hpair.memLp_term.1
  calc eLpNorm (defectFn ν θ f_init k) q νT ≤ K * residual ν p θ f_init k := hle
    _ ≤ ENNReal.ofReal Kr * ENNReal.ofReal (ε / (Kr + 1)) := by
        rw [ENNReal.ofReal_toReal hK]; exact mul_le_mul_right hθ.le _
    _ = ENNReal.ofReal (Kr * (ε / (Kr + 1))) := (ENNReal.ofReal_mul hKr).symm
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **`theo:RL_CV_bound_full`, item (2) at `p = ∞`, no hypothesis on `dν_T/dν_B` beyond
`ν_T ≪ ν_B`**: the paper's
"`q' = 1` when `p = ∞`, only the domination being required when `q = p = ∞`". -/
theorem inf_loss_eq_zero_top [IsFiniteMeasure ν] [IsFiniteMeasure νT] {q : ℝ≥0∞} (hq : 1 ≤ q)
    {Θ : Set (ProbabilityTheory.Kernel α α × (α → ℝ))} (hΘ : Family.WeaklyUniversal ν ⊤ Θ)
    (hpair : Family.IsAdmissiblePair ν ⊤ f_init k) (hac : νT ≪ ν) :
    ⨅ θ ∈ Θ, eLpNorm (defectFn ν θ f_init k) q νT = 0 :=
  inf_loss_eq_zero hq le_top hΘ hpair hac (memLp_rho_top q)

/-! ## Item (3): the initial family -/

/-- **An initial family** (`theo:RL_CV_bound_full`(3)): non-zero initial flows `F_init ≪ ν_B`,
carried by their densities — a.e. non-negative, integrable (`F_init` finite), not a.e. zero. -/
def IsInitialFamily (ν : Measure α) (I : Set (α → ℝ)) : Prop :=
  ∀ f ∈ I, 0 ≤ᵐ[ν] f ∧ Integrable f ν ∧ ¬ (f =ᵐ[ν] 0)

/-- `Z(𝓘) = {F_init(𝒮) : F_init ∈ 𝓘}` (`equ:initial_masses`). -/
def massSet (ν : Measure α) (I : Set (α → ℝ)) : Set ℝ := (fun f => ∫ x, f x ∂ν) '' I

/-- `Z^p(𝓘) = {F_init(𝒮) : F_init ∈ 𝓘, f_init ∈ L^p(ν_B)}` (`equ:initial_masses`). -/
def massSetLp (ν : Measure α) (p : ℝ≥0∞) (I : Set (α → ℝ)) : Set ℝ :=
  (fun f => ∫ x, f x ∂ν) '' {f | f ∈ I ∧ MemLp f p ν}

/-- "The two conditions coinciding when every member of `𝓘` has its density in `L^p(ν_B)`". -/
theorem massSetLp_eq_massSet {p : ℝ≥0∞} {I : Set (α → ℝ)} (h : ∀ f ∈ I, MemLp f p ν) :
    massSetLp ν p I = massSet ν I := by
  unfold massSetLp massSet
  congr 1
  ext f
  exact ⟨fun hf => hf.1, fun hf => ⟨hf, h f hf⟩⟩

/-- **The mass floor in `[0, ∞]`**, for any member and any loss value (finite or not):
`|F_init(𝒮) − κ(𝒮)| ≤ C₀ ‖e − k‖_{L^q(ν_T)}`. -/
theorem ofReal_mass_gap_le [IsFiniteMeasure ν] {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hθ : IsGenerativeFlow ν θ) (hac : ν.bind ⇑θ.1 ≪ ν)
    (hi : Integrable f_init ν) (hk : Integrable k ν) :
    ENNReal.ofReal |(∫ x, f_init x ∂ν) - ∫ x, k x ∂ν|
      ≤ ENNReal.ofReal (holderConst ν M q.toReal) * eLpNorm (defectFn ν θ f_init k) q νT := by
  rw [← integral_defectFn hθ hac hi hk, ← Real.enorm_eq_ofReal_abs]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_enorm_le_holderConst hdom hq
      (aestronglyMeasurable_defectFn hθ.integrable.1 hi.1 hk.1))

/-- **`equ:joint_infimum`, left implication** (`theo:RL_CV_bound_full`, item (3)):
`t ∈ closure Z^p(𝓘) ⟹ inf_{𝓘 × Θ} 𝓛 = 0`, under the hypotheses of (2) on `Θ`, `dκ/dν_B` and
`ν_T`. -/
theorem joint_inf_eq_zero [IsFiniteMeasure ν] [IsFiniteMeasure νT] {p q : ℝ≥0∞} (hq : 1 ≤ q)
    (hqp : q ≤ p) {Θ : Set (ProbabilityTheory.Kernel α α × (α → ℝ))}
    (hΘ : Family.WeaklyUniversal ν p Θ) {I : Set (α → ℝ)} (hI : IsInitialFamily ν I)
    (hk0 : 0 ≤ᵐ[ν] k) (hkp : MemLp k p ν) (ht0 : 0 < ∫ x, k x ∂ν) (hac : νT ≪ ν)
    (hρ : MemLp (rho νT ν) (conjExp p q) ν)
    (hZ : (∫ x, k x ∂ν) ∈ closure (massSetLp ν p I)) :
    ⨅ f ∈ I, ⨅ θ ∈ Θ, eLpNorm (defectFn ν θ f k) q νT = 0 := by
  have hp : 1 ≤ p := hq.trans hqp
  set t := ∫ x, k x ∂ν with htdef
  set K := transferConst νT ν p q with hKdef
  have hK : K ≠ ⊤ := transferConst_ne_top hρ
  set Kr := K.toReal
  have hKr : 0 ≤ Kr := ENNReal.toReal_nonneg
  set a := (eLpNorm k p ν).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  rw [Family.iInf_eq_zero_iff]
  intro ε hε
  set η : ℝ := ε / (2 * (Kr + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨z, hzZ, hzt⟩ := Metric.mem_closure_iff.1 hZ (η * t / (a + 1)) (by positivity)
  obtain ⟨f, ⟨hfI, hfp⟩, rfl⟩ := hzZ
  set z := ∫ x, f x ∂ν with hzdef
  obtain ⟨hf0, hfint, -⟩ := hI f hfI
  have hz0 : 0 ≤ z := integral_nonneg_of_ae hf0
  -- the admissible pair `(F_init, (z/t) κ)`
  have hpair : Family.IsAdmissiblePair ν p f (fun x => z / t * k x) :=
    { nonneg_init := hf0
      nonneg_term := by
        filter_upwards [hk0] with x hx
        exact mul_nonneg (div_nonneg hz0 ht0.le) hx
      memLp_init := hfp
      memLp_term := hkp.const_mul _
      mass := by
        rw [integral_const_mul, ← htdef, div_mul_cancel₀ _ ht0.ne'] }
  have hres := (Family.iInf_eq_zero_iff _ _).1 (hΘ.2.2 f _ hpair) η hη0
  obtain ⟨θ, hθΘ, hθ⟩ := hres
  refine ⟨f, hfI, ?_⟩
  refine lt_of_le_of_lt (iInf₂_le θ hθΘ) ?_
  have hθm : AEStronglyMeasurable θ.2 ν := (hΘ.1 θ hθΘ).integrable.1
  have hkm : AEStronglyMeasurable (fun x => z / t * k x) ν := (hkp.const_mul _).1
  -- `D_κ = D_{(z/t)κ} + (z/t − 1) κ`
  have hsplit : defectFn ν θ f k
      = fun x => defectFn ν θ f (fun x => z / t * k x) x + (z / t - 1) * k x := by
    funext x; simp only [defectFn]; ring
  have hDp : eLpNorm (defectFn ν θ f k) p ν
      ≤ residual ν p θ f (fun x => z / t * k x) + ENNReal.ofReal (|z / t - 1| * a) := by
    rw [hsplit]
    refine (eLpNorm_add_le (aestronglyMeasurable_defectFn hθm hfp.1 hkm)
      (hkp.const_mul _).1 hp).trans (add_le_add
        (eLpNorm_defectFn_le_residual hp hθm hfp.1 hkm) (le_of_eq ?_))
    have : (fun x => (z / t - 1) * k x) = (z / t - 1) • k := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg _),
      ENNReal.ofReal_toReal hkp.eLpNorm_ne_top]
  have hgap : |z / t - 1| * a ≤ η := by
    have h1 : |z / t - 1| = |t - z| / t := by
      rw [show z / t - 1 = (z - t) / t by field_simp, abs_div, abs_of_pos ht0, abs_sub_comm]
    rw [h1]
    have h2 : |t - z| < η * t / (a + 1) := by rwa [Real.dist_eq] at hzt
    have h3 : |t - z| / t * a ≤ |t - z| / t * (a + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : |t - z| / t * (a + 1) ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ht0]
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < a + 1)).1 h2
      nlinarith
    linarith
  calc eLpNorm (defectFn ν θ f k) q νT
      ≤ K * eLpNorm (defectFn ν θ f k) p ν :=
        eLpNorm_le_transferConst hac hq hqp (aestronglyMeasurable_defectFn hθm hfp.1 hkp.1)
    _ ≤ ENNReal.ofReal Kr * (ENNReal.ofReal η + ENNReal.ofReal η) := by
        rw [ENNReal.ofReal_toReal hK]
        exact mul_le_mul_right (hDp.trans (add_le_add hθ.le (ENNReal.ofReal_le_ofReal hgap))) _
    _ = ENNReal.ofReal (Kr * (η + η)) := by
        rw [← ENNReal.ofReal_add hη0.le hη0.le, ← ENNReal.ofReal_mul hKr]
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε, hη]
        have : Kr * (ε / (2 * (Kr + 1)) + ε / (2 * (Kr + 1))) = Kr * ε / (Kr + 1) := by
          field_simp; ring
        rw [this, div_lt_iff₀ (by positivity)]
        nlinarith

/-- **`equ:joint_infimum`, right implication** (`theo:RL_CV_bound_full`, item (3)):
`inf_{𝓘 × Θ} 𝓛 = 0 ⟹ t ∈ closure Z(𝓘)`, by `equ:mass_floor` along a minimizing sequence. Uses
of `Θ` only that it is a family of generative flows with `ν_B π⋆ ≪ ν_B`, both part of
`WeaklyUniversal`. -/
theorem mem_closure_of_joint_inf [IsFiniteMeasure ν] {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT)
    {p q : ℝ≥0∞} (hq : 1 ≤ q) {Θ : Set (ProbabilityTheory.Kernel α α × (α → ℝ))}
    (hΘ : Family.WeaklyUniversal ν p Θ) {I : Set (α → ℝ)} (hI : IsInitialFamily ν I)
    (hk : Integrable k ν) (h0 : ⨅ f ∈ I, ⨅ θ ∈ Θ, eLpNorm (defectFn ν θ f k) q νT = 0) :
    (∫ x, k x ∂ν) ∈ closure (massSet ν I) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set C := holderConst ν M q.toReal
  have hC : 0 ≤ C := holderConst_nonneg _ _ _
  obtain ⟨f, hfI, hf⟩ := (Family.iInf_eq_zero_iff _ _).1 h0 (ε / (C + 1)) (by positivity)
  obtain ⟨θ, hθ⟩ := iInf_lt_iff.1 hf
  obtain ⟨hθΘ, hθ⟩ := iInf_lt_iff.1 hθ
  refine ⟨∫ x, f x ∂ν, ⟨f, hfI, rfl⟩, ?_⟩
  have hfl := ofReal_mass_gap_le (k := k) hdom hq (hΘ.1 θ hθΘ) (hΘ.2.1 θ hθΘ).1 (hI f hfI).2.1 hk
  have hlt : ENNReal.ofReal |(∫ x, f x ∂ν) - ∫ x, k x ∂ν| ≤ ENNReal.ofReal (C * (ε / (C + 1))) := by
    rw [ENNReal.ofReal_mul hC]
    exact hfl.trans (mul_le_mul_right hθ.le _)
  have hle := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlt
  rw [Real.dist_eq, abs_sub_comm]
  have : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- **`equ:joint_infimum` in full, item (3) of `theo:RL_CV_bound_full`**:

  `t ∈ closure Z^p(𝓘) ⟹ inf_{𝓘 × Θ} 𝓛 = 0 ⟹ t ∈ closure Z(𝓘)`,

under the hypotheses of (2) on `Θ`, `dκ/dν_B` and `ν_T`, and the standing domination
`ν_B ≤ M ν_T` of the theorem. With `massSetLp_eq_massSet`, the two conditions coincide when every
member of `𝓘` has its density in `L^p(ν_B)`. -/
theorem joint_infimum [IsFiniteMeasure ν] [IsFiniteMeasure νT] {M : ℝ≥0}
    (hdom : ν ≤ (M : ℝ≥0∞) • νT) {p q : ℝ≥0∞} (hq : 1 ≤ q) (hqp : q ≤ p)
    {Θ : Set (ProbabilityTheory.Kernel α α × (α → ℝ))} (hΘ : Family.WeaklyUniversal ν p Θ)
    {I : Set (α → ℝ)} (hI : IsInitialFamily ν I) (hk0 : 0 ≤ᵐ[ν] k) (hkp : MemLp k p ν)
    (ht0 : 0 < ∫ x, k x ∂ν) (hac : νT ≪ ν) (hρ : MemLp (rho νT ν) (conjExp p q) ν) :
    ((∫ x, k x ∂ν) ∈ closure (massSetLp ν p I) →
        ⨅ f ∈ I, ⨅ θ ∈ Θ, eLpNorm (defectFn ν θ f k) q νT = 0) ∧
      ((⨅ f ∈ I, ⨅ θ ∈ Θ, eLpNorm (defectFn ν θ f k) q νT = 0) →
        (∫ x, k x ∂ν) ∈ closure (massSet ν I)) := by
  have hk : Integrable k ν := hkp.integrable (hq.trans hqp)
  exact ⟨joint_inf_eq_zero hq hqp hΘ hI hk0 hkp ht0 hac hρ,
    mem_closure_of_joint_inf hdom hq hΘ hI hk⟩

end ItemsTwoThree

/-! ## Inhabitation (kb `0025`, `0027`): the hypotheses of item (2) are jointly satisfiable -/

section Witness

open GFNBounds.Core.Family

theorem memLp_rho_self (ν : Measure α) [IsFiniteMeasure ν] (r : ℝ≥0∞) :
    MemLp (rho ν ν) r ν := by
  refine (memLp_const (1 : ℝ)).ae_eq ?_
  filter_upwards [Measure.rnDeriv_self ν] with x hx
  simp [rho, hx]

/-- **`theo:RL_CV_bound_full`, item (2) inhabited**: on any probability space, training against `ν_T = ν_B` over the
family of the i.i.d. resampling policy `π⋆(x) = ν_B` with free outflow in `L^p` drives the stable
loss to `0` for every admissible pair, `1 ≤ q ≤ p < ∞`. -/
theorem inf_loss_eq_zero_const_kernel (ν : Measure α) [IsProbabilityMeasure ν] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hq : 1 ≤ q) (hqp : q ≤ p) {f_init k : α → ℝ}
    (hpair : Family.IsAdmissiblePair ν p f_init k) :
    ⨅ θ ∈ fixedPolicyFamily ν p (ProbabilityTheory.Kernel.const α ν),
      eLpNorm (defectFn ν θ f_init k) q ν = 0 :=
  inf_loss_eq_zero hq hqp (weaklyUniversal_const_kernel hp) hpair
    (Measure.AbsolutelyContinuous.refl ν) (memLp_rho_self ν _)

end Witness

end GFNBounds.Core.RLBound
