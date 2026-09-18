import GFNBounds.Core.ILBound
import GFNBounds.Core.FamilyUniversality
import GFNBounds.Core.NegativeControl

/-!
# The KL-weak-FM loss, closed: Pinsker, Hölder at every `q`, the family `Θ`, and the paper's `+∞`

**`theo:IL_CV_bound`** — statement `proofs.tex:271–287`, proof following it (line numbers drift,
kb `0036`; the label is the anchor).

**`theo:IL_CV_bound_body`** — `cv_stable.tex:42–51`, the body restatement.

> Let `(𝒮, ν_B)` be a measured Polish space with `ν_B` finite and let `F_init, κ` be probability
> distributions absolutely continuous with respect to `ν_B`, with densities `f_init, k` and with
> finite self-entropy `𝓗`. Let `q ∈ [1,+∞]` and assume `ν_B ∼ ν_T` with
> `dν_B/dν_T ∈ L^{q*}(ν_T)` and `b ≥ 1 + ‖dν_B/dν_T‖_{L^{q*}(ν_T)}`. For a generative flow
> `(π⋆, f⋆_out)` whose star inflow satisfies `F⋆_← ≪ ν_B`, define `𝓛^q_{KL-wFM}(π⋆, f⋆_out)` as in
> Equation `equ:weakFM` and use `F_term = κ̂ := (F_init + F⋆_← − F⋆_out)⁺` during inference. Then:
>
> * for every Markov kernel `π⋆` on `𝒮` and every `f⋆_out ∈ L¹₊(𝒮, ν_B)` with `F⋆_← ≪ ν_B`,
>   `𝓛^q_{KL-wFM}(π⋆, f⋆_out) ≥ 𝓗` and
>   `TV(s_τ ‖ κ) ≤ (1/√2)√(𝓛^q_{KL-wFM} − 𝓗) + min(1, ‖dν_B/dν_T‖_{L^{q*}(ν_T)}(𝓛^q_{KL-wFM} − 𝓗))`;
> * let `Θ` be a family of generative flows on `(𝒮, ν_B)` whose outflows lie in `L¹₊(𝒮, ν_B)` and
>   whose star inflows are dominated by `ν_B`. If `(π⋆, f⋆_out) ∈ Θ` and `ε ∈ [0,1)` satisfy
>   `F_init + F⋆_out π⋆ − F⋆_out ≥ (1−ε)κ` as measures, then
>   `𝓛^q_{KL-wFM}(π⋆, f⋆_out) ≤ 𝓗 + log(1/(1−ε))`. Consequently, if for every `ε > 0` some member
>   of `Θ` satisfies `equ:il_domination`, then `inf_Θ 𝓛^q_{KL-wFM} = 𝓗`, and if some member
>   satisfies `equ:il_domination` with `ε = 0` — equivalently, if `Θ` contains a flow satisfying
>   the flow-matching constraint `equ:FM_const` exactly for the pair `(F_init, κ)`, in particular
>   if `f_init, k ∈ L^p(ν_B)` for some `p ∈ [1,+∞]` and `Θ` is strongly `L^p`-universal in the
>   sense of Definition `def:universality` — the infimum is attained at that flow.

> (body) For a probability initial flow, a normalized target and a forward policy whose star
> inflow has a density, trained with the KL-weak-FM loss at any `q ∈ [1,+∞]` and an admissible
> weight `b ≥ 1 + ‖dν_B/dν_T‖_{L^{q*}(ν_T)}`, the loss is bounded below by the self-entropy `𝓗`
> of the target — with equality as soon as the family contains flows dominating the target up to
> a factor `1−ε` for every `ε > 0`, attained at exact matching, which strong `L^p`-universality
> supplies when the initial flow and the target have densities in `L^p(ν_B)` — and the sampling
> error is `O(√(𝓛^q − 𝓗))` as the loss approaches `𝓗`.

`Core/ILBound.lean` (graduated 2026-09-08) proved the chain of the proof with its inputs carried
as hypotheses (`hNC`, `hPins`, `htri`, `hHolder`, `he1`). This file proves Pinsker, Hölder at every
`q` and `E(𝒮) = F_init(𝒮)` on a general space, and discharges `hNC` and `htri` on a finite state
space.

## What is proved

| | |
|---|---|
| `pollard_ineq`, `pollard_two`, `pinsker_pointwise`, **`pinsker`** | **Pinsker's inequality** on densities, `tvD ≤ (1/√2)√klD` — absent from Mathlib v4.31.0; Pollard's proof, AM–GM in place of Cauchy–Schwarz |
| `lqNormE`, `wklfmLossE`, `lqNormE_eq_lqNormD`, `wklfmLossE_eq_wklfmLoss` | the loss `equ:weakFM` at every `q ∈ [1,+∞]` (`eLpNorm`), equal to `ILBound`'s on `L^q` at finite `q` |
| **`il_holderE`** | `equ:il_holder` at **every** conjugate pair, `q ∈ {1, ∞}` included |
| `LossFinite`, **`ilLoss`**, `crossEntropy_posPart_integrable` | the loss in `(−∞, +∞]` with the paper's `+∞`, and why `⊤` is its value off `LossFinite` |
| `InflowAC`, `eFlow`, `densityAction_of_inflowAC`, **`eFlow_integral`** | a generative flow `θ = (π⋆, f⋆_out)` (`Family.IsGenerativeFlow`) with `F⋆_← ≪ ν_B`; `E(𝒮) = F_init(𝒮)` **derived** |
| `crossEntropy_decomposition`, `lossE_sub_selfEntropy_ge`, `il_bullet_one_dens` | the chain at every `q`, Pinsker proved |
| **`il_first_bullet`** (flows), `il_first_bullet_dens` (densities) | **first bullet**: `𝓛 ≥ 𝓗` in `(−∞,+∞]`, and `equ:il_tv_explicit` where `𝓛 < ∞` |
| **`il_first_bullet_finite`** | the first bullet on a finite space with **`theo:negative_control` and the triangle inequality discharged** |
| `crossEntropy_integrable_of_domination`, **`il_member_le`** | `equ:il_domination` ⇒ `𝓛` finite and `≤ 𝓗 + log(1/(1−ε))` |
| **`il_iInf_eq`**, **`il_attained`**, **`il_attained_of_stronglyUniversal`** | **second bullet** over a family `Θ` of generative flows: `inf_Θ 𝓛 = 𝓗` in `(−∞,+∞]`, attained at `ε = 0`, and at a realizing member of a strongly `L^p`-universal `Θ` (`Family.StronglyUniversal`) |
| **`il_tv_le_sqrt`** | the body's `O(√(𝓛 − 𝓗))`: constant `1/√2 + ‖dν_B/dν_T‖_{L^{q*}}` once `𝓛 − 𝓗 ≤ 1` |
| `Example.ilLoss_ne_top` | inhabitation: a flow meeting every hypothesis of `il_first_bullet_finite` with finite loss |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` Polish, `ν_B` finite | ⚠ weakened: any measurable space, `[SigmaFinite ν]`; Polish and finiteness are used nowhere. Finite `V`, with `ν_B` of full support (`hν`), in `il_first_bullet_finite` alone |
| `F_init, κ ≪ ν_B` probabilities with densities `f_init, k` | ✓ `k` integrable, `≥ 0` a.e., `∫ k = 1`; `f_init` integrable, `∫ f_init = 1`. `f_init ≥ 0` is used only where `theo:negative_control` and `def:universality` consume it (`il_first_bullet_finite`, `il_attained_of_stronglyUniversal`) |
| `𝓗` finite | ✓ `hklog : Integrable (k log k)` |
| `q ∈ [1,+∞]` | ✓ `q qstar : ℝ≥0∞` with `[ENNReal.HolderConjugate qstar q]`, which forces `q ≥ 1`; `q = 1` and `q = ∞` included |
| `ν_B ∼ ν_T`, `dν_B/dν_T ∈ L^{q*}(ν_T)` | ✓ `hνT : ν ≪ νT` (both bullets), `hTν : νT ≪ ν` (second bullet, where it is used), `hr : MemLp (dν/dν_T) q* ν_T` |
| `b ≥ 1 + ‖dν_B/dν_T‖_{L^{q*}(ν_T)}` | ✓ `hb : 1 + rnNorm ν νT qstar ≤ b` |
| `(π⋆, f⋆_out)` generative flow, `π⋆` Markov, `f⋆_out ∈ L¹₊`, `F⋆_← ≪ ν_B` | ✓ `Family.IsGenerativeFlow ν θ` and `InflowAC ν θ` |
| inference at `F_term = κ̂ = E⁺` | ✓ `κ̂ = e⁺ ν`, `e = eFlow ν θ f_init`; finite: `NegativeControl.inference` |
| the loss `equ:weakFM`, valued in `(−∞,+∞]` | ✓ `ilLoss`, `⊤` off `LossFinite` — see SCOPE |
| `TV(s_τ ‖ κ)` | ⚠ general space: abstract `tv`, `tvNC` with `hNC`, `htri`; ✓ finite: `tvD ν (p/ν) k`, `p` the law of `s_τ` |
| `theo:negative_control` (in the proof) | ✗ **hypothesis `hNC`** on a general space; ✓ discharged on a finite space by `NegativeControl.negative_control_hNC` |
| Pinsker (in the proof) | ✓ `pinsker` |
| `Θ` family of generative flows, outflows `L¹₊`, inflows `≪ ν_B` | ✓ `Θ : Set (Kernel α α × (α → ℝ))`, `hΘ : ∀ θ ∈ Θ, IsGenerativeFlow ν θ ∧ InflowAC ν θ` |
| `equ:il_domination` "as measures", `ε ∈ [0,1)` | ✓ on `ν_B`-densities, `(1−ε)k ≤ e` a.e. — the same statement, `E` having density `e` by `InflowAC`; `ε < 1` suffices in `il_member_le` |
| "for every `ε > 0` some member satisfies" | ✓ `hdomΘ` for `ε ∈ (0,1)`, which is all the paper's `ε ∈ [0,1)` range allows |
| `ε = 0` ⟺ `equ:FM_const` | ✓ `Core.eq_of_domination_zero` (graduated) |
| "in particular if `f_init, k ∈ L^p` and `Θ` strongly `L^p`-universal" | ✓ `il_attained_of_stronglyUniversal`, `p ≥ 1`, `f_init ≥ 0` a.e. |
| body: `O(√(𝓛 − 𝓗))` | ✓ `il_tv_le_sqrt`, explicit constant |

## SCOPE (disclosed)

* **`theo:negative_control` is proved on a finite state space only** (`Core/NegativeControl.lean`,
  row B). On the paper's general space the first bullet's TV clause therefore carries it as the
  hypothesis `hNC : tvNC ≤ δF_init(𝒮)/κ̂(𝒮)`, with `htri` the triangle inequality for the
  abstract sampler; `il_first_bullet_finite` discharges both, with every other hypothesis the
  paper's. **The row closes in bucket `B`, not `A`**: the fully discharged form is narrowed to a
  finite `V`, and the general form needs the general measure layer for the sampler (kb `0006`,
  obstruction 2). Everything else — Pinsker, Hölder at `q ∈ {1,∞}`, `E(𝒮) = F_init(𝒮)`, the family
  `Θ`, strong universality, the `+∞` convention — is proved on a general measurable space.
* **The paper's `+∞` is `ilLoss = ⊤`.** `LossFinite` is `κ ≪ κ̂`, `k log e⁺ ∈ L¹(ν_B)` and
  `δf_init ∈ L^q(ν_T)`. Off it the paper's loss is `+∞`: `−k log e⁺ = +∞` on a `ν_B`-positive set
  when `κ ≪ κ̂` fails; `∫ k log e⁺ = −∞` when it is not integrable, its positive part being
  integrable (`crossEntropy_posPart_integrable`); the penalty is `+∞` when `δf_init ∉ L^q(ν_T)`,
  with `b ≥ 1`. That the paper's extended-real integral *equals* `ilLoss` is this argument, not a
  Lean theorem — the paper's `(−∞,+∞]`-valued integral has no Lean definition to compare with.
  Where the loss is `+∞` both bullets hold trivially, which is what the `EReal` statements say.
* **Measures are carried by `ν_B`-densities**, as in `Core/StableBound.lean` and
  `Core/FamilyUniversality.lean`: `κ = k ν_B`, `E = e ν_B` with
  `e = f_init + densityAction π⋆ f⋆_out − f⋆_out` (`InflowAC` makes `densityAction` the whole
  density of `F⋆_←`), `κ̂ = e⁺ ν_B`.
* **The sampler on a general space is abstract** (`tv`, `tvNC`), as in `ILBound`; on a finite
  space it is `Core.Sampling`'s absorbing chain, its law the limit of its time-`n` marginals, and
  `NegativeControl`'s `hν : ∀ x, 0 < ν.real {x}` (full support) is inherited.
* **No `sorry`.**

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core.ILBoundFull

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## Pinsker's inequality on densities -/

/-- `u(x) = (x+1) log x − 2(x−1)` is monotone on `(0,∞)`: `u' = log x + 1/x − 1 ≥ 0`. -/
theorem padeAux_mono :
    MonotoneOn (fun x : ℝ => (x + 1) * Real.log x - 2 * (x - 1)) (Ioi 0) := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => (x + 1) * Real.log x - 2 * (x - 1))
      (Real.log x + (x + 1) * x⁻¹ - 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 := ((hasDerivAt_id' x).add_const 1).mul (Real.hasDerivAt_log hx0)
    have h2 := ((hasDerivAt_id' x).sub_const 1).const_mul 2
    refine (h1.sub h2).congr_deriv ?_
    ring
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hd x hx).deriv]
    have hx0 : (0 : ℝ) < x := hx
    have hl := Real.one_sub_inv_le_log_of_pos hx0
    have : (x + 1) * x⁻¹ = 1 + x⁻¹ := by field_simp
    rw [this]
    linarith

/-- The sign of `u(x) = (x+1) log x − 2(x−1)` is that of `x − 1`. -/
theorem padeAux_sign {x : ℝ} (hx : 0 < x) :
    0 ≤ (x - 1) * ((x + 1) * Real.log x - 2 * (x - 1)) := by
  have hm := padeAux_mono
  have h1 : (1 + 1) * Real.log 1 - 2 * ((1 : ℝ) - 1) = 0 := by simp
  rcases le_total 1 x with h | h
  · have := hm (show (1 : ℝ) ∈ Ioi 0 by norm_num) hx h
    simp only at this
    rw [h1] at this
    exact mul_nonneg (by linarith) this
  · have := hm hx (show (1 : ℝ) ∈ Ioi 0 by norm_num) h
    simp only at this
    rw [h1] at this
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) this

/-- The function `h(x) = (2x+4)(x log x − x + 1) − 3(x−1)²`, whose derivative is `4u(x)`. -/
noncomputable def pollardAux (x : ℝ) : ℝ :=
  (2 * x + 4) * (x * Real.log x - x + 1) - 3 * (x - 1) ^ 2

theorem pollardAux_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt pollardAux (4 * ((x + 1) * Real.log x - 2 * (x - 1))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxl : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log x + 1) x := by
    refine ((hasDerivAt_id' x).mul (Real.hasDerivAt_log hx0)).congr_deriv ?_
    field_simp
  have h1 := (((hasDerivAt_id' x).const_mul 2).add_const 4).mul
    ((hxl.sub (hasDerivAt_id' x)).add_const 1)
  have h2 := (((hasDerivAt_id' x).sub_const 1).pow 2).const_mul 3
  have h3 := h1.sub h2
  unfold pollardAux
  refine h3.congr_deriv ?_
  simp only [Pi.sub_apply]
  push_cast
  ring

theorem continuous_pollardAux : Continuous pollardAux := by
  unfold pollardAux
  have := Real.continuous_mul_log
  fun_prop

/-- **The pointwise inequality behind Pinsker** (the form of Pollard's proof):
`3(x−1)² ≤ (2x+4)(x log x − x + 1)` for `x ≥ 0`. -/
theorem pollard_ineq {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 ≤ (2 * x + 4) * (x * Real.log x - x + 1) := by
  suffices h : 0 ≤ pollardAux x by unfold pollardAux at h; linarith
  have h1 : pollardAux 1 = 0 := by simp [pollardAux]
  rcases le_total 1 x with h | h
  · have hmono : MonotoneOn pollardAux (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
        continuous_pollardAux.continuousOn ?_ ?_
      · intro y hy
        rw [interior_Ici] at hy
        exact (pollardAux_hasDerivAt (by linarith [mem_Ioi.1 hy])).differentiableAt
          |>.differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy1 : 1 < y := hy
        rw [(pollardAux_hasDerivAt (by linarith)).deriv]
        have := padeAux_sign (x := y) (by linarith)
        have hpos : 0 < y - 1 := by linarith
        have : 0 ≤ (y + 1) * Real.log y - 2 * (y - 1) := by
          by_contra hc
          have hc' := not_le.mp hc
          nlinarith
        linarith
    have := hmono (show (1 : ℝ) ∈ Ici 1 from mem_Ici.2 le_rfl) (show x ∈ Ici 1 from h) h
    linarith
  · have hanti : AntitoneOn pollardAux (Icc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
        continuous_pollardAux.continuousOn ?_ ?_
      · intro y hy
        rw [interior_Icc] at hy
        exact (pollardAux_hasDerivAt hy.1).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(pollardAux_hasDerivAt hy.1).deriv]
        have := padeAux_sign (x := y) hy.1
        have hneg : y - 1 < 0 := by linarith [hy.2]
        have : (y + 1) * Real.log y - 2 * (y - 1) ≤ 0 := by
          by_contra hc
          have hc' := not_le.mp hc
          nlinarith
        linarith
    have := hanti (show x ∈ Icc 0 1 from ⟨hx, h⟩) (show (1 : ℝ) ∈ Icc 0 1 by norm_num) h
    linarith

/-- Pollard's inequality at `x = k/g`, multiplied through by `g²`:
`3(k−g)² ≤ (2k+4g)(k log(k/g) − k + g)` for `k, g ≥ 0` with `g = 0 ⇒ k = 0`. -/
theorem pollard_two {k g : ℝ} (hk : 0 ≤ k) (hg : 0 ≤ g) (hac : g = 0 → k = 0) :
    3 * (k - g) ^ 2 ≤ (2 * k + 4 * g) * (k * Real.log (k / g) - k + g) := by
  rcases eq_or_lt_of_le hg with h0 | h0
  · have hk' := hac h0.symm
    rw [← h0, hk']
    simp
  · have h := pollard_ineq (x := k / g) (div_nonneg hk hg)
    have hgne : g ≠ 0 := ne_of_gt h0
    have key : 3 * (k - g) ^ 2 = g ^ 2 * (3 * (k / g - 1) ^ 2) := by
      field_simp
    have key2 : (2 * k + 4 * g) * (k * Real.log (k / g) - k + g)
        = g ^ 2 * ((2 * (k / g) + 4) * (k / g * Real.log (k / g) - k / g + 1)) := by
      field_simp
    rw [key, key2]
    exact mul_le_mul_of_nonneg_left h (sq_nonneg g)

/-- The pointwise form integrated in `pinsker`: for every `t > 0`,
`|k − g| ≤ c₁(t) k + c₂(t) g + (1/(2t)) k log(k/g)`, `c₁ = (2t/3 − 1/t)/2`, `c₂ = (4t/3 + 1/t)/2`.
It is `|k − g| ≤ (t a + φ/t)/2` with `a = (2k+4g)/3`, `φ = k log(k/g) − k + g`, i.e. AM–GM on
`(k − g)² ≤ aφ`. -/
theorem pinsker_pointwise {k g t : ℝ} (hk : 0 ≤ k) (hg : 0 ≤ g) (hac : g = 0 → k = 0)
    (ht : 0 < t) :
    |k - g| ≤ (2 * t / 3 - 1 / t) / 2 * k + (4 * t / 3 + 1 / t) / 2 * g
      + 1 / (2 * t) * (k * Real.log (k / g)) := by
  set a : ℝ := (2 * k + 4 * g) / 3 with ha
  set φ : ℝ := k * Real.log (k / g) - k + g with hφ
  have hφ0 : 0 ≤ φ := by
    have := GFNBounds.Core.sub_le_mul_log_div hk hg hac
    rw [hφ]; linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hsq : (k - g) ^ 2 ≤ a * φ := by
    have := pollard_two hk hg hac
    rw [ha, hφ]; nlinarith
  have hrhs : (2 * t / 3 - 1 / t) / 2 * k + (4 * t / 3 + 1 / t) / 2 * g
      + 1 / (2 * t) * (k * Real.log (k / g)) = (t * a + φ / t) / 2 := by
    rw [ha, hφ]; field_simp; ring
  rw [hrhs]
  have hB : 0 ≤ (t * a + φ / t) / 2 := by positivity
  refine abs_le_of_sq_le_sq ?_ hB
  have htne : t ≠ 0 := ne_of_gt ht
  have hamgm : 4 * (a * φ) ≤ (t * a + φ / t) ^ 2 := by
    have h0 : 0 ≤ (t * a - φ / t) ^ 2 := sq_nonneg _
    have hprod : (t * a) * (φ / t) = a * φ := by field_simp
    nlinarith
  nlinarith

/-- **Pinsker's inequality, on densities** (the step of `proofs.tex` in the proof of
`theo:IL_CV_bound` that cites it): for probability densities `k, g` against `ν` with
`k ≪ g` (`hac`) and `k log(k/g)` integrable,

  `tvD ν k g ≤ (1/√2) √(klD ν k g)` .

Mathlib v4.31.0 has no Pinsker inequality; this is Pollard's proof — the pointwise
`3(x−1)² ≤ (2x+4)(x log x − x + 1)` (`pollard_ineq`) and AM–GM in place of Cauchy–Schwarz. -/
theorem pinsker {ν : Measure α} {k g : α → ℝ}
    (hk : Integrable k ν) (hg : Integrable g ν) (hk0 : 0 ≤ᵐ[ν] k) (hg0 : 0 ≤ᵐ[ν] g)
    (hac : ∀ᵐ x ∂ν, g x = 0 → k x = 0)
    (hint : Integrable (fun x => k x * Real.log (k x / g x)) ν)
    (hk1 : ∫ x, k x ∂ν = 1) (hg1 : ∫ x, g x ∂ν = 1) :
    GFNBounds.Core.tvD ν k g
      ≤ 1 / Real.sqrt 2 * Real.sqrt (GFNBounds.Core.klD ν k g) := by
  set K := GFNBounds.Core.klD ν k g with hK
  have hK0 : 0 ≤ K := GFNBounds.Core.klD_nonneg hk hg hint hk0 hg0 hac (by rw [hk1, hg1])
  -- the integrated AM–GM bound
  have hbound : ∀ t : ℝ, 0 < t → ∫ x, |k x - g x| ∂ν ≤ t + K / (2 * t) := by
    intro t ht
    have hR : Integrable (fun x => (2 * t / 3 - 1 / t) / 2 * k x + (4 * t / 3 + 1 / t) / 2 * g x
        + 1 / (2 * t) * (k x * Real.log (k x / g x))) ν :=
      ((hk.const_mul _).add (hg.const_mul _)).add (hint.const_mul _)
    have hmono := integral_mono_ae (hk.sub hg).abs hR (by
      filter_upwards [hk0, hg0, hac] with x h1 h2 h3
      exact pinsker_pointwise h1 h2 h3 ht)
    have hval : ∫ x, ((2 * t / 3 - 1 / t) / 2 * k x + (4 * t / 3 + 1 / t) / 2 * g x
        + 1 / (2 * t) * (k x * Real.log (k x / g x))) ∂ν
        = (2 * t / 3 - 1 / t) / 2 * 1 + (4 * t / 3 + 1 / t) / 2 * 1 + 1 / (2 * t) * K := by
      rw [integral_add (f := fun x => (2 * t / 3 - 1 / t) / 2 * k x + (4 * t / 3 + 1 / t) / 2 * g x)
          ((hk.const_mul _).add (hg.const_mul _)) (hint.const_mul _),
        integral_add (hk.const_mul _) (hg.const_mul _), integral_const_mul, integral_const_mul,
        integral_const_mul, hk1, hg1]
      rfl
    rw [hval] at hmono
    have habs : ∫ x, |k x - g x| ∂ν = ∫ x, |(k - g) x| ∂ν := rfl
    rw [habs]
    have htne : t ≠ 0 := ne_of_gt ht
    have : (2 * t / 3 - 1 / t) / 2 * 1 + (4 * t / 3 + 1 / t) / 2 * 1 + 1 / (2 * t) * K
        = t + K / (2 * t) := by field_simp; ring
    linarith
  unfold GFNBounds.Core.tvD
  rcases eq_or_lt_of_le hK0 with h0 | hpos
  · -- `K = 0`: the `L¹` distance is below every `t > 0`
    rw [← h0, Real.sqrt_zero, mul_zero]
    have hle : ∫ x, |k x - g x| ∂ν ≤ 0 := by
      refine le_of_forall_pos_le_add fun t ht => ?_
      have := hbound t ht
      rw [← h0, zero_div, add_zero] at this
      linarith
    linarith
  · set t : ℝ := 1 / Real.sqrt 2 * Real.sqrt K with htdef
    have ht : 0 < t := by positivity
    have ht2 : t ^ 2 = K / 2 := by
      rw [htdef, mul_pow, Real.sq_sqrt hK0, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hKt : K / (2 * t) = t := by
      have htne : t ≠ 0 := ne_of_gt ht
      field_simp
      nlinarith
    have := hbound t ht
    rw [hKt] at this
    linarith

/-! ## The loss at every `q ∈ [1, +∞]`, and Hölder at every conjugate pair -/

/-- The `L^q(ν_T)` norm of a density at an extended exponent `q ∈ [1, +∞]`, as a real. It is
`Core.lqNormD` for a real exponent on `L^q` (`lqNormE_eq_lqNormD`) and the essential supremum at
`q = ∞`. -/
noncomputable def lqNormE (νT : Measure α) (q : ℝ≥0∞) (f : α → ℝ) : ℝ := (eLpNorm f q νT).toReal

theorem lqNormE_nonneg (νT : Measure α) (q : ℝ≥0∞) (f : α → ℝ) : 0 ≤ lqNormE νT q f :=
  ENNReal.toReal_nonneg

/-- At a finite positive exponent and on `L^q`, `lqNormE` is `ILBound`'s `lqNormD`. -/
theorem lqNormE_eq_lqNormD {νT : Measure α} {q : ℝ} (hq : 0 < q) {f : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) νT) :
    lqNormE νT (ENNReal.ofReal q) f = GFNBounds.Core.lqNormD νT q f := by
  rw [lqNormE, hf.eLpNorm_eq_integral_rpow_norm (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hq.le, GFNBounds.Core.lqNormD,
    one_div]
  rfl

/-- **The KL-weak-FM loss `equ:weakFM` at an extended exponent `q ∈ [1, +∞]`**, in densities:
`b‖δf_init‖_{L^q(ν_T)} − ∫ k log f̂_term dν_B`, `δf_init = e⁻`, `f̂_term = e⁺`. Real-valued; the
paper's `+∞` is `ilLoss`. -/
noncomputable def wklfmLossE (ν νT : Measure α) (q : ℝ≥0∞) (b : ℝ) (k e : α → ℝ) : ℝ :=
  b * lqNormE νT q (fun x => max (-e x) 0) - ∫ x, k x * Real.log (max (e x) 0) ∂ν

/-- At a finite exponent on `L^q`, `wklfmLossE` is `ILBound`'s `wklfmLoss`. -/
theorem wklfmLossE_eq_wklfmLoss {ν νT : Measure α} {q : ℝ} (hq : 0 < q) {b : ℝ} {k e : α → ℝ}
    (hf : MemLp (fun x => max (-e x) 0) (ENNReal.ofReal q) νT) :
    wklfmLossE ν νT (ENNReal.ofReal q) b k e = GFNBounds.Core.wklfmLoss ν νT q b k e := by
  rw [wklfmLossE, lqNormE_eq_lqNormD hq hf, GFNBounds.Core.wklfmLoss]

/-- **`equ:il_holder` at every conjugate pair `(q*, q)`, the endpoints `q ∈ {1, ∞}` included**:
`ν ≪ ν_T` gives `∫ f dν = ∫ (dν/dν_T) f dν_T ≤ ‖dν/dν_T‖_{L^{q*}(ν_T)} ‖f‖_{L^q(ν_T)}`. Mathlib's
`eLpNorm_smul_le_mul_eLpNorm` takes any `HolderTriple`, which is what removes `ILBound.il_holder`'s
restriction to `1 < q < ∞`. -/
theorem il_holderE {ν νT : Measure α} [SigmaFinite ν] [SigmaFinite νT] {f : α → ℝ}
    {q qstar : ℝ≥0∞} [ENNReal.HolderConjugate qstar q] (hac : ν ≪ νT)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT) (hf : MemLp f q νT) :
    ∫ x, f x ∂ν ≤ lqNormE νT qstar (fun x => (ν.rnDeriv νT x).toReal) * lqNormE νT q f := by
  set r : α → ℝ := fun x => (ν.rnDeriv νT x).toReal with hrdef
  have hchange : ∫ x, f x ∂ν = ∫ x, r x * f x ∂νT :=
    (integral_toReal_rnDeriv_mul (f := f) hac).symm
  have hH : eLpNorm (r • f) 1 νT ≤ eLpNorm r qstar νT * eLpNorm f q νT :=
    eLpNorm_smul_le_mul_eLpNorm hf.1 hr.1
  have hfin : eLpNorm r qstar νT * eLpNorm f q νT ≠ ⊤ :=
    ENNReal.mul_ne_top hr.eLpNorm_ne_top hf.eLpNorm_ne_top
  have h1 : ‖∫ x, r x * f x ∂νT‖ₑ ≤ eLpNorm (r • f) 1 νT := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_le_lintegral_enorm _
  have h2 : ‖∫ x, r x * f x ∂νT‖ₑ ≤ eLpNorm r qstar νT * eLpNorm f q νT := h1.trans hH
  have h3 : ‖∫ x, r x * f x ∂νT‖ ≤ (eLpNorm r qstar νT * eLpNorm f q νT).toReal := by
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono hfin h2
  rw [hchange, lqNormE, lqNormE, ← ENNReal.toReal_mul]
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ h3)

/-! ## The chain of `proofs.tex`, for any penalty -/

section Chain

variable {ν νT : Measure α} {k e : α → ℝ}

/-- The cross-entropy decomposition, penalty-free: `−∫ k log e⁺ = KL(κ ‖ κ̂/ẑ) − log ẑ + 𝓗`.
It is `ILBound.wklfmLoss_decomposition` at `b = 0`. -/
theorem crossEntropy_decomposition {zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0) (hzh0 : 0 < zhat) :
    -∫ x, k x * Real.log (max (e x) 0) ∂ν
      = GFNBounds.Core.klD ν k (fun x => max (e x) 0 / zhat) - Real.log zhat
        + GFNBounds.Core.selfEntropy ν k := by
  have h := GFNBounds.Core.wklfmLoss_decomposition (νT := ν) (q := 1) (b := 0)
    hk hk1 hk0 hklog helog hac hzh0
  simp only [GFNBounds.Core.wklfmLoss, zero_mul, zero_sub, add_zero] at h
  linarith

/-- **`proofs.tex`, `eq:wFM_strong_bound` composed with `eq:lp_delta`, at any `q ∈ [1,∞]`**:
`KL(κ ‖ κ̂/κ̂(𝒮)) + ‖δf_init‖_{L^q(ν_T)} ≤ 𝓛^q − 𝓗`, and `KL ≥ 0`. -/
theorem lossE_sub_selfEntropy_ge {q : ℝ≥0∞} {b N δ zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (he : Integrable e ν) (he1 : ∫ x, e x ∂ν = 1)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ) (hb : 1 + N ≤ b)
    (hHolder : δ ≤ N * lqNormE νT q (fun x => max (-e x) 0)) :
    0 ≤ GFNBounds.Core.klD ν k (fun x => max (e x) 0 / zhat) ∧
    GFNBounds.Core.klD ν k (fun x => max (e x) 0 / zhat) + lqNormE νT q (fun x => max (-e x) 0)
      ≤ wklfmLossE ν νT q b k e - GFNBounds.Core.selfEntropy ν k := by
  have hδ0 : 0 ≤ δ := hδ ▸ integral_nonneg fun _ => le_max_right _ _
  have hzh0 : 0 < zhat := by rw [hzh]; linarith
  have hdec := crossEntropy_decomposition hk hk1 hk0 hklog helog hac hzh0
  have hpen := GFNBounds.Core.penalty_ge (b := b) (N := N)
    (D := lqNormE νT q (fun x => max (-e x) 0)) (δ := δ) hδ0 (lqNormE_nonneg _ _ _) hb hHolder
  have hkl := GFNBounds.Core.klD_normalized_nonneg hk hk1 hk0 he he1 hklog helog hac hδ hzh
  refine ⟨hkl, ?_⟩
  rw [wklfmLossE]
  rw [hzh] at hdec ⊢
  linarith

/-- **The first bullet of `theo:IL_CV_bound` on densities, at any `q ∈ [1,∞]`, Pinsker proved**:
`𝓛^q ≥ 𝓗` and `equ:il_tv_explicit`. The two inputs left as hypotheses are `hNC`
(`theo:negative_control`, proved on a finite space only — `il_first_bullet_finite`) and `htri`
(the triangle inequality for the abstract sampler; `Core.tvD_triangle` when `s_τ` has a density).
Pinsker is `pinsker`; the Hölder estimate `hHolder` is `il_holderE`. -/
theorem il_bullet_one_dens {q : ℝ≥0∞} {b N δ zhat tv tvNC : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (he : Integrable e ν) (he1 : ∫ x, e x ∂ν = 1)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ) (hN0 : 0 ≤ N) (hb : 1 + N ≤ b)
    (hHolder : δ ≤ N * lqNormE νT q (fun x => max (-e x) 0))
    (hNC : tvNC ≤ δ / zhat)
    (htri : tv ≤ tvNC + GFNBounds.Core.tvD ν k (fun x => max (e x) 0 / zhat)) :
    GFNBounds.Core.selfEntropy ν k ≤ wklfmLossE ν νT q b k e ∧
    tv ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLossE ν νT q b k e - GFNBounds.Core.selfEntropy ν k)
        + min 1 (N * (wklfmLossE ν νT q b k e - GFNBounds.Core.selfEntropy ν k)) := by
  set L : ℝ := wklfmLossE ν νT q b k e - GFNBounds.Core.selfEntropy ν k with hL
  obtain ⟨hkl0, hmain⟩ := lossE_sub_selfEntropy_ge (νT := νT) (q := q) hk hk1 hk0 he he1 hklog
    helog hac hδ hzh hb hHolder
  have hD0 := lqNormE_nonneg νT q (fun x => max (-e x) 0)
  have hδ0 : 0 ≤ δ := hδ ▸ integral_nonneg fun _ => le_max_right _ _
  have hzh0 : 0 < zhat := by rw [hzh]; linarith
  refine ⟨by linarith, ?_⟩
  -- the negative-control term
  have hNCmin : tvNC ≤ min 1 δ := by
    refine hNC.trans ?_
    rw [hzh]
    exact GFNBounds.Core.negMass_ratio_le_min hδ0
  have hδL : δ ≤ N * L := hHolder.trans (mul_le_mul_of_nonneg_left (by linarith) hN0)
  have hmin : min 1 δ ≤ min 1 (N * L) := min_le_min le_rfl hδL
  -- the Pinsker term, proved
  have hmass : ∫ x, max (e x) 0 ∂ν = zhat := by
    rw [GFNBounds.Core.il_mass_identity he he1, hzh, hδ]
  have hPins := pinsker (ν := ν) (k := k) (g := fun x => max (e x) 0 / zhat) hk
    (he.pos_part.div_const _) hk0
    (Filter.Eventually.of_forall fun x => div_nonneg (le_max_right _ _) hzh0.le)
    (by filter_upwards [hac] with x hx hx0
        exact hx (by simpa [div_eq_zero_iff, ne_of_gt hzh0] using hx0))
    (GFNBounds.Core.klD_integrable hk hklog helog hk0 hac hzh0) hk1
    (by rw [integral_div, hmass, div_self (ne_of_gt hzh0)])
  have hsqrt : Real.sqrt (GFNBounds.Core.klD ν k (fun x => max (e x) 0 / zhat)) ≤ Real.sqrt L :=
    Real.sqrt_le_sqrt (by linarith)
  have hc : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  have hPins' := hPins.trans (mul_le_mul_of_nonneg_left hsqrt hc)
  linarith

end Chain

/-! ## The paper's `+∞`, made explicit -/

section Extended

variable {ν νT : Measure α} {k e : α → ℝ}

/-- **The loss is finite.** The paper's `𝓛^q` takes values in `(−∞, +∞]`, and it is finite exactly
when the three conditions hold: `κ ≪ κ̂` (else `−k log e⁺ = +∞` on a `ν_B`-positive set),
integrability of `k log e⁺` (its positive part always is, `crossEntropy_posPart_integrable`, so
failure means `∫ k log e⁺ = −∞`), and `δf_init ∈ L^q(ν_T)` (else the penalty is `+∞`, `b ≥ 1`). -/
structure LossFinite (ν νT : Measure α) (q : ℝ≥0∞) (k e : α → ℝ) : Prop where
  ac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0
  ce : Integrable (fun x => k x * Real.log (max (e x) 0)) ν
  pen : MemLp (fun x => max (-e x) 0) q νT

open Classical in
/-- **The KL-weak-FM loss with the paper's `+∞`**: `wklfmLossE` where the loss is finite, `⊤`
elsewhere. -/
noncomputable def ilLoss (ν νT : Measure α) (q : ℝ≥0∞) (b : ℝ) (k e : α → ℝ) : EReal :=
  if LossFinite ν νT q k e then ((wklfmLossE ν νT q b k e : ℝ) : EReal) else ⊤

theorem ilLoss_of_finite {q : ℝ≥0∞} {b : ℝ} (h : LossFinite ν νT q k e) :
    ilLoss ν νT q b k e = ((wklfmLossE ν νT q b k e : ℝ) : EReal) := by
  rw [ilLoss, if_pos h]

theorem finite_of_ilLoss_ne_top {q : ℝ≥0∞} {b : ℝ} (h : ilLoss ν νT q b k e ≠ ⊤) :
    LossFinite ν νT q k e := by
  by_contra hc
  exact h (by rw [ilLoss, if_neg hc])

/-- **Why `⊤` is the paper's value when `k log e⁺` is not integrable**: under `κ ≪ κ̂` its
positive part is integrable, dominated by `|k log k| + |e|`, so non-integrability means the
cross-entropy integral is `−∞` and the loss `+∞`. -/
theorem crossEntropy_posPart_integrable (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k)
    (he : Integrable e ν) (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0) :
    Integrable (fun x => max (k x * Real.log (max (e x) 0)) 0) ν := by
  have hmeas : AEStronglyMeasurable (fun x => k x * Real.log (max (e x) 0)) ν :=
    (hk.1.aemeasurable.mul (Real.measurable_log.comp_aemeasurable
      (he.1.aemeasurable.max aemeasurable_const))).aestronglyMeasurable
  refine Integrable.mono' (hklog.abs.add he.abs)
    (continuous_id.max continuous_const |>.comp_aestronglyMeasurable hmeas) ?_
  filter_upwards [hk0, hac] with x hx hxa
  have hx' : (0 : ℝ) ≤ k x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  simp only [Pi.add_apply]
  refine max_le ?_ (by positivity)
  rcases eq_or_lt_of_le hx' with h0 | h0
  · rw [← h0]; simp only [zero_mul]; positivity
  · have hE : 0 < max (e x) 0 := lt_of_le_of_ne (le_max_right _ _)
      (fun h => absurd (hxa h.symm) (ne_of_gt h0))
    have hlog := Real.log_le_sub_one_of_pos (div_pos hE h0)
    rw [Real.log_div (ne_of_gt hE) (ne_of_gt h0)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hx'
    have hsimp : k x * (max (e x) 0 / k x - 1) = max (e x) 0 - k x := by field_simp
    rw [hsimp] at hmul
    have h1 : max (e x) 0 ≤ |e x| := max_le (le_abs_self _) (abs_nonneg _)
    have h2 : k x * Real.log (k x) ≤ |k x * Real.log (k x)| := le_abs_self _
    nlinarith

end Extended

/-! ## Generative flows: `E = F_init + F⋆_← − F⋆_out` and its mass -/

section Flow

open GFNBounds.Core.Family

variable {ν νT : Measure α}

/-- The paper's standing hypothesis on a flow, `F⋆_← = F⋆_out π⋆ ≪ ν_B`. -/
def InflowAC (ν : Measure α) (θ : ProbabilityTheory.Kernel α α × (α → ℝ)) : Prop :=
  (ν.withDensity (fun x => ENNReal.ofReal (θ.2 x))).bind ⇑θ.1 ≪ ν

/-- The density `e = f_init + f⋆_← − f⋆_out` of `E = F_init + F⋆_← − F⋆_out`: `Family.defectFn`
with `F_term = 0`. -/
noncomputable def eFlow (ν : Measure α) (θ : ProbabilityTheory.Kernel α α × (α → ℝ))
    (f_init : α → ℝ) : α → ℝ :=
  defectFn ν θ f_init (fun _ => 0)

/-- `ν π⋆ ≪ ν` (the boundedness clause of `def:universality`) gives the flow's `InflowAC`. -/
theorem inflowAC_of_bind_ac {θ : ProbabilityTheory.Kernel α α × (α → ℝ)}
    (h : ν.bind ⇑θ.1 ≪ ν) : InflowAC ν θ :=
  bind_withDensity_ac θ.1 h _

/-- **Step 0 of the proof**: `F⋆_←(𝒮) = F⋆_out(𝒮)`, stochasticity of `π⋆` and `F⋆_← ≪ ν_B`. -/
theorem densityAction_of_inflowAC [SigmaFinite ν] {θ : ProbabilityTheory.Kernel α α × (α → ℝ)}
    (hθ : IsGenerativeFlow ν θ) (hin : InflowAC ν θ) :
    Integrable (densityAction θ.1 ν θ.2) ν ∧
      ∫ x, densityAction θ.1 ν θ.2 x ∂ν = ∫ x, θ.2 x ∂ν := by
  haveI := hθ.markov
  have hz : (fun y => ENNReal.ofReal (-θ.2 y)) = 0 := by
    funext y
    exact ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 (hθ.nonneg y))
  have hneg : bindDensity θ.1 ν (fun y => ENNReal.ofReal (-θ.2 y)) =ᵐ[ν] 0 := by
    rw [hz]; exact bindDensity_zero θ.1 ν
  have hlint : ∫⁻ x, bindDensity θ.1 ν (fun y => ENNReal.ofReal (θ.2 y)) x ∂ν
      = ∫⁻ x, ENNReal.ofReal (θ.2 x) ∂ν := by
    calc ∫⁻ x, bindDensity θ.1 ν (fun y => ENNReal.ofReal (θ.2 y)) x ∂ν
        = (ν.withDensity (bindDensity θ.1 ν (fun y => ENNReal.ofReal (θ.2 y)))) Set.univ := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = ((ν.withDensity (fun y => ENNReal.ofReal (θ.2 y))).bind ⇑θ.1) Set.univ := by
          rw [bindDensity, Measure.withDensity_rnDeriv_eq _ _ hin]
      _ = ∫⁻ x, ENNReal.ofReal (θ.2 x) ∂ν := bind_withDensity_univ θ.1 ν _
  have hfin : ∫⁻ x, bindDensity θ.1 ν (fun y => ENNReal.ofReal (θ.2 y)) x ∂ν ≠ ⊤ := by
    rw [hlint]; exact lintegral_ofReal_ne_top hθ.integrable
  have hI : Integrable (fun x => (bindDensity θ.1 ν (fun y => ENNReal.ofReal (θ.2 y)) x).toReal)
      ν := integrable_toReal_of_lintegral_ne_top (measurable_bindDensity _ _ _).aemeasurable hfin
  have hcongr : densityAction θ.1 ν θ.2
      =ᵐ[ν] fun x => (bindDensity θ.1 ν (fun y => ENNReal.ofReal (θ.2 y)) x).toReal := by
    filter_upwards [hneg] with x hx
    simp only [densityAction, hx, Pi.zero_apply, ENNReal.toReal_zero, sub_zero]
  refine ⟨hI.congr hcongr.symm, ?_⟩
  rw [integral_congr_ae hcongr, integral_toReal (measurable_bindDensity _ _ _).aemeasurable
    (ae_lt_top (measurable_bindDensity _ _ _) hfin), hlint,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hθ.nonneg) hθ.integrable.1]

/-- **`E(𝒮) = F_init(𝒮)`** (`proofs.tex`, first lines of the proof of `theo:IL_CV_bound`),
derived, where `ILBound` assumed it as `he1`. -/
theorem eFlow_integral [SigmaFinite ν] {θ : ProbabilityTheory.Kernel α α × (α → ℝ)}
    {f_init : α → ℝ} (hθ : IsGenerativeFlow ν θ) (hin : InflowAC ν θ)
    (hfi : Integrable f_init ν) :
    Integrable (eFlow ν θ f_init) ν ∧ ∫ x, eFlow ν θ f_init x ∂ν = ∫ x, f_init x ∂ν := by
  obtain ⟨hP, hPint⟩ := densityAction_of_inflowAC hθ hin
  have hI : Integrable (fun x => f_init x + densityAction θ.1 ν θ.2 x - θ.2 x) ν :=
    (hfi.add hP).sub hθ.integrable
  have heq : eFlow ν θ f_init = fun x => f_init x + densityAction θ.1 ν θ.2 x - θ.2 x := by
    funext x; simp only [eFlow, defectFn, sub_zero]
  rw [heq]
  refine ⟨hI, ?_⟩
  show ∫ x, (f_init x + densityAction θ.1 ν θ.2 x - θ.2 x) ∂ν = _
  rw [integral_sub (f := fun x => f_init x + densityAction θ.1 ν θ.2 x) (hfi.add hP)
    hθ.integrable, integral_add hfi hP, hPint]
  ring

end Flow

/-! ## `theo:IL_CV_bound`, first bullet, for a generative flow -/

section BulletOne

open GFNBounds.Core.Family

variable {ν νT : Measure α}

/-- The paper's constant `‖dν_B/dν_T‖_{L^{q*}(ν_T)}`. -/
noncomputable def rnNorm (ν νT : Measure α) (qstar : ℝ≥0∞) : ℝ :=
  lqNormE νT qstar (fun x => (ν.rnDeriv νT x).toReal)

/-- **`theo:IL_CV_bound`, first bullet, on densities**: `il_first_bullet` for any density `e` of
`E = F_init + F⋆_← − F⋆_out` with `E(𝒮) = 1`. `il_first_bullet` supplies `e` and `E(𝒮) = 1` from a
generative flow; `il_first_bullet_finite` from a finite flow. -/
theorem il_first_bullet_dens [SigmaFinite ν] [SigmaFinite νT] {q qstar : ℝ≥0∞}
    [ENNReal.HolderConjugate qstar q] (hνT : ν ≪ νT)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT) {b : ℝ}
    (hb : 1 + rnNorm ν νT qstar ≤ b)
    {k e : α → ℝ} (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (he : Integrable e ν) (he1 : ∫ x, e x ∂ν = 1) :
    ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) ≤ ilLoss ν νT q b k e ∧
    ∀ tv tvNC : ℝ, ilLoss ν νT q b k e ≠ ⊤ →
      tvNC ≤ (∫ x, max (-e x) 0 ∂ν) / ∫ x, max (e x) 0 ∂ν →
      tv ≤ tvNC + GFNBounds.Core.tvD ν k (fun x => max (e x) 0 / ∫ x, max (e x) 0 ∂ν) →
      tv ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLossE ν νT q b k e - GFNBounds.Core.selfEntropy ν k)
          + min 1 (rnNorm ν νT qstar * (wklfmLossE ν νT q b k e
              - GFNBounds.Core.selfEntropy ν k)) := by
  have hN0 : 0 ≤ rnNorm ν νT qstar := lqNormE_nonneg _ _ _
  have hmass := GFNBounds.Core.il_mass_identity he he1
  have key : ∀ _ : LossFinite ν νT q k e,
      GFNBounds.Core.selfEntropy ν k ≤ wklfmLossE ν νT q b k e ∧
      ∀ tv tvNC : ℝ,
      tvNC ≤ (∫ x, max (-e x) 0 ∂ν) / ∫ x, max (e x) 0 ∂ν →
      tv ≤ tvNC + GFNBounds.Core.tvD ν k (fun x => max (e x) 0 / ∫ x, max (e x) 0 ∂ν) →
      tv ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLossE ν νT q b k e - GFNBounds.Core.selfEntropy ν k)
          + min 1 (rnNorm ν νT qstar * (wklfmLossE ν νT q b k e
              - GFNBounds.Core.selfEntropy ν k)) := by
    intro hfin
    have hHolder := il_holderE (f := fun x => max (-e x) 0) hνT hr hfin.pen
    have h0 := il_bullet_one_dens (νT := νT) (q := q) (b := b) (N := rnNorm ν νT qstar)
      (tv := 0) (tvNC := 0) hk hk1 hk0 he he1 hklog hfin.ce hfin.ac rfl hmass hN0 hb hHolder
      (by positivity) (by rw [zero_add]; exact GFNBounds.Core.tvD_nonneg _ _ _)
    refine ⟨h0.1, fun tv tvNC hNC htri => ?_⟩
    exact (il_bullet_one_dens (νT := νT) (q := q) (b := b) (N := rnNorm ν νT qstar)
      hk hk1 hk0 he he1 hklog hfin.ce hfin.ac rfl hmass hN0 hb hHolder hNC htri).2
  refine ⟨?_, fun tv tvNC hne hNC htri => (key (finite_of_ilLoss_ne_top hne)).2 tv tvNC hNC htri⟩
  by_cases hfin : LossFinite ν νT q k e
  · rw [ilLoss_of_finite hfin]
    exact EReal.coe_le_coe_iff.2 (key hfin).1
  · rw [ilLoss, if_neg hfin]
    exact le_top

/-- **`theo:IL_CV_bound`, first bullet**, for a generative flow `θ = (π⋆, f⋆_out)` on any
measurable space, at any `q ∈ [1, +∞]` (with `q*` its conjugate):

* `𝓛^q_{KL-wFM}(θ) ≥ 𝓗`, in `(−∞, +∞]` with the paper's `+∞` (`ilLoss`), unconditionally;
* where the loss is finite, `equ:il_tv_explicit`
  `TV(s_τ ‖ κ) ≤ (1/√2)√(𝓛 − 𝓗) + min(1, ‖dν_B/dν_T‖_{L^{q*}(ν_T)}(𝓛 − 𝓗))`.

Pinsker (`pinsker`), Hölder (`il_holderE`) and `E(𝒮) = F_init(𝒮)` (`eFlow_integral`) are proved.
**Two inputs stay hypotheses on this general space**: `hNC`, `theo:negative_control` in the form
`TV(s_τ ‖ κ̂/κ̂(𝒮)) ≤ δF_init(𝒮)/κ̂(𝒮)`, proved in `Core.NegativeControl` on a finite space only,
and `htri`, the triangle inequality for the abstract sampler (`Core.tvD_triangle` whenever `s_τ`
has a `ν_B`-density); `il_first_bullet_finite` discharges both. -/
theorem il_first_bullet [SigmaFinite ν] [SigmaFinite νT] {q qstar : ℝ≥0∞}
    [ENNReal.HolderConjugate qstar q] (hνT : ν ≪ νT)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT) {b : ℝ}
    (hb : 1 + rnNorm ν νT qstar ≤ b)
    {k f_init : α → ℝ} (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (hfi : Integrable f_init ν) (hfi1 : ∫ x, f_init x ∂ν = 1)
    {θ : ProbabilityTheory.Kernel α α × (α → ℝ)} (hθ : IsGenerativeFlow ν θ)
    (hin : InflowAC ν θ) :
    ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) ≤ ilLoss ν νT q b k (eFlow ν θ f_init) ∧
    ∀ tv tvNC : ℝ, ilLoss ν νT q b k (eFlow ν θ f_init) ≠ ⊤ →
      tvNC ≤ (∫ x, max (-eFlow ν θ f_init x) 0 ∂ν) / ∫ x, max (eFlow ν θ f_init x) 0 ∂ν →
      tv ≤ tvNC + GFNBounds.Core.tvD ν k
        (fun x => max (eFlow ν θ f_init x) 0 / ∫ x, max (eFlow ν θ f_init x) 0 ∂ν) →
      tv ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLossE ν νT q b k (eFlow ν θ f_init)
              - GFNBounds.Core.selfEntropy ν k)
          + min 1 (rnNorm ν νT qstar * (wklfmLossE ν νT q b k (eFlow ν θ f_init)
              - GFNBounds.Core.selfEntropy ν k)) := by
  obtain ⟨he, he1'⟩ := eFlow_integral hθ hin hfi
  exact il_first_bullet_dens hνT hr hb hk hk1 hk0 hklog he (by rw [he1', hfi1])

/-- **The body's `O(√(𝓛 − 𝓗))`** (`theo:IL_CV_bound_body`): where `𝓛 − 𝓗 ≤ 1`, the right side of
`equ:il_tv_explicit` is at most `(1/√2 + ‖dν_B/dν_T‖_{L^{q*}(ν_T)}) √(𝓛 − 𝓗)`. -/
theorem il_tv_le_sqrt {L H N tv : ℝ} (hN0 : 0 ≤ N) (hLH : 0 ≤ L - H) (hsmall : L - H ≤ 1)
    (h : tv ≤ 1 / Real.sqrt 2 * Real.sqrt (L - H) + min 1 (N * (L - H))) :
    tv ≤ (1 / Real.sqrt 2 + N) * Real.sqrt (L - H) := by
  have hs : L - H ≤ Real.sqrt (L - H) := by
    have h1 : Real.sqrt (L - H) ≤ 1 := Real.sqrt_le_one.mpr hsmall
    have h2 := Real.sq_sqrt hLH
    nlinarith [Real.sqrt_nonneg (L - H)]
  have hmin : min 1 (N * (L - H)) ≤ N * Real.sqrt (L - H) :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hs hN0)
  linarith

end BulletOne

/-! ## `theo:IL_CV_bound`, second bullet, over a family `Θ` -/

section BulletTwo

open GFNBounds.Core.Family

variable {ν νT : Measure α}

/-- Under `equ:il_domination` the cross-entropy integrand is integrable: sandwiched between
`k log((1−ε)k)` and `k log k + e⁺ − k`. -/
theorem crossEntropy_integrable_of_domination {k e : α → ℝ} {ε : ℝ}
    (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k) (he : Integrable e ν)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν) (hε1 : ε < 1)
    (hdom : ∀ᵐ x ∂ν, (1 - ε) * k x ≤ e x) :
    Integrable (fun x => k x * Real.log (max (e x) 0)) ν := by
  have hε' : (0 : ℝ) < 1 - ε := by linarith
  have hmeas : AEStronglyMeasurable (fun x => k x * Real.log (max (e x) 0)) ν :=
    (hk.1.aemeasurable.mul (Real.measurable_log.comp_aemeasurable
      (he.1.aemeasurable.max aemeasurable_const))).aestronglyMeasurable
  have hbound : Integrable (fun x => |k x| * |Real.log (1 - ε)| + 2 * |k x * Real.log (k x)|
      + |e x| + |k x|) ν :=
    (((hk.abs.mul_const _).add (hklog.abs.const_mul 2)).add he.abs).add hk.abs
  refine Integrable.mono' hbound hmeas ?_
  filter_upwards [hk0, hdom] with x hx hd
  have hx' : (0 : ℝ) ≤ k x := hx
  rw [Real.norm_eq_abs]
  rcases eq_or_lt_of_le hx' with h0 | h0
  · rw [← h0]; simp only [zero_mul, abs_zero]; positivity
  · have hpos : 0 < (1 - ε) * k x := mul_pos hε' h0
    have hE : (1 - ε) * k x ≤ max (e x) 0 := le_max_of_le_left hd
    have hEpos : 0 < max (e x) 0 := lt_of_lt_of_le hpos hE
    -- lower bound
    have hlow : k x * Real.log (1 - ε) + k x * Real.log (k x)
        ≤ k x * Real.log (max (e x) 0) := by
      rw [← mul_add, ← Real.log_mul (ne_of_gt hε') (ne_of_gt h0)]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hE) hx'
    -- upper bound
    have hlog := Real.log_le_sub_one_of_pos (div_pos hEpos h0)
    rw [Real.log_div (ne_of_gt hEpos) (ne_of_gt h0)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hx'
    have hsimp : k x * (max (e x) 0 / k x - 1) = max (e x) 0 - k x := by field_simp
    rw [hsimp] at hmul
    have h1 : max (e x) 0 ≤ |e x| := max_le (le_abs_self _) (abs_nonneg _)
    have h2 := abs_le.mp (le_refl |k x * Real.log (k x)|)
    have h3 : k x * Real.log (1 - ε) ≥ -(|k x| * |Real.log (1 - ε)|) := by
      rw [← abs_mul]; exact neg_abs_le _
    have hk_abs : |k x| = k x := abs_of_nonneg hx'
    rw [abs_le]
    constructor
    · nlinarith [abs_nonneg (e x), abs_nonneg (k x * Real.log (k x)),
        neg_abs_le (k x * Real.log (k x))]
    · nlinarith [abs_nonneg (e x), abs_nonneg (k x * Real.log (k x)),
        le_abs_self (k x * Real.log (k x)), abs_nonneg (k x),
        abs_nonneg (Real.log (1 - ε)), mul_nonneg (abs_nonneg (k x)) (abs_nonneg (Real.log (1 - ε)))]

/-- **`equ:il_domination` bounds the loss**, for a member of `Θ` (`proofs.tex`, second half of the
proof of `theo:IL_CV_bound`): if `F_init + F⋆_out π⋆ − F⋆_out ≥ (1−ε)κ`, read on `ν_B`-densities,
then the loss is finite and `𝓛^q ≤ 𝓗 + log(1/(1−ε))`, at every `q`. `hTν : ν_T ≪ ν_B` is the half
of `ν_B ∼ ν_T` that moves `e⁻ = 0` from `ν_B` to `ν_T`. -/
theorem il_member_le [SigmaFinite ν] (hTν : νT ≪ ν) {q : ℝ≥0∞} {b ε : ℝ} (hε1 : ε < 1)
    {k f_init : α → ℝ} (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν) (hfi : Integrable f_init ν)
    {θ : ProbabilityTheory.Kernel α α × (α → ℝ)} (hθ : IsGenerativeFlow ν θ)
    (hin : InflowAC ν θ) (hdom : ∀ᵐ x ∂ν, (1 - ε) * k x ≤ eFlow ν θ f_init x) :
    LossFinite ν νT q k (eFlow ν θ f_init) ∧
      ilLoss ν νT q b k (eFlow ν θ f_init)
        ≤ ((GFNBounds.Core.selfEntropy ν k + Real.log (1 / (1 - ε)) : ℝ) : EReal) := by
  set e := eFlow ν θ f_init with he_def
  have he : Integrable e ν := (eFlow_integral hθ hin hfi).1
  have hε' : (0 : ℝ) < 1 - ε := by linarith
  have hneg : ∀ᵐ x ∂ν, max (-e x) 0 = 0 := by
    filter_upwards [hk0, hdom] with x hx hd
    have hx' : (0 : ℝ) ≤ k x := hx
    exact max_eq_right (neg_nonpos.mpr (le_trans (mul_nonneg hε'.le hx') hd))
  have hnegT : (fun x => max (-e x) 0) =ᵐ[νT] 0 := hTν hneg
  have helog := crossEntropy_integrable_of_domination hk hk0 he hklog hε1 hdom
  have hfin : LossFinite ν νT q k e :=
    { ac := by
        filter_upwards [hk0, hdom] with x hx hd hx0
        have hx' : (0 : ℝ) ≤ k x := hx
        have : e x ≤ 0 := by
          by_contra hc
          have := max_eq_left (le_of_lt (not_le.mp hc))
          rw [this] at hx0
          exact absurd hx0 (ne_of_gt (not_le.mp hc))
        nlinarith
      ce := helog
      pen := (memLp_congr_ae hnegT).2 MemLp.zero }
  refine ⟨hfin, ?_⟩
  rw [ilLoss_of_finite hfin]
  refine EReal.coe_le_coe_iff.2 ?_
  have hpenE : lqNormE νT q (fun x => max (-e x) 0) = 0 := by
    rw [lqNormE, eLpNorm_congr_ae hnegT, eLpNorm_zero, ENNReal.toReal_zero]
  have hpenD : GFNBounds.Core.lqNormD νT 1 (fun x => max (-e x) 0) = 0 := by
    have hz : ∫ x, |max (-e x) 0| ^ (1 : ℝ) ∂νT = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hnegT] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
    rw [GFNBounds.Core.lqNormD, hz, Real.zero_rpow (by norm_num)]
  have h := GFNBounds.Core.loss_le_of_domination (q := 1) (b := b) hk hk1 hk0 hklog helog
    one_pos hTν hε1 hdom
  rw [GFNBounds.Core.wklfmLoss, hpenD] at h
  rw [wklfmLossE, hpenE]
  linarith

/-- An `EReal` bounded above by `a + η` for every `η > 0` is at most `a`. -/
theorem ereal_le_of_forall_pos {x : EReal} {a : ℝ}
    (h : ∀ η : ℝ, 0 < η → x ≤ ((a + η : ℝ) : EReal)) : x ≤ (a : EReal) := by
  induction x using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd (h 1 one_pos) (not_le.2 (EReal.coe_lt_top _))
  | coe c =>
    refine EReal.coe_le_coe_iff.2 (le_of_forall_pos_le_add fun η hη => ?_)
    exact EReal.coe_le_coe_iff.1 (h η hη)

/-- **`theo:IL_CV_bound`, second bullet, the infimum**: if every member of `Θ` is a generative flow
with `F⋆_← ≪ ν_B`, and for every `ε ∈ (0,1)` some member satisfies `equ:il_domination`, then

  `inf_{θ ∈ Θ} 𝓛^q_{KL-wFM}(θ) = 𝓗` ,

the infimum taken in `(−∞, +∞]` with the paper's `+∞`. -/
theorem il_iInf_eq [SigmaFinite ν] [SigmaFinite νT] {q qstar : ℝ≥0∞}
    [ENNReal.HolderConjugate qstar q] (hνT : ν ≪ νT) (hTν : νT ≪ ν)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT) {b : ℝ}
    (hb : 1 + rnNorm ν νT qstar ≤ b)
    {k f_init : α → ℝ} (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (hfi : Integrable f_init ν) (hfi1 : ∫ x, f_init x ∂ν = 1)
    {Θ : Set (ProbabilityTheory.Kernel α α × (α → ℝ))}
    (hΘ : ∀ θ ∈ Θ, IsGenerativeFlow ν θ ∧ InflowAC ν θ)
    (hdomΘ : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ θ ∈ Θ, ∀ᵐ x ∂ν, (1 - ε) * k x ≤ eFlow ν θ f_init x) :
    ⨅ θ ∈ Θ, ilLoss ν νT q b k (eFlow ν θ f_init)
      = ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_iInf₂ fun θ hθ =>
    (il_first_bullet (q := q) hνT hr hb hk hk1 hk0 hklog hfi hfi1 (hΘ θ hθ).1 (hΘ θ hθ).2).1)
  refine ereal_le_of_forall_pos fun η hη => ?_
  set ε : ℝ := 1 - Real.exp (-η) with hε
  have hexp1 : Real.exp (-η) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hexp0 : 0 < Real.exp (-η) := Real.exp_pos _
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε < 1 := by rw [hε]; linarith
  obtain ⟨θ, hθΘ, hdom⟩ := hdomΘ ε hε0 hε1
  have hval : Real.log (1 / (1 - ε)) = η := by
    have h1 : 1 - ε = Real.exp (-η) := by rw [hε]; ring
    rw [h1, one_div, ← Real.exp_neg, Real.log_exp]
    ring
  have hle := (il_member_le (q := q) (b := b) hTν hε1 hk hk1 hk0 hklog hfi (hΘ θ hθΘ).1
    (hΘ θ hθΘ).2 hdom).2
  rw [hval] at hle
  exact (iInf₂_le θ hθΘ).trans hle

/-- **`theo:IL_CV_bound`, second bullet, attainment at `ε = 0`**: a member with `F_init + F⋆_out π⋆
− F⋆_out ≥ κ` has `𝓛^q = 𝓗`, which is then the infimum over `Θ`, attained. The equivalence of
`ε = 0` domination with `equ:FM_const` is `Core.eq_of_domination_zero` (`e = k` a.e.). -/
theorem il_attained [SigmaFinite ν] [SigmaFinite νT] {q qstar : ℝ≥0∞}
    [ENNReal.HolderConjugate qstar q] (hνT : ν ≪ νT) (hTν : νT ≪ ν)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT) {b : ℝ}
    (hb : 1 + rnNorm ν νT qstar ≤ b)
    {k f_init : α → ℝ} (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (hfi : Integrable f_init ν) (hfi1 : ∫ x, f_init x ∂ν = 1)
    {Θ : Set (ProbabilityTheory.Kernel α α × (α → ℝ))}
    (hΘ : ∀ θ ∈ Θ, IsGenerativeFlow ν θ ∧ InflowAC ν θ)
    {θ₀ : ProbabilityTheory.Kernel α α × (α → ℝ)} (hθ₀ : θ₀ ∈ Θ)
    (hdom : ∀ᵐ x ∂ν, k x ≤ eFlow ν θ₀ f_init x) :
    ilLoss ν νT q b k (eFlow ν θ₀ f_init) = ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) ∧
    ⨅ θ ∈ Θ, ilLoss ν νT q b k (eFlow ν θ f_init)
      = ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) := by
  have hdom' : ∀ᵐ x ∂ν, (1 - (0 : ℝ)) * k x ≤ eFlow ν θ₀ f_init x := by
    filter_upwards [hdom] with x hx; linarith
  have hup := (il_member_le (q := q) (b := b) hTν (by norm_num : (0 : ℝ) < 1) hk hk1 hk0 hklog
    hfi (hΘ θ₀ hθ₀).1 (hΘ θ₀ hθ₀).2 hdom').2
  simp only [sub_zero, div_one, Real.log_one, add_zero] at hup
  have hlow := (il_first_bullet (q := q) hνT hr hb hk hk1 hk0 hklog hfi hfi1 (hΘ θ₀ hθ₀).1
    (hΘ θ₀ hθ₀).2).1
  have h0 : ilLoss ν νT q b k (eFlow ν θ₀ f_init) = ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) :=
    le_antisymm hup hlow
  refine ⟨h0, le_antisymm ((iInf₂_le θ₀ hθ₀).trans h0.le) (le_iInf₂ fun θ hθ =>
    (il_first_bullet (q := q) hνT hr hb hk hk1 hk0 hklog hfi hfi1 (hΘ θ hθ).1 (hΘ θ hθ).2).1)⟩

/-- **`theo:IL_CV_bound`, second bullet, "in particular"**: if `f_init, k ∈ L^p(ν_B)`, `p ≥ 1`,
and `Θ` is strongly `L^p`-universal (`Family.StronglyUniversal`, `def:universality` for an
arbitrary family), some member realizes the pair `(F_init, κ)` exactly, so the infimum `𝓗` is
attained there. Members of a strongly universal family are generative flows with `ν π⋆ ≪ ν`, hence
`F⋆_← ≪ ν_B`: the standing hypothesis `hΘ` is not needed. -/
theorem il_attained_of_stronglyUniversal [SigmaFinite ν] [SigmaFinite νT] {q qstar : ℝ≥0∞}
    [ENNReal.HolderConjugate qstar q] (hνT : ν ≪ νT) (hTν : νT ≪ ν)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT) {b : ℝ}
    (hb : 1 + rnNorm ν νT qstar ≤ b)
    {k f_init : α → ℝ} (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (hfi1 : ∫ x, f_init x ∂ν = 1) (hfi0 : 0 ≤ᵐ[ν] f_init)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hfiLp : MemLp f_init p ν) (hkLp : MemLp k p ν)
    (hk : Integrable k ν) (hfi : Integrable f_init ν)
    {Θ : Set (ProbabilityTheory.Kernel α α × (α → ℝ))} (hU : GFNBounds.Core.Family.StronglyUniversal ν p Θ) :
    ∃ θ₀ ∈ Θ, ilLoss ν νT q b k (eFlow ν θ₀ f_init) = ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) ∧
    ⨅ θ ∈ Θ, ilLoss ν νT q b k (eFlow ν θ f_init)
      = ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) := by
  obtain ⟨hfam, hbdd, hreal⟩ := hU
  have hΘ : ∀ θ ∈ Θ, IsGenerativeFlow ν θ ∧ InflowAC ν θ := fun θ hθ =>
    ⟨hfam θ hθ, inflowAC_of_bind_ac (hbdd θ hθ).1⟩
  have hpair : GFNBounds.Core.Family.IsAdmissiblePair ν p f_init k :=
    ⟨hfi0, hk0, hfiLp, hkLp, by rw [hfi1, hk1]⟩
  obtain ⟨θ₀, hθ₀, hres⟩ := hreal f_init k hpair
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  obtain ⟨hI, hT⟩ := ae_eq_zero_of_residual_eq_zero hp0 (hfam θ₀ hθ₀).integrable.1
    hfiLp.1 hkLp.1 hres
  have hdom : ∀ᵐ x ∂ν, k x ≤ eFlow ν θ₀ f_init x := by
    filter_upwards [hI, hT] with x h1 h2
    have hD := defectFn_eq_sub (ν := ν) (θ := θ₀) (f_init := f_init) (f_term := k) x
    simp only [Pi.zero_apply] at h1 h2
    rw [h1, h2, sub_zero] at hD
    have : eFlow ν θ₀ f_init x = defectFn ν θ₀ f_init k x + k x := by
      simp only [eFlow, defectFn]; ring
    rw [this, hD, zero_add]
  exact ⟨θ₀, hθ₀, il_attained hνT hTν hr hb hk hk1 hk0 hklog hfi hfi1 hΘ hθ₀ hdom⟩

end BulletTwo

/-! ## On a finite state space: nothing external left -/

section Finite

open GFNBounds.Core.Sampling GFNBounds.Core.NegativeControl Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **`theo:IL_CV_bound`, first bullet, on a finite state space, with `theo:negative_control` and
the triangle inequality discharged**. `F` is a finite generative flow (`P⋆` stochastic,
`F⋆_out ≥ 0`), `F_init` a probability, `ν_B = ν` charges every atom, `κ = k·ν` a probability.
Inference is at `F_term = κ̂ := E⁺` (`NegativeControl.inference`); its sample `s_τ` has a law `p`
(the limit of `P(τ ≤ n, s_τ = ·)`), and

* `𝓛^q ≥ 𝓗` in `(−∞, +∞]`;
* where the loss is finite, `TV(s_τ ‖ κ) ≤ (1/√2)√(𝓛 − 𝓗) + min(1, ‖dν_B/dν_T‖_{L^{q*}}(𝓛 − 𝓗))`,
  `TV` in the ½-convention between the law `p` (density `p/ν`) and `κ`.

Every hypothesis is the paper's except two narrowings: the state space is finite, and `ν_B`
charges every atom (`hν`, inherited from `NegativeControl.negative_control_hNC`);
`[IsFiniteMeasure νT]` is σ-finiteness on a finite space. -/
theorem il_first_bullet_finite (ν νT : Measure V) [IsFiniteMeasure ν] [IsFiniteMeasure νT]
    (hν : ∀ x, 0 < ν.real {x}) (hνT : ν ≪ νT) {q qstar : ℝ≥0∞}
    [ENNReal.HolderConjugate qstar q] {b : ℝ} (hb : 1 + rnNorm ν νT qstar ≤ b)
    (F : FlowData V) (hfi : ∀ x, 0 ≤ F.finit x) (hfo : ∀ x, 0 ≤ F.fout x)
    (hP0 : ∀ x y, 0 ≤ F.P x y) (hP1 : ∀ x, ∑ y, F.P x y = 1) (hfi1 : ∑ x, F.finit x = 1)
    {k : V → ℝ} (hk0 : ∀ x, 0 ≤ k x) (hk1 : ∫ x, k x ∂ν = 1) :
    ((GFNBounds.Core.selfEntropy ν k : ℝ) : EReal) ≤ ilLoss ν νT q b k (eDens ν F) ∧
    ∃ p : V → ℝ,
      (∀ y, Tendsto (fun n => (inference F).law n (y, true)) atTop (𝓝 (p y))) ∧
      ∑ y, p y = 1 ∧
      (ilLoss ν νT q b k (eDens ν F) ≠ ⊤ →
        GFNBounds.Core.tvD ν (fun y => p y / ν.real {y}) k
          ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLossE ν νT q b k (eDens ν F)
              - GFNBounds.Core.selfEntropy ν k)
            + min 1 (rnNorm ν νT qstar * (wklfmLossE ν νT q b k (eDens ν F)
              - GFNBounds.Core.selfEntropy ν k))) := by
  have hinit : F.finit ≠ 0 := by
    intro h
    rw [h] at hfi1
    simp at hfi1
  obtain ⟨p, hp, hp1, hz, -, hNC⟩ := negative_control_hNC ν hν F hfi hfo hP0 hP1 hinit
  have hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) qstar νT := MemLp.of_discrete
  have hmain := il_first_bullet_dens (q := q) hνT hr hb (k := k) (e := eDens ν F)
    Integrable.of_finite hk1 (Filter.Eventually.of_forall hk0) Integrable.of_finite
    Integrable.of_finite (by rw [hz, hfi1])
  refine ⟨hmain.1, p, hp, hp1, fun hne => ?_⟩
  have htri := GFNBounds.Core.tvD_triangle (ν := ν) (f₁ := fun y => p y / ν.real {y})
    (f₂ := fun x => max (eDens ν F x) 0 / ∫ x, max (eDens ν F x) 0 ∂ν) (f₃ := k)
    Integrable.of_finite Integrable.of_finite
  rw [GFNBounds.Core.tvD_comm ν (fun x => max (eDens ν F x) 0 / ∫ x, max (eDens ν F x) 0 ∂ν) k]
    at htri
  exact hmain.2 _ _ hne hNC htri

end Finite

/-! ## Inhabitation: the finite branch is not empty -/

namespace Example

open GFNBounds.Core.Sampling GFNBounds.Core.NegativeControl

/-- One state, `F_init = 1`, no outflow, `P⋆ = 1`: `E = F_init = κ`. -/
noncomputable def flow : FlowData Unit where
  finit := fun _ => 1
  fterm := fun _ => 0
  fout := fun _ => 0
  P := fun _ _ => 1

/-- **The loss is finite on `flow`** against `κ = ν_B = δ_()`, at every `q` and `b`: the hypothesis
`ilLoss ≠ ⊤` of `il_first_bullet_finite`'s TV clause is met by a flow satisfying all its other
hypotheses (kb `0025`). -/
theorem ilLoss_ne_top (q : ℝ≥0∞) (b : ℝ) :
    ilLoss (Measure.dirac ()) (Measure.dirac ()) q b (fun _ => 1)
      (eDens (Measure.dirac ()) flow) ≠ ⊤ := by
  have he : ∀ x : Unit, eDens (Measure.dirac ()) flow x = 1 := by
    intro x
    have h1 : (Measure.dirac ()).real {x} = 1 := by
      rw [Subsingleton.elim x ()]; simp [Measure.real]
    simp [eDens, emass, flow, h1]
  have hfin : LossFinite (Measure.dirac ()) (Measure.dirac ()) q (fun _ => 1)
      (eDens (Measure.dirac ()) flow) :=
    { ac := Filter.Eventually.of_forall fun x hx => by rw [he x] at hx; norm_num at hx
      ce := Integrable.of_finite
      pen := MemLp.of_discrete }
  rw [ilLoss_of_finite hfin]
  exact EReal.coe_ne_top _

end Example

end GFNBounds.Core.ILBoundFull
