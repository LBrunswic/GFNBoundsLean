import Mathlib
import GFNBounds.Core.StableBound

/-!
# The KL-weak-FM loss has the target's self-entropy as its floor, and controls the sampling error

**`theo:IL_CV_bound`** — statement `proofs.tex:271–287`, proof `proofs.tex:289–372`.

> Let `(𝒮, ν_B)` be a measured Polish space with `ν_B` finite and let `F_init, κ` be probability
> distributions absolutely continuous with respect to `ν_B`, with densities `f_init, k` and with
> finite self-entropy `𝓗`. Let `q ∈ [1,+∞]` and assume `ν_B ∼ ν_T` with
> `dν_B/dν_T ∈ L^{q*}(ν_T)` and `b ≥ 1 + ‖dν_B/dν_T‖_{L^{q*}(ν_T)}`. For a generative flow
> `(π⋆, f⋆_out)` whose star inflow satisfies `F⋆_← ≪ ν_B`, define `𝓛^q_{KL-wFM}(π⋆, f⋆_out)` as in
> Equation `equ:weakFM` and use `F_term = κ̂ := (F_init + F⋆_← − F⋆_out)⁺` during inference. Then:
>
> * for every Markov kernel `π⋆` on `𝒮` and every `f⋆_out ∈ L¹₊(𝒮, ν_B)` with `F⋆_← ≪ ν_B`,
>   `𝓛^q_{KL-wFM} ≥ 𝓗` and
>   `TV(s_τ ‖ κ) ≤ (1/√2)·√(𝓛^q_{KL-wFM} − 𝓗) + min(1, ‖dν_B/dν_T‖_{L^{q*}(ν_T)}
>   (𝓛^q_{KL-wFM} − 𝓗))` (`equ:il_tv_explicit`);
> * let `Θ` be a family of generative flows […]. If `(π⋆, f⋆_out) ∈ Θ` and `ε ∈ [0,1)` satisfy
>   `F_init + F⋆_out π⋆ − F⋆_out ≥ (1−ε)κ` as measures (`equ:il_domination`), then
>   `𝓛^q_{KL-wFM}(π⋆, f⋆_out) ≤ 𝓗 + log(1/(1−ε))`. Consequently, if for every `ε > 0` some member
>   of `Θ` satisfies `equ:il_domination`, then `inf_Θ 𝓛^q_{KL-wFM} = 𝓗`, and if some member
>   satisfies it with `ε = 0` […] the infimum is attained at that flow.

The loss is `equ:weakFM` (`introduction.tex:122`),
`𝓛^q_{KL-wFM}(θ) := b‖δf_init‖_{L^q(ν_T)} − 𝔼_{s∼κ} log f̂_term(s)`.

The proof's steps map onto this file as follows. The mass identity `equ:il_mass_identity`
(`proofs.tex:292–297`) is `il_mass_identity`, one line from `Core.posPart_mass`. The
cross-entropy decomposition `eq:wFM_strong_bound` (`proofs.tex:311–314`) is
`wklfmLoss_decomposition`, resting on the pointwise `klD_integrand_eq`. The penalty estimate
`eq:lp_delta` (`proofs.tex:315–318`) is `penalty_ge`. Their composition is
`loss_sub_selfEntropy_ge`, from which `loss_ge_selfEntropy` (through Gibbs at the normalized
corrected terminal density, `klD_normalized_nonneg`), `klD_le_loss_sub_selfEntropy` and
`lqNormD_le_loss_sub_selfEntropy` follow; the last is `proofs.tex:332–334`. The Hölder step
`equ:il_holder` (`proofs.tex:305–310`) is `il_holder`. The first bullet's display
`equ:il_tv_explicit` is `il_tv_bound`. The second bullet is `loss_le_of_domination`,
`loss_eq_selfEntropy_of_domination_zero`, `eq_of_domination_zero` and `isGLB_of_domination`.

## The modelling decision

As in `GFNBounds.Core.StableBound`, everything is carried by **densities against the background
measure**, and total variation by the ½-convention of `app:notation`, whose `Core.tvD` is reused
unchanged. So `κ = k·ν_B`, `E = e·ν_B` with `e = f_init + f⋆_← − f⋆_out`, `κ̂ = e⁺·ν_B`,
`δf_init = e⁻·ν_B`, and `δ`, `κ̂(𝒮)` are the corresponding integrals.

Two quantities the appendix names have no Mathlib counterpart at this pin in the form the paper
uses them, and are defined here on densities: the **self-entropy** `𝓗 = −∫ k log k dν_B`
(`proofs.tex:264–266`) as `selfEntropy`, and the **Kullback–Leibler divergence**
`KL(κ ‖ κ̂/κ̂(𝒮)) = ∫ k log(k/g) dν_B` as `klD`. Mathlib *does* have `InformationTheory.klDiv`
(`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`), but it is `ℝ≥0∞`-valued and defined
between *measures* through `Measure.rnDeriv`; bridging it to the density picture is a
`withDensity`/`rnDeriv` computation this file does not perform, so `klD` and `klDiv` are related
by no proved lemma here. See SCOPE.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` Polish, `ν_B` finite | ⚠ weakened: any `MeasurableSpace α`, with `[SigmaFinite ν]` and `[SigmaFinite νT]` in `il_holder` alone, where the Radon–Nikodym derivative is formed. Polish is used nowhere, and finiteness nowhere |
| `F_init ≪ ν_B` a probability, density `f_init` | ⚠ absorbed: only `e = f_init + f⋆_← − f⋆_out` appears, with `he1 : ∫ e dν = 1`. See SCOPE — `he1` *is* `E(𝒮) = F_init(𝒮) = 1` |
| `κ ≪ ν_B` a probability, density `k` | ✓ carried: `k : α → ℝ`, `Integrable k ν`, `0 ≤ᵐ[ν] k`, `hk1 : ∫ k dν = 1` |
| `𝓗` finite | ✓ carried as `hklog : Integrable (fun x => k x * log (k x)) ν` |
| `q ∈ [1,+∞]` | ✓ in the main theorems: `q` enters only through `lqNormD νT q (e⁻)`, and the theorems are stated for every real `q` and every `νT`. ⚠ narrowed in `il_holder` alone, which needs `1 < q < ∞` |
| `ν_B ∼ ν_T`, `dν_B/dν_T ∈ L^{q*}(ν_T)` | ⚠ split: the equivalence is used only in `loss_le_of_domination`, as `hTac : νT ≪ ν`; the `L^{q*}` membership is `hr : MemLp _ (ofReal q*) νT` in `il_holder` |
| `b ≥ 1 + ‖dν_B/dν_T‖_{L^{q*}(ν_T)}` | ✓ carried as `hb : 1 + N ≤ b`, with `N` the `L^{q*}` norm; `hN0 : 0 ≤ N` is carried alongside it in `il_tv_bound` and `loss_eq_selfEntropy_of_domination_zero`, the two places that consume it. The floor `𝓛 ≥ 𝓗` needs only `hb` and `hHolder` |
| `(π⋆, f⋆_out)` a generative flow, `π⋆` a Markov kernel, `f⋆_out ∈ L¹₊`, `F⋆_← ≪ ν_B` | ⚠ weakened: only the density `e : α → ℝ` with `Integrable e ν`. No kernel, no outflow. The kernel enters exactly once, through `he1` |
| inference at `F_term = κ̂ := E⁺` | ✓ carried: `κ̂` is `fun x => max (e x) 0`, its mass `zhat` with `hzh : zhat = 1 + δ` |
| the loss `equ:weakFM` | ✓ carried, as `wklfmLoss`, real-valued |
| `𝓛` finite, i.e. `κ ≪ κ̂` | ⚠ **added**, as `hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0` and `helog`. The paper leaves it tacit; without it Lean's `log 0 = 0` would read the paper's `+∞` as a finite number. See SCOPE |
| `theo:negative_control` for the first TV term (`proofs.tex:299–304`) | ✗ **external**: hypothesis `hNC`. The paper quotes it from `\citet{brunswicEGF}` and does not prove it; neither does this library |
| Pinsker's inequality (`proofs.tex:299–304`) | ✗ **external**: hypothesis `hPins`. **Not in Mathlib v4.31.0** — see SCOPE |
| the triangle inequality for TV | ⚠ hypothesis `htri`, since `s_τ` is abstract. `Core.tvD_triangle` proves it whenever `s_τ` has a `ν_B`-density |
| conclusion `𝓛 ≥ 𝓗` | ✓ `loss_ge_selfEntropy` |
| conclusion `equ:il_tv_explicit` | ✓ `il_tv_bound` |
| second bullet, `ε ∈ [0,1)` | ⚠ **generalized**: `loss_le_of_domination` assumes only `ε < 1`. At `ε < 0` the domination hypothesis is stronger and the slack `log(1/(1−ε))` negative, so this is a generalization, not a weakening; `0 ≤ ε` is simply never used |
| second bullet, `𝓛 ≤ 𝓗 + log(1/(1−ε))` | ✓ `loss_le_of_domination` |
| second bullet, `inf_Θ 𝓛 = 𝓗` | ⚠ abstracted: `isGLB_of_domination` on the *set of achievable loss values*, `Θ` itself not modelled |
| second bullet, attainment at `ε = 0` | ✓ `loss_eq_selfEntropy_of_domination_zero`; the equivalence with `equ:FM_const` is `eq_of_domination_zero` |
| second bullet, "in particular if `Θ` is strongly `L^p`-universal" | ✗ not formalized — see SCOPE |

## SCOPE (disclosed)

* **Pinsker's inequality is not in Mathlib v4.31.0.** Grepping the whole pin for `insker` returns
  nothing; the information-theory layer is `Mathlib/InformationTheory/KullbackLeibler/` (`klDiv`,
  `klFun`, a chain rule, Gibbs as `integral_llr_add_sub_measure_univ_nonneg`) plus
  `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean` (`llr`), and there is no total-variation
  *distance* between measures at all — only `SignedMeasure.totalVariation` and
  `VectorMeasure.variation`, which are measures, not distances. Pinsker is therefore carried the
  way `theo:negative_control` is: as the named hypothesis `hPins` of `il_tv_bound`, on the two
  reals the step consumes, in exactly the form `TV ≤ (1/√2)√KL` that `proofs.tex:302` uses. It is
  not proved, not axiomatized, and not weakened.
* **`theo:negative_control` is an external input.** It is `proofs.tex:52–64`, quoted from
  `\citet{brunswicEGF}`, and the paper gives no proof of it. It appears here **only** as the
  hypothesis `hNC : tvNC ≤ δ / zhat` of `il_tv_bound`, in exactly the form
  `δF_init(𝒮)/F̂_term(𝒮)` the proof consumes.
* **The sampler is abstract**, as in `StableBound`: `tv` stands for `TV(s_τ ‖ κ)` and `tvNC` for
  `TV(s_τ ‖ κ̂/κ̂(𝒮))`, related by `htri`. The library builds no Markov chain (`CLAUDE.md`'s first
  obstruction).
* **`E(𝒮) = F_init(𝒮) = 1` is assumed, not derived.** The paper gets it from
  `F⋆_←(𝒮) = F⋆_out π⋆(𝒮) = F⋆_out(𝒮)`, which is the statement that `π⋆` is a Markov kernel. No
  kernel is modelled here, so it is the hypothesis `he1 : ∫ e dν = 1`. Everything downstream —
  `il_mass_identity` in particular — inherits it.
* **`hac` is an added hypothesis, and it is where the paper's `+∞` was.** The paper's loss takes
  values in `(−∞, +∞]`: when `κ` charges `{κ̂ = 0}` the cross-entropy is `+∞` and every inequality
  of the first bullet is vacuous. `wklfmLoss` is real-valued, and Lean's `Real.log 0 = 0` would
  silently read that `+∞` as a finite number, so the honest reading is to assume the loss finite.
  `hac` (`κ ≪ κ̂`) and `helog` (integrability of the cross-entropy integrand) are exactly that
  assumption. This is a **restriction**, not an extension: nothing here claims the bound in the
  case the paper handles by `+∞`.
* **The Hölder step is proved only for `1 < q < ∞`.** `il_holder` derives `equ:il_holder`'s
  `δ ≤ ‖dν_B/dν_T‖_{L^{q*}(ν_T)} ‖δf_init‖_{L^q(ν_T)}` from `ν_B ≪ ν_T` and Mathlib's
  `integral_mul_le_Lp_mul_Lq_of_nonneg`, which needs a `Real.HolderConjugate` pair and so excludes
  `q = 1` (`q* = ∞`) and `q = ∞` (`q* = 1`). The main theorems do **not** narrow: they carry the
  step's *conclusion* as the hypothesis `hHolder : δ ≤ N * lqNormD νT q (e⁻)`, so they hold at
  every `q ∈ [1,+∞]` for which that estimate is supplied, and `il_holder` supplies it in the
  interior.
* **`Θ` is not modelled.** The second bullet's `inf_Θ 𝓛 = 𝓗` is `isGLB_of_domination`, a statement
  about an arbitrary set `L ⊆ ℝ` of achievable loss values that is bounded below by `𝓗` and comes
  within `log(1/(1−ε))` of it for every `ε ∈ (0,1)`. Formalizing a family of generative flows
  needs the kernel layer this library does not have. The clause "in particular if `f_init, k ∈
  L^p(ν_B)` and `Θ` is strongly `L^p`-universal" is a citation of `def:universality` and is not
  formalized here; `GFNBounds.Core.StrongUniversality` carries that definition and no bridge to
  this file is proved.
* **`klD` is not Mathlib's `klDiv`.** No lemma relating them is proved. The bridge would be
  `klD ν k g = (klDiv (ν.withDensity k) (ν.withDensity g)).toReal` under the hypotheses above, via
  `Measure.rnDeriv_withDensity`; it is a `kb/` candidate, not a claim of this file. What *is*
  proved here is the one property the paper uses, `klD_nonneg` (Gibbs), from the pointwise
  `x − y ≤ x log(x/y)`.
* **No `sorry`.** Every declaration below is closed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## The three quantities of the statement -/

/-- **The self-entropy `𝓗` of `proofs.tex:264–266`**, the floor of the loss:
`𝓗 := −∫ k(s) log k(s) dν_B(s)` for a probability `κ = k·ν_B`. It is not a Shannon entropy:
replacing `ν_B` by `cν_B` shifts it by `log c`, and it is of either sign. -/
noncomputable def selfEntropy (ν : Measure α) (k : α → ℝ) : ℝ :=
  -∫ x, k x * Real.log (k x) ∂ν

/-- **The Kullback–Leibler divergence of `proofs.tex:302`, read between densities**:
`KL(k·ν ‖ g·ν) = ∫ k log(k/g) dν`. Mathlib's `InformationTheory.klDiv` is `ℝ≥0∞`-valued and
defined between measures through `Measure.rnDeriv`; this file works in densities throughout, and
proves the single property the appendix uses — non-negativity — directly. See this file's SCOPE. -/
noncomputable def klD (ν : Measure α) (k g : α → ℝ) : ℝ :=
  ∫ x, k x * Real.log (k x / g x) ∂ν

/-- The `L^q(ν_T)` norm of a density, at a real exponent: `‖f‖_{L^q(ν_T)} = (∫|f|^q dν_T)^{1/q}`.
This is `StableBound`'s `stableLoss` with its two densities not yet subtracted; see
`stableLoss_eq_lqNormD`. -/
noncomputable def lqNormD (νT : Measure α) (q : ℝ) (f : α → ℝ) : ℝ :=
  (∫ x, |f x| ^ q ∂νT) ^ (1 / q)

theorem lqNormD_nonneg (νT : Measure α) (q : ℝ) (f : α → ℝ) : 0 ≤ lqNormD νT q f :=
  Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) q) _

/-- The `L^q` norm of this file and the loss of `StableBound` are the same object: the file that
proves `theo:RL_CV_bound_full` measures `e − k`, this one measures `δf_init = e⁻`. -/
theorem stableLoss_eq_lqNormD (νT : Measure α) (q : ℝ) (e k : α → ℝ) :
    stableLoss νT q e k = lqNormD νT q (fun x => e x - k x) := rfl

/-- **The KL-weak-FM loss `equ:weakFM`** (`introduction.tex:122`), in densities:

  `𝓛^q_{KL-wFM} = b‖δf_init‖_{L^q(ν_T)} − 𝔼_{s∼κ} log f̂_term(s)`,

with `δf_init = e⁻` and `f̂_term = e⁺`. Real-valued: see this file's SCOPE on `hac`. -/
noncomputable def wklfmLoss (ν νT : Measure α) (q b : ℝ) (k e : α → ℝ) : ℝ :=
  b * lqNormD νT q (fun x => max (-e x) 0) - ∫ x, k x * Real.log (max (e x) 0) ∂ν

/-! ## Gibbs' inequality on densities -/

/-- The pointwise inequality behind `klD_nonneg`: `x − y ≤ x log(x/y)` for `x, y ≥ 0`, provided
`y = 0` forces `x = 0`. It is `log t ≤ t − 1` at `t = y/x`, and the proviso is where absolute
continuity enters — at `y = 0 < x` the true value is `+∞` and Lean's `log 0 = 0` is not it. -/
theorem sub_le_mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hac : y = 0 → x = 0) :
    x - y ≤ x * Real.log (x / y) := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0]
    simp only [zero_mul, zero_sub, neg_nonpos]
    exact hy
  · have hyne : y ≠ 0 := fun h => absurd (hac h) (ne_of_gt h0)
    have hy0 : 0 < y := lt_of_le_of_ne hy (Ne.symm hyne)
    have hlog : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 h0)
    have hxy : x / y = (y / x)⁻¹ := (inv_div y x).symm
    rw [hxy, Real.log_inv]
    have hmul : x * (y / x) = y := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hlog h0.le]

/-- **Gibbs' inequality, in the form `proofs.tex:322` uses it**: `KL(κ ‖ κ̂/κ̂(𝒮)) ≥ 0`. Stated on
densities against a common measure, for `κ` of mass at least that of the comparison, and under
the absolute continuity `hac` without which the left-hand side is `+∞` rather than a real. -/
theorem klD_nonneg {ν : Measure α} {k g : α → ℝ}
    (hk : Integrable k ν) (hg : Integrable g ν)
    (hint : Integrable (fun x => k x * Real.log (k x / g x)) ν)
    (hk0 : 0 ≤ᵐ[ν] k) (hg0 : 0 ≤ᵐ[ν] g)
    (hac : ∀ᵐ x ∂ν, g x = 0 → k x = 0)
    (hmass : ∫ x, g x ∂ν ≤ ∫ x, k x ∂ν) :
    0 ≤ klD ν k g := by
  have h : ∫ x, (k x - g x) ∂ν ≤ ∫ x, k x * Real.log (k x / g x) ∂ν := by
    refine integral_mono_ae (hk.sub hg) hint ?_
    filter_upwards [hk0, hg0, hac] with x h1 h2 h3
    exact sub_le_mul_log_div h1 h2 h3
  rw [integral_sub hk hg] at h
  unfold klD
  linarith

/-! ## The mass identity -/

/-- **`equ:il_mass_identity`** (`proofs.tex:292–297`): `E⁺` and `E⁻` having disjoint supports and
`E(𝒮) = F_init(𝒮) = 1`, the corrected terminal flow has mass `κ̂(𝒮) = 1 + δ ≥ 1`. In densities
this is `∫ e⁺ = 1 + ∫ e⁻`, one line from `Core.posPart_mass`. -/
theorem il_mass_identity {ν : Measure α} {e : α → ℝ} (he : Integrable e ν)
    (he1 : ∫ x, e x ∂ν = 1) :
    ∫ x, max (e x) 0 ∂ν = 1 + ∫ x, max (-e x) 0 ∂ν := by
  rw [posPart_mass he, he1]

/-! ## The cross-entropy decomposition -/

/-- The pointwise identity behind `wklfmLoss_decomposition`: on `{k > 0}`, where absolute
continuity makes `e⁺ > 0`, `log(k/(e⁺/ẑ)) = log k − log e⁺ + log ẑ`; on `{k = 0}` both sides
vanish. -/
theorem klD_integrand_eq {ν : Measure α} {k e : α → ℝ} {zhat : ℝ}
    (hk0 : 0 ≤ᵐ[ν] k) (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0) (hzh0 : 0 < zhat) :
    (fun x => k x * Real.log (k x / (max (e x) 0 / zhat)))
      =ᵐ[ν] fun x => k x * Real.log (k x) - k x * Real.log (max (e x) 0)
              + k x * Real.log zhat := by
  filter_upwards [hk0, hac] with x hx hxa
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ k x from hx) with h0 | h0
  · rw [← h0]; simp
  · have hE : max (e x) 0 ≠ 0 := fun h => absurd (hxa h) (ne_of_gt h0)
    have hkne : k x ≠ 0 := ne_of_gt h0
    have hzne : zhat ≠ 0 := ne_of_gt hzh0
    have key : k x / (max (e x) 0 / zhat) = k x * zhat / max (e x) 0 := by
      field_simp
    rw [key, Real.log_div (mul_ne_zero hkne hzne) hE, Real.log_mul hkne hzne]
    ring

/-- **`eq:wFM_strong_bound`** (`proofs.tex:311–314`): decomposing the cross-entropy of the target
against `f̂_term` as forward KL plus self-entropy plus normalization,

  `𝓛^q_{KL-wFM} = KL(κ ‖ κ̂/κ̂(𝒮)) + b‖δf_init‖_{L^q(ν_T)} − log κ̂(𝒮) + 𝓗` .

`zhat` is `κ̂(𝒮)`; `il_mass_identity` is what turns `log κ̂(𝒮)` into `log(1 + δ)` downstream. -/
theorem wklfmLoss_decomposition {ν νT : Measure α} {k e : α → ℝ} {q b zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0) (hzh0 : 0 < zhat) :
    wklfmLoss ν νT q b k e
      = klD ν k (fun x => max (e x) 0 / zhat) + b * lqNormD νT q (fun x => max (-e x) 0)
        - Real.log zhat + selfEntropy ν k := by
  have hcong := klD_integrand_eq (k := k) (e := e) hk0 hac hzh0
  have hconst : Integrable (fun x => k x * Real.log zhat) ν := hk.mul_const _
  have hsub : Integrable (fun x => k x * Real.log (k x) - k x * Real.log (max (e x) 0)) ν :=
    hklog.sub helog
  have hklD : klD ν k (fun x => max (e x) 0 / zhat)
      = (∫ x, k x * Real.log (k x) ∂ν) - (∫ x, k x * Real.log (max (e x) 0) ∂ν)
        + Real.log zhat := by
    rw [klD, integral_congr_ae hcong, integral_add hsub hconst,
      integral_sub hklog helog, integral_mul_const, hk1, one_mul]
  rw [wklfmLoss, selfEntropy, hklD]
  ring

/-- The integrand of `klD ν k (κ̂/κ̂(𝒮))` is integrable as soon as the two integrands of the
decomposition are: it is their difference plus a multiple of `k`, off a null set. -/
theorem klD_integrable {ν : Measure α} {k e : α → ℝ} {zhat : ℝ}
    (hk : Integrable k ν)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hk0 : 0 ≤ᵐ[ν] k) (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0) (hzh0 : 0 < zhat) :
    Integrable (fun x => k x * Real.log (k x / (max (e x) 0 / zhat))) ν :=
  ((hklog.sub helog).add (hk.mul_const (Real.log zhat))).congr
    (klD_integrand_eq (k := k) (e := e) hk0 hac hzh0).symm

/-! ## The penalty term, and the floor of the loss -/

/-- **`eq:lp_delta`** (`proofs.tex:315–318`): `b‖δf_init‖ − log(1+δ) ≥ ‖δf_init‖ ≥ 0`, by
`log(1+δ) ≤ δ` and the Hölder estimate `δ ≤ N‖δf_init‖` with `b ≥ 1 + N`. -/
theorem penalty_ge {b N D δ : ℝ} (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D)
    (hb : 1 + N ≤ b) (hHolder : δ ≤ N * D) :
    D ≤ b * D - Real.log (1 + δ) := by
  have hlog : Real.log (1 + δ) ≤ δ := by
    have h := Real.log_le_sub_one_of_pos (x := 1 + δ) (by linarith)
    linarith
  have hkey : 0 ≤ (b - 1 - N) * D := mul_nonneg (by linarith) hD0
  nlinarith

/-- **`proofs.tex:320–334` in one inequality**: the loss exceeds the floor by at least the KL term
and the `L^q` penalty together,

  `KL(κ ‖ κ̂/κ̂(𝒮)) + ‖δf_init‖_{L^q(ν_T)} ≤ 𝓛^q_{KL-wFM} − 𝓗` .

This is `eq:wFM_strong_bound` composed with `eq:lp_delta`; the two displays `proofs.tex:322` and
`proofs.tex:332–334` are its two halves. `hHolder` is `equ:il_holder`, which `il_holder` proves
for `1 < q < ∞`. -/
theorem loss_sub_selfEntropy_ge {ν νT : Measure α} {k e : α → ℝ} {q b N δ zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ) (hb : 1 + N ≤ b)
    (hHolder : δ ≤ N * lqNormD νT q (fun x => max (-e x) 0)) :
    klD ν k (fun x => max (e x) 0 / zhat) + lqNormD νT q (fun x => max (-e x) 0)
      ≤ wklfmLoss ν νT q b k e - selfEntropy ν k := by
  have hδ0 : 0 ≤ δ := hδ ▸ integral_nonneg fun _ => le_max_right _ _
  have hzh0 : 0 < zhat := by rw [hzh]; linarith
  have hdec := wklfmLoss_decomposition (νT := νT) (q := q) (b := b) hk hk1 hk0 hklog helog hac hzh0
  have hpen := penalty_ge (b := b) (N := N) (D := lqNormD νT q (fun x => max (-e x) 0)) (δ := δ)
    hδ0 (lqNormD_nonneg _ _ _) hb hHolder
  rw [hzh]
  rw [hzh] at hdec
  linarith

/-- **Gibbs at the normalized corrected terminal density** (`proofs.tex:322`):
`KL(κ ‖ κ̂/κ̂(𝒮)) ≥ 0`. The mass identity `equ:il_mass_identity` is what makes `κ̂/κ̂(𝒮)` a
probability density, which is the hypothesis `klD_nonneg` consumes. -/
theorem klD_normalized_nonneg {ν : Measure α} {k e : α → ℝ} {δ zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (he : Integrable e ν) (he1 : ∫ x, e x ∂ν = 1)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ) :
    0 ≤ klD ν k (fun x => max (e x) 0 / zhat) := by
  have hδ0 : 0 ≤ δ := hδ ▸ integral_nonneg fun _ => le_max_right _ _
  have hzh0 : 0 < zhat := by rw [hzh]; linarith
  have hmass : ∫ x, max (e x) 0 ∂ν = zhat := by rw [il_mass_identity he he1, hzh, hδ]
  refine klD_nonneg hk (he.pos_part.div_const _)
    (klD_integrable hk hklog helog hk0 hac hzh0) hk0
    (Filter.Eventually.of_forall fun x => div_nonneg (le_max_right _ _) hzh0.le)
    (by filter_upwards [hac] with x hx hx0
        exact hx (by simpa [div_eq_zero_iff, ne_of_gt hzh0] using hx0)) ?_
  rw [hk1, integral_div, hmass, div_self (ne_of_gt hzh0)]

/-- **The floor of the loss**, the first half of the first bullet (`proofs.tex:325`):
`𝓛^q_{KL-wFM} ≥ 𝓗`. Gibbs' inequality supplies `KL ≥ 0`, and the mass identity is what makes
`κ̂/κ̂(𝒮)` a probability density so that Gibbs applies. -/
theorem loss_ge_selfEntropy {ν νT : Measure α} {k e : α → ℝ} {q b N δ zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (he : Integrable e ν) (he1 : ∫ x, e x ∂ν = 1)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ) (hb : 1 + N ≤ b)
    (hHolder : δ ≤ N * lqNormD νT q (fun x => max (-e x) 0)) :
    selfEntropy ν k ≤ wklfmLoss ν νT q b k e := by
  have hmain := loss_sub_selfEntropy_ge hk hk1 hk0 hklog helog hac hδ hzh hb hHolder
  have hkl := klD_normalized_nonneg hk hk1 hk0 he he1 hklog helog hac hδ hzh
  have := lqNormD_nonneg νT q (fun x => max (-e x) 0)
  linarith

/-- **The KL term is at most the excess of the loss over its floor** (`proofs.tex:322`), the
inequality Pinsker is applied to. -/
theorem klD_le_loss_sub_selfEntropy {ν νT : Measure α} {k e : α → ℝ} {q b N δ zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ) (hb : 1 + N ≤ b)
    (hHolder : δ ≤ N * lqNormD νT q (fun x => max (-e x) 0)) :
    klD ν k (fun x => max (e x) 0 / zhat) ≤ wklfmLoss ν νT q b k e - selfEntropy ν k := by
  have hmain := loss_sub_selfEntropy_ge hk hk1 hk0 hklog helog hac hδ hzh hb hHolder
  have := lqNormD_nonneg νT q (fun x => max (-e x) 0)
  linarith

/-- **`proofs.tex:332–334`**: `𝓛^q_{KL-wFM} − 𝓗 ≥ ‖δf_init‖_{L^q(ν_T)}`, the inequality that
turns the loss into a bound on the initial defect, hence on `δ` through `equ:il_holder`. -/
theorem lqNormD_le_loss_sub_selfEntropy {ν νT : Measure α} {k e : α → ℝ} {q b N δ zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (he : Integrable e ν) (he1 : ∫ x, e x ∂ν = 1)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ) (hb : 1 + N ≤ b)
    (hHolder : δ ≤ N * lqNormD νT q (fun x => max (-e x) 0)) :
    lqNormD νT q (fun x => max (-e x) 0) ≤ wklfmLoss ν νT q b k e - selfEntropy ν k := by
  have hmain := loss_sub_selfEntropy_ge hk hk1 hk0 hklog helog hac hδ hzh hb hHolder
  have hkl := klD_normalized_nonneg hk hk1 hk0 he he1 hklog helog hac hδ hzh
  linarith

/-! ## The Hölder step -/

/-- **`equ:il_holder`** (`proofs.tex:305–310`): `ν_B ≪ ν_T` gives
`δ = ∫ δf_init (dν_B/dν_T) dν_T ≤ ‖dν_B/dν_T‖_{L^{q*}(ν_T)} ‖δf_init‖_{L^q(ν_T)}`, by Hölder with
the conjugate exponents `q*` and `q`. Proved for `1 < q < ∞` only: Mathlib's Hölder needs a
`Real.HolderConjugate` pair, which excludes the endpoints. See this file's SCOPE. -/
theorem il_holder {ν νT : Measure α} [SigmaFinite ν] [SigmaFinite νT] {e : α → ℝ} {q qstar : ℝ}
    (hqq : qstar.HolderConjugate q) (hac : ν ≪ νT)
    (hr : MemLp (fun x => (ν.rnDeriv νT x).toReal) (ENNReal.ofReal qstar) νT)
    (hf : MemLp (fun x => max (-e x) 0) (ENNReal.ofReal q) νT) :
    ∫ x, max (-e x) 0 ∂ν
      ≤ lqNormD νT qstar (fun x => (ν.rnDeriv νT x).toReal)
        * lqNormD νT q (fun x => max (-e x) 0) := by
  have hkey := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := νT) hqq
    (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
    (Filter.Eventually.of_forall fun x => le_max_right (-e x) 0) hr hf
  have h1 : ∫ x, (ν.rnDeriv νT x).toReal ^ qstar ∂νT
      = ∫ x, |(ν.rnDeriv νT x).toReal| ^ qstar ∂νT := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (ν.rnDeriv νT x).toReal ^ qstar = |(ν.rnDeriv νT x).toReal| ^ qstar
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
  have h2 : ∫ x, max (-e x) 0 ^ q ∂νT = ∫ x, |max (-e x) 0| ^ q ∂νT := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show max (-e x) 0 ^ q = |max (-e x) 0| ^ q
    rw [abs_of_nonneg (le_max_right (-e x) 0)]
  rw [h1, h2] at hkey
  have hchange : ∫ x, max (-e x) 0 ∂ν
      = ∫ x, (ν.rnDeriv νT x).toReal * max (-e x) 0 ∂νT :=
    (integral_toReal_rnDeriv_mul (f := fun x => max (-e x) 0) hac).symm
  rw [hchange, lqNormD, lqNormD]
  exact hkey

/-! ## The first bullet: the total-variation bound -/

/-- The first term of `equ:il_tv_split` (`proofs.tex:299–303`): `δ/κ̂(𝒮) = δ/(1+δ) ≤ min(1, δ)`,
by the mass identity. -/
theorem negMass_ratio_le_min {δ : ℝ} (hδ0 : 0 ≤ δ) : δ / (1 + δ) ≤ min 1 δ := by
  have h1 : (0 : ℝ) < 1 + δ := by linarith
  refine le_min ?_ ?_
  · rw [div_le_one h1]; linarith
  · rw [div_le_iff₀ h1]; nlinarith

/-- **`equ:il_tv_explicit`** (`proofs.tex:274–276`), the second display of the first bullet of
**`theo:IL_CV_bound`**:

  `TV(s_τ ‖ κ) ≤ (1/√2)√(𝓛^q_{KL-wFM} − 𝓗) + min(1, ‖dν_B/dν_T‖_{L^{q*}(ν_T)}(𝓛^q_{KL-wFM} − 𝓗))` .

`tv` is `TV(s_τ ‖ κ)` and `tvNC` is `TV(s_τ ‖ κ̂/κ̂(𝒮))`. Three inputs are hypotheses on reals:
`htri`, the triangle inequality, which `Core.tvD_triangle` supplies for any sampler with a
`ν_B`-density; `hNC`, which is **`theo:negative_control`**, quoted by the paper from
`\citet{brunswicEGF}` and proved nowhere; and `hPins`, which is **Pinsker's inequality**, absent
from Mathlib v4.31.0. All three are disclosed in this file's SCOPE. -/
theorem il_tv_bound {ν νT : Measure α} {k e : α → ℝ} {q b N δ zhat tv tvNC : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (he : Integrable e ν) (he1 : ∫ x, e x ∂ν = 1)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ)
    (hN0 : 0 ≤ N) (hb : 1 + N ≤ b)
    (hHolder : δ ≤ N * lqNormD νT q (fun x => max (-e x) 0))
    (hNC : tvNC ≤ δ / zhat)
    (hPins : tvD ν k (fun x => max (e x) 0 / zhat)
      ≤ 1 / Real.sqrt 2 * Real.sqrt (klD ν k (fun x => max (e x) 0 / zhat)))
    (htri : tv ≤ tvNC + tvD ν k (fun x => max (e x) 0 / zhat)) :
    tv ≤ 1 / Real.sqrt 2 * Real.sqrt (wklfmLoss ν νT q b k e - selfEntropy ν k)
        + min 1 (N * (wklfmLoss ν νT q b k e - selfEntropy ν k)) := by
  set L : ℝ := wklfmLoss ν νT q b k e - selfEntropy ν k with hL
  have hδ0 : 0 ≤ δ := hδ ▸ integral_nonneg fun _ => le_max_right _ _
  -- the negative-control term
  have hNCmin : tvNC ≤ min 1 δ := by
    refine hNC.trans ?_
    rw [hzh]
    exact negMass_ratio_le_min hδ0
  have hD : lqNormD νT q (fun x => max (-e x) 0) ≤ L :=
    lqNormD_le_loss_sub_selfEntropy hk hk1 hk0 he he1 hklog helog hac hδ hzh hb hHolder
  have hδL : δ ≤ N * L :=
    hHolder.trans (mul_le_mul_of_nonneg_left hD hN0)
  have hmin : min 1 δ ≤ min 1 (N * L) := min_le_min le_rfl hδL
  -- the Pinsker term
  have hkl : klD ν k (fun x => max (e x) 0 / zhat) ≤ L :=
    klD_le_loss_sub_selfEntropy hk hk1 hk0 hklog helog hac hδ hzh hb hHolder
  have hsqrt : Real.sqrt (klD ν k (fun x => max (e x) 0 / zhat)) ≤ Real.sqrt L :=
    Real.sqrt_le_sqrt hkl
  have hc : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  have hPins' : tvD ν k (fun x => max (e x) 0 / zhat) ≤ 1 / Real.sqrt 2 * Real.sqrt L :=
    hPins.trans (mul_le_mul_of_nonneg_left hsqrt hc)
  linarith

/-! ## The second bullet: the domination condition -/

/-- **`equ:il_domination` bounds the loss above** (`proofs.tex:344–354`): if
`F_init + F⋆_out π⋆ − F⋆_out ≥ (1−ε)κ` as measures, then `δf_init = 0`, `f̂_term = e` and

  `𝓛^q_{KL-wFM} ≤ 𝓗 + log(1/(1−ε))` .

The `L^q` penalty vanishes for every `q`, every admissible `b` and every `ν_T`; `hTac : ν_T ≪ ν_B`
is the half of the paper's `ν_B ∼ ν_T` that transports "`e⁻ = 0` `ν_B`-a.e." to `ν_T`. Only
`ε < 1` is used, not the paper's `ε ∈ [0,1)`: the estimate is the same one at a negative `ε`,
where `equ:il_domination` is a stronger hypothesis and `log(1/(1−ε))` a negative slack. -/
theorem loss_le_of_domination {ν νT : Measure α} {k e : α → ℝ} {q b ε : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hq0 : 0 < q) (hTac : νT ≪ ν) (hε1 : ε < 1)
    (hdom : ∀ᵐ x ∂ν, (1 - ε) * k x ≤ e x) :
    wklfmLoss ν νT q b k e ≤ selfEntropy ν k + Real.log (1 / (1 - ε)) := by
  have hε' : (0 : ℝ) < 1 - ε := by linarith
  -- the outflow defect vanishes
  have hneg : ∀ᵐ x ∂ν, max (-e x) 0 = 0 := by
    filter_upwards [hk0, hdom] with x hx hd
    have hx' : (0 : ℝ) ≤ k x := hx
    have he0 : 0 ≤ e x := le_trans (mul_nonneg hε'.le hx') hd
    exact max_eq_right (neg_nonpos.mpr he0)
  have hpen : lqNormD νT q (fun x => max (-e x) 0) = 0 := by
    have hz : ∫ x, |max (-e x) 0| ^ q ∂νT = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hTac hneg] with x hx
      simp [hx, Real.zero_rpow (ne_of_gt hq0)]
    rw [lqNormD, hz, Real.zero_rpow (by positivity)]
  -- the cross-entropy is dominated
  have hsplit : (fun x => k x * Real.log ((1 - ε) * k x))
      =ᵐ[ν] fun x => k x * Real.log (1 - ε) + k x * Real.log (k x) := by
    filter_upwards [hk0] with x hx
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ k x from hx) with h0 | h0
    · rw [← h0]; simp
    · rw [Real.log_mul (ne_of_gt hε') (ne_of_gt h0)]; ring
  have hlin : Integrable (fun x => k x * Real.log (1 - ε)) ν := hk.mul_const _
  have haux : Integrable (fun x => k x * Real.log (1 - ε) + k x * Real.log (k x)) ν :=
    hlin.add hklog
  have hcmp : Integrable (fun x => k x * Real.log ((1 - ε) * k x)) ν := haux.congr hsplit.symm
  have hle : ∫ x, k x * Real.log ((1 - ε) * k x) ∂ν
      ≤ ∫ x, k x * Real.log (max (e x) 0) ∂ν := by
    refine integral_mono_ae hcmp helog ?_
    filter_upwards [hk0, hdom] with x hx hd
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ k x from hx) with h0 | h0
    · rw [← h0]; simp
    · have hpos : 0 < (1 - ε) * k x := mul_pos hε' h0
      have hle' : (1 - ε) * k x ≤ max (e x) 0 := le_max_of_le_left hd
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle') h0.le
  have hval : ∫ x, k x * Real.log ((1 - ε) * k x) ∂ν
      = Real.log (1 - ε) + ∫ x, k x * Real.log (k x) ∂ν := by
    rw [integral_congr_ae hsplit, integral_add hlin hklog, integral_mul_const, hk1,
      one_mul]
  have hlog : Real.log (1 / (1 - ε)) = -Real.log (1 - ε) := by
    rw [one_div, Real.log_inv]
  rw [wklfmLoss, selfEntropy, hpen, hlog]
  rw [hval] at hle
  linarith

/-- **The `ε = 0` case of `equ:il_domination` is `equ:FM_const`** (`proofs.tex:359–362`): a
non-negative defect `E − κ` between measures of equal total mass is zero. In densities: `k ≤ e`
`ν_B`-a.e. with equal integrals forces `e = k` `ν_B`-a.e. -/
theorem eq_of_domination_zero {ν : Measure α} {k e : α → ℝ}
    (hk : Integrable k ν) (he : Integrable e ν)
    (hdom : ∀ᵐ x ∂ν, k x ≤ e x) (hmass : ∫ x, e x ∂ν = ∫ x, k x ∂ν) :
    e =ᵐ[ν] k := by
  have hsub : Integrable (fun x => e x - k x) ν := he.sub hk
  have hnn : 0 ≤ᵐ[ν] fun x => e x - k x := by
    filter_upwards [hdom] with x hx
    simp only [Pi.zero_apply]
    linarith
  have hzero : ∫ x, (e x - k x) ∂ν = 0 := by
    rw [integral_sub he hk, hmass, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hsub).mp hzero
  filter_upwards [hae] with x hx
  simp only [Pi.zero_apply] at hx
  linarith

/-- **Attainment at `ε = 0`** (`proofs.tex:364–365`): a flow satisfying `equ:il_domination` with
`ε = 0` — equivalently, satisfying the flow-matching constraint `equ:FM_const` for the pair
`(F_init, κ)` — has `𝓛^q_{KL-wFM} = 𝓗`, the floor. -/
theorem loss_eq_selfEntropy_of_domination_zero {ν νT : Measure α} {k e : α → ℝ} {q b N δ zhat : ℝ}
    (hk : Integrable k ν) (hk1 : ∫ x, k x ∂ν = 1) (hk0 : 0 ≤ᵐ[ν] k)
    (he : Integrable e ν) (he1 : ∫ x, e x ∂ν = 1)
    (hklog : Integrable (fun x => k x * Real.log (k x)) ν)
    (helog : Integrable (fun x => k x * Real.log (max (e x) 0)) ν)
    (hac : ∀ᵐ x ∂ν, max (e x) 0 = 0 → k x = 0)
    (hδ : δ = ∫ x, max (-e x) 0 ∂ν) (hzh : zhat = 1 + δ)
    (hN0 : 0 ≤ N) (hb : 1 + N ≤ b)
    (hq0 : 0 < q) (hTac : νT ≪ ν)
    (hdom : ∀ᵐ x ∂ν, k x ≤ e x) :
    wklfmLoss ν νT q b k e = selfEntropy ν k := by
  have hdom' : ∀ᵐ x ∂ν, (1 - (0 : ℝ)) * k x ≤ e x := by
    filter_upwards [hdom] with x hx
    linarith
  have hup := loss_le_of_domination (b := b) hk hk1 hk0 hklog helog hq0 hTac
    (by norm_num) hdom'
  simp only [sub_zero, div_one, Real.log_one, add_zero] at hup
  -- the defect vanishes, so the Hölder estimate is trivial
  have hneg : ∀ᵐ x ∂ν, max (-e x) 0 = 0 := by
    filter_upwards [hk0, hdom] with x hx hd
    have hx' : (0 : ℝ) ≤ k x := hx
    have he0 : 0 ≤ e x := le_trans hx' hd
    exact max_eq_right (neg_nonpos.mpr he0)
  have hδ0 : δ = 0 := by
    rw [hδ]
    exact integral_eq_zero_of_ae hneg
  have hHolder : δ ≤ N * lqNormD νT q (fun x => max (-e x) 0) := by
    rw [hδ0]
    exact mul_nonneg hN0 (lqNormD_nonneg _ _ _)
  have hlow := loss_ge_selfEntropy hk hk1 hk0 he he1 hklog helog hac hδ hzh hb hHolder
  linarith

/-- **`inf_Θ 𝓛^q_{KL-wFM} = 𝓗`** (`proofs.tex:356–359`), on the set of achievable loss values:
a set of reals bounded below by `𝓗` that comes within `log(1/(1−ε))` of it for every
`ε ∈ (0,1)` has `𝓗` for greatest lower bound. `Θ` itself is not modelled — see this file's
SCOPE — and the two hypotheses are supplied by `loss_ge_selfEntropy` and
`loss_le_of_domination` at each member. -/
theorem isGLB_of_domination (L : Set ℝ) (H : ℝ)
    (hlb : ∀ x ∈ L, H ≤ x)
    (hub : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ x ∈ L, x ≤ H + Real.log (1 / (1 - ε))) :
    IsGLB L H := by
  refine ⟨hlb, fun c hc => ?_⟩
  refine le_of_forall_sub_le fun η hη => ?_
  set ε : ℝ := 1 - Real.exp (-η) with hε
  have hexp1 : Real.exp (-η) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hexp0 : 0 < Real.exp (-η) := Real.exp_pos _
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε < 1 := by rw [hε]; linarith
  obtain ⟨x, hxL, hx⟩ := hub ε hε0 hε1
  have hval : Real.log (1 / (1 - ε)) = η := by
    have h1 : 1 - ε = Real.exp (-η) := by rw [hε]; ring
    rw [h1, one_div, ← Real.exp_neg, Real.log_exp]
    ring
  rw [hval] at hx
  exact le_trans (sub_le_sub_right (hc hxL) η) (by linarith)

end GFNBounds.Core
