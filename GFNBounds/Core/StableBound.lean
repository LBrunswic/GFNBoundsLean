import Mathlib

/-!
# A stable `L^q` flow-matching loss controls the sampling error and the initial-mass defect

**`theo:RL_CV_bound_full`** — statement `proofs.tex:148–184`, proof `proofs.tex:188–258`
(Theorem 16 of the ICLR build). **Item (1) only.**

> Write `C₀ := ν_B(𝒮)^{1−1/q} ‖dν_B/dν_T‖^{1/q}_{L^∞(ν_T)}`, `C := 2C₀/κ(𝒮)`
> (`equ:stable_constants`). Let `(π⋆, f⋆_out)` be a generative flow trained on the target
> `F_term = κ` with loss `𝓛`, but using `F_term = κ̂ := E⁺` during inference, where
> `E := F_init + F⋆_← − F⋆_out`. Write `t := κ(𝒮)`. Then:
> (1) the loss controls the sampling error and the initial-mass defect together,
> `TV(s_τ ‖ κ/t) ≤ C 𝓛` (`equ:stable_bound`), and `|F_init(𝒮) − κ(𝒮)| ≤ C₀ 𝓛`
> (`equ:mass_floor`).

The proof's five steps map onto this file as follows. Step 0 (`equ:mass_identity`,
`proofs.tex:195–202`) is `posPart_mass`. Step 1 (`equ:two_dominations`, `proofs.tex:204–207`) is
`negMass_le` and `hatDist_le`, each resting on a one-line pointwise inequality —
`negPart_le_abs_sub` and `abs_sub_posPart_le`. Step 2 (`proofs.tex:209–232`) is
`tvD_normalization`/`tvD_normalization_le` for the normalization comparison
(`equ:normalization_lemma`, `proofs.tex:217–220`), `mass_defect_le` for `equ:mass_defect`, and
`tv_le_two_fmL1` for the chain `equ:tv_chain` closing at `2Δ/t`. Step 3 (`proofs.tex:234–239`) is
`integral_le_measure_rpow_mul` and `integral_le_of_le_smul`, composed in
`fmL1_le_holderConst_mul_loss`. The two displays of item (1) are `mass_floor` and `stable_bound`;
Step 3b is absorbed into the latter, the chain being closed at `2Δ/t` before `Δ ≤ C₀𝓛` is
substituted rather than after.

## The modelling decision

Everything is carried by **densities against the background measure**, and total variation by the
½-convention the appendix fixes in `app:notation`:

  `tvD ν f g = ½ ∫ |f − g| dν`.

So `κ = k·ν_B`, `E = e·ν_B`, `κ̂ = e⁺·ν_B`, `δF_init = e⁻·ν_B`, and the masses `t`, `z`, `κ̂(𝒮)`
are the corresponding integrals. Measures are never formed: the objects the paper integrates are
already its densities, and every step of the proof except the two that leave the density picture
— `theo:negative_control` and the triangle inequality — is an inequality between integrals.

The two that leave it are carried as hypotheses on real numbers, `hNC` and `htri`, which is what
lets the sampler `s_τ` stay abstract: it is not constructible here, having no Markov chain behind
it, and it enters the statement only through the two reals `tv` and `tvNC`. `tvD_triangle`
discharges `htri` for any sampler whose law has a `ν_B`-density; nothing discharges `hNC`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` Polish, `ν_B` a non-negative finite background measure | ⚠ weakened: any `MeasurableSpace α` with `[IsFiniteMeasure ν]`. Polish is used nowhere in item (1) |
| `F_init ≪ ν_B` a non-zero initial flow | ⚠ weakened: only its mass is carried, as `z` with `hz : z = ∫ e dν` and `hz0 : 0 < z`. See SCOPE — `hz` *is* Step 0's `E(𝒮) = F_init(𝒮)`, assumed |
| `κ ≪ ν_B` non-zero, possibly unnormalized, with known density | ✓ carried: `k : α → ℝ`, `Integrable k ν`, `0 ≤ᵐ[ν] k`, `ht : t = ∫ k dν`, `ht0 : 0 < t` |
| `q ∈ [1,+∞]` | ⚠ narrowed: `q : ℝ` with `1 ≤ q`. `q = +∞` is not covered |
| `ν_T` a probability measure, `ν_B ≪ ν_T`, `dν_B/dν_T ∈ L^∞(ν_T)` | ⚠ restated: `hdom : ν ≤ (M : ℝ≥0∞) • ν_T` for `M : ℝ≥0`, which is the domination and the `L^∞` bound at once. That `ν_T` is a probability is never used |
| `E := F_init + F⋆_← − F⋆_out` with `(π⋆, f⋆_out)` a generative flow | ⚠ weakened: only the density `e : α → ℝ` with `Integrable e ν`. No kernel, no outflow |
| inference at `F_term = κ̂ := E⁺` | ✓ carried: `κ̂` is `fun x => max (e x) 0`, its mass `zhat` with `hzh` |
| the loss is `𝓛 = ‖e − k‖_{L^q(ν_T)}` (`proofs.tex:193`) | ✓ carried, as `stableLoss`, plus `MemLp (e − k) (ofReal q) ν_T` — the paper's tacit "the loss is finite" |
| `theo:negative_control` for term (i) (`proofs.tex:213–216`) | ✗ **external**: hypothesis `hNC`. The paper quotes it from `\citet{brunswicEGF}` and does not prove it; neither does this library |
| the triangle inequality for TV (`proofs.tex:209–212`) | ⚠ hypothesis `htri`, since `s_τ` is abstract. `tvD_triangle` proves it whenever `s_τ` has a `ν_B`-density |
| conclusion `equ:mass_floor` | ✓ `mass_floor` |
| conclusion `equ:stable_bound` with `C = 2C₀/t` | ✓ `stable_bound`, `stableConst` |
| items (2) and (3) of the theorem | ✗ not formalized — see SCOPE |

## SCOPE (disclosed)

* **Items (2) and (3) are not here.** (2) is the vanishing of the infimum over an `L^p`-universal
  family at a matched initial mass, and needs `def:universality` and a second Hölder transfer;
  (3) is the initial-family statement `equ:joint_infimum`, which needs (2) and a scaling argument
  on the pair `(F_init, (z/t)κ)`. Neither is attempted, and nothing below is used by them.
* **`theo:negative_control` is an external input.** It is `proofs.tex:52–61`, quoted from
  `\citet{brunswicEGF}`, and the paper gives no proof of it. It appears here **only** as the
  hypothesis `hNC : tvNC ≤ (∫ e⁻ dν) / zhat` of `tv_le_two_fmL1` and `stable_bound`, in exactly
  the form `δF_init(𝒮)/F̂_term(𝒮)` that Step 2 consumes. It is not proved, not axiomatized, and
  not weakened: term (i) is carried, not dropped.
* **The sampler is abstract.** `s_τ` is a real number's worth of information here: `tv` standing
  for `TV(s_τ ‖ κ/t)` and `tvNC` for `TV(s_τ ‖ κ̂/κ̂(𝒮))`, related by `htri`. This is the honest
  reading of a quantity the appendix obtains from a Markov chain the library does not build
  (`CLAUDE.md`'s first obstruction). The cost is that `htri` is assumed rather than derived; the
  price is bounded by `tvD_triangle`, which derives it as soon as the law of `s_τ` is `f·ν_B`.
* **Step 0's mass identity `E(𝒮) = F_init(𝒮)` is assumed, not derived.** The paper gets it from
  `F⋆_←(𝒮) = F⋆_out π⋆(𝒮) = F⋆_out(𝒮)`, which is the statement that `π⋆` is a Markov kernel. No
  kernel is modelled here, so `z` is introduced with `hz : z = ∫ e dν` and read as `F_init(𝒮)`.
  Everything downstream of that reading — `equ:mass_floor` in particular, whose left-hand side is
  `|F_init(𝒮) − κ(𝒮)|` — inherits the assumption.
* **`q = +∞` is not covered.** The paper's Step 3 handles it in two extra lines
  (`proofs.tex:239`), by `Δ ≤ ν_B(𝒮)‖e−k‖_{L^∞(ν_B)}` and `‖·‖_{L^∞(ν_B)} ≤ ‖·‖_{L^∞(ν_T)}`.
  Here `q : ℝ` with `1 ≤ q`, so `C₀` is `ν_B(𝒮)^{1−1/q} M^{1/q}` with both exponents real.
* **`‖dν_B/dν_T‖_{L^∞(ν_T)}` is carried in the `∃M` form**, as `ν ≤ (M : ℝ≥0∞) • ν_T`. For
  `ν_B ≪ ν_T` the two are the same statement, and this form needs no Radon–Nikodym derivative and
  no `essSup`. `M` is therefore an upper bound for the paper's `‖dν_B/dν_T‖_{L^∞(ν_T)}`, and
  `holderConst` is monotone in it, so the bound proved is the paper's bound at the least
  admissible `M` and weaker at any other.
* **`tvD_normalization` needs less than the paper's `equ:normalization_lemma` states.** The middle
  bound `TV(α/a ‖ β/b) ≤ (‖α−β‖ + |a−b|)/(2a)` holds for *any* `a > 0`, `b = β(𝒮) > 0` and
  `β ≥ 0`; that `a` is `α(𝒮)` is used only in the second inequality
  `≤ ‖α−β‖/a`, through `|a−b| ≤ ‖α−β‖_{L¹}`. The hypothesis is therefore dropped from the first
  lemma and kept in `tvD_normalization_le`. This is a generalization, not a weakening.
* **No `sorry`.** Every declaration below is closed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## Total variation between two densities -/

/-- **The ½-convention total variation of `app:notation`**, read between two densities against a
common dominating measure: `TV(f·ν ‖ g·ν) = ½ ∫ |f − g| dν`. This is the appendix's own
definition, `\TV(\mu\|\nu) := \tfrac12\int|\frac{d\mu}{d\rho}-\frac{d\nu}{d\rho}|d\rho`
(`proofs.tex:22`), with `ρ = ν`. -/
noncomputable def tvD (ν : Measure α) (f g : α → ℝ) : ℝ := (1 / 2) * ∫ x, |f x - g x| ∂ν

theorem tvD_nonneg (ν : Measure α) (f g : α → ℝ) : 0 ≤ tvD ν f g :=
  mul_nonneg (by norm_num) (integral_nonneg fun _ => abs_nonneg _)

theorem tvD_comm (ν : Measure α) (f g : α → ℝ) : tvD ν f g = tvD ν g f := by
  refine congrArg (fun s => (1 / 2 : ℝ) * s) (integral_congr_ae ?_)
  filter_upwards with x
  exact abs_sub_comm _ _

/-- **The triangle inequality Step 2 opens with** (`proofs.tex:209–212`), for densities against a
common measure. It is what discharges the hypothesis `htri` of `tv_le_two_fmL1` whenever the law
of `s_τ` is itself `f·ν_B`. -/
theorem tvD_triangle {ν : Measure α} {f₁ f₂ f₃ : α → ℝ}
    (h₁ : Integrable (fun x => f₁ x - f₂ x) ν) (h₂ : Integrable (fun x => f₂ x - f₃ x) ν) :
    tvD ν f₁ f₃ ≤ tvD ν f₁ f₂ + tvD ν f₂ f₃ := by
  have hfh : Integrable (fun x => f₁ x - f₃ x) ν := by
    refine (h₁.add h₂).congr ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    ring
  have hsum : Integrable (fun x => |f₁ x - f₂ x| + |f₂ x - f₃ x|) ν := h₁.abs.add h₂.abs
  have hmono : ∫ x, |f₁ x - f₃ x| ∂ν ≤ ∫ x, (|f₁ x - f₂ x| + |f₂ x - f₃ x|) ∂ν :=
    integral_mono hfh.abs hsum fun x => abs_sub_le _ _ _
  rw [integral_add h₁.abs h₂.abs] at hmono
  unfold tvD
  linarith

/-- **`equ:normalization_lemma`, first inequality** (`proofs.tex:217–220`): for `α = f·ν` and
`β = g·ν` non-negative and finite with masses `a, b > 0`,

  `TV(α/a ‖ β/b) ≤ (‖α − β‖_{L¹} + |a − b|)/(2a)`,

by the paper's own splitting `β/b − α/a = (β − α)/a + β(1/b − 1/a)`. Only `b = β(𝒮)` is needed;
see this file's SCOPE. -/
theorem tvD_normalization {ν : Measure α} {f g : α → ℝ} {a b : ℝ}
    (hf : Integrable f ν) (hg : Integrable g ν) (hg0 : 0 ≤ᵐ[ν] g)
    (hb : b = ∫ x, g x ∂ν) (ha0 : 0 < a) (hb0 : 0 < b) :
    tvD ν (fun x => f x / a) (fun x => g x / b)
      ≤ ((∫ x, |f x - g x| ∂ν) + |a - b|) / (2 * a) := by
  have hane : a ≠ 0 := ne_of_gt ha0
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hfg : Integrable (fun x => f x - g x) ν := hf.sub hg
  have hA : Integrable (fun x => |f x - g x| / a) ν := hfg.abs.div_const a
  have hB : Integrable (fun x => g x * |1 / a - 1 / b|) ν := hg.mul_const _
  have hint : Integrable (fun x => |f x - g x| / a + g x * |1 / a - 1 / b|) ν := hA.add hB
  have hlhs : Integrable (fun x => f x / a - g x / b) ν := (hf.div_const a).sub (hg.div_const b)
  have hpt : ∀ᵐ x ∂ν, |f x / a - g x / b| ≤ |f x - g x| / a + g x * |1 / a - 1 / b| := by
    filter_upwards [hg0] with x hx
    have key : f x / a - g x / b = (f x - g x) / a + g x * (1 / a - 1 / b) := by
      field_simp
      ring
    have e1 : |(f x - g x) / a| = |f x - g x| / a := by rw [abs_div, abs_of_pos ha0]
    have e2 : |g x * (1 / a - 1 / b)| = g x * |1 / a - 1 / b| := by
      rw [abs_mul, abs_of_nonneg hx]
    calc |f x / a - g x / b| = |(f x - g x) / a + g x * (1 / a - 1 / b)| := by rw [key]
      _ ≤ |(f x - g x) / a| + |g x * (1 / a - 1 / b)| := abs_add_le _ _
      _ = |f x - g x| / a + g x * |1 / a - 1 / b| := by rw [e1, e2]
  have hmono : ∫ x, |f x / a - g x / b| ∂ν
      ≤ ∫ x, (|f x - g x| / a + g x * |1 / a - 1 / b|) ∂ν :=
    integral_mono_ae hlhs.abs hint hpt
  rw [integral_add hA hB, integral_div, integral_mul_const, ← hb] at hmono
  have hb' : b * |1 / a - 1 / b| = |a - b| / a := by
    have : (1 : ℝ) / a - 1 / b = (b - a) / (a * b) := by field_simp
    rw [this, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
    field_simp
  rw [hb'] at hmono
  have hsplit : ((∫ x, |f x - g x| ∂ν) + |a - b|) / (2 * a)
      = (1 / 2 : ℝ) * ((∫ x, |f x - g x| ∂ν) / a + |a - b| / a) := by
    field_simp
  unfold tvD
  rw [hsplit]
  linarith

/-- **`equ:normalization_lemma`, second inequality** (`proofs.tex:217–220`):
`TV(α/a ‖ β/b) ≤ ‖α − β‖_{L¹}/a`, by `|a − b| ≤ ‖α − β‖_{L¹}`. Here `a` must be `α(𝒮)`. -/
theorem tvD_normalization_le {ν : Measure α} {f g : α → ℝ} {a b : ℝ}
    (hf : Integrable f ν) (hg : Integrable g ν) (hg0 : 0 ≤ᵐ[ν] g)
    (ha : a = ∫ x, f x ∂ν) (hb : b = ∫ x, g x ∂ν) (ha0 : 0 < a) (hb0 : 0 < b) :
    tvD ν (fun x => f x / a) (fun x => g x / b) ≤ (∫ x, |f x - g x| ∂ν) / a := by
  have hmain := tvD_normalization hf hg hg0 hb ha0 hb0
  have habs : |a - b| ≤ ∫ x, |f x - g x| ∂ν := by
    rw [ha, hb, ← integral_sub hf hg]
    exact abs_integral_le_integral_abs
  have hstep : ((∫ x, |f x - g x| ∂ν) + |a - b|) / (2 * a) ≤ (∫ x, |f x - g x| ∂ν) / a := by
    rw [← sub_nonneg]
    have key : (∫ x, |f x - g x| ∂ν) / a - ((∫ x, |f x - g x| ∂ν) + |a - b|) / (2 * a)
        = ((∫ x, |f x - g x| ∂ν) - |a - b|) / (2 * a) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (by linarith) (by positivity)
  linarith

/-! ## Step 0 and Step 1 -/

/-- **Step 1's first pointwise inequality** (`proofs.tex:204`): `k ≥ 0` gives `e⁻ ≤ |e − k|`,
because on `{e < 0}` one has `|e − k| = k − e ≥ −e`. -/
theorem negPart_le_abs_sub {x y : ℝ} (hy : 0 ≤ y) : max (-x) 0 ≤ |x - y| := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right (by linarith)]
    exact abs_nonneg _
  · rw [max_eq_left (by linarith)]
    have h2 : y - x ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith

/-- **Step 1's second pointwise inequality** (`proofs.tex:204`): `x ↦ x⁺` is `1`-Lipschitz and
`k⁺ = k`, so `|e⁺ − k| ≤ |e − k|`. -/
theorem abs_sub_posPart_le {x y : ℝ} (hy : 0 ≤ y) : |y - max x 0| ≤ |x - y| := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, abs_sub_comm]
  · rw [max_eq_right h, sub_zero, abs_of_nonneg hy]
    have h2 : y - x ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith

variable {ν : Measure α} {e k : α → ℝ}

/-- **`equ:mass_identity`, Step 0** (`proofs.tex:200–202`): `E⁺` and `E⁻` having disjoint
supports and `E(𝒮) = z`, the corrected terminal flow has mass `κ̂(𝒮) = z + E⁻(𝒮) ≥ z`. In
densities this is `∫ e⁺ = ∫ e + ∫ e⁻`. -/
theorem posPart_mass (he : Integrable e ν) :
    ∫ x, max (e x) 0 ∂ν = (∫ x, e x ∂ν) + ∫ x, max (-e x) 0 ∂ν := by
  rw [← integral_add he he.neg_part]
  refine integral_congr_ae ?_
  filter_upwards with x
  rcases le_total 0 (e x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), add_zero]
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

/-- **`equ:two_dominations`, first half** (`proofs.tex:205–207`): `δF_init(𝒮) = E⁻(𝒮) ≤ Δ`. -/
theorem negMass_le (he : Integrable e ν) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k) :
    ∫ x, max (-e x) 0 ∂ν ≤ ∫ x, |e x - k x| ∂ν := by
  refine integral_mono_ae he.neg_part (he.sub hk).abs ?_
  filter_upwards [hk0] with x hx
  exact negPart_le_abs_sub hx

/-- **`equ:two_dominations`, second half** (`proofs.tex:205–207`):
`‖κ̂ − κ‖_{L¹(ν_B)} ≤ Δ`. -/
theorem hatDist_le (he : Integrable e ν) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k) :
    ∫ x, |k x - max (e x) 0| ∂ν ≤ ∫ x, |e x - k x| ∂ν := by
  refine integral_mono_ae (hk.sub he.pos_part).abs (he.sub hk).abs ?_
  filter_upwards [hk0] with x hx
  exact abs_sub_posPart_le hx

/-- **`equ:mass_defect`** (`proofs.tex:226–228`): `|z − t| = |∫(e − k) dν_B| ≤ Δ`. -/
theorem mass_defect_le (he : Integrable e ν) (hk : Integrable k ν) :
    |(∫ x, e x ∂ν) - ∫ x, k x ∂ν| ≤ ∫ x, |e x - k x| ∂ν := by
  rw [← integral_sub he hk]
  exact abs_integral_le_integral_abs

/-! ## Step 2 -/

/-- **Term (ii) of Step 2** (`proofs.tex:217–221`): `TV(κ/t ‖ κ̂/κ̂(𝒮)) ≤ Δ/t`, by
`equ:normalization_lemma` at `α = κ`, `β = κ̂` and `equ:two_dominations`. -/
theorem normalization_bound (he : Integrable e ν) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k)
    {t zhat : ℝ} (ht : t = ∫ x, k x ∂ν) (hzh : zhat = ∫ x, max (e x) 0 ∂ν) (ht0 : 0 < t)
    (hzh0 : 0 < zhat) :
    tvD ν (fun x => k x / t) (fun x => max (e x) 0 / zhat) ≤ (∫ x, |e x - k x| ∂ν) / t := by
  have h1 := tvD_normalization_le (f := k) (g := fun x => max (e x) 0) hk he.pos_part
    (by filter_upwards with x; exact le_max_right _ _) ht hzh ht0 hzh0
  refine h1.trans ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hatDist_le he hk hk0) (by positivity)

/-- **`equ:tv_chain` closed at `2Δ/t`, Step 2 in full** (`proofs.tex:209–232`):

  `TV(s_τ ‖ κ/t) ≤ Δ/(z + Δ) + Δ/t ≤ 2Δ/t`,

with `Δ := ‖e − k‖_{L¹(ν_B)}`. Term (i) enters through `hNC`, which is
**`theo:negative_control`** (`proofs.tex:52–61`) — quoted by the paper from `\citet{brunswicEGF}`
and proved nowhere, here or there. Term (ii) is `normalization_bound`. The step
`u/(z+u) ≤ Δ/(z+Δ)` is the monotonicity of `x ↦ x/(z+x)` on `[0,∞)`, and `z + Δ ≥ t` is
`equ:mass_defect`. -/
theorem tv_le_two_fmL1 (he : Integrable e ν) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k)
    {z t zhat tv tvNC : ℝ} (hz : z = ∫ x, e x ∂ν) (ht : t = ∫ x, k x ∂ν)
    (hzh : zhat = ∫ x, max (e x) 0 ∂ν) (hz0 : 0 < z) (ht0 : 0 < t)
    (hNC : tvNC ≤ (∫ x, max (-e x) 0 ∂ν) / zhat)
    (htri : tv ≤ tvNC + tvD ν (fun x => max (e x) 0 / zhat) (fun x => k x / t)) :
    tv ≤ 2 * (∫ x, |e x - k x| ∂ν) / t := by
  set Δ : ℝ := ∫ x, |e x - k x| ∂ν
  set u : ℝ := ∫ x, max (-e x) 0 ∂ν with hu
  have hu0 : 0 ≤ u := integral_nonneg fun _ => le_max_right _ _
  have huΔ : u ≤ Δ := negMass_le he hk hk0
  have hzhat : zhat = z + u := by rw [hzh, hz, hu, posPart_mass he]
  have hzh0 : 0 < zhat := by rw [hzhat]; linarith
  have hmono : u / (z + u) ≤ Δ / (z + Δ) := by
    have h1 : (0 : ℝ) < z + u := by linarith
    have h2 : (0 : ℝ) < z + Δ := by linarith
    rw [← sub_nonneg]
    have key : Δ / (z + Δ) - u / (z + u) = z * (Δ - u) / ((z + Δ) * (z + u)) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (by nlinarith) (by positivity)
  have hzt : t ≤ z + Δ := by
    have hmd := mass_defect_le (e := e) (k := k) he hk
    rw [← hz, ← ht] at hmd
    have h2 : t - z ≤ |z - t| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have hi : tvNC ≤ Δ / t := by
    refine hNC.trans ?_
    rw [hzhat]
    refine hmono.trans ?_
    gcongr
  have hii : tvD ν (fun x => max (e x) 0 / zhat) (fun x => k x / t) ≤ Δ / t := by
    rw [tvD_comm]
    exact normalization_bound he hk hk0 ht hzh ht0 hzh0
  have hfin : tv ≤ Δ / t + Δ / t := le_trans htri (by linarith)
  have heq : Δ / t + Δ / t = 2 * Δ / t := by ring
  linarith

/-! ## Step 3 -/

/-- **Step 3, first Hölder** (`proofs.tex:236`): on a finite measure,
`∫ h dν ≤ ν(𝒮)^{1−1/q} ‖h‖_{L^q(ν)}` for `h ≥ 0` and `1 ≤ q < ∞`, by Hölder against the constant
`1` with the conjugate exponents `q` and `q/(q−1)`. -/
theorem integral_le_measure_rpow_mul {q : ℝ} (hq : 1 ≤ q) (ν : Measure α) [IsFiniteMeasure ν]
    {h : α → ℝ} (hh0 : 0 ≤ᵐ[ν] h) (hmem : MemLp h (ENNReal.ofReal q) ν) :
    ∫ x, h x ∂ν ≤ ν.real Set.univ ^ (1 - 1 / q) * (∫ x, h x ^ q ∂ν) ^ (1 / q) := by
  rcases eq_or_lt_of_le hq with hq1 | hq1
  · subst_vars
    simp
  · set q' : ℝ := q / (q - 1) with hq'
    have hpq : q.HolderConjugate q' := by
      refine Real.holderConjugate_iff.mpr ⟨hq1, ?_⟩
      rw [hq']
      field_simp
      ring
    have hg : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal q') ν := memLp_const 1
    have key := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) hpq hh0
      (Filter.Eventually.of_forall fun _ => zero_le_one) hmem hg
    simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul, mul_one] at key
    have hconj : 1 / q' = 1 - 1 / q := by
      have hsum := hpq.one_div_add_one_div
      norm_num at hsum
      simp only [one_div]
      linarith
    rw [hconj] at key
    calc ∫ x, h x ∂ν
        ≤ (∫ x, h x ^ q ∂ν) ^ (1 / q) * ν.real Set.univ ^ (1 - 1 / q) := key
      _ = ν.real Set.univ ^ (1 - 1 / q) * (∫ x, h x ^ q ∂ν) ^ (1 / q) := mul_comm _ _

/-- **Step 3, the change of measure** (`proofs.tex:237`): with `ν_B ≤ M ν_T`, an integral of a
non-negative function against `ν_B` is at most `M` times its integral against `ν_T`. This is the
paper's `∫ φ dν_B = ∫ φ (dν_B/dν_T) dν_T ≤ ‖dν_B/dν_T‖_{L^∞(ν_T)} ∫ φ dν_T`, in the form that
needs no Radon–Nikodym derivative. -/
theorem integral_le_of_le_smul {νT : Measure α} {M : ℝ≥0} (hdom : ν ≤ (M : ℝ≥0∞) • νT)
    {f : α → ℝ} (hf0 : 0 ≤ᵐ[νT] f) (hint : Integrable f νT) :
    ∫ x, f x ∂ν ≤ (M : ℝ) * ∫ x, f x ∂νT := by
  have hint' : Integrable f ((M : ℝ≥0∞) • νT) := hint.smul_measure (by simp)
  have hf0' : 0 ≤ᵐ[(M : ℝ≥0∞) • νT] f := Measure.ae_smul_measure hf0 _
  have hle := integral_mono_measure hdom hf0' hint'
  rwa [integral_smul_measure, smul_eq_mul, ENNReal.coe_toReal] at hle

/-- **`equ:stable_constants`, `C₀`** (`proofs.tex:152–156`):
`C₀ = ν_B(𝒮)^{1−1/q} ‖dν_B/dν_T‖^{1/q}_{L^∞(ν_T)}`, with the `L^∞` norm carried by `M`. -/
noncomputable def holderConst (ν : Measure α) (M : ℝ≥0) (q : ℝ) : ℝ :=
  ν.real Set.univ ^ (1 - 1 / q) * (M : ℝ) ^ (1 / q)

/-- **`equ:stable_constants`, `C`** (`proofs.tex:152–156`): `C = 2C₀/κ(𝒮)`. -/
noncomputable def stableConst (ν : Measure α) (M : ℝ≥0) (q t : ℝ) : ℝ :=
  2 * holderConst ν M q / t

/-- **The stable loss `𝓛` of `equ:FMloss`** as `proofs.tex:193` reads it,
`𝓛 = ‖e − k‖_{L^q(ν_T)}`, at `q < ∞`. -/
noncomputable def stableLoss (νT : Measure α) (q : ℝ) (e k : α → ℝ) : ℝ :=
  (∫ x, |e x - k x| ^ q ∂νT) ^ (1 / q)

/-- **Step 3 in full** (`proofs.tex:234–239`): `Δ ≤ C₀ 𝓛`, the two Hölder applications composed.
The constant produced is `ν_B(𝒮)^{1−1/q} M^{1/q}`, which is `equ:stable_constants`' `C₀` on the
nose. -/
theorem fmL1_le_holderConst_mul_loss {νT : Measure α} {M : ℝ≥0} {q : ℝ} (hq : 1 ≤ q)
    [IsFiniteMeasure ν] (hdom : ν ≤ (M : ℝ≥0∞) • νT)
    (hmem : MemLp (fun x => e x - k x) (ENNReal.ofReal q) νT) :
    ∫ x, |e x - k x| ∂ν ≤ holderConst ν M q * stableLoss νT q e k := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqinv : 0 ≤ 1 / q := by positivity
  have hne0 : ENNReal.ofReal q ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hmemν : MemLp (fun x => e x - k x) (ENNReal.ofReal q) ν :=
    MemLp.mono_measure hdom (hmem.smul_measure (by simp))
  have hmemabs : MemLp (fun x => |e x - k x|) (ENNReal.ofReal q) ν := by
    simpa [Real.norm_eq_abs] using hmemν.norm
  have hintT : Integrable (fun x => |e x - k x| ^ q) νT := by
    have hI := hmem.integrable_norm_rpow hne0 ENNReal.ofReal_ne_top
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hq0.le] using hI
  have h1 := integral_le_measure_rpow_mul (h := fun x => |e x - k x|) hq ν
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hmemabs
  have h2 : ∫ x, |e x - k x| ^ q ∂ν ≤ (M : ℝ) * ∫ x, |e x - k x| ^ q ∂νT :=
    integral_le_of_le_smul hdom
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) q) hintT
  have hIT : 0 ≤ ∫ x, |e x - k x| ^ q ∂νT :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) q
  have h3 : (∫ x, |e x - k x| ^ q ∂ν) ^ (1 / q)
      ≤ ((M : ℝ) * ∫ x, |e x - k x| ^ q ∂νT) ^ (1 / q) :=
    Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) q) h2 hqinv
  have h4 : ((M : ℝ) * ∫ x, |e x - k x| ^ q ∂νT) ^ (1 / q)
      = (M : ℝ) ^ (1 / q) * (∫ x, |e x - k x| ^ q ∂νT) ^ (1 / q) :=
    Real.mul_rpow (by positivity) hIT
  have hA : (0 : ℝ) ≤ ν.real Set.univ ^ (1 - 1 / q) := by positivity
  calc ∫ x, |e x - k x| ∂ν
      ≤ ν.real Set.univ ^ (1 - 1 / q) * (∫ x, |e x - k x| ^ q ∂ν) ^ (1 / q) := h1
    _ ≤ ν.real Set.univ ^ (1 - 1 / q) * ((M : ℝ) * ∫ x, |e x - k x| ^ q ∂νT) ^ (1 / q) :=
        mul_le_mul_of_nonneg_left h3 hA
    _ = holderConst ν M q * stableLoss νT q e k := by
        rw [h4, holderConst, stableLoss, mul_assoc]

/-! ## The two bounds of item (1) -/

/-- **`equ:mass_floor`** (`proofs.tex:164–166`), the second display of item (1) of
**`theo:RL_CV_bound_full`**:

  `|F_init(𝒮) − κ(𝒮)| ≤ C₀ 𝓛` .

`z` is `F_init(𝒮)` by Step 0's `E(𝒮) = F_init(𝒮)`, which is the hypothesis `hz` — see this
file's SCOPE. -/
theorem mass_floor {νT : Measure α} {M : ℝ≥0} {q z t : ℝ} (hq : 1 ≤ q) [IsFiniteMeasure ν]
    (hdom : ν ≤ (M : ℝ≥0∞) • νT) (hmem : MemLp (fun x => e x - k x) (ENNReal.ofReal q) νT)
    (he : Integrable e ν) (hk : Integrable k ν) (hz : z = ∫ x, e x ∂ν) (ht : t = ∫ x, k x ∂ν) :
    |z - t| ≤ holderConst ν M q * stableLoss νT q e k := by
  have h1 := mass_defect_le (e := e) (k := k) he hk
  rw [← hz, ← ht] at h1
  exact h1.trans (fmL1_le_holderConst_mul_loss hq hdom hmem)

/-- **`equ:stable_bound`** (`proofs.tex:160–162`), the first display of item (1) of
**`theo:RL_CV_bound_full`**:

  `TV(s_τ ‖ κ/t) ≤ C 𝓛`,  `C = 2C₀/t` .

`tv` is `TV(s_τ ‖ κ/t)` and `tvNC` is `TV(s_τ ‖ κ̂/κ̂(𝒮))`; `hNC` is
**`theo:negative_control`**, an external input the paper quotes and does not prove, and `htri`
is the triangle inequality Step 2 opens with, which `tvD_triangle` supplies for any sampler with
a `ν_B`-density. Both are disclosed in this file's SCOPE. -/
theorem stable_bound {νT : Measure α} {M : ℝ≥0} {q z t zhat tv tvNC : ℝ} (hq : 1 ≤ q)
    [IsFiniteMeasure ν] (hdom : ν ≤ (M : ℝ≥0∞) • νT)
    (hmem : MemLp (fun x => e x - k x) (ENNReal.ofReal q) νT)
    (he : Integrable e ν) (hk : Integrable k ν) (hk0 : 0 ≤ᵐ[ν] k)
    (hz : z = ∫ x, e x ∂ν) (ht : t = ∫ x, k x ∂ν) (hzh : zhat = ∫ x, max (e x) 0 ∂ν)
    (hz0 : 0 < z) (ht0 : 0 < t)
    (hNC : tvNC ≤ (∫ x, max (-e x) 0 ∂ν) / zhat)
    (htri : tv ≤ tvNC + tvD ν (fun x => max (e x) 0 / zhat) (fun x => k x / t)) :
    tv ≤ stableConst ν M q t * stableLoss νT q e k := by
  have h1 := tv_le_two_fmL1 he hk hk0 hz ht hzh hz0 ht0 hNC htri
  have h2 := fmL1_le_holderConst_mul_loss (ν := ν) (e := e) (k := k) hq hdom hmem
  have h3 : (2 : ℝ) * ∫ x, |e x - k x| ∂ν ≤ 2 * (holderConst ν M q * stableLoss νT q e k) := by
    linarith
  have h4 : 2 * (∫ x, |e x - k x| ∂ν) / t
      ≤ 2 * (holderConst ν M q * stableLoss νT q e k) / t := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr ht0.le)
  have h5 : 2 * (holderConst ν M q * stableLoss νT q e k) / t
      = stableConst ν M q t * stableLoss νT q e k := by
    rw [stableConst]
    ring
  linarith

end GFNBounds.Core
