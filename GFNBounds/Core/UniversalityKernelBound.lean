import GFNBounds.Core.StrongUniversality

/-!
# The quantitative universality bound, read at the density action of a Markov kernel

**`theo:universality_L2_full`** — statement `proofs.tex:65–74`, proof `proofs.tex:76–115`
(Theorem 15 of the ICLR build) — the display `equ:universality_quantitative` (`proofs.tex:70–72`)
and the sentences around it:

> More precisely, let `F_init, F_term ≪ ν_B` be distributions with densities in `L^p(ν_B)`, put
> `θ := f_term − f_init` and let `S := ∑_{n ≥ 0} (P⋆^n − Π)`, so that
> `‖Sθ‖_{L^p(ν_B)} ≤ B_p ‖θ‖_{L^p(ν_B)}`. Then for every `η > 0` the outflow density
> `f_out^η := (η − Sθ)⁺` belongs to `Θ` and satisfies
>
>   `‖δf_init‖_{L^p(ν_B)} + ‖δf_term‖_{L^p(ν_B)} ≤ 2 (1 + ‖π⋆‖_{L^p(ν_B)}) ‖(Sθ − η)⁺‖_{L^p(ν_B)}
>     → 0` as `η → +∞`.
>
> Furthermore, if `p = +∞` then `Θ` is strongly universal: taking `η := ‖Sθ‖_{L^∞(ν_B)}` gives
> `δf_init = δf_term = 0`, and the flow-matching constraint holds exactly.

`Core.Universality.residuals_le` proves the display on an abstract Banach lattice, for a
hypothesised operator `P` with `Mixing P Pi`, `P one = one` and `Pi θ = 0`. `Core.Kernel`
constructs the paper's `P⋆` from a Markov kernel and discharges the last two of those; `Core.Flow`
discharges `Mixing` from summability. Nothing composed them *at the display*: the kernel-level
theorems of `Core.Kernel` state only the qualitative conclusion. This file is that composition,
and it adds the one analytic fact the paper's arrow needs at `p = +∞` — that the truncation is
eventually `0` there — so that the limit is certified at **every** `p ∈ [1, +∞]`, as the display
claims, and not only at `p < +∞`.

## What is proved

| | |
|---|---|
| `coeFn_liftedOutflow` | the a.e. representative of `f_out^η` is `x ↦ max (η − Sθ x) 0`, the paper's `(η − Sθ)⁺` |
| `truncation_eq_zero_top` | at `p = +∞`, `ψ_η = 0` once `‖Sθ‖_∞ ≤ η` (`proofs.tex:114`) |
| `tendsto_truncation_norm_all` | `‖ψ_η‖_{L^p} → 0` as `η → +∞`, for every `p`, `p = +∞` included |
| `residuals_le_of_kernel` | at `P := P⋆` built from the kernel: `f_out^η ≥ 0`, `‖Sθ‖ ≤ B_p ‖θ‖`, the display with `2 (1 + ‖P⋆‖)`, and with `2 (1 + C)` |
| `tendsto_residuals_of_kernel` | the display's arrow: `‖δf_init‖ + ‖δf_term‖ → 0` as `η → +∞`, every `p` |
| `defect_eq_zero_of_kernel_top` | at `p = +∞` and `η := ‖Sθ‖_∞`: the defect is `0`, flow matching holds exactly |
| `residuals_eq_zero_of_kernel_top` | at `p = +∞` and `η := ‖Sθ‖_∞`: `δf_init = δf_term = 0` |

`coeFn_truncation` (`Core.UniversalityLp`) already identifies `ψ_η` with the paper's `(Sθ − η)⁺`
pointwise, so the norm on the right of the display is the paper's.

## SCOPE (disclosed)

**This file certifies the display and its arrow, not the theorem's first paragraph.** Weak
`L^p`-universality from the kernel is `Core.Kernel.weaklyUniversal_of_kernel`; strong
universality at `p = +∞` and its transfer to every `L^r` are `Core.StrongUniversality`. Nothing
here re-proves them.

**Ergodicity is split in two, as in `Core.Kernel`.** Its invariance half, `ν_B π⋆ = ν_B`, is
`hinv`: assumed, and used — it is what makes `𝟏` a `0`-flow and `∫ P⋆ f = ∫ f`. Its uniqueness
half ("the only `μ ≪ ν_B` it fixes are the multiples of `ν_B`") is dropped: `Π` is the *mean*
projection `meanProj`, and uniqueness has moved into the summability of `‖P⋆^n − Π‖` against it
(`Core.Flow.eq_meanProj_of_invariant`).

**The boundedness hypothesis `hb` is redundant under `hinv`, and carried because the paper
carries it.** For an *invariant* Markov kernel, `IsBoundedDensityAction κ ν p 1` holds at every
`p ∈ [1, +∞]`: at `p = +∞`, `(f ν) π⋆ ≤ ‖f‖_∞ ν π⋆ = ‖f‖_∞ ν`; at finite `p`, by duality
against the function action, Jensen for each `π⋆(x, ·)` and invariance; signed `f` through
`|P⋆ f| ≤ P⋆ |f|`. The operator norm is then `≤ 1`, and exactly `1` when `ν ≠ 0`, since
`P⋆ 𝟏 = 𝟏`. **This is not proved in this library**, and `hb` is not dropped: the theorem
quantifies over it as the paper does (`universality.tex:5–7`, `proofs.tex:67`). The paper's
"a genuine hypothesis beyond `p = 1`" (`universality.tex:27–28`) is too cautious for the kernels
the theorem is about.

**`‖π⋆‖_{L^p(ν_B)}` is read as the operator norm of the density-action CLM.** The paper defines
`‖π⋆‖_{L^p(ν_B)} := sup ‖fπ⋆‖/‖f‖` (`proofs.tex:17–21`), `f π⋆` being the density of the push —
which is `densityActionCLM` by construction. The display is stated both with that norm, which is
the paper's constant on the nose, and with the explicit bound `C` of the hypothesis.

**`η` ranges over all of `ℝ`**, not only `η > 0`. The bound holds for every real `η`, so this is
the paper's quantifier widened in the safe direction; the construction's `f_out^η ≥ 0` holds for
every `η` too.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` a measured Polish space, `ν_B` finite | ⚠ weakened: any `MeasurableSpace α` with `[IsFiniteMeasure ν]`; Polish is not consumed |
| `π⋆` a Markov kernel | ✓ `κ` with `[IsMarkovKernel κ]` |
| `ν_B π⋆ = ν_B` (in the statement through `ν_B`-ergodicity, `universality.tex:22–23`; used at `proofs.tex:100`) | ✓ `hinv : ν.bind ⇑κ = ν` |
| finite `L^p(ν_B) → L^p(ν_B)` operator norm | ✓ `hb : IsBoundedDensityAction κ ν p C`, constant explicit; redundant under `hinv` (norm `≤ 1`, not proved here), carried because the paper carries it — see SCOPE |
| `π⋆` ergodic | ⚠ weakened: the invariance half is `hinv` (assumed, used); only the uniqueness half is dropped, moved into `hsum` against `meanProj`; see SCOPE |
| summable `L^p`-mixing coefficients, `B_p < ∞` | ✓ `hsum`, against `Π = meanProj ν p` |
| `p ∈ [1, +∞]` | ✓ `[Fact (1 ≤ p)]`; no `p ≠ ⊤` anywhere in this file |
| `F_init, F_term` distributions with densities in `L^p(ν_B)` | ⚠ weakened: `f_init f_term : Lp ℝ p ν` with equal integrals `hmass`; non-negativity is not used |
| `η > 0` | ⚠ weakened: every `η : ℝ` |
| conclusion: `‖Sθ‖ ≤ B_p ‖θ‖` | ✓ `residuals_le_of_kernel`, second conjunct |
| conclusion: `f_out^η := (η − Sθ)⁺ ∈ Θ` | ✓ first conjunct (`≥ 0`; `∈ L^p` by type), representative `coeFn_liftedOutflow` |
| conclusion: `equ:universality_quantitative`, constant `2 (1 + ‖π⋆‖)` | ✓ third conjunct, on the nose; fourth with `2 (1 + C)` |
| conclusion: `→ 0` as `η → +∞` (`proofs.tex:71`, attached to the right side `2 (1 + ‖π⋆‖) ‖(Sθ − η)⁺‖`) | ✓ the right side: `tendsto_truncation_norm_all`; the left side, squeezed: `tendsto_residuals_of_kernel`; every `p` |
| conclusion: `p = +∞`, `η := ‖Sθ‖_∞` gives `δf_init = δf_term = 0` | ✓ `residuals_eq_zero_of_kernel_top` |
| conclusion: …and the flow-matching constraint holds exactly | ✓ `defect_eq_zero_of_kernel_top` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

section Lp

variable {ν : Measure α} [IsFiniteMeasure ν] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`theo:universality_L2_full`'s outflow density, pointwise**: the a.e. representative of the
lifted outflow `f_out^η = (η • 𝟏 - Sθ)⁺` is `x ↦ max (η - Sθ x) 0`, the appendix's
`(η − Sθ)⁺` (`proofs.tex:69`). -/
theorem coeFn_liftedOutflow (P Pi : Lp ℝ p ν →L[ℝ] Lp ℝ p ν) (θ : Lp ℝ p ν) (η : ℝ) :
    ⇑(liftedOutflow P Pi (constOne ν p) θ η)
      =ᵐ[ν] fun x => max (η - Mixing.S P Pi θ x) 0 := by
  have hsmul : ⇑(η • constOne ν p) =ᵐ[ν] fun _ => η := by
    filter_upwards [Lp.coeFn_smul η (constOne ν p), coeFn_constOne (ν := ν) (p := p)]
      with x hx h1
    rw [hx, _root_.Pi.smul_apply, h1, smul_eq_mul, mul_one]
  have hsub : ⇑(η • constOne ν p - Mixing.S P Pi θ)
      =ᵐ[ν] fun x => η - Mixing.S P Pi θ x := by
    filter_upwards [Lp.coeFn_sub (η • constOne ν p) (Mixing.S P Pi θ), hsmul] with x hx hs
    rw [hx, _root_.Pi.sub_apply, hs]
  have hdef : liftedOutflow P Pi (constOne ν p) θ η
      = (η • constOne ν p - Mixing.S P Pi θ) ⊔ 0 := rfl
  filter_upwards [Lp.coeFn_sup (η • constOne ν p - Mixing.S P Pi θ) (0 : Lp ℝ p ν),
    Lp.coeFn_zero ℝ p ν, hsub] with x hsup hzero hx
  show (liftedOutflow P Pi (constOne ν p) θ η) x = _
  rw [hdef, hsup, _root_.Pi.sup_apply, hzero, _root_.Pi.zero_apply, hx]

/-- **Step 3 of `theo:universality_L2_full` at `p = +∞`** (`proofs.tex:114`): for
`η ≥ ‖Sθ‖_{L^∞(ν)}` the truncation `ψ_η = (Sθ − η)⁺` is `0`. -/
theorem truncation_eq_zero_top (P Pi : Lp ℝ ⊤ ν →L[ℝ] Lp ℝ ⊤ ν) (θ : Lp ℝ ⊤ ν) {η : ℝ}
    (hη : ‖Mixing.S P Pi θ‖ ≤ η) : truncation P Pi (constOne ν ⊤) θ η = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [coeFn_truncation P Pi θ η, ae_le_norm_top (Mixing.S P Pi θ)] with x hx hle
  rw [hx, _root_.Pi.zero_apply]
  exact max_eq_right (by linarith)

/-- **Step 3 of `theo:universality_L2_full`, at every exponent**: `‖ψ_η‖_{L^p(ν)} → 0` as
`η → +∞`, for every
`p ∈ [1, +∞]`. Below `+∞` this is dominated convergence (`tendsto_truncation_norm`); at `+∞` the
truncation is eventually `0` (`truncation_eq_zero_top`). -/
theorem tendsto_truncation_norm_all (P Pi : Lp ℝ p ν →L[ℝ] Lp ℝ p ν) (θ : Lp ℝ p ν) :
    Tendsto (fun η : ℝ => ‖truncation P Pi (constOne ν p) θ η‖) atTop (𝓝 0) := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ‖Mixing.S P Pi θ‖] with η hη
    rw [truncation_eq_zero_top P Pi θ hη, norm_zero]
  · exact tendsto_truncation_norm hp P Pi θ

end Lp

/-- **`equ:universality_quantitative` at the kernel's own density action.**

`π⋆` a Markov kernel, `ν` finite and `π⋆`-invariant, `P⋆` bounded on `L^p(ν)` with constant `C`,
summable mixing against the mean projection, and `f_init, f_term ∈ L^p(ν)` of equal total mass.
With `P := P⋆`, `Π := meanProj ν p`, `θ := f_term − f_init` and any `η`:

1. `f_out^η = (η • 𝟏 − Sθ)⁺ ≥ 0`;
2. `‖Sθ‖ ≤ B_p ‖θ‖`;
3. `‖δf_init‖ + ‖δf_term‖ ≤ 2 (1 + ‖P⋆‖) ‖ψ_η‖` — the paper's constant on the nose;
4. the same with the explicit `2 (1 + C)`. -/
theorem residuals_le_of_kernel (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν p hinv hb) ^ n - meanProj ν p‖)
    {f_init f_term : Lp ℝ p ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) (η : ℝ) :
    0 ≤ liftedOutflow (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
        (f_term - f_init) η ∧
    ‖Mixing.S (densityActionCLM κ ν p hinv hb) (meanProj ν p) (f_term - f_init)‖
        ≤ Mixing.B (densityActionCLM κ ν p hinv hb) (meanProj ν p) * ‖f_term - f_init‖ ∧
    ‖resInit (densityActionCLM κ ν p hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
            (f_term - f_init) η)‖
        + ‖resTerm (densityActionCLM κ ν p hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
            (f_term - f_init) η)‖
      ≤ 2 * (1 + ‖densityActionCLM κ ν p hinv hb‖)
        * ‖truncation (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
            (f_term - f_init) η‖ ∧
    ‖resInit (densityActionCLM κ ν p hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
            (f_term - f_init) η)‖
        + ‖resTerm (densityActionCLM κ ν p hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
            (f_term - f_init) η)‖
      ≤ 2 * (1 + C)
        * ‖truncation (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
            (f_term - f_init) η‖ := by
  have hmix := mixing_of_massPreserving (densityActionCLM_constOne κ ν p hinv hb)
    (integral_densityActionCLM κ ν p hinv hb) hsum
  have hres := residuals_le hmix (densityActionCLM_constOne κ ν p hinv hb)
    (meanProj_sub_eq_zero hmass) η
  have hC := norm_densityActionCLM_le κ ν p hinv hb
  refine ⟨liftedOutflow_nonneg _ _ _ _ _, hmix.norm_S_apply_le _, hres, hres.trans ?_⟩
  gcongr

/-- **The arrow of `equ:universality_quantitative`**: at the kernel's density action, the two
residuals of the lifted outflow `f_out^η` vanish together as `η → +∞`, at **every**
`p ∈ [1, +∞]`. -/
theorem tendsto_residuals_of_kernel (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν p hinv hb) ^ n - meanProj ν p‖)
    {f_init f_term : Lp ℝ p ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    Tendsto (fun η : ℝ =>
      ‖resInit (densityActionCLM κ ν p hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
            (f_term - f_init) η)‖
        + ‖resTerm (densityActionCLM κ ν p hinv hb) (f_term - f_init)
          (liftedOutflow (densityActionCLM κ ν p hinv hb) (meanProj ν p) (constOne ν p)
            (f_term - f_init) η)‖) atTop (𝓝 0) := by
  have hlim := (tendsto_truncation_norm_all (densityActionCLM κ ν p hinv hb) (meanProj ν p)
    (f_term - f_init)).const_mul (2 * (1 + ‖densityActionCLM κ ν p hinv hb‖))
  rw [mul_zero] at hlim
  exact squeeze_zero (fun _ => by positivity)
    (fun η => (residuals_le_of_kernel κ ν p hinv hb hsum hmass η).2.2.1) hlim

/-- **The `p = +∞` sentence of `theo:universality_L2_full`, exact flow matching**: "taking
`η := ‖Sθ‖_{L^∞(ν_B)}` gives […] the flow-matching constraint holds exactly" (`proofs.tex:73`),
at the kernel's density action — the defect `D = (P⋆ − Id) f_out^η − θ` of the lifted outflow at
that `η` is `0`. -/
theorem defect_eq_zero_of_kernel_top (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] {C : ℝ} (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν ⊤ C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν ⊤ hinv hb) ^ n - meanProj ν ⊤‖)
    {f_init f_term : Lp ℝ ⊤ ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    defect (densityActionCLM κ ν ⊤ hinv hb) (f_term - f_init)
        (liftedOutflow (densityActionCLM κ ν ⊤ hinv hb) (meanProj ν ⊤) (constOne ν ⊤)
          (f_term - f_init)
          ‖Mixing.S (densityActionCLM κ ν ⊤ hinv hb) (meanProj ν ⊤) (f_term - f_init)‖) = 0 := by
  have hmix := mixing_of_massPreserving (densityActionCLM_constOne κ ν ⊤ hinv hb)
    (integral_densityActionCLM κ ν ⊤ hinv hb) hsum
  rw [defect_eq_truncation hmix (densityActionCLM_constOne κ ν ⊤ hinv hb)
    (meanProj_sub_eq_zero hmass), truncation_eq_zero_top _ _ _ le_rfl, map_zero, sub_zero]

/-- **The `p = +∞` sentence of `theo:universality_L2_full`**: "taking `η := ‖Sθ‖_{L^∞(ν_B)}`
gives `δf_init = δf_term = 0`" (`proofs.tex:73`), at the kernel's density action. -/
theorem residuals_eq_zero_of_kernel_top (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] {C : ℝ} (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν ⊤ C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν ⊤ hinv hb) ^ n - meanProj ν ⊤‖)
    {f_init f_term : Lp ℝ ⊤ ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    resInit (densityActionCLM κ ν ⊤ hinv hb) (f_term - f_init)
        (liftedOutflow (densityActionCLM κ ν ⊤ hinv hb) (meanProj ν ⊤) (constOne ν ⊤)
          (f_term - f_init)
          ‖Mixing.S (densityActionCLM κ ν ⊤ hinv hb) (meanProj ν ⊤) (f_term - f_init)‖) = 0 ∧
    resTerm (densityActionCLM κ ν ⊤ hinv hb) (f_term - f_init)
        (liftedOutflow (densityActionCLM κ ν ⊤ hinv hb) (meanProj ν ⊤) (constOne ν ⊤)
          (f_term - f_init)
          ‖Mixing.S (densityActionCLM κ ν ⊤ hinv hb) (meanProj ν ⊤) (f_term - f_init)‖) = 0 := by
  have hD := defect_eq_zero_of_kernel_top κ ν hinv hb hsum hmass
  simp only [resInit, resTerm, hD, negPart_zero, posPart_zero, and_self]

end GFNBounds.Core
