import GFNBounds.Core.Kernel

/-!
# Strong universality at `p = +∞`, and the transfer of the realized outflow to every `L^r`

**`theo:universality_L2_full`** — statement `proofs.tex:65–74`, proof `proofs.tex:76–115`
(Theorem 15 of the ICLR build) — the last sentence of the statement (`proofs.tex:73`) and the
second half of Step 3 (`proofs.tex:114`):

> Furthermore, if `p = +∞` then `Θ` is strongly universal: taking `η := ‖Sθ‖_{L^∞(ν_B)}` gives
> `δf_init = δf_term = 0`, and the flow-matching constraint `equ:FM_const` holds exactly.

> Let now `p = +∞`. For `η ≥ ‖Sθ‖_{L^∞(ν_B)}` we have `ψ_η = 0`, hence `D = 0` […]: the infimum
> is attained and the flow-matching constraint holds exactly. Since `ν_B` is finite,
> `f_out^η ∈ L^∞(ν_B) ⊂ L^r(ν_B)` for every `r ∈ [1,+∞]`, so the infimum is attained in every
> `L^r(ν_B)` and `Θ` is strongly universal.

**`def:universality`** — `universality.tex:10–19` — is what fixes the reading of that last
clause: its parenthetical records that *realization at one `p` implies it at every `p ≥ 1`*.

`Core/Universality.lean` and `Core/UniversalityLp.lean` disclose exactly this as their one
remaining gap, in two halves. Their `stronglyUniversalAt_of_le` proves the lattice half —
`Sθ ≤ η • 𝟏` forces `ψ_η = 0` and hence `D = 0` — but carries the order relation as a
hypothesis, and `UniversalityLp`'s SCOPE says that instantiating it at `L^∞(ν)` "would need
`Sθ ≤ ‖Sθ‖_∞ • 𝟏` in the `Lp` order, which is not proved here". `Core/Universality.lean`'s SCOPE
adds that "the cross-`p` transfer is not proved anywhere in this library". This file proves both.

## What is proved

| | |
|---|---|
| `ae_le_norm_top` | `g x ≤ ‖g‖` `ν`-a.e., for `g ∈ L^∞(ν)` |
| `le_norm_smul_constOne` | **the order fact**: `g ≤ ‖g‖ • 𝟏` in the `L^∞(ν)` order |
| `stronglyUniversalAt_top` | **strong universality at `p = +∞`**, with no order hypothesis left: `Mixing P Π`, `P 𝟏 = 𝟏`, `Π θ = 0` suffice |
| `StronglyUniversal` | `def:universality`'s strong form with its pair quantifier closed |
| `stronglyUniversal_top` | the family `Θ = {P} × L^∞_+(ν)` is strongly universal |
| `stronglyUniversal_of_kernel_top` | the same from the paper's hypotheses on the *kernel*, via `Core/Kernel.lean` |
| `stronglyUniversalAt_of_kernel_top` | the same at one admissible pair `(f_init, f_term)` of equal total mass |
| `inclTop`, `coeFn_inclTop`, `memLp_of_top` | the inclusion `L^∞(ν) ⊆ L^r(ν)`, `ν` finite |
| `exists_outflow_memLp_of_top` | **the transfer, in the form that needs nothing at `r`**: the realizing outflow lies in *every* `L^r(ν)` and satisfies `P f_out = f_out + θ` a.e. |
| `CompatibleAcrossTop` | the compatibility of `P` on `L^∞(ν)` with `Q` on `L^r(ν)` that an *operator-level* transfer consumes |
| `stronglyUniversalAt_inclTop` | **the cross-`p` transfer**: `StronglyUniversalAt P θ` at `⊤` gives `StronglyUniversalAt Q (inclTop θ)` at `r` |
| `compatibleAcrossTop_densityActionCLM` | the compatibility **discharged** for a Markov kernel: `densityAction` is a map on functions and does not know about `p` |
| `stronglyUniversalAt_of_kernel_Lr` | the payoff: the outflow built at `p = +∞` realizes the infimum in `L^r(ν)` too |

## Two forms of the transfer, and why both are here

`defect P θ f_out = 0` is an equation in `Lp ℝ ⊤ ν`. Saying it in `Lp ℝ r ν` needs the *same*
underlying function to lie in `L^r` — which is `MemLp.mono_exponent` and free, `ν` being
finite — and needs `P` to act on both spaces. **That second half is a real hypothesis and it is
carried as one**, `CompatibleAcrossTop`: two operators, one on each space, agreeing a.e. on the
image of the inclusion. It is *not* automatic for arbitrary bounded operators, since an operator
on `L^r(ν)` is not determined by one on `L^∞(ν)`.

For a Markov kernel it is discharged, and `Core/Kernel.lean` is why: `densityAction κ ν` is a map
on functions `α → ℝ`, defined pointwise from `bindDensity` and independent of `p`, and
`coeFn_densityActionCLM` says every `densityActionCLM κ ν p` is represented by it. Two exponents
therefore give two continuous linear maps *induced by one function-level map*, and
`densityAction_congr` — which is congruence for a.e. equality — closes the gap. So for the
paper's own object the transfer is real, not conditional.

`exists_outflow_memLp_of_top` records the half that needs no compatibility at all: the realizing
outflow is in every `L^r(ν)`, and the flow-matching identity holds a.e. as an identity of
functions. That is the whole mathematical content of the appendix's sentence; the operator form
is what it takes to say it inside `defect`, which is parameterized by `p`.

## SCOPE (disclosed)

**What is closed here, precisely.** The `p = +∞` clause of `theo:universality_L2_full` — "`Θ` is
strongly universal: taking `η := ‖Sθ‖_{L^∞(ν_B)}` gives `δf_init = δf_term = 0`" — is proved, at
one pair (`stronglyUniversalAt_top`) and for the family (`stronglyUniversal_top`), and from the
paper's hypotheses on the kernel (`stronglyUniversal_of_kernel_top`). The cross-`p` sentence is
proved at one pair (`stronglyUniversalAt_of_kernel_Lr`).

**The cross-`p` transfer does not deliver strong `L^r`-universality of the `L^r` family.** It
delivers, for a pair whose densities lie in `L^∞(ν)`, a realization of the infimum in `L^r(ν)`.
`def:universality` at exponent `r` quantifies over pairs with densities in `L^r(ν)`, and a pair
merely in `L^r` is *not* reached by this argument — `Sθ` need not be essentially bounded, and the
construction's `η` does not exist. The paper does not claim otherwise: its `p = +∞` clause is
stated under the `p = +∞` hypotheses, and "the infimum is attained in every `L^r(ν_B)`" is about
the outflow just constructed. `StronglyUniversal Q (meanProj ν r)` is therefore **not** proved
here for `r < ∞` and is not a consequence of what is.

**The `p = +∞` hypotheses are the paper's, and they are strong.** `Mixing P Π` at `p = ⊤` asks
for summability of `β_n = ‖P^n − Π‖_{L^∞→L^∞}`, and `IsBoundedDensityAction κ ν ⊤ C` asks for
boundedness of the density action on `L^∞(ν)`. Both are `theo:universality_L2_full`'s own
hypotheses read at `p = +∞`; neither is derived, and `Core/Kernel.lean`'s SCOPE already records
that boundedness is a requirement on the parameterization rather than a theorem. No kernel
satisfying the whole bundle at `p = +∞` is exhibited.

**The operator-level transfer needs boundedness at `r` too**, as `IsBoundedDensityAction κ ν r C'`
in `stronglyUniversalAt_of_kernel_Lr` — not because the mathematics needs it (the defect is
*exactly zero*, so `P f_out = f_out + θ ∈ L^∞ ⊆ L^r` with no bound anywhere), but because
`defect` takes a continuous linear map on `L^r(ν)` as an argument and there is no such map
without it. `exists_outflow_memLp_of_top` is the same content free of that artefact.

**Everything `Core/Universality.lean` and `Core/Kernel.lean` disclose is inherited.** `Π` is the
mean projection and not proved to be the projection onto `ker (Id − P)`; ergodicity has moved
into the summability hypothesis; the family is `Θ = {P} × L^p_+(ν)`, the one the theorem is
about, rather than `def:universality`'s arbitrary `Θ`; `θ` is an arbitrary element with `Π θ = 0`
rather than a difference of probability densities. Nothing here narrows or widens those.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` a measured Polish space, `ν_B` finite | ⚠ weakened: any `MeasurableSpace α` with `[IsFiniteMeasure ν]`; Polish is not used. Finiteness *is* used, twice — for `𝟏 ∈ L^∞` and for `L^∞ ⊆ L^r` |
| `π⋆` a Markov kernel with finite `L^p(ν_B) → L^p(ν_B)` operator norm | ⚠ **assumed** at `p = ⊤` as `IsBoundedDensityAction κ ν ⊤ C`, as in `Core/Kernel.lean`; the kernel itself is the primitive there |
| `π⋆` ergodic with summable `L^p`-mixing, at `p = +∞` | ⚠ **assumed** as `Mixing P Π` / `hsum`, exactly as the paper assumes it |
| `ν_B π⋆ = ν_B` | ✓ `hinv`, and `P 𝟏 = 𝟏` is **derived** from it in `Core/Kernel.lean` |
| `F_init, F_term` probability densities in `L^∞(ν_B)`, equal mass | ⚠ weakened to `θ ∈ L^∞(ν)` with `Π θ = 0`; `stronglyUniversalAt_of_kernel_top` restores the pair form with `∫f_init = ∫f_term` |
| `η := ‖Sθ‖_{L^∞(ν_B)}`, hence `ψ_η = 0` and `D = 0` | ✓ `le_norm_smul_constOne` + `stronglyUniversalAt_of_le`; the order fact is `MeasureTheory.ae_le_eLpNormEssSup` |
| `f_out^η ∈ L^∞(ν_B) ⊂ L^r(ν_B)` for every `r` | ✓ `memLp_of_top`, from `MemLp.mono_exponent` and finiteness of `ν` |
| the infimum is attained in every `L^r(ν_B)` | ✓ at one pair — `exists_outflow_memLp_of_top` unconditionally, `stronglyUniversalAt_of_kernel_Lr` inside `defect`. ✗ **not** as strong `L^r`-universality of the `L^r` family; see SCOPE |
| conclusion: `Θ` strongly universal at `p = +∞` | ✓ `stronglyUniversal_top`, `stronglyUniversal_of_kernel_top` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open MeasureTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-! ## The order fact at `p = +∞` -/

/-- **`g ≤ ‖g‖` a.e., on `L^∞(ν)`.** The essential supremum dominates a.e., and on `L^∞` it is
finite, so the `ℝ≥0∞` inequality `‖g x‖ₑ ≤ eLpNormEssSup g ν` may be read in `ℝ`.

This is the analytic content of `theo:universality_L2_full`'s "taking `η := ‖Sθ‖_{L^∞(ν_B)}`"
(`proofs.tex:73`): the choice is legitimate because the norm really does dominate the
function. -/
theorem ae_le_norm_top (g : Lp ℝ ⊤ ν) : ∀ᵐ x ∂ν, g x ≤ ‖g‖ := by
  filter_upwards [ae_le_eLpNormEssSup (f := ⇑g) (μ := ν)] with x hx
  have h : ‖g x‖ₑ ≤ eLpNorm (⇑g) ⊤ ν := by rwa [eLpNorm_exponent_top]
  have h2 : ‖g x‖ ≤ ‖g‖ := by
    have hmono := ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) h
    rwa [toReal_enorm, ← Lp.norm_def] at hmono
  exact (Real.le_norm_self (g x)).trans h2

variable [IsFiniteMeasure ν]

/-- **The order hypothesis of `stronglyUniversalAt_of_le`, discharged at `p = +∞`**:
`g ≤ ‖g‖ • 𝟏` in the `L^∞(ν)` order.

`Core/UniversalityLp.lean`'s SCOPE names exactly this — "instantiating it at `L^∞(ν)` would need
`Sθ ≤ ‖Sθ‖_∞ • 𝟏` in the `Lp` order, which is not proved here". The `Lp` order is the a.e.
order (`MeasureTheory.Lp.coeFn_le`), so `ae_le_norm_top` is the whole of it. -/
theorem le_norm_smul_constOne (g : Lp ℝ ⊤ ν) : g ≤ ‖g‖ • constOne ν ⊤ := by
  rw [← Lp.coeFn_le]
  filter_upwards [ae_le_norm_top g, Lp.coeFn_smul ‖g‖ (constOne ν ⊤),
    coeFn_constOne (ν := ν) (p := ⊤)] with x hx hsmul h1
  rw [hsmul, _root_.Pi.smul_apply, h1, smul_eq_mul, mul_one]
  exact hx

/-! ## Strong universality at `p = +∞` -/

/-- **`theo:universality_L2_full`'s `p = +∞` clause, at one admissible pair.**

"Taking `η := ‖Sθ‖_{L^∞(ν_B)}` gives `δf_init = δf_term = 0`, and the flow-matching constraint
holds exactly" (`proofs.tex:73`). No order hypothesis survives: `le_norm_smul_constOne` supplies
it, and what is left is the same bundle the weak half consumes — summable mixing, `P 𝟏 = 𝟏`,
`Π θ = 0`. -/
theorem stronglyUniversalAt_top {P Pi : Lp ℝ ⊤ ν →L[ℝ] Lp ℝ ⊤ ν} {θ : Lp ℝ ⊤ ν}
    (h : Mixing P Pi) (hone : P (constOne ν ⊤) = constOne ν ⊤) (hθ : Pi θ = 0) :
    StronglyUniversalAt P θ :=
  stronglyUniversalAt_of_le h hone hθ (le_norm_smul_constOne (Mixing.S P Pi θ))

section Family

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [NormedSpace ℝ E]

/-- **`def:universality`, strong form, with its pair quantifier closed**: the family
`Θ = {P} × E⁺` is strongly universal when *every* admissible pair is realized exactly — not
merely approached. This is `WeaklyUniversal`'s twin in `Core/Universality.lean`, with
`WeaklyUniversalAt` replaced by `StronglyUniversalAt`.

As there, `Pi θ = 0` is the paper's "distributions of equal total mass". -/
def StronglyUniversal (P Pi : E →L[ℝ] E) : Prop :=
  ∀ θ : E, Pi θ = 0 → StronglyUniversalAt P θ

theorem StronglyUniversal.weaklyUniversal [HasSolidNorm E] [IsOrderedAddMonoid E]
    {P Pi : E →L[ℝ] E} (h : StronglyUniversal P Pi) : WeaklyUniversal P Pi :=
  fun θ hθ => (h θ hθ).weaklyUniversalAt

end Family

/-- **`theo:universality_L2_full`'s `p = +∞` clause, for the family**: under summable `L^∞`-mixing
and with `P` fixing the constants, `Θ = {P} × L^∞_+(ν)` is strongly universal. -/
theorem stronglyUniversal_top {P Pi : Lp ℝ ⊤ ν →L[ℝ] Lp ℝ ⊤ ν}
    (h : Mixing P Pi) (hone : P (constOne ν ⊤) = constOne ν ⊤) :
    StronglyUniversal P Pi :=
  fun _θ hθ => stronglyUniversalAt_top h hone hθ

/-! ## From the kernel, as the paper states it -/

/-- **Strong universality at `p = +∞`, from the paper's hypotheses on the kernel.**

`π⋆` a Markov kernel, `ν` finite and `π⋆`-invariant, the density action bounded on `L^∞(ν)`, the
mixing coefficients summable there. `P⋆ 𝟏 = 𝟏` and `Π P⋆ = P⋆ Π = Π` are *derived*, in
`Core/Kernel.lean` and `Core/Flow.lean`; nothing is hypothesised about an operator. -/
theorem stronglyUniversal_of_kernel_top (κ : ProbabilityTheory.Kernel α α)
    [ProbabilityTheory.IsMarkovKernel κ] (ν : Measure α) [IsFiniteMeasure ν] {C : ℝ}
    (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν ⊤ C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν ⊤ hinv hb) ^ n - meanProj ν ⊤‖) :
    StronglyUniversal (densityActionCLM κ ν ⊤ hinv hb) (meanProj ν ⊤) :=
  stronglyUniversal_top
    (mixing_of_massPreserving (densityActionCLM_constOne κ ν ⊤ hinv hb)
      (integral_densityActionCLM κ ν ⊤ hinv hb) hsum)
    (densityActionCLM_constOne κ ν ⊤ hinv hb)

/-- **The same at one admissible pair**, in the paper's own terms: two densities in `L^∞(ν)` of
equal total mass are joined *exactly* — not approximately — by a non-negative outflow. -/
theorem stronglyUniversalAt_of_kernel_top (κ : ProbabilityTheory.Kernel α α)
    [ProbabilityTheory.IsMarkovKernel κ] (ν : Measure α) [IsFiniteMeasure ν] {C : ℝ}
    (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν ⊤ C)
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν ⊤ hinv hb) ^ n - meanProj ν ⊤‖)
    {f_init f_term : Lp ℝ ⊤ ν} (hmass : ∫ x, f_init x ∂ν = ∫ x, f_term x ∂ν) :
    StronglyUniversalAt (densityActionCLM κ ν ⊤ hinv hb) (f_term - f_init) :=
  stronglyUniversal_of_kernel_top κ ν hinv hb hsum _ (meanProj_sub_eq_zero hmass)

/-! ## `L^∞(ν) ⊆ L^r(ν)`, and the transfer -/

/-- **The inclusion `L^∞(ν) ↪ L^r(ν)`**, `ν` finite. It is the appendix's
"`f_out^η ∈ L^∞(ν_B) ⊂ L^r(ν_B)` for every `r ∈ [1,+∞]`, since `ν_B` is finite"
(`proofs.tex:114`). -/
noncomputable def inclTop (ν : Measure α) [IsFiniteMeasure ν] (r : ℝ≥0∞) (f : Lp ℝ ⊤ ν) :
    Lp ℝ r ν :=
  ((Lp.memLp f).mono_exponent le_top).toLp _

/-- An `L^∞(ν)` function is in every `L^r(ν)`: finiteness of `ν` and nothing else. -/
theorem memLp_of_top (r : ℝ≥0∞) (f : Lp ℝ ⊤ ν) : MemLp (⇑f) r ν :=
  (Lp.memLp f).mono_exponent le_top

theorem coeFn_inclTop (r : ℝ≥0∞) (f : Lp ℝ ⊤ ν) : ⇑(inclTop ν r f) =ᵐ[ν] ⇑f :=
  MemLp.coeFn_toLp _

/-- The inclusion is order-preserving, the `Lp` order being the a.e. order on both sides. -/
theorem inclTop_nonneg {r : ℝ≥0∞} {f : Lp ℝ ⊤ ν} (hf : 0 ≤ f) : 0 ≤ inclTop ν r f := by
  rw [← Lp.coeFn_nonneg] at hf ⊢
  filter_upwards [hf, coeFn_inclTop r f] with x hx hy
  rw [hy]
  exact hx

omit [IsFiniteMeasure ν] in
/-- The defect, read pointwise: `D = P f_out − f_out − θ` a.e. -/
theorem coeFn_defect {p : ℝ≥0∞} [Fact (1 ≤ p)] (P : Lp ℝ p ν →L[ℝ] Lp ℝ p ν)
    (θ fout : Lp ℝ p ν) :
    ⇑(defect P θ fout) =ᵐ[ν] fun x => (P fout) x - fout x - θ x := by
  have hd : defect P θ fout = P fout - fout - θ := rfl
  rw [hd]
  filter_upwards [Lp.coeFn_sub (P fout - fout) θ, Lp.coeFn_sub (P fout) fout] with x h1 h2
  rw [h1, _root_.Pi.sub_apply, h2, _root_.Pi.sub_apply]

/-- **The transfer, in the form that assumes nothing at `r`.** The `p = +∞` construction produces
a non-negative outflow that lies in *every* `L^r(ν)` and satisfies the flow-matching constraint
as an a.e. identity of functions, `P f_out = f_out + θ`.

This is the whole mathematical content of `proofs.tex:114`'s last sentence. Nothing is said here
inside `defect`, and so nothing is needed about how — or whether — `P` acts on `L^r(ν)`. -/
theorem exists_outflow_memLp_of_top {P Pi : Lp ℝ ⊤ ν →L[ℝ] Lp ℝ ⊤ ν} {θ : Lp ℝ ⊤ ν}
    (h : Mixing P Pi) (hone : P (constOne ν ⊤) = constOne ν ⊤) (hθ : Pi θ = 0) :
    ∃ fout : Lp ℝ ⊤ ν, 0 ≤ fout ∧ (∀ r : ℝ≥0∞, MemLp (⇑fout) r ν) ∧
      ∀ᵐ x ∂ν, (P fout) x = fout x + θ x := by
  obtain ⟨fout, hnn, hD⟩ := stronglyUniversalAt_top h hone hθ
  refine ⟨fout, hnn, fun r => memLp_of_top r fout, ?_⟩
  have h0 : ⇑(defect P θ fout) =ᵐ[ν] 0 := by
    rw [hD]
    exact Lp.coeFn_zero ℝ ⊤ ν
  filter_upwards [coeFn_defect P θ fout, h0] with x e1 e2
  rw [e1] at e2
  simp only [_root_.Pi.zero_apply] at e2
  linarith

/-- **The compatibility an operator-level transfer consumes**: `Q` on `L^r(ν)` and `P` on
`L^∞(ν)` agree a.e. on the image of the inclusion.

It is a genuine hypothesis, not a triviality — a bounded operator on `L^r(ν)` is not determined
by one on `L^∞(ν)`, and neither space's operator is canonically the other's restriction.
`compatibleAcrossTop_densityActionCLM` discharges it for the density action of a Markov kernel,
where both operators are induced by the single function-level map `densityAction κ ν`. -/
def CompatibleAcrossTop (ν : Measure α) [IsFiniteMeasure ν] (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (P : Lp ℝ ⊤ ν →L[ℝ] Lp ℝ ⊤ ν) (Q : Lp ℝ r ν →L[ℝ] Lp ℝ r ν) : Prop :=
  ∀ f : Lp ℝ ⊤ ν, ⇑(Q (inclTop ν r f)) =ᵐ[ν] ⇑(P f)

section Transfer

variable {r : ℝ≥0∞} [Fact (1 ≤ r)] {P : Lp ℝ ⊤ ν →L[ℝ] Lp ℝ ⊤ ν}
  {Q : Lp ℝ r ν →L[ℝ] Lp ℝ r ν}

/-- The two defects are the same function: `D` at `r` computed on the included data agrees a.e.
with `D` at `⊤`. -/
theorem coeFn_defect_inclTop (hc : CompatibleAcrossTop ν r P Q) (θ fout : Lp ℝ ⊤ ν) :
    ⇑(defect Q (inclTop ν r θ) (inclTop ν r fout)) =ᵐ[ν] ⇑(defect P θ fout) := by
  filter_upwards [coeFn_defect Q (inclTop ν r θ) (inclTop ν r fout), coeFn_defect P θ fout,
    hc fout, coeFn_inclTop r fout, coeFn_inclTop r θ] with x e1 e2 e3 e4 e5
  rw [e1, e2, e3, e4, e5]

/-- An exactly flow-matching outflow at `p = +∞` is exactly flow-matching at `r`. -/
theorem defect_inclTop_eq_zero (hc : CompatibleAcrossTop ν r P Q) {θ fout : Lp ℝ ⊤ ν}
    (h : defect P θ fout = 0) : defect Q (inclTop ν r θ) (inclTop ν r fout) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine (coeFn_defect_inclTop hc θ fout).trans ?_
  rw [h]
  exact Lp.coeFn_zero ℝ ⊤ ν

/-- **The cross-`p` transfer**, `def:universality`'s "realization at one `p` implies it at every
`p ≥ 1`": a pair realized exactly in `L^∞(ν)` is realized exactly in `L^r(ν)`, by the same
outflow.

It is a statement *at one pair*. It does not say that the `L^r` family is strongly universal —
see this file's SCOPE. -/
theorem stronglyUniversalAt_inclTop (hc : CompatibleAcrossTop ν r P Q) {θ : Lp ℝ ⊤ ν}
    (h : StronglyUniversalAt P θ) : StronglyUniversalAt Q (inclTop ν r θ) := by
  obtain ⟨fout, hnn, hD⟩ := h
  exact ⟨inclTop ν r fout, inclTop_nonneg hnn, defect_inclTop_eq_zero hc hD⟩

end Transfer

/-- **The compatibility, discharged for a Markov kernel.** `densityAction κ ν` is a map on
functions `α → ℝ` and knows nothing about `p`; `coeFn_densityActionCLM` says the operator at
either exponent is represented by it, and `densityAction_congr` says it only sees the a.e. class.
The two continuous linear maps are therefore induced by one function-level map, which is exactly
what `CompatibleAcrossTop` asks. -/
theorem compatibleAcrossTop_densityActionCLM (κ : ProbabilityTheory.Kernel α α)
    [ProbabilityTheory.IsMarkovKernel κ] (ν : Measure α) [IsFiniteMeasure ν] (r : ℝ≥0∞)
    [Fact (1 ≤ r)] {C C' : ℝ} (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν ⊤ C)
    (hb' : IsBoundedDensityAction κ ν r C') :
    CompatibleAcrossTop ν r (densityActionCLM κ ν ⊤ hinv hb)
      (densityActionCLM κ ν r hinv hb') := by
  intro f
  have h1 := coeFn_densityActionCLM κ ν r hinv hb' (inclTop ν r f)
  have h2 := coeFn_densityActionCLM κ ν ⊤ hinv hb f
  rw [densityAction_congr κ ν (coeFn_inclTop r f)] at h1
  exact h1.trans h2.symm

/-- **`proofs.tex:114`'s last sentence, inside `defect`**: the outflow constructed at `p = +∞`
realizes the infimum in `L^r(ν)` as well.

`IsBoundedDensityAction κ ν r C'` appears only to name the operator on `L^r(ν)`; the mathematics
uses no bound at `r`, the defect being exactly zero. `exists_outflow_memLp_of_top` is the same
statement without that artefact. -/
theorem stronglyUniversalAt_of_kernel_Lr (κ : ProbabilityTheory.Kernel α α)
    [ProbabilityTheory.IsMarkovKernel κ] (ν : Measure α) [IsFiniteMeasure ν] (r : ℝ≥0∞)
    [Fact (1 ≤ r)] {C C' : ℝ} (hinv : ν.bind ⇑κ = ν) (hb : IsBoundedDensityAction κ ν ⊤ C)
    (hb' : IsBoundedDensityAction κ ν r C')
    (hsum : Summable fun n : ℕ => ‖(densityActionCLM κ ν ⊤ hinv hb) ^ n - meanProj ν ⊤‖)
    {θ : Lp ℝ ⊤ ν} (hθ : meanProj ν ⊤ θ = 0) :
    StronglyUniversalAt (densityActionCLM κ ν r hinv hb') (inclTop ν r θ) :=
  stronglyUniversalAt_inclTop (compatibleAcrossTop_densityActionCLM κ ν r hinv hb hb')
    (stronglyUniversal_of_kernel_top κ ν hinv hb hsum θ hθ)

end GFNBounds.Core
