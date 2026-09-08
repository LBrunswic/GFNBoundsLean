import GFNBounds.Core.Mixing

/-!
# Universality: the lifted outflow, its defect, and the quantitative bound

**`theo:universality_L2_full`** — statement `proofs.tex:65–74`, proof `proofs.tex:76–115`
(Theorem 15 of the ICLR build) — Steps 2 (`:100`) and 3 (`:114`); Step 1 is
`GFNBounds.Core.Mixing`. **`def:universality`** — `universality.tex:10–19` — is what
`WeaklyUniversalAt` / `StronglyUniversalAt` below say *at one admissible pair*; see SCOPE.

The appendix's construction, in one line: the Poisson equation solves flow matching by a
*signed* outflow `-Sθ`, and the constants — which are `0`-flows, because `P` fixes `1` — buy
back non-negativity. For `η > 0`,

  `f_out^η := (η • 1 - Sθ)⁺`,   `ψ_η := (η • 1 - Sθ)⁻ = (Sθ - η • 1)⁺`,

so that `f_out^η ≥ 0` and `f_out^η = η • 1 - Sθ + ψ_η`. The exact part cancels in the defect
and only the truncation survives:

  `D = (P - 1) f_out^η - θ = (P - 1) ψ_η`   (`equ:defect_is_truncation`),

whence `‖δf_init‖ + ‖δf_term‖ ≤ 2 (1 + ‖P‖) ‖ψ_η‖` (`equ:universality_quantitative`).

## What is abstract here and what is not

Everything above is **lattice algebra and operator norms**: it needs a Banach lattice, a bounded
`P` fixing an element `one`, and the Poisson equation. No measure, no kernel, no `p`. So it is
proved here once, on a Banach lattice — the four-class bundle
`[NormedAddCommGroup] [Lattice] [HasSolidNorm] [IsOrderedAddMonoid]`, since Mathlib unbundled
`NormedLatticeAddCommGroup` before this pin — and `Core.UniversalityLp` instantiates it at
`L^p(ν_B)`.

The one step that is *not* abstract is Step 3's `‖ψ_η‖ → 0` as `η → +∞` for `p < ∞`, which is
dominated convergence on a concrete `L^p`. This file therefore proves:

* the defect identity and the quantitative bound, for every `η` — unconditionally;
* **strong universality** whenever `Sθ ≤ η • one` for some `η`, which at `p = +∞` is
  `η := ‖Sθ‖_∞` and is the appendix's "the infimum is attained and the flow-matching
  constraint holds exactly";
* weak universality **conditional on** `‖ψ_η‖ → 0`, stated as the hypothesis it is.

## SCOPE (disclosed)

**The family.** `WeaklyUniversalAt` fixes the family at `Θ = {P} × E⁺` of
`theo:universality_L2_full` — one policy, a free non-negative outflow — rather than the
arbitrary `Θ` of `def:universality`. That is the family the theorem is about, and the paper's
own theorem fixes the policy in its first line.

**The pair.** `def:universality` quantifies over *all* admissible pairs `(F_init, F_term)`:
"for any distributions `F_init, F_term ≪ ν_B` of equal total mass whose densities lie in
`L^p(ν_B)`", with the infimum inside that quantifier — so a *different* outflow per pair is
allowed, and the per-pair predicate is the right unit. `WeaklyUniversalAt P θ` is that unit;
`WeaklyUniversal P Pi` below closes the quantifier, and it is the one that matches
`def:universality`. Two further generalizations, both in the safe direction: `θ` is an arbitrary
element with `Pi θ = 0` rather than a difference of two non-negative equal-mass densities —
`Pi θ = 0` is all the proof consumes — and the mass condition is read off `Pi` rather than off
the measures.

**The `p = +∞` clause is narrowed.** `theo:universality_L2_full` concludes at `p = +∞` that `Θ`
is *strongly universal*, and its proof (`proofs.tex:114`) gets there in two moves: `ψ_η = 0` for
`η ≥ ‖Sθ‖_∞`, and then — because `ν_B` is finite and so `f_out^η ∈ L^∞ ⊂ L^r` for every `r` —
**the infimum is attained in every `L^r(ν_B)`**, which is what `def:universality`'s parenthetical
("realization at one `p` implies it at every `p ≥ 1`") records. `stronglyUniversalAt_of_le`
proves the first move only, and in the single abstract `E`. **The cross-`p` transfer is not
proved anywhere in this library**, and neither is the instantiation supplying `Sθ ≤ ‖Sθ‖_∞ • 1`
in the `L^∞(ν_B)` order. So "strongly universal" in the paper's full sense is *not* certified.

**The hypotheses are assumed, not derived.** `Mixing P Pi`, `P 1 = 1` and `Pi θ = 0` are
hypotheses here; the paper derives them from ergodicity of `π*`, `ν_B π* = ν_B` and equal
masses. That derivation is `Core.Flow` — the kernel-to-operator passage, `CLAUDE.md`'s
*obstruction 2* — and **does not exist**. Nothing here claims when the hypotheses hold.

The residuals are `δf_init := D⁻` and `δf_term := D⁺`, which is `theo:universality_L2_full`'s
own definition ("`δF_term = D⁺`, `δF_init = D⁻`", `proofs.tex:81`), and agrees with the paper's
first definition of them at `introduction.tex:103–105`. The `2` of `equ:defect_equivalence` is
recovered here as `norm_defect_le_residuals` and `residuals_le_two_norm_defect`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, ν_B)` a measured Polish space, `ν_B` finite | ⚠ weakened to a Banach lattice; no measure |
| `π*` a Markov kernel with finite `L^p` operator norm | ⚠ weakened to a bounded `P` |
| `π*` ergodic with summable `L^p`-mixing | ⚠ **assumed** as `Mixing P Pi` (`Core.Flow` would derive it) |
| `ν_B π* = ν_B`, hence `(Id − P⋆) 1 = 0` | ⚠ **assumed** as `P one = one` |
| `F_init, F_term` probability densities of equal mass | ⚠ weakened to `Pi θ = 0` |
| `equ:defect_equivalence` | ✓ both halves |
| `equ:defect_is_truncation` | ✓ `defect_eq_truncation` |
| `equ:universality_quantitative`, constant `2(1 + ‖π*‖)` | ✓ `residuals_le`, constant on the nose |
| weak `L^p`-universality, `p < ∞` | ✓ conditional here, discharged in `Core.UniversalityLp` |
| strong universality at `p = +∞`, attained in every `L^r` | ⚠ **only** `ψ_η = 0 ⟹ D = 0`; no cross-`p` transfer |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open scoped Topology

-- The Banach-lattice bundle. `NormedLatticeAddCommGroup` was unbundled in Mathlib before
-- `v4.31`; these four classes are what `Lp ℝ p μ` carries (`MeasureTheory/Function/LpOrder.lean`).
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E]
  [IsOrderedAddMonoid E] [NormedSpace ℝ E]

section Lattice

variable {F : Type*} [NormedAddCommGroup F] [Lattice F] [HasSolidNorm F] [IsOrderedAddMonoid F]

/-- `‖a⁺‖ ≤ ‖a‖` in a normed lattice: `a⁺ ≤ |a|` and both are non-negative, so the solid
axiom applies. -/
theorem norm_posPart_le (a : F) : ‖a⁺‖ ≤ ‖a‖ := by
  refine HasSolidNorm.solid ?_
  rw [abs_of_nonneg (posPart_nonneg a)]
  calc a⁺ ≤ a⁺ + a⁻ := le_add_of_nonneg_right (negPart_nonneg a)
    _ = |a| := posPart_add_negPart a

/-- `‖a⁻‖ ≤ ‖a‖`. -/
theorem norm_negPart_le (a : F) : ‖a⁻‖ ≤ ‖a‖ := by
  refine HasSolidNorm.solid ?_
  rw [abs_of_nonneg (negPart_nonneg a)]
  calc a⁻ ≤ a⁺ + a⁻ := le_add_of_nonneg_left (posPart_nonneg a)
    _ = |a| := posPart_add_negPart a

omit [HasSolidNorm F] in
/-- `‖a‖ ≤ ‖a⁺‖ + ‖a⁻‖`, from `a = a⁺ - a⁻`. -/
theorem norm_le_norm_posPart_add_norm_negPart (a : F) : ‖a‖ ≤ ‖a⁺‖ + ‖a⁻‖ := by
  calc ‖a‖ = ‖a⁺ - a⁻‖ := by rw [posPart_sub_negPart]
    _ ≤ ‖a⁺‖ + ‖a⁻‖ := norm_sub_le _ _

end Lattice

/-- The **flow-matching defect** of an outflow `fout` against the pair `(f_init, f_term)`,
written as its density: `D = (P - 1) fout - θ` with `θ = f_term - f_init`
(`theo:universality_L2_full`, `proofs.tex:78`). -/
noncomputable def defect (P : E →L[ℝ] E) (θ fout : E) : E := P fout - fout - θ

/-- The residual against the initial flow, `δf_init = D⁻`. -/
noncomputable def resInit (P : E →L[ℝ] E) (θ fout : E) : E := (defect P θ fout)⁻

/-- The residual against the target, `δf_term = D⁺`. -/
noncomputable def resTerm (P : E →L[ℝ] E) (θ fout : E) : E := (defect P θ fout)⁺

omit [HasSolidNorm E] in
/-- `equ:defect_equivalence`, lower half: `‖D‖ ≤ ‖δf_init‖ + ‖δf_term‖`. -/
theorem norm_defect_le_residuals (P : E →L[ℝ] E) (θ fout : E) :
    ‖defect P θ fout‖ ≤ ‖resInit P θ fout‖ + ‖resTerm P θ fout‖ := by
  simp only [resInit, resTerm]
  rw [add_comm]
  exact norm_le_norm_posPart_add_norm_negPart _

/-- `equ:defect_equivalence`, upper half: `‖δf_init‖ + ‖δf_term‖ ≤ 2 ‖D‖`. -/
theorem residuals_le_two_norm_defect (P : E →L[ℝ] E) (θ fout : E) :
    ‖resInit P θ fout‖ + ‖resTerm P θ fout‖ ≤ 2 * ‖defect P θ fout‖ := by
  have h₁ : ‖resInit P θ fout‖ ≤ ‖defect P θ fout‖ := by
    simpa only [resInit] using norm_negPart_le (defect P θ fout)
  have h₂ : ‖resTerm P θ fout‖ ≤ ‖defect P θ fout‖ := by
    simpa only [resTerm] using norm_posPart_le (defect P θ fout)
  linarith

/-- **Weak `L^p`-universality** of `def:universality`, for the family `Θ = {P} × E⁺` that
`theo:universality_L2_full` is about: the two residuals can be driven to `0` together by a
non-negative outflow. -/
def WeaklyUniversalAt (P : E →L[ℝ] E) (θ : E) : Prop :=
  ∀ ε > (0 : ℝ), ∃ fout : E, 0 ≤ fout ∧
    ‖resInit P θ fout‖ + ‖resTerm P θ fout‖ < ε

/-- **Strong universality**: the infimum is realized — some non-negative outflow makes the
flow-matching constraint hold exactly. -/
def StronglyUniversalAt (P : E →L[ℝ] E) (θ : E) : Prop :=
  ∃ fout : E, 0 ≤ fout ∧ defect P θ fout = 0

/-- **`def:universality`**, weak form, with its quantifier closed: the family `Θ = {P} × E⁺`
is weakly `L^p`-universal when *every* admissible pair is reachable.

`Pi θ = 0` is the paper's "distributions of equal total mass" — the defect integrates to
`F_init(𝒮) − F_term(𝒮)`, so unequal masses floor the infimum away from `0`
(`universality.tex:10–14`), and `Pi` is the mean projection, so `Pi θ = 0` says exactly that
the masses agree. -/
def WeaklyUniversal (P Pi : E →L[ℝ] E) : Prop :=
  ∀ θ : E, Pi θ = 0 → WeaklyUniversalAt P θ

theorem StronglyUniversalAt.weaklyUniversalAt {P : E →L[ℝ] E} {θ : E}
    (h : StronglyUniversalAt P θ) : WeaklyUniversalAt P θ := by
  obtain ⟨fout, hnn, hD⟩ := h
  intro ε hε
  refine ⟨fout, hnn, ?_⟩
  have : ‖resInit P θ fout‖ + ‖resTerm P θ fout‖ ≤ 2 * ‖defect P θ fout‖ :=
    residuals_le_two_norm_defect P θ fout
  rw [hD] at this
  simpa using this.trans_lt (by simpa using hε)

section Construction

variable {P Pi : E →L[ℝ] E} {one θ : E}

/-- The **lifted outflow** `f_out^η := (η • 1 - Sθ)⁺` of `theo:universality_L2_full`'s Step 2. -/
noncomputable def liftedOutflow (P Pi : E →L[ℝ] E) (one θ : E) (η : ℝ) : E :=
  (η • one - Mixing.S P Pi θ)⁺

/-- The **truncation** `ψ_η := (η • 1 - Sθ)⁻`, which the appendix also writes
`(Sθ - η)⁺`. It is the whole of the defect. -/
noncomputable def truncation (P Pi : E →L[ℝ] E) (one θ : E) (η : ℝ) : E :=
  (η • one - Mixing.S P Pi θ)⁻

omit [HasSolidNorm E] [IsOrderedAddMonoid E] in
theorem liftedOutflow_nonneg (P Pi : E →L[ℝ] E) (one θ : E) (η : ℝ) :
    0 ≤ liftedOutflow P Pi one θ η := posPart_nonneg _

omit [HasSolidNorm E] [IsOrderedAddMonoid E] in
theorem truncation_nonneg (P Pi : E →L[ℝ] E) (one θ : E) (η : ℝ) :
    0 ≤ truncation P Pi one θ η := negPart_nonneg _

omit [HasSolidNorm E] in
/-- `f_out^η = η • 1 - Sθ + ψ_η`: the appendix's `f_out^η ν_B - ν_∞^η = ψ_η ν_B`. -/
theorem liftedOutflow_eq (P Pi : E →L[ℝ] E) (one θ : E) (η : ℝ) :
    liftedOutflow P Pi one θ η
      = (η • one - Mixing.S P Pi θ) + truncation P Pi one θ η := by
  simp only [liftedOutflow, truncation]
  exact eq_add_of_sub_eq (posPart_sub_negPart (η • one - Mixing.S P Pi θ))

variable [CompleteSpace E]

omit [HasSolidNorm E] in
/-- **`equ:defect_is_truncation`** — the exact part cancels and only the truncation survives:
`D = (P - 1) ψ_η`.

The hypotheses are exactly the two the appendix uses: `P` fixes the constants (`P 1 = 1`,
from `ν_B π* = ν_B`) so that `η • 1` is a `0`-flow, and `Π θ = 0` (equal masses) so that the
Poisson equation solves exactly. -/
theorem defect_eq_truncation (h : Mixing P Pi) (hone : P one = one) (hθ : Pi θ = 0) (η : ℝ) :
    defect P θ (liftedOutflow P Pi one θ η)
      = P (truncation P Pi one θ η) - truncation P Pi one θ η := by
  -- The Poisson equation, in the form the cancellation consumes: `P S θ = S θ - θ`.
  have hP : P (Mixing.S P Pi θ) = Mixing.S P Pi θ - θ := by
    have h1 := h.poisson_solved hθ
    simp only [sub_apply, one_apply_eq_self] at h1
    exact (sub_eq_of_eq_add' (sub_eq_iff_eq_add.mp h1)).symm
  -- `η • 1` is a `0`-flow, because `P` fixes the constants.
  have hconst : P (η • one) = η • one := by rw [map_smul, hone]
  simp only [defect, liftedOutflow_eq P Pi one θ η, map_add, map_sub, hconst, hP]
  abel

/-- **`equ:universality_quantitative`**, the bound of `theo:universality_L2_full`:

  `‖δf_init‖ + ‖δf_term‖ ≤ 2 (1 + ‖P‖) ‖ψ_η‖`. -/
theorem residuals_le (h : Mixing P Pi) (hone : P one = one) (hθ : Pi θ = 0) (η : ℝ) :
    ‖resInit P θ (liftedOutflow P Pi one θ η)‖
        + ‖resTerm P θ (liftedOutflow P Pi one θ η)‖
      ≤ 2 * (1 + ‖P‖) * ‖truncation P Pi one θ η‖ := by
  have hD := defect_eq_truncation h hone hθ η
  have hnorm : ‖defect P θ (liftedOutflow P Pi one θ η)‖
      ≤ (1 + ‖P‖) * ‖truncation P Pi one θ η‖ := by
    rw [hD]
    calc ‖P (truncation P Pi one θ η) - truncation P Pi one θ η‖
        ≤ ‖P (truncation P Pi one θ η)‖ + ‖truncation P Pi one θ η‖ := norm_sub_le _ _
      _ ≤ ‖P‖ * ‖truncation P Pi one θ η‖ + ‖truncation P Pi one θ η‖ := by
          have := P.le_opNorm (truncation P Pi one θ η)
          linarith
      _ = (1 + ‖P‖) * ‖truncation P Pi one θ η‖ := by ring
  calc ‖resInit P θ (liftedOutflow P Pi one θ η)‖
          + ‖resTerm P θ (liftedOutflow P Pi one θ η)‖
      ≤ 2 * ‖defect P θ (liftedOutflow P Pi one θ η)‖ :=
        residuals_le_two_norm_defect _ _ _
    _ ≤ 2 * ((1 + ‖P‖) * ‖truncation P Pi one θ η‖) := by
        exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = 2 * (1 + ‖P‖) * ‖truncation P Pi one θ η‖ := by ring

omit [HasSolidNorm E] in
/-- **Strong universality when the truncation vanishes.** If `Sθ ≤ η • 1` for some `η` — which
at `p = +∞` is `η := ‖Sθ‖_∞`, the appendix's own choice — then `ψ_η = 0`, the defect is `0`
and the flow-matching constraint `equ:FM_const` holds *exactly*. -/
theorem stronglyUniversalAt_of_le (h : Mixing P Pi) (hone : P one = one) (hθ : Pi θ = 0)
    {η : ℝ} (hle : Mixing.S P Pi θ ≤ η • one) : StronglyUniversalAt P θ := by
  have hzero : truncation P Pi one θ η = 0 := by
    simp only [truncation]
    rw [negPart_eq_zero]
    exact sub_nonneg.2 hle
  refine ⟨liftedOutflow P Pi one θ η, liftedOutflow_nonneg _ _ _ _ _, ?_⟩
  rw [defect_eq_truncation h hone hθ η, hzero, map_zero, sub_zero]

/-- **Weak universality from a vanishing truncation.** Step 3 of `theo:universality_L2_full`
for `p < ∞`, with the analytic half — `‖ψ_η‖ → 0` as `η → +∞`, which is dominated convergence
on a concrete `L^p` — carried as the hypothesis it is. `Core.UniversalityLp` discharges it. -/
theorem weaklyUniversalAt_of_tendsto (h : Mixing P Pi) (hone : P one = one) (hθ : Pi θ = 0)
    (hlim : Filter.Tendsto (fun η : ℝ => ‖truncation P Pi one θ η‖) Filter.atTop (𝓝 0)) :
    WeaklyUniversalAt P θ := by
  intro ε hε
  have hpos : 0 < 2 * (1 + ‖P‖) := by positivity
  have hev : ∀ᶠ η : ℝ in Filter.atTop,
      ‖truncation P Pi one θ η‖ < ε / (2 * (1 + ‖P‖)) :=
    hlim.eventually_lt_const (div_pos hε hpos)
  obtain ⟨η, hη⟩ := hev.exists
  refine ⟨liftedOutflow P Pi one θ η, liftedOutflow_nonneg _ _ _ _ _, ?_⟩
  calc ‖resInit P θ (liftedOutflow P Pi one θ η)‖
          + ‖resTerm P θ (liftedOutflow P Pi one θ η)‖
      ≤ 2 * (1 + ‖P‖) * ‖truncation P Pi one θ η‖ := residuals_le h hone hθ η
    _ < 2 * (1 + ‖P‖) * (ε / (2 * (1 + ‖P‖))) := by
        exact mul_lt_mul_of_pos_left hη hpos
    _ = ε := by field_simp

end Construction

end GFNBounds.Core
