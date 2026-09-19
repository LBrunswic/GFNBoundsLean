import GFNBounds.Balance.LiftGeneralMixing
import GFNBounds.Balance.Flow
import GFNBounds.Balance.Discrete
import GFNBounds.Doubling.OperatorGeneral
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Convergence speed under a frozen backward policy, on a general state space

**`theo:db_stable_frozen_full`** — `proofs.tex`, the theorem carrying that label (line numbers
drift, kb `0036`; the label is the anchor); its body twin **`theo:db_stable_frozen`**
(`cv_divergence.tex`) is certified through it.

> Let `T`, `λ`, `P`, `A`, `w`, `M_w` and `ν` be as in Theorem `theo:gd_diffusion_full`, and let
> `g` be twice differentiable at `1` with `g''(1) > 0`. Assume moreover that `w ≥ w_min > 0` and
> that `B̂ ≥ 1` is a *coercivity constant* of `T`, `Π` denoting the `λ`-mean projection
> `h ↦ λ(𝒮)⁻¹∫h dλ`:
> `‖h − Πh‖_{L²(λ)} ≤ B̂ ‖(I − P)h‖_{L²(λ)}` for every `h ∈ L²(λ)`   (eq:coercivity).
> Set `ϱ := g''(1)w_min/B̂²`, `H := g''(1)A^†M_wA`. Then along the linearized gradient flow
> `ḣ_t = −Hh_t` of `𝓛_{g,ν}` at the balanced solution: the component `Πh_t` (the total flow
> normalization) is conserved, and `‖h_t − Πh_t‖_{L²(λ)} ≤ e^{−ϱt}‖h_0 − Πh_0‖_{L²(λ)}`.
> For the linearized gradient descent `h_{k+1} = h_k − εHh_k` with step
> `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}`, the contraction factor per step is `1 − εϱ`. For the FM loss
> `T = π_←`, and for the DB loss `T = K₂` with `λ₂` in place of `λ` (Definition `def:edge_lift`).
> When `π_←` has summable `L²`-mixing, `B := ∑_{n≥0} β_n < ∞` with `β_n` as in Lemma
> `lem:lift_mixing`, and its invariant measure `λ` is not a multiple of a Dirac mass,
> `B̂ := ∑_{n≥0} β̂_n`, where `β̂_n := ‖Pⁿ − Π‖_{L²(λ)}`, is a coercivity constant of `T` with
> `B̂ ≥ 1`, equal to `B` for the FM loss and to `1 + B` for the DB loss: *a backward policy with
> summable mixing makes the linearized gradient descent on the FM and DB losses with frozen
> backward policy converge to the balanced ray, at rate at least `g''(1)w_min/(1 + B)²`* […].

> (`theo:gd_diffusion_full`, the setting) Under the hypotheses of Lemma `lem:adjoint`, let `T` be
> ergodic; write `P` for the density action `h ↦ d((hλ)T)/dλ` of `T` on `L²(λ)`, `P^†` for its
> adjoint, `A := P − I`, and `M_w` for the multiplication by a non-negative `w ∈ L^∞(λ)`, and let
> `ν := wλ`.

## What is proved

| | |
|---|---|
| `stable_frozen_decay_forward` | the continuous display on an abstract inner-product space, for a curve solving `ḣ = −Hh` at **`t ≥ 0` only** (the strict `Flow.stable_frozen_decay` asks every real `t`) |
| `linearFlow_hasDerivAt`, `frozenDecay_flow_apply` | the flow hypothesis is inhabited from every `h₀`: `t ↦ exp(−tH)h₀` (kb `0025`) |
| `mulOpG`, `mulOpG_symm`, `mulOpG_lower`, `mulOpG_upper` | `M_w` on `L²(λ)` for `w ∈ L^∞(λ)`: self-adjoint, `w_min‖y‖² ≤ ⟪y, M_w y⟫ ≤ ‖w‖_{L^∞}‖y‖²` |
| `aOpG`, `hessG` | the paper's `A = P − I` and `H = g''(1)A^†M_wA`, `P = Core.densityActionL2`, `A^†` Mathlib's Hilbert adjoint on `Lp ℝ 2 λ` |
| `meanProj_hessG`, `hessG_symm`, `hessG_coercive`, `hessG_upper` | `ΠH = 0`, `H = H^†`, `ϱ‖x − Πx‖² ≤ ⟪x, Hx⟫` from `eq:coercivity`, and `⟪x, Hx⟫ ≤ 4g''(1)‖w‖_{L^∞}‖x‖²` from `‖A‖ ≤ 2` |
| `FrozenDecay` | the theorem's conclusion as one proposition: both displays, the per-step factor `1 − εϱ ≥ 0`, and its iterate |
| **`db_stable_frozen_general`** | **the theorem, from a coercivity constant `B̂ ≥ 1`**, any Markov `T` on any measurable space; `εϱ ≤ 1` is **derived** from the step cap and `B̂ ≥ 1` (it was a carried hypothesis `hrho` in `Discrete.lean`/`WeightedL2.lean`) |
| **`db_stable_frozen_DB`** | the DB instance `T = K₂` on `λ₂` (`LiftGeneral.edgeLift`, `edgeMeasure`), with `B̂ = 1 + C` from a coercivity constant `C` of `π_←` (`lem:lift_coercivity`) |
| **`db_stable_frozen_FM_mixing`** | **the summable-mixing clause, FM**: `B̂ = B` (literally the same sum, `mixSum`), coercive, `≥ 1`, and `g''(1)w_min/(1 + B)² ≤ ϱ` |
| **`db_stable_frozen_DB_mixing`** | **the summable-mixing clause, DB**: `K₂`'s coefficients summable, `B̂ = 1 + B` (`lem:lift_mixing`), coercive, `≥ 1`, rate `g''(1)w_min/(1 + B)²` |
| `stable_frozen_witness` | inhabitation of the mixing clause's whole bundle on the paper's two-state chain, `g = x²`, `w ≡ 1`: `B = 1`, `ϱ = 2` |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒮` Polish, `λ ∈ 𝓜⁺(𝒮, ν_B)` non-zero (`lem:adjoint`) | ⚠ weakened in `db_stable_frozen_general`/`_DB`: any measurable space, `λ` finite, possibly zero (on `λ = 0` everything is trivial, handled in the proof); ✓ carried in the mixing clauses as `[StandardBorelSpace S]` (the measurable content of Polish, as in `lem_sigma_mixing`) and `[NeZero lam]` |
| `T` Markov, `λ` finite and `T`-invariant | ✓ `[IsMarkovKernel T]`, `[IsFiniteMeasure lam]`, `hinv : lam.bind T = lam` |
| `T` ergodic (`theo:gd_diffusion_full`) | ⚠ weakened: not assumed, never used |
| `P` the density action on `L²(λ)`, `P^†` its adjoint, `A = P − I` | ✓ `densityActionL2`, `ContinuousLinearMap.adjoint`, `aOpG` |
| `w ∈ L^∞(λ)` non-negative, `M_w`, `‖w‖_{L^∞}` | ✓ `hw : MemLp w ⊤ lam`, `mulOpG`, `(eLpNorm w ⊤ lam).toReal`; non-negativity follows from `w ≥ w_min > 0` |
| `ν := wλ` | notation only; `ν` does not enter the statement |
| `g` twice differentiable at `1`, `g''(1) > 0` | ✓ `_hg` (`g` differentiable near `1`, `g'` differentiable at `1`) — carried, not consumed; `g''(1)` is `deriv (deriv g) 1`, `hg2 : 0 < …` |
| `w ≥ w_min > 0` | ✓ `hwmin : ∀ᵐ x ∂λ, wmin ≤ w x`, `hwmin0` |
| `B̂ ≥ 1` a coercivity constant, `eq:coercivity` | ✓ `hB`, `hcoer` |
| `ϱ`, `H` | ✓ `g2 * wmin / Bhat ^ 2`, `hessG T lam hinv g2 hw` |
| "along the linearized gradient flow `ḣ_t = −Hh_t`" | ✓ any `h : ℝ → L²(λ)` with `HasDerivAt h (−H(h t)) t` for every `t ≥ 0`; inhabited by `exp(−tH)h₀` |
| step `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}` | ✓ verbatim, with `0 ≤ ε`; `εϱ ≤ 1` derived, not carried |
| "contraction factor per step `1 − εϱ`" | ✓ `‖h_{k+1}^⊥‖ ≤ (1 − εϱ)‖h_k^⊥‖` for every `k`, with `0 ≤ 1 − εϱ`, and the iterate `(1 − εϱ)^k` |
| FM: `T = π_←`; DB: `T = K₂`, `λ₂` | ✓ the general theorem at `T`; `db_stable_frozen_DB` at `edgeLift T`, `edgeMeasure T lam` |
| summable mixing `B = ∑ β_n < ∞` | ✓ `hsum : Summable (Mixing.beta P Π)` |
| `λ` not a multiple of a Dirac mass | ✓ `hdirac : ∀ c x, lam ≠ c • dirac x` |
| conclusion `B̂` coercivity constant, `B̂ ≥ 1`, `= B` (FM), `= 1 + B` (DB) | ✓ |
| conclusion rate at least `g''(1)w_min/(1 + B)²` | ✓ `g2·w_min/(1+B)² ≤ g2·w_min/B²` (FM); equality of rates (DB) |

## SCOPE (disclosed)

* **"The linearized gradient flow of `𝓛_{g,ν}`" is the statement's own `ḣ = −Hh`**, `H` defined
  in the statement; that it *is* the linearization is `theo:gd_diffusion_full`'s claim, cited by
  the statement and not re-proved here.
* **The flow is quantified over curves solving the ODE at `t ≥ 0`**, with the two-sided
  derivative at `t = 0` (`IsGradientFlow`'s convention, kb `0025`); `exp(−tH)h₀` meets it from
  every `h₀` (`frozenDecay_flow_apply`). The ODE is linear with bounded `H`, so every forward
  solution extends to one on `ℝ`; this is not formalized and not needed.
* **`β_n`, `β̂_n` are operator norms of powers of the density action** (`Mixing.beta`), the
  reading of `lem:sigma_mixing`'s and `lem:lift_mixing`'s rows; the identification of `Pⁿ` with
  the density action of the `n`-step kernel is not formalized (inherited from
  `Balance/LiftGeneralMixing.lean`).
* **The step cap enters through the quadratic form** `⟪x, Hx⟫ ≤ 4g''(1)‖w‖_{L^∞}‖x‖²`, which is
  what `‖A‖ ≤ 2` gives; the proof's `‖H‖ ≤ 4g''(1)‖w‖_{L^∞}` is not computed as an operator norm.
  `H` self-adjoint and `Π` idempotent — the two hypotheses `Discrete.stable_frozen_discrete`
  carries — are **proved** here for the paper's `H` and `Π` (`hessG_symm`; `meanProj_idem`).
* **`g` enters only through `g''(1)`**; the twice-differentiability hypothesis is carried as the
  paper states it and not consumed, and `g : ℝ → ℝ` (the paper's `g : ℝ₊* → ℝ`) is read only at
  its germ at `1`.
* **`sorry`-free**; no new axiom.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance.StableFrozenGeneral

open MeasureTheory ProbabilityTheory Filter GFNBounds.Core
open scoped ENNReal Topology

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-! ### The abstract decay, forward in time -/

section Forward

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`theo:db_stable_frozen_full`, the continuous half, on the forward half-line**: the sibling
of `GFNBounds.Balance.stable_frozen_decay` whose curve solves `ḣ = −Hh` only at times `t ≥ 0`
(two-sided derivative at every `t ≥ 0`, as `IsGradientFlow` asks, kb `0025`). The component
`Πh_t` is conserved and `‖h_t − Πh_t‖ ≤ e^{−ϱt}‖h_0 − Πh_0‖` for `t ≥ 0`. -/
theorem stable_frozen_decay_forward {H Pi : E →L[ℝ] E} {rho : ℝ} {h : ℝ → E}
    (hPisa : ∀ x y : E, ⟪Pi x, y⟫ = ⟪x, Pi y⟫)
    (hPiH : ∀ x : E, Pi (H x) = 0)
    (hcoer : ∀ x : E, rho * ‖x - Pi x‖ ^ 2 ≤ ⟪x, H x⟫)
    (hflow : ∀ t : ℝ, 0 ≤ t → HasDerivAt h (-H (h t)) t) :
    (∀ t : ℝ, 0 ≤ t → Pi (h t) = Pi (h 0)) ∧
      ∀ t : ℝ, 0 ≤ t → ‖h t - Pi (h t)‖ ≤ Real.exp (-(rho * t)) * ‖h 0 - Pi (h 0)‖ := by
  -- (a) the projected component is conserved on `[0, ∞)`
  have hproj : ∀ t : ℝ, 0 ≤ t → HasDerivAt (⇑Pi ∘ h) 0 t := by
    intro t ht
    have := (Pi.hasFDerivAt (x := h t)).comp_hasDerivAt t (hflow t ht)
    simpa [map_neg, hPiH] using this
  have hconst : ∀ t : ℝ, 0 ≤ t → Pi (h t) = Pi (h 0) := by
    intro t ht
    have := constant_of_has_deriv_right_zero (f := ⇑Pi ∘ h) (a := 0) (b := t)
      (fun s hs => (hproj s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hproj s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
    simpa using this
  refine ⟨hconst, ?_⟩
  set c : E := Pi (h 0) with hc
  set F : ℝ → ℝ := fun s => ‖h s - c‖ ^ 2 with hF
  -- (b) the energy identity `F' = -2⟪h, Hh⟫` on `[0, ∞)`
  have hFd : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (-(2 * ⟪h t, H (h t)⟫)) t := by
    intro t ht
    have hsub : HasDerivAt (fun s : ℝ => h s - c) (-H (h t)) t := (hflow t ht).sub_const c
    have hin := hsub.inner ℝ hsub
    have hrw : ⟪h t - c, -H (h t)⟫ + ⟪-H (h t), h t - c⟫ = -(2 * ⟪h t, H (h t)⟫) := by
      have hsym : ⟪-H (h t), h t - c⟫ = ⟪h t - c, -H (h t)⟫ := real_inner_comm _ _
      have hzero : ⟪Pi (h t), H (h t)⟫ = 0 := by
        rw [hPisa, hPiH, inner_zero_right]
      have hsplit : ⟪h t - c, H (h t)⟫ = ⟪h t, H (h t)⟫ := by
        rw [inner_sub_left, ← hconst t ht, hzero, sub_zero]
      rw [hsym, inner_neg_right, hsplit]
      ring
    have hval : (fun s : ℝ => ⟪h s - c, h s - c⟫) = F := by
      funext s; rw [hF]; exact real_inner_self_eq_norm_sq _
    rw [hval] at hin
    rwa [hrw] at hin
  have hFbound : ∀ t : ℝ, 0 ≤ t → -(2 * ⟪h t, H (h t)⟫) ≤ -(2 * rho) * F t + 0 := by
    intro t ht
    have h1 : rho * ‖h t - Pi (h t)‖ ^ 2 ≤ ⟪h t, H (h t)⟫ := hcoer (h t)
    rw [hconst t ht] at h1
    simp only [hF, add_zero]
    nlinarith [h1]
  -- (c) Grönwall on `[0, t]`
  intro t ht
  have hcont : ContinuousOn F (Set.Icc 0 t) :=
    fun s hs => ((hFd s hs.1).continuousAt).continuousWithinAt
  have hslope : ∀ s ∈ Set.Ico (0:ℝ) t, ∀ r : ℝ, -(2 * ⟪h s, H (h s)⟫) < r →
      ∃ᶠ z in nhdsWithin s (Set.Ioi s), (z - s)⁻¹ * (F z - F s) < r := by
    intro s hs r hr
    have := (hFd s hs.1).hasDerivWithinAt.liminf_right_slope_le hr
    simpa [slope, vsub_eq_sub] using this
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (f := F)
    (f' := fun s => -(2 * ⟪h s, H (h s)⟫)) (δ := F 0) (K := -(2 * rho)) (ε := 0)
    hcont hslope le_rfl (fun s hs => hFbound s hs.1) t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0] at hgron
  -- (d) take square roots
  have hexp : F 0 * Real.exp (-(2 * rho) * (t - 0))
      = (Real.exp (-(rho * t)) * ‖h 0 - Pi (h 0)‖) ^ 2 := by
    have : Real.exp (-(2 * rho) * (t - 0)) = Real.exp (-(rho * t)) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [this, hF, hc]
    ring
  rw [hexp] at hgron
  have hnn : 0 ≤ Real.exp (-(rho * t)) * ‖h 0 - Pi (h 0)‖ :=
    mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have hFt : ‖h t - Pi (h t)‖ ^ 2 ≤ (Real.exp (-(rho * t)) * ‖h 0 - Pi (h 0)‖) ^ 2 := by
    rw [hconst t ht]; exact hgron
  have hroot := Real.sqrt_le_sqrt hFt
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hroot

/-- **The linearized flow exists**, forward and backward: for every bounded `H` on a Banach
space and every `h₀`, `t ↦ exp(−tH) h₀` solves `ḣ = −Hh` at every `t`. So the flow hypothesis of
`stable_frozen_decay_forward` is inhabited from every initial condition (kb `0025`). -/
theorem linearFlow_hasDerivAt [CompleteSpace E] (H : E →L[ℝ] E) (h0 : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • -H) h0)
      (-H (NormedSpace.exp (t • -H) h0)) t := by
  have hd := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-H) t
  have happ := (ContinuousLinearMap.apply ℝ E h0).hasFDerivAt.comp_hasDerivAt t hd
  simpa [Function.comp_def] using happ

theorem linearFlow_zero [CompleteSpace E] (H : E →L[ℝ] E) (h0 : E) :
    NormedSpace.exp ((0 : ℝ) • -H) h0 = h0 := by
  simp

end Forward

/-! ### The multiplication operator `M_w` on `L²(λ)`, for `w ∈ L^∞(λ)` -/

section Mul

variable {S : Type*} [MeasurableSpace S] {lam : Measure S}

/-- `|w| ≤ ‖w‖_{L^∞(λ)}`, `λ`-a.e. -/
theorem ae_norm_le_linfty {w : S → ℝ} (hw : MemLp w ⊤ lam) :
    ∀ᵐ x ∂lam, ‖w x‖ ≤ (eLpNorm w ⊤ lam).toReal := by
  have hfin : eLpNorm w ⊤ lam ≠ ⊤ := hw.eLpNorm_ne_top
  filter_upwards [ae_le_eLpNormEssSup (f := w) (μ := lam)] with x hx
  rw [← eLpNorm_exponent_top] at hx
  have := ENNReal.toReal_mono hfin hx
  rwa [toReal_enorm] at this

theorem linfty_nonneg (w : S → ℝ) : 0 ≤ (eLpNorm w ⊤ lam).toReal := ENNReal.toReal_nonneg

/-- **`M_w`**, the multiplication `f ↦ wf` on `L²(λ)` by `w ∈ L^∞(λ)`; `‖M_w‖ ≤ ‖w‖_{L^∞}`. -/
noncomputable def mulOpG (lam : Measure S) {w : S → ℝ} (hw : MemLp w ⊤ lam) :
    Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 lam :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).mul' hw : MemLp (fun x => w x * f x) 2 lam).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mul' hw :
            MemLp (fun x => w x * (f + g) x) 2 lam),
          MemLp.coeFn_toLp ((Lp.memLp f).mul' hw : MemLp (fun x => w x * f x) 2 lam),
          MemLp.coeFn_toLp ((Lp.memLp g).mul' hw : MemLp (fun x => w x * g x) 2 lam),
          Lp.coeFn_add f g,
          Lp.coeFn_add (((Lp.memLp f).mul' hw : MemLp (fun x => w x * f x) 2 lam).toLp _)
            (((Lp.memLp g).mul' hw : MemLp (fun x => w x * g x) 2 lam).toLp _)]
          with x h1 h2 h3 h4 h5
        rw [h5, h1, _root_.Pi.add_apply, h2, h3, h4, _root_.Pi.add_apply]
        ring
      map_smul' := by
        intro c f
        rw [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mul' hw :
            MemLp (fun x => w x * (c • f) x) 2 lam),
          MemLp.coeFn_toLp ((Lp.memLp f).mul' hw : MemLp (fun x => w x * f x) 2 lam),
          Lp.coeFn_smul c f,
          Lp.coeFn_smul c (((Lp.memLp f).mul' hw : MemLp (fun x => w x * f x) 2 lam).toLp _)]
          with x h1 h2 h3 h4
        rw [h4, h1, _root_.Pi.smul_apply, h2, h3, _root_.Pi.smul_apply,
          smul_eq_mul, smul_eq_mul]
        ring }
    (eLpNorm w ⊤ lam).toReal
    (fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [MemLp.coeFn_toLp ((Lp.memLp f).mul' hw : MemLp (fun x => w x * f x) 2 lam),
        ae_norm_le_linfty hw] with x h1 h2
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h1, norm_mul]
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

theorem coeFn_mulOpG {w : S → ℝ} (hw : MemLp w ⊤ lam) (f : Lp ℝ 2 lam) :
    ⇑(mulOpG lam hw f) =ᵐ[lam] fun x => w x * f x :=
  MemLp.coeFn_toLp ((Lp.memLp f).mul' hw : MemLp (fun x => w x * f x) 2 lam)

/-- `⟪y, z⟫ ≥ 0` when `z = v y` with `v ≥ 0` a.e. -/
theorem inner_nonneg_of_ae_mul (y z : Lp ℝ 2 lam) {v : S → ℝ} (hv : ∀ᵐ x ∂lam, 0 ≤ v x)
    (hz : ⇑z =ᵐ[lam] fun x => v x * y x) : 0 ≤ ⟪y, z⟫ := by
  rw [L2.inner_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hv, hz] with x h1 h2
  change (0 : ℝ) ≤ _
  rw [h2]
  simp only [RCLike.inner_apply, conj_trivial]
  nlinarith [mul_nonneg h1 (mul_self_nonneg (y x))]

/-- `M_w` is self-adjoint: `⟪M_w f, g⟫ = ⟪f, M_w g⟫`. -/
theorem mulOpG_symm {w : S → ℝ} (hw : MemLp w ⊤ lam) (f g : Lp ℝ 2 lam) :
    ⟪mulOpG lam hw f, g⟫ = ⟪f, mulOpG lam hw g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulOpG hw f, coeFn_mulOpG hw g] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- `⟪y, M_w y⟫ ≥ w_min ‖y‖²` when `w ≥ w_min` a.e. -/
theorem mulOpG_lower {w : S → ℝ} (hw : MemLp w ⊤ lam) {c : ℝ} (hc : ∀ᵐ x ∂lam, c ≤ w x)
    (y : Lp ℝ 2 lam) : c * ‖y‖ ^ 2 ≤ ⟪y, mulOpG lam hw y⟫ := by
  have key : 0 ≤ ⟪y, mulOpG lam hw y - c • y⟫ := by
    refine inner_nonneg_of_ae_mul y _ (v := fun x => w x - c) ?_ ?_
    · filter_upwards [hc] with x hx; linarith
    · filter_upwards [Lp.coeFn_sub (mulOpG lam hw y) (c • y), coeFn_mulOpG hw y,
        Lp.coeFn_smul c y] with x h1 h2 h3
      rw [h1, _root_.Pi.sub_apply, h2, h3, _root_.Pi.smul_apply, smul_eq_mul]
      ring
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at key
  linarith

/-- `⟪y, M_w y⟫ ≤ ‖w‖_{L^∞} ‖y‖²`. -/
theorem mulOpG_upper {w : S → ℝ} (hw : MemLp w ⊤ lam) (y : Lp ℝ 2 lam) :
    ⟪y, mulOpG lam hw y⟫ ≤ (eLpNorm w ⊤ lam).toReal * ‖y‖ ^ 2 := by
  set c := (eLpNorm w ⊤ lam).toReal
  have key : 0 ≤ ⟪y, c • y - mulOpG lam hw y⟫ := by
    refine inner_nonneg_of_ae_mul y _ (v := fun x => c - w x) ?_ ?_
    · filter_upwards [ae_norm_le_linfty hw] with x hx
      have := le_abs_self (w x)
      rw [Real.norm_eq_abs] at hx
      linarith
    · filter_upwards [Lp.coeFn_sub (c • y) (mulOpG lam hw y), coeFn_mulOpG hw y,
        Lp.coeFn_smul c y] with x h1 h2 h3
      rw [h1, _root_.Pi.sub_apply, h2, h3, _root_.Pi.smul_apply, smul_eq_mul]
      ring
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at key
  linarith

end Mul

/-! ### `A = P − I`, `H = g''(1)A^†M_wA`, and the facts the two decays consume -/

section Hess

variable {S : Type*} [MeasurableSpace S]

/-- On the zero measure `L²(λ)` is trivial. -/
theorem lp_eq_zero_of_measure_zero {lam : Measure S} (hlam : lam = 0) (f : Lp ℝ 2 lam) :
    f = 0 := by
  refine Lp.eq_zero_iff_ae_eq_zero.2 (ae_iff.2 ?_)
  have := congrArg (fun m : Measure S => m {x | ¬ (f : S → ℝ) x = (0 : S → ℝ) x}) hlam
  simpa using this

variable (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam]
  (hinv : lam.bind ⇑T = lam)

/-- **`A := P − I`**, `P` the density action `h ↦ d((hλ)T)/dλ` on `L²(λ)`. -/
noncomputable def aOpG : Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 lam := densityActionL2 T lam hinv - 1

/-- **`H := g''(1) A^† M_w A`**, with `A^†` the Hilbert adjoint on `L²(λ)`. -/
noncomputable def hessG (g2 : ℝ) {w : S → ℝ} (hw : MemLp w ⊤ lam) :
    Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 lam :=
  g2 • (ContinuousLinearMap.adjoint (aOpG T lam hinv)).comp
    ((mulOpG lam hw).comp (aOpG T lam hinv))

variable {T lam hinv}

theorem hessG_apply (g2 : ℝ) {w : S → ℝ} (hw : MemLp w ⊤ lam) (x : Lp ℝ 2 lam) :
    hessG T lam hinv g2 hw x
      = g2 • ContinuousLinearMap.adjoint (aOpG T lam hinv) (mulOpG lam hw (aOpG T lam hinv x)) :=
  rfl

/-- `(I − P)h = −Ah`. -/
theorem one_sub_eq_neg_aOpG (x : Lp ℝ 2 lam) :
    (1 - densityActionL2 T lam hinv) x = -aOpG T lam hinv x := by
  simp [aOpG, sub_apply]

/-- `‖Ah‖ ≤ 2‖h‖`: `‖P‖ ≤ 1`. -/
theorem norm_aOpG_apply_le (x : Lp ℝ 2 lam) : ‖aOpG T lam hinv x‖ ≤ 2 * ‖x‖ := by
  have hP : ‖densityActionL2 T lam hinv x‖ ≤ ‖x‖ :=
    ((densityActionL2 T lam hinv).le_opNorm x).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_densityActionL2_le T lam hinv))
  calc ‖aOpG T lam hinv x‖ = ‖densityActionL2 T lam hinv x - x‖ := by
        simp [aOpG, sub_apply]
    _ ≤ ‖densityActionL2 T lam hinv x‖ + ‖x‖ := norm_sub_le _ _
    _ ≤ 2 * ‖x‖ := by linarith

/-- `AΠ = 0`: `PΠ = Π` (invariance, `P𝟏 = 𝟏`). -/
theorem aOpG_meanProj (x : Lp ℝ 2 lam) : aOpG T lam hinv (meanProj lam 2 x) = 0 := by
  have h := ContinuousLinearMap.ext_iff.1
    (GFNBounds.Doubling.General.densityActionL2_mul_meanProj T lam hinv) x
  change densityActionL2 T lam hinv (meanProj lam 2 x) = meanProj lam 2 x at h
  simp [aOpG, sub_apply, h]

/-- `Π` is self-adjoint on `L²(λ)`. -/
theorem meanProj_symm (x y : Lp ℝ 2 lam) :
    ⟪meanProj lam 2 x, y⟫ = ⟪x, meanProj lam 2 y⟫ := by
  have h := ContinuousLinearMap.adjoint_inner_left (meanProj lam 2) y x
  rw [GFNBounds.Doubling.General.adjoint_meanProj] at h
  exact h

/-- `⟪Hx, y⟫ = g''(1)⟪M_wAx, Ay⟫`. -/
theorem inner_hessG_left (g2 : ℝ) {w : S → ℝ} (hw : MemLp w ⊤ lam) (x y : Lp ℝ 2 lam) :
    ⟪hessG T lam hinv g2 hw x, y⟫ = g2 * ⟪mulOpG lam hw (aOpG T lam hinv x), aOpG T lam hinv y⟫ := by
  rw [hessG_apply, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]

/-- `H` is self-adjoint. -/
theorem hessG_symm (g2 : ℝ) {w : S → ℝ} (hw : MemLp w ⊤ lam) (x y : Lp ℝ 2 lam) :
    ⟪hessG T lam hinv g2 hw x, y⟫ = ⟪x, hessG T lam hinv g2 hw y⟫ := by
  rw [inner_hessG_left, real_inner_comm (hessG T lam hinv g2 hw y) x, inner_hessG_left,
    mulOpG_symm, real_inner_comm (mulOpG lam hw (aOpG T lam hinv y))]

/-- `⟪x, Hx⟫ = g''(1)⟪Ax, M_wAx⟫`. -/
theorem inner_hessG_self (g2 : ℝ) {w : S → ℝ} (hw : MemLp w ⊤ lam) (x : Lp ℝ 2 lam) :
    ⟪x, hessG T lam hinv g2 hw x⟫ = g2 * ⟪aOpG T lam hinv x, mulOpG lam hw (aOpG T lam hinv x)⟫ := by
  rw [← hessG_symm, inner_hessG_left, mulOpG_symm]

/-- **`ΠH = 0`**: `P^†` preserves integrals, i.e. `ΠA^† = (AΠ)^† = 0`. -/
theorem meanProj_hessG (g2 : ℝ) {w : S → ℝ} (hw : MemLp w ⊤ lam) (x : Lp ℝ 2 lam) :
    meanProj lam 2 (hessG T lam hinv g2 hw x) = 0 := by
  set z := hessG T lam hinv g2 hw x
  have hall : ∀ u : Lp ℝ 2 lam, ⟪meanProj lam 2 z, u⟫ = 0 := by
    intro u
    rw [meanProj_symm, inner_hessG_left, aOpG_meanProj, inner_zero_right, mul_zero]
  exact inner_self_eq_zero.mp (hall _)

/-- **The coercivity of `H`**: `ϱ‖x − Πx‖² ≤ ⟪x, Hx⟫` with `ϱ = g''(1)w_min/B̂²`, from
`eq:coercivity` and `w ≥ w_min`. -/
theorem hessG_coercive {g2 : ℝ} (hg2 : 0 ≤ g2) {w : S → ℝ} (hw : MemLp w ⊤ lam) {wmin : ℝ}
    (hwmin : ∀ᵐ x ∂lam, wmin ≤ w x) (hwmin0 : 0 ≤ wmin) {Bhat : ℝ} (hB : 0 < Bhat)
    (hcoer : ∀ h : Lp ℝ 2 lam,
      ‖h - meanProj lam 2 h‖ ≤ Bhat * ‖(1 - densityActionL2 T lam hinv) h‖)
    (x : Lp ℝ 2 lam) :
    g2 * wmin / Bhat ^ 2 * ‖x - meanProj lam 2 x‖ ^ 2 ≤ ⟪x, hessG T lam hinv g2 hw x⟫ := by
  have h1 : g2 * (wmin * ‖aOpG T lam hinv x‖ ^ 2) ≤ ⟪x, hessG T lam hinv g2 hw x⟫ := by
    rw [inner_hessG_self]
    exact mul_le_mul_of_nonneg_left (mulOpG_lower hw hwmin _) hg2
  have h2 : ‖x - meanProj lam 2 x‖ ≤ Bhat * ‖aOpG T lam hinv x‖ := by
    have := hcoer x
    rwa [one_sub_eq_neg_aOpG, norm_neg] at this
  have h3 : ‖x - meanProj lam 2 x‖ ^ 2 ≤ Bhat ^ 2 * ‖aOpG T lam hinv x‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hB2 : 0 < Bhat ^ 2 := by positivity
  calc g2 * wmin / Bhat ^ 2 * ‖x - meanProj lam 2 x‖ ^ 2
      ≤ g2 * wmin / Bhat ^ 2 * (Bhat ^ 2 * ‖aOpG T lam hinv x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = g2 * (wmin * ‖aOpG T lam hinv x‖ ^ 2) := by field_simp
    _ ≤ _ := h1

/-- **The step bound**: `⟪x, Hx⟫ ≤ 4g''(1)‖w‖_{L^∞}‖x‖²`, the quadratic-form face of the paper's
`‖H‖ ≤ 4g''(1)‖w‖_{L^∞}` (`‖A‖ ≤ 2`). -/
theorem hessG_upper {g2 : ℝ} (hg2 : 0 ≤ g2) {w : S → ℝ} (hw : MemLp w ⊤ lam)
    (x : Lp ℝ 2 lam) :
    ⟪x, hessG T lam hinv g2 hw x⟫ ≤ 4 * g2 * (eLpNorm w ⊤ lam).toReal * ‖x‖ ^ 2 := by
  rw [inner_hessG_self]
  have h1 := mulOpG_upper hw (aOpG T lam hinv x)
  have h2 : ‖aOpG T lam hinv x‖ ^ 2 ≤ (2 * ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_aOpG_apply_le x) 2
  have hs := linfty_nonneg (lam := lam) w
  calc g2 * ⟪aOpG T lam hinv x, mulOpG lam hw (aOpG T lam hinv x)⟫
      ≤ g2 * ((eLpNorm w ⊤ lam).toReal * ‖aOpG T lam hinv x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hg2
    _ ≤ g2 * ((eLpNorm w ⊤ lam).toReal * (2 * ‖x‖) ^ 2) := by gcongr
    _ = 4 * g2 * (eLpNorm w ⊤ lam).toReal * ‖x‖ ^ 2 := by ring

end Hess

/-! ### `theo:db_stable_frozen_full`, assembled -/

section Main

variable {S : Type*} [MeasurableSpace S]

/-- The step cap `ε ≤ Λ⁻¹` gives `εΛ ≤ 1` (Lean's `0⁻¹ = 0` makes `Λ = 0` harmless). -/
theorem step_cap_mul {eps L : ℝ} (hL : 0 ≤ L) (hcap : eps ≤ L⁻¹) :
    eps * L ≤ 1 := by
  rcases hL.eq_or_lt with h | h
  · rw [← h, mul_zero]; exact zero_le_one
  · calc eps * L ≤ L⁻¹ * L := mul_le_mul_of_nonneg_right hcap hL
      _ = 1 := inv_mul_cancel₀ h.ne'

/-- **The conclusion of `theo:db_stable_frozen_full`**, for a Markov kernel `T` with finite
invariant `λ`, the second derivative `g2 = g''(1)`, the weight `w ∈ L^∞(λ)` with lower bound
`w_min`, and a coercivity constant `B̂`; `ϱ := g2·w_min/B̂²`, `H := g2·A^†M_wA`,
`‖w‖_{L^∞} = (eLpNorm w ∞ λ).toReal`:

* along every curve with `ḣ_t = −Hh_t` for `t ≥ 0`, `Πh_t` is conserved and
  `‖h_t − Πh_t‖ ≤ e^{−ϱt}‖h_0 − Πh_0‖`;
* along every recursion `h_{k+1} = h_k − εHh_k` with `0 ≤ ε ≤ (4g2‖w‖_{L^∞})^{−1}`, the factor
  `1 − εϱ` is non-negative, `Πh_k` is conserved, each step contracts `h − Πh` by `1 − εϱ`, hence
  `‖h_k − Πh_k‖ ≤ (1 − εϱ)^k‖h_0 − Πh_0‖`. -/
def FrozenDecay (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S) [IsFiniteMeasure lam]
    (hinv : lam.bind ⇑T = lam) (g2 : ℝ) {w : S → ℝ} (hw : MemLp w ⊤ lam) (wmin Bhat : ℝ) :
    Prop :=
  (∀ h : ℝ → Lp ℝ 2 lam,
    (∀ t : ℝ, 0 ≤ t → HasDerivAt h (-hessG T lam hinv g2 hw (h t)) t) →
    (∀ t : ℝ, 0 ≤ t → meanProj lam 2 (h t) = meanProj lam 2 (h 0)) ∧
    ∀ t : ℝ, 0 ≤ t → ‖h t - meanProj lam 2 (h t)‖
      ≤ Real.exp (-(g2 * wmin / Bhat ^ 2 * t)) * ‖h 0 - meanProj lam 2 (h 0)‖) ∧
  (∀ (eps : ℝ) (h : ℕ → Lp ℝ 2 lam), 0 ≤ eps →
    eps ≤ (4 * g2 * (eLpNorm w ⊤ lam).toReal)⁻¹ →
    (∀ k, h (k + 1) = h k - eps • hessG T lam hinv g2 hw (h k)) →
    0 ≤ 1 - eps * (g2 * wmin / Bhat ^ 2) ∧
    (∀ k, meanProj lam 2 (h k) = meanProj lam 2 (h 0)) ∧
    (∀ k, ‖h (k + 1) - meanProj lam 2 (h (k + 1))‖
      ≤ (1 - eps * (g2 * wmin / Bhat ^ 2)) * ‖h k - meanProj lam 2 (h k)‖) ∧
    ∀ k, ‖h k - meanProj lam 2 (h k)‖
      ≤ (1 - eps * (g2 * wmin / Bhat ^ 2)) ^ k * ‖h 0 - meanProj lam 2 (h 0)‖)

/-- **`theo:db_stable_frozen_full`, the two decays, from a coercivity constant** — on any
measurable space, for any Markov kernel `T` leaving a finite `λ` invariant, `g` twice
differentiable at `1` with `g''(1) > 0`, `w ∈ L^∞(λ)` with `w ≥ w_min > 0` `λ`-a.e., and
`B̂ ≥ 1` satisfying `eq:coercivity`. `ϱ = g''(1)w_min/B̂²`, `H = g''(1)A^†M_wA`; the step cap is
the paper's `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}`, and `εϱ ≤ 1` is **derived** from it and `B̂ ≥ 1`. -/
theorem db_stable_frozen_general (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind ⇑T = lam) (g : ℝ → ℝ)
    (_hg : (∀ᶠ x in 𝓝 (1 : ℝ), DifferentiableAt ℝ g x) ∧ DifferentiableAt ℝ (deriv g) 1)
    (hg2 : 0 < deriv (deriv g) 1) {w : S → ℝ} (hw : MemLp w ⊤ lam) {wmin : ℝ}
    (hwmin0 : 0 < wmin) (hwmin : ∀ᵐ x ∂lam, wmin ≤ w x) {Bhat : ℝ} (hB : 1 ≤ Bhat)
    (hcoer : ∀ h : Lp ℝ 2 lam,
      ‖h - meanProj lam 2 h‖ ≤ Bhat * ‖(1 - densityActionL2 T lam hinv) h‖) :
    FrozenDecay T lam hinv (deriv (deriv g) 1) hw wmin Bhat := by
  set g2 := deriv (deriv g) 1 with hg2def
  have hPisa := meanProj_symm (lam := lam)
  have hPiH := meanProj_hessG (hinv := hinv) g2 hw
  have hHsa := hessG_symm (hinv := hinv) g2 hw
  have hcoerH := hessG_coercive (hinv := hinv) hg2.le hw hwmin hwmin0.le (by linarith) hcoer
  have hup := hessG_upper (hinv := hinv) hg2.le hw
  refine ⟨fun h hflow => stable_frozen_decay_forward hPisa hPiH hcoerH hflow, ?_⟩
  intro eps h heps hcap hstep
  set rho := g2 * wmin / Bhat ^ 2 with hrho_def
  by_cases hlam : lam = 0
  · -- `L²(0)` is trivial and `‖w‖_{L^∞} = 0`, so the cap forces `ε = 0`
    have hz : ∀ f : Lp ℝ 2 lam, f = 0 := lp_eq_zero_of_measure_zero hlam
    have hw0 : (eLpNorm w ⊤ lam).toReal = 0 := by rw [hlam]; simp
    rw [hw0, mul_zero, inv_zero] at hcap
    have he : eps = 0 := le_antisymm hcap heps
    refine ⟨by rw [he, zero_mul, sub_zero]; exact zero_le_one, fun k => by rw [hz (meanProj lam 2 (h k)),
      hz (meanProj lam 2 (h 0))], fun k => ?_, fun k => ?_⟩
    · rw [hz (h (k + 1) - _), hz (h k - _), norm_zero, mul_zero]
    · rw [hz (h k - _), hz (h 0 - _), norm_zero, mul_zero]
  · have hν : lam Set.univ ≠ 0 := Measure.measure_univ_ne_zero.2 hlam
    have hid : meanProj lam 2 * meanProj lam 2 = meanProj lam 2 := meanProj_idem hν
    have hPiPi : ∀ x : Lp ℝ 2 lam, meanProj lam 2 (meanProj lam 2 x) = meanProj lam 2 x :=
      fun x => congrArg (fun L : Lp ℝ 2 lam →L[ℝ] Lp ℝ 2 lam => L x) hid
    haveI : (ae lam).NeBot := ae_neBot.2 hlam
    have hwle : wmin ≤ (eLpNorm w ⊤ lam).toReal := by
      obtain ⟨x, hx1, hx2⟩ := (hwmin.and (ae_norm_le_linfty hw)).exists
      rw [Real.norm_eq_abs] at hx2
      linarith [le_abs_self (w x)]
    have hs0 := linfty_nonneg (lam := lam) w
    have hepsL : eps * (4 * g2 * (eLpNorm w ⊤ lam).toReal) ≤ 1 :=
      step_cap_mul (by positivity) hcap
    have hrho_le : rho ≤ 4 * g2 * (eLpNorm w ⊤ lam).toReal := by
      have hB2 : 1 ≤ Bhat ^ 2 := one_le_pow₀ hB
      calc rho ≤ g2 * wmin := div_le_self (by positivity) hB2
        _ ≤ 4 * g2 * (eLpNorm w ⊤ lam).toReal := by nlinarith
    have hrho : eps * rho ≤ 1 :=
      (mul_le_mul_of_nonneg_left hrho_le heps).trans hepsL
    have key := stable_frozen_discrete hPisa hPiPi hHsa hPiH hcoerH hup heps hepsL hrho hstep
    refine ⟨by linarith, key.1, fun k => ?_, key.2⟩
    have key' := stable_frozen_discrete (h := fun j => h (k + j)) hPisa hPiPi hHsa hPiH hcoerH
      hup heps hepsL hrho (fun j => hstep (k + j))
    have h1 := key'.2 1
    beta_reduce at h1
    rwa [add_zero, pow_one] at h1

/-- **The mixing sum** `B = ∑_{n≥0} ‖Pⁿ − Π‖_{L²(λ)}` of a Markov kernel's density action
(`Core.Mixing.B`, a `tsum`, meaningful under summability). -/
noncomputable def mixSum (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind ⇑T = lam) : ℝ :=
  Mixing.B (densityActionL2 T lam hinv) (meanProj lam 2)

/-- **`theo:db_stable_frozen_full`, the DB instance from a coercivity constant of `π_←`**: if
`C ≥ 0` is a coercivity constant of `π_←` on `L²(λ)`, then `1 + C` is one of its edge lift `K₂`
on `L²(λ₂)` (`lem:lift_coercivity`), and the two decays hold for the DB loss, `T = K₂`, `λ₂` in
place of `λ`, at rate `g''(1)w_min/(1 + C)²`. -/
theorem db_stable_frozen_DB (T : Kernel S S) [IsMarkovKernel T] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind ⇑T = lam) {C : ℝ} (hC : 0 ≤ C)
    (hcoer : ∀ φ : Lp ℝ 2 lam,
      ‖φ - meanProj lam 2 φ‖ ≤ C * ‖(1 - densityActionL2 T lam hinv) φ‖)
    (g : ℝ → ℝ)
    (hg : (∀ᶠ x in 𝓝 (1 : ℝ), DifferentiableAt ℝ g x) ∧ DifferentiableAt ℝ (deriv g) 1)
    (hg2 : 0 < deriv (deriv g) 1) {w : S × S → ℝ}
    (hw : MemLp w ⊤ (LiftGeneral.edgeMeasure T lam)) {wmin : ℝ} (hwmin0 : 0 < wmin)
    (hwmin : ∀ᵐ p ∂(LiftGeneral.edgeMeasure T lam), wmin ≤ w p) :
    FrozenDecay (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
      (LiftGeneral.edgeMeasure_invariant T lam hinv) (deriv (deriv g) 1) hw wmin (1 + C) :=
  db_stable_frozen_general _ _ _ g hg hg2 hw hwmin0 hwmin (by linarith)
    (LiftGeneral.lift_coercivity_general T lam hinv hC hcoer)

/-- **`theo:db_stable_frozen_full`, the summable-mixing clause, FM loss** (`T = π_←`): when
`π_←` has summable `L²`-mixing, `B = ∑ β_n < ∞`, on a standard Borel space (the paper's Polish
`𝒮`), and its invariant `λ` is non-zero and not a multiple of a Dirac mass, `B̂ := ∑ β̂_n` —
which for `T = π_←` **is** `B` (`mixSum T λ`) — is a coercivity constant with `B̂ ≥ 1`
(`lem:sigma_mixing`), the two decays hold at rate `ϱ = g''(1)w_min/B²`, and
`ϱ ≥ g''(1)w_min/(1 + B)²`. -/
theorem db_stable_frozen_FM_mixing [StandardBorelSpace S] (T : Kernel S S) [IsMarkovKernel T]
    (lam : Measure S) [IsFiniteMeasure lam] [NeZero lam] (hinv : lam.bind ⇑T = lam)
    (hsum : Summable (Mixing.beta (densityActionL2 T lam hinv) (meanProj lam 2)))
    (hdirac : ∀ (c : ℝ≥0∞) (x : S), lam ≠ c • Measure.dirac x)
    (g : ℝ → ℝ)
    (hg : (∀ᶠ x in 𝓝 (1 : ℝ), DifferentiableAt ℝ g x) ∧ DifferentiableAt ℝ (deriv g) 1)
    (hg2 : 0 < deriv (deriv g) 1) {w : S → ℝ} (hw : MemLp w ⊤ lam) {wmin : ℝ}
    (hwmin0 : 0 < wmin) (hwmin : ∀ᵐ x ∂lam, wmin ≤ w x) :
    (∀ h : Lp ℝ 2 lam, ‖h - meanProj lam 2 h‖
      ≤ mixSum T lam hinv * ‖(1 - densityActionL2 T lam hinv) h‖) ∧
    1 ≤ mixSum T lam hinv ∧
    deriv (deriv g) 1 * wmin / (1 + mixSum T lam hinv) ^ 2
      ≤ deriv (deriv g) 1 * wmin / mixSum T lam hinv ^ 2 ∧
    FrozenDecay T lam hinv (deriv (deriv g) 1) hw wmin (mixSum T lam hinv) := by
  have hlem := lem_sigma_mixing T lam hinv hsum
  have hco : ∀ h : Lp ℝ 2 lam, ‖h - meanProj lam 2 h‖
      ≤ mixSum T lam hinv * ‖(1 - densityActionL2 T lam hinv) h‖ := hlem.1.2.2
  have hB : 1 ≤ mixSum T lam hinv := (hlem.2 hdirac).2
  refine ⟨hco, hB, ?_, db_stable_frozen_general T lam hinv g hg hg2 hw hwmin0 hwmin hB hco⟩
  have hB0 : 0 < mixSum T lam hinv := by linarith
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

/-- **`theo:db_stable_frozen_full`, the summable-mixing clause, DB loss** (`T = K₂` on `λ₂`):
when `π_←` has summable `L²`-mixing, `B = ∑ β_n < ∞`, on a standard Borel space, and its
invariant `λ` is non-zero and not a multiple of a Dirac mass, the edge lift's mixing
coefficients are summable, `B̂ := ∑ β̂_n` (computed for `K₂` on `L²(λ₂)`) is a coercivity
constant of `K₂` with `B̂ = 1 + B ≥ 1` (`lem:lift_mixing`, `lem:sigma_mixing`), and the two
decays hold for the DB loss at rate `g''(1)w_min/(1 + B)²`. -/
theorem db_stable_frozen_DB_mixing [StandardBorelSpace S] (T : Kernel S S) [IsMarkovKernel T]
    (lam : Measure S) [IsFiniteMeasure lam] [NeZero lam] (hinv : lam.bind ⇑T = lam)
    (hsum : Summable (Mixing.beta (densityActionL2 T lam hinv) (meanProj lam 2)))
    (hdirac : ∀ (c : ℝ≥0∞) (x : S), lam ≠ c • Measure.dirac x)
    (g : ℝ → ℝ)
    (hg : (∀ᶠ x in 𝓝 (1 : ℝ), DifferentiableAt ℝ g x) ∧ DifferentiableAt ℝ (deriv g) 1)
    (hg2 : 0 < deriv (deriv g) 1) {w : S × S → ℝ}
    (hw : MemLp w ⊤ (LiftGeneral.edgeMeasure T lam)) {wmin : ℝ} (hwmin0 : 0 < wmin)
    (hwmin : ∀ᵐ p ∂(LiftGeneral.edgeMeasure T lam), wmin ≤ w p) :
    Summable (Mixing.beta (densityActionL2 (LiftGeneral.edgeLift T)
      (LiftGeneral.edgeMeasure T lam) (LiftGeneral.edgeMeasure_invariant T lam hinv))
      (meanProj (LiftGeneral.edgeMeasure T lam) 2)) ∧
    (∀ h : Lp ℝ 2 (LiftGeneral.edgeMeasure T lam),
      ‖h - meanProj (LiftGeneral.edgeMeasure T lam) 2 h‖
        ≤ mixSum (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
            (LiftGeneral.edgeMeasure_invariant T lam hinv)
          * ‖(1 - densityActionL2 (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
              (LiftGeneral.edgeMeasure_invariant T lam hinv)) h‖) ∧
    mixSum (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
        (LiftGeneral.edgeMeasure_invariant T lam hinv) = 1 + mixSum T lam hinv ∧
    1 ≤ mixSum (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
        (LiftGeneral.edgeMeasure_invariant T lam hinv) ∧
    FrozenDecay (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
      (LiftGeneral.edgeMeasure_invariant T lam hinv) (deriv (deriv g) 1) hw wmin
      (1 + mixSum T lam hinv) := by
  have hsum2 := (LiftGeneral.lift_mixing_summable_iff T lam hinv).2 hsum
  obtain ⟨X, hX, hX0, hX1⟩ := exists_measurableSet_of_ne_smul_dirac hdirac
  have hBeq : mixSum (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
      (LiftGeneral.edgeMeasure_invariant T lam hinv) = 1 + mixSum T lam hinv :=
    LiftGeneral.lift_mixing_B_eq_one_add T lam hinv hsum hX hX0 hX1
  have hco := (sigma_mixing (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
    (LiftGeneral.edgeMeasure_invariant T lam hinv) hsum2).2.2
  have hB0 : 0 ≤ mixSum T lam hinv := Mixing.B_nonneg _ _
  have hB : 1 ≤ mixSum (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
      (LiftGeneral.edgeMeasure_invariant T lam hinv) := by rw [hBeq]; linarith
  refine ⟨hsum2, hco, hBeq, hB, ?_⟩
  have hco' : ∀ h : Lp ℝ 2 (LiftGeneral.edgeMeasure T lam),
      ‖h - meanProj (LiftGeneral.edgeMeasure T lam) 2 h‖
        ≤ (1 + mixSum T lam hinv)
          * ‖(1 - densityActionL2 (LiftGeneral.edgeLift T) (LiftGeneral.edgeMeasure T lam)
              (LiftGeneral.edgeMeasure_invariant T lam hinv)) h‖ := by
    intro h; rw [← hBeq]; exact hco h
  exact db_stable_frozen_general _ _ _ g hg hg2 hw hwmin0 hwmin (by linarith) hco'

/-- **The flow hypothesis of `FrozenDecay` is inhabited from every initial condition**
(kb `0025`): `t ↦ exp(−tH)h₀` solves `ḣ = −Hh` at every `t ≥ 0` and starts at `h₀`, so the
continuous conclusion applies to it. -/
theorem frozenDecay_flow_apply {T : Kernel S S} [IsMarkovKernel T] {lam : Measure S}
    [IsFiniteMeasure lam] {hinv : lam.bind ⇑T = lam} {g2 : ℝ} {w : S → ℝ} {hw : MemLp w ⊤ lam}
    {wmin Bhat : ℝ} (hD : FrozenDecay T lam hinv g2 hw wmin Bhat) (h0 : Lp ℝ 2 lam) :
    (∀ t : ℝ, 0 ≤ t → meanProj lam 2 (NormedSpace.exp (t • -hessG T lam hinv g2 hw) h0)
      = meanProj lam 2 h0) ∧
    ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • -hessG T lam hinv g2 hw) h0
        - meanProj lam 2 (NormedSpace.exp (t • -hessG T lam hinv g2 hw) h0)‖
      ≤ Real.exp (-(g2 * wmin / Bhat ^ 2 * t)) * ‖h0 - meanProj lam 2 h0‖ := by
  have key := hD.1 (fun s => NormedSpace.exp (s • -hessG T lam hinv g2 hw) h0)
    (fun t _ => linearFlow_hasDerivAt _ h0 t)
  simp only [linearFlow_zero] at key
  exact key

end Main

/-! ### Inhabitation: the paper's two-state chain -/

section Witness

/-- `g(x) = x²`: `g''(1) = 2`. -/
theorem deriv_deriv_sq_one : deriv (deriv fun x : ℝ => x ^ 2) 1 = 2 := by
  have h : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
    funext x; simp
  rw [h]; simp

/-- **Inhabitation of the whole hypothesis bundle of `db_stable_frozen_FM_mixing`**
(kb `0025`, `0027`), on the two-state chain `T(i → j) = 1/2`, `λ = (1/2, 1/2)` of
`prop:nonlinear_freezing`(2) (`Kernel.const Bool λ`, `Core.sigma_mixing_witness`), with
`g(x) = x²`, `w ≡ 1`, `w_min = 1`: the mixing clause fires, `B = 1`, and the decays hold at
`ϱ = g''(1)w_min/B² = 2`. -/
theorem stable_frozen_witness :
    mixSum (Kernel.const Bool boolUniform) boolUniform Family.bind_const_kernel = 1 ∧
    FrozenDecay (Kernel.const Bool boolUniform) boolUniform Family.bind_const_kernel
      (deriv (deriv fun x : ℝ => x ^ 2) 1) (memLp_top_const (μ := boolUniform) (1 : ℝ)) 1
      (mixSum (Kernel.const Bool boolUniform) boolUniform Family.bind_const_kernel) := by
  obtain ⟨_, hnd, hsum, _, hB⟩ := sigma_mixing_witness
  have hg : (∀ᶠ x in 𝓝 (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ => x ^ 2) x) ∧
      DifferentiableAt ℝ (deriv fun x : ℝ => x ^ 2) 1 := by
    refine ⟨Filter.Eventually.of_forall fun x => by fun_prop, ?_⟩
    have h : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
      funext x; simp
    rw [h]; fun_prop
  have hg2 : 0 < deriv (deriv fun x : ℝ => x ^ 2) 1 := by rw [deriv_deriv_sq_one]; norm_num
  refine ⟨hB, (db_stable_frozen_FM_mixing (Kernel.const Bool boolUniform) boolUniform
    Family.bind_const_kernel hsum hnd (fun x : ℝ => x ^ 2) hg hg2
    (memLp_top_const (μ := boolUniform) (1 : ℝ)) one_pos
    (Filter.Eventually.of_forall fun _ => le_rfl)).2.2.2⟩

end Witness

end GFNBounds.Balance.StableFrozenGeneral
