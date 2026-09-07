import GFNBounds.Doubling.LpLayer
import GFNBounds.Doubling.Unbounded

/-!
# An `L²` pair with no exact `L²` outflow

**`prop:doubling_unsolvable`** — `app_doubling.tex:2126–2181`.

> In the setting of Definition~\ref{def:doubling_setting}, let the backward policy be
> `eq:doubling_policy` with `ε(j) > 0` for every `j ≥ 1` and `ε_max = sup_{j≥1} ε(j) < 1`, let the
> loop-closed chain be positive recurrent with invariant probability `λ`, and assume
> `eq:doubling_star`. Then:
> *(1)* `(Id − P⋆)L²(λ)` is a dense proper linear subspace of `ker Π`;
> *(2)* there are probability densities `f_init, f_term ∈ L²(λ)` such that no `f ∈ L²(λ)`
> satisfies `(Id − P⋆)f = f_init − f_term`.

## What the proof runs on

The analysis is `theo:doubling_unbounded`(2) at `p = 2`, already proved: `eq:doubling_inf` is
`Stat.exists_small_mass_ratio`, and `Stat.exists_small_defect` is that inequality read as
`‖(Id − P⋆)F‖² ≤ t‖F‖²` on `L²(μ)` through the norm identification of `LpLayer.lean`. What this
file adds is the functional analysis around it:

* `Stat.tsum_pstar_eq` — `λ` is `P⋆`-invariant against every `f` with `λ|f|` summable, hence
  against every `f ∈ L²(λ)`. `Stat.inv` is stated for bounded test functions and
  `Stat.tsum_pstar_le` (`LpLayer.lean`) gives one inequality; the other is the same truncation
  read on finite partial sums. This is what puts the range of `Id − P⋆` inside `ker Π` and `1` in
  its orthogonal complement.
* `fixed_of_mem_orthogonal_range` — for a contraction `Q` of a Hilbert space, a vector orthogonal
  to the range of `Id − Q` is a fixed point of `Q`. With `Stat.fixed_const_memLp` this gives
  `((Id − P⋆)L²)ᗮ = ℝ·1`, hence `Stat.topologicalClosure_defectRange`.
* `exists_lower_bound_of_bijective` — the open mapping theorem
  (`ContinuousLinearEquiv.ofBijective`), in the form "a bijective bounded operator is bounded
  below", against which `eq:doubling_inf` refutes surjectivity
  (`Stat.defectRange_ne_kerPi`).

## SCOPE (disclosed)

* **This refutes exact `L²` flow matching, not weak universality.** Item (1) delivers a *dense*
  range, so the conclusion of `theo:universality_L2` — a defect infimum of zero — is not
  contradicted, and whether weak universality fails on the infinite chain stays open. The
  appendix flags this itself and this file does not go past it.
* **The witness pair of item (2) is non-explicit**, by construction: `ψ` is produced by the open
  mapping argument and only known to lie outside a proper subspace, so the Lean statement is an
  `∃` and nothing here computes `f_init` or `f_term`.
* **The adjoint is not used, and `lem:doubling_operator`(1) is not assumed.** The paper argues
  that `A` has dense range from `ker A* = 0`, using `P⋆ = P*` and the `P` half of
  `lem:doubling_fixed_points`; neither is available here, `P` not being modelled
  (`LpLayer.lean`, SCOPE). The same content is delivered by `fixed_of_mem_orthogonal_range`,
  which needs only that `P⋆` is a contraction — the `p = 2` clause of `lem:doubling_operator`(1),
  proved in `LpLayer.lean` as `Stat.norm_pstarL2_le`. Nothing in this file is conditional.
* **`ker Π` is `(ℝ·1)ᗮ`**, and `Stat.mem_kerPi_iff` is the identification with the classes of
  zero `λ`-mean, which is what `Π` means. Density is stated in the ambient `L²(μ)` as
  `Submodule.topologicalClosure (Id − P⋆)L² = ker Π` rather than inside `ker Π` as a subtype;
  the two say the same thing, `ker Π` being closed.
* **`L²(λ)` is a space of classes**, so item (2)'s equation is stated `λ`-a.e. On the loop
  closure `λ` is positive at every state, so a.e. equality *is* equality (`Stat.ae_iff_eq`) and
  the a.e. reading — which is the `L²(λ)` reading, and the stronger non-existence statement — is
  the same as the pointwise one.
* The chain is the loop closure (`cap = none`), as in the paper; the `RowOnChain` hypothesis that
  `LpLayer.lean`'s `L²` operator carries is then vacuous (`rowOnChain_none`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ε(j) > 0` for `j ≥ 1` | ✓ carried by `Setting` |
| `ε_max = sup ε < 1` | ✓ carried by `Setting` |
| positive recurrence, `λ` its invariant probability | ✓ carried as `Stat S none` |
| `eq:doubling_star` (★) | ✓ carried as `GrowthCond S` |
| (★), for the *dense* half of item (1) | ⚠ **weakened**: `Stat.topologicalClosure_defectRange` needs no growth condition; (★) enters only through properness |
| `f_init, f_term` are probability densities in `L²(λ)` | ✓ carried (non-negative, `MemLp _ 2`, `λ`-mass `1`) |
| `lem:doubling_fixed_points`, the `P⋆` half | ✓ carried (`Stat.fixed_const_memLp`) |
| `lem:doubling_operator`(1), `P⋆ = P*` | ⚠ **not needed** — the route replaces it; see SCOPE |
| `lem:doubling_fixed_points`, the `P` half | ⚠ **not needed** — same |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology Real
open scoped ENNReal NNReal InnerProductSpace

variable {S : Setting} {cap : Option ℕ}

/-! ## 0. `P⋆` is linear on differences -/

theorem pstar_sub {f g : St → ℝ} :
    pstar S cap (f - g) = pstar S cap f - pstar S cap g := by
  have h : f - g = f + (-1 : ℝ) • g := by funext x; simp; ring
  rw [h, pstar_add, pstar_smul]
  funext x; simp; ring

private theorem tendsto_min_nat (a : ℝ) :
    Tendsto (fun n : ℕ => min a (n : ℝ)) atTop (𝓝 a) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop ⌈a⌉₊] with n hn
  exact (min_eq_left ((Nat.le_ceil a).trans (by exact_mod_cast hn))).symm

/-! ## 1. `λ` is invariant against a square-integrable function -/

namespace Stat

variable (L : Stat S cap)

/-- **Invariance against an unbounded non-negative function**, as an equality. `Stat.inv` is
stated for bounded `f` and `Stat.tsum_pstar_le` extends it to an inequality; the reverse
inequality is the same truncation read on finite partial sums. -/
theorem tsum_pstar_eq_of_nonneg {g : St → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hsum : Summable fun x => L.lam x * g x) :
    ∑' x, L.lam x * pstar S cap g x = ∑' x, L.lam x * g x := by
  obtain ⟨hsummP, hle⟩ := L.tsum_pstar_le hg hsum
  refine le_antisymm hle ?_
  set T : ℕ → St → ℝ := fun n y => min (g y) (n : ℝ) with hTdef
  have hTnn : ∀ n x, 0 ≤ T n x := fun n x => le_min (hg x) (Nat.cast_nonneg n)
  have hTb : ∀ n : ℕ, ∃ C, ∀ x, |T n x| ≤ C := fun n =>
    ⟨(n : ℝ), fun x => by rw [abs_of_nonneg (hTnn n x)]; exact min_le_right _ _⟩
  have hTle : ∀ n x, T n x ≤ g x := fun _ x => min_le_left _ _
  have key : ∀ s : Finset St, ∑ x ∈ s, L.lam x * g x ≤ ∑' x, L.lam x * pstar S cap g x := by
    intro s
    have hlim : Tendsto (fun n => ∑ x ∈ s, L.lam x * T n x) atTop
        (𝓝 (∑ x ∈ s, L.lam x * g x)) :=
      tendsto_finsetSum _ fun x _ => (tendsto_min_nat (g x)).const_mul _
    refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hsummT : Summable fun x => L.lam x * pstar S cap (T n) x := by
      obtain ⟨C, hC⟩ := hTb n
      exact L.summable_mul ⟨C, fun x => pstar_bounded hC x⟩
    have h1 : ∑ x ∈ s, L.lam x * T n x ≤ ∑' x, L.lam x * T n x :=
      (L.summable_mul (hTb n)).sum_le_tsum s fun x _ => mul_nonneg (L.nonneg x) (hTnn n x)
    have h2 : ∑' x, L.lam x * T n x = ∑' x, L.lam x * pstar S cap (T n) x := (L.inv _ (hTb n)).symm
    have h3 : ∑' x, L.lam x * pstar S cap (T n) x ≤ ∑' x, L.lam x * pstar S cap g x :=
      hsummT.tsum_le_tsum
        (fun x => mul_le_mul_of_nonneg_left (pstar_mono (hTle n) x) (L.nonneg x)) hsummP
    linarith
  exact hsum.tsum_le_of_sum_le key

/-- **Invariance against a signed integrable function.** `λ` is `P⋆`-invariant against every
`f` with `λ·|f|` summable: split into positive and negative parts. -/
theorem tsum_pstar_eq {f : St → ℝ} (hsum : Summable fun x => L.lam x * |f x|) :
    ∑' x, L.lam x * pstar S cap f x = ∑' x, L.lam x * f x := by
  set fp : St → ℝ := fun x => max (f x) 0 with hfp
  set fm : St → ℝ := fun x => max (-f x) 0 with hfm
  have hfpn : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfmn : ∀ x, 0 ≤ fm x := fun x => le_max_right _ _
  have hsp : Summable fun x => L.lam x * fp x :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (L.nonneg x) (hfpn x))
      (fun x => mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (L.nonneg x))
      hsum
  have hsm : Summable fun x => L.lam x * fm x :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (L.nonneg x) (hfmn x))
      (fun x => mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _)) (L.nonneg x))
      hsum
  have hsplit : f = fp - fm := by
    funext x
    simp only [hfp, hfm, Pi.sub_apply]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  obtain ⟨hPp, -⟩ := L.tsum_pstar_le hfpn hsp
  obtain ⟨hPm, -⟩ := L.tsum_pstar_le hfmn hsm
  have hPsplit : (fun x => L.lam x * pstar S cap f x)
      = fun x => L.lam x * pstar S cap fp x - L.lam x * pstar S cap fm x := by
    funext x
    rw [hsplit, pstar_sub]
    simp only [Pi.sub_apply]
    ring
  have hsplit' : (fun x => L.lam x * f x)
      = fun x => L.lam x * fp x - L.lam x * fm x := by
    funext x; rw [hsplit]; simp only [Pi.sub_apply]; ring
  rw [hPsplit, hsplit', Summable.tsum_sub hPp hPm, Summable.tsum_sub hsp hsm,
    L.tsum_pstar_eq_of_nonneg hfpn hsp, L.tsum_pstar_eq_of_nonneg hfmn hsm]

/-! ## 2. The constants, the mean, and invariance in `L²` -/

/-- The constant function `1` as an element of `L²(μ)`; `μ` is a probability. -/
noncomputable def oneLp : Lp ℝ 2 L.mu := MemLp.toLp (fun _ => (1 : ℝ)) (memLp_const 1)

theorem coeFn_oneLp : ⇑L.oneLp =ᵐ[L.mu] (fun _ => (1 : ℝ)) := MemLp.coeFn_toLp _

theorem norm_oneLp : ‖L.oneLp‖ = 1 := by
  rw [oneLp, Lp.norm_toLp,
    eLpNorm_const (μ := L.mu) (1 : ℝ) (by norm_num) (IsProbabilityMeasure.ne_zero L.mu)]
  simp

/-- `λ·|f|` is summable at every `f ∈ L²(λ)`: `λ` is a probability. -/
theorem summable_lam_abs {f : St → ℝ} (hf : MemLp f 2 L.mu) :
    Summable fun x => L.lam x * |f x| := by
  have h1 : MemLp f 1 L.mu := hf.mono_exponent one_le_two
  have h2 := (L.memLp_iff (p := 1) one_ne_zero (by norm_num)).mp h1
  simp only [ENNReal.toReal_one, Real.rpow_one] at h2
  exact h2.congr fun x => mul_comm _ _

/-- The `μ`-integral is the `λ`-weighted sum. -/
theorem integral_eq_tsum {f : St → ℝ} (hf : MemLp f 2 L.mu) :
    ∫ x, f x ∂L.mu = ∑' x, L.lam x * f x := by
  rw [integral_countable (hf.integrable one_le_two)]
  refine tsum_congr fun x => ?_
  rw [measureReal_def, L.mu_singleton, ENNReal.toReal_ofReal (L.nonneg x), smul_eq_mul]

/-- **`Π`, read as an inner product.** `⟪1, F⟫ = ∫ F dλ`. -/
theorem inner_oneLp (F : Lp ℝ 2 L.mu) : ⟪L.oneLp, F⟫_ℝ = ∑' x, L.lam x * F x := by
  rw [L2.inner_def]
  have hint : ∫ a, ⟪(L.oneLp : St → ℝ) a, (F : St → ℝ) a⟫_ℝ ∂L.mu
      = ∫ a, (F : St → ℝ) a ∂L.mu := by
    refine integral_congr_ae ?_
    filter_upwards [L.coeFn_oneLp] with x hx
    rw [Real.inner_apply, hx, one_mul]
  rw [hint, L.integral_eq_tsum (Lp.memLp F)]

/-- **`P⋆` preserves the mean on `L²`.** This is `λ`-invariance, tested against a
square-integrable function. -/
theorem inner_oneLp_pstarLp (F : Lp ℝ 2 L.mu) :
    ⟪L.oneLp, L.pstarLp F⟫_ℝ = ⟪L.oneLp, F⟫_ℝ := by
  rw [L.inner_oneLp, L.inner_oneLp]
  have h : ∀ x, L.lam x * (L.pstarLp F : St → ℝ) x
      = L.lam x * pstar S cap (F : St → ℝ) x := by
    intro x
    by_cases hx : OnChain cap x
    · rw [L.ae_iff_eq.mp (L.coeFn_pstarLp F) x hx]
    · rw [L.vanish hx, zero_mul, zero_mul]
  rw [tsum_congr h, L.tsum_pstar_eq (L.summable_lam_abs (Lp.memLp F))]

/-- **`P⋆1 = 1` in `L²`.** -/
theorem pstarLp_oneLp (hrow : RowOnChain S cap) : L.pstarLp L.oneLp = L.oneLp := by
  refine Lp.ext ?_
  have hcong : ∀ x, OnChain cap x → pstar S cap ⇑L.oneLp x = pstar S cap (fun _ => (1 : ℝ)) x :=
    fun _ hx => pstar_congr_onChain hrow (L.ae_iff_eq.mp L.coeFn_oneLp) hx
  filter_upwards [L.coeFn_pstarLp L.oneLp, L.ae_eq_of_onChain hcong, L.coeFn_oneLp]
    with x h1 h2 h3
  rw [h1, h2, h3]
  simp only [pstar_const]

end Stat


/-! ## 3. Two facts about a contraction of a Hilbert space -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The step `lem:doubling_fixed_points` takes from `P⋆` to `P`.** For a contraction `Q` of a
Hilbert space, a vector orthogonal to the range of `Id − Q` is a fixed point of `Q` — the paper's
`ker(Id − Q*) ⊆ ker(Id − Q)`, in the form that needs no adjoint. -/
theorem fixed_of_mem_orthogonal_range {Q : E →L[ℝ] E} (hQ : ‖Q‖ ≤ 1) {g : E}
    (hg : g ∈ (LinearMap.range (((1 : E →L[ℝ] E) - Q : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ) : Q g = g := by
  have hall : ∀ y : E, ⟪y - Q y, g⟫_ℝ = 0 := by
    intro y
    refine (Submodule.mem_orthogonal _ _).mp hg _ ⟨y, ?_⟩
    simp
  refine eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) ?_ ?_
  · exact (Q.le_of_opNorm_le hQ g).trans_eq (by simp)
  · have h := hall g
    rw [inner_sub_left, sub_eq_zero] at h
    simp only [RCLike.re_to_real]
    rw [← h, real_inner_self_eq_norm_sq]

variable [CompleteSpace E]

/-- **The open mapping theorem, in the form the proof uses.** A bijective bounded operator of a
Hilbert space is bounded below. -/
theorem exists_lower_bound_of_bijective {A : E →L[ℝ] E}
    (hker : LinearMap.ker (A : E →ₗ[ℝ] E) = ⊥) (hran : LinearMap.range (A : E →ₗ[ℝ] E) = ⊤) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : E, ‖f‖ ≤ K * ‖A f‖ := by
  let e := ContinuousLinearEquiv.ofBijective A hker hran
  refine ⟨‖(e.symm : E →L[ℝ] E)‖ + 1, by positivity, fun f => ?_⟩
  have hf : (e.symm : E →L[ℝ] E) (A f) = f := by
    have hef : e f = A f := rfl
    rw [← hef]
    exact e.symm_apply_apply f
  calc ‖f‖ = ‖(e.symm : E →L[ℝ] E) (A f)‖ := by rw [hf]
    _ ≤ ‖(e.symm : E →L[ℝ] E)‖ * ‖A f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖(e.symm : E →L[ℝ] E)‖ + 1) * ‖A f‖ := by
        have h0 : 0 ≤ ‖A f‖ := norm_nonneg _
        nlinarith

end Hilbert

/-! ## 4. `Id − P⋆` and `ker Π` on the loop closure -/

namespace Stat

variable (L : Stat S none)

/-- **`Id − P⋆`** as a bounded operator of `L²(λ)`, on the loop closure. -/
noncomputable def defect : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu := 1 - L.pstarL2 (rowOnChain_none S)

theorem defect_apply (F : Lp ℝ 2 L.mu) : L.defect F = F - L.pstarLp F := rfl

/-- **`ker Π`**, the classes of `L²(λ)` of zero `λ`-mean. -/
noncomputable def kerPi : Submodule ℝ (Lp ℝ 2 L.mu) := (ℝ ∙ L.oneLp)ᗮ

/-- **`(Id − P⋆)L²(λ)`**. -/
noncomputable def defectRange : Submodule ℝ (Lp ℝ 2 L.mu) :=
  LinearMap.range (L.defect : Lp ℝ 2 L.mu →ₗ[ℝ] Lp ℝ 2 L.mu)

/-- `ker Π` is what its name says: `F` has zero mean. -/
theorem mem_kerPi_iff {F : Lp ℝ 2 L.mu} : F ∈ L.kerPi ↔ ∑' x, L.lam x * F x = 0 := by
  rw [kerPi, Submodule.mem_orthogonal_singleton_iff_inner_right, L.inner_oneLp]

/-- The defect of any class has zero mean: `Π(Id − P⋆) = 0`. -/
theorem defectRange_le_kerPi : L.defectRange ≤ L.kerPi := by
  rintro _ ⟨F, rfl⟩
  rw [kerPi, Submodule.mem_orthogonal_singleton_iff_inner_right]
  show ⟪L.oneLp, L.defect F⟫_ℝ = 0
  rw [defect_apply, inner_sub_right, L.inner_oneLp_pstarLp, sub_self]

/-- A fixed point of `P⋆` in `L²(λ)` is a constant class: `lem:doubling_fixed_points`, `P⋆` half,
transported to `Lp`. -/
theorem eq_smul_oneLp_of_fixed {F : Lp ℝ 2 L.mu} (hF : L.pstarLp F = F) :
    F = (F : St → ℝ) (.lad 0) • L.oneLp := by
  have hae : ∀ x, OnChain none x → pstar S none (F : St → ℝ) x = (F : St → ℝ) x := by
    have h := (L.coeFn_pstarLp F).symm.trans (by rw [hF] : ⇑(L.pstarLp F) =ᵐ[L.mu] ⇑F)
    exact L.ae_iff_eq.mp h
  have hconst := L.fixed_const_memLp (Lp.memLp F) hae
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul ((F : St → ℝ) (.lad 0)) L.oneLp, L.coeFn_oneLp] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, mul_one]
  exact hconst x trivial

/-- `1` is orthogonal to every defect. -/
theorem oneLp_mem_orthogonal : L.oneLp ∈ L.defectRangeᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨F, rfl⟩
  show ⟪L.defect F, L.oneLp⟫_ℝ = 0
  rw [real_inner_comm, defect_apply, inner_sub_right, L.inner_oneLp_pstarLp, sub_self]

/-- **The orthogonal complement of the range of `Id − P⋆` is the line of constants.** -/
theorem orthogonal_defectRange : L.defectRangeᗮ = ℝ ∙ L.oneLp := by
  refine le_antisymm (fun g hg => ?_) ?_
  · have hfix : L.pstarL2 (rowOnChain_none S) g = g :=
      fixed_of_mem_orthogonal_range (L.norm_pstarL2_le (rowOnChain_none S)) hg
    rw [L.eq_smul_oneLp_of_fixed hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact L.oneLp_mem_orthogonal

/-! ## 5. The range is dense in `ker Π` -/

/-- **`prop:doubling_unsolvable`(1), the dense half.** The closure of `(Id − P⋆)L²(λ)` is
`ker Π`. -/
theorem topologicalClosure_defectRange : L.defectRange.topologicalClosure = L.kerPi := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, L.orthogonal_defectRange, kerPi]

/-! ## 6. The range is proper -/

theorem coeFn_defect (F : Lp ℝ 2 L.mu) :
    ⇑(L.defect F) =ᵐ[L.mu] fun x => (F : St → ℝ) x - pstar S none (F : St → ℝ) x := by
  have h0 : ⇑(L.defect F) =ᵐ[L.mu] ⇑F - ⇑(L.pstarLp F) := by
    rw [defect_apply]; exact Lp.coeFn_sub _ _
  filter_upwards [h0, L.coeFn_pstarLp F] with x h1 h2
  rw [h1, Pi.sub_apply, h2]

theorem coeFn_defect_toLp {f : St → ℝ} (hf : MemLp f 2 L.mu) :
    ⇑(L.defect (hf.toLp f)) =ᵐ[L.mu] fun x => f x - pstar S none f x := by
  have hcong : ∀ x, OnChain none x → pstar S none ⇑(hf.toLp f) x = pstar S none f x :=
    fun _ hx => pstar_congr_onChain (rowOnChain_none S) (L.ae_iff_eq.mp (MemLp.coeFn_toLp hf)) hx
  filter_upwards [L.coeFn_defect (hf.toLp f), MemLp.coeFn_toLp hf,
    L.ae_eq_of_onChain hcong] with x h1 h2 h3
  rw [h1, h2, h3]

/-- The `L²` norm squared of a class is the `mass` of any of its representatives. -/
theorem norm_sq_eq_mass {F : Lp ℝ 2 L.mu} {g : St → ℝ} (h : ⇑F =ᵐ[L.mu] g)
    (hg : MemLp g 2 L.mu) : ‖F‖ ^ 2 = L.mass 2 g := by
  rw [Lp.norm_def, ← L.toReal_eLpNorm_two_sq hg, eLpNorm_congr_ae h]

/-- The `λ`-mean of a class is the `λ`-mean of any of its representatives. -/
theorem tsum_lam_congr_ae {F : Lp ℝ 2 L.mu} {g : St → ℝ} (h : ⇑F =ᵐ[L.mu] g) :
    ∑' x, L.lam x * (F : St → ℝ) x = ∑' x, L.lam x * g x := by
  refine tsum_congr fun x => ?_
  by_cases hx : OnChain none x
  · rw [L.ae_iff_eq.mp h x hx]
  · rw [L.vanish hx, zero_mul, zero_mul]

theorem memLp_centredTail (m : ℕ) : MemLp (L.centredTail m) 2 L.mu := by
  obtain ⟨C, hC⟩ := L.centredTail_bounded m
  refine MemLp.of_bound (L.aestronglyMeasurable _) C (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hC x

/-- **`eq:doubling_inf` at `p = 2`, in `L²(λ)`.** For every `t > 0` some non-zero mean-zero class
has `‖(Id − P⋆)F‖² ≤ t‖F‖²`. -/
theorem exists_small_defect (hstar : GrowthCond S) {t : ℝ} (ht : 0 < t) :
    ∃ F : Lp ℝ 2 L.mu, F ∈ L.kerPi ∧ F ≠ 0 ∧ ‖L.defect F‖ ^ 2 ≤ t * ‖F‖ ^ 2 := by
  obtain ⟨m, hmd, hbound⟩ := L.exists_small_mass_ratio hstar (by norm_num : (1:ℝ) ≤ 2) ht
  have hm1 : 1 < m := by have := S.d_pos; omega
  have hf := L.memLp_centredTail m
  refine ⟨hf.toLp _, ?_, ?_, ?_⟩
  · rw [L.mem_kerPi_iff, L.tsum_lam_congr_ae (MemLp.coeFn_toLp hf)]
    exact L.tsum_centredTail m
  · intro h0
    have hnorm : ‖hf.toLp (L.centredTail m)‖ ^ 2 = L.mass 2 (L.centredTail m) :=
      L.norm_sq_eq_mass (MemLp.coeFn_toLp hf) hf
    have hpos : 0 < L.mass 2 (L.centredTail m) :=
      lt_of_lt_of_le (mul_pos (L.tailMass_pos m) (Real.rpow_pos_of_pos (L.coTail_pos hm1) 2))
        (L.mass_centredTail_ge m 2)
    rw [h0] at hnorm
    simp only [norm_zero] at hnorm
    nlinarith
  · have hnum : ‖L.defect (hf.toLp (L.centredTail m))‖ ^ 2
        = L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x) :=
      L.norm_sq_eq_mass (L.coeFn_defect_toLp hf) (hf.sub (L.memLp_two_pstar hf))
    have hden : ‖hf.toLp (L.centredTail m)‖ ^ 2 = L.mass 2 (L.centredTail m) :=
      L.norm_sq_eq_mass (MemLp.coeFn_toLp hf) hf
    rw [hnum, hden]
    exact hbound

theorem eq_zero_of_mem_kerPi_of_fixed {F : Lp ℝ 2 L.mu} (hmem : F ∈ L.kerPi)
    (hfix : L.pstarLp F = F) : F = 0 := by
  have hc := L.eq_smul_oneLp_of_fixed hfix
  have hin : ⟪L.oneLp, F⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
  rw [hc, real_inner_smul_right, real_inner_self_eq_norm_sq, L.norm_oneLp, one_pow,
    mul_one] at hin
  rw [hc, hin, zero_smul]

theorem sub_mean_mem_kerPi (F : Lp ℝ 2 L.mu) : F - ⟪L.oneLp, F⟫_ℝ • L.oneLp ∈ L.kerPi := by
  rw [kerPi, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, L.norm_oneLp, one_pow, mul_one, sub_self]

theorem defect_oneLp : L.defect L.oneLp = 0 := by
  rw [defect_apply, L.pstarLp_oneLp (rowOnChain_none S), sub_self]

theorem defect_sub_mean (F : Lp ℝ 2 L.mu) :
    L.defect (F - ⟪L.oneLp, F⟫_ℝ • L.oneLp) = L.defect F := by
  rw [map_sub, map_smul, L.defect_oneLp, smul_zero, sub_zero]

/-- **`prop:doubling_unsolvable`(1), the proper half.** `(Id − P⋆)L²(λ)` is not all of `ker Π`:
were it, the open mapping theorem would bound `Id − P⋆` below on `ker Π`, against
`eq:doubling_inf`. -/
theorem defectRange_ne_kerPi (hstar : GrowthCond S) : L.defectRange ≠ L.kerPi := by
  intro hEq
  have hmaps : ∀ x ∈ L.kerPi, L.defect x ∈ L.kerPi := fun x _ =>
    L.defectRange_le_kerPi ⟨x, rfl⟩
  set A : L.kerPi →L[ℝ] L.kerPi := L.defect.restrict hmaps with hA
  have hAcoe : ∀ F : L.kerPi, ((A F : Lp ℝ 2 L.mu)) = L.defect (F : Lp ℝ 2 L.mu) := fun _ => rfl
  have hker : LinearMap.ker (A : L.kerPi →ₗ[ℝ] L.kerPi) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro F hF
    have h0 : L.defect (F : Lp ℝ 2 L.mu) = 0 := congrArg Subtype.val hF
    have hfix : L.pstarLp (F : Lp ℝ 2 L.mu) = (F : Lp ℝ 2 L.mu) := by
      rw [defect_apply, sub_eq_zero] at h0
      exact h0.symm
    exact Subtype.ext (L.eq_zero_of_mem_kerPi_of_fixed F.2 hfix)
  have hran : LinearMap.range (A : L.kerPi →ₗ[ℝ] L.kerPi) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro G
    have hG : (G : Lp ℝ 2 L.mu) ∈ L.defectRange := by rw [hEq]; exact G.2
    obtain ⟨F, hF⟩ := hG
    refine ⟨⟨F - ⟪L.oneLp, F⟫_ℝ • L.oneLp, L.sub_mean_mem_kerPi F⟩, Subtype.ext ?_⟩
    show L.defect (F - ⟪L.oneLp, F⟫_ℝ • L.oneLp) = (G : Lp ℝ 2 L.mu)
    rw [L.defect_sub_mean]
    exact hF
  haveI : CompleteSpace L.kerPi := by
    show CompleteSpace ((ℝ ∙ L.oneLp)ᗮ : Submodule ℝ (Lp ℝ 2 L.mu))
    infer_instance
  obtain ⟨K, hKpos, hK⟩ := exists_lower_bound_of_bijective hker hran
  obtain ⟨F, hFmem, hFne, hFbound⟩ :=
    L.exists_small_defect hstar (t := 1 / (2 * (K ^ 2 + 1))) (by positivity)
  have hnorm : ‖(⟨F, hFmem⟩ : L.kerPi)‖ = ‖F‖ := rfl
  have hAnorm : ‖A ⟨F, hFmem⟩‖ = ‖L.defect F‖ := rfl
  have hlow := hK ⟨F, hFmem⟩
  rw [hnorm, hAnorm] at hlow
  have hFpos : 0 < ‖F‖ := norm_pos_iff.mpr hFne
  have hsq : ‖F‖ ^ 2 ≤ K ^ 2 * ‖L.defect F‖ ^ 2 := by
    have h1 : 0 ≤ ‖L.defect F‖ := norm_nonneg _
    nlinarith
  have hkey : ‖F‖ ^ 2 ≤ K ^ 2 * (1 / (2 * (K ^ 2 + 1))) * ‖F‖ ^ 2 := by
    calc ‖F‖ ^ 2 ≤ K ^ 2 * ‖L.defect F‖ ^ 2 := hsq
      _ ≤ K ^ 2 * ((1 / (2 * (K ^ 2 + 1))) * ‖F‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hFbound (by positivity)
      _ = K ^ 2 * (1 / (2 * (K ^ 2 + 1))) * ‖F‖ ^ 2 := by ring
  have hlt : K ^ 2 * (1 / (2 * (K ^ 2 + 1))) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    nlinarith
  have hFsq : 0 < ‖F‖ ^ 2 := pow_pos hFpos 2
  have hstrict := mul_lt_mul_of_pos_right hlt hFsq
  linarith [hkey, hstrict]

/-! ## 7. A pair of probability densities with no exact `L²` outflow -/

/-- **`prop:doubling_unsolvable`(2).** There are probability densities `f_init, f_term ∈ L²(λ)`
whose difference is not a flow-matching defect: no `f ∈ L²(λ)` has `(Id − P⋆)f = f_init − f_term`.

The pair is not explicit: it is built from a `ψ ∈ ker Π` outside the range of `Id − P⋆`, and that
`ψ` exists only because the range is proper (`defectRange_ne_kerPi`), which is an open-mapping
argument. -/
theorem exists_unsolvable_pair (hstar : GrowthCond S) :
    ∃ fi fe : St → ℝ,
      (∀ x, 0 ≤ fi x) ∧ (∀ x, 0 ≤ fe x) ∧
      MemLp fi 2 L.mu ∧ MemLp fe 2 L.mu ∧
      ∑' x, L.lam x * fi x = 1 ∧ ∑' x, L.lam x * fe x = 1 ∧
      ¬ ∃ f : St → ℝ, MemLp f 2 L.mu ∧
          ∀ᵐ x ∂L.mu, f x - pstar S none f x = fi x - fe x := by
  obtain ⟨ψ, hψker, hψnot⟩ : ∃ ψ, ψ ∈ L.kerPi ∧ ψ ∉ L.defectRange := by
    by_contra hcon
    refine L.defectRange_ne_kerPi hstar (le_antisymm L.defectRange_le_kerPi fun x hx => ?_)
    by_contra hxn
    exact hcon ⟨x, hx, hxn⟩
  set psi : St → ℝ := ⇑ψ with hpsidef
  have hpsiL2 : MemLp psi 2 L.mu := Lp.memLp ψ
  have hmean : ∑' x, L.lam x * psi x = 0 := L.mem_kerPi_iff.mp hψker
  set pp : St → ℝ := fun x => max (psi x) 0 with hppdef
  set pm : St → ℝ := fun x => max (-psi x) 0 with hpmdef
  have hppnn : ∀ x, 0 ≤ pp x := fun x => le_max_right _ _
  have hpmnn : ∀ x, 0 ≤ pm x := fun x => le_max_right _ _
  have hsplit : ∀ x, psi x = pp x - pm x := by
    intro x
    simp only [hppdef, hpmdef]
    rcases le_total 0 (psi x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have habsp : ∀ x, |pp x| ≤ |psi x| := by
    intro x
    simp only [hppdef]
    rcases le_total 0 (psi x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
  have habsm : ∀ x, |pm x| ≤ |psi x| := by
    intro x
    simp only [hpmdef]
    rcases le_total 0 (psi x) with h | h
    · rw [max_eq_right (by linarith), abs_zero]; exact abs_nonneg _
    · rw [max_eq_left (by linarith), abs_neg]
  have hsumabs : Summable fun x => L.lam x * |psi x| := L.summable_lam_abs hpsiL2
  have hsp : Summable fun x => L.lam x * pp x :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (L.nonneg x) (hppnn x))
      (fun x => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (habsp x)) (L.nonneg x)) hsumabs
  have hsm : Summable fun x => L.lam x * pm x :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (L.nonneg x) (hpmnn x))
      (fun x => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (habsm x)) (L.nonneg x)) hsumabs
  have hppL2 : MemLp pp 2 L.mu :=
    hpsiL2.of_le (L.aestronglyMeasurable _)
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using habsp x)
  have hpmL2 : MemLp pm 2 L.mu :=
    hpsiL2.of_le (L.aestronglyMeasurable _)
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using habsm x)
  have hbal : ∑' x, L.lam x * pp x = ∑' x, L.lam x * pm x := by
    have hfun : (fun x => L.lam x * psi x)
        = fun x => L.lam x * pp x - L.lam x * pm x := by
      funext x; rw [hsplit x]; ring
    rw [hfun, Summable.tsum_sub hsp hsm, sub_eq_zero] at hmean
    exact hmean
  set Z : ℝ := 1 + ∑' x, L.lam x * pp x with hZdef
  have hZpos : 0 < Z := by
    have : 0 ≤ ∑' x, L.lam x * pp x :=
      tsum_nonneg fun x => mul_nonneg (L.nonneg x) (hppnn x)
    rw [hZdef]; linarith
  have hmass : ∀ q : St → ℝ, (Summable fun x => L.lam x * q x) →
      ∑' x, L.lam x * (Z⁻¹ * (1 + q x)) = Z⁻¹ * (1 + ∑' x, L.lam x * q x) := by
    intro q hq
    have hfun : (fun x => L.lam x * (Z⁻¹ * (1 + q x)))
        = fun x => Z⁻¹ * (L.lam x + L.lam x * q x) := by funext x; ring
    rw [hfun, tsum_mul_left, Summable.tsum_add L.summable hq, L.total]
  refine ⟨fun x => Z⁻¹ * (1 + pm x), fun x => Z⁻¹ * (1 + pp x), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x => mul_nonneg (le_of_lt (inv_pos.mpr hZpos)) (by linarith [hpmnn x])
  · exact fun x => mul_nonneg (le_of_lt (inv_pos.mpr hZpos)) (by linarith [hppnn x])
  · exact ((memLp_const (1 : ℝ)).add hpmL2).const_mul Z⁻¹
  · exact ((memLp_const (1 : ℝ)).add hppL2).const_mul Z⁻¹
  · rw [hmass pm hsm, ← hbal, ← hZdef]
    exact inv_mul_cancel₀ hZpos.ne'
  · rw [hmass pp hsp, ← hZdef]
    exact inv_mul_cancel₀ hZpos.ne'
  · rintro ⟨f, hf, hfeq⟩
    have hpt : ∀ᵐ x ∂L.mu, f x - pstar S none f x = -Z⁻¹ * psi x := by
      filter_upwards [hfeq] with x hx
      rw [hx, hsplit x]
      ring
    have hEq : L.defect (hf.toLp f) = (-Z⁻¹) • ψ := by
      refine Lp.ext ?_
      filter_upwards [L.coeFn_defect_toLp hf, Lp.coeFn_smul (-Z⁻¹) ψ, hpt] with x h1 h2 h3
      rw [h1, h2, Pi.smul_apply, smul_eq_mul, ← hpsidef]
      exact h3
    have hmem : ((-Z⁻¹) • ψ) ∈ L.defectRange := ⟨hf.toLp f, hEq⟩
    refine hψnot ?_
    have hsm2 : ((-Z) • ((-Z⁻¹) • ψ)) ∈ L.defectRange := Submodule.smul_mem _ _ hmem
    rwa [smul_smul, neg_mul_neg, mul_inv_cancel₀ hZpos.ne', one_smul] at hsm2

end Stat


/-! ## 8. The proposition -/

/-- **`prop:doubling_unsolvable`.** Under `eq:doubling_star`, on the positive recurrent loop
closure: *(1)* `(Id − P⋆)L²(λ)` is a dense proper linear subspace of `ker Π`; *(2)* some pair of
probability densities of `L²(λ)` has its difference outside it, so the exact `L²` flow-matching
problem it poses has no solution. -/
theorem doubling_unsolvable (L : Stat S none) (hstar : GrowthCond S) :
    (L.defectRange ≤ L.kerPi ∧ L.defectRange.topologicalClosure = L.kerPi ∧
        L.defectRange ≠ L.kerPi) ∧
      ∃ fi fe : St → ℝ,
        (∀ x, 0 ≤ fi x) ∧ (∀ x, 0 ≤ fe x) ∧
        MemLp fi 2 L.mu ∧ MemLp fe 2 L.mu ∧
        ∑' x, L.lam x * fi x = 1 ∧ ∑' x, L.lam x * fe x = 1 ∧
        ¬ ∃ f : St → ℝ, MemLp f 2 L.mu ∧
            ∀ᵐ x ∂L.mu, f x - pstar S none f x = fi x - fe x :=
  ⟨⟨L.defectRange_le_kerPi, L.topologicalClosure_defectRange, L.defectRange_ne_kerPi hstar⟩,
    L.exists_unsolvable_pair hstar⟩

end GFNBounds.Doubling
