import GFNBounds.Doubling.Remarks

/-!
# Every bounded solution of the renewal limit equation on `ℝ` is constant

**The renewal remark**, dropped from the draft by the author on 2026-09-19 (it was a remark; no proof
environment). Read against draft commit `3194054`.

`GFNBounds/Doubling/Remarks.lean` certifies every non-heuristic sentence of the remark. Its SCOPE
records, as a finding sent to the author and **not proved there**, that by Choquet–Deny every
bounded solution of the limit equation on all of `ℝ` is constant, so that the remark's limit
clause ("if `V` has a limit at `+∞` … that limit is `G` divided by `∫₀¹ k̄`") reads `ℓ = ℓ`. This
file proves that finding, without Choquet–Deny and without any compactness, from `G` being
constant, which the remark establishes (`renewal_G_const`), and a positive lower bound
`k ≥ c ln 2 · 2^{−|p|}` on `[0,1]`, proved here (`kern_ge`).

## What is proved

| claim | declaration |
|---|---|
| `k(v) ≥ c ln 2 · 2^{−|p|}` on `[0,1]` | `kern_ge` |
| `k̄(v) ≤ 1` on `[0,1]` | `kbar_le_one` |
| for `V ≤ S` everywhere: `S ∫₀¹k̄ − G(x) ≤ (S − V(x)) / (c ln 2 · 2^{−|p|})` | `sup_mul_sub_G_le` |
| every bounded measurable solution on `ℝ` is constant | `renewal_solution_const` |
| hence, under the remark's hypotheses, `ℓ = V(x)` for every `x`: the limit clause is `ℓ = ℓ` | `renewal_limit_trivial` |

The argument: with `S = sup V`, `A = ∫₀¹ k̄ > 0` and `g` the constant value of `G`,
`S A − g = ∫₀¹ k̄(v)(S − V(x−v))dv ≤ ∫₀¹ (S − V(x−v))dv ≤ k₀⁻¹ ∫₀¹ k(v)(S − V(x−v))dv
= k₀⁻¹ (S − V(x))`, the last step by the limit equation and `∫₀¹ k = 1`. Taking `x` along a
maximizing sequence gives `S A ≤ g`; the same for `−V` gives `g ≤ (inf V) A`. So `sup V ≤ inf V`.

## SCOPE (disclosed)

* The hypotheses are exactly those of `renewal_limit` in `Remarks.lean` (the range `c > 0`, any
  non-zero root `p` of `ψ`, as there); `renewal_solution_const` does not use a limit at `+∞`.
* This is a statement **about** the remark, not one the remark makes: it shows the remark's
  hypothesis class (bounded measurable solutions on `ℝ`) is the constants, which inhabit it
  (`const_isRenewalSolution`), so no clause of the remark is vacuous and none is false, but the
  limit clause carries no information and the "non-lattice" sentence is used by nothing.
* `sorry`-free.

## Inhabitation (kb `0025`)

The hypotheses are inhabited by the constants (`const_isRenewalSolution`, with the Cramér root of
`cramer_root_exists`); `renewal_limit_check` in `Remarks.lean` exhibits them at `c = 1/2`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling.RenewalClose

open Real MeasureTheory Set Filter Topology GFNBounds.Doubling.Remarks

variable {c p : ℝ} {V : ℝ → ℝ} {M : ℝ}

/-- The lower bound of the kernel on `[0,1]`: `k₀ := c ln 2 · 2^{−|p|}`. -/
noncomputable def kernInf (c p : ℝ) : ℝ := c * log 2 * (2 : ℝ) ^ (-|p|)

theorem kernInf_pos (hc : 0 < c) (p : ℝ) : 0 < kernInf c p := by
  have := two_rpow_pos (-|p|)
  have := log_two_pos
  unfold kernInf
  positivity

/-- `k(v) ≥ c ln 2 · 2^{−|p|}` for `v ∈ [0,1]`. -/
theorem kern_ge (hc : 0 < c) (p : ℝ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    kernInf c p ≤ kern c p v := by
  have hle : -|p| ≤ p * v := by
    have h1 : |p * v| ≤ |p| := by
      rw [abs_mul, abs_of_nonneg hv.1]
      exact mul_le_of_le_one_right (abs_nonneg p) hv.2
    linarith [neg_abs_le (p * v)]
  have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle
  have : 0 < c * log 2 := mul_pos hc log_two_pos
  unfold kernInf kern
  exact mul_le_mul_of_nonneg_left h2 this.le

/-- `k̄(v) ≤ 1` for `v ∈ [0,1]`. -/
theorem kbar_le_one (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : kbar c p v ≤ 1 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (kern c p) volume a b :=
    fun a b => (continuous_kern c p).intervalIntegrable a b
  have hsplit : (∫ w in (0 : ℝ)..v, kern c p w) + kbar c p v = ∫ w in (0 : ℝ)..1, kern c p w :=
    intervalIntegral.integral_add_adjacent_intervals (hint 0 v) (hint v 1)
  have hnn : 0 ≤ ∫ w in (0 : ℝ)..v, kern c p w :=
    intervalIntegral.integral_nonneg hv.1 fun w _ => (kern_pos hc p w).le
  rw [integral_kern hp0 hp] at hsplit
  linarith

/-- **The key estimate.** If `V ≤ S` everywhere, then
`S ∫₀¹ k̄ − G(x) ≤ (S − V(x)) / k₀` at every `x`. -/
theorem sup_mul_sub_G_le (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) (hVm : Measurable V)
    (hM : ∀ x, |V x| ≤ M) (heq : ∀ x, V x = ∫ v in (0 : ℝ)..1, kern c p v * V (x - v))
    {S : ℝ} (hS : ∀ x, V x ≤ S) (x : ℝ) :
    S * (∫ v in (0 : ℝ)..1, kbar c p v) - Gfun c p V x ≤ (S - V x) / kernInf c p := by
  have hk0 := kernInf_pos hc p
  have hVs : IntervalIntegrable (fun v => V (x - v)) volume 0 1 :=
    intervalIntegrable_of_abs_le (hVm.comp (measurable_const.sub measurable_id))
      (fun u => hM (x - u)) 0 1
  have hkbV := intervalIntegrable_mul_shift (continuous_kbar c p) hVm hM x 0 1
  have hkV := intervalIntegrable_mul_shift (continuous_kern c p) hVm hM x 0 1
  have hkb : IntervalIntegrable (kbar c p) volume 0 1 := (continuous_kbar c p).intervalIntegrable _ _
  have hk : IntervalIntegrable (kern c p) volume 0 1 := (continuous_kern c p).intervalIntegrable _ _
  have hSV : IntervalIntegrable (fun v => S - V (x - v)) volume 0 1 := IntervalIntegrable.sub intervalIntegrable_const hVs
  -- `S A − G(x) = ∫₀¹ k̄(v)(S − V(x−v))`
  have e1 : S * (∫ v in (0 : ℝ)..1, kbar c p v) - Gfun c p V x
      = ∫ v in (0 : ℝ)..1, kbar c p v * (S - V (x - v)) := by
    have : (fun v => kbar c p v * (S - V (x - v))) = fun v => S * kbar c p v - kbar c p v * V (x - v) := by
      funext v; ring
    rw [this, intervalIntegral.integral_sub (hkb.const_mul S) hkbV, intervalIntegral.integral_const_mul]
    rfl
  -- `≤ ∫₀¹ (S − V(x−v))`
  have e2 : (∫ v in (0 : ℝ)..1, kbar c p v * (S - V (x - v))) ≤ ∫ v in (0 : ℝ)..1, (S - V (x - v)) := by
    have hL : IntervalIntegrable (fun v => kbar c p v * (S - V (x - v))) volume 0 1 := by
      have : (fun v => kbar c p v * (S - V (x - v)))
          = fun v => S * kbar c p v - kbar c p v * V (x - v) := by
        funext v; ring
      rw [this]
      exact (hkb.const_mul S).sub hkbV
    refine intervalIntegral.integral_mono_on zero_le_one hL hSV ?_
    · intro v hv
      have h1 := kbar_le_one hc hp0 hp hv
      have h2 : 0 ≤ S - V (x - v) := sub_nonneg.2 (hS _)
      nlinarith
  -- `k₀ ∫₀¹ (S − V(x−v)) ≤ ∫₀¹ k(v)(S − V(x−v)) = S − V(x)`
  have e3 : kernInf c p * ∫ v in (0 : ℝ)..1, (S - V (x - v))
      ≤ ∫ v in (0 : ℝ)..1, kern c p v * (S - V (x - v)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one (hSV.const_mul _) ?_ ?_
    · have : (fun v => kern c p v * (S - V (x - v))) = fun v => S * kern c p v - kern c p v * V (x - v) := by
        funext v; ring
      rw [this]
      exact (hk.const_mul S).sub hkV
    · intro v hv
      have h1 := kern_ge hc p hv
      have h2 : 0 ≤ S - V (x - v) := sub_nonneg.2 (hS _)
      exact mul_le_mul_of_nonneg_right h1 h2
  have e4 : (∫ v in (0 : ℝ)..1, kern c p v * (S - V (x - v))) = S - V x := by
    have : (fun v => kern c p v * (S - V (x - v))) = fun v => S * kern c p v - kern c p v * V (x - v) := by
      funext v; ring
    rw [this, intervalIntegral.integral_sub (hk.const_mul S) hkV, intervalIntegral.integral_const_mul,
      integral_kern hp0 hp, mul_one, ← heq x]
  rw [e1, le_div_iff₀ hk0]
  have := e3.trans_eq e4
  nlinarith

/-- `−V` solves the limit equation when `V` does. -/
theorem neg_solution (heq : ∀ x, V x = ∫ v in (0 : ℝ)..1, kern c p v * V (x - v)) (x : ℝ) :
    (-V) x = ∫ v in (0 : ℝ)..1, kern c p v * (-V) (x - v) := by
  simp only [Pi.neg_apply, mul_neg, intervalIntegral.integral_neg]
  rw [← heq x]

theorem Gfun_neg (x : ℝ) : Gfun c p (-V) x = -Gfun c p V x := by
  simp only [Gfun, Pi.neg_apply, mul_neg, intervalIntegral.integral_neg]

/-- **the dropped renewal remark, the finding certified: every bounded measurable solution of the
limit equation `V(x) = ∫₀¹ k(v)V(x−v)dv` on `ℝ` is constant.** -/
theorem renewal_solution_const (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) (hVm : Measurable V)
    (hM : ∀ x, |V x| ≤ M) (heq : ∀ x, V x = ∫ v in (0 : ℝ)..1, kern c p v * V (x - v))
    (x y : ℝ) : V x = V y := by
  have hk0 := kernInf_pos hc p
  set A := ∫ v in (0 : ℝ)..1, kbar c p v with hA
  have hApos : 0 < A := by
    rw [hA, (integral_kbar_eq_kernMean (c := c) hp0).1]
    exact kernMean_pos hc
  set g := Gfun c p V 0 with hg
  have hG : ∀ z, Gfun c p V z = g := fun z => renewal_G_const hc hp0 hp hVm hM heq z 0
  have hbddA : BddAbove (range V) := ⟨M, by rintro _ ⟨z, rfl⟩; exact (le_abs_self _).trans (hM z)⟩
  have hbddB : BddBelow (range V) :=
    ⟨-M, by rintro _ ⟨z, rfl⟩; exact (neg_le_of_abs_le (hM z))⟩
  set S := ⨆ z, V z with hSdef
  set I := ⨅ z, V z with hIdef
  have hS : ∀ z, V z ≤ S := fun z => le_ciSup hbddA z
  have hI : ∀ z, I ≤ V z := fun z => ciInf_le hbddB z
  -- `S A ≤ g`
  have hup : S * A ≤ g := by
    refine le_of_not_gt fun hlt => ?_
    have hε : 0 < (S * A - g) * kernInf c p := mul_pos (by linarith) hk0
    obtain ⟨z, hz⟩ := exists_lt_of_lt_ciSup (f := V) (show S - (S * A - g) * kernInf c p < S by linarith)
    have h := sup_mul_sub_G_le hc hp0 hp hVm hM heq hS z
    rw [hG z, le_div_iff₀ hk0] at h
    linarith
  -- `g ≤ I A`, from the same estimate for `−V`
  have hlo : g ≤ I * A := by
    refine le_of_not_gt fun hlt => ?_
    have hε : 0 < (g - I * A) * kernInf c p := mul_pos (by linarith) hk0
    obtain ⟨z, hz⟩ := exists_lt_of_ciInf_lt (f := V) (show I < I + (g - I * A) * kernInf c p by linarith)
    have hMn : ∀ w, |(-V) w| ≤ M := fun w => by simpa only [Pi.neg_apply, abs_neg] using hM w
    have hSn : ∀ w, (-V) w ≤ -I := fun w => by simpa only [Pi.neg_apply, neg_le_neg_iff] using hI w
    have h : -I * A - Gfun c p (-V) z ≤ (-I - (-V) z) / kernInf c p :=
      sup_mul_sub_G_le hc hp0 hp hVm.neg hMn (neg_solution heq) hSn z
    rw [Gfun_neg, hG z, le_div_iff₀ hk0] at h
    simp only [Pi.neg_apply] at h
    linarith
  have hSI : S ≤ I := le_of_mul_le_mul_right (hup.trans hlo) hApos
  exact le_antisymm ((hS x).trans (hSI.trans (hI y))) ((hS y).trans (hSI.trans (hI x)))

/-- **the dropped renewal remark, the limit clause is `ℓ = ℓ`**: under the remark's hypotheses, the
limit `ℓ` at `+∞` is the value of `V` at every point, and `G ≡ ℓ ∫₀¹ k̄`. -/
theorem renewal_limit_trivial (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) (hVm : Measurable V)
    (hM : ∀ x, |V x| ≤ M) (heq : ∀ x, V x = ∫ v in (0 : ℝ)..1, kern c p v * V (x - v))
    {ℓ : ℝ} (hlim : Tendsto V atTop (𝓝 ℓ)) :
    V = (fun _ => ℓ) ∧ ∀ x, Gfun c p V x = ℓ * ∫ v in (0 : ℝ)..1, kbar c p v := by
  have hV : V = fun _ => V 0 := funext fun x => renewal_solution_const hc hp0 hp hVm hM heq x 0
  have hℓ : V 0 = ℓ := by
    rw [hV] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  refine ⟨hV.trans (by rw [hℓ]), fun x => ?_⟩
  rw [hV, hℓ]
  simp only [Gfun, mul_comm _ ℓ, intervalIntegral.integral_const_mul]

end GFNBounds.Doubling.RenewalClose
