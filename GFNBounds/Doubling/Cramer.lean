import GFNBounds.Doubling.Setting

/-!
# The Cramér root

**`lem:doubling_cramer_root`** — `app_doubling.tex:711–767`.

> Let `c > 0` and put `ψ(t) := c(2^t − 1) − t`, so that `eq:doubling_cramer` reads `ψ(p) = 0`.
> Then `ψ` is strictly convex and `ψ(0) = 0`; `ψ` has exactly one root other than `0` when
> `c ≠ 1/ln 2`, and none when `c = 1/ln 2`. Write `p_*` for that root and `τ := 2^{p_*}`. Then
> (1) `p_* > 0` iff `c < 1/ln 2`, and `p_* > 1` iff `c < 1`;
> (2) the Cramér equation reads `c(τ−1)/p_* = 1`, and `k(v) := c ln 2 · 2^{p_* v}` on `[0,1]`
>     has `∫₀¹ k = 1`;
> (3) if `0 < c < 1` then `τ > 2`, `τ > p_*+1`, `2τ > p_*+2`, `4τ > p_*+3`.

## SCOPE (disclosed)

The paper's `p_*` is *the* nonzero root; here `cramer_root_unique` proves it unique, and the
downstream files take a root as a hypothesis (`hp : psi c p = 0`, `hp0 : p ≠ 0`) rather than
through a choice function, so that no statement below depends on how the root is selected.

Two proofs are elementary where the paper's are not, and this is a *weakening of the tools*, not
of the statements. The paper reads item (3) off "`2^t − t − 1` is strictly convex, vanishes at
`0` and at `1`, hence is positive past `1`"; here `two_rpow_gt_add_one` gets `2^t > t+1` for
`t > 1` from `exp x ≥ x+1` and `2 ln 2 > 1`, with no convexity. The paper's `c = 1/ln 2` case
argues that strict convexity makes `0` the strict minimum; here `psi_pos_of_log_eq` gets it from
`x + 1 < exp x` for `x ≠ 0`. Strict convexity is still proved (`psi_strictConvexOn`) and is what
carries uniqueness.

## Hypothesis checklist against `lem:doubling_cramer_root`

| paper hypothesis | here |
|---|---|
| `c > 0` | ✓ carried (`hc`) |
| `c ≠ 1/ln 2` for the root | ✓ carried, as `c * log 2 ≠ 1` |
| `0 < c < 1` in item (3) | ✓ carried |
| item (2)'s `∫₀¹ k = 1` | ✓ carried (`cramer_kernel_integral`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Set

/-- `ψ(t) = c(2^t − 1) − t`, whose non-zero root is the Cramér exponent `p_*`. -/
noncomputable def psi (c t : ℝ) : ℝ := c * ((2 : ℝ) ^ t - 1) - t

theorem psi_zero (c : ℝ) : psi c 0 = 0 := by
  simp [psi]

/-- `2^t = exp (t · ln 2)`. -/
theorem two_rpow_eq (t : ℝ) : (2 : ℝ) ^ t = exp (t * log 2) := by
  rw [rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]

theorem two_rpow_pos (t : ℝ) : (0 : ℝ) < (2 : ℝ) ^ t :=
  rpow_pos_of_pos (by norm_num) t

theorem log_two_pos : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)

/-- `2 ln 2 > 1`, the one numeric fact behind `two_rpow_gt_add_one`. -/
theorem two_log_two_gt_one : (1 : ℝ) < 2 * log 2 := by
  have := Real.log_two_gt_d9
  nlinarith

/-- **`eq:doubling_cramer_ineq`, the engine.** `2^t > t + 1` for every `t > 1`.

The paper gets this from strict convexity of `2^t − t − 1` and its two roots `0`, `1`; here it is
`2^t = 2·2^{t−1} ≥ 2(1 + (t−1)ln 2) > 2 + (t−1) = t+1`, using `x + 1 ≤ exp x` and `2 ln 2 > 1`. -/
theorem two_rpow_gt_add_one {t : ℝ} (ht : 1 < t) : t + 1 < (2 : ℝ) ^ t := by
  have hstep : (t - 1) * log 2 + 1 ≤ exp ((t - 1) * log 2) := Real.add_one_le_exp _
  have hsplit : (2 : ℝ) ^ t = 2 * exp ((t - 1) * log 2) := by
    rw [two_rpow_eq, sub_mul, one_mul, Real.exp_sub,
      Real.exp_log (by norm_num : (0:ℝ) < 2)]
    ring
  have ht1 : 0 < t - 1 := by linarith
  have hkey : 1 * (t - 1) < 2 * log 2 * (t - 1) :=
    mul_lt_mul_of_pos_right two_log_two_gt_one ht1
  nlinarith [hstep, hsplit]

/-! ### Strict convexity -/

theorem hasDerivAt_two_rpow (t : ℝ) :
    HasDerivAt (fun x : ℝ => (2 : ℝ) ^ x) ((2 : ℝ) ^ t * log 2) t :=
  (hasStrictDerivAt_const_rpow (by norm_num : (0:ℝ) < 2) t).hasDerivAt

theorem hasDerivAt_psi (c t : ℝ) :
    HasDerivAt (psi c) (c * ((2 : ℝ) ^ t * log 2) - 1) t := by
  have h : HasDerivAt (fun x : ℝ => c * ((2 : ℝ) ^ x - 1)) (c * ((2 : ℝ) ^ t * log 2)) t :=
    ((hasDerivAt_two_rpow t).sub_const 1).const_mul c
  have hid : HasDerivAt (fun x : ℝ => x) (1 : ℝ) t := hasDerivAt_id t
  show HasDerivAt (fun x : ℝ => c * ((2 : ℝ) ^ x - 1) - x) _ t
  exact h.sub hid

theorem deriv_psi (c : ℝ) :
    deriv (psi c) = fun t => c * ((2 : ℝ) ^ t * log 2) - 1 := by
  funext t; exact (hasDerivAt_psi c t).deriv

theorem continuous_two_rpow : Continuous fun t : ℝ => (2 : ℝ) ^ t := by
  have h : (fun t : ℝ => (2 : ℝ) ^ t) = fun t : ℝ => exp (t * log 2) := funext two_rpow_eq
  rw [h]
  exact Real.continuous_exp.comp (continuous_id.mul continuous_const)

theorem continuous_psi (c : ℝ) : Continuous (psi c) := by
  show Continuous fun t : ℝ => c * ((2 : ℝ) ^ t - 1) - t
  exact ((continuous_two_rpow.sub continuous_const).const_mul c).sub continuous_id

/-- `ψ` is strictly convex on `ℝ`, for every `c > 0`. -/
theorem psi_strictConvexOn {c : ℝ} (hc : 0 < c) : StrictConvexOn ℝ univ (psi c) := by
  refine strictConvexOn_univ_of_deriv2_pos (continuous_psi c) (fun x => ?_)
  have h2 : deriv^[2] (psi c) x = deriv (deriv (psi c)) x := by
    simp [Function.iterate_succ, Function.comp]
  rw [h2, deriv_psi]
  have hd : HasDerivAt (fun t : ℝ => c * ((2 : ℝ) ^ t * log 2) - 1)
      (c * ((2 : ℝ) ^ x * log 2 * log 2)) x := by
    have := ((hasDerivAt_two_rpow x).mul_const (log 2)).const_mul c
    simpa [mul_assoc] using this.sub_const 1
  rw [hd.deriv]
  have := two_rpow_pos x
  have := log_two_pos
  positivity

/-! ### The roots of `ψ` -/

theorem psi_neg_of_mem_openSegment {c : ℝ} (hc : 0 < c) {a b t : ℝ}
    (ha : psi c a = 0) (hb : psi c b = 0) (hab : a ≠ b)
    (ht : t ∈ openSegment ℝ a b) : psi c t < 0 := by
  have h := (psi_strictConvexOn hc).lt_on_openSegment (mem_univ a) (mem_univ b) hab ht
  rw [ha, hb] at h; simpa using h

theorem psi_neg_of_between {c : ℝ} (hc : 0 < c) {a b t : ℝ}
    (ha : psi c a = 0) (hb : psi c b = 0) (hab : a < b) (h1 : a < t) (h2 : t < b) :
    psi c t < 0 := by
  refine psi_neg_of_mem_openSegment hc ha hb hab.ne ?_
  rw [openSegment_eq_Ioo hab]; exact ⟨h1, h2⟩

/-- Outside the closed interval spanned by two roots, `ψ` is strictly positive. -/
theorem psi_pos_of_outside {c : ℝ} (hc : 0 < c) {a b t : ℝ}
    (ha : psi c a = 0) (hb : psi c b = 0) (hab : a < b) (ht : t < a ∨ b < t) :
    0 < psi c t := by
  by_contra hcon
  rw [not_lt] at hcon
  rcases ht with ht | ht
  · have hlt : psi c a < max (psi c t) (psi c b) := by
      refine (psi_strictConvexOn hc).lt_on_openSegment (mem_univ t) (mem_univ b)
        (by linarith) ?_
      rw [openSegment_eq_Ioo (by linarith : t < b)]; exact ⟨ht, hab⟩
    rw [ha, hb] at hlt
    have : max (psi c t) 0 = 0 := max_eq_right hcon
    rw [this] at hlt; exact lt_irrefl 0 hlt
  · have hlt : psi c b < max (psi c a) (psi c t) := by
      refine (psi_strictConvexOn hc).lt_on_openSegment (mem_univ a) (mem_univ t)
        (by linarith) ?_
      rw [openSegment_eq_Ioo (by linarith : a < t)]; exact ⟨hab, ht⟩
    rw [ha, hb] at hlt
    have : max (0 : ℝ) (psi c t) = 0 := max_eq_left hcon
    rw [this] at hlt; exact lt_irrefl 0 hlt

/-- `ψ` has no three distinct roots. -/
theorem psi_no_three_roots {c : ℝ} (hc : 0 < c) {a b e : ℝ} (hab : a < b) (hbe : b < e)
    (ha : psi c a = 0) (hb : psi c b = 0) (he : psi c e = 0) : False := by
  have := psi_neg_of_between hc ha he (hab.trans hbe) hab hbe
  rw [hb] at this; exact lt_irrefl 0 this

/-- **Uniqueness.** `ψ` has at most one root other than `0`. -/
theorem cramer_root_unique {c : ℝ} (hc : 0 < c) {p q : ℝ}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hp : psi c p = 0) (hq : psi c q = 0) : p = q := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · rcases lt_trichotomy p 0 with hpz | hpz | hpz
    · rcases lt_trichotomy q 0 with hqz | hqz | hqz
      · exact psi_no_three_roots hc h hqz hp hq (psi_zero c)
      · exact hq0 hqz
      · exact psi_no_three_roots hc hpz hqz hp (psi_zero c) hq
    · exact hp0 hpz
    · exact psi_no_three_roots hc hpz h (psi_zero c) hp hq
  · rcases lt_trichotomy q 0 with hqz | hqz | hqz
    · rcases lt_trichotomy p 0 with hpz | hpz | hpz
      · exact psi_no_three_roots hc h hpz hq hp (psi_zero c)
      · exact hp0 hpz
      · exact psi_no_three_roots hc hqz hpz hq (psi_zero c) hp
    · exact hq0 hqz
    · exact psi_no_three_roots hc hqz h (psi_zero c) hq hp

/-! ### Existence -/

/-- At `c = 1/ln 2` the only root is `0`: `ψ(t) > 0` for `t ≠ 0`. -/
theorem psi_pos_of_log_eq {c : ℝ} (hc : c * log 2 = 1) {t : ℝ} (ht : t ≠ 0) : 0 < psi c t := by
  have hl := log_two_pos
  have hu : t * log 2 ≠ 0 := mul_ne_zero ht hl.ne'
  have hexp : t * log 2 + 1 < exp (t * log 2) := Real.add_one_lt_exp hu
  have hcpos : 0 < c := by nlinarith
  rw [psi, two_rpow_eq]
  have hct : c * (t * log 2) = t := by
    have h : c * (t * log 2) = t * (c * log 2) := by ring
    rw [h, hc, mul_one]
  have key : c * (t * log 2) < c * (exp (t * log 2) - 1) :=
    mul_lt_mul_of_pos_left (by linarith) hcpos
  linarith [hct, key]

/-- `ψ(T) > 0` for `T` far enough to the right: the exponential beats the line. -/
theorem psi_pos_atTop {c : ℝ} (hc : 0 < c) : ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t → 0 < psi c t := by
  set L := log 2 with hL
  have hLpos : 0 < L := log_two_pos
  set A := c * L ^ 2 / 4 with hA
  have hApos : 0 < A := by positivity
  set B := |1 - c * L| with hB
  refine ⟨max 1 ((B + 1) / A), lt_of_lt_of_le one_pos (le_max_left _ _), fun t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htA : (B + 1) / A ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  -- `exp u = (exp (u/2))^2 ≥ (1 + u/2)^2`
  have hhalf : 1 + t * L / 2 ≤ exp (t * L / 2) := by
    have := Real.add_one_le_exp (t * L / 2); linarith
  have hpos : 0 < 1 + t * L / 2 := by positivity
  have hsq : (1 + t * L / 2) ^ 2 ≤ exp (t * L) := by
    have h2 : exp (t * L / 2) ^ 2 = exp (t * L) := by
      rw [← Real.exp_nat_mul]; ring_nf
    calc (1 + t * L / 2) ^ 2 ≤ exp (t * L / 2) ^ 2 := by nlinarith
      _ = exp (t * L) := h2
  have hlb : c * ((2 : ℝ) ^ t - 1) ≥ c * (t * L + t ^ 2 * L ^ 2 / 4) := by
    rw [two_rpow_eq]
    have : t * L + t ^ 2 * L ^ 2 / 4 ≤ exp (t * L) - 1 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hc.le
  have hAt : B + 1 ≤ A * t := by
    rw [div_le_iff₀ hApos] at htA; linarith [htA]
  have hBge : 1 - c * L ≤ B := le_abs_self _
  have : A * t ^ 2 = c * (t ^ 2 * L ^ 2 / 4) := by rw [hA]; ring
  have hfin : psi c t ≥ c * (t * L + t ^ 2 * L ^ 2 / 4) - t := by
    rw [psi]; linarith
  nlinarith [hfin, hAt, hBge, htpos, this]

/-- `ψ(T) > 0` for `T` far enough to the left, where `c(2^T − 1) > −c`. -/
theorem psi_pos_atBot {c : ℝ} (hc : 0 < c) : ∃ T : ℝ, T < 0 ∧ ∀ t, t ≤ T → 0 < psi c t := by
  refine ⟨-(c + 2), by linarith, fun t ht => ?_⟩
  have h1 : (0 : ℝ) < (2 : ℝ) ^ t := two_rpow_pos t
  have : c * ((2 : ℝ) ^ t - 1) > -c := by nlinarith
  rw [psi]; linarith

/-- The root exists whenever `c ln 2 ≠ 1`, and its sign is that of `1 − c ln 2`. -/
theorem cramer_root_exists {c : ℝ} (hc : 0 < c) (hne : c * log 2 ≠ 1) :
    ∃ p : ℝ, p ≠ 0 ∧ psi c p = 0 ∧ (0 < p ↔ c * log 2 < 1) := by
  set L := log 2 with hL
  have hLpos : 0 < L := log_two_pos
  -- `t₀`, where `ψ' = 0`
  set t0 : ℝ := log (1 / (c * L)) / L with ht0
  have hcL : 0 < c * L := by positivity
  have hpow : (2 : ℝ) ^ t0 = 1 / (c * L) := by
    rw [two_rpow_eq, ht0, div_mul_cancel₀ _ hLpos.ne', Real.exp_log (by positivity)]
  have hderiv0 : c * ((2 : ℝ) ^ t0 * L) = 1 := by
    rw [hpow]; field_simp
  have hmono : ∀ t, t < t0 → deriv (psi c) t < 0 := by
    intro t ht
    rw [deriv_psi]
    have : (2 : ℝ) ^ t < (2 : ℝ) ^ t0 := by
      exact Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr ht
    nlinarith [hLpos, hcL, two_rpow_pos t]
  have hanti : StrictAntiOn (psi c) (Iic t0) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic t0) (continuous_psi c).continuousOn ?_
    intro x hx
    rw [interior_Iic] at hx
    exact hmono x hx
  have hup : ∀ t, t0 < t → 0 < deriv (psi c) t := by
    intro t ht
    rw [deriv_psi]
    have hlt : (2 : ℝ) ^ t0 < (2 : ℝ) ^ t :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr ht
    nlinarith [hLpos, hcL, two_rpow_pos t0, hderiv0]
  have hmonoOn : StrictMonoOn (psi c) (Ici t0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici t0) (continuous_psi c).continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    exact hup x hx
  rcases lt_trichotomy (c * L) 1 with hlt | heq | hgt
  · -- `t₀ > 0`: `ψ(t₀) < 0`, and `ψ > 0` far right.
    have ht0pos : 0 < t0 := by
      rw [ht0]
      apply div_pos _ hLpos
      apply Real.log_pos
      rw [lt_div_iff₀ hcL]; linarith
    have hneg : psi c t0 < 0 := by
      have := hanti (by simp [ht0pos.le] : (0:ℝ) ∈ Iic t0) (by simp : t0 ∈ Iic t0) ht0pos
      rw [psi_zero] at this; exact this
    obtain ⟨T, hTpos, hT⟩ := psi_pos_atTop hc
    have hTge : t0 ≤ max t0 T := le_max_left _ _
    have hpT : 0 < psi c (max t0 T) := hT _ (le_max_right _ _)
    obtain ⟨p, hpmem, hp⟩ := intermediate_value_Icc hTge (continuous_psi c).continuousOn
      (show (0:ℝ) ∈ Icc (psi c t0) (psi c (max t0 T)) from ⟨hneg.le, hpT.le⟩)
    have hppos : 0 < p := lt_of_lt_of_le ht0pos hpmem.1
    exact ⟨p, hppos.ne', hp, by simp [hppos, hlt]⟩
  · exact absurd heq hne
  · -- `t₀ < 0`: `ψ(t₀) < 0`, and `ψ > 0` far left.
    have ht0neg : t0 < 0 := by
      rw [ht0]
      apply div_neg_of_neg_of_pos _ hLpos
      apply Real.log_neg (by positivity)
      rw [div_lt_one hcL]; linarith
    have hneg : psi c t0 < 0 := by
      have := hmonoOn (by simp : t0 ∈ Ici t0) (by simp [ht0neg.le] : (0:ℝ) ∈ Ici t0) ht0neg
      rw [psi_zero] at this; exact this
    obtain ⟨T, hTneg, hT⟩ := psi_pos_atBot hc
    have hTle : min t0 T ≤ t0 := min_le_left _ _
    have hpT : 0 < psi c (min t0 T) := hT _ (min_le_right _ _)
    obtain ⟨p, hpmem, hp⟩ := intermediate_value_Icc' hTle (continuous_psi c).continuousOn
      (show (0:ℝ) ∈ Icc (psi c t0) (psi c (min t0 T)) from ⟨hneg.le, hpT.le⟩)
    have hpneg : p < 0 := lt_of_le_of_lt hpmem.2 ht0neg
    refine ⟨p, hpneg.ne, hp, ?_⟩
    constructor
    · intro h; linarith
    · intro h; linarith

/-! ### Item (1): the two sign equivalences -/

/-- **`lem:doubling_cramer_root`(1), second equivalence, `⟸`.** `c < 1` forces `p_* > 1`. -/
theorem cramer_root_gt_one {c p : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hp0 : p ≠ 0) (hp : psi c p = 0) : 1 < p := by
  have h1 : psi c 1 = c - 1 := by rw [psi]; norm_num
  have hneg : psi c 1 < 0 := by rw [h1]; linarith
  rcases lt_trichotomy p 0 with hpz | hpz | hpz
  · have := psi_pos_of_outside (t := 1) hc hp (psi_zero c) hpz (Or.inr (by norm_num))
    linarith
  · exact absurd hpz hp0
  · by_contra hcon
    rw [not_lt] at hcon
    have hne1 : p ≠ 1 := by rintro rfl; rw [hp] at hneg; exact lt_irrefl 0 hneg
    have hplt : p < 1 := lt_of_le_of_ne hcon hne1
    have := psi_pos_of_outside (t := 1) hc (psi_zero c) hp hpz (Or.inr hplt)
    linarith

/-- **`lem:doubling_cramer_root`(1), second equivalence, `⟹`.** `p_* > 1` forces `c < 1`. -/
theorem cramer_lt_one_of_root_gt_one {c p : ℝ} (hc : 0 < c) (hp : psi c p = 0) (hp1 : 1 < p) :
    c < 1 := by
  have := psi_neg_of_between hc (psi_zero c) hp (by linarith) (by norm_num) hp1
  rw [psi] at this; norm_num at this; linarith

/-- **`lem:doubling_cramer_root`(1), first equivalence.** -/
theorem cramer_root_pos_iff {c p : ℝ} (hc : 0 < c) (hne : c * log 2 ≠ 1)
    (hp0 : p ≠ 0) (hp : psi c p = 0) : 0 < p ↔ c * log 2 < 1 := by
  obtain ⟨q, hq0, hq, hqiff⟩ := cramer_root_exists hc hne
  rw [cramer_root_unique hc hp0 hq0 hp hq]; exact hqiff

/-! ### Item (2): the Cramér equation in ratio form, and the kernel -/

/-- **`eq:doubling_cramer_form`.** `c(τ−1)/p_* = 1`. -/
theorem cramer_form {c p : ℝ} (hp0 : p ≠ 0) (hp : psi c p = 0) :
    c * (((2 : ℝ) ^ p - 1) / p) = 1 := by
  rw [psi, sub_eq_zero] at hp
  field_simp
  linarith [hp]

/-- **`lem:doubling_cramer_root`(2), the kernel.** `∫₀¹ c ln 2 · 2^{p v} dv = 1`. -/
theorem cramer_kernel_integral {c p : ℝ} (hp0 : p ≠ 0) (hp : psi c p = 0) :
    (∫ v in (0 : ℝ)..1, c * log 2 * (2 : ℝ) ^ (p * v)) = 1 := by
  have hL : (0 : ℝ) < log 2 := log_two_pos
  have hpL : p * log 2 ≠ 0 := mul_ne_zero hp0 hL.ne'
  have hrw : ∀ v : ℝ, (2 : ℝ) ^ (p * v) = exp (p * log 2 * v) := by
    intro v; rw [two_rpow_eq]; ring_nf
  rw [intervalIntegral.integral_congr (g := fun v => c * log 2 * exp (p * log 2 * v))
      (fun v _ => by rw [hrw v])]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x : ℝ => exp x) hpL]
  rw [integral_exp]
  have hexp : exp (p * log 2) = (2 : ℝ) ^ p := by rw [two_rpow_eq]
  have hcf := cramer_form hp0 hp
  simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul]
  rw [hexp]
  field_simp at hcf ⊢
  linarith [hcf]

/-! ### Item (3): the four inequalities at `0 < c < 1` -/

section Ineq
variable {c p : ℝ}

/-- **`eq:doubling_cramer_ineq`.** At `0 < c < 1`, with `τ := 2^{p_*}`:
`τ > 2`, `τ > p_*+1`, `2τ > p_*+2` and `4τ > p_*+3`. -/
theorem cramer_ineq (hc : 0 < c) (hc1 : c < 1) (hp0 : p ≠ 0) (hp : psi c p = 0) :
    2 < (2 : ℝ) ^ p ∧ p + 1 < (2 : ℝ) ^ p ∧ p + 2 < 2 * (2 : ℝ) ^ p ∧
      p + 3 < 4 * (2 : ℝ) ^ p := by
  have hp1 : 1 < p := cramer_root_gt_one hc hc1 hp0 hp
  have e1 : (2 : ℝ) ^ (p + 1) = 2 * (2 : ℝ) ^ p := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  have e2 : (2 : ℝ) ^ (p + 2) = 4 * (2 : ℝ) ^ p := by
    have hsplit : p + 2 = p + 1 + 1 := by ring
    rw [hsplit, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one,
      Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
    ring
  refine ⟨?_, two_rpow_gt_add_one hp1, ?_, ?_⟩
  · have : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ p :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr hp1
    simpa using this
  · have := two_rpow_gt_add_one (show (1:ℝ) < p + 1 by linarith)
    rw [e1] at this; linarith
  · have := two_rpow_gt_add_one (show (1:ℝ) < p + 2 by linarith)
    rw [e2] at this; linarith

end Ineq

end GFNBounds.Doubling
