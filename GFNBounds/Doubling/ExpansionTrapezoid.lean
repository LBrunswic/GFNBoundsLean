import GFNBounds.Doubling.ExpansionSecond

/-!
# The paper's own Step 2: `eq:doubling_em` with the Euler–Maclaurin remainder bound

**`lem:doubling_expansion`** — `app_doubling.tex`, Step 2 of the proof (`eq:doubling_em`)
and **`rem:doubling_parity`** — `app_doubling.tex`, which reads off `eq:doubling_Rexp`.

> (Step 2, `eq:doubling_em`) Let `r > 1` and let `1 ≤ a < b` be integers. Euler–Maclaurin for
> `f(t) = t^{−r}` on `[a, b]`, truncated before its first Bernoulli term, gives
> `Σ_{j=a}^{b−1} j^{−r} = (a^{1−r} − b^{1−r})/(r−1) + (a^{−r} − b^{−r})/2 + E`,
> `|E| ≤ (r/12)(a^{−r−1} + b^{−r−1})`,
> the bound on `E` because `t ↦ t^{−r}` is completely monotone on `(0, +∞)`, so that the
> remainder of the expansion after any number of terms is bounded in modulus by the first omitted
> term, here `(1/12)|f′(b) − f′(a)| = (r/12)(a^{−r−1} − b^{−r−1})`.

## What is proved, and where

Every *statement* clause of `lem:doubling_expansion` and `rem:doubling_parity` is already closed in
the strict library (`GFNBounds/Doubling/Expansion.lean`, `GFNBounds/Doubling/ExpansionSecond.lean`:
`Decay.Rexp`, `Decay.Rexp_isBigO`, `Decay.cR_congr`, `Decay.A_gap`, `Decay.wm_foot_expansion`,
`Decay.R0_gt_one_of_even`, `Decay.R0_lt_one_of_odd`, `Decay.not_isSupersolution_Phi_zero`,
`Decay.not_isSubsolution_Phi_zero`). The one disclosure left on the expansion row was that the
proof's Step 2 went through Mathlib's trapezoidal rule with the cruder remainder
`|E| ≤ r(r+1)/12 · Σ j^{−r−2}` (`window_sum_second`), so the paper's own display `eq:doubling_em`
was not certified. This file certifies it, in the sharper form the paper's justification names:

| paper clause | Lean |
|---|---|
| `E ≥ 0` and `E ≤ (r/12)(a^{−r−1} − b^{−r−1})`, the first omitted term | `EMTrap.em_window_bounds` |
| `|E| ≤ (r/12)(a^{−r−1} + b^{−r−1})`, `eq:doubling_em` as printed | `EMTrap.em_window` |
| per unit interval, `0 ≤` trapezoid error `≤ (1/12)(f′(t+1) − f′(t))` | `EMTrap.trap_unit_lower`, `EMTrap.trap_unit_upper` (any `f` with `f″ ≥ 0`, resp. `f⁗ ≥ 0`) |

## SCOPE (disclosed)

* **The route to the remainder bound.** The paper invokes the classical fact that for a completely
  monotone `f` the Euler–Maclaurin remainder is bounded by the first omitted term. That theorem is
  not in Mathlib at this pin and is not formalized in general. What is proved is the instance the
  paper uses, at the first Bernoulli term: on each unit interval `[t, t+1]`, with
  `Φ(h) = h/2·(f(t)+f(t+h)) − ∫_t^{t+h} f − h²/12·(f′(t+h) − f′(t))`, one has
  `Φ(0) = Φ′(0) = Φ″(0) = 0` and `Φ‴(h) = −h²/12 · f⁗(t+h) ≤ 0`, so `Φ(1) ≤ 0`; and the plain
  trapezoid error has second derivative `h/2 · f″(t+h) ≥ 0`, so it is `≥ 0`. It uses only
  `f″ ≥ 0` and `f⁗ ≥ 0` on `[a, b]`, which `t^{−r}` satisfies; the integral is taken in closed form
  (an antiderivative `F` with `F′ = f`), so no integration theory is needed. Summing and
  telescoping gives `0 ≤ E ≤ (r/12)(a^{−r−1} − b^{−r−1})`, which implies the printed bound.
* **Range.** Stated for integers `1 ≤ a ≤ b`, containing the paper's `1 ≤ a < b` (at `a = b`
  the remainder `E` is `0`).
* **No new hypothesis bundle.** The statements quantify over reals `r > 1` and naturals `a ≤ b`
  only, so nothing here needs a witness.
* This file does not re-route `Decay.Rexp`: that theorem is closed and its constant stands.
  Swapping Step 2 into it would sharpen `cR` and change no statement.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `r > 1` | ✓ carried |
| integers `1 ≤ a < b` | ⚠ widened to `1 ≤ a ≤ b` (a stronger statement; `a = b` is trivial) |
| complete monotonicity of `t^{−r}` | used only through `f″ ≥ 0`, `f⁗ ≥ 0` on `[a, b]`, both proved |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

namespace EMTrap

open Real Set

/-! ## Sign from a derivative on `[0, 1]` -/

theorem le_zero_of_hasDerivAt {g g' : ℝ → ℝ} (hd : ∀ h ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' h) h)
    (hneg : ∀ h ∈ Icc (0 : ℝ) 1, g' h ≤ 0) (h0 : g 0 = 0) :
    ∀ h ∈ Icc (0 : ℝ) 1, g h ≤ 0 := by
  have hanti : AntitoneOn g (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (Ioo_subset_Icc_self hx)).deriv]
      exact hneg x (Ioo_subset_Icc_self hx)
  intro h hh
  have := hanti (left_mem_Icc.2 zero_le_one) hh hh.1
  linarith

theorem zero_le_of_hasDerivAt {g g' : ℝ → ℝ} (hd : ∀ h ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' h) h)
    (hpos : ∀ h ∈ Icc (0 : ℝ) 1, 0 ≤ g' h) (h0 : g 0 = 0) :
    ∀ h ∈ Icc (0 : ℝ) 1, 0 ≤ g h := by
  have hmono : MonotoneOn g (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (Ioo_subset_Icc_self hx)).deriv]
      exact hpos x (Ioo_subset_Icc_self hx)
  intro h hh
  have := hmono (left_mem_Icc.2 zero_le_one) hh hh.1
  linarith

theorem shift_mem {t h : ℝ} (hh : h ∈ Icc (0 : ℝ) 1) : t + h ∈ Icc t (t + 1) :=
  ⟨by linarith [hh.1], by linarith [hh.2]⟩

/-! ## One unit interval, for a general `f` -/

section Unit

variable {F f f1 f2 f3 f4 : ℝ → ℝ} {t : ℝ}

/-- **The trapezoid error is non-negative for a convex `f`.** If `F′ = f`, `f′ = f₁`, `f₁′ = f₂`
on `[t, t+1]` and `f₂ ≥ 0` there, then `(f(t) + f(t+1))/2 − (F(t+1) − F(t)) ≥ 0`. -/
theorem trap_unit_lower
    (hF : ∀ x ∈ Icc t (t + 1), HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Icc t (t + 1), HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Icc t (t + 1), HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x ∈ Icc t (t + 1), 0 ≤ f2 x) :
    0 ≤ (f t + f (t + 1)) / 2 - (F (t + 1) - F t) := by
  set P1 : ℝ → ℝ := fun h => 1 / 2 * (f t - f (t + h)) + h / 2 * f1 (t + h) with hP1
  set P : ℝ → ℝ := fun h => h / 2 * (f t + f (t + h)) - (F (t + h) - F t) with hP
  have dP1 : ∀ h ∈ Icc (0 : ℝ) 1, HasDerivAt P1 (h / 2 * f2 (t + h)) h := by
    intro h hh
    have hm := shift_mem (t := t) hh
    have e := (((hasDerivAt_const h (f t)).sub ((hf _ hm).comp_const_add t h)).const_mul
      (1 / 2 : ℝ)).add (((hasDerivAt_id' h).div_const 2).mul ((hf1 _ hm).comp_const_add t h))
    refine e.congr_deriv ?_
    ring
  have hP1nn := zero_le_of_hasDerivAt dP1
    (fun h hh => mul_nonneg (by linarith [hh.1]) (h2 _ (shift_mem hh)))
    (by simp only [hP1, add_zero, sub_self, mul_zero, zero_div, zero_mul])
  have dP : ∀ h ∈ Icc (0 : ℝ) 1, HasDerivAt P (P1 h) h := by
    intro h hh
    have hm := shift_mem (t := t) hh
    have e := (((hasDerivAt_id' h).div_const 2).mul
      ((hasDerivAt_const h (f t)).add ((hf _ hm).comp_const_add t h))).sub
      (((hF _ hm).comp_const_add t h).sub (hasDerivAt_const h (F t)))
    refine e.congr_deriv ?_
    simp only [Pi.add_apply]
    simp only [hP1]
    ring
  have hPnn := zero_le_of_hasDerivAt dP hP1nn
    (by simp only [hP, add_zero, sub_self, zero_div, zero_mul])
  have := hPnn 1 (right_mem_Icc.2 zero_le_one)
  simp only [hP] at this
  linarith

/-- **The trapezoid error is at most the first Euler–Maclaurin correction when `f⁗ ≥ 0`.** If
`F′ = f`, `f′ = f₁`, `f₁′ = f₂`, `f₂′ = f₃`, `f₃′ = f₄` on `[t, t+1]` and `f₄ ≥ 0` there, then
`(f(t) + f(t+1))/2 − (F(t+1) − F(t)) ≤ (f₁(t+1) − f₁(t))/12`. -/
theorem trap_unit_upper
    (hF : ∀ x ∈ Icc t (t + 1), HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Icc t (t + 1), HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Icc t (t + 1), HasDerivAt f1 (f2 x) x)
    (hf2 : ∀ x ∈ Icc t (t + 1), HasDerivAt f2 (f3 x) x)
    (hf3 : ∀ x ∈ Icc t (t + 1), HasDerivAt f3 (f4 x) x)
    (h4 : ∀ x ∈ Icc t (t + 1), 0 ≤ f4 x) :
    (f t + f (t + 1)) / 2 - (F (t + 1) - F t) ≤ (f1 (t + 1) - f1 t) / 12 := by
  set Q2 : ℝ → ℝ := fun h => -1 / 6 * (f1 (t + h) - f1 t) + h / 6 * f2 (t + h)
    - h * h / 12 * f3 (t + h) with hQ2
  set Q1 : ℝ → ℝ := fun h => 1 / 2 * (f t - f (t + h)) + h / 3 * f1 (t + h) + h / 6 * f1 t
    - h * h / 12 * f2 (t + h) with hQ1
  set Q : ℝ → ℝ := fun h => h / 2 * (f t + f (t + h)) - (F (t + h) - F t)
    - h * h / 12 * (f1 (t + h) - f1 t) with hQ
  have dQ2 : ∀ h ∈ Icc (0 : ℝ) 1, HasDerivAt Q2 (-(h * h / 12 * f4 (t + h))) h := by
    intro h hh
    have hm := shift_mem (t := t) hh
    have e := ((((hf1 _ hm).comp_const_add t h).sub (hasDerivAt_const h (f1 t))).const_mul
      (-1 / 6 : ℝ)).add (((hasDerivAt_id' h).div_const 6).mul ((hf2 _ hm).comp_const_add t h))
      |>.sub ((((hasDerivAt_id' h).mul (hasDerivAt_id' h)).div_const 12).mul
        ((hf3 _ hm).comp_const_add t h))
    refine e.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have nQ2 := le_zero_of_hasDerivAt dQ2
    (fun h hh => neg_nonpos.2 (mul_nonneg (by nlinarith [hh.1]) (h4 _ (shift_mem hh))))
    (by simp only [hQ2, add_zero, sub_self, mul_zero, zero_div, zero_mul])
  have dQ1 : ∀ h ∈ Icc (0 : ℝ) 1, HasDerivAt Q1 (Q2 h) h := by
    intro h hh
    have hm := shift_mem (t := t) hh
    have e := ((((hasDerivAt_const h (f t)).sub ((hf _ hm).comp_const_add t h)).const_mul
      (1 / 2 : ℝ)).add (((hasDerivAt_id' h).div_const 3).mul ((hf1 _ hm).comp_const_add t h))
      |>.add (((hasDerivAt_id' h).div_const 6).mul (hasDerivAt_const h (f1 t)))
      |>.sub ((((hasDerivAt_id' h).mul (hasDerivAt_id' h)).div_const 12).mul
        ((hf2 _ hm).comp_const_add t h)))
    refine e.congr_deriv ?_
    simp only [Pi.mul_apply]
    simp only [hQ2]
    ring
  have nQ1 := le_zero_of_hasDerivAt dQ1 nQ2
    (by simp only [hQ1, add_zero, sub_self, mul_zero, zero_div, zero_mul])
  have dQ : ∀ h ∈ Icc (0 : ℝ) 1, HasDerivAt Q (Q1 h) h := by
    intro h hh
    have hm := shift_mem (t := t) hh
    have e := ((((hasDerivAt_id' h).div_const 2).mul
      ((hasDerivAt_const h (f t)).add ((hf _ hm).comp_const_add t h))).sub
      (((hF _ hm).comp_const_add t h).sub (hasDerivAt_const h (F t)))).sub
      ((((hasDerivAt_id' h).mul (hasDerivAt_id' h)).div_const 12).mul
        (((hf1 _ hm).comp_const_add t h).sub (hasDerivAt_const h (f1 t))))
    refine e.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    simp only [hQ1]
    ring
  have nQ := le_zero_of_hasDerivAt dQ nQ1
    (by simp only [hQ, add_zero, sub_self, mul_zero, zero_div, zero_mul])
  have := nQ 1 (right_mem_Icc.2 zero_le_one)
  simp only [hQ] at this
  linarith

end Unit

/-! ## The instance `f(t) = t^{−r}` -/

theorem hasDerivAt_mul_rpow (k q q' : ℝ) (hq : q - 1 = q') {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => k * y ^ q) (k * q * x ^ q') x := by
  have e := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hx.ne')).const_mul k
  rw [← hq]
  exact e.congr_deriv (by ring)

/-- **One unit interval for `t^{−r}`.** For `r > 1` and `t > 0`, the trapezoid error of
`x ↦ x^{−r}` on `[t, t+1]` lies in `[0, (r/12)(t^{−r−1} − (t+1)^{−r−1})]`. -/
theorem trap_unit_rpow {r t : ℝ} (hr : 1 < r) (ht : 0 < t) :
    0 ≤ (t ^ (-r) + (t + 1) ^ (-r)) / 2 - (t ^ (1 - r) - (t + 1) ^ (1 - r)) / (r - 1)
    ∧ (t ^ (-r) + (t + 1) ^ (-r)) / 2 - (t ^ (1 - r) - (t + 1) ^ (1 - r)) / (r - 1)
      ≤ r / 12 * (t ^ (-r - 1) - (t + 1) ^ (-r - 1)) := by
  have hr0 : 0 < r := by linarith
  have hr1 : r - 1 ≠ 0 := by linarith
  have hpos : ∀ x ∈ Icc t (t + 1), 0 < x := fun x hx => lt_of_lt_of_le ht hx.1
  set F : ℝ → ℝ := fun y => (-1 / (r - 1)) * y ^ (1 - r) with hF
  set f : ℝ → ℝ := fun y => 1 * y ^ (-r) with hf
  set f1 : ℝ → ℝ := fun y => -r * y ^ (-r - 1) with hf1
  set f2 : ℝ → ℝ := fun y => (r * (r + 1)) * y ^ (-r - 2) with hf2
  set f3 : ℝ → ℝ := fun y => (-(r * (r + 1) * (r + 2))) * y ^ (-r - 3) with hf3
  set f4 : ℝ → ℝ := fun y => (r * (r + 1) * (r + 2) * (r + 3)) * y ^ (-r - 4) with hf4
  have dF : ∀ x ∈ Icc t (t + 1), HasDerivAt F (f x) x := by
    intro x hx
    have e := hasDerivAt_mul_rpow (-1 / (r - 1)) (1 - r) (-r) (by ring) (hpos x hx)
    convert e using 1
    simp only [hf]
    field_simp
    ring
  have df : ∀ x ∈ Icc t (t + 1), HasDerivAt f (f1 x) x := by
    intro x hx
    have e := hasDerivAt_mul_rpow 1 (-r) (-r - 1) (by ring) (hpos x hx)
    convert e using 1
    simp only [hf1]
    ring
  have df1 : ∀ x ∈ Icc t (t + 1), HasDerivAt f1 (f2 x) x := by
    intro x hx
    have e := hasDerivAt_mul_rpow (-r) (-r - 1) (-r - 2) (by ring) (hpos x hx)
    convert e using 1
    simp only [hf2]
    ring
  have df2 : ∀ x ∈ Icc t (t + 1), HasDerivAt f2 (f3 x) x := by
    intro x hx
    have e := hasDerivAt_mul_rpow (r * (r + 1)) (-r - 2) (-r - 3) (by ring) (hpos x hx)
    convert e using 1
    simp only [hf3]
    ring
  have df3 : ∀ x ∈ Icc t (t + 1), HasDerivAt f3 (f4 x) x := by
    intro x hx
    have e := hasDerivAt_mul_rpow (-(r * (r + 1) * (r + 2))) (-r - 3) (-r - 4) (by ring)
      (hpos x hx)
    convert e using 1
    simp only [hf4]
    ring
  have h2 : ∀ x ∈ Icc t (t + 1), 0 ≤ f2 x := fun x hx => by
    have := hpos x hx
    simp only [hf2]
    positivity
  have h4 : ∀ x ∈ Icc t (t + 1), 0 ≤ f4 x := fun x hx => by
    have := hpos x hx
    simp only [hf4]
    positivity
  have lo := trap_unit_lower dF df df1 h2
  have up := trap_unit_upper dF df df1 df2 df3 h4
  simp only [hF, hf, hf1, one_mul] at lo up
  have eF : ((-1 / (r - 1)) * (t + 1) ^ (1 - r) - (-1 / (r - 1)) * t ^ (1 - r))
      = (t ^ (1 - r) - (t + 1) ^ (1 - r)) / (r - 1) := by
    field_simp
    ring
  rw [eF] at lo up
  refine ⟨lo, ?_⟩
  have e1 : (-r * (t + 1) ^ (-r - 1) - -r * t ^ (-r - 1)) / 12
      = r / 12 * (t ^ (-r - 1) - (t + 1) ^ (-r - 1)) := by ring
  rw [e1] at up
  exact up

/-! ## The window: `eq:doubling_em` -/

/-- **`eq:doubling_em`, the paper's Step 2, with the first-omitted-term bound.** For `r > 1` and
integers `1 ≤ a ≤ b`, the remainder
`E := Σ_{j=a}^{b−1} j^{−r} − (a^{1−r} − b^{1−r})/(r−1) − (a^{−r} − b^{−r})/2`
satisfies `0 ≤ E ≤ (r/12)(a^{−r−1} − b^{−r−1})`. -/
theorem em_window_bounds {r : ℝ} (hr : 1 < r) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-r)
        - ((a : ℝ) ^ (1 - r) - (b : ℝ) ^ (1 - r)) / (r - 1)
        - ((a : ℝ) ^ (-r) - (b : ℝ) ^ (-r)) / 2
    ∧ ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-r)
        - ((a : ℝ) ^ (1 - r) - (b : ℝ) ^ (1 - r)) / (r - 1)
        - ((a : ℝ) ^ (-r) - (b : ℝ) ^ (-r)) / 2
      ≤ r / 12 * ((a : ℝ) ^ (-r - 1) - (b : ℝ) ^ (-r - 1)) := by
  set g : ℕ → ℝ := fun j => (j : ℝ) ^ (-r) with hg
  set G : ℕ → ℝ := fun j => (j : ℝ) ^ (1 - r) / (r - 1) with hG
  set K : ℕ → ℝ := fun j => r / 12 * (j : ℝ) ^ (-r - 1) with hK
  have hcast : ∀ j : ℕ, (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := fun j => by push_cast; ring
  have hkey : ∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-r)
        - ((a : ℝ) ^ (1 - r) - (b : ℝ) ^ (1 - r)) / (r - 1)
        - ((a : ℝ) ^ (-r) - (b : ℝ) ^ (-r)) / 2
      = ∑ j ∈ Finset.Ico a b,
          (((j : ℝ) ^ (-r) + ((j : ℝ) + 1) ^ (-r)) / 2
            - ((j : ℝ) ^ (1 - r) - ((j : ℝ) + 1) ^ (1 - r)) / (r - 1)) := by
    have t1 := telescope_Ico g hab
    have t2 := telescope_Ico G hab
    simp only [hg, hG, hcast] at t1 t2
    have hsplit : ∀ j ∈ Finset.Ico a b,
        (((j : ℝ) ^ (-r) + ((j : ℝ) + 1) ^ (-r)) / 2
            - ((j : ℝ) ^ (1 - r) - ((j : ℝ) + 1) ^ (1 - r)) / (r - 1))
          = (j : ℝ) ^ (-r) - ((j : ℝ) ^ (-r) - ((j : ℝ) + 1) ^ (-r)) / 2
            - ((j : ℝ) ^ (1 - r) / (r - 1) - ((j : ℝ) + 1) ^ (1 - r) / (r - 1)) := by
      intro j _
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, t1, t2]
    ring
  have tK := telescope_Ico K hab
  simp only [hK, hcast] at tK
  rw [hkey]
  have hunit : ∀ j ∈ Finset.Ico a b, _ := fun j hj =>
    trap_unit_rpow hr (show (0 : ℝ) < (j : ℝ) by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_trans ha (Finset.mem_Ico.mp hj).1))
  refine ⟨Finset.sum_nonneg fun j hj => (hunit j hj).1, ?_⟩
  have e : r / 12 * ((a : ℝ) ^ (-r - 1) - (b : ℝ) ^ (-r - 1))
      = ∑ j ∈ Finset.Ico a b,
          (r / 12 * (j : ℝ) ^ (-r - 1) - r / 12 * ((j : ℝ) + 1) ^ (-r - 1)) := by
    rw [tK]; ring
  rw [e]
  refine Finset.sum_le_sum fun j hj => ?_
  have := (hunit j hj).2
  linarith

/-- **`eq:doubling_em` as printed.** For `r > 1` and integers `1 ≤ a ≤ b`,
`|E| ≤ (r/12)(a^{−r−1} + b^{−r−1})`. -/
theorem em_window {r : ℝ} (hr : 1 < r) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |∑ j ∈ Finset.Ico a b, (j : ℝ) ^ (-r)
        - ((a : ℝ) ^ (1 - r) - (b : ℝ) ^ (1 - r)) / (r - 1)
        - ((a : ℝ) ^ (-r) - (b : ℝ) ^ (-r)) / 2|
      ≤ r / 12 * ((a : ℝ) ^ (-r - 1) + (b : ℝ) ^ (-r - 1)) := by
  obtain ⟨lo, up⟩ := em_window_bounds hr ha hab
  have hb : 0 ≤ (b : ℝ) ^ (-r - 1) := rpow_nonneg (Nat.cast_nonneg b) _
  have hr0 : 0 ≤ r / 12 := by linarith
  rw [abs_of_nonneg lo]
  nlinarith

end EMTrap

end GFNBounds.Doubling
