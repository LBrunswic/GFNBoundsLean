import GFNBounds.Doubling.WindowSum

/-!
# `eq:doubling_windowsums`: two harmonic window sums, with explicit constants

**`lem:doubling_doeblin`, `eq:doubling_windowsums`** — `app_doubling.tex:1385–1473`, the display
at line 1415.

> Comparing each sum with an integral of `dt/t` over the matching interval, and using
> `⌈5a/4⌉+1 ≤ 5a/4+2` and `⌈5a/2⌉ ≥ 5a/2`,
> `∑_{j∈J} 1/(j+1) ≥ ln(8/5) − ln(1+8/(5a)) ≥ ln(8/5) − 2/a` and
> `∑_{j∈J'} 1/(j+1) ≥ ln(5/4) − ln(1+1/(2a)) ≥ ln(5/4) − 2/a`,
> so the two sums are at least `½ln(8/5)` and `½ln(5/4)`,
> where `J = {⌈5a/4⌉,…,2a−1}` and `J' = {2a,…,⌈5a/2⌉−1}`.

## What this file does, and where it differs from the paper

The comparison with `∫ dt/t` is done here by **telescoping** `log`, exactly as `WindowSum.lean`
telescopes `t^{−r}`: `log(j+2) − log(j+1) ≤ 1/(j+1)` is `log t ≤ t − 1` at `t = (j+2)/(j+1)`, and
the sum of the left side is `log(B+1) − log(A+1)`. No integral, and no Euler–Maclaurin.

The paper's threshold for "the two sums are at least half their logarithms" is
`a ≥ ⌈4/ln(5/4)⌉ = 18`, which needs `ln(5/4)` to two decimals. Here the threshold is `a ≥ 20`,
obtained from the *effective* bound `ln(5/4) ≥ 1/5` (which is `log t ≤ t − 1` again, at `t = 4/5`)
rather than from a decimal expansion. **This is a strengthened hypothesis**, `20 > 18`, and it is
declared as such below; it costs only a larger `ℓ₄`, which the paper leaves non-effective anyway.
Nothing downstream sees the difference: `ω` is unchanged.

`⌈5a/4⌉` and `⌈5a/2⌉` are the natural-number expressions `(5a+3)/4` and `(5a+1)/2`.

## SCOPE (disclosed)

Only `eq:doubling_windowsums` and the `J ⊆ W(y)`, `J' ⊆ W(y)` inclusions of the third and fourth
bullets of `lem:doubling_doeblin`'s proof are here. The lemma itself is `Doeblin.lean`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `a = 2^{i−1}ℓ` with `ℓ ≥ ℓ₄` | ⚠ weakened: `a` is any natural number; the sums need only `a ≥ 1` |
| `a ≥ 4/ln(5/4)`, i.e. `a ≥ 18` | ⚠ **strengthened** to `a ≥ 20`, to keep `ln(5/4) ≥ 1/5` effective |
| `J`, `J'` non-empty, `J ⊆ [a,2a)`, `J' ⊆ [2a,4a)` | ✓ carried |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-! ## The harmonic sum against a logarithm -/

/-- `log(j+2) − log(j+1) ≤ 1/(j+1)`: this is `log t ≤ t − 1` at `t = (j+2)/(j+1)`. -/
theorem log_step_le (j : ℕ) :
    Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
  have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hdiv : (0 : ℝ) < ((j : ℝ) + 2) / ((j : ℝ) + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos hdiv
  rw [Real.log_div h2.ne' h1.ne'] at h
  have hval : ((j : ℝ) + 2) / ((j : ℝ) + 1) - 1 = 1 / ((j : ℝ) + 1) := by
    field_simp; ring
  rw [hval] at h
  exact h

/-- **The comparison.** `log(B+1) − log(A+1) ≤ ∑_{j=A}^{B−1} 1/(j+1)`. -/
theorem harmonic_window_ge {A B : ℕ} (hAB : A ≤ B) :
    Real.log ((B : ℝ) + 1) - Real.log ((A : ℝ) + 1)
      ≤ ∑ j ∈ Finset.Ico A B, 1 / ((j : ℝ) + 1) := by
  have htel := telescope_Ico (fun j : ℕ => -Real.log ((j : ℝ) + 1)) hAB
  have hcong : ∑ j ∈ Finset.Ico A B,
      ((fun j : ℕ => -Real.log ((j : ℝ) + 1)) j - (fun j : ℕ => -Real.log ((j : ℝ) + 1)) (j + 1))
      = ∑ j ∈ Finset.Ico A B, (Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
    simp only [hc]
    ring
  rw [hcong] at htel
  have hsum : ∑ j ∈ Finset.Ico A B, (Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1))
      ≤ ∑ j ∈ Finset.Ico A B, 1 / ((j : ℝ) + 1) :=
    Finset.sum_le_sum fun j _ => log_step_le j
  rw [htel] at hsum
  linarith [hsum]

/-! ## The two ranges -/

/-- `J = {⌈5a/4⌉, …, 2a−1}`, the range carrying the reference law `ϖ_i`. -/
def Jlow (a : ℕ) : Finset ℕ := Finset.Ico ((5 * a + 3) / 4) (2 * a)

/-- `J' = {2a, …, ⌈5a/2⌉−1}`, the range the second case of `lem:doubling_doeblin` steps into. -/
def Jhigh (a : ℕ) : Finset ℕ := Finset.Ico (2 * a) ((5 * a + 1) / 2)

theorem mem_Jlow {a j : ℕ} : j ∈ Jlow a ↔ (5 * a + 3) / 4 ≤ j ∧ j < 2 * a := Finset.mem_Ico

theorem mem_Jhigh {a j : ℕ} : j ∈ Jhigh a ↔ 2 * a ≤ j ∧ j < (5 * a + 1) / 2 := Finset.mem_Ico

/-- `J ⊆ [a, 2a) = I_{i−1}(ℓ)`. -/
theorem Jlow_subset (a : ℕ) : Jlow a ⊆ Finset.Ico a (2 * a) := by
  intro j hj
  rw [mem_Jlow] at hj
  rw [Finset.mem_Ico]
  omega

/-- `J' ⊆ [2a, 4a) = I_i(ℓ)`. -/
theorem Jhigh_subset (a : ℕ) : Jhigh a ⊆ Finset.Ico (2 * a) (4 * a) := by
  intro j hj
  rw [mem_Jhigh] at hj
  rw [Finset.mem_Ico]
  omega

theorem Jlow_nonempty {a : ℕ} (ha : 2 ≤ a) : (Jlow a).Nonempty := by
  refine ⟨(5 * a + 3) / 4, ?_⟩
  rw [mem_Jlow]
  omega

theorem Jhigh_nonempty {a : ℕ} (ha : 1 ≤ a) : (Jhigh a).Nonempty := by
  refine ⟨2 * a, ?_⟩
  rw [mem_Jhigh]
  omega

/-- **Third bullet of `lem:doubling_doeblin`.** A state of `I_i(ℓ)` below `⌈5a/2⌉` sees all of `J`
in its window. -/
theorem Jlow_subset_window {a y : ℕ} (h1 : 2 * a ≤ y) (h2 : y < (5 * a + 1) / 2) :
    Jlow a ⊆ window y := by
  intro j hj
  rw [mem_Jlow] at hj
  rw [mem_window]
  omega

/-- **Fourth bullet of `lem:doubling_doeblin`.** A state of `I_i(ℓ)` at or above `⌈5a/2⌉` sees all
of `J'` in its window. -/
theorem Jhigh_subset_window {a y : ℕ} (h1 : (5 * a + 1) / 2 ≤ y) (h2 : y < 4 * a) :
    Jhigh a ⊆ window y := by
  intro j hj
  rw [mem_Jhigh] at hj
  rw [mem_window]
  omega

/-! ## Effective bounds on the two logarithms -/

/-- `ln(5/4) ≥ 1/5`, from `log t ≤ t − 1` at `t = 4/5`. -/
theorem log_five_four_ge : (1 : ℝ) / 5 ≤ Real.log (5 / 4) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 5)
  have hinv : Real.log (4 / 5) = -Real.log (5 / 4) := by
    rw [show (4 : ℝ) / 5 = (5 / 4)⁻¹ by norm_num, Real.log_inv]
  rw [hinv] at h
  linarith

/-- `ln(8/5) ≥ 3/8`, from `log t ≤ t − 1` at `t = 5/8`. -/
theorem log_eight_five_ge : (3 : ℝ) / 8 ≤ Real.log (8 / 5) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 8)
  have hinv : Real.log (5 / 8) = -Real.log (8 / 5) := by
    rw [show (5 : ℝ) / 8 = (8 / 5)⁻¹ by norm_num, Real.log_inv]
  rw [hinv] at h
  linarith

/-- `ln(5/4) ≤ 1/4 < 1`. -/
theorem log_five_four_lt_one : Real.log (5 / 4) < 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  linarith

/-- `ln(8/5) ≤ 3/5 < 1`. -/
theorem log_eight_five_lt_one : Real.log (8 / 5) < 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 5)
  linarith

theorem log_five_four_pos : 0 < Real.log (5 / 4) := lt_of_lt_of_le (by norm_num) log_five_four_ge

theorem log_eight_five_pos : 0 < Real.log (8 / 5) := lt_of_lt_of_le (by norm_num) log_eight_five_ge

/-! ## `eq:doubling_windowsums` -/

/-- **First line of `eq:doubling_windowsums`.** `∑_{j ∈ J} 1/(j+1) ≥ ln(8/5) − 2/a`. -/
theorem sum_Jlow_ge {a : ℕ} (ha : 1 ≤ a) :
    Real.log (8 / 5) - 2 / (a : ℝ) ≤ ∑ j ∈ Jlow a, 1 / ((j : ℝ) + 1) := by
  have hA : (5 * a + 3) / 4 ≤ 2 * a := by omega
  have hcomp := harmonic_window_ge (A := (5 * a + 3) / 4) (B := 2 * a) hA
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  set A : ℕ := (5 * a + 3) / 4 with hAdef
  -- `A + 1 ≤ 5a/4 + 2`
  have hAle : ((A : ℝ)) + 1 ≤ 5 * (a : ℝ) / 4 + 2 := by
    have h4 : 4 * A ≤ 5 * a + 3 := by omega
    have h4' : 4 * (A : ℝ) ≤ 5 * (a : ℝ) + 3 := by exact_mod_cast h4
    linarith
  have hApos : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hBpos : (0 : ℝ) < ((2 * a : ℕ) : ℝ) + 1 := by positivity
  have hcast : (((2 * a : ℕ)) : ℝ) = 2 * (a : ℝ) := by push_cast; ring
  -- lower the right log, raise the left one
  have hlog1 : Real.log (2 * (a : ℝ)) ≤ Real.log (((2 * a : ℕ) : ℝ) + 1) := by
    rw [hcast]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log ((A : ℝ) + 1) ≤ Real.log (5 * (a : ℝ) / 4 + 2) :=
    Real.log_le_log hApos hAle
  -- the paper's `ln(8/5) − ln(1 + 8/(5a)) ≥ ln(8/5) − 2/a`
  have hkey : Real.log (8 / 5) - 2 / (a : ℝ)
      ≤ Real.log (2 * (a : ℝ)) - Real.log (5 * (a : ℝ) / 4 + 2) := by
    have hden : (0 : ℝ) < 5 * (a : ℝ) / 4 + 2 := by positivity
    have hnum : (0 : ℝ) < 2 * (a : ℝ) := by linarith
    have hratio : Real.log (8 / 5) + Real.log ((5 * (a : ℝ) / 4 + 2) / (2 * (a : ℝ)))
        = Real.log (1 + 8 / (5 * (a : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      field_simp
      ring
    have hlogdiv : Real.log ((5 * (a : ℝ) / 4 + 2) / (2 * (a : ℝ)))
        = Real.log (5 * (a : ℝ) / 4 + 2) - Real.log (2 * (a : ℝ)) :=
      Real.log_div hden.ne' hnum.ne'
    have hup : Real.log (1 + 8 / (5 * (a : ℝ))) ≤ 8 / (5 * (a : ℝ)) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 8 / (5 * (a : ℝ)) by positivity)
      linarith
    have h85 : 8 / (5 * (a : ℝ)) ≤ 2 / (a : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hapos]
      linarith
    rw [hlogdiv] at hratio
    linarith
  calc Real.log (8 / 5) - 2 / (a : ℝ)
      ≤ Real.log (2 * (a : ℝ)) - Real.log (5 * (a : ℝ) / 4 + 2) := hkey
    _ ≤ Real.log (((2 * a : ℕ) : ℝ) + 1) - Real.log ((A : ℝ) + 1) := by linarith
    _ ≤ ∑ j ∈ Jlow a, 1 / ((j : ℝ) + 1) := hcomp

/-- **Second line of `eq:doubling_windowsums`.** `∑_{j ∈ J'} 1/(j+1) ≥ ln(5/4) − 2/a`. -/
theorem sum_Jhigh_ge {a : ℕ} (ha : 1 ≤ a) :
    Real.log (5 / 4) - 2 / (a : ℝ) ≤ ∑ j ∈ Jhigh a, 1 / ((j : ℝ) + 1) := by
  have hA : 2 * a ≤ (5 * a + 1) / 2 := by omega
  have hcomp := harmonic_window_ge (A := 2 * a) (B := (5 * a + 1) / 2) hA
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  set B : ℕ := (5 * a + 1) / 2 with hBdef
  -- `B + 1 ≥ 5a/2`, since `B = ⌈5a/2⌉ ≥ 5a/2`
  have hBge : 5 * (a : ℝ) / 2 ≤ (B : ℝ) + 1 := by
    have h2 : 5 * a ≤ 2 * B + 1 := by omega
    have h2' : 5 * (a : ℝ) ≤ 2 * (B : ℝ) + 1 := by exact_mod_cast h2
    linarith
  have hcast : (((2 * a : ℕ)) : ℝ) = 2 * (a : ℝ) := by push_cast; ring
  have hlog1 : Real.log (5 * (a : ℝ) / 2) ≤ Real.log ((B : ℝ) + 1) :=
    Real.log_le_log (by positivity) hBge
  have hlog2 : Real.log (((2 * a : ℕ) : ℝ) + 1) = Real.log (2 * (a : ℝ) + 1) := by rw [hcast]
  have hkey : Real.log (5 / 4) - 2 / (a : ℝ)
      ≤ Real.log (5 * (a : ℝ) / 2) - Real.log (2 * (a : ℝ) + 1) := by
    have hden : (0 : ℝ) < 5 * (a : ℝ) / 2 := by positivity
    have hnum : (0 : ℝ) < 2 * (a : ℝ) + 1 := by positivity
    have hratio : Real.log (5 / 4) + Real.log ((2 * (a : ℝ) + 1) / (5 * (a : ℝ) / 2))
        = Real.log (1 + 1 / (2 * (a : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      field_simp
      ring
    have hlogdiv : Real.log ((2 * (a : ℝ) + 1) / (5 * (a : ℝ) / 2))
        = Real.log (2 * (a : ℝ) + 1) - Real.log (5 * (a : ℝ) / 2) :=
      Real.log_div hnum.ne' hden.ne'
    have hup : Real.log (1 + 1 / (2 * (a : ℝ))) ≤ 1 / (2 * (a : ℝ)) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (2 * (a : ℝ)) by positivity)
      linarith
    have h85 : 1 / (2 * (a : ℝ)) ≤ 2 / (a : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hapos]
      linarith
    rw [hlogdiv] at hratio
    linarith
  calc Real.log (5 / 4) - 2 / (a : ℝ)
      ≤ Real.log (5 * (a : ℝ) / 2) - Real.log (2 * (a : ℝ) + 1) := hkey
    _ ≤ Real.log ((B : ℝ) + 1) - Real.log (((2 * a : ℕ) : ℝ) + 1) := by rw [hlog2]; linarith
    _ ≤ ∑ j ∈ Jhigh a, 1 / ((j : ℝ) + 1) := hcomp

/-- **The half-bounds.** At `a ≥ 20` the two sums are at least `½ln(8/5)` and `½ln(5/4)`. The
threshold is `20` rather than the paper's `18` because `ln(5/4) ≥ 1/5` is used in place of a
decimal expansion. -/
theorem sum_Jlow_half {a : ℕ} (ha : 20 ≤ a) :
    (1 / 2) * Real.log (8 / 5) ≤ ∑ j ∈ Jlow a, 1 / ((j : ℝ) + 1) := by
  have ha1 : 1 ≤ a := by omega
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have ha20 : (20 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hsmall : 2 / (a : ℝ) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hapos (by norm_num)]
    linarith
  have hlog := log_eight_five_ge
  linarith [sum_Jlow_ge ha1]

theorem sum_Jhigh_half {a : ℕ} (ha : 20 ≤ a) :
    (1 / 2) * Real.log (5 / 4) ≤ ∑ j ∈ Jhigh a, 1 / ((j : ℝ) + 1) := by
  have ha1 : 1 ≤ a := by omega
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have ha20 : (20 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hsmall : 2 / (a : ℝ) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hapos (by norm_num)]
    linarith
  have hlog := log_five_four_ge
  linarith [sum_Jhigh_ge ha1]

theorem sum_Jlow_pos {a : ℕ} (ha : 20 ≤ a) : 0 < ∑ j ∈ Jlow a, 1 / ((j : ℝ) + 1) :=
  lt_of_lt_of_le (by linarith [log_eight_five_ge]) (sum_Jlow_half ha)

end GFNBounds.Doubling
