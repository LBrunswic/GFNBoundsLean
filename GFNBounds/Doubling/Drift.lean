import GFNBounds.Doubling.Range

/-!
# The drift of the backward chain, and when it is constant

**`prop:doubling_drift`** — `app_doubling.tex:379–397` (Proposition 95 of the ICLR build).

> On the standing range, for every `n ≥ 0` and every ladder `j ≥ 1`,
> `E[X_{n+1} − X_n | X_n = j] = c(j+1)^{1−s} − 1`, and this is independent of `j` **iff** `s = 1`,
> where it equals `c − 1`.

This is `eq:doubling_drift`. It is the fact the whole `s = 1` theory rests on: at `s = 1` the chain
has a *constant* drift `c − 1`, which is what makes `h(j) = j/(1−c)` an exact solution of the
Poisson equation in `lem:doubling_supersolution` and hence gives `prop:doubling_length` its closed
form `E(σ | X₀ = j) = j/(1−c)`.

## SCOPE (disclosed)

The drift is computed as `P⋆ V − V` at the ladder height `V`, which is the one-step expectation
`E[X_{n+1} − X_n | X_n = j]` of the statement; the appendix's `(X_n)` is not constructed here and
no trajectory measure is needed, `P⋆` being by definition the one-step conditional expectation
(`lem:adjoint`(3)). The identity is stated at a ladder state carrying its doubling edge, which on
the loop closure (`cap = none`) is every ladder state; the statement is silent at the source and
the sink, exactly as the paper is.

`height_pstar_sub` is stated for a **free** `ε`, in the form `ε(m)(m+1) − 1`. This is the honest
content: the appendix's `c(j+1)^{1−s} − 1` is that expression evaluated at `ε_{c,s}`, and the
`s = 1` specialisation `ε(j)(j+1) − 1 = c − 1` is the identity `drift_family_at_one` below.

## Hypothesis checklist against `prop:doubling_drift`

| paper hypothesis | here |
|---|---|
| standing range `s ≥ 0`, `0 < c < 2^s` | ⚠ weakened: `height_pstar_sub` needs none of it; `drift_family` needs only `0 < c` |
| ladder state `j ≥ 1` | ✓ carried (`hm`) |
| the loop closure | ⚠ weakened: stated for any `cap` at a state whose doubling edge survives |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

/-- The ladder height, the paper's `V` (`lem:doubling_ramp`): the index of a ladder state, and `0`
at the sink. Note `height .src = 0`, consistent with `s₀ = lad 0`. -/
def height : St → ℝ
  | .lad j => (j : ℝ)
  | .sink => 0

@[simp] theorem height_lad (j : ℕ) : height (.lad j) = (j : ℝ) := rfl
@[simp] theorem height_sink : height .sink = 0 := rfl

variable {S : Setting} {cap : Option ℕ}

/-- **`eq:doubling_drift`, for a free `ε`.** The one-step drift of the backward chain at a ladder
state carrying its doubling edge is `ε(m)(m+1) − 1`.

The computation is the whole content: the chain doubles to `2m` with probability `ε(m)` and
decrements to `m−1` otherwise, so the expected increment is
`ε(m)·m + (1 − ε(m))·(−1) = ε(m)(m+1) − 1`. -/
theorem height_pstar_sub {m : ℕ} (hm : 1 ≤ m) (h : HasDouble cap m) :
    pstar S cap height (.lad m) - height (.lad m) = S.eps m * ((m : ℝ) + 1) - 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  simp only [pstar_lad_succ, h, if_true, height_lad, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  ring

/-- `(m+1)·ε_{c,s}(m) = c(m+1)^{1−s}`, the drift coefficient of `eq:doubling_drift` isolated.
The phase-diagram files rewrite with this directly. -/
theorem base_mul_epsCS (c s : ℝ) (m : ℕ) :
    ((m : ℝ) + 1) * epsCS c s m = c * ((m : ℝ) + 1) ^ (1 - s) := by
  have hb : (0 : ℝ) < (m : ℝ) + 1 := base_pos m
  rw [epsCS, Real.rpow_sub hb, Real.rpow_one]
  field_simp

/-- **`eq:doubling_drift`.** On the family, the drift is `c(m+1)^{1−s} − 1`. -/
theorem drift_family (c s : ℝ) (m : ℕ) :
    epsCS c s m * ((m : ℝ) + 1) - 1 = c * ((m : ℝ) + 1) ^ (1 - s) - 1 := by
  have hb : (0 : ℝ) < (m : ℝ) + 1 := base_pos m
  have hs : ((m : ℝ) + 1) ^ (1 - s) = ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ s := by
    rw [rpow_sub hb, rpow_one]
  rw [epsCS, hs]
  field_simp

/-- The drift is **constant in `j`** at `s = 1`, where it equals `c − 1`. This is the identity
`ε_{c,1}(j)(j+1) − 1 = c − 1`, and it is what `lem:doubling_supersolution` consumes. -/
theorem drift_family_at_one {c : ℝ} (m : ℕ) :
    epsCS c 1 m * ((m : ℝ) + 1) - 1 = c - 1 := by
  have hb : (0 : ℝ) < (m : ℝ) + 1 := base_pos m
  rw [epsCS, rpow_one]
  field_simp

/-- Two evaluations of the base identity, used to run `prop:doubling_drift`'s "iff" backwards. -/
private theorem four_rpow (t : ℝ) : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
  rw [h4, ← rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- **The converse half of `prop:doubling_drift`.** If the drift does not depend on the ladder
state, then `s = 1`.

Two states suffice, and the proof exhibits them: the drift at `1` and at `3` are `c·2^{1−s}` and
`c·4^{1−s}`, and `2^{1−s} = 4^{1−s} = 2^{2(1−s)}` forces `1 − s = 2(1 − s)`. -/
theorem drift_const_iff {c s : ℝ} (hc : 0 < c)
    (hconst : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      c * ((i : ℝ) + 1) ^ (1 - s) - 1 = c * ((j : ℝ) + 1) ^ (1 - s) - 1) :
    s = 1 := by
  have h := hconst 1 3 (by norm_num) (by norm_num)
  norm_num at h
  have h2 : (2 : ℝ) ^ (1 - s) = (2 : ℝ) ^ (2 * (1 - s)) := by
    rw [← four_rpow]; exact h.resolve_right hc.ne'
  have hle : (1 : ℝ) - s ≤ 2 * (1 - s) := (rpow_le_rpow_left_iff (by norm_num)).mp h2.le
  have hge : 2 * ((1 : ℝ) - s) ≤ 1 - s := (rpow_le_rpow_left_iff (by norm_num)).mp h2.ge
  linarith

/-- The forward half: at `s = 1` the drift is the constant `c − 1`. -/
theorem drift_const_of_eq_one {c : ℝ} (i j : ℕ) :
    c * ((i : ℝ) + 1) ^ (1 - (1:ℝ)) - 1 = c * ((j : ℝ) + 1) ^ (1 - (1:ℝ)) - 1 := by
  norm_num

end GFNBounds.Doubling
