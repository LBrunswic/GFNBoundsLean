import Mathlib

/-!
# The diffusion operator: the resolvent identities

**`lem:doubling_operator`(3)** — `app_doubling.tex:166–262`.

> if `U := Σ_{n≥0}(P⋆^n − Π)` converges in operator norm on `L²(λ)`, then `Id − P⋆ + Π` is
> invertible with inverse `Π + U`, the operator `S` equals `U` and satisfies
> `eq:doubling_resolvent`, and `B̂ ≤ Σ_{n≥0} β̂_n`.

## SCOPE (disclosed)

**Item (3) only, and stated abstractly.** Its proof is pure operator algebra in a Banach algebra:
the only properties of `Π` it uses are `Π² = Π`, `ΠP⋆ = Π` and `P⋆Π = Π`, and the only property
of the space is completeness. So it is proved here for an arbitrary bounded operator `P` on a
Banach space with an idempotent `Pi` satisfying those two intertwining relations — which is
strictly more general than the paper's statement and needs no measure theory at all.

**Items (1) and (2) are not here.** Item (1) — `P⋆` a contraction of every `L^p(λ)` and the
`L²`-adjoint of the density action — is the one place the `Lp` layer is unavoidable, and the
density action `P` is not modelled in this library; the `p = ∞` case of the contraction is
`pstar_bounded` in `Setting.lean`, which is all the `tsum` estimates need. Item (2) is the
finite-dimensional case, which needs `lem:doubling_fixed_points` in its `L²` form and the
existence of `λ^K`; both are open.

`rem:doubling_two_constants` is the observation that `resolvent_norm_le` orders two numerically
distinct constants; it carries no further mathematics and is not formalized separately.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Π` the `λ`-mean projection | ⚠ weakened to `Pi² = Pi`, `Pi * P = Pi`, `P * Pi = Pi` |
| `L²(λ)` | ⚠ weakened to any Banach space over `ℝ` |
| the series converges in operator norm | ✓ carried (`hconv`) |
| `B̂ ≤ Σ β̂_n` | ✓ carried (`resolvent_norm_le`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Resolvent

variable {P Pi U : E →L[ℝ] E}

/-- `Π P⋆^n = Π` for every `n`. -/
theorem pi_mul_pow (hPiP : Pi * P = Pi) : ∀ n : ℕ, Pi * P ^ n = Pi := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, hPiP]

/-- `P⋆^n Π = Π` for every `n`. -/
theorem pow_mul_pi (hPPi : P * Pi = Pi) : ∀ n : ℕ, P ^ n * Pi = Pi := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, hPPi, ih]

/-- The partial sums of `Σ (P⋆^n − Π)`. -/
noncomputable def partialSum (P Pi : E →L[ℝ] E) (N : ℕ) : E →L[ℝ] E := ∑ n ∈ Finset.range N, (P ^ n - Pi)

/-- **The telescoping identity, on the left.** `(Id − P⋆) S_N = Id − P⋆^N`. -/
theorem one_sub_mul_partialSum (hPPi : P * Pi = Pi) (N : ℕ) :
    (1 - P) * partialSum P Pi N = 1 - P ^ N := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      have hstep : partialSum P Pi (N + 1) = partialSum P Pi N + (P ^ N - Pi) := by
        rw [partialSum, Finset.sum_range_succ, ← partialSum]
      have h0 : (1 - P) * Pi = 0 := by rw [sub_mul, one_mul, hPPi, sub_self]
      have h1 : (1 - P) * (P ^ N - Pi) = P ^ N - P ^ (N + 1) := by
        rw [mul_sub, h0, sub_zero, sub_mul, one_mul, pow_succ']
      rw [hstep, mul_add, ih, h1]
      abel

/-- **The telescoping identity, on the right.** `S_N (Id − P⋆) = Id − P⋆^N`. -/
theorem partialSum_mul_one_sub (hPiP : Pi * P = Pi) (N : ℕ) :
    partialSum P Pi N * (1 - P) = 1 - P ^ N := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      have hstep : partialSum P Pi (N + 1) = partialSum P Pi N + (P ^ N - Pi) := by
        rw [partialSum, Finset.sum_range_succ, ← partialSum]
      have h0 : Pi * (1 - P) = 0 := by rw [mul_sub, mul_one, hPiP, sub_self]
      have h1 : (P ^ N - Pi) * (1 - P) = P ^ N - P ^ (N + 1) := by
        rw [sub_mul, h0, sub_zero, mul_sub, mul_one, pow_succ]
      rw [hstep, add_mul, ih, h1]
      abel

/-- `Π S_N = 0`: every term of the series is killed by `Π` on the left. -/
theorem pi_mul_partialSum (hPi2 : Pi * Pi = Pi) (hPiP : Pi * P = Pi) (N : ℕ) :
    Pi * partialSum P Pi N = 0 := by
  rw [partialSum, Finset.mul_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [mul_sub, pi_mul_pow hPiP n, hPi2, sub_self]

/-- `S_N Π = 0`. -/
theorem partialSum_mul_pi (hPi2 : Pi * Pi = Pi) (hPPi : P * Pi = Pi) (N : ℕ) :
    partialSum P Pi N * Pi = 0 := by
  rw [partialSum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [sub_mul, pow_mul_pi hPPi n, hPi2, sub_self]

/-- Convergence of the series makes `P⋆^N → Π`: the general term goes to zero. -/
theorem tendsto_pow (hconv : Tendsto (partialSum P Pi) atTop (𝓝 U)) :
    Tendsto (fun N : ℕ => P ^ N) atTop (𝓝 Pi) := by
  have hshift : Tendsto (fun N : ℕ => partialSum P Pi (N + 1)) atTop (𝓝 U) :=
    hconv.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun N : ℕ => partialSum P Pi (N + 1) - partialSum P Pi N) atTop (𝓝 0) := by
    simpa using hshift.sub hconv
  have hterm : ∀ N : ℕ, partialSum P Pi (N + 1) - partialSum P Pi N = P ^ N - Pi := by
    intro N; rw [partialSum, partialSum, Finset.sum_range_succ]; abel
  have h0 : Tendsto (fun N : ℕ => P ^ N - Pi) atTop (𝓝 0) := by
    simpa [hterm] using hdiff
  have hconst : Tendsto (fun _ : ℕ => Pi) atTop (𝓝 Pi) := tendsto_const_nhds
  simpa using h0.add hconst

/-- **`eq:doubling_resolvent`, both halves.** -/
theorem resolvent_identities (hPi2 : Pi * Pi = Pi) (hPiP : Pi * P = Pi) (hPPi : P * Pi = Pi)
    (hconv : Tendsto (partialSum P Pi) atTop (𝓝 U)) :
    (1 - P) * U = 1 - Pi ∧ U * (1 - P) = 1 - Pi ∧ Pi * U = 0 ∧ U * Pi = 0 := by
  have hpow := tendsto_pow hconv
  have h1 : Tendsto (fun N : ℕ => (1 - P) * partialSum P Pi N) atTop (𝓝 ((1 - P) * U)) :=
    hconv.const_mul _
  have hconst1 : Tendsto (fun _ : ℕ => (1 : E →L[ℝ] E)) atTop (𝓝 1) := tendsto_const_nhds
  have h1' : Tendsto (fun N : ℕ => (1 : E →L[ℝ] E) - P ^ N) atTop (𝓝 (1 - Pi)) :=
    hconst1.sub hpow
  have h2 : Tendsto (fun N : ℕ => partialSum P Pi N * (1 - P)) atTop (𝓝 (U * (1 - P))) :=
    hconv.mul_const _
  have h3 : Tendsto (fun N : ℕ => Pi * partialSum P Pi N) atTop (𝓝 (Pi * U)) :=
    hconv.const_mul _
  have h4 : Tendsto (fun N : ℕ => partialSum P Pi N * Pi) atTop (𝓝 (U * Pi)) :=
    hconv.mul_const _
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine tendsto_nhds_unique ?_ h1'
    exact h1.congr fun N => (one_sub_mul_partialSum hPPi N)
  · refine tendsto_nhds_unique ?_ h1'
    exact h2.congr fun N => (partialSum_mul_one_sub hPiP N)
  · have hzero : Tendsto (fun _ : ℕ => (0 : E →L[ℝ] E)) atTop (𝓝 0) := tendsto_const_nhds
    refine tendsto_nhds_unique ?_ hzero
    exact h3.congr fun N => (pi_mul_partialSum hPi2 hPiP N)
  · have hzero : Tendsto (fun _ : ℕ => (0 : E →L[ℝ] E)) atTop (𝓝 0) := tendsto_const_nhds
    refine tendsto_nhds_unique ?_ hzero
    exact h4.congr fun N => (partialSum_mul_pi hPi2 hPPi N)

/-- **`lem:doubling_operator`(3).** `Id − P⋆ + Π` is invertible with inverse `Π + U`, so the
diffusion operator `S = (Id − P⋆ + Π)^{-1} − Π` is `U`. -/
theorem resolvent_inverse (hPi2 : Pi * Pi = Pi) (hPiP : Pi * P = Pi) (hPPi : P * Pi = Pi)
    (hconv : Tendsto (partialSum P Pi) atTop (𝓝 U)) :
    (1 - P + Pi) * (Pi + U) = 1 ∧ (Pi + U) * (1 - P + Pi) = 1 := by
  obtain ⟨e1, e2, e3, e4⟩ := resolvent_identities hPi2 hPiP hPPi hconv
  constructor
  · have hexp : (1 - P + Pi) * (Pi + U)
        = (Pi - P * Pi + Pi * Pi) + ((1 - P) * U + Pi * U) := by noncomm_ring
    rw [hexp, hPPi, hPi2, e1, e3]
    abel
  · have hexp : (Pi + U) * (1 - P + Pi)
        = (Pi - Pi * P + Pi * Pi) + (U * (1 - P) + U * Pi) := by noncomm_ring
    rw [hexp, hPiP, hPi2, e2, e4]
    abel

/-- **`B̂ ≤ Σ_{n≥0} β̂_n`.** The norm of the diffusion operator is at most the mixing sum: the two
constants written `B̂` in the appendix (`rem:doubling_two_constants`) are ordered, in this
direction and not the other. -/
theorem resolvent_norm_le {B : ℝ} (hconv : Tendsto (partialSum P Pi) atTop (𝓝 U))
    (hB : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖P ^ n - Pi‖ ≤ B) : ‖U‖ ≤ B := by
  have hnorm : Tendsto (fun N : ℕ => ‖partialSum P Pi N‖) atTop (𝓝 ‖U‖) :=
    hconv.norm
  refine le_of_tendsto hnorm (Filter.Eventually.of_forall fun N => ?_)
  exact le_trans (norm_sum_le _ _) (hB N)

end Resolvent

end GFNBounds.Doubling
