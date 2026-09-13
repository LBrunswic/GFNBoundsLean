import GFNBounds.Core.Mixing

/-!
# The base coefficient of the mixing sum: `β̂₀ = ‖I − Π‖ ≥ 1`, hence `B̂ ≥ 1`

**`lem:sigma_mixing`** — statement `proofs.tex:581–586`, proof `proofs.tex:588–590`
(Lemma 28 of the ICLR build). This file certifies a **hypothesis** of that lemma, not its
conclusion: the conclusion is closed in `GFNBounds/Core/Mixing.lean` (bucket `A`), whose
checklist records `β̂₀ = 1` as "not needed" for it. Downstream it *is* needed, and this file
supplies the half of it that downstream consumes.

> (`lem:sigma_mixing`, `proofs.tex:582`) Assume `B̂ := ∑_{n≥0} β̂_n < +∞` (summable `L²`-mixing,
> `β̂₀ = 1`). Then `S := ∑_{n≥0}(P^n − Π)` converges in operator norm, `S(I−P) = I − Π`, and
> consequently `∀ h ∈ L²(λ), ‖(I−P)h‖ ≥ ‖h − Πh‖ / B̂`.

## The debt this pays

`β̂₀ = ‖P⁰ − Π‖ = ‖I − Π‖`, so the parenthesis `β̂₀ = 1` in the hypothesis above is a
normalization the paper asserts and never uses again — except that it makes `B̂ = ∑_{n≥0} β̂_n`
at least `1`, and *that* the downstream files need. **The library never computes it.** Two of
them add `1 ≤ B̂` as a bare hypothesis at nine declaration sites — seven in
`GFNBounds/Balance/LocalConvergence.lean`, two in `GFNBounds/Balance/RatioBridge.lean` — and
disclose it (`LocalConvergence.lean:87`: "the paper has `β̂₀ = 1`, so `B̂ = ∑β̂_n ≥ 1` is true of
its `B̂`, but it is nowhere stated and `LocalEnergy` carries only `0 ≤ B̂`"). Two more take the
weaker `0 < B̂` at the mixing sum itself: `GFNBounds/Balance/Flow.lean:660`
(`inner_ge_of_mixing`) and `GFNBounds/Balance/WeightedL2.lean:616`
(`stable_frozen_discrete_mixing`). The analogous fact on the Morozov side is already *derived*
rather than assumed — `GFNBounds/Balance/TrainingSpeed.lean:216`'s `one_le_BhatSigma`.
`one_le_B` below is the missing mixing-side twin, and `B_pos` its `0 <` corollary.

## What is proved, and what is not

* **`beta_zero`** — `β₀ = ‖1 − Pi‖`, definitional.
* **`one_le_norm_of_isIdempotentElem`** — in any normed ring, a **non-zero idempotent has norm
  `≥ 1`**: `‖a‖ = ‖a·a‖ ≤ ‖a‖²`. Mathlib v4.31.0 has no such lemma (searched
  `Mathlib/Analysis/` for `one_le_norm` and for `IsIdempotentElem` together with `norm`; the
  only neighbours are `one_le_norm_one` for the unit of a nontrivial normed ring and
  `ContinuousLinearEquiv.one_le_norm_mul_norm_symm`), so it is proved here in the general form
  and used twice.
* **`one_le_beta_zero`, `one_le_B`, `B_pos`** — `1 ≤ β₀ ≤ B`, hence `0 < B`, for a
  `Mixing P Pi` given the side condition below. **This is the payoff.**
* **`Mixing.of_idem`, `Mixing.B_of_idem`** — an idempotent `Q` is its own mixing pair, and then
  `B̂ = ‖1 − Q‖`. General, and the machine for the two witnesses.
* **The numeric check.** `B_orthoPi`: `B̂ = 1` exactly for the coordinate projection of
  `ℝ × ℝ`, with `one_le_B_orthoPi` the payoff instantiated on it — so `one_le_B` is sharp and
  its hypotheses are satisfiable.
* **`β̂₀ = 1` itself is NOT proved, and is NOT provable from `Mixing`.** It needs
  `‖1 − Pi‖ ≤ 1`, which holds for an *orthogonal* projection and fails for a general
  idempotent; `Mixing` assumes neither orthogonality, nor self-adjointness, nor an inner
  product. `B_obliquePi` below is the counterexample: a `Mixing P Pi` on `ℝ × ℝ` with
  `β₀ = B̂ = 2`, and `not_forall_beta_zero_eq_one` states that refutation as such. So the
  paper's `β̂₀ = 1` is a genuine property of *its* `Π` — the mean projection of
  `proofs.tex:22`, orthogonal on `L²(λ)` — and not a consequence of summable
  mixing. What the equality would take is the missing upper bound `‖1 − Pi‖ ≤ 1`, and the
  cheapest Mathlib route to it is `IsStarProjection.norm_le`
  (`Mathlib/Analysis/CStarAlgebra/Basic.lean:265`, `‖e‖ ≤ 1` for a self-adjoint idempotent of a
  C*-ring) applied to `1 − Pi` — which needs a star structure and `Pi` self-adjoint, i.e.
  exactly the orthogonality `Mixing` declines to assume. The inequality is all any consumer
  needs, so the file stops there.

## The side condition, and whether the paper presupposes it

`1 ≤ ‖1 − Pi‖` is **false when `Pi = 1`**: then `1 − Pi = 0`, `β_n = 0` for every `n`, and
`B = 0`. So the side condition `hQ : (1 : E →L[ℝ] E) − Pi ≠ 0` is genuine, and
`one_sub_ne_zero_iff` reads it as `∃ x, Pi x ≠ x` — *`Π` is not everything*, i.e. some vector
is not invariant.

The paper's `β̂₀ = 1` presupposes it **silently and correctly**. `Π` there is the mean
projection `Πf = (∫f dλ) 1` onto the constants of `L²(λ)` (`proofs.tex:22`, `:589`); `Π = I`
would say every `L²(λ)` function is constant, i.e. `λ` is a point mass and the state space a
single state. Every setting the lemma is invoked in — `theo:db_stable_frozen_full`,
`theo:local_convergence`, `theo:global_dichotomy` — has a graph with at least one edge, so the
condition holds and the paper is entitled to it. It is recorded here rather than dropped
because the abstract `Mixing` bundle does not contain it: `Pi = P = 1` satisfies `Mixing`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `B̂ := ∑_{n≥0} β̂_n < +∞` | ✓ carried, as `Mixing.summable` |
| `β̂_n = ‖P^n − Π‖` on `L²(λ)` | ⚠ weakened: any real Banach space, any bounded `P`, `Pi` — inherited from `Core/Mixing.lean`'s own generalization |
| `β̂₀ = 1` | ⚠ **half of it**: `1 ≤ β̂₀` is proved (`one_le_beta_zero`), the equality is refuted at this generality (`B_obliquePi`, `not_forall_beta_zero_eq_one`). See SCOPE |
| (silent) `Π ≠ I` | ⚠ **made explicit** as `hQ`, and shown necessary |
| `S` converges, `S(I−P) = I−Π`, the coercivity | ✗ not restated — `GFNBounds.Core.Mixing` has them, closed |

## SCOPE (disclosed)

1. **Inequality, not equality.** `one_le_B` gives `1 ≤ B̂`, which is what
   `LocalConvergence.lean` and `RatioBridge.lean` consume, and `B_pos` the `0 < B̂` that
   `Flow.lean` and `WeightedL2.lean` consume. `β̂₀ = 1` exactly is not proved and, at the
   generality of `Mixing`, is false — see `B_obliquePi`. Recovering
   it would mean adding `Pi` self-adjoint on an inner-product space, which changes the
   hypothesis bundle of a *closed* file for no consumer's benefit.
2. **Nothing downstream is rewired.** `GFNBounds/Balance/WeightedL2.lean`'s
   `stable_frozen_discrete_mixing` takes `Bhat := Core.Mixing.B (densOp lam K) (meanOp lam)`
   with a hypothesis `hBpos : 0 < Bhat`; `B_pos` discharges exactly that, from
   `Core.Mixing (densOp lam K) (meanOp lam)` plus `1 − meanOp lam ≠ 0`. So does
   `Flow.lean:660`'s `hB`. The nine `hB1 : 1 ≤ Bhat` sites take an *abstract* `Bhat` alongside
   the finite coercivity `hcoer`, not `Core.Mixing`, so `one_le_B` supplies their hypothesis
   only once their `Bhat` is instantiated at the mixing sum. **No file outside this one is
   edited**, and no discharge is performed: that is the master session's call and belongs with
   the graduation of this file.
3. **`Mixing (densOp lam K) (meanOp lam)` is still never exhibited**, exactly as
   `WeightedL2.lean:112` says. This file adds a consequence of the bundle, not an instance of
   it. The two witnesses below are toys, present for non-vacuity only.
4. **Scaffold placement is not a `sorry`.Graduated into the strict library on 2026-09-13.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

/-! ### A non-zero idempotent of a normed ring has norm at least one

`‖a‖ = ‖a·a‖ ≤ ‖a‖·‖a‖`, and `‖a‖ > 0`. Not in Mathlib v4.31.0; stated for a general normed
ring because both uses below are at `E →L[ℝ] E`, and one of them is `1 - Pi` rather than `Pi`. -/

theorem one_le_norm_of_isIdempotentElem {R : Type*} [NormedRing R] {a : R}
    (ha : IsIdempotentElem a) (h0 : a ≠ 0) : 1 ≤ ‖a‖ := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr h0
  have hsub : ‖a‖ ≤ ‖a‖ * ‖a‖ := by
    have := norm_mul_le a a
    rwa [ha.eq] at this
  nlinarith

namespace Mixing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P Pi : E →L[ℝ] E}

/-! ### The base coefficient -/

/-- `β₀ = ‖I − Π‖`: the paper's `β̂₀`, unfolded. `P ^ 0 = 1`. -/
theorem beta_zero (P Pi : E →L[ℝ] E) : beta P Pi 0 = ‖(1 : E →L[ℝ] E) - Pi‖ := by
  rw [beta, pow_zero]

/-- The side condition, read on vectors: `I − Π ≠ 0` says exactly that some vector is not
`Π`-invariant. -/
theorem one_sub_ne_zero_iff : (1 : E →L[ℝ] E) - Pi ≠ 0 ↔ ∃ x, Pi x ≠ x := by
  -- `Pi` shadows Mathlib's `Pi` namespace, so the pointwise `simp` lemmas are unusable by
  -- name here (see `Core/Mixing.lean`'s "notation clash"); both directions go through `rfl`.
  have key : ∀ x : E, ((1 : E →L[ℝ] E) - Pi) x = x - Pi x := fun _ => rfl
  constructor
  · intro h
    by_contra hc
    push Not at hc
    refine h (ContinuousLinearMap.ext fun x => ?_)
    rw [key x, hc x, sub_self]
    rfl
  · rintro ⟨x, hx⟩ h
    refine hx ?_
    have hx0 : ((1 : E →L[ℝ] E) - Pi) x = 0 := by rw [h]; rfl
    rw [key x, sub_eq_zero] at hx0
    exact hx0.symm

/-- **`1 ≤ ‖I − Π‖`** whenever `Π` is an idempotent short of the identity. This is the cheap
half of the paper's `β̂₀ = 1`; the other half needs `‖I − Π‖ ≤ 1`, which is orthogonality. -/
theorem one_le_norm_one_sub_proj (hPi : Pi * Pi = Pi) (hQ : (1 : E →L[ℝ] E) - Pi ≠ 0) :
    1 ≤ ‖(1 : E →L[ℝ] E) - Pi‖ :=
  one_le_norm_of_isIdempotentElem (IsIdempotentElem.one_sub hPi) hQ

/-- **`1 ≤ β̂₀`** for a summably mixing pair: `Mixing.proj_idem` supplies the idempotence,
`hQ` the non-degeneracy. -/
theorem one_le_beta_zero [CompleteSpace E] (h : Mixing P Pi)
    (hQ : (1 : E →L[ℝ] E) - Pi ≠ 0) : 1 ≤ beta P Pi 0 := by
  rw [beta_zero]
  exact one_le_norm_one_sub_proj h.proj_idem hQ

/-- **`1 ≤ B̂`** — the hypothesis `LocalConvergence.lean`, `RatioBridge.lean` and
`WeightedL2.lean` each carry as `hB1`, here derived from `Mixing` and `Π ≠ I`.

`B̂ = ∑_{n≥0} β̂_n ≥ β̂₀ ≥ 1`, the first step by non-negativity of the remaining terms. -/
theorem one_le_B [CompleteSpace E] (h : Mixing P Pi)
    (hQ : (1 : E →L[ℝ] E) - Pi ≠ 0) : 1 ≤ B P Pi :=
  le_trans (h.one_le_beta_zero hQ)
    (h.summable_beta.le_tsum 0 fun n _ => beta_nonneg P Pi n)

/-- `0 < B̂`, the form `coercivity_div` and every `ϱ := c/B̂²` consume. -/
theorem B_pos [CompleteSpace E] (h : Mixing P Pi)
    (hQ : (1 : E →L[ℝ] E) - Pi ≠ 0) : 0 < B P Pi :=
  lt_of_lt_of_le zero_lt_one (h.one_le_B hQ)

/-! ### The degenerate mixing pair `P = Pi` idempotent

Used only to build the witnesses below, but true in general: an idempotent mixes in one step,
`Q ^ n - Q = 0` for `n ≥ 1`, and the whole mixing sum is its base coefficient. -/

/-- An idempotent operator is its own mixing pair. -/
theorem of_idem {Q : E →L[ℝ] E} (hQ : Q * Q = Q) : Mixing Q Q where
  proj_left := hQ
  proj_right := hQ
  summable := by
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) ?_
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [IsIdempotentElem.pow_succ_eq k hQ, sub_self, norm_zero]

/-- For an idempotent `Q`, the mixing sum collapses to its base coefficient `‖1 - Q‖`. -/
theorem B_of_idem {Q : E →L[ℝ] E} (hQ : Q * Q = Q) : B Q Q = ‖(1 : E →L[ℝ] E) - Q‖ := by
  rw [B, ← beta_zero Q Q]
  refine tsum_eq_single 0 ?_
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [beta, IsIdempotentElem.pow_succ_eq k hQ, sub_self, norm_zero]

end Mixing

/-! ### Non-vacuity, computed

Two witnesses on `E = ℝ × ℝ`, whose norm is `‖(a,b)‖ = max ‖a‖ ‖b‖`. Both take `P = Pi`
idempotent, so `P ^ n − Pi = 0` for `n ≥ 1` and `B` collapses to `β₀ = ‖1 − Pi‖`.

* `orthoPi (a,b) = (a,0)` — the coordinate projection. `B = 1` **exactly**: the paper's
  normalization is attained, and `one_le_B` is sharp.
* `obliquePi (a,b) = (−b,b)` — an idempotent that is not orthogonal. `B = 2`: `β̂₀ = 1` is not
  a consequence of `Mixing`. -/

section Witness

open ContinuousLinearMap

/-- The coordinate projection `(a,b) ↦ (a,0)` on `ℝ × ℝ`. -/
def orthoPi : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (inl ℝ ℝ ℝ).comp (fst ℝ ℝ ℝ)

@[simp] theorem orthoPi_apply (x : ℝ × ℝ) : orthoPi x = (x.1, 0) := rfl

theorem orthoPi_idem : orthoPi * orthoPi = orthoPi := by ext <;> rfl

/-- `1 − orthoPi` is the complementary coordinate projection, of norm exactly `1`. -/
theorem norm_one_sub_orthoPi : ‖(1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - orthoPi‖ = 1 := by
  have happ : ∀ x : ℝ × ℝ, ((1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - orthoPi) x = (0, x.2) := by
    intro x
    ext <;> simp
  refine le_antisymm (opNorm_le_bound _ zero_le_one fun x => ?_) ?_
  · rw [happ x, one_mul]
    calc ‖((0 : ℝ), x.2)‖ = ‖x.2‖ := by simp [Prod.norm_def]
      _ ≤ ‖x‖ := norm_snd_le x
  · refine Mixing.one_le_norm_one_sub_proj orthoPi_idem ?_
    intro h
    have := congrArg (fun T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => T (0, 1)) h
    rw [happ] at this
    simp at this

/-- The oblique idempotent `(a,b) ↦ (−b,b)`. Its complement is `(a,b) ↦ (a+b,0)`. -/
def obliquePi : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((inl ℝ ℝ ℝ).comp (-(snd ℝ ℝ ℝ))) + ((inr ℝ ℝ ℝ).comp (snd ℝ ℝ ℝ))

@[simp] theorem obliquePi_apply (x : ℝ × ℝ) : obliquePi x = (-x.2, x.2) := by
  simp [obliquePi]

theorem obliquePi_idem : obliquePi * obliquePi = obliquePi := by
  ext <;> simp

/-- `‖1 − obliquePi‖ = 2`: the complement `(a,b) ↦ (a+b,0)` doubles `(1,1)`. Hence a `Mixing`
pair with `β̂₀ = 2`, and the paper's `β̂₀ = 1` is not implied by summable mixing. -/
theorem norm_one_sub_obliquePi : ‖(1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - obliquePi‖ = 2 := by
  have happ : ∀ x : ℝ × ℝ, ((1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - obliquePi) x = (x.1 + x.2, 0) := by
    intro x
    ext <;> simp
  refine le_antisymm (opNorm_le_bound _ zero_le_two fun x => ?_) ?_
  · rw [happ x]
    have h1 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
    have h2 : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
    have habs : |x.1 + x.2| ≤ |x.1| + |x.2| := abs_add_le _ _
    calc ‖(x.1 + x.2, (0 : ℝ))‖ = |x.1 + x.2| := by simp [Prod.norm_def, Real.norm_eq_abs]
      _ ≤ |x.1| + |x.2| := habs
      _ ≤ 2 * ‖x‖ := by
          simp only [Real.norm_eq_abs] at h1 h2
          linarith
  · have hx : ((1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - obliquePi) (1, 1) = (2, 0) := by
      rw [happ]; norm_num
    have hle := ((1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - obliquePi).le_opNorm ((1 : ℝ), (1 : ℝ))
    rw [hx] at hle
    have h2 : ‖((2 : ℝ), (0 : ℝ))‖ = 2 := by simp [Prod.norm_def]
    have h1 : ‖((1 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    rw [h2, h1, mul_one] at hle
    exact hle

/-! #### The two `Mixing` instances, and their `B` -/

/-- `Mixing orthoPi orthoPi` holds: the hypothesis bundle is non-vacuous. -/
theorem orthoMixing : Mixing orthoPi orthoPi := Mixing.of_idem orthoPi_idem

/-- The side condition holds for `orthoPi`: `orthoPi ≠ 1`, i.e. `(0,1)` is not invariant. -/
theorem one_sub_orthoPi_ne_zero : (1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - orthoPi ≠ 0 := by
  intro h
  have hz : ‖(1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - orthoPi‖ = 0 := by rw [h, norm_zero]
  rw [norm_one_sub_orthoPi] at hz
  norm_num at hz

/-- **The numeric check.** `Mixing orthoPi orthoPi` holds, `orthoPi ≠ 1`, and `B̂ = 1`
*exactly* — the paper's normalization, attained. So `one_le_B` is sharp and not vacuous. -/
theorem B_orthoPi : Mixing.B orthoPi orthoPi = 1 := by
  rw [Mixing.B_of_idem orthoPi_idem, norm_one_sub_orthoPi]

/-- `one_le_B` evaluated on that witness: `1 ≤ B̂` with `B̂ = 1`. -/
theorem one_le_B_orthoPi : (1 : ℝ) ≤ Mixing.B orthoPi orthoPi :=
  orthoMixing.one_le_B one_sub_orthoPi_ne_zero

/-- `Mixing obliquePi obliquePi` holds too, and `obliquePi ≠ 1`. -/
theorem obliqueMixing : Mixing obliquePi obliquePi := Mixing.of_idem obliquePi_idem

/-- **The counterexample to the equality.** `B̂ = β̂₀ = 2` on a legitimate `Mixing` pair. So
`β̂₀ = 1` is a property of the paper's *orthogonal* mean projection, not a consequence of
summable mixing, and this file stops at `1 ≤ B̂`. -/
theorem B_obliquePi : Mixing.B obliquePi obliquePi = 2 := by
  rw [Mixing.B_of_idem obliquePi_idem, norm_one_sub_obliquePi]

/-- Restated as the refutation it is: summable mixing with `Π ≠ I` does **not** force
`β̂₀ = 1`. -/
theorem not_forall_beta_zero_eq_one :
    ¬ ∀ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E) (P Pi : E →L[ℝ] E),
        Mixing P Pi → (1 : E →L[ℝ] E) - Pi ≠ 0 → Mixing.beta P Pi 0 = 1 := by
  intro h
  have hne : (1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - obliquePi ≠ 0 := by
    intro hz
    have : ‖(1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) - obliquePi‖ = 0 := by rw [hz, norm_zero]
    rw [norm_one_sub_obliquePi] at this
    norm_num at this
  have := h (ℝ × ℝ) inferInstance inferInstance obliquePi obliquePi obliqueMixing hne
  rw [Mixing.beta_zero, norm_one_sub_obliquePi] at this
  norm_num at this

end Witness

end GFNBounds.Core
