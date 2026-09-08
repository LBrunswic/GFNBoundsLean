import Mathlib

/-!
# The diffusion operator on a finite chain: invertibility and the resolvent identities

**`lem:doubling_operator`(2)** — `app_doubling.tex:166–262`.

> if moreover the chain is finite and irreducible then `P⋆` fixes only the constant functions, the
> operator `Id − P⋆ + Π` is invertible, and
> `S(Id − P⋆) = (Id − P⋆)S = Id − Π`, `ΠS = SΠ = 0`.

The paper's proof:

> An irreducible Markov kernel on a finite state space carries a unique invariant probability,
> positive at every state, so `λ` is that probability and `P⋆` fixes only the constant functions
> (Lemma `lem:doubling_fixed_points`). The space `L²(λ)` is finite-dimensional and `Id − P⋆ + Π` is
> injective on it: `λT = λ` gives `ΠP⋆ = Π` and `Π² = Π`, `λ` being a probability, so
> `(Id − P⋆ + Π)f = 0` forces `Πf = 0` and then `P⋆f = f`, whence `f` is a constant of zero mean,
> that is `0`. That operator is therefore invertible […]

Every step of that paragraph after the words "finite-dimensional" is **algebra**, and is proved
here in that generality — for a bounded operator `P` on any finite-dimensional normed space with
an idempotent `Pi` intertwining it — exactly as `Operator.lean` proves item (3) in a Banach
algebra. The three hypotheses used are `Pi² = Pi`, `Pi·P = Pi`, `P·Pi = Pi` (the last only for the
identities), and the conclusion of `lem:doubling_fixed_points` in the form

  `hker : ∀ f, P f = f → Pi f = f`

— "a fixed point of `P⋆` is a constant, and `Π` fixes the constants". On this graph `hker` is
`GFNBounds.Doubling.Stat.ker_eq_const` together with `Π1 = 1`.

## SCOPE (disclosed)

* **This is the algebra of item (2), not its instantiation.** What is *not* here is
  `FiniteDimensional ℝ (Lp ℝ 2 λ^K)` and the construction of `Π` as a `ContinuousLinearMap` on
  that space; both are in `AdjointL2.lean` / `OperatorL2.lean`, where `Stat.exists_diffusionOp`
  instantiates the theorem below and closes `lem:doubling_operator`(2): the first of its three
  clauses is `FixedPointsP.ker_eq_const`, the second and third are the theorem below at that
  instance.
* **Uniqueness of the invariant probability on a finite irreducible chain is not proved and not
  used.** The paper invokes it to identify `λ`; here `λ` is whatever `Stat` supplies, and the
  argument needs only that it is *an* invariant probability positive on the chain.
* **`Id − P + Pi` is inverted, not `Id − P`.** As in the paper: `Id − P` is singular, its kernel
  being the constants.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the chain is finite | ⚠ weakened to `FiniteDimensional ℝ E` |
| the chain is irreducible | ⚠ **replaced** by its consequence `hker`, which is what the proof uses |
| `Π` the `λ`-mean projection | ⚠ weakened to `Pi * Pi = Pi`, `Pi * P = Pi`, `P * Pi = Pi` |
| `L²(λ)` | ⚠ weakened to any finite-dimensional normed `ℝ`-space |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P Pi : E →L[ℝ] E}

/-- `Π(Id − P⋆ + Π) = Π`. -/
theorem pi_mul_resolventOp (hPi2 : Pi * Pi = Pi) (hPiP : Pi * P = Pi) :
    Pi * (1 - P + Pi) = Pi := by
  have h : Pi * (1 - P + Pi) = Pi - Pi * P + Pi * Pi := by noncomm_ring
  rw [h, hPiP, hPi2]; abel

/-- `(Id − P⋆ + Π)Π = Π`. -/
theorem resolventOp_mul_pi (hPi2 : Pi * Pi = Pi) (hPPi : P * Pi = Pi) :
    (1 - P + Pi) * Pi = Pi := by
  have h : (1 - P + Pi) * Pi = Pi - P * Pi + Pi * Pi := by noncomm_ring
  rw [h, hPPi, hPi2]; abel

/-- **`Id − P⋆ + Π` is injective.** `Πf = 0` follows by applying `Π`; then `P⋆f = f`, so `f` is a
constant of zero mean, that is `0`. -/
theorem resolventOp_injective (hPi2 : Pi * Pi = Pi) (hPiP : Pi * P = Pi)
    (hker : ∀ f : E, P f = f → Pi f = f) : Function.Injective (1 - P + Pi : E →L[ℝ] E) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hPiM := pi_mul_resolventOp hPi2 hPiP
  have hPif : Pi f = 0 := by
    have h1 : (Pi * (1 - P + Pi)) f = Pi ((1 - P + Pi) f) := rfl
    rw [hPiM, hf, map_zero] at h1
    exact h1
  have hPf : P f = f := by
    have h2 : (1 - P + Pi) f = f - P f + Pi f := by simp
    rw [h2, hPif, add_zero, sub_eq_zero] at hf
    exact hf.symm
  have := hker f hPf
  rw [hPif] at this
  exact this.symm

/-- **`eq:doubling_resolvent`, from a two-sided inverse.** Pure algebra: once `Id − P⋆ + Π` has an
inverse `R`, the identities of the paper follow from `ΠR = RΠ = Π` and
`Π(Id − P⋆) = (Id − P⋆)Π = 0`. -/
theorem resolvent_identities_of_inverse {R : E →L[ℝ] E} (hPi2 : Pi * Pi = Pi)
    (hPiP : Pi * P = Pi) (hPPi : P * Pi = Pi)
    (hMR : (1 - P + Pi) * R = 1) (hRM : R * (1 - P + Pi) = 1) :
    (1 - P) * (R - Pi) = 1 - Pi ∧ (R - Pi) * (1 - P) = 1 - Pi
      ∧ Pi * (R - Pi) = 0 ∧ (R - Pi) * Pi = 0 := by
  have hPiR : Pi * R = Pi := by
    have h : Pi * (1 - P + Pi) * R = Pi * R := by rw [pi_mul_resolventOp hPi2 hPiP]
    rw [mul_assoc, hMR, mul_one] at h
    exact h.symm
  have hRPi : R * Pi = Pi := by
    have h : R * ((1 - P + Pi) * Pi) = R * Pi := by rw [resolventOp_mul_pi hPi2 hPPi]
    rw [← mul_assoc, hRM, one_mul] at h
    exact h.symm
  have hzeroR : (1 - P) * Pi = 0 := by rw [sub_mul, one_mul, hPPi, sub_self]
  have hzeroL : Pi * (1 - P) = 0 := by rw [mul_sub, mul_one, hPiP, sub_self]
  have hsplitR : (1 - P + Pi) * R = (1 - P) * R + Pi * R := by noncomm_ring
  have hsplitL : R * (1 - P + Pi) = R * (1 - P) + R * Pi := by noncomm_ring
  have h1 : (1 - P) * R = 1 - Pi := by
    rw [hsplitR, hPiR] at hMR
    exact eq_sub_of_add_eq hMR
  have h2 : R * (1 - P) = 1 - Pi := by
    rw [hsplitL, hRPi] at hRM
    exact eq_sub_of_add_eq hRM
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_sub, hzeroR, sub_zero, h1]
  · rw [sub_mul, hzeroL, sub_zero, h2]
  · rw [mul_sub, hPiR, hPi2, sub_self]
  · rw [sub_mul, hRPi, hPi2, sub_self]

end Algebra

section Finite

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {P Pi : E →L[ℝ] E}

/-- **`Id − P⋆ + Π` is invertible** on a finite-dimensional space: it is injective, hence
surjective, and in finite dimensions the inverse is again bounded. -/
theorem exists_inverse (hPi2 : Pi * Pi = Pi) (hPiP : Pi * P = Pi)
    (hker : ∀ f : E, P f = f → Pi f = f) :
    ∃ R : E →L[ℝ] E, (1 - P + Pi) * R = 1 ∧ R * (1 - P + Pi) = 1 := by
  have hinj : Function.Injective ((1 - P + Pi : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
    resolventOp_injective hPi2 hPiP hker
  have hsurj : Function.Surjective ((1 - P + Pi : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
    LinearMap.injective_iff_surjective.mp hinj
  set eqv : E ≃ₗ[ℝ] E :=
    LinearEquiv.ofBijective ((1 - P + Pi : E →L[ℝ] E) : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩ with heqv
  have hfwd : ∀ x : E, eqv x = (1 - P + Pi : E →L[ℝ] E) x := fun _ => rfl
  refine ⟨LinearMap.toContinuousLinearMap (eqv.symm : E →ₗ[ℝ] E), ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    show (1 - P + Pi : E →L[ℝ] E) ((LinearMap.toContinuousLinearMap
      (eqv.symm : E →ₗ[ℝ] E)) x) = x
    rw [LinearMap.coe_toContinuousLinearMap']
    rw [← hfwd]
    exact eqv.apply_symm_apply x
  · refine ContinuousLinearMap.ext fun x => ?_
    show (LinearMap.toContinuousLinearMap (eqv.symm : E →ₗ[ℝ] E))
      ((1 - P + Pi : E →L[ℝ] E) x) = x
    rw [LinearMap.coe_toContinuousLinearMap', ← hfwd]
    exact eqv.symm_apply_apply x

/-- **`lem:doubling_operator`(2), the algebra.** On a finite-dimensional space, `Id − P⋆ + Π` is
invertible and the diffusion operator `S := (Id − P⋆ + Π)^{-1} − Π` satisfies
`eq:doubling_resolvent`. -/
theorem exists_resolvent (hPi2 : Pi * Pi = Pi) (hPiP : Pi * P = Pi) (hPPi : P * Pi = Pi)
    (hker : ∀ f : E, P f = f → Pi f = f) :
    ∃ R : E →L[ℝ] E, (1 - P + Pi) * R = 1 ∧ R * (1 - P + Pi) = 1
      ∧ (1 - P) * (R - Pi) = 1 - Pi ∧ (R - Pi) * (1 - P) = 1 - Pi
      ∧ Pi * (R - Pi) = 0 ∧ (R - Pi) * Pi = 0 := by
  obtain ⟨R, hMR, hRM⟩ := exists_inverse hPi2 hPiP hker
  obtain ⟨e1, e2, e3, e4⟩ := resolvent_identities_of_inverse hPi2 hPiP hPPi hMR hRM
  exact ⟨R, hMR, hRM, e1, e2, e3, e4⟩

end Finite

end GFNBounds.Doubling
