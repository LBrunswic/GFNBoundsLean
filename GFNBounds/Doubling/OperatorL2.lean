import GFNBounds.Doubling.AdjointL2
import GFNBounds.Doubling.OperatorFinite

/-!
# The diffusion operator of the truncation, and `B̂_K < +∞`

**`lem:doubling_operator`(2) instantiated, which is `lem:doubling_truncation_irreducible` Step 4**
— `app_doubling.tex:166–262` and `app_doubling.tex:1805–1846`.

> (`lem:doubling_operator`(2)) if moreover the chain is finite and irreducible then `P⋆` fixes only
> the constant functions, the operator `Id − P⋆ + Π` is invertible, and
> `S(Id − P⋆) = (Id − P⋆)S = Id − Π`, `ΠS = SΠ = 0`.
>
> (`lem:doubling_truncation_irreducible`, Step 4) Lemma `lem:doubling_operator`(2), applied to that
> chain, gives `S` and `eq:doubling_resolvent`; `S` acts on the finite-dimensional space
> `L²(λ^K)`, so `B̂_K = ‖S‖_{L²(λ^K)} < +∞`.

## What was missing, and what this file supplies

`OperatorFinite.lean` proved the **algebra** of item (2) for a bounded operator `P` on any
finite-dimensional normed space with an idempotent `Pi` satisfying `Pi·Pi = Pi`, `Pi·P = Pi`,
`P·Pi = Pi` and `hker : ∀ f, P f = f → Pi f = f`, and disclosed in SCOPE that the instantiation was
missing two things: the construction of `Π` on `Lp ℝ 2 λ^K`, and
`FiniteDimensional ℝ (Lp ℝ 2 λ^K)`. `AdjointL2.lean` supplied the first (`Stat.piL2`, with its
three intertwining identities). This file supplies the second and closes the instantiation.

* `Stat.evalChain` evaluates a class at the states of the chain. On the truncation that is a
  **finite** set (`{s₀, 1, …, K, s_f}`, `finite_onChain`), evaluation is linear because a.e.
  equality is equality on the chain (`Stat.ae_iff_eq`), and it is injective for the same reason —
  so `Lp ℝ 2 λ^K` is finite-dimensional. No basis is exhibited and none is needed.
* `Stat.piL2_fixed_of_pstarL2_fixed` is `hker`, from `lem:doubling_fixed_points` in its `L²` form
  (`Stat.fixed_const_memLp`, `LpLayer.lean`): a fixed point of `P⋆` is a constant class, and `Π`
  fixes the constants.
* `Stat.exists_diffusionOp` is `lem:doubling_operator`(2) on the truncation, and
  `Stat.exists_bhat` reads it as Step 4: **`B̂_K` exists as a real number**, with the Rayleigh
  inequality `‖F − ΠF‖ ≤ B̂_K‖(Id − P⋆)F‖` that `cor:doubling_truncation` Step 3 consumes.

## SCOPE (disclosed)

* **`RowOnChain S (some K)` is carried**, which on the truncation is `d ≤ K` — a hypothesis
  `lem:doubling_truncation_irreducible` makes itself ("let `K ≥ d` be an even integer"). Evenness
  of `K` is **not** used here: it enters the paper's Steps 1–3, which are `Irreducible.lean`.
* **Irreducibility is not re-proved and is not used in this form.** The paper reaches `hker`
  through "an irreducible chain carries a unique invariant probability, positive at every state,
  so `λ` is that one, so `P⋆` fixes only the constants". Here `λ` is whatever `Stat S (some K)`
  supplies — the existence and uniqueness of `λ^K` are `TruncationStat.lean` — and `hker` comes
  from `Stat.fixed_const_memLp`, whose proof climbs the ladder by the decrement alone. Nothing is
  lost: `Stat.exists_diffusionOp` holds at *every* invariant probability of the truncation.
* **`B̂_K` is `‖S‖` for the `S` produced here**, and `S` is produced from *an* inverse of
  `Id − P⋆ + Π`; uniqueness of the inverse is standard but is not stated, so `Stat.exists_bhat` is
  an `∃` over the pair `(S, B̂_K)`. The paper's `B̂_K` is the same number.
* **This closes Step 4 of `lem:doubling_truncation_irreducible` and Step 1 of
  `cor:doubling_truncation`, not more.** In particular `Truncation.lean` continues to state items
  (1) and (3) of `cor:doubling_truncation` about *any* `B` bounding the `L²(λ^K)` Rayleigh
  quotient; feeding the `B̂_K` built here into those statements needs the identification of
  `Stat.mass` with the `Lp` norm applied to the test function `f_m` of `lem:doubling_percut`,
  which is not done here.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ε(j) ∈ (0,1)` for every `j ≥ 1` | ✓ carried by `Setting` |
| `K ≥ d` | ✓ carried as `RowOnChain S (some K)` |
| `K` even | ⚠ **not used** — it is Steps 1–3, not Step 4 |
| the truncation is irreducible | ⚠ **replaced** by its consequence `hker`, proved directly |
| `λ^K` the unique invariant probability, positive | ⚠ **weakened**: any `Stat S (some K)` |
| `L²(λ^K)` is finite-dimensional | ✓ **proved** (`Stat.evalChain_injective`) |
| `lem:doubling_operator`(2) | ✓ carried (`OperatorFinite.exists_resolvent`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

variable {S : Setting} {cap : Option ℕ}

/-- **The chain of the truncation at `K` is finite**: it is the `K + 2` states
`{s₀, 1, …, K, s_f}` of `lem:doubling_truncation_irreducible`, injected here into
`Option (Fin (K+1))`. -/
instance finite_onChain (K : ℕ) : Finite {x : St // OnChain (some K) x} := by
  refine Finite.of_injective (fun x => (match x with
    | ⟨.lad j, hj⟩ => some (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (K + 1))
    | ⟨.sink, _⟩ => none) : {x : St // OnChain (some K) x} → Option (Fin (K + 1))) ?_
  rintro ⟨(a | _), ha⟩ ⟨(b | _), hb⟩ h <;> simp_all

namespace Stat

/-! ## 1. `hker`: a fixed point of `P⋆` is fixed by `Π` -/

section AnyCap

variable (L : Stat S cap)

/-- A fixed point of `P⋆` in `L²(λ)` is a constant class — `lem:doubling_fixed_points`' `P⋆` half
(`Stat.fixed_const_memLp`), transported to `Lp` at an arbitrary cap. -/
theorem eq_smul_oneLp_of_pstarL2_fixed (hrow : RowOnChain S cap) {F : Lp ℝ 2 L.mu}
    (hF : L.pstarL2 hrow F = F) : F = (F : St → ℝ) (.lad 0) • L.oneLp := by
  have hstar : pstar S cap ⇑F =ᵐ[L.mu] ⇑F :=
    (L.coeFn_pstarL2 hrow F).symm.trans (by rw [hF] : ⇑(L.pstarL2 hrow F) =ᵐ[L.mu] ⇑F)
  have hconst := L.fixed_const_memLp (Lp.memLp F) (L.ae_iff_eq.mp hstar)
  refine Lp.ext ?_
  filter_upwards [L.ae_eq_of_onChain hconst,
    Lp.coeFn_smul ((F : St → ℝ) (.lad 0)) L.oneLp, L.coeFn_oneLp] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]

/-- **`hker`**: `P⋆f = f` forces `Πf = f`. This is the hypothesis
`OperatorFinite.exists_resolvent` consumes in place of irreducibility. -/
theorem piL2_fixed_of_pstarL2_fixed (hrow : RowOnChain S cap) {F : Lp ℝ 2 L.mu}
    (hF : L.pstarL2 hrow F = F) : L.piL2 F = F := by
  have h := L.eq_smul_oneLp_of_pstarL2_fixed hrow hF
  rw [piL2_apply, h, real_inner_smul_right, L.inner_oneLp_self, mul_one]

end AnyCap

/-! ## 2. `L²(λ^K)` is finite-dimensional -/

section Truncation

variable {K : ℕ} (L : Stat S (some K))

/-- **Evaluation at the states of the chain**, as a linear map into a finite product. It is linear
because a.e. equality is equality on the chain (`Stat.ae_iff_eq`), so the representative of a sum
*is* the sum of the representatives there. -/
noncomputable def evalChain :
    Lp ℝ 2 L.mu →ₗ[ℝ] ({x : St // OnChain (some K) x} → ℝ) where
  toFun F := fun x => F x.1
  map_add' F G := by
    funext x
    exact L.ae_iff_eq.mp (Lp.coeFn_add F G) x.1 x.2
  map_smul' c F := by
    funext x
    exact L.ae_iff_eq.mp (Lp.coeFn_smul c F) x.1 x.2

/-- Evaluation on the chain is injective: `λ` charges every state of the chain and vanishes off
it, so a class vanishing there is the zero class. -/
theorem evalChain_injective : Function.Injective L.evalChain := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  refine Lp.ext ?_
  have h0 : ∀ x, OnChain (some K) x → (F : St → ℝ) x = (0 : St → ℝ) x := by
    intro x hx
    have h := congrFun hF ⟨x, hx⟩
    exact h
  exact (L.ae_eq_of_onChain h0).trans (Lp.coeFn_zero ℝ 2 L.mu).symm

/-- **`L²(λ^K)` is finite-dimensional** — the sentence of Step 4 that
`OperatorFinite.exists_resolvent` waits on. -/
instance instFiniteDimensionalLp : FiniteDimensional ℝ (Lp ℝ 2 L.mu) :=
  FiniteDimensional.of_injective L.evalChain L.evalChain_injective

/-! ## 3. `lem:doubling_operator`(2) on the truncation -/

/-- **`lem:doubling_operator`(2), instantiated.** On the truncation `Id − P⋆ + Π` is invertible and
the diffusion operator `S := (Id − P⋆ + Π)^{-1} − Π` satisfies `eq:doubling_resolvent`. -/
theorem exists_diffusionOp (hrow : RowOnChain S (some K)) :
    ∃ R : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
      (1 - L.pstarL2 hrow + L.piL2) * R = 1
      ∧ R * (1 - L.pstarL2 hrow + L.piL2) = 1
      ∧ (1 - L.pstarL2 hrow) * (R - L.piL2) = 1 - L.piL2
      ∧ (R - L.piL2) * (1 - L.pstarL2 hrow) = 1 - L.piL2
      ∧ L.piL2 * (R - L.piL2) = 0
      ∧ (R - L.piL2) * L.piL2 = 0 :=
  exists_resolvent L.piL2_mul_piL2 (L.piL2_mul_pstarL2 hrow) (L.pstarL2_mul_piL2 hrow)
    fun _ hf => L.piL2_fixed_of_pstarL2_fixed hrow hf

/-- **`lem:doubling_truncation_irreducible` Step 4, and `cor:doubling_truncation` Step 1.**

There is a diffusion operator `S` on `L²(λ^K)` satisfying `eq:doubling_resolvent`, and its norm
`B̂_K` is a real number — which is `B̂_K < +∞`. The last clause is what Step 3 of
`cor:doubling_truncation` consumes: `‖F − ΠF‖ = ‖S(Id − P⋆)F‖ ≤ B̂_K‖(Id − P⋆)F‖`. -/
theorem exists_bhat (hrow : RowOnChain S (some K)) :
    ∃ Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
      (1 - L.pstarL2 hrow) * Sop = 1 - L.piL2
      ∧ Sop * (1 - L.pstarL2 hrow) = 1 - L.piL2
      ∧ L.piL2 * Sop = 0 ∧ Sop * L.piL2 = 0
      ∧ ∀ F : Lp ℝ 2 L.mu,
          ‖F - L.piL2 F‖ ≤ ‖Sop‖ * ‖F - L.pstarL2 hrow F‖ := by
  obtain ⟨R, -, -, e1, e2, e3, e4⟩ := L.exists_diffusionOp hrow
  refine ⟨R - L.piL2, e1, e2, e3, e4, fun F => ?_⟩
  have h : ((R - L.piL2) * (1 - L.pstarL2 hrow)) F = (1 - L.piL2) F := by rw [e2]
  have hl : ((R - L.piL2) * (1 - L.pstarL2 hrow)) F
      = (R - L.piL2) (F - L.pstarL2 hrow F) := by
    show (R - L.piL2) ((1 - L.pstarL2 hrow) F) = _
    congr 1
  have hr : (1 - L.piL2) F = F - L.piL2 F := by simp
  rw [hl, hr] at h
  rw [← h]
  exact ContinuousLinearMap.le_opNorm _ _

end Truncation

end Stat

end GFNBounds.Doubling
