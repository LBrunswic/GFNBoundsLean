import GFNBounds.Balance.Flow

/-!
# Discrete gradient descent contracts by `1 − εϱ` per step

**`theo:db_stable_frozen_full`** — statement `proofs.tex:592–602`, proof `proofs.tex:604–610`;
**the discrete half only**, the sibling of `GFNBounds.Balance.stable_frozen_decay`, with the
linearization hypothesised and not derived, see SCOPE.
(The bold-backtick form of the label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (`theo:db_stable_frozen_full`, the discrete sentence) For discrete gradient descent with step
> `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}`, the contraction factor per step is `1 − εϱ`.

> (its proof, last sentence) For the discrete case, `‖A‖ ≤ 2` gives `‖H‖ ≤ 4g''(1)‖w‖_{L^∞}`, so
> `ε‖H‖ ≤ 1` and `‖(I − εH)h_⊥‖ ≤ (1 − εϱ)‖h_⊥‖`.

## The finding: the printed factor is right, the named route gives its square root

The proof sentence names `ε‖H‖ ≤ 1` and then asserts `‖(I − εH)h_⊥‖ ≤ (1 − εϱ)‖h_⊥‖`. The
energy method — the discrete analogue of the continuous half's Grönwall step, and the only
argument the sentence points at — does **not** deliver that. Writing `T := I − εH`,

  `‖Th_⊥‖² = ‖h_⊥‖² − 2ε⟨h_⊥, Hh_⊥⟩ + ε²‖Hh_⊥‖² ≤ ‖h_⊥‖² − ε(2 − ε‖H‖)⟨h_⊥, Hh_⊥⟩`

(using `‖Hx‖² ≤ ‖H‖⟨x, Hx⟩`, which is itself a fact about **self-adjoint positive** `H`), so
with `ε‖H‖ ≤ 1` and the coercivity `⟨h_⊥, Hh_⊥⟩ ≥ ϱ‖h_⊥‖²` one gets
`‖Th_⊥‖² ≤ (1 − εϱ)‖h_⊥‖²` — the factor **`√(1 − εϱ)`** on the norm, which is strictly larger
than the printed `1 − εϱ` whenever `0 < εϱ < 1`. `scalar_discrete_check`(3) exhibits the gap
numerically at `εϱ = 1/2`: `√(1/2) = 0.707… > 1/2`.

The printed `1 − εϱ` is nevertheless **true**, by an argument the paper does not name. `T` is
self-adjoint; `ε‖H‖ ≤ 1` buys `0 ≤ ⟪y, Ty⟫` for **every** `y`; and the coercivity buys
`⟪y, Ty⟫ ≤ (1 − εϱ)‖y‖²` on `ker Π`, which `ΠH = 0` makes `T`-invariant. A self-adjoint operator
whose quadratic form is squeezed between `0` and `c` on an invariant subspace has norm at most
`c` there — for a symmetric semi-definite form that is the Cauchy–Schwarz inequality applied at
`(x, Tx)`, not the spectral theorem. `inner_sq_le_of_symm_nonneg` is that Cauchy–Schwarz (via
the discriminant of `t ↦ ⟪x + t•y, T(x + t•y)⟫ ≥ 0`) and `norm_apply_le_of_symm_bounds` is the
consequence. No spectral theory is used, and none exists in this library.

What the file therefore records as a paper finding: **self-adjointness of `H` is load-bearing
for the discrete clause and is nowhere named in its proof.** The paper's `H = g''(1)A^†M_wA` is
self-adjoint (`⟪A^†M_wAx, y⟫ = ⟪M_wAx, Ay⟫ = ⟪Ax, M_wAy⟫ = ⟪x, A^†M_wAy⟫` for real `w`), so the
theorem is correct as stated; but `H ⪰ 0` in the proof's first line asserts positivity, which
over a **real** space does not entail symmetry, and the continuous half genuinely does not need
either (`GFNBounds/Balance/Flow.lean` proves it without both). The hypothesis is new at the
discrete sentence and is carried here explicitly, as `hHsa`.

## What is proved

| | |
|---|---|
| `inner_sq_le_of_symm_nonneg` | Cauchy–Schwarz for the semi-definite form `⟪·, T·⟫` of a symmetric `T` with `⟪y, Ty⟫ ≥ 0`, by `discrim_le_zero` |
| `norm_apply_le_of_symm_bounds` | `0 ≤ T ≤ c` on a `T`-invariant set gives `‖Tx‖ ≤ c‖x‖` there — the spectral-theorem-free half of "norm = numerical radius for a symmetric operator" |
| `H_proj_eq_zero` | `ΠH = 0` plus self-adjointness of `Π` and `H` gives `HΠ = 0`, which is what makes `h_k − Πh_0` evolve autonomously |
| `stable_frozen_discrete` | **`theo:db_stable_frozen_full`, the discrete half**: `Πh_k` is conserved and `‖h_k − Πh_k‖ ≤ (1 − εϱ)^k ‖h_0 − Πh_0‖` |
| `scalar_discrete_check` | the contraction **evaluated**, attained with equality at every step, and the energy-method factor `√(1 − εϱ)` shown strictly weaker |

## Hypothesis checklist — `theo:db_stable_frozen_full`, discrete clause

| paper hypothesis | here |
|---|---|
| the setting of `theo:gd_diffusion_full`; `H = g''(1)A^†M_wA` | ✗ **not derived** — `H` is an abstract `E →L[ℝ] E`, exactly as in `Flow.lean`. See SCOPE |
| `T` ergodic with summable `L²`-mixing, `w ≥ w_min > 0`, `ϱ := g''(1)w_min/B̂²` | ⚠ folded into `hcoer : ϱ‖x − Πx‖² ≤ ⟪x, Hx⟫`, which `GFNBounds.Balance.inner_ge_of_mixing` produces from `lem:sigma_mixing` with `ϱ = c/B̂²`, `c = g''(1)w_min`. Composing the two gives the paper's `ϱ` |
| `ΠH = 0`, "since `P^†` preserves integrals" | ⚠ **hypothesis** `hPiH` |
| `Π` the projection onto the invariant functions | ⚠ **hypotheses** `hPisa` (self-adjoint, as in `Flow.lean`) and `hPiPi` (idempotent). `Flow.lean` needed only the first; the discrete iteration needs the second, to know `h_k − Πh_0 ∈ ker Π`. ⚠ **strengthened** relative to the sibling; true of the paper's `Π` |
| `H ⪰ 0` (the proof's first line) | ⚠ **strengthened** to `hHsa : ∀ x y, ⟪Hx, y⟫ = ⟪x, Hy⟫`, self-adjointness. See the finding above: positivity alone does not give the printed factor, and over a real space does not even give symmetry. True of the paper's `H`; **not** in the paper's sentence |
| `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}`, i.e. `ε‖H‖ ≤ 1` | ⚠ **weakened** to the quadratic-form bound `hup : ⟪x, Hx⟫ ≤ Λ‖x‖²` with `hepsL : εΛ ≤ 1`. The paper's `Λ = 4g''(1)‖w‖_{L^∞}` is an operator-norm bound, which implies `hup` by Cauchy–Schwarz; the converse fails, so this is the weaker hypothesis and the stronger theorem. The paper's `‖A‖ ≤ 2 ⇒ ‖H‖ ≤ 4g''(1)‖w‖_{L^∞}` is **not** derived — `A` is not present |
| `ε ≥ 0` | ⚠ **hypothesis** `heps`. Implicit in the paper ("step `ε ≤ …`"), used to multiply the two form bounds |
| `εϱ ≤ 1` | ⚠ **hypothesis** `hrho`, **strengthened**. The paper does not state it; it follows from `ϱ ≤ ‖H‖ ≤ 1/ε` whenever `ker Π ≠ 0` (put `x ∈ ker Π` in `hcoer`), but that derivation needs the operator-norm bound the file deliberately does not carry, and on a space with `ker Π = 0` the conclusion is vacuous anyway. Carried, not derived |
| `L²(λ)` | ⚠ **generalized**: any real inner-product space `E`, no completeness |
| `Πh_k` conserved | ✓ first conjunct — not in the paper's discrete sentence, which speaks only of `h_⊥`; supplied to match the continuous half |
| the contraction factor per step is `1 − εϱ` | ✓ second conjunct, `‖h_k − Πh_k‖ ≤ (1 − εϱ)^k‖h_0 − Πh_0‖`, and `scalar_discrete_check` shows it attained |

## SCOPE (disclosed)

* **The linearization is a hypothesis, not a derivation**, exactly as in
  `GFNBounds/Balance/Flow.lean`. `H := g''(1)A^†M_wA` comes from `theo:gd_diffusion_full`, which
  is bucket `D` and is not formalized; so `H` is abstract, `ϱ` is any constant satisfying
  `hcoer`, and `Λ` is any constant satisfying `hup`. Identifying them with
  `g''(1)w_min/B̂²` and `4g''(1)‖w‖_{L^∞}` is a separate job and is **not** done here. The
  bridge from `lem:sigma_mixing` to `hcoer` already exists and is reused, not reproved:
  `GFNBounds.Balance.inner_ge_of_mixing`.
* **`H` abstract here — but the finite-state instantiation now exists.** Nothing in *this* file
  is a statement about a Markov kernel, a backward policy or a state space.
  `GFNBounds/Balance/WeightedL2.lean` (2026-09-12) supplies the weighted-`L²` bridge and derives
  `stable_frozen_discrete_finite`, which is this theorem at the paper's own
  `H = g''(1)A^†M_wA`, with `ϱ = g''(1)w_min/B̂²` and the step condition written out.
* **The `lem:lift_mixing` transfer to the FM and DB losses is not stated**, here or in
  `Flow.lean`. The sentence "the statement covers the FM loss with `B̂ = B` and the DB loss with
  `B̂ ≤ 1 + B`" remains unformalized, as does the nonlinear upgrade
  `theo:local_convergence_full`.
* **The descent recursion is hypothesised, not produced.** `hstep : h (k+1) = h k − ε • H (h k)`
  is assumed of a given sequence; nothing here asserts that gradient descent on `𝓛_{g,ν}`
  *is* this recursion — that is again `theo:gd_diffusion_full`. This mirrors `Flow.lean`'s "no
  existence theorem, and none is needed".
* **`ϱ > 0` and `Λ ≥ 0` are not hypothesised.** The conclusion holds for any reals satisfying
  the four inequalities; for `ϱ ≤ 0` it is a growth bound rather than a contraction, and the
  paper's `ϱ = g''(1)w_min/B̂²` is positive on its own hypotheses. Recorded as a strengthening,
  not silently taken.
* **`scalar_discrete_check` runs at `Π = 0`**, where the conserved-component conjunct says
  nothing — the same partiality `Flow.lean` discloses for `scalar_decay_check`. Exercising both
  conjuncts at once needs `dim E ≥ 2` with a non-trivial projection, and is not done.
* **`sorry`-free.** This file is in the scaffold because graduation is the master session's
  decision, not because anything in it is open.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open scoped RealInnerProductSpace

/-! ### Symmetric semi-definite operators: Cauchy–Schwarz, and the norm from the form

Two facts about a symmetric `T` with non-negative quadratic form, both elementary and both
proved without any spectral theory. They are stated for an arbitrary `T`, with no reference to
the `H` of `theo:db_stable_frozen_full`. -/

section SymmetricForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cauchy–Schwarz for a symmetric positive semi-definite form.** If `T` is symmetric and
`⟪y, Ty⟫ ≥ 0` for every `y`, then `⟪·, T·⟫` is a positive semi-definite symmetric bilinear form
and obeys `⟪x, Ty⟫² ≤ ⟪x, Tx⟫⟪y, Ty⟫`.

The proof is the standard one and needs no definiteness: the real quadratic
`t ↦ ⟪x + t•y, T(x + t•y)⟫ = ⟪y, Ty⟫t² + 2⟪x, Ty⟫t + ⟪x, Tx⟫` is everywhere non-negative, so its
discriminant is non-positive (`discrim_le_zero`). -/
theorem inner_sq_le_of_symm_nonneg {T : E →L[ℝ] E}
    (hsymm : ∀ x y : E, ⟪T x, y⟫ = ⟪x, T y⟫) (hnn : ∀ y : E, 0 ≤ ⟪y, T y⟫) (x y : E) :
    ⟪x, T y⟫ ^ 2 ≤ ⟪x, T x⟫ * ⟪y, T y⟫ := by
  have hxy : ⟪y, T x⟫ = ⟪x, T y⟫ := (hsymm y x).symm.trans (real_inner_comm x (T y))
  have hq : ∀ t : ℝ, 0 ≤ ⟪y, T y⟫ * (t * t) + 2 * ⟪x, T y⟫ * t + ⟪x, T x⟫ := by
    intro t
    have h := hnn (x + t • y)
    have hexp : ⟪x + t • y, T (x + t • y)⟫
        = ⟪y, T y⟫ * (t * t) + 2 * ⟪x, T y⟫ * t + ⟪x, T x⟫ := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hxy]
      ring
    rwa [hexp] at h
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- **From the form to the norm, without the spectral theorem.** Let `T` be symmetric with
`⟪y, Ty⟫ ≥ 0` everywhere, let `S` be a set carried into itself by `T`, and suppose
`⟪y, Ty⟫ ≤ c‖y‖²` on `S` with `0 ≤ c`. Then `‖Tx‖ ≤ c‖x‖` for every `x ∈ S`.

This is the step the paper's `‖(I − εH)h_⊥‖ ≤ (1 − εϱ)‖h_⊥‖` needs and does not name; see the
module header. Apply `inner_sq_le_of_symm_nonneg` at the pair `(x, Tx)`: symmetry turns
`⟪x, T(Tx)⟫` into `‖Tx‖²`, so `‖Tx‖⁴ ≤ (c‖x‖²)(c‖Tx‖²)`, and the roots come off once `‖Tx‖ ≠ 0`
is separated. -/
theorem norm_apply_le_of_symm_bounds {T : E →L[ℝ] E} {S : Set E} {c : ℝ}
    (hsymm : ∀ x y : E, ⟪T x, y⟫ = ⟪x, T y⟫) (hnn : ∀ y : E, 0 ≤ ⟪y, T y⟫) (hc : 0 ≤ c)
    (hinv : ∀ x ∈ S, T x ∈ S) (hub : ∀ y ∈ S, ⟪y, T y⟫ ≤ c * ‖y‖ ^ 2)
    {x : E} (hx : x ∈ S) : ‖T x‖ ≤ c * ‖x‖ := by
  have key := inner_sq_le_of_symm_nonneg hsymm hnn x (T x)
  have hTT : ⟪x, T (T x)⟫ = ‖T x‖ ^ 2 :=
    (hsymm x (T x)).symm.trans (real_inner_self_eq_norm_sq (T x))
  rw [hTT] at key
  have h1 : ⟪x, T x⟫ ≤ c * ‖x‖ ^ 2 := hub x hx
  have h2 : ⟪T x, T (T x)⟫ ≤ c * ‖T x‖ ^ 2 := hub (T x) (hinv x hx)
  have h0' : 0 ≤ ⟪T x, T (T x)⟫ := hnn (T x)
  have h3 : (‖T x‖ ^ 2) ^ 2 ≤ c * ‖x‖ ^ 2 * (c * ‖T x‖ ^ 2) :=
    key.trans (mul_le_mul h1 h2 h0' (by positivity))
  rcases eq_or_lt_of_le (norm_nonneg (T x)) with hz | hpos
  · rw [← hz]; positivity
  · have hsq : (0 : ℝ) < ‖T x‖ ^ 2 := by positivity
    have h3' : ‖T x‖ ^ 2 * ‖T x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 * ‖T x‖ ^ 2 := by nlinarith [h3]
    have h4 : ‖T x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := le_of_mul_le_mul_right h3' hsq
    nlinarith [h4, norm_nonneg (T x), mul_nonneg hc (norm_nonneg x)]

end SymmetricForm

/-! ### `theo:db_stable_frozen_full`, the discrete half

`proofs.tex:592–610`. The sibling of `GFNBounds.Balance.stable_frozen_decay`: same abstract `H`,
same hypothesised linearization, the Euler step in place of the flow and
`norm_apply_le_of_symm_bounds` in place of Grönwall. -/

section LinearizedDiscrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`ΠH = 0` gives `HΠ = 0`** when both `Π` and `H` are self-adjoint. Used once, to see that
`h_k − Πh_0` satisfies the same recursion as `h_k` — which is what makes the iteration stay
inside `ker Π`, where the coercivity is a bound on the whole quadratic form. -/
theorem H_proj_eq_zero {H Pi : E →L[ℝ] E} (hPisa : ∀ x y : E, ⟪Pi x, y⟫ = ⟪x, Pi y⟫)
    (hHsa : ∀ x y : E, ⟪H x, y⟫ = ⟪x, H y⟫) (hPiH : ∀ x : E, Pi (H x) = 0) (x : E) :
    H (Pi x) = 0 := by
  have h : ∀ y : E, ⟪H (Pi x), y⟫ = 0 := by
    intro y
    rw [hHsa, hPisa, hPiH, inner_zero_right]
  exact inner_self_eq_zero.mp (h (H (Pi x)))

/-- **`theo:db_stable_frozen_full`, the discrete half** (statement `proofs.tex:592–602`, proof
`proofs.tex:604–610`): along the descent recursion `h_{k+1} = h_k − εHh_k`, the component `Πh_k`
is conserved and `‖h_k − Πh_k‖ ≤ (1 − εϱ)^k‖h_0 − Πh_0‖` — the paper's "the contraction factor
per step is `1 − εϱ`".

The paper's step condition `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}` enters as `hup` with
`Λ = 4g''(1)‖w‖_{L^∞}` together with `hepsL : εΛ ≤ 1`; `hrho : εϱ ≤ 1` is implicit in the paper
(`ϱ ≤ ‖H‖`) and is carried here rather than derived. **`hHsa` — self-adjointness of `H` — is
not in the paper's sentence and is load-bearing**; the module header explains why, and why the
route the sentence names delivers only `√(1 − εϱ)`.

The argument, in one line: `T := I − εH` is self-adjoint, `hup` with `εΛ ≤ 1` makes its form
non-negative everywhere, `hcoer` makes it at most `(1 − εϱ)‖y‖²` on the `T`-invariant subspace
`ker Π`, and `norm_apply_le_of_symm_bounds` converts that sandwich into the operator bound. `H`
is **abstract**: the identification with `g''(1)A^†M_wA` is `theo:gd_diffusion_full` and is not
done here. See the module SCOPE. -/
theorem stable_frozen_discrete {H Pi : E →L[ℝ] E} {rho Lam eps : ℝ} {h : ℕ → E}
    (hPisa : ∀ x y : E, ⟪Pi x, y⟫ = ⟪x, Pi y⟫)
    (hPiPi : ∀ x : E, Pi (Pi x) = Pi x)
    (hHsa : ∀ x y : E, ⟪H x, y⟫ = ⟪x, H y⟫)
    (hPiH : ∀ x : E, Pi (H x) = 0)
    (hcoer : ∀ x : E, rho * ‖x - Pi x‖ ^ 2 ≤ ⟪x, H x⟫)
    (hup : ∀ x : E, ⟪x, H x⟫ ≤ Lam * ‖x‖ ^ 2)
    (heps : 0 ≤ eps) (hepsL : eps * Lam ≤ 1) (hrho : eps * rho ≤ 1)
    (hstep : ∀ k, h (k + 1) = h k - eps • H (h k)) :
    (∀ k, Pi (h k) = Pi (h 0)) ∧
      ∀ k, ‖h k - Pi (h k)‖ ≤ (1 - eps * rho) ^ k * ‖h 0 - Pi (h 0)‖ := by
  -- (a) the projected component is conserved
  have hconst : ∀ k, Pi (h k) = Pi (h 0) := by
    intro k
    induction k with
    | zero => rfl
    | succ n ih =>
        rw [hstep n, map_sub, map_smul, hPiH, smul_zero, sub_zero, ih]
  refine ⟨hconst, ?_⟩
  -- (b) the one-step operator `T = I − εH`, and its three properties
  set T : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - eps • H with hTdef
  have hTapp : ∀ x : E, T x = x - eps • H x := by
    intro x
    simp only [hTdef, sub_apply, smul_apply,
      ContinuousLinearMap.coe_id', id_eq]
  have hTform : ∀ x : E, ⟪x, T x⟫ = ‖x‖ ^ 2 - eps * ⟪x, H x⟫ := by
    intro x
    rw [hTapp, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hTsymm : ∀ x y : E, ⟪T x, y⟫ = ⟪x, T y⟫ := by
    intro x y
    rw [hTapp, hTapp, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hHsa]
  have hTnn : ∀ y : E, 0 ≤ ⟪y, T y⟫ := by
    intro y
    have hb : eps * ⟪y, H y⟫ ≤ eps * (Lam * ‖y‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hup y) heps
    have hsq : (0 : ℝ) ≤ ‖y‖ ^ 2 := by positivity
    rw [hTform]
    nlinarith [hb, hsq, hepsL]
  -- (c) `ker Π` is `T`-invariant, and there the form is at most `(1 − εϱ)‖·‖²`
  have hinv : ∀ x ∈ {y : E | Pi y = 0}, T x ∈ {y : E | Pi y = 0} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [hTapp, map_sub, map_smul, hPiH, smul_zero, sub_zero, hx]
  have hub : ∀ y ∈ {y : E | Pi y = 0}, ⟪y, T y⟫ ≤ (1 - eps * rho) * ‖y‖ ^ 2 := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    have hco : rho * ‖y‖ ^ 2 ≤ ⟪y, H y⟫ := by
      have := hcoer y
      rwa [hy, sub_zero] at this
    have hb : eps * (rho * ‖y‖ ^ 2) ≤ eps * ⟪y, H y⟫ := mul_le_mul_of_nonneg_left hco heps
    rw [hTform]
    nlinarith [hb]
  have hc : (0 : ℝ) ≤ 1 - eps * rho := by linarith
  -- (d) the shifted iterate `y_k = h_k − Πh_0` lives in `ker Π` and obeys `y_{k+1} = T y_k`
  have hmem : ∀ k, h k - Pi (h 0) ∈ {y : E | Pi y = 0} := by
    intro k
    simp only [Set.mem_setOf_eq, map_sub, hconst k, hPiPi, sub_self]
  have hrec : ∀ k, h (k + 1) - Pi (h 0) = T (h k - Pi (h 0)) := by
    intro k
    have hH : H (h k - Pi (h 0)) = H (h k) := by
      rw [map_sub, H_proj_eq_zero hPisa hHsa hPiH, sub_zero]
    rw [hTapp, hH, hstep k]
    abel
  -- (e) the induction
  have hmain : ∀ k, ‖h k - Pi (h 0)‖ ≤ (1 - eps * rho) ^ k * ‖h 0 - Pi (h 0)‖ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
        have hone : ‖h (n + 1) - Pi (h 0)‖ ≤ (1 - eps * rho) * ‖h n - Pi (h 0)‖ := by
          rw [hrec n]
          exact norm_apply_le_of_symm_bounds hTsymm hTnn hc hinv hub (hmem n)
        calc ‖h (n + 1) - Pi (h 0)‖ ≤ (1 - eps * rho) * ‖h n - Pi (h 0)‖ := hone
          _ ≤ (1 - eps * rho) * ((1 - eps * rho) ^ n * ‖h 0 - Pi (h 0)‖) :=
              mul_le_mul_of_nonneg_left ih hc
          _ = (1 - eps * rho) ^ (n + 1) * ‖h 0 - Pi (h 0)‖ := by ring
  intro k
  rw [hconst k]
  exact hmain k

end LinearizedDiscrete

/-! ### The contraction, computed

A one-dimensional solution of `h_{k+1} = h_k − εHh_k` on which the bound is attained at every
step, so the factor is exactly `1 − εϱ` — and not the `√(1 − εϱ)` the paper's named route
delivers. -/

section ScalarDiscreteCheck

/-- **The discrete contraction, evaluated, attained, and separated from its square root.** On
`E = ℝ` with `H = 2·id`, `Π = 0`, `ε = 1/4`, `ϱ = 2`, `Λ = 2` and `h_k = 5·(1/2)^k` — a genuine
solution of `h_{k+1} = h_k − εHh_k`, since `h_k − (1/4)(2h_k) = h_k/2` — `stable_frozen_discrete`
gives `‖h_k‖ ≤ (1 − εϱ)^k‖h_0‖` with `1 − εϱ = 1/2`, and the two sides are **equal at every
`k`**.

Three things at once. *(1)* is proved **through** `stable_frozen_discrete`, discharging each of
its ten hypotheses, so nothing above is vacuous; *(2)* and *(3)* are arithmetic, and it is the
comparison of *(1)* with *(2)* that is the check. The factor is exactly `1 − εϱ`: equality at every step leaves no room
to improve it, and no room for a sign or factor error in the induction. And *(3)* pins the
finding of the module header — the energy method's factor `√(1 − εϱ) = √(1/2) = 0.707…` is
strictly larger than the attained `1/2`, so the route the paper's proof sentence names is
genuinely weaker than the statement it is offered for.

`Π = 0` here, so the conserved-component conjunct is exercised only vacuously; see the module
SCOPE. -/
theorem scalar_discrete_check :
    (∀ k : ℕ, ‖(5 : ℝ) * (1 / 2) ^ k‖
        ≤ (1 - (1 / 4 : ℝ) * 2) ^ k * ‖(5 : ℝ) * (1 / 2) ^ (0 : ℕ)‖)
      ∧ (∀ k : ℕ, ‖(5 : ℝ) * (1 / 2) ^ k‖
          = (1 - (1 / 4 : ℝ) * 2) ^ k * ‖(5 : ℝ) * (1 / 2) ^ (0 : ℕ)‖)
      ∧ (1 - (1 / 4 : ℝ) * 2) < Real.sqrt (1 - (1 / 4 : ℝ) * 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have key := stable_frozen_discrete (E := ℝ) (H := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (Pi := 0) (rho := 2) (Lam := 2) (eps := 1 / 4)
      (h := fun k : ℕ => (5 : ℝ) * (1 / 2) ^ k)
      (fun x y => by simp)
      (fun x => by simp)
      (fun x y => by
        simp only [smul_apply, ContinuousLinearMap.coe_id', id_eq,
          real_inner_smul_left, real_inner_smul_right])
      (fun x => by simp)
      (fun x => by
        simp only [zero_apply, sub_zero, smul_apply,
          ContinuousLinearMap.coe_id', id_eq, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        ring_nf
        exact le_rfl)
      (fun x => by
        simp only [smul_apply, ContinuousLinearMap.coe_id', id_eq,
          real_inner_smul_right, real_inner_self_eq_norm_sq]
        ring_nf
        exact le_rfl)
      (by norm_num) (by norm_num) (by norm_num)
      (fun k => by
        simp only [smul_apply, ContinuousLinearMap.coe_id', id_eq,
          smul_eq_mul, pow_succ]
        ring)
    simpa using key.2
  · intro k
    have h5 : ‖(5 : ℝ) * (1 / 2) ^ k‖ = 5 * (1 / 2) ^ k := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h5]
    norm_num
    ring
  · rw [show (1 - (1 / 4 : ℝ) * 2) = 1 / 2 by norm_num]
    rw [Real.lt_sqrt (by norm_num)]
    norm_num

end ScalarDiscreteCheck

end GFNBounds.Balance
