import Mathlib

/-!
# Appendix B: the shared vocabulary

The finite-sum quantities that both propositions of the Silva comparison
(`silva_comparison.tex`) are stated in, and the identities that are about those quantities
alone. This module certifies no paper label. It exists so that
`GFNBounds.Silva.Explicit` and `GFNBounds.Silva.NoUniform` — which were written
independently, each defining this vocabulary locally in the same namespace — can be imported
together.

| here | paper (`silva_comparison.tex`) |
|---|---|
| `tv p q` | `TV(p,q) = ½ ∑ₓ \|p(x) − q(x)\|` |
| `chiSq q p` | `χ²(q‖p) = ∑ₓ (q(x) − p(x))²/p(x)` |
| `unif X` | the uniform law `q_{E,T}` on `𝒳` |
| `logRatio π pB pF x t` | `log(p_F(τ)/(π(x) p_B(τ\|x)))`, the log-ratio of the proof at line 89 |
| `residual pET π pB pF` | `𝓔(p_F)` of lines 24–26 |
| `MprimeLe pB pF π c` | `M' := max(M, ‖π‖_∞) ≤ c`, with `M` of line 32 |
| `wMin pET pB h` | `w_min := min{ p_{E,T}(x) p_B(τ\|x) : p_B(τ\|x) > 0 }` |

`residual` rather than `energy`: the paper calls `𝓔(p_F)` "the residual" in prose
(`silva_comparison.tex:69`). Its argument order — training measure, target, backward policy,
forward policy — is the order in which the four appear in the display at
`silva_comparison.tex:25`.

## Conventions

* **Sums run over the whole finite type, never over a support.** Off the support of `p_B(·|x)`
  the factor `p_B(τ|x) = 0` kills the summand of `residual`, and Lean's `x/0 = 0` and `log 0 = 0`
  make `logRatio` harmless there. So no `Finset.filter` and no decidability are needed, and the
  hypotheses of the two propositions are conditioned on `0 < p_B(τ|x)` for the same reason.
* **`χ²` is the standard `∑ (q − p)²/p`**, not `∑ q²/p − 1`. The identity the factor `1 + χ²`
  of `eq:silva_bound` stands for is therefore `sum_sq_div_eq_one_add_chiSq`, and it is the place
  the normalizations `∑ q = 1` and `∑ p = 1` are consumed — with the other convention they would
  be invisible.
* **`M'` is a `Prop`, not a value.** `MprimeLe` unfolds `max(M, ‖π‖_∞) ≤ c` into its two halves
  rather than defining `M'` as a `Finset.sup'`, which would need the support nonempty.
  `Silva/Explicit.lean` states the same two halves inline as `hM` and `hPinf`, and its
  `tv_le_sqrt_residual_max` builds the two `Finset.sup'`s where it needs them.
* **`w_min` is `Finset.inf'` over the support pairs** `wSupport`, so it carries a nonemptiness
  argument. The general form used by the proof of `prop:silva_no_uniform`(i) takes any positive
  lower bound instead; the bound is monotone in it, so the two are the same content.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Nothing here is a
`sorry`.
-/

namespace GFNBounds.Silva

/-! ## The finite functionals -/

/-- Total variation on a finite set, with the ½-convention:
`TV(p,q) = ½ ∑_x |p(x) − q(x)|`. -/
noncomputable def tv {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ :=
  2⁻¹ * ∑ x, |p x - q x|

/-- The `χ²`-divergence in its standard finite form,
`χ²(q‖p) = ∑_x (q(x) − p(x))²/p(x)`. -/
noncomputable def chiSq {X : Type*} [Fintype X] (q p : X → ℝ) : ℝ :=
  ∑ x, (q x - p x) ^ 2 / p x

/-- The uniform law `q_{E,T}` on a finite set. -/
noncomputable def unif (X : Type*) [Fintype X] : X → ℝ :=
  fun _ => (Fintype.card X : ℝ)⁻¹

/-- The log-ratio `ℓ(τ) = log (p_F(τ) / (π(x) p_B(τ|x)))` of the proof at
`silva_comparison.tex:89`. -/
noncomputable def logRatio {X T : Type*} (π : X → ℝ) (pB : X → T → ℝ) (pF : T → ℝ)
    (x : X) (t : T) : ℝ :=
  Real.log (pF t / (π x * pB x t))

/-- The residual `𝓔(p_F) = E_{x∼p_{E,T}} E_{τ∼p_B(·|x)}[(log(p_F(τ)/(π(x) p_B(τ|x))))²]`
of `silva_comparison.tex:24–26`. Off the support of `p_B(·|x)` the factor `p_B(τ|x)` kills the
term, which is the intended reading of the inner expectation. -/
noncomputable def residual {X T : Type*} [Fintype X] [Fintype T]
    (pET π : X → ℝ) (pB : X → T → ℝ) (pF : T → ℝ) : ℝ :=
  ∑ x, pET x * ∑ t, pB x t * logRatio π pB pF x t ^ 2

/-- `residual` with the log written out, for rewriting. -/
theorem residual_eq {X T : Type*} [Fintype X] [Fintype T]
    (pET π : X → ℝ) (pB : X → T → ℝ) (pF : T → ℝ) :
    residual pET π pB pF
      = ∑ x, pET x * ∑ t, pB x t * Real.log (pF t / (π x * pB x t)) ^ 2 :=
  rfl

/-- `M' ≤ c`, with `M' = max(M, ‖π‖_∞)` and `M = max{p_F(τ)/p_B(τ|x) : p_B(τ|x) > 0}`
(`silva_comparison.tex:32`), unfolded into its two halves. -/
def MprimeLe {X T : Type*} [Fintype X] [Fintype T] (pB : X → T → ℝ) (pF : T → ℝ)
    (π : X → ℝ) (c : ℝ) : Prop :=
  (∀ x t, 0 < pB x t → pF t / pB x t ≤ c) ∧ ∀ x, π x ≤ c

/-! ## Identities about the vocabulary -/

/-- `χ²(q‖p) ≥ 0` whenever `p ≥ 0`: the factor `1 + χ²` under the square root is nonnegative,
which is what lets the final Cauchy–Schwarz step be multiplied through. -/
theorem chiSq_nonneg {X : Type*} [Fintype X] {q p : X → ℝ} (hp : ∀ x, 0 ≤ p x) :
    0 ≤ chiSq q p :=
  Finset.sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (hp x)

/-- `χ²(p‖p) = 0`: the training law that *is* the uniform one has no `χ²` term. -/
theorem chiSq_self {X : Type*} [Fintype X] (p : X → ℝ) : chiSq p p = 0 := by
  simp [chiSq]

/-- The uniform law is a probability law on a nonempty finite set. -/
theorem sum_unif {X : Type*} [Fintype X] (h : (Fintype.card X : ℝ) ≠ 0) :
    ∑ x, unif X x = 1 := by
  simp only [unif, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ h

/-- `∑_x q(x)²/p(x) = 1 + χ²(q‖p)`, the identity the factor `1 + χ²` of `eq:silva_bound` stands
for. It is the place the normalizations `∑ q = 1` and `∑ p = 1` are consumed. -/
theorem sum_sq_div_eq_one_add_chiSq {X : Type*} [Fintype X] {q p : X → ℝ}
    (hp : ∀ x, 0 < p x) (hq1 : ∑ x, q x = 1) (hp1 : ∑ x, p x = 1) :
    ∑ x, q x ^ 2 / p x = 1 + chiSq q p := by
  have key : ∀ x : X, q x ^ 2 / p x = (q x - p x) ^ 2 / p x + 2 * q x - p x := by
    intro x
    have hx : p x ≠ 0 := (hp x).ne'
    field_simp
    ring
  calc ∑ x, q x ^ 2 / p x
      = ∑ x, ((q x - p x) ^ 2 / p x + 2 * q x - p x) :=
        Finset.sum_congr rfl fun x _ => key x
    _ = (∑ x, (q x - p x) ^ 2 / p x) + 2 * (∑ x, q x) - ∑ x, p x := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 1 + chiSq q p := by rw [hq1, hp1]; simp only [chiSq]; ring

/-! ## `w_min` -/

/-- The pairs `(x,τ)` over which `w_min` is a minimum: those with `p_B(τ|x) > 0`. -/
noncomputable def wSupport {X T : Type*} [Fintype X] [Fintype T] (pB : X → T → ℝ) :
    Finset (X × T) :=
  Finset.univ.filter fun p => 0 < pB p.1 p.2

/-- **`w_min := min{ p_{E,T}(x) p_B(τ|x) : p_B(τ|x) > 0 }`** of `prop:silva_no_uniform`. -/
noncomputable def wMin {X T : Type*} [Fintype X] [Fintype T] (pET : X → ℝ) (pB : X → T → ℝ)
    (h : (wSupport pB).Nonempty) : ℝ :=
  (wSupport pB).inf' h fun p => pET p.1 * pB p.1 p.2

theorem wMin_le {X T : Type*} [Fintype X] [Fintype T] {pET : X → ℝ} {pB : X → T → ℝ}
    (h : (wSupport pB).Nonempty) {x : X} {t : T} (ht : 0 < pB x t) :
    wMin pET pB h ≤ pET x * pB x t :=
  Finset.inf'_le (fun p : X × T => pET p.1 * pB p.1 p.2)
    (show (x, t) ∈ wSupport pB by simp [wSupport, ht])

theorem wMin_pos {X T : Type*} [Fintype X] [Fintype T] {pET : X → ℝ} {pB : X → T → ℝ}
    (h : (wSupport pB).Nonempty) (hET : ∀ x, 0 < pET x) : 0 < wMin pET pB h := by
  refine (Finset.lt_inf'_iff _).2 fun p hp => ?_
  simp only [wSupport, Finset.mem_filter] at hp
  exact mul_pos (hET p.1) hp.2

end GFNBounds.Silva
