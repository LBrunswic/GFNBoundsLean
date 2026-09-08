import GFNBounds.Silva.Basic

/-!
# The Silva et al. total-variation bound, with the constant written out

**`prop:silva_explicit`** — statement `silva_comparison.tex:29–39`, proof
`silva_comparison.tex:40–50`. The setting is `silva_comparison.tex:9–28`; the hypotheses the
proof consumes are enumerated in `rem:silva_hypotheses`, `silva_comparison.tex:52–62`, and that
remark is the specification this file was written against.

> Let `𝒳` be finite, let `p_{E,T}` and `π` have full support on `𝒳`, assume `p_F(τ) > 0` for
> every trajectory `τ` with `p_B(τ | x) > 0`, and assume `p_B(· | x)` dominates the forward
> trajectory distribution into each `x`. Set
> `M := max{ p_F(τ)/p_B(τ|x) : p_B(τ|x) > 0 }` and `M' := max(M, ‖π‖_∞)`. Then
> `TV(p_T, π) ≤ (|𝒳|/2) M' [(1 + χ²(q_{E,T} ‖ p_{E,T})) 𝓔(p_F)]^{1/2}`,

with `q_{E,T}` uniform on `𝒳` and
`𝓔(p_F) := E_{x∼p_{E,T}} E_{τ∼p_B(·|x)}[(log(p_F(τ)/(π(x) p_B(τ|x))))²]`.

The point of the restatement is twofold: the constant absorbed in Silva et al.'s `≲` is written
out, and the log-Lipschitz step is corrected from `M` to `M' = max(M, ‖π‖_∞)`
(`rem:silva_hypotheses`, item 5 — on a tree `M ≤ 1` while `‖π‖_∞` may approach `1`, so `π(x) ≤ M`
is *not* implied). Both are visible in `tv_le_sqrt_residual`, whose constant is `max M Pinf`;
with `M` alone the proof of `logLipschitz` breaks at exactly the point where `b ≤ C` is used.

## The three steps, and what each turns on

1. **Change of measure and Cauchy–Schwarz.** `TV(p_T,π) = (|𝒳|/2) E_{q}[φ]` is definitional here
   (inline, as `hTV` in the main proof), `q` being the uniform law with mass `1/|𝒳|`; then
   `(E_q[φ])² ≤ (∑ q²/p)(E_p[φ²])` is `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`, and
   `∑ q²/p = 1 + χ²(q‖p)` is `sum_sq_div_eq_one_add_chiSq`.
2. **Jensen over backward trajectories.** `sq_sub_weighted_le`: for a probability weight `w`,
   `(c − ∑ w f)² ≤ ∑ w (c − f)²`, again by
   `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` with `∑ w = 1`.
3. **The log-Lipschitz step.** `logLipschitz`: `|a − b| ≤ C |log a − log b|` for `0 < a,b ≤ C`.
   The paper argues by the mean value theorem for `exp` on `(−∞, log C]`. The formalization uses
   the elementary substitute `Real.log_le_sub_one_of_pos` applied to `a/b`, which gives
   `log(b/a) ≥ (b−a)/b ≥ (b−a)/C` for `a ≤ b ≤ C` — the same constant, with no differentiability
   and no `deriv`. This is a change of route, not of statement; it is recorded here rather than
   passed off as the paper's argument.

## SCOPE (disclosed)

* **Trajectories are an abstract finite index type.** `T` is a `Fintype` and nothing else. The
  DAG, the uniform horizon `t_m`, and acyclicity — item 6 of `rem:silva_hypotheses`, the standing
  structural axioms of Silva et al.'s framework — are *not* modelled, because this proposition
  does not consume them: every step is a finite sum manipulation. What the graph structure would
  supply, namely that `p_B(·|x)` is a probability law on the trajectories into `x` and that
  `p_T` is the terminal marginal, appears here as the hypotheses `hB_sum` and `hdom`. A
  formalization carrying the DAG would prove the same inequality from strictly more.
* **`M` and `‖π‖_∞` are bounds, not maxima, in the main theorem.** `tv_le_sqrt_residual` takes
  any `M` with `p_F(τ)/p_B(τ|x) ≤ M` on the support and any `Pinf` with `π ≤ Pinf`; the paper's
  constants are the least such, so the paper's statement is the instance. That instance is
  `tv_le_sqrt_residual_max`, which uses `Finset.sup'` and is therefore forced to carry the two
  nonemptiness proofs `hX` and `hsupp` as parameters — `sup'` is undefined on the empty finset.
  Both follow from the other hypotheses (`hET_sum` forces `𝒳 ≠ ∅`, `hB_sum` forces a
  positive-probability trajectory at each `x`), but Lean needs them before the statement can be
  formed, so they are stated.
* **`π` is not assumed normalized.** The paper's `π = R/Z` is a probability law, but no step of
  the proof uses `∑ π = 1` — only `π > 0` and `π ≤ ‖π‖_∞`. Rather than carry an unused
  hypothesis (which `warningAsError` would flag), it is dropped. This makes the Lean theorem
  formally stronger than the paper's; see the checklist.
* **`χ²` convention.** `chiSq q p = ∑ (q − p)²/p`, the standard definition. The identity
  `∑ q²/p = 1 + χ²(q‖p)` that the paper's `1 + χ²` factor needs then requires *both* laws to be
  normalized, and `sum_sq_div_eq_one_add_chiSq` carries `∑ q = 1` and `∑ p = 1` as hypotheses.
  With the other common convention `χ² = ∑ q²/p − 1` the identity is definitional and the
  normalizations are invisible; taking the standard one makes the paper's implicit use of
  `∑ p_{E,T} = 1` explicit.
* **Division by zero is Lean's.** Off the support of `p_B(·|x)` every quantity in sight is a term
  `p_B(τ|x) · (…)` with `p_B(τ|x) = 0`, so `p_F(τ)/0 = 0` and `log 0 = 0` make those terms vanish
  — which is the intended reading of `E_{τ∼p_B(·|x)}` and is why no support-restricted sum is
  needed. The hypotheses `hF_pos`, `hM` and `hdom` are all conditioned on `0 < p_B(τ|x)` for the
  same reason.
* **`p_T` is a hypothesis, not a construction.** `hdom` *is* item 3 of `rem:silva_hypotheses`,
  the domination assumption; the identity `p_T(x) = E_{τ∼p_B(·|x)}[p_F/p_B]` is not derived here
  and could not be without the graph.
* **The vocabulary is shared.** `tv`, `chiSq`, `unif`, `residual` and the identities about
  them alone (`chiSq_nonneg`, `sum_unif`, `sum_sq_div_eq_one_add_chiSq`) live in
  `GFNBoundsScaffold.Silva.Basic`, shared with the sibling file for `prop:silva_no_uniform`;
  this file defines only what its own three steps need. Total variation was called `TV` here
  before that merge and is `tv` now — the same function, and the statements below are otherwise
  unchanged.
* Nothing in this file is a `sorry`, and nothing else in the library depends on it.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒳` finite | ✓ `[Fintype X]`; nonemptiness derived from `hET_sum`, not assumed |
| trajectory space: finite pointed DAG, horizon `t_m`, acyclic | ⚠ weakened to `[Fintype T]`; not used — see SCOPE |
| `p_{E,T}` full support | ✓ `hET_pos`, with `hET_sum : ∑ p_{E,T} = 1` |
| `π` full support | ✓ `hπ_pos` |
| `π = R/Z` normalized | ⚠ **dropped**; unused by the proof, so the Lean statement is stronger |
| `p_F(τ) > 0` whenever `p_B(τ|x) > 0` | ✓ `hF_pos` |
| `p_B(·|x)` a probability law | ✓ `hB_nonneg`, `hB_sum` |
| `p_B(·|x)` dominates forward trajectories into `x` | ✓ `hdom`, taken as a hypothesis on `p_T` |
| `M := max p_F/p_B` over the support | ⚠ any upper bound `hM` in `tv_le_sqrt_residual`; the max itself in `tv_le_sqrt_residual_max` |
| `‖π‖_∞` | ⚠ any upper bound `hPinf`; the max itself in `tv_le_sqrt_residual_max` |
| `M' = max(M, ‖π‖_∞)` — the paper's correction to Silva et al.'s `M` | ✓ `max M Pinf`, and the proof needs it |
| mean value theorem for `exp` on `(−∞, log M']` | ⚠ replaced by `Real.log_le_sub_one_of_pos`; same constant, elementary |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Silva

/-! ## Step 1: change of measure

The vocabulary — `tv`, `chiSq`, `unif`, `residual` — and Step 1's identity
`sum_sq_div_eq_one_add_chiSq` (`∑ q²/p = 1 + χ²(q‖p)`, where the normalizations are consumed)
are in `GFNBoundsScaffold.Silva.Basic`, shared with the sibling file for
`prop:silva_no_uniform`. What is left here is Steps 2 and 3 and the proposition itself. -/

/-! ## Step 2: Jensen over backward trajectories -/

/-- For a probability weight `w` on a finite set, `(c − ∑ w f)² ≤ ∑ w (c − f)²`. With
`w = p_B(·|x)`, `f = p_F/p_B` and `c = π(x)` this is the second display of the proof of
`prop:silva_explicit`. -/
theorem sq_sub_weighted_le {T : Type*} [Fintype T] {w f : T → ℝ} {c : ℝ}
    (hw : ∀ τ, 0 ≤ w τ) (hw1 : ∑ τ, w τ = 1) :
    (c - ∑ τ, w τ * f τ) ^ 2 ≤ ∑ τ, w τ * (c - f τ) ^ 2 := by
  have hstep : c - ∑ τ, w τ * f τ = ∑ τ, w τ * (c - f τ) := by
    have : ∀ τ : T, w τ * (c - f τ) = w τ * c - w τ * f τ := fun τ => mul_sub _ _ _
    rw [Finset.sum_congr rfl fun τ _ => this τ, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1,
      one_mul]
  rw [hstep]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset T)
    (r := fun τ => w τ * (c - f τ)) (f := w) (g := fun τ => w τ * (c - f τ) ^ 2)
    (fun τ _ => hw τ) (fun τ _ => mul_nonneg (hw τ) (sq_nonneg _))
    (fun τ _ => le_of_eq (by ring))
  rwa [hw1, one_mul] at h

/-! ## Step 3: the log-Lipschitz step, with the paper's corrected constant -/

/-- `|a − b| ≤ C |log a − log b|` for `0 < a ≤ C` and `0 < b ≤ C`. This is the third display of
the proof of `prop:silva_explicit`; `C` is the paper's `M' = max(M, ‖π‖_∞)`, and the hypothesis
`b ≤ C` is exactly what is unavailable for `C = M`, since `π(x) ≤ M` is not implied by the
definition of `M` — item 5 of `rem:silva_hypotheses`. -/
theorem logLipschitz {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (haC : a ≤ C) (hbC : b ≤ C) :
    |a - b| ≤ C * |Real.log a - Real.log b| := by
  have aux : ∀ u v : ℝ, 0 < u → 0 < v → u ≤ v → v ≤ C →
      0 ≤ Real.log v - Real.log u ∧ v - u ≤ C * (Real.log v - Real.log u) := by
    intro u v hu hv huv hvC
    have hlog : Real.log u - Real.log v ≤ u / v - 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos hu hv)
      rwa [Real.log_div hu.ne' hv.ne'] at h
    have heq : u / v - 1 = -((v - u) / v) := by
      field_simp
      ring
    rw [heq] at hlog
    have h1 : (v - u) / v ≤ Real.log v - Real.log u := by linarith
    have hd : 0 ≤ (v - u) / v := div_nonneg (by linarith) hv.le
    have hnn : 0 ≤ Real.log v - Real.log u := le_trans hd h1
    refine ⟨hnn, ?_⟩
    have h2 : v * ((v - u) / v) = v - u := by field_simp
    have h3 : v * ((v - u) / v) ≤ v * (Real.log v - Real.log u) :=
      mul_le_mul_of_nonneg_left h1 hv.le
    have h4 : v * (Real.log v - Real.log u) ≤ C * (Real.log v - Real.log u) :=
      mul_le_mul_of_nonneg_right hvC hnn
    linarith
  rcases le_total a b with h | h
  · obtain ⟨hnn, hle⟩ := aux a b ha hb h hbC
    rw [abs_sub_comm a b, abs_sub_comm (Real.log a) (Real.log b),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a), abs_of_nonneg hnn]
    exact hle
  · obtain ⟨hnn, hle⟩ := aux b a hb ha h haC
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b), abs_of_nonneg hnn]
    exact hle

/-- The squared form used in the proof: `(a − b)² ≤ C² (log(a/b))²` for `0 < a ≤ C`,
`0 < b ≤ C`. -/
theorem sq_sub_le_sq_mul_log_sq {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (haC : a ≤ C)
    (hbC : b ≤ C) : (a - b) ^ 2 ≤ C ^ 2 * Real.log (a / b) ^ 2 := by
  have h := logLipschitz ha hb haC hbC
  have hC : 0 ≤ C := ha.le.trans haC
  have hnn : 0 ≤ C * |Real.log a - Real.log b| := mul_nonneg hC (abs_nonneg _)
  calc (a - b) ^ 2 = |a - b| ^ 2 := (sq_abs _).symm
    _ ≤ (C * |Real.log a - Real.log b|) ^ 2 := sq_le_sq' (by linarith [abs_nonneg (a - b)]) h
    _ = C ^ 2 * Real.log (a / b) ^ 2 := by
        rw [mul_pow, sq_abs, Real.log_div ha.ne' hb.ne']

/-! ## The proposition -/

/-- **`prop:silva_explicit`** (`silva_comparison.tex:29–39`), with `M` and `‖π‖_∞` presented as
upper bounds: if `p_{E,T}` and `π` have full support, `p_B(·|x)` is a probability law dominating
the forward trajectories into `x` (`hdom`), `p_F` is positive on the support of `p_B`, and
`p_F(τ)/p_B(τ|x) ≤ M`, `π ≤ Pinf`, then

`TV(p_T, π) ≤ (|𝒳|/2) · max(M, Pinf) · sqrt((1 + χ²(q_{E,T}‖p_{E,T})) · 𝓔(p_F))`.

`tv_le_sqrt_residual_max` is the instance in which `M` and `Pinf` are the paper's maxima. -/
theorem tv_le_sqrt_residual {X T : Type*} [Fintype X] [Fintype T]
    {pET π pT : X → ℝ} {pB : X → T → ℝ} {pF : T → ℝ} {M Pinf : ℝ}
    (hET_pos : ∀ x, 0 < pET x) (hET_sum : ∑ x, pET x = 1)
    (hπ_pos : ∀ x, 0 < π x)
    (hB_nonneg : ∀ x τ, 0 ≤ pB x τ) (hB_sum : ∀ x, ∑ τ, pB x τ = 1)
    (hF_pos : ∀ x τ, 0 < pB x τ → 0 < pF τ)
    (hdom : ∀ x, pT x = ∑ τ, pB x τ * (pF τ / pB x τ))
    (hM : ∀ x τ, 0 < pB x τ → pF τ / pB x τ ≤ M)
    (hPinf : ∀ x, π x ≤ Pinf) :
    tv pT π ≤ (Fintype.card X : ℝ) / 2 * max M Pinf *
      Real.sqrt ((1 + chiSq (unif X) pET) * residual pET π pB pF) := by
  classical
  -- `𝒳` is nonempty: otherwise `∑ p_{E,T} = 0 ≠ 1`.
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
    · exfalso
      haveI := Fintype.card_eq_zero_iff.mp h
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hET_sum
      exact zero_ne_one hET_sum
    · exact_mod_cast h
  obtain ⟨x0⟩ : Nonempty X := Fintype.card_pos_iff.mp (by exact_mod_cast hcard)
  have hC_pos : 0 < max M Pinf :=
    lt_of_lt_of_le (hπ_pos x0) ((hPinf x0).trans (le_max_right M Pinf))
  -- Step 2 and Step 3, combined pointwise in `x`.
  have hkey : ∀ x, |π x - pT x| ^ 2 ≤
      max M Pinf ^ 2 * ∑ τ, pB x τ * Real.log (pF τ / (π x * pB x τ)) ^ 2 := by
    intro x
    rw [sq_abs, hdom x]
    refine (sq_sub_weighted_le (w := pB x) (f := fun τ => pF τ / pB x τ) (c := π x)
      (fun τ => hB_nonneg x τ) (hB_sum x)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    rcases (hB_nonneg x τ).eq_or_lt with h | h
    · simp [← h]
    · have ha : 0 < pF τ / pB x τ := div_pos (hF_pos x τ h) h
      have haC : pF τ / pB x τ ≤ max M Pinf := (hM x τ h).trans (le_max_left M Pinf)
      have hbC : π x ≤ max M Pinf := (hPinf x).trans (le_max_right M Pinf)
      have h3 := sq_sub_le_sq_mul_log_sq ha (hπ_pos x) haC hbC
      rw [div_div, mul_comm (pB x τ) (π x)] at h3
      have h4 : (π x - pF τ / pB x τ) ^ 2 ≤
          max M Pinf ^ 2 * Real.log (pF τ / (π x * pB x τ)) ^ 2 := by
        calc (π x - pF τ / pB x τ) ^ 2 = (pF τ / pB x τ - π x) ^ 2 := by ring
          _ ≤ _ := h3
      have h5 : max M Pinf ^ 2 * (pB x τ * Real.log (pF τ / (π x * pB x τ)) ^ 2)
          = pB x τ * (max M Pinf ^ 2 * Real.log (pF τ / (π x * pB x τ)) ^ 2) := by ring
      rw [h5]
      exact mul_le_mul_of_nonneg_left h4 h.le
  -- Step 1: Cauchy–Schwarz against the change of measure `q = (q/p) · p`.
  have hCS : (∑ x, unif X x * |π x - pT x|) ^ 2 ≤
      (∑ x, unif X x ^ 2 / pET x) * ∑ x, pET x * |π x - pT x| ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun x _ => div_nonneg (sq_nonneg _) (hET_pos x).le)
      (fun x _ => mul_nonneg (hET_pos x).le (sq_nonneg _)) (fun x _ => le_of_eq ?_)
    have hx : pET x ≠ 0 := (hET_pos x).ne'
    field_simp
  have hchi : ∑ x, unif X x ^ 2 / pET x = 1 + chiSq (unif X) pET :=
    sum_sq_div_eq_one_add_chiSq hET_pos (sum_unif hcard.ne') hET_sum
  have hres : ∑ x, pET x * |π x - pT x| ^ 2 ≤
      max M Pinf ^ 2 * residual pET π pB pF := by
    rw [residual_eq]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc pET x * |π x - pT x| ^ 2
        ≤ pET x * (max M Pinf ^ 2 * ∑ τ, pB x τ * Real.log (pF τ / (π x * pB x τ)) ^ 2) :=
          mul_le_mul_of_nonneg_left (hkey x) (hET_pos x).le
      _ = max M Pinf ^ 2 * (pET x * ∑ τ, pB x τ * Real.log (pF τ / (π x * pB x τ)) ^ 2) := by
          ring
  have hsq : (∑ x, unif X x * |π x - pT x|) ^ 2 ≤
      max M Pinf ^ 2 * ((1 + chiSq (unif X) pET) * residual pET π pB pF) := by
    have hchi_nn : (0 : ℝ) ≤ 1 + chiSq (unif X) pET := by
      have := chiSq_nonneg (q := unif X) (p := pET) fun x => (hET_pos x).le
      linarith
    calc (∑ x, unif X x * |π x - pT x|) ^ 2
        ≤ (∑ x, unif X x ^ 2 / pET x) * ∑ x, pET x * |π x - pT x| ^ 2 := hCS
      _ = (1 + chiSq (unif X) pET) * ∑ x, pET x * |π x - pT x| ^ 2 := by rw [hchi]
      _ ≤ (1 + chiSq (unif X) pET) * (max M Pinf ^ 2 * residual pET π pB pF) :=
          mul_le_mul_of_nonneg_left hres hchi_nn
      _ = max M Pinf ^ 2 * ((1 + chiSq (unif X) pET) * residual pET π pB pF) := by ring
  have hS : ∑ x, unif X x * |π x - pT x| ≤
      max M Pinf * Real.sqrt ((1 + chiSq (unif X) pET) * residual pET π pB pF) := by
    have h := Real.le_sqrt_of_sq_le hsq
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC_pos.le] at h
  -- `TV(p_T,π) = (|𝒳|/2) E_{q}[φ]`.
  have hTV : tv pT π = (Fintype.card X : ℝ) / 2 * ∑ x, unif X x * |π x - pT x| := by
    have h1 : ∑ x, unif X x * |π x - pT x| =
        (Fintype.card X : ℝ)⁻¹ * ∑ x, |π x - pT x| := by
      simp only [unif, ← Finset.mul_sum]
    have h2 : ∑ x, |pT x - π x| = ∑ x, |π x - pT x| :=
      Finset.sum_congr rfl fun x _ => abs_sub_comm _ _
    rw [tv, h1, h2]
    field_simp
  rw [hTV]
  calc (Fintype.card X : ℝ) / 2 * ∑ x, unif X x * |π x - pT x|
      ≤ (Fintype.card X : ℝ) / 2 *
        (max M Pinf * Real.sqrt ((1 + chiSq (unif X) pET) * residual pET π pB pF)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by ring

/-- **`prop:silva_explicit` with the paper's own constants**: `M` is the maximum of
`p_F(τ)/p_B(τ|x)` over the support of `p_B`, and `‖π‖_∞` the maximum of `π`. The two
nonemptiness arguments are forced by `Finset.sup'`; both follow from the other hypotheses, and
neither is a restriction (see SCOPE). The paper's `‖π‖_∞` is the maximum of `π` because `π > 0`
is assumed. -/
theorem tv_le_sqrt_residual_max {X T : Type*} [Fintype X] [Fintype T]
    {pET π pT : X → ℝ} {pB : X → T → ℝ} {pF : T → ℝ}
    (hX : (Finset.univ : Finset X).Nonempty)
    (hsupp : ((Finset.univ : Finset (X × T)).filter fun p => 0 < pB p.1 p.2).Nonempty)
    (hET_pos : ∀ x, 0 < pET x) (hET_sum : ∑ x, pET x = 1)
    (hπ_pos : ∀ x, 0 < π x)
    (hB_nonneg : ∀ x τ, 0 ≤ pB x τ) (hB_sum : ∀ x, ∑ τ, pB x τ = 1)
    (hF_pos : ∀ x τ, 0 < pB x τ → 0 < pF τ)
    (hdom : ∀ x, pT x = ∑ τ, pB x τ * (pF τ / pB x τ)) :
    tv pT π ≤ (Fintype.card X : ℝ) / 2 *
      max (((Finset.univ : Finset (X × T)).filter fun p => 0 < pB p.1 p.2).sup' hsupp
            fun p => pF p.2 / pB p.1 p.2)
          ((Finset.univ : Finset X).sup' hX π) *
      Real.sqrt ((1 + chiSq (unif X) pET) * residual pET π pB pF) := by
  have hmem : ∀ x τ, 0 < pB x τ →
      (x, τ) ∈ (Finset.univ : Finset (X × T)).filter fun p => 0 < pB p.1 p.2 := by
    intro x τ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  exact tv_le_sqrt_residual hET_pos hET_sum hπ_pos hB_nonneg hB_sum hF_pos hdom
    (fun x τ h => Finset.le_sup' (f := fun p : X × T => pF p.2 / pB p.1 p.2) (hmem x τ h))
    (fun x => Finset.le_sup' (f := π) (Finset.mem_univ x))

end GFNBounds.Silva
