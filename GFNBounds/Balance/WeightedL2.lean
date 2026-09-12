import GFNBounds.Balance.Expansion
import GFNBounds.Balance.Discrete
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Weighted `L²(λ)` as an inner-product space, and the contraction at `H = g''(1)A^†M_wA`

**`theo:db_stable_frozen_full`** — statement `proofs.tex:592–602`, proof `proofs.tex:604–610`;
**both halves, instantiated at the paper's own `H` on a finite state space**, in place of the
abstract `H : E →L[ℝ] E` of `GFNBounds.Balance.stable_frozen_discrete` and
`GFNBounds.Balance.stable_frozen_decay`.
(The bold-backtick form of the label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (`theo:db_stable_frozen_full`, the discrete sentence) For discrete gradient descent with step
> `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}`, the contraction factor per step is `1 − εϱ`.

> (`theo:db_stable_frozen_full`, the display it contracts towards) Then along the linearized
> gradient flow of `𝓛_{g,ν}` at the balanced solution: the component `Πh_t` (the total flow
> normalization) is conserved, and
> `‖h_t − Πh_t‖_{L²(λ)} ≤ e^{−ϱ t}‖h_0 − Πh_0‖_{L²(λ)}`, with
> `ϱ := g''(1)w_min/B̂²`.

> (its proof, first line) Let `H := g''(1)A^†M_wA ⪰ 0`.

## The bridge, and why it was needed

The library had two disconnected worlds. Every finite-state statement lives on `V → ℝ` with the
unbundled `Graph.ipL2 lam` / `Graph.nrmL2 lam` / `Graph.meanL2 lam`; `stable_frozen_discrete`
and `stable_frozen_decay` live on an abstract real inner-product space with
`ContinuousLinearMap`s. Three files' SCOPE sections named the missing bridge as their blocker,
and it is why Theorem 9's decay was stated for an abstract operator rather than the paper's own
`H`.

The bridge is the **weighting map** `w_λ : a ↦ (√λ(x)·a(x))_x` into `EuclideanSpace ℝ V`. It is
a linear equivalence when `λ > 0`, and it carries `⟪·∣·⟫_λ` and `‖·‖_{L²(λ)}` to the Euclidean
inner product and norm on the nose (`inner_wtL2`, `norm_wtL2`). No new `InnerProductSpace`
instance is declared: an instance on `V → ℝ` would clash with Mathlib's sup-norm
`Pi.normedAddCommGroup`, and the weight is a parameter, so it could not be global anyway. `H`,
`Π` and `P` are then conjugated into bundled `→L[ℝ]` maps, continuity being free in finite
dimension.

## What is proved

| | |
|---|---|
| `wtL2`, `unwtL2`, `wtCLM` | the weighting, its inverse, and the bounded-operator form |
| `inner_wtL2`, `norm_wtL2` | `⟪w_λa, w_λb⟫ = ⟪a ∣ b⟫_λ` and `‖w_λa‖ = ‖a‖_{L²(λ)}` |
| `funAct_add`, `Adj_add`, `densAct_add`, `Aop_add`, `meanL2_add`, `linHess_add`, `linHess_smul` | the `map_add` face of the `Balance` operators, which the toolkit did not carry |
| `hessOp`, `meanOp`, `densOp` | the paper's `H`, `Π` and `P` as `EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V` |
| `meanOp_selfAdjoint`, `meanOp_idem` | `Π` is an orthogonal projection: self-adjointness is free, idempotence is where `∑_x λ(x) = 1` is spent |
| `hessOp_selfAdjoint`, `meanOp_hessOp`, `hessOp_upper`, `hessOp_coercive` | `Expansion`'s five `linHess_*` facts transported |
| `mixing_coercivity_finite` | `lem:sigma_mixing`'s coercivity on `V → ℝ`, from `GFNBounds.Core.Mixing.coercivity` at `densOp`, so `B̂` is the paper's `∑_{n≥0}‖P^n − Π‖` |
| `stable_frozen_discrete_finite` | **the deliverable**: `‖h_k^⊥‖ ≤ (1 − εϱ)^k‖h_0^⊥‖` at `H = g''(1)A^†M_wA`, `ϱ = g''(1)w_min/B̂²`, step condition `ε·4g''(1)‖w‖_{L^∞} ≤ 1` |
| `stable_frozen_discrete_mixing` | the same with `B̂ := Core.Mixing.B (densOp lam K) (meanOp lam)` |
| `stable_frozen_decay_finite` | the continuous half, likewise at the paper's `H` |
| `twoState_contraction_check` | the contraction evaluated on `Expansion`'s two-state chain, **attained at every `k`**, on a trajectory whose conserved component is `1` rather than `0` |

## Hypothesis checklist — `theo:db_stable_frozen_full` at the paper's `H`

| paper hypothesis | here |
|---|---|
| `H = g''(1)A^†M_wA` | ✓ **carried**, as `Expansion.linHess K lam w g2` conjugated by `w_λ`. This is what the file exists to fix: `H` is no longer abstract |
| `L²(λ)`, `λ` an invariant probability | ⚠ **restricted** to a `Fintype V` with `λ > 0` pointwise and `∑_x λ(x) = 1`. `Core.IsInvariant` supplies invariance and `λ ≥ 0`; the normalization and the strict positivity are separate hypotheses (`htot`, `hlam`) |
| `T` a Markov kernel | ✓ `Core.IsMarkov K` |
| `T` ergodic with summable `L²`-mixing, `B̂ := ∑_{n≥0}β̂_n < ∞` | ⚠ two forms. `stable_frozen_discrete_finite` takes the *conclusion* `‖h^⊥‖ ≤ B̂‖Ah‖` as `hmix`; `stable_frozen_discrete_mixing` takes `Core.Mixing (densOp lam K) (meanOp lam)` and derives it, so its `B̂` is the paper's mixing sum. Ergodicity itself is nowhere proved — summability is the hypothesis, as in `Core/Mixing.lean` |
| `w ≥ w_min > 0` | ⚠ **split**: `hwmin : ∀ x, w_min ≤ w x` and `hwmin0 : 0 ≤ w_min`. Strict positivity is not used; non-negativity is, to scale the mixing inequality |
| `‖w‖_{L^∞}` | ⚠ `hwsup : ∀ x, w x ≤ w_sup` and `0 ≤ w_sup` — a one-sided bound, which is what `Expansion.linHess_upper` consumes |
| `g''(1) > 0` | ⚠ **weakened** to `0 ≤ g2`. The conclusion is a growth bound rather than a contraction when `ϱ ≤ 0`, and no hypothesis rules that out |
| `ϱ := g''(1)w_min/B̂²` | ✓ **the explicit formula**, in the statement, not an abstract constant. `0 < B̂` is carried |
| `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}` | ✓ as `hepsL : ε·(4g''(1)w_sup) ≤ 1`, with `Λ = 4g''(1)‖w‖_{L^∞}` now **derived** from `Expansion.linHess_upper` rather than hypothesised. The paper's route `‖A‖ ≤ 2 ⇒ ‖H‖ ≤ 4g''(1)‖w‖_{L^∞}` is the operator-norm statement; what is used is its quadratic-form reading, which `linHess_upper` proves with the same `‖A‖ ≤ 2` |
| `ε ≥ 0`, `εϱ ≤ 1` | ⚠ **hypotheses** `heps`, `hrho`, inherited from `stable_frozen_discrete`; `hrho` is not in the paper's sentence |
| `ΠH = 0` "since `P^†` preserves integrals" | ✓ **proved**, `meanOp_hessOp` from `Expansion.meanL2_linHess` |
| `Π` the projection onto the invariant functions | ✓ **proved** self-adjoint and idempotent (`meanOp_selfAdjoint`, `meanOp_idem`); both were hypotheses in `stable_frozen_discrete` |
| `H ⪰ 0`, read by the proof as symmetry | ✓ **proved**, `hessOp_selfAdjoint` from `Expansion.linHess_symm`. `Discrete.lean` records that self-adjointness is load-bearing for the printed factor `1 − εϱ` and is nowhere named in the paper's proof; here it is a theorem about the paper's `H`, so the gap is closed rather than assumed away |
| the descent recursion `h_{k+1} = h_k − εHh_k` | ⚠ **hypothesised** (`hstep`), stated pointwise on `V → ℝ`. That gradient descent on `𝓛_{g,ν}` *is* this recursion is `theo:gd_diffusion_full`, which is not formalized |
| `Πh_k` conserved | ✓ first conjunct, as `Graph.meanL2 lam (h k) = Graph.meanL2 lam (h 0)` |
| contraction factor `1 − εϱ` per step | ✓ second conjunct, and `twoState_contraction_check` shows it attained |
| the linearized flow, `e^{−ϱt}` | ✓ `stable_frozen_decay_finite`, with the flow `ḣ = −Hh` hypothesised as in `Flow.lean` |
| via `lem:lift_mixing`, the FM and DB losses | ✗ **not stated**, here or anywhere |

## SCOPE (disclosed)

* **Finite state spaces only.** Everything below is a `Fintype V` with `λ > 0` pointwise. The
  general `L^p` layer with its adjoint remains **obstruction 2**
  (`kb/entries/0006-three-obstructions.md`): nothing here builds `L^p(λ)` on a measure space, an
  adjoint there, or an operator norm there. What is done is the *finite-dimensional face* of
  that obstruction, deliberately and at `p = 2` only.
* **No new `InnerProductSpace` instance.** `V → ℝ` keeps Mathlib's sup norm; the weighted
  structure is reached through the linear equivalence `wtL2`/`unwtL2` and the two bridge
  identities. There is therefore **no** `⟪·,·⟫` or `‖·‖` notation for `L²(λ)` on `V → ℝ`, and
  the statements below still read in `Graph.ipL2`/`Graph.nrmL2`. A type synonym carrying `λ`
  plus `InnerProductSpace.ofCore` would give that notation; it was not taken, because it would
  duplicate `EuclideanSpace`'s instance and force every existing `Graph.*` lemma to be
  restated on the synonym.
* **`λ > 0` pointwise is required and is not the paper's hypothesis.** The weighting is
  invertible only there. The paper's `L²(λ)` tolerates `λ`-null states (they are quotiented
  out); this file excludes them from `V`. `Core.IsInvariant` alone is not enough.
* **`∑_x λ(x) = 1` is required**, and is spent in exactly two places: `Π² = Π`
  (`meanOp_idem`) and the derivation of `Nonempty V` used to read a constant function back as a
  scalar. `Π` is self-adjoint without it.
* **The descent recursion, and the flow, are still hypothesised.** `H` is no longer abstract,
  but `hstep` and `hflow` assert that a *given* sequence or curve obeys the linearized
  dynamics. Producing them from `𝓛_{g,ν}` is `theo:gd_diffusion_full`, bucket `D`. So one of
  the two disclosures `Discrete.lean` and `Flow.lean` carry — "`H` is abstract" — is closed
  here, and the other — "the recursion is hypothesised, not produced" — is not.
* **The nonlinear upgrade is untouched.** `theo:local_convergence_full` needs Steps 2–5 and the
  bootstrap; only Step 1's expansion exists, in `Expansion.lean`.
* **`lem:lift_mixing`, hence the FM and DB losses, is not stated.**
* **`Core.Mixing (densOp lam K) (meanOp lam)` is never exhibited.** `stable_frozen_discrete_mixing`
  is only as non-vacuous as that bundle is inhabitable, and no instance of it is built. On the
  two-state chain of `twoState_contraction_check` the density action *is* the mean projection,
  so `β̂_0 = ‖I − Π‖` and `β̂_n = 0` for `n ≥ 1`, giving `B̂ = 1`; proving `‖I − Π‖ = 1` is an
  operator-norm computation that is not done, so the numerical check goes through
  `stable_frozen_discrete_finite` with the coercivity proved directly (`twoState_mixing`,
  `B̂ = 1` exactly) rather than through the mixing corollary.
* **`ϱ > 0` and `Λ ≥ 0` are not hypothesised**, following `Discrete.lean`. For `ϱ ≤ 0` the
  conclusion is a growth bound; the paper's `ϱ` is positive on its own hypotheses.
* **The operator norms `‖A‖ ≤ 2` and `‖H‖ ≤ 4g''(1)‖w‖_{L^∞}` are not proved as operator
  norms.** `hessOp`'s norm is never computed; only the quadratic-form bounds are used, which is
  all the argument needs and is strictly weaker than what the paper's sentence asserts.
* **`sorry`-free and axiom-clean.** `#print axioms` on `stable_frozen_discrete_finite`,
  `stable_frozen_discrete_mixing`, `stable_frozen_decay_finite`, `mixing_coercivity_finite` and
  `twoState_contraction_check` returns `[propext, Classical.choice, Quot.sound]`. This file is
  in the scaffold because graduation is the master session's decision, not because anything in
  it is open.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset
open scoped RealInnerProductSpace

variable {V : Type*}

/-! ### The weighting isometry -/

/-- `w_λ a := (√λ(x)·a(x))_x`, read into `EuclideanSpace ℝ V`. -/
noncomputable def wtL2 (lam a : V → ℝ) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun x => Real.sqrt (lam x) * a x)

@[simp] theorem wtL2_apply (lam a : V → ℝ) (x : V) :
    wtL2 lam a x = Real.sqrt (lam x) * a x := rfl

/-- The inverse weighting, `v ↦ (v(x)/√λ(x))_x`. -/
noncomputable def unwtL2 (lam : V → ℝ) (v : EuclideanSpace ℝ V) : V → ℝ :=
  fun x => v x / Real.sqrt (lam x)

@[simp] theorem unwtL2_apply (lam : V → ℝ) (v : EuclideanSpace ℝ V) (x : V) :
    unwtL2 lam v x = v x / Real.sqrt (lam x) := rfl

theorem unwtL2_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (a : V → ℝ) :
    unwtL2 lam (wtL2 lam a) = a := by
  funext x
  have hs : Real.sqrt (lam x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hlam x))
  rw [unwtL2_apply, wtL2_apply, mul_comm, mul_div_assoc, div_self hs, mul_one]

theorem wtL2_unwtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (v : EuclideanSpace ℝ V) :
    wtL2 lam (unwtL2 lam v) = v := by
  ext x
  have hs : Real.sqrt (lam x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hlam x))
  rw [wtL2_apply, unwtL2_apply, mul_div_cancel₀ _ hs]

theorem exists_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (v : EuclideanSpace ℝ V) :
    ∃ a : V → ℝ, wtL2 lam a = v :=
  ⟨unwtL2 lam v, wtL2_unwtL2 hlam v⟩

variable [Fintype V]

/-! ### The two bridge identities -/

theorem inner_wtL2 {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a b : V → ℝ) :
    ⟪wtL2 lam a, wtL2 lam b⟫ = Graph.ipL2 lam a b := by
  rw [PiLp.inner_apply]
  simp only [wtL2_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial, Graph.ipL2]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hs : Real.sqrt (lam x) * Real.sqrt (lam x) = lam x :=
    Real.mul_self_sqrt (hnn x)
  linear_combination (a x * b x) * hs

theorem norm_wtL2 {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a : V → ℝ) :
    ‖wtL2 lam a‖ = Graph.nrmL2 lam a := by
  have h := inner_wtL2 hnn a a
  rw [real_inner_self_eq_norm_sq] at h
  rw [Graph.nrmL2, ← h, Real.sqrt_sq (norm_nonneg _)]


/-! ### Linearity: what the toolkit carries, and the `map_add` it does not -/

/-- `P†(a + b) = P†a + P†b`. The toolkit has only the `sub` and `smul` faces. -/
theorem funAct_add (K : V → V → ℝ) (a b : V → ℝ) :
    funAct K (fun y => a y + b y) = fun x => funAct K a x + funAct K b x := by
  funext x
  simp only [funAct]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- `A†(a + b) = A†a + A†b`. -/
theorem Adj_add (K : V → V → ℝ) (a b : V → ℝ) (x : V) :
    Adj K (fun y => a y + b y) x = Adj K a x + Adj K b x := by
  simp only [Adj_apply, funAct_add]
  ring

/-- `P(a + b) = Pa + Pb`, at every state and with no hypothesis. -/
theorem densAct_add (lam : V → ℝ) (K : V → V → ℝ) (a b : V → ℝ) (y : V) :
    Core.densAct lam K (fun x => a x + b x) y
      = Core.densAct lam K a y + Core.densAct lam K b y := by
  simp only [Core.densAct_apply]
  rw [← add_div, ← Finset.sum_add_distrib]
  exact congrArg (· / lam y) (Finset.sum_congr rfl fun x _ => by ring)

/-- `A(a + b) = Aa + Ab`. -/
theorem Aop_add (lam : V → ℝ) (K : V → V → ℝ) (a b : V → ℝ) (y : V) :
    Aop K lam (fun x => a x + b x) y = Aop K lam a y + Aop K lam b y := by
  rw [Aop_apply, Aop_apply, Aop_apply, densAct_add]
  ring

/-- `Π(a + b) = Πa + Πb`. -/
theorem meanL2_add (lam a b : V → ℝ) :
    Graph.meanL2 lam (fun x => a x + b x) = Graph.meanL2 lam a + Graph.meanL2 lam b := by
  simp only [Graph.meanL2]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `H(a + b) = Ha + Hb`. -/
theorem linHess_add (K : V → V → ℝ) (lam w : V → ℝ) (g2 : ℝ) (a b : V → ℝ) :
    linHess K lam w g2 (fun x => a x + b x)
      = fun x => linHess K lam w g2 a x + linHess K lam w g2 b x := by
  funext x
  have hw : (fun y => w y * Aop K lam (fun z => a z + b z) y)
      = fun y => w y * Aop K lam a y + w y * Aop K lam b y := by
    funext y; rw [Aop_add]; ring
  rw [linHess_apply, hw, Adj_add, linHess_apply, linHess_apply]
  ring

/-- `H(c·a) = c·Ha`. -/
theorem linHess_smul (K : V → V → ℝ) (lam w : V → ℝ) (g2 c : ℝ) (a : V → ℝ) :
    linHess K lam w g2 (fun x => c * a x) = fun x => c * linHess K lam w g2 a x := by
  funext x
  have hw : (fun y => w y * Aop K lam (fun z => c * a z) y)
      = fun y => c * (w y * Aop K lam a y) := by
    funext y; rw [Aop_smul]; ring
  rw [linHess_apply, hw, Adj_smul, linHess_apply]
  ring

/-! ### The weighting is linear -/

omit [Fintype V] in
theorem wtL2_add (lam a b : V → ℝ) :
    wtL2 lam (fun x => a x + b x) = wtL2 lam a + wtL2 lam b := by
  ext x
  simp only [wtL2_apply, PiLp.add_apply]
  ring

omit [Fintype V] in
theorem wtL2_smul (lam : V → ℝ) (c : ℝ) (a : V → ℝ) :
    wtL2 lam (fun x => c * a x) = c • wtL2 lam a := by
  ext x
  simp only [wtL2_apply, PiLp.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] in
theorem wtL2_sub (lam a b : V → ℝ) :
    wtL2 lam (fun x => a x - b x) = wtL2 lam a - wtL2 lam b := by
  ext x
  simp only [wtL2_apply, PiLp.sub_apply]
  ring

omit [Fintype V] in
theorem wtL2_neg (lam a : V → ℝ) : wtL2 lam (fun x => -a x) = -wtL2 lam a := by
  ext x
  simp only [wtL2_apply, PiLp.neg_apply, mul_neg]

omit [Fintype V] in
theorem unwtL2_add (lam : V → ℝ) (u v : EuclideanSpace ℝ V) :
    unwtL2 lam (u + v) = fun x => unwtL2 lam u x + unwtL2 lam v x := by
  funext x
  simp only [unwtL2_apply, PiLp.add_apply]
  ring

omit [Fintype V] in
theorem unwtL2_smul (lam : V → ℝ) (c : ℝ) (v : EuclideanSpace ℝ V) :
    unwtL2 lam (c • v) = fun x => c * unwtL2 lam v x := by
  funext x
  simp only [unwtL2_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ### `H` and `Π` as bundled operators on `EuclideanSpace ℝ V` -/

/-- The paper's `H = g''(1)A^†M_wA`, conjugated by the weighting, as a linear map. -/
noncomputable def hessLin (K : V → V → ℝ) (lam w : V → ℝ) (g2 : ℝ) :
    EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V where
  toFun v := wtL2 lam (linHess K lam w g2 (unwtL2 lam v))
  map_add' u v := by
    show wtL2 lam (linHess K lam w g2 (unwtL2 lam (u + v))) = _
    rw [unwtL2_add, linHess_add, wtL2_add]
  map_smul' c v := by
    show wtL2 lam (linHess K lam w g2 (unwtL2 lam (c • v))) = _
    rw [unwtL2_smul, linHess_smul, wtL2_smul]
    rfl

/-- The paper's `H`, bundled: continuity is free in finite dimension. -/
noncomputable def hessOp (K : V → V → ℝ) (lam w : V → ℝ) (g2 : ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  LinearMap.toContinuousLinearMap (hessLin K lam w g2)

theorem hessOp_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (K : V → V → ℝ) (w : V → ℝ)
    (g2 : ℝ) (a : V → ℝ) :
    hessOp K lam w g2 (wtL2 lam a) = wtL2 lam (linHess K lam w g2 a) := by
  show wtL2 lam (linHess K lam w g2 (unwtL2 lam (wtL2 lam a))) = _
  rw [unwtL2_wtL2 hlam]

/-- The mean projection `Π h = (∫ h dλ)·𝟙`, conjugated by the weighting, as a linear map. -/
noncomputable def meanLin (lam : V → ℝ) :
    EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V where
  toFun v := wtL2 lam (fun _ => Graph.meanL2 lam (unwtL2 lam v))
  map_add' u v := by
    show wtL2 lam (fun _ => Graph.meanL2 lam (unwtL2 lam (u + v))) = _
    rw [unwtL2_add, meanL2_add, ← wtL2_add]
  map_smul' c v := by
    show wtL2 lam (fun _ => Graph.meanL2 lam (unwtL2 lam (c • v))) = _
    rw [unwtL2_smul, meanL2_const_mul, ← wtL2_smul]
    rfl

/-- `Π`, bundled. -/
noncomputable def meanOp (lam : V → ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  LinearMap.toContinuousLinearMap (meanLin lam)

theorem meanOp_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (a : V → ℝ) :
    meanOp lam (wtL2 lam a) = wtL2 lam (fun _ => Graph.meanL2 lam a) := by
  show wtL2 lam (fun _ => Graph.meanL2 lam (unwtL2 lam (wtL2 lam a))) = _
  rw [unwtL2_wtL2 hlam]


/-! ### Two scalar identities the projection needs -/

/-- `⟪c·𝟙 ∣ b⟫_λ = c·Πb`. -/
theorem ipL2_const_left (lam b : V → ℝ) (c : ℝ) :
    Graph.ipL2 lam (fun _ => c) b = c * Graph.meanL2 lam b := by
  simp only [Graph.ipL2, Graph.meanL2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `Π(c·𝟙) = c` when `λ` is a probability. -/
theorem meanL2_const {lam : V → ℝ} (htot : ∑ x, lam x = 1) (c : ℝ) :
    Graph.meanL2 lam (fun _ => c) = c := by
  simp only [Graph.meanL2, ← Finset.sum_mul, htot, one_mul]

omit [Fintype V] in
theorem wtL2_zero (lam : V → ℝ) : wtL2 lam (fun _ => 0) = 0 := by
  ext x
  simp only [wtL2_apply, mul_zero, PiLp.zero_apply]

omit [Fintype V] in
theorem wtL2_injective {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) :
    Function.Injective (wtL2 lam) := by
  intro a b hab
  rw [← unwtL2_wtL2 hlam a, ← unwtL2_wtL2 hlam b, hab]

/-! ### The five hypotheses of `stable_frozen_discrete`, discharged at the paper's `H` -/

/-- `⟪a ∣ Hb⟫_λ` read through the weighting. -/
theorem inner_hessOp {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (hnn : ∀ x, 0 ≤ lam x)
    (K : V → V → ℝ) (w : V → ℝ) (g2 : ℝ) (a b : V → ℝ) :
    ⟪wtL2 lam a, hessOp K lam w g2 (wtL2 lam b)⟫
      = Graph.ipL2 lam a (linHess K lam w g2 b) := by
  rw [hessOp_wtL2 hlam, inner_wtL2 hnn]

/-- **`Π` is self-adjoint** for `⟪·∣·⟫_λ` — `stable_frozen_discrete`'s `hPisa`. No hypothesis on
`λ` beyond positivity: both sides are `Πa · Πb`. -/
theorem meanOp_selfAdjoint {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (hnn : ∀ x, 0 ≤ lam x)
    (u v : EuclideanSpace ℝ V) :
    ⟪meanOp lam u, v⟫ = ⟪u, meanOp lam v⟫ := by
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  obtain ⟨b, rfl⟩ := exists_wtL2 hlam v
  rw [meanOp_wtL2 hlam, meanOp_wtL2 hlam, inner_wtL2 hnn, inner_wtL2 hnn,
    ipL2_const_left, ipL2_comm, ipL2_const_left]
  ring

/-- **`Π² = Π`** — `stable_frozen_discrete`'s `hPiPi`. This is where `∑_x λ(x) = 1` is spent. -/
theorem meanOp_idem {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1)
    (u : EuclideanSpace ℝ V) : meanOp lam (meanOp lam u) = meanOp lam u := by
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  rw [meanOp_wtL2 hlam, meanOp_wtL2 hlam, meanL2_const htot]

/-- **`H` is self-adjoint** — `stable_frozen_discrete`'s `hHsa`, from `Expansion.linHess_symm`. -/
theorem hessOp_selfAdjoint {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hKnn : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) (w : V → ℝ) (g2 : ℝ)
    (u v : EuclideanSpace ℝ V) :
    ⟪hessOp K lam w g2 u, v⟫ = ⟪u, hessOp K lam w g2 v⟫ := by
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  obtain ⟨b, rfl⟩ := exists_wtL2 hlam v
  rw [hessOp_wtL2 hlam, inner_wtL2 hinv.nonneg, inner_hessOp hlam hinv.nonneg,
    linHess_symm hinv hKnn w g2 a b]

/-- **`ΠH = 0`** — `stable_frozen_discrete`'s `hPiH`, from `Expansion.meanL2_linHess`. -/
theorem meanOp_hessOp {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (w : V → ℝ) (g2 : ℝ) (u : EuclideanSpace ℝ V) :
    meanOp lam (hessOp K lam w g2 u) = 0 := by
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  rw [hessOp_wtL2 hlam, meanOp_wtL2 hlam,
    meanL2_linHess (invariant_of_isInvariant hinv) w g2 a, wtL2_zero]

/-- **`u − Πu` is the weighting of `h^⊥`.** -/
theorem sub_meanOp_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (a : V → ℝ) :
    wtL2 lam a - meanOp lam (wtL2 lam a) = wtL2 lam (perpL2 lam a) := by
  rw [meanOp_wtL2 hlam, perpL2_eq, wtL2_sub]

/-- **`⟪u ∣ Hu⟫ ≤ 4g''(1)‖w‖_∞‖u‖²`** — `stable_frozen_discrete`'s `hup`, from
`Expansion.linHess_upper`. -/
theorem hessOp_upper {K : V → V → ℝ} {lam : V → ℝ} (hK : Core.IsMarkov K)
    (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x) {w : V → ℝ} {g2 wsup : ℝ}
    (hw : ∀ x, w x ≤ wsup) (hg2 : 0 ≤ g2) (hwsup0 : 0 ≤ wsup) (u : EuclideanSpace ℝ V) :
    ⟪u, hessOp K lam w g2 u⟫ ≤ 4 * g2 * wsup * ‖u‖ ^ 2 := by
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  rw [inner_hessOp hlam hinv.nonneg, norm_wtL2 hinv.nonneg]
  exact linHess_upper hK hinv hw hg2 hwsup0 a

/-- **`(g''(1)w_min/B̂²)‖u − Πu‖² ≤ ⟪u ∣ Hu⟫`** — `stable_frozen_discrete`'s `hcoer`, from
`Expansion.linHess_coercive` composed with the mixing coercivity `‖h^⊥‖ ≤ B̂‖Ah‖`
(`lem:sigma_mixing`, hypothesised here in its finite-state form). -/
theorem hessOp_coercive {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hKnn : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) {w : V → ℝ} {g2 wmin Bhat : ℝ}
    (hw : ∀ x, wmin ≤ w x) (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hBhat : 0 < Bhat)
    (hmix : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (u : EuclideanSpace ℝ V) :
    g2 * wmin / Bhat ^ 2 * ‖u - meanOp lam u‖ ^ 2 ≤ ⟪u, hessOp K lam w g2 u⟫ := by
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  rw [sub_meanOp_wtL2 hlam, norm_wtL2 hinv.nonneg, inner_hessOp hlam hinv.nonneg]
  have hco := linHess_coercive hinv hKnn hw hg2 a
  have hp := hmix a
  have hp0 : 0 ≤ Graph.nrmL2 lam (perpL2 lam a) := Graph.nrmL2_nonneg _ _
  have hA0 : 0 ≤ Graph.nrmL2 lam (Aop K lam a) := Graph.nrmL2_nonneg _ _
  have hsq : Graph.nrmL2 lam (perpL2 lam a) ^ 2
      ≤ Bhat ^ 2 * Graph.nrmL2 lam (Aop K lam a) ^ 2 := by nlinarith [hp, hp0, hA0]
  have hgw : 0 ≤ g2 * wmin := mul_nonneg hg2 hwmin0
  have hB2 : (0 : ℝ) < Bhat ^ 2 := by positivity
  have hstep : g2 * wmin / Bhat ^ 2 * Graph.nrmL2 lam (perpL2 lam a) ^ 2
      ≤ g2 * wmin * Graph.nrmL2 lam (Aop K lam a) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hB2]
    nlinarith [hsq, hgw]
  exact hstep.trans hco


/-! ### `P` as an operator, and `B̂` as the paper's mixing sum

`lem:sigma_mixing` is already proved, on a Banach space, in `GFNBounds/Core/Mixing.lean`. Its
`P` is a `ContinuousLinearMap`; the finite-state `P` is `Core.densAct`. Conjugating the latter
by the weighting closes the last gap, so that the `B̂` of the contraction below is literally
`Core.Mixing.B`, the paper's `∑_{n≥0} β̂_n`, and not an abstract constant. -/

/-- `Π P = Π`: the density action preserves `λ`-integrals. -/
theorem meanL2_densAct {K : V → V → ℝ} {lam : V → ℝ} (hK : Core.IsMarkov K)
    (hlam : ∀ x, 0 < lam x) (a : V → ℝ) :
    Graph.meanL2 lam (Core.densAct lam K a) = Graph.meanL2 lam a := by
  have h1 : ∀ y : V, lam y * Core.densAct lam K a y = ∑ x, lam x * K x y * a x := by
    intro y
    rw [Core.densAct_apply, mul_comm, div_mul_cancel₀ _ (hlam y).ne']
  calc Graph.meanL2 lam (Core.densAct lam K a)
      = ∑ y, ∑ x, lam x * K x y * a x := by
        simp only [Graph.meanL2]
        exact Finset.sum_congr rfl fun y _ => h1 y
    _ = ∑ x, ∑ y, lam x * K x y * a x := Finset.sum_comm
    _ = ∑ x, lam x * a x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hx : ∑ y, lam x * K x y * a x = lam x * a x * ∑ y, K x y := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [hx, hK.row_sum x, mul_one]
    _ = Graph.meanL2 lam a := rfl

/-- The density action `P`, conjugated by the weighting, as a linear map. -/
noncomputable def densLin (lam : V → ℝ) (K : V → V → ℝ) :
    EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V where
  toFun v := wtL2 lam (Core.densAct lam K (unwtL2 lam v))
  map_add' u v := by
    show wtL2 lam (Core.densAct lam K (unwtL2 lam (u + v))) = _
    rw [unwtL2_add, show Core.densAct lam K
        (fun x => unwtL2 lam u x + unwtL2 lam v x)
          = fun y => Core.densAct lam K (unwtL2 lam u) y
              + Core.densAct lam K (unwtL2 lam v) y from
        funext fun y => densAct_add lam K _ _ y, wtL2_add]
  map_smul' c v := by
    show wtL2 lam (Core.densAct lam K (unwtL2 lam (c • v))) = _
    rw [unwtL2_smul, show Core.densAct lam K (fun x => c * unwtL2 lam v x)
        = fun y => c * Core.densAct lam K (unwtL2 lam v) y from
        funext fun y => densAct_smul lam K c _ y, wtL2_smul]
    rfl

/-- `P`, bundled. -/
noncomputable def densOp (lam : V → ℝ) (K : V → V → ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  LinearMap.toContinuousLinearMap (densLin lam K)

theorem densOp_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (K : V → V → ℝ) (a : V → ℝ) :
    densOp lam K (wtL2 lam a) = wtL2 lam (Core.densAct lam K a) := by
  show wtL2 lam (Core.densAct lam K (unwtL2 lam (wtL2 lam a))) = _
  rw [unwtL2_wtL2 hlam]

/-- **`ΠP = Π`** — `Core.Mixing`'s `proj_left`. -/
theorem meanOp_mul_densOp {K : V → V → ℝ} {lam : V → ℝ} (hK : Core.IsMarkov K)
    (hlam : ∀ x, 0 < lam x) : meanOp lam * densOp lam K = meanOp lam := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  show meanOp lam (densOp lam K (wtL2 lam a)) = meanOp lam (wtL2 lam a)
  rw [densOp_wtL2 hlam, meanOp_wtL2 hlam, meanOp_wtL2 hlam, meanL2_densAct hK hlam]

/-- **`PΠ = Π`** — `Core.Mixing`'s `proj_right`; `P` fixes the constants, `λ` being invariant. -/
theorem densOp_mul_meanOp {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) : densOp lam K * meanOp lam = meanOp lam := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  show densOp lam K (meanOp lam (wtL2 lam a)) = meanOp lam (wtL2 lam a)
  rw [meanOp_wtL2 hlam, densOp_wtL2 hlam,
    show Core.densAct lam K (fun _ => Graph.meanL2 lam a)
        = fun _ => Graph.meanL2 lam a from
      funext fun y => densAct_const hinv _ (hlam y).ne']

/-- **`(I − P)h` is `−Ah`**, so `‖(I − P)h‖ = ‖Ah‖_{L²(λ)}`. -/
theorem one_sub_densOp_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (K : V → V → ℝ) (f : V → ℝ) :
    (1 - densOp lam K) (wtL2 lam f) = -wtL2 lam (Aop K lam f) := by
  have hA : (fun x => -Aop K lam f x) = fun x => f x - Core.densAct lam K f x := by
    funext x
    rw [Aop_apply]
    ring
  rw [sub_apply, one_apply_eq_self, densOp_wtL2 hlam, ← wtL2_neg, hA, wtL2_sub]

/-- **`lem:sigma_mixing` on a finite state space**: `‖h^⊥‖_{L²(λ)} ≤ B̂‖Ah‖_{L²(λ)}` with
`B̂ = ∑_{n≥0}‖P^n − Π‖` the paper's mixing sum, read off `GFNBounds.Core.Mixing.coercivity`
through the weighting. This is what `stable_frozen_discrete_finite`'s `hmix` hypothesis asks
for, and it is now derived rather than assumed once summable mixing is granted. -/
theorem mixing_coercivity_finite {K : V → V → ℝ} {lam : V → ℝ}
    (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam)) (f : V → ℝ) :
    Graph.nrmL2 lam (perpL2 lam f)
      ≤ Core.Mixing.B (densOp lam K) (meanOp lam) * Graph.nrmL2 lam (Aop K lam f) := by
  have hco := hmx.coercivity (wtL2 lam f)
  rwa [sub_meanOp_wtL2 hlam, norm_wtL2 hinv.nonneg, one_sub_densOp_wtL2 hlam, norm_neg,
    norm_wtL2 hinv.nonneg] at hco

/-! ### The payoff: `theo:db_stable_frozen_full`'s discrete half at the paper's `H` -/

/-- **`theo:db_stable_frozen_full`, the discrete half, at `H = g''(1)A^†M_wA` on a finite state
space** (statement `proofs.tex:592–602`, proof `proofs.tex:604–610`).

Along the descent recursion `h_{k+1} = h_k − εHh_k` with `H` the paper's operator, the total-flow
normalization `Πh_k` is conserved and
`‖h_k^⊥‖_{L²(λ)} ≤ (1 − εϱ)^k ‖h_0^⊥‖_{L²(λ)}` with **`ϱ = g''(1)w_min/B̂²`** and the paper's step
condition `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}` in the form `ε·4g''(1)‖w‖_{L^∞} ≤ 1`.

Nothing is abstract here but `B̂`: `hmix` is `lem:sigma_mixing`'s conclusion
`‖h^⊥‖ ≤ B̂‖Ah‖` in the finite-state language, and every other hypothesis of
`GFNBounds.Balance.stable_frozen_discrete` is discharged from `Expansion`'s five `linHess_*`
facts through the weighting isometry `wtL2`. -/
theorem stable_frozen_discrete_finite
    {K : V → V → ℝ} {lam w : V → ℝ} {g2 wmin wsup Bhat eps : ℝ} {h : ℕ → V → ℝ}
    (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hwsup : ∀ x, w x ≤ wsup) (hwsup0 : 0 ≤ wsup) (hBhat : 0 < Bhat)
    (hmix : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (heps : 0 ≤ eps) (hepsL : eps * (4 * g2 * wsup) ≤ 1)
    (hrho : eps * (g2 * wmin / Bhat ^ 2) ≤ 1)
    (hstep : ∀ k x, h (k + 1) x = h k x - eps * linHess K lam w g2 (h k) x) :
    (∀ k, Graph.meanL2 lam (h k) = Graph.meanL2 lam (h 0)) ∧
      ∀ k, Graph.nrmL2 lam (perpL2 lam (h k))
        ≤ (1 - eps * (g2 * wmin / Bhat ^ 2)) ^ k * Graph.nrmL2 lam (perpL2 lam (h 0)) := by
  have hne : Nonempty V := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    simp at htot
  obtain ⟨x0⟩ := hne
  have hstepv : ∀ k, wtL2 lam (h (k + 1))
      = wtL2 lam (h k) - eps • hessOp K lam w g2 (wtL2 lam (h k)) := by
    intro k
    have hfun : h (k + 1) = fun x => h k x - eps * linHess K lam w g2 (h k) x :=
      funext (hstep k)
    rw [hfun, wtL2_sub, wtL2_smul, hessOp_wtL2 hlam]
  have key := stable_frozen_discrete
    (E := EuclideanSpace ℝ V) (H := hessOp K lam w g2) (Pi := meanOp lam)
    (rho := g2 * wmin / Bhat ^ 2) (Lam := 4 * g2 * wsup) (eps := eps)
    (h := fun k => wtL2 lam (h k))
    (meanOp_selfAdjoint hlam hinv.nonneg)
    (meanOp_idem hlam htot)
    (hessOp_selfAdjoint hinv hK.nonneg hlam w g2)
    (meanOp_hessOp hinv hlam w g2)
    (hessOp_coercive hinv hK.nonneg hlam hwmin hg2 hwmin0 hBhat hmix)
    (hessOp_upper hK hinv hlam hwsup hg2 hwsup0)
    heps hepsL hrho hstepv
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have hc := key.1 k
    rw [meanOp_wtL2 hlam, meanOp_wtL2 hlam] at hc
    exact congrFun (wtL2_injective hlam hc) x0
  · have hb := key.2 k
    rw [sub_meanOp_wtL2 hlam, sub_meanOp_wtL2 hlam, norm_wtL2 hinv.nonneg,
      norm_wtL2 hinv.nonneg] at hb
    exact hb


/-- **`theo:db_stable_frozen_full`, the discrete half, with `B̂` the paper's mixing sum.**
`stable_frozen_discrete_finite` with its one remaining abstract input discharged: `hmix` comes
from `GFNBounds.Core.Mixing` at the conjugated density action, so `ϱ = g''(1)w_min/B̂²` with
`B̂ = ∑_{n≥0}‖P^n − Π‖` exactly as the theorem defines it. Summable mixing — the paper's "`T`
ergodic with summable `L²`-mixing" — is the hypothesis `hmx`, and `0 < B̂` is carried. -/
theorem stable_frozen_discrete_mixing
    {K : V → V → ℝ} {lam w : V → ℝ} {g2 wmin wsup eps : ℝ} {h : ℕ → V → ℝ}
    (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hwsup : ∀ x, w x ≤ wsup) (hwsup0 : 0 ≤ wsup)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam))
    (hBpos : 0 < Core.Mixing.B (densOp lam K) (meanOp lam))
    (heps : 0 ≤ eps) (hepsL : eps * (4 * g2 * wsup) ≤ 1)
    (hrho : eps * (g2 * wmin / Core.Mixing.B (densOp lam K) (meanOp lam) ^ 2) ≤ 1)
    (hstep : ∀ k x, h (k + 1) x = h k x - eps * linHess K lam w g2 (h k) x) :
    (∀ k, Graph.meanL2 lam (h k) = Graph.meanL2 lam (h 0)) ∧
      ∀ k, Graph.nrmL2 lam (perpL2 lam (h k))
        ≤ (1 - eps * (g2 * wmin / Core.Mixing.B (densOp lam K) (meanOp lam) ^ 2)) ^ k
          * Graph.nrmL2 lam (perpL2 lam (h 0)) :=
  stable_frozen_discrete_finite hK hinv hlam htot hg2 hwmin0 hwmin hwsup hwsup0 hBpos
    (mixing_coercivity_finite hinv hlam hmx) heps hepsL hrho hstep

/-! ### The bonus: the continuous half at the paper's `H` -/

/-- The weighting as a linear map, so that a curve's derivative transports through it. -/
noncomputable def wtLin (lam : V → ℝ) : (V → ℝ) →ₗ[ℝ] EuclideanSpace ℝ V where
  toFun := wtL2 lam
  map_add' a b := wtL2_add lam a b
  map_smul' c a := wtL2_smul lam c a

/-- The weighting as a bounded operator; continuity is free in finite dimension. -/
noncomputable def wtCLM (lam : V → ℝ) : (V → ℝ) →L[ℝ] EuclideanSpace ℝ V :=
  LinearMap.toContinuousLinearMap (wtLin lam)

theorem wtCLM_apply (lam a : V → ℝ) : wtCLM lam a = wtL2 lam a := rfl

/-- **`theo:db_stable_frozen_full`, the continuous half, at `H = g''(1)A^†M_wA` on a finite state
space** (statement `proofs.tex:592–602`, proof `proofs.tex:604–610`). The sibling of
`stable_frozen_discrete_finite`, obtained by the same bridge from
`GFNBounds.Balance.stable_frozen_decay`: along `ḣ = −Hh` the normalization `Πh_t` is conserved
and `‖h_t^⊥‖_{L²(λ)} ≤ e^{−ϱt}‖h_0^⊥‖_{L²(λ)}` with `ϱ = g''(1)w_min/B̂²`. The flow is
hypothesised, not produced — as in `Flow.lean`. -/
theorem stable_frozen_decay_finite
    {K : V → V → ℝ} {lam w : V → ℝ} {g2 wmin Bhat : ℝ} {h : ℝ → V → ℝ}
    (hinv : Core.IsInvariant lam K) (hKnn : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1)
    (hg2 : 0 ≤ g2) (hwmin0 : 0 ≤ wmin) (hwmin : ∀ x, wmin ≤ w x) (hBhat : 0 < Bhat)
    (hmix : ∀ f : V → ℝ,
      Graph.nrmL2 lam (perpL2 lam f) ≤ Bhat * Graph.nrmL2 lam (Aop K lam f))
    (hflow : ∀ t : ℝ, HasDerivAt h (fun x => -(linHess K lam w g2 (h t) x)) t) :
    (∀ t : ℝ, Graph.meanL2 lam (h t) = Graph.meanL2 lam (h 0)) ∧
      ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (perpL2 lam (h t))
        ≤ Real.exp (-(g2 * wmin / Bhat ^ 2 * t)) * Graph.nrmL2 lam (perpL2 lam (h 0)) := by
  have hne : Nonempty V := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    simp at htot
  obtain ⟨x0⟩ := hne
  have hflowv : ∀ t : ℝ, HasDerivAt (fun s => wtL2 lam (h s))
      (-hessOp K lam w g2 (wtL2 lam (h t))) t := by
    intro t
    have hcomp := ((wtCLM lam).hasFDerivAt (x := h t)).comp_hasDerivAt t (hflow t)
    have hval : (wtCLM lam) (fun x => -(linHess K lam w g2 (h t) x))
        = -hessOp K lam w g2 (wtL2 lam (h t)) := by
      rw [wtCLM_apply, wtL2_neg, hessOp_wtL2 hlam]
    rwa [hval] at hcomp
  have key := stable_frozen_decay
    (E := EuclideanSpace ℝ V) (H := hessOp K lam w g2) (Pi := meanOp lam)
    (rho := g2 * wmin / Bhat ^ 2) (h := fun s => wtL2 lam (h s))
    (meanOp_selfAdjoint hlam hinv.nonneg)
    (meanOp_hessOp hinv hlam w g2)
    (hessOp_coercive hinv hKnn hlam hwmin hg2 hwmin0 hBhat hmix)
    hflowv
  refine ⟨fun t => ?_, fun t ht => ?_⟩
  · have hc := key.1 t
    rw [meanOp_wtL2 hlam, meanOp_wtL2 hlam] at hc
    exact congrFun (wtL2_injective hlam hc) x0
  · have hb := key.2 t ht
    rw [sub_meanOp_wtL2 hlam, sub_meanOp_wtL2 hlam, norm_wtL2 hinv.nonneg,
      norm_wtL2 hinv.nonneg] at hb
    exact hb

/-! ### The contraction, computed on the two-state chain

`Expansion.lean`'s instance — `T(i→j) = 1/2`, `λ = (1/2, 1/2)`, `w ≡ 1`, `g''(1) = 2` — carried
one step further. On it `Af = −f^⊥` at **every** `f`, so `lem:sigma_mixing` holds with
`B̂ = 1` exactly, and `ϱ = g''(1)w_min/B̂² = 2`. The step condition
`ε ≤ (4g''(1)‖w‖_{L^∞})^{−1} = 1/8` is taken with equality, so `1 − εϱ = 3/4`.

The trajectory carries a **non-zero conserved component**, unlike the `Π = 0` checks of
`Flow.lean` and `Discrete.lean`: `h_k = (3/4)^k·(1/5, −1/5) + 1` has `Πh_k = 1` at every `k`, so
both conjuncts are exercised. -/

section TwoStateContraction

/-- `h_k = (3/4)^k·h + 𝟙` on the two-state chain: mean `1`, perpendicular part `(3/4)^k h`. -/
noncomputable def twoStateSeq (k : ℕ) : Fin 2 → ℝ := fun x => (3 / 4 : ℝ) ^ k * expH x + 1

/-- `Πh_k = 1`: the conserved component is not zero. -/
theorem twoState_meanL2_seq (k : ℕ) : Graph.meanL2 twoStateLam (twoStateSeq k) = 1 := by
  simp only [Graph.meanL2, Fin.sum_univ_two, twoStateSeq, twoStateLam, expH]
  norm_num
  ring

theorem twoState_perp_seq (k : ℕ) :
    perpL2 twoStateLam (twoStateSeq k) = fun x => (3 / 4 : ℝ) ^ k * expH x := by
  funext x
  rw [perpL2_apply, twoState_meanL2_seq k]
  simp only [twoStateSeq, add_sub_cancel_right]

theorem twoState_nrm_perp_seq (k : ℕ) :
    Graph.nrmL2 twoStateLam (perpL2 twoStateLam (twoStateSeq k)) = (3 / 4 : ℝ) ^ k * (1 / 5) := by
  rw [twoState_perp_seq]
  have hip : Graph.ipL2 twoStateLam (fun x => (3 / 4 : ℝ) ^ k * expH x)
      (fun x => (3 / 4 : ℝ) ^ k * expH x) = ((3 / 4 : ℝ) ^ k * (1 / 5)) ^ 2 := by
    simp only [Graph.ipL2, Fin.sum_univ_two, twoStateLam, expH]
    norm_num
    ring
  simp only [Graph.nrmL2, hip]
  exact Real.sqrt_sq (by positivity)

/-- **`B̂ = 1` on this chain, exactly**: `Af = −f^⊥` at every `f`, `P` being the `λ`-average. -/
theorem twoState_Aop_eq_neg_perp (f : Fin 2 → ℝ) :
    Aop twoStateK twoStateLam f = fun y => -perpL2 twoStateLam f y := by
  funext y
  simp only [Aop_apply, Core.densAct_apply, perpL2_apply, Graph.meanL2, Fin.sum_univ_two,
    twoStateK, twoStateLam]
  fin_cases y <;> norm_num <;> ring

theorem twoState_mixing (f : Fin 2 → ℝ) :
    Graph.nrmL2 twoStateLam (perpL2 twoStateLam f)
      ≤ 1 * Graph.nrmL2 twoStateLam (Aop twoStateK twoStateLam f) := by
  rw [twoState_Aop_eq_neg_perp, one_mul]
  have h : (fun y => -perpL2 twoStateLam f y) = fun y => -(perpL2 twoStateLam f) y := rfl
  rw [h, ← nrmL2_neg twoStateLam (perpL2 twoStateLam f)]

/-- `Hh_k = 2·(3/4)^k h`: the descent recursion of the theorem, evaluated. -/
theorem twoState_step (k : ℕ) (x : Fin 2) :
    twoStateSeq (k + 1) x
      = twoStateSeq k x
        - 1 / 8 * linHess twoStateK twoStateLam (fun _ => 1) 2 (twoStateSeq k) x := by
  simp only [linHess_apply, Adj_apply, funAct, Aop_apply, Core.densAct_apply,
    Fin.sum_univ_two, twoStateSeq, twoStateK, twoStateLam, expH]
  fin_cases x <;> · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
                    rw [pow_succ]
                    norm_num
                    ring

/-- **The contraction, evaluated, attained, and with a non-zero conserved component.**

*(1)* and *(2)* are proved **through** `stable_frozen_discrete_finite`, discharging each of its
fifteen hypotheses at `g''(1) = 2`, `w ≡ 1` (so `w_min = ‖w‖_{L^∞} = 1`), `B̂ = 1`, `ϱ = 2` and
`ε = 1/8` — the step condition at equality. *(3)* is the same quantity computed directly, and
its comparison with *(2)* is the check: the two sides of the contraction are **equal at every
`k`**, so the factor `1 − εϱ = 3/4` leaves no room to improve and no room for a sign or factor
error in the bridge. *(1)* reads `Πh_k = 1`, not `0`, so the conserved-component conjunct is
exercised on a trajectory that actually carries one. -/
theorem twoState_contraction_check :
    (∀ k : ℕ, Graph.meanL2 twoStateLam (twoStateSeq k) = 1)
      ∧ (∀ k : ℕ, Graph.nrmL2 twoStateLam (perpL2 twoStateLam (twoStateSeq k))
          ≤ (1 - (1 / 8 : ℝ) * (2 * 1 / (1 : ℝ) ^ 2)) ^ k
            * Graph.nrmL2 twoStateLam (perpL2 twoStateLam (twoStateSeq 0)))
      ∧ (∀ k : ℕ, Graph.nrmL2 twoStateLam (perpL2 twoStateLam (twoStateSeq k))
          = (1 - (1 / 8 : ℝ) * (2 * 1 / (1 : ℝ) ^ 2)) ^ k
            * Graph.nrmL2 twoStateLam (perpL2 twoStateLam (twoStateSeq 0))) := by
  have key := stable_frozen_discrete_finite
    (K := twoStateK) (lam := twoStateLam) (w := fun _ => 1) (g2 := 2) (wmin := 1) (wsup := 1)
    (Bhat := 1) (eps := 1 / 8) (h := twoStateSeq)
    (twoState_isMarkovOn.toIsMarkov twoStateLam_pos) twoState_isInvariant twoStateLam_pos
    (by simp only [Fin.sum_univ_two, twoStateLam]; norm_num)
    (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl) (by norm_num) (by norm_num)
    twoState_mixing (by norm_num) (by norm_num) (by norm_num) twoState_step
  refine ⟨twoState_meanL2_seq, ?_, ?_⟩
  · intro k
    have h := key.2 k
    norm_num at h ⊢
    exact h
  · intro k
    rw [twoState_nrm_perp_seq, twoState_nrm_perp_seq]
    norm_num

end TwoStateContraction

end GFNBounds.Balance
