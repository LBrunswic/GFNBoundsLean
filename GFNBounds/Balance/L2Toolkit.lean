import GFNBounds.Core.Adjoint
import GFNBounds.Balance.MassIdentity

/-!
# The `L²(λ)` shelf the frozen-policy convergence block stands on: `A = P − I`, its adjoint, and a continuity bootstrap

**`theo:local_convergence_full`** — statement `proofs.tex:612–618`, proof `proofs.tex:620–657`.
**One line of that proof and nothing else**: the "recall" of `proofs.tex:621`, and of it only
`Ah = Ah_⊥`, `‖P‖ ≤ 1`, `‖A‖ ≤ 2`, `‖A†‖ ≤ 2`. Steps 1–5 of the proof are **not** here and no
constant of the theorem (`M₃`, `C₄`–`C₇`, `K`, `L`, `ε₀`, `ε₁`, `γ₀`) is defined below.
(The bold-backtick form of the label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> All norms are `L²(λ)`; set `M₃ := sup_{[1−a,1+a]}|g'''|`, `m_t := Π h_t` (a scalar, `T` being
> ergodic), `h^⊥ := h − m`, and recall `Ah = Ah^⊥`, `‖P‖ ≤ 1`, `‖A‖ ≤ 2`, `‖A†‖ ≤ 2`.

`A := P − I` and `A† := P† − I` are the paper's, read off `eq:linearized_flow`
(`proofs.tex:566`: `∇^λ 𝓛 = g''(1)(P† − I)[w(P − I)h]λ + err(h)`) and `proofs.tex:741`
(`u := log r̂ = (P − I)h + O(‖h‖²) = Ah + O(‖h‖²)`), with `P` the density action of the backward
chain and `P†` its function action — the `L²(λ)`-adjoint of `lem:adjoint`*(3)*.

**Most of this file is shelf, not certificate.** Only `Aop_perpL2` (`Ah = Ah_⊥`),
`nrmL2_Aop_le_two` (`‖A‖ ≤ 2`), `nrmL2_Adj_le_two` (`‖A†‖ ≤ 2`) and the two contraction wrappers
`nrmL2_densAct_le`, `nrmL2_funAct_le` (`‖P‖ ≤ 1`, and `‖P†‖ ≤ 1` which the paper writes as the
same line) answer to the label. Everything else — the triangle inequality for `nrmL2`, the
Pythagoras split of a norm into mean and mean-zero part, the `√λ_min` transfer to `L^∞`, and
`bootstrap_of_continuous` — is general-purpose `L²(λ)` and real-analysis material stated for
whoever needs it next. `bootstrap_of_continuous` is written *for* Step 4 of the same proof ("by
continuity the interval is all of `ℝ₊`") but is stated with no reference to the flow, and Step 4
itself is not formalized.

## Hypothesis checklist

The line certified is a recall inside a proof, so the "paper hypothesis" column is the standing
setting the recall is read in — `theo:db_stable_frozen_full`'s, `proofs.tex:592–602`.

| paper hypothesis | here |
|---|---|
| `T` ergodic with invariant `λ`, `P` its density action on `L²(λ)` | ⚠ **weakened to non-negative invariance**: `Core.IsInvariant lam K` (`λ ≥ 0`, `λK = λ`) plus `Core.IsMarkov K` / `Core.IsMarkovOn lam K`. Ergodicity is never used — `‖P‖ ≤ 1` and `‖A‖ ≤ 2` do not need it |
| `𝒮` a general state space, `L²(λ)` a Lebesgue space | ⚠ **restricted to a `Fintype`**, as everywhere in `GFNBounds.Balance`: `⟪·∣·⟫_λ` is `Graph.ipL2`, a `Finset` sum, and `‖·‖` is `Graph.nrmL2`, a `Real.sqrt` of one. No `InnerProductSpace` instance is built, so nothing below is stated with `‖·‖` or `⟪·,·⟫` |
| `Π h` the mean projection, a scalar (`T` ergodic) | ✓ carried as `Graph.meanL2`, the paper's own reading at `proofs.tex:22`. That it is *also* the orthogonal projection onto the invariant functions is not needed and not proved; what replaces it is `nrmL2_sq_eq_mean_sq_add_perp`, the Pythagoras identity, which needs only `∑λ = 1` |
| `h^⊥ := h − m` | ✓ `perpL2` |
| `g` is `C³` on `[1−a,1+a]`, `g''(1) > 0`, `M₃ := sup∣g'''∣` | ✗ **not carried and not needed**: no statement below mentions `g` |
| `‖·‖_{L^∞(λ)} ≤ C_∞‖·‖_{L²(λ)}` with `C_∞ = (min λ)^{−1/2}` | ✓ `abs_le_nrmL2_div_sqrt`, in the form `√λ_min·∣h(x)∣ ≤ ‖h‖`, with `λ_min` an explicit hypothesis rather than a `min` over the graph — `Graph.sqrt_minOver_mul_abs_le_nrmL2` is the same bound, but only for a `MarkedGraph` |
| `ν = wλ`, `w_min ≤ w ≤ ‖w‖_{L^∞}`, `B̂ < ∞`, `ϱ = g''(1)w_min/B̂²` | ✗ not carried: no rate, no loss and no training measure appears below |

## SCOPE (disclosed)

* **One line of one proof.** The theorem `theo:local_convergence_full` is **not** proved here, and
  nothing below should be read as progress on its statement. Its five steps need the first
  variation (`theo:first_variation_full`, bucket `D`), the linearization
  (`theo:gd_diffusion_full`, bucket `D`) and an ODE layer, none of which this library has. What is
  certified is that the four facts the proof *recalls* are true of `A = P − I` on a finite state
  space: `A` kills the mean, `P` and `P†` are `L²(λ)`-contractions, and `A`, `A†` have norm at
  most `2`.
* **The norm bounds are stated pointwise in the argument, not as operator norms.**
  `‖A‖ ≤ 2` appears as `∀ h, ‖Ah‖ ≤ 2‖h‖`; no `ContinuousLinearMap` is formed and no `IsLeast`
  claim is made, so *sharpness* is not asserted — `2` is an upper bound, as in the paper, and
  the paper does not claim it is attained either.
* **`Ah = Ah_⊥` holds `λ`-almost everywhere, and is stated that way.** `Aop_perpL2` carries
  `lam y ≠ 0`, because `Core.densAct` divides by `λ(y)` and returns `0` where `λ` vanishes; on
  that null set `A` annihilates every function, the identity included. Under `λ > 0` the
  hypothesis is discharged at every state. This mirrors the `λ`-a.e. discipline of
  `GFNBounds/Core/Adjoint.lean` rather than assuming it away.
* **`bootstrap_of_continuous` is a statement about a family of continuous scalar functions, not
  about a flow.** It is the shape Step 4 needs — a bound that reproduces itself at half strength
  propagates from `t = 0` to all of `ℝ₊` — but it takes the bootstrap implication `hboot` as a
  hypothesis. Deriving that implication from the gradient flow is Steps 1–3 and is not done.
  The hypothesis is a *family* indexed by the state, one inequality per `x`, which is what lets
  the proof run without a `Finset.sup'` of the coordinates and a continuity argument for it.
* **Nothing here is `theo:db_stable_frozen_full`'s discrete half either.** `‖A‖ ≤ 2` is what
  `proofs.tex:609` uses to get `ε‖H‖ ≤ 1`; that step needs `H` and is in
  `GFNBounds/Balance/Flow.lean`'s scope, where it is disclosed as absent.

## Reuse rather than redefinition

`Graph.ipL2`, `Graph.nrmL2`, `Graph.meanL2`, `Graph.sq_nrmL2` and the discrete Cauchy–Schwarz
`Graph.ipL2_le_mul_nrmL2` come from `GFNBounds/Graph/Morozov.lean` and are used as they stand.
The two contractions `‖P‖ ≤ 1` and `‖P†‖ ≤ 1` are **already proved** in
`GFNBounds/Core/Adjoint.lean` as `Core.nrmL2_densAct_le` and `Core.nrmL2_funAct_le` (the paper's
`eq:reversal_contraction`, `lem:adjoint`*(3)*); they are re-exported here under the
`GFNBounds.Balance` names so that a user of `Balance.funAct` need not know about `Core.funAct`,
and no Jensen inequality is proved a second time. Likewise `meanL2_funAct` is
`Balance.integral_funAct` of `GFNBounds/Balance/MassIdentity.lean` read on `meanL2`, and
`abs_le_nrmL2_div_sqrt` is `Graph.sqrt_minOver_mul_abs_le_nrmL2` with the `MarkedGraph` removed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### Bookkeeping for `⟪·∣·⟫_λ`, `‖·‖_λ` and `Π`

`Graph.ipL2`, `Graph.nrmL2` and `Graph.meanL2` are `Finset` sums; these are the linearity and
norm-algebra facts the rest of the file uses. None of them was in the library — the `L²(λ)` layer
of `GFNBounds/Graph/Morozov.lean` carries Cauchy–Schwarz and the two comparisons with `L^∞`, but
no triangle inequality and no linearity — except `abs_le_nrmL2_div_sqrt`, which is a `MarkedGraph`
lemma restated. -/

/-- `⟪a ∣ b⟫_λ = ⟪b ∣ a⟫_λ`. -/
theorem ipL2_comm (lam a b : V → ℝ) : Graph.ipL2 lam a b = Graph.ipL2 lam b a := by
  simp only [Graph.ipL2]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `⟪a − b ∣ c⟫_λ = ⟪a ∣ c⟫_λ − ⟪b ∣ c⟫_λ`. -/
theorem ipL2_sub_left (lam a b c : V → ℝ) :
    Graph.ipL2 lam (fun x => a x - b x) c = Graph.ipL2 lam a c - Graph.ipL2 lam b c := by
  simp only [Graph.ipL2]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `⟪a ∣ b − c⟫_λ = ⟪a ∣ b⟫_λ − ⟪a ∣ c⟫_λ`. -/
theorem ipL2_sub_right (lam a b c : V → ℝ) :
    Graph.ipL2 lam a (fun x => b x - c x) = Graph.ipL2 lam a b - Graph.ipL2 lam a c := by
  simp only [Graph.ipL2]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `Π(a − b) = Πa − Πb`. -/
theorem meanL2_sub (lam a b : V → ℝ) :
    Graph.meanL2 lam (fun x => a x - b x) = Graph.meanL2 lam a - Graph.meanL2 lam b := by
  simp only [Graph.meanL2]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `‖−a‖_λ = ‖a‖_λ`. -/
theorem nrmL2_neg (lam a : V → ℝ) :
    Graph.nrmL2 lam (fun x => -a x) = Graph.nrmL2 lam a := by
  simp only [Graph.nrmL2, Graph.ipL2, neg_mul_neg]

/-- `‖c·a‖_λ = |c|·‖a‖_λ`. -/
theorem nrmL2_smul (lam a : V → ℝ) (c : ℝ) :
    Graph.nrmL2 lam (fun x => c * a x) = |c| * Graph.nrmL2 lam a := by
  have hexp : Graph.ipL2 lam (fun x => c * a x) (fun x => c * a x)
      = c ^ 2 * Graph.ipL2 lam a a := by
    simp only [Graph.ipL2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [Graph.nrmL2, hexp]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **The triangle inequality for `‖·‖_{L²(λ)}`**, from the Cauchy–Schwarz
`Graph.ipL2_le_mul_nrmL2`. -/
theorem nrmL2_add_le {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a b : V → ℝ) :
    Graph.nrmL2 lam (fun x => a x + b x) ≤ Graph.nrmL2 lam a + Graph.nrmL2 lam b := by
  have hexp : Graph.ipL2 lam (fun x => a x + b x) (fun x => a x + b x)
      = Graph.ipL2 lam a a + 2 * Graph.ipL2 lam a b + Graph.ipL2 lam b b := by
    simp only [Graph.ipL2]
    have e1 : (2:ℝ) * (∑ x, lam x * (a x * b x)) = ∑ x, 2 * (lam x * (a x * b x)) := by
      rw [Finset.mul_sum]
    rw [e1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hcs : Graph.ipL2 lam a b ≤ Graph.nrmL2 lam a * Graph.nrmL2 lam b :=
    Graph.ipL2_le_mul_nrmL2 hnn a b
  have ha := Graph.sq_nrmL2 hnn a
  have hb := Graph.sq_nrmL2 hnn b
  have hsq : Graph.ipL2 lam (fun x => a x + b x) (fun x => a x + b x)
      ≤ (Graph.nrmL2 lam a + Graph.nrmL2 lam b) ^ 2 := by
    rw [hexp]; nlinarith [hcs, ha, hb]
  calc Graph.nrmL2 lam (fun x => a x + b x)
      ≤ Real.sqrt ((Graph.nrmL2 lam a + Graph.nrmL2 lam b) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Graph.nrmL2 lam a + Graph.nrmL2 lam b :=
        Real.sqrt_sq (add_nonneg (Graph.nrmL2_nonneg _ _) (Graph.nrmL2_nonneg _ _))

/-- `‖a − b‖_λ ≤ ‖a‖_λ + ‖b‖_λ` — the form the two "norm at most `2`" bounds consume. -/
theorem nrmL2_sub_le {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a b : V → ℝ) :
    Graph.nrmL2 lam (fun x => a x - b x) ≤ Graph.nrmL2 lam a + Graph.nrmL2 lam b := by
  have hrw : Graph.nrmL2 lam (fun x => a x - b x)
      = Graph.nrmL2 lam (fun x => a x + (fun z => -b z) x) := by
    simp only [sub_eq_add_neg]
  rw [hrw]
  refine le_trans (nrmL2_add_le hnn a (fun z => -b z)) ?_
  rw [nrmL2_neg]

/-- **A pointwise domination transfers to the norm**: `|a| ≤ c|b|` everywhere gives
`‖a‖_λ ≤ c‖b‖_λ`. -/
theorem nrmL2_le_of_abs_le {lam a b : V → ℝ} {c : ℝ} (hnn : ∀ x, 0 ≤ lam x) (hc : 0 ≤ c)
    (hab : ∀ x, |a x| ≤ c * |b x|) :
    Graph.nrmL2 lam a ≤ c * Graph.nrmL2 lam b := by
  have hsq : Graph.ipL2 lam a a ≤ c ^ 2 * Graph.ipL2 lam b b := by
    simp only [Graph.ipL2, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h2 : |a x| * |a x| ≤ (c * |b x|) * (c * |b x|) :=
      mul_self_le_mul_self (abs_nonneg _) (hab x)
    rw [abs_mul_abs_self] at h2
    have h1 : a x * a x ≤ c ^ 2 * (b x * b x) := by
      calc a x * a x ≤ (c * |b x|) * (c * |b x|) := h2
        _ = c ^ 2 * (|b x| * |b x|) := by ring
        _ = c ^ 2 * (b x * b x) := by rw [abs_mul_abs_self]
    calc lam x * (a x * a x) ≤ lam x * (c ^ 2 * (b x * b x)) :=
          mul_le_mul_of_nonneg_left h1 (hnn x)
      _ = c ^ 2 * (lam x * (b x * b x)) := by ring
  calc Graph.nrmL2 lam a ≤ Real.sqrt (c ^ 2 * Graph.ipL2 lam b b) := Real.sqrt_le_sqrt hsq
    _ = c * Graph.nrmL2 lam b := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
        rfl

/-- **`‖·‖_{L^∞} ≤ ‖·‖_{L²(λ)}/√λ_min`**, the paper's `C_∞ = (min λ)^{−1/2}`
(`proofs.tex:613`), with `λ_min` a hypothesis rather than a minimum over a `MarkedGraph`. This is
`Graph.sqrt_minOver_mul_abs_le_nrmL2` with the graph removed; `λ ≥ 0` is not assumed, being
implied by `0 < λ_min ≤ λ`. -/
theorem abs_le_nrmL2_div_sqrt {lam : V → ℝ} {lamMin : ℝ} (hlmin0 : 0 < lamMin)
    (hlmin : ∀ x, lamMin ≤ lam x) (a : V → ℝ) (x : V) :
    Real.sqrt lamMin * |a x| ≤ Graph.nrmL2 lam a := by
  have hnn : ∀ z, 0 ≤ lam z := fun z => le_trans hlmin0.le (hlmin z)
  have hterm : lamMin * (a x * a x) ≤ Graph.ipL2 lam a a := by
    refine le_trans (mul_le_mul_of_nonneg_right (hlmin x) (mul_self_nonneg (a x))) ?_
    exact Finset.single_le_sum (f := fun z => lam z * (a z * a z))
      (fun z _ => mul_nonneg (hnn z) (mul_self_nonneg (a z))) (Finset.mem_univ x)
  calc Real.sqrt lamMin * |a x|
      = Real.sqrt (lamMin * (a x * a x)) := by
        rw [Real.sqrt_mul hlmin0.le, ← Real.sqrt_mul_self_eq_abs]
    _ ≤ Graph.nrmL2 lam a := Real.sqrt_le_sqrt hterm

/-! ### `A = P − I`, `A† = P† − I`, and `h_⊥ = h − Πh` -/

/-- **The paper's `A = P − I`** (`eq:linearized_flow`, `proofs.tex:566`; `proofs.tex:741`), acting
on densities: `P` is `Core.densAct`, the density action of the kernel `K` on `𝓜²(λ)`. -/
noncomputable def Aop (K : V → V → ℝ) (lam h : V → ℝ) : V → ℝ :=
  fun y => Core.densAct lam K h y - h y

/-- **The paper's `A† = P† − I`**, acting on functions: `P†` is the function action
`(P†φ)(x) = ∑_y K(x,y)φ(y)`, the `L²(λ)`-adjoint of `P` by `lem:adjoint`*(3)*. -/
def Adj (K : V → V → ℝ) (φ : V → ℝ) : V → ℝ := fun x => funAct K φ x - φ x

/-- **The paper's `h^⊥ := h − m`** with `m = Πh` a scalar (`proofs.tex:621`). -/
def perpL2 (lam h : V → ℝ) : V → ℝ := fun x => h x - Graph.meanL2 lam h

/-- The unapplied form of `perpL2`. Lean's equation lemma for a definition whose body is a
lambda is generated at full arity, so it cannot rewrite `perpL2 lam h` standing as a function;
this can. -/
theorem perpL2_eq (lam h : V → ℝ) : perpL2 lam h = fun x => h x - Graph.meanL2 lam h := rfl

theorem perpL2_apply (lam h : V → ℝ) (x : V) :
    perpL2 lam h x = h x - Graph.meanL2 lam h := rfl

/-- The unapplied form of `Aop`. -/
theorem Aop_eq (K : V → V → ℝ) (lam h : V → ℝ) :
    Aop K lam h = fun y => Core.densAct lam K h y - h y := rfl

theorem Aop_apply (K : V → V → ℝ) (lam h : V → ℝ) (y : V) :
    Aop K lam h y = Core.densAct lam K h y - h y := rfl

/-- The unapplied form of `Adj`. -/
theorem Adj_eq (K : V → V → ℝ) (φ : V → ℝ) :
    Adj K φ = fun x => funAct K φ x - φ x := rfl

theorem Adj_apply (K : V → V → ℝ) (φ : V → ℝ) (x : V) :
    Adj K φ x = funAct K φ x - φ x := rfl

/-! ### Linearity and the constants -/

/-- `P†` is linear: `P†(a − b) = P†a − P†b`. -/
theorem funAct_sub (K : V → V → ℝ) (a b : V → ℝ) :
    funAct K (fun y => a y - b y) = fun x => funAct K a x - funAct K b x := by
  funext x
  simp only [funAct]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- `P` is linear: `P(a − b) = Pa − Pb`, at every state and with no hypothesis (both sides vanish
together where `λ` does). -/
theorem densAct_sub (lam : V → ℝ) (K : V → V → ℝ) (a b : V → ℝ) (y : V) :
    Core.densAct lam K (fun x => a x - b x) y
      = Core.densAct lam K a y - Core.densAct lam K b y := by
  simp only [Core.densAct_apply]
  rw [← sub_div, ← Finset.sum_sub_distrib]
  exact congrArg (· / lam y) (Finset.sum_congr rfl fun x _ => by ring)

/-- **`P†𝟏 = 𝟏`**: the function action fixes the constants, `K` being row-stochastic. -/
theorem funAct_const {K : V → V → ℝ} (hrow : ∀ x, ∑ y, K x y = 1) (c : ℝ) (x : V) :
    funAct K (fun _ => c) x = c := by
  simp only [funAct]
  rw [← Finset.sum_mul, hrow x, one_mul]

/-- **`P𝟏 = 𝟏` `λ`-almost everywhere**: the density action fixes the constants wherever `λ`
charges, `λ` being invariant. Where `λ(y) = 0` the Lean convention `a / 0 = 0` makes `P` return
`0`, so the hypothesis `lam y ≠ 0` is not removable. -/
theorem densAct_const {lam : V → ℝ} {K : V → V → ℝ} (hinv : Core.IsInvariant lam K) (c : ℝ)
    {y : V} (hy : lam y ≠ 0) : Core.densAct lam K (fun _ => c) y = c := by
  simp only [Core.densAct_apply]
  rw [← Finset.sum_mul, hinv.inv y, mul_comm, mul_div_assoc, div_self hy, mul_one]

/-- **`A𝟏 = 0`**, `λ`-almost everywhere. -/
theorem Aop_const {lam : V → ℝ} {K : V → V → ℝ} (hinv : Core.IsInvariant lam K) (c : ℝ)
    {y : V} (hy : lam y ≠ 0) : Aop K lam (fun _ => c) y = 0 := by
  rw [Aop_apply, densAct_const hinv c hy, sub_self]

/-- **`A†𝟏 = 0`**. -/
theorem Adj_const {K : V → V → ℝ} (hrow : ∀ x, ∑ y, K x y = 1) (c : ℝ) (x : V) :
    Adj K (fun _ => c) x = 0 := by
  rw [Adj_apply, funAct_const hrow c x, sub_self]

/-- **`Ah = Ah_⊥`** — the first of the four facts `proofs.tex:621` recalls. `λ`-almost
everywhere: where `λ` vanishes both sides are `−h(y)` and `−h_⊥(y)`, which differ by the mean. -/
theorem Aop_perpL2 {lam : V → ℝ} {K : V → V → ℝ} (hinv : Core.IsInvariant lam K) (h : V → ℝ)
    {y : V} (hy : lam y ≠ 0) : Aop K lam (perpL2 lam h) y = Aop K lam h y := by
  have hsub : Core.densAct lam K (perpL2 lam h) y
      = Core.densAct lam K h y - Graph.meanL2 lam h := by
    rw [show Core.densAct lam K (perpL2 lam h) y
        = Core.densAct lam K h y - Core.densAct lam K (fun _ => Graph.meanL2 lam h) y from
      densAct_sub lam K h (fun _ => Graph.meanL2 lam h) y, densAct_const hinv _ hy]
  rw [Aop_apply, Aop_apply, hsub, perpL2_apply]
  ring

/-! ### `A†` is the adjoint of `A`, and both kill the mean -/

/-- **`⟪A†φ ∣ h⟫_λ = ⟪φ ∣ Ah⟫_λ`** — `A† = P† − I` is the `L²(λ)`-adjoint of `A = P − I`,
`lem:adjoint`*(3)* minus the identity on both sides. -/
theorem ipL2_Adj_left {lam : V → ℝ} {K : V → V → ℝ} (hinv : Core.IsInvariant lam K)
    (hK : ∀ x y, 0 ≤ K x y) (φ h : V → ℝ) :
    Graph.ipL2 lam (Adj K φ) h = Graph.ipL2 lam φ (Aop K lam h) := by
  -- `Core.funAct` and `Balance.funAct` are the same definition; the ascription does the
  -- unfolding once, so that `rw` below sees a syntactic match.
  have hadj : Graph.ipL2 lam (Core.densAct lam K h) φ = Graph.ipL2 lam h (funAct K φ) :=
    Core.ipL2_densAct_funAct hinv hK h φ
  calc Graph.ipL2 lam (Adj K φ) h
      = Graph.ipL2 lam (funAct K φ) h - Graph.ipL2 lam φ h :=
        ipL2_sub_left lam (funAct K φ) φ h
    _ = Graph.ipL2 lam h (funAct K φ) - Graph.ipL2 lam φ h := by rw [ipL2_comm lam (funAct K φ) h]
    _ = Graph.ipL2 lam (Core.densAct lam K h) φ - Graph.ipL2 lam φ h := by rw [hadj]
    _ = Graph.ipL2 lam φ (Core.densAct lam K h) - Graph.ipL2 lam φ h := by
        rw [ipL2_comm lam (Core.densAct lam K h) φ]
    _ = Graph.ipL2 lam φ (Aop K lam h) :=
        (ipL2_sub_right lam φ (Core.densAct lam K h) h).symm

/-- **`∫ P†φ dλ = ∫ φ dλ`** read on `Π`: this is `Balance.integral_funAct` of
`GFNBounds/Balance/MassIdentity.lean`, which the paper writes `⟨φ, P𝟏⟩ = ∫φ dλ`
(`proofs.tex:802`). -/
theorem meanL2_funAct {lam : V → ℝ} {K : V → V → ℝ} (hinv : Invariant K lam) (φ : V → ℝ) :
    Graph.meanL2 lam (funAct K φ) = Graph.meanL2 lam φ :=
  integral_funAct hinv φ

/-- **`Π A†φ = 0`**: `A†` lands in the mean-zero subspace. -/
theorem meanL2_Adj {lam : V → ℝ} {K : V → V → ℝ} (hinv : Invariant K lam) (φ : V → ℝ) :
    Graph.meanL2 lam (Adj K φ) = 0 := by
  rw [show Graph.meanL2 lam (Adj K φ)
      = Graph.meanL2 lam (funAct K φ) - Graph.meanL2 lam φ from meanL2_sub lam (funAct K φ) φ,
    meanL2_funAct hinv, sub_self]

/-- `Core.IsInvariant` implies the `Balance` spelling of invariance; the two are the same
statement, `Core.IsInvariant` merely bundling `λ ≥ 0` with it. -/
theorem invariant_of_isInvariant {lam : V → ℝ} {K : V → V → ℝ} (hinv : Core.IsInvariant lam K) :
    Invariant K lam := hinv.inv

/-! ### `‖P‖ ≤ 1`, `‖A‖ ≤ 2`, `‖A†‖ ≤ 2` -/

/-- **`‖P†‖ ≤ 1`** — `Core.nrmL2_funAct_le`, restated for `Balance.funAct`. The Jensen step is
the paper's `eq:reversal_contraction` and is proved once, in `GFNBounds/Core/Adjoint.lean`. -/
theorem nrmL2_funAct_le {lam : V → ℝ} {K : V → V → ℝ} (hK : Core.IsMarkovOn lam K)
    (hinv : Core.IsInvariant lam K) (φ : V → ℝ) :
    Graph.nrmL2 lam (funAct K φ) ≤ Graph.nrmL2 lam φ :=
  Core.nrmL2_funAct_le hK hinv φ

/-- **`‖P‖ ≤ 1`** — `Core.nrmL2_densAct_le`, re-exported. -/
theorem nrmL2_densAct_le {lam : V → ℝ} {K : V → V → ℝ} (hK : Core.IsMarkov K)
    (hinv : Core.IsInvariant lam K) (u : V → ℝ) :
    Graph.nrmL2 lam (Core.densAct lam K u) ≤ Graph.nrmL2 lam u :=
  Core.nrmL2_densAct_le hK hinv u

/-- **`‖A‖ ≤ 2`** (`proofs.tex:621`, and `proofs.tex:609` where it buys `ε‖H‖ ≤ 1`): the triangle
inequality against `‖P‖ ≤ 1`. -/
theorem nrmL2_Aop_le_two {lam : V → ℝ} {K : V → V → ℝ} (hK : Core.IsMarkov K)
    (hinv : Core.IsInvariant lam K) (h : V → ℝ) :
    Graph.nrmL2 lam (Aop K lam h) ≤ 2 * Graph.nrmL2 lam h := by
  have h1 : Graph.nrmL2 lam (Aop K lam h)
      ≤ Graph.nrmL2 lam (Core.densAct lam K h) + Graph.nrmL2 lam h :=
    nrmL2_sub_le hinv.nonneg (Core.densAct lam K h) h
  have h2 := nrmL2_densAct_le hK hinv h
  linarith

/-- **`‖A†‖ ≤ 2`** (`proofs.tex:621`). -/
theorem nrmL2_Adj_le_two {lam : V → ℝ} {K : V → V → ℝ} (hK : Core.IsMarkovOn lam K)
    (hinv : Core.IsInvariant lam K) (φ : V → ℝ) :
    Graph.nrmL2 lam (Adj K φ) ≤ 2 * Graph.nrmL2 lam φ := by
  have h1 : Graph.nrmL2 lam (Adj K φ) ≤ Graph.nrmL2 lam (funAct K φ) + Graph.nrmL2 lam φ :=
    nrmL2_sub_le hinv.nonneg (funAct K φ) φ
  have h2 := nrmL2_funAct_le hK hinv φ
  linarith

/-! ### `‖h‖² = (Πh)² + ‖h_⊥‖²`

`Π` is the mean, so the splitting `h = m + h_⊥` is orthogonal for the sole reason that `λ` is a
probability. This is what replaces "`Π` is the orthogonal projection onto the invariant
functions", which is not proved in this library. -/

/-- **Pythagoras**: `‖h‖² = (Πh)² + ‖h_⊥‖²` when `λ` is a probability. -/
theorem nrmL2_sq_eq_mean_sq_add_perp {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x)
    (htot : ∑ x, lam x = 1) (h : V → ℝ) :
    Graph.nrmL2 lam h ^ 2
      = Graph.meanL2 lam h ^ 2 + Graph.nrmL2 lam (perpL2 lam h) ^ 2 := by
  have hkey : ∀ m : ℝ, Graph.ipL2 lam (fun x => h x - m) (fun x => h x - m)
      = Graph.ipL2 lam h h - 2 * m * Graph.meanL2 lam h + m ^ 2 * ∑ x, lam x := by
    intro m
    simp only [Graph.ipL2, Graph.meanL2]
    have e1 : (2:ℝ) * m * (∑ x, lam x * h x) = ∑ x, 2 * m * (lam x * h x) := by
      rw [Finset.mul_sum]
    have e2 : m ^ 2 * (∑ x, lam x) = ∑ x, m ^ 2 * lam x := by rw [Finset.mul_sum]
    rw [e1, e2, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Graph.sq_nrmL2 hnn h, Graph.sq_nrmL2 hnn (perpL2 lam h), perpL2_eq lam h,
    hkey (Graph.meanL2 lam h), htot]
  ring

/-- **`|Πh| ≤ ‖h‖`**. -/
theorem abs_meanL2_le_nrmL2 {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1)
    (h : V → ℝ) : |Graph.meanL2 lam h| ≤ Graph.nrmL2 lam h := by
  have hpy := nrmL2_sq_eq_mean_sq_add_perp hnn htot h
  have h1 : Graph.meanL2 lam h ^ 2 ≤ Graph.nrmL2 lam h ^ 2 := by
    nlinarith [sq_nonneg (Graph.nrmL2 lam (perpL2 lam h))]
  calc |Graph.meanL2 lam h| = Real.sqrt (Graph.meanL2 lam h ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Graph.nrmL2 lam h ^ 2) := Real.sqrt_le_sqrt h1
    _ = Graph.nrmL2 lam h := Real.sqrt_sq (Graph.nrmL2_nonneg _ _)

/-- **`‖h_⊥‖ ≤ ‖h‖`**. -/
theorem nrmL2_perpL2_le {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1)
    (h : V → ℝ) : Graph.nrmL2 lam (perpL2 lam h) ≤ Graph.nrmL2 lam h := by
  have hpy := nrmL2_sq_eq_mean_sq_add_perp hnn htot h
  have h1 : Graph.nrmL2 lam (perpL2 lam h) ^ 2 ≤ Graph.nrmL2 lam h ^ 2 := by
    nlinarith [sq_nonneg (Graph.meanL2 lam h)]
  calc Graph.nrmL2 lam (perpL2 lam h)
      = Real.sqrt (Graph.nrmL2 lam (perpL2 lam h) ^ 2) :=
        (Real.sqrt_sq (Graph.nrmL2_nonneg _ _)).symm
    _ ≤ Real.sqrt (Graph.nrmL2 lam h ^ 2) := Real.sqrt_le_sqrt h1
    _ = Graph.nrmL2 lam h := Real.sqrt_sq (Graph.nrmL2_nonneg _ _)

/-! ### Two pieces of real analysis the block will want -/

-- `hx0 : 0 ≤ x` is not consumed by the proof — `x ≤ 1` alone gives both steps. It is kept
-- because the statement is about `[0,1]`, and the linter is silenced rather than the hypothesis
-- dropped.
set_option linter.unusedVariables false in
/-- `√(1 − x) ≤ 1 − x/2` on `[0,1]` — the concavity step behind a "contracts by `1 − γϱ/4`"
reading of a "contracts by `1 − γϱ/2`" bound on the square (`proofs.tex:655–656`). -/
theorem sqrt_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt (1 - x) ≤ 1 - x / 2 := by
  have h1 : (0:ℝ) ≤ 1 - x / 2 := by linarith
  have h2 : 1 - x ≤ (1 - x / 2) ^ 2 := by nlinarith [sq_nonneg x]
  calc Real.sqrt (1 - x) ≤ Real.sqrt ((1 - x / 2) ^ 2) := Real.sqrt_le_sqrt h2
    _ = 1 - x / 2 := Real.sqrt_sq h1

/-- **The continuation bootstrap** — the shape of Step 4 of `theo:local_convergence_full`
(`proofs.tex:643`: *"on any interval where `‖h_s‖_{L^∞} ≤ ε` the estimates above give
`‖h_t‖_{L^∞} ≤ ε/2`: by continuity the interval is all of `ℝ₊`"*), stated for a family of
continuous scalar functions and with no flow in sight.

The hypothesis `hboot` is the conjunction of Steps 1–3 and is **assumed**, not derived; see the
module SCOPE. It is indexed by the state — one inequality per `x` — which is what lets the
argument run without taking a supremum over the states and proving that supremum continuous.

The proof is the standard first-failure argument: if the `ε/2` bound ever fails, let `T` be the
infimum of the failure times; below `T` the bound holds, at `T` it holds by closedness of
`{t ∣ |h t x| ≤ ε/2}`, and continuity then gives a right-neighbourhood of `T` on which the weaker
bound `ε` holds — on which `hboot` restores `ε/2`, pushing the infimum past itself. -/
theorem bootstrap_of_continuous {h : ℝ → V → ℝ} {eps : ℝ}
    (heps : 0 < eps)
    (hcont : ∀ x, Continuous fun t => h t x)
    (hstart : ∀ x, |h 0 x| ≤ eps / 2)
    (hboot : ∀ t : ℝ, 0 ≤ t → (∀ s ∈ Set.Icc (0:ℝ) t, ∀ x, |h s x| ≤ eps) →
              ∀ x, |h t x| ≤ eps / 2) :
    ∀ t : ℝ, 0 ≤ t → ∀ x, |h t x| ≤ eps / 2 := by
  -- `B` is the set of non-negative times at which the `ε/2` bound fails.
  set B : Set ℝ := {t : ℝ | 0 ≤ t ∧ ∃ x, eps / 2 < |h t x|} with hBdef
  have hBbd : BddBelow B := ⟨0, fun b hb => hb.1⟩
  have hempty : ∀ b : ℝ, b ∉ B := by
    intro b hbB
    have hBne : B.Nonempty := ⟨b, hbB⟩
    set T : ℝ := sInf B with hTdef
    have hT0 : 0 ≤ T := le_csInf hBne fun c hc => hc.1
    -- Below `T` the `ε/2` bound holds, `T` being the greatest lower bound of the failure set.
    have hbelow : ∀ s : ℝ, 0 ≤ s → s < T → ∀ x, |h s x| ≤ eps / 2 := by
      intro s hs hsT x
      by_contra hxs
      exact absurd (csInf_le hBbd (show s ∈ B from ⟨hs, x, not_le.mp hxs⟩)) (not_le.mpr hsT)
    -- At `T` it holds too: `{t ∣ |h t x| ≤ ε/2}` is closed and contains `[0, T)`.
    have hatT : ∀ x, |h T x| ≤ eps / 2 := by
      intro x
      rcases eq_or_lt_of_le hT0 with hz | hpos
      · rw [← hz]; exact hstart x
      · have hclosed : IsClosed {t : ℝ | |h t x| ≤ eps / 2} :=
          isClosed_le (hcont x).abs continuous_const
        have hsub : Set.Ico (0:ℝ) T ⊆ {t : ℝ | |h t x| ≤ eps / 2} :=
          fun s hs => hbelow s hs.1 hs.2 x
        have hmem : T ∈ closure (Set.Ico (0:ℝ) T) := by
          rw [closure_Ico (ne_of_lt hpos)]
          exact Set.right_mem_Icc.mpr hT0
        exact hclosed.closure_subset_iff.mpr hsub hmem
    -- Continuity gives a neighbourhood of `T` carrying the weaker bound `ε`, at every state.
    have hev : ∀ᶠ t in nhds T, ∀ x, |h t x| ≤ eps := by
      refine Filter.eventually_all.2 fun x => ?_
      have hopen : IsOpen {t : ℝ | |h t x| < eps} := isOpen_lt (hcont x).abs continuous_const
      have hmemT : T ∈ {t : ℝ | |h t x| < eps} := lt_of_le_of_lt (hatT x) (by linarith)
      refine Filter.mem_of_superset (hopen.mem_nhds hmemT) ?_
      intro t ht
      have ht' : |h t x| < eps := ht
      exact ht'.le
    obtain ⟨δ, hδ, hδH⟩ := Metric.eventually_nhds_iff.mp hev
    -- `hboot` then restores the `ε/2` bound on all of `[0, T + δ)`.
    have hgood : ∀ t : ℝ, 0 ≤ t → t < T + δ → ∀ x, |h t x| ≤ eps / 2 := by
      intro t ht htδ x
      rcases le_or_gt t T with hle | hgt
      · rcases eq_or_lt_of_le hle with he | hlt
        · rw [he]; exact hatT x
        · exact hbelow t ht hlt x
      · refine hboot t ht (fun s hs y => ?_) x
        rcases le_or_gt s T with hsle | hsgt
        · rcases eq_or_lt_of_le hsle with he | hlt
          · rw [he]; linarith [hatT y]
          · linarith [hbelow s hs.1 hlt y]
        · have hds : dist s T < δ := by
            rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < s - T)]
            linarith [hs.2]
          exact hδH hds y
    -- so every failure time is at least `T + δ`, and `T = sInf B` is pushed past itself.
    have hlb : T + δ ≤ T := by
      refine le_csInf hBne fun c hc => ?_
      by_contra hbb
      obtain ⟨y, hy⟩ := hc.2
      exact absurd (hgood c hc.1 (not_le.mp hbb) y) (not_le.mpr hy)
    linarith
  intro t ht x
  by_contra hxt
  exact hempty t ⟨ht, x, not_le.mp hxt⟩

end GFNBounds.Balance
