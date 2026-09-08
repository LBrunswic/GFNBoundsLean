import GFNBounds.Balance.FirstVariation
import GFNBounds.Balance.Lift

/-!
# The two corollaries of the first variation: the FM gradient and the DB gradient

**`cor:gradient_formulas`** — statement `proofs.tex:485–498`, proof `proofs.tex:500–502`.
**`cor:db_gradient`** — statement `proofs.tex:537–544`, proof `proofs.tex:546–548`.
(The bold-backtick form of each label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (`cor:gradient_formulas`) Under the assumptions of Theorem `theo:first_variation_full` with
> `T = π_←` and `μ = F_←`: `∇^λ_{F_←} 𝓛_{g,F_←} = (π_→^λ − r)[g'(r)λ]`. For `g(x) = (x−1)²`,
> `∇^λ_{F_←} 𝓛_{g,F_←} = 2(π_→^λ − r)[(r−1)λ] = 2(π_→^λ(rλ) − λ − r²λ + rλ)`. The case
> `g(x) = |x−1|` is analogous, with `g'(r)` replaced by the sign of `r−1` (Appendix A).

> (proof) Apply Theorem `theo:first_variation_full` to `T = π_←`, `μ = F_←`, with `ν_G = λ` and
> `ν = F_←`, so that `dν_G/dλ = dν/dF_← = 1`; this gives the first display. For `g(x) = (x−1)²`,
> `g'(r) = 2(r−1)` and the second display follows by expanding and using `λπ_→^λ = λ` […]. For
> `g(x) = |x−1|`, `g'(r) = ε(r)` almost everywhere.

> (`cor:db_gradient`) Under the hypotheses of Theorem `theo:first_variation_full` applied on
> `(𝒮², λ₂, K₂)`, the DB loss with frozen backward policy satisfies, with `r̂ := d(μK₂)/dμ`,
> `∇^{λ₂}_μ 𝓛_{DB,g,ν̂} = (K₂^{λ₂} − r̂)[g'(r̂)(dν̂/dμ)λ₂]`, where `K₂^{λ₂}` is the forward edge
> kernel of Lemma `lem:lift_wellposed`.

> (proof) By Lemma `lem:lift_wellposed`, `(𝒮², λ₂, K₂)` satisfies the hypotheses of Theorem
> `theo:first_variation_full`; the formula is its specialization `T = K₂`, applied to the DB
> loss of Proposition `prop:db_lift`.

## Why this file exists

`GFNBounds/Balance/FirstVariation.lean` closed `theo:first_variation_full` on a finite state
space and recorded, in its SCOPE, that "`cor:gradient_formulas` […] and `cor:db_gradient` […]
are not stated"; `GFNBounds/Balance/Lift.lean` recorded the same for `cor:db_gradient`. This
file states and proves both, and it is written the way the paper writes them: as
*specializations*, not as re-derivations. Nothing below reproves a first variation, an adjoint
identity, or an edge-lift fact. The only genuinely new mathematics is three small things —
the row-stochasticity step of the second display, the differentiability of `|x−1|` off `1`, and
the `Prod`/curried bridge for `𝒮²` — and each is isolated in its own declaration.

## What is proved

| | |
|---|---|
| `hasDerivAt_loss_atStates`, `hasDerivAt_loss_ipL2_atStates` | `theo:first_variation_full` with `g` differentiable **only at the finitely many values `r` takes**, instead of on all of `ℝ_+^*`. Pure bookkeeping — the proof of `hasDerivAt_loss` never used more — and it is what makes the `|x−1|` case reachable at all |
| `densAct_reversal_eq_funAct` | `[φλ]π_→^λ` has `λ`-density `π_← φ`: the computational face of `lem:adjoint`*(3)*, used to evaluate the paper's displays |
| `fmGradDensity_eq` | **`cor:gradient_formulas`, first display**: at `ν = μ = F_←` the weight `dν/dμ` is `1`, and the gradient density is `(π_→^λ − r)[g'(r)λ]` |
| `hasDerivAt_fmLoss_ipL2` | **the first display as a derivative**: `δ𝓛_{g,F_←} = ⟨(π_→^λ − r)[g'(r)λ] ∣ δ⟩_λ` |
| `fmGradDensity_sq_eq` | **`cor:gradient_formulas`, second display**: `2(π_→^λ − r)[(r−1)λ] = 2(π_→^λ(rλ) − λ − r²λ + rλ)`. This is the one step that needs `π_←` **row-stochastic**, which `theo:first_variation_full` does not carry |
| `hasDerivAt_fmLoss_sq_ipL2` | the `g(x) = (x−1)²` case as a derivative, in the paper's own second form |
| `hasDerivAt_abs_sub_one` | `|z−1|` is differentiable at every `y ≠ 1`, with derivative `sign(y−1)` |
| `hasDerivAt_fmLoss_abs_ipL2` | **`cor:gradient_formulas`, the `g(x) = |x−1|` case**, under `r(x) ≠ 1` at every state. See SCOPE for why that hypothesis is there and what it costs |
| `twoState_hasDerivAt_fmLoss` | the FM formula **evaluated**: `5/16`, against a derivative computed by hand off the paper's display |
| `twoState_hasDerivAt_fmLoss_abs` | the same for `g(x) = |x−1|`: `3/8`, on a flow with `r = (3/4, 3/2)`, so the `ε(r)` branch is evaluated too |
| `edgeKernelProd`, `edgeMeasureProd`, `dualEdgeKernelProd` | `Lift.lean`'s curried `𝒮²` objects read on `V × V`, which is the shape `theo:first_variation_full` is stated in |
| `edgeMeasureProd_pos`, `edgeKernelProd_nonneg`, `invariant_edgeKernelProd` | the hypothesis check: `(𝒮², λ₂, K₂)` satisfies `theo:first_variation_full`'s hypotheses. `invariant_edgeKernelProd` is `Lift.pushEdge_edgeMeasure` re-indexed and nothing else |
| `isReversalPair_edgeKernelProd` | **`K₂^{λ₂}` *is* the forward edge kernel of `lem:lift_wellposed`** — `Lift.edgeKernel_dual` read as `Core.IsReversalPair` |
| `ratio_edgeKernelProd`, `ratio_edgeKernelProd_db` | **`r̂ = d(μK₂)/dμ` is `Lift`'s lifted balance ratio**, hence by `prop:db_lift` the detailed-balance edge ratio `F(s')π_←(s'→s)/(F(s)π_→^μ(s→s'))`. This is what makes the loss below the *DB* loss |
| `hasDerivAt_dbLoss_ipL2` | **`cor:db_gradient`**: `δ𝓛_{DB,g,ν̂} = ⟨(K₂^{λ₂} − r̂)[g'(r̂)(dν̂/dμ)λ₂] ∣ δ⟩_{λ₂}` |
| `twoStateEdge_hasDerivAt_dbLoss` | the DB formula **evaluated**: `−17/32`, against a derivative computed by hand off the paper's display |

## SCOPE (disclosed)

* **⚠ Finite state space**, inherited from `theo:first_variation_full` and not weakened here.
  Both corollaries are corollaries *of a finite-space theorem*, so `paper-map.json`'s bucket `D`
  for the general statements stands: nothing below builds a Radon–Nikodym calculus.
* **⚠ A directional derivative, not a Fréchet derivative**, inherited verbatim from
  `FirstVariation.lean`'s SCOPE. What is proved is
  `HasDerivAt (fun t => 𝓛(μ + tδ)) ⟨Φ ∣ δ⟩ 0` for every direction `δ`.
* **The training measure is frozen at the base point.** `cor:gradient_formulas` sets `ν = F_←`
  *and* `μ = F_←`, but `𝓛_{g,ν}` differentiates `μ` with `ν` held fixed — that is what
  `theo:first_variation_full` differentiates and what `Freezing.loss` models. So `ν` is carried
  as the constant `fun x => λ(x)u(x)`, the mass function of the base flow, and `dν/dμ = 1` is an
  identity **at the base point only**. Anything else would be a different loss.
* **The second display carries a hypothesis the theorem it specializes does not.**
  `theo:first_variation_full` is proved in `FirstVariation.lean` for a kernel that is only
  assumed non-negative (its checklist records row-stochasticity as "used nowhere"). Passing from
  `2(π_→^λ − r)[(r−1)λ]` to `2(π_→^λ(rλ) − λ − r²λ + rλ)` needs `π_←(s → 𝒮) = 1` — it is where
  the paper's `λπ_→^λ = λ` enters — so `hasDerivAt_fmLoss_sq_ipL2` and `fmGradDensity_sq_eq`
  carry `hrow : ∀ x, ∑ y, K x y = 1` and the first display does not. The paper has this for free,
  `π_←` being a Markov kernel by hypothesis of `lem:adjoint`; it is named here because it is the
  only hypothesis in the file that the parent theorem does not already supply.
* **`|x−1|` is not differentiable at `1`, and this file restricts rather than smooths.**
  `hasDerivAt_fmLoss_abs_ipL2` hypothesises `hne : ∀ x, ratio K lam u x ≠ 1` — the flow is
  nowhere balanced — and on that set `g'(r) = ε(r) = sign(r−1)` is a genuine derivative
  (`hasDerivAt_abs_sub_one`), so the corollary's display holds with no reinterpretation. **What
  this costs is named:** the excluded set is exactly `{r = 1}`, which by
  `MassIdentity.ratio_eq_one_iff_balanced` is the *balanced* flow — the minimiser, and the only
  point the surrounding theory cares about. So the `|x−1|` case is proved **away from the
  solution and nowhere else**, and the honest reading of the paper's "analogous, with `g'(r)`
  replaced by the sign of `r−1`" at a balanced or partially balanced flow is a *subgradient*
  statement, which needs a non-smooth first variation this library does not have and which is
  **not** claimed here. A subdifferential of `𝓛` is never mentioned below; `Real.sign 0 = 0`
  appears only as the value of a function, never as a derivative.
* **The `Prod`/curried bridge, and what it cost.** `theo:first_variation_full` is stated over a
  single `Fintype V`; `Lift.lean` models `𝒮²` in curried form (`V → V → ℝ` for measures,
  `V → V → V → V → ℝ` for kernels). This file instantiates the theorem at `V × V` and bridges,
  rather than restating `Lift`. The bridge is three one-line definitions
  (`edgeKernelProd`, `edgeMeasureProd`, `dualEdgeKernelProd`, each `fun p q => … p.1 p.2 q.1 q.2`)
  and six short lemmas, and the *only* place currying is felt is
  `Fintype.sum_prod_type`, which turns `∑ p : V × V` into `∑ s, ∑ s'` and makes
  `Lift.pushEdge` and `MassIdentity.pushMass` literally the same sum — twice, in
  `invariant_edgeKernelProd` and `ratio_edgeKernelProd`, and nowhere else. **The mismatch was not
  the obstacle** — it cost about forty lines of proof and no mathematics — so a `Prod`-shaped
  restatement of `Lift.lean` is *not* recommended: it would move the same forty lines to the
  other side of the boundary and lose the readable `λ₂(s,s') = π_←(s'→s)λ(s')` of the curried
  form, in which the backward policy is visibly read at the second coordinate.
* **⚠ The real restriction on `cor:db_gradient` is `λ₂ > 0`, and it is a positivity assumption on
  `π_←`, not a technicality.** `theo:first_variation_full` needs `μ ∼ λ` — in the finite model,
  `hlam : ∀ x, 0 < lam x` — because `r = d(μT)/dμ` divides by `λ(x)u(x)`. On `𝒮²` that reads
  `λ₂(s,s') = π_←(s'→s)λ(s') > 0` at **every** pair, i.e. `π_←` is positive on all of `𝒮 × 𝒮`.
  On a marked graph `π̂_←` vanishes off the edges, so the theorem below does **not** apply to a
  sparse graph as stated. This is not a defect of the corollary: the paper's own `μ ∼ λ₂`
  confines the edge flow to the support of `λ₂`, so the correct general statement is
  `theo:first_variation_full` instantiated on the **edge set**
  `E = {(s,s') : π_←(s'→s)λ(s') > 0}`, a subtype of `V × V` that `K₂` preserves whenever `λ > 0`
  on `𝒮`. That instantiation is *not* done here; it is the one substantive gap this file leaves,
  and it is arithmetic on `Finset.sum_subtype`, not new mathematics.
* **The window lift `K_ℓ`, `ℓ ≥ 3`, is untouched**, as `Lift.lean`'s SCOPE records: `λ_ℓ` needs a
  path-measure construction on `𝒮^ℓ`. Accordingly `prop:tb_gradient` and `prop:tb_hessian` are
  **not** attempted and are not mentioned outside this sentence.
* **`g` is carried by a derivative only**, as in `FirstVariation.lean`: the hypothesis is
  `∀ y, 0 < y → HasDerivAt g (gd y) y`, or its pointwise weakening. Continuity of `g'` and the
  local Lipschitz bound of the paper are not carried; see `FirstVariation.lean`'s SCOPE for why
  the finite-dimensional chain rule replaces them.
* **The `sorry` list is empty and this file adds nothing to it.**

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the hypotheses of `theo:first_variation_full` | ⚠ inherited **on a finite space**, with its own checklist unchanged: `𝒮` Polish becomes `[Fintype V]`, `dμ/dλ ∈ L²`, `μT ≪ μ` and the `L^∞` conditions are vacuous, `r > 0` is derived (`MassIdentity.ratio_pos`) |
| `T = π_←` a backward policy, `λ` invariant | ✓ `hinv : Invariant K lam`, `hK : ∀ x y, 0 ≤ K x y`; row-stochasticity `hrow` **only** in the second display, where it is genuinely used |
| `μ = F_←`, `ν = F_←`, `ν_G = λ` | ✓ `μ = uλ` with `hu : ∀ x, 0 < u x`, `ν = λu` frozen, `ν_G = λ` (the appendix's standing choice, `proofs.tex:22`) |
| `g` continuously differentiable with locally Lipschitz `g'` | ⚠ **weakened** to a derivative at the relevant points; see SCOPE |
| `g(x) = (x−1)²` | ✓ `hasDerivAt_fmLoss_sq_ipL2`, in both of the paper's forms |
| `g(x) = |x−1|`, `g'(r) = ε(r)` a.e. | ⚠ **restricted to `r ≠ 1`**; the "a.e." of the paper is not formalized as an a.e. statement. See SCOPE |
| `theo:first_variation_full` applies on `(𝒮², λ₂, K₂)` (`lem:lift_wellposed`) | ✓ `invariant_edgeKernelProd`, `edgeKernelProd_nonneg`, `edgeMeasureProd_pos` — invariance is `Lift.pushEdge_edgeMeasure` re-indexed |
| `λ₂` non-zero and `μ ∼ λ₂` | ⚠ **strengthened to `λ₂ > 0` everywhere**, hence `π_←` positive on every pair. See SCOPE — this excludes sparse graphs |
| `K₂^{λ₂}` the forward edge kernel of `lem:lift_wellposed` | ✓ `isReversalPair_edgeKernelProd`, from `Lift.edgeKernel_dual`; `π_→^λ` is hypothesised abstractly by `hpf` exactly as `Lift.lean` does, and is discharged there by `Graph.Universality.reversal` |
| `r̂ = d(μK₂)/dμ` and `𝓛_{DB,g,ν̂}` the DB loss | ✓ `ratio_edgeKernelProd`, `ratio_edgeKernelProd_db`: the ratio is `Lift.pushEdge μ / μ`, which `prop:db_lift` identifies with the detailed-balance edge ratio |
| `ν̂` a training distribution on `𝒮²` | ⚠ an arbitrary `nuhat : V × V → ℝ`, as in `Lift.lean` |
| the window lift `K_ℓ`, `ℓ ≥ 3` | ✗ **absent**, as in `Lift.lean` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset

variable {V : Type*} [Fintype V]

/-! ### `theo:first_variation_full` with `g` differentiated only where the ratio lands

`FirstVariation.hasDerivAt_loss` asks `∀ y, 0 < y → HasDerivAt g (gd y) y`. Its proof uses that
hypothesis at the finitely many values `ratio K lam u z`, and nowhere else. The weakening below
is therefore free, and it is what the `|x−1|` case of `cor:gradient_formulas` needs: `|x−1|` is
differentiable at every positive `y` **except** `y = 1`, so the global hypothesis is
unsatisfiable for it while the pointwise one is not. -/

/-- **`proofs.tex:469–470` with a pointwise differentiability hypothesis**: the first variation
of the balance loss, before the adjoint step, asking only that `g` be differentiable at each
value the ratio takes.

Line for line `FirstVariation.hasDerivAt_loss`, with `hr` and `hg` replaced by their single
consequence. -/
theorem hasDerivAt_loss_atStates {K : V → V → ℝ} {lam nu u : V → ℝ} {g : ℝ → ℝ} {gdv : V → ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x)
    (hg : ∀ z : V, HasDerivAt g (gdv z) (ratio K lam u z)) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g)
      (∑ x, nu x * (gdv x *
        (dirPush K lam u d x - ratio K lam u x * dirDens u d x))) 0 := by
  have hz : (fun w => u w + (0 : ℝ) * d w) = u := by funext w; ring
  simp only [loss]
  refine HasDerivAt.fun_sum fun z _ => HasDerivAt.const_mul (nu z) ?_
  have hpt : HasDerivAt (fun t : ℝ => ratio K lam (fun w => u w + t * d w) z)
      (dirPush K lam u d z - ratio K lam u z * dirDens u d z) 0 :=
    hasDerivAt_ratio hlam hu d z
  have hgz : HasDerivAt g (gdv z) (ratio K lam (fun w => u w + (0 : ℝ) * d w) z) := by
    rw [hz]; exact hg z
  exact hgz.comp (0 : ℝ) hpt

/-- **`theo:first_variation_full` at `ν_G = λ`, with a pointwise differentiability hypothesis.**
`FirstVariation.hasDerivAt_loss_ipL2` with `hg` weakened; the adjoint step
(`FirstVariation.firstVariation_adjoint`) is reused unchanged, which is why the represented
density is still `MassIdentity.lossGradDensity`. -/
theorem hasDerivAt_loss_ipL2_atStates {K : V → V → ℝ} {lam nu u : V → ℝ} {g gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x)
    (hg : ∀ z : V, HasDerivAt g (gd (ratio K lam u z)) (ratio K lam u z)) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam nu (fun x => u x + t * d x) g)
      (Graph.ipL2 lam (lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd) d) 0 := by
  rw [← firstVariation_adjoint hinv hK hlam hu d]
  exact hasDerivAt_loss_atStates hlam hu hg d

/-! ### The computational face of `lem:adjoint`*(3)*

`[φλ]T^λ` has `λ`-density `Tφ`. `FirstVariation.gradDensity_eq_densAct_reversal` uses this to put
`gradDensity` in the paper's `(T^λ − r)[φλ]` form; the same identity read the other way is what
evaluates the paper's displays on an instance. -/

/-- **`d([φλ]π_→^λ)/dλ = π_← φ`** (`proofs.tex:407`, `:442`), at every state carrying `λ`-mass:
the density action of the `λ`-reversal is the function action of the kernel. This is
`Core.funAct_eq_densAct_reversal` on the pair `(K, K^λ)`, packaged so that the paper's
`π_→^λ[·]` can be computed. -/
theorem densAct_reversal_eq_funAct {K : V → V → ℝ} {lam : V → ℝ} (hinv : Invariant K lam)
    (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) (phi : V → ℝ) (x : V) :
    Core.densAct lam (Core.reversal lam K) phi x = funAct K phi x := by
  have hI : Core.IsInvariant lam K := ⟨fun z => (hlam z).le, hinv⟩
  exact Core.funAct_eq_densAct_reversal (hI.isReversalPair_reversal hK) phi (hlam x).ne'

/-! ### `cor:gradient_formulas`: the FM gradient

`ν = μ = F_←`, so `dν/dμ = 1` and the general formula collapses to `(π_→^λ − r)[g'(r)λ]`. The
training measure is the constant `x ↦ λ(x)u(x)` — the mass function of the base flow — and is
held fixed while `μ` varies; see the module SCOPE. -/

/-- **`cor:gradient_formulas`, the first display, on densities** (`proofs.tex:488`): at
`ν = μ = F_←` the weight `dν/dμ` is `1`, so `MassIdentity.lossGradDensity` is the paper's
`(π_→^λ − r)[g'(r)λ]` with no weight left in the bracket. -/
theorem fmGradDensity_eq {K : V → V → ℝ} {lam u : V → ℝ} (hinv : Invariant K lam)
    (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x) (gd : ℝ → ℝ) (x : V) :
    lossGradDensity K lam u (fun z => lam z * u z / (lam z * u z)) gd x
      = Core.densAct lam (Core.reversal lam K) (fun y => gd (ratio K lam u y)) x
        - ratio K lam u x * gd (ratio K lam u x) := by
  have hw : ∀ z : V, gd (ratio K lam u z) * (lam z * u z / (lam z * u z))
      = gd (ratio K lam u z) := fun z => by
    rw [div_self (mul_pos (hlam z) (hu z)).ne', mul_one]
  simp only [lossGradDensity, hw]
  exact gradDensity_eq_densAct_reversal hinv hK hlam _ _ x

/-- **`cor:gradient_formulas`, the first display** (`proofs.tex:487–489`): the derivative of
`t ↦ 𝓛_{g,F_←}(F_← + tδ)` at `t = 0` is `⟨(π_→^λ − r)[g'(r)λ] ∣ δ⟩_λ`.

`theo:first_variation_full` at `T = π_←`, `μ = F_←`, `ν = F_←`, `ν_G = λ`, which is the paper's
own proof. Nothing is recomputed: `FirstVariation.hasDerivAt_loss_ipL2` supplies the derivative
and `fmGradDensity_eq` puts its density in the corollary's form. -/
theorem hasDerivAt_fmLoss_ipL2 {K : V → V → ℝ} {lam u : V → ℝ} {g gd : ℝ → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam (fun x => lam x * u x) (fun x => u x + t * d x) g)
      (Graph.ipL2 lam (fun x =>
        Core.densAct lam (Core.reversal lam K) (fun y => gd (ratio K lam u y)) x
          - ratio K lam u x * gd (ratio K lam u x)) d) 0 := by
  have hD := hasDerivAt_loss_ipL2 (nu := fun x => lam x * u x) (gd := gd) hinv hK hlam hu hg d
  have heq : Graph.ipL2 lam
      (lossGradDensity K lam u (fun z => lam z * u z / (lam z * u z)) gd) d
      = Graph.ipL2 lam (fun x =>
        Core.densAct lam (Core.reversal lam K) (fun y => gd (ratio K lam u y)) x
          - ratio K lam u x * gd (ratio K lam u x)) d :=
    Finset.sum_congr rfl fun x _ => by rw [fmGradDensity_eq hinv hK hlam hu gd x]
  rwa [heq] at hD

/-- **`cor:gradient_formulas`, the second display's expansion** (`proofs.tex:493–494`):

    2(π_→^λ − r)[(r−1)λ] = 2(π_→^λ(rλ) − λ − r²λ + rλ),

read on `λ`-densities. This is the *only* step of the corollary that needs `π_←` to be
row-stochastic — it is the paper's "using `λπ_→^λ = λ`" — and `theo:first_variation_full` does
not carry it; see the module SCOPE. -/
theorem fmGradDensity_sq_eq {K : V → V → ℝ} {lam u : V → ℝ} (hinv : Invariant K lam)
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hlam : ∀ x, 0 < lam x) (x : V) :
    Core.densAct lam (Core.reversal lam K) (fun y => 2 * (ratio K lam u y - 1)) x
        - ratio K lam u x * (2 * (ratio K lam u x - 1))
      = 2 * (Core.densAct lam (Core.reversal lam K) (ratio K lam u) x - 1
          - ratio K lam u x ^ 2 + ratio K lam u x) := by
  rw [densAct_reversal_eq_funAct hinv hK hlam _ x,
    densAct_reversal_eq_funAct hinv hK hlam (ratio K lam u) x]
  have hsplit : funAct K (fun y => 2 * (ratio K lam u y - 1)) x
      = 2 * funAct K (ratio K lam u) x - 2 * ∑ y, K x y := by
    simp only [funAct, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hsplit, hrow x]
  ring

/-- **`cor:gradient_formulas` for `g(x) = (x−1)²`** (`proofs.tex:492–494`), in the paper's own
second form `2(π_→^λ(rλ) − λ − r²λ + rλ)`. -/
theorem hasDerivAt_fmLoss_sq_ipL2 {K : V → V → ℝ} {lam u : V → ℝ} (hinv : Invariant K lam)
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam (fun x => lam x * u x) (fun x => u x + t * d x)
        fun z => (z - 1) ^ 2)
      (Graph.ipL2 lam (fun x => 2 * (Core.densAct lam (Core.reversal lam K) (ratio K lam u) x
        - 1 - ratio K lam u x ^ 2 + ratio K lam u x)) d) 0 := by
  have hg : ∀ y : ℝ, 0 < y → HasDerivAt (fun z : ℝ => (z - 1) ^ 2) (2 * (y - 1)) y := fun y _ => by
    simpa using ((hasDerivAt_id' y).sub_const 1).fun_pow 2
  have hD := hasDerivAt_fmLoss_ipL2 (gd := fun z => 2 * (z - 1)) hinv hK hlam hu hg d
  have heq : (fun x =>
        Core.densAct lam (Core.reversal lam K) (fun y => 2 * (ratio K lam u y - 1)) x
          - ratio K lam u x * (2 * (ratio K lam u x - 1)))
      = fun x => 2 * (Core.densAct lam (Core.reversal lam K) (ratio K lam u) x
        - 1 - ratio K lam u x ^ 2 + ratio K lam u x) :=
    funext fun x => fmGradDensity_sq_eq (u := u) hinv hK hrow hlam x
  rwa [heq] at hD

/-! ### `cor:gradient_formulas` for `g(x) = |x−1|`

The paper writes "the case `g(x) = |x−1|` is analogous, with `g'(r)` replaced by the sign of
`r−1`", and its proof adds "`g'(r) = ε(r)` almost everywhere". `|x−1|` has no derivative at `1`,
so the statement below **restricts to flows with `r(x) ≠ 1` at every state**; the module SCOPE
says what that excludes and why no subgradient claim is made. -/

/-- **`|z−1|` is differentiable off `1`**, with derivative the sign of `y−1`. Away from `1` the
absolute value coincides with an affine function on a neighbourhood, which is the whole
content. -/
theorem hasDerivAt_abs_sub_one {y : ℝ} (hy : y ≠ 1) :
    HasDerivAt (fun z : ℝ => |z - 1|) (Real.sign (y - 1)) y := by
  rcases lt_or_gt_of_ne hy with h | h
  · have hev : (fun z : ℝ => |z - 1|) =ᶠ[nhds y] fun z : ℝ => 1 - z := by
      filter_upwards [isOpen_Iio.mem_nhds (show y ∈ Set.Iio (1 : ℝ) from h)] with z hz
      rw [abs_of_neg (by simpa using (sub_neg (a := z) (b := (1 : ℝ))).mpr hz)]
      ring
    have hd : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) y := by
      simpa using (hasDerivAt_id' y).const_sub (1 : ℝ)
    rw [Real.sign_of_neg (by linarith)]
    exact hd.congr_of_eventuallyEq hev
  · have hev : (fun z : ℝ => |z - 1|) =ᶠ[nhds y] fun z : ℝ => z - 1 := by
      filter_upwards [isOpen_Ioi.mem_nhds (show y ∈ Set.Ioi (1 : ℝ) from h)] with z hz
      exact abs_of_pos (by linarith [Set.mem_Ioi.mp hz])
    have hd : HasDerivAt (fun z : ℝ => z - 1) (1 : ℝ) y := (hasDerivAt_id' y).sub_const 1
    rw [Real.sign_of_pos (by linarith)]
    exact hd.congr_of_eventuallyEq hev

/-- **`cor:gradient_formulas` for `g(x) = |x−1|`** (`proofs.tex:497`, `:501`), on a flow that is
nowhere balanced: `g'(r)` is `ε(r) = sign(r−1)` and the first display holds unchanged,

    ∇^λ_{F_←} 𝓛_{g,F_←} = (π_→^λ − r)[ε(r)λ].

The hypothesis `hne` is the price of `|x−1|`'s corner: at a state with `r(x) = 1` the loss is not
differentiable in the direction that moves that ratio, and no derivative is claimed there. Since
`{r ≡ 1}` is exactly the balanced flow (`MassIdentity.ratio_eq_one_iff_balanced`), this proves
the case **away from the solution**; see the module SCOPE. -/
theorem hasDerivAt_fmLoss_abs_ipL2 {K : V → V → ℝ} {lam u : V → ℝ} (hinv : Invariant K lam)
    (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x)
    (hne : ∀ x, ratio K lam u x ≠ 1) (d : V → ℝ) :
    HasDerivAt (fun t : ℝ => loss K lam (fun x => lam x * u x) (fun x => u x + t * d x)
        fun z => |z - 1|)
      (Graph.ipL2 lam (fun x =>
        Core.densAct lam (Core.reversal lam K)
            (fun y => Real.sign (ratio K lam u y - 1)) x
          - ratio K lam u x * Real.sign (ratio K lam u x - 1)) d) 0 := by
  have hD := hasDerivAt_loss_ipL2_atStates (nu := fun x => lam x * u x)
    (g := fun z : ℝ => |z - 1|) (gd := fun z => Real.sign (z - 1)) hinv hK hlam hu
    (fun z => hasDerivAt_abs_sub_one (hne z)) d
  have heq : Graph.ipL2 lam
      (lossGradDensity K lam u (fun z => lam z * u z / (lam z * u z))
        fun z => Real.sign (z - 1)) d
      = Graph.ipL2 lam (fun x =>
        Core.densAct lam (Core.reversal lam K)
            (fun y => Real.sign (ratio K lam u y - 1)) x
          - ratio K lam u x * Real.sign (ratio K lam u x - 1)) d :=
    Finset.sum_congr rfl fun x _ => by
      rw [fmGradDensity_eq hinv hK hlam hu (fun z => Real.sign (z - 1)) x]
  rwa [heq] at hD

/-! ### `cor:gradient_formulas`, evaluated

A formula that has never been evaluated is a formula nobody has checked, and a formula proved by
`ring` from the library's own definitions says nothing about whether those definitions are the
paper's. The two-state chain of `prop:nonlinear_freezing`*(2)* is the cheapest instance; note
that it is a **different** number from `FirstVariation.twoState_hasDerivAt_loss`, which takes `ν`
to be the counting measure, whereas `cor:gradient_formulas` takes `ν = F_←`. -/

/-- **`cor:gradient_formulas` evaluated.** On `π_←(i→j) = 1/2`, `λ = (1/2,1/2)`, `F_← = (1,1/2)`
— i.e. `u = (2,1)`, and `ν = F_←`, so `dν/dμ ≡ 1` — with `g(x) = (x−1)²`, the derivative of
`t ↦ 𝓛_{g,F_←}(F_← + tδ)` along `δ = (1,0)·λ` is `5/16`.

Computed by hand off the paper's display, twice, without the library.

*From the loss.* `r_t = ((3+t)/(2(2+t)), (3+t)/2)`, so `r = (3/4, 3/2)` and `ṙ = (−1/8, 1/2)`;
`𝓛̇ = ∑ ν(x) g'(r(x)) ṙ(x) = 1·2(3/4−1)(−1/8) + (1/2)·2(3/2−1)(1/2) = 1/16 + 1/4 = 5/16`.

*From the gradient.* `π_→^λ(rλ)` has `λ`-density `π_← r ≡ (1/2)(3/4) + (1/2)(3/2) = 9/8`, so the
second display gives `2(9/8 − 1 − r² + r)`, i.e. `5/8` at state `0` and `−5/4` at state `1`; then
`⟨∇ ∣ δ⟩_λ = (1/2)(5/8)(1) + (1/2)(−5/4)(0) = 5/16`. The two agree. -/
theorem twoState_hasDerivAt_fmLoss :
    HasDerivAt (fun t : ℝ => loss twoStateK twoStateLam
        (fun x => twoStateLam x * twoStateU x)
        (fun x => twoStateU x + t * (![1, 0] : Fin 2 → ℝ) x) fun z => (z - 1) ^ 2)
      (5 / 16) 0 := by
  have hrow : ∀ x : Fin 2, ∑ y, twoStateK x y = 1 := by
    intro x; simp [twoStateK]
  have hK : ∀ x y : Fin 2, 0 ≤ twoStateK x y := fun _ _ => by norm_num [twoStateK]
  have hD := hasDerivAt_fmLoss_sq_ipL2 twoStateK_invariant hK hrow twoStateLam_pos
    twoStateU_pos (![1, 0] : Fin 2 → ℝ)
  have hval : Graph.ipL2 twoStateLam
      (fun x => 2 * (Core.densAct twoStateLam (Core.reversal twoStateLam twoStateK)
        (ratio twoStateK twoStateLam twoStateU) x - 1
        - ratio twoStateK twoStateLam twoStateU x ^ 2
        + ratio twoStateK twoStateLam twoStateU x)) (![1, 0] : Fin 2 → ℝ) = 5 / 16 := by
    have hd : ∀ x : Fin 2, Core.densAct twoStateLam (Core.reversal twoStateLam twoStateK)
        (ratio twoStateK twoStateLam twoStateU) x
          = funAct twoStateK (ratio twoStateK twoStateLam twoStateU) x := fun x =>
      densAct_reversal_eq_funAct twoStateK_invariant hK twoStateLam_pos _ x
    simp only [Graph.ipL2, Fin.sum_univ_two, hd, funAct, Fin.sum_univ_two,
      twoState_ratio_zero, twoState_ratio_one]
    norm_num [twoStateK, twoStateLam]
  rwa [hval] at hD

/-- **`cor:gradient_formulas` evaluated for `g(x) = |x−1|`.** The same chain and the same
direction: `r = (3/4, 3/2)`, nowhere `1`, so `hasDerivAt_fmLoss_abs_ipL2` applies and
`ε(r) = (−1, +1)`.

By hand off the paper's display: `π_→^λ[ε(r)λ]` has `λ`-density `π_← ε(r) ≡ (1/2)(−1) + (1/2)(1)
= 0`, so `(π_→^λ − r)[ε(r)λ]` has density `(0 + 3/4, 0 − 3/2) = (3/4, −3/2)` and
`⟨∇ ∣ δ⟩_λ = (1/2)(3/4)(1) + (1/2)(−3/2)(0) = 3/8`. From the loss:
`𝓛 = ν(0)|r_t(0)−1| + ν(1)|r_t(1)−1| = (1−r_t(0)) + (1/2)(r_t(1)−1)` near `t = 0`, whose
derivative is `−(−1/8) + (1/2)(1/2) = 3/8`. The two agree. -/
theorem twoState_hasDerivAt_fmLoss_abs :
    HasDerivAt (fun t : ℝ => loss twoStateK twoStateLam
        (fun x => twoStateLam x * twoStateU x)
        (fun x => twoStateU x + t * (![1, 0] : Fin 2 → ℝ) x) fun z => |z - 1|)
      (3 / 8) 0 := by
  have hK : ∀ x y : Fin 2, 0 ≤ twoStateK x y := fun _ _ => by norm_num [twoStateK]
  have hne : ∀ x : Fin 2, ratio twoStateK twoStateLam twoStateU x ≠ 1 := fun x => by
    match x with
    | 0 => rw [twoState_ratio_zero]; norm_num
    | 1 => rw [twoState_ratio_one]; norm_num
  have hD := hasDerivAt_fmLoss_abs_ipL2 twoStateK_invariant hK twoStateLam_pos twoStateU_pos hne
    (![1, 0] : Fin 2 → ℝ)
  have hval : Graph.ipL2 twoStateLam (fun x =>
      Core.densAct twoStateLam (Core.reversal twoStateLam twoStateK)
          (fun y => Real.sign (ratio twoStateK twoStateLam twoStateU y - 1)) x
        - ratio twoStateK twoStateLam twoStateU x
          * Real.sign (ratio twoStateK twoStateLam twoStateU x - 1))
      (![1, 0] : Fin 2 → ℝ) = 3 / 8 := by
    have hd : ∀ x : Fin 2, Core.densAct twoStateLam (Core.reversal twoStateLam twoStateK)
        (fun y => Real.sign (ratio twoStateK twoStateLam twoStateU y - 1)) x
          = funAct twoStateK
            (fun y => Real.sign (ratio twoStateK twoStateLam twoStateU y - 1)) x := fun x =>
      densAct_reversal_eq_funAct twoStateK_invariant hK twoStateLam_pos _ x
    have hs0 : Real.sign ((3 : ℝ) / 4 - 1) = -1 := Real.sign_of_neg (by norm_num)
    have hs1 : Real.sign ((3 : ℝ) / 2 - 1) = 1 := Real.sign_of_pos (by norm_num)
    simp only [Graph.ipL2, Fin.sum_univ_two, hd, funAct, twoState_ratio_zero,
      twoState_ratio_one, hs0, hs1]
    norm_num [twoStateK, twoStateLam]
  rwa [hval] at hD

/-! ### `cor:db_gradient`: the DB gradient

`theo:first_variation_full` on `(𝒮², λ₂, K₂)`. `GFNBounds/Balance/Lift.lean` has the whole
`ℓ = 2` layer already — `lem:lift_wellposed` and `prop:db_lift`, both `sorry`-free — in **curried**
form (`V → V → ℝ`), while the theorem is stated over a single `Fintype`. This section reads
`Lift`'s objects on `V × V` and checks the hypotheses; it proves no new fact about the edge
lift. -/

section Edge

variable [DecidableEq V]

/-- `K₂` on `V × V`: `Lift.edgeKernel` uncurried, which is the shape
`theo:first_variation_full` takes a kernel in. -/
def edgeKernelProd (pb : V → V → ℝ) : V × V → V × V → ℝ :=
  fun p q => edgeKernel pb p.1 p.2 q.1 q.2

/-- `λ₂` on `V × V`: `Lift.edgeMeasure` uncurried, `λ₂(s,s') = π_←(s'→s)λ(s')`. -/
def edgeMeasureProd (pb : V → V → ℝ) (lam : V → ℝ) : V × V → ℝ :=
  fun p => edgeMeasure pb lam p.1 p.2

/-- `K₂^{λ₂}` on `V × V`: `Lift.dualEdgeKernel` uncurried — the forward edge kernel
`(s,s') ↦ (s', π_→^λ(s'))` of `lem:lift_wellposed`. -/
def dualEdgeKernelProd (pf : V → V → ℝ) : V × V → V × V → ℝ :=
  fun p q => dualEdgeKernel pf p.1 p.2 q.1 q.2

omit [Fintype V] in
/-- `K₂ ≥ 0` — `Lift.edgeKernel_nonneg`, re-indexed. -/
theorem edgeKernelProd_nonneg {pb : V → V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y) (p q : V × V) :
    0 ≤ edgeKernelProd pb p q :=
  edgeKernel_nonneg hnn p.1 p.2 q.1 q.2

omit [Fintype V] [DecidableEq V] in
/-- **`λ₂ > 0` everywhere**, which is what `theo:first_variation_full`'s `μ ∼ λ` becomes on `𝒮²`
in the finite model. It forces `π_←` to be positive on *every* pair; see the module SCOPE, where
this is the file's one substantive restriction. -/
theorem edgeMeasureProd_pos {pb : V → V → ℝ} {lam : V → ℝ} (hpb : ∀ x y, 0 < pb x y)
    (hlam : ∀ x, 0 < lam x) (p : V × V) : 0 < edgeMeasureProd pb lam p :=
  mul_pos (hpb p.2 p.1) (hlam p.2)

/-- **`lem:lift_wellposed`, invariance, on `V × V`**: `λ₂ K₂ = λ₂`.

This is `Lift.pushEdge_edgeMeasure` and nothing else; `Fintype.sum_prod_type` is the entire
bridge, because `∑_{p : V × V} λ₂(p) K₂(p,q)` and `Lift.pushEdge` are the same double sum. -/
theorem invariant_edgeKernelProd {pb : V → V → ℝ} {lam : V → ℝ} (hinv : Invariant pb lam) :
    Invariant (edgeKernelProd pb) (edgeMeasureProd pb lam) := by
  intro q
  have hsum : ∑ p : V × V, edgeMeasureProd pb lam p * edgeKernelProd pb p q
      = pushEdge pb (edgeMeasure pb lam) q.1 q.2 := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [hsum, pushEdge_edgeMeasure hinv]
  rfl

omit [Fintype V] in
/-- **`K₂^{λ₂}` *is* the forward edge kernel of `lem:lift_wellposed`** (`proofs.tex:513`,
`:521`): `(λ₂, K₂, K₂*)` is a reversal pair in the sense of `lem:adjoint`*(1)*.

`Lift.edgeKernel_dual` proves the pointwise identity `λ₂ ⊗ K₂ = K₂* ⊗ λ₂`; `Core.IsReversalPair`
is that identity with the two arguments read in the other order. Nothing is recomputed. -/
theorem isReversalPair_edgeKernelProd {pb pf : V → V → ℝ} {lam : V → ℝ}
    (hpf : ∀ x y, lam x * pf x y = lam y * pb y x) :
    Core.IsReversalPair (edgeMeasureProd pb lam) (edgeKernelProd pb) (dualEdgeKernelProd pf) :=
  fun p q => (edgeKernel_dual hpf q.1 q.2 p.1 p.2).symm

/-- **`r̂ = d(μK₂)/dμ` is `Lift`'s lifted balance ratio**: for the edge flow `μ = u·λ₂`,
`MassIdentity.ratio` on `(𝒮², λ₂, K₂)` is `Lift.pushEdge μ / μ`. The bridge is again
`Fintype.sum_prod_type` alone. -/
theorem ratio_edgeKernelProd (pb : V → V → ℝ) (lam : V → ℝ) (u : V × V → ℝ) (p : V × V) :
    ratio (edgeKernelProd pb) (edgeMeasureProd pb lam) u p
      = pushEdge pb (fun a b => u (a, b) * edgeMeasure pb lam a b) p.1 p.2
          / (edgeMeasureProd pb lam p * u p) := by
  have hnum : pushMass (edgeKernelProd pb) (edgeMeasureProd pb lam) u p
      = pushEdge pb (fun a b => u (a, b) * edgeMeasure pb lam a b) p.1 p.2 := by
    rw [pushMass, Fintype.sum_prod_type, pushEdge]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by
      simp only [edgeMeasureProd, edgeKernelProd]; ring
  rw [ratio, hnum]

/-- **`r̂` is the detailed-balance edge ratio** (`prop:db_lift`, `proofs.tex:528`):

    r̂(s,s') = F(s') π_←(s'→s) / (F(s) π_→^μ(s→s')),   F = m₁μ,

so the loss differentiated below really is the `g`-divergence DB loss with frozen backward
policy. `Lift.db_lift_ratio` is the whole proof. -/
theorem ratio_edgeKernelProd_db (pb : V → V → ℝ) (lam : V → ℝ) (u : V × V → ℝ)
    (hmu : ∀ s s', 0 ≤ u (s, s') * edgeMeasure pb lam s s') (p : V × V) :
    ratio (edgeKernelProd pb) (edgeMeasureProd pb lam) u p
      = marg₁ (fun a b => u (a, b) * edgeMeasure pb lam a b) p.2 * pb p.2 p.1
          / (marg₁ (fun a b => u (a, b) * edgeMeasure pb lam a b) p.1
              * disint (fun a b => u (a, b) * edgeMeasure pb lam a b) p.1 p.2) := by
  rw [ratio_edgeKernelProd, ← db_lift_ratio hmu p.1 p.2]
  simp only [edgeMeasureProd]
  ring_nf

/-- **`cor:db_gradient`** (`proofs.tex:539–542`): the derivative of `t ↦ 𝓛_{DB,g,ν̂}(μ + tδ)` at
`t = 0` is `⟨(K₂^{λ₂} − r̂)[g'(r̂)(dν̂/dμ)λ₂] ∣ δ⟩_{λ₂}`.

This is `theo:first_variation_full` at `T = K₂`, `λ = λ₂`, exactly as the paper's proof says. The
hypotheses it needs on `(𝒮², λ₂, K₂)` are `lem:lift_wellposed`'s, discharged by
`invariant_edgeKernelProd` and `edgeKernelProd_nonneg`; the identification of `K₂^{λ₂}` with the
forward edge kernel is `isReversalPair_edgeKernelProd`; and `r̂ = d(μK₂)/dμ` is
`ratio_edgeKernelProd`. `hpb` and `hlam` deliver `λ₂ > 0`, which is the module SCOPE's one real
restriction. -/
theorem hasDerivAt_dbLoss_ipL2 {pb pf : V → V → ℝ} {lam : V → ℝ} {nuhat u : V × V → ℝ}
    {g gd : ℝ → ℝ} (hinv : Invariant pb lam) (hpb : ∀ x y, 0 < pb x y) (hlam : ∀ x, 0 < lam x)
    (hpf : ∀ x y, lam x * pf x y = lam y * pb y x) (hu : ∀ p, 0 < u p)
    (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y) (d : V × V → ℝ) :
    HasDerivAt (fun t : ℝ => loss (edgeKernelProd pb) (edgeMeasureProd pb lam) nuhat
        (fun p => u p + t * d p) g)
      (Graph.ipL2 (edgeMeasureProd pb lam) (fun p =>
        Core.densAct (edgeMeasureProd pb lam) (dualEdgeKernelProd pf)
            (fun q => gd (ratio (edgeKernelProd pb) (edgeMeasureProd pb lam) u q)
              * (nuhat q / (edgeMeasureProd pb lam q * u q))) p
          - ratio (edgeKernelProd pb) (edgeMeasureProd pb lam) u p
            * (gd (ratio (edgeKernelProd pb) (edgeMeasureProd pb lam) u p)
              * (nuhat p / (edgeMeasureProd pb lam p * u p)))) d) 0 := by
  have hlam₂ : ∀ p : V × V, 0 < edgeMeasureProd pb lam p := edgeMeasureProd_pos hpb hlam
  have hK₂ : ∀ p q : V × V, 0 ≤ edgeKernelProd pb p q :=
    edgeKernelProd_nonneg fun x y => (hpb x y).le
  have hD := hasDerivAt_loss_ipL2 (nu := nuhat) (gd := gd)
    (invariant_edgeKernelProd hinv) hK₂ hlam₂ hu hg d
  have heq : lossGradDensity (edgeKernelProd pb) (edgeMeasureProd pb lam) u
        (fun q => nuhat q / (edgeMeasureProd pb lam q * u q)) gd
      = fun p => Core.densAct (edgeMeasureProd pb lam) (dualEdgeKernelProd pf)
            (fun q => gd (ratio (edgeKernelProd pb) (edgeMeasureProd pb lam) u q)
              * (nuhat q / (edgeMeasureProd pb lam q * u q))) p
          - ratio (edgeKernelProd pb) (edgeMeasureProd pb lam) u p
            * (gd (ratio (edgeKernelProd pb) (edgeMeasureProd pb lam) u p)
              * (nuhat p / (edgeMeasureProd pb lam p * u p))) := by
    funext p
    simp only [lossGradDensity, gradDensity]
    rw [Core.funAct_eq_densAct_reversal (isReversalPair_edgeKernelProd hpf) _ (hlam₂ p).ne']
    rfl
  rwa [heq] at hD

/-! ### `cor:db_gradient`, evaluated

The same discipline as `twoState_hasDerivAt_fmLoss`: a number computed by hand off the paper's
display, against the same number computed by the formula. -/

/-- The `λ₂`-density of the edge flow used by `twoStateEdge_hasDerivAt_dbLoss`:
`u(0,0) = 1`, `u(0,1) = 3`, `u(1,0) = 2`, `u(1,1) = 4`. -/
def twoStateEdgeU : Fin 2 × Fin 2 → ℝ :=
  fun p => (![![1, 3], ![2, 4]] : Fin 2 → Fin 2 → ℝ) p.1 p.2

/-- **`cor:db_gradient` evaluated.** On `π_←(i→j) = 1/2` and `λ = (1/2,1/2)`, so that
`λ₂ ≡ 1/4` and `π_→^λ = π_←`, take the edge flow `μ = u·λ₂` with `u` as in `twoStateEdgeU` —
`μ = (1/4, 3/4, 1/2, 1)` — and `ν̂ = μ`, so `dν̂/dμ ≡ 1`. For `g(x) = (x−1)²`, the derivative of
`t ↦ 𝓛_{DB,g,ν̂}(μ + tδ)` along `δ = 1·λ₂` is `−17/32`.

Computed by hand off the paper's display, twice, without the library.

*From the loss.* `F_t = m₁μ_t = (1 + t/2, 3/2 + t/2)` and `(μ_tK₂)(z,w) = π_←(w→z)F_t(w)`, so
`r̂_t = ((2+t)/(1+t), 1, 1, (3+t)/(4+t))`; at `t = 0`, `r̂ = (2, 1, 1, 3/4)` and
`ṙ̂ = (−1, 0, 0, 1/16)`. Hence
`𝓛̇ = ∑ ν̂ g'(r̂) ṙ̂ = (1/4)·2(2−1)·(−1) + 1·2(3/4−1)·(1/16) = −1/2 − 1/32 = −17/32`.

*From the gradient.* `φ = g'(r̂) = (2, 0, 0, −1/2)`, and `[φλ₂]K₂^{λ₂}` has `λ₂`-density
`(s,s') ↦ ∑_z π_←(s→z)φ(z,s)`, which is `1` at `s = 0` and `−1/4` at `s = 1`. So
`(K₂^{λ₂} − r̂)[φλ₂]` has `λ₂`-density `(1 − 2·2, 1 − 0, −1/4 − 0, −1/4 + 3/8)
= (−3, 1, −1/4, 1/8)`, and `⟨∇ ∣ δ⟩_{λ₂} = (1/4)(−3 + 1 − 1/4 + 1/8) = −17/32`. The two agree,
which fixes the sign and the normalization of the DB formula against something outside the
derivation.

The Lean proof applies `hasDerivAt_dbLoss_ipL2` itself, at `π_→^λ = π_←` (which `hpf` verifies on
this chain), so what is evaluated is the paper's `K₂^{λ₂}` — `dualEdgeKernelProd`, the forward
edge kernel of `lem:lift_wellposed` — and not the function action of `K₂`. That the two give the
same number here is `lem:lift_wellposed`'s duality, used rather than assumed. -/
theorem twoStateEdge_hasDerivAt_dbLoss :
    HasDerivAt (fun t : ℝ => loss (edgeKernelProd twoStateK)
        (edgeMeasureProd twoStateK twoStateLam)
        (fun p => edgeMeasureProd twoStateK twoStateLam p * twoStateEdgeU p)
        (fun p => twoStateEdgeU p + t * (1 : ℝ)) fun z => (z - 1) ^ 2)
      (-17 / 32) 0 := by
  have hpb : ∀ x y : Fin 2, 0 < twoStateK x y := fun _ _ => by norm_num [twoStateK]
  have hu : ∀ p : Fin 2 × Fin 2, 0 < twoStateEdgeU p := by
    intro p
    obtain ⟨a, b⟩ := p
    fin_cases a <;> fin_cases b <;> norm_num [twoStateEdgeU]
  have hg : ∀ y : ℝ, 0 < y → HasDerivAt (fun z : ℝ => (z - 1) ^ 2) (2 * (y - 1)) y := fun y _ => by
    simpa using ((hasDerivAt_id' y).sub_const 1).fun_pow 2
  have hpf : ∀ x y : Fin 2, twoStateLam x * twoStateK x y = twoStateLam y * twoStateK y x :=
    fun _ _ => by norm_num [twoStateK, twoStateLam]
  have hD := hasDerivAt_dbLoss_ipL2 (pf := twoStateK)
    (nuhat := fun p => edgeMeasureProd twoStateK twoStateLam p * twoStateEdgeU p)
    (gd := fun z => 2 * (z - 1))
    twoStateK_invariant hpb twoStateLam_pos hpf hu hg (fun _ => (1 : ℝ))
  have hval : Graph.ipL2 (edgeMeasureProd twoStateK twoStateLam) (fun p =>
      Core.densAct (edgeMeasureProd twoStateK twoStateLam) (dualEdgeKernelProd twoStateK)
          (fun q => 2 * (ratio (edgeKernelProd twoStateK)
              (edgeMeasureProd twoStateK twoStateLam) twoStateEdgeU q - 1)
            * (edgeMeasureProd twoStateK twoStateLam q * twoStateEdgeU q
              / (edgeMeasureProd twoStateK twoStateLam q * twoStateEdgeU q))) p
        - ratio (edgeKernelProd twoStateK) (edgeMeasureProd twoStateK twoStateLam)
            twoStateEdgeU p
          * (2 * (ratio (edgeKernelProd twoStateK) (edgeMeasureProd twoStateK twoStateLam)
              twoStateEdgeU p - 1)
            * (edgeMeasureProd twoStateK twoStateLam p * twoStateEdgeU p
              / (edgeMeasureProd twoStateK twoStateLam p * twoStateEdgeU p))))
      (fun _ => (1 : ℝ)) = -17 / 32 := by
    simp only [Graph.ipL2, Core.densAct_apply, dualEdgeKernelProd, dualEdgeKernel, ratio,
      pushMass, Fintype.sum_prod_type, Fin.sum_univ_two, edgeMeasureProd, edgeKernelProd,
      edgeMeasure, edgeKernel, twoStateEdgeU]
    norm_num [twoStateK, twoStateLam]
  rwa [hval] at hD

end Edge

end GFNBounds.Balance
