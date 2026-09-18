import GFNBounds.Balance.GradientFormulas
import GFNBounds.Balance.C3Wrappers

/-!
# The trajectory-balance gradient, on a finite state space

**`prop:tb_gradient`** — statement `proofs.tex:755–772`, proof `proofs.tex:774–788`
(draft after Phase 1, commit `3194054`; line citations drift, `kb/entries/0036`: the label is the
anchor). **`eq:tb_gradient`** is the display inside it.

> Let `𝒮̂` be a finite set, `π_←` a Markov kernel on `𝒮̂` and `λ` a `π_←`-invariant probability
> with `λ(s) > 0` for every `s ∈ 𝒮̂`, and let `E := {(s,s') ∈ 𝒮̂² : π_←(s' → s) > 0}`, which the
> edge lift `K₂` of Definition `def:edge_lift` maps into itself and on which the edge measure `λ₂`
> is positive; write `K₂^{λ₂}` for the `λ₂`-reversal of `K₂` (Lemma `lem:lift_wellposed`).
> Identify a measure on `E` with its vector of weights and write
> `⟨μ ∣ δ⟩_{λ₂} := ∑_{e∈E} μ(e)δ(e)/λ₂(e)`. For an edge flow `μ ∈ (0,+∞)^E` write
> `F(s) := ∑_{s' : (s,s')∈E} μ(s,s')` for its first marginal, `π_→^μ(s → s') := μ(s,s')/F(s)`, and
> `r̂(e) := (μK₂)(e)/μ(e)` for `e ∈ E`. Let `ℓ ≥ 1`, let `ν̂` be a finite measure on `𝒮̂^{ℓ+1}`
> charging only trajectories `τ = (x_0, …, x_ℓ)` whose edges `e_k := (x_{k−1}, x_k)` all lie in
> `E`, let `ν̂_k` be the law of `e_k` under `ν̂`, let `g : ℝ₊^* → ℝ` be continuously
> differentiable, and define the TB loss with frozen backward policy
> `𝓛_{TB,g,ν̂}(μ) := ∫ g(ρ(τ)) dν̂(τ)`, `ρ(τ) := ∏_{k=1}^{ℓ} r̂(e_k)`.
> Then `F > 0` on `𝒮̂`, `r̂` takes its values in `(0,+∞)`, and the telescoping identity
> `ρ(τ) = F(x_ℓ) ∏_k π_←(x_k → x_{k−1}) / (F(x_0) ∏_k π_→^μ(x_{k−1} → x_k))` holds, which
> identifies `ρ` with the (inverted) trajectory balance ratio; on the loop closure of a marked
> graph (Theorem `theo:universality_graphs`), `F(x_0)` plays the role of `Z` when `x_0 = s_0`, […]
> and the target enters through the frozen row at the sink, `π̂_←(s_f → ·) = R/Z`. Moreover
> `𝓛_{TB,g,ν̂}` is `C¹` on `(0,+∞)^E`, and its gradient in `⟨·∣·⟩_{λ₂}` is
> `∇^{λ₂}_μ 𝓛_{TB,g,ν̂} = ∑_{k=1}^{ℓ} (K₂^{λ₂} − r̂)[ψ_k λ₂]`,
> `ψ_k := (1/r̂) 𝔼_{τ∼ν̂}(g'(ρ)ρ ∣ e_k) dν̂_k/dμ` where `ν̂_k > 0`, `ψ_k := 0` where `ν̂_k = 0`.
> For `ℓ = 1` this is the formula of Corollary `cor:db_gradient`.

The statement is the finite form the author ruled on 2026-09-14 ("narrow to what is proved"), and
this file certifies it **as printed**, `eq:tb_gradient` included: the formula is correct, with the
paper's sign, normalization and orientation of the reversal. No finding against the paper.

## What is proved

| | |
|---|---|
| `push` | `E`, `λ₂` and `K₂` are **reused** from `C3Wrappers` (`EdgeSet`, `edgeMeasureE`, `edgeKernelE`: `Lift.edgeMeasure`/`Lift.edgeKernel` read on `E`), not re-defined; `μK₂` is the measure action of `K₂` on `E` |
| `K2_row_sum` | **"`K₂` maps `E` into itself"**: from an edge of `E`, `K₂` puts mass `1` on `E` |
| `lam2_pos` | **"on which `λ₂` is positive"** |
| `lam2_invariant`, `reversal_row_sum` | `λ₂` is `K₂`-invariant on `E`, so the `λ₂`-reversal `K₂^{λ₂}` (`Core.reversal`) is a Markov kernel on `E` — the object `lem:lift_wellposed` names |
| `push_apply` | `(μK₂)(s,s') = π_←(s' → s) F(s')` on `E` (the proof's first display; `eq:muK2_density` on `E`) |
| `marg_pos` | **`F > 0` on `𝒮̂`** |
| `ratio_pos` | **`r̂ ∈ (0,+∞)`** on `E` |
| `rho_telescope` | **the telescoping identity**, for every trajectory along `E` |
| `loss_contDiffOn` | **`𝓛_{TB,g,ν̂}` is `C¹` on `(0,+∞)^E`** — Mathlib's `ContDiffOn ℝ 1` on `posOrthant` |
| `hasFDerivAt_loss` | **`eq:tb_gradient`**: `𝓛_{TB,g,ν̂}` is Fréchet-differentiable at every `μ ∈ (0,+∞)^E`, and its derivative is `δ ↦ ⟨∑_k (K₂^{λ₂} − r̂)[ψ_kλ₂] ∣ δ⟩_{λ₂}` |
| `grad_unique` | the gradient is *the* representing vector: any `G` with `D𝓛(μ)δ = ⟨G ∣ δ⟩_{λ₂}` for all `δ` is `grad` |
| `psi_eq` | the proof's step `ψ_k = a_k/(r̂μ) = a_k/(μK₂)`, from `ψ_k` **as printed** (the `ν̂_k = 0` branch included) |
| `sum_eq_ip_grad` | the proof's two-line display: the regrouping over `(k, e)` and the adjoint step, the latter by expanding `Core.reversal` on `E` |
| `psi_one`, `grad_one` | **"For `ℓ = 1` this is the formula of `cor:db_gradient`"**: `ψ_1 = g'(r̂) dν̂_1/dμ`, and the gradient is `(K₂^{λ₂} − r̂)[g'(r̂)(dν̂_1/dμ)λ₂]` |
| `witness` | **inhabitation** (kb `0025`): the swap chain on two states, whose `E = {(0,1),(1,0)}` is a *proper* subset of `𝒮²`, with `ℓ = 2`, `ν̂ = δ_{(0,1,0)}`, `g(x) = (x−1)²`, `μ ≡ 1` — every hypothesis holds and the conclusion is delivered |

## SCOPE (disclosed)

* **The loop-closure gloss is not formalized.** The sentence "on the loop closure of a marked
  graph, `F(x_0)` plays the role of `Z` when `x_0 = s_0`, `Z` being the target mass of
  Theorem `theo:universality_graphs`(3), and the target enters through the frozen row at the sink,
  `π̂_←(s_f → ·) = R/Z`" is an interpretation of the telescoping identity ("plays the role"), not
  a claim with a proof in the paper's proof environment, which proves the identity and nothing
  about `Z`. What *is* certified is the identity itself, `rho_telescope`, for every trajectory
  along `E` on every instance, loop closures included. Whether that sentence is terminal or a claim
  is the author's call; it is recorded here so the row is not read as covering it.
* **"Its gradient" is read as: Fréchet derivative + Riesz representative in `⟨·∣·⟩_{λ₂}`.**
  `hasFDerivAt_loss` gives `HasFDerivAt 𝓛 (fderiv ℝ 𝓛 μ) μ` and identifies `fderiv ℝ 𝓛 μ δ` with
  `⟨grad ∣ δ⟩_{λ₂}` for every `δ ∈ ℝ^E`; `grad_unique` shows the representative is unique. This is
  stronger than the *directional* derivative `FirstVariation.lean` and `GradientFormulas.lean`
  prove for the FM/DB losses, and it is what the paper's "`C¹` … its gradient" says on a finite
  space.
* **Measures on `E` are weight vectors** (the paper's own identification): `μ, δ : EdgeSet pb → ℝ`,
  `ν̂ : (Fin (ℓ+1) → V) → ℝ` with `ν̂ ≥ 0`, `∫ · dν̂` is `∑_τ ν̂(τ) ·`, `dν̂_k/dμ = ν̂_k/μ`, and the
  conditional expectation is `a_k/ν̂_k` on `{ν̂_k > 0}`.
* **Indexing.** The paper's `e_k = (x_{k−1}, x_k)`, `k = 1, …, ℓ`, is `(τ k.castSucc, τ k.succ)` at
  `k : Fin ℓ`, i.e. paper-`k` is Lean-`k+1`; at `ℓ = 1` the paper's `ψ_1` is `psi … 0`.
* **Junk values off `E`.** `ρ` is defined on every `τ : Fin (ℓ+1) → V`, with the factor `1`
  (`ratioAt`) at a pair outside `E`, and `π_→^μ` is `0` off `E`. Both are unreachable in every
  statement: the loss weighs `τ` by `ν̂(τ)`, which vanishes off trajectories along `E` (`hnuE`), and
  `rho_telescope` asks `AlongE`.
* **What the Markov hypothesis is used for.** The gradient, `C¹` and telescoping clauses use of
  `π_←` only that `λ` is `π_←`-invariant (`Invariant pb lam`) — `E` is defined by positivity, so no
  sign condition on `π_←` enters them; non-negativity enters `K2_row_sum`, `lam2_invariant` and
  `reversal_row_sum`, and row-stochasticity only `K2_row_sum`. `λ` being a probability is used
  nowhere (`∑λ = 1` plays no role in the statement). Each declaration carries only what it uses.
* **`K₂^{λ₂}` is `Core.reversal` on `E`, not `Lift.dualEdgeKernel`.** The paper defines it as the
  `λ₂`-reversal, and that is what `grad` uses; its identification with the forward edge lift
  `(s,s') ↦ (s', π_→^λ(s'))` is `Lift.edgeKernel_dual` and is not repeated here.
* **`ℓ = 1` is matched to `cor:db_gradient`'s *display*, on `E`.** `grad_one` is that display for
  the training distribution `ν̂_1`. It is not bridged to `GradientFormulas.hasDerivAt_dbLoss_ipL2`,
  which is stated on all of `𝒮²` in `λ₂`-density coordinates and needs `π_←` positive on every
  pair (its SCOPE records that restriction); this file is the edge-set instantiation that SCOPE
  names as missing, for `ℓ = 1` included.
* **The `sorry` list is empty and this file adds nothing to it.**

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒮̂` a finite set | ✓ `[Fintype V] [DecidableEq V]` |
| `π_←` a Markov kernel on `𝒮̂` | ✓ `pb : V → V → ℝ`; non-negativity `hnn` and row sums `hrow` carried exactly where used (see SCOPE) |
| `λ` a `π_←`-invariant probability | ✓ `hinv : Invariant pb lam`; `∑ λ = 1` not carried — used nowhere |
| `λ(s) > 0` for every `s` | ✓ `hlam : ∀ x, 0 < lam x` |
| `E := {(s,s') : π_←(s' → s) > 0}` | ✓ `EdgeSet pb := {p : V × V // 0 < pb p.2 p.1}` (`C3Wrappers`) |
| `K₂` maps `E` into itself | ✓ proved, `K2_row_sum` |
| `λ₂ > 0` on `E` | ✓ proved, `lam2_pos` |
| `K₂^{λ₂}` the `λ₂`-reversal of `K₂` | ✓ `Core.reversal (edgeMeasureE pb lam) (edgeKernelE pb)`, Markov on `E` by `reversal_row_sum` |
| `⟨μ ∣ δ⟩_{λ₂} = ∑_E μδ/λ₂` | ✓ `ip` |
| `μ ∈ (0,+∞)^E` | ✓ `hμ : ∀ e, 0 < μ e`; `posOrthant pb` for the `C¹` clause |
| `F`, `π_→^μ`, `r̂ = (μK₂)/μ` | ✓ `marg`, `fwd`, `ratio` (with `push` the measure action of `K₂` on `E`) |
| `ℓ ≥ 1` | ⚠ **not carried**: every clause holds at `ℓ = 0` too (`ρ ≡ 1`, the loss constant, `grad = 0`); nothing is lost by admitting it |
| `ν̂` a finite measure on `𝒮̂^{ℓ+1}` | ✓ `nu : (Fin (ℓ+1) → V) → ℝ`, `hnu : ∀ τ, 0 ≤ nu τ` (used by `psi_eq`, hence by the gradient clause) |
| `ν̂` charges only trajectories along `E` | ✓ `hnuE : ∀ τ, nu τ ≠ 0 → AlongE pb τ` |
| `ν̂_k` the law of `e_k` | ✓ `edgeMarg` |
| `g : ℝ₊^* → ℝ` continuously differentiable | ✓ `hg : ContDiffOn ℝ 1 g (Set.Ioi 0)`; `g'` is `deriv g` |
| `ψ_k` as printed, both branches | ✓ `psi`, verbatim; `psi_eq` is the proof's rewriting |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance.TBGradient

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The edge set `E` and the objects on it -/

variable (pb : V → V → ℝ)

/-- The first marginal `F(s) = ∑_{s' : (s,s') ∈ E} μ(s,s')` of an edge flow `μ` on `E`. -/
noncomputable def marg (μ : EdgeSet pb → ℝ) (s : V) : ℝ :=
  ∑ e : EdgeSet pb, if e.1.1 = s then μ e else 0

/-- The action of a kernel `A` on measures on `E`: `(mA)(e) = ∑_{e'} m(e') A(e' → e)`. -/
noncomputable def measAct (A : EdgeSet pb → EdgeSet pb → ℝ) (m : EdgeSet pb → ℝ) (e : EdgeSet pb) : ℝ :=
  ∑ e', m e' * A e' e

/-- `μK₂` on `E`. -/
noncomputable def push (μ : EdgeSet pb → ℝ) : EdgeSet pb → ℝ := measAct pb (edgeKernelE pb) μ

/-- `r̂(e) := (μK₂)(e)/μ(e)`. -/
noncomputable def ratio (μ : EdgeSet pb → ℝ) (e : EdgeSet pb) : ℝ := push pb μ e / μ e

/-- `π_→^μ(s → s') := μ(s,s')/F(s)` on `E`, and `0` off `E`. -/
noncomputable def fwd (μ : EdgeSet pb → ℝ) (s s' : V) : ℝ :=
  if h : 0 < pb s' s then μ ⟨(s, s'), h⟩ / marg pb μ s else 0

/-- `r̂` read at a pair of states: `r̂(s,s')` on `E`, and the junk value `1` off `E`. -/
noncomputable def ratioAt (μ : EdgeSet pb → ℝ) (s s' : V) : ℝ :=
  if h : 0 < pb s' s then ratio pb μ ⟨(s, s'), h⟩ else 1

variable {ℓ : ℕ}

/-- A trajectory `τ = (x_0, …, x_ℓ)` runs along `E`: every edge `e_k = (x_{k−1}, x_k)` is in `E`.
The paper's edge `e_k`, `k = 1, …, ℓ`, is `(τ k.castSucc, τ k.succ)` at `k : Fin ℓ`. -/
def AlongE (τ : Fin (ℓ + 1) → V) : Prop := ∀ k : Fin ℓ, 0 < pb (τ k.succ) (τ k.castSucc)

/-- `ρ(τ) := ∏_{k=1}^{ℓ} r̂(e_k)`. -/
noncomputable def rho (μ : EdgeSet pb → ℝ) (τ : Fin (ℓ + 1) → V) : ℝ :=
  ∏ k : Fin ℓ, ratioAt pb μ (τ k.castSucc) (τ k.succ)

/-- **The TB loss with frozen backward policy**, `𝓛_{TB,g,ν̂}(μ) = ∫ g(ρ(τ)) dν̂(τ)`, with `ν̂` a
finite measure on `𝒮^{ℓ+1}` given by its weights. -/
noncomputable def loss (nu : (Fin (ℓ + 1) → V) → ℝ) (g : ℝ → ℝ) (μ : EdgeSet pb → ℝ) : ℝ :=
  ∑ τ, nu τ * g (rho pb μ τ)

/-- The edge marginal `ν̂_k(e)`: the law of `e_k` under `ν̂`. -/
noncomputable def edgeMarg (nu : (Fin (ℓ + 1) → V) → ℝ) (k : Fin ℓ) (e : EdgeSet pb) : ℝ :=
  ∑ τ, if (τ k.castSucc, τ k.succ) = e.1 then nu τ else 0

/-- `a_k(e) := ∑_{τ : e_k = e} ν̂(τ) g'(ρ(τ)) ρ(τ)` (the paper's proof). -/
noncomputable def weight (nu : (Fin (ℓ + 1) → V) → ℝ) (g : ℝ → ℝ) (μ : EdgeSet pb → ℝ) (k : Fin ℓ)
    (e : EdgeSet pb) : ℝ :=
  ∑ τ, if (τ k.castSucc, τ k.succ) = e.1 then nu τ * (deriv g (rho pb μ τ) * rho pb μ τ) else 0

/-- `𝔼_{τ∼ν̂}(g'(ρ)ρ ∣ e_k = e) = a_k(e)/ν̂_k(e)`, read where `ν̂_k(e) > 0`. -/
noncomputable def condExp (nu : (Fin (ℓ + 1) → V) → ℝ) (g : ℝ → ℝ) (μ : EdgeSet pb → ℝ) (k : Fin ℓ)
    (e : EdgeSet pb) : ℝ :=
  weight pb nu g μ k e / edgeMarg pb nu k e

/-- **`ψ_k`, as printed**: `(1/r̂) 𝔼(g'(ρ)ρ ∣ e_k) dν̂_k/dμ` where `ν̂_k > 0`, and `0` where
`ν̂_k = 0`. -/
noncomputable def psi (nu : (Fin (ℓ + 1) → V) → ℝ) (g : ℝ → ℝ) (μ : EdgeSet pb → ℝ) (k : Fin ℓ)
    (e : EdgeSet pb) : ℝ :=
  if 0 < edgeMarg pb nu k e then
    (1 / ratio pb μ e) * condExp pb nu g μ k e * (edgeMarg pb nu k e / μ e)
  else 0

/-- The inner product `⟨m ∣ δ⟩_{λ₂} = ∑_{e ∈ E} m(e) δ(e)/λ₂(e)` on measures on `E`. -/
noncomputable def ip (w m d : EdgeSet pb → ℝ) : ℝ := ∑ e, m e * d e / w e

/-- **The right-hand side of `eq:tb_gradient`**:
`∑_{k=1}^{ℓ} (K₂^{λ₂} − r̂)[ψ_k λ₂]`, with `K₂^{λ₂}` the `λ₂`-reversal of `K₂` on `E`
(`Core.reversal`) acting on measures. -/
noncomputable def grad (lam : V → ℝ) (nu : (Fin (ℓ + 1) → V) → ℝ) (g : ℝ → ℝ)
    (μ : EdgeSet pb → ℝ) (e : EdgeSet pb) : ℝ :=
  ∑ k : Fin ℓ, (measAct pb (Core.reversal (edgeMeasureE pb lam) (edgeKernelE pb))
      (fun e' => psi pb nu g μ k e' * edgeMeasureE pb lam e') e
    - ratio pb μ e * (psi pb nu g μ k e * edgeMeasureE pb lam e))

/-! ### Elementary facts -/

variable {pb}

omit [Fintype V] in
/-- `K₂(e → e') = [e'.2 = e.1] π_←(e.1 → e'.1)`. -/
theorem K2_apply (e e' : EdgeSet pb) :
    edgeKernelE pb e e' = if e'.1.2 = e.1.1 then pb e.1.1 e'.1.1 else 0 := rfl

/-- **`eq:muK2_density` on `E`**: `(μK₂)(s,s') = π_←(s' → s) F(s')`. -/
theorem push_apply (μ : EdgeSet pb → ℝ) (e : EdgeSet pb) :
    push pb μ e = pb e.1.2 e.1.1 * marg pb μ e.1.2 := by
  simp only [push, measAct, K2_apply, marg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  by_cases h : e.1.2 = e'.1.1
  · rw [if_pos h, if_pos h.symm, h]; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

/-- `μ ↦ μK₂` is linear along a line. -/
theorem push_add_smul (μ d : EdgeSet pb → ℝ) (t : ℝ) (e : EdgeSet pb) :
    push pb (μ + t • d) e = push pb μ e + t * push pb d e := by
  simp only [push, measAct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **`prop:tb_gradient`, `F > 0` on `𝒮̂`**: every state has an outgoing edge in `E`, because `λ(s) > 0` is
`∑_z λ(z) π_←(z → s)`. -/
theorem marg_pos {lam : V → ℝ} (hinv : Invariant pb lam)
    (hlam : ∀ x, 0 < lam x) {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e) (s : V) :
    0 < marg pb μ s := by
  have hsum : 0 < ∑ z, lam z * pb z s := by rw [hinv s]; exact hlam s
  obtain ⟨z, hz⟩ : ∃ z, 0 < lam z * pb z s := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd hsum (not_lt.mpr (Finset.sum_nonpos fun z _ => hcon z))
  have hpz : 0 < pb z s := pos_of_mul_pos_right hz (hlam z).le
  have hle : μ ⟨(s, z), hpz⟩ ≤ marg pb μ s := by
    have h := Finset.single_le_sum (f := fun e : EdgeSet pb => if e.1.1 = s then μ e else 0)
      (fun e _ => by by_cases h : e.1.1 = s <;> simp [h, (hμ e).le])
      (Finset.mem_univ ⟨(s, z), hpz⟩)
    simpa [marg] using h
  exact lt_of_lt_of_le (hμ _) hle


omit [Fintype V] [DecidableEq V] in
/-- **`prop:tb_gradient`, "on which `λ₂` is positive"**: `λ₂ > 0` on `E` when `λ > 0`;
`C3Wrappers.edgeMeasureE_pos`. -/
theorem lam2_pos {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (e : EdgeSet pb) :
    0 < edgeMeasureE pb lam e :=
  edgeMeasureE_pos hlam e

/-- `(μK₂) > 0` on `E` when `F > 0`. -/
theorem push_pos {μ : EdgeSet pb → ℝ} (hF : ∀ s, 0 < marg pb μ s) (e : EdgeSet pb) :
    0 < push pb μ e := by
  rw [push_apply]; exact mul_pos e.2 (hF _)

/-- **`prop:tb_gradient`, `r̂` takes its values in `(0,+∞)`** on `E`. -/
theorem ratio_pos {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e) (hF : ∀ s, 0 < marg pb μ s)
    (e : EdgeSet pb) : 0 < ratio pb μ e :=
  div_pos (push_pos hF e) (hμ e)

theorem ratioAt_of_along {μ : EdgeSet pb → ℝ} {τ : Fin (ℓ + 1) → V} (hτ : AlongE pb τ) (k : Fin ℓ) :
    ratioAt pb μ (τ k.castSucc) (τ k.succ) = ratio pb μ ⟨(τ k.castSucc, τ k.succ), hτ k⟩ :=
  dif_pos (hτ k)

theorem rho_of_along (μ : EdgeSet pb → ℝ) {τ : Fin (ℓ + 1) → V} (hτ : AlongE pb τ) :
    rho pb μ τ = ∏ k : Fin ℓ, ratio pb μ ⟨(τ k.castSucc, τ k.succ), hτ k⟩ := by
  unfold rho
  exact Finset.prod_congr rfl fun k _ => ratioAt_of_along hτ k

theorem rho_pos {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e) (hF : ∀ s, 0 < marg pb μ s)
    {τ : Fin (ℓ + 1) → V} (hτ : AlongE pb τ) : 0 < rho pb μ τ := by
  rw [rho_of_along μ hτ]
  exact Finset.prod_pos fun k _ => ratio_pos hμ hF _

/-! ### The telescoping identity -/

omit [Fintype V] [DecidableEq V] in
/-- `∏_{k=1}^{n} f(k)/f(k−1) = f(n)/f(0)`. -/
theorem prod_succ_div_castSucc : ∀ {n : ℕ} (f : Fin (n + 1) → ℝ), (∀ i, f i ≠ 0) →
    ∏ k : Fin n, f k.succ / f k.castSucc = f (Fin.last n) / f 0
  | 0, f, hf => by simp [div_self (hf 0)]
  | n + 1, f, hf => by
    rw [Fin.prod_univ_castSucc]
    have ih := prod_succ_div_castSucc (fun i : Fin (n + 1) => f i.castSucc) (fun i => hf _)
    simp only [Fin.succ_castSucc] at ih ⊢
    rw [ih]
    have h1 := hf (Fin.last n).castSucc
    have h0 := hf 0
    simp only [Fin.castSucc_zero, Fin.succ_last] at ih ⊢
    field_simp

/-- **`prop:tb_gradient`, the telescoping identity**: along a trajectory in `E`,
`ρ(τ) = F(x_ℓ) ∏ π_←(x_k → x_{k−1}) / (F(x_0) ∏ π_→^μ(x_{k−1} → x_k))`. -/
theorem rho_telescope {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e) (hF : ∀ s, 0 < marg pb μ s)
    {τ : Fin (ℓ + 1) → V} (hτ : AlongE pb τ) :
    rho pb μ τ = marg pb μ (τ (Fin.last ℓ)) * (∏ k : Fin ℓ, pb (τ k.succ) (τ k.castSucc))
      / (marg pb μ (τ 0) * ∏ k : Fin ℓ, fwd pb μ (τ k.castSucc) (τ k.succ)) := by
  have hfac : ∀ k : Fin ℓ, ratio pb μ ⟨(τ k.castSucc, τ k.succ), hτ k⟩
      = marg pb μ (τ k.succ) / marg pb μ (τ k.castSucc)
        * (pb (τ k.succ) (τ k.castSucc) / fwd pb μ (τ k.castSucc) (τ k.succ)) := by
    intro k
    have hm := hμ ⟨(τ k.castSucc, τ k.succ), hτ k⟩
    have hFa := hF (τ k.castSucc)
    have hFb := hF (τ k.succ)
    simp only [ratio, push_apply, fwd, dif_pos (hτ k)]
    field_simp
  have htel := prod_succ_div_castSucc (fun i => marg pb μ (τ i)) (fun i => (hF _).ne')
  rw [rho_of_along μ hτ, Finset.prod_congr rfl fun k _ => hfac k, Finset.prod_mul_distrib, htel,
    Finset.prod_div_distrib, div_mul_div_comm]

/-! ### The derivative along a line -/

/-- `d log r̂(e)` along `d`: `(dK₂)(e)/(μK₂)(e) − d(e)/μ(e)`. -/
noncomputable def dir (μ d : EdgeSet pb → ℝ) (e : EdgeSet pb) : ℝ :=
  push pb d e / push pb μ e - d e / μ e

/-- `dir` read at a pair of states, `0` off `E`. -/
noncomputable def dirAt (μ d : EdgeSet pb → ℝ) (s s' : V) : ℝ :=
  if h : 0 < pb s' s then dir μ d ⟨(s, s'), h⟩ else 0

theorem hasDerivAt_ratio {μ : EdgeSet pb → ℝ} (d : EdgeSet pb → ℝ) {e : EdgeSet pb} (hμ : 0 < μ e)
    (hp : 0 < push pb μ e) :
    HasDerivAt (fun t : ℝ => ratio pb (μ + t • d) e) (ratio pb μ e * dir μ d e) 0 := by
  have hfun : (fun t : ℝ => ratio pb (μ + t • d) e)
      = fun t => (push pb μ e + t * push pb d e) / (μ e + t * d e) := by
    funext t
    simp only [ratio, push_add_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  have hn : HasDerivAt (fun t : ℝ => push pb μ e + t * push pb d e) (push pb d e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (push pb d e)).const_add (push pb μ e)
  have hd : HasDerivAt (fun t : ℝ => μ e + t * d e) (d e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d e)).const_add (μ e)
  refine (hn.div hd (by simpa using hμ.ne')).congr_deriv ?_
  simp only [ratio, dir, zero_mul, add_zero]
  field_simp

theorem hasDerivAt_rho {μ : EdgeSet pb → ℝ} (d : EdgeSet pb → ℝ) (hμ : ∀ e, 0 < μ e)
    (hF : ∀ s, 0 < marg pb μ s) {τ : Fin (ℓ + 1) → V} (hτ : AlongE pb τ) :
    HasDerivAt (fun t : ℝ => rho pb (μ + t • d) τ)
      (rho pb μ τ * ∑ k : Fin ℓ, dirAt μ d (τ k.castSucc) (τ k.succ)) 0 := by
  have hfun : (fun t : ℝ => rho pb (μ + t • d) τ)
      = fun t => ∏ k : Fin ℓ, ratio pb (μ + t • d) ⟨(τ k.castSucc, τ k.succ), hτ k⟩ := by
    funext t; exact rho_of_along _ hτ
  rw [hfun]
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := (0 : ℝ))
    (f := fun k t => ratio pb (μ + t • d) ⟨(τ k.castSucc, τ k.succ), hτ k⟩)
    (f' := fun k => ratio pb μ ⟨(τ k.castSucc, τ k.succ), hτ k⟩
      * dir μ d ⟨(τ k.castSucc, τ k.succ), hτ k⟩)
    (fun k _ => hasDerivAt_ratio d (hμ _) (push_pos hF _))
  refine h.congr_deriv ?_
  simp only [zero_smul, add_zero, smul_eq_mul, rho_of_along μ hτ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dirAt, dif_pos (hτ k), ← mul_assoc]
  congr 1
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ k)

theorem hasDerivAt_g {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g (Set.Ioi 0)) {y : ℝ} (hy : 0 < y) :
    HasDerivAt g (deriv g y) y :=
  ((hg.contDiffAt (Ioi_mem_nhds hy)).differentiableAt one_ne_zero).hasDerivAt

/-- The derivative of `t ↦ 𝓛_{TB}(μ + t d)` at `0`, before regrouping. -/
theorem hasDerivAt_loss {lam : V → ℝ} (hinv : Invariant pb lam) (hlam : ∀ x, 0 < lam x)
    {nu : (Fin (ℓ + 1) → V) → ℝ} (hnuE : ∀ τ, nu τ ≠ 0 → AlongE pb τ) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioi 0)) {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e)
    (d : EdgeSet pb → ℝ) :
    HasDerivAt (fun t : ℝ => loss pb nu g (μ + t • d))
      (∑ τ, nu τ * (deriv g (rho pb μ τ)
        * (rho pb μ τ * ∑ k : Fin ℓ, dirAt μ d (τ k.castSucc) (τ k.succ)))) 0 := by
  have hF := marg_pos hinv hlam hμ
  have h0 : μ + (0 : ℝ) • d = μ := by simp
  refine HasDerivAt.fun_sum (u := Finset.univ) fun τ _ => ?_
  by_cases hν : nu τ = 0
  · simp only [hν, zero_mul]
    exact hasDerivAt_const _ _
  · have hτ := hnuE τ hν
    have hg0 : HasDerivAt g (deriv g (rho pb μ τ)) (rho pb (μ + (0 : ℝ) • d) τ) := by
      rw [h0]; exact hasDerivAt_g hg (rho_pos hμ hF hτ)
    exact (hg0.comp (0 : ℝ) (hasDerivAt_rho d hμ hF hτ)).const_mul (nu τ)

/-! ### Regrouping: the paper's computation -/

/-- Summing over `E` against the indicator of a pair picks the edge, or nothing off `E`. -/
theorem sum_ite_edge (c : ℝ) (f : EdgeSet pb → ℝ) (s s' : V) :
    ∑ e : EdgeSet pb, (if (s, s') = e.1 then c * f e else 0)
      = c * (if h : 0 < pb s' s then f ⟨(s, s'), h⟩ else 0) := by
  by_cases h : 0 < pb s' s
  · rw [dif_pos h, Finset.sum_eq_single ⟨(s, s'), h⟩]
    · simp
    · intro e _ he
      rw [if_neg]
      intro hc
      exact he (Subtype.ext hc.symm)
    · simp
  · rw [dif_neg h, mul_zero]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg]
    intro hc
    have he := e.2
    rw [← hc] at he
    exact h he

/-- **The step `ψ_k = a_k/(r̂μ) = a_k/(μK₂)`** of the paper's proof, from the printed `ψ_k`. -/
theorem psi_eq {nu : (Fin (ℓ + 1) → V) → ℝ} (hnu : ∀ τ, 0 ≤ nu τ) (g : ℝ → ℝ)
    {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e) (hF : ∀ s, 0 < marg pb μ s) (k : Fin ℓ)
    (e : EdgeSet pb) : psi pb nu g μ k e = weight pb nu g μ k e / push pb μ e := by
  have hp := (push_pos hF e).ne'
  have hm := (hμ e).ne'
  unfold psi
  split_ifs with hpos
  · simp only [condExp, ratio]
    field_simp
  · have hle : edgeMarg pb nu k e = 0 :=
      le_antisymm (not_lt.mp hpos) (Finset.sum_nonneg fun τ _ => by split_ifs <;> simp [hnu τ])
    have hz : ∀ τ ∈ (Finset.univ : Finset (Fin (ℓ + 1) → V)),
        (if (τ k.castSucc, τ k.succ) = e.1 then nu τ else 0) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => by split_ifs <;> simp [hnu τ]).mp hle
    have hw : weight pb nu g μ k e = 0 := by
      refine Finset.sum_eq_zero fun τ hτ => ?_
      have := hz τ hτ
      split_ifs at this ⊢ with h
      · rw [this, zero_mul]
      · rfl
    rw [hw, zero_div]

/-- **The regrouping** of the paper's proof: the derivative along `d`, summed over trajectories,
is `⟨∑_k (K₂^{λ₂} − r̂)[ψ_k λ₂] ∣ d⟩_{λ₂}`. The second equality of the paper's display is
`lem:adjoint`*(3)* for the `λ₂`-reversal on `E`, done here by expanding `Core.reversal`. -/
theorem sum_eq_ip_grad {lam : V → ℝ} (hinv : Invariant pb lam) (hlam : ∀ x, 0 < lam x)
    {nu : (Fin (ℓ + 1) → V) → ℝ} (hnu : ∀ τ, 0 ≤ nu τ) (g : ℝ → ℝ)
    {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e) (d : EdgeSet pb → ℝ) :
    ∑ τ, nu τ * (deriv g (rho pb μ τ)
        * (rho pb μ τ * ∑ k : Fin ℓ, dirAt μ d (τ k.castSucc) (τ k.succ)))
      = ip pb (edgeMeasureE pb lam) (grad pb lam nu g μ) d := by
  have hF := marg_pos hinv hlam hμ
  have hl2 : ∀ e : EdgeSet pb, edgeMeasureE pb lam e ≠ 0 := fun e => (mul_pos e.2 (hlam _)).ne'
  -- the right-hand side, edge by edge
  have hA : ∀ k : Fin ℓ, ∑ e, measAct pb (Core.reversal (edgeMeasureE pb lam) (edgeKernelE pb))
        (fun e' => psi pb nu g μ k e' * edgeMeasureE pb lam e') e * d e / edgeMeasureE pb lam e
      = ∑ e', psi pb nu g μ k e' * push pb d e' := by
    intro k
    simp only [measAct, Core.reversal_apply, push, Finset.sum_div, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun e _ => ?_
    have h1 := hl2 e
    have h2 := hl2 e'
    field_simp
  have hB : ∀ k : Fin ℓ, ∑ e, ratio pb μ e * (psi pb nu g μ k e * edgeMeasureE pb lam e) * d e
        / edgeMeasureE pb lam e
      = ∑ e, ratio pb μ e * psi pb nu g μ k e * d e := by
    intro k
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 := hl2 e
    field_simp
  have hR : ip pb (edgeMeasureE pb lam) (grad pb lam nu g μ) d
      = ∑ k : Fin ℓ, ∑ e, weight pb nu g μ k e * dir μ d e := by
    have hsplit : ip pb (edgeMeasureE pb lam) (grad pb lam nu g μ) d
        = ∑ k : Fin ℓ, (∑ e, measAct pb (Core.reversal (edgeMeasureE pb lam) (edgeKernelE pb))
            (fun e' => psi pb nu g μ k e' * edgeMeasureE pb lam e') e * d e / edgeMeasureE pb lam e
          - ∑ e, ratio pb μ e * (psi pb nu g μ k e * edgeMeasureE pb lam e) * d e / edgeMeasureE pb lam e) := by
      simp only [ip, grad, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [hsplit]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA k, hB k, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hp := (push_pos hF e).ne'
    have hm := (hμ e).ne'
    rw [psi_eq hnu g hμ hF k e]
    simp only [dir, ratio]
    field_simp
  -- the left-hand side, trajectory by trajectory
  have hL : ∀ k : Fin ℓ, ∑ e, weight pb nu g μ k e * dir μ d e
      = ∑ τ, nu τ * (deriv g (rho pb μ τ) * rho pb μ τ)
          * dirAt μ d (τ k.castSucc) (τ k.succ) := by
    intro k
    simp only [weight, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [dirAt, ← sum_ite_edge]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  rw [hR, Finset.sum_congr rfl fun k _ => hL k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum]
  ring

/-! ### `prop:tb_gradient`: `C¹`, and the gradient -/

variable (pb) in
/-- The open orthant `(0,+∞)^E`. -/
def posOrthant : Set (EdgeSet pb → ℝ) := {μ | ∀ e, 0 < μ e}

omit [DecidableEq V] in
variable (pb) in
theorem isOpen_posOrthant : IsOpen (posOrthant pb) := by
  have h : posOrthant pb = ⋂ e, {μ : EdgeSet pb → ℝ | 0 < μ e} := by
    ext μ; simp [posOrthant]
  rw [h]
  exact isOpen_iInter_of_finite fun e => isOpen_lt continuous_const (continuous_apply e)

theorem contDiff_push (e : EdgeSet pb) : ContDiff ℝ 1 (fun μ : EdgeSet pb → ℝ => push pb μ e) := by
  unfold push measAct
  exact ContDiff.sum fun e' _ => (contDiff_apply ℝ ℝ e').mul contDiff_const

/-- **`prop:tb_gradient`, regularity**: `𝓛_{TB,g,ν̂}` is `C¹` on `(0,+∞)^E`. -/
theorem loss_contDiffOn {lam : V → ℝ} (hinv : Invariant pb lam) (hlam : ∀ x, 0 < lam x)
    {nu : (Fin (ℓ + 1) → V) → ℝ} (hnuE : ∀ τ, nu τ ≠ 0 → AlongE pb τ) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioi 0)) :
    ContDiffOn ℝ 1 (loss pb nu g) (posOrthant pb) := by
  unfold loss
  refine ContDiffOn.sum fun τ _ => ?_
  by_cases hν : nu τ = 0
  · simp only [hν, zero_mul]
    exact contDiffOn_const
  · have hτ := hnuE τ hν
    have hr : ContDiffOn ℝ 1 (fun μ => rho pb μ τ) (posOrthant pb) := by
      have h : (fun μ => rho pb μ τ)
          = fun μ => ∏ k : Fin ℓ, ratio pb μ ⟨(τ k.castSucc, τ k.succ), hτ k⟩ :=
        funext fun μ => rho_of_along μ hτ
      rw [h]
      refine contDiffOn_prod fun k _ => ?_
      exact (contDiff_push _).contDiffOn.div (contDiff_apply ℝ ℝ _).contDiffOn
        fun μ hμ => (hμ _).ne'
    have hmaps : Set.MapsTo (fun μ => rho pb μ τ) (posOrthant pb) (Set.Ioi 0) :=
      fun μ hμ => rho_pos hμ (marg_pos hinv hlam hμ) hτ
    exact contDiffOn_const.mul (hg.comp hr hmaps)

/-- **`prop:tb_gradient`, `eq:tb_gradient`**: at every `μ ∈ (0,+∞)^E`, `𝓛_{TB,g,ν̂}` is Fréchet
differentiable, and its derivative is `δ ↦ ⟨∑_k (K₂^{λ₂} − r̂)[ψ_k λ₂] ∣ δ⟩_{λ₂}`: the right-hand
side of `eq:tb_gradient` is the gradient in `⟨·∣·⟩_{λ₂}`. -/
theorem hasFDerivAt_loss {lam : V → ℝ} (hinv : Invariant pb lam) (hlam : ∀ x, 0 < lam x)
    {nu : (Fin (ℓ + 1) → V) → ℝ} (hnu : ∀ τ, 0 ≤ nu τ) (hnuE : ∀ τ, nu τ ≠ 0 → AlongE pb τ)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g (Set.Ioi 0)) {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e) :
    HasFDerivAt (loss pb nu g) (fderiv ℝ (loss pb nu g) μ) μ ∧
      ∀ d, fderiv ℝ (loss pb nu g) μ d = ip pb (edgeMeasureE pb lam) (grad pb lam nu g μ) d := by
  have hcd := (loss_contDiffOn hinv hlam hnuE hg).contDiffAt
    ((isOpen_posOrthant pb).mem_nhds (show μ ∈ posOrthant pb from hμ))
  have hF : HasFDerivAt (loss pb nu g) (fderiv ℝ (loss pb nu g) μ) μ :=
    (hcd.differentiableAt one_ne_zero).hasFDerivAt
  refine ⟨hF, fun d => ?_⟩
  have hline : HasDerivAt (fun t : ℝ => μ + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add μ
  have h1 := hF.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 := hasDerivAt_loss hinv hlam hnuE hg hμ d
  rw [← sum_eq_ip_grad hinv hlam hnu g hμ d]
  exact h1.unique h2

/-- `⟨m ∣ 𝟙_e⟩_w = m(e)/w(e)`. -/
theorem ip_single (w m : EdgeSet pb → ℝ) (e : EdgeSet pb) : ip pb w m (Pi.single e 1) = m e / w e := by
  unfold ip
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- **`prop:tb_gradient`, the gradient is unique**: `⟨·∣·⟩_{λ₂}` is non-degenerate on `E`, so the right-hand side of
`eq:tb_gradient` is the *only* measure representing the derivative. -/
theorem grad_unique {lam : V → ℝ} (hinv : Invariant pb lam) (hlam : ∀ x, 0 < lam x)
    {nu : (Fin (ℓ + 1) → V) → ℝ} (hnu : ∀ τ, 0 ≤ nu τ) (hnuE : ∀ τ, nu τ ≠ 0 → AlongE pb τ)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g (Set.Ioi 0)) {μ : EdgeSet pb → ℝ} (hμ : ∀ e, 0 < μ e)
    {G : EdgeSet pb → ℝ} (hG : ∀ d, fderiv ℝ (loss pb nu g) μ d = ip pb (edgeMeasureE pb lam) G d) :
    G = grad pb lam nu g μ := by
  funext e
  have h := (hG (Pi.single e 1)).symm.trans
    ((hasFDerivAt_loss hinv hlam hnu hnuE hg hμ).2 (Pi.single e 1))
  rw [ip_single, ip_single] at h
  have hl : edgeMeasureE pb lam e ≠ 0 := (mul_pos e.2 (hlam _)).ne'
  field_simp at h
  exact h

/-! ### `F > 0`, `r̂ > 0`, and `K₂` on `E` -/

/-- **`prop:tb_gradient`, "`K₂` maps `E` into itself"**: from an edge, `K₂` puts all its mass on `E`.
`C3Wrappers.edgeKernelE_isMarkovOn`, read at the reference weight `λ ≡ 1` (for which `λ₂ > 0` on
`E`). -/
theorem K2_row_sum (hnn : ∀ x y, 0 ≤ pb x y) (hrow : ∀ x, ∑ y, pb x y = 1) (e : EdgeSet pb) :
    ∑ e' : EdgeSet pb, edgeKernelE pb e e' = 1 :=
  (edgeKernelE_isMarkovOn (lam := fun _ => (1 : ℝ)) hnn hrow).row_sum
    (edgeMeasureE_pos (fun _ => one_pos) e).ne'

/-- **`λ₂` is `K₂`-invariant on `E`** (`lem:lift_wellposed`, read on `E`):
`C3Wrappers.edgeMeasureE_isInvariant`. -/
theorem lam2_invariant {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y) (hlam : ∀ x, 0 ≤ lam x)
    (hinv : Invariant pb lam) (e : EdgeSet pb) :
    ∑ e' : EdgeSet pb, edgeMeasureE pb lam e' * edgeKernelE pb e' e = edgeMeasureE pb lam e :=
  (edgeMeasureE_isInvariant hnn hlam hinv).2 e

/-- **`K₂^{λ₂}` is a Markov kernel on `E`**: its rows sum to `1`. -/
theorem reversal_row_sum {lam : V → ℝ} (hnn : ∀ x y, 0 ≤ pb x y) (hinv : Invariant pb lam)
    (hlam : ∀ x, 0 < lam x) (e : EdgeSet pb) :
    ∑ e' : EdgeSet pb, Core.reversal (edgeMeasureE pb lam) (edgeKernelE pb) e e' = 1 := by
  simp only [Core.reversal_apply]
  rw [← Finset.sum_div, lam2_invariant hnn (fun x => (hlam x).le) hinv e]
  exact div_self (mul_pos e.2 (hlam _)).ne'

/-! ### `ℓ = 1`: the formula of `cor:db_gradient` -/

theorem ratioAt_of_eq (μ : EdgeSet pb → ℝ) {a b : V} {e : EdgeSet pb} (h : (a, b) = e.1) :
    ratioAt pb μ a b = ratio pb μ e := by
  obtain ⟨⟨a', b'⟩, he⟩ := e
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact dif_pos he

/-- **`prop:tb_gradient`, at `ℓ = 1`: `ψ_1 = g'(r̂) dν̂_1/dμ`** (the proof's last bullet). -/
theorem psi_one {lam : V → ℝ} (hinv : Invariant pb lam) (hlam : ∀ x, 0 < lam x)
    {nu : (Fin (1 + 1) → V) → ℝ} (hnu : ∀ τ, 0 ≤ nu τ) (g : ℝ → ℝ) {μ : EdgeSet pb → ℝ}
    (hμ : ∀ e, 0 < μ e) (e : EdgeSet pb) :
    psi pb nu g μ 0 e = deriv g (ratio pb μ e) * (edgeMarg pb nu 0 e / μ e) := by
  have hF := marg_pos hinv hlam hμ
  rw [psi_eq hnu g hμ hF]
  have hw : weight pb nu g μ 0 e
      = deriv g (ratio pb μ e) * ratio pb μ e * edgeMarg pb nu 0 e := by
    simp only [weight, edgeMarg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs with h
    · have hr : rho pb μ τ = ratio pb μ e := by
        rw [rho, Fin.prod_univ_one]; exact ratioAt_of_eq μ h
      rw [hr]; ring
    · simp
  have hp := (push_pos hF e).ne'
  have hm := (hμ e).ne'
  rw [hw]
  simp only [ratio]
  field_simp

/-- **`prop:tb_gradient`, last sentence**: at `ℓ = 1` the right-hand side of `eq:tb_gradient` is
`(K₂^{λ₂} − r̂)[g'(r̂)(dν̂_1/dμ)λ₂]`, the display of `cor:db_gradient` for the training distribution
`ν̂_1`. -/
theorem grad_one {lam : V → ℝ} (hinv : Invariant pb lam) (hlam : ∀ x, 0 < lam x)
    {nu : (Fin (1 + 1) → V) → ℝ} (hnu : ∀ τ, 0 ≤ nu τ) (g : ℝ → ℝ) {μ : EdgeSet pb → ℝ}
    (hμ : ∀ e, 0 < μ e) (e : EdgeSet pb) :
    grad pb lam nu g μ e
      = measAct pb (Core.reversal (edgeMeasureE pb lam) (edgeKernelE pb))
          (fun e' => deriv g (ratio pb μ e') * (edgeMarg pb nu 0 e' / μ e') * edgeMeasureE pb lam e') e
        - ratio pb μ e
          * (deriv g (ratio pb μ e) * (edgeMarg pb nu 0 e / μ e) * edgeMeasureE pb lam e) := by
  simp only [grad, Fin.sum_univ_one, psi_one hinv hlam hnu g hμ]

/-! ### Inhabitation: a sparse edge set, `ℓ = 2` -/

/-- The swap on two states, `π_←(i → j) = [i ≠ j]`: `E = {(0,1), (1,0)}` is a proper subset of
`𝒮²`, so the witness exercises the edge-set restriction. -/
def swapPb : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 0 else 1

/-- The uniform law, invariant under the swap. -/
noncomputable def halfLam : Fin 2 → ℝ := fun _ => 1 / 2

/-- `ν̂ = δ_{(0,1,0)}`, a single trajectory of length `ℓ = 2` along `E`. -/
noncomputable def pathNu : (Fin (2 + 1) → Fin 2) → ℝ := fun τ => if τ = ![0, 1, 0] then 1 else 0

theorem swapPb_not_full : ¬ 0 < swapPb 0 0 := by simp [swapPb]

theorem halfLam_invariant : Invariant swapPb halfLam := by
  intro y
  fin_cases y <;> simp [swapPb, halfLam, Fin.sum_univ_two]

theorem pathNu_along : ∀ τ, pathNu τ ≠ 0 → AlongE swapPb τ := by
  intro τ h
  have hτ : τ = ![0, 1, 0] := by
    by_contra hc
    simp [pathNu, hc] at h
  subst hτ
  intro k
  fin_cases k <;> simp [swapPb]

/-- **`prop:tb_gradient`, inhabitation**: every hypothesis of `hasFDerivAt_loss` holds on the swap chain with a sparse
`E`, `ℓ = 2`, `ν̂ = δ_{(0,1,0)}` (charging a trajectory), `g(x) = (x−1)²` and `μ ≡ 1`, and the
conclusion is therefore delivered there. -/
theorem witness :
    pathNu ![0, 1, 0] = 1 ∧ ¬ 0 < swapPb 0 0 ∧
    HasFDerivAt (loss swapPb pathNu fun x => (x - 1) ^ 2)
        (fderiv ℝ (loss swapPb pathNu fun x => (x - 1) ^ 2) fun _ => 1) (fun _ => 1) ∧
      ∀ d, fderiv ℝ (loss swapPb pathNu fun x => (x - 1) ^ 2) (fun _ => 1) d
        = ip swapPb (edgeMeasureE swapPb halfLam)
            (grad swapPb halfLam pathNu (fun x => (x - 1) ^ 2) fun _ => 1) d := by
  refine ⟨by simp [pathNu], swapPb_not_full, ?_⟩
  exact hasFDerivAt_loss halfLam_invariant (fun _ => by norm_num [halfLam])
    (fun τ => by unfold pathNu; split_ifs <;> norm_num) pathNu_along
    ((contDiff_id.sub contDiff_const).pow 2).contDiffOn (fun _ => one_pos)

end GFNBounds.Balance.TBGradient
