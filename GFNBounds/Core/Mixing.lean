import GFNBounds.Doubling.Operator

/-!
# The mixing sum, and the Poisson equation it solves

**`lem:sigma_mixing`** — statement `proofs.tex:581–586`, proof `proofs.tex:588–590`
(Lemma 28 of the ICLR build) — and with it **Step 1** of **`theo:universality_L2_full`**
(`proofs.tex:87–98`).

The two statements are about one object: a bounded operator `P` on a Banach space together with
a projection `Pi` onto its invariant vectors, with `Pi P = P Pi = Pi` and

  `β n := ‖P ^ n - Pi‖`  summable,  `B := ∑' n, β n`.

The paper calls `β` the *`L^p`-mixing coefficients* (`equ:mixing_coefficients`,
`universality.tex:30–32`) and `B` the *mixing sum*. What the two statements need from that
setting is the same three conclusions, proved here once:

* `S := ∑' n, (P ^ n - Pi)` converges in operator norm, with `‖S‖ ≤ B`;
* the **Poisson equation** `S (1 - P) = (1 - P) S = 1 - Pi`;
* the **coercivity** `‖h - Pi h‖ ≤ B ‖(1 - P) h‖`, which is the "consequently" of
  `lem:sigma_mixing`.

**`lem:sigma_mixing` is the `p = 2` reading of Step 1 *with a different operator*.** The paper
says so at `proofs.tex:95`: "For `p = 2`, **and with `π*_→` replaced by the backward policy**,
this is Lemma `lem:sigma_mixing`" — so the invariant measure there is `λ`, not `ν_B`. The
abstraction below covers both, which is why one file discharges both; it is not that they are
the same instance.

## Reuse, and an architectural debt

The operator algebra is **not re-proved here.** `GFNBounds/Doubling/Operator.lean` already has
it — `partialSum`, `one_sub_mul_partialSum`, `partialSum_mul_one_sub`, `tendsto_pow`,
`resolvent_identities`, `resolvent_norm_le` — stated for an arbitrary bounded operator on a
Banach space, and in each case under a *weaker* hypothesis than summability (convergence of the
partial sums, and any bound on them). `docs/REPO-MAP.md` lists that file on the general-purpose
shelf, and the scaffold may import the strict library, so this file imports it and supplies only
what is new: the `Mixing` hypothesis bundle, `beta`/`B` as `tsum`s, and the coercivity.

The debt that creates: a `Core` module now depends on a `Doubling` one, which is backwards. The
shelf belongs in `Core/Operator.lean` with `Doubling` importing it. **Relocating it is the
master session's decision**, not this file's, so the dependency is recorded here rather than
silently taken.

## A notation clash, disclosed

The paper's projection onto the invariant densities is `Π`. `Π` is a reserved token in Lean 4,
so it is written **`Pi`** throughout this file, in the docstrings as well as the code, rather
than silently in one and not the other. Beware: a variable named `Pi` **shadows Mathlib's `Pi`
namespace**, so `Pi.sub_apply` and its neighbours must be written `_root_.Pi.sub_apply` in any
file that computes pointwise while a `Pi` is in scope.

## The modelling decision

**The operator is the primitive, not the kernel.** `theo:universality_L2_full` hypothesizes a
Markov kernel `π*` whose density action `P⋆` has *finite* `L^p(ν_B) → L^p(ν_B)` operator norm —
the body says in as many words that this is "a genuine requirement on the parameterization" and
not automatic beyond `p = 1` (`universality.tex:5–8`). Everything Step 1 uses is that bounded
operator and the projection; nothing here needs the kernel, the measure, or even the lattice
structure of `L^p`.

That is also why `Pi` is a hypothesis rather than a construction. On `L^p(ν_B)` with `ν_B`
finite and `π*` ergodic, `Pi f = (∫ f dν_B / ν_B(𝒮)) • 1` is the mean projection onto the
invariant densities (`proofs.tex:22`), and `Pi P = P Pi = Pi` holds because the density action
preserves integrals and `ν_B π* = ν_B` fixes the constants (`proofs.tex:589`). **That derivation
is not in this library.** It is `Core.Flow`, which **does not exist**: the kernel-to-operator
passage that `CLAUDE.md` names as *obstruction 2*, "the `L^p` layer with its adjoint — the
analysis is done; the functional analysis around it is not". Until it exists, `Mixing` is a
hypothesis, and nothing is claimed about when it holds.

## SCOPE (disclosed)

`Mixing` assumes the two intertwining identities and summability, and **not** idempotence of
`Pi`, `‖Pi‖ ≤ 1`, or that `Pi` projects onto `ker (1 - P)`. Two of those are not concessions but
consequences, and saying only "not assumed" would understate the bundle: `proj_idem` derives
`Pi * Pi = Pi` from summability alone, and if `(1 - P) x = 0` then `P ^ n x = x` for every `n`,
so `P ^ n → Pi` gives `Pi x = x` — `Pi` *is* forced to be the projection onto `ker (1 - P)`. The
hypothesis is therefore tighter than its statement suggests, in the safe direction.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `L^2(λ)` (`lem:sigma_mixing`) / `L^p(ν_B)` (Step 1) | ⚠ weakened to any Banach space over `ℝ` |
| `P` the density action of an ergodic policy | ⚠ weakened to any bounded operator |
| `Π` the mean projection onto the invariant densities | ⚠ weakened to `Pi * P = Pi`, `P * Pi = Pi` |
| `Π P = P Π = Π` *derived* from ergodicity and invariance | ⚠ **assumed**; the derivation is `Core.Flow`, which does not exist |
| `B̂ = Σ β̂_n < ∞` | ✓ carried (`Mixing.summable`) |
| `β̂_0 = 1` | not needed; the conclusions use only `B ≥ 0`, and `B̂ ≥ 1` holds in the paper's normalization |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Core

open scoped Topology

/-- The hypothesis shared by `lem:sigma_mixing` and Step 1 of `theo:universality_L2_full`:
a bounded operator `P` and a projection `Pi` onto its invariant vectors, whose mixing
coefficients `n ↦ ‖P ^ n - Pi‖` are summable.

`proj_left` and `proj_right` are the paper's `Π P_⋆ = P_⋆ Π = Π`, which on `L^p(ν_B)` hold
because the density action preserves `ν_B`-integrals and fixes the constants. -/
structure Mixing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Pi : E →L[ℝ] E) : Prop where
  /-- `Pi P = Pi`: the projection kills whatever one step of `P` changes. -/
  proj_left : Pi * P = Pi
  /-- `P Pi = Pi`: the invariant vectors are fixed by `P`. -/
  proj_right : P * Pi = Pi
  /-- Summable mixing: `∑ β n < ∞` with `β n = ‖P ^ n - Pi‖`. -/
  summable : Summable fun n : ℕ => ‖P ^ n - Pi‖

namespace Mixing

open Filter GFNBounds.Doubling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P Pi : E →L[ℝ] E}

/-- The mixing coefficients `β_n = ‖P ^ n - Pi‖` of `equ:mixing_coefficients`. -/
noncomputable def beta (P Pi : E →L[ℝ] E) (n : ℕ) : ℝ := ‖P ^ n - Pi‖

/-- The mixing sum `B = ∑_{n ≥ 0} β_n` of `equ:mixing_coefficients`; the appendix writes it
`B̂` at `p = 2`. -/
noncomputable def B (P Pi : E →L[ℝ] E) : ℝ := ∑' n : ℕ, beta P Pi n

theorem summable_beta (h : Mixing P Pi) : Summable (beta P Pi) := h.summable

theorem beta_nonneg (P Pi : E →L[ℝ] E) (n : ℕ) : 0 ≤ beta P Pi n := norm_nonneg _

theorem B_nonneg (P Pi : E →L[ℝ] E) : 0 ≤ B P Pi :=
  tsum_nonneg fun n => beta_nonneg P Pi n

/-- The family `n ↦ P ^ n - Pi` is summable: absolutely so, by hypothesis. -/
theorem summable_terms [CompleteSpace E] (h : Mixing P Pi) :
    Summable fun n : ℕ => P ^ n - Pi :=
  Summable.of_norm h.summable

/-- The **mixing sum operator** `S = ∑_{n ≥ 0} (P^n - Pi)` of `equ:poisson`. -/
noncomputable def S (P Pi : E →L[ℝ] E) : E →L[ℝ] E := ∑' n : ℕ, (P ^ n - Pi)

/-- `S` is the limit of `GFNBounds.Doubling.partialSum`, which is the hypothesis every result
of `Doubling/Operator.lean` consumes. -/
theorem tendsto_partialSum [CompleteSpace E] (h : Mixing P Pi) :
    Tendsto (partialSum P Pi) atTop (𝓝 (S P Pi)) :=
  h.summable_terms.hasSum.tendsto_sum_nat

/-- Summable mixing forces `P ^ n → Pi` in operator norm — the appendix's
`‖P^{N+1} - Π‖ = β_{N+1} → 0`. -/
theorem tendsto_pow [CompleteSpace E] (h : Mixing P Pi) :
    Tendsto (fun n : ℕ => P ^ n) atTop (𝓝 Pi) :=
  GFNBounds.Doubling.tendsto_pow h.tendsto_partialSum

/-- `Pi` is idempotent: `P ^ n → Pi` while `P ^ (n+1) Pi = Pi` throughout. Needed to feed
`resolvent_identities`, which carries idempotence as a hypothesis. -/
theorem proj_idem [CompleteSpace E] (h : Mixing P Pi) : Pi * Pi = Pi := by
  have hfix : ∀ n : ℕ, P ^ (n + 1) * Pi = Pi := by
    intro n
    induction n with
    | zero => simpa using h.proj_right
    | succ k ih => rw [pow_succ, mul_assoc, h.proj_right]; exact ih
  have hlim : Tendsto (fun n : ℕ => P ^ (n + 1) * Pi) atTop (𝓝 (Pi * Pi)) :=
    ((continuous_mul_const Pi).tendsto _).comp
      (h.tendsto_pow.comp (tendsto_add_atTop_nat 1))
  refine tendsto_nhds_unique hlim ?_
  simp only [hfix]
  exact tendsto_const_nhds

/-- `‖S‖ ≤ B`: the operator-norm bound behind `theo:universality_L2_full`'s
`‖Sθ‖ ≤ B_p ‖θ‖`. -/
theorem norm_S_le [CompleteSpace E] (h : Mixing P Pi) : ‖S P Pi‖ ≤ B P Pi :=
  resolvent_norm_le h.tendsto_partialSum fun N =>
    h.summable_beta.sum_le_tsum (Finset.range N) fun n _ => beta_nonneg P Pi n

/-- `‖S θ‖ ≤ B ‖θ‖`, which is how `theo:universality_L2_full` states the bound. -/
theorem norm_S_apply_le [CompleteSpace E] (h : Mixing P Pi) (θ : E) :
    ‖S P Pi θ‖ ≤ B P Pi * ‖θ‖ :=
  ((S P Pi).le_opNorm θ).trans (mul_le_mul_of_nonneg_right h.norm_S_le (norm_nonneg θ))

/-- **The Poisson equation, right form**: `S (1 - P) = 1 - Pi`. This is `equ:poisson` of
`theo:universality_L2_full` and the `S(I-P) = I - Π` of `lem:sigma_mixing`. -/
theorem poisson_right [CompleteSpace E] (h : Mixing P Pi) : S P Pi * (1 - P) = 1 - Pi :=
  (resolvent_identities h.proj_idem h.proj_left h.proj_right h.tendsto_partialSum).2.1

/-- **The Poisson equation, left form**: `(1 - P) S = 1 - Pi`. -/
theorem poisson_left [CompleteSpace E] (h : Mixing P Pi) : (1 - P) * S P Pi = 1 - Pi :=
  (resolvent_identities h.proj_idem h.proj_left h.proj_right h.tendsto_partialSum).1

/-- The Poisson equation, applied: `S ((1 - P) θ) = θ - Pi θ`. -/
theorem poisson_right_apply [CompleteSpace E] (h : Mixing P Pi) (θ : E) :
    S P Pi ((1 - P) θ) = θ - Pi θ := by
  have := congrArg (fun T : E →L[ℝ] E => T θ) h.poisson_right
  simpa using this

/-- The Poisson equation, applied on the other side: `(1 - P) (S θ) = θ - Pi θ`. -/
theorem poisson_left_apply [CompleteSpace E] (h : Mixing P Pi) (θ : E) :
    (1 - P) (S P Pi θ) = θ - Pi θ := by
  have := congrArg (fun T : E →L[ℝ] E => T θ) h.poisson_left
  simpa using this

/-- **The Poisson equation solves exactly on mean-zero data**, the form Step 2 consumes: if
`Pi θ = 0` then `(1 - P) (S θ) = θ`. The appendix's `equ:poisson_solved`
(`proofs.tex:96–98`). -/
theorem poisson_solved [CompleteSpace E] (h : Mixing P Pi) {θ : E} (hθ : Pi θ = 0) :
    (1 - P) (S P Pi θ) = θ := by
  rw [h.poisson_left_apply θ, hθ, sub_zero]

/-- **Mixing controls coercivity** — the "consequently" of `lem:sigma_mixing`, and the only
part of it the paper's downstream consumers use (`proofs.tex:872`).

Stated as a product rather than a quotient so that it says something at `B = 0` too: there
`Pi = P ^ 0 = 1` and `P = 1`, both sides are `0`, and the claim is true if contentless. In the
paper's normalization `β̂_0 = ‖I - Π‖ = 1`, so `B̂ ≥ 1` and that corner never arises. -/
theorem coercivity [CompleteSpace E] (h : Mixing P Pi) (x : E) :
    ‖x - Pi x‖ ≤ B P Pi * ‖(1 - P) x‖ := by
  have hx := h.poisson_right_apply x
  calc ‖x - Pi x‖ = ‖S P Pi ((1 - P) x)‖ := by rw [hx]
    _ ≤ B P Pi * ‖(1 - P) x‖ := h.norm_S_apply_le _

/-- The quotient form of `lem:sigma_mixing`'s display. The hypothesis `0 < B` is free in the
paper, where `β̂_0 = 1` forces `B̂ ≥ 1`. -/
theorem coercivity_div [CompleteSpace E] (h : Mixing P Pi) (hB : 0 < B P Pi) (x : E) :
    ‖x - Pi x‖ / B P Pi ≤ ‖(1 - P) x‖ :=
  (div_le_iff₀ hB).2 <| by rw [mul_comm]; exact h.coercivity x

end Mixing

end GFNBounds.Core
