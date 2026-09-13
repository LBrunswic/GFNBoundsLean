import GFNBounds.Balance.WeightedL2
import GFNBounds.Core.MixingBase

/-!
# The mean projection is orthogonal on `L²(λ)`, so `β̂₀ = ‖I − Π‖ = 1` exactly

**`lem:sigma_mixing`** — statement `proofs.tex:581–586`, proof `proofs.tex:588–590`. This file
certifies the **normalization inside its hypothesis**, `β̂₀ = 1`, on a finite state space; the
lemma's conclusion is closed in `GFNBounds/Core/Mixing.lean`.

**`prop:nonlinear_freezing`** — statement `proofs.tex:780–788`, item *(2)* at `:784`, its proof
at `:799`. This file certifies item *(2)*'s parenthesis `β̂ₙ = 0` for `n ≥ 1`, `B̂ = 1`,
`ϱ = 2w_min`, and its claim that this rate is maximal; the rest of item *(2)* is closed in
`GFNBounds/Balance/Freezing.lean`.

Neither label is certified whole here: the file serves both. (The bold-backtick form of a label
is what `scripts/trace_check.py` and the paper-side ledger machine-read.)

> (`lem:sigma_mixing`, `proofs.tex:582`) Assume `B̂ := ∑_{n≥0} β̂_n < +∞` (summable `L²`-mixing,
> `β̂₀ = 1`). Then `S := ∑_{n≥0}(P^n − Π)` converges in operator norm, `S(I−P) = I − Π`, and
> consequently `∀ h ∈ L²(λ), ‖(I−P)h‖_{L²(λ)} ≥ ‖h − Πh‖_{L²(λ)} / B̂`.

> (`prop:nonlinear_freezing`*(2)*, `proofs.tex:784`) on the two-state chain `T(i→j) = 1/2`,
> `λ = (1/2,1/2)` — for which `β̂ₙ = 0` for all `n ≥ 1`, `B̂ = 1`, and the rate `ϱ = 2w_min` of
> Theorem `theo:db_stable_frozen` is maximal — […]

> (its proof, `proofs.tex:799`) On the two-state chain, the density action is
> `Ph = (∫h dλ)𝟏 = Πh`, so `Pⁿ − Π = 0` for every `n ≥ 1`: `β̂ₙ = 0`, `B̂ = β̂₀ = 1` and
> `ϱ = g''(1)w_min = 2w_min`.

> (`theo:local_convergence_full`, Step 6, `proofs.tex:652`) since `B̂ ≥ β̂₀ = 1`,
> `ϱ ≤ g''(1)w_min`

## Why this needs the weighted inner product

`GFNBounds/Core/MixingBase.lean` proves `1 ≤ ‖I − Π‖` for any idempotent `Π ≠ I` and **refutes**
the equality at the generality of `Core.Mixing` (`not_forall_beta_zero_eq_one`, an oblique
projection with `β̂₀ = 2`). The equality is a property of the paper's `Π`, the mean projection
`Πh = (∫h dλ)𝟏` (`proofs.tex:22`), and what makes it true is that `Π` is **self-adjoint** for
`⟪·∣·⟫_λ`, so that the upper bound is Pythagoras, `‖h‖² = (Πh)² + ‖h − Πh‖²`. On `V → ℝ` that
identity is already `GFNBounds.Balance.nrmL2_perpL2_le` (`L2Toolkit.lean`), where `∑λ = 1` is
spent; the proof below transports it through the weighting (`sub_meanOp_wtL2`, `norm_wtL2`).

The operator norm is taken on `EuclideanSpace ℝ V`. That is the paper's `L²(λ)` operator norm:
`meanOp` and `densOp` are the paper's `Π` and `P` conjugated by the weighting `w_λ`, which is a
linear bijection carrying `‖·‖_{L²(λ)}` to the Euclidean norm (`norm_wtL2`, `exists_wtL2`), and
conjugation by a surjective isometry preserves operator norms.

## What is proved

| | |
|---|---|
| `one_sub_meanOp_ne_zero` | `I − Π ≠ 0` once `V` has two states: the indicator of a state is not constant |
| `norm_one_sub_meanOp` | **`‖I − Π‖ = 1`** on `L²(λ)` |
| `beta_zero_densOp_meanOp` | **`β̂₀ = 1`** for `Core.Mixing.beta (densOp λ K) (meanOp λ)`, every `K` |
| `one_le_B_densOp` | `1 ≤ B̂` for summable mixing at `(densOp λ K, meanOp λ)` |
| `twoState_densOp_eq_meanOp` | `P = Π` on the two-state chain, as bounded operators on `L²(λ)` |
| `twoState_mixing_densOp` | **`Core.Mixing (densOp λ K) (meanOp λ)` exhibited**, on the two-state chain |
| `twoState_beta_succ`, `twoState_beta_zero`, `twoState_B_densOp` | `β̂ₙ = 0` for `n ≥ 1`, `β̂₀ = 1`, `B̂ = 1` there |
| `twoState_mixing_coefficients` | item *(2)*'s parenthesis `β̂ₙ = 0 (n ≥ 1)`, `B̂ = β̂₀ = 1`, as one statement |
| `rho_densOp_le` | `ϱ = g''(1)w_min/B̂² ≤ g''(1)w_min` for summable mixing at `(P, Π)`: the general ceiling (`proofs.tex:652`) |
| `twoState_rho_eq` | `ϱ = g''(1)w_min/B̂² = g''(1)w_min` on the two-state chain: the ceiling attained |
| `twoState_rho_freezing` | `ϱ = 2w_min` at the generator of `prop:nonlinear_freezing`, `g''(1) = 2` from `FreezingBands.deriv_deriv_g_one` |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `L²(λ)`, `λ` a probability | ⚠ **restricted**, as in `WeightedL2.lean`: `Fintype V`, `λ > 0` pointwise (`hlam`), `∑_x λ(x) = 1` (`htot`) |
| (silent) the state space has at least two states | ⚠ **made explicit** as `[Nontrivial V]`, and necessary: with one state `Π = I`, `‖I − Π‖ = 0` and `β̂₀ = 0`. The paper's settings all carry an edge, so it is entitled to it |
| `β̂₀ = ‖P⁰ − Π‖ = ‖I − Π‖` on `L²(λ)` | ✓ carried, `Core.Mixing.beta_zero` at the conjugated operators |
| `β̂₀ = 1` | ✓ **proved** (`beta_zero_densOp_meanOp`); `htot` is spent through `meanOp_idem`, and `K` is unconstrained because `β̂₀` does not involve `P` |
| `Π` orthogonal | ✓ **proved**, not assumed: the Pythagoras bound `nrmL2_perpL2_le` and `meanOp_idem`; `meanOp_selfAdjoint` is the same fact in operator form |
| `B̂ ≥ β̂₀` | ✓ `one_le_B_densOp`, from `Core.Mixing.one_le_B`; needs `hmx` and `hlam` only |
| two-state chain `T(i→j) = 1/2`, `λ = (1/2,1/2)` | ✓ `twoStateK`, `twoStateLam` of `Freezing.lean`, the same objects its item *(2)* uses |
| `Ph = Πh` | ✓ `twoState_densOp_eq_meanOp`, as an operator identity |
| `β̂ₙ = 0` (`n ≥ 1`), `B̂ = β̂₀ = 1` | ✓ `twoState_mixing_coefficients`, with summability exhibited (`twoState_mixing_densOp`) rather than assumed |
| `ϱ = 2w_min` | ✓ `twoState_rho_freezing`, at `g''(1) := deriv (deriv F.g) 1` for every `F : FreezingBands`, with `g''(1) = 2` linked by `FreezingBands.deriv_deriv_g_one`; `twoState_rho_eq` is the same at an arbitrary `g''(1)` |
| "`ϱ` is maximal" | ✓ **certified** in the sense `proofs.tex:652` makes precise: every summably mixing `(P, Π)` on a finite `L²(λ)` with two states has `ϱ ≤ g''(1)w_min` (`rho_densOp_le`, from `B̂ ≥ β̂₀ = 1`), and the two-state chain attains it (`twoState_rho_eq`). `0 ≤ g''(1)w_min` is carried |

## SCOPE (disclosed)

* **Finite state spaces, `λ > 0` pointwise, `∑λ = 1`**, inherited from `WeightedL2.lean`. The
  general `L²(λ)` on a measure space with its adjoint is obstruction 2
  (`kb/entries/0006-three-obstructions.md`); this is its finite-dimensional face at `p = 2`.
* **`[Nontrivial V]` is required and is not written in the paper.** It is not a weakening of the
  paper's claim: on a one-state space the paper's `β̂₀ = 1` is false.
* **`lem:sigma_mixing`'s conclusion is not restated.** It is `GFNBounds.Core.Mixing.coercivity`,
  read on `V → ℝ` by `GFNBounds.Balance.mixing_coercivity_finite`.
* **`prop:nonlinear_freezing`*(2)* is not re-proved.** Only its parenthesis on the mixing
  coefficients is certified here; the frozen open set, the ratios and stationarity are in
  `Freezing.lean`. "`ϱ` is maximal" is read as `proofs.tex:652` reads it — the ceiling
  `ϱ ≤ g''(1)w_min` over summably mixing chains on a finite state space, attained here — and is
  certified in that form only, not as a comparison over the paper's general measured setting.
* **Nothing downstream is rewired.** `WeightedL2.lean`'s SCOPE records that
  `Core.Mixing (densOp λ K) (meanOp λ)` is never exhibited and that `‖I − Π‖ = 1` is not proved;
  both are now done here, and `stable_frozen_discrete_mixing`'s `hBpos` can be discharged by
  `Core.Mixing.B_pos` with `one_sub_meanOp_ne_zero`. Editing that file is the master's call.
* **`sorry`-free**; `#print axioms` on every declaration returns
  `[propext, Classical.choice, Quot.sound]`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

variable {V : Type*} [Fintype V]

/-! ### `‖I − Π‖ = 1` on `L²(λ)` -/

/-- **`I − Π ≠ 0`** as soon as there are two states: the weighting of the indicator of `x₀` is
not `Π`-invariant, since a constant cannot be `1` at `x₀` and `0` at `x₁ ≠ x₀`. No normalization
of `λ` is needed. -/
theorem one_sub_meanOp_ne_zero [Nontrivial V] {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) :
    (1 : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) - meanOp lam ≠ 0 := by
  classical
  obtain ⟨x0, x1, hx⟩ := exists_pair_ne V
  rw [Core.Mixing.one_sub_ne_zero_iff]
  refine ⟨wtL2 lam (fun x => if x = x0 then 1 else 0), fun hfix => ?_⟩
  rw [meanOp_wtL2 hlam] at hfix
  have hfun := wtL2_injective hlam hfix
  have h0 := congrFun hfun x0
  have h1 := congrFun hfun x1
  rw [if_pos rfl] at h0
  rw [if_neg hx.symm] at h1
  rw [h0] at h1
  exact one_ne_zero h1

/-- **`‖I − Π‖ = 1`** on `L²(λ)`, `Π` the mean projection. The upper bound is Pythagoras,
`‖h − Πh‖_{L²(λ)} ≤ ‖h‖_{L²(λ)}` (`nrmL2_perpL2_le`) read through the weighting; the lower bound
is `Core.Mixing.one_le_norm_one_sub_proj`. -/
theorem norm_one_sub_meanOp [Nontrivial V] {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) :
    ‖(1 : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) - meanOp lam‖ = 1 := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  have hidem : meanOp lam * meanOp lam = meanOp lam :=
    ContinuousLinearMap.ext fun u => meanOp_idem hlam htot u
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_)
    (Core.Mixing.one_le_norm_one_sub_proj hidem (one_sub_meanOp_ne_zero hlam))
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  have happ : ((1 : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) - meanOp lam) (wtL2 lam a)
      = wtL2 lam a - meanOp lam (wtL2 lam a) := rfl
  rw [happ, one_mul, sub_meanOp_wtL2 hlam, norm_wtL2 hnn, norm_wtL2 hnn]
  exact nrmL2_perpL2_le hnn htot a

/-! ### The mixing coefficients at `(P, Π)` -/

/-- **`β̂₀ = 1`** — the normalization in `lem:sigma_mixing`'s hypothesis (`proofs.tex:582`), for
the paper's `Π` on `L²(λ)`. `β̂₀ = ‖P⁰ − Π‖` does not involve `P`, so `K` is arbitrary. -/
theorem beta_zero_densOp_meanOp [Nontrivial V] {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (K : V → V → ℝ) :
    Core.Mixing.beta (densOp lam K) (meanOp lam) 0 = 1 := by
  rw [Core.Mixing.beta_zero, norm_one_sub_meanOp hlam htot]

/-- **`1 ≤ B̂`** for summable mixing at the paper's `(P, Π)`: the hypothesis
`LocalConvergence.lean` and `RatioBridge.lean` carry as `hB1`, once their `B̂` is the mixing sum.
Idempotence comes from `hmx`, so `∑λ = 1` is not needed. -/
theorem one_le_B_densOp [Nontrivial V] {lam : V → ℝ} {K : V → V → ℝ} (hlam : ∀ x, 0 < lam x)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam)) :
    1 ≤ Core.Mixing.B (densOp lam K) (meanOp lam) :=
  hmx.one_le_B (one_sub_meanOp_ne_zero hlam)

/-- **`ϱ ≤ g''(1)w_min`** (`proofs.tex:652`, "since `B̂ ≥ β̂₀ = 1`"): the rate
`ϱ = g''(1)w_min/B̂²` of `theo:db_stable_frozen_full`, with `B̂` the mixing sum at the paper's
`(P, Π)`, never exceeds `g''(1)w_min`. This is the ceiling `prop:nonlinear_freezing`*(2)* calls
maximal; `twoState_rho_eq` attains it. -/
theorem rho_densOp_le [Nontrivial V] {lam : V → ℝ} {K : V → V → ℝ} {g2 wmin : ℝ}
    (hlam : ∀ x, 0 < lam x) (hmx : Core.Mixing (densOp lam K) (meanOp lam))
    (h0 : 0 ≤ g2 * wmin) :
    g2 * wmin / Core.Mixing.B (densOp lam K) (meanOp lam) ^ 2 ≤ g2 * wmin :=
  div_le_self h0 (one_le_pow₀ (one_le_B_densOp hlam hmx))

/-! ### The two-state chain of `prop:nonlinear_freezing`*(2)* -/

section TwoState

theorem twoStateLam_sum : ∑ x, twoStateLam x = 1 := by
  simp only [Fin.sum_univ_two, twoStateLam]
  norm_num

/-- **`P = Π` on the two-state chain** (`proofs.tex:799`), as bounded operators on `L²(λ)`. -/
theorem twoState_densOp_eq_meanOp : densOp twoStateLam twoStateK = meanOp twoStateLam := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨a, rfl⟩ := exists_wtL2 twoStateLam_pos u
  rw [densOp_wtL2 twoStateLam_pos, meanOp_wtL2 twoStateLam_pos]
  congr 1
  funext y
  simp only [Core.densAct_apply, Graph.meanL2, Fin.sum_univ_two, twoStateK, twoStateLam]
  ring

theorem twoState_meanOp_idem : meanOp twoStateLam * meanOp twoStateLam = meanOp twoStateLam :=
  ContinuousLinearMap.ext fun u => meanOp_idem twoStateLam_pos twoStateLam_sum u

/-- **Summable mixing at `(P, Π)`, exhibited**: on the two-state chain `P = Π` is idempotent, so
`Pⁿ − Π = 0` for `n ≥ 1` and the sum is finite. -/
theorem twoState_mixing_densOp :
    Core.Mixing (densOp twoStateLam twoStateK) (meanOp twoStateLam) := by
  rw [twoState_densOp_eq_meanOp]
  exact Core.Mixing.of_idem twoState_meanOp_idem

/-- `β̂ₙ = 0` for `n ≥ 1` on the two-state chain. -/
theorem twoState_beta_succ (n : ℕ) :
    Core.Mixing.beta (densOp twoStateLam twoStateK) (meanOp twoStateLam) (n + 1) = 0 := by
  rw [Core.Mixing.beta, twoState_densOp_eq_meanOp,
    IsIdempotentElem.pow_succ_eq n twoState_meanOp_idem, sub_self, norm_zero]

/-- `β̂₀ = 1` on the two-state chain. -/
theorem twoState_beta_zero :
    Core.Mixing.beta (densOp twoStateLam twoStateK) (meanOp twoStateLam) 0 = 1 :=
  beta_zero_densOp_meanOp twoStateLam_pos twoStateLam_sum twoStateK

/-- `B̂ = 1` on the two-state chain. -/
theorem twoState_B_densOp :
    Core.Mixing.B (densOp twoStateLam twoStateK) (meanOp twoStateLam) = 1 := by
  rw [twoState_densOp_eq_meanOp, Core.Mixing.B_of_idem twoState_meanOp_idem,
    norm_one_sub_meanOp twoStateLam_pos twoStateLam_sum]

/-- **`prop:nonlinear_freezing`*(2)*, the parenthesis on the mixing coefficients**
(`proofs.tex:784`, proof `:799`): on the two-state chain `β̂ₙ = 0` for all `n ≥ 1` and
`B̂ = β̂₀ = 1`, with `B̂` the paper's `∑_{n≥0}‖Pⁿ − Π‖` on `L²(λ)`. -/
theorem twoState_mixing_coefficients :
    (∀ n : ℕ, 1 ≤ n →
        Core.Mixing.beta (densOp twoStateLam twoStateK) (meanOp twoStateLam) n = 0)
      ∧ Core.Mixing.B (densOp twoStateLam twoStateK) (meanOp twoStateLam)
          = Core.Mixing.beta (densOp twoStateLam twoStateK) (meanOp twoStateLam) 0
      ∧ Core.Mixing.beta (densOp twoStateLam twoStateK) (meanOp twoStateLam) 0 = 1 := by
  refine ⟨fun n hn => ?_, by rw [twoState_B_densOp, twoState_beta_zero], twoState_beta_zero⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact twoState_beta_succ k

/-- **`ϱ = g''(1)w_min`** on the two-state chain (`proofs.tex:799`): the rate
`ϱ = g''(1)w_min/B̂²` of `theo:db_stable_frozen_full`, with `B̂` the mixing sum, loses nothing to
mixing. At `g''(1) = 2` this is item *(2)*'s `ϱ = 2w_min`. -/
theorem twoState_rho_eq (g2 wmin : ℝ) :
    g2 * wmin / Core.Mixing.B (densOp twoStateLam twoStateK) (meanOp twoStateLam) ^ 2
      = g2 * wmin := by
  rw [twoState_B_densOp, one_pow, div_one]

/-- **`ϱ = 2w_min`** — `prop:nonlinear_freezing`*(2)* (`proofs.tex:784`, proof `:799`) at the
proposition's own generator: `g''(1) = deriv (deriv F.g) 1 = 2` for every `F : FreezingBands`
(`FreezingBands.deriv_deriv_g_one`), and `B̂ = 1` on the two-state chain. -/
theorem twoState_rho_freezing (F : FreezingBands) (wmin : ℝ) :
    deriv (deriv F.g) 1 * wmin
        / Core.Mixing.B (densOp twoStateLam twoStateK) (meanOp twoStateLam) ^ 2
      = 2 * wmin := by
  rw [twoState_rho_eq, F.deriv_deriv_g_one]

end TwoState

end GFNBounds.Balance
