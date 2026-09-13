import GFNBounds.Doubling.Operator
import GFNBounds.Doubling.OperatorL2

/-!
# On a finite chain the diffusion operator is at most the mixing sum

**`lem:doubling_operator`(3), its "in particular" clause** — `app_doubling.tex:166–262`
(statement `:166–191`, proof `:193–262`).

> in particular, on a finite irreducible chain `B̂ ≤ Σ_{n≥0} β̂_n`, the inequality being vacuous
> when its right side is `+∞`.

and the sentence of the proof that delivers it:

> On a finite irreducible chain `S` is defined by *(2)*: when `Σ_{n≥0} β̂_n = +∞` the bound
> `B̂ ≤ Σ_{n≥0} β̂_n` holds with an infinite right side, and when that sum is finite the series
> `Σ_{n≥0}(P⋆^n − Π)` converges absolutely in operator norm by *(1)*, so `S = U` and the bound is
> the one just proved.

Here `S := (Id − P⋆ + Π)^{-1} − Π` and `B̂ := ‖S‖_{L²(λ)}` (the lemma's preamble).

The same inequality is the one mathematical claim of **`rem:doubling_two_constants`** —
`app_doubling.tex:264–274`:

> item *(3)* of Lemma `lem:doubling_operator` orders the two on any finite irreducible chain

and it is certified by `Stat.inverse_sub_piL2_le_sum_betaHat` below.

## What was missing, and what this file supplies

`Operator.lean` proved item (3) under its own hypothesis — the partial sums of `Σ(P⋆^n − Π)`
converge in operator norm to a given `U` — and `OperatorL2.lean` produced *an* inverse of
`Id − P⋆ + Π` on the truncation. Nothing joined them, and nothing let the right side be infinite.

* `resolvent_eq_tsum_of_bdd` is the join, in a Banach space: a real `B` bounding every partial sum
  of `Σ‖P^n − Π‖` makes that series summable, hence `Σ(P^n − Π)` absolutely convergent
  (completeness), so `resolvent_inverse` applies, and uniqueness of a left inverse gives
  `R − Π = Σ'(P^n − Π)` with `‖R − Π‖ ≤ B`.
* `inverse_sub_le_of_bdd` is the "in particular" in the finite-dimensional abstract setting of
  `OperatorFinite.lean`, at `Ring.inverse` — no inverse is assumed.
* `Stat.bhat_le_sum_betaHat`, `Stat.sub_piL2_eq_tsum`, `Stat.inverse_sub_piL2_le_sum_betaHat` and
  `Stat.inverse_sub_piL2_eq_tsum` instantiate it on `L²(λ^K)`, with the paper's `β̂_n`
  (`Stat.betaHat`, defined on the density action) reached through
  `Stat.norm_pstarL2_pow_sub_piL2`.

**How "vacuous when `+∞`" is rendered.** The inequality is stated for every real `B` bounding the
partial sums `Σ_{n<N} β̂_n`. When the series diverges no such `B` exists and the statement says
nothing — exactly the paper's vacuity — and `tsum` is never evaluated off its domain, where it
would return `0`. When the series converges, `B := Σ' β̂_n` is admissible
(`Stat.inverse_sub_piL2_eq_tsum`), which is the paper's inequality with a finite right side,
together with `S = U`.

## SCOPE (disclosed)

* **The finite irreducible chain is the truncation of the doubling graph at `K`**, `Stat S (some K)`
  with `S.d ≤ K`, not an arbitrary finite irreducible chain. The library models `L²(λ)` and `P⋆`
  only for this graph. The mathematics is not specific to it: `inverse_sub_le_of_bdd` holds on
  every finite-dimensional space carrying the three intertwining identities and `hker`, which is
  the whole of what the paper's argument consumes; instantiating it at another finite chain needs
  that chain's `L²` layer, which this library does not have.
* **Irreducibility is not used in this form**, exactly as in `OperatorL2.lean`: invertibility of
  `Id − P⋆ + Π` comes from `Stat.exists_diffusionOp`, whose `hker` is proved from
  `Stat.fixed_const_memLp` directly. `λ` is any `Stat S (some K)`.
* **The `R`-forms assume only a left inverse** (`R * (Id − P⋆ + Π) = 1`). Bounded partial sums
  already force `Id − P⋆ + Π` to be invertible, so a left inverse is the inverse; the right-inverse
  hypothesis would be unused. This is a weakening of a hypothesis, not of a conclusion.
* **`rem:doubling_two_constants` beyond the ordering is not here**: that the two constants "need not
  coincide" and "differ on the truncation at which §`sec:doubling_measured` measures both" is a
  numerical observation, and the trajectory reading
  `(Sθ)(x) = Σ_n (E(θ(X_n) | X₀ = x) − λ(θ))` needs a chain, which Mathlib does not have
  (kb `0006`, obstruction 1).
* Items (1), (2) and the convergent case of (3) are `AdjointL2.lean`, `OperatorL2.lean` and
  `Operator.lean`; they are not restated here.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| a finite chain | ⚠ **specialized** to the truncation `Stat S (some K)`; abstractly `FiniteDimensional ℝ E` (`inverse_sub_le_of_bdd`) |
| irreducible | ⚠ **replaced** by its consequence `hker`, proved on the truncation (`Stat.exists_diffusionOp`) |
| `λ` the invariant probability | ⚠ weakened: any `Stat S (some K)` |
| `S := (Id − P⋆ + Π)^{-1} − Π` | ✓ carried as `Ring.inverse (1 − P⋆ + Π) − Π`; ⚠ `R`-forms: any left inverse |
| `β̂_n := ‖P^n − Π‖_{L²(λ)}` | ✓ carried (`Stat.betaHat`, on the density action) |
| `B̂ ≤ Σ β̂_n`, vacuous when `+∞` | ✓ carried: every real `B` bounding the partial sums |
| sum finite ⇒ `S = U` | ✓ carried (`Stat.inverse_sub_piL2_eq_tsum`, under `Summable`) |
| — | ⚠ **added**: `S.d ≤ K` (`RowOnChain`), as throughout the `L²` layer |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Filter Topology MeasureTheory

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P Pi R : E →L[ℝ] E}

/-- **`lem:doubling_operator`(3), with the partial sums bounded instead of convergent.** In a
Banach space, if every partial sum of `Σ‖P^n − Π‖` is at most `B`, then the series `Σ(P^n − Π)`
converges absolutely, a left inverse `R` of `Id − P + Π` satisfies `R − Π = Σ'(P^n − Π)`, and
`‖R − Π‖ ≤ B`. -/
theorem resolvent_eq_tsum_of_bdd [CompleteSpace E] (hPi2 : Pi * Pi = Pi) (hPiP : Pi * P = Pi)
    (hPPi : P * Pi = Pi) (hRM : R * (1 - P + Pi) = 1) {B : ℝ}
    (hB : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖P ^ n - Pi‖ ≤ B) :
    R - Pi = ∑' n : ℕ, (P ^ n - Pi) ∧ ‖R - Pi‖ ≤ B := by
  have hsn : Summable fun n : ℕ => ‖P ^ n - Pi‖ :=
    summable_of_sum_range_le (fun _ => norm_nonneg _) hB
  have hconv : Tendsto (partialSum P Pi) atTop (𝓝 (∑' n : ℕ, (P ^ n - Pi))) :=
    (Summable.of_norm hsn).hasSum.tendsto_sum_nat
  have hinv := (resolvent_inverse hPi2 hPiP hPPi hconv).1
  have hR : R = Pi + ∑' n : ℕ, (P ^ n - Pi) := by
    calc R = R * ((1 - P + Pi) * (Pi + ∑' n : ℕ, (P ^ n - Pi))) := by rw [hinv, mul_one]
      _ = (R * (1 - P + Pi)) * (Pi + ∑' n : ℕ, (P ^ n - Pi)) := by rw [mul_assoc]
      _ = Pi + ∑' n : ℕ, (P ^ n - Pi) := by rw [hRM, one_mul]
  have hU : R - Pi = ∑' n : ℕ, (P ^ n - Pi) := by rw [hR, add_sub_cancel_left]
  exact ⟨hU, hU ▸ resolvent_norm_le hconv hB⟩

/-- **`lem:doubling_operator`(3), "in particular", abstractly.** On a finite-dimensional space with
`Π² = Π`, `ΠP = PΠ = Π` and `hker` (the consequence of irreducibility the argument uses), the
diffusion operator `S = (Id − P + Π)^{-1} − Π` has `‖S‖ ≤ B` for every real `B` bounding the
partial sums of `Σ‖P^n − Π‖`. -/
theorem inverse_sub_le_of_bdd [FiniteDimensional ℝ E] (hPi2 : Pi * Pi = Pi)
    (hPiP : Pi * P = Pi) (hPPi : P * Pi = Pi) (hker : ∀ f : E, P f = f → Pi f = f) {B : ℝ}
    (hB : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖P ^ n - Pi‖ ≤ B) :
    Ring.inverse (1 - P + Pi) - Pi = ∑' n : ℕ, (P ^ n - Pi)
      ∧ ‖Ring.inverse (1 - P + Pi) - Pi‖ ≤ B := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨R, hMR, hRM⟩ := exists_inverse hPi2 hPiP hker
  have hunit : IsUnit (1 - P + Pi) := ⟨⟨_, R, hMR, hRM⟩, rfl⟩
  exact resolvent_eq_tsum_of_bdd hPi2 hPiP hPPi (Ring.inverse_mul_cancel _ hunit) hB

end Abstract

variable {S : Setting}

namespace Stat

variable {K : ℕ} (L : Stat S (some K))

/-- The partial sums of `Σ‖P⋆^n − Π‖` are those of `Σ β̂_n` (`lem:doubling_operator`(1)). -/
theorem sum_norm_pstarL2_pow_sub_piL2 (hdK : S.d ≤ K) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖L.pstarL2 (rowOnChain_some hdK) ^ n - L.piL2‖
      = ∑ n ∈ Finset.range N, L.betaHat (rowOnChain_some hdK) n :=
  Finset.sum_congr rfl fun n _ => L.norm_pstarL2_pow_sub_piL2 (rowOnChain_some hdK) n

/-- **`lem:doubling_operator`(3), "in particular", at a given inverse.** On the truncation, a left
inverse `R` of `Id − P⋆ + Π` has `‖R − Π‖ ≤ B` for every real `B` bounding the partial sums
`Σ_{n<N} β̂_n`: vacuous when `Σ β̂_n = +∞`. -/
theorem bhat_le_sum_betaHat (hdK : S.d ≤ K) {R : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu}
    (hRM : R * (1 - L.pstarL2 (rowOnChain_some hdK) + L.piL2) = 1) {B : ℝ}
    (hB : ∀ N : ℕ, ∑ n ∈ Finset.range N, L.betaHat (rowOnChain_some hdK) n ≤ B) :
    ‖R - L.piL2‖ ≤ B :=
  (resolvent_eq_tsum_of_bdd L.piL2_mul_piL2 (L.piL2_mul_pstarL2 _) (L.pstarL2_mul_piL2 _) hRM
    fun N => (L.sum_norm_pstarL2_pow_sub_piL2 hdK N).trans_le (hB N)).2

/-- **`lem:doubling_operator`(3), the finite case, at a given inverse.** When `Σ β̂_n < +∞` a left
inverse `R` of `Id − P⋆ + Π` has `R − Π = U := Σ'(P⋆^n − Π)` and `‖R − Π‖ ≤ Σ' β̂_n`. -/
theorem sub_piL2_eq_tsum (hdK : S.d ≤ K) {R : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu}
    (hRM : R * (1 - L.pstarL2 (rowOnChain_some hdK) + L.piL2) = 1)
    (hs : Summable (L.betaHat (rowOnChain_some hdK))) :
    R - L.piL2 = ∑' n : ℕ, (L.pstarL2 (rowOnChain_some hdK) ^ n - L.piL2)
      ∧ ‖R - L.piL2‖ ≤ ∑' n : ℕ, L.betaHat (rowOnChain_some hdK) n :=
  resolvent_eq_tsum_of_bdd L.piL2_mul_piL2 (L.piL2_mul_pstarL2 _) (L.pstarL2_mul_piL2 _) hRM
    fun N => (L.sum_norm_pstarL2_pow_sub_piL2 hdK N).trans_le
      (hs.sum_le_tsum _ fun n _ => (L.norm_pstarL2_pow_sub_piL2 _ n) ▸ norm_nonneg _)

/-- `Id − P⋆ + Π` is a unit on `L²(λ^K)` (`Stat.exists_diffusionOp`). -/
theorem isUnit_resolventOp (hdK : S.d ≤ K) :
    IsUnit (1 - L.pstarL2 (rowOnChain_some hdK) + L.piL2) := by
  obtain ⟨R, hMR, hRM, -⟩ := L.exists_diffusionOp (rowOnChain_some hdK)
  exact ⟨⟨_, R, hMR, hRM⟩, rfl⟩

/-- **`lem:doubling_operator`(3), "in particular": `B̂ ≤ Σ_{n≥0} β̂_n` on the truncation**, the
inequality being vacuous when its right side is `+∞`. Here `B̂ = ‖S‖` with the paper's
`S := (Id − P⋆ + Π)^{-1} − Π`, no inverse assumed, and the bound holds at every real `B` bounding
the partial sums of `Σ β̂_n`. This is also the ordering of the two constants written `B̂` that
**`rem:doubling_two_constants`** records. -/
theorem inverse_sub_piL2_le_sum_betaHat (hdK : S.d ≤ K) {B : ℝ}
    (hB : ∀ N : ℕ, ∑ n ∈ Finset.range N, L.betaHat (rowOnChain_some hdK) n ≤ B) :
    ‖Ring.inverse (1 - L.pstarL2 (rowOnChain_some hdK) + L.piL2) - L.piL2‖ ≤ B :=
  L.bhat_le_sum_betaHat hdK (Ring.inverse_mul_cancel _ (L.isUnit_resolventOp hdK)) hB

/-- **`lem:doubling_operator`(3), the finite case of "in particular": `S = U` and
`B̂ ≤ Σ β̂_n`** when `Σ β̂_n < +∞`, at the paper's `S := (Id − P⋆ + Π)^{-1} − Π`. -/
theorem inverse_sub_piL2_eq_tsum (hdK : S.d ≤ K)
    (hs : Summable (L.betaHat (rowOnChain_some hdK))) :
    Ring.inverse (1 - L.pstarL2 (rowOnChain_some hdK) + L.piL2) - L.piL2
        = ∑' n : ℕ, (L.pstarL2 (rowOnChain_some hdK) ^ n - L.piL2)
      ∧ ‖Ring.inverse (1 - L.pstarL2 (rowOnChain_some hdK) + L.piL2) - L.piL2‖
        ≤ ∑' n : ℕ, L.betaHat (rowOnChain_some hdK) n :=
  L.sub_piL2_eq_tsum hdK (Ring.inverse_mul_cancel _ (L.isUnit_resolventOp hdK)) hs

end Stat

end GFNBounds.Doubling
