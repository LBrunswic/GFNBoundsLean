import GFNBounds.Doubling.RayleighBridge
import GFNBounds.Doubling.Operator

/-!
# The diffusion operator is unbounded: the `p = 2` clauses

**`theo:doubling_unbounded`(2), at `p = 2`** — `app_doubling.tex:1945–2019`, and the `p = 2`
sentence of **`theo:doubling_main`(3)** — `app_doubling.tex:275–321`.

> At `p = 2` this gives `B̂ = +∞` by the convention of `def:doubling_setting`, the series
> `Σ_{n≥0}(P⋆ⁿ − Π)` does not converge in operator norm, and `Σ_{n≥0} β̂_n = +∞`.

`Unbounded.lean` proves the mass-layer inequality at every finite `p`; this file reads it at
`p = 2` on Mathlib's `Lp ℝ 2 L.mu` through `RayleighBridge.lean`, and then through the abstract
resolvent layer of `Operator.lean`:

* `no_diffusionOp` — no bounded `S` on `L²(λ)` has `S(Id − P⋆) = Id − Π`, which is the paper's
  convention `B̂ = +∞` (`def:doubling_setting`, `eq:doubling_Bhat`);
* `not_tendsto_partialSum` — the partial sums `Σ_{n<N}(P⋆ⁿ − Π)` have no limit in operator norm,
  since a limit `U` would satisfy `U(Id − P⋆) = Id − Π` (`lem:doubling_operator`(3));
* `not_summable_betaHat` — `Σ β̂_n = +∞`, since `‖P⋆ⁿ − Π‖ = β̂_n` (`lem:doubling_operator`(1)) and
  a norm-summable series converges in the complete space of operators.

## SCOPE (disclosed)

* Stated on the loop closure (`cap = none`) under the growth condition `GrowthCond S`, exactly as
  the paper's item (2); `growthCond_of_family` discharges it for the family.
* `B̂ = +∞` is not a value assigned to a constant: it is the paper's own convention, and it is
  stated as what that convention means — the non-existence of a bounded `S`.
* `Σ β̂_n = +∞` is stated as `¬ Summable`, which for a non-negative real sequence is the same
  thing.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology

namespace Stat

variable {S : Setting} (L : Stat S none)

/-- **`theo:doubling_unbounded`(2) at `p = 2`, the convention `B̂ = +∞`.** No bounded operator `S`
on `L²(λ)` satisfies `S(Id − P⋆) = Id − Π`. -/
theorem no_diffusionOp (hstar : GrowthCond S) :
    ¬ ∃ Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
      Sop * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2 := by
  rintro ⟨Sop, hS⟩
  exact L.no_bounded_inverse hstar (p := 2) (by norm_num)
    ⟨‖Sop‖ ^ 2, fun f hf hmean => L.mass_le_of_leftInverse (rowOnChain_none S) hS hf hmean⟩

/-- **`theo:doubling_unbounded`(2) at `p = 2`: the series does not converge in operator norm.**
The partial sums `Σ_{n<N}(P⋆ⁿ − Π)` have no limit in `L²(λ) →L L²(λ)`. -/
theorem not_tendsto_partialSum (hstar : GrowthCond S) :
    ¬ ∃ U : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
      Tendsto (partialSum (L.pstarL2 (rowOnChain_none S)) L.piL2) atTop (𝓝 U) := by
  rintro ⟨U, hU⟩
  obtain ⟨-, h2, -, -⟩ := resolvent_identities L.piL2_mul_piL2
    (L.piL2_mul_pstarL2 (rowOnChain_none S)) (L.pstarL2_mul_piL2 (rowOnChain_none S)) hU
  exact L.no_diffusionOp hstar ⟨U, h2⟩

/-- **`theo:doubling_unbounded`(2) at `p = 2`: `Σ β̂_n = +∞`.** The mixing coefficients
`β̂_n = ‖Pⁿ − Π‖_{L²(λ)}` are not summable. -/
theorem not_summable_betaHat (hstar : GrowthCond S) :
    ¬ Summable (L.betaHat (rowOnChain_none S)) := by
  intro hsum
  have hnorm : Summable fun n : ℕ => ‖(L.pstarL2 (rowOnChain_none S)) ^ n - L.piL2‖ :=
    hsum.congr fun n => (L.norm_pstarL2_pow_sub_piL2 (rowOnChain_none S) n).symm
  have hconv : Summable fun n : ℕ => (L.pstarL2 (rowOnChain_none S)) ^ n - L.piL2 :=
    Summable.of_norm hnorm
  exact L.not_tendsto_partialSum hstar ⟨_, hconv.hasSum.tendsto_sum_nat⟩

end Stat

end GFNBounds.Doubling
