import GFNBounds.Doubling.GeomFamily
import GFNBounds.Doubling.Main
import GFNBounds.Doubling.PhaseRecurrence

/-!
# The policy table of the doubling graph

Three backward policies on the infinite doubling graph, one row each, each row a single
certified statement on the loop closure:

| policy | `ε(j)` | phase | `B̂` | declaration |
|---|---|---|---|---|
| polynomial | `c/(j+1)^s`, `s ≥ 0` | (positive recurrent for `s > 1`, or `s = 1`, `c < 1`) | `+∞` | `table_polynomial` |
| uniform | `1/2` | transient, no invariant probability | — | `table_uniform` |
| geometric | `a ρ^j`, `0 < ρ < 1` | positive recurrent | `< +∞` | `table_geometric` |

The polynomial row restates `main_unbounded_two` (`theo:doubling_main`(3) at `p = 2`); the
uniform row is `phase_lt_one` and `isEmpty_stat_of_family_lt_one` at `(c, s) = (1/2, 0)`; the
geometric row is `main_geometric`.

## SCOPE (disclosed)

The table itself is not yet in the paper (requested by the author 2026-09-19). The polynomial
row carries no positive recurrence hypothesis of its own: like `main_unbounded_two` it speaks of
every invariant probability, and is vacuous where there is none.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology

variable {S : Setting}

/-- **Polynomial row.** For `ε(j) = c/(j+1)^s`, `s ≥ 0`, at every invariant probability no
bounded `S` on `L²(λ)` has `S(Id − P⋆) = Id − Π`: `B̂ = +∞`. -/
theorem table_polynomial {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (heps : ∀ j, S.eps j = epsCS c s j) (L : Stat S none) :
    ¬ ∃ Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
        Sop * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2 :=
  (main_unbounded_two hc hs heps L).1

/-- **Uniform row.** For `ε ≡ 1/2` the loop-closed backward chain is transient and carries no
invariant probability. -/
theorem table_uniform (heps : ∀ j, S.eps j = 1 / 2) :
    IsTransient S none ∧ IsEmpty (Stat S none) := by
  have h : ∀ j, S.eps j = epsCS (1 / 2) 0 j := fun j => by
    rw [heps j, epsCS, Real.rpow_zero, div_one]
  exact ⟨phase_lt_one (S := S) (by norm_num) (by norm_num) h,
    isEmpty_stat_of_family_lt_one (by norm_num) (by norm_num) S (funext h)⟩

/-- **Geometric row.** For `ε(j) = a ρ^j`, `0 < ρ < 1`, the chain is positive recurrent and, at
every invariant probability, some bounded `S` on `L²(λ)` has `S(Id − P⋆) = Id − Π`: `B̂ < +∞`. -/
theorem table_geometric {a ρ : ℝ} (ha : 0 < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (heps : ∀ j, 1 ≤ j → S.eps j = a * ρ ^ j) :
    Nonempty (Stat S none) ∧
      ∀ L : Stat S none, ∃ Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
        Sop * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2 :=
  ⟨geometric_exists_stat hρ0 hρ1 heps, geometric_diffusionOp ha hρ0 hρ1 heps⟩

end GFNBounds.Doubling
