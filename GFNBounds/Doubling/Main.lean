import GFNBounds.Doubling.Family
import GFNBounds.Doubling.Ramp
import GFNBounds.Doubling.Irreducible
import GFNBounds.Doubling.Supersolution

/-!
# The doubling graph in one statement

**`theo:doubling_main`** — `app_doubling.tex:275–321`.

This file assembles what is proved into the shape of the umbrella theorem, and says on its face
what is not. Nothing here is `sorry`; the open inputs are explicit hypotheses, so a reader can see
at a glance which items are unconditional and which are waiting on a lemma.

## The five items, and where they stand

| item | content | status |
|---|---|---|
| (1) | the phase diagram | **open** — `prop:doubling_phase`, Foster's criterion; scaffold |
| (2) | `L(m) = C m^{1−p_*}(1+o(1))/(p_*−1)` at `s=1`, `c<1` | **open** — needs `theo:doubling_sharp`; the two-sided form is `theo:doubling_decay`, conditional on `lem:doubling_product` |
| (3) | the diffusion operator, on the whole positive recurrent phase | **proved**, at every `p ∈ [1,∞]`: `main_unbounded`, `main_unbounded_infty`. The clause `σ̄ = j̄/(1−c)` is proved as the upper bound `main_sigmaBar_le`; the matching lower bound is `prop:doubling_length`, open. The `c₇√m` clause is `main_rate`, conditional on `eq:doubling_decay` |
| (4) | an unsolvable `L²` flow-matching problem | **open** — `prop:doubling_unsolvable`, needs the open mapping theorem on `L²(λ)` |
| (5) | the truncation | **partial** — irreducibility at an even cap is `main_truncation_irreducible`; `B̂_K < +∞` and `B̂_K ≥ c₈√K` are open |

Positive recurrence is a **hypothesis** throughout, carried as `Stat S none`: that is item (1),
and it is exactly what the paper's items (2)–(4) also assume ("at every `(c,s)` of the standing
range at which `X` is positive recurrent").

## SCOPE (disclosed)

The conventions of the files assembled here carry over unchanged, in particular: everything at
finite `p` is in the ℝ mass layer (`Stat.mass p f = ‖f‖_{L^p(λ)}^p`), `p = ∞` is stated against
the supremum over states, and "no bounded `S`" means no constant bounds the function by its
flow-matching defect. See `Unbounded.lean` and `Ramp.lean` for the exact readings.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting}

/-- **`theo:doubling_main`(3), the finite exponents.** At every member of the family in the
standing range, and at every positive recurrent `λ`, the flow-matching defect of the centred tail
indicators drives the `L^p(λ)` Rayleigh quotient to zero, and no constant bounds a mean-zero
function by its defect.

The growth condition `eq:doubling_star` is discharged for the family, so this is unconditional
given positive recurrence. -/
theorem main_unbounded {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (heps : ∀ j, S.eps j = epsCS c s j) (L : Stat S none) {p : ℝ} (hp : 1 ≤ p) :
    (∀ t : ℝ, 0 < t → ∃ m, S.d < m ∧
        L.mass p (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
          ≤ t * L.mass p (L.centredTail m)) ∧
      ¬ ∃ B : ℝ, ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) → (∑' x, L.lam x * f x = 0) →
          L.mass p f ≤ B * L.mass p (fun x => f x - pstar S none f x) := by
  have hstar := growthCond_of_family hc hs S heps
  exact ⟨fun t ht => L.exists_small_mass_ratio hstar hp ht, L.no_bounded_inverse hstar hp⟩

/-- **`theo:doubling_main`(3), the exponent `+∞`.** At `s ≥ 1` the family has
`γ = sup_j (j+1)ε(j) = c 2^{1−s} < ∞`, and the clipped ramps drive the `L^∞(λ)` Rayleigh quotient
to zero. -/
theorem main_unbounded_infty {c s : ℝ} (hc : 0 < c) (hs : 1 ≤ s)
    (heps : ∀ j, S.eps j = epsCS c s j) (L : Stat S none) :
    ¬ ∃ B : ℝ, ∀ (f : St → ℝ) (M Dd : ℝ),
        (∑' x, L.lam x * f x = 0) → (∃ x, M ≤ |f x|) →
        (∀ x, |f x - pstar S none f x| ≤ Dd) → M ≤ B * Dd := by
  refine L.no_bounded_inverse_infty (γ := c * 2 ^ (1 - s)) fun j hj => ?_
  rw [heps j]
  exact gamma_family hc hs j hj

/-- **`theo:doubling_main`(3), the backward-length clause, upper half.** At `s = 1` and `0 < c < 1`
the expected backward-trajectory length is at most `j̄/(1−c)`, on the loop closure and on every
truncation alike. The matching lower bound is `prop:doubling_length`, which is open. -/
theorem main_sigmaBar_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {cap : Option ℕ}
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 S.d, S.row k * hitExp S cap n (.lad k) ≤ S.jbar / (1 - c) :=
  sigmaBar_le hc0 hc1 heps n

/-- **`theo:doubling_main`(3), the `c₇√m` clause.** Conditional on `eq:doubling_decay`, which
`theo:doubling_decay` supplies once `lem:doubling_product` is proved. -/
theorem main_rate (L : Stat S none) (D : Decay) {c₁ c₂ : ℝ} (hc1 : 0 < c₁)
    (hbelow : ∀ j : ℕ, 1 ≤ j → c₁ * (j : ℝ) ^ (-D.p) ≤ L.lam (.lad j))
    (habove : ∀ j : ℕ, 1 ≤ j → L.lam (.lad j) ≤ c₂ * (j : ℝ) ^ (-D.p)) :
    ∃ m₂ : ℕ, S.d < m₂ ∧ ∀ m : ℕ, m₂ ≤ m →
      c₁ * (m : ℝ) * L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
        ≤ 4 * c₂ * (D.p - 1) * L.mass 2 (L.centredTail m) :=
  L.exists_rayleigh_family D hc1 hbelow habove

/-- **`theo:doubling_main`(5), the irreducibility clause.** The truncation at an even cap `K ≥ d`
is irreducible, and an invariant probability on it is positive at every state of it.
`B̂_K < +∞` and `B̂_K ≥ c₈√K` are open. -/
theorem main_truncation_irreducible {K : ℕ} (hK : Even K) (hdK : S.d ≤ K)
    (P : PreStat S (some K)) :
    (∀ x y : St, OnChain (some K) y → Reach S (some K) x y) ∧
      (∀ ⦃y : St⦄, OnChain (some K) y → 0 < P.lam y) :=
  ⟨fun _ _ hy => reach_all_some S hK hdK hy, fun _ hy =>
    P.pos_of_irreducible (fun _ _ hy' => reach_all_some S hK hdK hy') hy⟩

/-- **`theo:doubling_main`(1), the irreducibility clause.** The loop closure is irreducible, and
every invariant probability of it is positive at every state. The recurrence classification is
`prop:doubling_phase`, which is open. -/
theorem main_irreducible (P : PreStat S none) :
    (∀ x y : St, Reach S none x y) ∧ (∀ y : St, 0 < P.lam y) :=
  ⟨reach_all_none S, fun _ => P.pos_of_irreducible (fun _ _ _ => reach_all_none S _ _) trivial⟩

end GFNBounds.Doubling
