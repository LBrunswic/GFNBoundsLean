import GFNBounds.Doubling.Family
import GFNBounds.Doubling.Ramp
import GFNBounds.Doubling.Irreducible
import GFNBounds.Doubling.PhaseEmpty
import GFNBounds.Doubling.PhaseExists
import GFNBounds.Doubling.StatExists
import GFNBounds.Doubling.Supersolution
import GFNBounds.Doubling.Length
import GFNBounds.Doubling.SharpFull
import GFNBounds.Doubling.Unsolvable
import GFNBounds.Doubling.UnboundedL2
import GFNBounds.Doubling.OperatorL2
import GFNBounds.Doubling.TruncationStat
import GFNBounds.Doubling.Truncation
import GFNBounds.Doubling.Product
import GFNBounds.Doubling.ConstantFunctional

/-!
# The doubling graph in one statement

**`theo:doubling_main`** — `app_doubling.tex:275–321`.

This file assembles the closed results of the library into the shape of the umbrella theorem,
item by item, and says on its face what is not there. Nothing here is `sorry`; every theorem
below is a composition of certified inputs, and the one hypothesis that recurs — `L : Stat S none`,
an invariant probability of the loop closure — is the paper's own "at which `X` is positive
recurrent", supplied for rows (b) and (f) by `main_phase`.

## The five items, and where they stand

| item | content | here |
|---|---|---|
| (1) | irreducible; the phase diagram (a)–(f) | `main_irreducible`; `main_phase` — each row as the existence or non-existence of an invariant probability, row (d) inside `1 ≤ c` exactly as the paper's "not positive recurrent" |
| (2) | `L(m) = C m^{1−p_*}(1+o(1))/(p_*−1)`, `C > 0` determined by `c, d, λ_1..λ_d` | `main_invariant_measure` (the root `p_*`, the limit `C > 0`, the tail asymptotic, the rate `m^{−ϑ}`); `main_constant_determined` (the boundary data determine the whole sequence, hence `C`); `main_constant_functional` (`C = Σ_{j≤d} ν_j λ_j` with `ν_j ≥ 0`, `Σν_j > 0`, `ν_j = 0` for `2j ≤ d` — `prop:doubling_constant`) |
| (3) | the diffusion operator on the positive recurrent phase | `main_unbounded` (every finite `p`), `main_unbounded_infty` (`p = ∞`), `main_unbounded_two` (`p = 2`: no bounded `S`, the series diverges, `Σβ̂_n = +∞`), `main_sigmaBar_eq` and `main_sigmaBar_le` (`σ̄ = j̄/(1−c)`), `main_rate` (the `c₇√m` clause, unconditional) |
| (4) | an unsolvable `L²` flow-matching problem | `main_unsolvable` |
| (5) | the truncation | `main_truncation_irreducible`, `main_truncation_bhat` (a unique `λ^K`; a diffusion operator `S` with `eq:doubling_resolvent`, so `B̂_K < +∞`), `main_truncation_sqrtK` (`c₈ K ≤ ‖S‖²`, i.e. `B̂_K ≥ c₈√K`) |

## SCOPE (disclosed)

**Not stated, because the library builds no chain:** the words *transient* and *null recurrent*
in rows (a), (c), (e) — here every one of those rows reads "no invariant probability", which is
what the appendix uses them for and all it can mean for `Stat`; and the clause
`E(σ | X₀ = j) = +∞` at `1 ≤ c < 2` of `prop:doubling_phase`(3). Row (d), `c = 1/ln 2`, is stated
only as "no invariant probability", which is exactly the paper's claim there.

**Not stated, for other reasons:** the state count `K + 2` of the truncation (`St` is infinite,
the chain is `OnChain (some K)`); the dependence clauses "`c₇` depends only on `c, d,
λ_1..λ_{2m₀}`" and "`c₆` on `c, d, λ_1..λ_{2m₀}`" are not carried by the existential statements
here — they are carried, as formulas in `c`, `d` and the initial block of the profile, by
`Decay.decay_two_sided_explicit` (`Product.lean`) and `Decay.sharp_explicit` (`SharpFull.lean`),
of which the `∃` forms used in this file are the paper-shaped readings; and in
`main_truncation_sqrtK` the constant `c₈` depends on `c`, `d`, `j̄` and on the `Setting`'s bound
`ε_max` (for the family `ε_max = c/2`, so this is `c, d, j̄` as the paper says).

**Conventions.** Everything at finite `p` is in the ℝ mass layer (`Stat.mass p f =
‖f‖_{L^p(λ)}^p`); `p = ∞` is stated over bounded `f` against the supremum over states; the `L²`
operator statements are on Mathlib's `Lp ℝ 2 L.mu` with `P⋆ = Stat.pstarL2`, `Π = Stat.piL2`,
`β̂_n = Stat.betaHat`; `σ̄` is `⨆ₙ sbar S none n` with `hitExp` the paper's recursion for
`E(σ ∧ n | X₀ = ·)`; the invariant probability of the truncation is any `Stat S (some K)`, which
`main_truncation_bhat` shows unique. The `√K` bound is squared, `c₈ K ≤ ‖S‖²`, and `K₀` does not
require evenness (weaker than the paper). The Cramér root `p_*` enters through `Decay.ofC`, the
unique non-zero root at `0 < c < 1` (`lem:doubling_cramer_root`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology MeasureTheory

variable {S : Setting}

/-! ### The Cramér root as a `Decay` -/

/-- `c ln 2 < 1` on `0 < c < 1`, since `ln 2 < 1`. -/
theorem c_mul_log_two_lt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : c * Real.log 2 < 1 := by
  have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- **`p_*(c)` packaged.** At `0 < c < 1` the Cramér equation `c(2^p − 1) = p` has a non-zero real
root (`lem:doubling_cramer_root`, since `c ≠ 1/ln 2`); this is the `Decay` carrying it. -/
noncomputable def Decay.ofC {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : Decay where
  c := c
  p := (cramer_root_exists hc0 (ne_of_lt (c_mul_log_two_lt_one hc0 hc1))).choose
  c_pos := hc0
  c_lt_one := hc1
  p_ne := (cramer_root_exists hc0 (ne_of_lt (c_mul_log_two_lt_one hc0 hc1))).choose_spec.1
  root := (cramer_root_exists hc0 (ne_of_lt (c_mul_log_two_lt_one hc0 hc1))).choose_spec.2.1

@[simp] theorem Decay.ofC_c {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : (Decay.ofC hc0 hc1).c = c := rfl

/-- The family at `s = 1` is `c/(j+1)`. -/
theorem epsCS_one_apply (c : ℝ) (j : ℕ) : epsCS c 1 j = c / ((j : ℝ) + 1) := by
  rw [epsCS, Real.rpow_one]

/-- A `Setting` carrying the family at `s = 1` carries the `ε` of any `Decay` with that `c`. -/
theorem eps_eq_decay_eps {c : ℝ} (heps : ∀ j, S.eps j = epsCS c 1 j) (D : Decay) (hDc : D.c = c)
    (j : ℕ) : S.eps j = D.eps j := by
  rw [heps j, epsCS_one_apply, Decay.eps, hDc]

/-! ### Item (1): irreducibility and the phase diagram -/

/-- **`theo:doubling_main`(1), the irreducibility clause.** The loop closure is irreducible, and
every invariant probability of it is positive at every state. -/
theorem main_irreducible (P : PreStat S none) :
    (∀ x y : St, Reach S none x y) ∧ (∀ y : St, 0 < P.lam y) :=
  ⟨reach_all_none S, fun _ => P.pos_of_irreducible (fun _ _ _ => reach_all_none S _ _) trivial⟩

/-- **`theo:doubling_main`(1), the phase diagram**, each row as the existence or non-existence of
an invariant probability of the loop closure: (a) `s < 1`, none; (b) `s = 1`, `0 < c < 1`, one;
(c)–(e) `s = 1`, `1 ≤ c`, none — row (d), `c = 1/ln 2`, included, exactly as the paper's "not
positive recurrent"; (f) `s > 1`, one. The standing range `c < 2^s` is carried by the `Setting`.
The labels *transient* / *null recurrent* are not stated: see the SCOPE above. -/
theorem main_phase {c s : ℝ} (hc : 0 < c) (heps : ∀ j, S.eps j = epsCS c s j) :
    (s < 1 → IsEmpty (Stat S none)) ∧
      (s = 1 → c < 1 → Nonempty (Stat S none)) ∧
      (s = 1 → 1 ≤ c → IsEmpty (Stat S none)) ∧
      (1 < s → Nonempty (Stat S none)) := by
  have hS : S.eps = epsCS c s := funext heps
  refine ⟨fun hs => isEmpty_stat_of_family_lt_one hc hs S hS, fun hs hc1 => ?_,
    fun hs hc1 => ?_, fun hs => exists_stat_of_family_gt_one hc hs S hS⟩
  · subst hs; exact exists_stat_of_family hc hc1 S hS
  · subst hs; exact isEmpty_stat_of_family_ge_one hc1 S hS

/-! ### Item (2): the invariant measure at `s = 1` -/

/-- **`theo:doubling_main`(2).** At `s = 1`, `0 < c < 1`, with `p_* > 1` the root of the Cramér
equation and `λ` an invariant probability: there is `C > 0` with `λ_m m^{p_*} → C`, the tail obeys
`(p_*−1) m^{p_*−1} L(m) → C` — that is `L(m) = C m^{1−p_*}(1+o(1))/(p_*−1)` — and the convergence
carries a polynomial rate `|λ_m m^{p_*} − C| ≤ c₆ m^{−ϑ}` with `ϑ ∈ (0,1)`. -/
theorem main_invariant_measure {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) (L : Stat S none) :
    ∃ p : ℝ, psi c p = 0 ∧ 1 < p ∧ ∃ C : ℝ, 0 < C ∧
      Tendsto (fun m : ℕ => L.lam (.lad m) * (m : ℝ) ^ p) atTop (𝓝 C) ∧
      Tendsto (fun m : ℕ => (p - 1) * (m : ℝ) ^ (p - 1) * L.tailMass m) atTop (𝓝 C) ∧
      ∃ ϑ c₆ : ℝ, 0 < ϑ ∧ ϑ < 1 ∧ 0 < c₆ ∧
        ∀ m : ℕ, 1 ≤ m → |L.lam (.lad m) * (m : ℝ) ^ p - C| ≤ c₆ * (m : ℝ) ^ (-ϑ) := by
  obtain ⟨D, hDc⟩ : ∃ D : Decay, D.c = c := ⟨Decay.ofC hc0 hc1, rfl⟩
  have hcut : D.CutBal S.d (fun j => L.lam (.lad j)) ⊤ :=
    D.cutBal_of_setting (eps_eq_decay_eps heps D hDc) (cutBalanceSeq_of_stat L)
  have hpos : ∀ j : ℕ, 1 ≤ j → 0 < L.lam (.lad j) := fun _ _ => L.pos trivial
  obtain ⟨C, c₁, c₂, c₆, hc₁, hC1, hC2, hc₆, -, hlim, hrate⟩ := D.sharp_of_cutBal hcut hpos
  have hroot : psi c D.p = 0 := by rw [← hDc]; exact D.root
  refine ⟨D.p, hroot, D.p_gt_one, C, lt_of_lt_of_le hc₁ hC1, hlim, ?_,
    D.vartheta, c₆, D.vartheta_pos, D.vartheta_lt_one, hc₆, hrate⟩
  refine (D.tendsto_tail_sharp L.summable_lad hlim).congr fun m => ?_
  rw [L.tailSeq_eq_tailMass]

/-- **`theo:doubling_main`(2), "determined by `c`, `d` and `λ_1, …, λ_d`".** Two invariant
probabilities of loop closures with the same `c` and `d` that agree on `λ_1, …, λ_d` agree on the
whole ladder — so the constant `C` of `main_invariant_measure`, a limit along that ladder, is
determined by `c`, `d` and the boundary data. -/
theorem main_constant_determined {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) (L L' : Stat S none)
    (hagree : ∀ j : ℕ, 1 ≤ j → j ≤ S.d → L.lam (.lad j) = L'.lam (.lad j)) :
    ∀ m : ℕ, 1 ≤ m → L.lam (.lad m) = L'.lam (.lad m) := by
  obtain ⟨D, hDc⟩ : ∃ D : Decay, D.c = c := ⟨Decay.ofC hc0 hc1, rfl⟩
  exact D.cutBal_unique
    (D.cutBal_of_setting (eps_eq_decay_eps heps D hDc) (cutBalanceSeq_of_stat L))
    (D.cutBal_of_setting (eps_eq_decay_eps heps D hDc) (cutBalanceSeq_of_stat L')) hagree

/-- **`theo:doubling_main`(2), "determined by `c`, `d` and `λ_1, …, λ_d`", in the form of
`prop:doubling_constant`.** There are coefficients `ν_1, …, ν_d ≥ 0`, depending on `c` and `d`
alone, with `Σ ν_j > 0` and `ν_j = 0` for `2j ≤ d`, such that for every invariant probability `λ`
of the loop closure the constant of `main_invariant_measure` is `C = Σ_{j≤d} ν_j λ_j`. -/
theorem main_constant_functional {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) :
    ∃ p : ℝ, psi c p = 0 ∧ 1 < p ∧ ∃ ν : ℕ → ℝ, (∀ j, 0 ≤ ν j) ∧
      0 < ∑ j ∈ Finset.Icc 1 S.d, ν j ∧ (∀ j, 1 ≤ j → 2 * j ≤ S.d → ν j = 0) ∧
      ∀ L : Stat S none,
        Tendsto (fun m : ℕ => L.lam (.lad m) * (m : ℝ) ^ p) atTop
          (𝓝 (∑ j ∈ Finset.Icc 1 S.d, ν j * L.lam (.lad j))) := by
  obtain ⟨D, hDc⟩ : ∃ D : Decay, D.c = c := ⟨Decay.ofC hc0 hc1, rfl⟩
  have hroot : psi c D.p = 0 := by rw [← hDc]; exact D.root
  obtain ⟨ν, hν0, hνsum, hνzero, hlim⟩ := D.constant_functional S.d_pos
  refine ⟨D.p, hroot, D.p_gt_one, ν, hν0, hνsum, hνzero, fun L => ?_⟩
  exact hlim (fun j => L.lam (.lad j))
    (D.cutBal_of_setting (eps_eq_decay_eps heps D hDc) (cutBalanceSeq_of_stat L))
    (fun _ _ => L.pos trivial)

/-! ### Item (3): the diffusion operator on the whole positive recurrent phase -/

/-- **`theo:doubling_main`(3), the finite exponents.** At every member of the family in the
standing range, and at every positive recurrent `λ`, the flow-matching defect of the centred tail
indicators drives the `L^p(λ)` Rayleigh quotient to zero, and no constant bounds a bounded
mean-zero function by its defect.

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

/-- **`theo:doubling_main`(3), the exponent `+∞`.** At every member of the family and every
positive recurrent `λ`, no constant bounds the attained `L^∞` size of a bounded mean-zero function
by the uniform size of its flow-matching defect. At `s ≥ 1` the family has
`γ = sup_j (j+1)ε(j) = c 2^{1−s} < ∞` and the clipped ramps do the work (`lem:doubling_ramp`); at
`s < 1` no invariant probability exists (`prop:doubling_phase`, row (a)), so the clause holds
vacuously — the paper's item (3) ranges over the positive recurrent members, and so does this. No
hypothesis on `s` is needed. -/
theorem main_unbounded_infty {c s : ℝ} (hc : 0 < c)
    (heps : ∀ j, S.eps j = epsCS c s j) (L : Stat S none) :
    ¬ ∃ B : ℝ, ∀ (f : St → ℝ) (M Dd : ℝ),
        (∃ C, ∀ x, |f x| ≤ C) → (∑' x, L.lam x * f x = 0) → (∃ x, M ≤ |f x|) →
        (∀ x, |f x - pstar S none f x| ≤ Dd) → M ≤ B * Dd := by
  by_cases hs1 : 1 ≤ s
  · refine L.no_bounded_inverse_infty (γ := c * 2 ^ (1 - s)) fun j hj => ?_
    rw [heps j]
    exact gamma_family hc hs1 j hj
  · exact (isEmpty_stat_of_family_lt_one hc (not_le.mp hs1) S (funext heps)).elim L

/-- **`theo:doubling_main`(3), the `p = 2` sentence.** On `L²(λ)`: no bounded `S` satisfies
`S(Id − P⋆) = Id − Π` — the convention `B̂ = +∞` of `def:doubling_setting` — the series
`Σ_{n≥0}(P⋆ⁿ − Π)` does not converge in operator norm, and `Σ_{n≥0} β̂_n = +∞`. -/
theorem main_unbounded_two {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (heps : ∀ j, S.eps j = epsCS c s j) (L : Stat S none) :
    (¬ ∃ Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
        Sop * (1 - L.pstarL2 (rowOnChain_none S)) = 1 - L.piL2) ∧
      (¬ ∃ U : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
        Tendsto (partialSum (L.pstarL2 (rowOnChain_none S)) L.piL2) atTop (𝓝 U)) ∧
      ¬ Summable (L.betaHat (rowOnChain_none S)) := by
  have hstar := growthCond_of_family hc hs S heps
  exact ⟨L.no_diffusionOp hstar, L.not_tendsto_partialSum hstar, L.not_summable_betaHat hstar⟩

/-- **`theo:doubling_main`(3), the backward-length clause.** At `s = 1` and `0 < c < 1` the
expected backward-trajectory length of the loop closure is `σ̄ = j̄/(1−c)`
(`prop:doubling_length`). -/
theorem main_sigmaBar_eq {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) :
    ⨆ n, sbar S none n = S.jbar / (1 - c) :=
  sbar_iSup_eq hc0 hc1 fun j _ => by rw [heps j, epsCS_one_apply]

/-- **`theo:doubling_main`(3), the backward-length clause, on every truncation as well.** The
truncated expectations `σ̄⁽ⁿ⁾_K` are bounded by `j̄/(1−c)` uniformly in `n` and `K`
(`lem:doubling_supersolution`). -/
theorem main_sigmaBar_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {cap : Option ℕ}
    (heps : ∀ j, S.eps j = epsCS c 1 j) (n : ℕ) :
    sbar S cap n ≤ S.jbar / (1 - c) :=
  sigmaBar_le hc0 hc1 (fun j _ => by rw [heps j, epsCS_one_apply]) n

/-- **`theo:doubling_main`(3), the `c₇√m` clause, unconditional.** At `s = 1`, `0 < c < 1`, with
`p_*` the Cramér root and `λ` an invariant probability, there are `0 < c₁ ≤ c₂` and `m₂ > d` with
`c₁ m ‖(Id−P⋆)f_m‖² ≤ 4c₂(p_*−1) ‖f_m‖²` for every `m ≥ m₂`, i.e. `eq:doubling_explicit` with
`c₇ = ½√(c₁/(c₂(p_*−1)))`. The two-sided decay `eq:doubling_decay` is now supplied by
`theo:doubling_decay`, so nothing is conditional. -/
theorem main_rate {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) (L : Stat S none) :
    ∃ p : ℝ, psi c p = 0 ∧ 1 < p ∧ ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∃ m₂ : ℕ, S.d < m₂ ∧ ∀ m : ℕ, m₂ ≤ m →
        c₁ * (m : ℝ) * L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
          ≤ 4 * c₂ * (p - 1) * L.mass 2 (L.centredTail m) := by
  obtain ⟨D, hDc⟩ : ∃ D : Decay, D.c = c := ⟨Decay.ofC hc0 hc1, rfl⟩
  have hcut : D.CutBal S.d (fun j => L.lam (.lad j)) ⊤ :=
    D.cutBal_of_setting (eps_eq_decay_eps heps D hDc) (cutBalanceSeq_of_stat L)
  have hpos : ∀ j : ℕ, 1 ≤ j → 0 < L.lam (.lad j) := fun _ _ => L.pos trivial
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hbd⟩ := D.decay_two_sided_of_cutBal hcut hpos (le_refl (D.m0 S.d))
  have hroot : psi c D.p = 0 := by rw [← hDc]; exact D.root
  exact ⟨D.p, hroot, D.p_gt_one, c₁, c₂, hc₁, hc₁₂,
    L.exists_rayleigh_family D hc₁ (fun j hj => (hbd j hj).1) (fun j hj => (hbd j hj).2)⟩

/-! ### Item (4): an unsolvable flow-matching problem -/

/-- **`theo:doubling_main`(4).** At every member of the family in the standing range and every
positive recurrent `λ`: `(Id − P⋆)L²(λ)` is a dense proper subspace of `ker Π`, and there are
probability densities `f_init, f_term ∈ L²(λ)` such that no `f ∈ L²(λ)` satisfies the
flow-matching equation `(Id − P⋆)f = f_init − f_term` (`prop:doubling_unsolvable`). -/
theorem main_unsolvable {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (heps : ∀ j, S.eps j = epsCS c s j) (L : Stat S none) :
    (L.defectRange ≤ L.kerPi ∧ L.defectRange.topologicalClosure = L.kerPi ∧
        L.defectRange ≠ L.kerPi) ∧
      ∃ fi fe : St → ℝ,
        (∀ x, 0 ≤ fi x) ∧ (∀ x, 0 ≤ fe x) ∧
        MemLp fi 2 L.mu ∧ MemLp fe 2 L.mu ∧
        ∑' x, L.lam x * fi x = 1 ∧ ∑' x, L.lam x * fe x = 1 ∧
        ¬ ∃ f : St → ℝ, MemLp f 2 L.mu ∧
            ∀ᵐ x ∂L.mu, f x - pstar S none f x = fi x - fe x :=
  doubling_unsolvable L (growthCond_of_family hc hs S heps)

/-! ### Item (5): the truncation -/

/-- **`theo:doubling_main`(5), the irreducibility clause.** The truncation at an even cap `K ≥ d`
is irreducible, and an invariant probability on it is positive at every state of it. -/
theorem main_truncation_irreducible {K : ℕ} (hK : Even K) (hdK : S.d ≤ K)
    (P : PreStat S (some K)) :
    (∀ x y : St, OnChain (some K) y → Reach S (some K) x y) ∧
      (∀ ⦃y : St⦄, OnChain (some K) y → 0 < P.lam y) :=
  ⟨fun _ _ hy => reach_all_some S hK hdK hy, fun _ hy =>
    P.pos_of_irreducible (fun _ _ hy' => reach_all_some S hK hdK hy') hy⟩

/-- **`theo:doubling_main`(5), `λ^K` and `B̂_K < +∞`.** At an even cap `K ≥ d` the truncation
carries exactly one invariant probability, and on `L²(λ^K)` there is a diffusion operator `S`
satisfying `eq:doubling_resolvent` — a bounded operator, so `B̂_K = ‖S‖ < +∞`
(`lem:doubling_truncation_irreducible`). -/
theorem main_truncation_bhat {K : ℕ} (hK : Even K) (hdK : S.d ≤ K) :
    Nonempty (Stat S (some K)) ∧
      (∀ L L' : Stat S (some K), L.lam = L'.lam) ∧
      ∀ L : Stat S (some K), ∃ Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu,
        (1 - L.pstarL2 (rowOnChain_some hdK)) * Sop = 1 - L.piL2 ∧
        Sop * (1 - L.pstarL2 (rowOnChain_some hdK)) = 1 - L.piL2 ∧
        L.piL2 * Sop = 0 ∧ Sop * L.piL2 = 0 :=
  ⟨exists_stat hK hdK, stat_unique hK hdK, fun L => by
    obtain ⟨Sop, h1, h2, h3, h4, -⟩ := L.exists_bhat (rowOnChain_some hdK)
    exact ⟨Sop, h1, h2, h3, h4⟩⟩

/-- **`theo:doubling_main`(5), the proved `√K`, squared.** At `s = 1`, `0 < c < 1`, there are
`c₈ > 0` and `K₀` — depending on `c`, `d`, `j̄` and the `Setting`'s `ε_max` — such that for every
`K ≥ K₀`, every invariant probability `λ^K` of the truncation and every bounded `S` on `L²(λ^K)`
with `S(Id − P⋆) = Id − Π`, `c₈ K ≤ ‖S‖²`; read at the `S` of `main_truncation_bhat` this is
`B̂_K ≥ √c₈ · √K` (`cor:doubling_truncation`(3)). -/
theorem main_truncation_sqrtK {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) :
    ∃ c₈ : ℝ, 0 < c₈ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ (L : Stat S (some K)) (hrow : RowOnChain S (some K))
        (Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu),
        Sop * (1 - L.pstarL2 hrow) = 1 - L.piL2 → c₈ * (K : ℝ) ≤ ‖Sop‖ ^ 2 := by
  obtain ⟨D, hDc⟩ : ∃ D : Decay, D.c = c := ⟨Decay.ofC hc0 hc1, rfl⟩
  have hDeps : ∀ j, S.eps j = D.eps j := eps_eq_decay_eps heps D hDc
  have heps' : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1) :=
    fun j _ => by rw [heps j, epsCS_one_apply]
  -- the level of `theo:doubling_decay`, and the descent-weight window at that level
  set ℓ : ℕ := D.m0 S.d with hℓdef
  have hℓd : S.d < ℓ := D.lt_m0 S.d
  have hℓ1 : 1 ≤ ℓ := by have := S.d_pos; omega
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (show 0 < ℓ by omega)
  set Z₁ : ℝ := Real.exp (-(D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ))) with hZ₁def
  set Z₂ : ℝ := Real.exp (D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)) with hZ₂def
  have hZ1 : 0 < Z₁ := Real.exp_pos _
  have hZ2 : 0 < Z₂ := Real.exp_pos _
  have hZlo : ∀ y : ℕ, ℓ ≤ y → Z₁ ≤ D.descOne ℓ y :=
    fun y _ => (D.descOne_two_sided (d := S.d) (le_refl ℓ) y).1
  have hZhi : ∀ y : ℕ, ℓ ≤ y → D.descOne ℓ y ≤ Z₂ :=
    fun y _ => (D.descOne_two_sided (d := S.d) (le_refl ℓ) y).2
  -- the `K`-free constants
  have hem : 0 < 1 - S.epsMax := by have := S.epsMax_lt_one; linarith
  have hQpos : 0 < ((1 - S.epsMax)⁻¹) ^ ℓ + ((D.c / (2 * (ℓ : ℝ) + 1)) ^ ℓ)⁻¹ :=
    add_pos (pow_pos (inv_pos.mpr hem) _)
      (inv_pos.mpr (pow_pos (div_pos D.c_pos (by positivity)) _))
  set c₉ : ℝ := Z₂ / Z₁ * (2 : ℝ) ^ D.p
      * (((1 - S.epsMax)⁻¹) ^ ℓ + ((D.c / (2 * (ℓ : ℝ) + 1)) ^ ℓ)⁻¹) ^ 2 with hc₉def
  have hc₉ : 0 < c₉ :=
    mul_pos (mul_pos (div_pos hZ2 hZ1) (rpow_pos_of_pos two_pos _)) (pow_pos hQpos 2)
  have hjb : 0 ≤ S.jbar :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (S.row_nonneg k)
  set X : ℝ := (2 : ℝ) ^ D.p * 16 * (2 + S.jbar / (1 - c)) with hXdef
  have hX : 0 < X := by
    have h1 : 0 ≤ S.jbar / (1 - c) := div_nonneg hjb (by linarith)
    exact mul_pos (mul_pos (rpow_pos_of_pos two_pos _) (by norm_num)) (by linarith)
  refine ⟨1 / (c₉ * X), by positivity, max (4 * ℓ) 8, fun K hK L hrow Sop hS => ?_⟩
  have h4ℓK : 4 * ℓ ≤ K := le_trans (le_max_left _ _) hK
  have hK8 : 8 ≤ K := le_trans (le_max_right _ _) hK
  have hKd : 4 * (S.d + 1) ≤ K := by omega
  -- item (2) of `cor:doubling_truncation` at this level
  obtain ⟨Cm, Cp, hCm, hCp, hbds⟩ :=
    Stat.decayK D L hDeps hℓd hℓ1 h4ℓK hZ1 hZ2 hZlo hZhi
  have hlo : ∀ j : ℕ, K / 4 ≤ j → j ≤ 2 * (K / 4) →
      Cm * (j : ℝ) ^ (-D.p) ≤ L.lam (.lad j) :=
    fun j hj1 hj2 => (hbds j (by omega) (by omega)).1
  have hhi : L.lam (.lad (K / 4)) ≤ Cp * ((K / 4 : ℕ) : ℝ) ^ (-D.p) :=
    (hbds (K / 4) (by omega) (by omega)).2
  -- `Cp > 0`, read off the sandwich at the level itself
  have hCp0 : 0 < Cp := by
    have hx : (0 : ℝ) < (ℓ : ℝ) ^ (-D.p) := rpow_pos_of_pos hℓpos _
    obtain ⟨h1, h2⟩ := hbds ℓ le_rfl (by omega)
    exact (mul_pos_iff_of_pos_right hx).mp (lt_of_lt_of_le (mul_pos hCm hx) (le_trans h1 h2))
  -- the bridge: `‖S‖²` bounds the `L²(λ^K)` Rayleigh quotient in the mass layer
  have hB : ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) → (∑' x, L.lam x * f x = 0) →
      L.mass 2 f ≤ ‖Sop‖ ^ 2 * L.mass 2 (fun x => f x - pstar S (some K) f x) :=
    fun f hf hmean => L.mass_le_of_leftInverse hrow hS hf hmean
  have hsq := L.sqrtK D hc0 hc1 heps' hCm hKd hK8 hlo hhi hB
  -- assemble: `1/(c₉ X) ≤ Cm/(Cp X)` because `Cp ≤ c₉ Cm`
  have hden : Cp * (2 : ℝ) ^ D.p * 16 * (2 + S.jbar / (1 - c)) = Cp * X := by
    rw [hXdef]; ring
  rw [hden] at hsq
  have hle : 1 / (c₉ * X) ≤ Cm / (Cp * X) := by
    rw [div_le_div_iff₀ (mul_pos hc₉ hX) (mul_pos hCp0 hX)]
    have : Cp * X ≤ c₉ * Cm * X := mul_le_mul_of_nonneg_right hCp hX.le
    nlinarith
  calc 1 / (c₉ * X) * (K : ℝ) ≤ Cm / (Cp * X) * (K : ℝ) :=
        mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg K)
    _ ≤ ‖Sop‖ ^ 2 := hsq

end GFNBounds.Doubling
