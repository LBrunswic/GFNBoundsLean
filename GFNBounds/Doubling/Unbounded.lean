import GFNBounds.Doubling.PerCutNorms
import GFNBounds.Doubling.Ratios
import GFNBounds.Doubling.Range

/-!
# The diffusion operator is unbounded

**`theo:doubling_unbounded`** — `app_doubling.tex:1945–2019`.

> Let the backward policy be `eq:doubling_policy` with `ε(j) > 0` and `ε_max < 1`, and consider
> the growth condition
> `(★)  Σ_{i<D} log(1/ε(2^i)) = o(2^D)   (D → ∞)`.
> Then (1) at `ε = ε_{c,s}` with `s ≥ 0` and `0 < c < 2^s` the left side is `O(D²)` and (★) holds;
> (2) if the loop-closed chain is positive recurrent with invariant probability `λ` and (★) holds,
> then for every `p ∈ [1,∞)` the infimum `eq:doubling_inf` is `0` and no bounded operator `S` on
> `L^p(λ)` satisfies `S(Id − P⋆) = Id − Π`.

The two steps of the paper's proof are `Stat.exists_tailRatio_gt` — the ratio `L(m)/λ_m` is
unbounded, by an exponentially decaying tail against (★) — and `Stat.exists_small_mass_ratio`,
the infimum along the centred tail indicators, which consumes `lem:doubling_percut` through
`Stat.mass_defect_le` and `Stat.mass_centredTail_ge`.

## SCOPE (disclosed)

* Everything is in the **`ℝ` mass layer**: `Stat.mass p f = ∑' |f|^p λ` is `‖f‖_{L^p(λ)}^p`, not
  an `eLpNorm`. `eq:doubling_inf` becomes "for every `t > 0` some `f_m` has
  `mass p ((Id−P⋆)f_m) ≤ t · mass p f_m`", which is the same statement raised to the power `p`,
  and the mean-zero condition `Π f = 0` is `∑' λ·f = 0` (`Stat.tsum_centredTail`).
* "No bounded operator `S` on `L^p(λ)` satisfies `S(Id−P⋆) = Id−Π`" is stated as
  `Stat.no_bounded_inverse`: no real `B` bounds `mass p f ≤ B · mass p ((Id−P⋆)f)` over the
  bounded mean-zero `f`. That is the inequality the paper's Step 3 actually uses, and it is what
  makes the conclusion independent of the `Lp` layer.
* The `p = 2` clauses about `Σ β̂_n` need `lem:doubling_operator`, which is not formalized; they
  are **not** here.
* The chain here is the loop closure (`cap = none`), as in the paper.

## Hypothesis checklist against `theo:doubling_unbounded`

| paper hypothesis | here |
|---|---|
| `ε(j) > 0` for `j ≥ 1` | ✓ carried by `Setting` |
| `ε_max = sup ε < 1` | ✓ carried by `Setting` |
| (★) | ✓ carried as `GrowthCond` |
| positive recurrence, `λ` its invariant probability | ✓ carried as `Stat S none` |
| `p ∈ [1,∞)` | ✓ carried (`hp : 1 ≤ p`, `p` real) |
| `s ≥ 0`, `0 < c < 2^s` in item (1) | ✓ carried |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting}

/-! ## The tail of the invariant probability on the loop closure -/

namespace Stat

variable (L : Stat S none)

/-- The tail mass is the tail of a summable series over the ladder. -/
theorem hasSum_tailShift (m : ℕ) :
    HasSum (fun k : ℕ => L.lam (.lad (k + m))) (L.tailMass m) := by
  have hinj : Function.Injective (fun k : ℕ => (St.lad (k + m) : St)) := by
    intro a b hab
    simp only [St.lad.injEq] at hab
    omega
  have hz : ∀ x : St, x ∉ Set.range (fun k : ℕ => (St.lad (k + m) : St)) →
      L.lam x * tailInd none m x = 0 := by
    intro x hx
    rcases x with j | _
    · have hjm : j < m := by
        by_contra hc
        refine hx ⟨j - m, ?_⟩
        have hjj : j - m + m = j := by omega
        simp only [hjj]
      rw [tailInd_zero (not_inTail_of_lt hjm), mul_zero]
    · simp
  have h := (hinj.hasSum_iff hz).mpr (L.hasSum_tailMass m)
  have heq : ((fun x => L.lam x * tailInd none m x) ∘ fun k : ℕ => (St.lad (k + m) : St))
      = fun k : ℕ => L.lam (.lad (k + m)) := by
    funext k
    simp only [Function.comp_apply]
    rw [tailInd_one (show inTail none m (k + m) from Nat.le_add_left m k), mul_one]
  rwa [heq] at h

theorem summable_lad : Summable (fun j : ℕ => L.lam (.lad j)) := by
  have hinj : Function.Injective (fun j : ℕ => (St.lad j : St)) := by
    intro a b hab; simpa using hab
  exact L.summable.comp_injective hinj

/-- `λ_m = L(m) − L(m+1)`: the cut carries exactly the difference of two tails. -/
theorem tailMass_succ (m : ℕ) : L.tailMass m = L.lam (.lad m) + L.tailMass (m + 1) := by
  have h0 := L.hasSum_tailShift m
  have h1 : HasSum (fun n : ℕ => L.lam (.lad (n + 1 + m))) (L.tailMass (m + 1)) := by
    have h := L.hasSum_tailShift (m + 1)
    have he : (fun k : ℕ => L.lam (.lad (k + (m + 1))))
        = fun n : ℕ => L.lam (St.lad (n + 1 + m)) := by
      funext n; congr 2; omega
    rwa [he] at h
  have h2 := (hasSum_nat_add_iff (f := fun k : ℕ => L.lam (St.lad (k + m))) 1).mp h1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.zero_add] at h2
  have h3 := h0.unique h2
  rw [h3]; ring

/-- The tail vanishes: `L(m) → 0`. -/
theorem tailMass_tendsto_zero : Tendsto L.tailMass atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (fun j : ℕ => L.lam (St.lad j))
  have heq : (fun i : ℕ => ∑' k : ℕ, L.lam (St.lad (k + i))) = L.tailMass := by
    funext i; exact (L.hasSum_tailShift i).tsum_eq
  rwa [heq] at h

theorem tailMass_pos (m : ℕ) : 0 < L.tailMass m :=
  lt_of_lt_of_le (L.pos (x := St.lad m) trivial)
    (L.lam_le_tailMass (inTail_of le_rfl trivial))

/-- `1 − L(m) ≥ λ_1 > 0` for `m > 1`: the state `1` is outside the tail. -/
theorem coTail_pos {m : ℕ} (hm : 1 < m) : 0 < 1 - L.tailMass m :=
  lt_of_lt_of_le (L.pos (x := St.lad 1) trivial) (L.lam_one_le_coTailMass hm)

end Stat

/-! ## The growth condition (★) -/

/-- **`eq:doubling_star`.** `Σ_{i<D} log(1/ε(2^i)) = o(2^D)`. -/
def GrowthCond (S : Setting) : Prop :=
  Tendsto (fun D : ℕ => (∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))) / 2 ^ D)
    atTop (𝓝 0)

/-! ## Step 1: the ratio `L(m)/λ_m` is unbounded -/

namespace Stat

variable (L : Stat S none)

/-- `λ_{2^D} ≥ λ_1 · ∏_{i<D} ε(2^i)`: iterate `eq:doubling_ratios` along the powers of two. -/
theorem lam_pow_two_ge (D : ℕ) :
    L.lam (.lad 1) * ∏ i ∈ Finset.range D, S.eps (2 ^ i) ≤ L.lam (.lad (2 ^ D)) := by
  induction D with
  | zero => simp
  | succ D ih =>
      have hpow : (1 : ℕ) ≤ 2 ^ D := Nat.one_le_two_pow
      have hstep : L.lam (.lad (2 ^ D)) * S.eps (2 ^ D) ≤ L.lam (.lad (2 * 2 ^ D)) :=
        L.lam_double_ge hpow trivial
      have hpow2 : 2 * 2 ^ D = 2 ^ (D + 1) := by ring
      rw [hpow2] at hstep
      refine le_trans ?_ hstep
      rw [Finset.prod_range_succ, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right ih (S.eps_pos hpow).le

/-- **Step 1 of `theo:doubling_unbounded`(2).** Under (★) the ratio `L(m)/λ_m` is unbounded above
*every* cut: an exponentially decaying tail would force `Σ_{i<D} log(1/ε(2^i))` to grow like `2^D`,
which (★) forbids.

The start `m₁` is a parameter, which is the paper's "dropping finitely many cuts from the supremum
leaves it infinite" — proved rather than asserted.

⚠ weakened hypothesis: no relation between `m₁` and `d` is needed. The paper's supremum runs over
`m > d`; the decay argument never uses that, because the geometric bound starts at `m₁` and the
lower bound `λ_{2^D} ≥ λ_1 ∏ ε(2^i)` starts at `1`. -/
theorem exists_tailRatio_gt (hstar : GrowthCond S) (Q : ℝ) (m₁ : ℕ) :
    ∃ m, m₁ ≤ m ∧ Q * L.lam (.lad m) < L.tailMass m := by
  by_contra hcon
  have hbd : ∀ m, m₁ ≤ m → L.tailMass m ≤ Q * L.lam (.lad m) := by
    intro m hm
    by_contra h2
    exact hcon ⟨m, hm, lt_of_not_ge h2⟩
  set Q' : ℝ := max Q 2 with hQ'
  have hQ2 : (2 : ℝ) ≤ Q' := le_max_right _ _
  have hQpos : (0 : ℝ) < Q' := by linarith
  have hbd' : ∀ m, m₁ ≤ m → L.tailMass m ≤ Q' * L.lam (.lad m) := fun m hm =>
    (hbd m hm).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (L.nonneg _))
  set ρ : ℝ := 1 - 1 / Q' with hρ
  have hρ0 : (1 : ℝ) / 2 ≤ ρ := by
    have h : 1 / Q' ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hQ2
    rw [hρ]; linarith
  have hρ1 : ρ < 1 := by
    have h : 0 < 1 / Q' := by positivity
    rw [hρ]; linarith
  have hρpos : (0 : ℝ) < ρ := by linarith
  have hstep : ∀ m, m₁ ≤ m → L.tailMass (m + 1) ≤ ρ * L.tailMass m := by
    intro m hm
    have hsucc := L.tailMass_succ m
    have hlam : L.tailMass m / Q' ≤ L.lam (.lad m) := by
      rw [div_le_iff₀ hQpos, mul_comm]; exact hbd' m hm
    have key : L.tailMass m * (1 / Q') ≤ L.lam (.lad m) := by
      rw [← div_eq_mul_one_div]; exact hlam
    have hTm : L.tailMass (m + 1) = L.tailMass m - L.lam (.lad m) := by linarith
    rw [hTm, hρ]
    nlinarith [key]
  have hgeom : ∀ n : ℕ, L.tailMass (m₁ + n) ≤ L.tailMass m₁ * ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h := hstep (m₁ + n) (by omega)
        calc L.tailMass (m₁ + (n + 1)) = L.tailMass ((m₁ + n) + 1) := by congr 1
          _ ≤ ρ * L.tailMass (m₁ + n) := h
          _ ≤ ρ * (L.tailMass m₁ * ρ ^ n) := mul_le_mul_of_nonneg_left ih hρpos.le
          _ = L.tailMass m₁ * ρ ^ (n + 1) := by ring
  set A : ℝ := Real.log (L.tailMass m₁) - Real.log (L.lam (.lad 1)) with hA
  set β : ℝ := -Real.log ρ with hβ
  have hβpos : 0 < β := by
    rw [hβ, neg_pos]; exact Real.log_neg hρpos hρ1
  have hkey : ∀ D : ℕ, m₁ ≤ 2 ^ D →
      ((2 : ℝ) ^ D - (m₁ : ℝ)) * β
        ≤ A + ∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i)) := by
    intro D hD
    obtain ⟨n, hn⟩ : ∃ n, 2 ^ D = m₁ + n := ⟨2 ^ D - m₁, by omega⟩
    have hlow := L.lam_pow_two_ge D
    have hup : L.lam (.lad (2 ^ D)) ≤ L.tailMass m₁ * ρ ^ n :=
      le_trans (hn ▸ L.lam_le_tailMass (inTail_of le_rfl trivial)) (hn ▸ hgeom n)
    have hprodpos : 0 < ∏ i ∈ Finset.range D, S.eps (2 ^ i) :=
      Finset.prod_pos fun i _ => S.eps_pos Nat.one_le_two_pow
    have hlam1 : 0 < L.lam (.lad 1) := L.pos trivial
    have hleft : 0 < L.lam (.lad 1) * ∏ i ∈ Finset.range D, S.eps (2 ^ i) :=
      mul_pos hlam1 hprodpos
    have hlog := Real.log_le_log hleft (le_trans hlow hup)
    rw [Real.log_mul hlam1.ne' hprodpos.ne',
      Real.log_prod (fun i _ => (S.eps_pos Nat.one_le_two_pow).ne'),
      Real.log_mul (L.tailMass_pos m₁).ne' (by positivity), Real.log_pow] at hlog
    have hGeq : (∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i)))
        = -∑ i ∈ Finset.range D, Real.log (S.eps (2 ^ i)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [one_div, Real.log_inv]
    have hncast : ((n : ℝ)) = (2 : ℝ) ^ D - (m₁ : ℝ) := by
      have hcast : ((2 ^ D : ℕ) : ℝ) = ((m₁ + n : ℕ) : ℝ) := by rw [hn]
      push_cast at hcast
      linarith
    rw [hncast] at hlog
    rw [hGeq, hA, hβ]
    linarith [hlog]
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * A / β)
  have hev1 : ∀ᶠ D : ℕ in atTop,
      (∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))) / 2 ^ D < β / 4 :=
    hstar.eventually_lt_const (by linarith)
  obtain ⟨D, hD1, hD2, hD3⟩ :=
    (hev1.and ((eventually_ge_atTop (4 * m₁)).and (eventually_ge_atTop N))).exists
  set G : ℝ := ∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i)) with hG
  have hpowpos : (0 : ℝ) < 2 ^ D := by positivity
  have hDlt : (D : ℝ) < 2 ^ D := by exact_mod_cast Nat.lt_two_pow_self
  have hd4 : (4 : ℝ) * (m₁ : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD2
  have hNle : (N : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD3
  have hAbound : 4 * A / β < (2 : ℝ) ^ D := lt_of_lt_of_le hN (le_trans hNle hDlt.le)
  have hAb : 4 * A < (2 : ℝ) ^ D * β := by
    rw [div_lt_iff₀ hβpos] at hAbound; linarith
  have hDnat : m₁ ≤ 2 ^ D := by
    have hc : ((m₁ : ℝ)) ≤ (2 : ℝ) ^ D := by linarith
    exact_mod_cast hc
  have hmain := hkey D hDnat
  have hGlt : G < β / 4 * 2 ^ D := by
    rw [div_lt_iff₀ hpowpos] at hD1; linarith [hD1]
  have hsplit : ((m₁ : ℝ)) ≤ (2 : ℝ) ^ D / 4 := by linarith
  have hfin : (1 / 2) * ((2 : ℝ) ^ D * β) ≤ A := by nlinarith [hmain, hGlt, hsplit, hβpos]
  by_cases hA0 : 0 ≤ A
  · nlinarith [hfin, hAb]
  · nlinarith [hfin, hAb, hpowpos, hβpos]

end Stat

/-! ## Step 2: the infimum along the centred tail indicators -/

namespace Stat

/-- The centred tail indicator is bounded, hence a legitimate test function. -/
theorem centredTail_bounded {cap : Option ℕ} (L : Stat S cap) (m : ℕ) :
    ∃ C, ∀ x, |L.centredTail m x| ≤ C := by
  refine ⟨2, fun x => ?_⟩
  have h1 := tailInd_le_one (cap := cap) (m := m) x
  have h2 := tailInd_nonneg (cap := cap) (m := m) x
  have h3 := L.tailMass_nonneg m
  have h4 := L.tailMass_le_one m
  rw [Stat.centredTail, abs_le]
  constructor <;> linarith

/-- The mass ratio at one cut: `mass p ((Id−P⋆)f_m) ≤ 2λ_m` against `mass p f_m ≥ L(m)·2^{-p}`.
This is `eq:doubling_stepp` read as a ratio. -/
theorem mass_ratio_bound {cap : Option ℕ} (L : Stat S cap) {m : ℕ} (hdm : S.d < m)
    (hD : HasDouble cap m) {p : ℝ} (hp : 1 ≤ p) (hLpos : 0 < L.tailMass m)
    (hhalf : (1 : ℝ) / 2 ≤ 1 - L.tailMass m) {t : ℝ} (ht : 0 < t)
    (hsmall : 2 * L.lam (.lad m) ≤ t * (L.tailMass m * (1 / 2) ^ p)) :
    L.mass p (fun x => L.centredTail m x - pstar S cap (L.centredTail m) x)
      ≤ t * L.mass p (L.centredTail m) := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hpow : ((1 : ℝ) / 2) ^ p ≤ (1 - L.tailMass m) ^ p :=
    Real.rpow_le_rpow (by norm_num) hhalf hp0
  have hden : L.tailMass m * (1 / 2) ^ p ≤ L.mass p (L.centredTail m) :=
    le_trans (mul_le_mul_of_nonneg_left hpow hLpos.le) (L.mass_centredTail_ge m p)
  calc L.mass p (fun x => L.centredTail m x - pstar S cap (L.centredTail m) x)
      ≤ 2 * L.lam (.lad m) := L.mass_defect_le hdm hD hp
    _ ≤ t * (L.tailMass m * (1 / 2) ^ p) := hsmall
    _ ≤ t * L.mass p (L.centredTail m) := mul_le_mul_of_nonneg_left hden ht.le

variable (L : Stat S none)

/-- **`eq:doubling_inf`.** For every `t > 0` some centred tail indicator has flow-matching defect
of mass at most `t` times its own mass: the infimum of the Rayleigh quotient over the mean-zero
functions of unit norm is `0`. -/
theorem exists_small_mass_ratio (hstar : GrowthCond S) {p : ℝ} (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) :
    ∃ m, S.d < m ∧
      L.mass p (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
        ≤ t * L.mass p (L.centredTail m) := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hhalfpow : (0 : ℝ) < ((1 : ℝ) / 2) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → L.tailMass m ≤ 1 / 2 := by
    have h : ∀ᶠ m : ℕ in atTop, L.tailMass m < 1 / 2 :=
      L.tailMass_tendsto_zero.eventually_lt_const (by norm_num)
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp h
    exact ⟨m₀, fun m hm => (hm₀ m hm).le⟩
  have hm₁d : S.d < max m₀ (S.d + 1) := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  obtain ⟨m, hmge, hmQ⟩ :=
    L.exists_tailRatio_gt hstar (2 / (t * (1 / 2) ^ p)) (max m₀ (S.d + 1))
  have hmd : S.d < m := lt_of_lt_of_le hm₁d hmge
  have hhalf : (1 : ℝ) / 2 ≤ 1 - L.tailMass m := by
    have := hm₀ m (le_trans (le_max_left _ _) hmge); linarith
  refine ⟨m, hmd, L.mass_ratio_bound hmd trivial hp (L.tailMass_pos m) hhalf ht ?_⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at hmQ
  nlinarith [hmQ]

/-- **Step 3 of `theo:doubling_unbounded`(2).** No constant bounds the mass of a bounded mean-zero
function by the mass of its flow-matching defect: in `L^p(λ)` terms, no bounded `S` satisfies
`S(Id − P⋆) = Id − Π`. -/
theorem no_bounded_inverse (hstar : GrowthCond S) {p : ℝ} (hp : 1 ≤ p) :
    ¬ ∃ B : ℝ, ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) → (∑' x, L.lam x * f x = 0) →
        L.mass p f ≤ B * L.mass p (fun x => f x - pstar S none f x) := by
  rintro ⟨B, hB⟩
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have htpos : (0 : ℝ) < 1 / (2 * (|B| + 1)) := by positivity
  obtain ⟨m, hmd, hbound⟩ := L.exists_small_mass_ratio hstar hp htpos
  have hm1 : 1 < m := by have := S.d_pos; omega
  have hfpos : 0 < L.mass p (L.centredTail m) :=
    lt_of_lt_of_le (mul_pos (L.tailMass_pos m) (Real.rpow_pos_of_pos (L.coTail_pos hm1) p))
      (L.mass_centredTail_ge m p)
  have hdefnn : 0 ≤ L.mass p (fun x => L.centredTail m x - pstar S none (L.centredTail m) x) :=
    tsum_nonneg fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) p) (L.nonneg x)
  have happ := hB (L.centredTail m) (L.centredTail_bounded m) (L.tsum_centredTail m)
  have h1 : B * L.mass p (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
      ≤ |B| * L.mass p (fun x => L.centredTail m x - pstar S none (L.centredTail m) x) :=
    mul_le_mul_of_nonneg_right (le_abs_self B) hdefnn
  have h2 : |B| * L.mass p (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
      ≤ |B| * (1 / (2 * (|B| + 1)) * L.mass p (L.centredTail m)) :=
    mul_le_mul_of_nonneg_left hbound (abs_nonneg B)
  have h3 : |B| * (1 / (2 * (|B| + 1))) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith [abs_nonneg B]
  nlinarith [happ, h1, h2, h3, hfpos]

end Stat

/-! ## Item (1): the family satisfies (★) -/

/-- **`theo:doubling_unbounded`(1).** For `ε_{c,s}` the left side of (★) is `O(D²)`, hence
`o(2^D)`: `Σ_{i<D} log(1/ε_{c,s}(2^i)) = Σ_{i<D} (s log(2^i+1) − log c)`. -/
theorem growthCond_of_family {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (S : Setting) (heps : ∀ j, S.eps j = epsCS c s j) : GrowthCond S := by
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hkey : ∀ i : ℕ,
      Real.log (1 / S.eps (2 ^ i)) ≤ s * ((i : ℝ) + 1) * Real.log 2 + |Real.log c| := by
    intro i
    rw [one_div, Real.log_inv, heps, epsCS, Real.log_div hc.ne' (by positivity),
      Real.log_rpow (by positivity)]
    have hb : Real.log (((2 ^ i : ℕ) : ℝ) + 1) ≤ ((i : ℝ) + 1) * Real.log 2 := by
      have h1 : ((2 ^ i : ℕ) : ℝ) + 1 ≤ 2 ^ (i + 1) := by
        push_cast
        have hone : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        calc (2 : ℝ) ^ i + 1 ≤ 2 ^ i + 2 ^ i := by linarith
          _ = 2 ^ (i + 1) := by ring
      have h2 := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h2
    have hcabs : -Real.log c ≤ |Real.log c| := neg_le_abs _
    nlinarith [hb, hcabs, hs]
  have hnn : ∀ D : ℕ, (0 : ℝ) ≤ (∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))) / 2 ^ D := by
    intro D
    refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (by positivity)
    have hpos : 0 < S.eps (2 ^ i) := S.eps_pos Nat.one_le_two_pow
    have hlt : S.eps (2 ^ i) ≤ 1 := (S.eps_lt_one Nat.one_le_two_pow).le
    rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos hpos.le hlt
  have hub : ∀ D : ℕ, (∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))) / 2 ^ D
      ≤ (s * Real.log 2 * ((D : ℝ) * (D : ℝ)) + |Real.log c| * (D : ℝ)) / 2 ^ D := by
    intro D
    have hnum : ∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))
        ≤ s * Real.log 2 * ((D : ℝ) * (D : ℝ)) + |Real.log c| * (D : ℝ) := by
      calc ∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))
          ≤ ∑ _i ∈ Finset.range D, (s * (D : ℝ) * Real.log 2 + |Real.log c|) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hiD : (i : ℝ) + 1 ≤ (D : ℝ) := by
              have := Finset.mem_range.mp hi
              exact_mod_cast this
            refine (hkey i).trans ?_
            have hstep3 : (0:ℝ) ≤ s * ((D : ℝ) - ((i : ℝ) + 1)) * Real.log 2 :=
              mul_nonneg (mul_nonneg hs (by linarith)) hl2
            nlinarith [hstep3]
        _ = (D : ℝ) * (s * (D : ℝ) * Real.log 2 + |Real.log c|) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = s * Real.log 2 * ((D : ℝ) * (D : ℝ)) + |Real.log c| * (D : ℝ) := by ring
    gcongr
  have hlim : Tendsto (fun D : ℕ => (s * Real.log 2 * ((D : ℝ) * (D : ℝ))
      + |Real.log c| * (D : ℝ)) / 2 ^ D) atTop (𝓝 0) := by
    have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ) < 2)
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ) < 2)
    have hsum := (h2.const_mul (s * Real.log 2)).add (h1.const_mul |Real.log c|)
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr fun D => ?_
    have hd : ((2 : ℝ) ^ D) ≠ 0 := by positivity
    field_simp
  exact squeeze_zero hnn hub hlim

/-! ## `rem:doubling_geometric`: (★) is not vacuous -/

/-- **`rem:doubling_geometric`, the identity.** For a geometrically decaying doubling probability
`ε(j) = a ρ^j` the left side of (★) is `D log(1/a) + (2^D − 1) log(1/ρ)`. -/
theorem geometric_sum {a rho : ℝ} (ha : 0 < a) (hrho : 0 < rho) (S : Setting)
    (heps : ∀ j, S.eps j = a * rho ^ j) (D : ℕ) :
    ∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))
      = (D : ℝ) * Real.log (1 / a) + ((2 : ℝ) ^ D - 1) * Real.log (1 / rho) := by
  have hterm : ∀ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))
      = Real.log (1 / a) + (2 : ℝ) ^ i * Real.log (1 / rho) := by
    intro i _
    have hp : (0 : ℝ) < rho ^ (2 ^ i) := pow_pos hrho _
    rw [heps, one_div, mul_inv, ← one_div, ← one_div]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [show (1 : ℝ) / rho ^ 2 ^ i = (1 / rho) ^ 2 ^ i by rw [div_pow, one_pow],
      Real.log_pow]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.sum_mul, geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
  norm_num

/-- **`rem:doubling_geometric`.** (★) fails for `ε(j) = a ρ^j` with `ρ ∈ (0,1)`: the left side is
of order `2^D`, not `o(2^D)`. -/
theorem not_growthCond_geometric {a rho : ℝ} (ha : 0 < a) (hrho : 0 < rho) (hrho1 : rho < 1)
    (S : Setting) (heps : ∀ j, S.eps j = a * rho ^ j) : ¬ GrowthCond S := by
  intro hstar
  have hlogpos : 0 < Real.log (1 / rho) := by
    rw [one_div]
    exact Real.log_pos (by rw [lt_inv_comm₀ (by norm_num) hrho]; simpa using hrho1)
  have hlim : Tendsto (fun D : ℕ =>
      (∑ i ∈ Finset.range D, Real.log (1 / S.eps (2 ^ i))) / 2 ^ D) atTop
      (𝓝 (Real.log (1 / rho))) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ) < 2)
    have h2 : Tendsto (fun D : ℕ => (1 : ℝ) / 2 ^ D) atTop (𝓝 0) := by
      simpa using tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ) < 2)
    have hsum := (h1.const_mul (Real.log (1 / a))).add
      (((tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub h2).const_mul
        (Real.log (1 / rho)))
    simp only [mul_zero, zero_add, sub_zero, mul_one] at hsum
    refine hsum.congr fun D => ?_
    have hd : ((2 : ℝ) ^ D) ≠ 0 := by positivity
    rw [geometric_sum ha hrho S heps D]
    field_simp
  have := tendsto_nhds_unique hstar hlim
  exact absurd this.symm hlogpos.ne'

end GFNBounds.Doubling
