import GFNBounds.Doubling.Kac
import GFNBounds.Doubling.Descent
import GFNBounds.Doubling.Family

/-!
# The truncation, and a proved `√K`

**`cor:doubling_truncation`** — `app_doubling.tex:2199–2336`.

> Let `s = 1`, `0 < c < 1`, and for an even `K ≥ d` let `λ^K`, `L_K`, `B̂_K` be the invariant
> probability, the tail and the constant of the truncation at `K`. Then:
> (1) for `d < m ≤ K/2`, `B̂_K ≥ √(L_K(m)(1−L_K(m)) / (2λ^K_m))`;
> (2) there are `m₀`, `K₀ ≥ d` and `c₉ ≥ 1` depending only on `c` and `d` such that every even
> `K ≥ K₀` has `0 < C^K_- ≤ C^K_+` with `C^K_+/C^K_- ≤ c₉` and `C^K_- m^{−p_*} ≤ λ^K_m ≤
> C^K_+ m^{−p_*}` for `m₀ ≤ m ≤ K/2`;
> (3) there is `c₈ > 0` depending only on `c`, `d`, `j̄` with `B̂_K ≥ c₈√K` for every even
> `K ≥ K₀`.

## SCOPE (disclosed)

* **`B̂_K` is not used here.** Items (1) and (3) are stated about *any* `B` bounding the
  `L²(λ^K)` Rayleigh quotient in the mass layer, so they are lower bounds on every such
  constant. `B̂_K` itself is constructed in `OperatorL2.lean` (`Stat.exists_bhat`, Step 1), and
  `RayleighBridge.lean` turns `‖S‖` into such a `B = ‖S‖²`; `main_truncation_sqrtK` in
  `Main.lean` composes the two with item (3) into the paper's `B̂_K ≥ c₈√K`.
* Squared and cleared of roots, as in `cor:doubling_family`: `B` stands for `B̂_K²` and `c₈sq`
  for `c₈²`.
* Step 6 is `Kac.lean` and is **unconditional** — the paper cites Kac's formula, which mathlib
  does not have, and it is derived there from invariance alone.
* Item (2) is `decayK`, stated with the descent-weight window `Z₁ ≤ E(Z_ℓ) ≤ Z₂` as
  hypotheses; `Decay.descOne_two_sided` (`Product.lean`) discharges them at every level
  `ℓ ≥ m₀`, which is how `main_truncation_sqrtK` uses it. Item (3) takes `eq:doubling_decayK` as
  a hypothesis, so the composition sits in one place.
* ⚠ weakened: evenness of `K` enters only through `m ≤ K/2 ↔ 2m ≤ K`, and is not assumed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting} {K : ℕ}

namespace Stat

variable (L : Stat S (some K))

/-! ### Item (1): the per-cut inequality on the truncation -/

/-- **`eq:doubling_percut_K`, squared and cleared.** Every constant bounding the `L²(λ^K)`
Rayleigh quotient is at least `L_K(m)(1−L_K(m)) / (2λ^K_m)`. -/
theorem percut_K {B : ℝ} {m : ℕ} (hdm : S.d < m) (hD : HasDouble (some K) m)
    (hB : ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) → (∑' x, L.lam x * f x = 0) →
      L.mass 2 f ≤ B * L.mass 2 (fun x => f x - pstar S (some K) f x)) :
    L.tailMass m * (1 - L.tailMass m) ≤ 2 * L.lam (.lad m) * B := by
  have hnum : L.mass 2 (fun x => L.centredTail m x - pstar S (some K) (L.centredTail m) x)
      ≤ 2 * L.lam (.lad m) := L.mass_defect_le hdm hD (by norm_num)
  have hnn : 0 ≤ L.mass 2 (fun x => L.centredTail m x - pstar S (some K) (L.centredTail m) x) :=
    tsum_nonneg fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) 2) (L.nonneg x)
  have happ := hB (L.centredTail m) (L.centredTail_bounded m) (L.tsum_centredTail m)
  rw [L.mass_two_centredTail m] at happ
  have hpos := L.tailMass_mul_coTail_pos hdm hD
  have hBnn : 0 ≤ B := by
    by_contra hcon
    have hBneg : B < 0 := not_le.mp hcon
    nlinarith [happ, hnn, hpos]
  nlinarith [happ, hnum, hBnn]

/-! ### Step 5: the tail against the mass at the cut -/

/-- A finite block of the ladder below the cap is part of the tail. -/
theorem finset_sum_le_tailMass {m b : ℕ} (hbK : b ≤ K) :
    ∑ j ∈ Finset.Icc m b, L.lam (.lad j) ≤ L.tailMass m := by
  classical
  have hinj : Set.InjOn St.lad (Finset.Icc m b) := fun a _ b _ h => by simpa using h
  have hsum := sum_le_hasSum ((Finset.Icc m b).image St.lad)
    (fun x _ => mul_nonneg (L.nonneg x) (tailInd_nonneg x)) (L.hasSum_tailMass m)
  rw [Finset.sum_image hinj] at hsum
  refine le_trans (le_of_eq ?_) hsum
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_Icc.mp hj
  rw [tailInd_one (show inTail (some K) m j from ⟨hj'.1, le_trans hj'.2 hbK⟩), mul_one]

/-- **Step 5.** `L_K(m) ≥ (Cm/(Cp 2^{p_*})) · m · λ^K_m`: the tail is `m` times the mass at the
cut, up to the ratio of the two decay constants. -/
theorem tail_lower (D : Decay) {Cm Cp : ℝ} (hC : 0 < Cm) {m : ℕ} (hm : 1 ≤ m)
    (h2mK : 2 * m ≤ K)
    (hlo : ∀ j : ℕ, m ≤ j → j ≤ 2 * m → Cm * (j : ℝ) ^ (-D.p) ≤ L.lam (.lad j))
    (hhi : L.lam (.lad m) ≤ Cp * (m : ℝ) ^ (-D.p)) :
    Cm / (Cp * (2 : ℝ) ^ D.p) * (m : ℝ) * L.lam (.lad m) ≤ L.tailMass m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmp : (0 : ℝ) < (m : ℝ) ^ (-D.p) := rpow_pos_of_pos hmpos _
  have htwo : (0 : ℝ) < (2 : ℝ) ^ D.p := rpow_pos_of_pos (by norm_num) _
  have hCp : 0 < Cp := by
    have h1 := hlo m le_rfl (by omega)
    nlinarith [hhi, hmp, hC]
  -- `L_K(m) ≥ (m+1) Cm (2m)^{-p} ≥ m Cm 2^{-p} m^{-p}`
  have hblock : (m : ℝ) * (Cm * ((2 : ℝ) * (m : ℝ)) ^ (-D.p)) ≤ L.tailMass m := by
    refine le_trans ?_ (L.finset_sum_le_tailMass h2mK)
    have hterm : ∀ j ∈ Finset.Icc m (2 * m),
        Cm * ((2 : ℝ) * (m : ℝ)) ^ (-D.p) ≤ L.lam (.lad j) := by
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hjr : (j : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hj'.2
      have hjpos : (0 : ℝ) < (j : ℝ) := by
        have : 1 ≤ j := le_trans hm hj'.1
        exact_mod_cast this
      have hmono : ((2 : ℝ) * (m : ℝ)) ^ (-D.p) ≤ (j : ℝ) ^ (-D.p) :=
        rpow_le_rpow_of_nonpos hjpos hjr (by linarith [D.p_pos])
      exact le_trans (mul_le_mul_of_nonneg_left hmono hC.le) (hlo j hj'.1 hj'.2)
    have hcard : ((Finset.Icc m (2 * m)).card : ℝ) = (m : ℝ) + 1 := by
      rw [Nat.card_Icc]
      have h : 2 * m + 1 - m = m + 1 := by omega
      rw [h]; push_cast; ring
    have hnn : (0 : ℝ) ≤ Cm * ((2 : ℝ) * (m : ℝ)) ^ (-D.p) := by positivity
    calc (m : ℝ) * (Cm * ((2 : ℝ) * (m : ℝ)) ^ (-D.p))
        ≤ ((m : ℝ) + 1) * (Cm * ((2 : ℝ) * (m : ℝ)) ^ (-D.p)) := by nlinarith
      _ = (Finset.Icc m (2 * m)).card • (Cm * ((2 : ℝ) * (m : ℝ)) ^ (-D.p)) := by
          rw [nsmul_eq_mul, hcard]
      _ ≤ ∑ j ∈ Finset.Icc m (2 * m), L.lam (.lad j) :=
          Finset.card_nsmul_le_sum _ _ _ hterm
  have hsplit : ((2 : ℝ) * (m : ℝ)) ^ (-D.p) = ((2 : ℝ) ^ D.p)⁻¹ * (m : ℝ) ^ (-D.p) := by
    rw [Real.mul_rpow (by norm_num) hmpos.le, rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsplit] at hblock
  refine le_trans ?_ hblock
  have hkey : Cm / (Cp * (2 : ℝ) ^ D.p) * (m : ℝ) * L.lam (.lad m)
      ≤ Cm / (Cp * (2 : ℝ) ^ D.p) * (m : ℝ) * (Cp * (m : ℝ) ^ (-D.p)) :=
    mul_le_mul_of_nonneg_left hhi (by positivity)
  refine le_trans hkey (le_of_eq ?_)
  field_simp

/-! ### Step 6, wired: the boundedness hypothesis Kac needs -/

/-- On the truncation the supersolution is bounded by `K/(1−c)`, which is what makes the
hitting integrals converge. -/
theorem hitInt_le {c : ℝ} (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (hc0 : 0 < c) (n : ℕ) :
    L.hitInt n ≤ (K : ℝ) / (1 - c) := by
  have hcne : (0 : ℝ) < 1 - c := by linarith
  have hterm : ∀ x : St, L.lam x * hitExp S (some K) n x ≤ L.lam x * ((K : ℝ) / (1 - c)) := by
    intro x
    by_cases hx : OnChain (some K) x
    · refine mul_le_mul_of_nonneg_left ?_ (L.nonneg x)
      refine le_trans (hitExp_le_linSuper hc0 hc1 heps n x) ?_
      rcases x with j | _
      · have hjK : j ≤ K := hx
        have : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hjK
        rw [linSuper_lad]
        gcongr
      · rw [linSuper, height_sink, zero_div]
        positivity
    · rw [L.vanish hx, zero_mul, zero_mul]
  have hs1 := L.summable_mul (hitExp_bounded (S := S) (cap := some K) n)
  have hs2 : Summable (fun x => L.lam x * ((K : ℝ) / (1 - c))) := L.summable.mul_right _
  have hcmp := Summable.tsum_le_tsum hterm hs1 hs2
  have hfin : ∑' x, L.lam x * ((K : ℝ) / (1 - c)) = (K : ℝ) / (1 - c) := by
    rw [tsum_mul_right, L.total, one_mul]
  rw [hfin] at hcmp
  exact hcmp

/-! ### Item (3): the `√K` -/

/-- **`eq:doubling_sqrtK`, squared.** Every constant bounding the `L²(λ^K)` Rayleigh quotient is
at least `c₈² K`, with `c₈² = Cm / (Cp · 2^{p_*+4} · (2 + j̄/(1−c)))` — the paper's constant, since
`Cp/Cm = c₉`. -/
theorem sqrtK (D : Decay) {c B Cm Cp : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1))
    (hC : 0 < Cm) (hKd : 4 * (S.d + 1) ≤ K) (hK8 : 8 ≤ K)
    (hlo : ∀ j : ℕ, K / 4 ≤ j → j ≤ 2 * (K / 4) → Cm * (j : ℝ) ^ (-D.p) ≤ L.lam (.lad j))
    (hhi : L.lam (.lad (K / 4)) ≤ Cp * ((K / 4 : ℕ) : ℝ) ^ (-D.p))
    (hB : ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) → (∑' x, L.lam x * f x = 0) →
      L.mass 2 f ≤ B * L.mass 2 (fun x => f x - pstar S (some K) f x)) :
    Cm / (Cp * (2 : ℝ) ^ D.p * 16 * (2 + S.jbar / (1 - c))) * (K : ℝ) ≤ B := by
  set m : ℕ := K / 4 with hm
  have hm1 : 1 ≤ m := by omega
  have hdm : S.d < m := by omega
  have h2mK : 2 * m ≤ K := by omega
  have hD : HasDouble (some K) m := by show 2 * m ≤ K; omega
  have hmK8 : (K : ℝ) ≤ 8 * (m : ℝ) := by
    have h : K ≤ 8 * m := by omega
    exact_mod_cast h
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hcne : (0 : ℝ) < 1 - c := by linarith
  have htwo : (0 : ℝ) < (2 : ℝ) ^ D.p := rpow_pos_of_pos (by norm_num) _
  have hmp : (0 : ℝ) < ((m : ℕ) : ℝ) ^ (-D.p) := rpow_pos_of_pos hmpos _
  have hCp : 0 < Cp := by
    have h1 := hlo m le_rfl (by omega)
    nlinarith [hhi, hmp, hC]
  have hjb : 0 ≤ S.jbar :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (S.row_nonneg k)
  have hden : (0 : ℝ) < 2 + S.jbar / (1 - c) := by positivity
  -- the three inputs
  have hstep5 := L.tail_lower D hC hm1 h2mK hlo hhi
  have hstep6 : (2 + S.jbar / (1 - c))⁻¹ ≤ 1 - L.tailMass m := by
    refine le_trans (L.lam_one_ge hc0 hc1 heps (M := (K : ℝ) / (1 - c))
      (fun n => L.hitInt_le hc1 heps hc0 n)) ?_
    exact L.lam_one_le_coTailMass (by omega)
  have hstep1 := L.percut_K hdm hD hB
  have hmK : m ≤ K := by omega
  have honchain : OnChain (some K) (St.lad m) := hmK
  have hlampos : 0 < L.lam (.lad m) := L.pos honchain
  have hLpos : 0 < L.tailMass m := lt_of_lt_of_le hlampos
    (L.lam_le_tailMass (inTail_of le_rfl honchain))
  -- assemble
  set γ : ℝ := Cm / (Cp * (2 : ℝ) ^ D.p) with hγ
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hprod : γ * (m : ℝ) * L.lam (.lad m) * (2 + S.jbar / (1 - c))⁻¹
      ≤ L.tailMass m * (1 - L.tailMass m) := by
    have h1 : γ * (m : ℝ) * L.lam (.lad m) * (2 + S.jbar / (1 - c))⁻¹
        ≤ L.tailMass m * (2 + S.jbar / (1 - c))⁻¹ :=
      mul_le_mul_of_nonneg_right hstep5 (by positivity)
    have h2 : L.tailMass m * (2 + S.jbar / (1 - c))⁻¹ ≤ L.tailMass m * (1 - L.tailMass m) :=
      mul_le_mul_of_nonneg_left hstep6 hLpos.le
    linarith
  have hchain : γ * (m : ℝ) * L.lam (.lad m) * (2 + S.jbar / (1 - c))⁻¹
      ≤ 2 * L.lam (.lad m) * B := le_trans hprod hstep1
  -- divide by `λ_m > 0`
  have hB' : γ * (m : ℝ) * (2 + S.jbar / (1 - c))⁻¹ ≤ 2 * B := by
    refine le_of_mul_le_mul_right ?_ hlampos
    linarith [hchain]
  -- and `m ≥ K/8`
  have hfinal : γ * ((K : ℝ) / 8) * (2 + S.jbar / (1 - c))⁻¹ ≤ 2 * B := by
    refine le_trans ?_ hB'
    have : (K : ℝ) / 8 ≤ (m : ℝ) := by linarith
    have hnn : (0 : ℝ) ≤ γ * (2 + S.jbar / (1 - c))⁻¹ := by positivity
    nlinarith [this, hγpos, hden]
  have hrw : Cm / (Cp * (2 : ℝ) ^ D.p * 16 * (2 + S.jbar / (1 - c))) * (K : ℝ)
      = γ * ((K : ℝ) / 8) * (2 + S.jbar / (1 - c))⁻¹ / 2 := by
    rw [hγ]; field_simp; ring
  rw [hrw]
  linarith

/-! ### Item (2): the decay on the truncation, with a ratio free of `K` -/

/-- **The step down, from the cut balance.** `λ_{i−1} ε(i−1) ≤ λ_i`: keeping only the term
`y = i−1` of `eq:doubling_cut` at `i`, which is legitimate because `i−1 ∈ W(i)` for `i ≥ 2`. -/
theorem lam_ge_prev (L : Stat S (some K)) {i : ℕ} (hdi : S.d < i) (hD : HasDouble (some K) i)
    (hi2 : 2 ≤ i) : L.lam (.lad (i - 1)) * S.eps (i - 1) ≤ L.lam (.lad i) := by
  have hbal := cut_balance L hdi hD
  have hmem : i - 1 ∈ window i := by rw [mem_window]; omega
  have hsingle : L.lam (.lad (i - 1)) * S.eps (i - 1)
      ≤ ∑ y ∈ window i, L.lam (.lad y) * S.eps y := by
    refine Finset.single_le_sum (f := fun y => L.lam (.lad y) * S.eps y) (fun y hy => ?_) hmem
    have hy1 : 1 ≤ y := Decay.one_le_of_mem_window' (by omega) hy
    exact mul_nonneg (L.nonneg _) (S.eps_pos hy1).le
  have hi1 : 1 ≤ i := by omega
  have hle : L.lam (.lad i) * (1 - S.eps i) ≤ L.lam (.lad i) := by
    have := (S.eps_pos hi1).le
    nlinarith [L.nonneg (St.lad i)]
  rw [hbal] at hle
  linarith [hsingle, hle]

/-- Going up the ladder: `λ_{j+n} ≤ λ_j ρ^n` with `ρ = (1 − ε_max)^{-1}`. -/
theorem lam_chain_up (L : Stat S (some K)) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    L.lam (.lad (j + n)) ≤ L.lam (.lad j) * ((1 - S.epsMax)⁻¹) ^ n := by
  have hem : 0 < 1 - S.epsMax := by have := S.epsMax_lt_one; linarith
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : L.lam (.lad (j + n + 1)) * (1 - S.eps (j + n + 1)) ≤ L.lam (.lad (j + n)) := by
        have h := L.lam_le_prev (m := j + n + 1) (by omega)
        simpa using h
      have hge : 1 - S.epsMax ≤ 1 - S.eps (j + n + 1) := by
        have := S.eps_le (show 1 ≤ j + n + 1 by omega); linarith
      have hnn : 0 ≤ L.lam (.lad (j + n + 1)) := L.nonneg _
      have hup : L.lam (.lad (j + n + 1)) * (1 - S.epsMax) ≤ L.lam (.lad (j + n)) := by
        nlinarith [hstep, hge, hnn]
      have hρ : L.lam (.lad (j + n + 1)) ≤ L.lam (.lad (j + n)) * (1 - S.epsMax)⁻¹ := by
        rw [le_mul_inv_iff₀ hem]; linarith
      have hρnn : (0 : ℝ) ≤ ((1 - S.epsMax)⁻¹) ^ n := by positivity
      calc L.lam (.lad (j + (n + 1))) = L.lam (.lad (j + n + 1)) := by ring_nf
        _ ≤ L.lam (.lad (j + n)) * (1 - S.epsMax)⁻¹ := hρ
        _ ≤ (L.lam (.lad j) * ((1 - S.epsMax)⁻¹) ^ n) * (1 - S.epsMax)⁻¹ :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = L.lam (.lad j) * ((1 - S.epsMax)⁻¹) ^ (n + 1) := by ring

/-- Going up the ladder from below: `λ_j η^n ≤ λ_{j+n}` when `η` is a lower bound for `ε` on the
range crossed. -/
theorem lam_chain_down (L : Stat S (some K)) {η : ℝ} (hη : 0 ≤ η) {j : ℕ} :
    ∀ n : ℕ, (∀ i, j ≤ i → i < j + n →
        S.d < i + 1 ∧ HasDouble (some K) (i + 1) ∧ 1 ≤ i ∧ η ≤ S.eps i) →
      L.lam (.lad j) * η ^ n ≤ L.lam (.lad (j + n)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hall
      have ihn := ih fun i h1 h2 => hall i h1 (by omega)
      obtain ⟨hd, hD, hi1, hε⟩ := hall (j + n) (by omega) (by omega)
      have hstep : L.lam (.lad (j + n)) * η ≤ L.lam (.lad (j + n + 1)) := by
        have h := L.lam_ge_prev (i := j + n + 1) hd hD (by omega)
        simp only [Nat.add_sub_cancel] at h
        have hnn : 0 ≤ L.lam (.lad (j + n)) := L.nonneg _
        nlinarith [h, hε, hnn]
      have hnn : 0 ≤ L.lam (.lad j) := L.nonneg _
      calc L.lam (.lad j) * η ^ (n + 1) = (L.lam (.lad j) * η ^ n) * η := by ring
        _ ≤ L.lam (.lad (j + n)) * η := mul_le_mul_of_nonneg_right ihn hη
        _ ≤ L.lam (.lad (j + n + 1)) := hstep
        _ = L.lam (.lad (j + (n + 1))) := by ring_nf

/-- **The block ratio, free of `K`.** On `[ℓ, 2ℓ)` any two masses differ by at most
`Q = ρ^ℓ + (η^ℓ)^{-1}`, with `ρ = (1−ε_max)^{-1}` and `η = c/(2ℓ+1)` — constants of `c` and `ℓ`
alone. This is what makes `c₉` independent of the cap. -/
theorem block_ratio (D : Decay) (L : Stat S (some K)) (heps : ∀ j, S.eps j = D.eps j)
    {ℓ : ℕ} (hℓd : S.d < ℓ) (hℓ1 : 1 ≤ ℓ) (h4ℓK : 4 * ℓ ≤ K)
    {j j' : ℕ} (hj : ℓ ≤ j) (hj2 : j < 2 * ℓ) (hj' : ℓ ≤ j') (hj'2 : j' < 2 * ℓ) :
    L.lam (.lad j') ≤ (((1 - S.epsMax)⁻¹) ^ ℓ + ((D.c / (2 * (ℓ : ℝ) + 1)) ^ ℓ)⁻¹)
      * L.lam (.lad j) := by
  have hem : 0 < 1 - S.epsMax := by have := S.epsMax_lt_one; linarith
  have hρ1 : (1 : ℝ) ≤ (1 - S.epsMax)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hem]
    have := S.epsMax_pos; simp; linarith
  set η : ℝ := D.c / (2 * (ℓ : ℝ) + 1) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; exact div_pos D.c_pos (by positivity)
  have hη1 : η ≤ 1 := by
    rw [hηdef, div_le_one (by positivity)]
    have := D.c_lt_one
    have : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
    linarith [D.c_lt_one]
  have hηpow : (0 : ℝ) < η ^ ℓ := by positivity
  have hQ1 : (0 : ℝ) < ((1 - S.epsMax)⁻¹) ^ ℓ + (η ^ ℓ)⁻¹ := by positivity
  have hnn : 0 ≤ L.lam (.lad j) := L.nonneg _
  rcases le_or_gt j' j with hle | hgt
  · -- go down: `λ_{j'} η^{j−j'} ≤ λ_j`
    obtain ⟨n, hn⟩ : ∃ n, j = j' + n := ⟨j - j', by omega⟩
    have hnl : n ≤ ℓ := by omega
    have hchain := L.lam_chain_down (η := η) hηpos.le (j := j') n ?_
    · rw [← hn] at hchain
      have hpow : η ^ ℓ ≤ η ^ n := pow_le_pow_of_le_one hηpos.le hη1 hnl
      have h1 : L.lam (.lad j') * η ^ ℓ ≤ L.lam (.lad j) := by
        refine le_trans ?_ hchain
        exact mul_le_mul_of_nonneg_left hpow (L.nonneg _)
      have h2 : L.lam (.lad j') ≤ L.lam (.lad j) * (η ^ ℓ)⁻¹ := by
        rw [le_mul_inv_iff₀ hηpow]; linarith
      have h3 : L.lam (.lad j) * (η ^ ℓ)⁻¹
          ≤ (((1 - S.epsMax)⁻¹) ^ ℓ + (η ^ ℓ)⁻¹) * L.lam (.lad j) := by
        have hpp : (0 : ℝ) ≤ ((1 - S.epsMax)⁻¹) ^ ℓ := by positivity
        nlinarith [hnn, hpp]
      linarith
    · intro i h1 h2
      refine ⟨by omega, ?_, by omega, ?_⟩
      · show 2 * (i + 1) ≤ K; omega
      · rw [heps i, D.eps_eq, hηdef]
        have hir : (i : ℝ) + 1 ≤ 2 * (ℓ : ℝ) + 1 := by
          have : i ≤ 2 * ℓ := by omega
          have : (i : ℝ) ≤ 2 * (ℓ : ℝ) := by exact_mod_cast this
          linarith
        exact div_le_div_of_nonneg_left D.c_pos.le (by positivity) hir
  · -- go up: `λ_{j'} ≤ λ_j ρ^{j'−j}`
    obtain ⟨n, hn⟩ : ∃ n, j' = j + n := ⟨j' - j, by omega⟩
    have hnl : n ≤ ℓ := by omega
    have hchain := L.lam_chain_up (j := j) (by omega) n
    rw [← hn] at hchain
    have hpow : ((1 - S.epsMax)⁻¹) ^ n ≤ ((1 - S.epsMax)⁻¹) ^ ℓ :=
      pow_le_pow_right₀ hρ1 hnl
    have hpp : (0 : ℝ) < (η ^ ℓ)⁻¹ := by positivity
    calc L.lam (.lad j') ≤ L.lam (.lad j) * ((1 - S.epsMax)⁻¹) ^ n := hchain
      _ ≤ L.lam (.lad j) * ((1 - S.epsMax)⁻¹) ^ ℓ :=
          mul_le_mul_of_nonneg_left hpow hnn
      _ ≤ (((1 - S.epsMax)⁻¹) ^ ℓ + (η ^ ℓ)⁻¹) * L.lam (.lad j) := by nlinarith [hnn, hpp]

/-- The truncation's masses satisfy `eq:doubling_cut` up to `K/2`. -/
theorem cutBalanceSeq_trunc (L : Stat S (some K)) :
    CutBalanceSeq S (fun j => L.lam (.lad j)) ((K / 2 : ℕ) : ℕ∞) := by
  intro m hdm hM
  have hmK : m ≤ K / 2 := by exact_mod_cast hM
  exact cut_balance L hdm (show 2 * m ≤ K by omega)

/-- **`eq:doubling_decayK`.** Two constants sandwiching `λ^K` on `[ℓ, K/2]`, with a ratio
`C⁺/C⁻ ≤ (Z₂/Z₁) 2^{p_*} Q²` **free of `K`** — which is the `c₉` of the paper, since `Q` depends
on `c` and `ℓ` alone and `Z₁, Z₂` on `c` and `d` alone.

Stated with `Z₁ ≤ E(Z_ℓ) ≤ Z₂` — `eq:doubling_product` at the level `ℓ` — as hypotheses, which
`Decay.descOne_two_sided` (`Product.lean`) discharges for every `ℓ ≥ m₀`. -/
theorem decayK (D : Decay) (L : Stat S (some K)) (heps : ∀ j, S.eps j = D.eps j)
    {ℓ : ℕ} (hℓd : S.d < ℓ) (hℓ1 : 1 ≤ ℓ) (h4ℓK : 4 * ℓ ≤ K)
    {Z₁ Z₂ : ℝ} (hZ1 : 0 < Z₁) (hZ2 : 0 < Z₂)
    (hZlo : ∀ y : ℕ, ℓ ≤ y → Z₁ ≤ D.descOne ℓ y)
    (hZhi : ∀ y : ℕ, ℓ ≤ y → D.descOne ℓ y ≤ Z₂) :
    ∃ Cm Cp : ℝ, 0 < Cm ∧
      Cp ≤ Z₂ / Z₁ * (2 : ℝ) ^ D.p
            * (((1 - S.epsMax)⁻¹) ^ ℓ + ((D.c / (2 * (ℓ : ℝ) + 1)) ^ ℓ)⁻¹) ^ 2 * Cm ∧
      ∀ m : ℕ, ℓ ≤ m → m ≤ K / 2 →
        Cm * (m : ℝ) ^ (-D.p) ≤ L.lam (.lad m) ∧ L.lam (.lad m) ≤ Cp * (m : ℝ) ^ (-D.p) := by
  classical
  set lam : ℕ → ℝ := fun j => L.lam (.lad j) with hlam
  set Q : ℝ := ((1 - S.epsMax)⁻¹) ^ ℓ + ((D.c / (2 * (ℓ : ℝ) + 1)) ^ ℓ)⁻¹ with hQdef
  have hem : 0 < 1 - S.epsMax := by have := S.epsMax_lt_one; linarith
  have hηpos : (0 : ℝ) < D.c / (2 * (ℓ : ℝ) + 1) := div_pos D.c_pos (by positivity)
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hℓp : (0 : ℝ) < (ℓ : ℝ) ^ D.p := rpow_pos_of_pos hℓpos _
  have hℓK : ℓ ≤ K := by omega
  have hlamℓ : 0 < lam ℓ := L.pos (show OnChain (some K) (St.lad ℓ) from hℓK)
  -- the cut balance, on the truncation
  have hbal : D.CutBal S.d lam ((K / 2 : ℕ) : ℕ∞) :=
    D.cutBal_of_setting heps (cutBalanceSeq_trunc L)
  -- the block bounds
  set a : ℝ := lam ℓ * (ℓ : ℝ) ^ D.p / Q with hadef
  set b : ℝ := lam ℓ * ((2 * ℓ : ℕ) : ℝ) ^ D.p * Q with hbdef
  have hapos : 0 < a := by rw [hadef]; positivity
  have hab : ∀ j, ℓ ≤ j → j < 2 * ℓ → a ≤ D.uu lam j ∧ D.uu lam j ≤ b := by
    intro j hj hj2
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have : 1 ≤ j := le_trans hℓ1 hj
      exact_mod_cast this
    have hjp : (0 : ℝ) < (j : ℝ) ^ D.p := rpow_pos_of_pos hjpos _
    have hlow : lam ℓ ≤ Q * lam j :=
      L.block_ratio D heps hℓd hℓ1 h4ℓK hj hj2 le_rfl (by omega)
    have hhigh : lam j ≤ Q * lam ℓ :=
      L.block_ratio D heps hℓd hℓ1 h4ℓK le_rfl (by omega) hj hj2
    have hjℓ : (ℓ : ℝ) ^ D.p ≤ (j : ℝ) ^ D.p := by
      refine Real.rpow_le_rpow hℓpos.le ?_ D.p_pos.le
      exact_mod_cast hj
    have hj2ℓ : (j : ℝ) ^ D.p ≤ ((2 * ℓ : ℕ) : ℝ) ^ D.p := by
      refine Real.rpow_le_rpow hjpos.le ?_ D.p_pos.le
      have : j ≤ 2 * ℓ := by omega
      exact_mod_cast this
    constructor
    · rw [Decay.uu, hadef]
      rw [div_le_iff₀ hQpos]
      calc lam ℓ * (ℓ : ℝ) ^ D.p ≤ (Q * lam j) * (ℓ : ℝ) ^ D.p :=
            mul_le_mul_of_nonneg_right hlow hℓp.le
        _ ≤ (Q * lam j) * (j : ℝ) ^ D.p :=
            mul_le_mul_of_nonneg_left hjℓ (mul_nonneg hQpos.le (L.nonneg _))
        _ = lam j * (j : ℝ) ^ D.p * Q := by ring
    · rw [Decay.uu, hbdef]
      calc lam j * (j : ℝ) ^ D.p ≤ (Q * lam ℓ) * (j : ℝ) ^ D.p :=
            mul_le_mul_of_nonneg_right hhigh hjp.le
        _ ≤ (Q * lam ℓ) * ((2 * ℓ : ℕ) : ℝ) ^ D.p :=
            mul_le_mul_of_nonneg_left hj2ℓ (mul_nonneg hQpos.le hlamℓ.le)
        _ = lam ℓ * ((2 * ℓ : ℕ) : ℝ) ^ D.p * Q := by ring
  refine ⟨a * Z₁, b * Z₂, by positivity, ?_, ?_⟩
  · -- the ratio, `b Z₂ = (Z₂/Z₁) 2^p Q² (a Z₁)`
    have hsplit : ((2 * ℓ : ℕ) : ℝ) ^ D.p = (2 : ℝ) ^ D.p * (ℓ : ℝ) ^ D.p := by
      have hcast : ((2 * ℓ : ℕ) : ℝ) = 2 * (ℓ : ℝ) := by push_cast; ring
      rw [hcast, Real.mul_rpow (by norm_num) hℓpos.le]
    rw [hadef, hbdef, hsplit]
    have hne : Q ≠ 0 := hQpos.ne'
    have hZ1ne : Z₁ ≠ 0 := hZ1.ne'
    apply le_of_eq
    field_simp
  · intro m hm hmK
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : 1 ≤ m := le_trans hℓ1 hm
      exact_mod_cast this
    have hmp : (0 : ℝ) < (m : ℝ) ^ D.p := rpow_pos_of_pos hmpos _
    have hM : (m : ℕ∞) ≤ ((K / 2 : ℕ) : ℕ∞) := by exact_mod_cast hmK
    obtain ⟨h1, h2⟩ := D.decay_block hbal (by omega) hℓ1 hZlo hZhi hapos.le hab hm hM
    rw [Decay.uu] at h1 h2
    have hneg : (m : ℝ) ^ (-D.p) = ((m : ℝ) ^ D.p)⁻¹ := rpow_neg hmpos.le _
    rw [hneg]
    constructor
    · rw [mul_inv_le_iff₀ hmp]; linarith
    · rw [le_mul_inv_iff₀ hmp]; linarith

end Stat

end GFNBounds.Doubling
