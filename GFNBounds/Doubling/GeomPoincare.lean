import GFNBounds.Doubling.GeomHardy
import GFNBounds.Doubling.AdjointL2

/-!
# Coercivity of `Id − P⋆` on `ker Π` under a geometric tail

On the loop closure, let the tail `L(k) = Σ_{j ≥ k} λ_j` of the invariant probability be
comparable to the mass at the cut, `L(k) ≤ B λ_k` for every ladder state `k ≥ 1`. Then for every
class `F` of `L²(λ)` of zero mean

  `‖F‖ ≤ K ‖(Id − P⋆)F‖`,   `K = 2B/((1 − √q)²(1 − ε_max)) + 2/λ(s₀)`,  `q = 1 − 1/B`.

The proof is a Poincaré inequality for the part of the Dirichlet form carried by the decrement
edges and the wrap `s₀ → s_f`:

1. `⟨f, (Id − P⋆)f⟩_λ ≥ ½ Σ_x λ_x E_x[(f(X₁) − f(x))²]` (`tsum_pstar_le`, i.e. invariance against
   the unbounded `f²`), and the right side is at least
   `½ (Σ_{k≥1} λ_k(1 − ε_k)(f(k) − f(k−1))² + λ(s₀)(f(s_f) − f(s₀))²)`;
2. the weighted Hardy inequality of `GeomHardy.lean` bounds the ladder part of `‖f − f(s₀)‖²` by
   the decrement part, and the sink carries the wrap term;
3. a mean-zero `f` has `‖f‖² ≤ ‖f − c‖²` for every constant `c`, and Cauchy–Schwarz closes.

## SCOPE (disclosed)

Loop closure only (`cap = none`). The tail hypothesis is carried as `hB`; `GeomOperator.lean`
discharges it for a geometrically decaying doubling probability. Not a statement of the paper:
the geometric row of the policy table, proposed 2026-09-19.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology Finset Real
open scoped InnerProductSpace

variable {S : Setting}

namespace Stat

variable (L : Stat S none)

/-! ## 1. The Dirichlet form, pointwise -/

/-- The one-step variance `E_x[(f(X₁) − f(x))²] = P⋆(f²)(x) − 2f(x)P⋆f(x) + f(x)²`. -/
noncomputable def stepVar (f : St → ℝ) (x : St) : ℝ :=
  pstar S none (fun y => f y ^ 2) x - 2 * f x * pstar S none f x + f x ^ 2

theorem stepVar_nonneg (f : St → ℝ) (x : St) : 0 ≤ stepVar (S := S) f x := by
  have h := sq_pstar_le (S := S) (cap := none) f x
  have : 0 ≤ (pstar S none f x - f x) ^ 2 := sq_nonneg _
  unfold stepVar
  nlinarith

/-- At a ladder state the decrement edge alone contributes `(1 − ε_k)(f(k) − f(k−1))²`. -/
theorem stepVar_lad_ge (f : St → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (1 - S.eps k) * (f (.lad k) - f (.lad (k - 1))) ^ 2 ≤ stepVar (S := S) f (.lad k) := by
  unfold stepVar
  rw [pstar_lad_of_hasDouble hk (hasDouble_none k), pstar_lad_of_hasDouble hk (hasDouble_none k)]
  have he : 0 ≤ S.eps k := (S.eps_pos hk).le
  have : 0 ≤ S.eps k * (f (.lad (2 * k)) - f (.lad k)) ^ 2 := mul_nonneg he (sq_nonneg _)
  nlinarith

/-- At the source the wrap `s₀ → s_f` contributes `(f(s_f) − f(s₀))²`. -/
theorem stepVar_src (f : St → ℝ) :
    stepVar (S := S) f (.lad 0) = (f .sink - f (.lad 0)) ^ 2 := by
  unfold stepVar
  simp only [pstar_src]
  ring

/-! ## 2. The Dirichlet form, summed -/

variable {L}

theorem summable_lam_sq_pstar {f : St → ℝ} (hf2 : Summable fun x => L.lam x * f x ^ 2) :
    Summable fun x => L.lam x * pstar S none (fun y => f y ^ 2) x :=
  (L.tsum_pstar_le (fun x => sq_nonneg (f x)) hf2).1

theorem summable_lam_mul_defect {f : St → ℝ} (hf2 : Summable fun x => L.lam x * f x ^ 2) :
    Summable fun x => L.lam x * f x * (f x - pstar S none f x) := by
  have hP := summable_lam_sq_pstar hf2
  refine Summable.of_norm_bounded ((hf2.mul_left (3 / 2)).add (hP.mul_left (1 / 2))) fun x => ?_
  have hl := L.nonneg x
  have hj := sq_pstar_le (S := S) (cap := none) f x
  rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg hl]
  have hab : |f x * (f x - pstar S none f x)| ≤ 3 / 2 * f x ^ 2 + 1 / 2 * (pstar S none f x) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (f x + pstar S none f x),
      sq_nonneg (f x - pstar S none f x), sq_nonneg (2 * f x - pstar S none f x)]
  calc L.lam x * |f x * (f x - pstar S none f x)|
      ≤ L.lam x * (3 / 2 * f x ^ 2 + 1 / 2 * pstar S none (fun y => f y ^ 2) x) := by
        refine mul_le_mul_of_nonneg_left (hab.trans ?_) hl
        linarith
    _ = 3 / 2 * (L.lam x * f x ^ 2) + 1 / 2 * (L.lam x * pstar S none (fun y => f y ^ 2) x) := by
        ring

theorem summable_lam_stepVar {f : St → ℝ} (hf2 : Summable fun x => L.lam x * f x ^ 2) :
    Summable fun x => L.lam x * stepVar (S := S) f x := by
  have hP := summable_lam_sq_pstar hf2
  have hD := summable_lam_mul_defect hf2
  -- `λ V = λP⋆(f²) − λf² + 2 λ f (f − P⋆f)`
  have heq : (fun x => L.lam x * stepVar (S := S) f x) = fun x =>
      L.lam x * pstar S none (fun y => f y ^ 2) x - L.lam x * f x ^ 2
        + 2 * (L.lam x * f x * (f x - pstar S none f x)) := by
    funext x; unfold stepVar; ring
  rw [heq]
  exact (hP.sub hf2).add (hD.mul_left 2)

/-- **The Dirichlet form is dominated by `2⟨f, (Id − P⋆)f⟩_λ`.** -/
theorem tsum_stepVar_le {f : St → ℝ} (hf2 : Summable fun x => L.lam x * f x ^ 2) :
    ∑' x, L.lam x * stepVar (S := S) f x
      ≤ 2 * ∑' x, L.lam x * f x * (f x - pstar S none f x) := by
  have hP := summable_lam_sq_pstar hf2
  have hD := summable_lam_mul_defect hf2
  have hle := (L.tsum_pstar_le (fun x => sq_nonneg (f x)) hf2).2
  have heq : (fun x => L.lam x * stepVar (S := S) f x) = fun x =>
      L.lam x * pstar S none (fun y => f y ^ 2) x - L.lam x * f x ^ 2
        + 2 * (L.lam x * f x * (f x - pstar S none f x)) := by
    funext x; unfold stepVar; ring
  rw [heq, Summable.tsum_add (hP.sub hf2) (hD.mul_left 2), Summable.tsum_sub hP hf2, tsum_mul_left]
  linarith

/-- **The decrement part of the Dirichlet form, partial sums.** -/
theorem dirichlet_partial {f : St → ℝ} (hf2 : Summable fun x => L.lam x * f x ^ 2) (N : ℕ) :
    ∑ k ∈ Icc 1 N, L.lam (.lad k) * (1 - S.eps k) * (f (.lad k) - f (.lad (k - 1))) ^ 2
      + L.lam (.lad 0) * (f .sink - f (.lad 0)) ^ 2
      ≤ 2 * ∑' x, L.lam x * f x * (f x - pstar S none f x) := by
  have hV := summable_lam_stepVar hf2
  have hVnn : ∀ x, 0 ≤ L.lam x * stepVar (S := S) f x :=
    fun x => mul_nonneg (L.nonneg x) (stepVar_nonneg f x)
  have hinj : Function.Injective (fun k : ℕ => (St.lad k : St)) := fun a b h => by simpa using h
  -- the ladder part of the tsum
  have hlad : ∑' k : ℕ, L.lam (.lad k) * stepVar (S := S) f (.lad k)
      ≤ ∑' x, L.lam x * stepVar (S := S) f x :=
    tsum_comp_le_tsum_of_inj hV hVnn hinj
  have hladS : Summable fun k : ℕ => L.lam (.lad k) * stepVar (S := S) f (.lad k) :=
    hV.comp_injective hinj
  have hfin : ∑ k ∈ range (N + 1), L.lam (.lad k) * stepVar (S := S) f (.lad k)
      ≤ ∑' k : ℕ, L.lam (.lad k) * stepVar (S := S) f (.lad k) :=
    hladS.sum_le_tsum _ fun k _ => hVnn _
  have hsplit : ∑ k ∈ range (N + 1), L.lam (.lad k) * stepVar (S := S) f (.lad k)
      = L.lam (.lad 0) * stepVar (S := S) f (.lad 0)
        + ∑ k ∈ Icc 1 N, L.lam (.lad k) * stepVar (S := S) f (.lad k) := by
    rw [range_eq_Ico, ← Finset.Ico_add_one_right_eq_Icc, sum_eq_sum_Ico_succ_bot (by omega)]
  have hterm : ∀ k ∈ Icc 1 N,
      L.lam (.lad k) * (1 - S.eps k) * (f (.lad k) - f (.lad (k - 1))) ^ 2
        ≤ L.lam (.lad k) * stepVar (S := S) f (.lad k) := by
    intro k hk
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (stepVar_lad_ge f (mem_Icc.mp hk).1) (L.nonneg _)
  have h1 := sum_le_sum hterm
  have h2 := tsum_stepVar_le (L := L) hf2
  rw [stepVar_src] at hsplit
  linarith

/-! ## 3. The Poincaré inequality -/

/-- `Σ_{k=1}^{x} (f(k) − f(k−1)) = f(x) − f(0)`. -/
theorem sum_Icc_telescope (f : St → ℝ) (x : ℕ) :
    ∑ k ∈ Icc 1 x, (f (.lad k) - f (.lad (k - 1))) = f (.lad x) - f (.lad 0) := by
  induction x with
  | zero => simp
  | succ x ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- **The Poincaré inequality.** Under `L(k) ≤ B λ_k`, a mean-zero `f` of `L²(λ)` has
`Σ λ f² ≤ K Σ λ f(f − P⋆f)`. -/
theorem poincare {B : ℝ} (hB : ∀ k, 1 ≤ k → L.tailMass k ≤ B * L.lam (.lad k))
    {f : St → ℝ} (hf2 : Summable fun x => L.lam x * f x ^ 2)
    (hf1 : Summable fun x => L.lam x * f x) (hmean : ∑' x, L.lam x * f x = 0) :
    ∑' x, L.lam x * f x ^ 2
      ≤ (2 * B / ((1 - Real.sqrt (1 - 1 / B)) ^ 2 * (1 - S.epsMax)) + 2 / L.lam (.lad 0))
        * ∑' x, L.lam x * f x * (f x - pstar S none f x) := by
  set E := ∑' x, L.lam x * f x * (f x - pstar S none f x) with hE
  set c := f (.lad 0) with hc
  set q := 1 - 1 / B with hq
  have hlam : ∀ k, 0 < L.lam (.lad k) := fun k => L.pos trivial
  have hT : ∀ k, 0 < L.tailMass k := fun k => L.tailMass_pos k
  have hB1 : 1 ≤ B := by
    have h1 := hB 1 le_rfl
    have h2 : L.lam (.lad 1) ≤ L.tailMass 1 := by
      have := L.tailMass_succ 1; have := (hT 2).le; linarith
    have := hlam 1
    by_contra hlt; push Not at hlt; nlinarith
  have hBpos : 0 < B := by linarith
  have hq0 : 0 ≤ q := by rw [hq, sub_nonneg, div_le_one hBpos]; exact hB1
  have hq1 : q < 1 := by rw [hq]; have : 0 < 1 / B := by positivity
                         linarith
  have hTq : ∀ k, 1 ≤ k → L.tailMass (k + 1) ≤ q * L.tailMass k := by
    intro k hk
    have hs := L.tailMass_succ k
    have hb := hB k hk
    rw [hq, sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
    have : L.tailMass k / B ≤ L.lam (.lad k) := by rw [div_le_iff₀ hBpos]; linarith
    linarith
  have hlamT : ∀ k, 1 ≤ k → L.lam (.lad k) ≤ L.tailMass k := by
    intro k _; have := L.tailMass_succ k; have := (hT (k + 1)).le; linarith
  have h1e : 0 < 1 - S.epsMax := by linarith [S.epsMax_lt_one]
  have h1r : 0 < 1 - Real.sqrt q := by
    have : Real.sqrt q < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hq1
    linarith
  set H := B / (1 - Real.sqrt q) ^ 2 with hH
  have hHnn : 0 ≤ H := by positivity
  have hD := dirichlet_partial (L := L) hf2
  -- the ladder part of `‖f − c‖²`
  have hladder : ∀ N, ∑ x ∈ range N, L.lam (.lad x) * (f (.lad x) - c) ^ 2
      ≤ 2 * H / (1 - S.epsMax) * E := by
    intro N
    rcases N with _ | N
    · simp only [range_zero, sum_empty]
      have hE0 : 0 ≤ E := by
        have := hD 0
        rw [Finset.Icc_eq_empty (by omega), sum_empty, zero_add] at this
        have : 0 ≤ L.lam (.lad 0) * (f .sink - f (.lad 0)) ^ 2 :=
          mul_nonneg (hlam 0).le (sq_nonneg _)
        linarith
      positivity
    · have hsplit : ∑ x ∈ range (N + 1), L.lam (.lad x) * (f (.lad x) - c) ^ 2
          = ∑ x ∈ Icc 1 N, L.lam (.lad x) * (f (.lad x) - c) ^ 2 := by
        rw [range_eq_Ico, ← Finset.Ico_add_one_right_eq_Icc, sum_eq_sum_Ico_succ_bot (by omega)]
        simp [hc]
      have hhardy := Hardy.hardy (lam := fun k => L.lam (.lad k)) (T := L.tailMass)
        (D := fun k => f (.lad k) - f (.lad (k - 1))) hq0 hq1 (fun k _ => hT k) hTq
        (fun k => (hlam k).le) hlamT hB N
      simp only [sum_Icc_telescope] at hhardy
      have hmu : ∑ k ∈ Icc 1 N, L.lam (.lad k) * (f (.lad k) - f (.lad (k - 1))) ^ 2
          ≤ 1 / (1 - S.epsMax) * ∑ k ∈ Icc 1 N,
              L.lam (.lad k) * (1 - S.eps k) * (f (.lad k) - f (.lad (k - 1))) ^ 2 := by
        rw [mul_sum]
        refine sum_le_sum fun k hk => ?_
        have hk1 := (mem_Icc.mp hk).1
        have he : S.eps k ≤ S.epsMax := S.eps_le hk1
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h1e]
        have : 0 ≤ L.lam (.lad k) * (f (.lad k) - f (.lad (k - 1))) ^ 2 :=
          mul_nonneg (hlam k).le (sq_nonneg _)
        nlinarith
      have hwrap : 0 ≤ L.lam (.lad 0) * (f .sink - f (.lad 0)) ^ 2 :=
        mul_nonneg (hlam 0).le (sq_nonneg _)
      have hDN := hD N
      rw [hsplit, hc]
      calc ∑ x ∈ Icc 1 N, L.lam (.lad x) * (f (.lad x) - f (.lad 0)) ^ 2
          ≤ H * ∑ k ∈ Icc 1 N, L.lam (.lad k) * (f (.lad k) - f (.lad (k - 1))) ^ 2 := hhardy
        _ ≤ H * (1 / (1 - S.epsMax) * (2 * E)) := by
            gcongr
            exact hmu.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        _ = 2 * H / (1 - S.epsMax) * E := by ring
  -- summability of the pieces
  have hg2 : Summable fun x => L.lam x * (f x - c) ^ 2 := by
    have heq : (fun x => L.lam x * (f x - c) ^ 2)
        = fun x => L.lam x * f x ^ 2 - 2 * c * (L.lam x * f x) + c ^ 2 * L.lam x := by
      funext x; ring
    rw [heq]; exact (hf2.sub (hf1.mul_left _)).add (L.summable.mul_left _)
  have hinj : Function.Injective (fun k : ℕ => (St.lad k : St)) := fun a b h => by simpa using h
  have hladS : Summable fun k : ℕ => L.lam (.lad k) * (f (.lad k) - c) ^ 2 :=
    hg2.comp_injective hinj
  have hladT : ∑' k : ℕ, L.lam (.lad k) * (f (.lad k) - c) ^ 2 ≤ 2 * H / (1 - S.epsMax) * E :=
    Real.tsum_le_of_sum_range_le (fun k => mul_nonneg (hlam k).le (sq_nonneg _)) hladder
  have hst := hasSum_st (g := fun x => L.lam x * (f x - c) ^ 2) hladS.hasSum
  -- the sink
  have hsink : L.lam .sink * (f .sink - c) ^ 2 ≤ 2 / L.lam (.lad 0) * E := by
    have hs1 : L.lam .sink ≤ 1 := by
      rw [← L.total]; exact L.summable.le_tsum _ fun x _ => L.nonneg x
    have hw := hD 0
    rw [Finset.Icc_eq_empty (by omega), sum_empty, zero_add] at hw
    rw [hc]
    have hl0 := hlam 0
    rw [div_mul_eq_mul_div, le_div_iff₀ hl0]
    have h2 : 0 ≤ (f .sink - f (.lad 0)) ^ 2 := sq_nonneg _
    have h3 := mul_le_mul_of_nonneg_right hs1 (mul_nonneg h2 hl0.le)
    nlinarith
  -- `Σ λ f² ≤ Σ λ (f − c)²` for mean-zero `f`
  have hshift : ∑' x, L.lam x * f x ^ 2 ≤ ∑' x, L.lam x * (f x - c) ^ 2 := by
    have heq : (fun x => L.lam x * (f x - c) ^ 2)
        = fun x => L.lam x * f x ^ 2 - 2 * c * (L.lam x * f x) + c ^ 2 * L.lam x := by
      funext x; ring
    rw [heq, Summable.tsum_add (hf2.sub (hf1.mul_left _)) (L.summable.mul_left _),
      Summable.tsum_sub hf2 (hf1.mul_left _), tsum_mul_left, tsum_mul_left, hmean, L.total]
    nlinarith [sq_nonneg c]
  rw [hst.tsum_eq] at hshift
  calc ∑' x, L.lam x * f x ^ 2
      ≤ ∑' k : ℕ, L.lam (.lad k) * (f (.lad k) - c) ^ 2 + L.lam .sink * (f .sink - c) ^ 2 :=
        hshift
    _ ≤ 2 * H / (1 - S.epsMax) * E + 2 / L.lam (.lad 0) * E := add_le_add hladT hsink
    _ = (2 * B / ((1 - Real.sqrt q) ^ 2 * (1 - S.epsMax)) + 2 / L.lam (.lad 0)) * E := by
        rw [hH]; field_simp

/-! ## 4. Coercivity on `ker Π` -/

variable (L)

/-- The coercivity constant. -/
noncomputable def coerK (B : ℝ) : ℝ :=
  2 * B / ((1 - Real.sqrt (1 - 1 / B)) ^ 2 * (1 - S.epsMax)) + 2 / L.lam (.lad 0)

/-- **Coercivity of `Id − P⋆` on `ker Π`.** Under `L(k) ≤ B λ_k`, every mean-zero class `F` of
`L²(λ)` has `‖F‖ ≤ K‖(Id − P⋆)F‖`. -/
theorem coercive {B : ℝ} (hB : ∀ k, 1 ≤ k → L.tailMass k ≤ B * L.lam (.lad k))
    {F : Lp ℝ 2 L.mu} (hF : F ∈ L.kerPi) : ‖F‖ ≤ L.coerK B * ‖L.defect F‖ := by
  set f : St → ℝ := ⇑F with hfdef
  have hmem : MemLp f 2 L.mu := Lp.memLp F
  have hf2 : Summable fun x => L.lam x * f x ^ 2 := by
    have := L.memLp_two_iff.mp hmem
    exact this.congr fun x => by rw [abs_rpow_two']; ring
  have hf1 : Summable fun x => L.lam x * f x := (L.summable_lam_abs hmem).of_norm_bounded
    (fun x => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (L.nonneg x)])
  have hmean : ∑' x, L.lam x * f x = 0 := L.mem_kerPi_iff.mp hF
  have hP := poincare (L := L) hB hf2 hf1 hmean
  have hnorm : ‖F‖ ^ 2 = ∑' x, L.lam x * f x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L.inner_eq_tsum]
    exact tsum_congr fun x => by ring
  have hinner : ⟪F, L.defect F⟫_ℝ = ∑' x, L.lam x * f x * (f x - pstar S none f x) :=
    L.inner_eq_tsum_of_ae (Filter.EventuallyEq.refl _ _) (L.coeFn_defect F)
  have hcs : ⟪F, L.defect F⟫_ℝ ≤ ‖F‖ * ‖L.defect F‖ := real_inner_le_norm _ _
  have hK : 0 ≤ L.coerK B := by
    have hE : 0 ≤ ∑' x, L.lam x * f x * (f x - pstar S none f x) := by
      have := tsum_stepVar_le (L := L) hf2
      have : 0 ≤ ∑' x, L.lam x * stepVar (S := S) f x :=
        tsum_nonneg fun x => mul_nonneg (L.nonneg x) (stepVar_nonneg f x)
      linarith
    by_contra hneg; push Not at hneg
    -- `K < 0` would force `‖F‖² ≤ K·E ≤ 0` for every `F`, but the bound is only used below
    exact absurd hneg (not_lt.mpr (by
      unfold coerK
      have h0 := L.pos (x := St.lad 0) trivial
      have h1 : 0 < 1 - S.epsMax := by linarith [S.epsMax_lt_one]
      by_cases hB0 : 0 ≤ B
      · positivity
      · -- `B < 0` is impossible: `λ_1 ≤ L(1) ≤ Bλ_1`
        exfalso
        have h1' := hB 1 le_rfl
        have := L.tailMass_pos 1
        have := L.pos (x := St.lad 1) trivial
        nlinarith))
  have hsq : ‖F‖ ^ 2 ≤ L.coerK B * (‖F‖ * ‖L.defect F‖) := by
    rw [hnorm]
    calc ∑' x, L.lam x * f x ^ 2 ≤ L.coerK B * ∑' x, L.lam x * f x * (f x - pstar S none f x) :=
          hP
      _ = L.coerK B * ⟪F, L.defect F⟫_ℝ := by rw [hinner]
      _ ≤ L.coerK B * (‖F‖ * ‖L.defect F‖) := mul_le_mul_of_nonneg_left hcs hK
  rcases (norm_nonneg F).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hK (norm_nonneg _)
  · have : ‖F‖ * ‖F‖ ≤ ‖F‖ * (L.coerK B * ‖L.defect F‖) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

end Stat

end GFNBounds.Doubling
