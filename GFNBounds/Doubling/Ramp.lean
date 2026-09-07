import GFNBounds.Doubling.Unbounded
import GFNBounds.Doubling.Drift

/-!
# The clipped ramp: the exponent `p = ∞`

**`lem:doubling_ramp`** — `app_doubling.tex:2021–2085`.

> Let `ε(j) > 0`, `ε_max < 1`, let `γ := sup_j (j+1)ε(j)` be finite, and let the loop-closed chain
> be positive recurrent with invariant probability `λ`. Write `V` for the ladder height, put
> `r_N := min(V,N)` and `r̃_N := r_N − Π r_N`. Then `r̃_N ∈ L^∞(λ)` with `Π r̃_N = 0`,
> `‖r̃_N‖_∞ ≥ N/2`, `‖(Id − P⋆)r̃_N‖_∞ ≤ max(1,γ,j̄)`, and consequently the `L^∞` infimum is `0`
> and no bounded `S` on `L^∞(λ)` satisfies `S(Id−P⋆) = Id−Π`. For the family in the standing range
> `γ = c 2^{1−s}` is finite exactly when `s ≥ 1`.

The five cases of the paper's first bullet are `ramp_defect_src`, `ramp_defect_below`,
`ramp_defect_straddle`, `ramp_defect_above` and `ramp_defect_sink`.

## SCOPE (disclosed)

`L^∞(λ)` is not built. Since `λ` is positive at every state of the loop closure
(`lem:doubling_irreducible`), the `L^∞(λ)` norm *is* the supremum over states, and the two
inequalities of `eq:doubling_ramp` are stated in the two forms that supremum consumes: a pointwise
upper bound `∀ x, |·| ≤ max(1,γ,j̄)` for the defect, and an attained lower bound `∃ x, N/2 ≤ |·|`
for the function. `no_bounded_inverse_infty` is then phrased against any `B` bounding an attained
lower bound of `‖f‖` by a uniform upper bound of `‖(Id−P⋆)f‖`, which is exactly what
`‖f‖_∞ ≤ ‖S‖ ‖(Id−P⋆)f‖_∞` supplies. Nothing here depends on the `Lp` layer.

## Hypothesis checklist against `lem:doubling_ramp`

| paper hypothesis | here |
|---|---|
| `ε(j) > 0`, `ε_max < 1` | ✓ carried by `Setting` |
| `γ = sup_j (j+1)ε(j) < ∞` | ✓ carried as `hγ : ∀ j ≥ 1, (j+1)ε(j) ≤ γ` |
| positive recurrence, `λ` | ✓ carried as `Stat S none` |
| `N ≥ d` | ✓ carried (`hN`) |
| `γ = c 2^{1−s}` for the family | ✓ carried (`gamma_family`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting}

/-- `r_N := min(V, N)`, the clipped ramp of `lem:doubling_ramp`. -/
noncomputable def rampFn (N : ℕ) : St → ℝ := fun x => min (height x) (N : ℝ)

@[simp] theorem rampFn_sink (N : ℕ) : rampFn N .sink = 0 := by
  simp [rampFn]

theorem rampFn_lad (N j : ℕ) : rampFn N (.lad j) = min (j : ℝ) (N : ℝ) := rfl

theorem rampFn_lad_le (N j : ℕ) (h : j ≤ N) : rampFn N (.lad j) = (j : ℝ) := by
  rw [rampFn_lad, min_eq_left (by exact_mod_cast h)]

theorem rampFn_lad_ge (N j : ℕ) (h : N ≤ j) : rampFn N (.lad j) = (N : ℝ) := by
  rw [rampFn_lad, min_eq_right (by exact_mod_cast h)]

theorem rampFn_nonneg (N : ℕ) (x : St) : 0 ≤ rampFn N x := by
  rcases x with j | _
  · rw [rampFn_lad]; exact le_min (Nat.cast_nonneg j) (Nat.cast_nonneg N)
  · simp

theorem rampFn_le (N : ℕ) (x : St) : rampFn N x ≤ (N : ℝ) := by
  rcases x with j | _
  · rw [rampFn_lad]; exact min_le_right _ _
  · simp [Nat.cast_nonneg]

theorem rampFn_bounded (N : ℕ) : ∃ C, ∀ x, |rampFn N x| ≤ C :=
  ⟨(N : ℝ), fun x => by rw [abs_of_nonneg (rampFn_nonneg N x)]; exact rampFn_le N x⟩

/-! ## The five cases of the defect -/

section Defect

variable (S) {N : ℕ}

/-- At the source the ramp and its image both vanish. -/
theorem ramp_defect_src (N : ℕ) :
    rampFn N (.lad 0) - pstar S none (rampFn N) (.lad 0) = 0 := by
  simp [rampFn_lad_le N 0 (Nat.zero_le N)]

/-- At the sink the defect is `−j̄`: the target row has mean `j̄` and `r_N = V` on `{1,…,d}`. -/
theorem ramp_defect_sink (hN : S.d ≤ N) :
    rampFn N .sink - pstar S none (rampFn N) .sink = -S.jbar := by
  rw [rampFn_sink, pstar_sink, Setting.jbar]
  have : ∀ k ∈ Finset.Icc 1 S.d, S.row k * rampFn N (.lad k) = (k : ℝ) * S.row k := by
    intro k hk
    have hkd : k ≤ S.d := (Finset.mem_Icc.mp hk).2
    rw [rampFn_lad_le N k (le_trans hkd hN)]; ring
  rw [Finset.sum_congr rfl this]
  ring

/-- Below the clip: the defect is `1 − ε(m)(m+1)`. -/
theorem ramp_defect_below {m : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ N) :
    rampFn N (.lad m) - pstar S none (rampFn N) (.lad m) = 1 - S.eps m * ((m : ℝ) + 1) := by
  rw [pstar_lad_of_hasDouble (cap := none) hm trivial,
    rampFn_lad_le N (2 * m) h2m, rampFn_lad_le N (m - 1) (by omega),
    rampFn_lad_le N m (by omega)]
  have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := hm
    push_cast [Nat.cast_sub this]; ring
  rw [hc]
  push_cast
  ring

/-- Straddling the clip: the defect is `1 − ε(m)(N−m+1)`, and `2m > N` keeps `N−m+1 ≤ m+1`. -/
theorem ramp_defect_straddle {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (h2m : N < 2 * m) :
    rampFn N (.lad m) - pstar S none (rampFn N) (.lad m)
      = 1 - S.eps m * ((N : ℝ) - (m : ℝ) + 1) := by
  rw [pstar_lad_of_hasDouble (cap := none) hm trivial,
    rampFn_lad_ge N (2 * m) (by omega), rampFn_lad_le N (m - 1) (by omega),
    rampFn_lad_le N m hmN]
  have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := hm
    push_cast [Nat.cast_sub this]; ring
  rw [hc]
  ring

/-- Above the clip every image carries the value `N`, so the defect vanishes. -/
theorem ramp_defect_above {m : ℕ} (hm : 1 ≤ m) (hmN : N < m) :
    rampFn N (.lad m) - pstar S none (rampFn N) (.lad m) = 0 := by
  rw [pstar_lad_of_hasDouble (cap := none) hm trivial,
    rampFn_lad_ge N (2 * m) (by omega), rampFn_lad_ge N (m - 1) (by omega),
    rampFn_lad_ge N m (by omega)]
  ring

/-- **`eq:doubling_ramp`, second line.** The defect of the clipped ramp is bounded by
`max(1, γ, j̄)`, uniformly in `N`. -/
theorem ramp_defect_bounded {γ : ℝ} (hγ : ∀ j : ℕ, 1 ≤ j → ((j : ℝ) + 1) * S.eps j ≤ γ)
    (hN : S.d ≤ N) (x : St) :
    |rampFn N x - pstar S none (rampFn N) x| ≤ max 1 (max γ S.jbar) := by
  have hjbar : 0 ≤ S.jbar :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (S.row_nonneg k)
  have hmax1 : (1 : ℝ) ≤ max 1 (max γ S.jbar) := le_max_left _ _
  have hmaxγ : γ ≤ max 1 (max γ S.jbar) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hmaxj : S.jbar ≤ max 1 (max γ S.jbar) := le_trans (le_max_right _ _) (le_max_right _ _)
  rcases x with m | _
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [ramp_defect_src S N, abs_zero]; linarith
    · have hε0 : 0 < S.eps m := S.eps_pos hm
      have hγm : ((m : ℝ) + 1) * S.eps m ≤ γ := hγ m hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rcases le_or_gt (2 * m) N with h2m | h2m
      · rw [ramp_defect_below S hm h2m, abs_le]
        constructor <;> nlinarith
      · rcases le_or_gt m N with hmN | hmN
        · rw [ramp_defect_straddle S hm hmN h2m, abs_le]
          have hNm : (N : ℝ) - (m : ℝ) + 1 ≤ (m : ℝ) + 1 := by
            have : (N : ℝ) < 2 * (m : ℝ) := by exact_mod_cast h2m
            linarith
          have hNm0 : 0 ≤ (N : ℝ) - (m : ℝ) + 1 := by
            have : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
            linarith
          constructor <;> nlinarith
        · rw [ramp_defect_above S hm hmN, abs_zero]; linarith
  · rw [ramp_defect_sink S hN, abs_neg, abs_of_nonneg hjbar]; exact hmaxj

end Defect

/-! ## The centred ramp -/

namespace Stat

variable (L : Stat S none)

/-- `Π r_N`, the `λ`-mean of the clipped ramp. -/
noncomputable def rampMean (N : ℕ) : ℝ := ∑' x, L.lam x * rampFn N x

theorem rampMean_nonneg (N : ℕ) : 0 ≤ L.rampMean N :=
  tsum_nonneg fun x => mul_nonneg (L.nonneg x) (rampFn_nonneg N x)

theorem rampMean_le (N : ℕ) : L.rampMean N ≤ (N : ℝ) := by
  have hb : HasSum (fun x => L.lam x * (N : ℝ)) (N : ℝ) := by
    simpa using L.hasSum_one.mul_right ((N : ℝ))
  have hs : Summable fun x => L.lam x * rampFn N x := L.summable_mul (rampFn_bounded N)
  refine le_trans (Summable.tsum_le_tsum (fun x => ?_) hs hb.summable) (le_of_eq hb.tsum_eq)
  exact mul_le_mul_of_nonneg_left (rampFn_le N x) (L.nonneg x)

/-- `r̃_N := r_N − Π r_N`, the centred clipped ramp. -/
noncomputable def centredRamp (N : ℕ) : St → ℝ := fun x => rampFn N x - L.rampMean N

theorem centredRamp_bounded (N : ℕ) : ∃ C, ∀ x, |L.centredRamp N x| ≤ C := by
  refine ⟨2 * (N : ℝ), fun x => ?_⟩
  have h1 := rampFn_nonneg N x
  have h2 := rampFn_le N x
  have h3 := L.rampMean_nonneg N
  have h4 := L.rampMean_le N
  rw [Stat.centredRamp, abs_le]
  constructor <;> linarith

/-- **`Π r̃_N = 0`.** -/
theorem tsum_centredRamp (N : ℕ) : ∑' x, L.lam x * L.centredRamp N x = 0 := by
  have h : (fun x => L.lam x * L.centredRamp N x)
      = fun x => L.lam x * rampFn N x - L.rampMean N * L.lam x := by
    funext x; rw [Stat.centredRamp]; ring
  have hs : HasSum (fun x => L.lam x * L.centredRamp N x)
      (L.rampMean N - L.rampMean N * 1) := by
    rw [h]
    exact ((L.summable_mul (rampFn_bounded N)).hasSum).sub (L.hasSum_one.mul_left _)
  rw [hs.tsum_eq]; ring

/-- Centring leaves the defect unchanged: `P⋆` fixes the constants. -/
theorem centredRamp_defect (N : ℕ) (x : St) :
    L.centredRamp N x - pstar S none (L.centredRamp N) x
      = rampFn N x - pstar S none (rampFn N) x := by
  have hsplit : L.centredRamp N = rampFn N + fun _ => -L.rampMean N := by
    funext y; rw [Stat.centredRamp]; simp; ring
  rw [hsplit, pstar_add, pstar_const]
  simp only [Pi.add_apply]
  ring

/-- **`eq:doubling_ramp`, first line.** The centred ramp attains `N/2` in absolute value: the two
values `r_N(s₀) = 0` and `r_N(N) = N` are both attained, so one of `Π r_N` and `N − Π r_N` is at
least `N/2`. -/
theorem exists_centredRamp_ge (N : ℕ) : ∃ x : St, (N : ℝ) / 2 ≤ |L.centredRamp N x| := by
  rcases le_or_gt ((N : ℝ) / 2) (L.rampMean N) with h | h
  · refine ⟨.lad 0, ?_⟩
    rw [Stat.centredRamp, rampFn_lad_le N 0 (Nat.zero_le N)]
    rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (L.rampMean_nonneg N)]
    exact h
  · refine ⟨.lad N, ?_⟩
    rw [Stat.centredRamp, rampFn_lad_le N N le_rfl,
      abs_of_nonneg (by linarith [L.rampMean_le N] : (0:ℝ) ≤ (N : ℝ) - L.rampMean N)]
    linarith

/-- **`lem:doubling_ramp`, the conclusion.** No constant `B` bounds an attained lower bound of
`‖f‖_∞` by a uniform upper bound of `‖(Id−P⋆)f‖_∞` over the bounded mean-zero `f`: the clipped
ramps drive the `L^∞` Rayleigh quotient to zero. -/
theorem no_bounded_inverse_infty {γ : ℝ}
    (hγ : ∀ j : ℕ, 1 ≤ j → ((j : ℝ) + 1) * S.eps j ≤ γ) :
    ¬ ∃ B : ℝ, ∀ (f : St → ℝ) (M D : ℝ),
        (∑' x, L.lam x * f x = 0) → (∃ x, M ≤ |f x|) →
        (∀ x, |f x - pstar S none f x| ≤ D) → M ≤ B * D := by
  rintro ⟨B, hB⟩
  set C : ℝ := max 1 (max γ S.jbar) with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
  -- pick `N` past `2·max(B,0)·C` and past `d`
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * (max B 0) * C) (S.d : ℝ))
  have hNd : S.d ≤ N := by
    have : (S.d : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    exact_mod_cast this.le
  have hNB : 2 * (max B 0) * C < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  obtain ⟨x, hx⟩ := L.exists_centredRamp_ge N
  have hdef : ∀ y, |L.centredRamp N y - pstar S none (L.centredRamp N) y| ≤ C := by
    intro y
    rw [L.centredRamp_defect N y]
    exact ramp_defect_bounded S hγ hNd y
  have hmain := hB (L.centredRamp N) ((N : ℝ) / 2) C (L.tsum_centredRamp N) ⟨x, hx⟩ hdef
  have hBle : B ≤ max B 0 := le_max_left _ _
  nlinarith [hmain, hNB, hCpos, hBle]

end Stat

/-- **`lem:doubling_ramp`, last sentence.** For the family, `γ = c·2^{1−s}` bounds `(j+1)ε(j)`
exactly when `s ≥ 1`; the bound is stated, the "exactly when" being the observation that
`(j+1)ε_{c,s}(j) = c(j+1)^{1−s}` is unbounded for `s < 1`. -/
theorem gamma_family {c s : ℝ} (hc : 0 < c) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j) :
    ((j : ℝ) + 1) * epsCS c s j ≤ c * 2 ^ (1 - s) := by
  have hb : (0 : ℝ) < (j : ℝ) + 1 := base_pos j
  have h2 : (2 : ℝ) ≤ (j : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hval : ((j : ℝ) + 1) * epsCS c s j = c * ((j : ℝ) + 1) ^ (1 - s) := by
    rw [epsCS, rpow_sub hb, rpow_one]
    field_simp
  rw [hval]
  have hmono : ((j : ℝ) + 1) ^ (1 - s) ≤ (2 : ℝ) ^ (1 - s) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
  exact mul_le_mul_of_nonneg_left hmono hc.le

end GFNBounds.Doubling
