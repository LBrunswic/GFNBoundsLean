import GFNBounds.Doubling.LpLayer

/-!
# `P⋆` is a contraction of `L^p(λ)` at every `p ∈ [1,∞]`

**`lem:doubling_operator`(1), first clause** — `app_doubling.tex:166–262`.

> `P⋆` is a contraction of `L^p(λ)` for every `p ∈ [1,+∞]` and is the `L^2(λ)`-adjoint of `P`,
> so that `‖P⋆^n − Π‖_{L²(λ)} = β̂_n` for every `n ≥ 0`.

The paper's proof of the first clause, verbatim:

> Let `v ∈ L^p(λ)` with `p < +∞`. Jensen's inequality for the probability `T(x,·)` and the convex
> `t ↦ |t|^p` gives `|(P⋆v)(x)|^p ≤ (P⋆(|v|^p))(x)` for `λ`-almost every `x`, and `λT = λ` gives
> `∫P⋆(|v|^p)dλ = ∫|v|^p d(λT) = ‖v‖^p_{L^p(λ)}`: hence `‖P⋆v‖_{L^p(λ)} ≤ ‖v‖_{L^p(λ)}`. For
> `p = +∞` the set `Z := {|v| > ‖v‖_{L^∞(λ)}}` is `λ`-null, so `T(x,Z) = 0` and
> `|(P⋆v)(x)| ≤ ‖v‖_{L^∞(λ)}` for `λ`-almost every `x`.

Both halves are proved here, in the `eLpNorm` form: `Stat.eLpNorm_pstar_le` at finite `p`,
`Stat.eLpNormEssSup_pstar_le` at `p = ∞`, and `Stat.eLpNorm_pstar_le_of_memLp` for the two
together.

## The three ingredients

**Jensen is pointwise and finite.** `pstar` is a *finite* convex combination at every state — the
one-step law has at most `max(2, d)` atoms — so `abs_rpow_pstar_le` is a three-case split, the
ladder case being two-point convexity of `t ↦ t^p` on `[0,∞)` (`convexOn_rpow`) and the sink case
`Real.rpow_arith_mean_le_arith_mean_rpow` against the target row, whose weights sum to `1` by
`Setting.row_sum`. No measure theory enters, and the inequality holds at **every** state, not just
almost everywhere.

**Invariance is `Stat.tsum_pstar_le`.** `Stat.inv` is available against bounded test functions
only, and `|v|^p` is unbounded; the truncation argument of `LpLayer` supplies the inequality
`∫P⋆g dλ ≤ ∫g dλ` at every non-negative `g` with `∫g dλ < ∞`, which is the direction Jensen
needs. The paper has an equality there; an inequality suffices and is what is proved.

**The `p = ∞` case is `pstar_bounded` read on the chain.** `Stat.ae_iff_onChain` turns the paper's
`λ`-null set `Z` into the off-chain states, and `pstar_bounded_onChain` — `pstar_bounded` with its
hypothesis and conclusion restricted to the chain — is the transition step `T(x,Z) = 0`. It is
here that `RowOnChain` is consumed, exactly as in `LpLayer`: the sink reads the target row, and on
the truncation at `K < d` those states carry no `λ`-mass.

## SCOPE (disclosed)

* **The first clause of `lem:doubling_operator`(1) only.** The adjoint clause `P⋆ = P*` is *not*
  in this file: it needs the density action `P`, which is modelled in `Adjoint.lean`. The
  consequence `‖P⋆^n − Π‖ = β̂_n` therefore is not here either.
* **The contraction is proved as an inequality between `eLpNorm`s, not as a
  `ContinuousLinearMap` of norm `≤ 1`.** The only `p` at which `P⋆` is packaged as a bounded
  operator is `p = 2` (`LpLayer.Stat.pstarL2`), which is the one `lem:doubling_operator`(3) is
  instantiated at; the same `LinearMap.mkContinuous` construction would go through at every
  `p` with `Fact (1 ≤ p)` on the strength of `eLpNorm_pstar_le`, but it is **not built here** and
  is not claimed.
* **The contraction at finite `p` needs `MemLp f p μ`** to state `eLpNorm_pstar_le` — without it
  both sides are `∞` and the inequality is vacuously true, but the `mass` layer is where the
  content is and it is stated there (`Stat.mass_pstar_le`) with the summability hypothesis the
  paper's `v ∈ L^p(λ)` supplies.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `T` a Markov kernel with invariant probability `λ` | ✓ carried (`Stat`) |
| `p ∈ [1,∞)` | ✓ carried (`1 ≤ p`, `p ≠ ∞`) |
| `p = ∞` | ✓ carried (`eLpNormEssSup_pstar_le`) |
| `v ∈ L^p(λ)` | ✓ carried |
| — | ⚠ **added**: `RowOnChain S cap` in the `p = ∞` and `CLM` statements, as in `LpLayer` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology Real
open scoped ENNReal NNReal

variable {S : Setting} {cap : Option ℕ}

/-! ## 1. Jensen, pointwise -/

/-- Two-point convexity of `t ↦ t^p` on `[0,∞)`, composed with the triangle inequality: this is
the ladder case of `abs_rpow_pstar_le`. -/
theorem abs_rpow_add_le {a b s t p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hp : 1 ≤ p) : |a * s + b * t| ^ p ≤ a * |s| ^ p + b * |t| ^ p := by
  have h1 : |a * s + b * t| ≤ a * |s| + b * |t| := by
    calc |a * s + b * t| ≤ |a * s| + |b * t| := abs_add_le _ _
      _ = a * |s| + b * |t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h2 : |a * s + b * t| ^ p ≤ (a * |s| + b * |t|) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) h1 (by linarith)
  have h3 : (a * |s| + b * |t|) ^ p ≤ a * |s| ^ p + b * |t| ^ p := by
    have := (convexOn_rpow hp).2 (Set.mem_Ici.mpr (abs_nonneg s)) (Set.mem_Ici.mpr (abs_nonneg t))
      ha hb hab
    simpa only [smul_eq_mul] using this
  linarith

/-- **Jensen for the one-step law, at every state.** `|P⋆v|^p ≤ P⋆(|v|^p)` for `p ≥ 1`.

The one-step law is a finite convex combination at each of the three kinds of state, so this is
pointwise — the paper's "for `λ`-almost every `x`" is not needed. -/
theorem abs_rpow_pstar_le {p : ℝ} (hp : 1 ≤ p) (f : St → ℝ) (x : St) :
    |pstar S cap f x| ^ p ≤ pstar S cap (fun y => |f y| ^ p) x := by
  rcases x with (_ | j) | _
  · exact le_of_eq rfl
  · by_cases hD : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, hD, if_true]
      have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
      have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
      exact abs_rpow_add_le h1 h2 (by ring) hp
    · simp only [pstar_lad_succ, hD, if_false]
      exact le_rfl
  · simp only [pstar_sink]
    have hw : ∀ k ∈ Finset.Icc 1 S.d, 0 ≤ S.row k := fun k _ => S.row_nonneg k
    have hz : ∀ k ∈ Finset.Icc 1 S.d, 0 ≤ |f (St.lad k)| := fun k _ => abs_nonneg _
    have h1 : |∑ k ∈ Finset.Icc 1 S.d, S.row k * f (St.lad k)|
        ≤ ∑ k ∈ Finset.Icc 1 S.d, S.row k * |f (St.lad k)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun k _ => by
        rw [abs_mul, abs_of_nonneg (S.row_nonneg k)]
    calc |∑ k ∈ Finset.Icc 1 S.d, S.row k * f (St.lad k)| ^ p
        ≤ (∑ k ∈ Finset.Icc 1 S.d, S.row k * |f (St.lad k)|) ^ p :=
          Real.rpow_le_rpow (abs_nonneg _) h1 (by linarith)
      _ ≤ ∑ k ∈ Finset.Icc 1 S.d, S.row k * |f (St.lad k)| ^ p :=
          Real.rpow_arith_mean_le_arith_mean_rpow (Finset.Icc 1 S.d) S.row
            (fun k => |f (St.lad k)|) hw S.row_sum hz hp

/-! ## 2. The `p`-th power mass contracts -/

namespace Stat

variable (L : Stat S cap)

/-- **`‖P⋆v‖_{L^p(λ)} ≤ ‖v‖_{L^p(λ)}` on the plain-real layer**, at every `p ≥ 1`: Jensen
pointwise, then invariance against `|v|^p`. -/
theorem mass_pstar_le {p : ℝ} (hp : 1 ≤ p) {f : St → ℝ}
    (hs : Summable fun x => |f x| ^ p * L.lam x) :
    L.mass p (pstar S cap f) ≤ L.mass p f := by
  have hsum' : Summable fun x => L.lam x * |f x| ^ p := hs.congr fun x => mul_comm _ _
  obtain ⟨hsummP, hle⟩ :=
    L.tsum_pstar_le (g := fun y => |f y| ^ p) (fun y => Real.rpow_nonneg (abs_nonneg _) p) hsum'
  have hstep : ∀ x, L.lam x * |pstar S cap f x| ^ p
      ≤ L.lam x * pstar S cap (fun y => |f y| ^ p) x := fun x =>
    mul_le_mul_of_nonneg_left (abs_rpow_pstar_le hp f x) (L.nonneg x)
  have hLHS : Summable fun x => L.lam x * |pstar S cap f x| ^ p :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg (L.nonneg x) (Real.rpow_nonneg (abs_nonneg _) p)) hstep hsummP
  calc L.mass p (pstar S cap f) = ∑' x, L.lam x * |pstar S cap f x| ^ p :=
        tsum_congr fun x => mul_comm _ _
    _ ≤ ∑' x, L.lam x * pstar S cap (fun y => |f y| ^ p) x := hLHS.tsum_le_tsum hstep hsummP
    _ ≤ ∑' x, L.lam x * |f x| ^ p := hle
    _ = L.mass p f := tsum_congr fun x => mul_comm _ _

/-- `1 ≤ p.toReal` for a finite `p ≥ 1`. -/
theorem one_le_toReal {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞) : 1 ≤ p.toReal := by
  have := ENNReal.toReal_mono hpt hp1
  simpa using this

/-- `P⋆` maps `L^p(μ)` into itself, at every finite `p ≥ 1`. -/
theorem memLp_pstar {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞) {f : St → ℝ} (hf : MemLp f p L.mu) :
    MemLp (pstar S cap f) p L.mu := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp1; exact absurd hp1 (by simp)
  have hr : 1 ≤ p.toReal := one_le_toReal hp1 hpt
  rw [L.memLp_iff hp0 hpt] at hf ⊢
  have hsum' : Summable fun x => L.lam x * |f x| ^ p.toReal := hf.congr fun x => mul_comm _ _
  obtain ⟨hsummP, -⟩ :=
    L.tsum_pstar_le (g := fun y => |f y| ^ p.toReal)
      (fun y => Real.rpow_nonneg (abs_nonneg _) _) hsum'
  refine Summable.of_nonneg_of_le
    (fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (L.nonneg x)) (fun x => ?_) hsummP
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_rpow_pstar_le hr f x) (L.nonneg x)

/-- **`lem:doubling_operator`(1), first clause, at finite `p`.** `P⋆` is a contraction of
`L^p(μ)` for every `p ∈ [1,∞)`. -/
theorem eLpNorm_pstar_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞) {f : St → ℝ}
    (hf : MemLp f p L.mu) : eLpNorm (pstar S cap f) p L.mu ≤ eLpNorm f p L.mu := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp1; exact absurd hp1 (by simp)
  have hr : 1 ≤ p.toReal := one_le_toReal hp1 hpt
  have hr0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hr
  have hPf := L.memLp_pstar hp1 hpt hf
  have hsf : Summable fun x => |f x| ^ p.toReal * L.lam x := (L.memLp_iff hp0 hpt).mp hf
  have hsP : Summable fun x => |pstar S cap f x| ^ p.toReal * L.lam x :=
    (L.memLp_iff hp0 hpt).mp hPf
  have hmass : L.mass p.toReal (pstar S cap f) ≤ L.mass p.toReal f := L.mass_pstar_le hr hsf
  have hpow : (eLpNorm (pstar S cap f) p L.mu).toReal ^ p.toReal
      ≤ (eLpNorm f p L.mu).toReal ^ p.toReal := by
    rw [L.toReal_eLpNorm_rpow _ hp0 hpt hsP, L.toReal_eLpNorm_rpow _ hp0 hpt hsf]
    exact hmass
  have hle : (eLpNorm (pstar S cap f) p L.mu).toReal ≤ (eLpNorm f p L.mu).toReal :=
    (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg ENNReal.toReal_nonneg hr0).mp hpow
  exact (ENNReal.toReal_le_toReal hPf.eLpNorm_ne_top hf.eLpNorm_ne_top).mp hle

end Stat

/-! ## 3. The `p = ∞` case -/

/-- **`pstar_bounded`, read on the chain.** A bound holding at every state of the chain is
inherited by `P⋆` at every state of the chain.

This is the paper's `T(x,Z) = 0` for the `λ`-null set `Z := {|v| > ‖v‖_∞}`: on this graph the
one-step law out of an on-chain state charges on-chain states only, which for the sink is exactly
`RowOnChain`. -/
theorem pstar_bounded_onChain (hrow : RowOnChain S cap) {f : St → ℝ} {C : ℝ}
    (hC : ∀ x, OnChain cap x → |f x| ≤ C) {x : St} (hx : OnChain cap x) :
    |pstar S cap f x| ≤ C := by
  rcases x with (_ | j) | _
  · exact hC _ (onChain_sink cap)
  · by_cases hD : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, hD, if_true]
      have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
      have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
      have hb1 : |f (St.lad (2 * (j + 1)))| ≤ C := hC _ (onChain_double hD)
      have hb2 : |f (St.lad j)| ≤ C := hC _ (onChain_lad_of_succ hx)
      calc |S.eps (j+1) * f (.lad (2*(j+1))) + (1 - S.eps (j+1)) * f (.lad j)|
          ≤ |S.eps (j+1) * f (.lad (2*(j+1)))| + |(1 - S.eps (j+1)) * f (.lad j)| :=
            abs_add_le _ _
        _ ≤ S.eps (j+1) * C + (1 - S.eps (j+1)) * C := by
            rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
            gcongr
        _ = C := by ring
    · simp only [pstar_lad_succ, hD, if_false]
      exact hC _ (onChain_lad_of_succ hx)
  · simp only [pstar_sink]
    calc |∑ k ∈ Finset.Icc 1 S.d, S.row k * f (St.lad k)|
        ≤ ∑ k ∈ Finset.Icc 1 S.d, |S.row k * f (St.lad k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 S.d, S.row k * C := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_Icc.mp hk
          rw [abs_mul, abs_of_nonneg (S.row_nonneg k)]
          exact mul_le_mul_of_nonneg_left (hC _ (hrow k hk'.1 hk'.2)) (S.row_nonneg k)
      _ = C := by rw [← Finset.sum_mul, S.row_sum, one_mul]

namespace Stat

variable (L : Stat S cap)

/-- **`lem:doubling_operator`(1), first clause, at `p = ∞`.** `P⋆` is a contraction of
`L^∞(μ)`. -/
theorem eLpNormEssSup_pstar_le (hrow : RowOnChain S cap) (f : St → ℝ) :
    eLpNormEssSup (pstar S cap f) L.mu ≤ eLpNormEssSup f L.mu := by
  set M := eLpNormEssSup f L.mu with hM
  by_cases hMtop : M = ∞
  · rw [hMtop]; exact le_top
  have hae : ∀ x, OnChain cap x → ‖f x‖ₑ ≤ M := L.ae_iff_onChain.mp ae_le_eLpNormEssSup
  have hbd : ∀ x, OnChain cap x → |f x| ≤ M.toReal := by
    intro x hx
    have h := hae x hx
    rw [Real.enorm_eq_ofReal_abs] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hMtop).mp h
  refine eLpNormEssSup_le_of_ae_enorm_bound (C := M) ?_
  refine L.ae_iff_onChain.mpr fun x hx => ?_
  rw [Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal |pstar S cap f x|
      ≤ ENNReal.ofReal M.toReal :=
        ENNReal.ofReal_le_ofReal (pstar_bounded_onChain hrow hbd hx)
    _ = M := ENNReal.ofReal_toReal hMtop

/-- **`lem:doubling_operator`(1), first clause, in one statement.** `P⋆` is a contraction of
`L^p(μ)` for every `p ∈ [1,∞]`. -/
theorem eLpNorm_pstar_le_of_memLp (hrow : RowOnChain S cap) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {f : St → ℝ} (hf : MemLp f p L.mu) :
    eLpNorm (pstar S cap f) p L.mu ≤ eLpNorm f p L.mu := by
  by_cases hpt : p = ∞
  · subst hpt
    simpa only [eLpNorm_exponent_top] using L.eLpNormEssSup_pstar_le hrow f
  · exact L.eLpNorm_pstar_le hp1 hpt hf

end Stat

end GFNBounds.Doubling
