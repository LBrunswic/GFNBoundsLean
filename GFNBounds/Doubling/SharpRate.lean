import GFNBounds.Doubling.Sharp

/-!
# `eq:doubling_rate`: the sharp asymptotic carries a polynomial rate

**`theo:doubling_sharp`**, fourth bullet of the proof — `app_doubling.tex:1323–1341`, proof at
`1608–1640`.

> Put `α := log₂(1/(1−ω))` and `ϑ := α/(1+α)`, so that `α > 0` and `ϑ ∈ (0,1)`, `ω` lying in
> `(0,1)`; both depend on `c` alone. Put `m₃ := max(⌈ℓ₄^{1/ϑ}⌉, ⌈2^{1/(1−ϑ)}⌉)` and, for an
> integer `m ≥ 1`, `ℓ := ⌈m^ϑ⌉` and `i := ⌊log₂(m/ℓ)⌋`. … Hence
> `|u_m − C| ≤ c₂(4^α + 3c₃)m^{−ϑ}` at every integer `m ≥ m₃`; and at `1 ≤ m < m₃`, both `u_m` and
> `C` lying in `[c₁,c₂]`, `|u_m − C| ≤ c₂ ≤ c₂ m₃^ϑ m^{−ϑ}`. So
> `c₆ := c₂ max(4^α + 3c₃, m₃^ϑ)` satisfies `eq:doubling_rate`.

## What is proved

The whole bullet, with `ϑ` **explicit and defined exactly as the paper defines it**:

  `α = −log₂(1−ω)`,  `ϑ = α/(1+α)`,  `ω = (c²/16) ln(5/4) ln(8/5)`.

Two differences from the paper's proof, both in this library's favour:

* the coefficient is `4^α + 2c₃`, not `4^α + 3c₃`, because `Sharp.uu_diff_le` carries `2c₂c₃/ℓ`
  where the paper carries `3c₂c₃/ℓ` (see `Coupling.coupling_above`);
* the paper's second threshold `⌈2^{1/(1−ϑ)}⌉` — which it uses to force `ℓ ≤ m` — is not needed:
  `ℓ = ⌈m^ϑ⌉ ≤ m` follows from `m^ϑ ≤ m` alone, at every `m ≥ 1`. So `m₃` reduces to
  `max(1, ⌈L^{1/ϑ}⌉)`.

`i` is `Nat.log 2 (m / ℓ)` with **natural** division, which is the paper's `⌊log₂(m/ℓ)⌋`: the two
agree because `Nat.log 2 q ≤ log₂ q < Nat.log 2 q + 1` and `2^i ≤ m/ℓ < 2^{i+1}` in `ℕ` is what
the argument consumes, through `Nat.pow_log_le_self` and `Nat.lt_pow_succ_log_self`.

## SCOPE (disclosed)

* The input is `Sharp.sharp_limit`'s conclusion, taken here as the hypothesis `hCbound`; so this
  file inherits `Sharp.lean`'s one unproved input, `lem:doubling_weight`, and nothing more.
* `c₆` is delivered existentially, as the paper's is a `max`; it is `c₂(4^α + 2c₃) + c₂ m₃^ϑ`,
  which is explicit in `c`, `c₂`, `c₃` and `L`, i.e. in the paper's `c, d, λ_1,…,λ_{2m₀}`.
* `ϑ` is explicit and, exactly as the paper says, **not effective**: at `c = 1/2` the proved `ω`
  is `≈ 0.0016` and `ϑ ≈ 0.0024`, against a measured `0.22`. This library reproduces the paper's
  constant, it does not improve it.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ϑ = α/(1+α)`, `α = log₂(1/(1−ω))` | ✓ carried verbatim (`Decay.alph`, `Decay.vartheta`) |
| `c₁ ≤ u_m ≤ c₂` at every `m ≥ 1`, `C ∈ [c₁,c₂]` | ✓ carried |
| `|u_m − C| ≤ c₂(1−ω)^i + 3c₂c₃/ℓ` for `ℓ ≥ ℓ₄`, `2^iℓ ≤ m` | ⚠ **strengthened input**: `2c₂c₃/ℓ`, from `Sharp.sharp_limit` |
| `m ≥ m₃ = max(⌈ℓ₄^{1/ϑ}⌉, ⌈2^{1/(1−ϑ)}⌉)` | ⚠ **weakened**: only `max(1, ⌈L^{1/ϑ}⌉)` is needed |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

namespace Decay

variable (D : Decay)

/-- `α := log₂(1/(1−ω))`, the paper's exponent parameter. -/
noncomputable def alph : ℝ := -Real.logb 2 (1 - D.omeg)

/-- `ϑ := α/(1+α)`, the rate exponent of `eq:doubling_rate`. Explicit, and — as the paper says —
not effective. -/
noncomputable def vartheta : ℝ := D.alph / (1 + D.alph)

theorem one_sub_omeg_pos : 0 < 1 - D.omeg := by linarith [D.omeg_lt_one]

theorem one_sub_omeg_lt_one : 1 - D.omeg < 1 := by linarith [D.omeg_pos]

/-- `α > 0`, since `0 < 1 − ω < 1`. -/
theorem alph_pos : 0 < D.alph := by
  rw [alph, neg_pos]
  exact Real.logb_neg (by norm_num) D.one_sub_omeg_pos D.one_sub_omeg_lt_one

/-- `1 − ω = 2^{−α}`. -/
theorem two_rpow_neg_alph : (2 : ℝ) ^ (-D.alph) = 1 - D.omeg := by
  rw [alph, neg_neg]
  exact Real.rpow_logb (by norm_num) (by norm_num) D.one_sub_omeg_pos

theorem vartheta_pos : 0 < D.vartheta :=
  div_pos D.alph_pos (by linarith [D.alph_pos])

theorem vartheta_lt_one : D.vartheta < 1 := by
  rw [vartheta, div_lt_one (by linarith [D.alph_pos])]
  linarith

/-- `α(1 − ϑ) = ϑ`, the identity the rate turns on. -/
theorem alph_mul_one_sub : D.alph * (1 - D.vartheta) = D.vartheta := by
  have h : (1 : ℝ) + D.alph ≠ 0 := by linarith [D.alph_pos]
  rw [vartheta]
  field_simp
  ring

section Rate

variable {d L : ℕ} {lam : ℕ → ℝ} {c₁ c₂ c₃ C : ℝ}

/-- **The rate at a large index.** At every `m` with `L ≤ m^ϑ`, the level `ℓ := ⌈m^ϑ⌉` and the
index `i := ⌊log₂(m/ℓ)⌋` turn `Sharp.sharp_limit`'s error into `c₂(4^α + 2c₃) m^{−ϑ}`. -/
theorem rate_of_large (hL : 20 ≤ L) (hc₂ : 0 < c₂) (hc₃ : 0 ≤ c₃)
    (hCbound : ∀ ℓ i m : ℕ, L ≤ ℓ → 2 ^ i * ℓ ≤ m →
      |D.uu lam m - C| ≤ c₂ * (1 - D.omeg) ^ i + 2 * (c₂ * c₃ / ℓ))
    {m : ℕ} (hm1 : 1 ≤ m) (hmL : (L : ℝ) ≤ (m : ℝ) ^ D.vartheta) :
    |D.uu lam m - C| ≤ c₂ * (4 ^ D.alph + 2 * c₃) * (m : ℝ) ^ (-D.vartheta) := by
  have hϑ0 : 0 < D.vartheta := D.vartheta_pos
  have hϑ1 : D.vartheta < 1 := D.vartheta_lt_one
  have hα : 0 < D.alph := D.alph_pos
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmϑpos : (0 : ℝ) < (m : ℝ) ^ D.vartheta := Real.rpow_pos_of_pos hmpos _
  have hmϑ1 : (1 : ℝ) ≤ (m : ℝ) ^ D.vartheta := Real.one_le_rpow hmR hϑ0.le
  set ℓ : ℕ := ⌈(m : ℝ) ^ D.vartheta⌉₊ with hℓdef
  have hlb : (m : ℝ) ^ D.vartheta ≤ (ℓ : ℝ) := Nat.le_ceil _
  have hub : (ℓ : ℝ) ≤ 2 * (m : ℝ) ^ D.vartheta := by
    have := Nat.ceil_lt_add_one (le_of_lt hmϑpos)
    rw [← hℓdef] at this
    linarith
  have hLℓ : L ≤ ℓ := by
    have hcast : (L : ℝ) ≤ (ℓ : ℝ) := le_trans hmL hlb
    exact_mod_cast hcast
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hℓm : ℓ ≤ m := by
    refine Nat.ceil_le.mpr ?_
    calc (m : ℝ) ^ D.vartheta ≤ (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmR hϑ1.le
      _ = (m : ℝ) := Real.rpow_one _
  set i : ℕ := Nat.log 2 (m / ℓ) with hidef
  have hq : 1 ≤ m / ℓ := (Nat.one_le_div_iff (by omega)).mpr hℓm
  have hpow_le : 2 ^ i * ℓ ≤ m := by
    have h1 : 2 ^ i ≤ m / ℓ := Nat.pow_log_le_self 2 (by omega)
    calc 2 ^ i * ℓ ≤ (m / ℓ) * ℓ := Nat.mul_le_mul_right _ h1
      _ ≤ m := Nat.div_mul_le_self m ℓ
  have hltm : m < 2 ^ (i + 1) * ℓ :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_pow_succ_log_self (by norm_num) _)
  -- the geometric factor
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ (i : ℕ) := by positivity
  have hXge : (m : ℝ) / (2 * (ℓ : ℝ)) ≤ (2 : ℝ) ^ (i : ℕ) := by
    rw [div_le_iff₀ (by positivity)]
    have hcast : (m : ℝ) < (2 : ℝ) ^ (i + 1) * (ℓ : ℝ) := by exact_mod_cast hltm
    have hsplit : (2 : ℝ) ^ (i + 1) * (ℓ : ℝ) = (2 : ℝ) ^ (i : ℕ) * (2 * (ℓ : ℝ)) := by ring
    rw [hsplit] at hcast
    linarith
  have hXpos : (0 : ℝ) < (m : ℝ) / (2 * (ℓ : ℝ)) := by positivity
  have e1 : (1 - D.omeg) ^ i = (2 : ℝ) ^ ((-D.alph) * (i : ℝ)) := by
    rw [← D.two_rpow_neg_alph, ← Real.rpow_natCast ((2 : ℝ) ^ (-D.alph)) i,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have e2 : ((2 : ℝ) ^ (i : ℕ)) ^ (-D.alph) = (2 : ℝ) ^ ((i : ℝ) * (-D.alph)) := by
    rw [← Real.rpow_natCast (2 : ℝ) i, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (1 - D.omeg) ^ i = ((2 : ℝ) ^ (i : ℕ)) ^ (-D.alph) := by
    rw [e1, e2, mul_comm]
  have hstep : ((2 : ℝ) ^ (i : ℕ)) ^ (-D.alph) ≤ ((m : ℝ) / (2 * (ℓ : ℝ))) ^ (-D.alph) :=
    Real.rpow_le_rpow_of_nonpos hXpos hXge (by linarith)
  have hinv : ((m : ℝ) / (2 * (ℓ : ℝ))) ^ (-D.alph) = ((2 * (ℓ : ℝ)) / (m : ℝ)) ^ D.alph := by
    rw [Real.rpow_neg hXpos.le, ← Real.inv_rpow hXpos.le]
    congr 1
    rw [inv_div]
  have hratio : (2 * (ℓ : ℝ)) / (m : ℝ) ≤ 4 * (m : ℝ) ^ (D.vartheta - 1) := by
    have hrw : (m : ℝ) ^ (D.vartheta - 1) = (m : ℝ) ^ D.vartheta / (m : ℝ) := by
      rw [Real.rpow_sub hmpos, Real.rpow_one]
    have hR : 4 * ((m : ℝ) ^ D.vartheta / (m : ℝ)) = (4 * (m : ℝ) ^ D.vartheta) / (m : ℝ) := by
      ring
    rw [hrw, hR, div_le_div_iff_of_pos_right hmpos]
    linarith [hub]
  have hfinal : ((2 * (ℓ : ℝ)) / (m : ℝ)) ^ D.alph ≤ (4 * (m : ℝ) ^ (D.vartheta - 1)) ^ D.alph :=
    Real.rpow_le_rpow (by positivity) hratio hα.le
  have hexp : (4 * (m : ℝ) ^ (D.vartheta - 1)) ^ D.alph
      = (4 : ℝ) ^ D.alph * (m : ℝ) ^ (-D.vartheta) := by
    rw [Real.mul_rpow (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hmpos _)),
      ← Real.rpow_mul hmpos.le]
    congr 2
    have h := D.alph_mul_one_sub
    nlinarith [h]
  have hgeom : (1 - D.omeg) ^ i ≤ (4 : ℝ) ^ D.alph * (m : ℝ) ^ (-D.vartheta) := by
    rw [hpow]
    calc ((2 : ℝ) ^ (i : ℕ)) ^ (-D.alph)
        ≤ ((m : ℝ) / (2 * (ℓ : ℝ))) ^ (-D.alph) := hstep
      _ = ((2 * (ℓ : ℝ)) / (m : ℝ)) ^ D.alph := hinv
      _ ≤ (4 * (m : ℝ) ^ (D.vartheta - 1)) ^ D.alph := hfinal
      _ = (4 : ℝ) ^ D.alph * (m : ℝ) ^ (-D.vartheta) := hexp
  -- the weight factor
  have hmneg : (m : ℝ) ^ (-D.vartheta) = ((m : ℝ) ^ D.vartheta)⁻¹ := by
    rw [Real.rpow_neg hmpos.le]
  have hinvℓ : 1 / (ℓ : ℝ) ≤ (m : ℝ) ^ (-D.vartheta) := by
    rw [hmneg, ← one_div]
    exact one_div_le_one_div_of_le hmϑpos hlb
  have hwt : 2 * (c₂ * c₃ / (ℓ : ℝ)) ≤ 2 * c₂ * c₃ * (m : ℝ) ^ (-D.vartheta) := by
    have hdiv : c₂ * c₃ / (ℓ : ℝ) = (c₂ * c₃) * (1 / (ℓ : ℝ)) := by ring
    rw [hdiv]
    nlinarith [hinvℓ, mul_nonneg hc₂.le hc₃]
  have hbound := hCbound ℓ i m hLℓ hpow_le
  nlinarith [hbound, hgeom, hwt, hc₂]

/-- **`eq:doubling_rate`.** With `ϑ = α/(1+α)` and `α = log₂(1/(1−ω))`, there is an explicit
`c₆ > 0` with `|λ_m m^{p_*} − C| ≤ c₆ m^{−ϑ}` at every `m ≥ 1`. -/
theorem sharp_rate (hL : 20 ≤ L) (hc₁ : 0 < c₁) (hc₃ : 0 ≤ c₃)
    (hbd : ∀ j, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂)
    (hC1 : c₁ ≤ C) (hC2 : C ≤ c₂)
    (hCbound : ∀ ℓ i m : ℕ, L ≤ ℓ → 2 ^ i * ℓ ≤ m →
      |D.uu lam m - C| ≤ c₂ * (1 - D.omeg) ^ i + 2 * (c₂ * c₃ / ℓ)) :
    ∃ c₆ : ℝ, 0 < c₆ ∧
      ∀ m : ℕ, 1 ≤ m → |D.uu lam m - C| ≤ c₆ * (m : ℝ) ^ (-D.vartheta) := by
  have hϑ0 : 0 < D.vartheta := D.vartheta_pos
  have hα : 0 < D.alph := D.alph_pos
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ (le_trans (hbd 1 le_rfl).1 (hbd 1 le_rfl).2)
  set M : ℕ := max 1 ⌈(L : ℝ) ^ (1 / D.vartheta)⌉₊ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMϑpos : (0 : ℝ) < (M : ℝ) ^ D.vartheta := Real.rpow_pos_of_pos hMpos _
  refine ⟨c₂ * (4 ^ D.alph + 2 * c₃) + c₂ * (M : ℝ) ^ D.vartheta, ?_, ?_⟩
  · have h4 : (0 : ℝ) < (4 : ℝ) ^ D.alph := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [hc₂, hc₃, hMϑpos, h4]
  · intro m hm1
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hmneg : (0 : ℝ) < (m : ℝ) ^ (-D.vartheta) := Real.rpow_pos_of_pos hmpos _
    have h4 : (0 : ℝ) < (4 : ℝ) ^ D.alph := Real.rpow_pos_of_pos (by norm_num) _
    by_cases hMm : M ≤ m
    · -- the large range
      have hmL : (L : ℝ) ≤ (m : ℝ) ^ D.vartheta := by
        have hceil : ⌈(L : ℝ) ^ (1 / D.vartheta)⌉₊ ≤ m := le_trans (le_max_right _ _) hMm
        have hx : (L : ℝ) ^ (1 / D.vartheta) ≤ (m : ℝ) := Nat.ceil_le.mp hceil
        have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
        have hpow : ((L : ℝ) ^ (1 / D.vartheta)) ^ D.vartheta = (L : ℝ) := by
          rw [← Real.rpow_mul hLnn, one_div, inv_mul_cancel₀ hϑ0.ne', Real.rpow_one]
        calc (L : ℝ) = ((L : ℝ) ^ (1 / D.vartheta)) ^ D.vartheta := hpow.symm
          _ ≤ (m : ℝ) ^ D.vartheta := Real.rpow_le_rpow (Real.rpow_nonneg hLnn _) hx hϑ0.le
      have hmain := D.rate_of_large hL hc₂ hc₃ hCbound hm1 hmL
      have hle : c₂ * (4 ^ D.alph + 2 * c₃)
          ≤ c₂ * (4 ^ D.alph + 2 * c₃) + c₂ * (M : ℝ) ^ D.vartheta := by
        linarith [mul_nonneg hc₂.le hMϑpos.le]
      exact le_trans hmain (mul_le_mul_of_nonneg_right hle hmneg.le)
    · -- the finite range `1 ≤ m < M`
      have hmM : (m : ℝ) ≤ (M : ℝ) := by
        have : m ≤ M := by omega
        exact_mod_cast this
      have hsmall : |D.uu lam m - C| ≤ c₂ := by
        obtain ⟨h1, h2⟩ := hbd m hm1
        rw [abs_le]
        constructor <;> linarith
      have hmϑ : (m : ℝ) ^ D.vartheta ≤ (M : ℝ) ^ D.vartheta :=
        Real.rpow_le_rpow (by positivity) hmM hϑ0.le
      have hmϑpos : (0 : ℝ) < (m : ℝ) ^ D.vartheta := Real.rpow_pos_of_pos hmpos _
      have hkey : 1 ≤ (M : ℝ) ^ D.vartheta * (m : ℝ) ^ (-D.vartheta) := by
        rw [Real.rpow_neg hmpos.le]
        have hcancel : (m : ℝ) ^ D.vartheta * ((m : ℝ) ^ D.vartheta)⁻¹ = 1 :=
          mul_inv_cancel₀ hmϑpos.ne'
        have hmul : (m : ℝ) ^ D.vartheta * ((m : ℝ) ^ D.vartheta)⁻¹
            ≤ (M : ℝ) ^ D.vartheta * ((m : ℝ) ^ D.vartheta)⁻¹ :=
          mul_le_mul_of_nonneg_right hmϑ (by positivity)
        linarith [hmul, hcancel]
      have h1 : c₂ ≤ c₂ * (M : ℝ) ^ D.vartheta * (m : ℝ) ^ (-D.vartheta) := by
        nlinarith [mul_le_mul_of_nonneg_left hkey hc₂.le]
      have hnn : 0 ≤ c₂ * (4 ^ D.alph + 2 * c₃) := by nlinarith [h4, hc₃, hc₂]
      have h2 : c₂ * (M : ℝ) ^ D.vartheta * (m : ℝ) ^ (-D.vartheta)
          ≤ (c₂ * (4 ^ D.alph + 2 * c₃) + c₂ * (M : ℝ) ^ D.vartheta)
            * (m : ℝ) ^ (-D.vartheta) := by
        nlinarith [hnn, hmneg]
      linarith [hsmall, h1, h2]

/-- **`theo:doubling_sharp`, assembled.** The rescaled profile `λ_m m^{p_*}` converges to a limit
`C ∈ [c₁,c₂]` — this is `eq:doubling_sharp` — and the convergence carries the polynomial rate
`eq:doubling_rate` with the paper's exponent `ϑ = α/(1+α)`, `α = log₂(1/(1−ω))`.

`Decay.cutBal_unique` supplies the remaining clause of the theorem: `C` is determined by `c`, `d`
and `λ_1,…,λ_d`.

The sole unproved input is `hweight`, which is `lem:doubling_weight`; see `Sharp.lean`. -/
theorem sharp (hcut : D.CutBal d lam ⊤) (hLd : d < 2 * L) (hL : 20 ≤ L)
    (hLτ : 32 * D.c * D.tau ≤ (L : ℝ)) (hc₁ : 0 < c₁) (hc₃ : 0 ≤ c₃)
    (hbd : ∀ j, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂)
    (hweight : ∀ ℓ y : ℕ, L ≤ ℓ → 2 * ℓ ≤ y →
      |D.descW ℓ (D.uu lam) y - D.descP ℓ (D.uu lam) y| ≤ c₂ * c₃ / ℓ) :
    ∃ C c₆ : ℝ, 0 < c₆ ∧ c₁ ≤ C ∧ C ≤ c₂ ∧
      Tendsto (fun m : ℕ => lam m * (m : ℝ) ^ D.p) atTop (𝓝 C) ∧
      ∀ m : ℕ, 1 ≤ m →
        |lam m * (m : ℝ) ^ D.p - C| ≤ c₆ * (m : ℝ) ^ (-D.vartheta) := by
  obtain ⟨C, hC, hC1, hC2, hCbound⟩ :=
    D.sharp_limit hcut hLd hL hLτ hc₁ hc₃ hbd hweight
  obtain ⟨c₆, hc₆, hrate⟩ := D.sharp_rate hL hc₁ hc₃ hbd hC1 hC2 hCbound
  exact ⟨C, c₆, hc₆, hC1, hC2, hC, hrate⟩

end Rate

end Decay

end GFNBounds.Doubling
