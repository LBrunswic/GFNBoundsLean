import GFNBounds.Doubling.SharpRate
import GFNBounds.Doubling.Weight

/-!
# `theo:doubling_sharp`, unconditional

**`theo:doubling_sharp`** — `app_doubling.tex:1323–1341`, proof at `1535–1658`.

> Let `s = 1` and `0 < c < 1`, with the integer `m₀` of `theo:doubling_decay`, and let `(λ_j)` be
> any positive sequence satisfying `eq:doubling_cut` for every `m > d`. Then `lim_j λ_j j^{p_*}`
> exists and lies in `[c₁',c₂']` for every pair `0 < c₁' ≤ c₂'` for which `eq:doubling_decay`
> holds with `c₁'` and `c₂'`; writing `C` for that limit, `λ_j = C j^{−p_*}(1+o(1))`, `C` is
> determined by `c`, `d` and `λ_1,…,λ_d`, and there are `ϑ ∈ (0,1)` depending on `c` alone and
> `c₆ > 0` with `|λ_j j^{p_*} − C| ≤ c₆ j^{−ϑ}`.

## What this file is

`Sharp.lean` and `SharpRate.lean` prove `theo:doubling_sharp` from two named hypotheses:
`theo:doubling_decay`(2) — the two-sided bound `c₁ ≤ u_m ≤ c₂` — and `lem:doubling_weight`, in
the form `|descW ℓ u y − descP ℓ u y| ≤ c₂c₃/ℓ`. **Both are now theorems**: the first is
`Product.decay_two_sided_of_cutBal`, the second `Weight.weight_bound`. This file discharges them
and states the conclusion with no hypothesis beyond the cut balance and positivity.

The one choice it makes is the level. `Sharp.lean` runs at a single integer `L` subject to four
effective conditions, and they are met at

  `L := max(ℓ₃, 20, d + 1, m₀(d), ⌈32cτ⌉)`,

`ℓ₃ = max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉)` of `Weight.lean` and `m₀(d) = max(ℓ₂(d), ⌈96cτ/γ²⌉)` of
`Product.lean`. Everything in that maximum is explicit in `c`, `p_*` and `d`.

## SCOPE (disclosed)

* The limit's membership in `[c₁',c₂']` **for every** admissible pair is the conclusion
  `c₁ ≤ C ≤ c₂` read at the pair `Sharp.sharp_limit` is run with; here that pair is the one
  `theo:doubling_decay`(2) produces, and it is returned with `C` so the reading is available.
* "`C` is determined by `c`, `d` and `λ_1,…,λ_d`" is `Sharp.cutBal_unique`, already
  unconditional, and is not restated.
* `ϑ = Decay.vartheta` is explicit and, as the paper says, **not effective**; see
  `SharpRate.lean`'s SCOPE.
* `c₆` is existential, as the paper's is a `max`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1`, `p = p_*` | ✓ carried (`Decay`) |
| `(λ_j)` positive satisfying `eq:doubling_cut` at every `m > d` | ✓ carried (`D.CutBal d lam ⊤`, `hpos`) |
| `theo:doubling_decay`(2) | ✓ carried, and **proved** (`Decay.uu_bounded_of_cutBal`) |
| `lem:doubling_weight` | ✓ carried, and **proved** (`Decay.weight_bound`) |
| `ℓ ≥ ℓ₄ ≥ ℓ₃`, `m ≥ m₀` | ⚠ **replaced** by the single explicit `L` above |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

namespace Decay

variable (D : Decay)

/-- **`theo:doubling_decay`(2) in the `u` variable, unconditional.** The same preamble as
`Product.decay_two_sided_of_cutBal`, stopped one step earlier: it is the rescaled profile, not the
sequence, that `Sharp.lean` takes bounds on. -/
theorem uu_bounded_of_cutBal {d ℓ : ℕ} {lam : ℕ → ℝ} (h : D.CutBal d lam ⊤)
    (hpos : ∀ j, 1 ≤ j → 0 < lam j) (hℓ : D.m0 d ≤ ℓ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ j : ℕ, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂ := by
  have hd : d < ℓ := lt_of_lt_of_le (D.lt_m0 d) hℓ
  have hℓ2 : D.ell2 d ≤ ℓ := le_trans (D.ell2_le_m0 d) hℓ
  have hthr : 32 * D.c * D.tau ≤ 2 * (ℓ : ℝ) := by
    have h' := D.thr_of_level hℓ2 (le_refl (2 * ℓ))
    push_cast at h'
    linarith
  have hℓ16 := D.sixteen_lt_level hthr
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hgp := D.gam_pos
  have hc5pos : (0 : ℝ) < D.c5 := by rw [c5]; positivity
  have hct := D.ctau_pos
  have hH0 : (0 : ℝ) ≤ 16 * D.c * D.tau := by nlinarith
  have hT0 : 0 ≤ D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ) :=
    div_nonneg (mul_nonneg hc5pos.le hH0) hℓpos.le
  refine D.uu_bounded h hpos (by omega) (by omega) (Real.exp_pos _) ?_ ?_
    (fun y _ => (D.descOne_two_sided hℓ y).1) (fun y _ => (D.descOne_two_sided hℓ y).2)
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hT0

/-- **`theo:doubling_sharp`, with no hypothesis beyond the cut balance and positivity.**

`eq:doubling_sharp` is the convergence, `eq:doubling_rate` the bound with `ϑ = Decay.vartheta`,
and `c₁ ≤ C ≤ c₂` records the limit inside the decay window that `theo:doubling_decay`(2)
produces. -/
theorem sharp_of_cutBal {d : ℕ} {lam : ℕ → ℝ} (hcut : D.CutBal d lam ⊤)
    (hpos : ∀ j, 1 ≤ j → 0 < lam j) :
    ∃ C c₁ c₂ c₆ : ℝ, 0 < c₁ ∧ c₁ ≤ C ∧ C ≤ c₂ ∧ 0 < c₆ ∧
      (∀ j : ℕ, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂) ∧
      Tendsto (fun m : ℕ => lam m * (m : ℝ) ^ D.p) atTop (𝓝 C) ∧
      ∀ m : ℕ, 1 ≤ m →
        |lam m * (m : ℝ) ^ D.p - C| ≤ c₆ * (m : ℝ) ^ (-D.vartheta) := by
  classical
  set L : ℕ := max (max D.ell3 20) (max (max (d + 1) (D.m0 d)) ⌈32 * D.c * D.tau⌉₊) with hLdef
  have hLℓ₃ : D.ell3 ≤ L := le_trans (le_max_left _ 20) (le_max_left _ _)
  have hL20 : 20 ≤ L := le_trans (le_max_right D.ell3 20) (le_max_left _ _)
  have hLd1 : d + 1 ≤ L :=
    le_trans (le_trans (le_max_left (d + 1) (D.m0 d)) (le_max_left _ _)) (le_max_right _ _)
  have hLm0 : D.m0 d ≤ L :=
    le_trans (le_trans (le_max_right (d + 1) (D.m0 d)) (le_max_left _ _)) (le_max_right _ _)
  have hLτ : 32 * D.c * D.tau ≤ (L : ℝ) := by
    have h1 : ⌈32 * D.c * D.tau⌉₊ ≤ L :=
      le_trans (le_max_right (max (d + 1) (D.m0 d)) _) (le_max_right _ _)
    have h2 : (⌈32 * D.c * D.tau⌉₊ : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1
    exact le_trans (Nat.le_ceil _) h2
  have hLd : d < 2 * L := by omega
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hbd⟩ := D.uu_bounded_of_cutBal hcut hpos hLm0
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  -- the profile is bounded by `c₂` in modulus, index `0` included
  have hg : ∀ j : ℕ, |D.uu lam j| ≤ c₂ := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hz : D.uu lam 0 = 0 := by
        rw [Decay.uu, Nat.cast_zero, Real.zero_rpow D.p_ne, mul_zero]
      rw [hz, abs_zero]
      exact hc₂pos.le
    · obtain ⟨h1, h2⟩ := hbd j hj
      rw [abs_le]
      exact ⟨by linarith, h2⟩
  have hweight : ∀ ℓ y : ℕ, L ≤ ℓ → 2 * ℓ ≤ y →
      |D.descW ℓ (D.uu lam) y - D.descP ℓ (D.uu lam) y| ≤ c₂ * D.c3 / ℓ :=
    fun ℓ y hℓ _ => D.weight_bound (le_trans hLℓ₃ hℓ) hg y
  obtain ⟨C, c₆, hc₆, hC1, hC2, hlim, hrate⟩ :=
    D.sharp hcut hLd hL20 hLτ hc₁ D.c3_nonneg hbd hweight
  exact ⟨C, c₁, c₂, c₆, hc₁, hC1, hC2, hc₆, hbd, hlim, hrate⟩

end Decay

end GFNBounds.Doubling
