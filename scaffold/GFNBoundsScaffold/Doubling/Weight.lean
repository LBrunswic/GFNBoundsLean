import GFNBounds.Doubling.SharpRate

/-!
# The weight of a descent

**`lem:doubling_weight`** — `app_doubling.tex:1343–1383`.

> With the constant `c₄` of `lem:doubling_descent` and `γ`, `c₅`, `ℓ₂` of `lem:doubling_escape`,
> put `c₃ := 8c₅c₄` and `ℓ₃ := max(ℓ₂, ⌈2c₄⌉, ⌈24c₄/γ²⌉, ⌈4c₄c₅⌉)`. Let `ℓ ≥ ℓ₃`, let `(Y_n)` and
> `N_ℓ` be the descent chain at the level `ℓ` and its exit time, and let
> `Z_ℓ := ∏_{n<N_ℓ} R₀(Y_n)`. Then, for every integer `m ≥ 2ℓ`,
> `E(|Z_ℓ − 1| ∣ Y_0 = m) ≤ c₃/ℓ`.

## Why it is here and not in `GFNBounds/`

This is the **one** open input of the whole sharp-asymptotic block. Its proof reduces
`|Z_ℓ − 1|` to `∏_{n<N_ℓ}(1 + b(Y_n)) − 1` and then invokes `lem:doubling_product`
(`app_doubling.tex:1110–1153`), whose own proof needs `lem:doubling_escape`
(`app_doubling.tex:1026–1108`) — the exit-time law of the descent from a dyadic block, with the
geometric tail `P(ς > k) ≤ (1−γ)^k`. Both are genuine Markov-chain statements about a stopping
time, and Mathlib v4.31.0 has no discrete-time chain theory to state them in. They are
obstruction 1 of the README.

Everything else of the block is closed in `GFNBounds/`:
`Doeblin.doeblin` (`lem:doubling_doeblin`), `Coupling.coupling` (`lem:doubling_coupling`),
`Sharp.sharp_limit` and `SharpRate.sharp` (`theo:doubling_sharp`, both `eq:doubling_sharp` and
`eq:doubling_rate`) — the last two conditional on exactly the statement below.

## The form stated

Not `E(|Z_ℓ − 1|) ≤ c₃/ℓ` itself — `Z_ℓ` is a random variable and this library builds no chain —
but the consequence the proof of `theo:doubling_sharp` consumes, twice:
for a test function `g` bounded by `B`,

  `|descW ℓ g y − descP ℓ g y| = |E((Z_ℓ − 1) g(Y_{N_ℓ}) ∣ Y_0 = y)| ≤ B · E|Z_ℓ − 1| ≤ B c₃/ℓ`,

`descW` being the unnormalised descent transform of `Descent.lean` (which carries `Z_ℓ`) and
`descP` the normalised one of `DescentLaw.lean` (which does not). `c₃` and `ℓ₃` are existential
here because the paper's own values are non-effective: they come from `c₄`, `γ`, `c₅`, `ℓ₂`, of
which only `c₄` has been effectivized (`R0Bound.lean`, `c₄ = 16cτ`).

`sharp_of_decay` below shows the block closes the moment this lands: it derives the whole of
`theo:doubling_sharp` from it plus `theo:doubling_decay`(2), and carries no gap of its own.
-/

namespace GFNBoundsScaffold.Doubling

open GFNBounds.Doubling

/-- **`eq:doubling_weight`**, in the form the sharp block consumes. -/
theorem exists_weight_bound (D : Decay) :
    ∃ (c₃ : ℝ) (ℓ₃ : ℕ), 0 ≤ c₃ ∧ 1 ≤ ℓ₃ ∧
      ∀ (B : ℝ) (g : ℕ → ℝ), (∀ j, |g j| ≤ B) → ∀ ℓ y : ℕ, ℓ₃ ≤ ℓ → 2 * ℓ ≤ y →
        |D.descW ℓ g y - D.descP ℓ g y| ≤ B * c₃ / ℓ :=
  sorry -- SORRY(lem:doubling_weight): needs an absolute-deviation transform E(|Z_ℓ−1|) as a descW-style recursion; NOT blocked on Mathlib — lem:doubling_escape and lem:doubling_product are both proved chain-free in Escape/Sojourn/Product.

/-- **`theo:doubling_sharp` in full**, from `theo:doubling_decay`(2) and the weight bound above.
Gap-free: everything but `exists_weight_bound` is proved in `GFNBounds/`. -/
theorem sharp_of_decay (D : Decay) {d : ℕ} {lam : ℕ → ℝ} {c₁ c₂ : ℝ}
    (hcut : D.CutBal d lam ⊤) (hc₁ : 0 < c₁)
    (hbd : ∀ j, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂) :
    ∃ C c₆ : ℝ, 0 < c₆ ∧ c₁ ≤ C ∧ C ≤ c₂ ∧
      Filter.Tendsto (fun m : ℕ => lam m * (m : ℝ) ^ D.p) Filter.atTop (nhds C) ∧
      ∀ m : ℕ, 1 ≤ m →
        |lam m * (m : ℝ) ^ D.p - C| ≤ c₆ * (m : ℝ) ^ (-D.vartheta) := by
  obtain ⟨c₃, ℓ₃, hc₃, hℓ₃, hw⟩ := exists_weight_bound D
  have hc₂ : c₁ ≤ c₂ := le_trans (hbd 1 le_rfl).1 (hbd 1 le_rfl).2
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le hc₁ hc₂
  -- the level: large enough for the Doeblin block, for `R₀ ≤ 2`, for the cut window, and for `ℓ₃`
  set L : ℕ := max (max ℓ₃ 20) (max (d + 1) ⌈32 * D.c * D.tau⌉₊) with hLdef
  have hL20 : 20 ≤ L := le_trans (le_max_right ℓ₃ 20) (le_max_left _ _)
  have hLd1 : d + 1 ≤ L := le_trans (le_max_left (d + 1) _) (le_max_right _ _)
  have hLd : d < 2 * L := by omega
  have hLτ : 32 * D.c * D.tau ≤ (L : ℝ) := by
    have h1 : ⌈32 * D.c * D.tau⌉₊ ≤ L := le_trans (le_max_right (d + 1) _) (le_max_right _ _)
    have h2 : (⌈32 * D.c * D.tau⌉₊ : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1
    exact le_trans (Nat.le_ceil _) h2
  have hLℓ₃ : ℓ₃ ≤ L := le_trans (le_max_left ℓ₃ 20) (le_max_left _ _)
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
      |D.descW ℓ (D.uu lam) y - D.descP ℓ (D.uu lam) y| ≤ c₂ * c₃ / ℓ :=
    fun ℓ y hℓ hy => hw c₂ (D.uu lam) hg ℓ y (le_trans hLℓ₃ hℓ) hy
  exact D.sharp hcut hLd hL20 hLτ hc₁ hc₃ hbd hweight

end GFNBoundsScaffold.Doubling
