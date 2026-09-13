import GFNBounds.Doubling.Main

/-!
# The truncation at the paper's `B̂_K`, with constants of `c`, `d` and `j̄` alone

**`cor:doubling_truncation`** — `app_doubling.tex:2202–2339` (statement 2202–2224, proof
2226–2339).

> In the setting of Definition `def:doubling_setting`, let `s=1` and `0<c<1`, and for an even
> integer `K ≥ d` let `λ^K`, `L_K` and `B̂_K` be the invariant probability, the tail and the
> constant `eq:doubling_Bhat` of the truncation at `K`. Then:
> (1) for every even integer `K ≥ d` and every integer `m` with `d < m ≤ K/2`,
> `B̂_K ≥ √( L_K(m)(1 − L_K(m)) / (2 λ^K_m) )`;
> (2) there are integers `m₀` and `K₀ ≥ d` and a constant `c₉ ≥ 1`, depending only on `c` and
> `d`, such that for every even integer `K ≥ K₀` there are constants `0 < C^K_- ≤ C^K_+` with
> `C^K_+/C^K_- ≤ c₉` and, for every integer `m` with `m₀ ≤ m ≤ K/2`,
> `C^K_- m^{−p_*} ≤ λ^K_m ≤ C^K_+ m^{−p_*}`;
> (3) there is `c₈ > 0`, depending only on `c`, `d` and `j̄`, with `B̂_K ≥ c₈ √K` for every
> even integer `K ≥ K₀`, `K₀` being the integer of (2).

`Truncation.lean` proves the three items about an abstract constant `B` bounding the `L²(λ^K)`
Rayleigh quotient, with the decay window and the ratio bound threaded through the free field
`S.epsMax`; `Main.lean`'s `main_truncation_sqrtK` composes them into an `∃ c₈` whose value
depends on that field. This file closes the remaining distance to the paper's wording:

* `Stat.bhatK` **is** `eq:doubling_Bhat`: `‖(Id − P⋆ + Π)^{-1} − Π‖` on `L²(λ^K)`, the inverse
  being `Ring.inverse`, shown to be the two-sided inverse by `Stat.diffOpK_resolvent`.
* item (1) at `B̂_K`, as written (`Stat.percut_bhatK`), and squared at every bounded left inverse
  of `Id − P⋆` (`Stat.percut_leftInverse`);
* items (2) and (3) with `m₀ = D.m0 d`, `K₀ = D.K0Of d = 8m₀ + 2` (the paper's own), `c₉ =
  D.c9Of d` and `c₈ = D.c8Of d j̄` as **formulas** (`Stat.decayK_explicit`,
  `Stat.sqrtK_explicit`, `Stat.sqrtK_bhatK`), so the dependence clauses are literal;
* the corollary in one statement: `truncation_explicit` (witnesses named) and `main_truncation`
  (the paper's quantifier order, in terms of `c`, with every existential placed before the
  setting, so that `m₀`, `K₀`, `c₉` see only `c` and `d`, and `c₈` only `c`, `d` and `j̄`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1` | ✓ carried: `heps`, `hc0`, `hc1` in `main_truncation`; a `D : Decay` with `S.eps = D.eps` in the explicit forms. ⚠ weakened for item (1): not used, it holds for every `Setting` |
| `K` even | stated for every `K`, but **vacuous at odd `K`**: there no `Stat S (some K)` exists (`lad K` is unreachable, so invariance forces `λ(lad K) = 0`, contradicting `pos`). The even case is the content; nothing beyond the paper is claimed |
| `K ≥ d` | ✓ carried as `hdK` (items (1), (3)); in (2) it follows from `K ≥ K₀` |
| `λ^K` the unique invariant probability | ⚠ weakened: any `Stat S (some K)`; uniqueness at even `K ≥ d` is `main_truncation_bhat` |
| `B̂_K := ‖(Id − P⋆ + Π)^{-1} − Π‖_{L²(λ^K)}` | ✓ `Stat.bhatK`, literally |
| `L_K(m) = λ^K([m, K])` | ✓ `Stat.tailMass` at `cap = some K` |
| `d < m ≤ K/2` in (1); `m₀ ≤ m ≤ K/2` in (2) | ✓ carried |
| `m₀`, `K₀ ≥ d`, `c₉ ≥ 1` depending only on `c`, `d` | ✓ `D.m0 d`, `D.K0Of d`, `D.c9Of d`; `Decay.le_K0Of`, `Decay.one_le_c9Of` |
| `c₈ > 0` depending only on `c`, `d`, `j̄` | ✓ `D.c8Of d j̄`; `Decay.c8Of_pos` |
| `ε_max = c/2` (Step 3, Step 4) | ✓ supplied, not assumed: `Setting.withEpsMax` |
| `ε(j) = c/(j+1)` for `j ≥ 1` (`eq:doubling_family`, `ε` used only at `j ≥ 1`) | ⚠ strengthened: `heps`/`hDeps` range over every `j : ℕ`, so they also fix `S.eps 0 = c`. Harmless: `Setting.eps` is read only at `j ≥ 1`, and any setting can be rebuilt with that value at `0` without changing its chain |

## SCOPE (disclosed)

* **What "depending only on" means here.** `Decay` has two data fields, `c` and `p`, and `p` is
  the Cramér root of `c`, unique at `0 < c < 1` (`lem:doubling_cramer_root`), so a function of
  `(D, d)` is a function of `(c, d)`. In `main_truncation` the witnesses are hidden behind `∃`,
  as the paper's sentence reads, and the existentials are placed **before** the setting: `∃ m₀
  K₀ c₉` sits under `∀ d` only, and `∃ c₈` under `∀ d, ∀ j̄` only, the setting `S` being
  quantified afterwards with `S.d = d` and `S.jbar = j̄`. So the dependence clauses are enforced
  by the binder order, not only by the explicit witnesses of `truncation_explicit`. `j̄ ≥ 0` is
  carried there as a hypothesis on the bare real `j̄`; every setting has it.
* **`c₉` is an explicit formula the paper does not print.** The paper bounds the block ratio
  `max_{J₀} λ^K / min_{J₀} λ^K` by "a constant depending only on `c` and `m₀`"; here it is `Q²`
  with `Q = (1 − c/2)^{−m₀} + ((c/(2m₀+1))^{m₀})^{−1}` (`Decay.truncQ`, from the two chains of
  Step 4), and `c₉ = e^{2c₅c₄/m₀} 2^{p_*} Q²` with the library's effective `c₄ = 16cτ` and
  `c₅ = 6/γ²`. `c₈ = (2^{p_*+4} c₉ (2 + j̄/(1−c)))^{−1/2}` is the paper's formula, written as
  `(√·)⁻¹`.
* **`ε_max` is routed, not hypothesized.** `Stat.decayK` bounds through `S.epsMax`, a free field
  of `Setting` that nothing pins to `c/2`. `Setting.withEpsMax` replaces only that field, so the
  chain, `P⋆` and every invariant probability are unchanged (`Stat.withEpsMax` is the identity on
  masses: `Stat.withEpsMax_lam`, by `rfl`), and `decayK` is applied there at `ε_max = c/2`. No
  hypothesis `S.epsMax = c/2` is carried.
* **Items (1) and (3) are also stated at every bounded left inverse** `S(Id − P⋆) = Id − Π`
  (`percut_leftInverse`, `sqrtK_explicit`), which includes the paper's `S`
  (`diffOpK_resolvent`); the `B̂_K` forms are corollaries.
* Uniqueness of the inverse of `Id − P⋆ + Π` is not needed and not stated: `Ring.inverse` is a
  fixed choice and equals any two-sided inverse.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real MeasureTheory

variable {S : Setting}

/-! ### `B̂_K`, as the paper defines it -/

namespace Stat

variable {K : ℕ}

/-- **`eq:doubling_Bhat` on the truncation.** `S := (Id − P⋆ + Π)^{-1} − Π` on `L²(λ^K)`, the
inverse being `Ring.inverse`, which is the two-sided inverse wherever one exists
(`diffOpK_resolvent`). -/
noncomputable def diffOpK (L : Stat S (some K)) (hdK : S.d ≤ K) :
    Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu :=
  Ring.inverse (1 - L.pstarL2 (rowOnChain_some hdK) + L.piL2) - L.piL2

/-- **`B̂_K := ‖S‖_{L²(λ^K)}`** (`eq:doubling_Bhat`). -/
noncomputable def bhatK (L : Stat S (some K)) (hdK : S.d ≤ K) : ℝ := ‖L.diffOpK hdK‖

/-- **`eq:doubling_resolvent` at the paper's `S`.** The operator `diffOpK` satisfies
`(Id − P⋆)S = S(Id − P⋆) = Id − Π` and `ΠS = SΠ = 0`: `Ring.inverse` is the inverse that
`Stat.exists_diffusionOp` produces. -/
theorem diffOpK_resolvent (L : Stat S (some K)) (hdK : S.d ≤ K) :
    (1 - L.pstarL2 (rowOnChain_some hdK)) * L.diffOpK hdK = 1 - L.piL2 ∧
      L.diffOpK hdK * (1 - L.pstarL2 (rowOnChain_some hdK)) = 1 - L.piL2 ∧
      L.piL2 * L.diffOpK hdK = 0 ∧ L.diffOpK hdK * L.piL2 = 0 := by
  obtain ⟨R, hAR, hRA, e1, e2, e3, e4⟩ := L.exists_diffusionOp (rowOnChain_some hdK)
  have hinv : Ring.inverse (1 - L.pstarL2 (rowOnChain_some hdK) + L.piL2) = R := by
    let u : (Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu)ˣ := ⟨_, R, hAR, hRA⟩
    exact Ring.inverse_unit u
  have hS : L.diffOpK hdK = R - L.piL2 := by rw [diffOpK, hinv]
  rw [hS]
  exact ⟨e1, e2, e3, e4⟩

/-! ### Item (1) -/

/-- **`eq:doubling_percut_K`, squared, at every bounded left inverse.** If `S(Id − P⋆) = Id − Π`
on `L²(λ^K)` then `L_K(m)(1 − L_K(m)) ≤ 2λ^K_m ‖S‖²` at every cut `d < m ≤ K/2`. -/
theorem percut_leftInverse (L : Stat S (some K)) (hdK : S.d ≤ K)
    {Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu}
    (hS : Sop * (1 - L.pstarL2 (rowOnChain_some hdK)) = 1 - L.piL2)
    {m : ℕ} (hdm : S.d < m) (hmK : m ≤ K / 2) :
    L.tailMass m * (1 - L.tailMass m) ≤ 2 * L.lam (.lad m) * ‖Sop‖ ^ 2 :=
  L.percut_K hdm (show 2 * m ≤ K by omega)
    fun _ hf hmean => L.mass_le_of_leftInverse (rowOnChain_some hdK) hS hf hmean

/-- **`eq:doubling_percut_K`, as written.** `B̂_K ≥ √(L_K(m)(1 − L_K(m)) / (2λ^K_m))` at every cut
`d < m ≤ K/2`. -/
theorem percut_bhatK (L : Stat S (some K)) (hdK : S.d ≤ K) {m : ℕ} (hdm : S.d < m)
    (hmK : m ≤ K / 2) :
    Real.sqrt (L.tailMass m * (1 - L.tailMass m) / (2 * L.lam (.lad m))) ≤ L.bhatK hdK := by
  have hsq := L.percut_leftInverse hdK (L.diffOpK_resolvent hdK).2.1 hdm hmK
  have hlam : 0 < L.lam (.lad m) := L.pos (show m ≤ K by omega)
  have hq : L.tailMass m * (1 - L.tailMass m) / (2 * L.lam (.lad m)) ≤ L.bhatK hdK ^ 2 := by
    rw [div_le_iff₀ (by positivity), bhatK]
    linarith
  calc Real.sqrt (L.tailMass m * (1 - L.tailMass m) / (2 * L.lam (.lad m)))
      ≤ Real.sqrt (L.bhatK hdK ^ 2) := Real.sqrt_le_sqrt hq
    _ = L.bhatK hdK := Real.sqrt_sq (norm_nonneg _)

end Stat

/-! ### The constants of items (2) and (3), as formulas in `c`, `p_*` and `d` -/

/-- The same setting with its bound `ε_max` replaced by another admissible bound. Nothing but the
field `epsMax` moves, so the chain, `P⋆` and every invariant probability are unchanged. -/
def Setting.withEpsMax (S : Setting) (e : ℝ) (he : ∀ ⦃j⦄, 1 ≤ j → S.eps j ≤ e) (he1 : e < 1) :
    Setting :=
  { S with epsMax := e, eps_le := he, epsMax_lt_one := he1 }

/-- An invariant probability of `S` is one of `S.withEpsMax e`, with the same masses. -/
def Stat.withEpsMax {cap : Option ℕ} (L : Stat S cap) (e : ℝ)
    (he : ∀ ⦃j⦄, 1 ≤ j → S.eps j ≤ e) (he1 : e < 1) : Stat (S.withEpsMax e he he1) cap :=
  ⟨L.lam, L.nonneg, L.pos, L.vanish, L.summable, L.total, L.inv⟩

/-- The transported invariant probability has the same masses. -/
@[simp] theorem Stat.withEpsMax_lam {cap : Option ℕ} (L : Stat S cap) (e : ℝ)
    (he : ∀ ⦃j⦄, 1 ≤ j → S.eps j ≤ e) (he1 : e < 1) : (L.withEpsMax e he he1).lam = L.lam :=
  rfl

namespace Decay

variable (D : Decay)

/-- The block-ratio constant `Q = (1 − c/2)^{−m₀} + ((c/(2m₀+1))^{m₀})^{−1}` of
`cor:doubling_truncation` Step 4, with `ε_max = c/2` the family's supremum. -/
noncomputable def truncQ (d : ℕ) : ℝ :=
  ((1 - D.c / 2)⁻¹) ^ D.m0 d + ((D.c / (2 * (D.m0 d : ℝ) + 1)) ^ D.m0 d)⁻¹

/-- **`c₉`** of `cor:doubling_truncation`(2): `e^{2c₅c₄/m₀} · 2^{p_*} · Q²`, with `c₄ = 16cτ`. -/
noncomputable def c9Of (d : ℕ) : ℝ :=
  Real.exp (2 * (D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ))) * (2 : ℝ) ^ D.p * D.truncQ d ^ 2

/-- **`K₀ := 8m₀ + 2`** of `cor:doubling_truncation`(2), Step 4. -/
noncomputable def K0Of (d : ℕ) : ℕ := 8 * D.m0 d + 2

/-- **`c₈ := (2^{p_*+4} c₉ (2 + j̄/(1−c)))^{−1/2}`** of `cor:doubling_truncation`(3), Step 7. -/
noncomputable def c8Of (d : ℕ) (jbar : ℝ) : ℝ :=
  (Real.sqrt ((2 : ℝ) ^ (D.p + 4) * D.c9Of d * (2 + jbar / (1 - D.c))))⁻¹

theorem one_le_truncQ (d : ℕ) : 1 ≤ D.truncQ d := by
  have hc := D.c_lt_one
  have hc0 := D.c_pos
  have hpos : 0 < 1 - D.c / 2 := by linarith
  have h1 : 1 ≤ (1 - D.c / 2)⁻¹ := (one_le_inv₀ hpos).mpr (by linarith)
  have h2 : 1 ≤ ((1 - D.c / 2)⁻¹) ^ D.m0 d := one_le_pow₀ h1
  have h3 : 0 < ((D.c / (2 * (D.m0 d : ℝ) + 1)) ^ D.m0 d)⁻¹ := by positivity
  rw [truncQ]
  linarith

/-- `c₉ ≥ 1`. -/
theorem one_le_c9Of (d : ℕ) : 1 ≤ D.c9Of d := by
  have hz : 0 ≤ 2 * (D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ)) := by
    have := D.c5_pos; have := D.c_pos; have := D.tau_pos; positivity
  have he : 1 ≤ Real.exp (2 * (D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ))) := Real.one_le_exp hz
  have h2 : 1 ≤ (2 : ℝ) ^ D.p := Real.one_le_rpow (by norm_num) D.p_pos.le
  have hQ : 1 ≤ D.truncQ d ^ 2 := one_le_pow₀ (D.one_le_truncQ d)
  rw [c9Of]
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he h2) hQ

/-- `K₀ ≥ d` — indeed `K₀ > d`. -/
theorem le_K0Of (d : ℕ) : d ≤ D.K0Of d := by
  have := D.lt_m0 d; rw [K0Of]; omega

/-- `c₈ > 0` when `j̄ ≥ 0`, which every target row has. -/
theorem c8Of_pos (d : ℕ) {jbar : ℝ} (hjb : 0 ≤ jbar) : 0 < D.c8Of d jbar := by
  have hc := D.c_lt_one
  have h9 : 0 < D.c9Of d := lt_of_lt_of_le one_pos (D.one_le_c9Of d)
  have hden : 0 < 2 + jbar / (1 - D.c) := by
    have : 0 ≤ jbar / (1 - D.c) := div_nonneg hjb (by linarith)
    linarith
  rw [c8Of]
  positivity

end Decay

/-! ### Item (2): the decay on the truncation, with constants of `c` and `d` alone -/

namespace Stat

variable {K : ℕ}

/-- **`eq:doubling_decayK` with its constants written out.** For every `K ≥ K₀ = 8m₀ + 2` and
every invariant probability `λ^K` of the truncation there are `0 < C⁻ ≤ C⁺` with `C⁺ ≤ c₉ C⁻` and
`C⁻ m^{−p_*} ≤ λ^K_m ≤ C⁺ m^{−p_*}` for `m₀ ≤ m ≤ K/2`; `m₀ = D.m0 d`, `K₀ = D.K0Of d` and
`c₉ = D.c9Of d` are formulas in `c`, `p_*` and `d`. -/
theorem decayK_explicit (D : Decay) (hDeps : ∀ j, S.eps j = D.eps j) (hK : D.K0Of S.d ≤ K)
    (L : Stat S (some K)) :
    ∃ Cm Cp : ℝ, 0 < Cm ∧ Cm ≤ Cp ∧ Cp ≤ D.c9Of S.d * Cm ∧
      ∀ m : ℕ, D.m0 S.d ≤ m → m ≤ K / 2 →
        Cm * (m : ℝ) ^ (-D.p) ≤ L.lam (.lad m) ∧ L.lam (.lad m) ≤ Cp * (m : ℝ) ^ (-D.p) := by
  -- pass to the bound `ε_max = c/2`, the family's supremum
  have he : ∀ ⦃j⦄, 1 ≤ j → S.eps j ≤ D.c / 2 := fun j hj => by
    rw [hDeps j]; exact D.eps_le_half hj
  have he1 : D.c / 2 < 1 := by have := D.c_lt_one; linarith
  set ℓ : ℕ := D.m0 S.d
  have hℓd : S.d < ℓ := D.lt_m0 S.d
  have hℓ1 : 1 ≤ ℓ := by have := S.d_pos; omega
  have h4ℓK : 4 * ℓ ≤ K := by rw [Decay.K0Of] at hK; omega
  set z : ℝ := D.c5 * (16 * D.c * D.tau) / (ℓ : ℝ)
  obtain ⟨Cm, Cp, hCm, hCp, hbds⟩ :=
    Stat.decayK D (L.withEpsMax (D.c / 2) he he1) hDeps hℓd hℓ1 h4ℓK
      (Real.exp_pos (-z)) (Real.exp_pos z)
      (fun y _ => (D.descOne_two_sided (d := S.d) (le_refl ℓ) y).1)
      (fun y _ => (D.descOne_two_sided (d := S.d) (le_refl ℓ) y).2)
  have hratio : Real.exp z / Real.exp (-z) = Real.exp (2 * z) := by
    rw [← Real.exp_sub]; ring_nf
  have hc9 : Real.exp z / Real.exp (-z) * (2 : ℝ) ^ D.p
      * (((1 - D.c / 2)⁻¹) ^ ℓ + ((D.c / (2 * (ℓ : ℝ) + 1)) ^ ℓ)⁻¹) ^ 2 = D.c9Of S.d := by
    rw [hratio, Decay.c9Of, Decay.truncQ]
  have hbds' : ∀ m : ℕ, ℓ ≤ m → m ≤ K / 2 →
      Cm * (m : ℝ) ^ (-D.p) ≤ L.lam (.lad m) ∧ L.lam (.lad m) ≤ Cp * (m : ℝ) ^ (-D.p) := hbds
  have hCp' : Cp ≤ D.c9Of S.d * Cm := by rw [← hc9]; exact hCp
  refine ⟨Cm, Cp, hCm, ?_, hCp', hbds'⟩
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hx : (0 : ℝ) < (ℓ : ℝ) ^ (-D.p) := rpow_pos_of_pos hℓpos _
  obtain ⟨h1, h2⟩ := hbds' ℓ le_rfl (by omega)
  exact le_of_mul_le_mul_right (le_trans h1 h2) hx

/-! ### Item (3) -/

/-- **`eq:doubling_sqrtK` with its constant written out, at every bounded left inverse.** For
every `K ≥ K₀` and every `S` on `L²(λ^K)` with `S(Id − P⋆) = Id − Π`, `c₈ √K ≤ ‖S‖`, where
`c₈ = D.c8Of d j̄` is a formula in `c`, `p_*`, `d` and `j̄`. -/
theorem sqrtK_explicit (D : Decay) (hDeps : ∀ j, S.eps j = D.eps j) (hK : D.K0Of S.d ≤ K)
    (L : Stat S (some K)) (hrow : RowOnChain S (some K))
    {Sop : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu} (hS : Sop * (1 - L.pstarL2 hrow) = 1 - L.piL2) :
    D.c8Of S.d S.jbar * Real.sqrt (K : ℝ) ≤ ‖Sop‖ := by
  have hc0 := D.c_pos
  have hc1 := D.c_lt_one
  have heps' : ∀ j : ℕ, 1 ≤ j → S.eps j = D.c / ((j : ℝ) + 1) := fun j _ => by
    rw [hDeps j, D.eps_eq]
  have hℓd : S.d < D.m0 S.d := D.lt_m0 S.d
  have hK' : 8 * D.m0 S.d + 2 ≤ K := hK
  have hKd : 4 * (S.d + 1) ≤ K := by omega
  have hK8 : 8 ≤ K := by omega
  obtain ⟨Cm, Cp, hCm, hCmp, hCp, hbds⟩ := L.decayK_explicit D hDeps hK
  have hlo : ∀ j : ℕ, K / 4 ≤ j → j ≤ 2 * (K / 4) →
      Cm * (j : ℝ) ^ (-D.p) ≤ L.lam (.lad j) :=
    fun j hj1 hj2 => (hbds j (by omega) (by omega)).1
  have hhi : L.lam (.lad (K / 4)) ≤ Cp * ((K / 4 : ℕ) : ℝ) ^ (-D.p) :=
    (hbds (K / 4) (by omega) (by omega)).2
  have hB : ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) → (∑' x, L.lam x * f x = 0) →
      L.mass 2 f ≤ ‖Sop‖ ^ 2 * L.mass 2 (fun x => f x - pstar S (some K) f x) :=
    fun f hf hmean => L.mass_le_of_leftInverse hrow hS hf hmean
  have hsq := L.sqrtK D hc0 hc1 heps' hCm hKd hK8 hlo hhi hB
  -- the constants
  have hjb : 0 ≤ S.jbar :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (S.row_nonneg k)
  set X : ℝ := 2 + S.jbar / (1 - D.c)
  have hX : 0 < X := by
    have : 0 ≤ S.jbar / (1 - D.c) := div_nonneg hjb (by linarith)
    linarith
  have h9 : 0 < D.c9Of S.d := lt_of_lt_of_le one_pos (D.one_le_c9Of S.d)
  have htwo : (0 : ℝ) < (2 : ℝ) ^ D.p := rpow_pos_of_pos two_pos _
  have hCp0 : 0 < Cp := lt_of_lt_of_le hCm hCmp
  have h24 : (2 : ℝ) ^ (D.p + 4) = (2 : ℝ) ^ D.p * 16 := by
    rw [Real.rpow_add two_pos]; norm_num
  set Y : ℝ := (2 : ℝ) ^ (D.p + 4) * D.c9Of S.d * X with hYdef
  have hY : 0 < Y := by rw [hYdef]; positivity
  -- `c₈² K = K / Y ≤ Cm/(Cp 2^p 16 X) K ≤ ‖S‖²`
  have hc8sq : D.c8Of S.d S.jbar ^ 2 = Y⁻¹ := by
    rw [Decay.c8Of, inv_pow, Real.sq_sqrt hY.le]
  have hle : Y⁻¹ ≤ Cm / (Cp * (2 : ℝ) ^ D.p * 16 * X) := by
    rw [hYdef, h24, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : Cp * X ≤ D.c9Of S.d * Cm * X := mul_le_mul_of_nonneg_right hCp hX.le
    nlinarith [htwo]
  have hmain : (D.c8Of S.d S.jbar * Real.sqrt (K : ℝ)) ^ 2 ≤ ‖Sop‖ ^ 2 := by
    rw [mul_pow, hc8sq, Real.sq_sqrt (Nat.cast_nonneg K)]
    exact le_trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg K)) hsq
  have hlhs : 0 ≤ D.c8Of S.d S.jbar * Real.sqrt (K : ℝ) :=
    mul_nonneg (D.c8Of_pos S.d hjb).le (Real.sqrt_nonneg _)
  calc D.c8Of S.d S.jbar * Real.sqrt (K : ℝ)
      = Real.sqrt ((D.c8Of S.d S.jbar * Real.sqrt (K : ℝ)) ^ 2) := (Real.sqrt_sq hlhs).symm
    _ ≤ Real.sqrt (‖Sop‖ ^ 2) := Real.sqrt_le_sqrt hmain
    _ = ‖Sop‖ := Real.sqrt_sq (norm_nonneg _)

/-- **`eq:doubling_sqrtK`, as written.** `B̂_K ≥ c₈ √K` for every `K ≥ K₀`. -/
theorem sqrtK_bhatK (D : Decay) (hDeps : ∀ j, S.eps j = D.eps j) (hK : D.K0Of S.d ≤ K)
    (hdK : S.d ≤ K) (L : Stat S (some K)) :
    D.c8Of S.d S.jbar * Real.sqrt (K : ℝ) ≤ L.bhatK hdK :=
  L.sqrtK_explicit D hDeps hK (rowOnChain_some hdK) (L.diffOpK_resolvent hdK).2.1

end Stat

/-! ### The corollary, in the paper's quantifier order -/

/-- **`cor:doubling_truncation`, with its constants.** At `s = 1`, for any `Decay` `D` carrying the
family (`ε(j) = c/(j+1)`, `p = p_*`), with `m₀ = D.m0 d`, `K₀ = D.K0Of d = 8m₀+2`,
`c₉ = D.c9Of d` and `c₈ = D.c8Of d j̄`:
(1) `B̂_K ≥ √(L_K(m)(1−L_K(m))/(2λ^K_m))` for `K ≥ d`, `d < m ≤ K/2`;
(2) `K₀ ≥ d`, `c₉ ≥ 1`, and every `K ≥ K₀` has `0 < C⁻ ≤ C⁺`, `C⁺/C⁻ ≤ c₉`, and the sandwich
`eq:doubling_decayK` on `m₀ ≤ m ≤ K/2`;
(3) `c₈ > 0` and `B̂_K ≥ c₈√K` for every `K ≥ K₀`. -/
theorem truncation_explicit (D : Decay) (hDeps : ∀ j, S.eps j = D.eps j) :
    (∀ (K : ℕ) (hdK : S.d ≤ K) (L : Stat S (some K)) (m : ℕ), S.d < m → m ≤ K / 2 →
        Real.sqrt (L.tailMass m * (1 - L.tailMass m) / (2 * L.lam (.lad m))) ≤ L.bhatK hdK) ∧
      S.d ≤ D.K0Of S.d ∧ 1 ≤ D.c9Of S.d ∧
      (∀ K : ℕ, D.K0Of S.d ≤ K → ∀ L : Stat S (some K),
        ∃ Cm Cp : ℝ, 0 < Cm ∧ Cm ≤ Cp ∧ Cp / Cm ≤ D.c9Of S.d ∧
          ∀ m : ℕ, D.m0 S.d ≤ m → m ≤ K / 2 →
            Cm * (m : ℝ) ^ (-D.p) ≤ L.lam (.lad m) ∧ L.lam (.lad m) ≤ Cp * (m : ℝ) ^ (-D.p)) ∧
      0 < D.c8Of S.d S.jbar ∧
      ∀ (K : ℕ), D.K0Of S.d ≤ K → ∀ (hdK : S.d ≤ K) (L : Stat S (some K)),
        D.c8Of S.d S.jbar * Real.sqrt (K : ℝ) ≤ L.bhatK hdK := by
  have hjb : 0 ≤ S.jbar :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (S.row_nonneg k)
  refine ⟨fun K hdK L m hdm hmK => L.percut_bhatK hdK hdm hmK, D.le_K0Of S.d, D.one_le_c9Of S.d,
    fun K hK L => ?_, D.c8Of_pos S.d hjb, fun K hK hdK L => L.sqrtK_bhatK D hDeps hK hdK⟩
  obtain ⟨Cm, Cp, hCm, hCmp, hCp, hbds⟩ := L.decayK_explicit D hDeps hK
  exact ⟨Cm, Cp, hCm, hCmp, (div_le_iff₀ hCm).mpr hCp, hbds⟩

/-- **`cor:doubling_truncation`.** At `s = 1`, `0 < c < 1`, with `p_*` the Cramér root, for every
`d` there are `m₀`, `K₀ ≥ d` and `c₉ ≥ 1`, and for every `j̄ ≥ 0` a `c₈ > 0`, such that every
setting with that `d`, that `j̄` and the family `ε(j) = c/(j+1)` has:
(1) for every `K ≥ d` and `d < m ≤ K/2`, `B̂_K ≥ √(L_K(m)(1−L_K(m))/(2λ^K_m))`;
(2) every `K ≥ K₀` has `0 < C⁻_K ≤ C⁺_K` with `C⁺_K/C⁻_K ≤ c₉` and
`C⁻_K m^{−p_*} ≤ λ^K_m ≤ C⁺_K m^{−p_*}` for `m₀ ≤ m ≤ K/2`;
(3) `B̂_K ≥ c₈√K` for every `K ≥ K₀`, `K₀` the integer of (2).
The existentials precede the setting, so `m₀, K₀, c₉` depend only on `c, d` and `c₈` only on
`c, d, j̄`; the witnesses are those of `truncation_explicit` at `Decay.ofC`. -/
theorem main_truncation {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ p : ℝ, psi c p = 0 ∧ 1 < p ∧
      ∀ d : ℕ, ∃ m₀ K₀ : ℕ, ∃ c₉ : ℝ, d ≤ K₀ ∧ 1 ≤ c₉ ∧
        ∀ jbar : ℝ, 0 ≤ jbar → ∃ c₈ : ℝ, 0 < c₈ ∧
          ∀ S : Setting, S.d = d → S.jbar = jbar → (∀ j, S.eps j = epsCS c 1 j) →
            (∀ (K : ℕ) (hdK : S.d ≤ K) (L : Stat S (some K)) (m : ℕ), S.d < m → m ≤ K / 2 →
              Real.sqrt (L.tailMass m * (1 - L.tailMass m) / (2 * L.lam (.lad m)))
                ≤ L.bhatK hdK) ∧
            (∀ K : ℕ, K₀ ≤ K → ∀ L : Stat S (some K),
              ∃ Cm Cp : ℝ, 0 < Cm ∧ Cm ≤ Cp ∧ Cp / Cm ≤ c₉ ∧
                ∀ m : ℕ, m₀ ≤ m → m ≤ K / 2 →
                  Cm * (m : ℝ) ^ (-p) ≤ L.lam (.lad m) ∧ L.lam (.lad m) ≤ Cp * (m : ℝ) ^ (-p)) ∧
            ∀ (K : ℕ), K₀ ≤ K → ∀ (hdK : S.d ≤ K) (L : Stat S (some K)),
              c₈ * Real.sqrt (K : ℝ) ≤ L.bhatK hdK := by
  set D : Decay := Decay.ofC hc0 hc1
  have hroot : psi c D.p = 0 := D.root
  refine ⟨D.p, hroot, D.p_gt_one, fun d => ⟨D.m0 d, D.K0Of d, D.c9Of d, D.le_K0Of d,
    D.one_le_c9Of d, fun jbar hjb => ⟨D.c8Of d jbar, D.c8Of_pos d hjb,
      fun S hSd hSj heps => ?_⟩⟩⟩
  subst hSd hSj
  obtain ⟨h1, -, -, h2, -, h3⟩ := truncation_explicit D (eps_eq_decay_eps heps D rfl)
  exact ⟨h1, h2, h3⟩

end GFNBounds.Doubling
