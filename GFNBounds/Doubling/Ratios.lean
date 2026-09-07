import GFNBounds.Doubling.CutBalance

/-!
# The one-step ratio inequalities

**`prop:doubling_cut`, `eq:doubling_ratios`** — `app_doubling.tex:641–692`.

> for every `j ≥ 1` with `2j` a state and every `m ≥ 2`:
> `λ_{2j} ≥ λ_j ε(j)` and `λ_m ≤ λ_{m−1}/(1 − ε(m))`.

The first is the only input `theo:doubling_unbounded` Step 1 needs beyond the growth condition
(★): iterating it along the powers of two gives `L(2^D) ≥ λ_1 Π_{i<D} ε(2^i)`, which contradicts a
tail decaying exponentially in `2^D`. The second bounds the mass at a cut by the mass just below.

## How pointwise balance is obtained without a `kern` layer

Both are statements of *pointwise* balance at a single state, where `Stat` carries invariance only
in the integral form `∫ P⋆f dλ = ∫ f dλ`. No bridge lemma is needed: testing that identity against
the point mass `dirac j`, which is bounded, gives

  `λ_j = ∑' x, λ_x · (P⋆ 1_{\{j\}})(x)`,

and `(P⋆ 1_{\{j\}})(x)` is precisely the one-step probability of `x → j`. Every summand is
non-negative (`pstar_nonneg`), so keeping a single one and discarding the rest — `le_hasSum` —
gives each inequality. The transition matrix is never written down.

## SCOPE (disclosed)

`lam_double_ge` needs `HasDouble cap j`, which on the loop closure is vacuous and on the
truncation is the paper's "with `2j` a state". `lam_le_prev` holds on either chain, whether or not
the doubling edge at `m` survives: when it does not, the decrement carries the whole mass, and the
inequality is only slacker.

## Hypothesis checklist against `eq:doubling_ratios`

| paper hypothesis | here |
|---|---|
| `ε(j) ∈ (0,1)` for every `j ≥ 1` | ✓ carried (in `Setting`) |
| `λ` any invariant probability | ✓ carried (`Stat`) |
| `j ≥ 1`, `2j` a state | ✓ `hj`, `hD` |
| `m ≥ 2` | ✓ `hm` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

variable {S : Setting} {cap : Option ℕ}

theorem dirac_nonneg (j : ℕ) (x : St) : 0 ≤ dirac j x := by
  rw [dirac]; split <;> norm_num

theorem dirac_bounded (j : ℕ) : ∃ C, ∀ x, |dirac j x| ≤ C :=
  ⟨1, fun x => by rw [abs_of_nonneg (dirac_nonneg j x), dirac]; split <;> norm_num⟩

/-- **Pointwise balance, from the integral form.** `λ_j` is the total one-step flux into `j`.

This is `Stat.inv` tested against `dirac j`; the right-hand side is `λ_j` by
`tsum_lam_mul_dirac`. -/
theorem Stat.hasSum_flux (L : Stat S cap) (j : ℕ) :
    HasSum (fun x => L.lam x * pstar S cap (dirac j) x) (L.lam (.lad j)) := by
  have hsum : Summable (fun x => L.lam x * pstar S cap (dirac j) x) := by
    obtain ⟨C, hC⟩ := dirac_bounded j
    exact L.summable_mul ⟨C, fun x => pstar_bounded hC x⟩
  have := hsum.hasSum
  rwa [L.inv (dirac j) (dirac_bounded j), tsum_lam_mul_dirac] at this

/-- Every one-step flux term is non-negative, so a single one may be kept and the rest discarded. -/
theorem Stat.flux_nonneg (L : Stat S cap) (j : ℕ) (x : St) :
    0 ≤ L.lam x * pstar S cap (dirac j) x :=
  mul_nonneg (L.nonneg x) (pstar_nonneg (dirac_nonneg j) x)

/-- The doubling edge out of `j` carries `ε(j)` into `2j`. -/
theorem pstar_dirac_double {j : ℕ} (hj : 1 ≤ j) (hD : HasDouble cap j) :
    pstar S cap (dirac (2 * j)) (.lad j) = S.eps j := by
  rw [pstar_lad_of_hasDouble hj hD, dirac_lad, dirac_lad, if_pos rfl,
    if_neg (by omega : ¬ (j - 1 = 2 * j))]
  ring

/-- The decrement edge out of `m` carries at least `1 − ε(m)` into `m − 1`, with equality when the
doubling edge survives and value `1` when it has been truncated away. -/
theorem one_sub_eps_le_pstar_dirac_pred {m : ℕ} (hm : 1 ≤ m) :
    1 - S.eps m ≤ pstar S cap (dirac (m - 1)) (.lad m) := by
  by_cases hD : HasDouble cap m
  · rw [pstar_lad_of_hasDouble hm hD, dirac_lad, dirac_lad, if_pos rfl,
      if_neg (by omega : ¬ (2 * m = m - 1))]
    have := (S.eps_pos hm).le
    nlinarith
  · rw [pstar_lad_of_not_hasDouble hm hD, dirac_lad, if_pos rfl]
    have := (S.eps_pos hm).le
    linarith

/-- **`eq:doubling_ratios`, first half.** `λ_{2j} ≥ λ_j ε(j)`: the doubling edge out of `j`
deposits at least its own share at `2j`, whatever else arrives there. -/
theorem Stat.lam_double_ge (L : Stat S cap) {j : ℕ} (hj : 1 ≤ j) (hD : HasDouble cap j) :
    L.lam (.lad j) * S.eps j ≤ L.lam (.lad (2 * j)) := by
  have h := le_hasSum (L.hasSum_flux (2 * j)) (St.lad j) fun x _ => L.flux_nonneg (2 * j) x
  rwa [pstar_dirac_double hj hD] at h

/-- **`eq:doubling_ratios`, second half.** `λ_m (1 − ε(m)) ≤ λ_{m−1}`. -/
theorem Stat.lam_le_prev (L : Stat S cap) {m : ℕ} (hm : 1 ≤ m) :
    L.lam (.lad m) * (1 - S.eps m) ≤ L.lam (.lad (m - 1)) := by
  have h := le_hasSum (L.hasSum_flux (m - 1)) (St.lad m) fun x _ => L.flux_nonneg (m - 1) x
  refine le_trans ?_ h
  exact mul_le_mul_of_nonneg_left (one_sub_eps_le_pstar_dirac_pred hm) (L.nonneg _)

end GFNBounds.Doubling
