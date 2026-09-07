import GFNBounds.Doubling.CutBalance

/-!
# The one-step ratio inequalities

**`prop:doubling_cut`, `eq:doubling_ratios`** — `app_doubling.tex:641–692`.

> for every `j ≥ 1` with `2j` a state and every `m ≥ 2`:
> `λ_{2j} ≥ λ_j ε(j)` and `λ_m ≤ λ_{m−1}/(1 − ε(m))`.

The first is `theo:doubling_unbounded` Step 1's only input beyond the growth condition (★): it is
what gives `L(2^D) ≥ λ_1 Π_{i<D} ε(2^i)` and so contradicts an exponentially decaying tail. The
second bounds the mass at a cut by the mass just below it.

Both are *pointwise* balance at a single state, so they need the pointwise form `λT = λ` rather
than the integral form carried by `Stat.inv`. The bridge is available in principle — testing
`Stat.inv` against `dirac j`, which is bounded, gives pointwise balance at `lad j` — but it needs
the one-step law of `P⋆`'s adjoint written out, which is the `kern` layer this library has not
built yet.

## SCOPE (disclosed)

Both statements are **open here**. Nothing in `GFNBounds/` depends on them.
-/

namespace GFNBoundsScaffold.Doubling

open GFNBounds.Doubling

variable {S : Setting} {cap : Option ℕ}

/-- `λ_{2j} ≥ λ_j ε(j)`: the doubling edge out of `j` deposits at least its own mass at `2j`. -/
theorem lam_double_ge (L : Stat S cap) {j : ℕ} (hj : 1 ≤ j) (hD : HasDouble cap j) :
    L.lam (.lad j) * S.eps j ≤ L.lam (.lad (2 * j)) :=
  sorry -- SORRY(prop:doubling_cut): needs pointwise balance at `lad (2j)`; the `kern` layer and the `Stat.inv`-tested-against-`dirac` bridge are not built.

/-- `λ_m ≤ λ_{m−1}/(1 − ε(m))`. -/
theorem lam_le_prev (L : Stat S cap) {m : ℕ} (hm : 2 ≤ m) :
    L.lam (.lad m) * (1 - S.eps m) ≤ L.lam (.lad (m - 1)) :=
  sorry -- SORRY(prop:doubling_cut): same missing bridge as `lam_double_ge`.

end GFNBoundsScaffold.Doubling
