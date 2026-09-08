import GFNBounds.Doubling.PerCutIdentity

/-!
# Cut balance

**`prop:doubling_cut`** — `app_doubling.tex:641–692`, `eq:doubling_cut`
(Proposition 100 of the ICLR build).

> Let `ε(j) ∈ (0,1)` for every `j ≥ 1` and let `λ` be **any** invariant probability of the
> loop-closed chain. Then for every `m > d`,
> `λ_m (1 − ε(m)) = Σ_{j=⌈m/2⌉}^{m−1} λ_j ε(j)`.
> On the truncation at even `K ≥ d`, the same holds for `d < m ≤ K/2`.

This is the identity `exp20` measured exact to `0.0e0` at every cut, and it is the recursion the
whole decay block analyses. Here it is the `λ`-integral of the pointwise identity
`eq:doubling_step1` of `GFNBounds.Doubling.PerCutIdentity`: the defect `(Id − P⋆)1_A` is finitely
supported, so integrating it against `λ` and using invariance is the whole proof.

## SCOPE (disclosed)

The truncation clause is not a separate theorem: the `cap` parameter carries it, and the paper's
range condition `d < m ≤ K/2` is exactly `hdm` together with `hD : HasDouble cap m`, which unfolds
to `2m ≤ K`.

Note what the hypothesis is **not**. `cut_balance` is stated for a `Stat`, an invariant
probability; but the downstream decay results (`theo:doubling_decay`, `theo:doubling_sharp`) are
stated in the paper for an *arbitrary positive sequence* satisfying the recursion, with no
invariance and no normalisation — and `cor:doubling_truncation` Step 4 relies on that, feeding them
`λ^K` extended past the cap by `1`. `CutBalanceSeq` below is that weaker predicate, and it is what
those results will consume; `cut_balance` is the bridge saying an invariant probability satisfies
it.

## Hypothesis checklist against `prop:doubling_cut`

| paper hypothesis | here |
|---|---|
| `ε(j) ∈ (0,1)` for every `j ≥ 1` | ⚠ strengthened: `Setting` carries `sup ε ≤ ε_max < 1`; only per-edge positivity is used |
| `λ` any invariant probability | ✓ carried (`Stat`; positivity a field, derivable via `PreStat.toStatNone`) |
| `m > d` | ✓ carried (`hdm`) |
| truncation: `K` even, `d < m ≤ K/2` | ✓ `hdm` and `hD`; ⚠ weakened, evenness unused |
| `eq:doubling_ratios` (`λ_{2j} ≥ λ_j ε(j)`, `λ_m ≤ λ_{m−1}/(1−ε(m))`) | ✓ `Stat.lam_double_ge`, `Stat.lam_le_prev` (`Ratios.lean`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

variable {S : Setting} {cap : Option ℕ}

/-- `λ` against a point mass is the mass of the point. -/
theorem lam_mul_dirac_eq (L : Stat S cap) (j : ℕ) :
    (fun x => L.lam x * dirac j x) = (fun x => if x = St.lad j then L.lam (St.lad j) else 0) := by
  funext x
  by_cases h : x = St.lad j
  · subst h; simp [dirac]
  · simp [dirac, h]

theorem hasSum_lam_mul_dirac (L : Stat S cap) (j : ℕ) :
    HasSum (fun x => L.lam x * dirac j x) (L.lam (.lad j)) := by
  rw [lam_mul_dirac_eq]; exact hasSum_ite_eq _ _

theorem summable_lam_mul_dirac (L : Stat S cap) (j : ℕ) :
    Summable (fun x => L.lam x * dirac j x) := (hasSum_lam_mul_dirac L j).summable

theorem tsum_lam_mul_dirac (L : Stat S cap) (j : ℕ) :
    ∑' x, L.lam x * dirac j x = L.lam (.lad j) := (hasSum_lam_mul_dirac L j).tsum_eq

/-- The `λ`-integral of the per-cut defect vanishes: this is invariance, tested against `1_A`. -/
theorem tsum_lam_mul_cutFn (L : Stat S cap) {m : ℕ} (hdm : S.d < m) (hD : HasDouble cap m) :
    ∑' x, L.lam x * cutFn S m x = 0 := by
  have key : ∀ x, L.lam x * cutFn S m x
      = L.lam x * (tailInd cap m x - pstar S cap (tailInd cap m) x) := by
    intro x
    by_cases hx : OnChain cap x
    · rw [percut_id S cap hdm hD hx]
    · rw [L.vanish hx, zero_mul, zero_mul]
  simp only [key]
  exact L.tsum_sub_pstar tailInd_bounded

/-- **`eq:doubling_cut`.** The mass leaving the cut at `m` by decrement equals the mass entering it
from the window below by doubling. -/
theorem cut_balance (L : Stat S cap) {m : ℕ} (hdm : S.d < m) (hD : HasDouble cap m) :
    L.lam (.lad m) * (1 - S.eps m) = ∑ j ∈ window m, L.lam (.lad j) * S.eps j := by
  have expand : ∀ x, L.lam x * cutFn S m x
      = (1 - S.eps m) * (L.lam x * dirac m x)
        - ∑ y ∈ window m, S.eps y * (L.lam x * dirac y x) := by
    intro x
    rw [cutFn, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun y _ => by ring
  have hA : HasSum (fun x => (1 - S.eps m) * (L.lam x * dirac m x))
      ((1 - S.eps m) * L.lam (.lad m)) := (hasSum_lam_mul_dirac L m).mul_left _
  have hB : HasSum (fun x => ∑ y ∈ window m, S.eps y * (L.lam x * dirac y x))
      (∑ y ∈ window m, S.eps y * L.lam (.lad y)) :=
    hasSum_sum fun y _ => (hasSum_lam_mul_dirac L y).mul_left _
  have hC : HasSum (fun x => L.lam x * cutFn S m x)
      ((1 - S.eps m) * L.lam (.lad m) - ∑ y ∈ window m, S.eps y * L.lam (.lad y)) := by
    rw [funext expand]; exact hA.sub hB
  have hzero := tsum_lam_mul_cutFn L hdm hD
  rw [hC.tsum_eq] at hzero
  have hcomm : ∑ y ∈ window m, S.eps y * L.lam (.lad y)
      = ∑ j ∈ window m, L.lam (.lad j) * S.eps j :=
    Finset.sum_congr rfl fun y _ => mul_comm _ _
  rw [hcomm] at hzero
  linarith [hzero]

/-- The recursion `eq:doubling_cut` as a predicate on a bare real sequence, with no invariance and
no normalisation.

This is the hypothesis `theo:doubling_decay` and `theo:doubling_sharp` actually carry
(`app_doubling.tex:1155`, `:1323`: "any positive sequence satisfying `eq:doubling_cut` at every
`m > d`"), and stating it this way is what lets `cor:doubling_truncation` apply them to `λ^K`
extended past the cap. `M₁` is the upper end of the range on which the recursion is asserted:
`⊤` on the loop closure, `K/2` on the truncation. -/
def CutBalanceSeq (S : Setting) (lam : ℕ → ℝ) (M₁ : ℕ∞) : Prop :=
  ∀ m : ℕ, S.d < m → (m : ℕ∞) ≤ M₁ →
    lam m * (1 - S.eps m) = ∑ j ∈ window m, lam j * S.eps j

/-- An invariant probability of the loop closure gives a sequence satisfying the recursion
everywhere: the bridge from `Stat` to `CutBalanceSeq`. -/
theorem cutBalanceSeq_of_stat (L : Stat S none) :
    CutBalanceSeq S (fun j => L.lam (.lad j)) ⊤ :=
  fun _ hm _ => cut_balance L hm trivial

end GFNBounds.Doubling
