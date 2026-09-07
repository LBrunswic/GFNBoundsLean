import GFNBounds.Doubling.Balance
import GFNBounds.Doubling.LpContraction

/-!
# The density action `P`, and `P⋆ = P*`

**`lem:doubling_operator`(1), the adjoint clause** — `app_doubling.tex:166–262`.

> let `P` be its density action `Pu := d((uλ)T)/dλ` and `P⋆` its function action
> `(P⋆v)(x) := ∫v dT(x,·)` […] `P⋆` is a contraction of `L^p(λ)` for every `p ∈ [1,+∞]` and is the
> `L²(λ)`-adjoint of `P`.
>
> […] the display reads `⟨Pu,v⟩_λ = ⟨u,P⋆v⟩_λ`, that is `P⋆ = P*`.

The density action was, until this file, the one object of `def:doubling_setting` that the library
did not model (`Setting.lean`, SCOPE). It is modelled here in closed form, like `P⋆`:

  `(Pu)(s_f) = u(s₀)`,
  `(Pu)(j) = w₁(j)·u(j+1) + w₂(j)·u(j/2) + w₃(j)·u(s_f)`,

with `w₁(j) = λ_{j+1}dec(j+1)/λ_j`, `w₂(j) = λ_{j/2}dbl(j/2)/λ_j` when `j` is even and positive
and `0` otherwise, and `w₃(j) = λ(s_f)row(j)/λ_j` — the reversed one-step law
`T̂(y,x) = λ(x)T(x,y)/λ(y)`. Its weights are non-negative and, **by the balance equations**
`Stat.mact_lam`, sum to `1` at every state of the chain: `P` is again an averaging operator, and
every argument that Jensen's inequality gives for `P⋆` it gives for `P` verbatim.

## What is proved, and what it costs

* `Stat.tsum_dens_mul` is `⟨Pu,v⟩_λ = ⟨u,P⋆v⟩_λ` at **bounded** `v`; `Stat.tsum_dens_mul_sq`
  removes that restriction by truncation and states it at `u,v ∈ L²(λ)`, which is the paper's
  hypothesis pair. Together they are the adjoint clause on the plain-real layer.
* `Stat.mass_dens_le` and `Stat.eLpNorm_dens_le` are the `L^p(λ)` contraction of `P`,
  `p ∈ [1,∞)`, which the paper does not state separately — it reads it off the adjoint and the
  contraction of `P⋆`. Here it is proved directly from Jensen for `T̂`, and it is what makes `P`
  an operator of `L²(λ)` at all.
* `Stat.dens_const` is `P1 = 1` on the chain, the invariance of `λ` read at the level of `P`, and
  `Stat.tsum_lam_pstar_sq` is the invariance identity `∫P⋆v dλ = ∫v dλ` widened from the bounded
  test functions of `Stat.inv` to `v ∈ L²(λ)`.

## SCOPE (disclosed)

* **`P` is defined by its closed form, not by a Radon–Nikodym derivative.** The paper's
  `d((uλ)T)/dλ` is characterised by `∫v d((uλ)T) = ⟨Pu,v⟩_λ` at every bounded `v`; that is
  `Stat.tsum_dens_mul` read with `Balance.tsum_mact`, and it pins `Pu` at every state of the
  chain, `λ` being positive there. No Riesz representation theorem is used, and none is needed:
  the space is a weighted sequence space.
* **The identity is on the plain-real layer**, `∑' x, λ(x)·(Pu)(x)·v(x) = ∑' x, λ(x)·u(x)·(P⋆v)(x)`.
  Its transcription into `⟪·,·⟫` on `MeasureTheory.Lp ℝ 2 μ` needs the Bochner-integral half of the
  `LpLayer` dictionary, which is not built; so `ContinuousLinearMap.adjoint (pstarL2) = densL2`
  is **not** claimed here, and neither is `‖P⋆^n − Π‖ = β̂_n`, which is its corollary.
* **`RowOnChain` is carried**, as everywhere in this layer: off the chain the transported measure
  must vanish for `Pu := (uλ)T/λ` to be the honest quotient, and at the sink that is exactly
  `d ≤ K` (`LpLayer`, SCOPE).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `T` Markov with invariant probability `λ` | ✓ carried (`Stat`) |
| `λ` positive at every state | ✓ carried on the chain (`Stat.pos`), which is where `P` divides |
| `u, v ∈ L²(λ)` | ✓ carried in `tsum_dens_mul_sq`; ⚠ `v` bounded in `tsum_dens_mul` |
| Fubini for `T(x,dy)λ(dx)` | ✓ replaced by `Balance.hasSum_mact`, a rearrangement of four series |
| Riesz representation | ⚠ **not used** — `P` is exhibited, not extracted |
| — | ⚠ **added**: `RowOnChain S cap` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Filter Topology Real MeasureTheory
open scoped ENNReal NNReal

variable {S : Setting} {cap : Option ℕ}

/-! ## 0. Three-point Jensen -/

/-- Jensen's inequality for a three-atom probability and the convex `t ↦ |t|^p`, `p ≥ 1`. -/
theorem abs_rpow_add3_le {w₁ w₂ w₃ u₁ u₂ u₃ p : ℝ} (h1 : 0 ≤ w₁) (h2 : 0 ≤ w₂) (h3 : 0 ≤ w₃)
    (hw : w₁ + w₂ + w₃ = 1) (hp : 1 ≤ p) :
    |w₁ * u₁ + w₂ * u₂ + w₃ * u₃| ^ p ≤ w₁ * |u₁| ^ p + w₂ * |u₂| ^ p + w₃ * |u₃| ^ p := by
  have hw' : ∑ i : Fin 3, ![w₁, w₂, w₃] i = 1 := by
    simp [Fin.sum_univ_three]; linarith
  have hwn : ∀ i ∈ Finset.univ, 0 ≤ ![w₁, w₂, w₃] i := by
    intro i _; fin_cases i <;> simpa using ‹_›
  have hzn : ∀ i ∈ Finset.univ, 0 ≤ ![|u₁|, |u₂|, |u₃|] i := by
    intro i _; fin_cases i <;> simp
  have hkey := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ ![w₁, w₂, w₃]
    ![|u₁|, |u₂|, |u₃|] hwn hw' hzn hp
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hkey
  have htri : |w₁ * u₁ + w₂ * u₂ + w₃ * u₃| ≤ w₁ * |u₁| + w₂ * |u₂| + w₃ * |u₃| := by
    calc |w₁ * u₁ + w₂ * u₂ + w₃ * u₃| ≤ |w₁ * u₁ + w₂ * u₂| + |w₃ * u₃| := abs_add_le _ _
      _ ≤ |w₁ * u₁| + |w₂ * u₂| + |w₃ * u₃| := by
          have := abs_add_le (w₁ * u₁) (w₂ * u₂); linarith
      _ = w₁ * |u₁| + w₂ * |u₂| + w₃ * |u₃| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3]
  have hmono : |w₁ * u₁ + w₂ * u₂ + w₃ * u₃| ^ p ≤ (w₁ * |u₁| + w₂ * |u₂| + w₃ * |u₃|) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) htri (by linarith)
  linarith

/-! ## 1. The transported measure vanishes off the chain -/

/-- Off the chain the transported measure vanishes: no edge of the chain leaves it.

The decrement source `k+1` is itself off the chain; the doubling source `k/2` has had its edge
truncated away, since `2(k/2) = k > K`; and the target row is supported in `{1,…,d} ⊆ {0,…,K}`,
which is `RowOnChain`. -/
theorem mact_vanish_offChain (hrow : RowOnChain S cap) {nu : St → ℝ}
    (hnu : ∀ x, ¬ OnChain cap x → nu x = 0) {y : St} (hy : ¬ OnChain cap y) :
    mact S cap nu y = 0 := by
  rcases y with k | _
  · rw [mact_lad]
    have h1 : nu (St.lad (k + 1)) = 0 := hnu _ fun hc => hy (onChain_lad_of_succ hc)
    have h2 : (if 1 ≤ k ∧ 2 ∣ k then nu (St.lad (k / 2)) * dblW S cap (k / 2) else 0) = 0 := by
      by_cases hc : 1 ≤ k ∧ 2 ∣ k
      · rw [if_pos hc, dblW, if_neg, mul_zero]
        intro hD
        obtain ⟨-, m, hm⟩ := hc
        have hk2 : 2 * (k / 2) = k := by omega
        exact hy (hk2 ▸ onChain_double hD)
      · rw [if_neg hc]
    have h3 : S.row k = 0 := by
      by_contra hne
      obtain ⟨hk1, hkd⟩ := S.row_supp hne
      exact hy (hrow k hk1 hkd)
    rw [h1, h2, h3, zero_mul, mul_zero]
    ring
  · exact absurd (onChain_sink cap) hy

/-! ## 2. The density action -/

namespace Stat

variable (L : Stat S cap)

/-- **The density action** `Pu := d((uλ)T)/dλ`, in closed form: the transported measure `(uλ)T`
of `Balance.mact`, divided by `λ`. -/
noncomputable def dens (u : St → ℝ) (y : St) : ℝ :=
  mact S cap (fun x => L.lam x * u x) y / L.lam y

/-- The reversed one-step law: the decrement weight, read backwards. -/
noncomputable def w1 (k : ℕ) : ℝ := L.lam (.lad (k + 1)) * decW S cap (k + 1) / L.lam (.lad k)

/-- The reversed one-step law: the doubling weight, read backwards. -/
noncomputable def w2 (k : ℕ) : ℝ :=
  (if 1 ≤ k ∧ 2 ∣ k then L.lam (.lad (k / 2)) * dblW S cap (k / 2) else 0) / L.lam (.lad k)

/-- The reversed one-step law: the target-row weight, read backwards. -/
noncomputable def w3 (k : ℕ) : ℝ := L.lam .sink * S.row k / L.lam (.lad k)

theorem w1_nonneg (k : ℕ) : 0 ≤ L.w1 k :=
  div_nonneg (mul_nonneg (L.nonneg _) (decW_nonneg (Nat.le_add_left 1 k))) (L.nonneg _)

theorem w2_nonneg (k : ℕ) : 0 ≤ L.w2 k := by
  refine div_nonneg ?_ (L.nonneg _)
  by_cases hc : 1 ≤ k ∧ 2 ∣ k
  · rw [if_pos hc]
    exact mul_nonneg (L.nonneg _) (dblW_nonneg (by omega))
  · rw [if_neg hc]

theorem w3_nonneg (k : ℕ) : 0 ≤ L.w3 k :=
  div_nonneg (mul_nonneg (L.nonneg _) (S.row_nonneg k)) (L.nonneg _)

/-- **The reversed law is a probability at every state of the chain.** This is the balance
equation `λT = λ` divided by `λ_k`, and it is the only place invariance enters. -/
theorem w_sum {k : ℕ} (hk : OnChain cap (.lad k)) : L.w1 k + L.w2 k + L.w3 k = 1 := by
  have hpos : L.lam (St.lad k) ≠ 0 := (L.pos hk).ne'
  rw [w1, w2, w3, ← add_div, ← add_div, div_eq_one_iff_eq hpos]
  exact (L.lam_lad k).symm

/-- `P` at the sink: the wrap is the only incoming edge, so `(Pu)(s_f) = u(s₀)`. -/
theorem dens_sink (u : St → ℝ) : L.dens u .sink = u (.lad 0) := by
  rw [dens, mact_sink]
  rw [L.lam_sink]
  exact mul_div_cancel_left₀ _ (L.pos (onChain_src cap)).ne'

/-- `P` at a ladder state, as a three-atom average. -/
theorem dens_lad (u : St → ℝ) (k : ℕ) :
    L.dens u (.lad k)
      = L.w1 k * u (.lad (k + 1)) + L.w2 k * u (.lad (k / 2)) + L.w3 k * u .sink := by
  rw [dens, mact_lad, w1, w2, w3]
  by_cases hc : 1 ≤ k ∧ 2 ∣ k
  · rw [if_pos hc, if_pos hc]; ring
  · rw [if_neg hc, if_neg hc]; ring

/-- **`λ·Pu = (uλ)T`.** On the chain this is the definition with the division cleared; off it both
sides vanish, `λ` by `Stat.vanish` and the transported measure by `mact_vanish_offChain`. -/
theorem lam_mul_dens (hrow : RowOnChain S cap) (u : St → ℝ) (y : St) :
    L.lam y * L.dens u y = mact S cap (fun x => L.lam x * u x) y := by
  by_cases hy : OnChain cap y
  · rw [dens, mul_div_cancel₀ _ (L.pos hy).ne']
  · rw [L.vanish hy, zero_mul]
    exact (mact_vanish_offChain hrow (fun x hx => by rw [L.vanish hx, zero_mul]) hy).symm

/-- **`P` fixes the constants** on the chain: the reversed law is a probability. -/
theorem dens_const (hrow : RowOnChain S cap) {y : St} (hy : OnChain cap y) :
    L.dens (fun _ => (1 : ℝ)) y = 1 := by
  have h := L.lam_mul_dens hrow (fun _ => (1 : ℝ)) y
  simp only [mul_one] at h
  rw [L.mact_lam] at h
  exact (mul_left_cancel₀ (L.pos hy).ne' (by rw [h, mul_one])).symm

/-- `λ·g` is absolutely ladder-summable whenever `g` has finite `λ`-integral. -/
theorem summable_abs_lad_mul {g : St → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hs : Summable fun x => L.lam x * g x) :
    Summable fun k : ℕ => |L.lam (.lad k) * g (.lad k)| := by
  have hinj : Function.Injective fun k : ℕ => (St.lad k) := by intro a b h; injection h
  exact (hs.comp_injective hinj).congr fun k =>
    (abs_of_nonneg (mul_nonneg (L.nonneg _) (hg _))).symm

/-- **`∫ Pg dλ = ∫ g dλ`** at every non-negative `g` with finite `λ`-integral: the transported
measure has the same total mass. -/
theorem tsum_lam_dens (hrow : RowOnChain S cap) {g : St → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hs : Summable fun x => L.lam x * g x) :
    ∑' y, L.lam y * L.dens g y = ∑' x, L.lam x * g x := by
  rw [tsum_congr fun y => L.lam_mul_dens hrow g y]
  exact tsum_mact_eq S cap (nu := fun x => L.lam x * g x) (L.summable_abs_lad_mul hg hs)

theorem summable_lam_dens (hrow : RowOnChain S cap) {g : St → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hs : Summable fun x => L.lam x * g x) :
    Summable fun y => L.lam y * L.dens g y := by
  have hb : ∃ C, ∀ _ : St, |(1 : ℝ)| ≤ C := ⟨1, fun _ => by norm_num⟩
  have h0 := summable_mact S cap (nu := fun x => L.lam x * g x)
    (L.summable_abs_lad_mul hg hs) (f := fun _ => (1 : ℝ)) hb
  have h : Summable fun y => mact S cap (fun x => L.lam x * g x) y := by
    simp only [mul_one] at h0
    exact h0
  exact h.congr fun y => (L.lam_mul_dens hrow g y).symm

/-! ## 3. Jensen for the reversed law, and the `L^p` contraction of `P` -/

/-- **Jensen for `P`**, at every state of the chain: `|Pu|^p ≤ P(|u|^p)` for `p ≥ 1`. -/
theorem abs_rpow_dens_le {p : ℝ} (hp : 1 ≤ p) (u : St → ℝ)
    {y : St} (hy : OnChain cap y) :
    |L.dens u y| ^ p ≤ L.dens (fun z => |u z| ^ p) y := by
  rcases y with k | _
  · rw [L.dens_lad, L.dens_lad]
    exact abs_rpow_add3_le (L.w1_nonneg k) (L.w2_nonneg k) (L.w3_nonneg k) (L.w_sum hy) hp
  · rw [L.dens_sink, L.dens_sink]

/-- **`P` is a contraction of `L^p(λ)`**, `p ∈ [1,∞)` — the mirror of `Stat.mass_pstar_le`, and
what makes `P` an operator of `L²(λ)`. -/
theorem mass_dens_le (hrow : RowOnChain S cap) {p : ℝ} (hp : 1 ≤ p) {u : St → ℝ}
    (hs : Summable fun x => |u x| ^ p * L.lam x) :
    L.mass p (L.dens u) ≤ L.mass p u := by
  have hg : ∀ x, 0 ≤ |u x| ^ p := fun x => Real.rpow_nonneg (abs_nonneg _) p
  have hs' : Summable fun x => L.lam x * |u x| ^ p := hs.congr fun x => mul_comm _ _
  have hstep : ∀ y, L.lam y * |L.dens u y| ^ p ≤ L.lam y * L.dens (fun z => |u z| ^ p) y := by
    intro y
    by_cases hy : OnChain cap y
    · exact mul_le_mul_of_nonneg_left (L.abs_rpow_dens_le hp u hy) (L.nonneg y)
    · rw [L.vanish hy, zero_mul, zero_mul]
  have hsumR : Summable fun y => L.lam y * L.dens (fun z => |u z| ^ p) y :=
    L.summable_lam_dens hrow hg hs'
  have hsumL : Summable fun y => L.lam y * |L.dens u y| ^ p :=
    Summable.of_nonneg_of_le
      (fun y => mul_nonneg (L.nonneg y) (Real.rpow_nonneg (abs_nonneg _) p)) hstep hsumR
  calc L.mass p (L.dens u) = ∑' y, L.lam y * |L.dens u y| ^ p :=
        tsum_congr fun y => mul_comm _ _
    _ ≤ ∑' y, L.lam y * L.dens (fun z => |u z| ^ p) y := hsumL.tsum_le_tsum hstep hsumR
    _ = ∑' x, L.lam x * |u x| ^ p := L.tsum_lam_dens hrow hg hs'
    _ = L.mass p u := tsum_congr fun x => mul_comm _ _

/-! ## 4. The adjoint identity -/

/-- **`⟨Pu,v⟩_λ = ⟨u,P⋆v⟩_λ` at bounded `v`.**

This is `lem:doubling_operator`(1)'s adjoint clause on the plain-real layer, and it is also the
characterisation of `Pu` as a Radon–Nikodym derivative: taking `v = 1_{\{y\}}` reads off
`λ(y)(Pu)(y) = ((uλ)T)(\{y\})`. -/
theorem tsum_dens_mul (hrow : RowOnChain S cap) {u : St → ℝ}
    (hu : Summable fun k : ℕ => |L.lam (.lad k) * u (.lad k)|) {v : St → ℝ}
    (hv : ∃ C, ∀ x, |v x| ≤ C) :
    ∑' y, L.lam y * L.dens u y * v y = ∑' x, L.lam x * u x * pstar S cap v x := by
  have hcongr : ∀ y : St, L.lam y * L.dens u y * v y
      = mact S cap (fun x => L.lam x * u x) y * v y := fun y => by
    rw [L.lam_mul_dens hrow u y]
  rw [tsum_congr hcongr]
  exact (tsum_mact S cap (nu := fun x => L.lam x * u x) hu hv).symm

end Stat

/-! ## 5. The adjoint identity at `u, v ∈ L²(λ)`

`tsum_dens_mul` tests against bounded `v`; the paper's hypothesis is `v ∈ L²(λ)`. Truncating `v`
at height `n` and letting `n → ∞` removes the restriction: both sides are dominated by summable
functions — `λ|Pu||v|` on the left and `λ|u|P⋆|v|` on the right, each by `2ab ≤ a² + b²` and the
two contractions — so Tannery's theorem applies to each. -/

/-- `|t|^{(2:ℝ)} = t^2`: the bridge between the `rpow` form of `Stat.mass` and the natural power
the summability estimates are written in. -/
theorem abs_rpow_two' (t : ℝ) : |t| ^ (2 : ℝ) = t ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

/-- `|P⋆f| ≤ P⋆|f|`: Jensen at `p = 1`. -/
theorem abs_pstar_le (f : St → ℝ) (x : St) :
    |pstar S cap f x| ≤ pstar S cap (fun y => |f y|) x := by
  have h := abs_rpow_pstar_le (S := S) (cap := cap) (p := 1) le_rfl f x
  simpa using h

namespace Stat

variable (L : Stat S cap)

/-- `P⋆` preserves the `L^p` summability of the mass — the summability half of
`Stat.mass_pstar_le`. -/
theorem summable_mass_pstar {p : ℝ} (hp : 1 ≤ p) {f : St → ℝ}
    (hs : Summable fun x => |f x| ^ p * L.lam x) :
    Summable fun x => |pstar S cap f x| ^ p * L.lam x := by
  have hsum' : Summable fun x => L.lam x * |f x| ^ p := hs.congr fun x => mul_comm _ _
  obtain ⟨hsummP, -⟩ :=
    L.tsum_pstar_le (g := fun y => |f y| ^ p) (fun y => Real.rpow_nonneg (abs_nonneg _) p) hsum'
  refine Summable.of_nonneg_of_le
    (fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) p) (L.nonneg x)) (fun x => ?_) hsummP
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_rpow_pstar_le hp f x) (L.nonneg x)

/-- `P` preserves the `L^p` summability of the mass — the summability half of
`Stat.mass_dens_le`. -/
theorem summable_mass_dens (hrow : RowOnChain S cap) {p : ℝ} (hp : 1 ≤ p) {u : St → ℝ}
    (hs : Summable fun x => |u x| ^ p * L.lam x) :
    Summable fun x => |L.dens u x| ^ p * L.lam x := by
  have hg : ∀ x, 0 ≤ |u x| ^ p := fun x => Real.rpow_nonneg (abs_nonneg _) p
  have hs' : Summable fun x => L.lam x * |u x| ^ p := hs.congr fun x => mul_comm _ _
  have hsumR : Summable fun y => L.lam y * L.dens (fun z => |u z| ^ p) y :=
    L.summable_lam_dens hrow hg hs'
  have hstep : ∀ y, L.lam y * |L.dens u y| ^ p ≤ L.lam y * L.dens (fun z => |u z| ^ p) y := by
    intro y
    by_cases hy : OnChain cap y
    · exact mul_le_mul_of_nonneg_left (L.abs_rpow_dens_le hp u hy) (L.nonneg y)
    · rw [L.vanish hy, zero_mul, zero_mul]
  have hsumL : Summable fun y => L.lam y * |L.dens u y| ^ p :=
    Summable.of_nonneg_of_le
      (fun y => mul_nonneg (L.nonneg y) (Real.rpow_nonneg (abs_nonneg _) p)) hstep hsumR
  exact hsumL.congr fun x => mul_comm _ _

/-- The Cauchy–Schwarz-free product bound: `2|a||b| ≤ a² + b²`, summed against `λ`. -/
theorem summable_lam_mul_mul {a b : St → ℝ} (ha : Summable fun x => |a x| ^ (2 : ℝ) * L.lam x)
    (hb : Summable fun x => |b x| ^ (2 : ℝ) * L.lam x) :
    Summable fun x => L.lam x * |a x| * |b x| := by
  have ha' : Summable fun x => L.lam x * a x ^ 2 :=
    ha.congr fun x => by rw [abs_rpow_two']; ring
  have hb' : Summable fun x => L.lam x * b x ^ 2 :=
    hb.congr fun x => by rw [abs_rpow_two']; ring
  refine Summable.of_nonneg_of_le
    (fun x => mul_nonneg (mul_nonneg (L.nonneg x) (abs_nonneg _)) (abs_nonneg _))
    (fun x => ?_) ((ha'.add hb').div_const 2)
  have hsq : (|a x| - |b x|) ^ 2 ≥ 0 := sq_nonneg _
  have h1 : |a x| ^ 2 = a x ^ 2 := sq_abs _
  have h2 : |b x| ^ 2 = b x ^ 2 := sq_abs _
  have hlam := L.nonneg x
  nlinarith [mul_nonneg hlam hsq]

/-- `λ·u` is absolutely ladder-summable whenever `u ∈ L²(λ)`. -/
theorem summable_abs_lad_of_sq {u : St → ℝ} (hu : Summable fun x => |u x| ^ (2 : ℝ) * L.lam x) :
    Summable fun k : ℕ => |L.lam (.lad k) * u (.lad k)| := by
  have hone : Summable fun x => |(1 : ℝ)| ^ (2 : ℝ) * L.lam x := by
    simpa using L.summable
  have h := L.summable_lam_mul_mul hu hone
  simp only [abs_one, mul_one] at h
  have hinj : Function.Injective fun k : ℕ => (St.lad k) := by intro a b hab; injection hab
  refine ((h.comp_injective hinj)).congr fun k => ?_
  simp only [Function.comp_apply]
  rw [abs_mul, abs_of_nonneg (L.nonneg _)]

/-- **`⟨Pu,v⟩_λ = ⟨u,P⋆v⟩_λ` at `u, v ∈ L²(λ)`** — `lem:doubling_operator`(1)'s adjoint clause,
at the paper's own hypothesis. -/
theorem tsum_dens_mul_sq (hrow : RowOnChain S cap) {u v : St → ℝ}
    (hu : Summable fun x => |u x| ^ (2 : ℝ) * L.lam x)
    (hv : Summable fun x => |v x| ^ (2 : ℝ) * L.lam x) :
    ∑' y, L.lam y * L.dens u y * v y = ∑' x, L.lam x * u x * pstar S cap v x := by
  classical
  set V : ℕ → St → ℝ := fun n x => if |v x| ≤ (n : ℝ) then v x else 0 with hVdef
  have hVabs : ∀ n x, |V n x| ≤ |v x| := by
    intro n x
    simp only [hVdef]
    by_cases h : |v x| ≤ (n : ℝ)
    · rw [if_pos h]
    · rw [if_neg h]
      simp
  have hVb : ∀ n : ℕ, ∃ C, ∀ x, |V n x| ≤ C := by
    intro n
    refine ⟨(n : ℝ), fun x => ?_⟩
    simp only [hVdef]
    by_cases h : |v x| ≤ (n : ℝ)
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      simp
  have hVlim : ∀ x, Tendsto (fun n : ℕ => V n x) atTop (𝓝 (v x)) := by
    intro x
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈|v x|⌉₊) fun n hn => ?_
    have hle : |v x| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simp only [hVdef, if_pos hle]
  have hulad := L.summable_abs_lad_of_sq hu
  have hbase : ∀ n : ℕ, ∑' y, L.lam y * L.dens u y * V n y
      = ∑' x, L.lam x * u x * pstar S cap (V n) x := fun n =>
    L.tsum_dens_mul hrow hulad (hVb n)
  -- the left side converges
  have hdens := L.summable_mass_dens hrow (p := 2) one_le_two hu
  have hboundL : Summable fun y => L.lam y * |L.dens u y| * |v y| :=
    L.summable_lam_mul_mul hdens hv
  have hL : Tendsto (fun n : ℕ => ∑' y, L.lam y * L.dens u y * V n y) atTop
      (𝓝 (∑' y, L.lam y * L.dens u y * v y)) := by
    refine tendsto_tsum_of_dominated_convergence hboundL
      (fun y => ((hVlim y).const_mul (L.lam y * L.dens u y))) (Filter.Eventually.of_forall ?_)
    intro n y
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (L.nonneg y)]
    exact mul_le_mul_of_nonneg_left (hVabs n y) (mul_nonneg (L.nonneg y) (abs_nonneg _))
  -- the right side converges
  have habsv : Summable fun x => |(|v x|)| ^ (2 : ℝ) * L.lam x := by
    simpa using hv
  have hpv := L.summable_mass_pstar (p := 2) one_le_two habsv
  have hboundR : Summable fun x => L.lam x * |u x| * |pstar S cap (fun y => |v y|) x| :=
    L.summable_lam_mul_mul hu hpv
  have hR : Tendsto (fun n : ℕ => ∑' x, L.lam x * u x * pstar S cap (V n) x) atTop
      (𝓝 (∑' x, L.lam x * u x * pstar S cap v x)) := by
    refine tendsto_tsum_of_dominated_convergence hboundR
      (fun x => ((tendsto_pstar hVlim x).const_mul (L.lam x * u x)))
      (Filter.Eventually.of_forall ?_)
    intro n x
    have hmono : pstar S cap (fun y => |V n y|) x ≤ pstar S cap (fun y => |v y|) x :=
      pstar_mono (fun y => hVabs n y) x
    have hstep : |pstar S cap (V n) x| ≤ |pstar S cap (fun y => |v y|) x| := by
      refine le_trans (abs_pstar_le _ x) (le_trans hmono (le_abs_self _))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (L.nonneg x)]
    exact mul_le_mul_of_nonneg_left hstep (mul_nonneg (L.nonneg x) (abs_nonneg _))
  exact tendsto_nhds_unique hL (hR.congr fun n => (hbase n).symm)

/-- **Invariance against a square-integrable test function.** `Stat.inv` is stated against bounded
`f`; `u ≡ 1` in the adjoint identity, where `P1 = 1`, removes that restriction at `L²(λ)`. -/
theorem tsum_lam_pstar_sq (hrow : RowOnChain S cap) {v : St → ℝ}
    (hv : Summable fun x => |v x| ^ (2 : ℝ) * L.lam x) :
    ∑' x, L.lam x * pstar S cap v x = ∑' x, L.lam x * v x := by
  have hone : Summable fun x => |(1 : ℝ)| ^ (2 : ℝ) * L.lam x := by simpa using L.summable
  have h := L.tsum_dens_mul_sq hrow (u := fun _ => (1 : ℝ)) hone hv
  have hL : ∀ y : St, L.lam y * L.dens (fun _ => (1 : ℝ)) y * v y = L.lam y * v y := by
    intro y
    by_cases hy : OnChain cap y
    · rw [L.dens_const hrow hy, mul_one]
    · simp [L.vanish hy]
  rw [tsum_congr hL] at h
  simp only [mul_one] at h
  exact h.symm

/-- `P` maps `L^p(μ)` into itself, at every finite `p ≥ 1`. -/
theorem memLp_dens (hrow : RowOnChain S cap) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞)
    {u : St → ℝ} (hu : MemLp u p L.mu) : MemLp (L.dens u) p L.mu := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp1; exact absurd hp1 (by simp)
  rw [L.memLp_iff hp0 hpt] at hu ⊢
  exact L.summable_mass_dens hrow (one_le_toReal hp1 hpt) hu

/-- **`P` is a contraction of `L^p(μ)`**, `p ∈ [1,∞)` — the `eLpNorm` form of
`Stat.mass_dens_le`. In particular `P` is a bounded operator of `L²(λ)`, which is what
`lem:doubling_operator`(1) needs of it. -/
theorem eLpNorm_dens_le (hrow : RowOnChain S cap) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞)
    {u : St → ℝ} (hu : MemLp u p L.mu) :
    eLpNorm (L.dens u) p L.mu ≤ eLpNorm u p L.mu := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp1; exact absurd hp1 (by simp)
  have hr : 1 ≤ p.toReal := one_le_toReal hp1 hpt
  have hr0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hr
  have hPu := L.memLp_dens hrow hp1 hpt hu
  have hsu : Summable fun x => |u x| ^ p.toReal * L.lam x := (L.memLp_iff hp0 hpt).mp hu
  have hsP : Summable fun x => |L.dens u x| ^ p.toReal * L.lam x := (L.memLp_iff hp0 hpt).mp hPu
  have hpow : (eLpNorm (L.dens u) p L.mu).toReal ^ p.toReal
      ≤ (eLpNorm u p L.mu).toReal ^ p.toReal := by
    rw [L.toReal_eLpNorm_rpow _ hp0 hpt hsP, L.toReal_eLpNorm_rpow _ hp0 hpt hsu]
    exact L.mass_dens_le hrow hr hsu
  have hle : (eLpNorm (L.dens u) p L.mu).toReal ≤ (eLpNorm u p L.mu).toReal :=
    (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg ENNReal.toReal_nonneg hr0).mp hpow
  exact (ENNReal.toReal_le_toReal hPu.eLpNorm_ne_top hu.eLpNorm_ne_top).mp hle

end Stat

end GFNBounds.Doubling
