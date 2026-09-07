import GFNBounds.Doubling.PointwiseInv

/-!
# The measure action, its duality with `P⋆`, and the pointwise balance equations

**`lem:doubling_operator`(1), the Fubini step** — `app_doubling.tex:166–262`.

> In particular `P⋆` is bounded on `L²(λ)`, so for `u,v ∈ L²(λ)` the function `(x,y) ↦ u(x)v(y)`
> is `T(x,dy)λ(dx)`-integrable […] and Fubini gives
> `∫v d((uλ)T) = ∬v(y)T(x,dy)u(x)λ(dx) = ⟨u,P⋆v⟩_λ`.

This file supplies the `∫v d((uλ)T) = ⟨u, P⋆v⟩_λ` half of that display — the *measure* action
`ν ↦ νT`, before any division by `λ`. `Adjoint.lean` divides.

## The modelling decision

**The kernel is not built; the transported measure is.** `(νT)(y)` is written in closed form, one
line per kind of incoming edge, exactly as `pstar` is written in closed form for the outgoing
ones:

  `(νT)(s_f) = ν(s₀)`,
  `(νT)(j) = ν(j+1)·dec(j+1) + [j even, j ≥ 2] ν(j/2)·dbl(j/2) + ν(s_f)·row(j)`,

where `dbl(j) = ε(j)` when the doubling edge out of `j` survives the truncation and `0` when it
does not, and `dec(j) = 1 − dbl(j)`. So Fubini becomes a **rearrangement of four `HasSum`s**: the
decrement flux, the doubling flux, the target-row flux and the wrap. The one non-trivial step is
that the doubling flux indexed by its *source* `k+1` is the same series as the doubling flux
indexed by its *target* `2(k+1)`, which is `Function.Injective.hasSum_iff` along `n ↦ 2(n+1)` —
the same move `PointwiseInv.inv_of_pointwise` makes, and this file generalises that proof: there
the transported measure was *assumed* equal to `ν`, here it is *computed*.

The pointwise balance equations `λT = λ` are then a **corollary**, not a hypothesis: test the
duality against the indicator of a single state, and use `Stat.inv`, whose test functions are
exactly the bounded ones (`kb/0003`). That is `Stat.mact_lam`, and it is what makes the density
action an averaging operator in `Adjoint.lean`.

## SCOPE (disclosed)

* **The test function `f` is bounded.** The duality is proved against bounded `f` and absolutely
  ladder-summable `ν`, which is the hypothesis pair every consumer here supplies (`f = 1`,
  `f = 1_{\{y\}}`, `f = v` truncated). The extension to `v ∈ L²(λ)` is done in `Adjoint.lean` by
  a truncation argument; it is not claimed here.
* **No positivity, no normalisation, no invariance** is used by the duality itself: `mact` is
  linear in `ν` and `hasSum_mact` holds for any signed `ν` whose ladder restriction is absolutely
  summable. Invariance enters only in `Stat.mact_lam`.
* **Both `cap`s at once**, as in `pstar`: `PointwiseInv` treats the loop closure only, and the
  weights `dblW`/`decW` here carry the truncation as well.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `T` a Markov kernel | ✓ carried: `dblW + decW = 1` at every `j ≥ 1`, `row` sums to `1` |
| `λ` invariant | ✓ carried (`Stat.inv`), and only in `mact_lam` |
| `u ∈ L¹(λ)` for `(uλ)T` to be defined | ⚠ carried as absolute summability of `ν` along the ladder |
| `v ∈ L²(λ)` | ⚠ **narrowed to bounded `v`** here; widened in `Adjoint.lean` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

variable {S : Setting} {cap : Option ℕ}

/-! ## 1. The two edge weights out of a ladder state -/

/-- The doubling weight out of the ladder state `j ≥ 1`: `ε(j)` when the edge `j → 2j` survives
the truncation, `0` when it has been deleted. -/
noncomputable def dblW (S : Setting) (cap : Option ℕ) (j : ℕ) : ℝ :=
  if HasDouble cap j then S.eps j else 0

/-- The decrement weight out of the ladder state `j ≥ 1`: `1 − ε(j)` when the doubling edge
survives, `1` when it has been deleted and the decrement carries the whole mass. -/
noncomputable def decW (S : Setting) (cap : Option ℕ) (j : ℕ) : ℝ :=
  if HasDouble cap j then 1 - S.eps j else 1

theorem dblW_nonneg {j : ℕ} (hj : 1 ≤ j) : 0 ≤ dblW S cap j := by
  rw [dblW]; split
  · exact (S.eps_pos hj).le
  · exact le_rfl

theorem decW_nonneg {j : ℕ} (hj : 1 ≤ j) : 0 ≤ decW S cap j := by
  rw [decW]; split
  · exact (S.one_sub_eps_pos hj).le
  · exact zero_le_one

/-- The one-step law out of a ladder state is a probability. -/
theorem dblW_add_decW {j : ℕ} : dblW S cap j + decW S cap j = 1 := by
  rw [dblW, decW]; split <;> ring

theorem dblW_le_one {j : ℕ} (hj : 1 ≤ j) : dblW S cap j ≤ 1 := by
  have h := decW_nonneg (S := S) (cap := cap) hj
  have := dblW_add_decW (S := S) (cap := cap) (j := j)
  linarith

theorem decW_le_one {j : ℕ} (hj : 1 ≤ j) : decW S cap j ≤ 1 := by
  have h := dblW_nonneg (S := S) (cap := cap) hj
  have := dblW_add_decW (S := S) (cap := cap) (j := j)
  linarith

/-- `P⋆` at a ladder state, with the two weights named: this is `pstar_lad_succ` with the
`if` pushed into `dblW` and `decW`. -/
theorem pstar_lad_succ_weights {f : St → ℝ} (j : ℕ) :
    pstar S cap f (.lad (j + 1))
      = dblW S cap (j + 1) * f (.lad (2 * (j + 1))) + decW S cap (j + 1) * f (.lad j) := by
  rw [pstar_lad_succ, dblW, decW]
  by_cases h : HasDouble cap (j + 1) <;> simp [h]

/-- The target row vanishes at `0`: `row_supp` forces `1 ≤ j` at every non-zero entry. -/
theorem row_zero (S : Setting) : S.row 0 = 0 := by
  by_contra h
  exact absurd (S.row_supp h).1 (by omega)

/-! ## 2. The measure action -/

/-- **The transported measure `νT`**, in closed form: one summand per kind of incoming edge.

At the sink the only incoming edge is the wrap `s₀ → s_f`, of probability one. At the ladder
state `k` they are the decrement out of `k + 1`, the doubling out of `k/2` when `k` is even and
positive, and the target row fired from the sink. -/
noncomputable def mact (S : Setting) (cap : Option ℕ) (nu : St → ℝ) : St → ℝ
  | .lad k =>
      nu (.lad (k + 1)) * decW S cap (k + 1)
        + (if 1 ≤ k ∧ 2 ∣ k then nu (.lad (k / 2)) * dblW S cap (k / 2) else 0)
        + nu .sink * S.row k
  | .sink => nu (.lad 0)

@[simp] theorem mact_sink (nu : St → ℝ) : mact S cap nu .sink = nu (.lad 0) := rfl

theorem mact_lad (nu : St → ℝ) (k : ℕ) :
    mact S cap nu (.lad k)
      = nu (.lad (k + 1)) * decW S cap (k + 1)
        + (if 1 ≤ k ∧ 2 ∣ k then nu (.lad (k / 2)) * dblW S cap (k / 2) else 0)
        + nu .sink * S.row k := rfl

/-! ## 3. Duality: `∫ v d(νT) = ∫ P⋆v dν` -/

/-- **The duality identity, in `HasSum` form.** Both series converge, to the same value.

This is the Fubini step of `lem:doubling_operator`(1) on this graph: the double integral
`∬ v(y) T(x,dy) ν(dx)` is summed in the two orders, and the two orders differ only by the
reindexing `k + 1 ↦ 2(k+1)` of the doubling flux. -/
theorem hasSum_mact (S : Setting) (cap : Option ℕ) {nu : St → ℝ}
    (hsum : Summable fun k : ℕ => |nu (.lad k)|) {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) :
    ∃ V : ℝ, HasSum (fun x => nu x * pstar S cap f x) V
      ∧ HasSum (fun y => mact S cap nu y * f y) V := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC .sink)
  have hsum1 : Summable fun k : ℕ => |nu (St.lad (k + 1))| := (summable_nat_add_iff 1).mpr hsum
  set a : ℕ → ℝ := fun k => nu (.lad (k + 1)) * decW S cap (k + 1) * f (.lad k) with ha_def
  set b : ℕ → ℝ := fun k =>
    (if 1 ≤ k ∧ 2 ∣ k then nu (.lad (k / 2)) * dblW S cap (k / 2) else 0) * f (.lad k) with hb_def
  set c : ℕ → ℝ := fun k => nu .sink * S.row k * f (.lad k) with hc_def
  set e : ℕ → ℝ := fun k => nu (.lad (k + 1)) * dblW S cap (k + 1) * f (.lad (2 * (k + 1)))
    with he_def
  have hA : Summable a := by
    refine Summable.of_norm_bounded (g := fun k => C * |nu (St.lad (k + 1))|)
      (hsum1.mul_left C) fun k => ?_
    rw [Real.norm_eq_abs, ha_def]
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg (decW_nonneg (S := S) (cap := cap) (Nat.le_add_left 1 k))]
    have hn : (0:ℝ) ≤ |nu (St.lad (k + 1))| := abs_nonneg _
    have hw0 : (0:ℝ) ≤ decW S cap (k + 1) := decW_nonneg (Nat.le_add_left 1 k)
    have hw1 : decW S cap (k + 1) ≤ 1 := decW_le_one (Nat.le_add_left 1 k)
    calc |nu (St.lad (k + 1))| * decW S cap (k + 1) * |f (St.lad k)|
        ≤ |nu (St.lad (k + 1))| * decW S cap (k + 1) * C :=
          mul_le_mul_of_nonneg_left (hC _) (mul_nonneg hn hw0)
      _ ≤ |nu (St.lad (k + 1))| * 1 * C :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw1 hn) hC0
      _ = C * |nu (St.lad (k + 1))| := by ring
  have hE : Summable e := by
    refine Summable.of_norm_bounded (g := fun k => C * |nu (St.lad (k + 1))|)
      (hsum1.mul_left C) fun k => ?_
    rw [Real.norm_eq_abs, he_def]
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg (dblW_nonneg (S := S) (cap := cap) (Nat.le_add_left 1 k))]
    have hn : (0:ℝ) ≤ |nu (St.lad (k + 1))| := abs_nonneg _
    have hw0 : (0:ℝ) ≤ dblW S cap (k + 1) := dblW_nonneg (Nat.le_add_left 1 k)
    have hw1 : dblW S cap (k + 1) ≤ 1 := dblW_le_one (Nat.le_add_left 1 k)
    calc |nu (St.lad (k + 1))| * dblW S cap (k + 1) * |f (St.lad (2 * (k + 1)))|
        ≤ |nu (St.lad (k + 1))| * dblW S cap (k + 1) * C :=
          mul_le_mul_of_nonneg_left (hC _) (mul_nonneg hn hw0)
      _ ≤ |nu (St.lad (k + 1))| * 1 * C :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw1 hn) hC0
      _ = C * |nu (St.lad (k + 1))| := by ring
  have hinj : Function.Injective fun n : ℕ => 2 * (n + 1) := by
    intro x y h; simp only at h; omega
  have hzero : ∀ x ∉ Set.range fun n : ℕ => 2 * (n + 1), b x = 0 := by
    intro x hx
    have hcond : ¬ (1 ≤ x ∧ 2 ∣ x) := by
      rintro ⟨hx1, m, rfl⟩
      refine hx ⟨m - 1, ?_⟩
      simp only
      omega
    rw [hb_def]
    simp only [hcond, if_false, zero_mul]
  have hcomp : b ∘ (fun n : ℕ => 2 * (n + 1)) = e := by
    funext n
    have h1 : 2 * (n + 1) / 2 = n + 1 := by omega
    have h2 : 1 ≤ 2 * (n + 1) ∧ 2 ∣ 2 * (n + 1) := ⟨by omega, ⟨n + 1, rfl⟩⟩
    simp only [Function.comp_apply, hb_def, he_def, h1, if_pos h2]
  have hBsum : HasSum b (∑' k, e k) := by
    rw [← hinj.hasSum_iff hzero, hcomp]
    exact hE.hasSum
  have hCsum : HasSum c (∑ k ∈ Finset.Icc 1 S.d, c k) := by
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    have hrow : S.row k = 0 := by
      by_contra hne
      exact hk (Finset.mem_Icc.mpr (S.row_supp hne))
    rw [hc_def]; simp [hrow]
  have hCval : ∑ k ∈ Finset.Icc 1 S.d, c k = nu .sink * pstar S cap f .sink := by
    rw [pstar_sink, Finset.mul_sum, hc_def]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hR1 : HasSum (fun k : ℕ => mact S cap nu (.lad k) * f (.lad k))
      (∑' k, a k + ∑' k, e k + ∑ k ∈ Finset.Icc 1 S.d, c k) := by
    refine ((hA.hasSum.add hBsum).add hCsum).congr_fun fun k => ?_
    rw [mact_lad, ha_def, hb_def, hc_def]
    ring
  have hR := hasSum_st (g := fun x => mact S cap nu x * f x) hR1
  have hL1 : HasSum (fun k : ℕ => nu (.lad (k + 1)) * pstar S cap f (.lad (k + 1)))
      (∑' k, e k + ∑' k, a k) := by
    refine (hE.hasSum.add hA.hasSum).congr_fun fun k => ?_
    rw [pstar_lad_succ_weights, ha_def, he_def]
    ring
  have hL2 := (hasSum_nat_add_iff
    (f := fun k : ℕ => nu (.lad k) * pstar S cap f (.lad k)) 1).mp hL1
  rw [Finset.sum_range_one] at hL2
  have hL := hasSum_st (g := fun x => nu x * pstar S cap f x) hL2
  refine ⟨_, hL, ?_⟩
  have hval : ∑' k, a k + ∑' k, e k + ∑ k ∈ Finset.Icc 1 S.d, c k
        + mact S cap nu .sink * f .sink
      = ∑' k, e k + ∑' k, a k + nu (.lad 0) * pstar S cap f (.lad 0)
        + nu .sink * pstar S cap f .sink := by
    rw [hCval, mact_sink, pstar_src]
    ring
  rw [← hval]
  exact hR

/-- **The duality identity.** `∫ v d(νT) = ∫ P⋆v dν`. -/
theorem tsum_mact (S : Setting) (cap : Option ℕ) {nu : St → ℝ}
    (hsum : Summable fun k : ℕ => |nu (.lad k)|) {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) :
    ∑' x, nu x * pstar S cap f x = ∑' y, mact S cap nu y * f y := by
  obtain ⟨V, hL, hR⟩ := hasSum_mact S cap hsum hf
  rw [hL.tsum_eq, hR.tsum_eq]

theorem summable_mact (S : Setting) (cap : Option ℕ) {nu : St → ℝ}
    (hsum : Summable fun k : ℕ => |nu (.lad k)|) {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) :
    Summable fun y => mact S cap nu y * f y :=
  let ⟨_, _, hR⟩ := hasSum_mact S cap hsum hf
  hR.summable

/-- The transported measure has the same total mass: `f = 1` in the duality, `P⋆1 = 1`. -/
theorem tsum_mact_eq (S : Setting) (cap : Option ℕ) {nu : St → ℝ}
    (hsum : Summable fun k : ℕ => |nu (.lad k)|) :
    ∑' y, mact S cap nu y = ∑' x, nu x := by
  have h := tsum_mact S cap hsum (f := fun _ => (1 : ℝ)) ⟨1, fun _ => by simp⟩
  simpa [pstar_const] using h.symm

/-! ## 4. The pointwise balance equations -/

namespace Stat

variable (L : Stat S cap)

/-- `λ` restricted to the ladder is absolutely summable — the hypothesis every use of the duality
takes. -/
theorem summable_abs_lad : Summable fun k : ℕ => |L.lam (.lad k)| := by
  have hinj : Function.Injective (fun k : ℕ => (St.lad k)) := by
    intro a b h; injection h
  have h := L.summable.comp_injective hinj
  exact h.congr fun k => (abs_of_nonneg (L.nonneg _)).symm

/-- **`λT = λ`, pointwise.** The paper's invariance hypothesis is carried in `Stat` in the
integral form against bounded test functions; testing it against the indicator of a single state
and reading the duality identity on the other side gives the balance equation at that state.

This is the identity `PointwiseInv.inv_of_pointwise` *assumes*; here it is derived. -/
theorem mact_lam (y : St) : mact S cap L.lam y = L.lam y := by
  have hb : ∃ C, ∀ x : St, |(if x = y then (1 : ℝ) else 0)| ≤ C := by
    refine ⟨1, fun x => ?_⟩
    by_cases h : x = y <;> simp [h]
  have hdual := tsum_mact S cap L.summable_abs_lad hb
  have hL : ∑' x, L.lam x * (if x = y then (1 : ℝ) else 0) = L.lam y := by
    rw [tsum_congr (fun x : St => by
      by_cases h : x = y
      · simp [h]
      · simp [h] : ∀ x : St, L.lam x * (if x = y then (1 : ℝ) else 0)
          = if x = y then L.lam y else 0)]
    exact tsum_ite_eq y (fun _ => L.lam y)
  have hR : ∑' z, mact S cap L.lam z * (if z = y then (1 : ℝ) else 0)
      = mact S cap L.lam y := by
    rw [tsum_congr (fun z : St => by
      by_cases h : z = y
      · simp [h]
      · simp [h] : ∀ z : St, mact S cap L.lam z * (if z = y then (1 : ℝ) else 0)
          = if z = y then mact S cap L.lam y else 0)]
    exact tsum_ite_eq y (fun _ => mact S cap L.lam y)
  rw [L.inv _ hb, hL] at hdual
  rw [← hR, ← hdual]

/-- The balance equation at the sink: `λ(s_f) = λ(s₀)`, the wrap being the only incoming edge. -/
theorem lam_sink : L.lam .sink = L.lam (.lad 0) :=
  (L.mact_lam .sink).symm.trans (mact_sink L.lam)

/-- The balance equation at a ladder state, written out. -/
theorem lam_lad (k : ℕ) :
    L.lam (.lad k)
      = L.lam (.lad (k + 1)) * decW S cap (k + 1)
        + (if 1 ≤ k ∧ 2 ∣ k then L.lam (.lad (k / 2)) * dblW S cap (k / 2) else 0)
        + L.lam .sink * S.row k := by
  rw [← mact_lad L.lam k, L.mact_lam]

end Stat

end GFNBounds.Doubling
