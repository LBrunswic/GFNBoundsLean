import GFNBounds.Doubling.Irreducible

/-!
# The fixed points of the function action are the constants

**`lem:doubling_fixed_points`** — `app_doubling.tex:130–164`.

> Let `T` be an irreducible Markov kernel on a countable state space carrying an invariant
> probability `λ` positive at every state, let `P` be its density action and `P⋆` its function
> action. Then `ker(Id − P⋆) ∩ L²(λ) = ker(Id − P) ∩ L²(λ) = ℝ·1`.

## SCOPE (disclosed)

⚠ **weakened hypothesis, and a narrowed statement.** Two departures, both on the face of the
Lean statement:

* `L²(λ)` is replaced by **bounded** functions. Boundedness is what makes `Stat.inv` applicable
  to `f²` without an integrability side condition, and every consumer in this library tests
  against bounded functions. A bounded function on a probability space is in `L²`, so this is a
  sub-case of the paper's, not a generalization.
* Only the `P⋆` half is proved *in this file*. Both halves at the paper's hypothesis
  `f ∈ L²(λ)` are `Stat.ker_eq_const` in `FixedPointsP.lean`, with the density action `P`
  modelled as `Stat.dens` (`Adjoint.lean`); this file stays as the elementary route.

The proof is the paper's: Jensen for the one-step law and the strictly convex `t ↦ t²` gives
`(P⋆f)² ≤ P⋆(f²)` pointwise, invariance makes the `λ`-integral of the gap vanish, positivity of
`λ` makes the gap vanish at every state of the chain, and equality in Jensen at a doubling state
forces `f(2m) = f(m−1)`. Constancy then follows along the ladder without ever using the target
row, since the decrement alone connects it.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| irreducible kernel | ✓ implied: the ladder is connected by the decrement alone |
| invariant probability positive at every state | ✓ carried (`Stat`, positivity on chain) |
| `f ∈ L²(λ)` with `P⋆f = f` | ⚠ narrowed to bounded `f` |
| conclusion `= ℝ·1` | ✓ carried, as `f x = f s₀` at every state of the chain |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

variable {S : Setting} {cap : Option ℕ}

/-- **Jensen at one state.** `(P⋆f)(x)² ≤ P⋆(f²)(x)`: the one-step law is a probability and
`t ↦ t²` is convex. -/
theorem sq_pstar_le (f : St → ℝ) (x : St) :
    (pstar S cap f x) ^ 2 ≤ pstar S cap (fun y => (f y) ^ 2) x := by
  rcases x with j | _
  · rcases j with _ | j
    · exact le_of_eq rfl
    · by_cases hD : HasDouble cap (j + 1)
      · simp only [pstar_lad_succ, hD, if_true]
        have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
        have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
        nlinarith [mul_nonneg (mul_nonneg h1 h2)
          (sq_nonneg (f (St.lad (2 * (j + 1))) - f (St.lad j)))]
      · simp only [pstar_lad_succ, hD, if_false]
        exact le_rfl
  · simp only [pstar_sink]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 S.d)
      (fun k => Real.sqrt (S.row k)) (fun k => Real.sqrt (S.row k) * f (.lad k))
    have hfg : ∀ k ∈ Finset.Icc 1 S.d,
        Real.sqrt (S.row k) * (Real.sqrt (S.row k) * f (.lad k)) = S.row k * f (.lad k) := by
      intro k _
      rw [← mul_assoc, Real.mul_self_sqrt (S.row_nonneg k)]
    have hf2 : ∀ k ∈ Finset.Icc 1 S.d, Real.sqrt (S.row k) ^ 2 = S.row k := fun k _ =>
      Real.sq_sqrt (S.row_nonneg k)
    have hg2 : ∀ k ∈ Finset.Icc 1 S.d,
        (Real.sqrt (S.row k) * f (.lad k)) ^ 2 = S.row k * (f (.lad k)) ^ 2 := by
      intro k _
      rw [mul_pow, Real.sq_sqrt (S.row_nonneg k)]
    rw [Finset.sum_congr rfl hfg, Finset.sum_congr rfl hf2, Finset.sum_congr rfl hg2,
      S.row_sum, one_mul] at hcs
    exact hcs

/-- **Equality in Jensen at a doubling state.** The gap is `ε(m)(1−ε(m))(f(2m) − f(m−1))²`. -/
theorem pstar_sq_gap (f : St → ℝ) {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m) :
    pstar S cap (fun y => (f y) ^ 2) (.lad m) - (pstar S cap f (.lad m)) ^ 2
      = S.eps m * (1 - S.eps m) * (f (.lad (2 * m)) - f (.lad (m - 1))) ^ 2 := by
  rw [pstar_lad_of_hasDouble hm hD, pstar_lad_of_hasDouble hm hD]
  ring

namespace Stat

variable (L : Stat S cap)

/-- The `λ`-integral of the Jensen gap of a bounded fixed point vanishes. -/
theorem tsum_jensen_gap {f : St → ℝ} (hb : ∃ C, ∀ x, |f x| ≤ C)
    (hfix : pstar S cap f = f) :
    ∑' x, L.lam x * (pstar S cap (fun y => (f y) ^ 2) x - (pstar S cap f x) ^ 2) = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hsq : ∃ C', ∀ x, |(f x) ^ 2| ≤ C' := by
    refine ⟨C ^ 2, fun x => ?_⟩
    rw [abs_pow]
    have h0 : 0 ≤ |f x| := abs_nonneg _
    nlinarith [hC x, h0]
  have hpsq : ∃ C', ∀ x, |pstar S cap (fun y => (f y) ^ 2) x| ≤ C' := by
    obtain ⟨C', hC'⟩ := hsq
    exact ⟨C', fun x => pstar_bounded hC' x⟩
  have hfixsq : ∃ C', ∀ x, |(pstar S cap f x) ^ 2| ≤ C' := by
    rw [hfix]; exact hsq
  have hs1 := L.summable_mul hpsq
  have hs2 := L.summable_mul hfixsq
  have hsplit : (fun x => L.lam x * (pstar S cap (fun y => (f y) ^ 2) x - (pstar S cap f x) ^ 2))
      = fun x => L.lam x * pstar S cap (fun y => (f y) ^ 2) x
        - L.lam x * (pstar S cap f x) ^ 2 := by
    funext x; ring
  rw [hsplit, Summable.tsum_sub hs1 hs2, L.inv _ hsq, hfix, sub_self]

/-- **Equality in Jensen, at every state of the chain.** -/
theorem jensen_gap_zero (L : Stat S cap) {f : St → ℝ} (hb : ∃ C, ∀ x, |f x| ≤ C)
    (hfix : pstar S cap f = f) {x : St} (hx : OnChain cap x) :
    pstar S cap (fun y => (f y) ^ 2) x - (pstar S cap f x) ^ 2 = 0 := by
  set g : St → ℝ := fun y => pstar S cap (fun z => (f z) ^ 2) y - (pstar S cap f y) ^ 2 with hg
  have hgnn : ∀ y, 0 ≤ g y := fun y => by
    rw [hg]; simpa using sq_pstar_le (S := S) (cap := cap) f y
  have hgb : ∃ C, ∀ y, |g y| ≤ C := by
    obtain ⟨C, hC⟩ := hb
    have hsq : ∃ C', ∀ y, |(f y) ^ 2| ≤ C' := by
      refine ⟨C ^ 2, fun y => ?_⟩
      rw [abs_pow]
      nlinarith [hC y, abs_nonneg (f y)]
    obtain ⟨C', hC'⟩ := hsq
    refine ⟨C' + C', fun y => ?_⟩
    have h1 : |pstar S cap (fun z => (f z) ^ 2) y| ≤ C' := pstar_bounded hC' y
    have h2 : |(pstar S cap f y) ^ 2| ≤ C' := by rw [hfix]; exact hC' y
    calc |g y| = |pstar S cap (fun z => (f z) ^ 2) y - (pstar S cap f y) ^ 2| := rfl
      _ ≤ |pstar S cap (fun z => (f z) ^ 2) y| + |(pstar S cap f y) ^ 2| := abs_sub _ _
      _ ≤ C' + C' := by linarith
  have hsum : HasSum (fun y => L.lam y * g y) 0 := by
    have h := (L.summable_mul hgb).hasSum
    rwa [L.tsum_jensen_gap hb hfix] at h
  have hle := le_hasSum hsum x (fun y _ => mul_nonneg (L.nonneg y) (hgnn y))
  have hpos := L.pos hx
  nlinarith [hle, hgnn x, hpos]

/-- **`eq:doubling_fixed`, the `P⋆` half.** A bounded fixed point of the function action is
constant on the chain.

The ladder is climbed by the decrement alone: at a state whose doubling edge has been truncated
away the fixed-point equation gives `f(m) = f(m−1)` outright, and where it survives, equality in
Jensen gives `f(2m) = f(m−1)` and the fixed-point equation then averages the two into
`f(m) = f(m−1)`. The target row is never used. -/
theorem fixed_const (L : Stat S cap) {f : St → ℝ} (hb : ∃ C, ∀ x, |f x| ≤ C)
    (hfix : pstar S cap f = f) :
    ∀ x : St, OnChain cap x → f x = f (.lad 0) := by
  have hstep : ∀ n : ℕ, OnChain cap (St.lad (n + 1)) → f (.lad (n + 1)) = f (.lad n) := by
    intro n hn
    have hfn := congrFun hfix (St.lad (n + 1))
    by_cases hD : HasDouble cap (n + 1)
    · have hgap := L.jensen_gap_zero hb hfix hn
      rw [pstar_sq_gap f (Nat.le_add_left 1 n) hD] at hgap
      have he : 0 < S.eps (n + 1) * (1 - S.eps (n + 1)) :=
        mul_pos (S.eps_pos (Nat.le_add_left 1 n)) (S.one_sub_eps_pos (Nat.le_add_left 1 n))
      have hzero : f (.lad (2 * (n + 1))) - f (.lad (n + 1 - 1)) = 0 := by
        have hsq : (f (.lad (2 * (n + 1))) - f (.lad (n + 1 - 1))) ^ 2 = 0 := by
          by_contra hne
          have hpos : 0 < (f (.lad (2 * (n + 1))) - f (.lad (n + 1 - 1))) ^ 2 :=
            lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
          nlinarith [hgap, he, hpos]
        exact (pow_eq_zero_iff (two_ne_zero)).mp hsq
      simp only [Nat.add_sub_cancel] at hzero
      rw [pstar_lad_succ, if_pos hD] at hfn
      have heq : f (.lad (2 * (n + 1))) = f (.lad n) := by linarith
      rw [heq] at hfn
      linarith [hfn]
    · rw [pstar_lad_succ, if_neg hD] at hfn
      exact hfn.symm
  have hlad : ∀ n : ℕ, OnChain cap (St.lad n) → f (.lad n) = f (.lad 0) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
        intro hn
        have hn' : OnChain cap (St.lad n) := by
          cases cap with
          | none => trivial
          | some K => exact le_trans (Nat.le_succ n) hn
        rw [hstep n hn, ih hn']
  intro x hx
  rcases x with n | _
  · exact hlad n hx
  · have hfn := congrFun hfix (St.lad 0)
    rw [pstar_src] at hfn
    exact hfn

end Stat

end GFNBounds.Doubling
