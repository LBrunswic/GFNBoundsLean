import GFNBounds.Doubling.Adjoint

/-!
# The fixed points of the density action are the constants

**`lem:doubling_fixed_points`, the `P` half** — `app_doubling.tex:130–164`.

> Let `T` be an irreducible Markov kernel on a countable state space carrying an invariant
> probability `λ` positive at every state, let `P` be its density action `Pu := d((uλ)T)/dλ` and
> `P⋆` its function action `(P⋆v)(x) := ∫v dT(x,·)`. Then
> `ker(Id − P⋆) ∩ L²(λ) = ker(Id − P) ∩ L²(λ) = ℝ·1`.

The `P⋆` half is `LpLayer`'s `Stat.fixed_const_memLp`. This file closes the `P` half, and
`Stat.ker_eq_const` states the two together — `eq:doubling_fixed` in full, on this graph.

## The route, and why it is not the paper's

The paper deduces the `P` half from the `P⋆` half by a Hilbert-space argument: `P⋆ = P*`, both
are contractions of `L²(λ)`, and a contraction `Q` has `ker(Id − Q*) ⊆ ker(Id − Q)`.

Here `P` is an explicit averaging operator — `Adjoint.lean` exhibits it as the *reversed* one-step
law `T̂(y,x) = λ(x)T(x,y)/λ(y)`, whose weights are non-negative and sum to `1` at every state of
the chain by the balance equations. So the `P⋆` argument runs verbatim for `P`, with Jensen taken
against `T̂` instead of `T`, and no adjoint, no Riesz representation and no Hilbert space are
used. Concretely: equality in Jensen is the vanishing of a variance, `Σᵢ wᵢ(uᵢ − m)² = 0` with
`m = (Pu)(y) = u(y)`, so `u` is constant on the atoms of `T̂(y,·)` of positive weight — and the
climbing atom `y = j ↦ j+1` has weight `λ_{j+1}dec(j+1)/λ_j > 0` at every `j` with `j+1` on the
chain, which climbs the whole ladder from `s₀`.

Irreducibility of `T̂` is therefore never invoked as a hypothesis: the single climbing edge does
the work, exactly as the single decrementing edge does it in `FixedPoints.fixed_const`.

## SCOPE (disclosed)

* **The fixed-point equation is required on the chain**, i.e. `λ`-a.e., which is what membership
  of `L²(λ)` — a space of classes — makes available, and the conclusion is likewise `u = u(s₀)` on
  the chain. On the loop closure `OnChain` is vacuous and both are pointwise statements.
* **`u ∈ L²(λ)` is carried**, as the paper states it. It is used exactly once: to make the total
  Jensen gap a convergent sum, so that a sum of non-negative terms vanishing forces each term to.
* **`RowOnChain` is carried**, as everywhere in this layer (`LpLayer`, SCOPE).
* The statement is about `ker(Id − P)` **as a set of `λ`-classes on this graph**; the paper's
  `= ℝ·1` is rendered as "constant on the chain", the two being the same statement in `L²(λ)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `T` irreducible | ⚠ **not assumed**; the climbing edge of `T̂` is exhibited instead, which is stronger information about this graph and weaker as a hypothesis |
| `λ` invariant probability, positive at every state | ✓ carried (`Stat`; positivity on the chain) |
| `u ∈ L²(λ)` | ✓ carried |
| `Pu = u` | ✓ carried, on the chain (`λ`-a.e.) |
| — | ⚠ **added**: `RowOnChain S cap` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

variable {S : Setting} {cap : Option ℕ}

/-- The first of three non-negative reals summing to zero is zero. -/
theorem eq_zero_of_three_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 0) : a = 0 := by linarith

/-- **Equality in Jensen for a three-atom probability, at the first atom.** If the second moment
of `(u₁,u₂,u₃)` against `(w₁,w₂,w₃)` equals the square of its mean, then every atom of positive
weight carries the mean; this is that statement at the first atom. -/
theorem eq_mean_of_var_zero {w₁ w₂ w₃ u₁ u₂ u₃ : ℝ} (h2 : 0 ≤ w₂) (h3 : 0 ≤ w₃)
    (hw : w₁ + w₂ + w₃ = 1) (hpos : 0 < w₁)
    (hgap : w₁ * u₁ ^ 2 + w₂ * u₂ ^ 2 + w₃ * u₃ ^ 2
      = (w₁ * u₁ + w₂ * u₂ + w₃ * u₃) ^ 2) :
    u₁ = w₁ * u₁ + w₂ * u₂ + w₃ * u₃ := by
  have hid : w₁ * (u₁ - (w₁ * u₁ + w₂ * u₂ + w₃ * u₃)) ^ 2
      + w₂ * (u₂ - (w₁ * u₁ + w₂ * u₂ + w₃ * u₃)) ^ 2
      + w₃ * (u₃ - (w₁ * u₁ + w₂ * u₂ + w₃ * u₃)) ^ 2 = 0 := by
    linear_combination hgap + ((w₁ * u₁ + w₂ * u₂ + w₃ * u₃) ^ 2) * hw
  have hz := eq_zero_of_three_nonneg
    (mul_nonneg hpos.le (sq_nonneg (u₁ - (w₁ * u₁ + w₂ * u₂ + w₃ * u₃))))
    (mul_nonneg h2 (sq_nonneg (u₂ - (w₁ * u₁ + w₂ * u₂ + w₃ * u₃))))
    (mul_nonneg h3 (sq_nonneg (u₃ - (w₁ * u₁ + w₂ * u₂ + w₃ * u₃)))) hid
  have hsq : (u₁ - (w₁ * u₁ + w₂ * u₂ + w₃ * u₃)) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hpos.ne'
    · exact h
  have := (pow_eq_zero_iff two_ne_zero).mp hsq
  linarith

/-- A ladder state below an on-chain ladder state is on the chain. -/
theorem onChain_lad_of_le {j k : ℕ} (hjk : j ≤ k) (hk : OnChain cap (.lad k)) :
    OnChain cap (.lad j) := by
  cases cap with
  | none => trivial
  | some K => exact le_trans hjk hk

namespace Stat

variable (L : Stat S cap)

/-- The climbing weight of the reversed law is positive wherever the state above is on the
chain: `w₁(j) = λ_{j+1}dec(j+1)/λ_j`, and `dec` never vanishes. -/
theorem w1_pos {k : ℕ} (hk : OnChain cap (.lad k)) (hk1 : OnChain cap (.lad (k + 1))) :
    0 < L.w1 k := by
  have hdec : 0 < decW S cap (k + 1) := by
    rw [decW]
    split
    · exact S.one_sub_eps_pos (Nat.le_add_left 1 k)
    · exact zero_lt_one
  exact div_pos (mul_pos (L.pos hk1) hdec) (L.pos hk)

/-- **The Jensen gap of `P` vanishes on the chain at a fixed point in `L²(λ)`.**

The gap is non-negative pointwise and its `λ`-integral is zero, `P` preserving the `λ`-integral
and `Pu = u` on the chain; a convergent sum of non-negative terms vanishing forces each term to. -/
theorem dens_gap_zero (hrow : RowOnChain S cap) {u : St → ℝ}
    (hu : Summable fun x => |u x| ^ (2 : ℝ) * L.lam x)
    (hfix : ∀ x, OnChain cap x → L.dens u x = u x) {y : St} (hy : OnChain cap y) :
    L.dens (fun z => (u z) ^ 2) y = (L.dens u y) ^ 2 := by
  have hsqnn : ∀ x : St, 0 ≤ (u x) ^ 2 := fun x => sq_nonneg _
  have hu' : Summable fun x => L.lam x * (u x) ^ 2 :=
    hu.congr fun x => by rw [abs_rpow_two']; ring
  have hJ : ∀ z : St, OnChain cap z →
      (L.dens u z) ^ 2 ≤ L.dens (fun w => (u w) ^ 2) z := by
    intro z hz
    have h := L.abs_rpow_dens_le (p := 2) one_le_two u hz
    rw [abs_rpow_two'] at h
    have hcongr : (fun w => |u w| ^ (2 : ℝ)) = fun w => (u w) ^ 2 := by
      funext w; rw [abs_rpow_two']
    rwa [hcongr] at h
  have hsumR : Summable fun z => L.lam z * L.dens (fun w => (u w) ^ 2) z :=
    L.summable_lam_dens hrow hsqnn hu'
  have hsumL : Summable fun z => L.lam z * (L.dens u z) ^ 2 := by
    have h := L.summable_mass_dens hrow (p := 2) one_le_two hu
    exact h.congr fun x => by rw [abs_rpow_two']; ring
  have hsplit : (fun z => L.lam z * (L.dens (fun w => (u w) ^ 2) z - (L.dens u z) ^ 2))
      = fun z => L.lam z * L.dens (fun w => (u w) ^ 2) z - L.lam z * (L.dens u z) ^ 2 := by
    funext z; ring
  have hgapnn : ∀ z : St, 0 ≤ L.lam z * (L.dens (fun w => (u w) ^ 2) z - (L.dens u z) ^ 2) := by
    intro z
    by_cases hz : OnChain cap z
    · exact mul_nonneg (L.nonneg z) (by linarith [hJ z hz])
    · rw [L.vanish hz, zero_mul]
  have hsumgap : Summable fun z =>
      L.lam z * (L.dens (fun w => (u w) ^ 2) z - (L.dens u z) ^ 2) := by
    rw [hsplit]; exact hsumR.sub hsumL
  have hzero : ∑' z, L.lam z * (L.dens (fun w => (u w) ^ 2) z - (L.dens u z) ^ 2) = 0 := by
    have hEq : ∀ z : St, L.lam z * (L.dens u z) ^ 2 = L.lam z * (u z) ^ 2 := by
      intro z
      by_cases hz : OnChain cap z
      · rw [hfix z hz]
      · rw [L.vanish hz, zero_mul, zero_mul]
    rw [hsplit, Summable.tsum_sub hsumR hsumL, L.tsum_lam_dens hrow hsqnn hu', tsum_congr hEq]
    ring
  have hsum0 : HasSum
      (fun z => L.lam z * (L.dens (fun w => (u w) ^ 2) z - (L.dens u z) ^ 2)) 0 := by
    have h := hsumgap.hasSum
    rwa [hzero] at h
  have hlex := le_hasSum hsum0 y fun z _ => hgapnn z
  have hpos := L.pos hy
  rcases eq_or_lt_of_le (by linarith [hJ y hy] :
      (0 : ℝ) ≤ L.dens (fun w => (u w) ^ 2) y - (L.dens u y) ^ 2) with h | h
  · linarith
  · exact absurd hlex (not_le.mpr (mul_pos hpos h))

/-- **`eq:doubling_fixed`, the `P` half.** A fixed point of the density action in `L²(λ)` is
constant on the chain.

Equality in Jensen for the reversed law makes `u` constant on the atoms of positive weight, and
the climbing atom `j ↦ j+1` has positive weight at every `j` with `j+1` on the chain: the ladder
is climbed from the source, exactly as `FixedPoints.fixed_const` descends it. -/
theorem dens_fixed_const (hrow : RowOnChain S cap) {u : St → ℝ}
    (hu : Summable fun x => |u x| ^ (2 : ℝ) * L.lam x)
    (hfix : ∀ x, OnChain cap x → L.dens u x = u x) :
    ∀ x : St, OnChain cap x → u x = u (.lad 0) := by
  have hstep : ∀ k : ℕ, OnChain cap (.lad (k + 1)) → u (.lad (k + 1)) = u (.lad k) := by
    intro k hk1
    have hk : OnChain cap (.lad k) := onChain_lad_of_succ hk1
    have hgap := L.dens_gap_zero hrow hu hfix hk
    rw [L.dens_lad (fun z => (u z) ^ 2) k, L.dens_lad u k] at hgap
    have hmean := eq_mean_of_var_zero (L.w2_nonneg k) (L.w3_nonneg k) (L.w_sum hk)
      (L.w1_pos hk hk1) hgap
    rw [← L.dens_lad u k, hfix _ hk] at hmean
    exact hmean
  have hlad : ∀ k : ℕ, OnChain cap (.lad k) → u (.lad k) = u (.lad 0) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro hk; rw [hstep k hk, ih (onChain_lad_of_succ hk)]
  intro x hx
  rcases x with k | _
  · exact hlad k hx
  · have h := hfix .sink (onChain_sink cap)
    rw [L.dens_sink] at h
    exact h.symm

/-- The converse inclusion: `P` fixes every function constant on the chain. -/
theorem dens_fixed_of_const {u : St → ℝ} (hc : ∀ x, OnChain cap x → u x = u (.lad 0))
    {y : St} (hy : OnChain cap y) : L.dens u y = u y := by
  rcases y with k | _
  · rw [L.dens_lad]
    have hw := L.w_sum hy
    have h2 : u (.lad (k / 2)) = u (.lad 0) := hc _ (onChain_lad_of_le (Nat.div_le_self k 2) hy)
    have h3 : u .sink = u (.lad 0) := hc _ (onChain_sink cap)
    have hk : u (.lad k) = u (.lad 0) := hc _ hy
    have h1 : L.w1 k * u (.lad (k + 1)) = L.w1 k * u (.lad 0) := by
      by_cases hk1 : OnChain cap (.lad (k + 1))
      · rw [hc _ hk1]
      · rw [w1, L.vanish hk1, zero_mul, zero_div, zero_mul, zero_mul]
    linear_combination h1 + L.w2 k * h2 + L.w3 k * h3 - hk + u (St.lad 0) * hw
  · rw [L.dens_sink]
    exact (hc _ (onChain_sink cap)).symm

/-- The converse inclusion for the function action: `P⋆` fixes every function constant on the
chain. -/
theorem pstar_fixed_of_const (hrow : RowOnChain S cap) {u : St → ℝ}
    (hc : ∀ x, OnChain cap x → u x = u (.lad 0)) {y : St} (hy : OnChain cap y) :
    pstar S cap u y = u y := by
  rcases y with (_ | j) | _
  · rw [pstar_src, hc _ (onChain_sink cap)]
  · have hj : u (.lad j) = u (.lad 0) := hc _ (onChain_lad_of_succ hy)
    have hj1 : u (.lad (j + 1)) = u (.lad 0) := hc _ hy
    by_cases hD : HasDouble cap (j + 1)
    · have hd : u (.lad (2 * (j + 1))) = u (.lad 0) := hc _ (onChain_double hD)
      rw [pstar_lad_succ, if_pos hD, hd, hj, hj1]
      ring
    · rw [pstar_lad_succ, if_neg hD, hj, hj1]
  · rw [pstar_sink, hc _ (onChain_sink cap)]
    have hrw : ∀ k ∈ Finset.Icc 1 S.d, S.row k * u (.lad k) = S.row k * u (.lad 0) := by
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      rw [hc _ (hrow k hk'.1 hk'.2)]
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_mul, S.row_sum, one_mul]

/-- **`eq:doubling_fixed`, both halves.** In `L²(λ)`, the fixed points of the density action and
of the function action are exactly the functions constant on the chain — that is, `ℝ·1`. -/
theorem ker_eq_const (hrow : RowOnChain S cap) {u : St → ℝ}
    (hu : Summable fun x => |u x| ^ (2 : ℝ) * L.lam x) :
    ((∀ x, OnChain cap x → L.dens u x = u x) ↔ (∀ x, OnChain cap x → u x = u (.lad 0)))
      ∧ ((∀ x, OnChain cap x → pstar S cap u x = u x)
          ↔ (∀ x, OnChain cap x → u x = u (.lad 0))) := by
  have hmem : MeasureTheory.MemLp u 2 L.mu := L.memLp_two_iff.mpr hu
  refine ⟨⟨fun h => L.dens_fixed_const hrow hu h, fun h _ hy => L.dens_fixed_of_const h hy⟩,
    ⟨fun h => L.fixed_const_memLp hmem h, fun h _ hy => pstar_fixed_of_const hrow h hy⟩⟩

end Stat

end GFNBounds.Doubling
