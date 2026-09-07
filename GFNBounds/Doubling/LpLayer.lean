import GFNBounds.Doubling.FixedPoints
import GFNBounds.Doubling.PerCutNorms

/-!
# The `L^p(λ)` layer: the measure, the a.e. bridge, and the norm identification

**No paper label of its own.** This file is the infrastructure spike that
`lem:doubling_operator`(1)–(2) (`app_doubling.tex:166–262`),
`lem:doubling_fixed_points`' `P` half (`app_doubling.tex:130–164`) and
`prop:doubling_unsolvable` (`app_doubling.tex:2126–2181`) all wait on: those three statements are
about `L^2(λ)` as a *Hilbert space* — an adjoint, a dense range, an open-mapping argument — while
everything already proved in this library lives on the plain-real layer `Stat.mass` of
`PerCutNorms.lean`. What is missing is the dictionary between the two.

The relevant sentences of the three consumers:

> (`lem:doubling_operator`(1)) `P⋆` is a contraction of `L^p(λ)` for every `p ∈ [1,+∞]` and is the
> `L^2(λ)`-adjoint of `P`.
>
> (`lem:doubling_fixed_points`) `ker(Id − P⋆) ∩ L²(λ) = ker(Id − P) ∩ L²(λ) = ℝ·1`.
>
> (`prop:doubling_unsolvable`) `(Id − P⋆)L²(λ)` is a dense proper linear subspace of `ker Π`.

## The three pieces

**The measure.** `λ` is a summable positive real sequence on the countable `St`, so the measure it
carries is `count.withDensity (ENNReal.ofReal ∘ λ)`; `Stat.mu_singleton` says it charges `{x}` by
exactly `λ(x)` and `Stat.total` makes it a probability.

**The bridge, `Stat.ae_iff_eq`.** `f =ᵐ[μ] g ↔ ∀ x, OnChain cap x → f x = g x`. This is the
make-or-break lemma: on the loop closure `OnChain` is vacuous, so a.e. equality *is* equality, and
on the truncation it is equality on the `K + 2` states of `lem:doubling_truncation_irreducible`.
Both directions are immediate from `Stat`'s own fields — `pos` charges every on-chain point,
`vanish` kills the rest — and together they say that `L^p(λ)` here is a *sequence* space, with no
null-set bookkeeping anywhere downstream.

**The norm.** `Stat.mass p f = ∑' x |f x|^p λ x` is identified with `(eLpNorm f p μ).toReal ^ p`
at every `p ∈ [1,∞)`, so every estimate already proved on the plain-real layer — in particular
`lem:doubling_percut`'s `eq:doubling_step2` and `eq:doubling_stepp` — transfers to `eLpNorm`
verbatim. `MeasureTheory.lintegral_countable'` does the work and needs no measurability
hypothesis, `St` carrying the discrete σ-algebra.

Two consequences are drawn here rather than left to the consumers, because the layer is what
makes them available. `Stat.pstarL2` is `P⋆` as a bounded operator of `L²(μ)` of norm at most
`1`; and `Stat.fixed_const_memLp` re-proves the `P⋆` half of `eq:doubling_fixed` at the paper's
own hypothesis `f ∈ L²(λ)`, lifting the narrowing to *bounded* `f` that `FixedPoints.lean`
discloses. The ingredient that lifts it is `Stat.tsum_pstar_le`: `Stat.inv` holds by hypothesis
only against bounded functions, and truncating at `n` and letting `n → ∞` extends it to an
inequality `∫ P⋆g dλ ≤ ∫ g dλ` at every non-negative `g` with `∫ g dλ < ∞` — which is what a
square-integrable `f` needs, `f²` being unbounded.

## SCOPE (disclosed)

The file is definitions plus the dictionary. It settles **no** statement of the appendix in
full; the one statement it advances is `lem:doubling_fixed_points`, whose `P⋆` half it upgrades
from bounded `f` to `f ∈ L²(λ)` and whose `P` half remains open.

* **`P⋆` on `L²` is here; its adjoint `P` is not.** `pstarL2` is built as a contraction of
  `L²(μ)`, which is the `p = 2` case of `lem:doubling_operator`(1)'s first clause. The second
  clause — `P⋆ = P*` — is *not* proved: the density action `P` is not modelled in this library at
  all (`Setting.lean`, SCOPE). So `lem:doubling_operator`(1) stays open, and this file does not
  claim it.
* **The contraction is proved at `p = 2` only.** The pointwise Jensen step available here is
  `sq_pstar_le` (`FixedPoints.lean`), which is the square. For general `p ∈ [1,∞)` the same
  argument needs convexity of `t ↦ |t|^p` against a finite convex combination, which is not
  developed here. `Stat.eLpNorm_two_pstar_le` is therefore stated at `2`.
* **`fixed_const_memLp` states the fixed-point equation on the chain, i.e. `λ`-a.e.**, which is
  weaker than the paper's pointwise `P⋆f = f` and is what `prop:doubling_unsolvable` (working in
  `L²(λ)`, a space of classes) actually has. The conclusion is likewise `f = f(s₀)` on the chain,
  i.e. `f = f(s₀)` in `L²(λ)`, which is `ker(Id − P⋆) ∩ L²(λ) = ℝ·1`. The `P` half of
  `eq:doubling_fixed` is **not** proved, for the same reason as everywhere else: `P` is not
  modelled.
* **The `L²` operator carries one hypothesis the paper does not name: `RowOnChain`.** On the
  truncation at `K`, `pstar` at the sink reads the target row at `1, …, d`, and if `K < d` those
  states are off-chain — where `λ` vanishes and a.e. equality says nothing — so `pstar` would not
  descend to `λ`-classes. `RowOnChain S cap` is `d ≤ K`, automatic on the loop closure
  (`rowOnChain_none`), and `cor:doubling_truncation` takes `K ≥ d` throughout. This is a genuine
  hypothesis of the construction, not of the mathematics, and it is on the face of the statement.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| invariant probability `λ` positive at every state | ✓ carried (`Stat`; positivity on chain) |
| the state space is countable | ✓ carried (`St` is `Countable`, `Setting.lean`; discrete σ-algebra) |
| `p ∈ [1,∞)` for the norm identification | ✓ carried (`hp0`, `hpt`) |
| `p ∈ [1,∞]` for the contraction | ⚠ **narrowed to `p = 2`** — see SCOPE |
| `P⋆ = P*` on `L²(λ)` | ⚠ **not claimed** — `P` is not modelled |
| `f ∈ L²(λ)` with `P⋆f = f` (`lem:doubling_fixed_points`) | ✓ carried, at `L²` and a.e. |
| irreducibility (`lem:doubling_fixed_points`) | ✓ implied: the ladder is connected by the decrement alone |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open MeasureTheory Filter Topology Real
open scoped ENNReal NNReal

/-- `St` carries the discrete σ-algebra: it is countable, and every statement of the appendix
about `L^p(λ)` is a statement about a sequence space. -/
instance : MeasurableSpace St := ⊤

instance : DiscreteMeasurableSpace St := ⟨fun _ => trivial⟩

variable {S : Setting} {cap : Option ℕ}

namespace Stat

variable (L : Stat S cap)

/-! ## 1. The measure -/

/-- **The measure `λ` carries**, as a measure on `St`: the counting measure weighted by `λ`. -/
noncomputable def mu : Measure St :=
  Measure.count.withDensity (fun x => ENNReal.ofReal (L.lam x))

/-- `μ{x} = λ(x)`. -/
@[simp] theorem mu_singleton (x : St) : L.mu {x} = ENNReal.ofReal (L.lam x) := by
  rw [mu, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
    Measure.count_singleton, mul_one]

/-- `μ` is a probability measure: this is `Stat.total`. -/
instance instIsProbabilityMeasure : IsProbabilityMeasure L.mu := by
  constructor
  rw [mu, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
    ← ENNReal.ofReal_tsum_of_nonneg L.nonneg L.summable, L.total, ENNReal.ofReal_one]

/-! ## 2. The bridge: a.e. equality is equality on the chain -/

/-- `μ` charges exactly the states of the chain. -/
theorem mu_singleton_ne_zero_iff {x : St} : L.mu {x} ≠ 0 ↔ OnChain cap x := by
  rw [mu_singleton]
  constructor
  · intro h
    by_contra hx
    exact h (by rw [L.vanish hx, ENNReal.ofReal_zero])
  · intro hx h
    exact absurd (ENNReal.ofReal_eq_zero.mp h) (not_le.mpr (L.pos hx))

/-- **The bridge, for a predicate.** A `μ`-a.e. property is a property of the chain. -/
theorem ae_iff_onChain {p : St → Prop} : (∀ᵐ x ∂L.mu, p x) ↔ ∀ x, OnChain cap x → p x := by
  rw [ae_iff_of_countable]
  exact forall_congr' fun x => imp_congr_left L.mu_singleton_ne_zero_iff

/-- **The bridge.** `f =ᵐ[μ] g` iff `f` and `g` agree at every state of the chain.

`λ` charges every on-chain state (`Stat.pos`) and vanishes off it (`Stat.vanish`), so the only
`μ`-null set meeting the chain is empty. On the loop closure `OnChain` is vacuous and a.e.
equality is equality. -/
theorem ae_iff_eq {f g : St → ℝ} : f =ᵐ[L.mu] g ↔ ∀ x, OnChain cap x → f x = g x :=
  L.ae_iff_onChain

/-- Equality on the chain gives a.e. equality — the direction the `Lp` constructions consume. -/
theorem ae_eq_of_onChain {f g : St → ℝ} (h : ∀ x, OnChain cap x → f x = g x) : f =ᵐ[L.mu] g :=
  L.ae_iff_eq.mpr h

/-! ## 3. The norm: `Stat.mass` is the `L^p` norm -/

/-- Every function on `St` is measurable, the σ-algebra being discrete. -/
theorem aestronglyMeasurable (f : St → ℝ) : AEStronglyMeasurable f L.mu :=
  (Measurable.of_discrete (f := f)).stronglyMeasurable.aestronglyMeasurable

/-- The `μ`-lower integral is the `λ`-weighted sum. -/
theorem lintegral_eq_tsum (g : St → ℝ≥0∞) :
    ∫⁻ x, g x ∂L.mu = ∑' x, g x * ENNReal.ofReal (L.lam x) := by
  rw [lintegral_countable']
  exact tsum_congr fun x => by rw [L.mu_singleton]

/-- The `p`-th power integrand of `eLpNorm`, on the plain-real layer. -/
theorem lintegral_rpow_enorm (f : St → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ x, ‖f x‖ₑ ^ r ∂L.mu = ∑' x, ENNReal.ofReal (|f x| ^ r * L.lam x) := by
  rw [L.lintegral_eq_tsum]
  refine tsum_congr fun x => ?_
  rw [ENNReal.ofReal_mul (rpow_nonneg (abs_nonneg _) r), Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr]

/-- **`Stat.mass` is the `L^p` integrand's total mass**, whenever that mass is finite. -/
theorem lintegral_rpow_enorm_eq_mass (f : St → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hs : Summable fun x => |f x| ^ r * L.lam x) :
    ∫⁻ x, ‖f x‖ₑ ^ r ∂L.mu = ENNReal.ofReal (L.mass r f) := by
  rw [L.lintegral_rpow_enorm f hr, Stat.mass,
    ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (rpow_nonneg (abs_nonneg _) r)
      (L.nonneg x)) hs]

theorem mass_nonneg (f : St → ℝ) {r : ℝ} : 0 ≤ L.mass r f :=
  tsum_nonneg fun x => mul_nonneg (rpow_nonneg (abs_nonneg _) r) (L.nonneg x)

/-- **`f ∈ L^p(μ)` iff its `p`-th power mass converges.** -/
theorem memLp_iff {f : St → ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    MemLp f p L.mu ↔ Summable fun x => |f x| ^ p.toReal * L.lam x := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  constructor
  · intro hf
    have hnn : ∀ x : St, 0 ≤ |f x| ^ p.toReal * L.lam x := fun x =>
      mul_nonneg (rpow_nonneg (abs_nonneg _) _) (L.nonneg x)
    have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpt hf.eLpNorm_lt_top
    rw [L.lintegral_rpow_enorm f hr.le] at hlt
    have hnn' : Summable fun x => (|f x| ^ p.toReal * L.lam x).toNNReal := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      exact hlt.ne
    refine (NNReal.summable_coe.mpr hnn').congr fun x => ?_
    exact Real.coe_toNNReal _ (hnn x)
  · intro hs
    refine ⟨L.aestronglyMeasurable f, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt,
      L.lintegral_rpow_enorm_eq_mass f hr.le hs]
    exact ENNReal.ofReal_lt_top

/-- **The norm identification.** `‖f‖_{L^p(μ)}^p = Stat.mass p f`, at every `p ∈ [1,∞)`. -/
theorem toReal_eLpNorm_rpow (f : St → ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hs : Summable fun x => |f x| ^ p.toReal * L.lam x) :
    (eLpNorm f p L.mu).toReal ^ p.toReal = L.mass p.toReal f := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hM : 0 ≤ L.mass p.toReal f := L.mass_nonneg f
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
    L.lintegral_rpow_enorm_eq_mass f hr.le hs,
    ENNReal.ofReal_rpow_of_nonneg hM (one_div_nonneg.mpr hr.le),
    ENNReal.toReal_ofReal (rpow_nonneg hM _), ← Real.rpow_mul hM, one_div,
    inv_mul_cancel₀ hr.ne', Real.rpow_one]


end Stat

/-! ## 4. `P⋆` as a contraction of `L²(μ)` -/

/-- `P⋆` is monotone: it is an average over the one-step law. -/
theorem pstar_mono {f g : St → ℝ} (h : ∀ x, f x ≤ g x) (x : St) :
    pstar S cap f x ≤ pstar S cap g x := by
  rcases x with (_ | j) | _
  · exact h _
  · by_cases hD : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, hD, if_true]
      have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
      have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
      exact add_le_add (mul_le_mul_of_nonneg_left (h _) h1) (mul_le_mul_of_nonneg_left (h _) h2)
    · simp only [pstar_lad_succ, hD, if_false]; exact h _
  · exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h _) (S.row_nonneg k)

/-- `P⋆` is continuous for pointwise convergence: each of its three cases is a finite
combination of finitely many values. -/
theorem tendsto_pstar {F : ℕ → St → ℝ} {f : St → ℝ}
    (h : ∀ y, Tendsto (fun n => F n y) atTop (𝓝 (f y))) (x : St) :
    Tendsto (fun n => pstar S cap (F n) x) atTop (𝓝 (pstar S cap f x)) := by
  rcases x with (_ | j) | _
  · exact h _
  · by_cases hD : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, hD, if_true]
      exact ((h _).const_mul _).add ((h _).const_mul _)
    · simp only [pstar_lad_succ, hD, if_false]; exact h _
  · simp only [pstar_sink]
    exact tendsto_finsetSum _ fun k _ => (h _).const_mul _

/-- The target row reaches only states of the chain.

Vacuous on the loop closure; on the truncation at `K` it is `d ≤ K`, which
`cor:doubling_truncation` assumes anyway (it takes `K ≥ 2d`). It is what makes `P⋆` descend to
`λ`-classes: the sink reads `f` at `1, …, d`, and off the chain a.e. equality says nothing. -/
def RowOnChain (S : Setting) (cap : Option ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ S.d → OnChain cap (.lad k)

theorem rowOnChain_none (S : Setting) : RowOnChain S none := fun _ _ _ => trivial

theorem rowOnChain_some {K : ℕ} (h : S.d ≤ K) : RowOnChain S (some K) :=
  fun _ _ hk => hk.trans h

/-- The predecessor of an on-chain ladder state is on the chain. -/
theorem onChain_lad_of_succ {j : ℕ} (h : OnChain cap (.lad (j + 1))) : OnChain cap (.lad j) := by
  cases cap with
  | none => trivial
  | some K => exact (Nat.le_succ j).trans h

/-- The source is on the chain, on either chain. -/
theorem onChain_src (cap : Option ℕ) : OnChain cap (St.lad 0) := by
  cases cap with
  | none => trivial
  | some K => exact Nat.zero_le K

/-- **`P⋆` descends to `λ`-classes.** Two functions agreeing on the chain have `P⋆`-images
agreeing on the chain. -/
theorem pstar_congr_onChain (hrow : RowOnChain S cap) {f g : St → ℝ}
    (h : ∀ x, OnChain cap x → f x = g x) {x : St} (hx : OnChain cap x) :
    pstar S cap f x = pstar S cap g x := by
  rcases x with (_ | j) | _
  · exact h _ (onChain_sink cap)
  · by_cases hD : HasDouble cap (j + 1)
    · simp only [pstar_lad_succ, hD, if_true]
      rw [h _ (onChain_double hD), h _ (onChain_lad_of_succ hx)]
    · simp only [pstar_lad_succ, hD, if_false]
      exact h _ (onChain_lad_of_succ hx)
  · simp only [pstar_sink]
    exact Finset.sum_congr rfl fun k hk => by
      have hk' := Finset.mem_Icc.mp hk
      rw [h _ (hrow k hk'.1 hk'.2)]

private theorem tendsto_min_natCast (a : ℝ) :
    Tendsto (fun n : ℕ => min a (n : ℝ)) atTop (𝓝 a) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop ⌈a⌉₊] with n hn
  exact (min_eq_left ((Nat.le_ceil a).trans (by exact_mod_cast hn))).symm

private theorem abs_rpow_two (t : ℝ) : |t| ^ (2 : ℝ) = t ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast, sq_abs]

namespace Stat

variable (L : Stat S cap)

/-- **Invariance against an unbounded non-negative function.** `Stat.inv` is stated for bounded
`f`; truncating at `n` and letting `n → ∞` extends it to an inequality at every non-negative
`g` with `λ g` summable, which is what the `L²` estimate needs (`g = f²` is unbounded). -/
theorem tsum_pstar_le {g : St → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hsum : Summable fun x => L.lam x * g x) :
    Summable (fun x => L.lam x * pstar S cap g x) ∧
      ∑' x, L.lam x * pstar S cap g x ≤ ∑' x, L.lam x * g x := by
  have hnn : ∀ x, 0 ≤ L.lam x * pstar S cap g x := fun x =>
    mul_nonneg (L.nonneg x) (pstar_nonneg hg x)
  set T : ℕ → St → ℝ := fun n y => min (g y) (n : ℝ) with hTdef
  have hTnn : ∀ n x, 0 ≤ T n x := fun n x => le_min (hg x) (Nat.cast_nonneg n)
  have hTb : ∀ n : ℕ, ∃ C, ∀ x, |T n x| ≤ C := fun n =>
    ⟨(n : ℝ), fun x => by rw [abs_of_nonneg (hTnn n x)]; exact min_le_right _ _⟩
  have hTle : ∀ n x, T n x ≤ g x := fun _ x => min_le_left _ _
  have key : ∀ s : Finset St, ∑ x ∈ s, L.lam x * pstar S cap g x
      ≤ ∑' x, L.lam x * g x := by
    intro s
    have hlim : Tendsto (fun n => ∑ x ∈ s, L.lam x * pstar S cap (T n) x) atTop
        (𝓝 (∑ x ∈ s, L.lam x * pstar S cap g x)) :=
      tendsto_finsetSum _ fun x _ =>
        (tendsto_pstar (fun y => tendsto_min_natCast (g y)) x).const_mul _
    refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hsummT : Summable fun x => L.lam x * pstar S cap (T n) x := by
      obtain ⟨C, hC⟩ := hTb n
      exact L.summable_mul ⟨C, fun x => pstar_bounded hC x⟩
    have h1 : ∑ x ∈ s, L.lam x * pstar S cap (T n) x ≤ ∑' x, L.lam x * pstar S cap (T n) x :=
      hsummT.sum_le_tsum s fun x _ => mul_nonneg (L.nonneg x) (pstar_nonneg (hTnn n) x)
    have h2 : ∑' x, L.lam x * pstar S cap (T n) x = ∑' x, L.lam x * T n x := L.inv _ (hTb n)
    have h3 : ∑' x, L.lam x * T n x ≤ ∑' x, L.lam x * g x :=
      (L.summable_mul (hTb n)).tsum_le_tsum
        (fun x => mul_le_mul_of_nonneg_left (hTle n x) (L.nonneg x)) hsum
    linarith
  have hsumm : Summable fun x => L.lam x * pstar S cap g x :=
    summable_of_sum_le (fun x => hnn x) key
  exact ⟨hsumm, hsumm.tsum_le_of_sum_le key⟩

/-- **`P⋆` contracts the `L²(λ)` mass.** Jensen (`sq_pstar_le`) pointwise, then invariance. -/
theorem mass_two_pstar_le {f : St → ℝ} (hs : Summable fun x => |f x| ^ (2 : ℝ) * L.lam x) :
    L.mass 2 (pstar S cap f) ≤ L.mass 2 f := by
  have hsum' : Summable fun x => L.lam x * (f x) ^ 2 :=
    hs.congr fun x => by rw [abs_rpow_two]; ring
  obtain ⟨hsummP, hle⟩ := L.tsum_pstar_le (fun x => sq_nonneg (f x)) hsum'
  have hstep : ∀ x, L.lam x * (pstar S cap f x) ^ 2
      ≤ L.lam x * pstar S cap (fun y => (f y) ^ 2) x := fun x =>
    mul_le_mul_of_nonneg_left (sq_pstar_le f x) (L.nonneg x)
  have hLHS : Summable fun x => L.lam x * (pstar S cap f x) ^ 2 :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (L.nonneg x) (sq_nonneg _)) hstep hsummP
  calc L.mass 2 (pstar S cap f) = ∑' x, L.lam x * (pstar S cap f x) ^ 2 :=
        tsum_congr fun x => by rw [abs_rpow_two]; ring
    _ ≤ ∑' x, L.lam x * pstar S cap (fun y => (f y) ^ 2) x :=
        hLHS.tsum_le_tsum hstep hsummP
    _ ≤ ∑' x, L.lam x * (f x) ^ 2 := hle
    _ = L.mass 2 f := tsum_congr fun x => by rw [abs_rpow_two]; ring

theorem memLp_two_iff {f : St → ℝ} :
    MemLp f 2 L.mu ↔ Summable fun x => |f x| ^ (2 : ℝ) * L.lam x := by
  simpa using L.memLp_iff (f := f) (p := 2) (by norm_num) (by norm_num)

/-- `P⋆` maps `L²(μ)` into itself. -/
theorem memLp_two_pstar {f : St → ℝ} (hf : MemLp f 2 L.mu) : MemLp (pstar S cap f) 2 L.mu := by
  rw [L.memLp_two_iff] at hf ⊢
  have hsum' : Summable fun x => L.lam x * (f x) ^ 2 :=
    hf.congr fun x => by rw [abs_rpow_two]; ring
  obtain ⟨hsummP, -⟩ := L.tsum_pstar_le (fun x => sq_nonneg (f x)) hsum'
  refine Summable.of_nonneg_of_le
    (fun x => mul_nonneg (rpow_nonneg (abs_nonneg _) _) (L.nonneg x)) (fun x => ?_) hsummP
  rw [abs_rpow_two]
  exact (mul_comm ((pstar S cap f x) ^ 2) (L.lam x)) ▸
    mul_le_mul_of_nonneg_left (sq_pstar_le f x) (L.nonneg x)

/-- **`‖f‖²_{L²(μ)} = Stat.mass 2 f`**, the identification at `p = 2` with the square written
as a natural power — the form the estimates of `PerCutNorms` are stated in. -/
theorem toReal_eLpNorm_two_sq {f : St → ℝ} (hf : MemLp f 2 L.mu) :
    (eLpNorm f 2 L.mu).toReal ^ 2 = L.mass 2 f := by
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  have hs : Summable fun x => |f x| ^ (2 : ℝ≥0∞).toReal * L.lam x := by
    rw [h2]; exact L.memLp_two_iff.mp hf
  have key := L.toReal_eLpNorm_rpow f (p := 2) (by norm_num) (by norm_num) hs
  rw [h2] at key
  rw [← key, ← Real.rpow_natCast (eLpNorm f 2 L.mu).toReal 2]
  norm_num

/-- **`P⋆` is a contraction of `L²(μ)`** — the `p = 2` case of `lem:doubling_operator`(1)'s
first clause. -/
theorem eLpNorm_two_pstar_le {f : St → ℝ} (hf : MemLp f 2 L.mu) :
    eLpNorm (pstar S cap f) 2 L.mu ≤ eLpNorm f 2 L.mu := by
  have hPf := L.memLp_two_pstar hf
  have hmass := L.mass_two_pstar_le (L.memLp_two_iff.mp hf)
  have hsq : (eLpNorm (pstar S cap f) 2 L.mu).toReal ^ 2 ≤ (eLpNorm f 2 L.mu).toReal ^ 2 := by
    rw [L.toReal_eLpNorm_two_sq hPf, L.toReal_eLpNorm_two_sq hf]; exact hmass
  have ha : 0 ≤ (eLpNorm (pstar S cap f) 2 L.mu).toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ (eLpNorm f 2 L.mu).toReal := ENNReal.toReal_nonneg
  refine (ENNReal.toReal_le_toReal hPf.eLpNorm_ne_top hf.eLpNorm_ne_top).mp ?_
  nlinarith

/-! ### The operator on `L²(μ)` -/

/-- `P⋆` acting on `L²(μ)`, as a map of the space into itself. -/
noncomputable def pstarLp (F : Lp ℝ 2 L.mu) : Lp ℝ 2 L.mu :=
  MemLp.toLp _ (L.memLp_two_pstar (Lp.memLp F))

theorem coeFn_pstarLp (F : Lp ℝ 2 L.mu) : ⇑(L.pstarLp F) =ᵐ[L.mu] pstar S cap ⇑F :=
  MemLp.coeFn_toLp _

theorem norm_pstarLp_le (F : Lp ℝ 2 L.mu) : ‖L.pstarLp F‖ ≤ ‖F‖ := by
  rw [pstarLp, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp F).eLpNorm_ne_top (L.eLpNorm_two_pstar_le (Lp.memLp F))

theorem pstarLp_add (hrow : RowOnChain S cap) (F G : Lp ℝ 2 L.mu) :
    L.pstarLp (F + G) = L.pstarLp F + L.pstarLp G := by
  refine Lp.ext ?_
  have hcong : ∀ x, OnChain cap x → pstar S cap ⇑(F + G) x = pstar S cap (⇑F + ⇑G) x :=
    fun _ hx => pstar_congr_onChain hrow (L.ae_iff_eq.mp (Lp.coeFn_add F G)) hx
  filter_upwards [L.coeFn_pstarLp (F + G), Lp.coeFn_add (L.pstarLp F) (L.pstarLp G),
    L.coeFn_pstarLp F, L.coeFn_pstarLp G, L.ae_eq_of_onChain hcong] with x h1 h2 h3 h4 h5
  rw [h1, h5, pstar_add, h2]
  simp [h3, h4]

theorem pstarLp_smul (hrow : RowOnChain S cap) (c : ℝ) (F : Lp ℝ 2 L.mu) :
    L.pstarLp (c • F) = c • L.pstarLp F := by
  refine Lp.ext ?_
  have hcong : ∀ x, OnChain cap x → pstar S cap ⇑(c • F) x = pstar S cap (c • ⇑F) x :=
    fun _ hx => pstar_congr_onChain hrow (L.ae_iff_eq.mp (Lp.coeFn_smul c F)) hx
  filter_upwards [L.coeFn_pstarLp (c • F), Lp.coeFn_smul c (L.pstarLp F),
    L.coeFn_pstarLp F, L.ae_eq_of_onChain hcong] with x h1 h2 h3 h4
  rw [h1, h4, pstar_smul, h2]
  simp [h3]

/-- **`P⋆` as a bounded linear operator on `L²(μ)`**, of norm at most `1`.

This is the `p = 2` case of `lem:doubling_operator`(1)'s first clause, and the operator that
`lem:doubling_operator`(3) — proved abstractly in `Operator.lean` — is meant to be instantiated
at. The adjoint clause `P⋆ = P*` is *not* proved: the density action `P` is not modelled here. -/
noncomputable def pstarL2 (hrow : RowOnChain S cap) : Lp ℝ 2 L.mu →L[ℝ] Lp ℝ 2 L.mu :=
  LinearMap.mkContinuous
    { toFun := L.pstarLp
      map_add' := L.pstarLp_add hrow
      map_smul' := fun c F => L.pstarLp_smul hrow c F } 1
    fun F => by simpa using L.norm_pstarLp_le F

@[simp] theorem pstarL2_apply (hrow : RowOnChain S cap) (F : Lp ℝ 2 L.mu) :
    L.pstarL2 hrow F = L.pstarLp F := rfl

theorem coeFn_pstarL2 (hrow : RowOnChain S cap) (F : Lp ℝ 2 L.mu) :
    ⇑(L.pstarL2 hrow F) =ᵐ[L.mu] pstar S cap ⇑F :=
  L.coeFn_pstarLp F

/-- `‖P⋆‖ ≤ 1` on `L²(μ)`. -/
theorem norm_pstarL2_le (hrow : RowOnChain S cap) : ‖L.pstarL2 hrow‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### `lem:doubling_fixed_points`, the `P⋆` half, in `L²(λ)`

`FixedPoints.lean` proves it for **bounded** `f`, `Stat.inv` being available only there. The
extension of invariance to unbounded non-negative functions (`tsum_pstar_le`) removes exactly
that narrowing, so the `P⋆` half of `eq:doubling_fixed` is proved here at the paper's own
hypothesis `f ∈ L²(λ)`, and with `P⋆ f = f` required only on the chain — that is, `λ`-a.e. -/

/-- Equality in Jensen at every state of the chain, for a fixed point in `L²(λ)`. -/
theorem jensen_gap_zero_memLp {f : St → ℝ} (hf : MemLp f 2 L.mu)
    (hfix : ∀ x, OnChain cap x → pstar S cap f x = f x) {x : St} (hx : OnChain cap x) :
    pstar S cap (fun y => (f y) ^ 2) x - (pstar S cap f x) ^ 2 = 0 := by
  have hsq : Summable fun y => L.lam y * (f y) ^ 2 :=
    (L.memLp_two_iff.mp hf).congr fun y => by rw [abs_rpow_two]; ring
  obtain ⟨hsummP, hle⟩ := L.tsum_pstar_le (fun y => sq_nonneg (f y)) hsq
  have hEq : ∀ y : St, L.lam y * (pstar S cap f y) ^ 2 = L.lam y * (f y) ^ 2 := by
    intro y
    by_cases hy : OnChain cap y
    · rw [hfix y hy]
    · rw [L.vanish hy, zero_mul, zero_mul]
  have hsummF : Summable fun y => L.lam y * (pstar S cap f y) ^ 2 :=
    hsq.congr fun y => (hEq y).symm
  have hgapnn : ∀ y : St,
      0 ≤ L.lam y * (pstar S cap (fun z => (f z) ^ 2) y - (pstar S cap f y) ^ 2) := fun y =>
    mul_nonneg (L.nonneg y) (by linarith [sq_pstar_le (S := S) (cap := cap) f y])
  have hsplit : (fun y => L.lam y * (pstar S cap (fun z => (f z) ^ 2) y
        - (pstar S cap f y) ^ 2))
      = fun y => L.lam y * pstar S cap (fun z => (f z) ^ 2) y
          - L.lam y * (pstar S cap f y) ^ 2 := by
    funext y; ring
  have hgapsum : Summable fun y => L.lam y * (pstar S cap (fun z => (f z) ^ 2) y
      - (pstar S cap f y) ^ 2) := by
    rw [hsplit]; exact hsummP.sub hsummF
  have htotal : ∑' y, L.lam y * (pstar S cap (fun z => (f z) ^ 2) y
      - (pstar S cap f y) ^ 2) ≤ 0 := by
    rw [hsplit, Summable.tsum_sub hsummP hsummF, tsum_congr hEq]
    linarith
  have hzero : ∑' y, L.lam y * (pstar S cap (fun z => (f z) ^ 2) y
      - (pstar S cap f y) ^ 2) = 0 :=
    le_antisymm htotal (tsum_nonneg hgapnn)
  have hsum0 : HasSum (fun y => L.lam y * (pstar S cap (fun z => (f z) ^ 2) y
      - (pstar S cap f y) ^ 2)) 0 := by
    have h := hgapsum.hasSum
    rwa [hzero] at h
  have hlex := le_hasSum hsum0 x fun y _ => hgapnn y
  have hpos := L.pos hx
  have hg0 : 0 ≤ pstar S cap (fun z => (f z) ^ 2) x - (pstar S cap f x) ^ 2 := by
    linarith [sq_pstar_le (S := S) (cap := cap) f x]
  refine le_antisymm ?_ hg0
  rcases le_or_gt (pstar S cap (fun z => (f z) ^ 2) x - (pstar S cap f x) ^ 2) 0 with h | h
  · exact h
  · exact absurd hlex (not_le.mpr (mul_pos hpos h))

/-- **`eq:doubling_fixed`, the `P⋆` half, at the paper's hypothesis.** A fixed point of the
function action in `L²(λ)` is constant on the chain.

The ladder is climbed by the decrement alone, exactly as in `FixedPoints.fixed_const`; what is
new is that `f` is only assumed square-integrable, and the fixed-point equation only `λ`-a.e. -/
theorem fixed_const_memLp {f : St → ℝ} (hf : MemLp f 2 L.mu)
    (hfix : ∀ x, OnChain cap x → pstar S cap f x = f x) :
    ∀ x : St, OnChain cap x → f x = f (.lad 0) := by
  have hstep : ∀ n : ℕ, OnChain cap (St.lad (n + 1)) → f (.lad (n + 1)) = f (.lad n) := by
    intro n hn
    have hfn := hfix (St.lad (n + 1)) hn
    by_cases hD : HasDouble cap (n + 1)
    · have hgap := L.jensen_gap_zero_memLp hf hfix hn
      rw [pstar_sq_gap f (Nat.le_add_left 1 n) hD] at hgap
      have he : 0 < S.eps (n + 1) * (1 - S.eps (n + 1)) :=
        mul_pos (S.eps_pos (Nat.le_add_left 1 n)) (S.one_sub_eps_pos (Nat.le_add_left 1 n))
      have hzero : f (.lad (2 * (n + 1))) - f (.lad (n + 1 - 1)) = 0 := by
        have hsq0 : (f (.lad (2 * (n + 1))) - f (.lad (n + 1 - 1))) ^ 2 = 0 := by
          by_contra hne
          have hpos : 0 < (f (.lad (2 * (n + 1))) - f (.lad (n + 1 - 1))) ^ 2 :=
            lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
          nlinarith [hgap, he, hpos]
        exact (pow_eq_zero_iff two_ne_zero).mp hsq0
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
    | succ n ih => intro hn; rw [hstep n hn, ih (onChain_lad_of_succ hn)]
  intro x hx
  rcases x with n | _
  · exact hlad n hx
  · have hfn := hfix (St.lad 0) (onChain_src cap)
    rw [pstar_src] at hfn
    exact hfn

end Stat

end GFNBounds.Doubling
