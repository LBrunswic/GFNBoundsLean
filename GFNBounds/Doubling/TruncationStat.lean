import GFNBounds.Doubling.Irreducible

/-!
# The truncation carries a unique invariant probability

**`lem:doubling_truncation_irreducible`, Step 4** — `app_doubling.tex:1805–1846`.

> *Step 4 (the invariant probability and the diffusion operator).* By Steps 2 and 3 every state
> leads to every other, so the truncation is an irreducible chain on a finite state space and
> carries a unique invariant probability `λ^K`, positive at every state
> \citep{levin2017markov}. Lemma `lem:doubling_operator`*(2)*, applied to that chain, gives `S`
> and `eq:doubling_resolvent`; `S` acts on the finite-dimensional space `L²(λ^K)`, so
> `B̂_K = ‖S‖_{L²(λ^K)} < +∞`.

Steps 1–3 are `Irreducible.lean` (`reach_all_some`). What is added here is the citation Step 4
makes: **existence**, **uniqueness** and **positivity** of `λ^K`.

## The modelling decision: finite linear algebra, not Perron–Frobenius

Mathlib v4.31.0 has no stationary-distribution existence theorem and no Perron–Frobenius, and this
library builds no chain. It does not need one: at a finite cap the statement is linear algebra on
`K + 2` coordinates, and each of the three assertions has an elementary proof that uses only what
`Setting` and `Irreducible` already carry.

* **Existence.** `chainFinset K` is the closed state set `{s₀,1,…,K,s_f}`; `pstar_congr_trunc`
  says `P⋆` at an on-chain state reads `f` only there (this is Step 1's "the state set is
  closed", and it is where `d ≤ K` is consumed). Writing `kern x y := P⋆(1_{\{y\}})(x)` — the
  *tested* `pstar`, not a second model of the chain — `pstar_eq_sum_kern` turns `P⋆` into a finite
  matrix product and `sum_kern` says the rows sum to `1`. The density action `densMap` is then an
  endomorphism of the finite-dimensional `CVec K = ↥(chainFinset K) → ℝ` preserving total mass, so
  its range misses the vector `1`, `densMap − Id` is not surjective, hence — finite dimension —
  not injective, and a non-zero fixed vector `l` exists. Non-negativity is the standard `|·|`
  argument: `|l| ≤ densMap |l|` pointwise by the triangle inequality, with equal total masses, so
  the two are equal; normalizing gives a probability. No spectral theory is used.
* **Positivity** is not re-proved: `PreStat.toStatSome` already derives it from `reach_all_some`,
  which is what makes the existence statement land on `Stat` rather than `PreStat`.
* **Uniqueness** is the ratio maximum principle, and it runs on `Edge`/`Reach` directly. If `λ`
  and `λ'` are two invariant probabilities, let `t` minimize `λ/λ'` over the chain, attained at
  `x₀`. Then `ν := λ − tλ'` is `≥ 0`, invariant and vanishes at `x₀`; invariance at a state where
  `ν` vanishes forces `ν` to vanish at every state carrying a positive edge *into* it
  (`le_hasSum` on a non-negative summable family with sum `0`), so `ν = 0` propagates backwards
  along `Reach _ x₀`, which by `reach_all_some` reaches every state. Both being probabilities
  gives `t = 1`.

## SCOPE (disclosed)

* **`B̂_K < +∞` is not proved here.** It is the second sentence of Step 4 and needs
  `lem:doubling_operator`(2) — the `L^p` layer with its adjoint, the library's obstruction 2. Only
  the first sentence, the invariant probability, is closed.
* ⚠ **Existence needs less than the paper's hypotheses**: `exists_preStat` uses only `d ≤ K`, not
  the parity of `K`. Parity enters through `reach_all_some`, hence only in the *positivity* and
  *uniqueness* halves (`exists_stat`, `stat_unique`). This is a strengthening, disclosed rather
  than silently absorbed.
* The count "`K + 2` states" is not formalized, as in `Irreducible.lean`: `St` remains infinite,
  the chain set is the `Finset` `chainFinset K`, and `mem_chainFinset` identifies it with
  `OnChain (some K)`.
* `kern` is a `def` unfolding to `pstar S cap (ptFn y) x`, so it introduces no second description
  of the dynamics; `Ratios.lean`'s "the transition matrix is never written down" stays true of
  every statement that does not need finite-dimensionality. Here finite-dimensionality *is* the
  argument, and the matrix is used only over `chainFinset K`.
* `truncStat` is `Nonempty.some` on the existence theorem, so it is noncomputable and not
  canonical as a term; `stat_unique` says it is canonical as a function.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ε(j) ∈ (0,1)` for every `j ≥ 1` | ✓ carried (in `Setting`) |
| the target row is a probability on `{1,…,d}` | ✓ carried (in `Setting`) |
| `K ≥ d` | ✓ carried (`hdK`), and it is what closes the state set |
| `K` even | ✓ carried (`hK`) for positivity and uniqueness; ⚠ **not needed** for existence |
| chain irreducible (Steps 2–3) | ✓ carried, imported as `reach_all_some` |

## What the paper's Step 4 concludes and this file delivers

| paper | here |
|---|---|
| `λ^K` exists | `exists_preStat`, `exists_stat`, `truncStat` |
| `λ^K` is unique | `stat_unique` |
| `λ^K` is positive at every state | `Stat.pos` of `exists_stat`, via `PreStat.toStatSome` |
| `B̂_K < +∞` | ✗ not proved; needs `lem:doubling_operator`(2) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/


namespace GFNBounds.Doubling

variable {S : Setting} {K : ℕ}

/-- The `K + 2` states `{s₀, 1, …, K, s_f}` of the truncation, as a `Finset`. -/
def chainFinset (K : ℕ) : Finset St := insert St.sink ((Finset.range (K + 1)).image St.lad)

@[simp] theorem mem_chainFinset {x : St} : x ∈ chainFinset K ↔ OnChain (some K) x := by
  rcases x with j | _
  · simp [chainFinset]
  · simp [chainFinset]

theorem sink_mem_chainFinset : (St.sink : St) ∈ chainFinset K := by simp

theorem chainFinset_nonempty : (chainFinset K).Nonempty := ⟨St.sink, sink_mem_chainFinset⟩

/-- The chain set is closed: `P⋆` at an on-chain state reads `f` only at on-chain states. -/
theorem pstar_congr_trunc (hdK : S.d ≤ K) {f g : St → ℝ}
    (h : ∀ z, OnChain (some K) z → f z = g z) {x : St} (hx : OnChain (some K) x) :
    pstar S (some K) f x = pstar S (some K) g x := by
  rcases x with j | _
  · rcases j with _ | j
    · simpa using h St.sink (onChain_sink _)
    · have hjK : j + 1 ≤ K := hx
      by_cases hD : HasDouble (some K) (j + 1)
      · have h2 : 2 * (j + 1) ≤ K := hD
        rw [pstar_lad_succ, pstar_lad_succ, if_pos hD, if_pos hD,
          h _ (show OnChain (some K) (St.lad (2 * (j + 1))) from h2),
          h _ (show OnChain (some K) (St.lad j) by exact Nat.le_of_succ_le hjK)]
      · rw [pstar_lad_succ, pstar_lad_succ, if_neg hD, if_neg hD,
          h _ (show OnChain (some K) (St.lad j) by exact Nat.le_of_succ_le hjK)]
  · simp only [pstar_sink]
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k ≤ K := le_trans (Finset.mem_Icc.mp hk).2 hdK
    rw [h _ (show OnChain (some K) (St.lad k) from this)]

/-- `P⋆` commutes with a finite sum of functions. -/
theorem pstar_finsetSum {ι : Type*} {cap : Option ℕ} (s : Finset ι) (F : ι → St → ℝ) (x : St) :
    pstar S cap (fun z => ∑ i ∈ s, F i z) x = ∑ i ∈ s, pstar S cap (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [congrFun (pstar_const (S := S) (cap := cap) 0) x]
  | insert a s ha ih =>
      have hfun : (fun z => ∑ i ∈ insert a s, F i z)
          = F a + fun z => ∑ i ∈ s, F i z := by
        funext z; simp [Finset.sum_insert ha]
      rw [hfun, pstar_add]
      simp only [Pi.add_apply]
      rw [ih, Finset.sum_insert ha]

/-! ### The transition matrix, read off `P⋆` -/

/-- The one-step transition probability `x → y`, *defined* as `P⋆` applied to the point mass at
`y`. It is not a second model of the chain: it is the same `pstar`, tested. -/
noncomputable def kern (S : Setting) (cap : Option ℕ) (x y : St) : ℝ := pstar S cap (ptFn y) x

theorem kern_nonneg {cap : Option ℕ} (x y : St) : 0 ≤ kern S cap x y :=
  pstar_nonneg (ptFn_nonneg y) x

/-- The rows of the truncation sum to `1` over the chain set. -/
theorem sum_kern (hdK : S.d ≤ K) {x : St} (hx : OnChain (some K) x) :
    ∑ y ∈ chainFinset K, kern S (some K) x y = 1 := by
  classical
  have h1 : ∑ y ∈ chainFinset K, kern S (some K) x y
      = pstar S (some K) (fun z => ∑ y ∈ chainFinset K, ptFn y z) x :=
    (pstar_finsetSum _ _ _).symm
  have h2 : ∀ z : St, OnChain (some K) z →
      (∑ y ∈ chainFinset K, ptFn y z) = (1 : ℝ) := by
    intro z hz
    have : ∑ y ∈ chainFinset K, ptFn y z = if z ∈ chainFinset K then (1 : ℝ) else 0 := by
      simp only [ptFn]
      exact Finset.sum_ite_eq (chainFinset K) z (fun _ => (1 : ℝ))
    rw [this, if_pos (mem_chainFinset.mpr hz)]
  rw [h1, pstar_congr_trunc hdK (g := fun _ => (1 : ℝ)) h2 hx]
  exact congrFun (pstar_const (S := S) (cap := some K) 1) x

/-- **The representation.** At an on-chain state, `P⋆` is the finite matrix product. -/
theorem pstar_eq_sum_kern (hdK : S.d ≤ K) (f : St → ℝ) {x : St} (hx : OnChain (some K) x) :
    pstar S (some K) f x = ∑ y ∈ chainFinset K, kern S (some K) x y * f y := by
  classical
  have h1 : ∑ y ∈ chainFinset K, kern S (some K) x y * f y
      = ∑ y ∈ chainFinset K, pstar S (some K) (fun z => f y * ptFn y z) x := by
    refine Finset.sum_congr rfl fun y _ => ?_
    have := congrFun (pstar_smul (S := S) (cap := some K) (f := ptFn y) (f y)) x
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [kern, mul_comm]
    exact this.symm
  rw [h1, ← pstar_finsetSum]
  refine pstar_congr_trunc hdK (g := fun z => ∑ y ∈ chainFinset K, f y * ptFn y z) ?_ hx
  intro z hz
  have : ∑ y ∈ chainFinset K, f y * ptFn y z
      = if z ∈ chainFinset K then f z else 0 := by
    simp only [ptFn, mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq (chainFinset K) z f
  rw [this, if_pos (mem_chainFinset.mpr hz)]

/-! ### A non-negative fixed vector of the density action -/

/-- Measures on the truncated chain: a finite-dimensional real vector space. -/
abbrev CVec (K : ℕ) : Type := ↥(chainFinset K) → ℝ

/-- The **density** action `l ↦ lP` on the truncated chain, the transpose of `P⋆`. -/
noncomputable def densMap (S : Setting) (K : ℕ) : CVec K →ₗ[ℝ] CVec K where
  toFun l := fun y => ∑ x : ↥(chainFinset K), l x * kern S (some K) (x : St) (y : St)
  map_add' l l' := by
    funext y; simp only [Pi.add_apply, add_mul]; exact Finset.sum_add_distrib
  map_smul' c l := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem densMap_apply (l : CVec K) (y : ↥(chainFinset K)) :
    densMap S K l y = ∑ x : ↥(chainFinset K), l x * kern S (some K) (x : St) (y : St) := rfl

/-- The density action preserves total mass. -/
theorem sum_densMap (hdK : S.d ≤ K) (l : CVec K) :
    ∑ y : ↥(chainFinset K), densMap S K l y = ∑ x : ↥(chainFinset K), l x := by
  simp only [densMap_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ y : ↥(chainFinset K), kern S (some K) (x : St) (y : St) = 1 := by
    rw [Finset.sum_coe_sort (chainFinset K) (fun y => kern S (some K) (x : St) y)]
    exact sum_kern hdK (mem_chainFinset.mp x.2)
  rw [this, mul_one]

/-- `Id − P` is not injective on the finite-dimensional space of measures: its range lies in the
mass-zero hyperplane. -/
theorem exists_fixed (hdK : S.d ≤ K) : ∃ l : CVec K, l ≠ 0 ∧ densMap S K l = l := by
  classical
  set g : CVec K →ₗ[ℝ] CVec K := densMap S K - LinearMap.id with hg
  have hns : ¬ Function.Surjective g := by
    intro hsurj
    obtain ⟨l, hl⟩ := hsurj (fun _ => (1 : ℝ))
    have h0 : ∑ y : ↥(chainFinset K), g l y = 0 := by
      have : ∀ y : ↥(chainFinset K), g l y = densMap S K l y - l y := fun y => rfl
      simp only [this, Finset.sum_sub_distrib, sum_densMap hdK, sub_self]
    rw [hl] at h0
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h0
    have hcard : 0 < (Finset.univ : Finset ↥(chainFinset K)).card :=
      Finset.card_pos.mpr ⟨⟨St.sink, sink_mem_chainFinset⟩, Finset.mem_univ _⟩
    have hR : (0 : ℝ) < (Finset.univ : Finset ↥(chainFinset K)).card := by exact_mod_cast hcard
    rw [h0] at hR
    exact lt_irrefl _ hR
  have hni : ¬ Function.Injective g := fun h => hns (LinearMap.injective_iff_surjective.mp h)
  have hker : LinearMap.ker g ≠ ⊥ := fun h => hni (LinearMap.ker_eq_bot.mp h)
  obtain ⟨l, hlmem, hlne⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨l, hlne, ?_⟩
  have : densMap S K l - l = 0 := hlmem
  funext y
  have := congrFun this y
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- **The non-negative fixed vector.** `|l|` is a supersolution with the same total mass, hence a
solution; normalizing gives a probability. -/
theorem exists_stationary (hdK : S.d ≤ K) :
    ∃ l : CVec K, (∀ y, 0 ≤ l y) ∧ (∑ y : ↥(chainFinset K), l y) = 1 ∧ densMap S K l = l := by
  classical
  obtain ⟨l, hlne, hlfix⟩ := exists_fixed (S := S) (K := K) hdK
  set m : CVec K := fun y => |l y| with hm
  have hmnn : ∀ y, 0 ≤ m y := fun y => abs_nonneg _
  have hsuper : ∀ y, m y ≤ densMap S K m y := by
    intro y
    have h1 : m y = |densMap S K l y| := by rw [hlfix]
    rw [h1, densMap_apply, densMap_apply]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_mul, abs_of_nonneg (kern_nonneg (S := S) (cap := some K) (x : St) (y : St))]
  have hsum : ∑ y : ↥(chainFinset K), m y = ∑ y : ↥(chainFinset K), densMap S K m y :=
    (sum_densMap hdK m).symm
  have hfix : ∀ y, m y = densMap S K m y :=
    fun y => (Finset.sum_eq_sum_iff_of_le (fun i _ => hsuper i)).mp hsum y (Finset.mem_univ y)
  have hZpos : 0 < ∑ y : ↥(chainFinset K), m y := by
    obtain ⟨y0, hy0⟩ : ∃ y0, l y0 ≠ 0 := by
      by_contra hc
      exact hlne (funext fun y => by simpa using not_not.mp (not_exists.mp hc y))
    exact Finset.sum_pos' (fun i _ => hmnn i) ⟨y0, Finset.mem_univ _, abs_pos.mpr hy0⟩
  refine ⟨fun y => m y / (∑ z : ↥(chainFinset K), m z),
    fun y => div_nonneg (hmnn y) hZpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self (ne_of_gt hZpos)]
  · have : (fun y => m y / (∑ z : ↥(chainFinset K), m z))
        = ((∑ z : ↥(chainFinset K), m z)⁻¹ : ℝ) • m := by
      funext y; simp [div_eq_inv_mul]
    rw [this, map_smul]
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hfix y]

/-! ### The invariant probability of the truncation -/

/-- A measure on the chain set, read as a function on `St` vanishing off the chain. -/
noncomputable def extendCVec (K : ℕ) (l : CVec K) : St → ℝ :=
  fun x => if h : x ∈ chainFinset K then l ⟨x, h⟩ else 0

theorem extendCVec_of_mem {l : CVec K} {x : St} (h : x ∈ chainFinset K) :
    extendCVec K l x = l ⟨x, h⟩ := dif_pos h

theorem extendCVec_of_not_mem {l : CVec K} {x : St} (h : x ∉ chainFinset K) :
    extendCVec K l x = 0 := dif_neg h

theorem sum_extendCVec (l : CVec K) (f : St → ℝ) :
    ∑ x ∈ chainFinset K, extendCVec K l x * f x
      = ∑ x : ↥(chainFinset K), l x * f (x : St) := by
  rw [← Finset.sum_coe_sort (chainFinset K) (fun x => extendCVec K l x * f x)]
  exact Finset.sum_congr rfl fun x _ => by rw [extendCVec_of_mem x.2]

/-- **`lem:doubling_truncation_irreducible`, Step 4 (existence).** The truncation at an even cap
`K ≥ d` carries an invariant probability. -/
theorem exists_preStat (hdK : S.d ≤ K) : Nonempty (PreStat S (some K)) := by
  classical
  obtain ⟨l, hnn, htot, hfix⟩ := exists_stationary (S := S) (K := K) hdK
  refine ⟨{
    lam := extendCVec K l
    nonneg := ?_
    vanish := ?_
    summable := ?_
    total := ?_
    inv := ?_ }⟩
  · intro x
    by_cases hx : x ∈ chainFinset K
    · rw [extendCVec_of_mem hx]; exact hnn _
    · rw [extendCVec_of_not_mem hx]
  · intro x hx
    exact extendCVec_of_not_mem (fun h => hx (mem_chainFinset.mp h))
  · exact summable_of_ne_finset_zero (s := chainFinset K) fun x hx => extendCVec_of_not_mem hx
  · rw [tsum_eq_sum (s := chainFinset K) fun x hx => extendCVec_of_not_mem hx]
    have := sum_extendCVec (K := K) l (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    rw [this, htot]
  · intro f _
    have hoff : ∀ x ∉ chainFinset K, extendCVec K l x * pstar S (some K) f x = 0 := by
      intro x hx; rw [extendCVec_of_not_mem hx, zero_mul]
    have hoff' : ∀ x ∉ chainFinset K, extendCVec K l x * f x = 0 := by
      intro x hx; rw [extendCVec_of_not_mem hx, zero_mul]
    rw [tsum_eq_sum hoff, tsum_eq_sum hoff', sum_extendCVec, sum_extendCVec]
    have hstep : ∀ x : ↥(chainFinset K),
        l x * pstar S (some K) f (x : St)
          = ∑ y : ↥(chainFinset K), l x * kern S (some K) (x : St) (y : St) * f (y : St) := by
      intro x
      rw [pstar_eq_sum_kern hdK f (mem_chainFinset.mp x.2),
        ← Finset.sum_coe_sort (chainFinset K) (fun y => kern S (some K) (x : St) y * f y),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, ← densMap_apply, hfix]

/-- **`lem:doubling_truncation_irreducible`, Step 4.** At an even cap `K ≥ d` the truncation
carries an invariant probability, positive at every state of the chain. -/
theorem exists_stat (hK : Even K) (hdK : S.d ≤ K) : Nonempty (Stat S (some K)) :=
  (exists_preStat hdK).elim fun P => ⟨P.toStatSome hK hdK⟩

/-- The invariant probability `λ^K` of the truncation at an even cap `K ≥ d`. -/
noncomputable def truncStat (S : Setting) {K : ℕ} (hK : Even K) (hdK : S.d ≤ K) :
    Stat S (some K) := (exists_stat hK hdK).some

/-! ### Uniqueness -/

/-- Every `Stat` is a `PreStat`; positivity is the only extra field. -/
def Stat.toPreStat {cap : Option ℕ} (L : Stat S cap) : PreStat S cap where
  lam := L.lam
  nonneg := L.nonneg
  vanish := L.vanish
  summable := L.summable
  total := L.total
  inv := L.inv

/-- Total one-step flux into `y` is `λ(y)`. -/
theorem Stat.hasSum_kern_flux {cap : Option ℕ} (L : Stat S cap) (y : St) :
    HasSum (fun x => L.lam x * kern S cap x y) (L.lam y) :=
  L.toPreStat.hasSum_flux y

/-- **`lem:doubling_truncation_irreducible`, Step 4 (uniqueness).** At an even cap `K ≥ d` the
truncation carries at most one invariant probability. -/
theorem stat_unique (hK : Even K) (hdK : S.d ≤ K) (L L' : Stat S (some K)) : L.lam = L'.lam := by
  classical
  obtain ⟨x0, hx0mem, hx0min⟩ :=
    Finset.exists_min_image (chainFinset K) (fun x => L.lam x / L'.lam x) chainFinset_nonempty
  set t : ℝ := L.lam x0 / L'.lam x0 with ht
  have hL'0 : 0 < L'.lam x0 := L'.pos (mem_chainFinset.mp hx0mem)
  have hzero0 : L.lam x0 - t * L'.lam x0 = 0 := by
    rw [ht, div_mul_cancel₀ _ (ne_of_gt hL'0), sub_self]
  have hnu : ∀ x, 0 ≤ L.lam x - t * L'.lam x := by
    intro x
    by_cases hx : x ∈ chainFinset K
    · have hpos : 0 < L'.lam x := L'.pos (mem_chainFinset.mp hx)
      have := hx0min x hx
      rw [ht] at this ⊢
      have := (le_div_iff₀ hpos).mp this
      linarith
    · have h1 : L.lam x = 0 := L.vanish fun h => hx (mem_chainFinset.mpr h)
      have h2 : L'.lam x = 0 := L'.vanish fun h => hx (mem_chainFinset.mpr h)
      rw [h1, h2]; simp
  have hflux : ∀ y : St, HasSum (fun x => (L.lam x - t * L'.lam x) * kern S (some K) x y)
      (L.lam y - t * L'.lam y) := by
    intro y
    have h := (L.hasSum_kern_flux y).sub ((L'.hasSum_kern_flux y).mul_left t)
    refine h.congr_fun ?_
    intro x
    ring
  have hprop : ∀ x y : St, Edge S (some K) x y → L.lam y - t * L'.lam y = 0 →
      L.lam x - t * L'.lam x = 0 := by
    intro x y hxy hy
    have hs := hflux y
    rw [hy] at hs
    have hle := le_hasSum hs x fun j _ => mul_nonneg (hnu j) (kern_nonneg _ _)
    have hge : 0 ≤ (L.lam x - t * L'.lam x) * kern S (some K) x y :=
      mul_nonneg (hnu x) (kern_nonneg _ _)
    have heq : (L.lam x - t * L'.lam x) * kern S (some K) x y = 0 := le_antisymm hle hge
    have hkpos : 0 < kern S (some K) x y := edge_pstar_pos hxy
    rcases mul_eq_zero.mp heq with h | h
    · exact h
    · exact absurd h (ne_of_gt hkpos)
  have hall : ∀ x : St, L.lam x - t * L'.lam x = 0 := by
    intro x
    have hreach : Reach S (some K) x x0 := reach_all_some S hK hdK (mem_chainFinset.mp hx0mem)
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact hzero0
    | head h' _ ih => exact hprop _ _ h' ih
  have ht1 : t = 1 := by
    have h1 : ∑' x, L.lam x = ∑' x, t * L'.lam x :=
      tsum_congr fun x => by have := hall x; linarith
    rw [L.total, tsum_mul_left, L'.total, mul_one] at h1
    exact h1.symm
  funext x
  have := hall x
  rw [ht1, one_mul] at this
  linarith

end GFNBounds.Doubling
