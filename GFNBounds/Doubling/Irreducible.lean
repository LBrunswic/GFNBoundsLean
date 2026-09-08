import GFNBounds.Doubling.Ratios

/-!
# Irreducibility, and why an invariant probability is positive

**`lem:doubling_irreducible`** — `app_doubling.tex:101–128`
and **`lem:doubling_truncation_irreducible`** — `app_doubling.tex:1805–1846` (Steps 1–3).

> (irreducible) let `ε(j) ∈ (0,1)` for every `j ≥ 1`. Then the loop-closed backward chain is
> irreducible, and every invariant probability of it is positive at every state.
>
> (truncation) let `ε(j) ∈ (0,1)` and let `K ≥ d` be an *even* integer. Then the truncation at `K`
> is an irreducible Markov chain on the `K+2` states `{s₀,1,…,K,s_f}` […]

Irreducibility is carried by an explicit reachability relation `Reach`, the reflexive-transitive
closure of the edge relation `Edge`, whose four constructors are the four positive transitions of
`eq:doubling_policy`. `edge_pstar_pos` is the bridge: an edge is exactly a state at which the
one-step law `P⋆(1_{\{y\}})(x)` is positive, so nothing here is a second model of the chain.

Positivity of an invariant probability is then *derived*, not assumed: `PreStat` carries every
field of `Stat` except `pos`, and `PreStat.toStat` supplies `pos` from irreducibility. That closes
the second sentence of `lem:doubling_irreducible` and removes the one place where the Lean
`Setting` layer was stronger than the paper.

## SCOPE (disclosed)

* Both directions of the truncation argument are proved, including the parity: `reach_one_lad`
  needs `K` even exactly where the paper does — at an odd `n` with `2^r < n ≤ K`, where the route
  is through `n+1`, which must still be `≤ K`.
* The state set of the truncation is `{s₀,1,…,K,s_f}` in the paper and `OnChain (some K)` here.
  `St` remains infinite; the count `K+2` is not formalized, and the claim proved is that `Reach`
  is total on `OnChain`, which is what every consumer uses.
* `lem:doubling_truncation_irreducible`'s Step 4 — existence and uniqueness of `λ^K`, and
  `B̂_K < +∞` — is not here: the first two are `TruncationStat.lean` (`exists_stat`,
  `stat_unique`, by finite-dimensional linear algebra rather than Perron–Frobenius) and the last
  is `OperatorL2.lean` (`Stat.exists_bhat`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ε(j) ∈ (0,1)` for `j ≥ 1` | ⚠ strengthened: `Setting` carries `sup ε ≤ ε_max < 1` (`eps_pos`, `eps_le`, `epsMax_lt_one`) where the paper needs only pointwise `ε(j) < 1`; the proof uses per-edge positivity alone |
| the target row is a probability on `{1,…,d}` | ✓ carried (`row_sum`, `row_supp`, `row_nonneg`) |
| `K ≥ d` | ✓ carried (`hdK`) |
| `K` even | ✓ carried (`hK`) |
| `λ` an invariant probability | ✓ carried as `PreStat` |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

variable {S : Setting} {cap : Option ℕ}

/-- The positive transitions of `eq:doubling_policy`: the wrap `s₀ → s_f`, the decrement
`j+1 → j`, the doubling `j+1 → 2(j+1)` where that edge survives the cap, and the target row
`s_f → k` at every `k` the row charges. -/
inductive Edge (S : Setting) (cap : Option ℕ) : St → St → Prop
  | wrap : Edge S cap (.lad 0) .sink
  | dec (j : ℕ) : Edge S cap (.lad (j + 1)) (.lad j)
  | dbl (j : ℕ) (h : HasDouble cap (j + 1)) : Edge S cap (.lad (j + 1)) (.lad (2 * (j + 1)))
  | row (k : ℕ) (hk : k ∈ Finset.Icc 1 S.d) (hpos : 0 < S.row k) : Edge S cap .sink (.lad k)

/-- Reachability: the reflexive-transitive closure of `Edge`. -/
abbrev Reach (S : Setting) (cap : Option ℕ) : St → St → Prop :=
  Relation.ReflTransGen (Edge S cap)

/-- The point mass at an arbitrary state, generalizing `dirac`. -/
def ptFn (y : St) : St → ℝ := fun x => if x = y then 1 else 0

theorem ptFn_nonneg (y x : St) : 0 ≤ ptFn y x := by rw [ptFn]; split <;> norm_num

theorem ptFn_bounded (y : St) : ∃ C, ∀ x, |ptFn y x| ≤ C :=
  ⟨1, fun x => by rw [abs_of_nonneg (ptFn_nonneg y x), ptFn]; split <;> norm_num⟩

@[simp] theorem ptFn_self (y : St) : ptFn y y = 1 := by simp [ptFn]

theorem ptFn_of_ne {y x : St} (h : x ≠ y) : ptFn y x = 0 := by simp [ptFn, h]

/-- **The bridge.** An edge is a positive one-step transition: `P⋆(1_{\{y\}})(x) > 0`. -/
theorem edge_pstar_pos {x y : St} (h : Edge S cap x y) : 0 < pstar S cap (ptFn y) x := by
  cases h with
  | wrap => simp
  | dec j =>
      by_cases hD : HasDouble cap (j + 1)
      · rw [pstar_lad_succ, if_pos hD, ptFn_self,
          ptFn_of_ne (by simp; omega : (St.lad (2 * (j + 1)) : St) ≠ St.lad j)]
        have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
        have h2 : 0 < 1 - S.eps (j + 1) := S.one_sub_eps_pos (Nat.le_add_left 1 j)
        nlinarith
      · rw [pstar_lad_succ, if_neg hD, ptFn_self]; norm_num
  | dbl j hD =>
      rw [pstar_lad_succ, if_pos hD, ptFn_self,
        ptFn_of_ne (by simp; omega : (St.lad j : St) ≠ St.lad (2 * (j + 1)))]
      have h1 : 0 < S.eps (j + 1) := S.eps_pos (Nat.le_add_left 1 j)
      have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
      nlinarith
  | row k hk hpos =>
      rw [pstar_sink]
      have hterm : ∀ i ∈ Finset.Icc 1 S.d, S.row i * ptFn (St.lad k) (St.lad i) =
          if i = k then S.row k else 0 := by
        intro i _
        by_cases hik : i = k
        · subst hik; simp
        · rw [ptFn_of_ne (by simp [hik]), mul_zero, if_neg hik]
      rw [Finset.sum_congr rfl hterm,
        Finset.sum_ite_eq' (Finset.Icc 1 S.d) k (fun _ => S.row k), if_pos hk]
      exact hpos

/-! ### The reachability facts -/

/-- The target row charges some index in `{1,…,d}`: it is a probability there. -/
theorem exists_row_pos (S : Setting) : ∃ k, k ∈ Finset.Icc 1 S.d ∧ 0 < S.row k := by
  by_contra hcon
  have hz : ∀ k ∈ Finset.Icc 1 S.d, S.row k = 0 := by
    intro k hk
    rcases lt_or_eq_of_le (S.row_nonneg k) with h | h
    · exact absurd ⟨k, hk, h⟩ hcon
    · exact h.symm
  have := S.row_sum
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero] at this
  exact zero_ne_one this

/-- `n` consecutive decrements: every ladder state reaches every lower one. -/
theorem reach_dec (S : Setting) (cap : Option ℕ) (j n : ℕ) :
    Reach S cap (.lad (j + n)) (.lad j) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      refine Relation.ReflTransGen.head ?_ ih
      exact (Edge.dec (j + n) : Edge S cap (.lad (j + n + 1)) (.lad (j + n)))

theorem reach_dec_le (S : Setting) (cap : Option ℕ) {i j : ℕ} (h : j ≤ i) :
    Reach S cap (.lad i) (.lad j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  exact reach_dec S cap j n

/-- Every state reaches the ladder state `1`: down to `s₀`, wrap to `s_f`, fire the row, then
decrement. -/
theorem reach_one (S : Setting) (cap : Option ℕ) (x : St) : Reach S cap x (.lad 1) := by
  obtain ⟨k, hk, hkpos⟩ := exists_row_pos S
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hsink : Reach S cap .sink (.lad 1) :=
    Relation.ReflTransGen.head (Edge.row k hk hkpos) (reach_dec_le S cap hk1)
  have hsrc : Reach S cap (.lad 0) (.lad 1) :=
    Relation.ReflTransGen.head Edge.wrap hsink
  rcases x with j | _
  · exact (reach_dec_le S cap (Nat.zero_le j)).trans hsrc
  · exact hsink

/-! ### From `1` to everywhere: the loop closure -/

/-- On the loop closure `1` reaches every ladder state, by the paper's induction: from `n` the
doubling edge reaches `2n ≥ n+1`, and `2n − (n+1)` decrements land on `n+1`. -/
theorem reach_lad_none (S : Setting) : ∀ n : ℕ, 1 ≤ n → Reach S none (.lad 1) (.lad n) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · exact Relation.ReflTransGen.refl
      · have hstep : Edge S none (.lad n) (.lad (2 * n)) := by
          obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn1).symm⟩
          exact Edge.dbl i trivial
        exact ((ih hn1).tail hstep).trans (reach_dec_le S none (by omega : n + 1 ≤ 2 * n))

/-- **`lem:doubling_irreducible`, the graph half.** On the loop closure every state reaches every
state. -/
theorem reach_all_none (S : Setting) (x y : St) : Reach S none x y := by
  refine (reach_one S none x).trans ?_
  rcases y with j | _
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact reach_dec_le S none (Nat.zero_le 1)
    · exact reach_lad_none S j hj
  · exact ((reach_lad_none S 1 le_rfl)).trans
      (Relation.ReflTransGen.head (Edge.dec 0) (Relation.ReflTransGen.single Edge.wrap))

/-! ### From `1` to everywhere: the truncation at an even cap -/

section Truncation

variable {K : ℕ}

/-- Doubling along the powers of two: `1 → 2 → 4 → ⋯ → 2^r`, every edge present while `2^r ≤ K`. -/
theorem reach_pow_two (S : Setting) :
    ∀ r : ℕ, 2 ^ r ≤ K → Reach S (some K) (.lad 1) (.lad (2 ^ r)) := by
  intro r
  induction r with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ r ih =>
      intro hle
      have hr : 2 ^ r ≤ K := by
        have : 2 ^ r ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hpos : 0 < 2 ^ r := pow_pos (by norm_num : 0 < 2) r
      have hstep : Edge S (some K) (.lad (2 ^ r)) (.lad (2 * 2 ^ r)) := by
        obtain ⟨i, hi⟩ : ∃ i, 2 ^ r = i + 1 := ⟨2 ^ r - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
        rw [hi]
        refine Edge.dbl i ?_
        show 2 * (i + 1) ≤ K
        rw [← hi]; rw [pow_succ] at hle; omega
      have : 2 * 2 ^ r = 2 ^ (r + 1) := by rw [pow_succ]; ring
      rw [← this]
      exact (ih hr).tail hstep

/-- **`lem:doubling_truncation_irreducible`, Step 3.** On the truncation at an even cap `K ≥ 1`
the ladder state `1` reaches every ladder state `n ≤ K`. -/
theorem reach_one_lad (S : Setting) (hK : Even K) (hK1 : 1 ≤ K) {n : ℕ} (hn : 1 ≤ n)
    (hnK : n ≤ K) : Reach S (some K) (.lad 1) (.lad n) := by
  -- `r` is the largest exponent with `2^r ≤ K`
  obtain ⟨r, hr1, hr2⟩ : ∃ r, 2 ^ r ≤ K ∧ K < 2 ^ (r + 1) := by
    refine ⟨Nat.log 2 K, Nat.pow_log_le_self 2 (by omega), ?_⟩
    exact Nat.lt_pow_succ_log_self (by norm_num) K
  have hbase : ∀ i : ℕ, 1 ≤ i → i ≤ 2 ^ r → Reach S (some K) (.lad 1) (.lad i) := by
    intro i _ hi
    exact (reach_pow_two S r hr1).trans (reach_dec_le S (some K) hi)
  have heven : ∀ i : ℕ, 2 ^ r < i → i ≤ K → Even i → Reach S (some K) (.lad 1) (.lad i) := by
    intro i hlt hle hev
    obtain ⟨t, ht⟩ := hev
    have ht' : i = 2 * t := by omega
    have htpos : 1 ≤ t := by omega
    have hthalf : t ≤ 2 ^ r := by
      have h2 : 2 * t ≤ K := by omega
      have : K < 2 * 2 ^ r := by rw [pow_succ] at hr2; omega
      omega
    have hstep : Edge S (some K) (.lad t) (.lad (2 * t)) := by
      obtain ⟨u, hu⟩ : ∃ u, t = u + 1 := ⟨t - 1, (Nat.succ_pred_eq_of_pos htpos).symm⟩
      rw [hu]
      refine Edge.dbl u ?_
      show 2 * (u + 1) ≤ K
      rw [← hu]; omega
    rw [ht']
    exact (hbase t htpos hthalf).tail hstep
  rcases le_or_gt n (2 ^ r) with hle | hgt
  · exact hbase n hn hle
  · rcases Nat.even_or_odd n with hev | hodd
    · exact heven n hgt hnK hev
    · -- `n` odd: `n ≠ K` since `K` is even, so `n + 1 ≤ K` is even and above `2^r`
      have hne : n ≠ K := by
        rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) hK
      have hn1K : n + 1 ≤ K := by omega
      have hev1 : Even (n + 1) := Odd.add_one hodd
      exact (heven (n + 1) (by omega) hn1K hev1).tail (Edge.dec n)

/-- **`lem:doubling_truncation_irreducible`, Steps 2–3.** On the truncation at an even cap every
on-chain state reaches every on-chain state. -/
theorem reach_all_some (S : Setting) (hK : Even K) (hdK : S.d ≤ K) {x y : St}
    (hy : OnChain (some K) y) : Reach S (some K) x y := by
  have hK1 : 1 ≤ K := le_trans S.d_pos hdK
  refine (reach_one S (some K) x).trans ?_
  rcases y with j | _
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact reach_dec_le S (some K) (Nat.zero_le 1)
    · exact reach_one_lad S hK hK1 hj hy
  · exact Relation.ReflTransGen.head (Edge.dec 0) (Relation.ReflTransGen.single Edge.wrap)

end Truncation

/-! ### An invariant probability is positive at every state it can reach -/

/-- Every field of `Stat` except positivity. `PreStat.toStat` recovers positivity from
irreducibility, which is the second sentence of `lem:doubling_irreducible`. -/
structure PreStat (S : Setting) (cap : Option ℕ) where
  lam : St → ℝ
  nonneg : ∀ x, 0 ≤ lam x
  vanish : ∀ ⦃x⦄, ¬ OnChain cap x → lam x = 0
  summable : Summable lam
  total : ∑' x, lam x = 1
  inv : ∀ f : St → ℝ, (∃ C, ∀ x, |f x| ≤ C) →
          ∑' x, lam x * pstar S cap f x = ∑' x, lam x * f x

namespace PreStat

variable (P : PreStat S cap)

theorem summable_mul {f : St → ℝ} (hf : ∃ C, ∀ x, |f x| ≤ C) :
    Summable (fun x => P.lam x * f x) := by
  obtain ⟨C, hC⟩ := hf
  refine Summable.of_norm_bounded (g := fun x => C * P.lam x) (P.summable.mul_left C) ?_
  intro x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (P.nonneg x)]
  exact mul_le_mul_of_nonneg_left (hC x) (P.nonneg x) |>.trans_eq (by ring)

theorem hasSum_mul_ptFn (y : St) : HasSum (fun x => P.lam x * ptFn y x) (P.lam y) := by
  have h : (fun x => P.lam x * ptFn y x) = fun x => if x = y then P.lam y else 0 := by
    funext x
    by_cases hx : x = y
    · subst hx; simp
    · simp [ptFn, hx]
  rw [h]; exact hasSum_ite_eq _ _

/-- Total one-step flux into `y` is `λ(y)`: `inv` tested against the point mass at `y`. -/
theorem hasSum_flux (y : St) :
    HasSum (fun x => P.lam x * pstar S cap (ptFn y) x) (P.lam y) := by
  have hsum : Summable (fun x => P.lam x * pstar S cap (ptFn y) x) := by
    obtain ⟨C, hC⟩ := ptFn_bounded y
    exact P.summable_mul ⟨C, fun x => pstar_bounded hC x⟩
  have h := hsum.hasSum
  rwa [P.inv (ptFn y) (ptFn_bounded y), (P.hasSum_mul_ptFn y).tsum_eq] at h

/-- Positivity travels along an edge. -/
theorem lam_pos_step {x y : St} (h : Edge S cap x y) (hx : 0 < P.lam x) : 0 < P.lam y := by
  have hle := le_hasSum (P.hasSum_flux y) x
    (fun z _ => mul_nonneg (P.nonneg z) (pstar_nonneg (ptFn_nonneg y) z))
  exact lt_of_lt_of_le (mul_pos hx (edge_pstar_pos h)) hle

/-- Positivity travels along a path. -/
theorem lam_pos_of_reach {x y : St} (h : Reach S cap x y) (hx : 0 < P.lam x) : 0 < P.lam y := by
  induction h with
  | refl => exact hx
  | tail _ hstep ih => exact P.lam_pos_step hstep ih

/-- A probability charges some state, and by `vanish` that state is on chain. -/
theorem exists_pos : ∃ x, OnChain cap x ∧ 0 < P.lam x := by
  by_contra hcon
  have hz : ∀ x, P.lam x = 0 := by
    intro x
    by_cases hx : OnChain cap x
    · rcases lt_or_eq_of_le (P.nonneg x) with h | h
      · exact absurd ⟨x, hx, h⟩ hcon
      · exact h.symm
    · exact P.vanish hx
  have := P.total
  rw [tsum_congr hz, tsum_zero] at this
  exact zero_ne_one this

/-- **`lem:doubling_irreducible`, the measure half.** An invariant probability of an irreducible
chain is positive at every state of that chain. -/
theorem pos_of_irreducible (hirr : ∀ x y : St, OnChain cap y → Reach S cap x y)
    ⦃y : St⦄ (hy : OnChain cap y) : 0 < P.lam y := by
  obtain ⟨x, _, hx⟩ := P.exists_pos
  exact P.lam_pos_of_reach (hirr x y hy) hx

/-- Positivity is not an extra hypothesis: irreducibility supplies it. -/
def toStat (hirr : ∀ x y : St, OnChain cap y → Reach S cap x y) : Stat S cap where
  lam := P.lam
  nonneg := P.nonneg
  pos := P.pos_of_irreducible hirr
  vanish := P.vanish
  summable := P.summable
  total := P.total
  inv := P.inv

end PreStat

/-- On the loop closure, positivity comes free. -/
def PreStat.toStatNone (P : PreStat S none) : Stat S none :=
  P.toStat fun x y _ => reach_all_none S x y

/-- On the truncation at an even cap `K ≥ d`, positivity comes free. -/
def PreStat.toStatSome {K : ℕ} (P : PreStat S (some K)) (hK : Even K) (hdK : S.d ≤ K) :
    Stat S (some K) :=
  P.toStat fun _ _ hy => reach_all_some S hK hdK hy

end GFNBounds.Doubling
