import GFNBounds.Doubling.TruncationBhat

/-!
# The umbrella theorem's dependence clauses and state count, as formulas

**`theo:doubling_main`** — `app_doubling.tex:276–322` (proof `2341–2393`).

> (3) *(the diffusion operator, on the whole positive recurrent phase)* […] At `s=1` and `0<c<1`
> the expected backward-trajectory length is finite, `σ̄ = j̄/(1−c)`, and there are moreover
> `c₇>0`, depending only on `c`, `d` and `λ_1,…,λ_{2m₀}` with `m₀` the integer of
> Theorem `theo:doubling_decay`, and an integer `m₂>d` with
> `‖f_m‖_{L²(λ)} ≥ c₇ √m ‖(Id−P⋆)f_m‖_{L²(λ)}` for every `m ≥ m₂`;
>
> (5) *(the truncation)* at `s=1` and `0<c<1`, the truncation at `K` is a finite irreducible
> chain on `K+2` states and `B̂_K<+∞` for every even integer `K ≥ d`, and there are `c₈>0` and an
> integer `K₀ ≥ d`, depending only on `c`, `d` and `j̄`, with `B̂_K ≥ c₈ √K` for every even
> `K ≥ K₀`.

`Main.lean` certifies items (1)–(5) in existential form and discloses in its SCOPE two gaps this
file closes: the **state count** `K + 2` of the truncation, and the **dependence clauses** of
items (3) and (5), which an `∃ c₇` or `∃ c₈` does not carry. Here the constants are named
formulas:

* `Decay.c1Of D d λ = (min_{1≤j<2m₀} λ_j j^{p_*}) e^{−c₅c₄/m₀}` and
  `Decay.c2Of D d λ = (max_{1≤j<2m₀} λ_j j^{p_*}) e^{c₅c₄/m₀}`, `c₄ = 16cτ`, `m₀ = D.m0 d` — the
  witnesses of `Decay.decay_two_sided_explicit` at the level `ℓ = m₀`, the decay constants
  `c₁, c₂` of `theo:doubling_decay`(2);
* `Decay.c7Of D d λ = ½ √(c₁/(c₂(p_*−1)))`, the paper's own formula (`cor:doubling_family`);
* `Decay.c7Of_congr`: two profiles agreeing on `1 ≤ j < 2m₀` have the same `c₇` — **this is the
  literal "depending only on `c`, `d` and `λ_1,…,λ_{2m₀}`"**, `D = Decay.ofC` being a function of
  `c` alone; `main_c7_congr` reads it across two settings with the same `d`;
* `main_rate_explicit`: item (3)'s `c₇√m` clause at `c₇ = c7Of`, in the squared form of
  `main_rate`, in the norm form `c₇ √m ‖(Id−P⋆)f_m‖ ≤ ‖f_m‖`, and in the paper's ratio form with
  its denominator shown positive (`Stat.mass_defect_centredTail_pos`);
* `card_chainFinset`, `main_truncation_states`: the on-chain states of the truncation number
  `K + 2`;
* `main_truncation_explicit`: item (5) in one statement, with `c₈ = D.c8Of d j̄` and
  `K₀ = D.K0Of d = 8m₀ + 2` re-exported from `TruncationBhat.lean`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1` | ✓ carried: `hc0`, `hc1`, `heps : ∀ j, S.eps j = epsCS c 1 j` in the `main_` forms; `D : Decay` with `S.eps = D.eps` in `Stat.rate_explicit`. ⚠ strengthened as in `TruncationBhat.lean`: `heps` also fixes `S.eps 0 = c`, a value the chain never reads |
| positive recurrence, `λ` its invariant probability | ✓ carried as `L : Stat S none` (supplied at row (b) by `main_phase`) |
| `m₀` the integer of `theo:doubling_decay` | ✓ `D.m0 d` |
| `c₇ > 0` depending only on `c, d, λ_1..λ_{2m₀}` | ✓ `Decay.c7Of_pos`, `Decay.c7Of_congr`, in the sharper form the paper's proof of `theo:doubling_decay` delivers: agreement is required only on `1 ≤ j < 2m₀`, i.e. `λ_1..λ_{2m₀−1}` ("hence on `λ_1,…,λ_{2m₀}`", `app_doubling.tex:1226–1229`), so the stated clause is implied |
| `m₂ > d`, the inequality for every `m ≥ m₂` | ✓ carried |
| `‖·‖_{L²(λ)}` | ✓ as `√(Stat.mass 2 ·)`, `Stat.mass 2 f = ‖f‖²_{L²(λ)}` (the mass-layer convention of `Main.lean`) |
| the ratio `‖f_m‖/‖(Id−P⋆)f_m‖` is defined | ✓ `Stat.mass_defect_centredTail_pos`, from `eq:doubling_step1` |
| `K` even, `K ≥ d` (first sentence of (5)) | ✓ carried |
| finite, on `K+2` states | ✓ `main_truncation_states` (`Nat.card` of the on-chain subtype) |
| irreducible, `B̂_K < +∞` | ✓ `main_truncation_irreducible`, `main_truncation_bhat`, `Stat.diffOpK_resolvent` |
| `c₈ > 0`, `K₀ ≥ d` depending only on `c, d, j̄` | ✓ `D.c8Of d j̄`, `D.K0Of d` with `D = Decay.ofC hc0 hc1`; `Decay.c8Of_pos`, `Decay.le_K0Of` |
| `K` even in `B̂_K ≥ c₈√K` | ✓ the bound is stated for every `K ≥ K₀` but holds **vacuously** at odd `K` (`K₀ > d`): the ladder state `K` has no on-chain predecessor (`P⋆` moves `j → 2j`, `j → j−1`, `s_f → k ≤ d`), so invariance forces `λ^K(K) = 0`, contradicting on-chain positivity, and no `Stat S (some K)` exists. The even case is the content, and it is non-vacuous (`main_truncation_bhat`) |

## SCOPE (disclosed)

* **Not this file:** item (1)'s recurrence labels, item (2)'s uniqueness of `λ`, and every other
  clause of items (1)–(4); those stand in `Main.lean` as disclosed there.
* **"Depends only on" is a congruence, not a binder order.** For `c₇` the clause is certified by
  `Decay.c7Of_congr` (equal constants from equal block data, `D` fixed by `c`, `d` fixed); the
  statement `main_rate_explicit` names `c₇` as `c7Of (Decay.ofC hc0 hc1) S.d (λ restricted to
  the ladder)`. `Decay` has data `c` and `p`, and `p` is the Cramér root of `c`, unique at
  `0 < c < 1` (`lem:doubling_cramer_root`), so a function of `D` is a function of `c`. For `c₈`,
  `K₀` the witnesses are formulas in `(D, d)` and `(D, d, j̄)` and `main_truncation`
  (`TruncationBhat.lean`) additionally enforces the clause by binder order.
* **The block is `1 ≤ j < 2m₀`**, `λ_1, …, λ_{2m₀−1}`: the index `2m₀` the paper's statement
  names is not read. This is what the paper's own proof delivers (its `c₁`, `c₂` are extrema over
  `1 ≤ j < 2m₀`), and dependence on fewer data implies the stated clause.
* **`c₄` and `c₅` are the library's effective constants**, `c₄ = 16cτ` (`R0Bound.lean`) and
  `c₅ = 6/γ²`, as in `Decay.decay_two_sided_explicit` and `TruncationBhat.lean`; `m₀ = D.m0 d`
  is built from them.
* **Norms are in the mass layer.** `√(Stat.mass 2 f)` is `‖f‖_{L²(λ)}`; the bridge to Mathlib's
  `Lp ℝ 2 L.mu` is `Stat.norm_sq_eq_mass_of_ae` (`RayleighBridge.lean`), not restated here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology MeasureTheory

variable {S : Setting}

/-! ### Item (5): `K + 2` states -/

/-- The chain set of the truncation at `K` has `K + 2` elements: the `K + 1` ladder states
`0, …, K` and the sink. -/
theorem card_chainFinset (K : ℕ) : (chainFinset K).card = K + 2 := by
  have hinj : Function.Injective St.lad := fun _ _ h => St.lad.inj h
  have hsink : (St.sink : St) ∉ (Finset.range (K + 1)).image St.lad := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro j _ h
    cases h
  rw [chainFinset, Finset.card_insert_of_notMem hsink, Finset.card_image_of_injective _ hinj,
    Finset.card_range]

/-- **`theo:doubling_main`(5), "on `K + 2` states".** The on-chain states of the truncation at
`K` number exactly `K + 2`. -/
theorem main_truncation_states (K : ℕ) : Nat.card {x : St // OnChain (some K) x} = K + 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => (mem_chainFinset (K := K) (x := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, card_chainFinset]

/-! ### Item (3): the constants `c₁`, `c₂`, `c₇` as formulas -/

namespace Decay

variable (D : Decay)

/-- The initial block `1 ≤ j < 2m₀` is non-empty, `m₀ > d ≥ 0`. -/
theorem block_nonempty (d : ℕ) : (Finset.Ico 1 (2 * D.m0 d)).Nonempty :=
  ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by have := D.lt_m0 d; omega⟩⟩

/-- **`c₁` of `theo:doubling_decay`(2), written out**: `(min_{1≤j<2m₀} λ_j j^{p_*}) e^{−c₅c₄/m₀}`,
`c₄ = 16cτ`. -/
noncomputable def c1Of (d : ℕ) (lam : ℕ → ℝ) : ℝ :=
  (Finset.Ico 1 (2 * D.m0 d)).inf' (D.block_nonempty d) (D.uu lam)
    * Real.exp (-(D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ)))

/-- **`c₂` of `theo:doubling_decay`(2), written out**: `(max_{1≤j<2m₀} λ_j j^{p_*}) e^{c₅c₄/m₀}`. -/
noncomputable def c2Of (d : ℕ) (lam : ℕ → ℝ) : ℝ :=
  (Finset.Ico 1 (2 * D.m0 d)).sup' (D.block_nonempty d) (D.uu lam)
    * Real.exp (D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ))

/-- **`c₇ := ½ √(c₁/(c₂(p_*−1)))`** of `cor:doubling_family` and `theo:doubling_main`(3). -/
noncomputable def c7Of (d : ℕ) (lam : ℕ → ℝ) : ℝ :=
  1 / 2 * Real.sqrt (D.c1Of d lam / (D.c2Of d lam * (D.p - 1)))

variable {D}

theorem c1Of_congr {d : ℕ} {lam lam' : ℕ → ℝ}
    (h : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 d → lam j = lam' j) : D.c1Of d lam = D.c1Of d lam' := by
  unfold c1Of
  congr 1
  refine Finset.inf'_congr _ rfl fun j hj => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
  rw [uu, uu, h j h1 h2]

theorem c2Of_congr {d : ℕ} {lam lam' : ℕ → ℝ}
    (h : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 d → lam j = lam' j) : D.c2Of d lam = D.c2Of d lam' := by
  unfold c2Of
  congr 1
  refine Finset.sup'_congr _ rfl fun j hj => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
  rw [uu, uu, h j h1 h2]

/-- **`theo:doubling_main`(3), "`c₇` depends only on `c`, `d` and `λ_1, …, λ_{2m₀}`".** Two
profiles agreeing on the initial block `1 ≤ j < 2m₀` have the same `c₇`. -/
theorem c7Of_congr {d : ℕ} {lam lam' : ℕ → ℝ}
    (h : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 d → lam j = lam' j) : D.c7Of d lam = D.c7Of d lam' := by
  rw [c7Of, c7Of, c1Of_congr h, c2Of_congr h]

/-- The exponent `c₅c₄/m₀` is non-negative. -/
theorem expo_nonneg (d : ℕ) : 0 ≤ D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ) := by
  have := D.c5_pos
  have := D.c_pos
  have := D.tau_pos
  positivity

theorem c1Of_pos {d : ℕ} {lam : ℕ → ℝ} (hpos : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 d → 0 < lam j) :
    0 < D.c1Of d lam := by
  refine mul_pos ((Finset.lt_inf'_iff _).mpr fun j hj => ?_) (Real.exp_pos _)
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast h1
  exact mul_pos (hpos j h1 h2) (Real.rpow_pos_of_pos hj0 _)

theorem c1Of_le_c2Of {d : ℕ} {lam : ℕ → ℝ}
    (hpos : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 d → 0 < lam j) : D.c1Of d lam ≤ D.c2Of d lam := by
  have h1 : 1 ∈ Finset.Ico 1 (2 * D.m0 d) :=
    Finset.mem_Ico.mpr ⟨le_rfl, by have := D.lt_m0 d; omega⟩
  have hab : (Finset.Ico 1 (2 * D.m0 d)).inf' (D.block_nonempty d) (D.uu lam)
      ≤ (Finset.Ico 1 (2 * D.m0 d)).sup' (D.block_nonempty d) (D.uu lam) :=
    le_trans (Finset.inf'_le _ h1) (Finset.le_sup' _ h1)
  have ha : 0 < (Finset.Ico 1 (2 * D.m0 d)).inf' (D.block_nonempty d) (D.uu lam) :=
    lt_of_lt_of_le (mul_pos (c1Of_pos hpos) (Real.exp_pos
      (D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ)))) (le_of_eq (by
        rw [c1Of, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]))
  have hz := D.expo_nonneg d
  have he : Real.exp (-(D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ)))
      ≤ Real.exp (D.c5 * (16 * D.c * D.tau) / (D.m0 d : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [c1Of, c2Of]
  exact mul_le_mul hab he (Real.exp_pos _).le (ha.le.trans hab)

theorem c7Of_pos {d : ℕ} {lam : ℕ → ℝ} (hpos : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 d → 0 < lam j) :
    0 < D.c7Of d lam := by
  have h1 := c1Of_pos hpos
  have h2 := lt_of_lt_of_le h1 (c1Of_le_c2Of hpos)
  have hp : 0 < D.p - 1 := by have := D.p_gt_one; linarith
  rw [c7Of]
  have : 0 < Real.sqrt (D.c1Of d lam / (D.c2Of d lam * (D.p - 1))) :=
    Real.sqrt_pos.mpr (div_pos h1 (mul_pos h2 hp))
  positivity

/-- `c₇² = c₁/(4c₂(p_*−1))`. -/
theorem c7Of_sq {d : ℕ} {lam : ℕ → ℝ} (hpos : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 d → 0 < lam j) :
    D.c7Of d lam ^ 2 = D.c1Of d lam / (4 * D.c2Of d lam * (D.p - 1)) := by
  have h1 := c1Of_pos hpos
  have h2 := lt_of_lt_of_le h1 (c1Of_le_c2Of hpos)
  have hp : 0 < D.p - 1 := by have := D.p_gt_one; linarith
  rw [c7Of, mul_pow, Real.sq_sqrt (div_pos h1 (mul_pos h2 hp)).le]
  field_simp
  ring

/-- **`eq:doubling_decay` at `c₁ = c1Of`, `c₂ = c2Of`.** -/
theorem decay_c1Of_c2Of {d : ℕ} {lam : ℕ → ℝ} (h : D.CutBal d lam ⊤)
    (hpos : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 d → 0 < lam j) :
    ∀ j : ℕ, 1 ≤ j →
      D.c1Of d lam * (j : ℝ) ^ (-D.p) ≤ lam j ∧ lam j ≤ D.c2Of d lam * (j : ℝ) ^ (-D.p) := by
  have ha : 0 ≤ (Finset.Ico 1 (2 * D.m0 d)).inf' (D.block_nonempty d) (D.uu lam) := by
    refine le_of_lt ((Finset.lt_inf'_iff _).mpr fun j hj => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast h1
    exact mul_pos (hpos j h1 h2) (Real.rpow_pos_of_pos hj0 _)
  exact D.decay_two_sided_explicit h (le_refl (D.m0 d)) ha fun j h1 h2 =>
    ⟨Finset.inf'_le _ (Finset.mem_Ico.mpr ⟨h1, h2⟩),
      Finset.le_sup' (D.uu lam) (Finset.mem_Ico.mpr ⟨h1, h2⟩)⟩

end Decay

/-! ### Item (3): the `c₇ √m` clause at `c₇ = c7Of` -/

namespace Stat

/-- **`eq:doubling_step1`'s consequence**: on the loop closure the defect of `f_m` has positive
`L²(λ)` mass at every cut `m > d` — it is at least `λ_m (1 − ε(m))²`. -/
theorem mass_defect_centredTail_pos (L : Stat S none) {m : ℕ} (hdm : S.d < m) :
    0 < L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x) := by
  have hm : 1 ≤ m := by have := S.d_pos; omega
  rw [L.mass_centredTail_defect hdm trivial, mass_cutFn L hm (by norm_num)]
  have h1 : 0 < L.lam (.lad m) * (1 - S.eps m) ^ (2 : ℝ) :=
    mul_pos (L.pos trivial) (Real.rpow_pos_of_pos (S.one_sub_eps_pos hm) _)
  have h2 : 0 ≤ ∑ y ∈ window m, L.lam (.lad y) * S.eps y ^ (2 : ℝ) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (L.nonneg _) (by rw [Real.rpow_two]; positivity)
  linarith

/-- **`theo:doubling_main`(3), the `c₇√m` clause, with its constants written out.** For any
`Decay` `D` carrying the family and any invariant probability `λ` of the loop closure, with
`λ_j := λ(j)` on the ladder: `0 < c₁ ≤ c₂` for `c₁ = c1Of`, `c₂ = c2Of`, the two-sided decay holds
with them, `c₇ = c7Of > 0`, and there is `m₂ > d` such that for every `m ≥ m₂`
`c₁ m ‖(Id−P⋆)f_m‖² ≤ 4c₂(p_*−1) ‖f_m‖²`, `c₇ √m ‖(Id−P⋆)f_m‖ ≤ ‖f_m‖`, the denominator is
positive, and `c₇ √m ≤ ‖f_m‖ / ‖(Id−P⋆)f_m‖` (`eq:doubling_explicit`). -/
theorem rate_explicit (D : Decay) (hDeps : ∀ j, S.eps j = D.eps j) (L : Stat S none) :
    0 < D.c1Of S.d (fun j => L.lam (.lad j)) ∧
      D.c1Of S.d (fun j => L.lam (.lad j)) ≤ D.c2Of S.d (fun j => L.lam (.lad j)) ∧
      (∀ j : ℕ, 1 ≤ j →
        D.c1Of S.d (fun j => L.lam (.lad j)) * (j : ℝ) ^ (-D.p) ≤ L.lam (.lad j) ∧
          L.lam (.lad j) ≤ D.c2Of S.d (fun j => L.lam (.lad j)) * (j : ℝ) ^ (-D.p)) ∧
      0 < D.c7Of S.d (fun j => L.lam (.lad j)) ∧
      ∃ m₂ : ℕ, S.d < m₂ ∧ ∀ m : ℕ, m₂ ≤ m →
        D.c1Of S.d (fun j => L.lam (.lad j)) * (m : ℝ)
            * L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)
          ≤ 4 * D.c2Of S.d (fun j => L.lam (.lad j)) * (D.p - 1) * L.mass 2 (L.centredTail m) ∧
        D.c7Of S.d (fun j => L.lam (.lad j)) * Real.sqrt (m : ℝ)
            * Real.sqrt (L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x))
          ≤ Real.sqrt (L.mass 2 (L.centredTail m)) ∧
        0 < L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x) ∧
        D.c7Of S.d (fun j => L.lam (.lad j)) * Real.sqrt (m : ℝ)
          ≤ Real.sqrt (L.mass 2 (L.centredTail m))
            / Real.sqrt
                (L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)) := by
  set lam : ℕ → ℝ := fun j => L.lam (.lad j) with hlam
  have hcut : D.CutBal S.d lam ⊤ := D.cutBal_of_setting hDeps (cutBalanceSeq_of_stat L)
  have hblk : ∀ j : ℕ, 1 ≤ j → j < 2 * D.m0 S.d → 0 < lam j := fun _ _ _ => L.pos trivial
  have hc1 : 0 < D.c1Of S.d lam := Decay.c1Of_pos hblk
  have hc12 : D.c1Of S.d lam ≤ D.c2Of S.d lam := Decay.c1Of_le_c2Of hblk
  have hbd := Decay.decay_c1Of_c2Of hcut hblk
  have hc7 : 0 < D.c7Of S.d lam := Decay.c7Of_pos hblk
  have hc7sq := Decay.c7Of_sq hblk
  have hc2 : 0 < D.c2Of S.d lam := lt_of_lt_of_le hc1 hc12
  have hp : 0 < D.p - 1 := by have := D.p_gt_one; linarith
  obtain ⟨m₂, hm₂, hrate⟩ :=
    L.exists_rayleigh_family D hc1 (fun j hj => (hbd j hj).1) (fun j hj => (hbd j hj).2)
  refine ⟨hc1, hc12, hbd, hc7, m₂, hm₂, fun m hm => ?_⟩
  set A : ℝ := L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x) with hA
  set B : ℝ := L.mass 2 (L.centredTail m) with hB
  have hsq := hrate m hm
  have hApos : 0 < A := L.mass_defect_centredTail_pos (lt_of_lt_of_le hm₂ hm)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- `(c₇ √m √A)² = c₁ m A / (4c₂(p−1)) ≤ B`
  have hden : 0 < 4 * D.c2Of S.d lam * (D.p - 1) := by positivity
  have hkey : (D.c7Of S.d lam * Real.sqrt (m : ℝ) * Real.sqrt A) ^ 2 ≤ B := by
    rw [mul_pow, mul_pow, hc7sq, Real.sq_sqrt hm0, Real.sq_sqrt hApos.le,
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hden]
    linarith
  have hnorm : D.c7Of S.d lam * Real.sqrt (m : ℝ) * Real.sqrt A ≤ Real.sqrt B :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt hkey)
  refine ⟨hsq, hnorm, hApos, ?_⟩
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hApos)]
  exact hnorm

end Stat

/-- **`theo:doubling_main`(3), the `c₇√m` clause, with `c₇` named.** At `s = 1`, `0 < c < 1`,
with `p_* = (Decay.ofC hc0 hc1).p` the Cramér root and `λ` an invariant probability of the loop
closure: `c₇ := c7Of (Decay.ofC hc0 hc1) d (λ on the ladder) = ½√(c₁/(c₂(p_*−1)))` is positive
and there is `m₂ > d` with `‖f_m‖_{L²(λ)} ≥ c₇ √m ‖(Id−P⋆)f_m‖_{L²(λ)}` for every `m ≥ m₂`,
in norm form and in the paper's ratio form with a positive denominator. Its dependence on `c`,
`d` and `λ_1, …, λ_{2m₀−1}` alone is `Decay.c7Of_congr` / `main_c7_congr`. -/
theorem main_rate_explicit {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) (L : Stat S none) :
    psi c (Decay.ofC hc0 hc1).p = 0 ∧ 1 < (Decay.ofC hc0 hc1).p ∧
      0 < (Decay.ofC hc0 hc1).c7Of S.d (fun j => L.lam (.lad j)) ∧
      ∃ m₂ : ℕ, S.d < m₂ ∧ ∀ m : ℕ, m₂ ≤ m →
        (Decay.ofC hc0 hc1).c7Of S.d (fun j => L.lam (.lad j)) * Real.sqrt (m : ℝ)
            * Real.sqrt (L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x))
          ≤ Real.sqrt (L.mass 2 (L.centredTail m)) ∧
        0 < L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x) ∧
        (Decay.ofC hc0 hc1).c7Of S.d (fun j => L.lam (.lad j)) * Real.sqrt (m : ℝ)
          ≤ Real.sqrt (L.mass 2 (L.centredTail m))
            / Real.sqrt
                (L.mass 2 (fun x => L.centredTail m x - pstar S none (L.centredTail m) x)) := by
  obtain ⟨-, -, -, hc7, m₂, hm₂, hrate⟩ :=
    Stat.rate_explicit (Decay.ofC hc0 hc1) (eps_eq_decay_eps heps _ rfl) L
  exact ⟨(Decay.ofC hc0 hc1).root, (Decay.ofC hc0 hc1).p_gt_one, hc7, m₂, hm₂,
    fun m hm => (hrate m hm).2⟩

/-- **`theo:doubling_main`(3), "`c₇` depends only on `c`, `d` and `λ_1, …, λ_{2m₀}`", across
settings.** Two invariant probabilities of loop closures with the same `c` and `d` whose ladder
masses agree on `1 ≤ j < 2m₀` have the same `c₇`. -/
theorem main_c7_congr {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {S' : Setting} (hd : S.d = S'.d)
    (L : Stat S none) (L' : Stat S' none)
    (hagree : ∀ j : ℕ, 1 ≤ j → j < 2 * (Decay.ofC hc0 hc1).m0 S.d →
      L.lam (.lad j) = L'.lam (.lad j)) :
    (Decay.ofC hc0 hc1).c7Of S.d (fun j => L.lam (.lad j))
      = (Decay.ofC hc0 hc1).c7Of S'.d (fun j => L'.lam (.lad j)) := by
  rw [← hd]
  exact Decay.c7Of_congr hagree

/-! ### Item (5), in one statement -/

/-- **`theo:doubling_main`(5), with `c₈` and `K₀` named.** At `s = 1`, `0 < c < 1`, with
`D = Decay.ofC hc0 hc1`: for every even `K ≥ d` the truncation has `K + 2` on-chain states, is
irreducible, carries exactly one invariant probability `λ^K`, and at every such `λ^K` the paper's
operator `S = (Id − P⋆ + Π)^{-1} − Π` satisfies `eq:doubling_resolvent`, so
`B̂_K = ‖S‖ < +∞`; `K₀ := D.K0Of d = 8m₀ + 2 ≥ d` and `c₈ := D.c8Of d j̄ > 0`, formulas in `c`,
`d` and `j̄`, give `B̂_K ≥ c₈ √K` for every `K ≥ K₀`. That clause is stated without evenness but
holds vacuously at odd `K > d`, where no on-chain-positive invariant probability exists (`λ^K(K)`
would receive no mass); the even case is the content, and is non-vacuous. -/
theorem main_truncation_explicit {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j, S.eps j = epsCS c 1 j) :
    (∀ K : ℕ, Even K → ∀ hdK : S.d ≤ K,
        Nat.card {x : St // OnChain (some K) x} = K + 2 ∧
        (∀ x y : St, OnChain (some K) y → Reach S (some K) x y) ∧
        Nonempty (Stat S (some K)) ∧
        (∀ L L' : Stat S (some K), L.lam = L'.lam) ∧
        ∀ L : Stat S (some K),
          (1 - L.pstarL2 (rowOnChain_some hdK)) * L.diffOpK hdK = 1 - L.piL2 ∧
          L.diffOpK hdK * (1 - L.pstarL2 (rowOnChain_some hdK)) = 1 - L.piL2 ∧
          L.piL2 * L.diffOpK hdK = 0 ∧ L.diffOpK hdK * L.piL2 = 0 ∧
          L.bhatK hdK = ‖L.diffOpK hdK‖) ∧
      S.d ≤ (Decay.ofC hc0 hc1).K0Of S.d ∧ 0 < (Decay.ofC hc0 hc1).c8Of S.d S.jbar ∧
      ∀ K : ℕ, (Decay.ofC hc0 hc1).K0Of S.d ≤ K → ∀ (hdK : S.d ≤ K) (L : Stat S (some K)),
        (Decay.ofC hc0 hc1).c8Of S.d S.jbar * Real.sqrt (K : ℝ) ≤ L.bhatK hdK := by
  obtain ⟨-, hK0, -, -, hc8, hsqrt⟩ :=
    truncation_explicit (Decay.ofC hc0 hc1) (eps_eq_decay_eps heps _ rfl)
  refine ⟨fun K hK hdK => ?_, hK0, hc8, hsqrt⟩
  obtain ⟨hne, huniq, -⟩ := main_truncation_bhat hK hdK
  refine ⟨main_truncation_states K, fun x y hy => (main_truncation_irreducible hK hdK
    hne.some.toPreStat).1 x y hy, hne, huniq, fun L => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := L.diffOpK_resolvent hdK
  exact ⟨h1, h2, h3, h4, rfl⟩

end GFNBounds.Doubling
