import GFNBounds.Doubling.DecayNotation

/-!
# The descent chain, as a recursion

**`lem:doubling_descent`** — `app_doubling.tex:965–1024`
and **`theo:doubling_decay`** — `app_doubling.tex:1155–1228`.

> (descent) with `(Y_n)` the Markov chain on the integers `≥ ℓ` with
> `P(Y_{n+1}=j | Y_n=y) = w_y(j)/R_0(y)` on `W(y)` when `y ≥ 2ℓ` and `Y_{n+1}=Y_n` when `y < 2ℓ`,
> and `N_ℓ := inf{n : Y_n < 2ℓ}`: (1) `⌈Y_n/2⌉ ≤ Y_{n+1} ≤ Y_n − 1` and `N_ℓ ≤ m`;
> (2) `Y_{N_ℓ} ∈ [ℓ,2ℓ)` almost surely; (3) with `Z_ℓ := ∏_{n<N_ℓ} R_0(Y_n)`,
> `u_m = E(Z_ℓ u_{Y_{N_ℓ}} | Y_0 = m)`.
>
> (decay, item 1) `e^{−c₅c₄/ℓ} min_{ℓ≤j<2ℓ} u_j ≤ u_m ≤ e^{c₅c₄/ℓ} max_{ℓ≤j<2ℓ} u_j`;
> (item 2) there are `0 < c₁ ≤ c₂` with `c₁ j^{−p_*} ≤ λ_j ≤ c₂ j^{−p_*}` for every `j ≥ 1`.

## The modelling decision

**The chain is not built.** The three items of `lem:doubling_descent` are, respectively, the
recursion's well-foundedness, the range of its base case, and its fixed point; and the quantity
`E(Z_ℓ u_{Y_{N_ℓ}})` — an expectation against the *unnormalized* weights times the product of the
normalizations — is exactly the unnormalized transform

  `descW g m = if m < 2ℓ then g m else Σ_{j ∈ W(m)} w_m(j) · descW g j`,

because the `R_0(y)` of the transition law and the `R_0(y)` of the product cancel term by term.
So `descW` is defined by well-founded recursion on `m` (every `j ∈ W(m)` has `j < m`, which is
item (1)), its base case is reached with `ℓ ≤ m < 2ℓ` (item (2), `descW_between`), and
`eq:doubling_pathid` is `descW_uu` — proved by strong induction, exactly as the paper's is.

`E(Z_ℓ | Y_0 = m)` is `descW D ℓ 1 m`, written `descOne`. What `lem:doubling_product` supplies is
`e^{−c₅c₄/ℓ} ≤ descOne m ≤ e^{c₅c₄/ℓ}`, and that is the **one** input `theo:doubling_decay` takes
as a hypothesis here; see SCOPE.

## SCOPE (disclosed)

* `lem:doubling_expansion`, `lem:doubling_escape` and `lem:doubling_product` are **not** proved.
  `theo:doubling_decay` therefore carries the two-sided bound on `descOne` as a hypothesis
  (`hlo`, `hhi`), which is precisely `eq:doubling_product` at `b := R_0 − 1`, `H := c₄`. Nothing
  else of the decay block is assumed. The constants `c₄, ℓ₁, γ, c₅, ℓ₂, m₀` are consequently not
  named here: the level `ℓ` and the two bounds are parameters.
* The paper's `R_0(y) > 0` (needed for the transition law to be a probability) is not needed by
  the recursion, which never divides; `w_m ≥ 0` is what `descW_between` uses.
* `Y_{N_ℓ} ∈ [ℓ, 2ℓ)` appears as the hypothesis pattern `∀ j, ℓ ≤ j → j < 2ℓ → …` of
  `descW_between`, which is where the paper's item (2) is consumed.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ℓ ≥ ℓ₁ > d` | ✓ carried as `d < 2ℓ` and `1 ≤ ℓ`, which is all the argument uses |
| `M₁ ∈ {2ℓ,…} ∪ {∞}` and cut balance up to `M₁` | ✓ carried (`Decay.CutBal d lam M₁`) |
| `2ℓ ≤ m ≤ M₁` | ✓ carried |
| `(λ_j)` positive | ✓ carried where the extrema must be positive |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

/-- **The descent transform.** `descW D ℓ g m = E(Z_ℓ · g(Y_{N_ℓ}) | Y_0 = m)`, written as an
unnormalized recursion: the `R_0` of the transition law and the `R_0` of the weight `Z_ℓ` cancel.

Well-founded because every `j ∈ W(m)` has `j < m` — which is `lem:doubling_descent`(1). -/
noncomputable def descW (D : Decay) (ℓ : ℕ) (g : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < 2 * ℓ then g m
  else ∑ j ∈ (window m).attach, D.wm m j.1 * descW D ℓ g j.1
termination_by m
decreasing_by exact window_lt j.2

variable (D : Decay)

theorem descW_of_lt {ℓ : ℕ} (g : ℕ → ℝ) {m : ℕ} (h : m < 2 * ℓ) : D.descW ℓ g m = g m := by
  rw [descW, if_pos h]

theorem descW_of_ge {ℓ : ℕ} (g : ℕ → ℝ) {m : ℕ} (h : ¬ m < 2 * ℓ) :
    D.descW ℓ g m = ∑ j ∈ window m, D.wm m j * D.descW ℓ g j := by
  rw [descW, if_neg h]
  exact Finset.sum_attach (window m) fun j => D.wm m j * D.descW ℓ g j

/-- `E(Z_ℓ | Y_0 = m)`, the expected weight of a descent. -/
noncomputable def descOne (ℓ m : ℕ) : ℝ := D.descW ℓ (fun _ => 1) m

theorem descOne_of_lt {ℓ m : ℕ} (h : m < 2 * ℓ) : D.descOne ℓ m = 1 :=
  D.descW_of_lt _ h

theorem descOne_of_ge {ℓ m : ℕ} (h : ¬ m < 2 * ℓ) :
    D.descOne ℓ m = ∑ j ∈ window m, D.wm m j * D.descOne ℓ j :=
  D.descW_of_ge _ h

/-- Every index of the window of an `m ≥ 2ℓ` is at least `ℓ`: this is `⌈m/2⌉ ≥ ℓ`, and it is where
`lem:doubling_descent`(2) — the descent lands in `[ℓ,2ℓ)` — enters. -/
theorem le_of_mem_window_of_ge {ℓ m j : ℕ} (hm : 2 * ℓ ≤ m) (hj : j ∈ window m) : ℓ ≤ j := by
  rw [mem_window] at hj
  omega

/-- **`eq:doubling_pathid`.** The rescaled profile is the fixed point of the descent transform:
`u_m = E(Z_ℓ u_{Y_{N_ℓ}} | Y_0 = m)`. Proved by strong induction on `m`, as the paper's is. -/
theorem descW_uu {ℓ d : ℕ} {lam : ℕ → ℝ} {M₁ : ℕ∞} (h : D.CutBal d lam M₁)
    (hℓ : d < 2 * ℓ) :
    ∀ m : ℕ, (m : ℕ∞) ≤ M₁ → D.uu lam m = D.descW ℓ (D.uu lam) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hM
      by_cases hlt : m < 2 * ℓ
      · rw [D.descW_of_lt _ hlt]
      · rw [D.descW_of_ge _ hlt]
        have hm1 : 1 ≤ m := by omega
        have hdm : d < m := by omega
        rw [D.uavg_of_cutBal h hm1 hdm hM]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjm : j < m := window_lt hj
        have hjM : (j : ℕ∞) ≤ M₁ :=
          le_trans (by exact_mod_cast hjm.le : (j : ℕ∞) ≤ (m : ℕ∞)) hM
        rw [← ih j hjm hjM]

/-- **The sandwich.** A function bounded between `a` and `b` on the base block `[ℓ,2ℓ)` has its
descent transform bounded between `a·E(Z_ℓ)` and `b·E(Z_ℓ)`.

This is where items (1) and (2) of `lem:doubling_descent` are consumed: the recursion terminates
(item 1) and its base case is reached inside `[ℓ,2ℓ)` (item 2). -/
theorem descW_between {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) {g : ℕ → ℝ} {a b : ℝ}
    (hab : ∀ j, ℓ ≤ j → j < 2 * ℓ → a ≤ g j ∧ g j ≤ b) :
    ∀ m : ℕ, ℓ ≤ m →
      a * D.descOne ℓ m ≤ D.descW ℓ g m ∧ D.descW ℓ g m ≤ b * D.descOne ℓ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hlt : m < 2 * ℓ
    · rw [D.descW_of_lt _ hlt, D.descOne_of_lt hlt]
      obtain ⟨h1, h2⟩ := hab m hm hlt
      exact ⟨by linarith, by linarith⟩
    · have hge : 2 * ℓ ≤ m := by omega
      have hm1 : 1 ≤ m := by omega
      rw [D.descW_of_ge _ hlt, D.descOne_of_ge hlt, Finset.mul_sum, Finset.mul_sum]
      constructor
      · refine Finset.sum_le_sum fun j hj => ?_
        have hjℓ : ℓ ≤ j := le_of_mem_window_of_ge hge hj
        have hj1 : 1 ≤ j := le_trans hℓ1 hjℓ
        have hstep := (ih j (window_lt hj) hjℓ).1
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left hstep (D.wm_nonneg hm1 hj1)
      · refine Finset.sum_le_sum fun j hj => ?_
        have hjℓ : ℓ ≤ j := le_of_mem_window_of_ge hge hj
        have hj1 : 1 ≤ j := le_trans hℓ1 hjℓ
        have hstep := (ih j (window_lt hj) hjℓ).2
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left hstep (D.wm_nonneg hm1 hj1)

/-! ## `theo:doubling_decay` -/

/-- **`eq:doubling_block`.** One block of the profile bounds every index above it, within the
two-sided bound on `E(Z_ℓ)` that `lem:doubling_product` supplies.

`hlo` and `hhi` are `eq:doubling_product` at `b := R_0 − 1`, `H := c₄`; they are the block's only
unproved input, and are hypotheses here rather than hidden. -/
theorem decay_block {ℓ d : ℕ} {lam : ℕ → ℝ} {M₁ : ℕ∞} (h : D.CutBal d lam M₁)
    (hℓ : d < 2 * ℓ) (hℓ1 : 1 ≤ ℓ) {Z₁ Z₂ : ℝ}
    (hlo : ∀ y : ℕ, ℓ ≤ y → Z₁ ≤ D.descOne ℓ y) (hhi : ∀ y : ℕ, ℓ ≤ y → D.descOne ℓ y ≤ Z₂)
    {a b : ℝ} (ha : 0 ≤ a)
    (hab : ∀ j, ℓ ≤ j → j < 2 * ℓ → a ≤ D.uu lam j ∧ D.uu lam j ≤ b)
    {m : ℕ} (hm : ℓ ≤ m) (hM : (m : ℕ∞) ≤ M₁) :
    a * Z₁ ≤ D.uu lam m ∧ D.uu lam m ≤ b * Z₂ := by
  have hb : 0 ≤ b := by
    have := hab ℓ le_rfl (by omega)
    linarith [this.1, this.2]
  obtain ⟨hlow, hhigh⟩ := D.descW_between hℓ1 hab m hm
  rw [← D.descW_uu h hℓ m hM] at hlow hhigh
  exact ⟨le_trans (mul_le_mul_of_nonneg_left (hlo m hm) ha) hlow,
    le_trans hhigh (mul_le_mul_of_nonneg_left (hhi m hm) hb)⟩

/-- **`eq:doubling_decay`, in the `u` variable.** The rescaled profile is bounded above and below
by positive constants, on the whole ladder. -/
theorem uu_bounded {ℓ d : ℕ} {lam : ℕ → ℝ} (h : D.CutBal d lam ⊤)
    (hpos : ∀ j, 1 ≤ j → 0 < lam j) (hℓ : d < 2 * ℓ) (hℓ1 : 1 ≤ ℓ) {Z₁ Z₂ : ℝ}
    (hZ1 : 0 < Z₁) (hZ1' : Z₁ ≤ 1) (hZ2 : 1 ≤ Z₂)
    (hlo : ∀ y : ℕ, ℓ ≤ y → Z₁ ≤ D.descOne ℓ y) (hhi : ∀ y : ℕ, ℓ ≤ y → D.descOne ℓ y ≤ Z₂) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ j : ℕ, 1 ≤ j → c₁ ≤ D.uu lam j ∧ D.uu lam j ≤ c₂ := by
  classical
  have hne : (Finset.Ico 1 (2 * ℓ)).Nonempty := ⟨1, by rw [Finset.mem_Ico]; omega⟩
  set a : ℝ := (Finset.Ico 1 (2 * ℓ)).inf' hne (D.uu lam) with ha'
  set b : ℝ := (Finset.Ico 1 (2 * ℓ)).sup' hne (D.uu lam) with hb'
  have huu_pos : ∀ j : ℕ, 1 ≤ j → 0 < D.uu lam j := by
    intro j hj
    have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    exact mul_pos (hpos j hj) (rpow_pos_of_pos hj' D.p)
  have hapos : 0 < a := by
    rw [ha']
    refine (Finset.lt_inf'_iff hne).mpr fun i hi => ?_
    exact huu_pos i (Finset.mem_Ico.mp hi).1
  have hmem : ∀ j : ℕ, 1 ≤ j → j < 2 * ℓ → a ≤ D.uu lam j ∧ D.uu lam j ≤ b := by
    intro j hj1 hj2
    have hin : j ∈ Finset.Ico 1 (2 * ℓ) := by rw [Finset.mem_Ico]; omega
    exact ⟨Finset.inf'_le _ hin, Finset.le_sup' _ hin⟩
  have hab : ∀ j, ℓ ≤ j → j < 2 * ℓ → a ≤ D.uu lam j ∧ D.uu lam j ≤ b :=
    fun j h1 h2 => hmem j (le_trans hℓ1 h1) h2
  refine ⟨a * Z₁, b * Z₂, by positivity, ?_, ?_⟩
  · have hble : a ≤ b := (hmem ℓ hℓ1 (by omega)).1.trans (hmem ℓ hℓ1 (by omega)).2
    have hbpos : 0 < b := lt_of_lt_of_le hapos hble
    nlinarith [hZ1', hZ2, hapos, hbpos, hble, hZ1]
  · intro j hj
    by_cases hjs : j < 2 * ℓ
    · obtain ⟨h1, h2⟩ := hmem j hj hjs
      have hbpos : 0 < b := lt_of_lt_of_le hapos (h1.trans h2)
      constructor
      · nlinarith [hZ1', hapos]
      · nlinarith [hZ2, hbpos]
    · exact D.decay_block h hℓ hℓ1 hlo hhi hapos.le hab (by omega : ℓ ≤ j) le_top

/-- **`eq:doubling_decay`.** `c₁ j^{−p_*} ≤ λ_j ≤ c₂ j^{−p_*}` for every `j ≥ 1`. -/
theorem decay_two_sided {ℓ d : ℕ} {lam : ℕ → ℝ} (h : D.CutBal d lam ⊤)
    (hpos : ∀ j, 1 ≤ j → 0 < lam j) (hℓ : d < 2 * ℓ) (hℓ1 : 1 ≤ ℓ) {Z₁ Z₂ : ℝ}
    (hZ1 : 0 < Z₁) (hZ1' : Z₁ ≤ 1) (hZ2 : 1 ≤ Z₂)
    (hlo : ∀ y : ℕ, ℓ ≤ y → Z₁ ≤ D.descOne ℓ y) (hhi : ∀ y : ℕ, ℓ ≤ y → D.descOne ℓ y ≤ Z₂) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ j : ℕ, 1 ≤ j →
        c₁ * (j : ℝ) ^ (-D.p) ≤ lam j ∧ lam j ≤ c₂ * (j : ℝ) ^ (-D.p) := by
  obtain ⟨c₁, c₂, hc1, hc12, hbd⟩ := D.uu_bounded h hpos hℓ hℓ1 hZ1 hZ1' hZ2 hlo hhi
  refine ⟨c₁, c₂, hc1, hc12, fun j hj => ?_⟩
  have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hjp : (0 : ℝ) < (j : ℝ) ^ D.p := rpow_pos_of_pos hj' D.p
  have hneg : (j : ℝ) ^ (-D.p) = ((j : ℝ) ^ D.p)⁻¹ := by
    rw [rpow_neg hj'.le]
  obtain ⟨h1, h2⟩ := hbd j hj
  rw [uu] at h1 h2
  rw [hneg]
  constructor
  · rw [mul_inv_le_iff₀ hjp]; linarith
  · rw [le_mul_inv_iff₀ hjp]; linarith

end Decay

end GFNBounds.Doubling
