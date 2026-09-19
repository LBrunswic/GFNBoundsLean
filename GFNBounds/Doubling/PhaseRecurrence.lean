import GFNBounds.Doubling.RecurrenceClass

/-!
# The phase diagram of the family, with its recurrence classes

**`prop:doubling_phase`** — `app_doubling.tex`, label `prop:doubling_phase` ("the phase diagram
of the family") — and the table of item (1) of **`theo:doubling_main`**, with the uniqueness of
`λ` that item (2) of `theo:doubling_main` presupposes ("`λ` the invariant probability of `X`").

> Let `(c,s)` lie in the standing range and let `X` be the loop-closed backward chain. Then `X` is
> irreducible, and: (1) if `s > 1`, `X` is positive recurrent; (2) if `s < 1`, `X` is transient;
> (3) if `s = 1`, `X` is positive recurrent for `0 < c < 1`, with `E(σ | X₀ = j) = j/(1−c)` at
> every ladder state `j ≥ 1`; for every `1 ≤ c < 2`, `E(σ | X₀ = j) = +∞` at every ladder state
> `j ≥ 1` and `X` is not positive recurrent; and `X` is null recurrent for `1 ≤ c < 1/ln 2` and
> transient for `1/ln 2 < c < 2`.

The classes are those of `GFNBounds.Doubling.RecurrenceClass`, in the language of ruling
R8 (2026-09-14): a state is recurrent when the least nonnegative solution of its
return-probability recursion is `1`, transient when it is below `1`, positive recurrent when it is
recurrent and the least solution of its expected-return-time recursion is finite, null recurrent
when that least solution is infinite; the chain is in a class when every state is.

## How each step of the paper's proof is carried

| paper step | here |
|---|---|
| 1, irreducibility | `reach_all_none` (`lem:doubling_irreducible`) |
| 3, Foster for `s > 1` | ⚠ changed route: `exists_stat_of_family_gt_one` (`PhaseExists.lean`) gives an invariant probability, and **Kac's identity** (`Stat.kac_hitP`, from invariance alone) makes every state positive recurrent. Foster's criterion is not used |
| 4, transience for `s < 1` | `exists_Wpow_one_drift_nonpos` (`Lyapunov.lean`) fed to `ladder_survival_ge`, which is the transience criterion proved as a comparison with the least solution; then `transient_src_of_sv` and solidarity |
| 5, `s = 1`, `c < 1` | `exists_stat_of_family` + Kac, and `hitExp_iSup_eq` (`prop:doubling_length`) for `E(σ | X₀ = j) = j/(1−c)` |
| 6, recurrence for `c ln 2 < 1` | `exists_logHeight_drift_nonpos` fed to `ladder_recurrent`, Foster's recurrence criterion proved for the least solution by a maximum principle on a finite window; then solidarity |
| 7, `E(σ) = +∞` for `c ≥ 1` | `hitLad_unbdd`: were `E(σ | X₀ = m)` finite at one ladder state it would be finite at all (`LDom`), its supremum would solve the recursion, and `E(X_{n∧σ}) = m − (1−c)E(σ ∧ n) ≥ m` would contradict `E(X_{n∧σ}) ≤ E(σ) − E(σ ∧ n) → 0`. ⚠ changed route: no optional stopping, no strong Markov property, no excursion maximum. Not positive recurrent at `s₀` by `retT_src_succ` (`E_{s₀}τ⁺ = 2 + σ̄`), at every state by solidarity |
| 8, transience for `c ln 2 > 1` | `exists_Wpow_drift_neg` fed to the same criterion as Step 4, at `t = (c ln 2 − 1)/(2 ln 2)` |
| Levin–Peres (class properties of an irreducible chain) | `recurrent_solidarity`, `posRecurrent_solidarity`, proved from the renewal identities |

## SCOPE (disclosed)

* **The classes are defined by recursions, not by a chain** (ruling R8). What is certified is the
  paper's classification with those definitions; that the least solution of the return recursion
  is the return probability of a Markov chain on a path space is the modelling decision of
  `RecurrenceClass.lean`, as it is of `lem:doubling_supersolution`'s `E(σ ∧ n)`.
* `E(σ | X₀ = j) = +∞` is stated as `¬ BddAbove (range fun n => hitExp S none n (.lad j))`, since
  `⨆` of an unbounded family is a junk value in `ℝ`.
* **The standing range enters through the `Setting`**, exactly as in `main_phase`: the
  hypotheses are `0 < c` and `ε = ε_{c,s}`, and a `Setting` with that `ε` exists precisely on the
  standing range (`ε(1) = c 2^{-s} < 1`, and `ε` bounded forces `s ≥ 0`). The rows are inhabited:
  `Setting.ofFamily` builds one at every `(c,s)` of the standing range (`exists_family_setting`).
  The paper's `c < 2` at `s = 1` is therefore not a hypothesis here; it is implied.
* Row (d), `c = 1/ln 2`, is stated as "no state is positive recurrent", which is the paper's
  claim; null recurrence versus transience there is open in the paper and is not touched.
* Uniqueness (`main_invariant_unique`) holds for **every** `Setting` on the loop closure, not
  only for the family: it needs only irreducibility and the existence of one invariant
  probability, which makes every state recurrent.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| setting of `def:doubling_setting` | ✓ carried (`Setting`, `pstar S none`) |
| `(c,s)` in the standing range | ⚠ carried through the `Setting` (see SCOPE); `0 < c` explicit |
| `ε = ε_{c,s}` | ✓ carried (`heps`) |
| the loop closure | ✓ carried (`cap = none`) |
| Foster's criterion, the transience criterion, optional stopping, the strong Markov property | ✗ not used; each replaced by a comparison with a least solution, proved here |
| the class properties of an irreducible chain (Levin–Peres) | ✓ proved (`recurrent_solidarity`, `posRecurrent_solidarity`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting}

/-! ### The ladder chain killed at the source -/

/-- `P_j(σ > n)`: the survival weights of the ladder chain killed at `s₀`. -/
noncomputable def sv (S : Setting) (n j : ℕ) : ℝ := (ladT S)^[n] stepCost j

theorem sv_zero (j : ℕ) : sv S 0 j = stepCost j := rfl

theorem sv_succ (n j : ℕ) : sv S (n + 1) j = ladT S (sv S n) j := by
  unfold sv; rw [Function.iterate_succ_apply']

theorem sv_nonneg (n j : ℕ) : 0 ≤ sv S n j := ladT_iterate_nonneg stepCost_nonneg n j

@[simp] theorem sv_src (n : ℕ) : sv S n 0 = 0 := by
  cases n with
  | zero => rfl
  | succ n => rw [sv_succ, ladT_zero]

theorem ladT_one_succ (m : ℕ) : ladT S (fun _ => (1 : ℝ)) (m + 1) = 1 := by
  rw [ladT_succ]; ring

theorem ladT_stepCost_le (m : ℕ) : ladT S stepCost m ≤ stepCost m := by
  cases m with
  | zero => simp
  | succ j =>
      have h := ladT_mono (S := S) (f := stepCost) (g := fun _ => (1 : ℝ))
        (fun k => by cases k <;> simp) (j + 1)
      rw [ladT_one_succ] at h; simpa using h

theorem sv_le_one (n j : ℕ) : sv S n j ≤ 1 := by
  have h := ladT_iterate_mono (S := S) (f := stepCost) (g := fun _ => (1 : ℝ))
    (fun k => by cases k <;> simp) n j
  have h1 : ∀ n : ℕ, ∀ k, (ladT S)^[n] (fun _ => (1 : ℝ)) k ≤ 1 := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
        intro k
        rw [Function.iterate_succ_apply']
        cases k with
        | zero => simp
        | succ k =>
            have := ladT_mono (S := S) (f := (ladT S)^[n] (fun _ => (1 : ℝ)))
              (g := fun _ => (1 : ℝ)) ih (k + 1)
            rwa [ladT_one_succ] at this
  exact le_trans h (h1 n j)

theorem sv_anti_succ (n j : ℕ) : sv S (n + 1) j ≤ sv S n j := by
  unfold sv; rw [Function.iterate_succ_apply]
  exact ladT_iterate_mono (fun k => ladT_stepCost_le k) n j

theorem sv_anti (j : ℕ) : Antitone fun n => sv S n j :=
  antitone_nat_of_succ_le fun n => sv_anti_succ n j

/-- `ladT` passes to pointwise limits. -/
theorem tendsto_ladT {F : ℕ → ℕ → ℝ} {G : ℕ → ℝ}
    (h : ∀ k, Tendsto (fun n => F n k) atTop (𝓝 (G k))) (m : ℕ) :
    Tendsto (fun n => ladT S (F n) m) atTop (𝓝 (ladT S G m)) := by
  cases m with
  | zero => simp only [ladT_zero]; exact tendsto_const_nhds
  | succ j =>
      simp only [ladT_succ]
      exact ((h _).const_mul _).add ((h _).const_mul _)

/-- `ladT` of an affine function of `V`, at a ladder state. -/
theorem ladT_affine (a b : ℝ) (V : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ladT S (fun k => a + b * V k) m = a + b * ladT S V m := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  rw [ladT_succ, ladT_succ]; ring

/-- The probability of `j` straight decrements, `Π_{i=1}^{j} (1 − ε(i))`. -/
noncomputable def pdown (S : Setting) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (1 - S.eps (i + 1))

theorem pdown_pos (j : ℕ) : 0 < pdown S j :=
  Finset.prod_pos fun i _ => S.one_sub_eps_pos (Nat.le_add_left 1 i)

theorem pdown_le_one (j : ℕ) : pdown S j ≤ 1 := by
  refine Finset.prod_le_one (fun i _ => (S.one_sub_eps_pos (Nat.le_add_left 1 i)).le)
    fun i _ => ?_
  linarith [S.eps_pos (Nat.le_add_left 1 i)]

theorem pdown_anti {i j : ℕ} (h : i ≤ j) : pdown S j ≤ pdown S i := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · refine le_trans ?_ (ih (by omega))
        unfold pdown
        rw [Finset.prod_range_succ]
        have h1 := pdown_pos (S := S) j
        have h2 : 1 - S.eps (j + 1) ≤ 1 := by linarith [S.eps_pos (Nat.le_add_left 1 j)]
        unfold pdown at h1
        nlinarith

/-- **Straight decrements escape.** `P_j(σ > n) ≤ 1 − Π_{i ≤ j}(1 − ε(i))` once `n ≥ j`. -/
theorem sv_le_pdown : ∀ (j n : ℕ), j ≤ n → sv S n j ≤ 1 - pdown S j := by
  intro j
  induction j with
  | zero => intro n _; simp [pdown]
  | succ j ih =>
      intro n hn
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [sv_succ, ladT_succ]
      have h1 := sv_le_one (S := S) n' (2 * (j + 1))
      have h2 := ih n' (by omega)
      have he0 := S.eps_pos (Nat.le_add_left 1 j)
      have he1 := S.one_sub_eps_pos (Nat.le_add_left 1 j)
      have hp : pdown S (j + 1) = pdown S j * (1 - S.eps (j + 1)) := by
        unfold pdown; rw [Finset.prod_range_succ]
      rw [hp]
      nlinarith

/-! ### Domination along the ladder -/

/-- `j` dominates `m`: some power of the killed operator sees `m` from `j` with positive weight. -/
def LDom (S : Setting) (j m : ℕ) : Prop :=
  ∃ L : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → ρ * f m ≤ (ladT S)^[L] f j

theorem ldom_refl (j : ℕ) : LDom S j j := ⟨0, 1, one_pos, fun f _ => by simp⟩

theorem ldom_trans {a b c : ℕ} (h1 : LDom S a b) (h2 : LDom S b c) : LDom S a c := by
  obtain ⟨L1, ρ1, hρ1, h1⟩ := h1
  obtain ⟨L2, ρ2, hρ2, h2⟩ := h2
  refine ⟨L1 + L2, ρ1 * ρ2, mul_pos hρ1 hρ2, fun f hf => ?_⟩
  rw [Function.iterate_add_apply]
  have hg : ∀ k, 0 ≤ (ladT S)^[L2] f k := fun k => ladT_iterate_nonneg hf L2 k
  have := h1 _ hg
  have := mul_le_mul_of_nonneg_left (h2 f hf) hρ1.le
  nlinarith

theorem ldom_double {j : ℕ} (hj : 1 ≤ j) : LDom S j (2 * j) := by
  refine ⟨1, S.eps j, S.eps_pos hj, fun f hf => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Function.iterate_one, ladT_succ]
  have := mul_nonneg (S.one_sub_eps_pos hj).le (hf i)
  linarith

theorem ldom_dec (j : ℕ) : LDom S (j + 1) j := by
  refine ⟨1, 1 - S.eps (j + 1), S.one_sub_eps_pos (Nat.le_add_left 1 j), fun f hf => ?_⟩
  simp only [Function.iterate_one, ladT_succ]
  have := mul_nonneg (S.eps_pos (Nat.le_add_left 1 j)).le (hf (2 * (j + 1)))
  linarith

theorem ldom_down {a b : ℕ} (h : b ≤ a) : LDom S a b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n with
  | zero => exact ldom_refl b
  | succ n ih => exact ldom_trans (ldom_dec (b + n)) (ih (by omega))

/-- **Every ladder state dominates every ladder state** (`lem:doubling_irreducible`, on the ladder
with `s₀` removed). -/
theorem ldom_all {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) : LDom S j m := by
  refine ldom_trans (ldom_down hj) ?_
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · exact ldom_refl 1
      · exact ldom_trans (ih hm1) (ldom_trans (ldom_double hm1) (ldom_down (by omega)))

theorem sv_ldom {j m : ℕ} (h : LDom S j m) :
    ∃ L : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n, ρ * sv S n m ≤ sv S (L + n) j := by
  obtain ⟨L, ρ, hρ, h⟩ := h
  refine ⟨L, ρ, hρ, fun n => ?_⟩
  unfold sv; rw [Function.iterate_add_apply]
  exact h _ fun k => ladT_iterate_nonneg stepCost_nonneg n k

/-! ### The recurrence criterion on the ladder -/

/-- **Foster's recurrence criterion, as a statement about the least solution.** If `V ≥ 0` is a
supersolution of the killed operator off `{0, …, j₀}` and `V → ∞`, the ladder chain started
anywhere hits `s₀` with probability one: `P_j(σ > n) → 0`. -/
theorem ladder_recurrent {V : ℕ → ℝ} (hV0 : ∀ j, 0 ≤ V j) {j₀ : ℕ}
    (hdrift : ∀ m, j₀ < m → ladT S V m ≤ V m)
    (hgrow : ∀ M : ℝ, ∃ J : ℕ, ∀ j, J < j → M ≤ V j) (j : ℕ) :
    Tendsto (fun n => sv S n j) atTop (𝓝 0) := by
  -- the limit of the survival weights
  set w : ℕ → ℝ := fun k => ⨅ n, sv S n k with hw
  have hbb : ∀ k, BddBelow (Set.range fun n => sv S n k) :=
    fun k => ⟨0, by rintro _ ⟨n, rfl⟩; exact sv_nonneg n k⟩
  have htend : ∀ k, Tendsto (fun n => sv S n k) atTop (𝓝 (w k)) :=
    fun k => tendsto_atTop_ciInf (sv_anti k) (hbb k)
  have hw0 : ∀ k, 0 ≤ w k := fun k => le_ciInf fun n => sv_nonneg n k
  have hw1 : ∀ k, w k ≤ 1 := fun k => le_trans (ciInf_le (hbb k) 0) (sv_le_one 0 k)
  have hwsrc : w 0 = 0 := by simp [hw]
  have hfix : ∀ k, ladT S w k = w k := by
    intro k
    have h1 : Tendsto (fun n => sv S (n + 1) k) atTop (𝓝 (w k)) :=
      (htend k).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => ladT S (sv S n) k) atTop (𝓝 (ladT S w k)) := tendsto_ladT htend k
    exact tendsto_nhds_unique (h2.congr fun n => (sv_succ n k).symm) h1
  have hiter : ∀ n, (ladT S)^[n] w = w := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; funext k; exact hfix k
  -- its supremum `Q`
  have hwb : BddAbove (Set.range w) := ⟨1, by rintro _ ⟨k, rfl⟩; exact hw1 k⟩
  set Q : ℝ := ⨆ k, w k with hQ
  have hwQ : ∀ k, w k ≤ Q := fun k => le_ciSup hwb k
  have hQ0 : 0 ≤ Q := le_trans (hw0 0) (hwQ 0)
  -- on `{0, …, j₀}`, `w ≤ Q(1 − δ)`
  set δ : ℝ := pdown S j₀ with hδ
  have hδ0 : 0 < δ := pdown_pos j₀
  have hδ1 : δ ≤ 1 := pdown_le_one j₀
  have hlow : ∀ k, k ≤ j₀ → w k ≤ Q * (1 - δ) := by
    intro k hk
    have hle : ∀ i, w i ≤ Q * stepCost i := by
      intro i; cases i with
      | zero => simp [hwsrc]
      | succ i => simpa using hwQ (i + 1)
    have h1 := ladT_iterate_mono (S := S) hle k k
    rw [hiter, ladT_iterate_const_mul] at h1
    have h2 : sv S k k ≤ 1 - δ :=
      le_trans (sv_le_pdown k k le_rfl) (by linarith [pdown_anti (S := S) hk])
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hQ0)
  -- the maximum principle: `w ≤ Q(1 − δ) + (Q/M) V` for every `M > 0`
  have hmain : ∀ M : ℝ, 0 < M → ∀ x, w x ≤ Q * (1 - δ) + Q / M * V x := by
    intro M hM
    set g : ℕ → ℝ := fun k => Q * (1 - δ) + Q / M * V k with hg
    set h : ℕ → ℝ := fun k => w k - g k with hh
    obtain ⟨J, hJ⟩ := hgrow M
    have hQM : 0 ≤ Q / M := div_nonneg hQ0 hM.le
    have hout : ∀ k, (k ≤ j₀ ∨ J < k) → h k ≤ 0 := by
      intro k hk
      simp only [hh, hg]
      rcases hk with hk | hk
      · have := hlow k hk; have := mul_nonneg hQM (hV0 k); linarith
      · have hVk := hJ k hk
        have : Q ≤ Q / M * V k := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hM]; exact mul_le_mul_of_nonneg_left hVk hQ0
        have := hwQ k
        nlinarith
    have hsub : ∀ k, j₀ < k → h k ≤ ladT S h k := by
      intro k hk
      have hk1 : 1 ≤ k := by omega
      have e1 : ladT S h k = ladT S w k - ladT S g k := ladT_sub w g k
      have e2 : ladT S g k = Q * (1 - δ) + Q / M * ladT S V k := ladT_affine _ _ V hk1
      rw [e1, e2, hfix k]
      simp only [hh, hg]
      have := mul_le_mul_of_nonneg_left (hdrift k hk) hQM
      linarith
    intro x
    by_contra hcon
    push Not at hcon
    have hx : 0 < h x := by simp only [hh, hg]; linarith
    have hxin : x ∈ Finset.Icc (j₀ + 1) J := by
      rw [Finset.mem_Icc]
      by_contra hn
      have := hout x (by omega)
      linarith
    obtain ⟨xm, hxm, hmax⟩ := Finset.exists_max_image (Finset.Icc (j₀ + 1) J) h ⟨x, hxin⟩
    set T := h xm with hT
    have hTpos : 0 < T := lt_of_lt_of_le hx (hmax x hxin)
    have hall : ∀ k, h k ≤ T := by
      intro k
      by_cases hk : k ∈ Finset.Icc (j₀ + 1) J
      · exact hmax k hk
      · rw [Finset.mem_Icc] at hk
        have := hout k (by omega)
        linarith
    have hex : ∃ k, k ∈ Finset.Icc (j₀ + 1) J ∧ h k = T := ⟨xm, hxm, rfl⟩
    classical
    obtain ⟨ks, hks_mem0, hTeq0, hks_min⟩ : ∃ ks, ks ∈ Finset.Icc (j₀ + 1) J ∧ h ks = T ∧
        ∀ k < ks, ¬ (k ∈ Finset.Icc (j₀ + 1) J ∧ h k = T) :=
      ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk => Nat.find_min hex hk⟩
    have hks_mem := hks_mem0
    rw [Finset.mem_Icc] at hks_mem
    obtain ⟨i, hi⟩ : ∃ i, ks = i + 1 := ⟨ks - 1, by omega⟩
    have hprev : h i < T := by
      rcases lt_or_eq_of_le (hall i) with hlt | heq
      · exact hlt
      · exfalso
        by_cases hi0 : j₀ + 1 ≤ i
        · exact hks_min i (by omega) ⟨Finset.mem_Icc.mpr ⟨hi0, by omega⟩, heq⟩
        · have := hout i (by omega); linarith
    have hstep := hsub ks (by omega)
    rw [hi, ladT_succ] at hstep
    have hTeq : h (i + 1) = T := hi ▸ hTeq0
    have he0 := S.eps_pos (Nat.le_add_left 1 i)
    have he1 := S.one_sub_eps_pos (Nat.le_add_left 1 i)
    have h2 := hall (2 * (i + 1))
    rw [hTeq] at hstep
    nlinarith
  -- let `M → ∞`: `w ≤ Q(1 − δ)`, hence `Q ≤ Q(1 − δ)` and `Q = 0`
  have hw_le : ∀ x, w x ≤ Q * (1 - δ) := by
    intro x
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set M : ℝ := (Q * V x + 1) / ε with hMdef
    have hMpos : 0 < M := by
      have := mul_nonneg hQ0 (hV0 x); positivity
    have h1 := hmain M hMpos x
    have h2 : Q / M * V x ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hMpos, hMdef]
      field_simp
      linarith
    linarith
  have hQle : Q ≤ Q * (1 - δ) := ciSup_le hw_le
  have hQz : Q = 0 := by nlinarith
  have hwj : w j = 0 := le_antisymm (by linarith [hwQ j]) (hw0 j)
  rw [← hwj]; exact htend j

/-! ### The transience criterion on the ladder -/

/-- **The bounded-supermartingale transience criterion, as a comparison with the least solution.**
If `W ≥ 0` is a supersolution of the killed operator off `{0, …, j₀}` and `W ≥ w > 0` on that
set, then `P_j(σ ≤ n) ≤ W(j)/w` at every `j` and `n`. -/
theorem ladder_survival_ge {W : ℕ → ℝ} (hW0 : ∀ j, 0 ≤ W j) {j₀ : ℕ} {w : ℝ} (hw : 0 < w)
    (hwF : ∀ j, j ≤ j₀ → w ≤ W j) (hdrift : ∀ m, j₀ < m → ladT S W m ≤ W m) (n j : ℕ) :
    1 - W j / w ≤ sv S n j := by
  induction n generalizing j with
  | zero =>
      rw [sv_zero]
      cases j with
      | zero =>
          have := hwF 0 (Nat.zero_le _)
          rw [stepCost_zero, sub_nonpos, le_div_iff₀ hw]; linarith
      | succ j =>
          rw [stepCost_succ]; have := div_nonneg (hW0 (j + 1)) hw.le; linarith
  | succ n ih =>
      by_cases hj : j ≤ j₀
      · have := hwF j hj
        have : 1 ≤ W j / w := by rw [le_div_iff₀ hw]; linarith
        linarith [sv_nonneg (S := S) (n + 1) j]
      · push Not at hj
        rw [sv_succ]
        have h1 := ladT_mono (S := S) (f := fun k => 1 + (-(1 / w)) * W k) (g := sv S n)
          (fun k => by have := ih k; rw [div_eq_mul_one_div] at this; linarith) j
        rw [ladT_affine _ _ W (by omega)] at h1
        have h2 := hdrift j hj
        have h3 : (-(1 / w)) * ladT S W j ≥ (-(1 / w)) * W j :=
          mul_le_mul_of_nonpos_left h2 (by have := one_div_pos.mpr hw; linarith)
        rw [div_eq_mul_one_div]
        linarith

/-! ### The expected hitting time at `c ≥ 1` -/

theorem hitLad_ge_min (n k : ℕ) : ((min n k : ℕ) : ℝ) ≤ hitLad S n k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ i =>
          rw [hitLad_succ, stepCost_succ, ladT_succ]
          have h1 := ih (2 * (i + 1))
          have h2 := ih i
          have hmono : ((min n i : ℕ) : ℝ) ≤ ((min n (2 * (i + 1)) : ℕ) : ℝ) := by
            exact_mod_cast (by omega : min n i ≤ min n (2 * (i + 1)))
          have he0 := S.eps_pos (Nat.le_add_left 1 i)
          have he1 := S.one_sub_eps_pos (Nat.le_add_left 1 i)
          have hcast : ((min (n + 1) (i + 1) : ℕ) : ℝ) = ((min n i : ℕ) : ℝ) + 1 := by
            rw [show min (n + 1) (i + 1) = min n i + 1 by omega]; push_cast; ring
          rw [hcast]
          nlinarith

theorem hitLad_ge_iterate (n : ℕ) : ∀ L j, (ladT S)^[L] (hitLad S n) j ≤ hitLad S (L + n) j := by
  intro L
  induction L with
  | zero => intro j; simp
  | succ L ih =>
      intro j
      rw [Function.iterate_succ_apply']
      have h1 := ladT_mono (S := S) ih j
      rw [ladT_hitLad, show L + 1 + n = L + n + 1 by omega] at *
      linarith [stepCost_nonneg j]

theorem hitLad_bdd_of_ldom {j m : ℕ} (h : LDom S j m)
    (hb : BddAbove (Set.range fun n => hitLad S n j)) :
    BddAbove (Set.range fun n => hitLad S n m) := by
  obtain ⟨L, ρ, hρ, h⟩ := h
  obtain ⟨B, hB⟩ := hb
  refine ⟨B / ρ, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [le_div_iff₀ hρ, mul_comm]
  have h1 := h (hitLad S n) (hitLad_nonneg n)
  have h2 := hitLad_ge_iterate (S := S) n L j
  have h3 : hitLad S (L + n) j ≤ B := hB ⟨L + n, rfl⟩
  linarith

/-- **`E(σ | X₀ = m) = +∞` at every ladder state, for `s = 1` and `c ≥ 1`.** The truncated
expectations `E(σ ∧ n | X₀ = m)` are unbounded. -/
theorem hitLad_unbdd {c : ℝ} (hc1 : 1 ≤ c) (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1))
    {m : ℕ} (hm : 1 ≤ m) : ¬ BddAbove (Set.range fun n => hitLad S n m) := by
  intro hbm
  have hball : ∀ k, BddAbove (Set.range fun n => hitLad S n k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨0, by rintro _ ⟨n, rfl⟩; simp⟩
    · exact hitLad_bdd_of_ldom (ldom_all hm hk) hbm
  set v : ℕ → ℝ := fun k => ⨆ n, hitLad S n k with hv
  have htend : ∀ k, Tendsto (fun n => hitLad S n k) atTop (𝓝 (v k)) :=
    fun k => tendsto_atTop_ciSup (fun _ _ h => hitLad_mono h k) (hball k)
  have hvsol : ∀ k, ladT S v k = v k - stepCost k := by
    intro k
    have h1 : Tendsto (fun n => hitLad S (n + 1) k) atTop (𝓝 (v k)) :=
      (htend k).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => ladT S (hitLad S n) k) atTop (𝓝 (ladT S v k)) :=
      tendsto_ladT htend k
    have h3 : Tendsto (fun n => stepCost k + ladT S (hitLad S n) k) atTop
        (𝓝 (stepCost k + ladT S v k)) := h2.const_add _
    have := tendsto_nhds_unique (h3.congr fun n => (hitLad_succ n k).symm) h1
    linarith
  have hiter : ∀ n, (ladT S)^[n] v = fun k => v k - hitLad S n k := by
    intro n
    induction n with
    | zero => funext k; simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        funext k
        rw [ladT_sub, hvsol, ladT_hitLad]; ring
  have hvge : ∀ k : ℕ, (k : ℝ) ≤ v k := by
    intro k
    have h1 := hitLad_ge_min (S := S) k k
    rw [min_self] at h1
    exact le_trans h1 (le_ciSup (hball k) k)
  have hbound : ∀ n, (m : ℝ) ≤ v m - hitLad S n m := by
    intro n
    have h1 := ladT_iterate_mono (S := S) (f := ladId) (g := v) (fun k => by simpa using hvge k) n m
    rw [hiter, ladT_iterate_id_eq heps] at h1
    have h2 := hitLad_nonneg (S := S) n m
    have : (1 - c) * hitLad S n m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h2
    linarith
  have hlim : Tendsto (fun n => v m - hitLad S n m) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := v m)).sub (htend m)
  have := ge_of_tendsto hlim (Eventually.of_forall hbound)
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-! ### The return to `s₀`, read on the ladder -/

theorem one_sub_hitP_src (n j : ℕ) : 1 - hitP S none (.lad 0) n (.lad j) = sv S n j := by
  induction n generalizing j with
  | zero =>
      rw [hitP_zero, sv_zero]
      cases j with
      | zero => simp
      | succ j => rw [ptFn_of_ne (by simp), stepCost_succ]; ring
  | succ n ih =>
      cases j with
      | zero => rw [hitP_succ, if_pos rfl, sv_src]; ring
      | succ i =>
          rw [hitP_succ_of_ne (by simp), pstar_lad_succ, if_pos (hasDouble_none _), sv_succ,
            ladT_succ, ← ih, ← ih]
          ring

theorem one_sub_retP_src (n : ℕ) :
    1 - retP S none (.lad 0) (n + 1) = ∑ k ∈ Finset.Icc 1 S.d, S.row k * sv S n k := by
  unfold retP
  rw [pstar_src, hitP_succ_of_ne (by simp), pstar_sink]
  have h : ∀ k ∈ Finset.Icc 1 S.d, S.row k * sv S n k
      = S.row k - S.row k * hitP S none (.lad 0) n (.lad k) := by
    intro k _; rw [← one_sub_hitP_src]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, S.row_sum]

theorem hitT_src_lad (n j : ℕ) : hitT S none (.lad 0) n (.lad j) = hitExp S none n (.lad j) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      cases j with
      | zero => simp
      | succ i =>
          rw [hitT_succ, if_neg (by simp), hitExp_succ_lad, pstar_lad_succ, pstar_lad_succ, ih, ih]

theorem retT_src_succ (n : ℕ) : retT S none (.lad 0) (n + 1) = 2 + sbar S none n := by
  unfold retT
  rw [pstar_src, hitT_succ, if_neg (by simp), pstar_sink, sbar]
  rw [Finset.sum_congr rfl fun k _ => by rw [hitT_src_lad]]
  ring

theorem pstar_lad_eq_ladT (F : St → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    pstar S none F (.lad m) = ladT S (fun k => F (.lad k)) m := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  rw [pstar_lad_succ, if_pos (hasDouble_none _), ladT_succ]

/-- If the ladder chain hits `s₀` with probability one from every ladder state, `s₀` is
recurrent. -/
theorem recurrent_src_of_sv (h : ∀ k, Tendsto (fun n => sv S n k) atTop (𝓝 0)) :
    IsRecurrentAt S none (.lad 0) := by
  have h1 : Tendsto (fun n => ∑ k ∈ Finset.Icc 1 S.d, S.row k * sv S n k) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.Icc 1 S.d) fun k _ => (h k).const_mul (S.row k)
  have h2 : Tendsto (fun n => retP S none (.lad 0) (n + 1)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    simp only [sub_zero] at this
    exact this.congr fun n => by rw [← one_sub_retP_src]; ring
  exact tendsto_nhds_unique ((tendsto_retP).comp (tendsto_add_atTop_nat 1)) h2

/-- If the ladder chain survives with probability bounded below from one ladder state, `s₀` is
transient. -/
theorem transient_src_of_sv {m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη : 0 < η)
    (h : ∀ n, η ≤ sv S n m) : IsTransientAt S none (.lad 0) := by
  obtain ⟨k, hk, hkpos⟩ := exists_row_pos S
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  obtain ⟨L, ρ, hρ, hdom⟩ := sv_ldom (ldom_all (S := S) hk1 hm)
  have hlow : ∀ n, S.row k * (ρ * η) ≤ 1 - retP S none (.lad 0) (n + 1) := by
    intro n
    rw [one_sub_retP_src]
    have h1 : ρ * η ≤ sv S n k := by
      have := mul_le_mul_of_nonneg_left (h n) hρ.le
      exact le_trans this (le_trans (hdom n) (sv_anti k (by omega : n ≤ L + n)))
    have h2 : S.row k * (ρ * η) ≤ S.row k * sv S n k :=
      mul_le_mul_of_nonneg_left h1 (S.row_nonneg k)
    exact le_trans h2 (Finset.single_le_sum (f := fun k => S.row k * sv S n k)
      (fun i _ => mul_nonneg (S.row_nonneg i) (sv_nonneg n i)) hk)
  have hlim := (tendsto_retP (S := S) (cap := none) (y := .lad 0)).comp (tendsto_add_atTop_nat 1)
  have hle : retProb S none (.lad 0) ≤ 1 - S.row k * (ρ * η) :=
    le_of_tendsto hlim (Eventually.of_forall fun n => by
      have := hlow n; simp only [Function.comp]; linarith)
  unfold IsTransientAt
  have : 0 < S.row k * (ρ * η) := by positivity
  linarith

/-- An infinite expected hitting time at one ladder state makes `s₀` not positive recurrent. -/
theorem not_posRecurrent_src {m : ℕ} (hm : 1 ≤ m)
    (hunb : ¬ BddAbove (Set.range fun n => hitLad S n m)) :
    ¬ IsPosRecurrentAt S none (.lad 0) := by
  rintro ⟨-, B, hB⟩
  obtain ⟨k, hk, hkpos⟩ := exists_row_pos S
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  apply hunb
  refine hitLad_bdd_of_ldom (ldom_all hk1 hm) ⟨B / S.row k, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [le_div_iff₀ hkpos, mul_comm]
  have h1 : retT S none (.lad 0) (n + 1) ≤ B := hB ⟨n + 1, rfl⟩
  rw [retT_src_succ, sbar] at h1
  have h2 := Finset.single_le_sum (f := fun k => S.row k * hitExp S none n (.lad k))
    (fun i _ => mul_nonneg (S.row_nonneg i) (hitExp_nonneg n _)) hk
  have h3 := sbar_nonneg (S := S) (cap := none) n
  unfold hitLad
  linarith

/-! ### The Lyapunov functions, fed to the two criteria -/

/-- **Transience from a supermartingale `W_t`.** If `W_t` has non-positive drift past `m₀`, the
loop closure is transient. -/
theorem transient_of_Wpow {t : ℝ} (ht : 0 < t) {m₀ : ℕ}
    (hdrift : ∀ m : ℕ, m₀ ≤ m → 1 ≤ m →
      pstar S none (Wpow t) (.lad m) - Wpow t (.lad m) ≤ 0) : IsTransient S none := by
  set W : ℕ → ℝ := fun k => Wpow t (.lad k) with hW
  have hW0 : ∀ k, 0 ≤ W k := fun k => (Wpow_pos t _).le
  have hw : 0 < W m₀ := Wpow_pos t _
  have hwF : ∀ j, j ≤ m₀ → W m₀ ≤ W j := fun j hj => Wpow_antitone ht.le hj
  have hdr : ∀ m, m₀ < m → ladT S W m ≤ W m := by
    intro m hm
    have := hdrift m hm.le (by omega)
    rw [pstar_lad_eq_ladT _ (by omega)] at this
    simp only [hW]; linarith
  have hsurv := ladder_survival_ge (S := S) hW0 hw hwF hdr
  have hlt : W (m₀ + 1) < W m₀ := Wpow_strictAnti ht (by omega)
  have hη : 0 < 1 - W (m₀ + 1) / W m₀ := by
    rw [sub_pos, div_lt_one hw]; exact hlt
  have hsrc := transient_src_of_sv (S := S) (m := m₀ + 1) (by omega) hη
    (fun n => hsurv n (m₀ + 1))
  exact fun y _ => transient_solidarity hsrc

/-- **Recurrence from `V₂ = log(j+1)`.** If `V₂` has non-positive drift past `m₀`, the loop closure
is recurrent. -/
theorem recurrent_of_logHeight {m₀ : ℕ}
    (hdrift : ∀ m : ℕ, m₀ ≤ m → 1 ≤ m →
      pstar S none logHeight (.lad m) - logHeight (.lad m) ≤ 0) : IsRecurrent S none := by
  set V : ℕ → ℝ := fun k => Real.log ((k : ℝ) + 1) with hV
  have hV0 : ∀ k, 0 ≤ V k := fun k => Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hdr : ∀ m, m₀ < m → ladT S V m ≤ V m := by
    intro m hm
    have := hdrift m hm.le (by omega)
    rw [pstar_lad_eq_ladT _ (by omega)] at this
    simp only [logHeight_lad] at this
    simp only [hV]; linarith
  have hgrow : ∀ M : ℝ, ∃ J : ℕ, ∀ j, J < j → M ≤ V j := by
    intro M
    refine ⟨⌈Real.exp M⌉₊, fun j hj => ?_⟩
    have h1 : Real.exp M ≤ (j : ℝ) + 1 := by
      have := Nat.le_ceil (Real.exp M)
      have : (⌈Real.exp M⌉₊ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.le
      linarith
    simp only [hV]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr h1
  have hsrc := recurrent_src_of_sv (S := S) (ladder_recurrent hV0 hdr hgrow)
  exact fun y _ => recurrent_solidarity hsrc

/-! ### The rows of the phase diagram -/

section Rows

variable {c s : ℝ}

/-- **Row `s > 1`.** Positive recurrent (Step 3). -/
theorem phase_gt_one (hc : 0 < c) (hs : 1 < s) (heps : ∀ j, S.eps j = epsCS c s j) :
    IsPositiveRecurrent S none :=
  (exists_stat_of_family_gt_one hc hs S (funext heps)).some.isPositiveRecurrent

/-- **Row `s < 1`.** Transient (Step 4). -/
theorem phase_lt_one (hc : 0 < c) (hs : s < 1) (heps : ∀ j, S.eps j = epsCS c s j) :
    IsTransient S none := by
  obtain ⟨m₀, hm₀⟩ := exists_Wpow_one_drift_nonpos (S := S) (cap := none) hc hs
    (fun j _ => heps j)
  exact transient_of_Wpow one_pos fun m hm hm1 => hm₀ m hm hm1 trivial

/-- **Row `s = 1`, `0 < c < 1`.** Positive recurrent, with `E(σ | X₀ = j) = j/(1−c)` (Step 5). -/
theorem phase_one_lt (hc0 : 0 < c) (hc1 : c < 1) (heps : ∀ j, S.eps j = epsCS c 1 j) :
    IsPositiveRecurrent S none ∧
      ∀ j : ℕ, 1 ≤ j → ⨆ n, hitExp S none n (.lad j) = (j : ℝ) / (1 - c) :=
  ⟨(exists_stat_of_family hc0 hc1 S (funext heps)).some.isPositiveRecurrent,
    fun j _ => hitExp_iSup_eq hc0 hc1 (fun i _ => by rw [heps, epsCS_one_apply]) j⟩

/-- **Row `s = 1`, `1 ≤ c`.** `E(σ | X₀ = j) = +∞` at every ladder state and no state is positive
recurrent (Step 7). -/
theorem phase_one_ge (hc1 : 1 ≤ c) (heps : ∀ j, S.eps j = epsCS c 1 j) :
    (∀ j : ℕ, 1 ≤ j → ¬ BddAbove (Set.range fun n => hitExp S none n (.lad j))) ∧
      ∀ y, ¬ IsPosRecurrentAt S none y := by
  have heps' : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1) := fun j _ => by
    rw [heps, epsCS_one_apply]
  refine ⟨fun j hj => hitLad_unbdd hc1 heps' hj, fun y hy => ?_⟩
  exact not_posRecurrent_src le_rfl (hitLad_unbdd hc1 heps' le_rfl) (posRecurrent_solidarity hy)

/-- **Row `s = 1`, `c < 1/ln 2`.** Recurrent (Step 6). -/
theorem phase_one_recurrent (hc0 : 0 < c) (hclog : c < 1 / Real.log 2)
    (heps : ∀ j, S.eps j = epsCS c 1 j) : IsRecurrent S none := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcl : c * Real.log 2 < 1 := by rwa [lt_div_iff₀ hlog2] at hclog
  obtain ⟨m₀, hm₀⟩ := exists_logHeight_drift_nonpos (S := S) (cap := none) hc0.le
    (fun j _ => heps j) hcl
  exact recurrent_of_logHeight fun m hm hm1 => hm₀ m hm hm1 trivial

/-- **Row `s = 1`, `1 ≤ c < 1/ln 2`.** Null recurrent (Steps 6–7). -/
theorem phase_one_null (hc1 : 1 ≤ c) (hclog : c < 1 / Real.log 2)
    (heps : ∀ j, S.eps j = epsCS c 1 j) : IsNullRecurrent S none := by
  have hrec := phase_one_recurrent (by linarith) hclog heps
  have hnp := (phase_one_ge hc1 heps).2
  exact fun y hy => ⟨hrec y hy, fun hb => hnp y ⟨hrec y hy, hb⟩⟩

/-- **Row `s = 1`, `1/ln 2 < c`.** Transient (Step 8). -/
theorem phase_one_transient (hclog : 1 / Real.log 2 < c) (heps : ∀ j, S.eps j = epsCS c 1 j) :
    IsTransient S none := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcl : 1 < c * Real.log 2 := by rwa [div_lt_iff₀ hlog2] at hclog
  have hc0 : 0 ≤ c := by
    have : 0 < 1 / Real.log 2 := by positivity
    linarith
  set t : ℝ := (c * Real.log 2 - 1) / (2 * Real.log 2) with ht
  have ht0 : 0 < t := by rw [ht]; apply div_pos <;> linarith
  have hlt : t * Real.log 2 < c * Real.log 2 - 1 := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  obtain ⟨m₀, hm₀⟩ := exists_Wpow_drift_neg (S := S) (cap := none) hc0 ht0
    (fun j _ => heps j) hlt
  exact transient_of_Wpow ht0 fun m hm hm1 => (hm₀ m hm hm1 trivial).le

end Rows

/-! ### `prop:doubling_phase` and `theo:doubling_main`(1) -/

/-- **The rows are inhabited.** At every `(c,s)` of the standing range the family is a `Setting`
(`Setting.ofFamily`, `lem:doubling_range`), here with the target row the point mass at `1`. -/
theorem exists_family_setting {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) (hcs : c < 2 ^ s) :
    ∃ S : Setting, ∀ j, S.eps j = epsCS c s j := by
  refine ⟨Setting.ofFamily c s hc hs hcs 1 le_rfl (fun j => if j = 1 then 1 else 0)
    (fun j => by split <;> norm_num) (fun j hj => ?_) (by simp), fun j => rfl⟩
  by_cases h : j = 1
  · omega
  · simp [h] at hj

/-- **`prop:doubling_phase`.** In the setting of `def:doubling_setting`, with `ε = ε_{c,s}`:
the loop-closed backward chain is irreducible, and
(1) if `s > 1` it is positive recurrent;
(2) if `s < 1` it is transient;
(3) if `s = 1`: positive recurrent for `0 < c < 1`, with `E(σ | X₀ = j) = j/(1−c)` at every
ladder state; for `1 ≤ c`, `E(σ | X₀ = j) = +∞` at every ladder state and no state is positive
recurrent; null recurrent for `1 ≤ c < 1/ln 2`; transient for `1/ln 2 < c`. -/
theorem prop_doubling_phase {c s : ℝ} (hc : 0 < c) (heps : ∀ j, S.eps j = epsCS c s j) :
    (∀ x y : St, Reach S none x y) ∧
    (1 < s → IsPositiveRecurrent S none) ∧
    (s < 1 → IsTransient S none) ∧
    (s = 1 →
      (c < 1 → IsPositiveRecurrent S none ∧
        ∀ j : ℕ, 1 ≤ j → ⨆ n, hitExp S none n (.lad j) = (j : ℝ) / (1 - c)) ∧
      (1 ≤ c → (∀ j : ℕ, 1 ≤ j → ¬ BddAbove (Set.range fun n => hitExp S none n (.lad j))) ∧
        ∀ y, ¬ IsPosRecurrentAt S none y) ∧
      (1 ≤ c → c < 1 / Real.log 2 → IsNullRecurrent S none) ∧
      (1 / Real.log 2 < c → IsTransient S none)) := by
  refine ⟨reach_all_none S, fun hs => phase_gt_one hc hs heps,
    fun hs => phase_lt_one hc hs heps, fun hs => ?_⟩
  subst hs
  exact ⟨fun hc1 => phase_one_lt hc hc1 heps, fun hc1 => phase_one_ge hc1 heps,
    fun hc1 hcl => phase_one_null hc1 hcl heps, fun hcl => phase_one_transient hcl heps⟩

/-- **`theo:doubling_main`(1), the table.** Irreducible, and rows (a)–(f), with row (d) exactly
the paper's "not positive recurrent" (at every state). -/
theorem main_phase_classes {c s : ℝ} (hc : 0 < c) (heps : ∀ j, S.eps j = epsCS c s j) :
    (∀ x y : St, Reach S none x y) ∧
    (s < 1 → IsTransient S none) ∧
    (s = 1 → c < 1 → IsPositiveRecurrent S none) ∧
    (s = 1 → 1 ≤ c → c < 1 / Real.log 2 → IsNullRecurrent S none) ∧
    (s = 1 → c = 1 / Real.log 2 → ∀ y, ¬ IsPosRecurrentAt S none y) ∧
    (s = 1 → 1 / Real.log 2 < c → IsTransient S none) ∧
    (1 < s → IsPositiveRecurrent S none) := by
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨reach_all_none S, fun hs => phase_lt_one hc hs heps, fun hs hc1 => ?_,
    fun hs hc1 hcl => ?_, fun hs hcd => ?_, fun hs hcl => ?_, fun hs => phase_gt_one hc hs heps⟩
  · subst hs; exact (phase_one_lt hc hc1 heps).1
  · subst hs; exact phase_one_null hc1 hcl heps
  · subst hs
    have hc1 : 1 ≤ c := by
      rw [hcd, le_div_iff₀ hlog0]; linarith
    exact (phase_one_ge hc1 heps).2
  · subst hs; exact phase_one_transient hcl heps

/-- **`theo:doubling_main`(2), "the invariant probability".** The loop closure carries at most one
invariant probability, positive or not: any two invariant probabilities (`PreStat`, which carries
no positivity field) coincide. The form over `Stat` is `stat_unique_none`, where moreover
`λ(y) = 1/E_y τ_y⁺` at every state (`Stat.kac_eq`). -/
theorem main_invariant_unique (P P' : PreStat S none) : P.lam = P'.lam :=
  stat_unique_none P.toStatNone P'.toStatNone

end GFNBounds.Doubling
