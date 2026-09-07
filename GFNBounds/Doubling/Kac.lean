import GFNBounds.Doubling.Supersolution
import GFNBounds.Doubling.Irreducible
import GFNBounds.Doubling.PerCutNorms

/-!
# Kac's formula on the doubling graph, from invariance alone

**`cor:doubling_truncation`, Step 6** — `app_doubling.tex:2199–2336`.

> By Step 1 the truncation is a finite irreducible chain, so `λ^K(s₀)` is the reciprocal of the
> expected return time of that chain to `s₀`. A return from `s₀` is the wrap `s₀ → s_f`, the step
> from `s_f` to a state of the target row, and the run from that state to `s₀`, so its expected
> length is `2 + σ̄_K`. […] Hence `λ^K_1 ≥ λ^K(s₀) = 1/(2 + σ̄_K)`, and `σ̄_K ≤ j̄/(1−c)`, so for
> every `m ≥ 2`, `1 − L_K(m) ≥ λ^K_1 ≥ (2 + j̄/(1−c))^{-1}`, a bound free of `K`.

## What is proved here, and why it is not a citation

The paper cites Kac's formula. Mathlib v4.31.0 has none, and this library builds no chain — but
Kac's formula on *this* graph is a consequence of invariance in the integral form `Stat` already
carries, tested against the truncated hitting expectations `hitExp` of `lem:doubling_supersolution`.
The one-step recursion `u_{n+1} = 1 + P⋆u_n` makes

  `a_{n+1} − a_n = 1 − λ(s₀) − (1 + σ̄⁽ⁿ⁾) λ(s_f)`,   `a_n := ∫ u_n dλ`,

because `u_{n+1} − P⋆u_n` is `1` at every ladder state, `0` at `s₀` and `−σ̄⁽ⁿ⁾` at `s_f`. Both `a_n`
and `σ̄⁽ⁿ⁾` are monotone and bounded, so `a_{n+1} − a_n → 0`, and the limit is

  **`λ(s₀) · (2 + σ̄) = 1`**   (`kac_identity`),

once `λ(s_f) = λ(s₀)`, which is the flux into the sink. That is exactly the identity the lab
register records as measured — `1/λ(s₀) − σ̄ ∈ [1.999999994526, 2.000000000004]` over twenty cells
— and it is `prop:morozov_rate`(1) read at `s₀`.

## SCOPE (disclosed)

* `σ̄` here is `⨆ₙ σ̄⁽ⁿ⁾`, the limit of the target-row averages of the truncated hitting
  expectations, which is what `lem:doubling_supersolution` bounds. That it *is* the expected
  backward-trajectory length is the modelling decision of that file, not a theorem.
* The boundedness hypothesis `hM` — the supersolution is bounded on the chain — holds on every
  truncation with `M = K/(1−c)` and is what makes `a_n` converge. On the loop closure it is false,
  and Kac's formula there would need `∫ h dλ < ∞`; the corollary needs only the truncation.
* ⚠ weakened: irreducibility is **not** used. The paper reaches Kac through "finite irreducible
  chain"; here invariance plus the recursion suffices, and no chain is built.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real Filter Topology

variable {S : Setting} {cap : Option ℕ}

/-! ### The truncated hitting expectations are bounded at each `n` -/

/-- `E(σ ∧ n) ≤ n`: the truncated hitting time is at most `n`. -/
theorem hitExp_le_nat (n : ℕ) (x : St) : hitExp S cap n x ≤ (n : ℝ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rcases x with j | _
      · rcases j with _ | j
        · simp; positivity
        · rw [hitExp_succ_lad]
          have hb : ∀ y, |hitExp S cap n y| ≤ (n : ℝ) := fun y => by
            rw [abs_of_nonneg (hitExp_nonneg n y)]; exact ih y
          have := pstar_bounded (S := S) (cap := cap) hb (St.lad (j + 1))
          have h2 : pstar S cap (hitExp S cap n) (.lad (j + 1)) ≤ (n : ℝ) :=
            le_trans (le_abs_self _) this
          push_cast
          linarith
      · simp; positivity

theorem hitExp_bounded (n : ℕ) : ∃ C, ∀ x, |hitExp S cap n x| ≤ C :=
  ⟨(n : ℝ), fun x => by rw [abs_of_nonneg (hitExp_nonneg n x)]; exact hitExp_le_nat n x⟩

/-! ### Point masses, and the two flux computations -/

theorem hasSum_lam_mul_ptFn (L : Stat S cap) (y : St) :
    HasSum (fun x => L.lam x * ptFn y x) (L.lam y) := by
  have h : (fun x => L.lam x * ptFn y x) = fun x => if x = y then L.lam y else 0 := by
    funext x
    by_cases hx : x = y
    · subst hx; simp
    · simp [ptFn, hx]
  rw [h]; exact hasSum_ite_eq _ _

/-- Total flux into `y` is `λ(y)`: invariance tested against the point mass at `y`. -/
theorem Stat.hasSum_flux_pt (L : Stat S cap) (y : St) :
    HasSum (fun x => L.lam x * pstar S cap (ptFn y) x) (L.lam y) := by
  have hsum : Summable (fun x => L.lam x * pstar S cap (ptFn y) x) := by
    obtain ⟨C, hC⟩ := ptFn_bounded y
    exact L.summable_mul ⟨C, fun x => pstar_bounded hC x⟩
  have h := hsum.hasSum
  rwa [L.inv (ptFn y) (ptFn_bounded y), (hasSum_lam_mul_ptFn L y).tsum_eq] at h

/-- **The wrap.** `P⋆ 1_{\{s_f\}} = 1_{\{s₀\}}`: the sink is entered from the source alone, with
probability one. -/
theorem pstar_ptFn_sink : pstar S cap (ptFn .sink) = ptFn (.lad 0) := by
  funext x
  rcases x with j | _
  · rcases j with _ | j
    · simp [ptFn]
    · by_cases hD : HasDouble cap (j + 1) <;>
        simp [pstar_lad_succ, hD, ptFn]
  · simp [ptFn]

/-- **The decrement out of `1`.** Nothing but the state `1` flows into `s₀`. -/
theorem pstar_ptFn_src_le (x : St) :
    pstar S cap (ptFn (.lad 0)) x ≤ ptFn (.lad 1) x := by
  rcases x with j | _
  · rcases j with _ | j
    · simp [ptFn]
    · rcases j with _ | i
      · by_cases hD : HasDouble cap 1
        · rw [pstar_lad_succ, if_pos hD]
          have h1 : 0 ≤ S.eps 1 := (S.eps_pos le_rfl).le
          have h2 : 0 ≤ 1 - S.eps 1 := (S.one_sub_eps_pos le_rfl).le
          simp only [ptFn, St.lad.injEq]
          norm_num
          linarith
        · rw [pstar_lad_succ, if_neg hD]
          simp [ptFn]
      · by_cases hD : HasDouble cap (i + 1 + 1) <;>
          simp [pstar_lad_succ, hD, ptFn]
  · simp [ptFn]

/-- `λ(s_f) = λ(s₀)`. -/
theorem Stat.lam_sink_eq_src (L : Stat S cap) : L.lam .sink = L.lam (.lad 0) := by
  have h1 := L.hasSum_flux_pt .sink
  rw [pstar_ptFn_sink] at h1
  exact h1.unique (hasSum_lam_mul_ptFn L (.lad 0))

/-- `λ(s₀) ≤ λ_1`. -/
theorem Stat.lam_src_le_lam_one (L : Stat S cap) : L.lam (.lad 0) ≤ L.lam (.lad 1) := by
  have h1 := L.hasSum_flux_pt (.lad 0)
  have h2 := hasSum_lam_mul_ptFn L (.lad 1)
  exact hasSum_le (fun x => mul_le_mul_of_nonneg_left (pstar_ptFn_src_le x) (L.nonneg x)) h1 h2

/-! ### The defect of the truncated hitting expectation -/

/-- `σ̄⁽ⁿ⁾`, the target-row average of `E(σ ∧ n)`. -/
noncomputable def sbar (S : Setting) (cap : Option ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 S.d, S.row k * hitExp S cap n (.lad k)

theorem sbar_nonneg (n : ℕ) : 0 ≤ sbar S cap n :=
  Finset.sum_nonneg fun k _ => mul_nonneg (S.row_nonneg k) (hitExp_nonneg n _)

theorem sbar_mono : Monotone (sbar S cap) := by
  intro a b hab
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (hitExp_mono hab _) (S.row_nonneg k)

/-- **The defect, in closed form.** `u_{n+1} − P⋆u_n` is `1` at every ladder state, `0` at `s₀`
and `−σ̄⁽ⁿ⁾` at `s_f`; as a function it is `1 − 1_{\{s₀\}} − (1+σ̄⁽ⁿ⁾) 1_{\{s_f\}}`. -/
theorem hitExp_defect (n : ℕ) :
    (fun x => hitExp S cap (n + 1) x - pstar S cap (hitExp S cap n) x)
      = fun x => 1 - ptFn (.lad 0) x - (1 + sbar S cap n) * ptFn .sink x := by
  funext x
  rcases x with j | _
  · rcases j with _ | j
    · rw [hitExp_src, pstar_src, hitExp_sink, ptFn_self, ptFn_of_ne (by simp)]
      ring
    · rw [hitExp_succ_lad, ptFn_of_ne (by simp), ptFn_of_ne (by simp)]
      ring
  · rw [hitExp_sink, pstar_sink, ptFn_of_ne (by simp), ptFn_self, sbar]
    ring

/-! ### Kac's formula -/

namespace Stat

variable (L : Stat S cap)

/-- `aₙ = ∫ E(σ ∧ n) dλ`. -/
noncomputable def hitInt (n : ℕ) : ℝ := ∑' x, L.lam x * hitExp S cap n x

theorem hitInt_mono : Monotone L.hitInt := by
  intro a b hab
  refine Summable.tsum_le_tsum (fun x => ?_) (L.summable_mul (hitExp_bounded a))
    (L.summable_mul (hitExp_bounded b))
  exact mul_le_mul_of_nonneg_left (hitExp_mono hab x) (L.nonneg x)

/-- **The one-step identity.** `a_{n+1} − a_n = 1 − λ(s₀) − (1 + σ̄⁽ⁿ⁾) λ(s_f)`. -/
theorem hitInt_succ_sub (n : ℕ) :
    L.hitInt (n + 1) - L.hitInt n
      = 1 - L.lam (.lad 0) - (1 + sbar S cap n) * L.lam .sink := by
  have hs1 := L.summable_mul (hitExp_bounded (S := S) (cap := cap) (n + 1))
  have hpb : ∃ C, ∀ x, |pstar S cap (hitExp S cap n) x| ≤ C := by
    obtain ⟨C, hC⟩ := hitExp_bounded (S := S) (cap := cap) n
    exact ⟨C, fun x => pstar_bounded hC x⟩
  have hs2 := L.summable_mul hpb
  have hsplit : (fun x => L.lam x * (hitExp S cap (n + 1) x - pstar S cap (hitExp S cap n) x))
      = fun x => L.lam x * hitExp S cap (n + 1) x - L.lam x * pstar S cap (hitExp S cap n) x := by
    funext x; ring
  have hleft : ∑' x, L.lam x * (hitExp S cap (n + 1) x - pstar S cap (hitExp S cap n) x)
      = L.hitInt (n + 1) - L.hitInt n := by
    rw [hsplit, Summable.tsum_sub hs1 hs2, hitInt, hitInt,
      L.inv (hitExp S cap n) (hitExp_bounded n)]
  have hright : HasSum
      (fun x => L.lam x * (1 - ptFn (.lad 0) x - (1 + sbar S cap n) * ptFn .sink x))
      (1 - L.lam (.lad 0) - (1 + sbar S cap n) * L.lam .sink) := by
    have hexp : (fun x => L.lam x * (1 - ptFn (.lad 0) x - (1 + sbar S cap n) * ptFn .sink x))
        = fun x => L.lam x - L.lam x * ptFn (.lad 0) x
            - (1 + sbar S cap n) * (L.lam x * ptFn .sink x) := by
      funext x; ring
    rw [hexp]
    exact (L.hasSum_one.sub (hasSum_lam_mul_ptFn L (.lad 0))).sub
      ((hasSum_lam_mul_ptFn L .sink).mul_left _)
  have hpt : ∀ x, L.lam x * (hitExp S cap (n + 1) x - pstar S cap (hitExp S cap n) x)
      = L.lam x * (1 - ptFn (.lad 0) x - (1 + sbar S cap n) * ptFn .sink x) := by
    intro x; rw [congrFun (hitExp_defect (S := S) (cap := cap) n) x]
  rw [← hleft, tsum_congr hpt, hright.tsum_eq]

/-- **Kac's formula on the doubling graph.** With `σ̄ := ⨆ₙ σ̄⁽ⁿ⁾`, `λ(s₀)(2 + σ̄) = 1`.

The hypothesis `hM` — the truncated hitting expectations are uniformly bounded in the `λ`-mean —
holds on every truncation, with `M = K/(1−c)` by `lem:doubling_supersolution`. -/
theorem kac_identity {M B : ℝ} (hM : ∀ n : ℕ, L.hitInt n ≤ M)
    (hB : ∀ n : ℕ, sbar S cap n ≤ B) :
    L.lam (.lad 0) * (2 + ⨆ n, sbar S cap n) = 1 := by
  -- `aₙ` converges, so its increments tend to `0`
  have hbdd : BddAbove (Set.range L.hitInt) := ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  have ha : Tendsto L.hitInt atTop (𝓝 (⨆ n, L.hitInt n)) :=
    tendsto_atTop_ciSup L.hitInt_mono hbdd
  have hashift : Tendsto (fun n => L.hitInt (n + 1)) atTop (𝓝 (⨆ n, L.hitInt n)) :=
    ha.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun n => L.hitInt (n + 1) - L.hitInt n) atTop (𝓝 0) := by
    simpa using hashift.sub ha
  -- `σ̄⁽ⁿ⁾` converges to its supremum
  have hbdd2 : BddAbove (Set.range (sbar S cap)) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  have hs : Tendsto (sbar S cap) atTop (𝓝 (⨆ n, sbar S cap n)) :=
    tendsto_atTop_ciSup sbar_mono hbdd2
  -- pass to the limit in the one-step identity
  have hrhs : Tendsto (fun n => 1 - L.lam (.lad 0) - (1 + sbar S cap n) * L.lam .sink) atTop
      (𝓝 (1 - L.lam (.lad 0) - (1 + ⨆ n, sbar S cap n) * L.lam .sink)) := by
    exact (tendsto_const_nhds.sub
      (((tendsto_const_nhds.add hs)).mul_const (L.lam .sink)))
  have heq : (0 : ℝ) = 1 - L.lam (.lad 0) - (1 + ⨆ n, sbar S cap n) * L.lam .sink :=
    tendsto_nhds_unique (hdiff.congr fun n => L.hitInt_succ_sub n) hrhs
  rw [L.lam_sink_eq_src] at heq
  ring_nf at heq ⊢
  linarith [heq]

/-- **Step 6 of `cor:doubling_truncation`.** `λ_1 ≥ (2 + j̄/(1−c))^{-1}`, a bound free of `K`. -/
theorem lam_one_ge {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) {M : ℝ}
    (hM : ∀ n : ℕ, L.hitInt n ≤ M) :
    (2 + S.jbar / (1 - c))⁻¹ ≤ L.lam (.lad 1) := by
  have hjb : 0 ≤ S.jbar :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (S.row_nonneg k)
  have hcne : (0 : ℝ) < 1 - c := by linarith
  have hB : ∀ n : ℕ, sbar S cap n ≤ S.jbar / (1 - c) := fun n => sigmaBar_le hc0 hc1 heps n
  have hkac := L.kac_identity hM hB
  have hsup_le : (⨆ n, sbar S cap n) ≤ S.jbar / (1 - c) :=
    ciSup_le fun n => hB n
  have hsup_nn : (0 : ℝ) ≤ ⨆ n, sbar S cap n :=
    le_ciSup_of_le ⟨S.jbar / (1 - c), by rintro _ ⟨n, rfl⟩; exact hB n⟩ 0 (sbar_nonneg 0)
  have hden : (0 : ℝ) < 2 + S.jbar / (1 - c) := by positivity
  have hsrc : (2 + S.jbar / (1 - c))⁻¹ ≤ L.lam (.lad 0) := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith [hkac, hsup_le, hsup_nn, L.nonneg (St.lad 0)]
  exact le_trans hsrc L.lam_src_le_lam_one

end Stat

end GFNBounds.Doubling
