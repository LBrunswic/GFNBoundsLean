import GFNBounds.Doubling.Excursion
import GFNBounds.Doubling.Drift

/-!
# The linear supersolution

**`lem:doubling_supersolution`** — `app_doubling.tex:426–474`.

> Let `s = 1` and `0 < c < 1`, put `h(j) := j/(1−c)` and `h(s₀) := 0`. Then
> `h(j) = 1 + ε(j)h(2j) + (1−ε(j))h(j−1)` on the loop closure; on the truncation at `K`,
> `h(j) ≥ 1 + E(h(X₁)|X₀=j)` for `1 ≤ j ≤ K`, with equality for `2j ≤ K`. Consequently, on both
> chains, `E(σ|X₀=j) ≤ j/(1−c) < +∞`, so `σ < ∞` a.s., and `σ̄ ≤ j̄/(1−c)`, `σ̄_K ≤ j̄/(1−c)`.

## The modelling decision

The paper's Step 3 introduces `u_n(x) := E(σ ∧ n | X₀ = x)` and proves `u_n ≤ h` by induction on
`n` from `u_{n+1}(j) = 1 + E(u_n(X₁) | X₀ = j)`. That recursion is **taken as the definition**
here: `hitExp S cap n` is `u_n`, defined by the same recursion with `P⋆`, so Step 3 is a plain
induction. `E(σ | X₀ = j)` is then `sup_n u_n`, and `hitExp_iSup_le` is the paper's conclusion.

## SCOPE (disclosed)

* `E(σ ∧ n)` is *defined* by its one-step recursion rather than derived from a chain. That is the
  same modelling decision as `pstar` itself, and the recursion is the paper's own display; what is
  not formalized is that this recursion computes the expectation of a stopping time, since no
  chain is built.
* Monotone convergence `σ ∧ n ↑ σ` becomes `hitExp_mono` plus `ciSup`: the supremum exists because
  the sequence is bounded by `h`, which is the lemma's own conclusion.
* `σ < ∞` almost surely does **not** appear: it is a statement about the law of `σ`, and its
  content here — that the expected hitting time is finite — is `hitExp_iSup_le`.
* Both chains are covered by the `cap` parameter, and the truncation case is the inequality, with
  equality for `2j ≤ K`, exactly as in the paper.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s = 1`, `0 < c < 1` | ✓ carried as `heps` and `hc0`, `hc1` |
| `K ≥ d` | ⚠ weakened: not needed; the inequality holds at every cap |
| `j ≥ 1` | ✓ carried |
| the target row has mean `j̄` | ✓ carried (`Setting.jbar`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

variable {S : Setting} {cap : Option ℕ}

/-- `P⋆` is monotone: it is an average over the one-step law. -/
theorem pstar_mono {f g : St → ℝ} (h : ∀ x, f x ≤ g x) (x : St) :
    pstar S cap f x ≤ pstar S cap g x := by
  rcases x with j | _
  · rcases j with _ | j
    · exact h _
    · by_cases hD : HasDouble cap (j + 1)
      · simp only [pstar_lad_succ, hD, if_true]
        have h1 : 0 ≤ S.eps (j + 1) := (S.eps_pos (Nat.le_add_left 1 j)).le
        have h2 : 0 ≤ 1 - S.eps (j + 1) := (S.one_sub_eps_pos (Nat.le_add_left 1 j)).le
        have := h (St.lad (2 * (j + 1)))
        have := h (St.lad j)
        nlinarith
      · simp only [pstar_lad_succ, hD, if_false]; exact h _
  · exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h _) (S.row_nonneg k)

/-- The linear supersolution `h(j) = j/(1−c)`, with `h(s₀) = h(s_f) = 0`. -/
noncomputable def linSuper (c : ℝ) : St → ℝ := fun x => height x / (1 - c)

theorem linSuper_nonneg {c : ℝ} (hc1 : c < 1) (x : St) : 0 ≤ linSuper c x := by
  have hc : (0 : ℝ) < 1 - c := by linarith
  rcases x with j | _
  · rw [linSuper, height_lad]; positivity
  · rw [linSuper, height_sink, zero_div]

theorem linSuper_lad {c : ℝ} (j : ℕ) : linSuper c (.lad j) = (j : ℝ) / (1 - c) := rfl

/-- **`eq:doubling_super`, Step 1.** On the loop closure, and at every state of the truncation
carrying its doubling edge, `h` solves the one-step equation exactly. -/
theorem linSuper_eq {c : ℝ} (hc1 : c < 1) (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1))
    {m : ℕ} (hm : 1 ≤ m) (hD : HasDouble cap m) :
    linSuper c (.lad m) = 1 + pstar S cap (linSuper c) (.lad m) := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hb : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hcne : (1 : ℝ) - c ≠ 0 := by linarith
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := hm
    push_cast [Nat.cast_sub this]; ring
  rw [pstar_lad_of_hasDouble hm hD, heps m hm, linSuper_lad, linSuper_lad, linSuper_lad, hcast]
  push_cast
  field_simp
  ring

/-- **`eq:doubling_super`, Step 2.** Where the doubling edge has been truncated away, `h` is a
strict supersolution: the decrement carries the whole mass and `1 ≤ 1/(1−c)`. -/
theorem linSuper_ge {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {m : ℕ} (hm : 1 ≤ m)
    (hD : ¬ HasDouble cap m) :
    1 + pstar S cap (linSuper c) (.lad m) ≤ linSuper c (.lad m) := by
  have hcne : (0 : ℝ) < 1 - c := by linarith
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := hm
    push_cast [Nat.cast_sub this]; ring
  rw [pstar_lad_of_not_hasDouble hm hD, linSuper_lad, linSuper_lad, hcast]
  have hgap : (m : ℝ) / (1 - c) - ((m : ℝ) - 1) / (1 - c) = 1 / (1 - c) := by
    field_simp; ring
  have h1 : (1 : ℝ) ≤ 1 / (1 - c) := by rw [le_div_iff₀ hcne]; linarith
  linarith

/-- `E(σ ∧ n | X₀ = ·)`, defined by the recursion of Step 3: `u_0 = 0`, `u_n(s₀) = 0` and
`u_{n+1}(j) = 1 + E(u_n(X₁) | X₀ = j)` at a ladder state `j ≥ 1`. -/
noncomputable def hitExp (S : Setting) (cap : Option ℕ) : ℕ → St → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      match x with
      | .lad 0 => 0
      | .sink => 0
      | .lad (j + 1) => 1 + pstar S cap (hitExp S cap n) (.lad (j + 1))

@[simp] theorem hitExp_zero (x : St) : hitExp S cap 0 x = 0 := rfl
@[simp] theorem hitExp_src (n : ℕ) : hitExp S cap n (.lad 0) = 0 := by cases n <;> rfl
@[simp] theorem hitExp_sink (n : ℕ) : hitExp S cap n .sink = 0 := by cases n <;> rfl

theorem hitExp_succ_lad (n j : ℕ) :
    hitExp S cap (n + 1) (.lad (j + 1)) = 1 + pstar S cap (hitExp S cap n) (.lad (j + 1)) := rfl

theorem hitExp_nonneg (n : ℕ) (x : St) : 0 ≤ hitExp S cap n x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rcases x with j | _
      · rcases j with _ | j
        · simp
        · rw [hitExp_succ_lad]
          have := pstar_nonneg (f := hitExp S cap n) (S := S) (cap := cap) (fun y => ih y)
            (St.lad (j + 1))
          linarith
      · simp

/-- **Step 3.** A non-negative supersolution dominates the truncated hitting expectations. -/
theorem hitExp_le_linSuper {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (n : ℕ) (x : St) :
    hitExp S cap n x ≤ linSuper c x := by
  induction n generalizing x with
  | zero => simpa using linSuper_nonneg hc1 x
  | succ n ih =>
      rcases x with j | _
      · rcases j with _ | j
        · simp [linSuper_lad]
        · rw [hitExp_succ_lad]
          have hmono : pstar S cap (hitExp S cap n) (.lad (j + 1))
              ≤ pstar S cap (linSuper c) (.lad (j + 1)) := pstar_mono ih _
          by_cases hD : HasDouble cap (j + 1)
          · rw [linSuper_eq hc1 heps (Nat.le_add_left 1 j) hD]
            linarith
          · have := linSuper_ge (S := S) (cap := cap) hc0 hc1 (Nat.le_add_left 1 j) hD
            linarith
      · simpa using linSuper_nonneg hc1 (St.sink)

/-- The truncated hitting expectations increase in `n` — `σ ∧ n ↑ σ`. -/
theorem hitExp_mono {n m : ℕ} (h : n ≤ m) (x : St) :
    hitExp S cap n x ≤ hitExp S cap m x := by
  induction m generalizing n x with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · have hnm : n ≤ m := by omega
        rcases n with _ | n
        · simpa using hitExp_nonneg (S := S) (cap := cap) (m + 1) x
        · rcases x with j | _
          · rcases j with _ | j
            · simp
            · rw [hitExp_succ_lad, hitExp_succ_lad]
              have : pstar S cap (hitExp S cap n) (.lad (j + 1))
                  ≤ pstar S cap (hitExp S cap m) (.lad (j + 1)) :=
                pstar_mono (fun y => ih (by omega) y) _
              linarith
          · simp

/-- **`lem:doubling_supersolution`, the conclusion.** `E(σ | X₀ = j) ≤ j/(1−c) < +∞` on both
chains: the supremum of the truncated hitting expectations is bounded by the supersolution. -/
theorem hitExp_iSup_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (x : St) :
    ⨆ n, hitExp S cap n x ≤ linSuper c x :=
  ciSup_le fun n => hitExp_le_linSuper hc0 hc1 heps n x

/-- **`σ̄ ≤ j̄/(1−c)`.** Averaging the bound over the target row, whose mean is `j̄`. -/
theorem sigmaBar_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (heps : ∀ j : ℕ, 1 ≤ j → S.eps j = c / ((j : ℝ) + 1)) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 S.d, S.row k * hitExp S cap n (.lad k) ≤ S.jbar / (1 - c) := by
  have hcne : (0 : ℝ) < 1 - c := by linarith
  have hstep : ∀ k ∈ Finset.Icc 1 S.d, S.row k * hitExp S cap n (.lad k)
      ≤ (k : ℝ) * S.row k / (1 - c) := by
    intro k _
    have hle := hitExp_le_linSuper (S := S) (cap := cap) hc0 hc1 heps n (St.lad k)
    rw [linSuper_lad] at hle
    have := mul_le_mul_of_nonneg_left hle (S.row_nonneg k)
    calc S.row k * hitExp S cap n (.lad k) ≤ S.row k * ((k : ℝ) / (1 - c)) := this
      _ = (k : ℝ) * S.row k / (1 - c) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_div, Setting.jbar]

end GFNBounds.Doubling
