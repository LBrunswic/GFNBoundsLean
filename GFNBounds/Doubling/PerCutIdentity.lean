import GFNBounds.Doubling.Setting

/-!
# The exact per-cut identity

**`lem:doubling_percut`, Step 2** — `app_doubling.tex:1848–1944`, `eq:doubling_step1`
(Lemma 122 of the ICLR build).

> `(Id − P⋆) 1_A = (1 − ε(m)) 1_{\{m\}} − Σ_{x=⌈m/2⌉}^{m−1} ε(x) 1_{\{x\}}`

with `A := [m, +∞)` on the loop closure and `A := [m, K]` on the truncation at `K`. This is the
identity the paper proves by "six cases" on the transitions, and it is the engine of the whole
unboundedness block: `theo:doubling_unbounded` reads off from it that
`‖(Id − P⋆)f_m‖ ≲ λ_m` while `‖f_m‖ ≳ L(m)`, and `prop:doubling_cut` is its `λ`-integral.

## Why this file comes before `prop:doubling_cut`

The appendix proves cut balance first, by a flux argument across the cut, and then re-derives the
same six-case analysis inside `lem:doubling_percut`. Here the order is inverted: the identity below
is **pointwise** — no summation, no invariance, no measure — so it is a case analysis and nothing
else, and `prop:doubling_cut` becomes its `λ`-integral in a few lines
(`GFNBounds.Doubling.CutBalance`). The mathematics is the paper's; only the order is changed, and
the change is recorded here because the dependency in `paper-map.json` runs the other way from the
`.tex`.

## SCOPE (disclosed)

The identity is asserted **on the chain** (`OnChain cap x`), which on the loop closure is every
state and on the truncation at `K` is the `K + 2` states `{s₀, 1, …, K, s_f}`. It genuinely fails
off the chain: at `x = lad (K+1)` with `m ≤ K` the left side is `−1` and the right side is `0`.
That is not a defect — those states carry no incoming edge from within the truncated chain, so
`λ` vanishes on them (`Stat.vanish`) and they contribute nothing to any integral or norm. The
paper avoids the issue by taking the truncation to *be* a chain on `K + 2` states; `St` is one
type serving both, so the restriction is explicit here instead.

## Hypothesis checklist against `lem:doubling_percut`

| paper hypothesis | here |
|---|---|
| `ε(j) > 0` for every `j ≥ 1` | ✓ carried (in `Setting`) |
| `ε_max < 1` | ✓ carried (in `Setting`), though Step 2 does not use it |
| case (1): loop closure, positive recurrent, `m > d` | ✓ `cap = none`, `hdm`; positive recurrence is not needed for the identity |
| case (2): `K ≥ d` even, `d < m ≤ K/2` | ✓ `cap = some K`, `hdm`, and `hD : HasDouble cap m` **is** `2m ≤ K` |
| — | ⚠ weakened: evenness of `K` is not needed here (it is needed for irreducibility, not for this identity) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

/-- Membership of the tail set `A`: `[m, +∞)` on the loop closure, `[m, K]` on the truncation. -/
def inTail : Option ℕ → ℕ → ℕ → Prop
  | none, m, j => m ≤ j
  | some K, m, j => m ≤ j ∧ j ≤ K

instance : ∀ (cap : Option ℕ) (m j : ℕ), Decidable (inTail cap m j)
  | none, m, j => inferInstanceAs (Decidable (m ≤ j))
  | some K, m, j => inferInstanceAs (Decidable (m ≤ j ∧ j ≤ K))

variable {cap : Option ℕ} {m j : ℕ}

theorem inTail_of (h : m ≤ j) (hx : OnChain cap (.lad j)) : inTail cap m j := by
  cases cap with
  | none => exact h
  | some K => exact ⟨h, hx⟩

theorem not_inTail_of_lt (h : j < m) : ¬ inTail cap m j := by
  cases cap with
  | none => exact fun hc => absurd (show m ≤ j from hc) (by omega)
  | some K => exact fun hc => absurd (show m ≤ j from hc.1) (by omega)

/-- `1_A`, the indicator of the tail set. -/
def tailInd (cap : Option ℕ) (m : ℕ) : St → ℝ
  | .lad j => if inTail cap m j then 1 else 0
  | .sink => 0

@[simp] theorem tailInd_sink : tailInd cap m .sink = 0 := rfl

theorem tailInd_lad (j : ℕ) : tailInd cap m (.lad j) = if inTail cap m j then 1 else 0 := rfl

theorem tailInd_one (h : inTail cap m j) : tailInd cap m (.lad j) = 1 := by
  simp [tailInd_lad, h]

theorem tailInd_zero (h : ¬ inTail cap m j) : tailInd cap m (.lad j) = 0 := by
  simp [tailInd_lad, h]

theorem tailInd_nonneg (x : St) : 0 ≤ tailInd cap m x := by
  rcases x with j | _
  · rw [tailInd_lad]; split <;> norm_num
  · simp

theorem tailInd_le_one (x : St) : tailInd cap m x ≤ 1 := by
  rcases x with j | _
  · rw [tailInd_lad]; split <;> norm_num
  · simp

theorem tailInd_bounded : ∃ C, ∀ x, |tailInd cap m x| ≤ C :=
  ⟨1, fun x => by rw [abs_of_nonneg (tailInd_nonneg x)]; exact tailInd_le_one x⟩

/-- The point mass at the ladder state `j`, as a function on `St`. -/
def dirac (j : ℕ) : St → ℝ := fun x => if x = .lad j then 1 else 0

@[simp] theorem dirac_sink (j : ℕ) : dirac j .sink = 0 := by simp [dirac]

@[simp] theorem dirac_lad (i j : ℕ) : dirac j (.lad i) = if i = j then 1 else 0 := by
  simp [dirac]

/-- The right-hand side of `eq:doubling_step1`:
`(1 − ε(m)) 1_{\{m\}} − Σ_{x ∈ W(m)} ε(x) 1_{\{x\}}`. -/
noncomputable def cutFn (S : Setting) (m : ℕ) : St → ℝ := fun x =>
  (1 - S.eps m) * dirac m x - ∑ y ∈ window m, S.eps y * dirac y x

@[simp] theorem cutFn_sink (S : Setting) (m : ℕ) : cutFn S m .sink = 0 := by
  simp [cutFn]

/-- The window sum collapses to a single term, by `Finset.sum_ite_eq`. -/
theorem sum_eps_dirac (S : Setting) (m j : ℕ) :
    ∑ y ∈ window m, S.eps y * dirac y (.lad j) = if j ∈ window m then S.eps j else 0 := by
  simp only [dirac_lad, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq (window m) j S.eps

theorem cutFn_lad (S : Setting) (m j : ℕ) :
    cutFn S m (.lad j) =
      (1 - S.eps m) * (if j = m then 1 else 0) - (if j ∈ window m then S.eps j else 0) := by
  rw [cutFn, dirac_lad, sum_eps_dirac]

/-- **`eq:doubling_step1`.** The flow-matching defect of the tail indicator is exactly a point mass
of size `1 − ε(m)` at the cut, minus the doubling weights of the window below it.

The six cases of the paper, in order of appearance below: the source, the sink, a state strictly
above the cut, the cut itself, a state of the window, and a state below the window. -/
theorem percut_id (S : Setting) (cap : Option ℕ) {m : ℕ} (hdm : S.d < m)
    (hD : HasDouble cap m) {x : St} (hx : OnChain cap x) :
    tailInd cap m x - pstar S cap (tailInd cap m) x = cutFn S m x := by
  have hd1 : 1 ≤ S.d := S.d_pos
  have hm1 : 1 ≤ m := by omega
  have hhalf : 1 ≤ (m + 1) / 2 := by omega
  rcases x with (_ | n) | _
  · -- the source `s₀ = lad 0`: outside `A`, and it steps to the sink, which is outside `A`
    rw [pstar_src, tailInd_sink, tailInd_zero (not_inTail_of_lt (show 0 < m by omega)), cutFn_lad]
    have h0 : (0 : ℕ) ∉ window m := fun hc => absurd (mem_window.mp hc).1 (by omega)
    rw [if_neg (show ¬ (0 = m) by omega), if_neg h0]
    ring
  · -- a ladder state `n + 1`
    rcases lt_trichotomy (n + 1) m with hlt | heq | hgt
    · -- strictly below the cut: the state and its decrement are both outside `A`
      have hDj : HasDouble cap (n + 1) := hasDouble_mono hD (by omega)
      rw [pstar_lad_succ, if_pos hDj, cutFn_lad, if_neg (show ¬ (n + 1 = m) by omega),
        tailInd_zero (not_inTail_of_lt hlt),
        tailInd_zero (not_inTail_of_lt (show n < m by omega))]
      by_cases hw : n + 1 ∈ window m
      · -- a state of the window `W(m)`: its doubling edge lands at or above the cut
        have h2 : m ≤ 2 * (n + 1) := by have := (mem_window.mp hw).1; omega
        rw [tailInd_one (inTail_of h2 (onChain_double hDj)), if_pos hw]
        ring
      · -- below the window: the doubling edge still lands below the cut
        have h2 : 2 * (n + 1) < m := by rw [mem_window] at hw; omega
        rw [tailInd_zero (not_inTail_of_lt h2), if_neg hw]
        ring
    · -- the cut itself: `n + 1 = m`, the one state where the defect is `1 − ε(m)`
      subst heq
      have hDj : HasDouble cap (n + 1) := hD
      have hw : n + 1 ∉ window (n + 1) := by rw [mem_window]; omega
      rw [pstar_lad_succ, if_pos hDj, cutFn_lad, if_pos rfl, if_neg hw,
        tailInd_one (inTail_of le_rfl (onChain_lad_of_hasDouble hD le_rfl)),
        tailInd_one (inTail_of (show n + 1 ≤ 2 * (n + 1) by omega) (onChain_double hDj)),
        tailInd_zero (not_inTail_of_lt (show n < n + 1 by omega))]
      ring
    · -- strictly above the cut: the state, its decrement and its doubling all lie inside `A`
      have hAn1 : inTail cap m (n + 1) := inTail_of (by omega) hx
      have hAn : inTail cap m n := by
        refine inTail_of (by omega) ?_
        cases cap with
        | none => trivial
        | some K => show n ≤ K; exact le_trans (by omega) (hx : n + 1 ≤ K)
      have hw : n + 1 ∉ window m := fun hc => absurd (mem_window.mp hc).2 (by omega)
      rw [pstar_lad_succ, tailInd_one hAn1, cutFn_lad,
        if_neg (show ¬ (n + 1 = m) by omega), if_neg hw]
      by_cases hDj : HasDouble cap (n + 1)
      · rw [if_pos hDj, tailInd_one (inTail_of (by omega) (onChain_double hDj)), tailInd_one hAn]
        ring
      · rw [if_neg hDj, tailInd_one hAn]
        ring
  · -- the sink: it fires the target row, supported in `{1, …, d}`, entirely below the cut
    rw [pstar_sink, tailInd_sink, cutFn_sink]
    have hrow : ∀ k ∈ Finset.Icc 1 S.d, S.row k * tailInd cap m (.lad k) = 0 := by
      intro k hk
      have hk2 : k < m := by have := (Finset.mem_Icc.mp hk).2; omega
      rw [tailInd_zero (not_inTail_of_lt hk2), mul_zero]
    rw [Finset.sum_congr rfl hrow, Finset.sum_const_zero, sub_zero]

end GFNBounds.Doubling
