import GFNBounds.Doubling.Setting

/-!
# Total variation as a finite sum, and the Doeblin contraction

Support for **`lem:doubling_coupling`** — `app_doubling.tex:1475–1533` — and for the two
"profiles of one block differ by little" steps of **`theo:doubling_sharp`** —
`app_doubling.tex:1323–1341`, proof at `1535–1658`.

> (coupling) with `ω` and `ℓ₄` of `lem:doubling_doeblin`, for every `i ≥ 0` and every pair of
> states `y, y' ∈ I_i(ℓ)`, `TV(P(Y_{N_ℓ} ∈ · | Y_0=y) ‖ P(Y_{N_ℓ} ∈ · | Y_0=y')) ≤ (1−ω)^i`,
> the total variation carrying the ½-convention of §`app:notation`.

## The modelling decision

Mathlib v4.31.0 has no total-variation distance for kernels, and none is built. The descent
leaves its base block `[ℓ,2ℓ)` at one of **finitely many** states, so every law in this block is
a function `ℕ → ℝ` supported on one `Finset`, and the ½-convention total variation is literally

  `tvOn F μ ν = ½ ∑_{k ∈ F} |μ k − ν k|`.

Everything below is then finite linear algebra over `ℝ`. Two facts carry the block:

* `tvOn_mix_le` — the **Doeblin contraction**. It is the third and fourth bullets of the proof of
  `lem:doubling_coupling`, stated without any chain: if two probabilities `μ, μ'` on a finite `G`
  both dominate one non-negative `ν` of mass `ω`, and a family `(π_z)_{z ∈ G}` of laws has
  `TV(π_z ‖ π_{z'}) ≤ B` throughout `G`, then the two mixtures are within `(1−ω)B`. The paper's
  `μ̃_y := (μ_y − ω ϖ)/(1−ω)` is `α := μ − ν` here, unnormalised, which removes the division.
* `abs_sum_sub_le` — the displayed inequality
  `|∫ f d(π−π')| ≤ (sup f − inf f) TV(π‖π')` of the first bullet of the proof of
  `theo:doubling_sharp`, with the paper's own centring `f − ½(sup f + inf f)`.

## SCOPE (disclosed)

This file is about `tvOn` alone; it references no descent chain and no doubling graph. It proves
none of `lem:doubling_coupling` by itself — the chain-level statement is `Coupling.lean`, which
supplies the mixture identity that `tvOn_mix_le` consumes.

`tvOn` is a distance between *functions* `ℕ → ℝ` relative to a `Finset`, not between measures: no
hypothesis forces `μ` to vanish off `F`. Every consumer supplies laws carried by `F`, and the
statements that need `μ` to be a probability say so (`hμsum`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ω ∈ (0,1)` | ⚠ weakened to `0 ≤ ω < 1`; the contraction is vacuous but true at `ω = 0` |
| `μ_y ≥ ω ϖ_i` with `ϖ_i` a probability | ⚠ weakened: `ν ≤ μ` pointwise on `G` with `∑_G ν = ω`, which is that hypothesis with `ν := ω ϖ_i` and needs no normalisation |
| `μ_y` a probability carried by `I_{i-1}(ℓ)` | ✓ carried (`hμsum`, and `G` is the block) |
| `I_{i-1}(ℓ)` finite | ✓ carried, `G` being a `Finset` |
| the ½-convention | ✓ carried, in `tvOn`'s definition |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

/-- **Total variation, ½-convention.** `tvOn F μ ν = ½ ∑_{k ∈ F} |μ k − ν k|`. -/
noncomputable def tvOn (F : Finset ℕ) (μ ν : ℕ → ℝ) : ℝ :=
  (1 / 2) * ∑ k ∈ F, |μ k - ν k|

theorem tvOn_nonneg (F : Finset ℕ) (μ ν : ℕ → ℝ) : 0 ≤ tvOn F μ ν := by
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => abs_nonneg _)

theorem tvOn_self (F : Finset ℕ) (μ : ℕ → ℝ) : tvOn F μ μ = 0 := by
  simp [tvOn]

theorem tvOn_comm (F : Finset ℕ) (μ ν : ℕ → ℝ) : tvOn F μ ν = tvOn F ν μ := by
  refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun k _ => ?_)
  rw [abs_sub_comm]

/-- The sum form: `∑_{k ∈ F} |μ k − ν k| = 2 · tvOn F μ ν`, the ½-convention read backwards. -/
theorem sum_abs_eq (F : Finset ℕ) (μ ν : ℕ → ℝ) :
    ∑ k ∈ F, |μ k - ν k| = 2 * tvOn F μ ν := by
  rw [tvOn]; ring

/-- Two probabilities carried by `F` are at total variation at most `1`. -/
theorem tvOn_le_one {F : Finset ℕ} {μ ν : ℕ → ℝ} (hμ : ∀ k ∈ F, 0 ≤ μ k)
    (hν : ∀ k ∈ F, 0 ≤ ν k) (hμs : ∑ k ∈ F, μ k = 1) (hνs : ∑ k ∈ F, ν k = 1) :
    tvOn F μ ν ≤ 1 := by
  have hstep : ∑ k ∈ F, |μ k - ν k| ≤ ∑ k ∈ F, (μ k + ν k) := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hν k hk], by linarith [hμ k hk]⟩
  rw [Finset.sum_add_distrib, hμs, hνs] at hstep
  rw [tvOn]
  linarith

/-- **The displayed inequality of `theo:doubling_sharp`, first bullet.**
`|∫ f d(π − π')| ≤ (sup f − inf f) · TV(π ‖ π')`, for `f` ranged between `lo` and `hi` on `F` and
`π, π'` of equal mass. The proof is the paper's: centre `f` at `½(hi + lo)`, which the equal
masses allow, and bound the centred integrand by `½(hi − lo)`. -/
theorem abs_sum_sub_le {F : Finset ℕ} {π π' f : ℕ → ℝ} {lo hi : ℝ}
    (hF : F.Nonempty) (hf : ∀ k ∈ F, lo ≤ f k ∧ f k ≤ hi)
    (hmass : ∑ k ∈ F, π k = ∑ k ∈ F, π' k) :
    |∑ k ∈ F, f k * (π k - π' k)| ≤ (hi - lo) * tvOn F π π' := by
  obtain ⟨k₀, hk₀⟩ := hF
  have hle : lo ≤ hi := le_trans (hf k₀ hk₀).1 (hf k₀ hk₀).2
  set c : ℝ := (hi + lo) / 2 with hc
  have hzero : ∑ k ∈ F, c * (π k - π' k) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hmass, sub_self, mul_zero]
  have hrw : ∑ k ∈ F, f k * (π k - π' k) = ∑ k ∈ F, (f k - c) * (π k - π' k) := by
    have : ∑ k ∈ F, (f k - c) * (π k - π' k)
        = (∑ k ∈ F, f k * (π k - π' k)) - ∑ k ∈ F, c * (π k - π' k) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hzero, sub_zero]
  rw [hrw]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ k ∈ F, |(f k - c) * (π k - π' k)| ≤ ((hi - lo) / 2) * |π k - π' k| := by
    intro k hk
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    obtain ⟨h1, h2⟩ := hf k hk
    rw [abs_le, hc]
    constructor <;> linarith
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, sum_abs_eq]
  nlinarith [tvOn_nonneg F π π']

/-- The mixture `∑_{z ∈ G} μ(z) π_z`, as a function on the states. -/
noncomputable def mix (G : Finset ℕ) (μ : ℕ → ℝ) (P : ℕ → ℕ → ℝ) : ℕ → ℝ :=
  fun k => ∑ z ∈ G, μ z * P z k

theorem mix_apply (G : Finset ℕ) (μ : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (k : ℕ) :
    mix G μ P k = ∑ z ∈ G, μ z * P z k := rfl

/-- **The Doeblin contraction.** Two probabilities on a finite `G` that both dominate one
non-negative `ν` of mass `ω < 1` mix a family of laws to within `(1 − ω)` times the family's own
diameter in total variation.

This is bullets three and four of the proof of `lem:doubling_coupling`, with the paper's
`μ̃ := (μ − ω ϖ)/(1 − ω)` replaced by the unnormalised `α := μ − ν`: the product measure
`α ⊗ β` has mass `(1 − ω)²`, and the identity
`(1−ω)(mix μ − mix μ') = ∑_{z,z'} α(z) β(z') (π_z − π_{z'})` is the paper's, cleared of its
denominator. -/
theorem tvOn_mix_le {F G : Finset ℕ} {μ μ' ν : ℕ → ℝ} {P : ℕ → ℕ → ℝ} {ω B : ℝ}
    (hω1 : ω < 1)
    (hν : ∀ z ∈ G, ν z ≤ μ z) (hν' : ∀ z ∈ G, ν z ≤ μ' z)
    (hνsum : ∑ z ∈ G, ν z = ω)
    (hμsum : ∑ z ∈ G, μ z = 1) (hμ'sum : ∑ z ∈ G, μ' z = 1)
    (hB : ∀ z ∈ G, ∀ z' ∈ G, tvOn F (P z) (P z') ≤ B) :
    tvOn F (mix G μ P) (mix G μ' P) ≤ (1 - ω) * B := by
  classical
  set r : ℝ := 1 - ω with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  set α : ℕ → ℝ := fun z => μ z - ν z with hα
  set β : ℕ → ℝ := fun z => μ' z - ν z with hβ
  have hαnn : ∀ z ∈ G, 0 ≤ α z := fun z hz => by rw [hα]; exact sub_nonneg.mpr (hν z hz)
  have hβnn : ∀ z ∈ G, 0 ≤ β z := fun z hz => by rw [hβ]; exact sub_nonneg.mpr (hν' z hz)
  have hαsum : ∑ z ∈ G, α z = r := by
    rw [hα, Finset.sum_sub_distrib, hμsum, hνsum, hr]
  have hβsum : ∑ z ∈ G, β z = r := by
    rw [hβ, Finset.sum_sub_distrib, hμ'sum, hνsum, hr]
  -- `B ≥ 0`, since `G` is nonempty and `tvOn F (P z) (P z) = 0`.
  have hGne : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hG
    rw [hG, Finset.sum_empty] at hμsum
    norm_num at hμsum
  obtain ⟨z₀, hz₀⟩ := hGne
  have hB0 : 0 ≤ B := le_trans (le_of_eq (tvOn_self F (P z₀)).symm) (hB z₀ hz₀ z₀ hz₀)
  -- the paper's identity, cleared of its denominator
  have hkey : ∀ k : ℕ,
      r * (mix G μ P k - mix G μ' P k)
        = ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * (P z k - P z' k) := by
    intro k
    have hsplit : ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * (P z k - P z' k)
        = (∑ z ∈ G, ∑ z' ∈ G, α z * β z' * P z k)
          - ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * P z' k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z' _ => by ring
    have h1 : ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * P z k = r * ∑ z ∈ G, α z * P z k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      have : ∑ z' ∈ G, α z * β z' * P z k = (∑ z' ∈ G, β z') * (α z * P z k) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun z' _ => by ring
      rw [this, hβsum]
    have h2 : ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * P z' k = r * ∑ z' ∈ G, β z' * P z' k := by
      have : ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * P z' k
          = ∑ z ∈ G, α z * ∑ z' ∈ G, β z' * P z' k := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z' _ => by ring
      rw [this, ← Finset.sum_mul, hαsum]
    have hmixdiff : mix G μ P k - mix G μ' P k
        = (∑ z ∈ G, α z * P z k) - ∑ z ∈ G, β z * P z k := by
      have e : ∑ z ∈ G, (α z * P z k - β z * P z k)
          = (∑ z ∈ G, α z * P z k) - ∑ z ∈ G, β z * P z k := Finset.sum_sub_distrib _ _
      have e2 : ∑ z ∈ G, (α z * P z k - β z * P z k)
          = ∑ z ∈ G, (μ z * P z k - μ' z * P z k) :=
        Finset.sum_congr rfl fun z _ => by rw [hα, hβ]; ring
      rw [← e, e2, Finset.sum_sub_distrib, mix_apply, mix_apply]
    rw [hsplit, h1, h2, hmixdiff, mul_sub]
  -- now sum the absolute values
  have hbound : r * (2 * tvOn F (mix G μ P) (mix G μ' P)) ≤ r * (2 * (r * B)) := by
    have hL : r * (2 * tvOn F (mix G μ P) (mix G μ' P))
        = ∑ k ∈ F, |r * (mix G μ P k - mix G μ' P k)| := by
      rw [← sum_abs_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [abs_mul, abs_of_pos hrpos]
    rw [hL]
    have hstep : ∀ k ∈ F, |r * (mix G μ P k - mix G μ' P k)|
        ≤ ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * |P z k - P z' k| := by
      intro k _
      rw [hkey k]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun z hz => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun z' hz' => ?_)
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hαnn z hz) (hβnn z' hz'))]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hcomm : ∑ k ∈ F, ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * |P z k - P z' k|
        = ∑ z ∈ G, ∑ z' ∈ G, ∑ k ∈ F, α z * β z' * |P z k - P z' k| := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_comm
    rw [hcomm]
    have hswap : ∑ z ∈ G, ∑ z' ∈ G, ∑ k ∈ F, α z * β z' * |P z k - P z' k|
        ≤ ∑ z ∈ G, ∑ z' ∈ G, α z * β z' * (2 * B) := by
      refine Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun z' hz' => ?_
      rw [← Finset.mul_sum, sum_abs_eq]
      exact mul_le_mul_of_nonneg_left
        (by linarith [hB z hz z' hz']) (mul_nonneg (hαnn z hz) (hβnn z' hz'))
    refine le_trans hswap (le_of_eq ?_)
    have hinner : ∀ z ∈ G, ∑ z' ∈ G, α z * β z' * (2 * B) = α z * (r * (2 * B)) := by
      intro z _
      have h : ∑ z' ∈ G, α z * β z' * (2 * B) = (α z * (2 * B)) * ∑ z' ∈ G, β z' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z' _ => by ring
      rw [h, hβsum]; ring
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, hαsum]
    ring
  have h2 : (2 : ℝ) * tvOn F (mix G μ P) (mix G μ' P) ≤ 2 * (r * B) :=
    le_of_mul_le_mul_left hbound hrpos
  linarith

/-- The geometric iteration of `lem:doubling_coupling`, as pure arithmetic: a family of
diameters that contracts by `(1 − ω)` at each step and starts at most `1` is at most `(1 − ω)^i`.
`Coupling.lean` supplies the two hypotheses from the descent recursion. -/
theorem geom_iterate {Δ : ℕ → ℝ} {ω : ℝ} (hω1 : ω < 1)
    (h0 : Δ 0 ≤ 1) (hstep : ∀ i, Δ (i + 1) ≤ (1 - ω) * Δ i) :
    ∀ i, Δ i ≤ (1 - ω) ^ i := by
  intro i
  induction i with
  | zero => simpa using h0
  | succ n ih =>
      have hpos : (0 : ℝ) ≤ 1 - ω := by linarith
      calc Δ (n + 1) ≤ (1 - ω) * Δ n := hstep n
        _ ≤ (1 - ω) * (1 - ω) ^ n := mul_le_mul_of_nonneg_left ih hpos
        _ = (1 - ω) ^ (n + 1) := by ring

end GFNBounds.Doubling
