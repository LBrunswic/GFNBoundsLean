import GFNBounds.Doubling.Doeblin
import GFNBounds.Doubling.TotalVariation

/-!
# `lem:doubling_coupling`: two descents from one block reach the base block with nearly the same law

**`lem:doubling_coupling`** — `app_doubling.tex:1475–1533`.

> In the setting of Definitions `def:doubling_setting` and `def:doubling_decay_notation`, with `ω`
> and the integer `ℓ₄` of `lem:doubling_doeblin`, let `ℓ ≥ ℓ₄` be an integer and let `(Y_n)` and
> `N_ℓ` be the descent chain at the level `ℓ` and its exit time. Then, for every integer `i ≥ 0`
> and every pair of states `y, y' ∈ I_i(ℓ)`,
> `TV(P(Y_{N_ℓ} ∈ · | Y_0=y) ‖ P(Y_{N_ℓ} ∈ · | Y_0=y')) ≤ (1−ω)^i`,
> the total variation carrying the ½-convention of §`app:notation`.

## What the proof is here

Exactly the paper's four bullets, with each supplied by a file that owes nothing to a chain:

| paper bullet | here |
|---|---|
| the claim at `i = 0`: two Dirac masses | `TotalVariation.tvOn_le_one`, from `DescentLaw.exitLaw_sum` — no Dirac needed, only that both are probabilities on `[ℓ,2ℓ)` |
| `μ̃_y := (μ_y − ω ϖ_i)/(1−ω)` is a probability on `I_{i−1}(ℓ)` | `Doeblin.doeblin` and `Doeblin.varpi_sum`, fed to `tvOn_mix_le` **unnormalised** |
| `π_y = ∑_{z ∈ I_{i−1}(ℓ)} μ_y(z) π_z`, by the strong Markov property at `ς` | `DescentLaw.exitLaw_mix`, a strong induction on `y` |
| the claim at `i−1` implies the claim at `i` | `TotalVariation.tvOn_mix_le` |

The induction is on `i` and is stated in the paper's own form — "the claim at `i` being that
`TV(π_y‖π_{y'}) ≤ (1−ω)^i` for every pair `y, y' ∈ I_i(ℓ)`" — so no supremum over the block is
formed and `geom_iterate` is not needed.

## SCOPE (disclosed)

* `π_z` is the exit law of the **recursion** `DescentLaw.descP`, not of a stochastic process; see
  the SCOPE of `DescentLaw.lean`. Given that reading, `eq:doubling_coupling` is proved in full,
  unconditionally, at every `i ≥ 0`.
* The paper's `ℓ ≥ ℓ₄` is the pair `20 ≤ ℓ` and `32cτ ≤ ℓ`, both effective; see `Doeblin.lean`.
  The first is `18` in the paper and `20` here.
* `ω` is the paper's `(c²/16) ln(5/4) ln(8/5)` exactly, and is bounded below by `3c²/640`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `0 < c < 1`, `s = 1`, `p = p_*` | ✓ carried (`Decay`) |
| `ℓ ≥ ℓ₄` | ⚠ **strengthened/replaced** by `20 ≤ ℓ` and `32cτ ≤ ℓ`, both effective |
| `i ≥ 0`, `y, y' ∈ I_i(ℓ)` | ✓ carried |
| `ω ∈ (0,1)` | ✓ carried, and proved (`Doeblin.omeg_pos`, `Doeblin.omeg_lt_one`) |
| the ½-convention for `TV` | ✓ carried (`tvOn`) |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

open Real

namespace Decay

variable (D : Decay)

/-- `I_i(ℓ) = [a, 2a)` with `a = 2^i ℓ`. -/
theorem block_eq (i ℓ : ℕ) : block i ℓ = Finset.Ico (2 ^ i * ℓ) (2 * (2 ^ i * ℓ)) := by
  rw [block]
  congr 1
  ring

theorem le_pow_mul (i ℓ : ℕ) : ℓ ≤ 2 ^ i * ℓ :=
  Nat.le_mul_of_pos_left ℓ (pow_pos (by norm_num : 0 < 2) i)

/-- **`eq:doubling_coupling`.** Two descents started in `I_i(ℓ)` reach the base block `[ℓ,2ℓ)`
with laws at total variation at most `(1−ω)^i`.

By induction on `i`, exactly as the paper's proof. -/
theorem coupling {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hℓτ : 32 * D.c * D.tau ≤ (ℓ : ℝ)) :
    ∀ i : ℕ, ∀ y ∈ block i ℓ, ∀ y' ∈ block i ℓ,
      tvOn (Finset.Ico ℓ (2 * ℓ)) (D.exitLaw ℓ y) (D.exitLaw ℓ y') ≤ (1 - D.omeg) ^ i := by
  have hℓ1 : 1 ≤ ℓ := by omega
  intro i
  induction i with
  | zero =>
      intro y hy y' hy'
      rw [block, pow_zero, one_mul, pow_one] at hy hy'
      have hyl : ℓ ≤ y := (Finset.mem_Ico.mp hy).1
      have hyl' : ℓ ≤ y' := (Finset.mem_Ico.mp hy').1
      rw [pow_zero]
      exact tvOn_le_one (fun k _ => D.exitLaw_nonneg hℓ1 k y hyl)
        (fun k _ => D.exitLaw_nonneg hℓ1 k y' hyl') (D.exitLaw_sum hℓ1 hyl)
        (D.exitLaw_sum hℓ1 hyl')
  | succ i ih =>
      intro y hy y' hy'
      set a : ℕ := 2 ^ i * ℓ with hadef
      have hla : ℓ ≤ a := le_pow_mul i ℓ
      have ha1 : 1 ≤ a := le_trans hℓ1 hla
      have ha20 : 20 ≤ a := le_trans hℓ hla
      have haτ : 32 * D.c * D.tau ≤ (a : ℝ) := by
        refine le_trans hℓτ ?_
        exact_mod_cast (Nat.cast_le (α := ℝ)).mpr hla
      -- `I_{i+1}(ℓ) = [2a, 4a)`
      have hmem : ∀ z, z ∈ block (i + 1) ℓ ↔ 2 * a ≤ z ∧ z < 4 * a := by
        intro z
        rw [block, Finset.mem_Ico, hadef]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨by linarith [h1, (by ring : 2 ^ (i + 1) * ℓ = 2 * (2 ^ i * ℓ))], ?_⟩
          have e : 2 ^ (i + 1 + 1) * ℓ = 4 * (2 ^ i * ℓ) := by ring
          omega
        · rintro ⟨h1, h2⟩
          have e1 : 2 ^ (i + 1) * ℓ = 2 * (2 ^ i * ℓ) := by ring
          have e2 : 2 ^ (i + 1 + 1) * ℓ = 4 * (2 ^ i * ℓ) := by ring
          omega
      obtain ⟨hy1, hy2⟩ := (hmem y).mp hy
      obtain ⟨hy1', hy2'⟩ := (hmem y').mp hy'
      have hay : a ≤ y := by omega
      have hay' : a ≤ y' := by omega
      -- the mixture identity
      have hmix : D.exitLaw ℓ y
          = mix (Finset.Ico a (2 * a)) (D.exitLaw a y) (fun z => D.exitLaw ℓ z) := by
        funext k
        rw [mix_apply]
        exact D.exitLaw_mix hla hay k
      have hmix' : D.exitLaw ℓ y'
          = mix (Finset.Ico a (2 * a)) (D.exitLaw a y') (fun z => D.exitLaw ℓ z) := by
        funext k
        rw [mix_apply]
        exact D.exitLaw_mix hla hay' k
      -- the reference measure `ν = ω ϖ_i`
      have hνsum : ∑ z ∈ Finset.Ico a (2 * a), D.omeg * varpi a z = D.omeg := by
        rw [← Finset.mul_sum, varpi_sum ha20, mul_one]
      have hblock : Finset.Ico a (2 * a) = block i ℓ := (block_eq i ℓ).symm
      rw [hmix, hmix']
      have hgoal := tvOn_mix_le (F := Finset.Ico ℓ (2 * ℓ)) (G := Finset.Ico a (2 * a))
        (μ := D.exitLaw a y) (μ' := D.exitLaw a y') (ν := fun z => D.omeg * varpi a z)
        (P := fun z => D.exitLaw ℓ z) (ω := D.omeg) (B := (1 - D.omeg) ^ i)
        D.omeg_lt_one
        (fun z _ => D.doeblin ha20 haτ hy1 hy2 z)
        (fun z _ => D.doeblin ha20 haτ hy1' hy2' z)
        hνsum
        (D.exitLaw_sum ha1 hay) (D.exitLaw_sum ha1 hay')
        (fun z hz z' hz' => ih z (hblock ▸ hz) z' (hblock ▸ hz'))
      calc tvOn (Finset.Ico ℓ (2 * ℓ))
              (mix (Finset.Ico a (2 * a)) (D.exitLaw a y) fun z => D.exitLaw ℓ z)
              (mix (Finset.Ico a (2 * a)) (D.exitLaw a y') fun z => D.exitLaw ℓ z)
          ≤ (1 - D.omeg) * (1 - D.omeg) ^ i := hgoal
        _ = (1 - D.omeg) ^ (i + 1) := by ring

/-- **The coupling bound above a block.** Two descents started anywhere above `2^i ℓ` — not
necessarily in the same block — reach the base block `[ℓ,2ℓ)` with laws at total variation at
most `(1−ω)^i`.

This is `eq:doubling_coupling` composed with one further application of the mixture identity, at
`ω = 0`, where `tvOn_mix_le` degenerates to the triangle inequality. It replaces the paper's
*second* bullet in the proof of `theo:doubling_sharp` ("two states above `2^iℓ` have profiles
differing by at most `c₂(1−ω)^i + 3c₂c₃/ℓ`") and is strictly stronger: it needs neither the
block index of `m` nor a second descent at the level `2^jℓ`, and the constant it yields
downstream is `2c₂c₃/ℓ` rather than `3c₂c₃/ℓ`. -/
theorem coupling_above {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hℓτ : 32 * D.c * D.tau ≤ (ℓ : ℝ))
    (i : ℕ) {m m' : ℕ} (hm : 2 ^ i * ℓ ≤ m) (hm' : 2 ^ i * ℓ ≤ m') :
    tvOn (Finset.Ico ℓ (2 * ℓ)) (D.exitLaw ℓ m) (D.exitLaw ℓ m') ≤ (1 - D.omeg) ^ i := by
  have hℓ1 : 1 ≤ ℓ := by omega
  set a : ℕ := 2 ^ i * ℓ with hadef
  have hla : ℓ ≤ a := le_pow_mul i ℓ
  have ha1 : 1 ≤ a := le_trans hℓ1 hla
  have hmix : D.exitLaw ℓ m
      = mix (Finset.Ico a (2 * a)) (D.exitLaw a m) (fun z => D.exitLaw ℓ z) := by
    funext k
    rw [mix_apply]
    exact D.exitLaw_mix hla hm k
  have hmix' : D.exitLaw ℓ m'
      = mix (Finset.Ico a (2 * a)) (D.exitLaw a m') (fun z => D.exitLaw ℓ z) := by
    funext k
    rw [mix_apply]
    exact D.exitLaw_mix hla hm' k
  have hblock : Finset.Ico a (2 * a) = block i ℓ := (block_eq i ℓ).symm
  rw [hmix, hmix']
  have hgoal := tvOn_mix_le (F := Finset.Ico ℓ (2 * ℓ)) (G := Finset.Ico a (2 * a))
    (μ := D.exitLaw a m) (μ' := D.exitLaw a m') (ν := fun _ => (0 : ℝ))
    (P := fun z => D.exitLaw ℓ z) (ω := 0) (B := (1 - D.omeg) ^ i)
    (by norm_num)
    (fun z _ => D.exitLaw_nonneg ha1 z m hm)
    (fun z _ => D.exitLaw_nonneg ha1 z m' hm')
    (by simp)
    (D.exitLaw_sum ha1 hm) (D.exitLaw_sum ha1 hm')
    (fun z hz z' hz' => D.coupling hℓ hℓτ i z (hblock ▸ hz) z' (hblock ▸ hz'))
  calc tvOn (Finset.Ico ℓ (2 * ℓ))
          (mix (Finset.Ico a (2 * a)) (D.exitLaw a m) fun z => D.exitLaw ℓ z)
          (mix (Finset.Ico a (2 * a)) (D.exitLaw a m') fun z => D.exitLaw ℓ z)
      ≤ (1 - 0) * (1 - D.omeg) ^ i := hgoal
    _ = (1 - D.omeg) ^ i := by ring

end Decay

end GFNBounds.Doubling
