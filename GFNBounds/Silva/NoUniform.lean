import GFNBounds.Silva.Basic

/-!
# The state-space dependence of the Silva bound is unavoidable

**`prop:silva_no_uniform`** — statement `silva_comparison.tex:74–87`, proof
`silva_comparison.tex:88–96`, with the setting at `silva_comparison.tex:9–39` and the reading of
the two items at `silva_comparison.tex:98–100`.

> Let `w_min := min{ p_{E,T}(x) p_B(τ|x) : p_B(τ|x) > 0 }`.
>
> 1. On every finite pointed DAG, for every full-support forward policy,
>    `TV(p_T, π) ≤ ½ (e^{√(𝓔(p_F)/w_min)} − 1)`.
> 2. For every `ε > 0` there exist a finite pointed DAG with uniform `p_B`, a target `π`, the
>    *uniform* training distribution `p_{E,T}` (so `χ²(q_{E,T}‖p_{E,T}) = 0`) and a full-support
>    forward policy `p_F` with `M' ≤ 1` such that `𝓔(p_F) ≤ ε` and `TV(p_T, π) = ⅛`.
>
> In particular, no bound `TV ≤ F(𝓔, χ², M')` with `F` independent of the state space and
> `F(𝓔,0,1) → 0` as `𝓔 → 0` can hold: the factor `1/w_min` in *(i)* — of order `|𝒳| e^{c t_m}` in
> general — is not an artifact of the proof.

with, from `silva_comparison.tex:24–26`,

> `𝓔(p_F) := 𝔼_{x∼p_{E,T}} 𝔼_{τ∼p_B(·|x)} [ (log (p_F(τ) / (π(x) p_B(τ|x))))² ]`

and, from `silva_comparison.tex:32`, `M := max{ p_F(τ)/p_B(τ|x) : p_B(τ|x) > 0 }` and
`M' := max(M, ‖π‖_∞)`.

## SCOPE (disclosed)

**No graph, no horizon, no pointedness, no acyclicity.** Neither item consumes them.

*Item (i)* is a statement about a finite terminal type `X`, a finite trajectory type `T`, a
backward kernel `pB : X → T → ℝ`, a forward trajectory weight `pF : T → ℝ`, a target `π` and a
training law `pET`. The paper's "finite pointed DAG" enters its proof only through the
**domination identity** `p_T(x) = 𝔼_{τ∼p_B(·|x)}[p_F(τ)/p_B(τ|x)]`, which the paper itself lists
as a hypothesis (`rem:silva_hypotheses`(3), `silva_comparison.tex:57`) rather than a theorem.
Here it is `hdom`, and `pT` is a variable constrained by it — nothing is claimed about *when* a
DAG supplies it. Consequently `tv_le_exp_sqrt_energy` is **not** a statement about DAGs; it is
the inequality the DAG statement reduces to once the identity is granted.

*Item (ii)* needs even less. In the star DAG every terminal has exactly one incoming trajectory,
so `p_B(τ|x) = 1`, the trajectory type is the terminal type, and the backward kernel is the
Kronecker delta `deltaPB` — which is what "uniform `p_B`" means here. The witness is therefore built on the bare finite type
`Star K = Bool ⊕ Fin K` — the two `inl`s are `x*` and `x'`, the `K` `inr`s are `b₁,…,b_K` — with
explicit `π`, `p_F` and `p_{E,T}`. **No DAG library is used or needed.** That the delta kernel
does satisfy the domination identity is `hdom_deltaPB`, so the witness is an instance of item
(i)'s own setting and not of a parallel one.

**Sums run over all of `T`, not over the support of `p_B(·|x)`.** Off the support
`p_B(τ|x) = 0` kills the summand of `residual` and of the domination identity alike, so the two
conventions agree and no `Finset.filter` — and no decidability — is needed.

**`w_min` versus a lower bound.** `tv_le_exp_sqrt_energy` is stated with an arbitrary `w > 0`
bounding `p_{E,T}(x) p_B(τ|x)` from below on the support. The paper's statement is the instance
`w = w_min`, recovered in `tv_le_exp_sqrt_energy_wmin`; the general form is what the proof uses
and the bound is monotone in `w`, so the two are the same content. Note that `w_min > 0` forces
`p_{E,T}` to have full support, exactly as `rem:silva_hypotheses`(1) says.

**The vocabulary is shared.** `tv`, `chiSq`, `unif`, `logRatio`, `residual`, `MprimeLe`,
`wSupport`, `wMin` and the identities about them alone are in `GFNBounds.Silva.Basic`,
shared with the sibling file for `prop:silva_explicit`. The residual was called `energy` here
before that merge, with its target argument last; it is `residual pET π pB pF` now — the same
function of the same four arguments, in the order they appear in the paper's display at
`silva_comparison.tex:25`. The theorem names `tv_le_exp_sqrt_energy` and
`tv_le_exp_sqrt_energy_wmin` keep the old word.

**`M' ≤ 1` is a Prop, not a value.** `MprimeLe pB pF π c` unfolds `max(M, ‖π‖_∞) ≤ c` into its
two halves rather than defining `M'` as a `Finset.sup'` (which would need the support nonempty).
This is equivalent for every use the proposition makes of `M'`.

**The final clause, and one gap in it.** `no_state_space_free_bound` is that clause on the slice
the witness occupies: no `F : ℝ → ℝ` with `F(𝓔) → 0` as `𝓔 → 0⁺` bounds `TV` over all finite
instances with `χ² = 0` and `M' ≤ 1`. The paper's literal three-argument form is
`no_three_argument_bound`, where `F`'s third slot is fed **any** `c` with `M' ≤ c` (so in
particular `c = 1`). That reading is deliberate: the star witness has `M' = 3/8`, not `1`, so
deducing a contradiction from `F(𝓔,0,1) → 0` alone needs either this reading or monotonicity of
`F` in its third argument, and the paper leaves the point implicit. **The literal "`F` evaluated
at the instance's own `M'`" statement is not formalized**, and that is a genuine (small) gap
between the display at `silva_comparison.tex:86` and what item (ii) delivers.

**Not formalized:** `prop:silva_explicit` and the two remarks; the ladder-corridor degeneracy of
`rem:silva_model_constant`; the order-of-magnitude claim `1/w_min ∼ |𝒳| e^{c t_m}` in the "in
particular" sentence, which the paper asserts without proof.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒳` finite | ✓ carried (`Fintype X`) |
| finite pointed DAG, horizon `t_m`, acyclicity | ⚠ **dropped** — replaced by `hdom`; see SCOPE |
| `p_B(·\|x)` a probability over the trajectories into `x` | ✓ carried (`hB`, `hB1`) |
| `π` full support, a probability | ✓ carried (`hπ`, `hπ1`) |
| `p_F` full support (`p_F(τ) > 0` where `p_B(τ\|x) > 0`) | ✓ carried (`hF`) |
| domination: `p_T(x) = 𝔼_{p_B}[p_F/p_B]` | ⚠ **assumed** (`hdom`), as in `rem:silva_hypotheses`(3) |
| `w_min > 0`, i.e. `p_{E,T}` full support | ✓ carried (`hw`, `hwle`); see `rem:silva_hypotheses`(1) |
| item (ii): uniform `p_B` | ✓ carried — `deltaPB`, the one-parent case, so `p_B(τ\|x) = 1` |
| item (ii): uniform `p_{E,T}`, hence `χ² = 0` | ✓ carried (`starPET`, `star_chiSq`) |
| item (ii): `M' ≤ 1` | ✓ carried (`star_Mprime`), for every `K ≥ 1` |
| "`1/w_min` of order `\|𝒳\| e^{c t_m}`" | ⚠ **not formalized** — asserted, not proved, in the paper |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Silva

open Finset Filter Topology

/-! ## The finite functionals

`tv`, `chiSq`, `unif`, `logRatio`, `residual` and `MprimeLe` — with `chiSq_self`, and with
`wSupport`, `wMin`, `wMin_le`, `wMin_pos` for the paper's `w_min` — are in
`GFNBounds.Silva.Basic`, shared with the sibling file for `prop:silva_explicit`. -/

/-! ## Item (i): a per-graph model-free bound always exists -/

section ItemOne

variable {X T : Type*} [Fintype X] [Fintype T]

/-- If `|u| ≤ s` then `|e^u − 1| ≤ e^s − 1`: the upper half is monotonicity of `exp`, the lower
half is `1 − e^{−s} ≤ s ≤ e^s − 1`. -/
theorem abs_exp_sub_one_le {u s : ℝ} (h : |u| ≤ s) :
    |Real.exp u - 1| ≤ Real.exp s - 1 := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  have hup : Real.exp u ≤ Real.exp s := Real.exp_le_exp.mpr h₂
  have hlow : Real.exp (-s) ≤ Real.exp u := Real.exp_le_exp.mpr h₁
  have hes : -s + 1 ≤ Real.exp (-s) := Real.add_one_le_exp _
  have hes' : s + 1 ≤ Real.exp s := Real.add_one_le_exp _
  rw [abs_le]
  constructor <;> linarith

/-- **`prop:silva_no_uniform`(i)**, in the form its proof uses: with `w` any positive lower bound
for `p_{E,T}(x) p_B(τ|x)` on the support of `p_B`,
`TV(p_T,π) ≤ ½ (e^{√(𝓔(p_F)/w)} − 1)`. The paper's `w_min` is the largest such `w`; see
`tv_le_exp_sqrt_energy_wmin`. -/
theorem tv_le_exp_sqrt_energy
    {pET : X → ℝ} {pB : X → T → ℝ} {pF : T → ℝ} {π pT : X → ℝ} {w : ℝ}
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hET : ∀ x, 0 ≤ pET x)
    (hB : ∀ x t, 0 ≤ pB x t) (hB1 : ∀ x, ∑ t, pB x t = 1)
    (hF : ∀ x t, 0 < pB x t → 0 < pF t)
    (hdom : ∀ x, pT x = ∑ t, pB x t * (pF t / pB x t))
    (hw : 0 < w) (hwle : ∀ x t, 0 < pB x t → w ≤ pET x * pB x t) :
    tv pT π ≤ 2⁻¹ * (Real.exp (Real.sqrt (residual pET π pB pF / w)) - 1) := by
  set E := residual pET π pB pF with hEdef
  set s := Real.sqrt (E / w) with hsdef
  have hinner : ∀ x, 0 ≤ ∑ t, pB x t * logRatio π pB pF x t ^ 2 := fun x =>
    Finset.sum_nonneg fun t _ => mul_nonneg (hB x t) (sq_nonneg _)
  -- every log-ratio on the support is bounded by `s`
  have hkey : ∀ x t, 0 < pB x t → |logRatio π pB pF x t| ≤ s := by
    intro x t ht
    have h1 : pB x t * logRatio π pB pF x t ^ 2
        ≤ ∑ t', pB x t' * logRatio π pB pF x t' ^ 2 :=
      Finset.single_le_sum (f := fun t' => pB x t' * logRatio π pB pF x t' ^ 2)
        (fun t' _ => mul_nonneg (hB x t') (sq_nonneg _)) (Finset.mem_univ t)
    have h2 : pET x * (pB x t * logRatio π pB pF x t ^ 2)
        ≤ pET x * ∑ t', pB x t' * logRatio π pB pF x t' ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (hET x)
    have h3 : pET x * (∑ t', pB x t' * logRatio π pB pF x t' ^ 2) ≤ E :=
      Finset.single_le_sum (f := fun x' => pET x' * ∑ t', pB x' t' * logRatio π pB pF x' t' ^ 2)
        (fun x' _ => mul_nonneg (hET x') (hinner x')) (Finset.mem_univ x)
    have h4 : w * logRatio π pB pF x t ^ 2 ≤ E := by
      have h5 := mul_le_mul_of_nonneg_right (hwle x t ht)
        (sq_nonneg (logRatio π pB pF x t))
      nlinarith [h2, h3]
    have h6 : logRatio π pB pF x t ^ 2 ≤ E / w := by
      rw [le_div_iff₀ hw]; linarith
    calc |logRatio π pB pF x t| = Real.sqrt (logRatio π pB pF x t ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (E / w) := Real.sqrt_le_sqrt h6
  -- the domination identity, in exponential form
  have hexp : ∀ x, pT x = π x * ∑ t, pB x t * Real.exp (logRatio π pB pF x t) := by
    intro x
    rw [hdom x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases (hB x t).lt_or_eq with ht | ht
    · have hpos : 0 < pF t / (π x * pB x t) := div_pos (hF x t ht) (mul_pos (hπ x) ht)
      have hπx : π x ≠ 0 := (hπ x).ne'
      have hbt : pB x t ≠ 0 := ht.ne'
      rw [logRatio, Real.exp_log hpos]
      field_simp
    · rw [← ht]; ring
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- the pointwise bound
  have hpt : ∀ x, |pT x - π x| ≤ π x * (Real.exp s - 1) := by
    intro x
    have hrw : pT x - π x = π x * ∑ t, pB x t * (Real.exp (logRatio π pB pF x t) - 1) := by
      have hsplit : ∑ t, pB x t * (Real.exp (logRatio π pB pF x t) - 1)
          = (∑ t, pB x t * Real.exp (logRatio π pB pF x t)) - ∑ t, pB x t := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [hexp x, hsplit, hB1 x]; ring
    rw [hrw, abs_mul, abs_of_pos (hπ x)]
    refine mul_le_mul_of_nonneg_left ?_ (hπ x).le
    calc |∑ t, pB x t * (Real.exp (logRatio π pB pF x t) - 1)|
        ≤ ∑ t, |pB x t * (Real.exp (logRatio π pB pF x t) - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, pB x t * (Real.exp s - 1) := by
          refine Finset.sum_le_sum fun t _ => ?_
          rcases (hB x t).lt_or_eq with ht | ht
          · rw [abs_mul, abs_of_pos ht]
            exact mul_le_mul_of_nonneg_left (abs_exp_sub_one_le (hkey x t ht)) ht.le
          · rw [← ht]; simp
      _ = Real.exp s - 1 := by rw [← Finset.sum_mul, hB1 x, one_mul]
  have hsum : ∑ x, |pT x - π x| ≤ Real.exp s - 1 := by
    calc ∑ x, |pT x - π x| ≤ ∑ x, π x * (Real.exp s - 1) := Finset.sum_le_sum fun x _ => hpt x
      _ = Real.exp s - 1 := by rw [← Finset.sum_mul, hπ1, one_mul]
  rw [tv]
  linarith

/-- **`prop:silva_no_uniform`(i)** with the paper's own constant `w_min`. -/
theorem tv_le_exp_sqrt_energy_wmin
    {pET : X → ℝ} {pB : X → T → ℝ} {pF : T → ℝ} {π pT : X → ℝ}
    (h : (wSupport pB).Nonempty)
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hET : ∀ x, 0 < pET x)
    (hB : ∀ x t, 0 ≤ pB x t) (hB1 : ∀ x, ∑ t, pB x t = 1)
    (hF : ∀ x t, 0 < pB x t → 0 < pF t)
    (hdom : ∀ x, pT x = ∑ t, pB x t * (pF t / pB x t)) :
    tv pT π ≤ 2⁻¹ * (Real.exp (Real.sqrt (residual pET π pB pF / wMin pET pB h)) - 1) :=
  tv_le_exp_sqrt_energy hπ hπ1 (fun x => (hET x).le) hB hB1 hF hdom
    (wMin_pos h hET) (fun _ _ ht => wMin_le h ht)

end ItemOne

/-! ## The one-parent kernel

Each terminal of the star DAG has the single parent `s_o`, so the unique trajectory into `x` is
`(s_o, x)` and `p_B(τ|x) = 1`. The trajectory type is therefore the terminal type and the
backward kernel is the Kronecker delta. -/

section Delta

variable {X : Type*} [DecidableEq X]

/-- The backward kernel of a graph in which each terminal `x` has one incoming trajectory,
identified with `x` itself: `p_B(τ|x) = 1` for `τ = x` and `0` otherwise. -/
def deltaPB (X : Type*) [DecidableEq X] : X → X → ℝ := fun x t => if t = x then 1 else 0

theorem deltaPB_nonneg (x t : X) : 0 ≤ deltaPB X x t := by
  by_cases h : t = x <;> simp [deltaPB, h]

theorem deltaPB_pos_iff {x t : X} : 0 < deltaPB X x t ↔ t = x := by
  by_cases h : t = x <;> simp [deltaPB, h]

variable [Fintype X]

theorem deltaPB_sum (x : X) : ∑ t, deltaPB X x t = 1 := by
  simp [deltaPB]

/-- The domination identity holds for the one-parent kernel, with `p_T = p_F`. -/
theorem hdom_deltaPB (pF : X → ℝ) (x : X) :
    pF x = ∑ t, deltaPB X x t * (pF t / deltaPB X x t) := by
  rw [Finset.sum_eq_single x] <;> simp +contextual [deltaPB]

/-- `𝓔(p_F)` for the one-parent kernel: one term per terminal state. -/
theorem energy_deltaPB (pET pF π : X → ℝ) :
    residual pET π (deltaPB X) pF = ∑ x, pET x * Real.log (pF x / π x) ^ 2 := by
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [Finset.sum_eq_single x] <;> simp +contextual [deltaPB, logRatio]

end Delta

/-! ## Item (ii): the star witness -/

/-- The terminal states of the star DAG: `x* = inl false`, `x' = inl true`, and the `K` filler
states `b₁,…,b_K = inr i`. -/
abbrev Star (K : ℕ) := Bool ⊕ Fin K

/-- The target `π` of the star witness: `π(x*) = π(x') = ¼`, `π(bᵢ) = 1/(2K)`. -/
noncomputable def starPi (K : ℕ) : Star K → ℝ
  | .inl _ => 1 / 4
  | .inr _ => 1 / (2 * K)

/-- The forward policy of the star witness: `p_F(s_o→x*) = ⅜`, `p_F(s_o→x') = ⅛`,
`p_F(s_o→bᵢ) = 1/(2K)`. -/
noncomputable def starPF (K : ℕ) : Star K → ℝ
  | .inl false => 3 / 8
  | .inl true => 1 / 8
  | .inr _ => 1 / (2 * K)

/-- The uniform training distribution on the `K+2` terminals. -/
noncomputable def starPET (K : ℕ) : Star K → ℝ := fun _ => ((K : ℝ) + 2)⁻¹

theorem card_star (K : ℕ) : (Fintype.card (Star K) : ℝ) = (K : ℝ) + 2 := by
  have h : Fintype.card (Star K) = 2 + K := by simp [Star]
  rw [h]
  push_cast
  ring

theorem starPET_pos (K : ℕ) (x : Star K) : 0 < starPET K x := by
  simp only [starPET]
  positivity

theorem starPET_sum (K : ℕ) : ∑ x, starPET K x = 1 := by
  have hden : (0 : ℝ) < (K : ℝ) + 2 := by positivity
  simp only [starPET, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_star]
  field_simp

/-- `χ²(q_{E,T}‖p_{E,T}) = 0`: the training distribution *is* the uniform one. -/
theorem star_chiSq (K : ℕ) : chiSq (unif (Star K)) (starPET K) = 0 := by
  have h : unif (Star K) = starPET K := by
    funext _; simp only [unif, starPET, card_star]
  rw [h, chiSq_self]

/-- **`TV(p_T,π) = ⅛`** for the star witness, for every `K`. -/
theorem star_tv (K : ℕ) : tv (starPF K) (starPi K) = 1 / 8 := by
  have hb : ∑ b : Bool, |starPF K (Sum.inl b) - starPi K (Sum.inl b)| = 1 / 4 := by
    rw [Fintype.sum_bool]
    simp only [starPF, starPi]
    rw [show (1 : ℝ) / 8 - 1 / 4 = -(1 / 8) by norm_num,
      show (3 : ℝ) / 8 - 1 / 4 = 1 / 8 by norm_num, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    norm_num
  have hf : ∑ i : Fin K, |starPF K (Sum.inr i) - starPi K (Sum.inr i)| = 0 := by
    simp [starPF, starPi]
  rw [tv, Fintype.sum_sum_type, hb, hf]
  norm_num

section StarFacts

variable {K : ℕ} (hK : 0 < K)
include hK

theorem starK_pos : (0 : ℝ) < K := by exact_mod_cast hK

theorem starK_one : (1 : ℝ) ≤ K := by
  have h : 1 ≤ K := hK
  exact_mod_cast h

theorem starPi_pos (x : Star K) : 0 < starPi K x := by
  have hK' := starK_pos hK
  cases x with
  | inl b => norm_num [starPi]
  | inr i => exact div_pos one_pos (by linarith)

theorem starPF_pos (x : Star K) : 0 < starPF K x := by
  have hK' := starK_pos hK
  cases x with
  | inl b => cases b <;> norm_num [starPF]
  | inr i => exact div_pos one_pos (by linarith)

theorem starPi_sum : ∑ x, starPi K x = 1 := by
  have hK' := starK_pos hK
  have hb : ∑ b : Bool, starPi K (Sum.inl b) = 1 / 2 := by
    rw [Fintype.sum_bool]; norm_num [starPi]
  have hf : ∑ _i : Fin K, starPi K (Sum.inr _i) = 1 / 2 := by
    simp only [starPi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [Fintype.sum_sum_type, hb, hf]
  norm_num

theorem starPF_sum : ∑ x, starPF K x = 1 := by
  have hK' := starK_pos hK
  have hb : ∑ b : Bool, starPF K (Sum.inl b) = 1 / 2 := by
    rw [Fintype.sum_bool]; norm_num [starPF]
  have hf : ∑ _i : Fin K, starPF K (Sum.inr _i) = 1 / 2 := by
    simp only [starPF, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [Fintype.sum_sum_type, hb, hf]
  norm_num

/-- **`M' ≤ 1`** for the star witness. The paper's parenthetical `M = ⅜`, `‖π‖_∞ = ¼` holds
for `K ≥ 2`; at `K = 1` the filler weight `1/(2K) = ½` is the largest, so `M = ½`. Either way
`M' ≤ 1`, which is all the statement claims, and `K` is taken large. -/
theorem star_Mprime : MprimeLe (deltaPB (Star K)) (starPF K) (starPi K) 1 := by
  have hK1 := starK_one hK
  have hone : ∀ x : Star K, starPF K x ≤ 1 := by
    intro x
    cases x with
    | inl b => cases b <;> norm_num [starPF]
    | inr i =>
        simp only [starPF]
        rw [div_le_one (by linarith)]
        linarith
  refine ⟨?_, ?_⟩
  · intro x t ht
    rw [deltaPB_pos_iff] at ht
    subst ht
    simpa [deltaPB] using hone t
  · intro x
    cases x with
    | inl b => norm_num [starPi]
    | inr i =>
        simp only [starPi]
        rw [div_le_one (by linarith)]
        linarith

/-- **`𝓔(p_F) = ((log 3/2)² + (log 2)²)/(K+2)`** for the star witness: the log-ratios vanish on
the `bᵢ`. -/
theorem star_energy :
    residual (starPET K) (starPi K) (deltaPB (Star K)) (starPF K)
      = ((Real.log (3 / 2)) ^ 2 + (Real.log 2) ^ 2) / ((K : ℝ) + 2) := by
  have hK' := starK_pos hK
  have h1 : starPF K (Sum.inl false) / starPi K (Sum.inl false) = 3 / 2 := by
    norm_num [starPF, starPi]
  have h2 : starPF K (Sum.inl true) / starPi K (Sum.inl true) = 1 / 2 := by
    norm_num [starPF, starPi]
  have h3 : ∀ i : Fin K, starPF K (Sum.inr i) / starPi K (Sum.inr i) = 1 := by
    intro i
    have hne : (1 : ℝ) / (2 * (K : ℝ)) ≠ 0 := ne_of_gt (div_pos one_pos (by linarith))
    simp only [starPF, starPi]
    exact div_self hne
  rw [energy_deltaPB, Fintype.sum_sum_type]
  simp only [Fintype.sum_bool, starPET, h1, h2, h3]
  rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]
  simp
  ring

end StarFacts

/-- `(log 3/2)² + (log 2)² ≤ 1`: `log(3/2) ≤ 1/2` because `log x ≤ x − 1`, and
`log 2 < 0.6931471808` by `Real.log_two_lt_d9`; the sum of squares is at most `0.7305`. -/
theorem log_sq_sum_le_one : (Real.log (3 / 2)) ^ 2 + (Real.log 2) ^ 2 ≤ 1 := by
  have h1 : Real.log (3 / 2) ≤ 1 / 2 := by
    have h := Real.log_le_sub_one_of_pos (x := (3 : ℝ) / 2) (by norm_num)
    linarith
  have h1' : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- **`prop:silva_no_uniform`(ii)**: for every `ε > 0` the star witness with `K` large has
`χ² = 0`, `M' ≤ 1`, `𝓔(p_F) ≤ ε` and `TV(p_T,π) = ⅛`. The `K` is effective — the proof takes
`K = ⌈1/ε⌉₊ + 1`, since `𝓔 = ((log 3/2)² + (log 2)²)/(K+2) ≤ 1/(K+2)`. -/
theorem exists_star_witness {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧
      (∀ x, 0 < starPi K x) ∧ (∀ x, 0 < starPF K x) ∧
      (∑ x, starPi K x = 1) ∧ (∑ x, starPF K x = 1) ∧
      (∀ x, 0 < starPET K x) ∧ (∑ x, starPET K x = 1) ∧
      chiSq (unif (Star K)) (starPET K) = 0 ∧
      MprimeLe (deltaPB (Star K)) (starPF K) (starPi K) 1 ∧
      0 < residual (starPET K) (starPi K) (deltaPB (Star K)) (starPF K) ∧
      residual (starPET K) (starPi K) (deltaPB (Star K)) (starPF K) ≤ ε ∧
      tv (starPF K) (starPi K) = 1 / 8 := by
  obtain ⟨K, hK, hKε⟩ : ∃ K : ℕ, 0 < K ∧ 1 / ε ≤ (K : ℝ) + 2 := by
    refine ⟨⌈1 / ε⌉₊ + 1, Nat.succ_pos _, ?_⟩
    have h := Nat.le_ceil (1 / ε)
    push_cast
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : (0 : ℝ) < (K : ℝ) + 2 := by positivity
  have hnum : 0 < (Real.log (3 / 2)) ^ 2 + (Real.log 2) ^ 2 := by
    have hsq := pow_pos hlog2 2
    have := sq_nonneg (Real.log (3 / 2))
    linarith
  refine ⟨K, hK, starPi_pos hK, starPF_pos hK, starPi_sum hK, starPF_sum hK,
    starPET_pos K, starPET_sum K, star_chiSq K, star_Mprime hK, ?_, ?_, star_tv K⟩
  · rw [star_energy hK]
    exact div_pos hnum hden
  · rw [star_energy hK, div_le_iff₀ hden]
    rw [div_le_iff₀ hε] at hKε
    linarith [log_sq_sum_le_one]

/-! ## The final clause: no state-space-free `F` -/

/-- **`prop:silva_no_uniform`, the "in particular"**: no function of the residual alone,
vanishing as the residual vanishes, bounds the total variation over all finite instances with
`χ²(q_{E,T}‖p_{E,T}) = 0` and `M' ≤ 1`. -/
theorem no_state_space_free_bound :
    ¬ ∃ F : ℝ → ℝ,
      Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ (X T : Type) [Fintype X] [Fintype T]
        (pET : X → ℝ) (pB : X → T → ℝ) (pF : T → ℝ) (π pT : X → ℝ),
        (∀ x, 0 < π x) → (∑ x, π x = 1) →
        (∀ x, 0 < pET x) → (∑ x, pET x = 1) →
        (∀ x t, 0 ≤ pB x t) → (∀ x, ∑ t, pB x t = 1) →
        (∀ x t, 0 < pB x t → 0 < pF t) →
        (∀ x, pT x = ∑ t, pB x t * (pF t / pB x t)) →
        chiSq (unif X) pET = 0 →
        MprimeLe pB pF π 1 →
        tv pT π ≤ F (residual pET π pB pF) := by
  rintro ⟨F, hF, hbound⟩
  obtain ⟨δ, hδ, hδF⟩ := Metric.tendsto_nhdsWithin_nhds.mp hF (1 / 8) (by norm_num)
  obtain ⟨K, _, hπpos, hFpos, hπ1, _, hETpos, hET1, hchi, hM, hEpos, hEle, htv⟩ :=
    exists_star_witness (half_pos hδ)
  have hle := hbound (Star K) (Star K) (starPET K) (deltaPB (Star K)) (starPF K)
    (starPi K) (starPF K) hπpos hπ1 hETpos hET1 deltaPB_nonneg deltaPB_sum
    (fun _ t ht => by rw [deltaPB_pos_iff] at ht; subst ht; exact hFpos t)
    (hdom_deltaPB (starPF K)) hchi hM
  have hd : dist (residual (starPET K) (starPi K) (deltaPB (Star K)) (starPF K)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hEpos]
    linarith
  have hlt := hδF (Set.mem_Ioi.mpr hEpos) hd
  rw [Real.dist_eq, sub_zero] at hlt
  rw [htv] at hle
  linarith [(abs_lt.mp hlt).2]

/-- **`prop:silva_no_uniform`, the "in particular" in the paper's three-argument form**: no
`F(𝓔, χ², M')` with `F(·,0,1) → 0` bounds `TV`, when `F`'s third slot may be fed any bound on
`M'`. See SCOPE for why the third slot is quantified rather than evaluated at the instance's
own `M'`. -/
theorem no_three_argument_bound :
    ¬ ∃ F : ℝ → ℝ → ℝ → ℝ,
      Tendsto (fun e => F e 0 1) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ (X T : Type) [Fintype X] [Fintype T]
        (pET : X → ℝ) (pB : X → T → ℝ) (pF : T → ℝ) (π pT : X → ℝ) (c : ℝ),
        (∀ x, 0 < π x) → (∑ x, π x = 1) →
        (∀ x, 0 < pET x) → (∑ x, pET x = 1) →
        (∀ x t, 0 ≤ pB x t) → (∀ x, ∑ t, pB x t = 1) →
        (∀ x t, 0 < pB x t → 0 < pF t) →
        (∀ x, pT x = ∑ t, pB x t * (pF t / pB x t)) →
        MprimeLe pB pF π c →
        tv pT π ≤ F (residual pET π pB pF) (chiSq (unif X) pET) c := by
  rintro ⟨F, hF, hbound⟩
  refine no_state_space_free_bound ⟨fun e => F e 0 1, hF, ?_⟩
  intro X T _ _ pET pB pF π pT hπ hπ1 hET hET1 hB hB1 hFpos hdom hchi hM
  have h := hbound X T pET pB pF π pT 1 hπ hπ1 hET hET1 hB hB1 hFpos hdom hM
  rwa [hchi] at h

end GFNBounds.Silva
