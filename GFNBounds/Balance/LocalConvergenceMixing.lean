import GFNBounds.Balance.LocalConvergence
import GFNBounds.Balance.WeightedL2Norm
import GFNBounds.Balance.LocalConvergenceClauses

/-!
# The local convergence theorem at the paper's mixing sum `B̂`

**`theo:local_convergence_full`** — statement `proofs.tex:612–618`, proof `proofs.tex:620–678`.
`GFNBounds/Balance/LocalConvergence.lean` certifies the theorem's two estimates for a free
constant `B̂` subject to two hypotheses the paper does not write, `hB1 : 1 ≤ B̂` and the coercivity
`hcoer : ‖f^⊥‖ ≤ B̂‖Af‖`; `GFNBounds/Balance/LocalConvergenceClauses.lean`
certifies the theorem's four remaining clauses under the same two. This file states all six at the
paper's `B̂` — the mixing sum `∑_{n≥0}‖Pⁿ − Π‖_{L²(λ)}` — and discharges both hypotheses from
summable mixing. It also proves that the Lean form of the mixing hypothesis is exactly the
paper's, and that it implies the paper's ergodicity.

> (`theo:db_stable_frozen_full`, the setting inherited, `proofs.tex:593`) assume moreover that `T`
> is ergodic with summable `L²`-mixing, `B̂ := ∑_{n≥0} β̂_n < ∞`, and `w ≥ w_min > 0`. Set
> `ϱ := g''(1)w_min/B̂²`.

> (`theo:local_convergence_full`, `proofs.tex:613`) Then there are explicit
> `ε₀ ∈ (0, a/(16C_∞)]` and `C ≥ 1`, depending only on `g''(1)`, `sup_{[1−a,1+a]}|g'''|`, `a`,
> `w_min`, `‖w‖_{L^∞}`, `B̂` and `C_∞`, such that for every initialization `μ₀ = (1+h₀)λ` with
> `‖h₀‖_{L²(λ)} ≤ ε₀`, the *nonlinear* gradient flow `μ̇_t = −∇^λ𝓛_{g,ν}(μ_t)` converges to a
> balanced flow `c_∞λ` with `|c_∞ − 1 − Πh₀| ≤ C‖h₀ − Πh₀‖²` and
> `‖h_t − (c_∞−1)‖_{L²(λ)} ≤ 2e^{−ϱt/2}‖h₀ − Πh₀‖_{L²(λ)}`.
> There is moreover an explicit `γ₀ > 0`, depending only on the same quantities, such that for
> every such `h₀` and every step `0 < γ ≤ γ₀` the gradient descent `h_{k+1} := h_k − γD_k`,
> `D_k` the density against `λ` of `∇^λ𝓛_{g,ν}((1+h_k)λ)`, is well defined and satisfies `‖h_{k+1} − Πh_{k+1}‖_{L²(λ)} ≤ (1 − γϱ/4)‖h_k − Πh_k‖_{L²(λ)}` for every `k ≥ 0`.

> (Step 2, `proofs.tex:634`) `‖h^⊥‖ ≤ B̂‖Ah^⊥‖` (Lemma `lem:sigma_mixing`)

> (Step 6, `proofs.tex:652`) since `B̂ ≥ β̂₀ = 1`, `ϱ ≤ g''(1)w_min`

## What is proved

| | |
|---|---|
| **`local_convergence_full_mixing`** | the flow clause, `LocalConvergence.local_convergence_full` at `B̂ := Core.Mixing.B (densOp λ K) (meanOp λ)`, with `hB1` and `hcoer` **removed** and `hmx : Core.Mixing (densOp λ K) (meanOp λ)` in their place |
| **`local_convergence_gd_mixing`** | the discrete clause, `LocalConvergence.local_convergence_gd` at the same `B̂`, the same two hypotheses removed |
| **`eps0_mem_Ioc_mixing`** | `ε₀ ∈ (0, a/(16C_∞)]` at the paper's `B̂`, off `LocalConvergenceClauses.eps0_mem_Ioc`, `hB1` removed |
| **`local_convergence_full_C_mixing`** | the flow clause with the printed `C := max(1, C₇)`, off `local_convergence_full_C`, `hB1` and `hcoer` removed |
| **`gamma0_pos_of_weights_mixing`** | `γ₀ > 0` at the paper's `B̂`, off `gamma0_pos_of_weights`, whose `0 ≤ B̂` is `Core.Mixing.B_nonneg` — no `hmx`, no `[Nontrivial V]` |
| **`local_convergence_gd_welldefined_mixing`** | "the gradient descent … is well defined", all three parts, off `local_convergence_gd_welldefined`, `hB1` and `hcoer` removed |
| **`mixing_densOp_iff_summable`** | under `hK`, `hinv`, `λ > 0`: `Core.Mixing (densOp λ K) (meanOp λ) ↔ Summable (n ↦ ‖Pⁿ − Π‖)`. The structure's `ΠP = PΠ = Π` fields are theorems (`meanOp_mul_densOp`, `densOp_mul_meanOp`), so `hmx` assumes nothing beyond the paper's summability |
| **`meanOp_eq_of_densOp_eq`**, **`eq_const_of_densAct_eq`** | summable mixing **implies ergodicity**: a `P`-fixed vector is `Π`-fixed; on functions, `densAct f = f` forces `f` to be the constant `∫f dλ`. Via `Core.Mixing.tendsto_pow` |

The six clause theorems are one-line specialisations. `hcoer` is `WeightedL2.mixing_coercivity_finite`, which is
`lem:sigma_mixing`'s conclusion read through the weighting isometry; `hB1` is
`WeightedL2Norm.one_le_B_densOp`, which is `B̂ ≥ β̂₀ = 1` with `β̂₀ = ‖I − Π‖_{L²(λ)} ≥ 1` from
`Π` idempotent and `Π ≠ I`.

## Hypothesis checklist — against the new signatures

The rows not listed are `LocalConvergence.lean`'s checklist, unchanged: finite state space;
`Core.IsMarkovOn`, `Core.IsInvariant`, `λ > 0`, `∑λ = 1`; `ν = λw`, `|w| ≤ ‖w‖_{L^∞}`,
`w ≥ w_min > 0`; `g` through `gd`, `g''(1) > 0` and the Taylor bound `htaylor`; `C_∞` as
`Cinf lamMin` with `0 < lamMin ≤ λ`; the flow and the descent sequence hypothesised; `ε₀`, `γ₀`,
`ϱ` the printed formulas.

| paper hypothesis | here |
|---|---|
| `T` ergodic with summable `L²`-mixing, `B̂ := ∑_{n≥0} β̂_n < ∞`, `β̂_n = ‖Pⁿ − Π‖_{L²(λ)}` | ✓ **carried**: `hmx : Core.Mixing (densOp λ K) (meanOp λ)`, and `B̂` **is** `Core.Mixing.B (densOp λ K) (meanOp λ) = ∑' n, ‖densOp λ K ^ n − meanOp λ‖`, the operator norm on `EuclideanSpace ℝ V` being the `L²(λ)` operator norm under the weighting isometry (`WeightedL2Norm.lean`, "Why this needs the weighted inner product"). `Core.Mixing` also packages `ΠP = PΠ = Π`, which the paper derives rather than assumes ("`P` preserves `λ`-integrals and fixes constants"); **`mixing_densOp_iff_summable`** proves they add nothing: under `hK`, `hinv`, `λ > 0`, `hmx` is equivalent to summability of `‖Pⁿ − Π‖` alone |
| `T` ergodic | ✓ **implied by `hmx`**, not an extra hypothesis and not merely unused: `eq_const_of_densAct_eq` (a `P`-fixed density is constant) and `meanOp_eq_of_densOp_eq` (operator form). No proof step consumes it, as in `LocalConvergence.lean`; it is what makes `Πh` a scalar, which `Graph.meanL2` is by definition |
| `‖h^⊥‖ ≤ B̂‖Ah^⊥‖` (Step 2, by `lem:sigma_mixing`) | ✓ **derived**, no longer hypothesised: `mixing_coercivity_finite hinv hlam hmx` |
| `B̂ ≥ β̂₀ = 1` (Step 6, and `ϱ > 0`) | ✓ **derived**, no longer hypothesised: `one_le_B_densOp hlam hmx` |
| `β̂₀ = 1` — the parenthesis of `lem:sigma_mixing`, inherited | ⚠ **`[Nontrivial V]` added**, see SCOPE. On a one-state space `Π = I`, so `β̂₀ = 0` and the parenthesis is false: the paper presupposes two states, and the Lean says so |
| `a ∈ (0,1)` | unchanged from the specialised theorems: `0 < a` in the flow clause, `ε₀ ∈ (0,·]` and well-definedness, `0 ≤ a` in the discrete contraction and `γ₀ > 0`; `a < 1` carried nowhere (`LocalConvergence.lean`, `LocalConvergenceClauses.lean`) |
| `0 < γ ≤ γ₀` | unchanged: ⚠ weakened to `0 ≤ γ` |
| `C ≥ 1`, `ε₀ ∈ (0, a/(16C_∞)]`, `γ₀ > 0`, "well defined" | ✓ at the paper's `B̂`, `hB1`/`hcoer` discharged: `local_convergence_full_C_mixing`, `eps0_mem_Ioc_mixing`, `gamma0_pos_of_weights_mixing`, `local_convergence_gd_welldefined_mixing`. Their own rows (`hg` on the open window, the route for part (iii)) are `LocalConvergenceClauses.lean`'s, unchanged |

## SCOPE (disclosed)

* **`[Nontrivial V]` is an added hypothesis, and the paper presupposes it.** With one state the
  mean projection is the identity, `β̂ₙ = 0` for every `n`, `B̂ = 0`, and `ϱ = g''(1)w_min/B̂²` is
  undefined in the paper (it is `0` in Lean's division). `lem:sigma_mixing` writes `β̂₀ = 1`, which
  is exactly the statement that `Π ≠ I`, i.e. two states. Whether the estimates still hold,
  degenerately, on one state is **not** examined: `one_le_B_densOp` is false there and the
  specialised theorems consume `1 ≤ B̂`. `gamma0_pos_of_weights_mixing` alone does not need it.
* **Finite state space**, as everywhere in `GFNBounds.Balance`; lifting it is Wave 3.
* **Depends on two ungraduated scaffold files**, `WeightedL2Norm.lean` (for `one_le_B_densOp`) and
  `LocalConvergenceClauses.lean` (for the four clauses). This file cannot graduate before both.
  Neither is edited here; the unprimed theorems there still carry `hB1`/`hcoer`.
* **`C`**: `local_convergence_full_mixing` carries `C₇`, as `local_convergence_full` does;
  `local_convergence_full_C_mixing` is the printed `max(1, C₇)`.
* **`sorry`-free.**

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

variable {V : Type*} [Fintype V]

/-! ### The mixing hypothesis, unpacked -/

/-- **`Core.Mixing (P, Π)` is exactly summable mixing** at the paper's `(P, Π)`: the two
structure fields `ΠP = Π` and `PΠ = Π` are theorems under `hK`, `hinv` and `λ > 0`
(`meanOp_mul_densOp`, `densOp_mul_meanOp`), so the only content of `hmx` is
`∑_{n≥0}‖Pⁿ − Π‖_{L²(λ)} < ∞`, the paper's hypothesis. -/
theorem mixing_densOp_iff_summable {K : V → V → ℝ} {lam : V → ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x) :
    Core.Mixing (densOp lam K) (meanOp lam)
      ↔ Summable fun n : ℕ => ‖densOp lam K ^ n - meanOp lam‖ :=
  ⟨fun hmx => hmx.summable, fun hs =>
    ⟨meanOp_mul_densOp (hK.toIsMarkov hlam) hlam, densOp_mul_meanOp hinv hlam, hs⟩⟩

/-- **Summable mixing implies ergodicity**, at the operator level: a `P`-fixed vector of
`L²(λ)` is `Π`-fixed. `Pⁿu = u` for every `n` while `Pⁿ → Π` (`Core.Mixing.tendsto_pow`). -/
theorem meanOp_eq_of_densOp_eq {K : V → V → ℝ} {lam : V → ℝ}
    (hmx : Core.Mixing (densOp lam K) (meanOp lam)) {u : EuclideanSpace ℝ V}
    (hu : densOp lam K u = u) : meanOp lam u = u := by
  have hpow : ∀ n : ℕ, (densOp lam K ^ n) u = u := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ]
      show (densOp lam K ^ k) (densOp lam K u) = u
      rw [hu, ih]
  have hlim : Filter.Tendsto (fun n : ℕ => (densOp lam K ^ n) u) Filter.atTop
      (nhds (meanOp lam u)) :=
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ V) u).continuous.tendsto _).comp
      hmx.tendsto_pow
  simp only [hpow] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- **Summable mixing implies ergodicity** (the paper's "`T` ergodic", `proofs.tex:593`), on
functions: a density fixed by the density action `P` is the constant `Πf = ∫f dλ`. -/
theorem eq_const_of_densAct_eq {K : V → V → ℝ} {lam : V → ℝ} (hlam : ∀ x, 0 < lam x)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam)) {f : V → ℝ}
    (hf : Core.densAct lam K f = f) : f = fun _ => Graph.meanL2 lam f := by
  have hu : densOp lam K (wtL2 lam f) = wtL2 lam f := by rw [densOp_wtL2 hlam, hf]
  have h := meanOp_eq_of_densOp_eq hmx hu
  rw [meanOp_wtL2 hlam] at h
  exact (wtL2_injective hlam h).symm

/-- **`theo:local_convergence_full`, the flow clause, at the paper's `B̂`** (`proofs.tex:612–618`):
`local_convergence_full` with `B̂ := ∑_{n≥0}‖Pⁿ − Π‖_{L²(λ)}` the mixing sum, under summable mixing
`hmx`. The coercivity of Step 2 is `lem:sigma_mixing` (`mixing_coercivity_finite`) and
`B̂ ≥ β̂₀ = 1` is `one_le_B_densOp`; neither is a hypothesis. `[Nontrivial V]` is the paper's
`β̂₀ = 1`. -/
theorem local_convergence_full_mixing [Nontrivial V] {K : V → V → ℝ} {lam w : V → ℝ}
    {gd : ℝ → ℝ} {h : ℝ → V → ℝ} {g2 a M3 wsup wmin lamMin : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hnorm0 : Graph.nrmL2 lam (h 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) (Core.Mixing.B (densOp lam K) (meanOp lam)))
          (Cinf lamMin) (C7 (C6 (Cg g2 a M3) wsup) g2 wmin)
          (rhoL g2 wmin (Core.Mixing.B (densOp lam K) (meanOp lam))) (C6 (Cg g2 a M3) wsup)) :
    ∃ cinf : ℝ,
      |cinf - 1 - Graph.meanL2 lam (h 0)|
          ≤ C7 (C6 (Cg g2 a M3) wsup) g2 wmin * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (fun x => h t x - (cinf - 1))
            ≤ 2 * Real.exp (-(rhoL g2 wmin (Core.Mixing.B (densOp lam K) (meanOp lam)) * t / 2))
                * Graph.nrmL2 lam (perpL2 lam (h 0)) :=
  local_convergence_full hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha hwsup hwmin0 hwmin
    (one_le_B_densOp hlam hmx) (mixing_coercivity_finite hinv hlam hmx) htaylor hflow hnorm0

/-- **`theo:local_convergence_full`, the gradient-descent clause, at the paper's `B̂`**
(`proofs.tex:617`, Step 6 at `:652–677`): `local_convergence_gd` with `B̂` the mixing sum,
under summable mixing `hmx`; `hcoer` and `hB1` are discharged as in
`local_convergence_full_mixing`. -/
theorem local_convergence_gd_mixing [Nontrivial V] {K : V → V → ℝ} {lam w : V → ℝ}
    {gd : ℝ → ℝ} {hk : ℕ → V → ℝ} {g2 a M3 wsup wmin lamMin gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hstep : ∀ k : ℕ, hk (k + 1) = fun x =>
      hk k x - gam * lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + hk k z) x)
    (hgam0 : 0 ≤ gam)
    (hgam : gam ≤ gamma0 g2 wmin
      (Lgd g2 wsup (Kexp g2 a M3 wsup)
        (epsW a g2 wmin (Kexp g2 a M3 wsup) (Core.Mixing.B (densOp lam K) (meanOp lam)))))
    (hnorm0 : Graph.nrmL2 lam (hk 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) (Core.Mixing.B (densOp lam K) (meanOp lam)))
          (Cinf lamMin) (C7 (C6 (Cg g2 a M3) wsup) g2 wmin)
          (rhoL g2 wmin (Core.Mixing.B (densOp lam K) (meanOp lam))) (C6 (Cg g2 a M3) wsup)) :
    ∀ k : ℕ, Graph.nrmL2 lam (perpL2 lam (hk (k + 1)))
      ≤ (1 - gam * rhoL g2 wmin (Core.Mixing.B (densOp lam K) (meanOp lam)) / 4)
          * Graph.nrmL2 lam (perpL2 lam (hk k)) :=
  local_convergence_gd hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha0 hwsup hwmin0 hwmin
    (one_le_B_densOp hlam hmx) (mixing_coercivity_finite hinv hlam hmx) htaylor hstep hgam0 hgam
    hnorm0

/-! ### The four clauses of `LocalConvergenceClauses.lean`, at the paper's `B̂` -/

/-- **`ε₀ ∈ (0, a/(16C_∞)]`** (`proofs.tex:613`, Step 4 at `:643`) at the paper's `B̂`:
`eps0_mem_Ioc` with `hB1` discharged by `one_le_B_densOp`. -/
theorem eps0_mem_Ioc_mixing [Nontrivial V] {K : V → V → ℝ} {lam w : V → ℝ}
    {g2 a M3 wsup wmin lamMin : ℝ} (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam)) :
    eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) (Core.Mixing.B (densOp lam K) (meanOp lam)))
        (Cinf lamMin) (C7 (C6 (Cg g2 a M3) wsup) g2 wmin)
        (rhoL g2 wmin (Core.Mixing.B (densOp lam K) (meanOp lam))) (C6 (Cg g2 a M3) wsup)
      ∈ Set.Ioc 0 (a / (16 * Cinf lamMin)) :=
  eps0_mem_Ioc htot hlmin0 hg2 hM3 ha hwsup hwmin0 hwmin (one_le_B_densOp hlam hmx)

/-- **`theo:local_convergence_full`, the flow clause with the printed `C := max(1, C₇)`, at the
paper's `B̂`** (`proofs.tex:612–618`, Step 5 at `:645`): `local_convergence_full_C` with `hB1`
and `hcoer` discharged. -/
theorem local_convergence_full_C_mixing [Nontrivial V] {K : V → V → ℝ} {lam w : V → ℝ}
    {gd : ℝ → ℝ} {h : ℝ → V → ℝ} {g2 a M3 wsup wmin lamMin : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam))
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hflow : IsGradientFlow K lam (fun z => lam z * w z) gd fun s x => 1 + h s x)
    (hnorm0 : Graph.nrmL2 lam (h 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) (Core.Mixing.B (densOp lam K) (meanOp lam)))
          (Cinf lamMin) (C7 (C6 (Cg g2 a M3) wsup) g2 wmin)
          (rhoL g2 wmin (Core.Mixing.B (densOp lam K) (meanOp lam))) (C6 (Cg g2 a M3) wsup)) :
    ∃ cinf : ℝ,
      |cinf - 1 - Graph.meanL2 lam (h 0)|
          ≤ max 1 (C7 (C6 (Cg g2 a M3) wsup) g2 wmin) * Graph.nrmL2 lam (perpL2 lam (h 0)) ^ 2
        ∧ ∀ t : ℝ, 0 ≤ t → Graph.nrmL2 lam (fun x => h t x - (cinf - 1))
            ≤ 2 * Real.exp (-(rhoL g2 wmin (Core.Mixing.B (densOp lam K) (meanOp lam)) * t / 2))
                * Graph.nrmL2 lam (perpL2 lam (h 0)) :=
  local_convergence_full_C hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha hwsup hwmin0 hwmin
    (one_le_B_densOp hlam hmx) (mixing_coercivity_finite hinv hlam hmx) htaylor hflow hnorm0

/-- **`γ₀ > 0`** (`proofs.tex:617`, formula at Step 6, `:652`) at the paper's `B̂`:
`gamma0_pos_of_weights`, whose only `B̂` hypothesis is `0 ≤ B̂`. That is `Core.Mixing.B_nonneg`, a
tsum of norms, so **neither `hmx` nor `[Nontrivial V]` is needed** here. -/
theorem gamma0_pos_of_weights_mixing {K : V → V → ℝ} {lam w : V → ℝ} {g2 a M3 wsup wmin : ℝ}
    (htot : ∑ x, lam x = 1) (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha0 : 0 ≤ a)
    (hwsup : ∀ x, |w x| ≤ wsup) (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x) :
    0 < gamma0 g2 wmin
      (Lgd g2 wsup (Kexp g2 a M3 wsup)
        (epsW a g2 wmin (Kexp g2 a M3 wsup) (Core.Mixing.B (densOp lam K) (meanOp lam)))) :=
  gamma0_pos_of_weights htot hg2 hM3 ha0 hwsup hwmin0 hwmin (Core.Mixing.B_nonneg _ _)

/-- **`theo:local_convergence_full`, "the gradient descent … is well defined", at the paper's
`B̂`** (`proofs.tex:617`, proof `:662`): `local_convergence_gd_welldefined` with `hB1` and `hcoer`
discharged. -/
theorem local_convergence_gd_welldefined_mixing [Nontrivial V] {K : V → V → ℝ} {lam w : V → ℝ}
    {g gd : ℝ → ℝ} {hk : ℕ → V → ℝ} {g2 a M3 wsup wmin lamMin gam : ℝ}
    (hK : Core.IsMarkovOn lam K) (hinv : Core.IsInvariant lam K) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hlmin0 : 0 < lamMin) (hlmin : ∀ x, lamMin ≤ lam x)
    (hg2 : 0 < g2) (hM3 : 0 ≤ M3) (ha : 0 < a) (hwsup : ∀ x, |w x| ≤ wsup)
    (hwmin0 : 0 < wmin) (hwmin : ∀ x, wmin ≤ w x)
    (hmx : Core.Mixing (densOp lam K) (meanOp lam))
    (hg : ∀ y : ℝ, |y - 1| < a → HasDerivAt g (gd y) y)
    (htaylor : ∀ y : ℝ, |y - 1| ≤ a → |gd y - g2 * (y - 1)| ≤ M3 / 2 * (y - 1) ^ 2)
    (hstep : ∀ k : ℕ, hk (k + 1) = fun x =>
      hk k x - gam * lossGrad K lam (fun z => lam z * w z) gd (fun z => 1 + hk k z) x)
    (hgam0 : 0 ≤ gam)
    (hgam : gam ≤ gamma0 g2 wmin
      (Lgd g2 wsup (Kexp g2 a M3 wsup)
        (epsW a g2 wmin (Kexp g2 a M3 wsup) (Core.Mixing.B (densOp lam K) (meanOp lam)))))
    (hnorm0 : Graph.nrmL2 lam (hk 0)
      ≤ eps0 (epsW a g2 wmin (Kexp g2 a M3 wsup) (Core.Mixing.B (densOp lam K) (meanOp lam)))
          (Cinf lamMin) (C7 (C6 (Cg g2 a M3) wsup) g2 wmin)
          (rhoL g2 wmin (Core.Mixing.B (densOp lam K) (meanOp lam))) (C6 (Cg g2 a M3) wsup)) :
    ∀ k : ℕ, (∀ x : V, 0 < 1 + hk k x)
      ∧ (∀ x : V, |ratio K lam (fun z => 1 + hk k z) x - 1| ≤ 2 * a / 3)
      ∧ ∀ d : V → ℝ,
          HasDerivAt
            (fun t : ℝ => loss K lam (fun z => lam z * w z) (fun x => 1 + hk k x + t * d x) g)
            (Graph.ipL2 lam (lossGrad K lam (fun z => lam z * w z) gd fun z => 1 + hk k z) d) 0 :=
  local_convergence_gd_welldefined hK hinv hlam htot hlmin0 hlmin hg2 hM3 ha hwsup hwmin0 hwmin
    (one_le_B_densOp hlam hmx) (mixing_coercivity_finite hinv hlam hmx) hg htaylor hstep hgam0
    hgam hnorm0

end GFNBounds.Balance
