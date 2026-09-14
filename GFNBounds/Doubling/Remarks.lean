import GFNBounds.Doubling.Cramer
import GFNBounds.Doubling.OperatorFiniteSum
import GFNBounds.Balance.WeightedL2Norm

/-!
# The renewal form of the cut balance, and the two constants written `B̂`

**`rem:doubling_renewal`** — `app_doubling.tex:1285–1316` (a remark; no proof environment).

**`rem:doubling_two_constants`** — `app_doubling.tex:264–277` (a remark; no proof environment).

Both read against draft commit `3194054`.

> (`rem:doubling_renewal`) In the variable `x = log₂ m` the cut balance `eq:doubling_cut`, read on
> the rescaled profile `u_m` of Definition `def:doubling_decay_notation`, is heuristically, to
> leading order, the renewal equation `V(x) = ∫₀¹ k(v) V(x − v) dv`, with the kernel `k` of
> Lemma `lem:doubling_cramer_root`(2), whose normalization `∫₀¹ k = 1` is the Cramér relation
> `eq:doubling_cramer_form`; that kernel has a density, hence is non-lattice. Let `V` be a bounded
> measurable solution of that limit equation on `ℝ` and put `k̄(v) := ∫_v^1 k(w) dw`, so that
> `k̄(0) = 1`, `k̄(1) = 0` and `k̄' = −k`. The right side `∫_{x−1}^x k(x − y) V(y) dy` of the limit
> equation is Lipschitz in `x`, `k` being bounded and of bounded variation on `[0,1]` and `V`
> bounded, so `V` is Lipschitz and the boundary terms below are the Leibniz terms at every `x`.
> Then
> `G(x) := ∫₀¹ k̄(v) V(x − v) dv = ∫_{x−1}^x k̄(x − y) V(y) dy`,
> `G'(x) = k̄(0) V(x) − k̄(1) V(x − 1) − ∫₀¹ k(v) V(x − v) dv = 0`,
> the identity for `G'` by differentiating the rightmost expression for `G` and using the limit
> equation; so `G` is constant, and if `V` has a limit at `+∞`, dominated convergence in the
> leftmost expression makes that limit `G` divided by `∫₀¹ k̄(v) dv = ∫₀¹ v k(v) dv`, the mean of
> the kernel, which is `ψ'(p_*)/(p_* ln 2) = τ/(τ − 1) − 1/(p_* ln 2)` with `ψ(t) := c(2^t − 1) − t`
> the function of Lemma `lem:doubling_cramer_root` — integrate `v ↦ v 2^{p_* v}` and use
> `eq:doubling_cramer_form`. This computation is made on the limit equation and not on
> `eq:doubling_cut`, whose window starts at `⌈m/2⌉` and whose coefficients carry `1/(j+1)` and
> `1 − ε(m)`, and this remark does not derive the constant `C` of Theorem `theo:doubling_sharp`;
> `C` is the linear functional of Proposition `prop:doubling_constant`. The convergence and its
> rate `eq:doubling_rate` are Theorem `theo:doubling_sharp`, and that the decay carries no
> log-periodic term is Remark `rem:doubling_no_logperiodic`.

> (`rem:doubling_two_constants`) The constant `eq:doubling_Bhat` is the norm of the diffusion
> operator, not the mixing sum `Σₙ β̂ₙ` that Lemma `lem:sigma_mixing` also writes `B̂`, and item
> (3) of Lemma `lem:doubling_operator` orders the two on any finite irreducible chain. They need
> not coincide: on the two-state chain that flips with probability `3/4`, whose invariant
> probability is uniform and whose centred functions are eigenfunctions of its transition
> operator at the eigenvalue `−1/2`, `B̂ = 2/3` while `β̂ₙ = 2^{−n}` for every `n ≥ 0` and
> `Σₙ β̂ₙ = 2`; at the flip probability `1/2` both equal `1`. Numerically they also differ on the
> truncation at which §`sec:doubling_measured` measures both. On a finite irreducible chain,
> wherever the series of that item converges,
> `(Sθ)(x) = Σ_{n≥0} (E(θ(Xₙ) | X₀ = x) − λ(θ))` — the operator is read along backward
> trajectories, `(P⋆f)(x) = E(f(X₁) | X₀ = x)` for `f ∈ L²(λ)`.

## What is proved

### `rem:doubling_renewal`

| paper claim | declaration |
|---|---|
| `∫₀¹ k = 1` is the Cramér relation | `integral_kern` (from `cramer_kernel_integral`); as a probability law, `kernMeasure_univ` |
| the kernel has a density | `kernMeasure_absolutelyContinuous` |
| hence is non-lattice | `kernMeasure_nonlattice`: no lattice `a + hℤ` carries the law, for any `a`, `h` |
| `k̄(0) = 1`, `k̄(1) = 0`, `k̄' = −k` | `kbar_zero` (uses the Cramér relation), `kbar_one`, `hasDerivAt_kbar` (at every `v ∈ ℝ`) |
| `k` bounded on `[0,1]` | `abs_kern_le`, with the explicit bound `kernSup c p = c ln 2 (1 + τ)` |
| `k` of bounded variation on `[0,1]` | `kern_boundedVariationOn` (via `abs_kern_sub_le`, Lipschitz constant `kernLip c p = c (ln 2)² |p| (1 + τ)`) |
| the right side is `∫_{x−1}^x k(x−y)V(y)dy` | `rhs_eq_shift` |
| the right side is Lipschitz in `x` | `renewal_rhs_lipschitz`, constant `M(2·kernSup + kernLip)`, from the general `conv_lipschitz` |
| so `V` is Lipschitz | `renewal_lipschitz`, same constant |
| `G(x) = ∫₀¹ k̄(v)V(x−v)dv = ∫_{x−1}^x k̄(x−y)V(y)dy` | `Gfun` (the leftmost expression), `Gfun_eq_shift` |
| `G'(x) = k̄(0)V(x) − k̄(1)V(x−1) − ∫₀¹ k(v)V(x−v)dv`, at every `x` | `hasDerivAt_Gfun` (for continuous `V`) |
| `… = 0`, by the limit equation | `renewal_hasDerivAt_G` |
| so `G` is constant | `renewal_G_const` |
| if `V → ℓ` at `+∞`, `ℓ = G / ∫₀¹ k̄` (dominated convergence) | `renewal_limit` |
| `∫₀¹ k̄ = ∫₀¹ v k(v) dv` | `integral_kbar_eq_kernMean` (both in closed form) |
| `= ψ'(p_*)/(p_* ln 2) = τ/(τ−1) − 1/(p_* ln 2)` | `kernMean_eq` |

### `rem:doubling_two_constants`

| paper claim | declaration |
|---|---|
| `P⋆` is the `L²(λ)`-adjoint of `P`, so `‖P⋆ⁿ − Π‖ = β̂ₙ` (the finite face of `lem:doubling_operator`(1), used here) | `inner_funOp`, `funOp_eq_star`, `norm_funOp_pow_sub` |
| item (3) orders the two on a finite chain: `B̂ ≤ Σ β̂ₙ`, vacuous when `+∞` | `bhat_le_mixing_sum` |
| flip `3/4`: invariant probability uniform (and unique) | `flipK_isInvariant`, `flipK_invariant_unique` |
| centred functions are eigenfunctions of `P⋆` at `−1/2` | `flipK_funAct_centred` (at `1 − 2q` for every `q`) |
| `B̂ = 2/3`, `β̂ₙ = 2^{−n}` for every `n ≥ 0`, `Σ β̂ₙ = 2` | `two_constants_flip_three_quarters` (from `norm_diffusion_flipK`, `beta_flipK`, `B_flipK`) |
| they need not coincide | last conjunct of `two_constants_flip_three_quarters` |
| flip `1/2`: both equal `1` | `two_constants_flip_half`; the chain is `Freezing.lean`'s `twoStateK` (`flipK_half_eq_twoStateK`) |
| wherever the series converges, `(Sθ)(x) = Σ_{n≥0}((P⋆ⁿθ)(x) − λ(θ))` | `diffusion_apply_eq_series` (the series as the limit of its partial sums), with `S = U` from `inverse_sub_eq_of_tendsto` |

## SCOPE (disclosed)

### `rem:doubling_renewal`

* **The heuristic sentence is not a target.** "In the variable `x = log₂ m` the cut balance … is
  heuristically, to leading order, the renewal equation" is marked heuristic in the text and is
  not stated. Neither are the closing pointers (`theo:doubling_sharp`, `prop:doubling_constant`,
  `rem:doubling_no_logperiodic`): they are citations, and "this remark does not derive `C`" is a
  disclaimer with nothing to certify.
* **Wider parameter range, in the safe direction.** The remark sits in the setting of
  `def:doubling_decay_notation` (`s = 1`, `0 < c < 1`, so `p_* > 1`). Every statement here holds for
  any `c > 0` and any non-zero root `p` of `ψ` (`hp0 : p ≠ 0`, `hp : psi c p = 0`, as in
  `Cramer.lean`); `renewal_rhs_lipschitz`, `renewal_lipschitz`, `abs_kern_le` and
  `kern_boundedVariationOn` do not even need the root. The specialisation to `0 < c < 1` is
  immediate (`cramer_root_gt_one`) and is not restated.
* **"Bounded measurable solution"** is carried as `Measurable V`, an explicit bound
  `∀ x, |V x| ≤ M`, and the limit equation at **every** `x ∈ ℝ` (`heq`). The paper's equation is
  pointwise, so no almost-everywhere reading is dropped.
* **"Bounded and of bounded variation" is proved, but the Lipschitz sentence is proved through a
  Lipschitz bound on `k`, not through its variation.** `conv_lipschitz` takes a kernel bounded by
  `K₀` and `K₁`-Lipschitz on `[0,1]`, which the paper's `k` is (`abs_kern_sub_le`); the general
  bounded-variation version of the estimate is not stated. For the paper's `k` the conclusion is
  the paper's, with the explicit constant `M(2K₀ + K₁)`.
* **`k̄' = −k` is certified at every `v ∈ ℝ`**, `k` being read by its formula off `[0,1]`; the
  remark needs it on `[0,1]`.
* **The Leibniz computation is certified in closed form.** `hasDerivAt_Gfun` differentiates
  `∫_{x−1}^x k̄(x−y)V(y)dy` by writing `k̄(v) = (c/p)(τ − 2^{pv})` (`kbar_eq`), splitting the
  integrand into two primitives and applying the fundamental theorem of calculus at `x` and
  `x − 1`; the resulting derivative is then shown equal to the paper's
  `k̄(0)V(x) − k̄(1)V(x−1) − ∫₀¹ k(v)V(x−v)dv`. The general Leibniz rule for a `C¹` kernel is not
  stated. Continuity of `V` is the hypothesis there, and is supplied by `renewal_lipschitz` in
  `renewal_hasDerivAt_G`, as in the paper.
* **The limit is stated as an equation `ℓ = G(x₀)/∫₀¹ k̄` at an arbitrary `x₀`**, `G` being
  constant; positivity of `∫₀¹ k̄` (`kernMean_pos`) is proved, not assumed.
* **The limit clause is tautological on `ℝ` — a finding about the paper, sent to the author
  (2026-09-14).** By the Choquet–Deny theorem in its bounded-continuous form (the law of `−v` has
  support `[−1,0]`, which generates `ℝ`), every bounded continuous — here Lipschitz — solution of
  the limit equation on all of `ℝ` is constant; equivalently `V = V∗k` in tempered distributions
  with `|k̂(ξ)| < 1` for `ξ ≠ 0` forces `supp V̂ ⊂ {0}`. This is **not** proved or used here. The
  remark's hypothesis class is therefore the constants, which inhabit it
  (`const_isRenewalSolution`), and its limit clause reads `ℓ = ℓ`; its "non-lattice" sentence is
  used nowhere. The content the remark presumably intends is the one-sided problem (the equation
  for `x ≥ x₀` with data on `[x₀−1, x₀)`), where the key renewal theorem needs non-lattice; a
  restatement there would change sentences this file certifies. The Lean states exactly the
  current text.

### `rem:doubling_two_constants`

* **Finite chains on the `WeightedL2` layer.** `L²(λ)` is `EuclideanSpace ℝ V` through the
  weighting `wtL2` (`Balance/WeightedL2.lean`), with `V` a `Fintype`, `λ > 0` pointwise and
  `∑ λ = 1`; `Π = meanOp λ`, `P = densOp λ K`, and `P⋆ = funOp λ K` is new here. The mixing sum is
  `Core.Mixing.B (densOp λ K) (meanOp λ) = ∑' n, ‖Pⁿ − Π‖`, which is `lem:sigma_mixing`'s `B̂`
  (`WeightedL2Norm.lean`), and `B̂ = ‖Ring.inverse (1 − P⋆ + Π) − Π‖` is `eq:doubling_Bhat`.
* **"Any finite irreducible chain" is read as any finite Markov chain with a positive invariant
  probability.** Irreducibility is not used: bounded partial sums of `Σ β̂ₙ` already make
  `Id − P⋆ + Π` invertible (`inverse_sub_eq_of_tendsto`, from `resolvent_inverse`), and when they
  are unbounded the statement is vacuous, as the paper says. A finite irreducible chain has a
  positive invariant probability, so the paper's case is covered; `λ > 0` and `λ` given, rather
  than constructed, are the modelling choices of the layer. This is **wider** than
  `Doubling/OperatorFiniteSum.lean`'s `Stat.inverse_sub_piL2_le_sum_betaHat`, which certifies the
  ordering on the doubling truncation only.
* **The numerical sentence is not a target** (author's ruling R18): "Numerically they also differ
  on the truncation at which §`sec:doubling_measured` measures both" reports a measurement
  (`exp20`), and nothing here states it.
* **The trajectory reading is certified as a pointwise series, not as an expectation.** The
  `n`-th term is `(Core.funAct K)^[n] θ x`, the `n`-fold function action `∑_y Tⁿ(x→y)θ(y)`; the
  remark's display writes it as `E(θ(Xₙ) | X₀ = x)`, and that identification is **not stated
  here**. On a finite chain it is a finite path-law identity (routine, as `lem:doubling_descent`
  closed it), not obstruction 1. "The series" is read as the limit of its partial sums (operator-norm convergence of
  item (3)'s series, `hconv`), not as an unconditional `HasSum`.
* **The eigenvalue sentence is certified for the function action `P⋆`** — the paper's "transition
  operator" — on `V → ℝ`; on the flip chain `P = P⋆` anyway (`densOp_flipK`, `funOp_flipK`).
* **`β̂ₙ = 2^{−n}` is stated as `((2 : ℝ)^n)⁻¹`.**
* `sorry`-free; `#print axioms` on every declaration returns `[propext, Classical.choice, Quot.sound]`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (renewal) `0 < c < 1`, `p_*` the Cramér root | ⚠ widened to `0 < c`, `p ≠ 0`, `psi c p = 0` (safe direction; see SCOPE) |
| (renewal) `V` bounded | ✓ `hM : ∀ x, |V x| ≤ M` |
| (renewal) `V` measurable | ✓ `hVm : Measurable V` |
| (renewal) `V` solves the limit equation on `ℝ` | ✓ `heq : ∀ x, V x = ∫ v in 0..1, kern c p v * V (x − v)` |
| (renewal) `V` has a limit at `+∞` | ✓ `hlim : Tendsto V atTop (𝓝 ℓ)` |
| (two constants) a finite irreducible chain | ⚠ `Fintype V`, `Core.IsMarkov K`; irreducibility not needed |
| (two constants) `λ` its invariant probability | ✓ `Core.IsInvariant λ K`, `∑ λ = 1`; ⚠ `λ > 0` pointwise (automatic when irreducible) |
| (two constants) `L²(λ)`, `Π` the `λ`-mean projection | ✓ `EuclideanSpace ℝ V` via `wtL2`, `meanOp λ` |
| (two constants) `β̂ₙ = ‖Pⁿ − Π‖`, `P` the density action | ✓ `Core.Mixing.beta (densOp λ K) (meanOp λ) n` |
| (two constants) `S = (Id − P⋆ + Π)^{-1} − Π`, `B̂ = ‖S‖` | ✓ `Ring.inverse (1 − funOp λ K + meanOp λ) − meanOp λ`, no inverse assumed |
| (two constants) "wherever the series of that item converges" | ✓ `hconv : Tendsto (partialSum P⋆ Π) atTop (𝓝 U)` |
| (witness) the chain flipping with probability `3/4` (resp. `1/2`) | ✓ `flipK (3/4)` (resp. `flipK (1/2) = twoStateK`), `λ = twoStateLam` |

## Inhabitation (kb `0025`)

* The limit equation: every constant solves it (`const_isRenewalSolution`); `renewal_limit_check`
  applies `renewal_limit` at `c = 1/2`, with the Cramér root produced by `cramer_root_exists`.
* The finite-chain hypotheses: the flip chain meets them (`flipK_isMarkov`, `flipK_isInvariant`,
  `twoStateLam_pos`, `twoStateLam_sum`); `bhat_le_mixing_sum_check` applies `bhat_le_mixing_sum`
  there; `diffusion_series_converges_check` exhibits the operator-norm convergence
  `diffusion_apply_eq_series` hypothesises; `mixing_flipK` exhibits `Core.Mixing`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling.Remarks

open Real MeasureTheory Set Filter Topology

section Renewal

/-- The kernel `k(v) = c ln 2 · 2^{p v}` of `lem:doubling_cramer_root`(2). -/
noncomputable def kern (c p v : ℝ) : ℝ := c * log 2 * (2 : ℝ) ^ (p * v)

theorem continuous_kern (c p : ℝ) : Continuous (kern c p) := by
  show Continuous fun v : ℝ => c * log 2 * (2 : ℝ) ^ (p * v)
  exact continuous_const.mul (continuous_two_rpow.comp (continuous_const.mul continuous_id))

theorem hasDerivAt_kern (c p v : ℝ) :
    HasDerivAt (kern c p) (c * log 2 * ((2 : ℝ) ^ (p * v) * log 2 * p)) v := by
  have h1 : HasDerivAt (fun w : ℝ => p * w) p v := by
    simpa using (hasDerivAt_id v).const_mul p
  have h2 := (hasDerivAt_two_rpow (p * v)).comp v h1
  exact h2.const_mul (c * log 2)

theorem kern_pos {c : ℝ} (hc : 0 < c) (p v : ℝ) : 0 < kern c p v := by
  have := two_rpow_pos (p * v)
  have := log_two_pos
  unfold kern
  positivity

theorem two_rpow_mul_le {p v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    (2 : ℝ) ^ (p * v) ≤ 1 + (2 : ℝ) ^ p := by
  have hp2 := two_rpow_pos p
  rcases le_or_gt 0 p with hp | hp
  · have hle : p * v ≤ p := by nlinarith [hv.1, hv.2]
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle
    linarith
  · have hle : p * v ≤ 0 := by nlinarith [hv.1, hv.2]
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle
    rw [Real.rpow_zero] at this
    linarith

/-- The explicit sup bound of the kernel on `[0,1]`: `K₀ := c ln 2 (1 + τ)`. -/
noncomputable def kernSup (c p : ℝ) : ℝ := c * log 2 * (1 + (2 : ℝ) ^ p)

/-- The explicit Lipschitz constant of the kernel on `[0,1]`: `K₁ := c (ln 2)² |p| (1 + τ)`. -/
noncomputable def kernLip (c p : ℝ) : ℝ := c * log 2 * log 2 * |p| * (1 + (2 : ℝ) ^ p)

/-- **`rem:doubling_renewal`, "`k` being bounded … on `[0,1]`"**: `|k(v)| ≤ c ln 2 (1 + τ)`. -/
theorem abs_kern_le {c : ℝ} (hc : 0 < c) (p : ℝ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    |kern c p v| ≤ kernSup c p := by
  rw [abs_of_pos (kern_pos hc p v)]
  have h := two_rpow_mul_le (p := p) hv
  have hL : 0 < c * log 2 := mul_pos hc log_two_pos
  unfold kern kernSup
  exact mul_le_mul_of_nonneg_left h hL.le

theorem kernLip_nonneg {c : ℝ} (hc : 0 < c) (p : ℝ) : 0 ≤ kernLip c p := by
  have := log_two_pos
  have := two_rpow_pos p
  unfold kernLip
  positivity

/-- **`rem:doubling_renewal`, the kernel is Lipschitz on `[0,1]`**, with constant
`c (ln 2)² |p| (1 + τ)` — the form in which its regularity enters `conv_lipschitz`. -/
theorem abs_kern_sub_le {c : ℝ} (hc : 0 < c) (p : ℝ) {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) : |kern c p u - kern c p v| ≤ kernLip c p * |u - v| := by
  have hL := log_two_pos
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := kern c p)
    (f' := fun w => c * log 2 * ((2 : ℝ) ^ (p * w) * log 2 * p)) (s := Icc (0 : ℝ) 1)
    (C := kernLip c p) (fun w _ => (hasDerivAt_kern c p w).hasDerivWithinAt)
    (fun w hw => ?_) (convex_Icc 0 1) hv hu
  · simpa [Real.norm_eq_abs] using h
  · have h2 := two_rpow_mul_le (p := p) hw
    have hpos := two_rpow_pos (p * w)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hc, abs_of_pos hL,
      abs_of_pos hpos]
    unfold kernLip
    have hc' : 0 ≤ c * log 2 * log 2 * |p| := by positivity
    calc c * log 2 * ((2 : ℝ) ^ (p * w) * log 2 * |p|)
        = c * log 2 * log 2 * |p| * (2 : ℝ) ^ (p * w) := by ring
      _ ≤ c * log 2 * log 2 * |p| * (1 + (2 : ℝ) ^ p) := mul_le_mul_of_nonneg_left h2 hc'

/-- **`rem:doubling_renewal`, "`k` being … of bounded variation on `[0,1]`"** — it is Lipschitz
there. -/
theorem kern_boundedVariationOn {c : ℝ} (hc : 0 < c) (p : ℝ) :
    BoundedVariationOn (kern c p) (Icc (0 : ℝ) 1) := by
  have hlip : LipschitzOnWith (Real.toNNReal (kernLip c p)) (kern c p) (Icc (0 : ℝ) 1) := by
    refine LipschitzOnWith.of_dist_le' fun u hu v hv => ?_
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_kern_sub_le hc p hu hv
  have h := hlip.locallyBoundedVariationOn 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  simpa [Set.inter_self] using h

end Renewal

section Convolution

/-- A bounded measurable function is interval integrable on every interval. -/
theorem intervalIntegrable_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := M) ?_ hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
  exact ((measure_mono Set.uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne

variable {k V : ℝ → ℝ} {K0 K1 M : ℝ}

theorem intervalIntegrable_mul_shift (hk : Continuous k) (hV : Measurable V)
    (hM : ∀ x, |V x| ≤ M) (x a b : ℝ) :
    IntervalIntegrable (fun u => k u * V (x - u)) volume a b := by
  have hVs : IntervalIntegrable (fun u => V (x - u)) volume a b :=
    intervalIntegrable_of_abs_le (hV.comp (measurable_const.sub measurable_id))
      (fun u => hM (x - u)) a b
  exact hVs.continuousOn_mul hk.continuousOn

theorem intervalIntegrable_mul_shift' (hk : Continuous k) (hV : Measurable V)
    (hM : ∀ x, |V x| ≤ M) (x h a b : ℝ) :
    IntervalIntegrable (fun u => k (u + h) * V (x - u)) volume a b :=
  intervalIntegrable_mul_shift (k := fun u => k (u + h)) (hk.comp (continuous_id.add
    continuous_const)) hV hM x a b

/-- The one-sided estimate behind the Lipschitz bound: for `0 ≤ h`,
`|F(x+h) − F(x)| ≤ M(2K₀ + K₁)h` with `F(x) = ∫₀¹ k(v)V(x−v)dv`. -/
theorem conv_sub_le (hk : Continuous k) (hK0 : ∀ v ∈ Icc (0 : ℝ) 1, |k v| ≤ K0)
    (hK1 : 0 ≤ K1) (hK1' : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, |k u - k v| ≤ K1 * |u - v|)
    (hV : Measurable V) (hM : ∀ x, |V x| ≤ M) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |(∫ v in (0 : ℝ)..1, k v * V (x + h - v)) - ∫ v in (0 : ℝ)..1, k v * V (x - v)|
      ≤ M * (2 * K0 + K1) * h := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK00 : 0 ≤ K0 := (abs_nonneg _).trans (hK0 0 ⟨le_rfl, zero_le_one⟩)
  -- a crude bound on each integral
  have hbound : ∀ z : ℝ, |∫ v in (0 : ℝ)..1, k v * V (z - v)| ≤ K0 * M := by
    intro z
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := K0 * M) (f := fun v => k v * V (z - v)) (fun v hv => by
        rw [Set.uIoc_of_le zero_le_one] at hv
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hK0 v ⟨hv.1.le, hv.2⟩) (hM _) (abs_nonneg _) hK00)
    simpa [Real.norm_eq_abs] using this
  rcases le_or_gt 1 h with h1 | h1
  · have e1 := hbound (x + h)
    have e2 := hbound x
    have : |(∫ v in (0 : ℝ)..1, k v * V (x + h - v)) - ∫ v in (0 : ℝ)..1, k v * V (x - v)|
        ≤ 2 * (K0 * M) := by
      calc _ ≤ |∫ v in (0 : ℝ)..1, k v * V (x + h - v)| + |∫ v in (0 : ℝ)..1, k v * V (x - v)| :=
            abs_sub _ _
        _ ≤ 2 * (K0 * M) := by linarith
    have hKM : 0 ≤ K1 * M := mul_nonneg hK1 hM0
    nlinarith [mul_nonneg hK00 hM0]
  · -- `0 ≤ h < 1`: shift and split
    have h1' : 0 ≤ 1 - h := by linarith
    have eshift : (∫ v in (0 : ℝ)..1, k v * V (x + h - v))
        = ∫ u in -h..1 - h, k (u + h) * V (x - u) := by
      have := intervalIntegral.integral_comp_add_right (a := -h) (b := 1 - h)
        (fun v => k v * V (x + h - v)) h
      simp only [neg_add_cancel, sub_add_cancel] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun u _ => ?_
      congr 2
      ring
    have hI := intervalIntegrable_mul_shift hk hV hM x
    have hI' := intervalIntegrable_mul_shift' hk hV hM x h
    have esplit1 : (∫ u in -h..1 - h, k (u + h) * V (x - u))
        = (∫ u in -h..0, k (u + h) * V (x - u)) + ∫ u in (0 : ℝ)..1 - h, k (u + h) * V (x - u) :=
      (intervalIntegral.integral_add_adjacent_intervals (hI' _ _) (hI' _ _)).symm
    have esplit2 : (∫ u in (0 : ℝ)..1, k u * V (x - u))
        = (∫ u in (0 : ℝ)..1 - h, k u * V (x - u)) + ∫ u in 1 - h..1, k u * V (x - u) :=
      (intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _)).symm
    have esub : (∫ u in (0 : ℝ)..1 - h, k (u + h) * V (x - u))
        - (∫ u in (0 : ℝ)..1 - h, k u * V (x - u))
        = ∫ u in (0 : ℝ)..1 - h, (k (u + h) - k u) * V (x - u) := by
      rw [← intervalIntegral.integral_sub (hI' _ _) (hI _ _)]
      refine intervalIntegral.integral_congr fun u _ => ?_
      ring
    have bA : |∫ u in -h..0, k (u + h) * V (x - u)| ≤ K0 * M * h := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -h) (b := 0)
        (C := K0 * M) (f := fun u => k (u + h) * V (x - u)) (fun u hu => by
          rw [Set.uIoc_of_le (by linarith)] at hu
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hK0 _ ⟨by linarith [hu.1], by linarith [hu.2]⟩) (hM _)
            (abs_nonneg _) hK00)
      simpa [Real.norm_eq_abs, abs_of_nonneg hh] using this
    have bC : |∫ u in 1 - h..1, k u * V (x - u)| ≤ K0 * M * h := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1 - h) (b := 1)
        (C := K0 * M) (f := fun u => k u * V (x - u)) (fun u hu => by
          rw [Set.uIoc_of_le (by linarith)] at hu
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hK0 _ ⟨by linarith [hu.1], hu.2⟩) (hM _) (abs_nonneg _) hK00)
      simpa [Real.norm_eq_abs, abs_of_nonneg hh] using this
    have bB : |∫ u in (0 : ℝ)..1 - h, (k (u + h) - k u) * V (x - u)| ≤ K1 * h * M := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1 - h)
        (C := K1 * h * M) (f := fun u => (k (u + h) - k u) * V (x - u)) (fun u hu => by
          rw [Set.uIoc_of_le h1'] at hu
          rw [Real.norm_eq_abs, abs_mul]
          have hk := hK1' (u + h) ⟨by linarith [hu.1], by linarith [hu.2]⟩ u
            ⟨hu.1.le, by linarith [hu.2]⟩
          rw [add_sub_cancel_left, abs_of_nonneg hh] at hk
          exact mul_le_mul hk (hM _) (abs_nonneg _) (mul_nonneg hK1 hh))
      have hC0 : 0 ≤ K1 * h * M := mul_nonneg (mul_nonneg hK1 hh) hM0
      have e : ‖(1 : ℝ) - h - 0‖ ≤ 1 := by
        rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg h1']; linarith
      calc |∫ u in (0 : ℝ)..1 - h, (k (u + h) - k u) * V (x - u)|
          ≤ K1 * h * M * ‖(1 : ℝ) - h - 0‖ := by simpa [Real.norm_eq_abs] using this
        _ ≤ K1 * h * M * 1 := mul_le_mul_of_nonneg_left e hC0
        _ = K1 * h * M := mul_one _
    rw [eshift, esplit1, esplit2]
    have hre : (∫ u in -h..0, k (u + h) * V (x - u)) + (∫ u in (0 : ℝ)..1 - h, k (u + h) * V (x - u))
        - ((∫ u in (0 : ℝ)..1 - h, k u * V (x - u)) + ∫ u in 1 - h..1, k u * V (x - u))
        = (∫ u in -h..0, k (u + h) * V (x - u))
          + ((∫ u in (0 : ℝ)..1 - h, k (u + h) * V (x - u))
            - (∫ u in (0 : ℝ)..1 - h, k u * V (x - u)))
          - ∫ u in 1 - h..1, k u * V (x - u) := by ring
    rw [hre, esub]
    calc _ ≤ |(∫ u in -h..0, k (u + h) * V (x - u))
              + ∫ u in (0 : ℝ)..1 - h, (k (u + h) - k u) * V (x - u)|
            + |∫ u in 1 - h..1, k u * V (x - u)| := abs_sub _ _
      _ ≤ |∫ u in -h..0, k (u + h) * V (x - u)|
            + |∫ u in (0 : ℝ)..1 - h, (k (u + h) - k u) * V (x - u)|
            + |∫ u in 1 - h..1, k u * V (x - u)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ K0 * M * h + K1 * h * M + K0 * M * h := by gcongr
      _ = M * (2 * K0 + K1) * h := by ring

/-- **`rem:doubling_renewal`, "the right side is Lipschitz in `x`, `k` being bounded and of bounded
variation on `[0,1]` and `V` bounded"**, for a kernel bounded by `K₀` and `K₁`-Lipschitz on
`[0,1]`: `x ↦ ∫₀¹ k(v)V(x−v)dv` is `M(2K₀ + K₁)`-Lipschitz. -/
theorem conv_lipschitz (hk : Continuous k) (hK0 : ∀ v ∈ Icc (0 : ℝ) 1, |k v| ≤ K0)
    (hK1 : 0 ≤ K1) (hK1' : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, |k u - k v| ≤ K1 * |u - v|)
    (hV : Measurable V) (hM : ∀ x, |V x| ≤ M) :
    LipschitzWith (Real.toNNReal (M * (2 * K0 + K1)))
      (fun x => ∫ v in (0 : ℝ)..1, k v * V (x - v)) := by
  refine LipschitzWith.of_dist_le' fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total y x with hxy | hxy
  · have := conv_sub_le hk hK0 hK1 hK1' hV hM y (h := x - y) (by linarith)
    rw [add_sub_cancel] at this
    rwa [abs_of_nonneg (by linarith : 0 ≤ x - y)]
  · have := conv_sub_le hk hK0 hK1 hK1' hV hM x (h := y - x) (by linarith)
    rw [add_sub_cancel, abs_sub_comm] at this
    rwa [abs_sub_comm x y, abs_of_nonneg (by linarith : 0 ≤ y - x)]

end Convolution

section RenewalMain

variable {c p : ℝ}

/-- **`rem:doubling_renewal`, "whose normalization `∫₀¹ k = 1` is the Cramér relation"**: the
kernel of `lem:doubling_cramer_root`(2) integrates to `1` at a root of `ψ`
(`cramer_kernel_integral`). -/
theorem integral_kern (hp0 : p ≠ 0) (hp : psi c p = 0) : ∫ v in (0 : ℝ)..1, kern c p v = 1 :=
  cramer_kernel_integral hp0 hp

/-- `k̄(v) := ∫_v^1 k(w) dw`. -/
noncomputable def kbar (c p v : ℝ) : ℝ := ∫ w in v..1, kern c p w

/-- **`rem:doubling_renewal`, `k̄(0) = 1`** — the Cramér relation again. -/
theorem kbar_zero (hp0 : p ≠ 0) (hp : psi c p = 0) : kbar c p 0 = 1 := integral_kern hp0 hp

/-- **`rem:doubling_renewal`, `k̄(1) = 0`**. -/
theorem kbar_one : kbar c p 1 = 0 := intervalIntegral.integral_same

/-- **`rem:doubling_renewal`, `k̄' = −k`**, at every `v`. -/
theorem hasDerivAt_kbar (v : ℝ) : HasDerivAt (kbar c p) (-kern c p v) v :=
  intervalIntegral.integral_hasDerivAt_left ((continuous_kern c p).intervalIntegrable _ _)
    ((continuous_kern c p).stronglyMeasurableAtFilter _ _) (continuous_kern c p).continuousAt

/-- `2^{p·w}` has derivative `2^{p·w} ln 2 · p`. -/
theorem hasDerivAt_two_rpow_mul (p w : ℝ) :
    HasDerivAt (fun v : ℝ => (2 : ℝ) ^ (p * v)) ((2 : ℝ) ^ (p * w) * log 2 * p) w := by
  have h1 : HasDerivAt (fun v : ℝ => p * v) p w := by
    simpa using (hasDerivAt_id w).const_mul p
  exact (hasDerivAt_two_rpow (p * w)).comp w h1

/-- The closed form `k̄(v) = (c/p)(τ − 2^{p v})`. -/
theorem kbar_eq (hp0 : p ≠ 0) (v : ℝ) :
    kbar c p v = c / p * ((2 : ℝ) ^ p - (2 : ℝ) ^ (p * v)) := by
  have hderiv : ∀ w ∈ Set.uIcc v 1,
      HasDerivAt (fun w : ℝ => c / p * (2 : ℝ) ^ (p * w)) (kern c p w) w := by
    intro w _
    have h := (hasDerivAt_two_rpow_mul p w).const_mul (c / p)
    have e : kern c p w = c / p * ((2 : ℝ) ^ (p * w) * log 2 * p) := by
      unfold kern
      field_simp
    rw [e]
    exact h
  rw [kbar, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_kern c p).intervalIntegrable _ _), mul_one]
  ring

theorem continuous_kbar (c p : ℝ) : Continuous (kbar c p) :=
  continuous_iff_continuousAt.2 fun v => (hasDerivAt_kbar (c := c) (p := p) v).continuousAt

/-- `G(x) := ∫₀¹ k̄(v) V(x − v) dv`, the leftmost expression of the remark's display. -/
noncomputable def Gfun (c p : ℝ) (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, kbar c p v * V (x - v)

/-- **`rem:doubling_renewal`, the two expressions of `G` agree**:
`∫₀¹ k̄(v)V(x−v)dv = ∫_{x−1}^x k̄(x−y)V(y)dy`. -/
theorem Gfun_eq_shift (V : ℝ → ℝ) (x : ℝ) :
    Gfun c p V x = ∫ y in (x - 1)..x, kbar c p (x - y) * V y := by
  have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun y => kbar c p (x - y) * V y) x
  simp only [sub_sub_cancel, sub_zero] at this
  exact this

/-- **`rem:doubling_renewal`, the right side of the limit equation, in both forms**:
`∫₀¹ k(v)V(x−v)dv = ∫_{x−1}^x k(x−y)V(y)dy`. -/
theorem rhs_eq_shift (V : ℝ → ℝ) (x : ℝ) :
    (∫ v in (0 : ℝ)..1, kern c p v * V (x - v)) = ∫ y in (x - 1)..x, kern c p (x - y) * V y := by
  have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun y => kern c p (x - y) * V y) x
  simp only [sub_sub_cancel, sub_zero] at this
  exact this

end RenewalMain

section RenewalSolution

variable {c p : ℝ} {V : ℝ → ℝ} {M : ℝ}

/-- **`rem:doubling_renewal`, the Lipschitz sentence, first half**: for bounded measurable `V`, the
right side `x ↦ ∫₀¹ k(v)V(x−v)dv` of the limit equation is Lipschitz, with the explicit constant
`M(2K₀ + K₁)`, `K₀ = c ln 2 (1+τ)` and `K₁ = c (ln 2)² |p| (1+τ)`. -/
theorem renewal_rhs_lipschitz (hc : 0 < c) (hVm : Measurable V) (hM : ∀ x, |V x| ≤ M) :
    LipschitzWith (Real.toNNReal (M * (2 * kernSup c p + kernLip c p)))
      (fun x => ∫ v in (0 : ℝ)..1, kern c p v * V (x - v)) :=
  conv_lipschitz (continuous_kern c p) (fun _ hv => abs_kern_le hc p hv) (kernLip_nonneg hc p)
    (fun _ hu _ hv => abs_kern_sub_le hc p hu hv) hVm hM

/-- **`rem:doubling_renewal`, the Lipschitz sentence, second half**: a bounded measurable solution
`V` of the limit equation `V(x) = ∫₀¹ k(v)V(x−v)dv` is Lipschitz, with the same constant. -/
theorem renewal_lipschitz (hc : 0 < c) (hVm : Measurable V) (hM : ∀ x, |V x| ≤ M)
    (heq : ∀ x, V x = ∫ v in (0 : ℝ)..1, kern c p v * V (x - v)) :
    LipschitzWith (Real.toNNReal (M * (2 * kernSup c p + kernLip c p))) V := by
  have h : V = fun x => ∫ v in (0 : ℝ)..1, kern c p v * V (x - v) := funext heq
  have hL := renewal_rhs_lipschitz (p := p) hc hVm hM
  rw [← h] at hL
  exact hL

/-- **`rem:doubling_renewal`, the Leibniz computation of the display**, for continuous `V`:
`G'(x) = k̄(0)V(x) − k̄(1)V(x−1) − ∫₀¹ k(v)V(x−v)dv`, at every `x`. -/
theorem hasDerivAt_Gfun (hp0 : p ≠ 0) (hVc : Continuous V) (x : ℝ) :
    HasDerivAt (Gfun c p V)
      (kbar c p 0 * V x - kbar c p 1 * V (x - 1) - ∫ v in (0 : ℝ)..1, kern c p v * V (x - v)) x := by
  set e : ℝ → ℝ := fun y => (2 : ℝ) ^ (-(p * y)) with he
  have hec : Continuous e :=
    continuous_two_rpow.comp (continuous_const.mul continuous_id).neg
  have hW : Continuous fun y => e y * V y := hec.mul hVc
  set Φ₁ : ℝ → ℝ := fun u => ∫ y in (0 : ℝ)..u, V y with hΦ₁
  set Φ₂ : ℝ → ℝ := fun u => ∫ y in (0 : ℝ)..u, e y * V y with hΦ₂
  have hmul : ∀ z y : ℝ, (2 : ℝ) ^ (p * (z - y)) = (2 : ℝ) ^ (p * z) * e y := by
    intro z y
    rw [he]
    simp only
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hint : ∀ (f : ℝ → ℝ), Continuous f → ∀ z : ℝ,
      (∫ y in (z - 1)..z, f y) = (∫ y in (0 : ℝ)..z, f y) - ∫ y in (0 : ℝ)..(z - 1), f y := by
    intro f hf z
    exact (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  -- `G` as a combination of primitives
  have hG : Gfun c p V = fun z => c / p * (2 : ℝ) ^ p * (Φ₁ z - Φ₁ (z - 1))
      - c / p * (2 : ℝ) ^ (p * z) * (Φ₂ z - Φ₂ (z - 1)) := by
    funext z
    rw [Gfun_eq_shift]
    have hcongr : (∫ y in (z - 1)..z, kbar c p (z - y) * V y)
        = ∫ y in (z - 1)..z, (c / p * (2 : ℝ) ^ p * V y
            - c / p * (2 : ℝ) ^ (p * z) * (e y * V y)) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [kbar_eq hp0, hmul]
      ring
    rw [hcongr, intervalIntegral.integral_sub ((hVc.intervalIntegrable _ _).const_mul _)
      ((hW.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hint V hVc, hint _ hW]
  -- the right side as a primitive
  have hR : (∫ v in (0 : ℝ)..1, kern c p v * V (x - v))
      = c * log 2 * (2 : ℝ) ^ (p * x) * (Φ₂ x - Φ₂ (x - 1)) := by
    rw [rhs_eq_shift]
    have hcongr : (∫ y in (x - 1)..x, kern c p (x - y) * V y)
        = ∫ y in (x - 1)..x, c * log 2 * (2 : ℝ) ^ (p * x) * (e y * V y) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [kern, hmul]
      ring
    rw [hcongr, intervalIntegral.integral_const_mul, hint _ hW]
  -- derivatives of the pieces
  have dΦ₁ : ∀ z, HasDerivAt Φ₁ (V z) z := fun z => (hVc.integral_hasStrictDerivAt 0 z).hasDerivAt
  have dΦ₂ : ∀ z, HasDerivAt Φ₂ (e z * V z) z :=
    fun z => (hW.integral_hasStrictDerivAt 0 z).hasDerivAt
  have d1 : HasDerivAt (fun z => Φ₁ z - Φ₁ (z - 1)) (V x - V (x - 1)) x :=
    (dΦ₁ x).sub (HasDerivAt.comp_sub_const x 1 (dΦ₁ (x - 1)))
  have d2 : HasDerivAt (fun z => Φ₂ z - Φ₂ (z - 1)) (e x * V x - e (x - 1) * V (x - 1)) x :=
    (dΦ₂ x).sub (HasDerivAt.comp_sub_const x 1 (dΦ₂ (x - 1)))
  have d3 : HasDerivAt (fun z => c / p * (2 : ℝ) ^ (p * z))
      (c / p * ((2 : ℝ) ^ (p * x) * log 2 * p)) x :=
    (hasDerivAt_two_rpow_mul p x).const_mul (c / p)
  have hD : HasDerivAt (fun z => c / p * (2 : ℝ) ^ p * (Φ₁ z - Φ₁ (z - 1))
      - c / p * (2 : ℝ) ^ (p * z) * (Φ₂ z - Φ₂ (z - 1)))
      (c / p * (2 : ℝ) ^ p * (V x - V (x - 1)) -
        (c / p * ((2 : ℝ) ^ (p * x) * log 2 * p) * (Φ₂ x - Φ₂ (x - 1)) +
          c / p * (2 : ℝ) ^ (p * x) * (e x * V x - e (x - 1) * V (x - 1)))) x :=
    (d1.const_mul (c / p * (2 : ℝ) ^ p)).sub (d3.mul d2)
  rw [hG]
  refine hD.congr_deriv ?_
  -- the algebra
  have hex : (2 : ℝ) ^ (p * x) * e x = 1 := by
    have := hmul x x
    rw [sub_self, mul_zero, Real.rpow_zero] at this
    exact this.symm
  have hex1 : (2 : ℝ) ^ (p * x) * e (x - 1) = (2 : ℝ) ^ p := by
    have := hmul x (x - 1)
    rw [sub_sub_cancel, mul_one] at this
    exact this.symm
  rw [kbar_eq hp0, kbar_one, hR, mul_zero, Real.rpow_zero]
  have hcp : c / p * p = c := div_mul_cancel₀ c hp0
  linear_combination (-(log 2 * (2 : ℝ) ^ (p * x) * (Φ₂ x - Φ₂ (x - 1)))) * hcp
    + (-(c / p * V x)) * hex + (c / p * V (x - 1)) * hex1

/-- **`rem:doubling_renewal`, `G' = 0`**: for a bounded measurable solution `V` of the limit
equation, `G'(x) = k̄(0)V(x) − k̄(1)V(x−1) − ∫₀¹ k(v)V(x−v)dv = 0` at every `x`. -/
theorem renewal_hasDerivAt_G (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) (hVm : Measurable V)
    (hM : ∀ x, |V x| ≤ M) (heq : ∀ x, V x = ∫ v in (0 : ℝ)..1, kern c p v * V (x - v))
    (x : ℝ) :
    HasDerivAt (Gfun c p V)
      (kbar c p 0 * V x - kbar c p 1 * V (x - 1) - ∫ v in (0 : ℝ)..1, kern c p v * V (x - v)) x
    ∧ kbar c p 0 * V x - kbar c p 1 * V (x - 1) - ∫ v in (0 : ℝ)..1, kern c p v * V (x - v)
      = 0 := by
  have hVc : Continuous V := (renewal_lipschitz hc hVm hM heq).continuous
  refine ⟨hasDerivAt_Gfun hp0 hVc x, ?_⟩
  rw [kbar_zero hp0 hp, kbar_one, ← heq x]
  ring

/-- **`rem:doubling_renewal`, "so `G` is constant"**. -/
theorem renewal_G_const (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) (hVm : Measurable V)
    (hM : ∀ x, |V x| ≤ M) (heq : ∀ x, V x = ∫ v in (0 : ℝ)..1, kern c p v * V (x - v))
    (x y : ℝ) : Gfun c p V x = Gfun c p V y := by
  have hd : ∀ z, HasDerivAt (Gfun c p V) 0 z := fun z => by
    obtain ⟨h1, h2⟩ := renewal_hasDerivAt_G hc hp0 hp hVm hM heq z
    rwa [h2] at h1
  exact is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt) (fun z => (hd z).deriv) x y

/-- The mean of the kernel, `∫₀¹ v k(v) dv`. -/
noncomputable def kernMean (c p : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, v * kern c p v

/-- **`rem:doubling_renewal`, `∫₀¹ k̄ = ∫₀¹ v k(v) dv`**, both in closed form: `(c/p)(τ − (τ−1)/(p ln 2))`. -/
theorem integral_kbar_eq_kernMean (hp0 : p ≠ 0) :
    (∫ v in (0 : ℝ)..1, kbar c p v) = kernMean c p
      ∧ kernMean c p = c / p * ((2 : ℝ) ^ p - ((2 : ℝ) ^ p - 1) / (p * log 2)) := by
  have hL : log 2 ≠ 0 := log_two_pos.ne'
  have hpL : p * log 2 ≠ 0 := mul_ne_zero hp0 hL
  -- `∫₀¹ v k(v) dv`
  have hmean : kernMean c p = c / p * ((2 : ℝ) ^ p - ((2 : ℝ) ^ p - 1) / (p * log 2)) := by
    have hderiv : ∀ w ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
        (fun v : ℝ => c / p * (v * (2 : ℝ) ^ (p * v) - (2 : ℝ) ^ (p * v) / (p * log 2)))
        (w * kern c p w) w := by
      intro w _
      have h1 := ((hasDerivAt_id w).mul (hasDerivAt_two_rpow_mul p w)).sub
        ((hasDerivAt_two_rpow_mul p w).div_const (p * log 2))
      have h2 := h1.const_mul (c / p)
      refine h2.congr_deriv ?_
      unfold kern
      simp only [id]
      field_simp
      ring
    have hcont : Continuous fun v : ℝ => v * kern c p v := continuous_id.mul (continuous_kern c p)
    rw [kernMean, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable _ _)]
    simp only [mul_one, mul_zero, Real.rpow_zero, zero_sub]
    field_simp
    ring
  refine ⟨?_, hmean⟩
  have hderiv : ∀ w ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun v : ℝ => c / p * ((2 : ℝ) ^ p * v - (2 : ℝ) ^ (p * v) / (p * log 2)))
      (kbar c p w) w := by
    intro w _
    have h1 := ((hasDerivAt_id w).const_mul ((2 : ℝ) ^ p)).sub
      ((hasDerivAt_two_rpow_mul p w).div_const (p * log 2))
    have h2 := h1.const_mul (c / p)
    refine h2.congr_deriv ?_
    rw [kbar_eq hp0]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_kbar c p).intervalIntegrable _ _), hmean]
  simp only [mul_one, mul_zero, Real.rpow_zero]
  field_simp
  ring

/-- **`rem:doubling_renewal`, the mean of the kernel is `ψ'(p_*)/(p_* ln 2) = τ/(τ−1) − 1/(p_* ln 2)`**,
by the Cramér relation `eq:doubling_cramer_form`. -/
theorem kernMean_eq (hp0 : p ≠ 0) (hp : psi c p = 0) :
    kernMean c p = deriv (psi c) p / (p * log 2)
      ∧ kernMean c p = (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1) - 1 / (p * log 2) := by
  have hL : log 2 ≠ 0 := log_two_pos.ne'
  have hcf := cramer_form hp0 hp
  have hτ : (2 : ℝ) ^ p - 1 ≠ 0 := by
    intro h0
    rw [h0, zero_div, mul_zero] at hcf
    exact zero_ne_one hcf
  have hc' : c = p / ((2 : ℝ) ^ p - 1) := by
    field_simp at hcf ⊢
    linarith
  rw [(integral_kbar_eq_kernMean hp0).2, deriv_psi]
  constructor
  · rw [hc']
    field_simp
  · rw [hc']
    field_simp

/-- The mean of the kernel is positive, for `c > 0`. -/
theorem kernMean_pos (hc : 0 < c) : 0 < kernMean c p := by
  have hcont : Continuous fun v : ℝ => v * kern c p v := continuous_id.mul (continuous_kern c p)
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
    (fun v hv => mul_pos hv.1 (kern_pos hc p v)) zero_lt_one

/-- **`rem:doubling_renewal`, the limit**: if a bounded measurable solution `V` of the limit
equation has a limit `ℓ` at `+∞`, then, dominated convergence in the leftmost expression of `G`,
`ℓ = G / ∫₀¹ k̄` — with `∫₀¹ k̄ = ∫₀¹ v k(v) dv = ψ'(p_*)/(p_* ln 2) = τ/(τ−1) − 1/(p_* ln 2)`
(`integral_kbar_eq_kernMean`, `kernMean_eq`). `G` being constant (`renewal_G_const`), the
quotient is evaluated at any point `x₀`. -/
theorem renewal_limit (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) (hVm : Measurable V)
    (hM : ∀ x, |V x| ≤ M) (heq : ∀ x, V x = ∫ v in (0 : ℝ)..1, kern c p v * V (x - v))
    {ℓ : ℝ} (hlim : Tendsto V atTop (𝓝 ℓ)) (x₀ : ℝ) :
    ℓ = Gfun c p V x₀ / ∫ v in (0 : ℝ)..1, kbar c p v := by
  have hkb := (integral_kbar_eq_kernMean (c := c) hp0).1
  have hpos : 0 < ∫ v in (0 : ℝ)..1, kbar c p v := hkb ▸ kernMean_pos hc
  have hkbc := continuous_kbar c p
  obtain ⟨Kb, hKb⟩ : ∃ Kb, ∀ v ∈ Set.uIcc (0 : ℝ) 1, ‖kbar c p v‖ ≤ Kb :=
    (isCompact_uIcc.exists_bound_of_continuousOn hkbc.continuousOn)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have htend : Tendsto (Gfun c p V) atTop (𝓝 (∫ v in (0 : ℝ)..1, kbar c p v * ℓ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Kb * M)
      (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      intervalIntegrable_const ?_
    · exact (intervalIntegrable_mul_shift hkbc hVm hM x 0 1).def'.aestronglyMeasurable
    · refine Eventually.of_forall fun v hv => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have hv' : v ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hv
      have := hKb v hv'
      rw [Real.norm_eq_abs] at this
      exact mul_le_mul this (hM _) (abs_nonneg _) ((abs_nonneg _).trans this)
    · refine Eventually.of_forall fun v _ => ?_
      exact (hlim.comp (tendsto_atTop_add_const_right _ (-v) tendsto_id)).const_mul _ |>.congr
        fun x => by simp only [Function.comp, id, sub_eq_add_neg]
  have hconst : Tendsto (Gfun c p V) atTop (𝓝 (Gfun c p V x₀)) := by
    have : Gfun c p V = fun _ => Gfun c p V x₀ :=
      funext fun x => renewal_G_const hc hp0 hp hVm hM heq x x₀
    rw [this]
    exact tendsto_const_nhds
  have heqlim := tendsto_nhds_unique htend hconst
  rw [intervalIntegral.integral_mul_const] at heqlim
  rw [← heqlim]
  field_simp

/-- The law with density `k` on `[0,1]`. -/
noncomputable def kernMeasure (c p : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) 1)).withDensity fun v => ENNReal.ofReal (kern c p v)

/-- **`rem:doubling_renewal`, `∫₀¹ k = 1` as a probability law**: the kernel is a probability
density. -/
theorem kernMeasure_univ (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) :
    kernMeasure c p univ = 1 := by
  rw [kernMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((continuous_kern c p).integrableOn_Icc)
      (Eventually.of_forall fun v => (kern_pos hc p v).le),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_kern hp0 hp, ENNReal.ofReal_one]

/-- **`rem:doubling_renewal`, "that kernel has a density"**: its law is absolutely continuous. -/
theorem kernMeasure_absolutelyContinuous (c p : ℝ) : kernMeasure c p ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous

/-- **`rem:doubling_renewal`, "hence is non-lattice"**: no lattice `a + hℤ` carries the law,
since it charges no countable set. -/
theorem kernMeasure_nonlattice (hc : 0 < c) (hp0 : p ≠ 0) (hp : psi c p = 0) (a h : ℝ) :
    ¬ ∀ᵐ x ∂kernMeasure c p, ∃ n : ℤ, x = a + n * h := by
  intro hae
  have hnull : kernMeasure c p {x | ∃ n : ℤ, x = a + n * h} = 0 := by
    have hset : {x : ℝ | ∃ n : ℤ, x = a + n * h} = Set.range fun n : ℤ => a + n * h := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]
    rw [hset]
    exact kernMeasure_absolutelyContinuous c p ((Set.countable_range _).measure_zero _)
  have hcompl := ae_iff.mp hae
  have h1 : kernMeasure c p univ ≤ 0 := by
    calc kernMeasure c p univ
        ≤ kernMeasure c p ({x | ∃ n : ℤ, x = a + n * h} ∪ {x | ¬ ∃ n : ℤ, x = a + n * h}) := by
          refine measure_mono fun x _ => ?_
          by_cases hx : ∃ n : ℤ, x = a + n * h
          · exact Or.inl hx
          · exact Or.inr hx
      _ ≤ _ := measure_union_le _ _
      _ = 0 := by rw [hnull, hcompl, add_zero]
  rw [kernMeasure_univ hc hp0 hp] at h1
  exact absurd h1 (by norm_num)

/-! ### Inhabitation -/

/-- **The limit equation is inhabited**: every constant is a bounded measurable solution. -/
theorem const_isRenewalSolution (hp0 : p ≠ 0) (hp : psi c p = 0) (ℓ x : ℝ) :
    (fun _ : ℝ => ℓ) x = ∫ v in (0 : ℝ)..1, kern c p v * (fun _ : ℝ => ℓ) (x - v) := by
  simp only
  rw [intervalIntegral.integral_mul_const, integral_kern hp0 hp, one_mul]

/-- **Non-vacuity check of `renewal_limit`**: at `c = 1/2` the Cramér root exists, and on the
constant solution `V ≡ ℓ` the limit formula returns `ℓ`, `G ≡ ℓ ∫₀¹ k̄`. -/
theorem renewal_limit_check (ℓ : ℝ) :
    ∃ p : ℝ, p ≠ 0 ∧ psi (1 / 2) p = 0 ∧
      ℓ = Gfun (1 / 2) p (fun _ => ℓ) 0 / ∫ v in (0 : ℝ)..1, kbar (1 / 2) p v := by
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hne : (1 / 2 : ℝ) * log 2 ≠ 1 := by
    have := Real.log_two_lt_d9
    intro h
    linarith
  obtain ⟨p, hp0, hp, -⟩ := cramer_root_exists hc hne
  refine ⟨p, hp0, hp, ?_⟩
  exact renewal_limit hc hp0 hp measurable_const (M := |ℓ|) (fun _ => le_rfl)
    (const_isRenewalSolution hp0 hp ℓ) tendsto_const_nhds 0

end RenewalSolution

section FiniteChain

open GFNBounds.Balance
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V]

theorem funAct_add' (K : V → V → ℝ) (a b : V → ℝ) :
    Core.funAct K (fun y => a y + b y) = fun x => Core.funAct K a x + Core.funAct K b x := by
  funext x
  simp only [Core.funAct_apply, mul_add, Finset.sum_add_distrib]

theorem funAct_smul' (K : V → V → ℝ) (c : ℝ) (a : V → ℝ) :
    Core.funAct K (fun y => c * a y) = fun x => c * Core.funAct K a x := by
  funext x
  simp only [Core.funAct_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The function action `(P⋆f)(x) = ∑_y T(x→y)f(y)`, conjugated by the weighting, as a linear
map on `L²(λ) ≅ EuclideanSpace ℝ V`. -/
noncomputable def funLin (lam : V → ℝ) (K : V → V → ℝ) :
    EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V where
  toFun v := wtL2 lam (Core.funAct K (unwtL2 lam v))
  map_add' u v := by
    show wtL2 lam (Core.funAct K (unwtL2 lam (u + v))) = _
    rw [unwtL2_add, funAct_add', wtL2_add]
  map_smul' c v := by
    show wtL2 lam (Core.funAct K (unwtL2 lam (c • v))) = _
    rw [unwtL2_smul, funAct_smul', wtL2_smul]
    rfl

/-- `P⋆`, the function action, bundled on `L²(λ)`. -/
noncomputable def funOp (lam : V → ℝ) (K : V → V → ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  LinearMap.toContinuousLinearMap (funLin lam K)

theorem funOp_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (K : V → V → ℝ) (a : V → ℝ) :
    funOp lam K (wtL2 lam a) = wtL2 lam (Core.funAct K a) := by
  show wtL2 lam (Core.funAct K (unwtL2 lam (wtL2 lam a))) = _
  rw [unwtL2_wtL2 hlam]

theorem funOp_pow_wtL2 {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (K : V → V → ℝ) (a : V → ℝ)
    (n : ℕ) : (funOp lam K ^ n) (wtL2 lam a) = wtL2 lam ((Core.funAct K)^[n] a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      show funOp lam K ((funOp lam K ^ n) (wtL2 lam a)) = _
      rw [ih, funOp_wtL2 hlam, Function.iterate_succ_apply']

/-- **`rem:doubling_two_constants`, the adjoint behind the ordering**: on a finite chain `P⋆` is
the `L²(λ)`-adjoint of the density action `P`, `⟪P⋆u, v⟫ = ⟪u, Pv⟫` — the finite face of
`lem:doubling_operator`(1). -/
theorem inner_funOp {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (K : V → V → ℝ)
    (u v : EuclideanSpace ℝ V) : ⟪funOp lam K u, v⟫ = ⟪u, densOp lam K v⟫ := by
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hlam x).le
  obtain ⟨a, rfl⟩ := exists_wtL2 hlam u
  obtain ⟨b, rfl⟩ := exists_wtL2 hlam v
  rw [funOp_wtL2 hlam, densOp_wtL2 hlam, inner_wtL2 hnn, inner_wtL2 hnn]
  simp only [Graph.ipL2, Core.funAct_apply, Core.densAct_apply]
  calc ∑ x, lam x * ((∑ y, K x y * a y) * b x)
      = ∑ x, ∑ y, lam x * K x y * b x * a y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ y, ∑ x, lam x * K x y * b x * a y := Finset.sum_comm
    _ = ∑ y, lam y * (a y * ((∑ x, lam x * K x y * b x) / lam y)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul]
        field_simp [(hlam y).ne']

theorem funOp_eq_star {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (K : V → V → ℝ) :
    funOp lam K = star (densOp lam K) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  exact inner_funOp hlam K

theorem meanOp_eq_star {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) :
    meanOp lam = star (meanOp lam) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  exact meanOp_selfAdjoint hlam fun x => (hlam x).le

/-- **`rem:doubling_two_constants`, `‖P⋆ⁿ − Π‖ = β̂ₙ`** on a finite chain — the finite face of
`lem:doubling_operator`(1). -/
theorem norm_funOp_pow_sub {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (K : V → V → ℝ) (n : ℕ) :
    ‖funOp lam K ^ n - meanOp lam‖ = Core.Mixing.beta (densOp lam K) (meanOp lam) n := by
  have h1 : funOp lam K ^ n - meanOp lam = star (densOp lam K ^ n - meanOp lam) := by
    have e := star_sub (densOp lam K ^ n) (meanOp lam)
    rw [star_pow, ← funOp_eq_star hlam, ← meanOp_eq_star hlam] at e
    exact e.symm
  rw [Core.Mixing.beta, h1]
  exact norm_star (densOp lam K ^ n - meanOp lam)

/-- `Π P⋆ = Π`, the adjoint of `P Π = Π` (invariance of `λ`). -/
theorem meanOp_mul_funOp {K : V → V → ℝ} {lam : V → ℝ} (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) : meanOp lam * funOp lam K = meanOp lam := by
  have h1 : meanOp lam * funOp lam K = star (densOp lam K * meanOp lam) := by
    rw [star_mul, ← funOp_eq_star hlam, ← meanOp_eq_star hlam]
  rw [h1, densOp_mul_meanOp hinv hlam, ← meanOp_eq_star hlam]

/-- `P⋆ Π = Π`, the adjoint of `Π P = Π` (`T` is Markov). -/
theorem funOp_mul_meanOp {K : V → V → ℝ} {lam : V → ℝ} (hK : Core.IsMarkov K)
    (hlam : ∀ x, 0 < lam x) : funOp lam K * meanOp lam = meanOp lam := by
  have h1 : funOp lam K * meanOp lam = star (meanOp lam * densOp lam K) := by
    rw [star_mul, ← funOp_eq_star hlam, ← meanOp_eq_star hlam]
  rw [h1, meanOp_mul_densOp hK hlam, ← meanOp_eq_star hlam]

theorem meanOp_mul_self {lam : V → ℝ} (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) :
    meanOp lam * meanOp lam = meanOp lam :=
  ContinuousLinearMap.ext fun u => meanOp_idem hlam htot u

end FiniteChain

section FiniteOrdering

open GFNBounds.Balance

variable {V : Type*} [Fintype V] {K : V → V → ℝ} {lam : V → ℝ}

/-- When the partial sums of `Σ(P⋆ⁿ − Π)` converge in operator norm to `U`, `Id − P⋆ + Π` is a
unit and the paper's `S = (Id − P⋆ + Π)^{-1} − Π` is `U`. -/
theorem inverse_sub_eq_of_tendsto (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1)
    {U : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V}
    (hconv : Tendsto (partialSum (funOp lam K) (meanOp lam)) atTop (𝓝 U)) :
    IsUnit (1 - funOp lam K + meanOp lam)
      ∧ Ring.inverse (1 - funOp lam K + meanOp lam) - meanOp lam = U := by
  obtain ⟨h1, h2⟩ := resolvent_inverse (meanOp_mul_self hlam htot) (meanOp_mul_funOp hinv hlam)
    (funOp_mul_meanOp hK hlam) hconv
  have hunit : IsUnit (1 - funOp lam K + meanOp lam) := ⟨⟨_, _, h1, h2⟩, rfl⟩
  refine ⟨hunit, ?_⟩
  have hR : Ring.inverse (1 - funOp lam K + meanOp lam) = meanOp lam + U := by
    calc Ring.inverse (1 - funOp lam K + meanOp lam)
        = Ring.inverse (1 - funOp lam K + meanOp lam)
          * ((1 - funOp lam K + meanOp lam) * (meanOp lam + U)) := by rw [h1, mul_one]
      _ = (Ring.inverse (1 - funOp lam K + meanOp lam) * (1 - funOp lam K + meanOp lam))
          * (meanOp lam + U) := by rw [mul_assoc]
      _ = meanOp lam + U := by rw [Ring.inverse_mul_cancel _ hunit, one_mul]
  rw [hR, add_sub_cancel_left]

/-- **`rem:doubling_two_constants`, "item (3) of `lem:doubling_operator` orders the two on any
finite irreducible chain"**, on every finite chain with `λ > 0` its invariant probability:
the norm `B̂ = ‖(Id − P⋆ + Π)^{-1} − Π‖` of the diffusion operator is at most every real `B`
bounding the partial sums of the mixing sum `Σ β̂ₙ`, `β̂ₙ = ‖Pⁿ − Π‖` on the density action. The
statement is vacuous exactly when `Σ β̂ₙ = +∞`. -/
theorem bhat_le_mixing_sum (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1) {B : ℝ}
    (hB : ∀ N : ℕ, ∑ n ∈ Finset.range N, Core.Mixing.beta (densOp lam K) (meanOp lam) n ≤ B) :
    ‖Ring.inverse (1 - funOp lam K + meanOp lam) - meanOp lam‖ ≤ B := by
  have hB' : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖funOp lam K ^ n - meanOp lam‖ ≤ B := fun N =>
    (Finset.sum_congr rfl fun n _ => norm_funOp_pow_sub hlam K n).trans_le (hB N)
  have hsn : Summable fun n : ℕ => ‖funOp lam K ^ n - meanOp lam‖ :=
    summable_of_sum_range_le (fun _ => norm_nonneg _) hB'
  haveI : CompleteSpace (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :=
    FiniteDimensional.complete ℝ _
  have hconv : Tendsto (partialSum (funOp lam K) (meanOp lam)) atTop
      (𝓝 (∑' n : ℕ, (funOp lam K ^ n - meanOp lam))) :=
    (Summable.of_norm hsn).hasSum.tendsto_sum_nat
  have hunit := (inverse_sub_eq_of_tendsto hK hinv hlam htot hconv).1
  exact (resolvent_eq_tsum_of_bdd (meanOp_mul_self hlam htot) (meanOp_mul_funOp hinv hlam)
    (funOp_mul_meanOp hK hlam) (Ring.inverse_mul_cancel _ hunit) hB').2

/-- **`rem:doubling_two_constants`, the trajectory reading, as a pointwise series**: on a finite
chain, wherever `Σ(P⋆ⁿ − Π)` converges in operator norm,
`(Sθ)(x) = Σ_{n≥0}((P⋆ⁿθ)(x) − λ(θ))`, with `(P⋆ⁿθ)(x) = ∑_y Tⁿ(x→y)θ(y)` the `n`-fold function
action, which the paper reads as `E(θ(Xₙ) | X₀ = x)` (not identified here). The series is the
limit of its partial sums. -/
theorem diffusion_apply_eq_series (hK : Core.IsMarkov K) (hinv : Core.IsInvariant lam K)
    (hlam : ∀ x, 0 < lam x) (htot : ∑ x, lam x = 1)
    {U : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V}
    (hconv : Tendsto (partialSum (funOp lam K) (meanOp lam)) atTop (𝓝 U))
    (θ : V → ℝ) (x : V) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((Core.funAct K)^[n] θ x - Graph.meanL2 lam θ)) atTop
      (𝓝 (unwtL2 lam ((Ring.inverse (1 - funOp lam K + meanOp lam) - meanOp lam)
        (wtL2 lam θ)) x)) := by
  rw [(inverse_sub_eq_of_tendsto hK hinv hlam htot hconv).2]
  have hev : Continuous fun T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V =>
      unwtL2 lam (T (wtL2 lam θ)) x := by
    have h1 : Continuous fun T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V => T (wtL2 lam θ) :=
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ V) (wtL2 lam θ)).continuous
    exact ((EuclideanSpace.proj x).continuous.comp h1).div_const _
  refine ((hev.tendsto U).comp hconv).congr fun N => ?_
  simp only [Function.comp]
  have hps : partialSum (funOp lam K) (meanOp lam) N (wtL2 lam θ)
      = wtL2 lam (fun y => ∑ n ∈ Finset.range N,
          ((Core.funAct K)^[n] θ y - Graph.meanL2 lam θ)) := by
    rw [partialSum, sum_apply]
    induction N with
    | zero =>
        ext y
        simp only [Finset.sum_range_zero, wtL2_apply, mul_zero, PiLp.zero_apply]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, sub_apply, funOp_pow_wtL2 hlam,
          meanOp_wtL2 hlam, ← wtL2_sub, ← wtL2_add]
        congr 1
        funext y
        rw [Finset.sum_range_succ]
  rw [hps, unwtL2_wtL2 hlam]

end FiniteOrdering

section FlipChain

open GFNBounds.Balance

/-- The two-state chain that flips with probability `q`. -/
noncomputable def flipK (q : ℝ) : Fin 2 → Fin 2 → ℝ := fun x y => if x = y then 1 - q else q

variable {q : ℝ}

theorem flipK_isMarkov (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Core.IsMarkov (flipK q) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · unfold flipK
    split_ifs <;> linarith
  · fin_cases x <;> simp [flipK, Fin.sum_univ_two]

theorem flipK_isInvariant (q : ℝ) : Core.IsInvariant twoStateLam (flipK q) := by
  refine ⟨fun x => (twoStateLam_pos x).le, fun y => ?_⟩
  fin_cases y <;> simp [flipK, twoStateLam, Fin.sum_univ_two] <;> ring

/-- **`rem:doubling_two_constants`, "whose invariant probability is uniform"**: for `q ≠ 0` the uniform law is the only invariant
probability of the flip chain. -/
theorem flipK_invariant_unique (hq : q ≠ 0) {mu : Fin 2 → ℝ}
    (hinv : ∀ y, ∑ x, mu x * flipK q x y = mu y) (htot : ∑ x, mu x = 1) : mu = twoStateLam := by
  have h0 := hinv 0
  simp only [Fin.sum_univ_two, flipK] at h0 htot
  norm_num at h0
  have h01 : mu 0 = mu 1 := by
    have : q * (mu 1 - mu 0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hq
    · linarith
  funext x
  fin_cases x <;> simp only [twoStateLam] <;> simp <;> linarith

/-- The flip chain's operators, in terms of `Π`: `P = P⋆ = Π + (1 − 2q)(Id − Π)`. -/
theorem densOp_flipK (q : ℝ) :
    densOp twoStateLam (flipK q)
      = meanOp twoStateLam + (1 - 2 * q) • (1 - meanOp twoStateLam) := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨a, rfl⟩ := exists_wtL2 twoStateLam_pos u
  rw [densOp_wtL2 twoStateLam_pos, add_apply,
    smul_apply, sub_apply, one_apply_eq_self,
    meanOp_wtL2 twoStateLam_pos, ← wtL2_sub, ← wtL2_smul, ← wtL2_add]
  congr 1
  funext y
  fin_cases y <;>
    simp [Core.densAct_apply, flipK, twoStateLam, Graph.meanL2, Fin.sum_univ_two] <;> ring

theorem funOp_flipK (q : ℝ) :
    funOp twoStateLam (flipK q)
      = meanOp twoStateLam + (1 - 2 * q) • (1 - meanOp twoStateLam) := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨a, rfl⟩ := exists_wtL2 twoStateLam_pos u
  rw [funOp_wtL2 twoStateLam_pos, add_apply,
    smul_apply, sub_apply, one_apply_eq_self,
    meanOp_wtL2 twoStateLam_pos, ← wtL2_sub, ← wtL2_smul, ← wtL2_add]
  congr 1
  funext y
  fin_cases y <;>
    simp [Core.funAct_apply, flipK, twoStateLam, Graph.meanL2, Fin.sum_univ_two] <;> ring

/-- **`rem:doubling_two_constants`, "centred functions are eigenfunctions of its transition
operator"**, at the eigenvalue `1 − 2q` (`−1/2` at `q = 3/4`). -/
theorem flipK_funAct_centred (q : ℝ) {f : Fin 2 → ℝ} (hf : Graph.meanL2 twoStateLam f = 0) :
    Core.funAct (flipK q) f = fun x => (1 - 2 * q) * f x := by
  simp only [Graph.meanL2, Fin.sum_univ_two, twoStateLam] at hf
  have h1 : f 1 = -f 0 := by linarith
  funext x
  fin_cases x <;> simp [Core.funAct_apply, flipK, Fin.sum_univ_two, h1] <;> ring

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Q : E →L[ℝ] E}

/-- Operators of the form `Q + a(Id − Q)`, `Q` idempotent, multiply by multiplying `a`. -/
theorem mul_proj_add_smul (hQ : Q * Q = Q) (a b : ℝ) :
    (Q + a • (1 - Q)) * (Q + b • (1 - Q)) = Q + (a * b) • (1 - Q) := by
  have h1 : Q * (1 - Q) = 0 := by rw [mul_sub, mul_one, hQ, sub_self]
  have h2 : (1 - Q) * Q = 0 := by rw [sub_mul, one_mul, hQ, sub_self]
  have h3 : (1 - Q) * (1 - Q) = 1 - Q := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hQ, h1, h2, h3,
    smul_zero, add_zero, zero_add, smul_smul]
  rw [mul_comm b a]

theorem pow_proj_add_smul (hQ : Q * Q = Q) (r : ℝ) (n : ℕ) :
    (Q + r • (1 - Q)) ^ n = Q + r ^ n • (1 - Q) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_smul]; abel
  | succ n ih => rw [pow_succ, ih, mul_proj_add_smul hQ, pow_succ]

end Algebra

variable {q : ℝ}

/-- `β̂ₙ = |1 − 2q|ⁿ` on the flip chain, with `β̂ₙ = ‖Pⁿ − Π‖` on the density action. -/
theorem beta_flipK (q : ℝ) (n : ℕ) :
    Core.Mixing.beta (densOp twoStateLam (flipK q)) (meanOp twoStateLam) n = |1 - 2 * q| ^ n := by
  rw [Core.Mixing.beta, densOp_flipK, pow_proj_add_smul (meanOp_mul_self twoStateLam_pos
    twoStateLam_sum), add_sub_cancel_left, norm_smul, norm_pow, Real.norm_eq_abs,
    norm_one_sub_meanOp twoStateLam_pos twoStateLam_sum, mul_one]

/-- **Summable mixing exhibited** on the flip chain, `0 < q < 1`. -/
theorem mixing_flipK (hq0 : 0 < q) (hq1 : q < 1) :
    Core.Mixing (densOp twoStateLam (flipK q)) (meanOp twoStateLam) where
  proj_left := meanOp_mul_densOp (flipK_isMarkov hq0.le hq1.le) twoStateLam_pos
  proj_right := densOp_mul_meanOp (flipK_isInvariant q) twoStateLam_pos
  summable := by
    have h : (fun n : ℕ => ‖densOp twoStateLam (flipK q) ^ n - meanOp twoStateLam‖)
        = fun n => |1 - 2 * q| ^ n := funext (beta_flipK q)
    rw [h]
    exact summable_geometric_of_lt_one (abs_nonneg _) (by rw [abs_lt]; constructor <;> linarith)

/-- The mixing sum `Σ β̂ₙ = (1 − |1 − 2q|)⁻¹` on the flip chain, `0 < q < 1`. -/
theorem B_flipK (hq0 : 0 < q) (hq1 : q < 1) :
    Core.Mixing.B (densOp twoStateLam (flipK q)) (meanOp twoStateLam) = (1 - |1 - 2 * q|)⁻¹ := by
  rw [Core.Mixing.B]
  simp_rw [beta_flipK]
  exact tsum_geometric_of_lt_one (abs_nonneg _) (by rw [abs_lt]; constructor <;> linarith)

/-- **`rem:doubling_two_constants`, the diffusion operator of the flip chain**: `S = (Id − P⋆ + Π)^{-1} − Π = (2q)^{-1}(Id − Π)`,
for `q ≠ 0`. -/
theorem diffusion_flipK (hq : q ≠ 0) :
    Ring.inverse (1 - funOp twoStateLam (flipK q) + meanOp twoStateLam) - meanOp twoStateLam
      = (2 * q)⁻¹ • (1 - meanOp twoStateLam) := by
  set Q := meanOp twoStateLam with hQdef
  have hQ : Q * Q = Q := meanOp_mul_self twoStateLam_pos twoStateLam_sum
  have hM : 1 - funOp twoStateLam (flipK q) + Q = Q + (2 * q) • (1 - Q) := by
    rw [funOp_flipK]
    module
  have h2q : (2 * q) * (2 * q)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero two_ne_zero hq)
  have h2q' : (2 * q)⁻¹ * (2 * q) = 1 := inv_mul_cancel₀ (mul_ne_zero two_ne_zero hq)
  have hMR : (Q + (2 * q) • (1 - Q)) * (Q + (2 * q)⁻¹ • (1 - Q)) = 1 := by
    rw [mul_proj_add_smul hQ, h2q, one_smul, add_sub_cancel]
  have hRM : (Q + (2 * q)⁻¹ • (1 - Q)) * (Q + (2 * q) • (1 - Q)) = 1 := by
    rw [mul_proj_add_smul hQ, h2q', one_smul, add_sub_cancel]
  have hinv : Ring.inverse (Q + (2 * q) • (1 - Q)) = Q + (2 * q)⁻¹ • (1 - Q) := by
    let u : (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))ˣ := ⟨_, _, hMR, hRM⟩
    exact Ring.inverse_unit u
  rw [hM, hinv, add_sub_cancel_left]

end FlipChain

section Witness

open GFNBounds.Balance

/-- `‖S‖ = (2q)^{-1}` on the flip chain, `q > 0`. -/
theorem norm_diffusion_flipK {q : ℝ} (hq : 0 < q) :
    ‖Ring.inverse (1 - funOp twoStateLam (flipK q) + meanOp twoStateLam) - meanOp twoStateLam‖
      = (2 * q)⁻¹ := by
  rw [diffusion_flipK hq.ne', norm_smul, norm_one_sub_meanOp twoStateLam_pos twoStateLam_sum,
    mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **`rem:doubling_two_constants`, the witness**: on the two-state chain that flips with
probability `3/4`, whose invariant probability is uniform and whose centred functions are
eigenfunctions of its transition operator at `−1/2`, the diffusion constant is `B̂ = 2/3` while
`β̂ₙ = 2^{-n}` for every `n ≥ 0` and `Σₙ β̂ₙ = 2`: the two constants written `B̂` do not
coincide. -/
theorem two_constants_flip_three_quarters :
    (∀ mu : Fin 2 → ℝ, (∀ y, ∑ x, mu x * flipK (3 / 4) x y = mu y) → ∑ x, mu x = 1 →
        mu = twoStateLam)
    ∧ Core.IsInvariant twoStateLam (flipK (3 / 4))
    ∧ (∀ f : Fin 2 → ℝ, Graph.meanL2 twoStateLam f = 0 →
        Core.funAct (flipK (3 / 4)) f = fun x => -(1 / 2) * f x)
    ∧ ‖Ring.inverse (1 - funOp twoStateLam (flipK (3 / 4)) + meanOp twoStateLam)
        - meanOp twoStateLam‖ = 2 / 3
    ∧ (∀ n : ℕ, Core.Mixing.beta (densOp twoStateLam (flipK (3 / 4))) (meanOp twoStateLam) n
        = ((2 : ℝ) ^ n)⁻¹)
    ∧ Core.Mixing (densOp twoStateLam (flipK (3 / 4))) (meanOp twoStateLam)
    ∧ Core.Mixing.B (densOp twoStateLam (flipK (3 / 4))) (meanOp twoStateLam) = 2
    ∧ ‖Ring.inverse (1 - funOp twoStateLam (flipK (3 / 4)) + meanOp twoStateLam)
        - meanOp twoStateLam‖
      ≠ Core.Mixing.B (densOp twoStateLam (flipK (3 / 4))) (meanOp twoStateLam) := by
  have hq0 : (0 : ℝ) < 3 / 4 := by norm_num
  have hq1 : (3 / 4 : ℝ) < 1 := by norm_num
  have habs : |1 - 2 * (3 / 4 : ℝ)| = 1 / 2 := by norm_num [abs_of_neg]
  have hS : ‖Ring.inverse (1 - funOp twoStateLam (flipK (3 / 4)) + meanOp twoStateLam)
      - meanOp twoStateLam‖ = 2 / 3 := by
    rw [norm_diffusion_flipK hq0]; norm_num
  have hB : Core.Mixing.B (densOp twoStateLam (flipK (3 / 4))) (meanOp twoStateLam) = 2 := by
    rw [B_flipK hq0 hq1, habs]; norm_num
  refine ⟨fun mu hinv htot => flipK_invariant_unique (by norm_num) hinv htot,
    flipK_isInvariant _, fun f hf => ?_, hS, fun n => ?_, mixing_flipK hq0 hq1, hB, ?_⟩
  · rw [flipK_funAct_centred _ hf]
    funext x
    norm_num
  · rw [beta_flipK, habs, one_div, inv_pow]
  · rw [hS, hB]; norm_num

/-- **`rem:doubling_two_constants`, "at the flip probability `1/2` both equal `1`"**. -/
theorem two_constants_flip_half :
    ‖Ring.inverse (1 - funOp twoStateLam (flipK (1 / 2)) + meanOp twoStateLam)
        - meanOp twoStateLam‖ = 1
    ∧ Core.Mixing.B (densOp twoStateLam (flipK (1 / 2))) (meanOp twoStateLam) = 1 := by
  have hq0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hq1 : (1 / 2 : ℝ) < 1 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [norm_diffusion_flipK hq0]; norm_num
  · rw [B_flipK hq0 hq1]; norm_num

/-- The flip chain at `q = 1/2` is `Freezing.lean`'s `twoStateK`, the chain of
`prop:nonlinear_freezing`(2), whose `B̂ = 1` is `twoState_B_densOp`. -/
theorem flipK_half_eq_twoStateK : flipK (1 / 2) = twoStateK := by
  funext x y
  unfold flipK twoStateK
  split_ifs <;> norm_num

/-- **The ordering, checked on the witness**: `bhat_le_mixing_sum` applies to the flip chain at
`3/4` (its hypotheses are met), and returns `2/3 ≤ 2`. -/
theorem bhat_le_mixing_sum_check :
    ‖Ring.inverse (1 - funOp twoStateLam (flipK (3 / 4)) + meanOp twoStateLam)
        - meanOp twoStateLam‖ ≤ 2 := by
  refine bhat_le_mixing_sum (flipK_isMarkov (by norm_num) (by norm_num)) (flipK_isInvariant _)
    twoStateLam_pos twoStateLam_sum fun N => ?_
  have hm := mixing_flipK (q := 3 / 4) (by norm_num) (by norm_num)
  have hB : Core.Mixing.B (densOp twoStateLam (flipK (3 / 4))) (meanOp twoStateLam) = 2 :=
    two_constants_flip_three_quarters.2.2.2.2.2.2.1
  rw [← hB]
  exact hm.summable.sum_le_tsum _ fun n _ => norm_nonneg _

/-- **Non-vacuity of `diffusion_apply_eq_series`**: on the flip chain at `3/4` the series
`Σ(P⋆ⁿ − Π)` converges in operator norm, so the trajectory reading applies there. -/
theorem diffusion_series_converges_check :
    ∃ U : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      Tendsto (partialSum (funOp twoStateLam (flipK (3 / 4))) (meanOp twoStateLam)) atTop
        (𝓝 U) := by
  have hs : Summable fun n : ℕ =>
      ‖funOp twoStateLam (flipK (3 / 4)) ^ n - meanOp twoStateLam‖ := by
    have h : (fun n : ℕ => ‖funOp twoStateLam (flipK (3 / 4)) ^ n - meanOp twoStateLam‖)
        = fun n => Core.Mixing.beta (densOp twoStateLam (flipK (3 / 4))) (meanOp twoStateLam) n :=
      funext fun n => norm_funOp_pow_sub twoStateLam_pos _ n
    rw [h]
    exact (mixing_flipK (q := 3 / 4) (by norm_num) (by norm_num)).summable
  haveI : CompleteSpace (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
    FiniteDimensional.complete ℝ _
  exact ⟨_, (Summable.of_norm hs).hasSum.tendsto_sum_nat⟩

end Witness

end GFNBounds.Doubling.Remarks
