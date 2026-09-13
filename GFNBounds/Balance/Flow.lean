import GFNBounds.Core.Mixing
import GFNBounds.Balance.FirstVariation
import GFNBounds.Balance.Lojasiewicz
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The gradient flow: the identity `−𝓛̇ = ‖D‖²`, and the decay Grönwall turns the coercivity into

**`theo:first_variation_full`** — statement `proofs.tex:447–453`, proof `proofs.tex:455–483`;
**along a trajectory only**, see SCOPE.
**`theo:db_stable_frozen_full`** — statement `proofs.tex:592–602`, proof `proofs.tex:604–610`;
**the continuous half only**, with the linearization hypothesised and not derived, see SCOPE.
**`cor:global_lojasiewicz`** — statement `proofs.tex:875–886`, proof `proofs.tex:887–898`;
**both displays**, along the flow.
**`prop:no_distant_equilibrium`** **item *(2)***, its **first half only** — statement
`proofs.tex:791`, proof `proofs.tex:807`; see SCOPE.
(The bold-backtick form of each label is what `scripts/trace_check.py` and the paper-side ledger
machine-read; a label mentioned only in prose is not a claim to certify it.)

> (`theo:db_stable_frozen_full`) In the setting of Theorem `theo:gd_diffusion_full`, assume
> moreover that `T` is ergodic with summable `L²`-mixing, `B̂ := ∑_{n≥0} β̂_n < ∞`, and
> `w ≥ w_min > 0`. Set `ϱ := g''(1) w_min / B̂²`. Then along the linearized gradient flow of
> `𝓛_{g,ν}` at the balanced solution: the component `Πh_t` (the total flow normalization) is
> conserved, and `‖h_t − Πh_t‖_{L²(λ)} ≤ e^{−ϱt} ‖h_0 − Πh_0‖_{L²(λ)}`. For discrete gradient
> descent with step `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}`, the contraction factor per step is `1 − εϱ`.

> (proof) Let `H := g''(1) A^† M_w A ⪰ 0`. `ΠH = 0` since `P^†` preserves integrals, so `Πh_t`
> is conserved; and for `h_⊥ := h − Πh`, using `Ah = Ah_⊥` and Lemma `lem:sigma_mixing`,
> `⟨h, Hh⟩ ≥ g''(1) w_min ‖Ah_⊥‖² ≥ ϱ‖h_⊥‖²`, whence
> `d/dt ‖h_⊥‖² = −2⟨h, Hh⟩ ≤ −2ϱ‖h_⊥‖²` and Grönwall concludes.

> (`prop:no_distant_equilibrium`*(2)*) *The inflation is the algorithm.* For fixed `ν = wλ` the
> loss is scale-invariant, so the gradient flow preserves `‖u_t‖_{L²(λ)}`, while by *(1)* the
> total mass `μ_t(𝒮̂)` strictly increases off balance: training is a monotone ascent of the mass
> on a sphere of `𝓜²(λ)`, whose unique maximizer (Cauchy–Schwarz) is the balanced flow. […]

> (proof of *(2)*) For fixed `ν`, `r(cμ) = r(μ)` gives `𝓛_{g,ν}(cμ) = 𝓛_{g,ν}(μ)`, whence
> `0 = d/dc 𝓛(cμ)|_{c=1} = ⟨∇𝓛, μ⟩_{𝓜²(λ)} = ∫ Du dλ`: the gradient is orthogonal to the radial
> direction, so `d/dt ‖u_t‖²_{L²(λ)} = −2∫ Du dλ = 0`. […]

> (`cor:global_lojasiewicz`) In the setting of Proposition `prop:no_distant_equilibrium`*(3)* —
> `g = (log x)²`, finite state space, `ν = wλ` with `w_min ≤ w ≤ ‖w‖_{L^∞}` — set
> `M := max(1, √(𝓛(μ₀)/(w_min λ_min)))` and
> `κ := w_min λ_min^{1/2}/(‖u₀‖_{L²(λ)} ‖w‖_{L^∞} M)`. Then, along the gradient flow,
> `−d𝓛/dt ≥ κ²𝓛²`, hence `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1} + κ²t)^{−1}`.

> (its proof, last words) […] conclude with `−𝓛' = ‖∇𝓛‖²`.

## Why this file exists

Three places in the strict library disclose the same missing layer, in the same words.
`GFNBounds/Balance/MassIdentity.lean` records that items *(2)*–*(3)* of
`prop:no_distant_equilibrium` and the convergence half of `theo:global_dichotomy_full` "need a
gradient-flow / LaSalle layer". `GFNBounds/Balance/Lojasiewicz.lean` certifies
`cor:global_lojasiewicz` only in its **static** form `‖D‖² ≥ κ²𝓛²`, and says that the paper's
`−𝓛̇ ≥ κ²𝓛²` follows from it "only through the flow identity `−𝓛̇ = ‖D‖²`, which this library
does not have and does not state". `theo:db_stable_frozen_full` has no Lean at all.

The layer is supplied here, and it is smaller than it looks. **On a finite state space a
gradient flow is an ODE in `ℝ^V`**: `IsGradientFlow` is `u̇(t)(x) = −D(u(t))(x)`, one scalar
equation per state, and the flow identity is the chain rule composed with
`FirstVariation.hasDerivAt_loss_ipL2` — the derivative in the direction `u̇ = −D` is
`⟪D ∣ −D⟫_λ = −‖D‖²`. Nothing below asserts that such a curve *exists*: every statement is of
the form "for any curve satisfying the ODE, …", which is a conditional statement and is exactly
how the paper's own proofs read.

`hasDerivAt_loss_flow` discharges the disclosure in all three places at once, and
`global_lojasiewicz_flow` is `cor:global_lojasiewicz` with both of its displays, no longer
conditional on an unstated identity.

## What is proved

| | |
|---|---|
| `lossGrad`, `IsGradientFlow` | `D` as a function of the flow, and the ODE `u̇ = −D(u)` |
| `isGradientFlow_iff` | the componentwise ODE **is** the vector-valued one, by `hasDerivAt_pi` — the "ODE in `ℝ^V`" is not a reading, it is the same statement |
| `hasDerivAt_ratio_comp` | `δr = v − ru` along an arbitrary curve, by the quotient rule |
| `hasDerivAt_loss_comp` | `δ𝓛_{g,ν} = ∫ g'(r)[d(δT)/dμ − r dδ/dμ] dν` along an arbitrary curve — `proofs.tex:469–470` |
| `hasDerivAt_loss_comp_ipL2` | `d/dt 𝓛_{g,ν}(μ_t) = ⟨D(μ_t) ∣ μ̇_t⟩_λ`: `theo:first_variation_full`'s display read along a trajectory. The adjoint step is `FirstVariation.firstVariation_adjoint`, reused and not reproved |
| `hasDerivAt_loss_flow_at`, `hasDerivAt_loss_flow` | **the flow identity** `−𝓛̇ = ‖D‖²_{L²(λ)}` — `proofs.tex:813`, `proofs.tex:897`. This is the statement the three disclosures name. `_at` asks positivity at **one** time; `hasDerivAt_loss_flow` asks it on `[0,∞)`, where `BoundaryBlowup.flow_pos_graph` supplies it |
| `hasDerivAt_loss_flow_line` | the same along the Euler line `u − sD(u)`, which needs no existence theorem: the gradient-descent direction dissipates at rate `‖D‖²` |
| `ipL2_lossGrad_self` | `∫ Du dλ = 0`, the orthogonality of `prop:no_distant_equilibrium`*(2)* — an identity, needing neither invariance of `λ` nor anything of `g` |
| `nrmL2_const_on_Ici`, `nrmL2_const_of_flow` | **the invariant sphere**: the gradient flow preserves `‖u_t‖_{L²(λ)}` on `[0,∞)`. `Lojasiewicz.lean` carries this as a hypothesis and discloses that it is item *(2)*'s; here it is a conclusion. The two differ only in whether `t` is explicit; `ipL2_lossGrad_self` asks positivity at **one** time, which is what lets the sphere be used inside `BoundaryBlowup`'s continuation |
| `eq_of_hasDerivAt_zero_on` | vanishing derivative on a convex set gives a constant; general-purpose, and the half-line replacement for `is_const_of_deriv_eq_zero` |
| `hasDerivAt_logSq` | `g = (log x)²` has `g' = 2 log x / x` on `ℝ_+^*` — `Lojasiewicz.lean` declares `logSq` and `logSqDeriv` independently and never ties them; the flow ODE needs the tie |
| `lossGrad_of_weight`, `loss_eq_lossVal` | the two changes of variable that let `Lojasiewicz.lean`'s `ν = wλ` statements meet `Freezing.lean`'s `loss` |
| `lojasiewicz_integrated` | `−L' ≥ κ²L² ⇒ L(t) ≤ (L(0)^{−1} + κ²t)^{−1}`: `cor:global_lojasiewicz`'s **second** display, integrated by monotonicity of `1/L − κ²t`. Every hypothesis is on `[0,∞)` |
| `global_lojasiewicz_flow` | **`cor:global_lojasiewicz`**, both displays, along the gradient flow, with `κ` an explicit formula |
| `inner_ge_of_mixing` | `⟨h, Hh⟩ ≥ (c/B̂²)‖h − Πh‖²` from `⟨h, Hh⟩ ≥ c‖(I−P)h‖²` and `lem:sigma_mixing` — the display `proofs.tex:606–608`, with `c = g''(1)w_min` |
| `stable_frozen_decay` | **`theo:db_stable_frozen_full`**, continuous half: `Πh_t` conserved, and `‖h_t − Πh_t‖ ≤ e^{−ϱt}‖h_0 − Πh_0‖` |
| `twoState_nrmL2_lossGrad_sq`, `twoState_hasDerivAt_loss_flow` | the flow identity **evaluated**: `405/128`, against a number computed by hand off the paper's display |
| `scalar_decay_check` | the decay **evaluated**, and shown tight: the hypotheses of `stable_frozen_decay` are jointly satisfiable and the bound is attained |

## SCOPE (disclosed)

* **No existence theorem, and none is needed.** Nothing here produces a solution of
  `u̇ = −D(u)`, or of `ḣ = −Hh`. Every statement quantifies over curves that satisfy the ODE, so
  a reader who wants a trajectory must supply one; `hasDerivAt_loss_flow_line` and
  `scalar_decay_check` supply the two the file uses, both by hand. This is what the paper's own
  proofs assume — "along the gradient flow" — and no more.
* **Finite state space**, for everything in `GFNBounds.Balance`: `∫ · dλ` is `∑ x, λ x * ·` and a
  measure is carried by a density. `paper-map.json` records the general statements as bucket
  `D`; nothing below moves them.
* **The linearization of `theo:db_stable_frozen_full` is a hypothesis, not a derivation.** The
  paper's `H := g''(1) A^† M_w A` comes from `theo:gd_diffusion_full`, which is bucket `D` and is
  not formalized. `stable_frozen_decay` therefore takes an *abstract* `H : E →L[ℝ] E` and asks of
  it only what the paper's proof uses: `Π H = 0` and `⟨x, Hx⟩ ≥ ϱ‖x − Πx‖²`. Identifying that
  `H` with the Hessian of `𝓛_{g,ν}` at the balanced solution — and hence `ϱ` with
  `g''(1)w_min/B̂²` — is a separate job and is **not** done here. What *is* delivered is the step
  the proof calls "Grönwall concludes", and `inner_ge_of_mixing` is the step before it, which is
  where `lem:sigma_mixing` enters.
* **`Π` is hypothesised self-adjoint** (`hPisa`), which the paper's `Π` — the orthogonal
  projection `f ↦ (∫f dλ)𝟏` onto the invariant functions — is. It is used once, to turn
  `⟨h_⊥, Hh⟩` into the paper's `⟨h, Hh⟩`; self-adjointness of `H` is *not* assumed and is not
  needed. Idempotence of `Π` is not assumed either.
* **The discrete half of `theo:db_stable_frozen_full` is not in *this* file.** "For discrete
  gradient descent with step `ε ≤ (4g''(1)‖w‖_{L^∞})^{−1}`, the contraction factor per step is
  `1 − εϱ`" is `GFNBounds/Balance/Discrete.lean` (2026-09-12), which carries the two hypotheses
  the abstract `H` above does not — `H` **self-adjoint** and `Π` idempotent — and shows that the
  route this sentence's proof names, the energy method through `‖Hx‖² ≤ ‖H‖⟨x, Hx⟩`, delivers
  only `√(1 − εϱ)`; the printed factor needs symmetry. `WeightedL2.lean` then instantiates it at
  the paper's own `H`. Neither is the transfer to the FM
  and DB losses through `lem:lift_mixing`, nor the nonlinear upgrade
  `theo:local_convergence_full`.
* **`inner_ge_of_mixing` is stated with `(1 − P)`, the paper's `A` with `A = P − I`.** The two
  differ by a sign and have the same norm, and `Core.Mixing.coercivity` — which is
  `lem:sigma_mixing`, already closed — is stated with `1 − P`. The hypothesis
  `c‖(1−P)x‖² ≤ ⟨x, Hx⟩` is the paper's `⟨h, Hh⟩ ≥ g''(1)w_min‖Ah_⊥‖²` **after** its own step
  `Ah = Ah_⊥`; that step is a property of the paper's `A` and is folded into the hypothesis
  rather than derived.
* **`global_lojasiewicz_flow` carries two hypotheses the paper derives, and no longer a third.**
  The standing bound `𝓛(μ_t) ≤ L₀` (`hL0`, which the paper's `𝓛(μ_t) ≤ 𝓛(μ₀)` supplies — that
  `𝓛` decreases along the flow follows from the flow identity but is not stated) and positivity
  `𝓛(μ_t) > 0` (`hpos`) are assumed at every time. Positivity is not in the paper at all: the
  conclusion is trivially true where `𝓛` vanishes, but the route through `1/𝓛` needs it, and
  `𝓛 = ∫ g(r)dν` is `0` only at balance. The **invariant sphere** used to be the third and is
  now `nrmL2_const_of_flow`, so `‖u₀‖` in `κ` is literally `‖u_0‖ = ‖dμ₀/dλ‖_{L²(λ)}`.
* **Of item *(2)* only the first half is proved.** `ipL2_lossGrad_self` and
  `nrmL2_const_of_flow` give "the loss is scale-invariant, so the gradient flow preserves
  `‖u_t‖_{L²(λ)}`". The rest of the item — the total mass strictly increases off balance, the
  mass is a strict Lyapunov function, and its unique maximizer on the sphere is the balanced flow
  by Cauchy–Schwarz — is **not** stated. `MassIdentity.no_distant_equilibrium_one` has the
  ingredient (`∫ D dλ ≤ 0`, `= 0` iff balanced) but the monotonicity and the maximizer are not
  assembled, and the LaSalle argument of item *(3)*'s convergence half is untouched.
* **`lojasiewicz_integrated` is a statement about real functions**, with no flow in it: it
  integrates `−L' ≥ κ²L²` on `[0,∞)` by the monotonicity of `1/L − κ²t`. It is stated for any
  `L` positive and differentiable on `[0,∞)` — every one of its three hypotheses ranges over the
  half-line its conclusion does, so a caller that only has the flow on `[0,∞)` can discharge them
  all (kb `0022`).
* **The chain rule along a curve is proved directly, not by upgrading the directional
  derivative.** `FirstVariation.lean`'s theorem is `HasDerivAt (fun t => 𝓛(μ + tδ)) ⟪Φ∣δ⟩ 0` —
  a derivative along a *line*, which does not compose with an arbitrary curve. Rather than prove
  Fréchet differentiability (which the paper's uniform remainder estimate would support, and
  which `FirstVariation.lean` deliberately does not state), `hasDerivAt_ratio_comp` and
  `hasDerivAt_loss_comp` redo the quotient rule and the one-variable chain rule along the curve,
  in the same two steps. Only the **adjoint** step is reused —
  `FirstVariation.firstVariation_adjoint`, which is where `lem:adjoint`*(3)* and invariance of
  `λ` are spent — so nothing about `theo:first_variation_full` is reproved and nothing about it
  is strengthened beyond "the same derivative formula holds along a curve".
* **`T` Markov is never used.** As in `FirstVariation.lean`, `K ≥ 0` and `λ`-invariance are all
  that is carried, and row-stochasticity is used nowhere.
* **`ϱ > 0` is not hypothesised**, in `stable_frozen_decay` or in `inner_ge_of_mixing`'s output.
  Grönwall gives the display for any real `ϱ` by the same proof — for `ϱ ≤ 0` it is a growth
  bound rather than a decay — and the paper's `ϱ = g''(1)w_min/B̂²` is positive on its own
  hypotheses. Recorded as a strengthening, not silently taken.
* **The two numerical checks are each partial.** `twoState_hasDerivAt_loss_flow` evaluates the
  flow identity, and `scalar_decay_check` evaluates the decay — but the latter runs at `Π = 0`,
  where the conserved-component conjunct of `stable_frozen_decay` says nothing. Exercising both
  conjuncts at once needs `dim E ≥ 2` with a non-trivial orthogonal projection, and is not done.
* **The trajectory's positivity is ranged over `[0,∞)`, and is no longer a standing
  hypothesis of the convergence block.** `hasDerivAt_loss_flow`, `nrmL2_const_of_flow` and
  `global_lojasiewicz_flow` take `hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x`, which is what
  `BoundaryBlowup.flow_pos_graph` proves from `0 < u₀`; they read `∀ t x` until 2026-09-13 and
  were undischargeable in that form (kb `0022`). The price is paid in two conclusions:
  `hasDerivAt_loss_flow` and `nrmL2_const_of_flow` now take `ht : 0 ≤ t` as well, because
  nothing about a flow on `[0,∞)` says anything at a negative time. Neither is used at a negative
  time anywhere in this library, and `hasDerivAt_loss_flow_at` — which asks positivity at the one
  time it differentiates at — is unchanged and available at any real `t`.
* **`sorry`-free.** `#print axioms` on `hasDerivAt_loss_flow`, `nrmL2_const_on_Ici`,
  `stable_frozen_decay`, `inner_ge_of_mixing`, `lojasiewicz_integrated`,
  `global_lojasiewicz_flow` and both numerical
  checks returns `[propext, Classical.choice, Quot.sound]`. Graduated into the strict library on 2026-09-12.

## Hypothesis checklist — `theo:first_variation_full`, along a trajectory

| paper hypothesis | here |
|---|---|
| `𝒮` Polish, `T` a Markov kernel, `λ` invariant | ⚠ **finite** `[Fintype V]`, `K ≥ 0`, `Invariant K lam` — inherited verbatim from `FirstVariation.lean` |
| `μ ∼ λ`, `dμ/dλ ∈ L²(λ)`, `μT ≪ μ`, `r` bounded away from `0`, `∞` | ⚠ `hu : ∀ x, 0 < u t x` and `hlam`; the rest is automatic or vacuous on a `Fintype`, exactly as in `FirstVariation.lean` |
| `g` `C¹` with locally Lipschitz `g'` | ⚠ **weakened** to `∀ y, 0 < y → HasDerivAt g (gd y) y` |
| directions `δ ≪ μ`, `‖dδ/dμ‖_{L^∞} < 1` | ⚠ replaced by *a curve*: `hd : ∀ x, HasDerivAt (fun s => u s x) (v x) t`. The size constraint is what `HasDerivAt … t` quantifies away |
| the conclusion `δ𝓛 = ⟨Φ ∣ δ⟩_λ` | ✓ `hasDerivAt_loss_comp_ipL2`, with `Φ = lossGrad` |

## Hypothesis checklist — `theo:db_stable_frozen_full`

| paper hypothesis | here |
|---|---|
| the setting of `theo:gd_diffusion_full`; `H = g''(1)A^†M_wA` | ✗ **not derived** — `H` is an abstract `E →L[ℝ] E`. See SCOPE |
| `T` ergodic with summable `L²`-mixing, `B̂ < ∞` | ⚠ enters only through `inner_ge_of_mixing`, as `Core.Mixing P Pi` with `0 < B P Pi`; `stable_frozen_decay` itself carries no mixing hypothesis, only the coercivity it produces |
| `w ≥ w_min > 0` | ⚠ folded into the hypothesis `c‖(1−P)x‖² ≤ ⟨x, Hx⟩` of `inner_ge_of_mixing`, with `c = g''(1)w_min` |
| `ϱ := g''(1)w_min/B̂²` | ⚠ **an explicit formula, at one remove**: `inner_ge_of_mixing` produces `c/B P Pi ^ 2` and `stable_frozen_decay` consumes any `rho` satisfying the coercivity. Composing the two gives the paper's `ϱ` once `c = g''(1)w_min` |
| `Π H = 0`, "since `P^†` preserves integrals" | ⚠ **hypothesis** `hPiH`, plus `Π` self-adjoint (`hPisa`). See SCOPE |
| `Ah = Ah_⊥` | ⚠ folded into `inner_ge_of_mixing`'s hypothesis. See SCOPE |
| `L²(λ)` | ⚠ **generalized**: any real inner-product space `E`; `[CompleteSpace E]` only where `lem:sigma_mixing` is invoked |
| `Πh_t` conserved | ✓ first conjunct of `stable_frozen_decay` |
| `‖h_t − Πh_t‖ ≤ e^{−ϱt}‖h_0 − Πh_0‖` | ✓ second conjunct, for `t ≥ 0` |
| the discrete step `1 − εϱ`; the FM/DB transfer | ✗ not stated. See SCOPE |

## Hypothesis checklist — `cor:global_lojasiewicz`

| paper hypothesis | here |
|---|---|
| the setting of `prop:no_distant_equilibrium`*(3)*, `g = (log x)²`, `ν = wλ`, `w_min ≤ w ≤ ‖w‖_{L^∞}` | ✓ inherited from `Lojasiewicz.global_lojasiewicz_sq`, whose own checklist governs |
| `M`, `κ` as displayed | ✓ **explicit formulas**, copied from `global_lojasiewicz_sq` |
| "along the gradient flow" | ✓ `IsGradientFlow K lam (λw) logSqDeriv u` — the ODE, hypothesised of a given curve |
| `−𝓛̇ = ‖∇𝓛‖²` | ✓ `hasDerivAt_loss_flow`. **This is the identity the corollary was conditional on** |
| `−d𝓛/dt ≥ κ²𝓛²` | ✓ the first goal inside `global_lojasiewicz_flow`, from `global_lojasiewicz_sq` |
| `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1} + κ²t)^{−1}` | ✓ the conclusion, for `t ≥ 0` |
| `𝓛` decreases along the flow (used to build `M` from `𝓛(μ₀)`) | ⚠ **hypothesis** `hL0 : ∀ t ≥ 0, 𝓛(μ_t) ≤ L₀`, discharged by `MassAscent.loss_antitone_flow`. Ranged over the half-line on 2026-09-12: it read `∀ t : ℝ` and was then undischargeable at the paper's own `L₀ = 𝓛(μ₀)` — kb `0022`. See SCOPE |
| the invariant sphere `‖u_t‖ = ‖u₀‖` | ✓ **derived**, `nrmL2_const_of_flow`; no longer a hypothesis |
| `𝓛 > 0` along the flow | ⚠ **hypothesis** `hpos`, not in the paper. See SCOPE |

## Hypothesis checklist — `prop:no_distant_equilibrium`*(2)*, first half

| paper hypothesis | here |
|---|---|
| `g` admissible, differentiable, strictly unimodal | ✗ **not carried and not needed**: `ipL2_lossGrad_self` is an identity in `gd`, whatever `gd` is |
| `(𝒮̂, λ, T)` ergodic | ✗ **not carried and not needed**: not even invariance of `λ` is used |
| `ν = wλ` fixed | ✓ `nu` is an arbitrary fixed function of the state; the flow is `IsGradientFlow … nu …` |
| `μ ∼ λ`, `u = dμ/dλ` | ✓ `hlam`, `hu` |
| `r(cμ) = r(μ)`, hence `⟨∇𝓛, μ⟩ = 0` | ⚠ the *conclusion* `∫ Du dλ = 0` is proved directly from `D = Qφ − rφ`, not through scale invariance of the loss, which is not stated |
| `d/dt‖u_t‖² = −2∫ Du dλ = 0` | ✓ `nrmL2_const_of_flow`, along any curve solving the ODE |
| the mass increases off balance; Cauchy–Schwarz; the strict Lyapunov function | ✗ not stated. See SCOPE |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Balance

open Finset
open scoped RealInnerProductSpace

/-! ### The gradient flow, and the identity `−𝓛̇ = ‖D‖²`

`proofs.tex:813`, `:897`. On a finite state space the flow is an ODE in `ℝ^V`, and the identity
is the chain rule of `theo:first_variation_full` evaluated in the direction `μ̇ = −D`. -/

section FlowIdentity

variable {V : Type*} [Fintype V]

/-- **`D(μ) = ∇^λ 𝓛_{g,ν}(μ)` as a function of the flow alone** — `MassIdentity.lossGradDensity`
with `dν/dμ = ν/(λu)` substituted, so that the only free variable left is `u = dμ/dλ`.

This is the right-hand side of the gradient-flow ODE and nothing more; that it *is* the gradient
is `theo:first_variation_full`, proved on a finite state space in
`GFNBounds/Balance/FirstVariation.lean` and used below through `hasDerivAt_loss_comp_ipL2`. -/
noncomputable def lossGrad (K : V → V → ℝ) (lam nu : V → ℝ) (gd : ℝ → ℝ) (u : V → ℝ) : V → ℝ :=
  lossGradDensity K lam u (fun z => nu z / (lam z * u z)) gd

/-- **`μ̇_t = −∇^λ 𝓛_{g,ν}(μ_t)`** (`proofs.tex:569`, `:613`, `:880`), the gradient flow, written
on a finite state space as what it is there: an **ODE in `ℝ^V`**, one scalar equation per state.

`u t x` is the `λ`-density of `μ_t` at the state `x`. Existence of such a curve is not claimed
anywhere in this file; every statement below hypothesises one. -/
def IsGradientFlow (K : V → V → ℝ) (lam nu : V → ℝ) (gd : ℝ → ℝ) (u : ℝ → V → ℝ) : Prop :=
  ∀ (t : ℝ) (x : V), HasDerivAt (fun s : ℝ => u s x) (-lossGrad K lam nu gd (u t) x) t

/-- **The componentwise ODE is the vector-valued one**: `IsGradientFlow` says exactly that the
curve `u : ℝ → (V → ℝ)` has derivative `−D(u t)` in `V → ℝ`.

`Mathlib.hasDerivAt_pi`. This is not a reading of the definition, it is the same statement, and
it is what makes "on a finite state space a gradient flow is an ODE in `ℝ^V`" a theorem rather
than a slogan. -/
theorem isGradientFlow_iff (K : V → V → ℝ) (lam nu : V → ℝ) (gd : ℝ → ℝ) (u : ℝ → V → ℝ) :
    IsGradientFlow K lam nu gd u
      ↔ ∀ t : ℝ, HasDerivAt u (fun x => -lossGrad K lam nu gd (u t) x) t :=
  ⟨fun h t => hasDerivAt_pi.2 (h t), fun h t => hasDerivAt_pi.1 (h t)⟩

/-- **`δr = v − r·u`** (`proofs.tex:463`, `:470`) **along an arbitrary curve**: if the flow moves
with velocity `v` at time `t`, the ratio `r = d(μT)/dμ` moves with velocity
`dirPush − r·dirDens`.

`FirstVariation.hasDerivAt_ratio` is this along a *line*; the proof is the same quotient rule,
`ratio` being a quotient of two affine functionals of the density. Nothing about `K` is used. -/
theorem hasDerivAt_ratio_comp {K : V → V → ℝ} {lam : V → ℝ} {u : ℝ → V → ℝ} {v : V → ℝ} {t : ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u t x)
    (hd : ∀ x, HasDerivAt (fun s : ℝ => u s x) (v x) t) (y : V) :
    HasDerivAt (fun s : ℝ => ratio K lam (u s) y)
      (dirPush K lam (u t) v y - ratio K lam (u t) y * dirDens (u t) v y) t := by
  have h1 : lam y ≠ 0 := (hlam y).ne'
  have h2 : u t y ≠ 0 := (hu y).ne'
  have hM : lam y * u t y ≠ 0 := mul_ne_zero h1 h2
  have hN : HasDerivAt (fun s : ℝ => pushMass K lam (u s) y) (pushMass K lam v y) t := by
    simp only [pushMass]
    exact HasDerivAt.fun_sum fun x _ => ((hd x).const_mul (lam x)).mul_const (K x y)
  have hD : HasDerivAt (fun s : ℝ => lam y * u s y) (lam y * v y) t := (hd y).const_mul (lam y)
  have hD0 : (fun s : ℝ => lam y * u s y) t ≠ 0 := hM
  have hq := hN.fun_div hD hD0
  have hval : dirPush K lam (u t) v y - ratio K lam (u t) y * dirDens (u t) v y
      = (pushMass K lam v y * (lam y * u t y) - pushMass K lam (u t) y * (lam y * v y))
        / (lam y * u t y) ^ 2 := by
    simp only [dirPush, dirDens, ratio]
    field_simp
  rw [hval]
  exact hq

/-- **`δ𝓛_{g,ν} = ∫ g'(r)[d(δT)/dμ − r dδ/dμ] dν`** (`proofs.tex:469–470`) **along an arbitrary
curve** — the first variation before the adjoint step.

`FirstVariation.hasDerivAt_loss` is this along a line. Only three things are used: `λ > 0`,
`u_t > 0`, and differentiability of `g` at the values `r` takes; `K` is an arbitrary matrix. -/
theorem hasDerivAt_loss_comp {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ}
    {u : ℝ → V → ℝ} {v : V → ℝ} {t : ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u t x) (hr : ∀ x, 0 < ratio K lam (u t) x)
    (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hd : ∀ x, HasDerivAt (fun s : ℝ => u s x) (v x) t) :
    HasDerivAt (fun s : ℝ => loss K lam nu (u s) g)
      (∑ x, nu x * (gd (ratio K lam (u t) x) *
        (dirPush K lam (u t) v x - ratio K lam (u t) x * dirDens (u t) v x))) t := by
  simp only [loss]
  refine HasDerivAt.fun_sum fun z _ => HasDerivAt.const_mul (nu z) ?_
  exact (hg _ (hr z)).comp t (hasDerivAt_ratio_comp hlam hu hd z)

/-- **`theo:first_variation_full` read along a trajectory**: `d/dt 𝓛_{g,ν}(μ_t) = ⟨D(μ_t) ∣ μ̇_t⟩_λ`
(`proofs.tex:450`, `:475`), with `D = lossGrad`.

The adjoint step — `lem:adjoint`*(3)*, where invariance of `λ` and `K ≥ 0` are spent — is
`FirstVariation.firstVariation_adjoint`, reused verbatim rather than reproved. What is new is
only that the direction is the velocity of a curve instead of a fixed vector. -/
theorem hasDerivAt_loss_comp_ipL2 {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ}
    {u : ℝ → V → ℝ} {v : V → ℝ} {t : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u t x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hd : ∀ x, HasDerivAt (fun s : ℝ => u s x) (v x) t) :
    HasDerivAt (fun s : ℝ => loss K lam nu (u s) g)
      (Graph.ipL2 lam (lossGrad K lam nu gd (u t)) v) t := by
  rw [lossGrad, ← firstVariation_adjoint hinv hK hlam hu v]
  exact hasDerivAt_loss_comp hlam hu (ratio_pos hinv hK hlam hu) hg hd

/-- **The flow identity `−𝓛̇ = ‖D‖²_{L²(λ)}`** (`proofs.tex:813`: "`d𝓛/dt = −‖D‖²`";
`proofs.tex:897`: "conclude with `−𝓛' = ‖∇𝓛‖²`"), hypothesised at a single time `t`.

This is the statement `GFNBounds/Balance/MassIdentity.lean`, `GFNBounds/Balance/Lojasiewicz.lean`
and the map's `cor:global_lojasiewicz` row all disclose as missing. It is the chain rule
`hasDerivAt_loss_comp_ipL2` evaluated in the direction `μ̇ = −D`, where the pairing
`⟪D ∣ −D⟫_λ` is `−‖D‖²`.

Stated at one time so that a *straight line* through `μ` — which satisfies the ODE at `t` and
nowhere else — is admissible; see `hasDerivAt_loss_flow_line`. -/
theorem hasDerivAt_loss_flow_at {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ}
    {u : ℝ → V → ℝ} {t : ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u t x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hflow : ∀ x, HasDerivAt (fun s : ℝ => u s x) (-lossGrad K lam nu gd (u t) x) t) :
    HasDerivAt (fun s : ℝ => loss K lam nu (u s) g)
      (-(Graph.nrmL2 lam (lossGrad K lam nu gd (u t)) ^ 2)) t := by
  have h := hasDerivAt_loss_comp_ipL2 (nu := nu) (g := g)
    (v := fun x => -lossGrad K lam nu gd (u t) x) hinv hK hlam hu hg hflow
  have hval : Graph.ipL2 lam (lossGrad K lam nu gd (u t))
      (fun x => -lossGrad K lam nu gd (u t) x)
      = -(Graph.nrmL2 lam (lossGrad K lam nu gd (u t)) ^ 2) := by
    rw [Graph.sq_nrmL2 (fun x => (hlam x).le)]
    simp only [Graph.ipL2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rwa [hval] at h

/-- **The flow identity `−𝓛̇ = ‖D‖²_{L²(λ)}` along a gradient flow** (`proofs.tex:813`, `:897`):
the loss decreases at exactly the squared norm of its gradient, at every time of `[0,∞)`.

`hu` is ranged over the half-line the trajectory lives on, which is where
`BoundaryBlowup.flow_pos_graph` discharges it — kb `0022`. -/
theorem hasDerivAt_loss_flow {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ}
    {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y)
    (hflow : IsGradientFlow K lam nu gd u) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => loss K lam nu (u s) g)
      (-(Graph.nrmL2 lam (lossGrad K lam nu gd (u t)) ^ 2)) t :=
  hasDerivAt_loss_flow_at hinv hK hlam (hu t ht) hg (hflow t)

/-- **The flow identity along the Euler line `u − sD(u)`**: the gradient-descent *direction*
dissipates the loss at rate `‖D‖²_{L²(λ)}`, with no flow to exist.

The straight line through `μ` with velocity `−D(μ)` satisfies the gradient-flow ODE at `s = 0`
and in general nowhere else, which is all `hasDerivAt_loss_flow_at` asks. It is what makes the
identity checkable on an explicit instance (`twoState_hasDerivAt_loss_flow`) without a solution
of the ODE. -/
theorem hasDerivAt_loss_flow_line {K : V → V → ℝ} {lam nu : V → ℝ} {g gd : ℝ → ℝ} {u : V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (hu : ∀ x, 0 < u x) (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (gd y) y) :
    HasDerivAt (fun s : ℝ => loss K lam nu (fun x => u x - s * lossGrad K lam nu gd u x) g)
      (-(Graph.nrmL2 lam (lossGrad K lam nu gd u) ^ 2)) 0 := by
  have hline : (fun x => u x - (0 : ℝ) * lossGrad K lam nu gd u x) = u := by
    funext x; ring
  have hcurve : ∀ x : V, HasDerivAt (fun s : ℝ => u x - s * lossGrad K lam nu gd u x)
      (-lossGrad K lam nu gd u x) 0 := by
    intro x
    have h1 : HasDerivAt (fun s : ℝ => u x - s * lossGrad K lam nu gd u x)
        (0 - 1 * lossGrad K lam nu gd u x) 0 :=
      (hasDerivAt_const (0 : ℝ) (u x)).sub
        ((hasDerivAt_id' (0 : ℝ)).mul_const (lossGrad K lam nu gd u x))
    rwa [zero_sub, one_mul] at h1
  have h := hasDerivAt_loss_flow_at (K := K) (lam := lam) (nu := nu) (g := g) (gd := gd)
    (u := fun (s : ℝ) (x : V) => u x - s * lossGrad K lam nu gd u x) (t := 0)
    hinv hK hlam (fun x => by simpa using hu x) hg
    (by rw [hline]; exact hcurve)
  rw [hline] at h
  exact h

/-- **`prop:no_distant_equilibrium`*(2)*, the orthogonality**: `∫ D u dλ = 0` (`proofs.tex:791`,
"the gradient is orthogonal to the radial direction").

An identity, with no hypothesis beyond `λ, u > 0`: both terms of `D = Qφ − rφ` pair against `u`
to `∑_y φ(y) (μT)(y)`, the first by exchanging the two sums and the second because
`λ(x)u(x)r(x)` is `(μT)(x)` by definition of `r`. Invariance of `λ` is not used. -/
theorem ipL2_lossGrad_self {K : V → V → ℝ} {lam u : V → ℝ} (nu : V → ℝ) (gd : ℝ → ℝ)
    (hlam : ∀ x, 0 < lam x) (hu : ∀ x, 0 < u x) :
    Graph.ipL2 lam (lossGrad K lam nu gd u) u = 0 := by
  set phi : V → ℝ := fun y => gd (ratio K lam u y) * (nu y / (lam y * u y)) with hphi
  have hQ : (∑ x, lam x * (funAct K phi x * u x)) = ∑ y, phi y * pushMass K lam u y := by
    have hexp : ∀ x : V, lam x * (funAct K phi x * u x)
        = ∑ y, lam x * u x * K x y * phi y := by
      intro x
      simp only [funAct, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hexp x, Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => by rw [← Finset.sum_mul, pushMass, mul_comm]
  have hR : (∑ x, lam x * (ratio K lam u x * phi x * u x))
      = ∑ y, phi y * pushMass K lam u y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : lam x ≠ 0 := (hlam x).ne'
    have h2 : u x ≠ 0 := (hu x).ne'
    have hkey : lam x * u x * ratio K lam u x = pushMass K lam u x := by
      simp only [ratio]
      field_simp
    calc lam x * (ratio K lam u x * phi x * u x)
        = lam x * u x * ratio K lam u x * phi x := by ring
      _ = phi x * pushMass K lam u x := by rw [hkey]; ring
  simp only [Graph.ipL2, lossGrad, lossGradDensity, gradDensity, ← hphi]
  have hsplit : ∀ x : V, lam x * ((funAct K phi x - ratio K lam u x * phi x) * u x)
      = lam x * (funAct K phi x * u x) - lam x * (ratio K lam u x * phi x * u x) :=
    fun x => by ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hsplit x,
    Finset.sum_sub_distrib, hQ, hR, sub_self]

omit [Fintype V] in
/-- A function with vanishing derivative on a convex set is constant on it. -/
theorem eq_of_hasDerivAt_zero_on {f : ℝ → ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (hf : ∀ s ∈ D, HasDerivAt f 0 s) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≤ b) :
    f b = f a := by
  have hmono : MonotoneOn f D :=
    monotoneOn_of_deriv_nonneg hD (fun s hs => ((hf s hs).continuousAt).continuousWithinAt)
      (fun s hs => ((hf s (interior_subset hs)).differentiableAt).differentiableWithinAt)
      fun s hs => by simp [(hf s (interior_subset hs)).deriv]
  have hanti : AntitoneOn f D :=
    antitoneOn_of_deriv_nonpos hD (fun s hs => ((hf s hs).continuousAt).continuousWithinAt)
      (fun s hs => ((hf s (interior_subset hs)).differentiableAt).differentiableWithinAt)
      fun s hs => by simp [(hf s (interior_subset hs)).deriv]
  exact le_antisymm (hanti ha hb hab) (hmono ha hb hab)

/-- **`prop:no_distant_equilibrium`*(2)*, the invariant sphere, on `[0,∞)`**: the gradient flow
preserves `‖u_t‖_{L²(λ)}` (`proofs.tex:791`, "the loss is scale-invariant, so the gradient flow
preserves `‖u_t‖_{L²(λ)}`").

`d/dt‖u_t‖² = −2∫Du dλ = 0` by `ipL2_lossGrad_self`, **which asks positivity at one time only**:
that is what lets the sphere be used inside the continuation of
`BoundaryBlowup.flow_pos_of_pos`. `GFNBounds/Balance/Lojasiewicz.lean` discloses the sphere as
"a hypothesis, not a conclusion", item *(2)* being unformalized; here it is a conclusion, of the
flow. -/
theorem nrmL2_const_on_Ici {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hlam : ∀ x, 0 < lam x) (hupos : ∀ s : ℝ, 0 ≤ s → ∀ x, 0 < u s x)
    (hflow : IsGradientFlow K lam nu gd u) {t : ℝ} (ht : 0 ≤ t) :
    Graph.nrmL2 lam (u t) = Graph.nrmL2 lam (u 0) := by
  have hN : ∀ s ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun z : ℝ => ∑ x, lam x * (u z x * u z x)) 0 s := by
    intro s hs
    have hsum : HasDerivAt (fun z : ℝ => ∑ x, lam x * (u z x * u z x))
        (∑ x, lam x * (-lossGrad K lam nu gd (u s) x * u s x
          + u s x * -lossGrad K lam nu gd (u s) x)) s :=
      HasDerivAt.fun_sum fun x _ => HasDerivAt.const_mul (lam x) ((hflow s x).fun_mul (hflow s x))
    have hrw : ∀ x : V, lam x * (-lossGrad K lam nu gd (u s) x * u s x
        + u s x * -lossGrad K lam nu gd (u s) x)
        = -2 * (lam x * (lossGrad K lam nu gd (u s) x * u s x)) := fun x => by ring
    have hzero : (∑ x, lam x * (-lossGrad K lam nu gd (u s) x * u s x
        + u s x * -lossGrad K lam nu gd (u s) x)) = 0 := by
      rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset V)) => hrw x, ← Finset.mul_sum]
      have h := ipL2_lossGrad_self (K := K) (lam := lam) (u := u s) nu gd hlam (hupos s hs)
      simp only [Graph.ipL2] at h
      rw [h, mul_zero]
    rwa [hzero] at hsum
  have hconst := eq_of_hasDerivAt_zero_on (convex_Ici 0) hN (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr ht) ht
  simp only [Graph.nrmL2, Graph.ipL2]
  rw [hconst]

/-- **`prop:no_distant_equilibrium`*(2)*, the invariant sphere**, in the applied form the
convergence block cites: `‖u_t‖_{L²(λ)} = ‖u₀‖_{L²(λ)}` at every `t ≥ 0`. `nrmL2_const_on_Ici`
with `t` explicit. -/
theorem nrmL2_const_of_flow {K : V → V → ℝ} {lam nu : V → ℝ} {gd : ℝ → ℝ} {u : ℝ → V → ℝ}
    (hlam : ∀ x, 0 < lam x) (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x)
    (hflow : IsGradientFlow K lam nu gd u) (t : ℝ) (ht : 0 ≤ t) :
    Graph.nrmL2 lam (u t) = Graph.nrmL2 lam (u 0) :=
  nrmL2_const_on_Ici hlam hu hflow ht

end FlowIdentity

/-! ### `cor:global_lojasiewicz`, along the flow

`proofs.tex:875–898`. `Lojasiewicz.global_lojasiewicz_sq` supplies `κ²𝓛² ≤ ‖D‖²`; the flow
identity turns it into `−𝓛̇ ≥ κ²𝓛²`, and one integration into the decay. -/

section Lojasiewicz

variable {V : Type*} [Fintype V]

/-- **`g = (log x)²` has `g'(x) = 2 log x / x` on `ℝ_+^*`** (`proofs.tex:809`).

`GFNBounds/Balance/Lojasiewicz.lean` declares `logSq` and `logSqDeriv` as two independent
definitions and discloses that "that `logSqDeriv` is `deriv logSq` is elementary calculus, is not
stated, and is not used". It becomes used here: the gradient-flow ODE for the corollary's
generator is `u̇ = −D` with `D` built from `logSqDeriv`, and the loss being differentiated is
built from `logSq`, so the two must be tied. -/
theorem hasDerivAt_logSq {y : ℝ} (hy : 0 < y) : HasDerivAt logSq (logSqDeriv y) y := by
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy.ne'
  have h2 := hlog.fun_pow 2
  show HasDerivAt (fun x : ℝ => Real.log x ^ 2) (logSqDeriv y) y
  simpa [logSqDeriv, div_eq_mul_inv] using h2

/-- **`dν/dμ = w/u` for `ν = wλ` and `μ = uλ`**, the Radon–Nikodym chain rule on a finite space:
`lossGrad`'s third argument, written in `Lojasiewicz.lean`'s variables. -/
theorem lossGrad_of_weight {K : V → V → ℝ} {lam wf u : V → ℝ} {gd : ℝ → ℝ}
    (hlam : ∀ x, 0 < lam x) :
    lossGrad K lam (fun x => lam x * wf x) gd u
      = lossGradDensity K lam u (fun x => wf x / u x) gd := by
  have hw : (fun z => lam z * wf z / (lam z * u z)) = fun z => wf z / u z := by
    funext z
    rw [mul_div_mul_left _ _ (hlam z).ne']
  simp only [lossGrad, hw]

/-- **`𝓛_{g,ν}(μ) = ∫ g(r) dν = ∑_x λ(x) w(x) g(r(x))`** for `ν = wλ`: `Freezing.loss` and
`Lojasiewicz.lossVal` are the same functional, written against the two parameterizations the two
files use. -/
theorem loss_eq_lossVal (K : V → V → ℝ) (lam wf u : V → ℝ) (gg : ℝ → ℝ) :
    loss K lam (fun x => lam x * wf x) u gg = lossVal lam wf gg (ratio K lam u) :=
  Finset.sum_congr rfl fun x _ => by ring

/-- **`cor:global_lojasiewicz`'s second display** (`proofs.tex:884`): from `−L' ≥ κ²L²` on
`[0,∞)`, `L(t) ≤ (L(0)^{−1} + κ²t)^{−1}`.

A statement about real functions, with no flow in it: `1/L − κ²t` has non-negative derivative on
`(0,∞)`, hence is monotone, which is the inequality. Positivity of `L` on `[0,∞)` is what the
route through `1/L` costs; see the module SCOPE. -/
theorem lojasiewicz_integrated {L L' : ℝ → ℝ} {kappa : ℝ}
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt L (L' t) t)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < L t)
    (hineq : ∀ t : ℝ, 0 ≤ t → kappa ^ 2 * L t ^ 2 ≤ -L' t) :
    ∀ t : ℝ, 0 ≤ t → L t ≤ ((L 0)⁻¹ + kappa ^ 2 * t)⁻¹ := by
  have hyd : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun z : ℝ => (L z)⁻¹ - kappa ^ 2 * z) (-L' s / L s ^ 2 - kappa ^ 2) s := by
    intro s hs
    have h1 : HasDerivAt (fun z : ℝ => (L z)⁻¹) (-L' s / L s ^ 2) s :=
      (hderiv s hs).inv (hpos s hs).ne'
    have h2 : HasDerivAt (fun z : ℝ => kappa ^ 2 * z) (kappa ^ 2) s := by
      simpa using (hasDerivAt_id' s).const_mul (kappa ^ 2)
    exact h1.sub h2
  have hnn : ∀ s : ℝ, 0 < s → 0 ≤ -L' s / L s ^ 2 - kappa ^ 2 := by
    intro s hs
    have hL := hpos s hs.le
    rw [sub_nonneg, le_div_iff₀ (by positivity)]
    exact hineq s hs.le
  have hmono : MonotoneOn (fun z : ℝ => (L z)⁻¹ - kappa ^ 2 * z) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun s hs => ?_) (fun s hs => ?_)
      (fun s hs => ?_)
    · exact ((hyd s hs).continuousAt).continuousWithinAt
    · rw [interior_Ici] at hs
      exact ((hyd s hs.le).differentiableAt).differentiableWithinAt
    · rw [interior_Ici] at hs
      rw [(hyd s hs.le).deriv]
      exact hnn s hs
  intro t ht
  have hle := hmono Set.self_mem_Ici (Set.mem_Ici.2 ht) ht
  simp only [mul_zero, sub_zero] at hle
  have h0 : (L 0)⁻¹ + kappa ^ 2 * t ≤ (L t)⁻¹ := by linarith
  have hL0 : 0 < (L 0)⁻¹ := inv_pos.2 (hpos 0 le_rfl)
  have hkt : 0 ≤ kappa ^ 2 * t := mul_nonneg (sq_nonneg _) ht
  have hden : 0 < (L 0)⁻¹ + kappa ^ 2 * t := by linarith
  have hLt : 0 < L t := hpos t ht
  have hkey : L t * ((L 0)⁻¹ + kappa ^ 2 * t) ≤ 1 := by
    have h1 : L t * ((L 0)⁻¹ + kappa ^ 2 * t) ≤ L t * (L t)⁻¹ :=
      mul_le_mul_of_nonneg_left h0 hLt.le
    rwa [mul_inv_cancel₀ hLt.ne'] at h1
  have hfin : L t ≤ 1 / ((L 0)⁻¹ + kappa ^ 2 * t) := (le_div_iff₀ hden).2 hkey
  rwa [one_div] at hfin

/-- **`cor:global_lojasiewicz`**, both displays, along the gradient flow (statement
`proofs.tex:875–886`, proof `proofs.tex:887–898`): with
`M := max(1, √(L₀/(w_min λ_min)))` and `κ := w_min λ_min^{1/2}/(‖u₀‖ ‖w‖_{L^∞} M)`,
`−d𝓛/dt ≥ κ²𝓛²` and hence `𝓛(μ_t) ≤ (𝓛(μ₀)^{−1} + κ²t)^{−1}`.

`Lojasiewicz.global_lojasiewicz_sq` supplies `κ²𝓛² ≤ ‖D‖²`, `hasDerivAt_loss_flow` supplies
`−𝓛̇ = ‖D‖²`, and `lojasiewicz_integrated` integrates. The constant is an explicit formula, not
an `∃ C`.

Three hypotheses the paper derives are carried here instead — the invariant sphere, the standing
bound `𝓛(μ_t) ≤ L₀`, and `𝓛 > 0`; see the module SCOPE. -/
theorem global_lojasiewicz_flow
    {K : V → V → ℝ} {lam wf : V → ℝ} {lamMin wmin wsup L0 : ℝ} {u : ℝ → V → ℝ}
    (hinv : Invariant K lam) (hK : ∀ x y, 0 ≤ K x y) (hlam : ∀ x, 0 < lam x)
    (htot : ∑ x, lam x = 1) (hu : ∀ t, 0 ≤ t → ∀ x, 0 < u t x)
    (hlmin : ∀ x, lamMin ≤ lam x) (hlmin0 : 0 < lamMin)
    (hwmin : 0 < wmin) (hw : ∀ x, wmin ≤ wf x) (hwsup : ∀ x, wf x ≤ wsup)
    (hu0 : 0 < Graph.nrmL2 lam (u 0))
    (hL0 : ∀ t : ℝ, 0 ≤ t → lossVal lam wf logSq (ratio K lam (u t)) ≤ L0)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < lossVal lam wf logSq (ratio K lam (u t)))
    (hflow : IsGradientFlow K lam (fun x => lam x * wf x) logSqDeriv u) :
    ∀ t : ℝ, 0 ≤ t →
      lossVal lam wf logSq (ratio K lam (u t))
        ≤ ((lossVal lam wf logSq (ratio K lam (u 0)))⁻¹
            + (wmin * Real.sqrt lamMin
                / (Graph.nrmL2 lam (u 0) * wsup
                    * max 1 (Real.sqrt (L0 / (wmin * lamMin))))) ^ 2 * t)⁻¹ := by
  refine lojasiewicz_integrated
    (L := fun s => lossVal lam wf logSq (ratio K lam (u s)))
    (L' := fun s => -(Graph.nrmL2 lam
      (lossGradDensity K lam (u s) (fun x => wf x / u s x) logSqDeriv) ^ 2))
    ?_ hpos ?_
  · intro s hs
    have h := hasDerivAt_loss_flow (K := K) (lam := lam) (nu := fun x => lam x * wf x)
      (g := logSq) (gd := logSqDeriv) hinv hK hlam hu (fun _ hy => hasDerivAt_logSq hy) hflow s hs
    rw [lossGrad_of_weight hlam] at h
    simpa only [loss_eq_lossVal] using h
  · intro s hs
    rw [neg_neg]
    exact global_lojasiewicz_sq hinv hK hlam htot (hu s hs) hlmin hlmin0 hwmin hw hwsup
      (nrmL2_const_of_flow hlam hu hflow s hs) hu0 (hL0 s hs)

end Lojasiewicz

/-! ### One instance, computed

`prop:nonlinear_freezing`*(2)*'s two-state chain, already in the library with its ratios
`r = (3/4, 3/2)` proved, is the cheapest place to evaluate the flow identity. -/

section TwoState

/-- **The dissipation rate, evaluated.** On `T(i→j) = 1/2`, `λ = (1/2,1/2)`, `μ = (1,1/2)` —
i.e. `u = (2,1)` — with `ν` the counting measure and `g(x) = (x−1)²`, the gradient density is
`D = (9/8, −9/4)` and `‖D‖²_{L²(λ)} = 405/128`.

By hand, off `theo:first_variation_full`'s display: `r = (3/4, 3/2)`, `dν/dμ = (1, 2)`,
`ψ = g'(r)(dν/dμ) = (−1/2, 2)`, `Qψ ≡ 3/4`, so `D(0) = 3/4 − (3/4)(−1/2) = 9/8` and
`D(1) = 3/4 − (3/2)(2) = −9/4`; then `½(9/8)² + ½(9/4)² = 81/128 + 324/128 = 405/128`.
`FirstVariation.twoState_hasDerivAt_loss` independently pins `D(0) = 9/8` through
`⟨D ∣ (1,0)⟩_λ = 9/16`. -/
theorem twoState_nrmL2_lossGrad_sq :
    Graph.nrmL2 twoStateLam
        (lossGrad twoStateK twoStateLam (fun _ => 1) (fun z => 2 * (z - 1)) twoStateU) ^ 2
      = 405 / 128 := by
  rw [Graph.sq_nrmL2 fun x => (twoStateLam_pos x).le]
  simp only [Graph.ipL2, lossGrad, lossGradDensity, gradDensity, funAct, Fin.sum_univ_two,
    twoState_ratio_zero, twoState_ratio_one]
  norm_num [twoStateK, twoStateLam, twoStateU]

/-- **The flow identity, evaluated**: at the two-state point above, the loss falls at rate
`405/128` along the gradient-descent direction.

A formula that has never been evaluated is a formula nobody has checked. This fixes the sign —
`𝓛̇` is *negative* — and the normalization of `lossGrad` against a number computed outside the
derivation. -/
theorem twoState_hasDerivAt_loss_flow :
    HasDerivAt (fun s : ℝ => loss twoStateK twoStateLam (fun _ => 1)
        (fun x => twoStateU x
          - s * lossGrad twoStateK twoStateLam (fun _ => 1) (fun z => 2 * (z - 1)) twoStateU x)
        fun z => (z - 1) ^ 2) (-(405 / 128)) 0 := by
  have hg : ∀ y : ℝ, 0 < y → HasDerivAt (fun z : ℝ => (z - 1) ^ 2) (2 * (y - 1)) y := fun y _ => by
    simpa using ((hasDerivAt_id' y).sub_const 1).fun_pow 2
  rw [← twoState_nrmL2_lossGrad_sq]
  exact hasDerivAt_loss_flow_line (nu := fun _ => 1) twoStateK_invariant
    (fun _ _ => by norm_num [twoStateK]) twoStateLam_pos twoStateU_pos hg

end TwoState

/-! ### `theo:db_stable_frozen_full`: coercivity, then Grönwall

`proofs.tex:592–610`. The linearization is hypothesised — see the module SCOPE — and what is
proved is the decay it implies. -/

section Linearized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`⟨h, Hh⟩ ≥ ϱ‖h − Πh‖²` with `ϱ = c/B̂²`** — the display of `theo:db_stable_frozen_full`'s
proof (`proofs.tex:606–608`), whose `c` is the paper's `g''(1)w_min`.

The input `c‖(I−P)h‖² ≤ ⟨h, Hh⟩` is the paper's `⟨h,Hh⟩ ≥ g''(1)w_min‖Ah_⊥‖²` after its own step
`Ah = Ah_⊥`; the passage to `‖h − Πh‖` is `lem:sigma_mixing`, i.e. `Core.Mixing.coercivity`,
already closed in `GFNBounds/Core/Mixing.lean`. See the module SCOPE for what is hypothesised
rather than derived. -/
theorem inner_ge_of_mixing [CompleteSpace E] {P Pi H : E →L[ℝ] E} {c : ℝ}
    (hmix : Core.Mixing P Pi) (hB : 0 < Core.Mixing.B P Pi) (hc : 0 ≤ c)
    (hH : ∀ x : E, c * ‖(1 - P) x‖ ^ 2 ≤ ⟪x, H x⟫) (x : E) :
    c / Core.Mixing.B P Pi ^ 2 * ‖x - Pi x‖ ^ 2 ≤ ⟪x, H x⟫ := by
  have hco : ‖x - Pi x‖ ≤ Core.Mixing.B P Pi * ‖(1 - P) x‖ := hmix.coercivity x
  have hsq : ‖x - Pi x‖ ^ 2 ≤ (Core.Mixing.B P Pi * ‖(1 - P) x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hco 2
  have hstep : c / Core.Mixing.B P Pi ^ 2 * ‖x - Pi x‖ ^ 2 ≤ c * ‖(1 - P) x‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hB 2)]
    nlinarith [hsq, hc]
  exact hstep.trans (hH x)

/-- **`theo:db_stable_frozen_full`, the continuous half** (statement `proofs.tex:592–602`, proof
`proofs.tex:604–610`): along a curve solving `ḣ = −Hh`, the component `Πh_t` is conserved and
`‖h_t − Πh_t‖ ≤ e^{−ϱt}‖h_0 − Πh_0‖` for `t ≥ 0`.

The paper's proof, step for step: `ΠH = 0` makes `Πh_t` constant; then for `h_⊥ = h − Πh`,
`d/dt‖h_⊥‖² = −2⟨h, Hh⟩ ≤ −2ϱ‖h_⊥‖²`, and **Grönwall concludes** —
`Mathlib.le_gronwallBound_of_liminf_deriv_right_le` at `K = −2ϱ`, `ε = 0`, whose
`gronwallBound δ K 0 x = δ e^{Kx}` is the exponential; the square root is taken at the end.

`H` is **abstract**: the identification with `g''(1)A^†M_wA` is `theo:gd_diffusion_full` and is
not done here, so `ϱ` is any constant satisfying the coercivity rather than `g''(1)w_min/B̂²`.
`inner_ge_of_mixing` produces such a constant from `lem:sigma_mixing`. See the module SCOPE. -/
theorem stable_frozen_decay {H Pi : E →L[ℝ] E} {rho : ℝ} {h : ℝ → E}
    (hPisa : ∀ x y : E, ⟪Pi x, y⟫ = ⟪x, Pi y⟫)
    (hPiH : ∀ x : E, Pi (H x) = 0)
    (hcoer : ∀ x : E, rho * ‖x - Pi x‖ ^ 2 ≤ ⟪x, H x⟫)
    (hflow : ∀ t : ℝ, HasDerivAt h (-H (h t)) t) :
    (∀ t : ℝ, Pi (h t) = Pi (h 0)) ∧
      ∀ t : ℝ, 0 ≤ t → ‖h t - Pi (h t)‖ ≤ Real.exp (-(rho * t)) * ‖h 0 - Pi (h 0)‖ := by
  -- (a) the projected component is conserved
  have hproj : ∀ t : ℝ, HasDerivAt (⇑Pi ∘ h) 0 t := by
    intro t
    have := (Pi.hasFDerivAt (x := h t)).comp_hasDerivAt t (hflow t)
    simpa [map_neg, hPiH] using this
  have hconst : ∀ t : ℝ, Pi (h t) = Pi (h 0) :=
    fun t => is_const_of_deriv_eq_zero (fun s => (hproj s).differentiableAt)
      (fun s => (hproj s).deriv) t 0
  refine ⟨hconst, ?_⟩
  set c : E := Pi (h 0) with hc
  set F : ℝ → ℝ := fun s => ‖h s - c‖ ^ 2 with hF
  -- (b) the energy identity `F' = -2⟪h, Hh⟫`
  have hFd : ∀ t : ℝ, HasDerivAt F (-(2 * ⟪h t, H (h t)⟫)) t := by
    intro t
    have hsub : HasDerivAt (fun s : ℝ => h s - c) (-H (h t)) t := (hflow t).sub_const c
    have hin := hsub.inner ℝ hsub
    have hrw : ⟪h t - c, -H (h t)⟫ + ⟪-H (h t), h t - c⟫ = -(2 * ⟪h t, H (h t)⟫) := by
      have hsym : ⟪-H (h t), h t - c⟫ = ⟪h t - c, -H (h t)⟫ := real_inner_comm _ _
      have hzero : ⟪Pi (h t), H (h t)⟫ = 0 := by
        rw [hPisa, hPiH, inner_zero_right]
      have hsplit : ⟪h t - c, H (h t)⟫ = ⟪h t, H (h t)⟫ := by
        rw [inner_sub_left, ← hconst t, hzero, sub_zero]
      rw [hsym, inner_neg_right, hsplit]
      ring
    have hval : (fun s : ℝ => ⟪h s - c, h s - c⟫) = F := by
      funext s; rw [hF]; exact real_inner_self_eq_norm_sq _
    rw [hval] at hin
    rwa [hrw] at hin
  have hFbound : ∀ t : ℝ, -(2 * ⟪h t, H (h t)⟫) ≤ -(2 * rho) * F t + 0 := by
    intro t
    have h1 : rho * ‖h t - Pi (h t)‖ ^ 2 ≤ ⟪h t, H (h t)⟫ := hcoer (h t)
    rw [hconst t] at h1
    simp only [hF, add_zero]
    nlinarith [h1]
  -- (c) Grönwall
  intro t ht
  have hcont : ContinuousOn F (Set.Icc 0 t) :=
    fun s _ => ((hFd s).continuousAt).continuousWithinAt
  have hslope : ∀ s ∈ Set.Ico (0:ℝ) t, ∀ r : ℝ, -(2 * ⟪h s, H (h s)⟫) < r →
      ∃ᶠ z in nhdsWithin s (Set.Ioi s), (z - s)⁻¹ * (F z - F s) < r := by
    intro s _ r hr
    have := (hFd s).hasDerivWithinAt.liminf_right_slope_le hr
    simpa [slope, vsub_eq_sub] using this
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (f := F)
    (f' := fun s => -(2 * ⟪h s, H (h s)⟫)) (δ := F 0) (K := -(2 * rho)) (ε := 0)
    hcont hslope le_rfl (fun s _ => hFbound s) t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0] at hgron
  -- (d) take square roots
  have hexp : F 0 * Real.exp (-(2 * rho) * (t - 0))
      = (Real.exp (-(rho * t)) * ‖h 0 - Pi (h 0)‖) ^ 2 := by
    have : Real.exp (-(2 * rho) * (t - 0)) = Real.exp (-(rho * t)) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [this, hF, hc]
    ring
  rw [hexp] at hgron
  have hnn : 0 ≤ Real.exp (-(rho * t)) * ‖h 0 - Pi (h 0)‖ :=
    mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have hFt : ‖h t - Pi (h t)‖ ^ 2 ≤ (Real.exp (-(rho * t)) * ‖h 0 - Pi (h 0)‖) ^ 2 := by
    rw [hconst t]; exact hgron
  have hroot := Real.sqrt_le_sqrt hFt
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hroot

end Linearized

/-! ### The decay, computed

A one-dimensional solution of `ḣ = −Hh` on which the bound is attained: the hypotheses are
satisfiable and the rate in the exponent is exactly `ϱ`. -/

section ScalarCheck

/-- **The decay, evaluated and shown tight.** On `E = ℝ` with `H = 2·id`, `Π = 0`, `ϱ = 2` and
`h_t = 5e^{−2t}` — a genuine solution of `ḣ = −Hh` — `stable_frozen_decay` gives
`‖h_t‖ ≤ e^{−2t}‖h_0‖`, and at `t = 1` the two sides are **equal**.

Two things at once: the hypotheses of `stable_frozen_decay` are jointly satisfiable, so nothing
above is vacuous; and the rate in the exponent is exactly `ϱ`, not `ϱ/2` or `2ϱ`, which is
what a sign or factor error in the Grönwall step would have moved.

`Π = 0` here, so the conserved-component conjunct is exercised only vacuously; see the module
SCOPE. -/
theorem scalar_decay_check :
    (∀ t : ℝ, 0 ≤ t →
        ‖5 * Real.exp (-(2 * t))‖ ≤ Real.exp (-(2 * t)) * ‖5 * Real.exp (-(2 * (0 : ℝ)))‖)
      ∧ ‖5 * Real.exp (-(2 * (1 : ℝ)))‖
          = Real.exp (-(2 * (1 : ℝ))) * ‖5 * Real.exp (-(2 * (0 : ℝ)))‖ := by
  constructor
  · have key := stable_frozen_decay (E := ℝ) (H := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (Pi := 0) (rho := 2) (h := fun s : ℝ => 5 * Real.exp (-(2 * s)))
      (fun x y => by simp) (fun x => by simp)
      (fun x => by
        simp only [zero_apply, sub_zero, smul_apply, ContinuousLinearMap.coe_id', id_eq,
          real_inner_smul_right, real_inner_self_eq_norm_sq]
        exact le_rfl)
      (fun t => by
        have h1 : HasDerivAt (fun s : ℝ => -(2 * s)) (-2 : ℝ) t := by
          have h := ((hasDerivAt_id' t).const_mul (2 : ℝ)).neg
          rwa [mul_one] at h
        have h3 : HasDerivAt (fun s : ℝ => 5 * Real.exp (-(2 * s)))
            (5 * (Real.exp (-(2 * t)) * (-2))) t := h1.exp.const_mul 5
        have hval : (5 : ℝ) * (Real.exp (-(2 * t)) * (-2))
            = -((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (5 * Real.exp (-(2 * t))) := by
          simp only [smul_apply, ContinuousLinearMap.coe_id', id_eq]
          ring
        rwa [hval] at h3)
    simpa using key.2
  · norm_num [mul_comm]

end ScalarCheck

end GFNBounds.Balance
