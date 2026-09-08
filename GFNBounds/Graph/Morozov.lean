import GFNBounds.Graph.Setting

/-!
# The training rate in the variables of Morozov et al., with no Markov chain underneath

**`prop:morozov_rate`** — statement `proofs.tex:834–856`, proof `proofs.tex:858–873`.

> Let `(Ĝ, π̂_←)` be the loop closure (Definition `def:loop_closure`) of a finite path-connected
> marked graph with a backward policy positive on its edges, `λ` its invariant probability and
> `P` the density action of the backward chain. For `x ∈ 𝒱` let `σ(x)` be the hitting time of
> `s₀` by the backward chain started at `x` — *the time spent in the graph by the backward
> trajectory of `x`* — and set
>
>   `σ_* := max_x E(σ | X₀ = x)`,  `σ̄ := E_{x ∼ π̂_←(s_f → ·)} E(σ | X₀ = x)`,
>
> `σ̄` being the expected backward-trajectory length of Morozov et al., and let `N(x)` be the
> expected number of visits to `x` of one backward trajectory drawn from the target row
> `π̂_←(s_f → ·)`, with the convention `N(s₀) = N(s_f) = 1`. Then:
> *(1)* `λ(x) = N(x)/(2 + σ̄)` for every `x ∈ 𝒱`; in particular `λ(s₀) = λ(s_f) = 1/(2+σ̄)`;
> *(2)* for every `h ∈ L²(λ)`, `‖h − Πh‖_{L²(λ)} ≤ B̂_σ ‖(I−P)h‖_{L²(λ)}`, with
> `B̂_σ := σ_* √((2+σ̄)/min_x N(x))`;
> *(3)* consequently every occurrence of `B̂` in Theorems `theo:db_stable_frozen`,
> `theo:local_convergence` and `theo:global_dichotomy` may be replaced by `B̂_σ`.
>
> The constant `B̂_σ` is finite without any aperiodicity assumption — on a leveled graph, where
> every trajectory has the same length `t_m` (the autoregressive case), the loop-closed chain is
> periodic and `B̂ = +∞` while `B̂_σ ≤ (t_m+1)√((2+t_m)/min_x N(x))`.

## The question this file was opened to answer

`CLAUDE.md`'s **obstruction 1** — Mathlib v4.31.0 has no discrete-time Markov chain theory — with
its standing caveat, *but check whether the statement really needs one*. Every object the
proposition names is a chain object: `σ` is a hitting time, `N` an expected visit count, and the
proof of item *(2)* builds `u(x) = E(∑_{n<σ(x)} f(X_n) | X₀ = x)`. **None of the three needs a
chain.** Each is the unique solution of a square linear system on `𝒱`, and the systems are what
this file works with:

| paper object | here, as a linear system |
|---|---|
| `E(σ ∣ X₀ = ·)` | `IsHitExp u`: `u(s₀) = 0`, `u(x) = 1 + (Qu)(x)` for `x ≠ s₀` |
| `E(∑_{n<σ} f(X_n) ∣ X₀ = ·)` | `IsPoisson f u`: `u(s₀) = 0`, `u(x) = f(x) + (Qu)(x)` for `x ≠ s₀` |
| the killed occupation measure | `IsGreen g`: `g(s₀) = 0`, `g(y) = π̂(s_f→y) + (g P̂)(y)` for `y ≠ s₀` |
| `N` | `visits g := g + 1_{s₀} + 1_{s_f}` |

Uniqueness of each is a maximum principle plus the irreducibility already proved in
`GFNBounds/Graph/Setting.lean`; existence is then `LinearMap.injective_iff_surjective` on a
finite-dimensional space, the move `Setting.lean`'s `exists_fixed` already makes. Item *(1)*
becomes `visits g` is `P̂`-invariant with total mass `2 + σ̄`, hence `(2+σ̄)λ` — the `Kac.lean`
route on a general finite graph, and with the visit counts rather than just `λ(s₀)`.

**The bound `‖u‖_∞ ≤ σ_* ‖f‖_∞` survives.** That was the open question, since the paper reads it
probabilistically ("a sum of at most `σ_*` terms in expectation"). Algebraically it is a
comparison: `φ := ‖f‖_∞ u − u_f` vanishes at `s₀` and is superharmonic off `s₀`, so the minimum
principle `nonneg_of_superharm_off_src` gives `φ ≥ 0`, i.e. `u_f ≤ ‖f‖_∞ u ≤ ‖f‖_∞ σ_*` — and the
same applied to `−f` bounds `|u_f|`. Unlike the pointwise `u ≥ 0` bound it *does* need
irreducibility, to walk the argmin set down to `s₀`.

## One deviation from the paper's proof, in the safe direction

The paper's item *(2)* proves the coercivity for `I − Q` and then transfers it to `I − P` by
"their restricted inverses have the same norm", an operator-adjoint argument on the mean-zero
subspace — `CLAUDE.md`'s obstruction 2. It is avoided here: the same conclusion follows from
`⟪h₀, h₀⟫ = ⟪h₀, (I−Q)w⟫ = ⟪(I−P)h₀, w⟫ ≤ ‖(I−P)h₀‖ ‖w‖` and `‖w‖ ≤ B̂_σ ‖h₀‖`, so only the
pointwise adjointness identity `⟪Pa, b⟫ = ⟪a, Qb⟫` is used, never an operator norm. The paper's
"`h − u` is `Q`-harmonic, hence constant" step is not needed on this route and is not formalized.

## SCOPE (disclosed)

* **`σ` and `N` are *characterized*, not *constructed*.** `IsHitExp`, `IsPoisson`, `IsGreen` are
  the linear systems the probabilistic objects satisfy, proved here to have exactly one solution
  each. **That those solutions are the expectations the paper names is not formalized** — there
  is no trajectory space, no `E(· ∣ X₀ = x)`, and no chain in this file. Every statement below is
  therefore about a solution of a linear system, and reading it as a statement about hitting
  times is a modelling step taken on the paper's authority, exactly as in
  `GFNBounds/Doubling/Kac.lean`. The identification is the standard first-step decomposition and
  is not in doubt; it is simply not certified here.
* **Item *(3)* is not stated.** It is a remark about how three downstream theorems consume the
  constant — "Lemma `lem:sigma_mixing` enters the proofs only through the coercivity inequality;
  item *(2)* provides the same inequality with `B̂_σ`, and the substitution propagates verbatim".
  Certifying it means formalizing `theo:db_stable_frozen`, `theo:local_convergence` and
  `theo:global_dichotomy` and re-running their proofs with the other constant; none of the three
  is in this library. What *is* checkable is that the inequality delivered here has the same
  shape as `GFNBounds.Core.Mixing.coercivity`, and `morozov_rate` is stated so that a reader can
  see it. The rate `ϱ_σ = g''(1) w_min min N/(σ_*²(2+σ̄))` is not stated: it is `B̂_σ`
  substituted into a theorem this library does not have.
* **The leveled-graph witness is stated only in its `B̂_σ` half.** `Leveled.bsigma_le` proves
  `B̂_σ ≤ (t_m+1)√((2+t_m)/min N)` with `t_m := ℓ(s_f)`, and in fact the sharper
  `σ_* = t_m`, `σ̄ = t_m − 1`. The other half — that the loop-closed chain is periodic, so
  `‖P^n − Π‖ ↛ 0` and `B̂ = +∞` — needs the operator-norm layer of obstruction 2 and is **not**
  stated. Without it the file exhibits a finite `B̂_σ` on a graph where the paper says `B̂` is
  infinite, but does not certify that `B̂` is infinite there.
* **`Leveled` is this file's reading of "leveled graph"**, which the paper describes rather than
  defines: a height `ℓ : 𝒱 → ℝ` with `ℓ(s₀) = 0` rising by exactly `1` along every edge. The
  paper's `t_m` is then `ℓ(s_f)`; its `σ(s_f) ≤ t_m + 1` suggests a convention one shorter than
  this one, so the bound is stated in the paper's looser form, which both readings satisfy.
* **`Π` is the mean.** `proofs.tex:22` fixes `Π f = (∫f dρ/ρ(𝒮))·1` against the kernel's
  invariant measure; `λ` being a probability, that is `meanL2 lam h`. That `Π` is also the
  orthogonal projection onto the invariant functions is not needed and not proved.
* **`L²(λ)` is a weighted sum, not a `MeasureTheory` space.** `ipL2`, `nrmL2` are `Finset` sums
  and a `Real.sqrt`; no `InnerProductSpace` instance is built, so nothing here is stated in terms
  of `‖·‖` or `⟪·,·⟫`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Ĝ` the loop closure of a finite marked graph | ✓ carried — `MarkedGraph`, `BackwardPolicy.phat` of `GFNBounds/Graph/Setting.lean` |
| path-connected | ✓ carried (`MarkedGraph.PathConnected`), read as walks |
| backward policy positive on the edges | ✓ carried (`BackwardPolicy.PositiveOnEdges`) |
| `λ` its invariant probability | ✓ carried as `IsInvProb lam`, whose existence and uniqueness are `theo:universality_graphs`*(1)* |
| `P` the density action of the backward chain | ✓ carried (`pdens`), `(Pa)(y) = (∑_x λ(x)π̂(x→y)a(x))/λ(y)`, the function action of the `λ`-reversal (`proofs.tex:407`) |
| `Q` the function action, the `L²(λ)`-adjoint of `P` | ✓ carried (`qact`); adjointness is `ipL2_pdens_qact`, proved, not assumed |
| `σ(x)` the hitting time of `s₀` | ⚠ **characterized**, not constructed — see SCOPE |
| `N(x)` the expected visit count, `N(s₀) = N(s_f) = 1` | ⚠ **characterized** — `visits`; the two conventions are *proved* (`visits_src`, `visits_snk`), not imposed |
| `h ∈ L²(λ)` | ✓ every `h : V → ℝ`, the space being finite |
| aperiodicity | ✓ not assumed, as the paper insists |
| `s₀ ≠ s_f` | ✓ carried (`MarkedGraph.src_ne_snk`); item *(1)* uses it, unlike `theo:universality_graphs`*(1)* |

## What the paper claims and this file delivers

| paper | here |
|---|---|
| `σ` is well defined | `exists_isHitExp`, `IsHitExp.unique` |
| `N` is well defined | `exists_isGreen`, `IsGreen.unique` |
| `N(s₀) = N(s_f) = 1` | `IsGreen.visits_src`, `IsGreen.visits_snk` |
| `min_x N(x) > 0`, so `B̂_σ` is finite | `IsGreen.visits_pos` |
| the excursion length `∑_x N(x) = 2 + σ̄` | `IsGreen.sum_visits`, from `IsGreen.sum_eq_sigmaBar` |
| *(1)* `λ(x) = N(x)/(2+σ̄)` | `lam_eq_visits_div` |
| *(1)* `λ(s₀) = λ(s_f) = 1/(2+σ̄)` | `lam_src_eq`, `lam_snk_eq` |
| *(2)* `‖h − Πh‖ ≤ B̂_σ ‖(I−P)h‖` | `coercivity_morozov`; `coercivity_lamMin` is the `σ_*/√λ_min` form of `proofs.tex:931` |
| *(2)*'s `‖u‖_∞ ≤ σ_*‖f‖_∞` | `IsPoisson.abs_le_supAbs_mul_sigmaStar` |
| *(1)* and *(2)* at once | `morozov_rate` |
| the leveled bound on `B̂_σ` | `Leveled.bsigma_le` |
| *(3)*, and `B̂ = +∞` on a leveled graph | not stated — see SCOPE |

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph

variable {V : Type*} [Fintype V]

/-! ### Extrema over the (nonempty) vertex set

`𝒱` is nonempty because a marked graph carries `s₀`, so `Finset.sup'`/`inf'` apply with no extra
instance. -/

/-- `max_x u(x)` over the vertices of a marked graph. -/
noncomputable def maxOver (G : MarkedGraph V) (u : V → ℝ) : ℝ :=
  Finset.univ.sup' ⟨G.src, Finset.mem_univ _⟩ u

/-- `min_x u(x)` over the vertices of a marked graph. -/
noncomputable def minOver (G : MarkedGraph V) (u : V → ℝ) : ℝ :=
  Finset.univ.inf' ⟨G.src, Finset.mem_univ _⟩ u

variable {G : MarkedGraph V}

theorem le_maxOver (u : V → ℝ) (x : V) : u x ≤ maxOver G u :=
  Finset.le_sup' u (Finset.mem_univ x)

theorem maxOver_le {u : V → ℝ} {c : ℝ} (h : ∀ x, u x ≤ c) : maxOver G u ≤ c :=
  Finset.sup'_le _ u fun b _ => h b

theorem minOver_le (u : V → ℝ) (x : V) : minOver G u ≤ u x :=
  Finset.inf'_le u (Finset.mem_univ x)

theorem le_minOver {u : V → ℝ} {c : ℝ} (h : ∀ x, c ≤ u x) : c ≤ minOver G u :=
  Finset.le_inf' _ u fun b _ => h b

theorem minOver_pos {u : V → ℝ} (h : ∀ x, 0 < u x) : 0 < minOver G u := by
  obtain ⟨b, -, hb⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V) u ⟨G.src, Finset.mem_univ _⟩
  exact lt_of_lt_of_le (h b) (le_minOver fun x => hb x (Finset.mem_univ x))

/-- `‖f‖_{L^∞}` on a finite vertex set. -/
noncomputable def supAbs (G : MarkedGraph V) (f : V → ℝ) : ℝ := maxOver G fun x => |f x|

theorem le_supAbs (f : V → ℝ) (x : V) : |f x| ≤ supAbs G f :=
  le_maxOver (fun z => |f z|) x

theorem supAbs_nonneg (f : V → ℝ) : 0 ≤ supAbs G f :=
  le_trans (abs_nonneg (f G.src)) (le_supAbs f G.src)

theorem supAbs_le {f : V → ℝ} {c : ℝ} (h : ∀ x, |f x| ≤ c) : supAbs G f ≤ c :=
  maxOver_le (u := fun z => |f z|) h

/-- `σ_* := max_x E(σ ∣ X₀ = x)` (`proofs.tex:837`). It reads only the graph, the policy entering
through `u`; see `BackwardPolicy.IsHitExp`. -/
noncomputable def sigmaStar (G : MarkedGraph V) (u : V → ℝ) : ℝ := maxOver G u

theorem le_sigmaStar (u : V → ℝ) (x : V) : u x ≤ sigmaStar G u := le_maxOver u x

/-! ### `L²(λ)` on a finite state space

`λ` is a probability on `𝒱`, so the inner product is the weighted sum and `Π` is the mean
(`proofs.tex:22`: `Π f = (∫ f dρ / ρ(𝒮))·1`). No `MeasureTheory` or `InnerProductSpace` layer is
introduced; see the module SCOPE. -/

/-- `⟪a ∣ b⟫_{L²(λ)} = ∫ a b dλ`. -/
def ipL2 (lam a b : V → ℝ) : ℝ := ∑ x, lam x * (a x * b x)

/-- `‖a‖_{L²(λ)}`. -/
noncomputable def nrmL2 (lam a : V → ℝ) : ℝ := Real.sqrt (ipL2 lam a a)

/-- `Π a`, the mean of `a` against `λ` — a scalar, `Π` being the mean projection onto the
constants (`proofs.tex:22`). -/
def meanL2 (lam a : V → ℝ) : ℝ := ∑ x, lam x * a x

theorem ipL2_self_nonneg {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a : V → ℝ) :
    0 ≤ ipL2 lam a a :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hnn x) (mul_self_nonneg (a x))

theorem nrmL2_nonneg (lam a : V → ℝ) : 0 ≤ nrmL2 lam a := Real.sqrt_nonneg _

theorem sq_nrmL2 {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a : V → ℝ) :
    nrmL2 lam a ^ 2 = ipL2 lam a a :=
  Real.sq_sqrt (ipL2_self_nonneg hnn a)

/-- **Cauchy–Schwarz in `L²(λ)`.** -/
theorem ipL2_le_mul_nrmL2 {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a b : V → ℝ) :
    ipL2 lam a b ≤ nrmL2 lam a * nrmL2 lam b := by
  have hcs : ipL2 lam a b ^ 2 ≤ ipL2 lam a a * ipL2 lam b b := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun x _ => mul_nonneg (hnn x) (mul_self_nonneg (a x)))
      (fun x _ => mul_nonneg (hnn x) (mul_self_nonneg (b x))) (fun x _ => ?_)
    nlinarith [hnn x, sq_nonneg (a x * b x), sq_nonneg (lam x)]
  calc ipL2 lam a b ≤ |ipL2 lam a b| := le_abs_self _
    _ = Real.sqrt (ipL2 lam a b ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (ipL2 lam a a * ipL2 lam b b) := Real.sqrt_le_sqrt hcs
    _ = nrmL2 lam a * nrmL2 lam b := Real.sqrt_mul (ipL2_self_nonneg hnn a) _

/-- `‖a‖_{L²(λ)} ≤ ‖a‖_{L^∞}` when `λ` is a probability. -/
theorem nrmL2_le_supAbs {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (htot : ∑ x, lam x = 1)
    (a : V → ℝ) : nrmL2 lam a ≤ supAbs G a := by
  have hb : ipL2 lam a a ≤ supAbs G a ^ 2 := by
    calc ipL2 lam a a ≤ ∑ x, lam x * supAbs G a ^ 2 := by
          refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hnn x)
          have h1 : |a x| ≤ supAbs G a := le_supAbs (G := G) a x
          nlinarith [abs_nonneg (a x), sq_abs (a x), supAbs_nonneg (G := G) a]
      _ = supAbs G a ^ 2 := by rw [← Finset.sum_mul, htot, one_mul]
  calc nrmL2 lam a ≤ Real.sqrt (supAbs G a ^ 2) := Real.sqrt_le_sqrt hb
    _ = supAbs G a := Real.sqrt_sq (supAbs_nonneg (G := G) a)

/-- `√λ_min · |a(x)| ≤ ‖a‖_{L²(λ)}`, i.e. `‖a‖_{L^∞} ≤ ‖a‖_{L²(λ)}/√λ_min` — the paper's
`C_∞ = (min λ)^{-1/2}` (`proofs.tex:613`). -/
theorem sqrt_minOver_mul_abs_le_nrmL2 {lam : V → ℝ} (hnn : ∀ x, 0 ≤ lam x) (a : V → ℝ) (x : V) :
    Real.sqrt (minOver G lam) * |a x| ≤ nrmL2 lam a := by
  have hmin : 0 ≤ minOver G lam := le_minOver hnn
  have hterm : minOver G lam * (a x * a x) ≤ ipL2 lam a a := by
    refine le_trans (mul_le_mul_of_nonneg_right (minOver_le lam x) (mul_self_nonneg (a x))) ?_
    exact Finset.single_le_sum (f := fun z => lam z * (a z * a z))
      (fun z _ => mul_nonneg (hnn z) (mul_self_nonneg (a z))) (Finset.mem_univ x)
  calc Real.sqrt (minOver G lam) * |a x|
      = Real.sqrt (minOver G lam * (a x * a x)) := by
        rw [Real.sqrt_mul hmin, ← Real.sqrt_mul_self_eq_abs]
    _ ≤ nrmL2 lam a := Real.sqrt_le_sqrt hterm

variable [DecidableEq V]

/-- **`N`**, the paper's visit counts (`proofs.tex:840`): the occupation measure `g` of the
backward chain killed at `s₀` — see `BackwardPolicy.IsGreen` — plus the one visit each to `s₀`
and `s_f` that the convention `N(s₀) = N(s_f) = 1` records.

It reads only the graph, the policy entering through `g`. -/
def visits (G : MarkedGraph V) (g : V → ℝ) : V → ℝ :=
  fun y => g y + (if y = G.src then 1 else 0) + (if y = G.snk then 1 else 0)

namespace BackwardPolicy

variable (B : BackwardPolicy G)

/-! ### The function action `Q` of the backward chain

`proofs.tex:861` — "Let `Q` be the function action of the backward chain, the `L²(λ)`-adjoint of
`P`". -/

/-- The **function action** `Q` of the backward chain: `(Qu)(x) = ∑_y π̂_←(x→y) u(y)`. -/
noncomputable def qact (u : V → ℝ) : V → ℝ := fun x => ∑ y, B.phat x y * u y

variable {B}

theorem qact_apply (u : V → ℝ) (x : V) : B.qact u x = ∑ y, B.phat x y * u y := rfl

theorem qact_const (c : ℝ) (x : V) : B.qact (fun _ => c) x = c := by
  rw [qact_apply, ← Finset.sum_mul, B.phat_row_sum, one_mul]

theorem qact_sub (u u' : V → ℝ) (x : V) :
    B.qact (fun z => u z - u' z) x = B.qact u x - B.qact u' x := by
  simp only [qact_apply, mul_sub, Finset.sum_sub_distrib]

theorem qact_neg (u : V → ℝ) (x : V) : B.qact (fun z => -u z) x = -B.qact u x := by
  simp only [qact_apply, mul_neg, Finset.sum_neg_distrib]

theorem qact_smul (c : ℝ) (u : V → ℝ) (x : V) :
    B.qact (fun z => c * u z) x = c * B.qact u x := by
  simp only [qact_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem qact_le {u : V → ℝ} {c : ℝ} (h : ∀ y, u y ≤ c) (x : V) : B.qact u x ≤ c := by
  calc B.qact u x ≤ ∑ y, B.phat x y * c :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (B.phat_nonneg x y)
    _ = c := qact_const c x

theorem le_qact {u : V → ℝ} {c : ℝ} (h : ∀ y, c ≤ u y) (x : V) : c ≤ B.qact u x := by
  calc c = ∑ y, B.phat x y * c := (qact_const c x).symm
    _ ≤ B.qact u x :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (B.phat_nonneg x y)

/-! ### The minimum principle at the regeneration state

The one analytic ingredient of the whole file. `proofs.tex:865` uses it twice implicitly —
"since the chain is irreducible on a finite space, `h − u` is `Q`-harmonic, hence constant", and
the `‖u‖_∞ ≤ σ_*‖f‖_∞` bound — and both are maximum principles walked down to `s₀` along the
irreducibility of `theo:universality_graphs`*(1)*. -/

/-- A minimizer of `φ` at which `φ` is superharmonic passes its value to every state the backward
chain can step to. -/
theorem eq_of_bstep_of_min {φ : V → ℝ} {m : ℝ} (hm : ∀ z, m ≤ φ z) {x : V}
    (hx : φ x = m) (hs : B.qact φ x ≤ φ x) {y : V} (hxy : B.BStep x y) : φ y = m := by
  have hxy' : (0 : ℝ) < B.phat x y := hxy
  have heq : B.qact φ x = m := le_antisymm (hx ▸ hs) (le_qact hm x)
  have hzero : ∑ z, B.phat x z * (φ z - m) = 0 := by
    have hsplit : ∑ z, B.phat x z * (φ z - m) = B.qact φ x - m := by
      simp only [mul_sub, qact_apply]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, B.phat_row_sum, one_mul]
    rw [hsplit, heq, sub_self]
  have hnn : ∀ z ∈ (Finset.univ : Finset V), 0 ≤ B.phat x z * (φ z - m) := fun z _ =>
    mul_nonneg (B.phat_nonneg x z) (sub_nonneg.mpr (hm z))
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero y (Finset.mem_univ y)
  rcases mul_eq_zero.mp hterm with h | h
  · exact absurd h (ne_of_gt hxy')
  · linarith

/-- The minimizing set propagates along walks of the backward chain, as long as `φ` is
superharmonic at each state it passes. -/
theorem eq_of_breach_of_min {φ : V → ℝ} {m : ℝ} (hm : ∀ z, m ≤ φ z)
    (hoff : ∀ z, φ z = m → B.qact φ z ≤ φ z) {x y : V} (hx : φ x = m) (hr : B.BReach x y) :
    φ y = m := by
  induction hr with
  | refl => exact hx
  | tail _ hstep ih => exact eq_of_bstep_of_min hm ih (hoff _ ih) hstep

/-- **The minimum principle at `s₀`.** A function vanishing at the regeneration state and
superharmonic for the backward chain off it is non-negative. Irreducibility is what walks a
negative minimum down to `s₀`. -/
theorem nonneg_of_superharm_off_src (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {φ : V → ℝ} (h0 : φ G.src = 0) (hs : ∀ x, x ≠ G.src → B.qact φ x ≤ φ x) (x : V) :
    0 ≤ φ x := by
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V) φ ⟨G.src, Finset.mem_univ _⟩
  set m : ℝ := φ x0 with hmdef
  have hm : ∀ z, m ≤ φ z := fun z => hx0 z (Finset.mem_univ z)
  have hmle : m ≤ 0 := by have := hm G.src; rwa [h0] at this
  rcases eq_or_lt_of_le hmle with h | h
  · linarith [hm x]
  · exfalso
    have hoff : ∀ z, φ z = m → B.qact φ z ≤ φ z := by
      intro z hz
      refine hs z ?_
      rintro rfl
      rw [h0] at hz
      linarith
    have hsrc := eq_of_breach_of_min hm hoff hmdef.symm (B.breach_all hpc hpos x0 G.src)
    rw [h0] at hsrc
    linarith

/-! ### The Poisson system at `s₀`, and its unique solution -/

variable (B)

/-- **The Poisson system at the regeneration state.** `u(s₀) = 0` and `u = f + Qu` off `s₀`.

This is the linear characterization of `u(x) = E(∑_{n<σ(x)} f(X_n) ∣ X₀ = x)` of
`proofs.tex:863`, obtained there by conditioning on the first step. The identification with that
expectation is not formalized; see the module SCOPE. -/
def IsPoisson (f u : V → ℝ) : Prop :=
  u G.src = 0 ∧ ∀ x, x ≠ G.src → u x = f x + B.qact u x

variable {B}

/-- A function vanishing at `s₀` and `Q`-harmonic off `s₀` vanishes identically: the minimum
principle applied to `d` and to `−d`. -/
theorem eq_zero_of_harm_off_src (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {d : V → ℝ} (h0 : d G.src = 0) (hh : ∀ x, x ≠ G.src → d x = B.qact d x) : d = 0 := by
  have hup : ∀ x, 0 ≤ d x :=
    nonneg_of_superharm_off_src hpc hpos h0 fun x hx => le_of_eq (hh x hx).symm
  have hdn : ∀ x, 0 ≤ -d x := by
    refine nonneg_of_superharm_off_src hpc hpos (by rw [h0]; ring) fun x hx => ?_
    rw [qact_neg]
    exact le_of_eq (by rw [← hh x hx])
  funext x
  have h1 := hup x
  have h2 := hdn x
  simp only [Pi.zero_apply]
  linarith

/-- **The Poisson system has at most one solution.** -/
theorem IsPoisson.unique (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {f u u' : V → ℝ}
    (h : B.IsPoisson f u) (h' : B.IsPoisson f u') : u = u' := by
  have hd : (fun x => u x - u' x) = 0 := by
    refine eq_zero_of_harm_off_src hpc hpos (by rw [h.1, h'.1]; ring) fun x hx => ?_
    rw [qact_sub, ← sub_eq_of_eq_add' (h.2 x hx), ← sub_eq_of_eq_add' (h'.2 x hx)]
    ring
  funext x
  have := congrFun hd x
  simp only [Pi.zero_apply] at this
  linarith

variable (B)

/-- The linear map whose kernel is the homogeneous Poisson system: `u ↦ u(s₀)` at `s₀` and
`u ↦ u − Qu` elsewhere. Its injectivity is the minimum principle, and in finite dimension
injectivity is surjectivity — the route `GFNBounds/Graph/Setting.lean`'s `exists_fixed` takes. -/
noncomputable def poissonMap : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun u := fun x => if x = G.src then u G.src else u x - B.qact u x
  map_add' u u' := by
    funext x
    by_cases hx : x = G.src
    · simp [hx]
    · simp only [if_neg hx, Pi.add_apply, qact_apply, mul_add, Finset.sum_add_distrib]
      ring
  map_smul' c u := by
    funext x
    by_cases hx : x = G.src
    · simp [hx]
    · simp only [if_neg hx, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, qact_apply]
      rw [show (∑ y, B.phat x y * (c * u y)) = c * ∑ y, B.phat x y * u y from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring]
      ring

variable {B}

theorem poissonMap_apply (u : V → ℝ) (x : V) :
    B.poissonMap u x = if x = G.src then u G.src else u x - B.qact u x := rfl

/-- **The Poisson system is solvable, for every source term.** -/
theorem exists_isPoisson (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) (f : V → ℝ) :
    ∃ u, B.IsPoisson f u := by
  have hinj : Function.Injective B.poissonMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    refine eq_zero_of_harm_off_src hpc hpos ?_ ?_
    · have := congrFun hd G.src
      rwa [poissonMap_apply, if_pos rfl] at this
    · intro x hx
      have := congrFun hd x
      rw [poissonMap_apply, if_neg hx] at this
      simp only [Pi.zero_apply] at this
      linarith
  obtain ⟨u, hu⟩ :=
    LinearMap.injective_iff_surjective.mp hinj (fun x => if x = G.src then 0 else f x)
  refine ⟨u, ?_, ?_⟩
  · have := congrFun hu G.src
    rwa [poissonMap_apply, if_pos rfl, if_pos rfl] at this
  · intro x hx
    have := congrFun hu x
    rw [poissonMap_apply, if_neg hx, if_neg hx] at this
    linarith

variable (B)

/-! ### `σ`: the hitting time of `s₀`, characterized

`proofs.tex:835` — "`σ(x)` the hitting time of `s₀` by the backward chain started at `x`". -/

/-- **`E(σ ∣ X₀ = ·)`, characterized**: the Poisson system with unit source. -/
def IsHitExp (u : V → ℝ) : Prop := B.IsPoisson (fun _ => 1) u

variable {B}

theorem exists_isHitExp (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) :
    ∃ u, B.IsHitExp u := exists_isPoisson hpc hpos _

theorem IsHitExp.unique (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {u u' : V → ℝ}
    (h : B.IsHitExp u) (h' : B.IsHitExp u') : u = u' := IsPoisson.unique hpc hpos h h'

/-- `E(σ ∣ X₀ = x) ≥ 0`: the minimum of `u` can only be at `s₀`, since anywhere else `u` exceeds
its own average by `1`. Irreducibility is *not* needed here. -/
theorem IsHitExp.nonneg {u : V → ℝ} (hu : B.IsHitExp u) (x : V) : 0 ≤ u x := by
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V) u ⟨G.src, Finset.mem_univ _⟩
  by_cases h : x0 = G.src
  · have h1 := hx0 x (Finset.mem_univ x)
    rw [h, hu.1] at h1
    exact h1
  · exfalso
    have h1 := hu.2 x0 h
    have h2 : u x0 ≤ B.qact u x0 := le_qact (fun z => hx0 z (Finset.mem_univ z)) x0
    linarith

variable (B)

/-- `σ̄ := E_{x ∼ π̂_←(s_f→·)} E(σ ∣ X₀ = x)`, the expected backward-trajectory length of Morozov
et al. (`proofs.tex:838`). The target row is `π̂_←(s_f→·)`, so the average against it is `Q` read
at `s_f`. -/
noncomputable def sigmaBar (u : V → ℝ) : ℝ := B.qact u G.snk

variable {B}

theorem sigmaStar_nonneg {u : V → ℝ} (hu : B.IsHitExp u) : 0 ≤ sigmaStar G u :=
  le_trans (hu.nonneg G.src) (le_maxOver u G.src)

theorem sigmaBar_nonneg {u : V → ℝ} (hu : B.IsHitExp u) : 0 ≤ B.sigmaBar u :=
  le_qact (fun y => hu.nonneg y) G.snk

/-! ### The target row, and the two edges the marks force -/

/-- The only backward transition into `s_f` is from `s₀`: `s_f` has no outgoing edge in `G`. -/
theorem phat_snk_eq_zero_of_ne {x : V} (hx : x ≠ G.src) : B.phat x G.snk = 0 := by
  rw [B.phat_of_ne_src hx]
  by_contra hc
  exact G.no_edge_out_of_snk x (B.supp hx hc)

/-- `π̂_←(s₀→s₀) = 0`, the source row being the point mass at `s_f`. -/
theorem phat_src_src : B.phat G.src G.src = 0 := B.phat_src_of_ne G.src_ne_snk

/-! ### `N`: the visit counts, characterized

`proofs.tex:840` — "`N(x)` the expected number of visits to `x` of one backward trajectory drawn
from the target row `π̂_←(s_f→·)`, with the convention `N(s₀) = N(s_f) = 1`". The trajectory is
the chain killed at `s₀`, so its occupation measure `g` solves the renewal equation
`g = π̂_←(s_f→·) + g P̂` off `s₀`, with `g(s₀) = 0`; and `N = g + 1_{s₀} + 1_{s_f}` adds the two
states of the excursion the paper counts by convention. -/

variable (B)

/-- **The occupation measure of the backward chain killed at `s₀`, characterized**: the renewal
equation with the target row as source. -/
def IsGreen (g : V → ℝ) : Prop :=
  g G.src = 0 ∧ ∀ y, y ≠ G.src → g y = B.phat G.snk y + B.densMap g y

variable {B}

/-- **`prop:morozov_rate`*(1)*, one-dimensionality.** An invariant signed measure of the backward
chain is a multiple of `λ`: the ratio maximum principle of `theo:universality_graphs`*(1)*, with
`eq_zero_of_breach` reused verbatim. -/
theorem eq_smul_lam_of_invariant (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam e : V → ℝ} (hl : B.IsInvProb lam) (he : ∀ y, ∑ x, e x * B.phat x y = e y) (x : V) :
    e x = (∑ z, e z) * lam x := by
  classical
  have hp : ∀ z, 0 < lam z := fun z => hl.pos hpc hpos z
  obtain ⟨x0, -, hx0min⟩ := Finset.exists_min_image (Finset.univ : Finset V)
    (fun z => e z / lam z) ⟨G.src, Finset.mem_univ _⟩
  set t : ℝ := e x0 / lam x0 with ht
  have hnn : ∀ z, 0 ≤ e z - t * lam z := by
    intro z
    have hz : t ≤ e z / lam z := hx0min z (Finset.mem_univ z)
    have := (le_div_iff₀ (hp z)).mp hz
    linarith
  have h0 : e x0 - t * lam x0 = 0 := by
    rw [ht, div_mul_cancel₀ _ (ne_of_gt (hp x0)), sub_self]
  have hinv : ∀ y, ∑ z, (e z - t * lam z) * B.phat z y = e y - t * lam y := by
    intro y
    have hrw : ∀ z : V, (e z - t * lam z) * B.phat z y
        = e z * B.phat z y - t * (lam z * B.phat z y) := fun z => by ring
    rw [Finset.sum_congr rfl (fun z _ => hrw z), Finset.sum_sub_distrib, ← Finset.mul_sum,
      he y, hl.inv y]
  have hall : ∀ z, e z - t * lam z = 0 := fun z =>
    eq_zero_of_breach hnn hinv h0 (B.breach_all hpc hpos z x0)
  have hsum : ∑ z, e z = t := by
    have h1 : ∑ z, e z = ∑ z, t * lam z :=
      Finset.sum_congr rfl fun z _ => by have := hall z; linarith
    rwa [← Finset.mul_sum, hl.total, mul_one] at h1
  have := hall x
  rw [hsum]
  linarith

/-- **The flux identity.** `(g P̂)(s₀) + π̂_←(s_f→s₀) = 1`: the killed chain reaches `s₀` with
total mass one. Purely algebraic — the rows of `π̂_←` sum to `1`, and `g P̂` has the same total
mass as `g`. -/
theorem IsGreen.flux {g : V → ℝ} (hg : B.IsGreen g) :
    B.densMap g G.src + B.phat G.snk G.src = 1 := by
  have hsum : ∑ y, (g y - B.phat G.snk y - B.densMap g y) = -1 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, B.phat_row_sum, B.sum_densMap]
    ring
  have hsingle : ∑ y, (g y - B.phat G.snk y - B.densMap g y)
      = g G.src - B.phat G.snk G.src - B.densMap g G.src := by
    refine Finset.sum_eq_single G.src (fun b _ hb => ?_)
      (fun hn => absurd (Finset.mem_univ G.src) hn)
    rw [hg.2 b hb]; ring
  rw [hsingle, hg.1] at hsum
  linarith

/-- The killed occupation measure does not charge `s_f`: nothing but `s₀` steps into `s_f`, and
`g(s₀) = 0`. -/
theorem IsGreen.snk {g : V → ℝ} (hg : B.IsGreen g) : g G.snk = 0 := by
  have hd : B.densMap g G.snk = 0 := by
    rw [densMap_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x = G.src
    · rw [hx, hg.1, zero_mul]
    · rw [phat_snk_eq_zero_of_ne hx, mul_zero]
  rw [hg.2 G.snk (Ne.symm G.src_ne_snk), hd, phat_snk_eq_zero_of_ne (Ne.symm G.src_ne_snk)]
  ring

theorem IsGreen.unique (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam g g' : V → ℝ}
    (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hg' : B.IsGreen g') : g = g' := by
  set e : V → ℝ := fun y => g y - g' y with he
  have hsrc : e G.src = 0 := by simp only [he, hg.1, hg'.1, sub_self]
  have hoff : ∀ y, y ≠ G.src → B.densMap e y = e y := by
    intro y hy
    have hlin : B.densMap e y = B.densMap g y - B.densMap g' y := by
      simp only [densMap_apply, he, sub_mul, Finset.sum_sub_distrib]
    rw [hlin, he]
    simp only
    rw [hg.2 y hy, hg'.2 y hy]
    ring
  -- the equation at `s₀` follows by conservation of total mass
  have hall : ∀ y, B.densMap e y = e y := by
    have h1 : ∑ y, (B.densMap e y - e y) = 0 := by
      rw [Finset.sum_sub_distrib, B.sum_densMap, sub_self]
    have h2 : ∑ y, (B.densMap e y - e y) = B.densMap e G.src - e G.src :=
      Finset.sum_eq_single G.src (fun b _ hb => by rw [hoff b hb]; ring)
        (fun hn => absurd (Finset.mem_univ G.src) hn)
    intro y
    by_cases hy : y = G.src
    · subst hy; rw [h2] at h1; linarith
    · exact hoff y hy
  have hsmul := eq_smul_lam_of_invariant hpc hpos hl
    (fun y => by rw [← densMap_apply]; exact hall y)
  have hzero : ∑ z, e z = 0 := by
    have := hsmul G.src
    rw [hsrc] at this
    have hp : 0 < lam G.src := hl.pos hpc hpos G.src
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt hp)
  funext y
  have := hsmul y
  rw [hzero, zero_mul] at this
  simp only [he] at this
  linarith

variable (B)

/-- The linear map whose kernel is the homogeneous renewal system. -/
noncomputable def greenMap : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun e := fun y => if y = G.src then e G.src else e y - B.densMap e y
  map_add' e e' := by
    funext y
    by_cases hy : y = G.src
    · simp [hy]
    · simp only [if_neg hy, Pi.add_apply, map_add]
      ring
  map_smul' c e := by
    funext y
    by_cases hy : y = G.src
    · simp [hy]
    · simp only [if_neg hy, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_smul]
      ring

variable {B}

theorem greenMap_apply (e : V → ℝ) (y : V) :
    B.greenMap e y = if y = G.src then e G.src else e y - B.densMap e y := rfl

/-- **The renewal system is solvable**: `N` exists. -/
theorem exists_isGreen (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam : V → ℝ}
    (hl : B.IsInvProb lam) : ∃ g, B.IsGreen g := by
  have hinj : Function.Injective B.greenMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e hd
    have hsrc : e G.src = 0 := by
      have := congrFun hd G.src
      rwa [greenMap_apply, if_pos rfl] at this
    have hoff : ∀ y, y ≠ G.src → B.densMap e y = e y := by
      intro y hy
      have := congrFun hd y
      rw [greenMap_apply, if_neg hy] at this
      simp only [Pi.zero_apply] at this
      linarith
    have hall : ∀ y, B.densMap e y = e y := by
      have h1 : ∑ y, (B.densMap e y - e y) = 0 := by
        rw [Finset.sum_sub_distrib, B.sum_densMap, sub_self]
      have h2 : ∑ y, (B.densMap e y - e y) = B.densMap e G.src - e G.src :=
        Finset.sum_eq_single G.src (fun b _ hb => by rw [hoff b hb]; ring)
          (fun hn => absurd (Finset.mem_univ G.src) hn)
      intro y
      by_cases hy : y = G.src
      · subst hy; rw [h2] at h1; linarith
      · exact hoff y hy
    have hsmul := eq_smul_lam_of_invariant hpc hpos hl
      (fun y => by rw [← densMap_apply]; exact hall y)
    have hzero : ∑ z, e z = 0 := by
      have h3 := hsmul G.src
      rw [hsrc] at h3
      have hp : 0 < lam G.src := hl.pos hpc hpos G.src
      rcases mul_eq_zero.mp h3.symm with h | h
      · exact h
      · exact absurd h (ne_of_gt hp)
    funext y
    have := hsmul y
    rw [hzero, zero_mul] at this
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.injective_iff_surjective.mp hinj
    (fun y => if y = G.src then 0 else B.phat G.snk y)
  refine ⟨g, ?_, ?_⟩
  · have := congrFun hg G.src
    rwa [greenMap_apply, if_pos rfl, if_pos rfl] at this
  · intro y hy
    have := congrFun hg y
    rw [greenMap_apply, if_neg hy, if_neg hy] at this
    linarith

/-! ### Item (1) -/

/-- **`prop:morozov_rate`*(1)*, `N(s₀) = 1`** — the paper's convention, here a consequence of
`g(s₀) = 0`. -/
theorem IsGreen.visits_src {g : V → ℝ} (hg : B.IsGreen g) : visits G g G.src = 1 := by
  simp [visits, hg.1, G.src_ne_snk]

/-- **`prop:morozov_rate`*(1)*, `N(s_f) = 1`** — likewise, from `g(s_f) = 0`. -/
theorem IsGreen.visits_snk {g : V → ℝ} (hg : B.IsGreen g) : visits G g G.snk = 1 := by
  simp [visits, hg.snk, Ne.symm G.src_ne_snk]

/-- **`N` is `P̂`-invariant.** The renewal equation off `s₀` plus the flux identity at `s₀`; the
two indicator terms carry the wrap `s₀ → s_f` and the target row out of `s_f`. -/
theorem IsGreen.visits_invariant {g : V → ℝ} (hg : B.IsGreen g) (y : V) :
    ∑ x, visits G g x * B.phat x y = visits G g y := by
  have hsplit : ∑ x, visits G g x * B.phat x y
      = B.densMap g y + B.phat G.src y + B.phat G.snk y := by
    have hexp : ∀ x : V, visits G g x * B.phat x y
        = g x * B.phat x y + (if x = G.src then B.phat x y else 0)
          + (if x = G.snk then B.phat x y else 0) := by
      intro x
      by_cases h1 : x = G.src <;> by_cases h2 : x = G.snk <;>
        simp [visits, h1, h2, add_mul]
    rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.univ : Finset V) G.src (fun x => B.phat x y),
      Finset.sum_ite_eq' (Finset.univ : Finset V) G.snk (fun x => B.phat x y),
      if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ← densMap_apply]
  rw [hsplit]
  by_cases hy : y = G.src
  · subst hy
    rw [phat_src_src, hg.visits_src]
    have := hg.flux
    linarith
  · simp only [visits, if_neg hy]
    rw [hg.2 y hy]
    by_cases hy2 : y = G.snk
    · subst hy2
      rw [if_pos rfl, B.phat_src_snk]
      ring
    · rw [if_neg hy2, B.phat_src_of_ne hy2]
      ring

/-- **The duality identity.** `∑_x g(x) = σ̄`: pairing the renewal system for `g` against the
hitting system for `u` collapses to the total mass on one side and the target-row average on the
other. This is the algebraic content of `∑_{n<σ} 1 = σ`. -/
theorem IsGreen.sum_eq_sigmaBar {g u : V → ℝ} (hg : B.IsGreen g) (hu : B.IsHitExp u) :
    ∑ x, g x = B.sigmaBar u := by
  set A : ℝ := ∑ x, g x * u x with hA
  -- expand `A` through the renewal equation
  have h1 : A = B.sigmaBar u + ∑ x, g x * B.qact u x := by
    have hpt : ∀ y : V, g y * u y = B.phat G.snk y * u y + B.densMap g y * u y := by
      intro y
      by_cases hy : y = G.src
      · subst hy; rw [hg.1, hu.1]; ring
      · rw [hg.2 y hy]; ring
    have hswap : ∑ y, B.densMap g y * u y = ∑ x, g x * B.qact u x := by
      simp only [densMap_apply, qact_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [hA, Finset.sum_congr rfl (fun y _ => hpt y), Finset.sum_add_distrib, hswap, sigmaBar,
      qact_apply]
  -- expand the same sum through the hitting system
  have h2 : ∑ x, g x * B.qact u x = A - ∑ x, g x := by
    have hpt : ∀ x : V, g x * B.qact u x = g x * u x - g x := by
      intro x
      by_cases hx : x = G.src
      · subst hx; rw [hg.1]; ring
      · have hstep : u x = 1 + B.qact u x := hu.2 x hx
        rw [hstep]; ring
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, ← hA]
  rw [h2] at h1
  linarith

/-- `∑_x N(x) = 2 + σ̄`: the expected length of one excursion from `s₀`, which is what Kac's
formula divides by. -/
theorem IsGreen.sum_visits {g u : V → ℝ} (hg : B.IsGreen g) (hu : B.IsHitExp u) :
    ∑ x, visits G g x = 2 + B.sigmaBar u := by
  have hexp : ∑ x, visits G g x
      = (∑ x, g x) + (∑ x : V, if x = G.src then (1 : ℝ) else 0)
        + ∑ x : V, if x = G.snk then (1 : ℝ) else 0 := by
    simp only [visits]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hexp, Finset.sum_ite_eq' (Finset.univ : Finset V) G.src (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' (Finset.univ : Finset V) G.snk (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), hg.sum_eq_sigmaBar hu]
  ring

theorem two_add_sigmaBar_pos {u : V → ℝ} (hu : B.IsHitExp u) : 0 < 2 + B.sigmaBar u := by
  have := sigmaBar_nonneg hu
  linarith

/-- **`prop:morozov_rate`*(1)***: `λ(x) = N(x)/(2 + σ̄)` for every `x`.

`N` is `P̂`-invariant with total mass `2 + σ̄`, and an invariant signed measure of an irreducible
chain is a multiple of `λ`. This is Kac's formula on a general finite marked graph, the
`GFNBounds/Doubling/Kac.lean` argument with the visit counts kept rather than only `λ(s₀)`. -/
theorem lam_eq_visits_div (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam g u : V → ℝ}
    (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hu : B.IsHitExp u) (x : V) :
    lam x = visits G g x / (2 + B.sigmaBar u) := by
  have hsmul := eq_smul_lam_of_invariant hpc hpos hl (hg.visits_invariant) x
  rw [hg.sum_visits hu] at hsmul
  rw [hsmul, mul_comm, mul_div_assoc, div_self (ne_of_gt (two_add_sigmaBar_pos hu)), mul_one]

/-- **`prop:morozov_rate`*(1)*, at the source**: `λ(s₀) = 1/(2+σ̄)`. -/
theorem lam_src_eq (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam g u : V → ℝ}
    (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hu : B.IsHitExp u) :
    lam G.src = 1 / (2 + B.sigmaBar u) := by
  rw [lam_eq_visits_div hpc hpos hl hg hu G.src, hg.visits_src]

/-- **`prop:morozov_rate`*(1)*, at the sink**: `λ(s_f) = 1/(2+σ̄)`. -/
theorem lam_snk_eq (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam g u : V → ℝ}
    (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hu : B.IsHitExp u) :
    lam G.snk = 1 / (2 + B.sigmaBar u) := by
  rw [lam_eq_visits_div hpc hpos hl hg hu G.snk, hg.visits_snk]

/-- **`min_x N(x) > 0`**, which is what makes `B̂_σ` a finite constant: `N = (2+σ̄)λ` and `λ > 0`.
-/
theorem IsGreen.visits_pos (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam g u : V → ℝ}
    (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hu : B.IsHitExp u) (x : V) :
    0 < visits G g x := by
  have hsb : 0 < 2 + B.sigmaBar u := two_add_sigmaBar_pos hu
  have hx : (2 + B.sigmaBar u) * lam x = visits G g x := by
    rw [lam_eq_visits_div hpc hpos hl hg hu x, mul_div_cancel₀ _ (ne_of_gt hsb)]
  rw [← hx]
  exact mul_pos hsb (hl.pos hpc hpos x)

/-! ### The density action `P`, and its adjointness to `Q` -/

variable (B)

/-- The **density action** `P` of the backward chain, read on `L²(λ)` densities
(`proofs.tex:22`, `proofs.tex:407`): `(Pa)(y) = (∑_x λ(x) π̂_←(x→y) a(x))/λ(y)`, which is the
function action of the `λ`-reversal. -/
noncomputable def pdens (lam a : V → ℝ) : V → ℝ :=
  fun y => (∑ x, lam x * B.phat x y * a x) / lam y

variable {B}

/-- **`P` and `Q` are `L²(λ)`-adjoint** (`proofs.tex:861`), by a swap of two finite sums. -/
theorem ipL2_pdens_qact {lam : V → ℝ} (hp : ∀ x, 0 < lam x) (a b : V → ℝ) :
    ipL2 lam (B.pdens lam a) b = ipL2 lam a (B.qact b) := by
  have hleft : ipL2 lam (B.pdens lam a) b = ∑ y, ∑ x, lam x * B.phat x y * a x * b y := by
    simp only [ipL2, pdens]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [div_mul_eq_mul_div, mul_div_assoc', mul_comm (lam y), mul_div_assoc,
      div_self (ne_of_gt (hp y)), mul_one, Finset.sum_mul]
  have hright : ipL2 lam a (B.qact b) = ∑ x, ∑ y, lam x * B.phat x y * a x * b y := by
    simp only [ipL2, qact_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hleft, hright, Finset.sum_comm]

/-- `P` fixes the constants: `λ` is invariant. -/
theorem pdens_const {lam : V → ℝ} (hl : B.IsInvProb lam) (hp : ∀ x, 0 < lam x) (c : ℝ) (y : V) :
    B.pdens lam (fun _ => c) y = c := by
  have h : ∑ x, lam x * B.phat x y * c = lam y * c := by
    rw [← Finset.sum_mul, hl.inv y]
  rw [pdens, h, mul_comm, mul_div_assoc, div_self (ne_of_gt (hp y)), mul_one]

theorem pdens_sub (lam a a' : V → ℝ) (y : V) :
    B.pdens lam (fun z => a z - a' z) y = B.pdens lam a y - B.pdens lam a' y := by
  simp only [pdens, ← sub_div, mul_sub, Finset.sum_sub_distrib]

/-! ### Item (2) -/

/-- **The Poisson solution is closed at `s₀` too** when the source is mean-zero
(`proofs.tex:865`): the paper gets it from the occupation identity of item *(1)*, here it is
invariance of `λ` tested against `u − Qu`. -/
theorem IsPoisson.at_src {lam f w : V → ℝ} (hl : B.IsInvProb lam) (hp : ∀ x, 0 < lam x)
    (hw : B.IsPoisson f w) (hf : meanL2 lam f = 0) :
    ∀ x, w x - B.qact w x = f x := by
  have hQ : meanL2 lam (B.qact w) = meanL2 lam w := by
    have hswap : ∑ x, lam x * B.qact w x = ∑ y, (∑ x, lam x * B.phat x y) * w y := by
      simp only [qact_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
    simp only [meanL2]
    rw [hswap]
    exact Finset.sum_congr rfl fun y _ => by rw [hl.inv y]
  have hzero : ∑ x, lam x * (w x - B.qact w x - f x) = 0 := by
    have hexp : ∀ x : V, lam x * (w x - B.qact w x - f x)
        = lam x * w x - lam x * B.qact w x - lam x * f x := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ x, lam x * B.qact w x = ∑ x, lam x * w x := hQ
    have h2 : ∑ x, lam x * f x = 0 := hf
    rw [h1, h2]
    ring
  have hsingle : ∑ x, lam x * (w x - B.qact w x - f x)
      = lam G.src * (w G.src - B.qact w G.src - f G.src) := by
    refine Finset.sum_eq_single G.src (fun b _ hb => ?_)
      (fun hn => absurd (Finset.mem_univ G.src) hn)
    rw [hw.2 b hb]; ring
  rw [hsingle] at hzero
  have hsrc : w G.src - B.qact w G.src - f G.src = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (ne_of_gt (hp G.src))
    · exact h
  intro x
  by_cases hx : x = G.src
  · subst hx; linarith
  · have := hw.2 x hx; linarith

/-- **`‖u_f‖_∞ ≤ ‖f‖_∞ σ_*`, the comparison form.** `φ := c·u − w` vanishes at `s₀` and is
superharmonic off it, `c − f ≥ 0` being the slack; the minimum principle does the rest. This is
the step the paper reads probabilistically — "a sum of at most `σ_*` terms in expectation" — and
it is exactly where irreducibility enters item *(2)*. -/
theorem IsPoisson.le_smul_hitExp (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {f w u : V → ℝ} {c : ℝ} (hw : B.IsPoisson f w) (hu : B.IsHitExp u) (hc : ∀ x, f x ≤ c)
    (x : V) : w x ≤ c * u x := by
  have hsuper : ∀ z, z ≠ G.src → B.qact (fun y => c * u y - w y) z ≤ (c * u z - w z) := by
    intro z hz
    rw [qact_sub, qact_smul]
    have h1 := hu.2 z hz
    have h2 := hw.2 z hz
    have : c * u z - w z = (c - f z) + (c * B.qact u z - B.qact w z) := by
      rw [h1, h2]; ring
    have hcf : 0 ≤ c - f z := by linarith [hc z]
    linarith
  have := nonneg_of_superharm_off_src hpc hpos
    (φ := fun y => c * u y - w y) (by rw [hu.1, hw.1]; ring) hsuper x
  linarith

theorem IsPoisson.neg {f w : V → ℝ} (hw : B.IsPoisson f w) :
    B.IsPoisson (fun z => -f z) (fun z => -w z) := by
  refine ⟨by simp [hw.1], fun x hx => ?_⟩
  show -w x = -f x + B.qact (fun z => -w z) x
  rw [qact_neg, hw.2 x hx]
  ring

/-- **`‖u_f‖_∞ ≤ ‖f‖_∞ σ_*`** (`proofs.tex:868`), both signs. -/
theorem IsPoisson.abs_le_supAbs_mul_sigmaStar (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {f w u : V → ℝ} (hw : B.IsPoisson f w) (hu : B.IsHitExp u) (x : V) :
    |w x| ≤ supAbs G f * sigmaStar G u := by
  have hbound : ∀ {w' f' : V → ℝ}, B.IsPoisson f' w' → (∀ z, |f' z| ≤ supAbs G f) →
      w' x ≤ supAbs G f * sigmaStar G u := by
    intro w' f' hw' hf'
    refine le_trans (hw'.le_smul_hitExp hpc hpos hu (fun z => le_of_abs_le (hf' z)) x) ?_
    exact mul_le_mul_of_nonneg_left (le_sigmaStar u x) (supAbs_nonneg (G := G) f)
  refine abs_le.mpr ⟨?_, hbound hw fun z => le_supAbs (G := G) f z⟩
  have hneg := hbound hw.neg (fun z => by simpa using le_supAbs (G := G) f z)
  linarith

/-- **`prop:morozov_rate`*(2)*, in the `σ_*/√λ_min` form of `proofs.tex:931`**:
`‖h − Πh‖_{L²(λ)} ≤ (σ_*/√(min λ)) ‖(I−P)h‖_{L²(λ)}`.

The route is `proofs.tex:861–870` with its last step replaced: instead of transferring the bound
from `I − Q` to `I − P` through the equality of the norms of two adjoint restricted inverses,
`⟪h₀, h₀⟫ = ⟪h₀, (I−Q)w⟫ = ⟪(I−P)h₀, w⟫` uses only the pointwise adjointness `ipL2_pdens_qact`.
No aperiodicity is assumed anywhere. -/
theorem coercivity_lamMin (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam u : V → ℝ}
    (hl : B.IsInvProb lam) (hu : B.IsHitExp u) (h : V → ℝ) :
    nrmL2 lam (fun x => h x - meanL2 lam h)
      ≤ sigmaStar G u / Real.sqrt (minOver G lam)
        * nrmL2 lam (fun x => h x - B.pdens lam h x) := by
  classical
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hnn : ∀ x, 0 ≤ lam x := fun x => (hp x).le
  set m : ℝ := meanL2 lam h with hm
  set h₀ : V → ℝ := fun x => h x - m with hh₀
  have hmean : meanL2 lam h₀ = 0 := by
    simp only [meanL2, hh₀, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hl.total, one_mul, hm, meanL2, sub_self]
  obtain ⟨w, hw⟩ := exists_isPoisson hpc hpos h₀
  have hpoi : ∀ x, w x - B.qact w x = h₀ x := hw.at_src hl hp hmean
  -- `(I − P) h₀ = (I − P) h`, `P` fixing the constants
  have hIP : ∀ y, h₀ y - B.pdens lam h₀ y = h y - B.pdens lam h y := by
    intro y
    have hsub : B.pdens lam h₀ y = B.pdens lam h y - B.pdens lam (fun _ => m) y := by
      simpa [hh₀] using pdens_sub (B := B) lam h (fun _ => m) y
    rw [hsub, pdens_const hl hp m y]
    simp only [hh₀]
    ring
  -- the duality identity
  have hdual : ipL2 lam h₀ h₀ = ipL2 lam (fun y => h y - B.pdens lam h y) w := by
    have e1 : ipL2 lam h₀ h₀ = ipL2 lam h₀ w - ipL2 lam h₀ (B.qact w) := by
      simp only [ipL2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx : h₀ x = w x - B.qact w x := (hpoi x).symm
      rw [hx]; ring
    have e2 : ipL2 lam h₀ (B.qact w) = ipL2 lam (B.pdens lam h₀) w :=
      (ipL2_pdens_qact hp h₀ w).symm
    have e3 : ipL2 lam h₀ w - ipL2 lam (B.pdens lam h₀) w
        = ipL2 lam (fun y => h₀ y - B.pdens lam h₀ y) w := by
      simp only [ipL2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e1, e2, e3]
    refine Finset.sum_congr rfl fun x _ => ?_
    show lam x * ((h₀ x - B.pdens lam h₀ x) * w x)
      = lam x * ((h x - B.pdens lam h x) * w x)
    rw [hIP x]
  -- the sup bound on the Poisson solution
  have hwsup : ∀ x, |w x| ≤ supAbs G h₀ * sigmaStar G u := fun x =>
    hw.abs_le_supAbs_mul_sigmaStar hpc hpos hu x
  have hmin : 0 < minOver G lam := minOver_pos hp
  have hsq : 0 < Real.sqrt (minOver G lam) := Real.sqrt_pos.mpr hmin
  have hsupbd : supAbs G h₀ ≤ nrmL2 lam h₀ / Real.sqrt (minOver G lam) := by
    refine supAbs_le fun x => ?_
    rw [le_div_iff₀ hsq, mul_comm]
    exact sqrt_minOver_mul_abs_le_nrmL2 hnn h₀ x
  have hwnrm : nrmL2 lam w ≤ sigmaStar G u / Real.sqrt (minOver G lam) * nrmL2 lam h₀ := by
    refine le_trans (nrmL2_le_supAbs (G := G) hnn hl.total w) ?_
    refine le_trans (supAbs_le hwsup) ?_
    rw [div_mul_eq_mul_div, mul_comm (sigmaStar G u), ← div_mul_eq_mul_div]
    exact mul_le_mul_of_nonneg_right hsupbd (sigmaStar_nonneg hu)
  -- put the three together
  have hcs : ipL2 lam (fun y => h y - B.pdens lam h y) w
      ≤ nrmL2 lam (fun y => h y - B.pdens lam h y) * nrmL2 lam w :=
    ipL2_le_mul_nrmL2 hnn _ _
  have hkey : nrmL2 lam h₀ ^ 2
      ≤ nrmL2 lam (fun y => h y - B.pdens lam h y)
        * (sigmaStar G u / Real.sqrt (minOver G lam) * nrmL2 lam h₀) := by
    rw [sq_nrmL2 hnn, hdual]
    refine le_trans hcs (mul_le_mul_of_nonneg_left hwnrm (nrmL2_nonneg _ _))
  rcases eq_or_lt_of_le (nrmL2_nonneg lam h₀) with hz | hz
  · rw [← hz]
    exact mul_nonneg (div_nonneg (sigmaStar_nonneg hu) (Real.sqrt_nonneg _)) (nrmL2_nonneg _ _)
  · have hpos' : 0 < nrmL2 lam h₀ := hz
    nlinarith [hkey, hpos']

/-- **`prop:morozov_rate`*(2)***: `‖h − Πh‖_{L²(λ)} ≤ B̂_σ ‖(I−P)h‖_{L²(λ)}` with
`B̂_σ = σ_*√((2+σ̄)/min_x N(x))`.

Item *(1)* turns `λ_min` into `min N/(2+σ̄)`; the bound is then `coercivity_lamMin` with a
`√` rearranged. -/
theorem coercivity_morozov (hpc : G.PathConnected) (hpos : B.PositiveOnEdges)
    {lam g u : V → ℝ} (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hu : B.IsHitExp u)
    (h : V → ℝ) :
    nrmL2 lam (fun x => h x - meanL2 lam h)
      ≤ sigmaStar G u * Real.sqrt ((2 + B.sigmaBar u) / minOver G (visits G g))
        * nrmL2 lam (fun x => h x - B.pdens lam h x) := by
  have hp : ∀ x, 0 < lam x := fun x => hl.pos hpc hpos x
  have hmin : 0 < minOver G lam := minOver_pos hp
  have hsb : 0 < 2 + B.sigmaBar u := two_add_sigmaBar_pos hu
  have hvis : ∀ x, (2 + B.sigmaBar u) * lam x = visits G g x := fun x => by
    rw [lam_eq_visits_div hpc hpos hl hg hu x, mul_div_cancel₀ _ (ne_of_gt hsb)]
  have hNpos : 0 < minOver G (visits G g) := by
    refine minOver_pos fun x => ?_
    rw [← hvis x]
    exact mul_pos hsb (hp x)
  -- `min N ≤ (2 + σ̄) λ_min`
  have hNle : minOver G (visits G g) ≤ (2 + B.sigmaBar u) * minOver G lam := by
    obtain ⟨x0, -, hx0⟩ :=
      Finset.exists_min_image (Finset.univ : Finset V) lam ⟨G.src, Finset.mem_univ _⟩
    have heq : minOver G lam = lam x0 :=
      le_antisymm (minOver_le lam x0) (le_minOver fun z => hx0 z (Finset.mem_univ z))
    rw [heq, hvis x0]
    exact minOver_le _ x0
  -- hence `1/√λ_min ≤ √((2+σ̄)/min N)`
  have hinv : (Real.sqrt (minOver G lam))⁻¹
      ≤ Real.sqrt ((2 + B.sigmaBar u) / minOver G (visits G g)) := by
    rw [← Real.sqrt_inv]
    refine Real.sqrt_le_sqrt ?_
    rw [inv_eq_one_div, div_le_div_iff₀ hmin hNpos, one_mul]
    linarith [hNle]
  refine le_trans (coercivity_lamMin hpc hpos hl hu h) ?_
  refine mul_le_mul_of_nonneg_right ?_ (nrmL2_nonneg _ _)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hinv (sigmaStar_nonneg hu)

/-- **`prop:morozov_rate`, items *(1)* and *(2)***, on the loop closure of a finite
path-connected marked graph with a backward policy positive on its edges: `λ(x) = N(x)/(2+σ̄)`
with `λ(s₀) = λ(s_f) = 1/(2+σ̄)`, and the coercivity with `B̂_σ = σ_*√((2+σ̄)/min N)`.

Item *(3)* is a remark about how three downstream theorems consume the constant and is not
stated; see the module SCOPE. -/
theorem morozov_rate (hpc : G.PathConnected) (hpos : B.PositiveOnEdges) {lam g u : V → ℝ}
    (hl : B.IsInvProb lam) (hg : B.IsGreen g) (hu : B.IsHitExp u) :
    (∀ x, lam x = visits G g x / (2 + B.sigmaBar u))
      ∧ lam G.src = 1 / (2 + B.sigmaBar u)
      ∧ lam G.snk = 1 / (2 + B.sigmaBar u)
      ∧ ∀ h : V → ℝ, nrmL2 lam (fun x => h x - meanL2 lam h)
          ≤ sigmaStar G u * Real.sqrt ((2 + B.sigmaBar u) / minOver G (visits G g))
            * nrmL2 lam (fun x => h x - B.pdens lam h x) :=
  ⟨lam_eq_visits_div hpc hpos hl hg hu, lam_src_eq hpc hpos hl hg hu,
    lam_snk_eq hpc hpos hl hg hu, coercivity_morozov hpc hpos hl hg hu⟩

end BackwardPolicy

/-! ### The leveled graph: `B̂_σ` stays finite where `B̂` does not

`proofs.tex:855` — "on a leveled graph, where every trajectory has the same length `t_m` (the
autoregressive case), the loop-closed chain is periodic and `B̂ = +∞` while
`B̂_σ ≤ (t_m+1)√((2+t_m)/min_x N(x))`". Only the `B̂_σ` half is stated; the periodicity half needs
operator norms. See the module SCOPE. -/

/-- A **leveled** marked graph: a height rising by exactly one along every edge, with the source
at height `0`. Every source-to-sink walk then has the same length `ℓ(s_f)`, which is the paper's
`t_m`. The height is real-valued so that `ℓ(y) = ℓ(x) − 1` needs no truncation. -/
structure Leveled (G : MarkedGraph V) where
  /-- The height. -/
  lvl : V → ℝ
  /-- The source sits at height `0`. -/
  lvl_src : lvl G.src = 0
  /-- Every edge climbs by exactly one. -/
  lvl_edge : ∀ {x y : V}, G.Edge x y → lvl y = lvl x + 1

namespace Leveled

variable {B : BackwardPolicy G} (L : Leveled G)

omit [Fintype V] [DecidableEq V] in
/-- The height is monotone along walks of `G`. -/
theorem lvl_mono {x y : V} (h : G.Reach x y) : L.lvl x ≤ L.lvl y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => rw [L.lvl_edge hstep]; linarith

/-- **On a leveled graph the height *is* the hitting time.** Off `s₀` every backward step drops
the height by exactly one, so `ℓ = 1 + Qℓ`; with `ℓ(s₀) = 0` that is the hitting system, and by
uniqueness `E(σ ∣ X₀ = ·) = ℓ`. -/
theorem isHitExp : B.IsHitExp L.lvl := by
  refine ⟨L.lvl_src, fun x hx => ?_⟩
  have hstep : ∀ y : V, B.phat x y * L.lvl y = B.phat x y * (L.lvl x - 1) := by
    intro y
    by_cases hz : B.phat x y = 0
    · rw [hz, zero_mul, zero_mul]
    · have hedge : G.Edge y x := B.supp hx (by rwa [B.phat_of_ne_src hx] at hz)
      rw [L.lvl_edge hedge]
      ring
  rw [BackwardPolicy.qact_apply, Finset.sum_congr rfl (fun y _ => hstep y), ← Finset.sum_mul,
    B.phat_row_sum, one_mul]
  ring

omit [DecidableEq V] in
/-- `σ_* = t_m`: the sink is the unique maximum of the height, every vertex reaching it. -/
theorem sigmaStar_eq (hpc : G.PathConnected) : sigmaStar G L.lvl = L.lvl G.snk :=
  le_antisymm (maxOver_le fun x => L.lvl_mono (hpc.to_snk x)) (le_maxOver _ G.snk)

/-- `σ̄ = t_m − 1`: the target row sits one level below the sink. -/
theorem sigmaBar_eq : B.sigmaBar L.lvl = L.lvl G.snk - 1 := by
  have h := (L.isHitExp (B := B)).2 G.snk (Ne.symm G.src_ne_snk)
  rw [BackwardPolicy.sigmaBar]
  linarith

/-- **The leveled witness for `B̂_σ`** (`proofs.tex:855`): with `t_m := ℓ(s_f)`,
`B̂_σ ≤ (t_m + 1)√((2 + t_m)/min_x N(x))` — a finite bound with no aperiodicity anywhere, on the
graphs where the paper says the mixing constant `B̂` is infinite.

Sharper on this reading of *leveled*: `σ_* = t_m` and `σ̄ = t_m − 1` exactly
(`sigmaStar_eq`, `sigmaBar_eq`). The paper's looser form is stated because its `σ(s_f) ≤ t_m + 1`
points to a convention one shorter than this one; see the module SCOPE. -/
theorem bsigma_le (hpc : G.PathConnected) {N : V → ℝ} (hN : 0 < minOver G N) :
    sigmaStar G L.lvl * Real.sqrt ((2 + B.sigmaBar L.lvl) / minOver G N)
      ≤ (L.lvl G.snk + 1) * Real.sqrt ((2 + L.lvl G.snk) / minOver G N) := by
  have hnn : 0 ≤ L.lvl G.snk := by
    have := L.lvl_mono (hpc.to_snk G.src)
    rwa [L.lvl_src] at this
  rw [L.sigmaStar_eq hpc, L.sigmaBar_eq (B := B)]
  have hle : (2 + (L.lvl G.snk - 1)) / minOver G N ≤ (2 + L.lvl G.snk) / minOver G N := by
    gcongr
    linarith
  exact mul_le_mul (by linarith) (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _) (by linarith)

end Leveled

end GFNBounds.Graph
