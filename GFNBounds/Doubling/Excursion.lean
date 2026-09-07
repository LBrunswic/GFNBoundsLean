import GFNBounds.Doubling.Setting

/-!
# The excursion maximum is bounded by the hitting time

**`lem:doubling_excursion`** — `app_doubling.tex:398–424`.

> Let `(X_n)` be either the backward chain of the loop closure or, for `K ≥ d`, that of the
> truncation at `K`, and let `σ` be its hitting time of `s₀`. Then `X_{n+1} ≥ X_n − 1` at every
> step issued from a ladder state, and for every ladder state `j`,
> `max_{0≤n≤σ} X_n ≤ σ`  `P(·|X₀=j)`-almost surely.

## The modelling decision

The statement is **pathwise**: it holds for every trajectory, not almost every one, and the
"almost surely" of the paper is quantification over the paths of positive probability. Here it is
quantification over every sequence whose steps are admissible — `LadderStep` — which is the
strongest reading and needs no measure. The two chains are the two values of `cap`, exactly as in
`pstar`.

The bound is the paper's counting argument, run as a downward induction: from `n` to `σ` each of
the `σ − n` steps lowers the path by at most one and `X_σ = 0`, so `X_n ≤ σ − n ≤ σ`.

## SCOPE (disclosed)

* The path is a sequence of **ladder indices** `ℕ`, with `s₀` read as `0`; the sink is not on it.
  That is the paper's "started at a ladder state the chain visits only ladder states before `σ`",
  which is therefore built into the formulation rather than proved.
* `σ` is any index at which the path is at `0`, not necessarily the first: the bound holds at
  every such index, which is stronger and is what the downward induction gives.
* The `{σ = +∞}` branch of the paper's statement — where the assertion reads `sup X_n ≤ +∞` and
  is vacuous — has no counterpart: `σ : ℕ` here, and the vacuous branch carries nothing.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GFNBounds.Doubling

/-- One admissible step of the backward chain along the ladder: double, when that edge survives
the cap, or decrement. `s₀` is the index `0`, and `0 - 1 = 0` in `ℕ` makes it absorbing for the
decrement, which is harmless: the bound is asserted at an index where the path is already at `0`. -/
def LadderStep (cap : Option ℕ) (a b : ℕ) : Prop :=
  (b = 2 * a ∧ HasDouble cap a) ∨ b = a - 1

/-- **The first half of `lem:doubling_excursion`.** `X_{n+1} ≥ X_n − 1`, in the form `X_n ≤
X_{n+1} + 1`. -/
theorem LadderStep.le_succ_add_one {cap : Option ℕ} {a b : ℕ} (h : LadderStep cap a b) :
    a ≤ b + 1 := by
  rcases h with ⟨rfl, -⟩ | rfl <;> omega

/-- **`eq:doubling_excursion`.** Along any admissible path reaching `0` at time `σ`, every value up
to `σ` is at most `σ`: the excursion maximum is bounded by the hitting time. -/
theorem excursion_le {cap : Option ℕ} {x : ℕ → ℕ}
    (hstep : ∀ n, LadderStep cap (x n) (x (n + 1))) {σ : ℕ} (hσ : x σ = 0) :
    ∀ n, n ≤ σ → x n ≤ σ := by
  have key : ∀ k n : ℕ, n + k = σ → x n ≤ k := by
    intro k
    induction k with
    | zero => intro n hn; rw [show n = σ by omega, hσ]
    | succ k ih =>
        intro n hn
        have h1 : (n + 1) + k = σ := by omega
        have h2 : x (n + 1) ≤ k := ih (n + 1) h1
        have h3 : x n ≤ x (n + 1) + 1 := (hstep n).le_succ_add_one
        omega
  intro n hn
  have := key (σ - n) n (by omega)
  omega

end GFNBounds.Doubling
