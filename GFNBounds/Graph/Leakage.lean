import Mathlib

/-!
# Leakage: the sampler of a frozen backward policy whose backward walk can escape

A backward policy held fixed on a graph with countably many states moves the backward walk among
the internal states by a kernel `Q` and steps to the source with probability `k`; the sink row
`ρ` is where a backward trajectory starts. On a finite path-connected graph the backward walk
reaches the source almost surely. On an infinite graph it may escape to infinity instead, and
`h(x)`, the probability that the backward walk from `x` ever reaches the source, is then below
one. This file computes what the sampler of a flow of the frozen family does in that case.

With the policy frozen a flow is its state mass `μ`, the inflow of each state, and it is balanced
at every internal state exactly when `μ = μQ + Zρ` on the internal states, `Z` the terminal mass.
The edge into `x` from `y` carries `μ(x)Q(x,y)`, the edge from the source to `x` carries
`μ(x)k(x)`, and the initial mass is `m = Σ μ(x)k(x)`. The sampler starts from the source, moves
from `y` to `x` with probability `μ(x)Q(x,y)/μ(y)`, and stops at `y` with probability
`Zρ(y)/μ(y)`: these are the forward policy and the stopping rate of the flow.

## What is proved

| | |
|---|---|
| **`fwdLaw_eq`** | the sampler's law at step `n`, among the states it has not left, is `μ(x)(Qⁿk)(x)/m` |
| **`stopLaw_eq`** | it stops at `x` with probability `Zρ(x)h(x)/m`, whatever the flow |
| **`mass_step`, `mass_partial`** | with balance: what has stopped by step `N` plus what is still running is `1` |
| **`sampler_leaks`** | with balance: the stopping law is `Zρh/m`, its total is `Z⟨ρ,h⟩/m ≤ 1`, so `m ≥ Z⟨ρ,h⟩` |
| **`sampler_leaks_matched`** | at matched mass, `m = Z` and `⟨ρ,1⟩ = 1`: the sampler stops with probability `⟨ρ,h⟩` and stops at `x` with probability `ρ(x)h(x)` |

So the sampler stops with probability `Z⟨ρ,h⟩/m` and escapes to infinity otherwise; when it
stops it draws `ρh/⟨ρ,h⟩`, the sink row tilted towards the states whose backward walk comes back,
and not the sink row itself. The flow enters only through its initial mass `m`.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| a backward policy on countably many states | `Q : V → V → ℝ≥0∞` among the internal states, `k : V → ℝ≥0∞` to the source; no row-sum condition is needed |
| `h`, the probability of reaching the source | `absorb Q k := Σₙ absorbN Q k n`, `absorbN Q k n = Qⁿk` |
| a flow of the frozen family | `μ : V → ℝ≥0∞`, positive and finite at every state (`hμ0`, `hμt`) |
| balanced at every internal state | `hbal : μ y = Σₓ μ(x)Q(x,y) + Zρ(y)`; used only from `mass_step` on |
| the initial mass | `m = Σ μ(x)k(x)`, nonzero and finite |

## SCOPE (disclosed)

* **The sampler is its sequence of laws.** `fwdLaw n` is the law of the sampler at step `n`
  restricted to the event that it has not stopped, defined by its one-step recursion; the
  stopping law is the sum over `n` of `fwdLaw n` times the stopping rate. No path space is built.
* **The total mass of `μ` may be infinite**, and is so whenever `h < 1` somewhere on the support
  of `ρ`, since the escaping backward trajectories are infinitely long. The sampling theorem asks
  for a finite outflow, which is why it does not apply here; nothing in this file needs it.
* **No `sorry`.**

Provenance: mathlib tag `v4.31.0`, pinned via `lakefile.toml`.
-/

namespace GFNBounds.Graph.Leakage

open scoped ENNReal

variable {V : Type*}

/-- **`(Qⁿk)(x)`**: the probability that the backward walk from `x`, moving by `Q` among the
internal states, steps to the source at step `n + 1` exactly. -/
noncomputable def absorbN (Q : V → V → ℝ≥0∞) (k : V → ℝ≥0∞) : ℕ → V → ℝ≥0∞
  | 0 => k
  | n + 1 => fun x => ∑' y, Q x y * absorbN Q k n y

/-- **`h(x)`**: the probability that the backward walk from `x` ever reaches the source. -/
noncomputable def absorb (Q : V → V → ℝ≥0∞) (k : V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ∑' n, absorbN Q k n x

/-- **The sampler's law at step `n`**, among the states it has not left: it starts at `x` with
probability `μ(x)k(x)/m` and moves from `y` to `x` with probability `μ(x)Q(x,y)/μ(y)`. -/
noncomputable def fwdLaw (Q : V → V → ℝ≥0∞) (k μ : V → ℝ≥0∞) (m : ℝ≥0∞) : ℕ → V → ℝ≥0∞
  | 0 => fun x => μ x * k x / m
  | n + 1 => fun x => ∑' y, fwdLaw Q k μ m n y * (μ x * Q x y / μ y)

/-- **The stopping law**: the sampler stops at `x` at some step, at the rate `Zρ(x)/μ(x)`. -/
noncomputable def stopLaw (Q : V → V → ℝ≥0∞) (k μ : V → ℝ≥0∞) (m Z : ℝ≥0∞) (ρ : V → ℝ≥0∞)
    (x : V) : ℝ≥0∞ :=
  ∑' n, fwdLaw Q k μ m n x * (Z * ρ x / μ x)

variable {Q : V → V → ℝ≥0∞} {k μ ρ : V → ℝ≥0∞} {m Z : ℝ≥0∞}

/-- **The step law is the backward absorption read forward**: `μ(x)(Qⁿk)(x)/m`. -/
theorem fwdLaw_eq (hμ0 : ∀ y, μ y ≠ 0) (hμt : ∀ y, μ y ≠ ∞) (n : ℕ) (x : V) :
    fwdLaw Q k μ m n x = μ x * absorbN Q k n x / m := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hterm : ∀ y, fwdLaw Q k μ m n y * (μ x * Q x y / μ y)
        = μ x * m⁻¹ * (Q x y * absorbN Q k n y) := by
      intro y
      rw [ih y, div_eq_mul_inv, div_eq_mul_inv]
      calc μ y * absorbN Q k n y * m⁻¹ * (μ x * Q x y * (μ y)⁻¹)
          = μ x * m⁻¹ * (Q x y * absorbN Q k n y) * (μ y * (μ y)⁻¹) := by ring
        _ = μ x * m⁻¹ * (Q x y * absorbN Q k n y) := by
          rw [ENNReal.mul_inv_cancel (hμ0 y) (hμt y), mul_one]
    show ∑' y, fwdLaw Q k μ m n y * (μ x * Q x y / μ y) = μ x * absorbN Q k (n + 1) x / m
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    show μ x * m⁻¹ * ∑' y, Q x y * absorbN Q k n y
      = μ x * (∑' y, Q x y * absorbN Q k n y) / m
    rw [div_eq_mul_inv]
    ring

/-- **The stopping law is the sink row times the absorption probability**: `Zρ(x)h(x)/m`,
whatever the flow, through its initial mass only. -/
theorem stopLaw_eq (hμ0 : ∀ y, μ y ≠ 0) (hμt : ∀ y, μ y ≠ ∞) (x : V) :
    stopLaw Q k μ m Z ρ x = Z * ρ x * absorb Q k x / m := by
  have hterm : ∀ n, fwdLaw Q k μ m n x * (Z * ρ x / μ x)
      = Z * ρ x * m⁻¹ * absorbN Q k n x := by
    intro n
    rw [fwdLaw_eq hμ0 hμt n x, div_eq_mul_inv, div_eq_mul_inv]
    calc μ x * absorbN Q k n x * m⁻¹ * (Z * ρ x * (μ x)⁻¹)
        = Z * ρ x * m⁻¹ * absorbN Q k n x * (μ x * (μ x)⁻¹) := by ring
      _ = Z * ρ x * m⁻¹ * absorbN Q k n x := by
        rw [ENNReal.mul_inv_cancel (hμ0 x) (hμt x), mul_one]
  unfold stopLaw
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, absorb, div_eq_mul_inv]
  ring

/-- **One step of mass accounting**: what is running at step `n + 1` plus what stops at step
`n` is what was running at step `n`. This is where balance enters. -/
theorem mass_step (hμ0 : ∀ y, μ y ≠ 0) (hμt : ∀ y, μ y ≠ ∞)
    (hbal : ∀ y, μ y = (∑' x, μ x * Q x y) + Z * ρ y) (n : ℕ) :
    (∑' x, fwdLaw Q k μ m (n + 1) x) + ∑' y, fwdLaw Q k μ m n y * (Z * ρ y / μ y)
      = ∑' y, fwdLaw Q k μ m n y := by
  have hrun : (∑' x, fwdLaw Q k μ m (n + 1) x)
      = ∑' y, fwdLaw Q k μ m n y * ((∑' x, μ x * Q x y) * (μ y)⁻¹) := by
    show (∑' x, ∑' y, fwdLaw Q k μ m n y * (μ x * Q x y / μ y)) = _
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun y => ?_
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [div_eq_mul_inv]
  rw [hrun, ← ENNReal.tsum_add]
  refine tsum_congr fun y => ?_
  rw [div_eq_mul_inv, ← mul_add, ← add_mul, ← hbal y,
    ENNReal.mul_inv_cancel (hμ0 y) (hμt y), mul_one]

/-- **Mass accounting to step `N`**: what has stopped before step `N` plus what is still running
at step `N` is the initial law's mass. -/
theorem mass_partial (hμ0 : ∀ y, μ y ≠ 0) (hμt : ∀ y, μ y ≠ ∞)
    (hbal : ∀ y, μ y = (∑' x, μ x * Q x y) + Z * ρ y) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑' y, fwdLaw Q k μ m n y * (Z * ρ y / μ y))
      + ∑' x, fwdLaw Q k μ m N x = ∑' x, fwdLaw Q k μ m 0 x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, add_comm _ (∑' x, fwdLaw Q k μ m (N + 1) x),
      mass_step hμ0 hμt hbal N, ih]

/-- The initial law has mass one. -/
theorem fwdLaw_zero_mass (hm : m = ∑' x, μ x * k x) (hm0 : m ≠ 0) (hmt : m ≠ ∞) :
    (∑' x, fwdLaw Q k μ m 0 x) = 1 := by
  show (∑' x, μ x * k x / m) = 1
  simp only [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, ← hm, ENNReal.mul_inv_cancel hm0 hmt]

/-- **The sampler of a frozen backward policy leaks.** For a flow of the frozen family, balanced
at every internal state, with positive finite state mass and initial mass `m`, the sampler started
from the source stops at `x` with probability `Zρ(x)h(x)/m`; it stops at all with probability
`Z⟨ρ,h⟩/m ≤ 1` and escapes otherwise; and `m ≥ Z⟨ρ,h⟩`. -/
theorem sampler_leaks (hμ0 : ∀ y, μ y ≠ 0) (hμt : ∀ y, μ y ≠ ∞)
    (hbal : ∀ y, μ y = (∑' x, μ x * Q x y) + Z * ρ y)
    (hm : m = ∑' x, μ x * k x) (hm0 : m ≠ 0) (hmt : m ≠ ∞) :
    (∀ x, stopLaw Q k μ m Z ρ x = Z * ρ x * absorb Q k x / m)
    ∧ (∑' x, stopLaw Q k μ m Z ρ x) = Z * (∑' x, ρ x * absorb Q k x) / m
    ∧ (∑' x, stopLaw Q k μ m Z ρ x) ≤ 1
    ∧ Z * (∑' x, ρ x * absorb Q k x) ≤ m := by
  have hlaw := stopLaw_eq (Q := Q) (k := k) (m := m) (Z := Z) (ρ := ρ) hμ0 hμt
  have htot : (∑' x, stopLaw Q k μ m Z ρ x) = Z * (∑' x, ρ x * absorb Q k x) / m := by
    rw [tsum_congr hlaw]
    simp only [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    congr 1
    refine tsum_congr fun x => ?_
    ring
  have hle : (∑' x, stopLaw Q k μ m Z ρ x) ≤ 1 := by
    unfold stopLaw
    rw [ENNReal.tsum_comm, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    have h := mass_partial (m := m) (k := k) hμ0 hμt hbal N
    rw [fwdLaw_zero_mass hm hm0 hmt] at h
    rw [← h]
    exact le_self_add
  refine ⟨hlaw, htot, hle, ?_⟩
  have h1 : Z * (∑' x, ρ x * absorb Q k x) / m ≤ 1 := by rw [← htot]; exact hle
  rwa [ENNReal.div_le_iff hm0 hmt, one_mul] at h1

/-- **At matched mass the escape probability is the backward escape probability.** If the
initial mass equals the terminal mass and the sink row is a probability, the sampler stops at `x`
with probability `ρ(x)h(x)`, and at all with probability `⟨ρ,h⟩`: it escapes with the probability
that a backward trajectory started from the sink row escapes, and when it stops it draws the sink
row tilted by `h`. -/
theorem sampler_leaks_matched (hμ0 : ∀ y, μ y ≠ 0) (hμt : ∀ y, μ y ≠ ∞)
    (hbal : ∀ y, μ y = (∑' x, μ x * Q x y) + Z * ρ y)
    (hm : Z = ∑' x, μ x * k x) (hZ0 : Z ≠ 0) (hZt : Z ≠ ∞) :
    (∀ x, stopLaw Q k μ Z Z ρ x = ρ x * absorb Q k x)
    ∧ (∑' x, stopLaw Q k μ Z Z ρ x) = ∑' x, ρ x * absorb Q k x := by
  obtain ⟨hlaw, htot, -, -⟩ := sampler_leaks (m := Z) hμ0 hμt hbal hm hZ0 hZt
  refine ⟨fun x => ?_, ?_⟩
  · rw [hlaw x, div_eq_mul_inv]
    calc Z * ρ x * absorb Q k x * Z⁻¹ = ρ x * absorb Q k x * (Z * Z⁻¹) := by ring
      _ = ρ x * absorb Q k x := by rw [ENNReal.mul_inv_cancel hZ0 hZt, mul_one]
  · rw [htot, div_eq_mul_inv]
    calc Z * (∑' x, ρ x * absorb Q k x) * Z⁻¹ = (∑' x, ρ x * absorb Q k x) * (Z * Z⁻¹) := by ring
      _ = ∑' x, ρ x * absorb Q k x := by rw [ENNReal.mul_inv_cancel hZ0 hZt, mul_one]

end GFNBounds.Graph.Leakage
