import GFNBounds.Doubling.Drift

/-!
# The phase diagram

**`prop:doubling_phase`** — `app_doubling.tex:510–627` (Proposition 99 of the ICLR build), and
`theo:doubling_main`(1).

The recurrence classification of the loop-closed chain on the standing range: transient for
`s < 1`; positive recurrent for `s = 1`, `0 < c < 1`; null recurrent for `s = 1`, `1 ≤ c < 1/ln 2`;
**undecided** at `c = 1/ln 2`; transient for `s = 1`, `1/ln 2 < c < 2`; positive recurrent for
`s > 1`.

## SCOPE (disclosed)

This is the appendix's single largest dependency on machinery Mathlib v4.31.0 does not have.
Its eight steps consume: **Foster's criterion** in both its positive-recurrence and its recurrence
form; the **bounded-supermartingale transience criterion** (which the appendix states but does not
cite); **optional stopping** for a bounded stopped submartingale; the **strong Markov property**;
and the Kac-type equivalences "irreducible with infinite expected return time ⟹ not positive
recurrent" and "…and recurrent ⟹ null recurrent". Mathlib has martingales and optional stopping
but no discrete-time Markov-chain recurrence theory at all.

Nothing in `GFNBounds/` depends on this file. The results that consume positive recurrence
(`lem:doubling_percut` case (1), `theo:doubling_unbounded`, `lem:doubling_ramp`,
`prop:doubling_unsolvable`) take it as a **hypothesis**, exactly as the paper does — in this
library, as the existence of a `Stat`. So the headline is reachable with this file still open.

Row (d) of the table, `c = 1/ln 2`, is **open in the paper too**: the chain is not positive
recurrent, and null recurrence versus transience is not decided (`app_doubling.tex:626`). It is
not stated here, and must not be added as if settled.
-/

namespace GFNBoundsScaffold.Doubling

open GFNBounds.Doubling

/-- Positive recurrence at `s = 1`, `0 < c < 1` — row (b), the case the rest of the appendix
works in. Phrased as the existence of an invariant probability, which is what every downstream
statement actually consumes. -/
theorem exists_stat_of_lt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Setting) (hS : S.eps = epsCS c 1) : Nonempty (Stat S none) :=
  sorry -- SORRY(prop:doubling_phase): Foster's criterion for positive recurrence; Mathlib v4.31.0 has no discrete-time Markov-chain recurrence theory.

end GFNBoundsScaffold.Doubling
