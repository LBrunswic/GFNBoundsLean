---
declaration: GFNBounds.Doubling.main_irreducible
sig_sha256: b53264b7d5b15c1a
---

## statement

On the loop closure every state reaches every other, and every invariant measure of it is
strictly positive at every state.

## relation

Irreducibility and positivity are the standing hypotheses under which the rest of this appendix
speaks of \emph{the} invariant probability and of the operators built from it. The main text's
universality and convergence theorems are stated for chains carrying such a measure; what
follows establishes, for each member of the family, whether one exists.

## sketch

The graph half is a pair of explicit paths [[GFNBounds.Doubling.reach_all_none]]. Every state
reaches the ladder state $1$: from a ladder state the decrements walk down to the source, the
wrap carries it to the sink, and the target row re-enters the ladder. Conversely $1$ reaches
every state, by climbing: from $n$ the doubling edge to $2n$ followed by $n-1$ decrements lands
on $n+1$, and $2n\geq n+1$. Concatenating the two gives reachability between any pair.

The measure half is general and needs only that [[GFNBounds.Doubling.PreStat.pos_of_irreducible]]:
an invariant measure is positive somewhere, and invariance transports that positivity along any
path, so irreducibility spreads it over the whole state space.
