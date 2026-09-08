---
declaration: GFNBounds.Doubling.main_truncation_irreducible
sig_sha256: b8800ab3e3c4aff3
---

## statement

At an even cap $K\geq d$ the truncation is irreducible on its $K+2$ states, and every invariant
measure of it is strictly positive at each of them.

## relation

The truncation is what a numerical experiment can actually run, and this is what makes it a
legitimate finite approximation: the same qualitative structure as the infinite chain, on a
finite state space where the diffusion constant is finite and can be measured.

## sketch

Only the climbing half differs from the infinite chain, because the doubling edges above $K/2$
have been cut. Let $2^{r}$ be the largest power of two at most $K$: the edges
$2^{i}\rightarrow2^{i+1}$ all survive for $i<r$, so the ladder state $1$ reaches $2^{r}$ and,
by decrements, every state below it. Above $2^{r}$ an even $n$ is reached by doubling from
$n/2\leq K/2<2^{r}$, and an odd $n$ is not the cap --- which is even --- so $n+1$ is even and
in range and one decrement finishes [[GFNBounds.Doubling.reach_all_some]]. Positivity is the
same general fact as on the loop closure
[[GFNBounds.Doubling.PreStat.pos_of_irreducible]].
