---
declaration: GFNBounds.Doubling.main_unbounded_two
sig_sha256: 5918ba8382cfbd1b
---

## statement

Let $\varepsilon_{c,s}$ be a member of the family with $c>0$, $s\geq0$, and let $\lambda$ be an
invariant probability of the loop closure. On $L^2(\lambda)$: no bounded operator $S$ satisfies
$S(\mathrm{Id}-P_\star)=\mathrm{Id}-\Pi$; the series $\sum_{n\geq0}(P_\star^n-\Pi)$ does not
converge in operator norm; and $\sum_{n\geq0}\widehat\beta_n=+\infty$, where
$\widehat\beta_n=\|P^n-\Pi\|_{L^2(\lambda)}$.

## relation

This is the sentence that separates the two conditions. The summable-mixing hypothesis of the
main text's $L^2$ universality theorem, and of its frozen detailed-balance theorem in the
flow-matching instance --- where the constant is exactly the state-space mixing sum
$\sum_n\widehat\beta_n$ --- is repaired by no positive recurrent member of this family, while
the backward length above is finite throughout. The divergence is a statement about the
flow-matching instance; the detailed-balance instance, whose coefficients are the edge-lifted
ones, is not covered.

## sketch

All three are the same fact at $p=2$. The family satisfies the growth condition
[[GFNBounds.Doubling.GrowthCond]], discharged as before
[[GFNBounds.Doubling.growthCond_of_family]]; the vanishing infimum of the Rayleigh quotient
then excludes a bounded left inverse [[GFNBounds.Doubling.Stat.no_diffusionOp]]. The other two
follow from that one: a norm-convergent series would furnish such an inverse, since its sum
$U$ satisfies $(\mathrm{Id}-P_\star)U=U(\mathrm{Id}-P_\star)=\mathrm{Id}-\Pi$ by telescoping
[[GFNBounds.Doubling.Stat.not_tendsto_partialSum]]; and a summable
$\sum_n\widehat\beta_n$ would make that series absolutely convergent, the norms being the
$\widehat\beta_n$ [[GFNBounds.Doubling.Stat.not_summable_betaHat]].
