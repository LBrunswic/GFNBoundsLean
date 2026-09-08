---
declaration: GFNBounds.Doubling.main_constant_determined
sig_sha256: 034406ea0f1c43da
---

## statement

At $s=1$ and $0<c<1$, two invariant probabilities of the loop closure that agree on the first
$d$ ladder states agree at every ladder state.

## relation

The boundary data of the target row therefore fix the whole invariant measure, and with it the
constant of the asymptotic below. This is what makes that constant a property of the policy and
the target row rather than a free parameter.

## sketch

At $s=1$ the cut balance expresses $\lambda_m$, for every $m>d$, as a positive combination of
the $\lambda_j$ with $\lceil m/2\rceil\leq j\leq m-1$ — indices all smaller than $m$. Induction
on $m$ therefore determines the whole sequence from $\lambda_1,\dots,\lambda_d$, which is the
uniqueness statement [[GFNBounds.Doubling.Decay.cutBal_unique]]; the Cramér root that the
surrounding parameters need is supplied by [[GFNBounds.Doubling.Decay.ofC]].
