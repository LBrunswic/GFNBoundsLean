---
declaration: GFNBounds.Doubling.main_unsolvable
sig_sha256: f97fe737cac1091e
---

## statement

Let $\varepsilon_{c,s}$ be a member of the family with $c>0$, $s\geq0$, and let $\lambda$ be an
invariant probability of the loop closure. Then $(\mathrm{Id}-P_\star)L^2(\lambda)$ is a dense
proper subspace of $\ker\Pi$, and there are probability densities
$\finit,\fterm\in L^2(\lambda)$ for which no $f\in L^2(\lambda)$ satisfies the flow-matching
equation $(\mathrm{Id}-P_\star)f=\finit-\fterm$.

## relation

What this refutes is \emph{exact} $L^2$ flow matching on the infinite chain: a pair of $L^2$
densities the loop closure cannot balance at all. It does not refute the weak universality of
the main text, whose conclusion is a defect infimum of zero --- density of the range is exactly
what the first clause asserts, and whether the weak form fails here is not decided.

## sketch

Write $A$ for the restriction of $\mathrm{Id}-P_\star$ to $\ker\Pi$. It is injective, its
kernel being the mean-zero fixed points of $P_\star$, which irreducibility reduces to the
constants and hence to zero; its adjoint inside $\ker\Pi$ is the restriction of
$\mathrm{Id}-P$, injective for the same reason, so the range of $A$ is dense. It is not
surjective: a surjective bounded injection of a Hilbert space is boundedly invertible by the
open mapping theorem, and that contradicts the vanishing infimum established above. Picking
$\psi\in\ker\Pi$ outside the range and splitting it into positive and negative parts produces
the two densities [[GFNBounds.Doubling.doubling_unsolvable]]. The growth condition the argument
needs is discharged for the family as before
[[GFNBounds.Doubling.growthCond_of_family]].
