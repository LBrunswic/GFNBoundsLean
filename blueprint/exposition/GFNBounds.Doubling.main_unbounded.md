---
declaration: GFNBounds.Doubling.main_unbounded
sig_sha256: eef36ec81c01b391
---

## statement

Let $\varepsilon_{c,s}$ be a member of the family with $c>0$, $s\geq0$, let $\lambda$ be an
invariant probability of the loop closure, and let $1\leq p<\infty$. Then:
\begin{itemize}
  \item for every $t>0$ there is a cut $m>d$ whose centred tail indicator $f_m$ satisfies
        $\|(\mathrm{Id}-P_\star)f_m\|^p_{L^p(\lambda)}\leq t\,\|f_m\|^p_{L^p(\lambda)}$; and
  \item no constant $B$ satisfies $\|f\|_{L^p(\lambda)}\leq B\,\|(\mathrm{Id}-P_\star)f\|_{L^p(\lambda)}$
        for every bounded mean-zero $f$.
\end{itemize}

## relation

The second clause is the failure of a bounded diffusion operator at every finite exponent. The
main text's convergence bounds are stated with a constant of exactly this shape; on this graph
no such constant exists, at any $p$, at any positive recurrent member of the family. The first
clause is the sharper fact behind it: the infimum of the Rayleigh quotient is not merely
unattained but zero.

## sketch

The family satisfies the growth condition $\sum_{i<D}\log(1/\varepsilon(2^i))=o(2^{D})$
[[GFNBounds.Doubling.GrowthCond]], because for $\varepsilon_{c,s}$ that sum is $O(D^2)$
[[GFNBounds.Doubling.growthCond_of_family]].

Given the growth condition, the ratio $L(m)/\lambda_m$ is unbounded: were it bounded by $Q$,
the tail would decay geometrically at rate $e^{-1/Q}$, while iterating the doubling inequality
along the powers of two forces $L(2^{D})\geq\lambda_1\prod_{i<D}\varepsilon(2^{i})$, and the
growth condition makes the second bound incompatible with the first. Choosing cuts along that
unbounded ratio makes the centred tail indicator's defect small against its own mass
[[GFNBounds.Doubling.Stat.exists_small_mass_ratio]], which is the first clause; the second is
that same infimum read as the non-existence of a bound
[[GFNBounds.Doubling.Stat.no_bounded_inverse]].
