---
declaration: GFNBounds.Doubling.main_truncation_bhat
sig_sha256: 3fab388627fd9fe6
---

## statement

At an even cap $K\geq d$ the truncation carries exactly one invariant probability $\lambda^K$,
and on $L^2(\lambda^K)$ there is a bounded operator $S$ with
\[ S(\mathrm{Id}-P_\star)=(\mathrm{Id}-P_\star)S=\mathrm{Id}-\Pi,\qquad \Pi S=S\Pi=0 . \]
In particular the diffusion constant $\widehat B_K=\|S\|$ is finite at every even cap.

## relation

So the object that fails to exist on the infinite chain does exist on every truncation of it.
Nothing diverges at a finite cap; what the next result shows is that the constant grows without
bound as the cap does, which is how an infinite constant is visible to a finite computation.

## sketch

Existence and uniqueness of the invariant probability are those of a finite irreducible chain
[[GFNBounds.Doubling.exists_stat]], [[GFNBounds.Doubling.stat_unique]]. On a finite state space
$\mathrm{Id}-P_\star+\Pi$ is then injective --- a vector it kills has zero mean and is fixed by
$P_\star$, hence is a constant of zero mean --- and injective is invertible in finite
dimension; writing $R$ for the inverse and $S=R-\Pi$, the relations $\Pi P_\star=P_\star\Pi=\Pi$
and $\Pi^2=\Pi$ give the four identities [[GFNBounds.Doubling.Stat.exists_bhat]]. Boundedness
is automatic, the space being finite-dimensional.
