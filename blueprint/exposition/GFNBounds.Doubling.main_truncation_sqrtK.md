---
declaration: GFNBounds.Doubling.main_truncation_sqrtK
sig_sha256: 3b505edfd8112914
---

## statement

At $s=1$ and $0<c<1$ there are $c_8>0$ and a cap $K_0$ such that, for every $K\geq K_0$ and
every bounded operator $S$ on $L^2(\lambda^K)$ with $S(\mathrm{Id}-P_\star)=\mathrm{Id}-\Pi$,
\[ c_8\,K \;\leq\; \|S\|^2 . \]
That is, $\widehat B_K\geq\sqrt{c_8}\,\sqrt K$ at every large even cap.

## relation

This is the quantitative form of the separation, and the one a measurement can be compared
against: the diffusion constant of the truncation is finite but grows at least like $\sqrt K$,
so it diverges as the truncation is lifted, while the backward length stays at
$\bar\jmath/(1-c)$ throughout. The bound holds for \emph{every} left inverse, so it is a
property of the chain and not of a particular construction.

## sketch

The argument is the per-cut inequality applied at a cut of order $K$. The decay bound transfers
to the truncation with constants that do not depend on the cap
[[GFNBounds.Doubling.Stat.decayK]]: extending $\lambda^K$ above the cap gives a positive
sequence satisfying the cut balance below $K/2$, so the block estimate applies at the level
$m_0$ [[GFNBounds.Doubling.Decay.m0]], and the ratio of the two constants is controlled by
chaining the cut-balance inequalities across one block. The descent weight at that level is
two-sided [[GFNBounds.Doubling.Decay.descOne_two_sided]] with the escape constant
[[GFNBounds.Doubling.Decay.c5]], and the Cram\'er root is again
[[GFNBounds.Doubling.Decay.ofC]].

Taking the cut at $\lfloor K/4\rfloor$ then makes $L_K(m)/\lambda^K_m$ of order $K$, while the
mass below the cut is bounded away from zero uniformly in $K$ --- on a finite irreducible chain
the mass at the source is the reciprocal of the expected return time, which is
$2+\bar\sigma_K\leq2+\bar\jmath/(1-c)$. Feeding both into the per-cut inequality gives the
displayed bound [[GFNBounds.Doubling.Stat.sqrtK]].
