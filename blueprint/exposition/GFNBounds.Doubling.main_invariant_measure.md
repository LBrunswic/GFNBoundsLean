---
declaration: GFNBounds.Doubling.main_invariant_measure
sig_sha256: 9349ecc0e7335694
---

## statement

At $s=1$ and $0<c<1$, let $\lambda$ be an invariant probability of the loop closure. Then the
Cram\'er equation $\psi_c(p)=0$ has a root $p>1$, and there is a constant $C>0$ with
\[ \lambda_m\,m^{p}\longrightarrow C, \qquad (p-1)\,m^{p-1}L(m)\longrightarrow C, \]
where $L(m)=\sum_{j\geq m}\lambda_j$; and the first convergence carries a polynomial rate:
there are $\vartheta\in(0,1)$ and $c_6>0$ with $|\lambda_m m^{p}-C|\leq c_6\,m^{-\vartheta}$ at
every $m\geq1$.

## relation

The invariant measure of this graph decays like a power, not geometrically, and the exponent is
the Cram\'er root of the doubling probability. That is the mechanism behind everything that
follows: a power tail is heavy enough that the centred tail indicators below have vanishing
Rayleigh quotient, which is what breaks the mixing hypothesis of the main text.

## sketch

The Cram\'er root and the parameters it fixes are packaged by [[GFNBounds.Doubling.Decay.ofC]].
Given them, the invariant probability yields a positive sequence satisfying the cut balance
above $d$, and the whole asymptotic follows from that alone
[[GFNBounds.Doubling.Decay.sharp_of_cutBal]]: a contraction estimate on dyadic blocks shows the
rescaled profile $\lambda_m m^{p}$ is Cauchy, its limit lies between the two constants of the
two-sided decay bound and is therefore positive, and balancing the block index against the
level gives the exponent $\vartheta$. The statement about the tail is the same limit summed
[[GFNBounds.Doubling.Decay.tendsto_tail_sharp]]: comparing $\sum_{j\geq m}j^{-p}$ with its
integral turns a limit for the profile into one for the tail.
