---
declaration: GFNBounds.Doubling.main_rate
sig_sha256: 95f823bf59148a65
---

## statement

At $s=1$ and $0<c<1$, with $p>1$ the Cram\'er root and $\lambda$ an invariant probability of
the loop closure, there are constants $0<c_1\leq c_2$ and a cut $m_2>d$ such that the centred
tail indicators satisfy
\[ c_1\,m\;\bigl\|(\mathrm{Id}-P_\star)f_m\bigr\|^2_{L^2(\lambda)}
   \;\leq\; 4c_2(p-1)\,\|f_m\|^2_{L^2(\lambda)} \qquad (m\geq m_2). \]

## relation

Unboundedness above says only that the Rayleigh quotient has infimum zero; this says how fast,
along an explicit family of trial functions. Squared and rearranged it is
$\|f_m\|\geq c_7\sqrt m\,\|(\mathrm{Id}-P_\star)f_m\|$. It is not a lower bound on the
diffusion constant of the infinite chain, which is $+\infty$ there; it is a rate along the
$f_m$, and it is the truncation below that converts a rate into a bound on a finite constant.

## sketch

The two-sided decay bound $c_1 j^{-p}\leq\lambda_j\leq c_2 j^{-p}$ holds unconditionally at
this level [[GFNBounds.Doubling.Decay.decay_two_sided_of_cutBal]], run at the level $m_0$ at
which the descent-weight window is controlled [[GFNBounds.Doubling.Decay.m0]], with the root
supplied by [[GFNBounds.Doubling.Decay.ofC]]. Summing that bound over $j\geq m$ gives
$L(m)/\lambda_m\geq c_1m/(c_2(p-1))$, so the per-cut inequality --- the defect of $f_m$ is
carried by the cut and the window alone, and the cut balance collapses the window --- reads as
the display once the mass below the cut is bounded away from zero. The cut $m_2$ past which
that last condition holds exists because $L(m)\to0$
[[GFNBounds.Doubling.Stat.exists_rayleigh_family]].
