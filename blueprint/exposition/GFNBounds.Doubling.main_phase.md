---
declaration: GFNBounds.Doubling.main_phase
sig_sha256: e40c4e078728208c
---

## statement

Let $\varepsilon_{c,s}(j)=c(j+1)^{-s}$ with $c>0$, in the standing range. The loop-closed
backward chain admits an invariant probability exactly in two of the four regimes: it admits
none for $s<1$; exactly one for $s=1$ with $c<1$; none for $s=1$ with $c\geq1$; and one for
$s>1$.

## relation

This is the phase diagram that decides which members of the family the main text's theorems can
even be stated about. In the two regimes with no invariant probability there is no $\lambda$,
hence no $\Pi$, no mixing coefficients and no diffusion constant: the hypotheses of those
theorems fail there for want of the objects they quantify over, which is a different kind of
failure from the one this appendix is about.

## sketch

Three cases, each a drift computation against a Lyapunov function, and no more.

For $s<1$ the drift coefficient $c(m+1)^{1-s}$ grows without bound, which forces the tail of
any candidate invariant sequence to grow too fast to be summable
[[GFNBounds.Doubling.isEmpty_stat_of_family_lt_one]]. For $s=1$ the coefficient is the constant
$c$, and $c\geq1$ is exactly the threshold past which the same tail argument applies
[[GFNBounds.Doubling.isEmpty_stat_of_family_ge_one]]. For $s>1$ the drift is eventually
negative and a Foster argument on the ladder height produces an invariant probability
[[GFNBounds.Doubling.exists_stat_of_family_gt_one]]; the remaining regime $s=1$, $c<1$ is the
same argument at the explicit threshold.

Each conclusion is drawn from the cut balance directly, without constructing the chain as a
stochastic process.
