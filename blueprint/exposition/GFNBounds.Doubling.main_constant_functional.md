---
declaration: GFNBounds.Doubling.main_constant_functional
sig_sha256: f6bec6dd0d95adc8
---

## statement

At $s=1$ and $0<c<1$ there is a root $p>1$ of the Cramér equation $\psi_c(p)=0$ and there are
coefficients $\nu_1,\dots,\nu_d\geq0$ with $\sum_{j\leq d}\nu_j>0$ and $\nu_j=0$ whenever
$2j\leq d$, such that for \emph{every} invariant probability $\lambda$ of the loop closure,
\[ \lambda_m\,m^{p}\;\longrightarrow\;\sum_{j=1}^{d}\nu_j\,\lambda_j . \]

## relation

The constant of the tail asymptotic is thus a fixed non-negative linear functional of the
boundary data, the same functional for every invariant probability. The vanishing of $\nu_j$
for $2j\leq d$ says that the low half of the target row contributes nothing: only the states
the doubling edge can reach from above carry weight.

## sketch

The sequences satisfying the cut balance above $d$ form a real vector space, and restriction to
the first $d$ coordinates is an isomorphism onto $\mathbb R^{d}$ — that is the content of the
determinacy above. Each map $\lambda\mapsto\lambda_m m^{p}$ is linear in those coordinates, so
their limit is additive and positively homogeneous on the cone of positive sequences and
extends to a linear functional on the whole space; its coefficients are the $\nu_j$
[[GFNBounds.Doubling.Decay.constant_functional]]. Positivity of $\sum_j\nu_j$ comes from the
two-sided decay bound, and $\nu_j=0$ for $2j\leq d$ because no window above $d$ ever reads
those indices. The root and the parameters it determines are again
[[GFNBounds.Doubling.Decay.ofC]].
