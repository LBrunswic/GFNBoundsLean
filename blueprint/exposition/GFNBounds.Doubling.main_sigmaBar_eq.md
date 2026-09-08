---
declaration: GFNBounds.Doubling.main_sigmaBar_eq
sig_sha256: f48617e30e10c2da
---

## statement

At $s=1$ and $0<c<1$ the expected backward-trajectory length of the loop closure is exactly
\[ \bar\sigma \;=\; \frac{\bar\jmath}{1-c}, \]
the supremum of the truncated expectations $\bar\sigma^{(n)}$.

## relation

This is the quantity Morozov et al.\ (2025) require to be finite, and on this graph it is
finite throughout the positive recurrent regime at $s=1$. It is the first half of the
separation this appendix is for: the condition of the main text that is repaired here.

## sketch

The linear function $h(x)=x/(1-c)$ is an exact solution of the one-step equation at $s=1$: the
substitution $\varepsilon(j)=c/(j+1)$ collapses the average of the state after one step to
$c+j-1$, and $1+h(c+j-1)=h(j)$. A non-negative solution of that equation dominates the
truncated hitting-time expectations by induction, and the constant drift $c-1$ makes the
inequality an equality in the limit [[GFNBounds.Doubling.sbar_iSup_eq]]. Averaging over the
target row, whose mean is $\bar\jmath$ and on which $h$ is linear, gives the stated value.
