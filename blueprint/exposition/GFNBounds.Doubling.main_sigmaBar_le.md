---
declaration: GFNBounds.Doubling.main_sigmaBar_le
sig_sha256: ff95b20e19d40530
---

## statement

At $s=1$ and $0<c<1$, on the loop closure and on every truncation alike, the truncated expected
backward-trajectory lengths satisfy $\bar\sigma^{(n)}\leq\bar\jmath/(1-c)$ for every $n$.

## relation

The bound is uniform in the truncation, so the finiteness that repairs the condition of the
main text is not an artefact of the infinite chain: it survives every finite approximation of
it, which is what the measurements of a truncated system can be compared against.

## sketch

The same linear supersolution as above serves here, and the one place the truncation differs is
harmless: at a state whose doubling edge has been cut the decrement carries all the mass, and
the one-step equation becomes an inequality in the right direction, because $1\leq1/(1-c)$. The
induction and the target-row average then run unchanged [[GFNBounds.Doubling.sigmaBar_le]].
