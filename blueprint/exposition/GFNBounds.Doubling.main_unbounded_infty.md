---
declaration: GFNBounds.Doubling.main_unbounded_infty
sig_sha256: 740a44b122c9ba51
---

## statement

Let $\varepsilon_{c,s}$ be a member of the family with $c>0$ and let $\lambda$ be an invariant
probability of the loop closure. There is no constant $B$ such that every bounded mean-zero
$f$, attaining size $M$ somewhere and having flow-matching defect bounded uniformly by $D$,
satisfies $M\leq B\,D$.

## relation

The failure therefore reaches the uniform norm as well, where the main text's stable bounds are
most often read. No hypothesis on $s$ is needed: above $s=1$ the clipped ramps do the work, and
below it there is no invariant probability at all, so the claim is vacuous exactly where the
objects it quantifies over do not exist.

## sketch

The witnesses are clipped ramps: $r_N$ is the ladder height cut off at $N$. Its
flow-matching defect is bounded independently of $N$ — at a state below the clip the defect is
$1-\varepsilon(j)(j+1)$, at a state above it the defect vanishes, and at the sink it is
$-\bar\jmath$ — while centring leaves the defect unchanged and leaves the function attaining at
least $N/2$. So $M/D$ grows without bound
[[GFNBounds.Doubling.Stat.no_bounded_inverse_infty]].

That the defect is bounded uses $\gamma=\sup_j(j+1)\varepsilon(j)<\infty$, which for this
family holds exactly when $s\geq1$, with $\gamma=c\,2^{1-s}$
[[GFNBounds.Doubling.gamma_family]]. Below $s=1$ there is no invariant probability to quantify
over [[GFNBounds.Doubling.isEmpty_stat_of_family_lt_one]], and the statement holds for that
reason instead.
