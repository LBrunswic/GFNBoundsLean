# GFNBoundsLean

A Lean 4 / Mathlib formalization of **Appendix H** of *Universality and Convergence of Generative
Flows* — the doubling-graph counter-example of `app_doubling.tex`.

Coverage: **[`docs/COVERAGE.md`](docs/COVERAGE.md)** — 41 statements, what is closed and what is
not. Open `sorry`s: [`docs/SORRY-STATUS.md`](docs/SORRY-STATUS.md).

## What this is for

Appendix H is the paper's most contested mathematics and its most active. It was restructured on
2026-09-04 into an umbrella theorem plus ten promoted lemmas, then re-proved on 2026-09-05 with the
decay theorem redone via a descent chain and its constant via a Doeblin coupling — retiring a
Choquet–Deny route that had already been caught invoking a named theorem in a form more general
than the one that holds. The lab register's retraction list shows the pattern: on this material,
careful proof-checking has repeatedly found real errors *after* the claim was written down.

Two concrete goals, beyond the obvious one:

1. **Effectivize the constants.** `c₄` and `ℓ₁` are non-effective in the paper, and everything
   downstream inherits it — `ℓ₂, ℓ₃, ℓ₄, m₀, m₃, c₃, c₅, c₆, c₉, K₀, c₈`. Lean forces explicit
   values. This is where the author has already flagged the weakest link: `ϑ` is proved at 0.0024
   against a measured 0.22.
2. **Keep the flags.** Where the appendix says a thing is open, or formal, or non-explicit, this
   library says so too rather than laundering it. See *What is deliberately not claimed* below.

## Build

```
lake exe cache get      # Mathlib v4.31.0, rev fabf563a7c95
make check              # build both libraries, then the three audits
```

Mathlib is pinned to the same commit as `~/LeanAI/library`, so a lemma can migrate between the two
without a version fight.

## The two libraries, and the firewall between them

| | `GFNBounds/` | `scaffold/GFNBoundsScaffold/` |
|---|---|---|
| `sorry` | a **compile error** (`warningAsError := true`) | permitted, tagged, audited |
| default build target | yes | no |
| imports the other | never | freely |

Graduation is a file move. That is what makes "the sorry list only shrinks" enforceable by the
compiler rather than by discipline, for everything that has graduated.

Three audits back it up, run by `make check`:

- `scripts/sorry_audit.py` — every `sorry` in `scaffold/` must read
  `sorry -- SORRY(<paper label>): <reason>`. Bare ones fail. Each is keyed by a line-stable
  `sha1(label + decl)[:8]`, and the check fails if any id is new or the count rose. `--accept`
  rewrites the baseline as a deliberate, reviewable diff.
- `scripts/axiom_audit.py` — parses the `#print axioms` output of `GFNBounds/Audit.lean` and fails
  on `sorryAx` or any axiom outside `{propext, Classical.choice, Quot.sound}`. This is the
  anti-laundering check: `sorry` being a compile error in `GFNBounds` only catches a `sorry`
  written there, not one reached through an import.
- `scripts/trace_check.py` — see below.

## Traceability to the `.tex`

`paper-map.json` maps each of the 41 labels to its line span in `app_doubling.tex`, a **sha256 of
that statement's own LaTeX block** (statement plus proof, whitespace-normalised), the Lean files
and declarations certifying it, a status, a difficulty bucket, and scope notes.

`scripts/trace_check.py` enforces four invariants: the label still exists; every listed
declaration exists in its listed file; no Lean file cites a doubling label absent from the map;
and the digests are current. A changed LaTeX block flips that statement's status to `stale` and
prints what to do. Clearing it is deliberate:

```
python3 scripts/trace_check.py --reaffirm lem:doubling_percut
```

Digests are **per statement**, not per file, so editing `lem:doubling_doeblin` does not mark
`lem:doubling_percut` stale.

## Design: no Markov-chain theory is built

Mathlib v4.31.0 has no discrete-time Markov chain theory — no recurrence or transience, no Kac
formula, no stationary-distribution existence, no Perron–Frobenius, no coupling, no Doeblin, no
total-variation distance. Building that first would sink the project, and it is unnecessary,
because of how the appendix is written:

- `theo:doubling_decay` and `theo:doubling_sharp` are stated for **any positive real sequence
  satisfying the cut-balance recursion** — no invariance, no normalisation, no positive
  recurrence. That is `CutBalanceSeq` here, and `cor:doubling_truncation` needs it stated that way,
  since it feeds in `λ^K` extended past the cap by `1`.
- The descent chain is strictly decreasing and absorbed in at most `m` steps from a deterministic
  start, so every quantity from `lem:doubling_descent` through `lem:doubling_coupling` is a
  *finite* path expectation, and each of the paper's proofs is already "by induction on `y`".

So the chain is modelled concretely, each object is defined by the equation characterising it, and
probabilistic hypotheses stay hypotheses. Positive recurrence can remain open indefinitely without
blocking the headline: the statements that consume it take it as a hypothesis, exactly as the paper
does — here, as the existence of a `Stat`.

Three decisions carry most of the weight, and are argued in the module docstring of
`GFNBounds/Doubling/Setting.lean`:

- **`s₀` is the integer `0`** (`St.src` is `St.lad 0`), which is the paper's own convention, so the
  source is not a special case in any transition proof.
- **`P⋆` is total and in closed form**, not `∑' y, kern x y * f y`, so it carries no integrability
  side condition and every proof touching it is a case analysis.
- **`λ` is a real sequence**, not `ℝ≥0∞` or a `PMF`: 31 of the 41 statements are arithmetic on
  reals with subtraction and division throughout.

One thing `St` does *not* model is that the truncation at `K` is a chain on `K + 2` states while
`St` is infinite. States above the cap carry no incoming edge from within the truncated chain, so
`λ` vanishes there (`Stat.vanish`), and the per-cut identity is asserted `OnChain`. It genuinely
fails off-chain, and the docstring of `PerCutIdentity.lean` says where and why.

## What is deliberately not claimed

The appendix flags these itself; this library mirrors the flags rather than laundering them.

- `theo:doubling_main`(1) row (d), `c = 1/ln 2`: not positive recurrent, but null recurrence versus
  transience is **open in the paper**. Not stated here.
- Whether **weak** universality fails is open: `prop:doubling_unsolvable`(1) gives a *dense* range,
  so only *exact* `L²` flow matching is refuted.
- `rem:doubling_second_order` is explicitly "a formal matching computation and is not proved here".
- `prop:doubling_unsolvable`'s witness pair is non-explicit by construction (open mapping), so the
  Lean statement will be an `∃`.
- `rem:doubling_renewal`'s kernel-mean identity is exact for the limit equation only and does not
  determine `C`.

## Verification

`lake build GFNBounds` succeeding with zero warnings is itself the certificate that the strict
library is `sorry`-free. Beyond that, the formalized constants should agree with `exp20`
(`~/NonAcyclicGFN/results/exp20*.csv`), which measured this graph: `σ̄ = 6.000000` at `c = 0.25`
and `8.99991` at `c = 0.5` against `j̄/(1−c)` with `j̄ = 4.5`; fitted `p_*` of 4.130 / 2.659 /
1.719 / 1.269 against the predicted 4.1314 / 2.6599 / 1.7189 / 1.2691; cut balance exact to
`0.0e0`. Any Lean statement whose numerical instance disagrees is wrong.

## Relation to the draft

Nothing here edits `app_doubling.tex`. If formalization forces a change to a statement in the
draft, that change goes through `/writer`, like every other edit to the paper.
