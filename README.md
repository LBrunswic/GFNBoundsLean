# GFNBoundsLean

A Lean 4 / Mathlib formalization of the **proofs** of *Universality and Convergence of Generative
Flows* — **Appendices A, B and H**:

| appendix | source | what it is | statements |
|---|---|---|---|
| **A** | `proofs.tex` | the paper's proofs: universality, the stable bounds, the first variation, the frozen-policy dynamics, universality on finite graphs | 37 |
| **B** | `silva_comparison.tex` | the explicit-constant restatement of Silva et al.'s bound, and why its state-space dependence is unavoidable | 6 |
| **H** | `app_doubling.tex` | the doubling-graph counter-example: an unbounded diffusion operator at finite backward length | 41 |

The library began as Appendix H alone and was widened to A and B on 2026-09-08, at the author's
instruction. Appendices C–G are **not** in scope.

Coverage: **[`docs/COVERAGE.md`](docs/COVERAGE.md)**. Open `sorry`s:
[`docs/SORRY-STATUS.md`](docs/SORRY-STATUS.md). The whole-paper ledger — all 129 statements with
their natural-language status, their Lean status and the dependency DAG — lives on the paper side
at `FORMALIZATION-LEDGER.md`.

## Where it stands

The strict library is **`sorry`-free** and every one of its 1,800-odd declarations depends only
on `propext`, `Classical.choice` and `Quot.sound` (`scripts/AxiomSweep.lean`). The umbrella
theorem `theo:doubling_main` is assembled item by item in `Main.lean` from closed inputs; the
coverage table (`docs/COVERAGE.md`) says per statement what is closed, what is partial and why.
`theo:doubling_decay` and `theo:doubling_sharp` are unconditional from the cut balance and
positivity, with `m₀`, `ℓ₂`, `ℓ₃`, `c₃`, `c₄ = 16cτ`, `c₅`, `ω`, `ϑ` and `c₆` explicit
(`Decay.sharp_explicit`); `prop:doubling_unsolvable` is closed on Mathlib's `Lp`, and the `p = 2`
clauses of `theo:doubling_unbounded` on the same space (`UnboundedL2.lean`).

What is left divides into the **three obstructions** below, and every non-closed row in the
coverage table names which one stops it:

1. **A chain.** Mathlib v4.31.0 has no discrete-time Markov chain theory. Everything the appendix
   proves *about the chain as a process* — the labels *transient* and *null recurrent* in
   `prop:doubling_phase`, `E(σ | X₀ = j) = +∞` on the non-positive-recurrent rows, `E|Z_ℓ − 1|` in
   `lem:doubling_weight` (stated here in the transform form the sharp theorem consumes) — is
   either restated as what it is used for (existence or non-existence of an invariant
   probability; a bound on transforms) or not stated. What did **not** need a chain turned out to
   be most of the appendix: the decay and sharp blocks run on recursions, and Kac's formula
   (`Kac.lean`) is derived from invariance alone — the identity the lab record measures as
   `1/λ(s₀) − σ̄ ∈ [1.999999994526, 2.000000000004]`.
2. **The `L^p` layer with its adjoint** — **built.** `P` is modelled (`Stat.dens`, `Stat.densL2`),
   `P⋆ = P*` is Mathlib's adjoint (`Stat.adjoint_pstarL2`), the diffusion operator exists on every
   truncation (`Stat.exists_bhat`), and the mass layer and `Lp` are bridged both ways where the
   umbrella needs it (`RayleighBridge.lean`). What remains here is bookkeeping: the "in
   particular" clause of `lem:doubling_operator`(3) and a standalone unconditional item (2) of
   `cor:doubling_truncation`.
3. ~~Euler–Maclaurin~~ — **routed around.** `lem:doubling_expansion` was the appendix's one
   analytic wall, but the descent block consumes only `eq:doubling_R0`, and a first-order
   telescoping comparison suffices for that. `R0Bound.lean` proves
   `|R₀(m) − 1| ≤ 16cτ/m` at every `m ≥ 1`, with `½ ≤ R₀ ≤ 2` for `m ≥ 32cτ` — the paper's `c₄`
   and `ℓ₁`, made **effective**. The refined expansion is now needed only by
   `rem:doubling_parity` and by `rem:doubling_second_order`, which the paper does not prove either.

`theo:doubling_decay` is one lemma away from unconditional, and that lemma
(`lem:doubling_product`) now needs obstruction 1 alone. `prop:doubling_exponent` — the one
statement that needed neither obstruction — is closed at every real `p ≠ 0`.

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
  Lean statement is an `∃`.
- `rem:doubling_renewal`'s kernel-mean identity is exact for the limit equation only and does not
  determine `C`.

## Verification

`lake build GFNBounds` succeeding with zero warnings is itself the certificate that the strict
library is `sorry`-free. Beyond that, the formalized constants should agree with `exp20`
(`~/NonAcyclicGFN/results/exp20*.csv`), which measured this graph: `σ̄ = 6.000000` at `c = 0.25`
and `8.99991` at `c = 0.5` against `j̄/(1−c)` with `j̄ = 4.5`; fitted `p_*` of 4.130 / 2.659 /
1.719 / 1.269 against the predicted 4.1314 / 2.6599 / 1.7189 / 1.2691; cut balance exact to
`0.0e0`. Any Lean statement whose numerical instance disagrees is wrong.

## Working on this with sub-sessions

[`CLAUDE.md`](CLAUDE.md) is the standing brief every session loads. Four specialist sub-sessions
are defined in `.claude/agents/` and are dispatched by the master session:

| agent | for | writes? |
|---|---|---|
| `lean-formalizer` | a paper label with no Lean yet: signatures, docstring, hypothesis checklist, map wiring, tagged `sorry`s | scaffold + map |
| `lean-prover` | a stated declaration that needs closing | scaffold, one file |
| `mathlib-scout` | "does this lemma exist at the v4.31.0 pin, and what is it called" | no — read-only |
| `lean-auditor` | finished work, before graduation or commit | no — reports findings |

None of them may graduate a file into `GFNBounds/`, commit, or run `sorry_audit.py --accept`;
those stay with the master. They draw on two generated references and one accumulating one:

- [`docs/REPO-MAP.md`](docs/REPO-MAP.md) — orientation: loose ends, layer order, the
  general-purpose shelf, one line per file. Small enough to read whole.
- [`docs/REPO-INDEX.md`](docs/REPO-INDEX.md) — every declaration with its statement, plus the name
  index. Grepped, not read.
- [`kb/`](kb/README.md) — the knowledge base: patterns, pitfalls, obstructions and house rules
  learned while proving here. Each session reads it before starting and adds to it when it learns
  something that would have saved it time. `python3 scripts/kb.py search <terms>`.

`make map` and `make kb` regenerate the first two and validate the third; `make check` runs both.

## Relation to the draft

Nothing here edits `app_doubling.tex`. If formalization forces a change to a statement in the
draft, that change goes through `/writer`, like every other edit to the paper.

In the other direction, `blueprint/` holds a **draft replacement for Appendix H generated from
this development** — not from the appendix, whose prose proofs are not machine-checked:

```
make appendix       # -> blueprint/print/print.pdf, blueprint/appendix_H.tex, docs/lean-graph.svg
```

`scripts/lean_facts.lean` walks the compiled environment and records, for every declaration,
the project constants its proof term invokes. The fifteen results of `Doubling/Main.lean` are
then stated in English, sketched, and related to the main text in `blueprint/exposition/`, and
`scripts/appendix.py --lint` checks the writing against the environment: a sketch may not cite
a lemma the proof does not invoke, may not drop a named result it does, and goes stale the
moment its theorem changes shape. See [`blueprint/README.md`](blueprint/README.md).

This is a **draft for discussion** — replacing the appendix is a decision about the paper, so
it goes through `/writer` too.
