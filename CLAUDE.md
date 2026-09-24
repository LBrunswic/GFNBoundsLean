# GFNBoundsLean — standing rules

A Lean 4 / Mathlib formalization of the **proofs** of *Universality and Convergence of Generative
Flows* — **Appendices A, B and H**. Read `README.md` for what the project is and where it stands.
This file is what binds every session, master and sub-session alike.

| appendix | source `.tex` | Lean namespace |
|---|---|---|
| **A** — the paper's proofs | `proofs.tex` | `GFNBounds.Core`, `GFNBounds.Graph` |
| **B** — the Silva comparison | `silva_comparison.tex` | `GFNBounds.Silva` |
| **H** — the doubling graph | `app_doubling.tex` | `GFNBounds.Doubling` |
| **I** — the Lean appendix (out of the paper build; digested since 2026-09-24) | `app_lean.tex` | restates `GFNBounds.Doubling`'s main theorems |

**Appendices C–G are not in scope.** The library began as Appendix H alone and was widened to A
and B on 2026-09-08 at the author's instruction; where a file, a script or a docstring still says
"Appendix H" as if it were the whole charter, that is a leftover and may be corrected.

**The body is traced too, since 2026-09-14** (author's ruling R2: "as many programmatic bindings
of the tex–Lean link as possible"). `scripts/paper.py`'s `SOURCES` lists the three appendix files
and the three body files (`universality.tex` S2, `cv_stable.tex` S3, `cv_divergence.tex` S4), so
`trace_check` digests all twelve body statements and its invariant (c) polices their labels. A
body row with an appendix twin (`theo:local_convergence` for `theo:local_convergence_full`, …)
carries the twin's files, declarations, status and bucket, and says so in its scope notes; the
twin's row carries the disclosures. The two body statements without a twin, `def:universality`
and `theo:no_bound_divergence`, have their own rows. This closes the gap recorded on 2026-09-12:
`theo:no_bound_divergence` was a closed certificate with no digest on this side, so a reworded
Theorem 5 would have left `make check` green. The paper-side ledger
(`FORMALIZATION-LEDGER.md`, all 131 statements) still cross-checks every mapped row.

**Appendix I is digested too, since 2026-09-24.** `SOURCES` gained `app_lean.tex` (I). Its two
statements, `def:lean_setting` and `theo:lean_main`, restate the doubling setting and main theorem in
the form the certificate carries. The paper-side ledger had counted them in scope since 2026-09-13
through curated links, so the two views disagreed on the count: 96 target rows there, 94 here. The
same day `theo:training_speed` left bucket B: its body form claims one sentence its twin lacks, the
DB instance through the edge lift, now certified by `Balance/TrainingSpeedDB.lean`. The ledger had
shown that row in A by inheriting its twin's bucket. Closure has read 96 of 96 on both sides since
then, and `formalization_ledger.py crosscheck` now compares buckets as well as statuses.

## Orientation, in reading order

| | |
|---|---|
| [`docs/REPO-MAP.md`](docs/REPO-MAP.md) | **Orientation.** Loose ends, layer order, the general-purpose shelf, one line per file. ~15 KB — read it whole. Generated. |
| [`docs/REPO-INDEX.md`](docs/REPO-INDEX.md) | **Where is the lemma I need.** Every declaration with its statement, and the name index. Large — `grep` it, do not read it. Generated. |
| [`kb/INDEX.md`](kb/INDEX.md) | **What working here is like.** Patterns, pitfalls, obstructions, house rules. Read before you start; write to it when you finish. |
| [`docs/COVERAGE.md`](docs/COVERAGE.md) | **How far it has got.** All 100 mapped statements — Appendix A's 39, B's 7, H's 40, I's 2 and the body's 12 — with status and difficulty bucket. Generated. |
| [`docs/SORRY-STATUS.md`](docs/SORRY-STATUS.md) | Every open `sorry`, keyed and justified. Generated. |
| `paper-map.json` | The traceability spine: label → tex span → LaTeX digest → Lean files and declarations → status, bucket, scope notes. |

The paper is at `/home/maxbrain/Dropbox/GFN Bounds/`; the three files in scope are
`proofs.tex`, `silva_comparison.tex` and `app_doubling.tex`. **Nothing here edits them.** If
formalizing forces a change to the draft, that change goes through `/writer`.

The whole-paper ledger — all 131 statements with natural-language status, Lean status and the
dependency DAG — is on the paper side at `FORMALIZATION-LEDGER.md` (generator
`formalization_ledger.py`, machine twin `formalization-ledger.json`). It reads `paper-map.json`
and never writes it. Use it to pick the next target: `python3 formalization_ledger.py ready`
lists what is unformalized and has every dependency closed. Since 2026-09-19 that queue is
**empty**. Closure is 96 of 96, and since 2026-09-24 the Lean map agrees row for row. New work here
comes from a change to the paper, or from the author widening the scope beyond Appendices A, B, H
and I.

## The five rules

1. **Never state more than the paper proves.** Where the appendix says a thing is open, formal, or
   non-explicit, this library says so too rather than laundering it. A `SCOPE (disclosed)` section
   and a `partial` status are the correct outputs of a partial result — a quietly weaker theorem
   under the paper's label is not. See `kb/entries/0005-never-outrun-the-paper.md`.
2. **The scaffold firewall.** `sorry` is a compile error in `GFNBounds/`; it is permitted, tagged
   and audited in `scaffold/GFNBoundsScaffold/`. `GFNBounds` never imports the scaffold.
   **Graduation is a file move, and it is the master session's decision.** Sub-sessions land work
   in the scaffold. See `kb/entries/0011-scaffold-firewall.md`.
3. **Constants are explicit formulas**, never a bare `∃ C`. Effectivization is one of the project's
   two goals; `c₄` and `ℓ₁` are the root that eleven downstream constants inherit from.
   See `kb/entries/0007-effective-constants.md`.
4. **Every claim is traceable.** A Lean file citing a paper label absent from `paper-map.json`
   fails `trace_check`. Adding a certificate means editing the map and `GFNBounds/Audit.lean` in
   the same change. See `kb/entries/0013-trace-map-upkeep.md`.
5. **`make check` is the gate.** Every audit passes before work is handed back.

## Build

```
lake exe cache get                        # Mathlib v4.31.0, rev fabf563a7c95
lake build GFNBounds.Doubling.Tail        # one module — the iteration loop
make check                                # build + scaffold + audits + generated docs
make map                                  # regenerate docs/REPO-MAP.md alone
```

`.lake/` is 7.5 GB. **Do not create a git worktree** for parallel work — it would re-fetch all of
it. Parallel sessions share this tree and must own **disjoint files**.

**This tree is worked in concurrently.** The lakefile globs `GFNBounds.*`, so every `.lean` under
the directory is built whether or not the root module imports it — which means uncommitted work by
another session is compiling alongside yours. `docs/REPO-MAP.md`'s *Loose ends* section lists what
is currently untracked or unimported. Read it before creating a file, and never assume the master
session knows those files exist.

`warningAsError := true` in the strict library: an unused variable or a deprecation is a build
failure. Fix it; do not suppress it.

## The three obstructions

Before accepting any task, check whether it sits behind one of these. If it does, say so and stop
rather than spending a session rediscovering it. `kb/entries/0006-three-obstructions.md` has the
detail, and `docs/COVERAGE.md`'s bucket column is the standing record.

1. **A chain — narrowed.** The pin has `Kernel.traj` (Ionescu–Tulcea), hitting times and bounded
   optional stopping, but no recurrence/transience classification, Foster criterion or strong
   Markov property. **No row is behind it any more.** The last two, `prop:doubling_phase` and the
   recurrence labels of `theo:doubling_main`(1), closed on 2026-09-19 as the least-solution classes
   of `RecurrenceClass.lean` under ruling R8, which builds no path space — the disclosure is in
   their scope notes. *Check whether the statement really needs a chain* — `Kac.lean`, the decay
   block and `DescentStatement.lean`'s pathwise reading did not.
2. **The general measure layer** — the density action on `L^p(λ)` for an arbitrary kernel with its
   `λ`-reversal and adjoint, a Radon–Nikodym calculus on `𝓜⁺`, disintegration. The doubling
   instances are done (`LpLayer.lean`, committed); what remains is the generality Appendix A states.
3. **Euler–Maclaurin — no longer a wall.** The pin has `trapezoidal_error_le`, which gives the
   second-order window sum `lem:doubling_expansion` needs; `R0Bound.lean`'s first-order telescoping
   stands as it is.

**A defect found and repaired (2026-09-13):** `Balance/Flow.lean`'s `IsGradientFlow` asked the ODE
at every real `t` and had no solution from a non-balanced start, so every theorem hypothesising it
was vacuous there. It now asks `0 ≤ t` (author's approval); 17 auxiliary signatures gained a
`0 ≤ t` or lost their negative times, no paper-level statement changed. Existence of a forward
solution — the inhabitation the repair left owed, and a theorem about solutions of a predicate is
only as good as it — is **proved since 2026-09-19** in `Balance/FlowExistence.lean`, with
uniqueness and positivity, on a finite ergodic chain for both generators. `kb/entries/0025` has
the detail, and the lesson outlives the instance.

## The team

Four sub-sessions, defined in `.claude/agents/`. The master session dispatches them and owns
everything they are not allowed to do: graduating a file into `GFNBounds/`, `git commit`,
`sorry_audit.py --accept`, and any change to `app_doubling.tex`'s status in the map that is not a
straightforward consequence of work just done.

| agent | for | writes? |
|---|---|---|
| `lean-formalizer` | a paper label with no Lean yet: signatures, docstring, checklist, map wiring, tagged `sorry`s | scaffold + map |
| `lean-prover` | a stated declaration that needs closing | scaffold, one file |
| `mathlib-scout` | "does this lemma exist, and what is it called at this pin" | no — read-only |
| `lean-auditor` | finished work, before graduation or commit | no — reports findings |

**Dispatch shape.** Give the agent the paper label, the file it owns, and the boundary:

> `lean-prover`: close `product_bound` in
> `scaffold/GFNBoundsScaffold/Doubling/Product.lean`, certifying `lem:doubling_product`
> (`app_doubling.tex:1110–1153`). You own that file only. Report what you closed, what you did not,
> and whether the statement still matches the paper.

Run `mathlib-scout` in parallel with a prover when the question is "does this exist" — it is
read-only and cannot conflict. Never run two provers on the same file. Run `lean-auditor` on work
before graduating it, and prefer an auditor that did not write the proof.

**Every sub-session ends by asking whether it learned something worth a KB entry.** That is the
mechanism by which this repository gets easier to work in; `kb/README.md` says what earns one and,
just as importantly, what does not.
