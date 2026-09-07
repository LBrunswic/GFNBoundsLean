# GFNBoundsLean — standing rules

A Lean 4 / Mathlib formalization of **Appendix H** of *Universality and Convergence of Generative
Flows*: the doubling-graph counter-example of `app_doubling.tex`. Read `README.md` for what the
project is and where it stands. This file is what binds every session, master and sub-session
alike.

## Orientation, in reading order

| | |
|---|---|
| [`docs/REPO-MAP.md`](docs/REPO-MAP.md) | **Orientation.** Loose ends, layer order, the general-purpose shelf, one line per file. ~15 KB — read it whole. Generated. |
| [`docs/REPO-INDEX.md`](docs/REPO-INDEX.md) | **Where is the lemma I need.** Every declaration with its statement, and the name index. Large — `grep` it, do not read it. Generated. |
| [`kb/INDEX.md`](kb/INDEX.md) | **What working here is like.** Patterns, pitfalls, obstructions, house rules. Read before you start; write to it when you finish. |
| [`docs/COVERAGE.md`](docs/COVERAGE.md) | **How far it has got.** All 41 statements, status and difficulty bucket. Generated. |
| [`docs/SORRY-STATUS.md`](docs/SORRY-STATUS.md) | Every open `sorry`, keyed and justified. Generated. |
| `paper-map.json` | The traceability spine: label → tex span → LaTeX digest → Lean files and declarations → status, bucket, scope notes. |

The paper is at `/home/maxbrain/Dropbox/GFN Bounds/app_doubling.tex`. **Nothing here edits it.**
If formalizing forces a change to the draft, that change goes through `/writer`.

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

1. **A chain.** Mathlib v4.31.0 has no discrete-time Markov chain theory at all. *But check
   whether the statement really needs one* — `Kac.lean` and the whole decay block did not.
2. **The `L^p` layer with its adjoint.** The analysis is done; the functional analysis around it is
   not. An uncommitted spike sits at `GFNBounds/Doubling/LpLayer.lean`.
3. **Euler–Maclaurin — routed around.** `R0Bound.lean` gets `|R₀(m) − 1| ≤ 16cτ/m` by telescoping.
   Do not re-open it casually.

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
