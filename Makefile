# The gate. `make check` is what pre-push runs.
#
# bash with pipefail, so that `lake build … | tee` fails when lake fails (until 2026-09-07 the
# exit status was tee's, and a compile error could only be caught indirectly).
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c
#
# Lake's post-build hooks are awkward at v4.31, so the audits are driven from here rather than
# from the lakefile. `lake build GFNBounds` alone already certifies the strict library is
# sorry-free: it is built with `warningAsError := true`, which turns Lean's own
# "declaration uses 'sorry'" warning into an error.
#
# `lake build` trusts the environment the elaborator produced. `kernel_replay.py` drives
# `leanchecker` (toolchain-shipped since v4.28; the standalone lean4checker was archived
# 2026-03-25) over one module at a time, replaying every declaration through the kernel from the
# .olean files -- which is what rules out an environment reached by metaprogramming rather than
# by proof. Per module, not whole-library: the whole library at once was OOM-killed at 42 GB.
# 84 modules, 90 seconds, 6.2 GB peak. Mathlib is imported and trusted; it runs this in its own CI.

.PHONY: check build scaffold audit certificate map kb facts appendix browser dashboard deploy clean

check: build scaffold audit certificate

build:
	lake build GFNBounds 2>&1 | tee build.log

scaffold:
	lake build GFNBoundsScaffold 2>&1 | tee -a build.log

audit:
	python3 scripts/sorry_audit.py
	python3 scripts/axiom_audit.py build.log
	python3 scripts/root_closure.py
	lake env lean scripts/AxiomSweep.lean
	python3 scripts/kernel_replay.py
	python3 scripts/trace_check.py
	python3 scripts/coverage.py
	python3 scripts/repo_map.py
	python3 scripts/kb.py lint
	python3 scripts/kb.py index

# What this commit certifies, for a reader with no Mathlib: the commit, the toolchain, the
# Mathlib rev, the gates it passed, and the sha256 of the lean-facts.json beside it. Depends on
# `facts` because a certificate that does not pin the statement dump certifies nothing the paper
# can use. This is the artifact the paper repository's `certificate-fresh` gate reads.
#
# It runs LAST in `check`, and the gate results are recorded by construction: with pipefail and
# no `-` prefixes, any earlier failure aborts before this ever runs.
certificate: facts
	python3 scripts/certificate.py

# The map of the library that a sub-session reads before it touches anything.
map:
	python3 scripts/repo_map.py

# The draft replacement for Appendix H, generated from the Lean development: statements
# translated from the Lean statements, sketches drawn from the Lean proofs, and both checked
# against the compiled environment by `--lint`. Deliberately NOT part of `check`: it needs a
# TeX Live and `pip install leanblueprint`. Requires a current build, since the first step
# reads the environment. See blueprint/README.md.
# The compiled environment, dumped to docs/lean-facts.json. Must run from the repo root:
# scripts/lean_facts.lean writes a relative path. Shared by `appendix` and `browser`, which
# is why it is factored out -- it was being paid twice.
facts:
	lake env lean scripts/lean_facts.lean

appendix: facts
	python3 scripts/appendix.py --paper --graph
	python3 scripts/appendix.py --lint
	dot -Tsvg docs/lean-graph.dot -o docs/lean-graph.svg
	leanblueprint pdf
	leanblueprint web

# The knowledge base: validate every entry, then regenerate the index.
kb:
	python3 scripts/kb.py lint
	python3 scripts/kb.py index

# The formal statement browser: every declaration as the kernel elaborated it, with both
# directions of its dependency edges. Like `appendix`, deliberately NOT part of `check` --
# it needs its own pass over the whole environment. The generator refuses to run against a
# lean-facts.json older than any source file, so `browser/` cannot be quietly stale.
browser: facts
	python3 scripts/lean_browser.py --verify

# The static site node1 serves: the blueprint, the generated docs, and the headline numbers.
# Reads artefacts only — `make check` and `make appendix` are what produce them, so a dashboard
# built on a stale tree is stale rather than wrong.
dashboard:
	python3 scripts/dashboard.py

# Ship it. Refuses a tree whose gate is not green; `FORCE=1 make deploy` overrides.
# PUBLIC AND UNAUTHENTICATED by the author's instruction — see nginx/gfnbounds-blueprint.conf.
deploy: dashboard
	scripts/deploy.sh

clean:
	rm -f build.log
	rm -rf dashboard
