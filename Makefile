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

.PHONY: check build scaffold audit map kb appendix clean

check: build scaffold audit

build:
	lake build GFNBounds 2>&1 | tee build.log

scaffold:
	lake build GFNBoundsScaffold 2>&1 | tee -a build.log

audit:
	python3 scripts/sorry_audit.py
	python3 scripts/axiom_audit.py build.log
	python3 scripts/root_closure.py
	lake env lean scripts/AxiomSweep.lean
	python3 scripts/trace_check.py
	python3 scripts/coverage.py
	python3 scripts/repo_map.py
	python3 scripts/kb.py lint
	python3 scripts/kb.py index

# The map of the library that a sub-session reads before it touches anything.
map:
	python3 scripts/repo_map.py

# The draft replacement for Appendix H, generated from the Lean development: statements
# translated from the Lean statements, sketches drawn from the Lean proofs, and both checked
# against the compiled environment by `--lint`. Deliberately NOT part of `check`: it needs a
# TeX Live and `pip install leanblueprint`. Requires a current build, since the first step
# reads the environment. See blueprint/README.md.
appendix:
	lake env lean scripts/lean_facts.lean
	python3 scripts/appendix.py --paper --graph
	python3 scripts/appendix.py --lint
	dot -Tsvg docs/lean-graph.dot -o docs/lean-graph.svg
	leanblueprint pdf
	leanblueprint web

# The knowledge base: validate every entry, then regenerate the index.
kb:
	python3 scripts/kb.py lint
	python3 scripts/kb.py index

clean:
	rm -f build.log
