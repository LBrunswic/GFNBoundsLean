# The gate. `make check` is what pre-push runs.
#
# Lake's post-build hooks are awkward at v4.31, so the audits are driven from here rather than
# from the lakefile. `lake build GFNBounds` alone already certifies the strict library is
# sorry-free: it is built with `warningAsError := true`, which turns Lean's own
# "declaration uses 'sorry'" warning into an error.

.PHONY: check build scaffold audit clean

check: build scaffold audit

build:
	lake build GFNBounds 2>&1 | tee build.log

scaffold:
	lake build GFNBoundsScaffold 2>&1 | tee -a build.log

audit:
	python3 scripts/sorry_audit.py
	python3 scripts/axiom_audit.py build.log
	python3 scripts/trace_check.py
	python3 scripts/coverage.py

clean:
	rm -f build.log
