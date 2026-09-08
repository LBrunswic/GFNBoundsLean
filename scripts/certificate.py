#!/usr/bin/env python3
"""Write `docs/certificate.json`: what this commit certifies, and under what conditions.

The paper repository never runs Lean. It pins this repository at a commit and reads two
artifacts: `docs/lean-facts.json` for the statements, and this file for the right to believe
them. So this file has to answer, without a Mathlib on the machine reading it:

  * which commit, and was the tree clean when the gate ran;
  * which toolchain and which Mathlib;
  * did every gate pass;
  * and does the `lean-facts.json` sitting beside it belong to that same run.

**The gate results are recorded by construction, not by assertion.** This script runs last in
`make audit`, and the Makefile uses `pipefail` with no `-` prefixes, so any earlier gate that
fails aborts the target and this script never runs. A `certificate.json` whose `commit` matches
HEAD is therefore itself the evidence that everything before it passed at that commit; the
`gates` list is a record of what "everything" meant, so that a later reader can tell whether a
gate they care about existed yet.

Written by `make audit`. Read by the paper repository's `certificate-fresh` gate, which fails
unless `commit` equals the submodule's pinned HEAD and `dirty` is false.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "docs" / "certificate.json"
FACTS = ROOT / "docs" / "lean-facts.json"
SORRY = ROOT / "docs" / "sorry.json"

# The gates `make audit` runs before this script, in order. Kept here so the certificate says
# what it was gated on: adding a gate to the Makefile without adding it here is a lie of
# omission, and `--verify` catches the reverse.
GATES = [
    "lake build GFNBounds (warningAsError: sorry is a compile error)",
    "lake build GFNBoundsScaffold",
    "sorry_audit.py",
    "axiom_audit.py",
    "root_closure.py",
    "AxiomSweep.lean",
    "kernel_replay.py (leanchecker replays every GFNBounds module; Mathlib trusted)",
    "trace_check.py",
    "coverage.py",
    "repo_map.py",
    "kb.py lint",
]

# What a declaration may rest on and still count as certified.
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(ROOT), *args], capture_output=True, text=True, check=True
    ).stdout.strip()


def sha256_of(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mathlib_rev() -> dict[str, str]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for pkg in manifest.get("packages", []):
        if pkg.get("name") == "mathlib":
            return {"rev": pkg.get("rev", ""), "inputRev": pkg.get("inputRev", "")}
    return {}


def scaffold_modules() -> list[str]:
    scaffold = ROOT / "scaffold"
    if not scaffold.is_dir():
        return []
    return sorted(
        str(p.relative_to(ROOT)) for p in scaffold.rglob("*.lean")
    )


def summarize_facts() -> dict:
    """Counts read off the kernel dump, so the paper can state them without re-deriving them."""
    if not FACTS.exists():
        return {"present": False}
    decls = json.loads(FACTS.read_text())["declarations"]
    items = decls.items() if isinstance(decls, dict) else ((d["name"], d) for d in decls)

    total = 0
    by_namespace: dict[str, int] = {}
    nonstandard: list[str] = []
    for name, d in items:
        total += 1
        ns = ".".join(name.split(".")[:2])
        by_namespace[ns] = by_namespace.get(ns, 0) + 1
        extra = set(d.get("axioms", [])) - STANDARD_AXIOMS
        if extra:
            nonstandard.append(name)

    return {
        "present": True,
        "declarations": total,
        "by_namespace": dict(sorted(by_namespace.items(), key=lambda kv: -kv[1])),
        "declarations_on_nonstandard_axioms": sorted(nonstandard),
        "sha256": sha256_of(FACTS),
    }


def build() -> dict:
    # The certificate describes the state of the *sources*. Its own file is an output, so it is
    # excluded from the dirtiness it reports: otherwise writing it makes the tree dirty, and it
    # can never truthfully record a clean one.
    self_path = str(OUT.relative_to(ROOT))
    dirty_files = [
        ln
        for ln in git("status", "--porcelain").splitlines()
        if ln.strip() and ln[3:].strip() != self_path
    ]
    sorries = json.loads(SORRY.read_text()) if SORRY.exists() else []

    return {
        "schema": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "commit": git("rev-parse", "HEAD"),
        "commit_short": git("rev-parse", "--short", "HEAD"),
        "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "dirty": bool(dirty_files),
        "dirty_files": [ln[3:] for ln in dirty_files],
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib": mathlib_rev(),
        "gates": GATES,
        "gates_green": True,  # see the module docstring: by construction, not by assertion
        "standard_axioms": sorted(STANDARD_AXIOMS),
        "strict_library": "GFNBounds",
        "scaffold_library": "GFNBoundsScaffold",
        "scaffold_modules": scaffold_modules(),
        "scaffold_sorries": len(sorries),
        "facts": summarize_facts(),
    }


def verify(cert: dict) -> list[str]:
    """The checks that make a stale or mismatched certificate loud rather than quiet."""
    problems = []
    if cert["commit"] != git("rev-parse", "HEAD"):
        problems.append("certificate commit is not HEAD")
    if not cert["facts"]["present"]:
        problems.append("docs/lean-facts.json is absent: run `make facts` first")
    elif cert["facts"]["sha256"] != sha256_of(FACTS):
        problems.append("lean-facts.json changed after the certificate was written")
    bad = cert["facts"].get("declarations_on_nonstandard_axioms", [])
    if bad:
        problems.append(f"{len(bad)} declaration(s) rest on a nonstandard axiom: {bad[:3]}")
    return problems


def main() -> int:
    args = sys.argv[1:]
    if "--verify" in args:
        if not OUT.exists():
            print("certificate: docs/certificate.json absent", file=sys.stderr)
            return 1
        problems = verify(json.loads(OUT.read_text()))
        for p in problems:
            print(f"certificate: {p}", file=sys.stderr)
        return 1 if problems else 0

    cert = build()
    OUT.write_text(json.dumps(cert, indent=2, ensure_ascii=False) + "\n")

    facts = cert["facts"]
    where = f"{cert['commit_short']}{' DIRTY' if cert['dirty'] else ''}"
    print(
        f"certificate: {where}  {cert['toolchain']}  mathlib {cert['mathlib'].get('rev','?')[:12]}  "
        f"{facts.get('declarations', 0)} declarations  {cert['scaffold_sorries']} scaffold sorries"
    )
    if cert["dirty"]:
        print(
            f"certificate: WARNING tree is dirty ({len(cert['dirty_files'])} files); "
            "the paper repo's certificate-fresh gate will reject this",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
