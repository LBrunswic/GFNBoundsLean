#!/usr/bin/env python3
"""Replay every declaration of the strict library through the kernel, module by module.

`lake build` certifies that the *elaborator* accepted the library. It does not certify that the
declarations in the resulting environment were reached by proof rather than by metaprogramming:
the environment is whatever the elaborator put there. `leanchecker` (shipped with the toolchain
since v4.28; the standalone `lean4checker` was archived 2026-03-25) replays declarations through
the kernel from the `.olean` files, which is the check that closes that gap.

**Why per module, and not `leanchecker GFNBounds`.** Naming the root replays every module in the
environment at once and holds them all, and the cost is superlinear in a way that matters here:
one module peaks at 5.9 GB, eight at 31.6 GB, and the whole library was killed by the OOM killer
at 42 GB on a 45 GB machine (2026-09-08). Per module the peak is flat at ~5.9 GB and the wall
time is ~3.6 s regardless of how many declarations the module carries, because the cost is
dominated by loading the environment rather than by the replay. So the work parallelises across
processes and does not parallelise inside one.

**What this does and does not certify.** It replays the declarations of every `GFNBounds.*`
module. It does *not* re-verify Mathlib, whose `.olean`s are imported and trusted -- Mathlib runs
this same check in its own CI, and re-verifying it here would cost the 42 GB that does not fit.
So the claim is: given Mathlib, every declaration of the strict library is kernel-accepted.

Run by `make audit`. Exits non-zero naming every module that failed.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "GFNBounds"

# One replay peaked at 5.9 GB in measurement. Four at a time is 24 GB, which leaves room on a
# 45 GB machine; raise it with --jobs on a bigger one, and note that the failure mode of raising
# it too far is the OOM killer rather than a clean error.
DEFAULT_JOBS = 4


def modules() -> list[str]:
    """Every module of the strict library, as Lean names.

    `GFNBounds.lean` itself is excluded: it declares nothing and only imports, so naming it is
    the whole-library invocation this script exists to avoid.
    """
    out = []
    for p in sorted(LIB.rglob("*.lean")):
        rel = p.relative_to(ROOT).with_suffix("")
        out.append(".".join(rel.parts))
    return out


def replay(module: str) -> tuple[str, int, str]:
    proc = subprocess.run(
        ["lake", "env", "leanchecker", module],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    return module, proc.returncode, (proc.stdout + proc.stderr).strip()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("REPLAY_JOBS", DEFAULT_JOBS)))
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    mods = modules()
    if not mods:
        print("kernel_replay: no modules found under GFNBounds/", file=sys.stderr)
        return 1

    failures: list[tuple[str, int, str]] = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for i, (module, code, output) in enumerate(pool.map(replay, mods), 1):
            if code != 0:
                failures.append((module, code, output))
                print(f"kernel_replay: FAIL {module} (exit {code})", file=sys.stderr)
                if output:
                    print("  " + output.replace("\n", "\n  "), file=sys.stderr)
            elif not args.quiet and i % 20 == 0:
                print(f"kernel_replay: {i}/{len(mods)} modules replayed")

    if failures:
        print(
            f"kernel_replay: {len(failures)} of {len(mods)} modules failed kernel replay",
            file=sys.stderr,
        )
        return 1

    print(f"kernel_replay: {len(mods)} modules, every declaration kernel-accepted "
          f"(Mathlib imported and trusted)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
