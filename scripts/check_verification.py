#!/usr/bin/env python3
"""Run preserved exact verifiers and require byte-for-byte reference output."""

from concurrent.futures import ThreadPoolExecutor
import difflib
import os
from pathlib import Path
import subprocess
import sys

SCRIPTS = Path(__file__).resolve().parent
NAMES = ("counterexample", "sparse", "sympy", "claude_audit")


def check(name):
    stem = f"verify_rank2_poisson_{name}"
    expected = (SCRIPTS / f"{stem}.txt").read_bytes()
    env = dict(os.environ)
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONHASHSEED"] = "0"
    try:
        run = subprocess.run(
            [sys.executable, "-u", str(SCRIPTS / f"{stem}.py")],
            cwd=SCRIPTS.parent, env=env, capture_output=True, timeout=1200,
        )
    except subprocess.TimeoutExpired:
        return False, f"FAIL {stem}: timed out after 1200 seconds"
    if run.returncode != 0 or run.stdout != expected or run.stderr:
        diff = "".join(difflib.unified_diff(
            expected.decode().splitlines(keepends=True),
            run.stdout.decode(errors="replace").splitlines(keepends=True),
            fromfile=f"{stem}.txt (recorded)", tofile=f"{stem}.txt (fresh)",
        ))
        return False, (f"FAIL {stem}: exit {run.returncode}\n" + diff
                       + run.stderr.decode(errors="replace"))
    return True, f"PASS {stem}: exact output match"


def main():
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(check, NAMES))
    for _, report in results:
        print(report)
    return 0 if all(ok for ok, _ in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
