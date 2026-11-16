# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""Run every example script in this directory; exit non-zero if any fails.

Each script asserts the claims it prints, so a clean run is a test of the
book's computational statements.  Scripts are discovered (all *.py except
this file), run in sorted order, each in a fresh interpreter.
Usage: python3 examples/run_all.py [-v]
"""
import pathlib
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
TIMEOUT = 120                               # seconds per script (each targets <= 20 s)


def main():
    verbose = "-v" in sys.argv[1:]
    scripts = sorted(p for p in HERE.glob("*.py") if p.name != pathlib.Path(__file__).name)
    failed = []
    for p in scripts:
        t0 = time.time()
        try:
            r = subprocess.run([sys.executable, str(p)], capture_output=True, text=True,
                               timeout=TIMEOUT, cwd=HERE)
            ok, out = r.returncode == 0, r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            ok, out = False, f"timeout after {TIMEOUT} s"
        dt = time.time() - t0
        print(f"{'PASS' if ok else 'FAIL'}  {p.name:40} {dt:6.2f} s")
        if verbose or not ok:
            print(out)
        if not ok:
            failed.append(p.name)
    print(f"\n{len(scripts) - len(failed)}/{len(scripts)} passed")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
