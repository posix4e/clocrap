#!/usr/bin/env python3
"""Times clocrap against cloc and tokei on one directory, when they are installed.

Each tool runs RUNS times (default 3) and the best wall-clock time is reported,
with the code-line total each tool gives, so the speed and the numbers can be
compared together. The totals differ by design: the tools disagree about what
a comment is. Set CLOCRAP to a binary path to
benchmark a build that is not on PATH. Usage: scripts/bench.py [DIR]
"""

import json
import os
import shutil
import subprocess
import sys
import time

RUNS = int(os.environ.get("RUNS", "3"))


def best_time(command):
    """The fastest of RUNS runs, and the stdout of the last one."""
    best = None
    output = b""
    for _ in range(RUNS):
        start = time.perf_counter()
        result = subprocess.run(command, capture_output=True, check=True)
        elapsed = time.perf_counter() - start
        best = elapsed if best is None else min(best, elapsed)
        output = result.stdout
    return best, output


def clocrap_code(output):
    return json.loads(output)["total"]["code"]


def cloc_code(output):
    return json.loads(output)["SUM"]["code"]


def tokei_code(output):
    return json.loads(output)["Total"]["code"]


def main():
    target = sys.argv[1] if len(sys.argv) > 1 else "."
    tools = [
        ("clocrap", [os.environ.get("CLOCRAP", "clocrap"), "--json", target], clocrap_code),
        ("cloc", ["cloc", "--json", "--quiet", target], cloc_code),
        ("tokei", ["tokei", "--output", "json", target], tokei_code),
    ]
    print(f"{'tool':<10}{'best seconds':>14}{'code lines':>14}")
    for name, command, read_code in tools:
        if shutil.which(command[0]) is None:
            print(f"{name:<10}{'not installed':>28}")
            continue
        seconds, output = best_time(command)
        print(f"{name:<10}{seconds:>14.3f}{read_code(output):>14}")


if __name__ == "__main__":
    main()
