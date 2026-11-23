#!/usr/bin/env python3
"""Time a certificate checker over certificate files and write Google Benchmark JSON.

Runs `<checker> FILE` (for example `lean/.lake/build/bin/zeno-check`, or
`build/release/zeno check`) on every `*.cert` file under the given
directories, --repetitions times each, and records the median wall time, the
child's peak RSS, the certificate size and the verdict (exit status 0 =
accepted). Same schema as bench/tools/run_suite.py, so
bench/tools/check_regression.py compares two runs.

Examples:
  bench/tools/time_checker.py --checker lean/.lake/build/bin/zeno-check \\
      --certs lean/test/certificates --out lean-check.json
  bench/tools/time_checker.py --checker "build/release/zeno check" \\
      --certs lean/test/certificates --out cpp-check.json
"""

import argparse
import datetime
import json
import os
import platform
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run_suite import run_measured  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--checker", required=True, help="checker command; the certificate path is appended")
    parser.add_argument("--certs", action="append", required=True, help="directory searched recursively for *.cert (repeatable)")
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=300.0)
    parser.add_argument("--machine", default=platform.node().split(".")[0])
    parser.add_argument("--out", required=True)
    opts = parser.parse_args()

    command = opts.checker.split()
    command[0] = str(Path(command[0]).resolve()) if Path(command[0]).exists() else command[0]
    files = sorted(p for d in opts.certs for p in Path(d).rglob("*.cert"))
    benchmarks = []
    for path in files:
        walls, rss, status, code = [], [], "ok", None
        for _ in range(opts.repetitions):
            st, wall, _cpu, peak, _out = run_measured(command + [str(path)], opts.timeout)
            status = st
            if st == "timeout":
                break
            walls.append(wall)
            if peak:
                rss.append(peak)
        name = f"{path.parent.name}/{path.stem}"
        entry = {
            "name": name,
            "family_index": len(benchmarks),
            "per_family_instance_index": 0,
            "run_name": name,
            "run_type": "iteration",
            "repetitions": len(walls),
            "repetition_index": 0,
            "threads": 1,
            "iterations": max(len(walls), 1),
            "real_time": 1000 * (statistics.median(walls) if walls else opts.timeout),
            "cpu_time": 1000 * (statistics.median(walls) if walls else opts.timeout),
            "time_unit": "ms",
            "certificate_bytes": path.stat().st_size,
            "verdict": "accepted" if status == "ok" else ("timeout" if status == "timeout" else "not accepted"),
        }
        if rss:
            entry["peak_rss_mib"] = max(rss) / (1024 * 1024)
        if status == "timeout":
            entry["error_occurred"] = True
            entry["error_message"] = "timeout"
        benchmarks.append(entry)
        print(f"{name:50s} {entry['real_time']:9.1f} ms  {entry['verdict']}", flush=True)

    context = {
        "date": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
        "host_name": opts.machine,
        "executable": " ".join(Path(command[0]).name if i == 0 else c for i, c in enumerate(command)),
        "num_cpus": os.cpu_count(),
        "mhz_per_cpu": 0,
        "cpu_scaling_enabled": False,
        "caches": [],
        "library_build_type": "release",
        "zs_runner": "bench/tools/time_checker.py",
    }
    Path(opts.out).parent.mkdir(parents=True, exist_ok=True)
    Path(opts.out).write_text(json.dumps({"context": context, "benchmarks": benchmarks}, indent=2) + "\n")


if __name__ == "__main__":
    main()
