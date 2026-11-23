#!/usr/bin/env python3
"""Time a solver executable over instance suites and write Google Benchmark JSON.

Each suite file in bench/instances has lines `name|arguments`; `@DATA@` in the
arguments expands to bench/instances/data. Every instance is run --repetitions
times; the entry records the median wall and CPU time, the peak resident set
size of the child process, the front size (number of non-empty stdout lines when
the solver prints its front) and a status (ok, timeout, error). An instance that
times out is not repeated.

The output follows the schema of Google Benchmark's --benchmark_out=json, so
benchmark's tools/compare.py and bench/tools/check_regression.py read it.

Examples:
  bench/tools/run_suite.py --exe build/bench/zeno \\
      --suite bench/instances/regimes.txt --timeout 120 \\
      --out bench/baselines/zeno/apple-m4-max/zeno.json --machine apple-m4-max
"""

import argparse
import datetime
import json
import os
import platform
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "bench" / "instances" / "data"


def read_suite(path):
    entries = []
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "|" not in line:
            continue
        name, args = line.split("|", 1)
        entries.append((name.strip(), args.replace("@DATA@", str(DATA)).split()))
    return entries


def run_measured(cmd, timeout):
    """Run cmd once; return (status, wall_s, cpu_s, peak_rss_bytes, stdout).

    The child is reaped with wait4, so its CPU time and peak RSS are its own.
    stdout goes to a temporary file, so a large front cannot block the child.
    """
    with tempfile.TemporaryFile(mode="w+") as out:
        start = time.perf_counter()
        proc = subprocess.Popen(cmd, stdout=out, stderr=subprocess.DEVNULL)
        deadline = start + timeout
        while True:
            pid, status, usage = os.wait4(proc.pid, os.WNOHANG)
            if pid != 0:
                break
            if time.perf_counter() > deadline:
                proc.kill()
                os.wait4(proc.pid, 0)
                proc.returncode = -9  # already reaped; keep Popen from waiting again
                return "timeout", float(timeout), None, None, ""
            time.sleep(0.001)
        wall = time.perf_counter() - start
        proc.returncode = os.waitstatus_to_exitcode(status)
        out.seek(0)
        text = out.read()
    rss = usage.ru_maxrss if sys.platform == "darwin" else usage.ru_maxrss * 1024
    return ("ok" if proc.returncode == 0 else "error"), wall, usage.ru_utime + usage.ru_stime, rss, text


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--exe", required=True, help="solver executable")
    parser.add_argument("--args", default="", help="extra arguments placed before the instance arguments (e.g. -F, or 'front')")
    parser.add_argument("--suite", action="append", required=True, help="suite file (repeatable)")
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=60.0, help="seconds per run")
    parser.add_argument("--machine", default=platform.node().split(".")[0], help="machine label stored in the context")
    parser.add_argument("--out", required=True, help="output JSON file")
    opts = parser.parse_args()

    exe = str(Path(opts.exe).resolve())
    extra = opts.args.split()
    benchmarks = []
    for suite in opts.suite:
        suite_name = Path(suite).stem
        for name, args in read_suite(suite):
            cmd = [exe] + extra + args
            walls, cpus, rss, status, front = [], [], [], "ok", None
            for _ in range(opts.repetitions):
                st, wall, cpu, peak, out = run_measured(cmd, opts.timeout)
                status = st
                if st != "ok":
                    break
                walls.append(wall)
                cpus.append(cpu)
                rss.append(peak)
                front = sum(1 for line in out.splitlines() if line.strip())
            entry = {
                "name": f"{suite_name}/{name}",
                "family_index": len(benchmarks),
                "per_family_instance_index": 0,
                "run_name": f"{suite_name}/{name}",
                "run_type": "iteration",
                "repetitions": len(walls),
                "repetition_index": 0,
                "threads": 1,
                "iterations": max(len(walls), 1),
                "real_time": 1000 * (statistics.median(walls) if walls else opts.timeout),
                "cpu_time": 1000 * (statistics.median(cpus) if cpus else opts.timeout),
                "time_unit": "ms",
                "status": status,
                "arguments": " ".join(extra + args).replace(str(DATA), "@DATA@"),
            }
            if rss:
                entry["peak_rss_mib"] = max(rss) / (1024 * 1024)
            if front is not None:
                entry["front_size"] = front
            if status != "ok":
                entry["error_occurred"] = True
                entry["error_message"] = status if status == "timeout" else "non-zero exit status"
            benchmarks.append(entry)
            shown = f"{entry['real_time']:.1f} ms" if status == "ok" else status
            print(f"{entry['name']:40s} {shown:>14s}  front={front}", flush=True)

    context = {
        "date": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
        "host_name": opts.machine,
        "executable": Path(exe).name,
        "num_cpus": os.cpu_count(),
        "mhz_per_cpu": 0,
        "cpu_scaling_enabled": False,
        "caches": [],
        "library_build_type": "release",
        "zs_runner": "bench/tools/run_suite.py",
        "zs_timeout_s": opts.timeout,
        "zs_platform": f"{platform.system()} {platform.machine()}",
    }
    Path(opts.out).parent.mkdir(parents=True, exist_ok=True)
    Path(opts.out).write_text(json.dumps({"context": context, "benchmarks": benchmarks}, indent=2) + "\n")


if __name__ == "__main__":
    main()
