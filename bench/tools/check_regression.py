#!/usr/bin/env python3
"""Compare two benchmark JSON files and fail on regressions.

Both files use the Google Benchmark JSON schema (component benchmarks with
--benchmark_out, or bench/tools/run_suite.py). Entries are matched by name;
aggregate rows other than the median are ignored, and so are entries with an
error in either file (a timeout in the baseline cannot regress).

A benchmark regresses when its time (real_time, in the file's unit) or its
peak_rss_mib counter grows by more than --threshold (default 10%) and by more
than the absolute noise floor --min-delta-ms / --min-delta-mib. It also fails
when an entry that succeeded in the baseline now has an error or a different
front_size.

Exit status: 0 no regression, 1 regression, 2 usage error.
"""

import argparse
import json
import sys

UNIT_TO_MS = {"ns": 1e-6, "us": 1e-3, "ms": 1.0, "s": 1e3}


def load(path):
    rows = {}
    for b in json.load(open(path))["benchmarks"]:
        if b.get("run_type") == "aggregate" and b.get("aggregate_name") != "median":
            continue
        name = b.get("run_name", b["name"]) if b.get("run_type") == "aggregate" else b["name"]
        rows[name] = b
    return rows


def time_ms(b):
    return b["real_time"] * UNIT_TO_MS[b.get("time_unit", "ns")]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("baseline")
    parser.add_argument("current")
    parser.add_argument("--threshold", type=float, default=0.10)
    parser.add_argument("--min-delta-ms", type=float, default=1.0)
    parser.add_argument("--min-delta-mib", type=float, default=1.0)
    opts = parser.parse_args()

    base, cur = load(opts.baseline), load(opts.current)
    failures, compared = [], 0
    for name, b in sorted(base.items()):
        c = cur.get(name)
        if c is None or b.get("error_occurred"):
            continue
        if c.get("error_occurred"):
            failures.append(f"{name}: {c.get('error_message', 'error')} (baseline {time_ms(b):.2f} ms)")
            continue
        compared += 1
        tb, tc = time_ms(b), time_ms(c)
        if tc > tb * (1 + opts.threshold) and tc - tb > opts.min_delta_ms:
            failures.append(f"{name}: time {tb:.2f} -> {tc:.2f} ms (+{100 * (tc / tb - 1):.0f}%)")
        mb, mc = b.get("peak_rss_mib"), c.get("peak_rss_mib")
        if mb and mc and mc > mb * (1 + opts.threshold) and mc - mb > opts.min_delta_mib:
            failures.append(f"{name}: peak RSS {mb:.1f} -> {mc:.1f} MiB (+{100 * (mc / mb - 1):.0f}%)")
        if "front_size" in b and b.get("front_size") != c.get("front_size"):
            failures.append(f"{name}: front size {b['front_size']} -> {c.get('front_size')}")

    print(f"compared {compared} benchmarks, {len(failures)} regressions (threshold {100 * opts.threshold:.0f}%)")
    for line in failures:
        print("  " + line)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
