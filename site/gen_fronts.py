#!/usr/bin/env python3
"""Compute the Pareto front of every catalogued instance, for the instance catalogue.

    python3 site/gen_fronts.py [--zeno build/release/zeno] [--timeout 30]

Writes `site/instances/fronts.json`, one compact JSON file loaded by `instances/index.qmd`, and
`site/instances/_catalogue.md`, the page's section per group (heading, description, an empty grid
that js/catalogue.js fills from the JSON), so that the headings reach the table of contents:

* the golden instances (`tests/golden/instances.txt`, `@DATA@` = `tests/golden/data`);
* every benchmark suite (`bench/instances/*.txt`, `@DATA@` = `bench/instances/data`);
* the metric instances of METRIC below (`zeno --metric`), one of them non-symmetric
  (`--hubs apart`), for which zeno prints achieved points and says on stderr whether they are
  the exact front or only a bracket (recorded as `exact` and `notes`).

Every front is the output of `zeno`, never typed. zeno solves each of these instances in well
under a second; `--timeout` only guards against a hung run.
"""

from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
from pathlib import Path

SITE = Path(__file__).resolve().parent
ROOT = SITE.parent
OUT = SITE / "instances" / "fronts.json"
PARTIAL = SITE / "instances" / "_catalogue.md"

# The groups, in catalogue order: id (the suite file's stem), title, description (Markdown).
GROUPS = [
    ("golden", "Golden instances",
     "Small symmetric instances ($t \\le 5$) whose fronts were also computed by the brute-force "
     "oracle (`tests/oracle`); zeno's regression tests compare against them. The `-C`/`-D` suffix of "
     "a name is historical: the arguments are what zeno runs."),
    ("paper-table1", "n = t, two planes", "$n = t$ cities and passengers, $p = 2$, default generator."),
    ("quick", "Quick suite", "The short suite run on every pull request."),
    ("regimes", "Regimes",
     "Many cities and few passengers; balanced; $p$ close to $t$; medium; large. Default generator "
     "($c_i = i$, $d_i = n + 1 - i$)."),
    ("families", "Generator families",
     "$n = 10$, $t = 8$, $p = 3$. `-C`/`-D`: 1 log, 2 sqrt, 3 identity, 4 power of two, 5 staircase; "
     "`-r` scales before truncation to integers."),
    ("adversarial", "Adversarial",
     "Instances where greedy rules fail or search is hard: the LPT counterexample, clustered and "
     "near-equal durations, multiples, and a 3-Partition gadget (12 cities forming four triples of "
     "sum 100, $t = 8$, $p = 4$)."),
    ("scaling-n", "Scaling: cities", "Number of cities $n$, with $t = 6$, $p = 3$."),
    ("scaling-t", "Scaling: passengers", "Number of passengers $t$, with $n = 8$, $p = 3$."),
    ("scaling-p", "Scaling: planes", "Number of planes $p$, with $n = 8$, $t = 13$."),
    ("scaling-D", "Scaling: duration magnitude",
     "The sqrt family scaled by `-r`, $n = 10$, $t = 8$, $p = 3$."),
    ("scaling-distinct", "Scaling: distinct durations",
     "Number of distinct durations among $n = 24$ cities, $t = 8$, $p = 3$."),
    ("metric", "Metric instances",
     "Points drawn at random (seeded) in the plane or on a sphere; every flight lasts the distance "
     "between its ends, so central flights satisfy the triangle inequality. With `--hubs apart`, "
     "$C_I$ and $C_G$ are two points and the instance is non-symmetric."),
]

# Metric (geographic) instances: name, arguments, comment.
METRIC = [
    ("plane-n12t8p3", "--metric plane --seed 2 -n 12 -t 8 -p 3 --random-costs 1,20", ""),
    ("plane-n20t12p4", "--metric plane --seed 1 -n 20 -t 12 -p 4 --random-costs 1,50", ""),
    ("sphere-n12t8p3", "--metric sphere --seed 1 -n 12 -t 8 -p 3 --random-costs 1,30",
     "Durations are great-circle distances in km, on a sphere of radius 6371 km."),
    ("plane-apart-n6t5p2", "--metric plane --hubs apart --seed 5 -n 6 -t 5 -p 2 --random-costs 1,20",
     "Non-symmetric: the two hubs are two different points."),
]


def parse_list(path: Path, data_dir: str) -> list[tuple[str, str, str]]:
    """[(name, arguments, comment)] of an instance list of `name|arguments` lines."""
    rows = []
    for line in path.read_text().splitlines():
        if "|" in line and not line.startswith("#"):
            name, args = line.split("|", 1)
            rows.append((name.strip(), args.strip().replace("@DATA@", data_dir), ""))
    return rows


def groups() -> list[dict]:
    out = []
    for gid, title, desc in GROUPS:
        if gid == "golden":
            source, rows = "tests/golden/instances.txt", parse_list(ROOT / "tests/golden/instances.txt", "tests/golden/data")
        elif gid == "metric":
            source, rows = "site/gen_fronts.py", METRIC
        else:
            source = f"bench/instances/{gid}.txt"
            rows = parse_list(ROOT / source, "bench/instances/data")
        out.append({"id": gid, "title": title, "description": desc, "source": source, "rows": rows})
    return out


def npt(args: list[str]) -> tuple[int, int, int]:
    val = {"-n": 3, "-t": 3, "-p": 2}  # zeno's defaults
    for i, a in enumerate(args[:-1]):
        if a in val:
            val[a] = int(args[i + 1])
    return val["-n"], val["-t"], val["-p"]


def run_zeno(zeno: str, args: str, timeout: float) -> tuple[list[list[int]], list[str]]:
    """The front printed by zeno (`cost makespan` lines) and the summary lines of its stderr
    (the per-gap details, indented, are dropped)."""
    proc = subprocess.run([zeno, *shlex.split(args)], cwd=ROOT, capture_output=True, text=True,
                          timeout=timeout, check=True)
    front = [[int(a), int(b)] for a, b in (l.split() for l in proc.stdout.splitlines() if l.strip())]
    notes = [l.strip() for l in proc.stderr.splitlines() if l.strip() and not l.startswith("  ")]
    return front, notes


def partial(gs: list[dict], instances: list[dict]) -> str:
    count = {g["id"]: sum(1 for i in instances if i["group"] == g["id"]) for g in gs}
    pts = sum(len(i["front"]) for i in instances)
    out = ["<!-- Generated by site/gen_fronts.py; do not edit. -->", "",
           f"{len(instances)} instances in {len(gs)} groups, {pts:,} front points in all.", ""]
    for g in gs:
        out += [f"## {g['title']} {{#{g['id']}}}", "",
                f"{g['description']} {count[g['id']]} instances; source `{g['source']}`.", "",
                f'::: {{.zs-cat data-group="{g["id"]}"}}', ":::", ""]
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--zeno", default=str(ROOT / "build/release/zeno"))
    ap.add_argument("--timeout", type=float, default=30.0, help="seconds per instance")
    ap.add_argument("--out", default=str(OUT))
    opt = ap.parse_args()

    gs = groups()
    instances, failed = [], []
    for g in gs:
        for name, args, comment in g["rows"]:
            try:
                front, notes = run_zeno(opt.zeno, args, opt.timeout)
            except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as e:
                failed.append(f"{g['id']}/{name}: {type(e).__name__}")
                continue
            n, t, p = npt(shlex.split(args))
            inst = {"group": g["id"], "name": name, "args": args, "n": n, "t": t, "p": p, "front": front}
            if comment:
                inst["comment"] = comment
            if notes:
                inst["notes"] = notes
                summary = next((s for s in notes if s.startswith("non-symmetric instance")), None)
                if summary:
                    inst["exact"] = summary.endswith("the front is exact")
            instances.append(inst)

    data = {"generator": "site/gen_fronts.py",
            "groups": [{k: g[k] for k in ("id", "title", "description", "source")} for g in gs],
            "instances": instances}
    out = Path(opt.out)
    out.write_text(json.dumps(data, separators=(",", ":"), ensure_ascii=False) + "\n")
    PARTIAL.write_text(partial(gs, instances))
    pts = sum(len(i["front"]) for i in instances)
    shown = out.relative_to(ROOT) if out.is_relative_to(ROOT) else out
    print(f"{shown}: {len(instances)} instances, {pts} points, {out.stat().st_size / 1024:.0f} KiB")
    for f in failed:
        print("failed:", f, file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
