#!/usr/bin/env python3
"""Score a planner's runs against the exact Pareto front of a MultiZenoTravel instance.

    score_front.py FRONT RUN [RUN ...] [--floor-makespan] [--ref R] [--json]

FRONT is the exact front: a problem file written by `zeno pddl` (its trailing comments list the
front, as `makespan cost` lines), or a text file of `cost makespan` lines (the output of
`zeno front`, or tests/golden/fronts/*.front).

Each RUN is one run of the planner, scored on its own:
  - a file of `cost makespan` lines (blank lines and lines starting with # are skipped);
  - a plan file in the IPC format, one action per line (`0.000: (fly plane1 city0 city1) [2.000]`),
    which counts as one point: its cost is the sum of (citythreat ?to) over its fly actions, read
    from FRONT, which must then be a problem file, and its makespan is the end of its last action;
  - a directory, whose files are read as above and pooled into one run (a planner that writes one
    plan per point of its front).

For each run the script prints:
  points      the points read;
  found       the points of the exact front that the run reaches, out of |F|;
  hv          the hypervolume of the run's points over that of the exact front: 1 is best;
  eps         the additive epsilon indicator: how far, in normalized units, the run's points must
              move for every point of the exact front to be weakly dominated: 0 is best;
  impossible  points that no plan achieves, because they are better than the exact front. They
              come from an invalid plan or a makespan measured another way; they are left out of
              hv and eps, and the exit status is 1.

Normalization: cost and makespan are mapped to [0, 1] by the ideal and nadir points of the exact
front (a range of 0, for a front of one point, counts as 1). The hypervolume reference point is
(r, r) with r = 1 + 1/(|F| - 1), and r = 2 for |F| = 1 (Ishibuchi et al., "How to specify a
reference point in hypervolume calculation for fair performance comparison", Evolutionary
Computation 26(3), 2018): for points evenly spread on a line, the volume that only an end of
the front dominates then equals the volume that only a point between them dominates.
--ref R sets r instead. Points beyond the reference point add no volume.

Makespans: durations are integers, so a plan's makespan is an integer. PDDL 2.1 planners separate
dependent actions by a small epsilon and report M + k*epsilon; --floor-makespan rounds makespans
down, which recovers M while k*epsilon < 1. Validate plans with VAL: this script reads the points,
it does not check the plans.

Exit status: 0 scored, 1 a run has impossible points, 2 usage or input error.
"""

import argparse
import json
import math
import os
import re
import sys

EPS = 1e-9
FRONT_HEADER = re.compile(r"^\s*;\s*Pareto points\b", re.IGNORECASE)
COMMENT_PAIR = re.compile(r"^\s*;\s*(-?[\d.]+)\s+(-?[\d.]+)\s*$")
CITYTHREAT = re.compile(r"\(\s*=\s*\(\s*citythreat\s+(\S+)\s*\)\s*(-?[\d.]+)\s*\)", re.IGNORECASE)
PLAN_ACTION = re.compile(r"^\s*(-?[\d.]+)\s*:\s*\(([^)]*)\)\s*(?:\[\s*(-?[\d.]+)\s*\])?")
TIMETERRE = re.compile(r"\(\s*=\s*\(\s*timeTerre\s+(\S+)\s+(\S+)\s*\)\s*(-?[\d.]+)\s*\)", re.IGNORECASE)


class InputError(Exception):
    pass


def number(text):
    value = float(text)
    return int(value) if value.is_integer() else value


def read_pairs(lines, path):
    """`cost makespan` lines; blank lines and # comments skipped."""
    points = []
    for k, line in enumerate(lines, 1):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        fields = line.replace(",", " ").split()
        if len(fields) != 2:
            raise InputError(f"{path}:{k}: expected `cost makespan`, got {line!r}")
        try:
            points.append((number(fields[0]), number(fields[1])))
        except ValueError:
            raise InputError(f"{path}:{k}: not two numbers: {line!r}") from None
    return points


class Problem:
    """The exact front, and for a problem file the landing costs and the flight durations."""

    def __init__(self, path):
        with open(path, encoding="utf-8") as f:
            lines = f.read().splitlines()
        self.path = path
        self.threat = {}
        self.duration = {}
        text = "\n".join(lines)
        if "(define" in text:
            self.threat = {c.lower(): number(v) for c, v in CITYTHREAT.findall(text)}
            self.duration = {(a.lower(), b.lower()): number(v) for a, b, v in TIMETERRE.findall(text)}
            self.front = self._front_from_comments(lines)
        else:
            self.front = read_pairs(lines, path)
        if not self.front:
            raise InputError(f"{path}: no front points")
        self.front = sorted(set(self.front))

    def _front_from_comments(self, lines):
        for i, line in enumerate(lines):
            if FRONT_HEADER.match(line):
                front = []
                for later in lines[i + 1:]:
                    m = COMMENT_PAIR.match(later)
                    if not m:
                        break
                    makespan, cost = number(m.group(1)), number(m.group(2))
                    front.append((cost, makespan))
                return front
        raise InputError(f"{self.path}: no `; Pareto points` comment; zeno pddl writes the front "
                         "for symmetric instances, without --no-front")

    def plan_point(self, lines, path):
        """(cost, makespan) of an IPC plan, or None when the lines are not a plan."""
        actions = [m for m in (PLAN_ACTION.match(line) for line in lines) if m]
        if not actions:
            return None
        if not self.threat:
            raise InputError(f"{path}: a plan needs FRONT to be a problem file (for citythreat)")
        cost, end = 0, 0
        for m in actions:
            start = float(m.group(1))
            words = m.group(2).split()
            name = words[0].lower() if words else ""
            duration = float(m.group(3)) if m.group(3) is not None else None
            if name == "fly":
                if len(words) != 4:
                    raise InputError(f"{path}: fly takes a plane and two cities: ({m.group(2)})")
                source, target = words[2].lower(), words[3].lower()
                if target not in self.threat:
                    raise InputError(f"{path}: no citythreat for {target} in {self.path}")
                cost += self.threat[target]
                if duration is None:
                    duration = self.duration.get((source, target))
                    if duration is None:
                        raise InputError(f"{path}: no duration for ({m.group(2)})")
            end = max(end, start + (duration or 0.0))
        return (cost, int(end) if float(end).is_integer() else end)


def read_run(path, problem):
    files = [path]
    if os.path.isdir(path):
        files = sorted(os.path.join(path, f) for f in os.listdir(path)
                       if not f.startswith(".") and os.path.isfile(os.path.join(path, f)))
        if not files:
            raise InputError(f"{path}: empty directory")
    points = []
    for f in files:
        with open(f, encoding="utf-8") as h:
            lines = h.read().splitlines()
        point = problem.plan_point(lines, f)
        points.extend([point] if point is not None else read_pairs(lines, f))
    return points


def nondominated(points):
    """The points that no other point weakly dominates (duplicates kept once), by increasing cost."""
    best = []
    for c, m in sorted(set(points)):
        if not best or m < best[-1][1] - EPS:
            best.append((c, m))
    return best


def hypervolume(points, ref):
    """Area dominated by the points and bounded by ref, for two objectives to minimize."""
    inside = nondominated([p for p in points if p[0] < ref[0] and p[1] < ref[1]])
    area = 0.0
    for i, (c, m) in enumerate(inside):
        right = inside[i + 1][0] if i + 1 < len(inside) else ref[0]
        area += (right - c) * (ref[1] - m)
    return area


def score(front, points, ref_coord=None):
    cmin, cmax = min(c for c, _ in front), max(c for c, _ in front)
    mmin, mmax = min(m for _, m in front), max(m for _, m in front)
    rc = (cmax - cmin) or 1
    rm = (mmax - mmin) or 1

    def norm(p):
        return ((p[0] - cmin) / rc, (p[1] - mmin) / rm)

    def achievable(p):
        return any(f[0] <= p[0] + EPS and f[1] <= p[1] + EPS for f in front)

    impossible = [p for p in points if not achievable(p)]
    valid = [p for p in points if achievable(p)]
    found = sum(1 for f in front if any(abs(f[0] - p[0]) <= EPS and abs(f[1] - p[1]) <= EPS for p in valid))
    r = ref_coord if ref_coord is not None else (1 + 1 / (len(front) - 1) if len(front) > 1 else 2.0)
    nf = [norm(f) for f in front]
    nv = [norm(p) for p in valid]
    hv = hypervolume(nv, (r, r)) / hypervolume(nf, (r, r))
    eps = max((min(max(a[0] - f[0], a[1] - f[1]) for a in nv) for f in nf), default=0.0) if nv else math.inf
    return {
        "points": len(points),
        "found": found,
        "front": len(front),
        "hv": hv,
        "eps": max(eps, 0.0),
        "impossible": [list(p) for p in impossible],
        "ref": r,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("front", help="the exact front: a `zeno pddl` problem file, or `cost makespan` lines")
    parser.add_argument("runs", nargs="+", help="a run: a file of `cost makespan` lines, an IPC plan, or a directory of either")
    parser.add_argument("--floor-makespan", action="store_true", help="round makespans down (removes PDDL epsilon separations)")
    parser.add_argument("--ref", type=float, help="hypervolume reference coordinate in normalized units (default 1 + 1/(|F|-1))")
    parser.add_argument("--json", action="store_true", help="print one JSON object per run")
    args = parser.parse_args(argv)
    if args.ref is not None and args.ref <= 1:
        parser.error("--ref must be above 1, the nadir of the front")

    try:
        problem = Problem(args.front)
        results = []
        for run in args.runs:
            points = read_run(run, problem)
            if args.floor_makespan:
                points = [(c, math.floor(m + EPS)) for c, m in points]
            results.append(dict(run=run, **score(problem.front, points, args.ref)))
    except (InputError, OSError) as e:
        print(f"score_front: {e}", file=sys.stderr)
        return 2

    if args.json:
        for row in results:
            print(json.dumps({k: (None if v == math.inf else v) for k, v in row.items()}))
    else:
        width = max(len("run"), *(len(r["run"]) for r in results))
        print(f"{'run':<{width}}  points  found     hv      eps  impossible")
        for r in results:
            found = f"{r['found']}/{r['front']}"
            print(f"{r['run']:<{width}}  {r['points']:>6}  {found:>5}  {r['hv']:.4f}  {r['eps']:.4f}  {len(r['impossible']):>10}")
    for r in results:
        for c, m in r["impossible"]:
            print(f"score_front: {r['run']}: no plan achieves cost {c}, makespan {m}: "
                  "check the plan with VAL, and how its makespan was measured", file=sys.stderr)
    return 1 if any(r["impossible"] for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
