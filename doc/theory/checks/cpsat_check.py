"""Independent check of the symmetric solver at sizes enumeration cannot reach.

For a symmetric instance, E(T) is the cheapest admissible partition of the
s = 2t - p landings into p non-empty groups whose durations each sum to at
most T (Theorem 4.5 of doc/theory/exact-front.md). This script states that
problem directly as a CP-SAT model, with admissibility by Claim A (a 0/1
parity matrix h: h[k][i] <= x[k][i], each row of parity |X_k| + 1, each column
even), and checks zeno's front against it: every front point (C, M) must have
E(M / 2g) = C, and the level just below the next point must still cost C.
It shares no code with the solver.

usage: cpsat_check.py <zeno> <trials> <seed> [maxN maxT maxP maxD]
needs: ortools (pip install ortools)
"""
import random
import subprocess
import sys
import tempfile

from ortools.sat.python import cp_model


def level_cost(d, c, t, p, T):
    """E(T) by CP-SAT, or None when infeasible."""
    n, s = len(d), 2 * t - p
    m = cp_model.CpModel()
    x = [[m.NewIntVar(0, s, f"x{k}_{i}") for i in range(n)] for k in range(p)]
    h = [[m.NewBoolVar(f"h{k}_{i}") for i in range(n)] for k in range(p)]
    for k in range(p):
        size = sum(x[k])
        m.Add(size >= 1)
        m.Add(sum(d[i] * x[k][i] for i in range(n)) <= T)
        for i in range(n):
            m.Add(x[k][i] >= h[k][i])  # h inside the support of X_k
        z = m.NewIntVar(-s, s, f"z{k}")
        m.Add(sum(h[k]) == size + 1 + 2 * z)  # row parity |X_k| + 1
    for i in range(n):
        w = m.NewIntVar(0, p, f"w{i}")
        m.Add(sum(h[k][i] for k in range(p)) == 2 * w)  # even columns
    m.Add(sum(x[k][i] for k in range(p) for i in range(n)) == s)
    m.Minimize(sum(c[i] * x[k][i] for k in range(p) for i in range(n)))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60
    solver.parameters.num_workers = 8
    status = solver.Solve(m)
    if status == cp_model.OPTIMAL:
        return round(solver.ObjectiveValue())
    if status == cp_model.INFEASIBLE:
        return None
    raise RuntimeError("CP-SAT did not finish")


def main():
    zeno, trials, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    maxN, maxT, maxP, maxD = (int(v) for v in sys.argv[4:8]) if len(sys.argv) > 7 else (8, 16, 6, 40)
    rng = random.Random(seed)
    checked = mismatches = 0
    for _ in range(trials):
        p = rng.randint(2, maxP)
        t = rng.randint(p, maxT)
        n = rng.randint(2, maxN)
        d = [rng.randint(1, maxD) for _ in range(n)]
        c = [rng.randint(1, 60) for _ in range(n)]
        # Before #64 the data-file reader swapped the duration and cost vectors
        # when d[0] > d[1]. Reordering the first two cities (a relabelling, so
        # the front is unchanged) keeps this script valid for older builds.
        if d[0] > d[1]:
            d[0], d[1], c[0], c[1] = d[1], d[0], c[1], c[0]
        with tempfile.NamedTemporaryFile("w", suffix=".dat") as f:
            f.write(" ".join(map(str, d)) + "\n" + " ".join(map(str, c)) + "\n")
            f.flush()
            out = subprocess.run([zeno, "-n", str(n), "-t", str(t), "-p", str(p), "-d", f.name], capture_output=True, text=True, check=True).stdout
        front = sorted((int(a), int(b)) for a, b in (line.split() for line in out.splitlines()))  # (cost, makespan)
        front.sort(key=lambda point: point[1])  # by makespan
        for i, (cost, makespan) in enumerate(front):
            got = level_cost(d, c, t, p, makespan // 2)
            ok = got == cost
            if i + 1 < len(front):
                below = (front[i + 1][1] - 1) // 2
                ok = ok and level_cost(d, c, t, p, below) == cost
            checked += 1
            if not ok:
                mismatches += 1
                print("MISMATCH", d, c, t, p, "point", (cost, makespan), "cp-sat", got, flush=True)
    print(f"{checked} front points checked against CP-SAT, {mismatches} mismatches")


if __name__ == "__main__":
    main()
