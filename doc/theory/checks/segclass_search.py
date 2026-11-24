"""Which segments with central flights does the non-symmetric front need under (AΔ)? (§6.4, Conj 6.7)

On random tiny non-symmetric instances whose central table satisfies (AΔ) but not (A1-NS), compare the
front of all plans with the fronts of plans restricted to segment classes (`bin/segclass_truth`):
  none      simple plans, i.e. role configurations (Cor 6.10)
  GI2       plus shuttles C_G -> i -> j -> C_I (the B-Abar-Bbar shuttle triples of the arXiv paper)
  IG2       plus crossings C_I -> i -> j -> C_G with one central flight
  IG2e      plus split crossings: the same with an empty central flight
  IG2+GI2   both IG2 and GI2
  seg2      every segment with at most two central landings (II2+IG2+GI2+GG2); likewise seg3 to seg6
  all       all plans (the search of truth.cpp)
A class misses the front when some point of the all-plans front is not weakly dominated by its front.
Tables: `tight` is the least table (AΔ) allows, d_ij = max(|d_i - d_j|, |dbar_i - dbar_j|, 1), with the
flight left out when that exceeds min(d_i + d_j, dbar_i + dbar_j); `random` draws each d_ij between that
least value and min(d_i + d_j, dbar_i + dbar_j) - 1 (or, with probability 0.15, takes that minimum itself)
and keeps the table only if every triangle holds;
`sparse` is `tight` with each flight left out with probability 0.4; `mixed` picks tight or random.

usage: python3 segclass_search.py <bin dir> <trials> <seed> [tight|random|mixed|sparse] [maxT maxP maxN maxD workers classes]
  classes: comma-separated list (default none,GI2,IG2,IG2+GI2,seg2)
"""
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor



def front(out):
    return sorted(tuple(map(int, l.split())) for l in out.strip().splitlines() if l.strip())


def dominated(pt, fr):
    return any(c <= pt[0] and m <= pt[1] for c, m in fr)


def table_of(dW, dE, mode, rng):
    """Upper triangle of an (AΔ) table, or None if no flight can violate (A1-NS)."""
    n = len(dW)
    D = [[0] * n for _ in range(n)]
    useful = False
    for i in range(n):
        for j in range(i + 1, n):
            lo = max(abs(dW[i] - dW[j]), abs(dE[i] - dE[j]), 1)
            hi = min(dW[i] + dW[j], dE[i] + dE[j])
            if lo > hi:
                continue
            if mode == "sparse" and rng.random() < 0.4:
                continue  # leave the flight out
            if mode in ("tight", "sparse"):
                v = lo
            else:
                v = rng.randint(lo, max(lo, hi - 1)) if rng.random() < 0.85 else hi
            D[i][j] = D[j][i] = v
            useful |= v < hi
    for i in range(n):  # every triangle of existing central flights
        for j in range(n):
            for k in range(n):
                if len({i, j, k}) == 3 and D[i][j] and D[j][k] and D[i][k] and D[i][k] > D[i][j] + D[j][k]:
                    return None
    return ([D[i][j] for i in range(n) for j in range(i + 1, n)], useful) if useful else None


def main():
    bindir, trials, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    mode = sys.argv[4] if len(sys.argv) > 4 else "tight"
    maxT = int(sys.argv[5]) if len(sys.argv) > 5 else 5
    maxP = int(sys.argv[6]) if len(sys.argv) > 6 else 3
    maxN = int(sys.argv[7]) if len(sys.argv) > 7 else 3
    maxD = int(sys.argv[8]) if len(sys.argv) > 8 else 7
    workers = int(sys.argv[9]) if len(sys.argv) > 9 else 12
    classes = sys.argv[10].split(",") if len(sys.argv) > 10 else ["none", "GI2", "IG2", "IG2+GI2", "seg2"]
    rng = random.Random(seed)
    jobs = []
    while len(jobs) < trials:
        n = rng.randint(2, maxN)
        p = rng.randint(1, maxP)
        t = rng.randint(max(p, 2), maxT)
        dW = [rng.randint(1, maxD) for _ in range(n)]
        dE = [rng.randint(1, maxD) for _ in range(n)]
        c = [rng.randint(0, 9) for _ in range(n)]
        m = mode if mode != "mixed" else rng.choice(["tight", "random"])
        tab = table_of(dW, dE, m, rng)
        if tab is None:
            continue
        jobs.append((dW, dE, c, t, p, ",".join(map(str, tab[0])), m))

    def run(job):
        dW, dE, c, t, p, tab, m = job
        res = {}
        for cl in ["all"] + classes:
            arg = "+".join(f"{a}{b}{cl[3]}" for a in "IG" for b in "IG") if cl.startswith("seg") else cl
            try:
                out = subprocess.run([f"{bindir}/segclass_truth", ",".join(map(str, dW)), ",".join(map(str, dE)),
                                      ",".join(map(str, c)), str(t), str(p), tab, arg, "2"],
                                     capture_output=True, text=True, timeout=900, check=True).stdout
            except subprocess.TimeoutExpired:
                return job, None
            res[cl] = front(out)
        return job, res

    counts = {cl: 0 for cl in classes}
    done = timeouts = 0
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for job, res in ex.map(run, jobs):
            if res is None:
                timeouts += 1
                continue
            done += 1
            for cl in classes:
                missed = [pt for pt in res["all"] if not dominated(pt, res[cl])]
                if missed:
                    counts[cl] += 1
                    print(f"MISS {cl}: dW={job[0]} dE={job[1]} c={job[2]} t={job[3]} p={job[4]} D={job[5]} ({job[6]}) "
                          f"all={res['all']} {cl}={res[cl]} missed={missed}", flush=True)
    print(f"{done} instances ({timeouts} timeouts); instances on which a class misses the all-plans front: {counts}")


if __name__ == "__main__":
    main()
