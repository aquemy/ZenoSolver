"""Front-level search for plans with central flights that beat the admissible-partition front.

Theorem 4.10 says there are none under (S) and (AΔ). For each random symmetric
instance, zeno's certificate gives the front of admissible partitions (E) and the
gaps where the relaxation L is below E (`forest`), the only places a plan using
central flights could be cheaper (Lemma 3.4 holds whatever the central flights).
For each such gap between front points i and i+1, the exact flow model
(flowplan.py) gives the least cost of any plan with the tightest central flights
allowed by (AΔ), D_ij = |d_i - d_j| (durations are distinct, so D_ij >= 1), and
makespan at most M_{i+1} - 1. Every plan whose central flights satisfy (AΔ) is
still a plan, no later, with this table, so the comparison covers every table.

Families: uniform, anti (costs decreasing in duration), hub (one cheap slow city
among fast dear ones), cluster (cities in groups of close durations, so central
flights between them are short), offset (d_i = a + b i, the family with L < E of §10).

usage: python3 thm410_search.py <zeno> <family> <trials> <seed> <nmax> <tmax> <pmin> <pmax> <dmax> [workers [seconds [table]]]
(seconds: time limit of one integer program, default 300; a gap not solved in time counts as a timeout.
table: tight (default), or below: random central flights of 1..|d_i - d_j|, which violate (AΔ) and (A1)
and can beat E, Example 4.13)
"""
import json
import multiprocessing as mp
import random
import subprocess
import sys
import tempfile
import time

from flowplan import min_cost, simulate, tight_table

ZENO = None


def zeno_front(d, c, t, p):
    with tempfile.TemporaryDirectory() as tmp:
        data, cert = f"{tmp}/i.dat", f"{tmp}/i.cert"
        with open(data, "w") as f:
            f.write(" ".join(map(str, d)) + "\n" + " ".join(map(str, c)) + "\n")
        out = subprocess.run([ZENO, "-n", str(len(d)), "-t", str(t), "-p", str(p), "-d", data, "--certificate", cert,
                              "--threads", "1"], capture_output=True, text=True, check=True).stdout
        with open(cert) as f:
            text = f.read()
    gaps = [line.split() for line in text.split("lower-bounds")[1].splitlines()[1:] if line.strip() and line.strip() != "end"]
    forest = [int(g[0]) - 1 for g in gaps if g[1] == "forest"]
    E = sorted(((int(a), int(b)) for a, b in (l.split() for l in out.strip().splitlines())), key=lambda x: x[1])
    return E, forest


def gen(rng, family, nmax, tmax, pmin, pmax, dmax):
    p = rng.randint(pmin, pmax)
    t = rng.randint(p + 1, max(p + 1, tmax))
    n = rng.randint(2, nmax)
    if family == "uniform":
        d = rng.sample(range(1, dmax + 1), n)
        c = [rng.randint(0, 40) for _ in range(n)]
    elif family == "anti":
        d = sorted(rng.sample(range(1, dmax + 1), n))
        c = sorted(rng.sample(range(0, 61), n), reverse=True)
    elif family == "hub":
        d = sorted(rng.sample(range(1, dmax + 1), n))
        c = [rng.randint(15, 60) for _ in range(n)]
        c[rng.randrange(n // 2, n)] = rng.randint(0, 5)
    elif family == "cluster":
        centres = rng.sample(range(2, dmax - 1), rng.randint(1, 2))
        d = set()
        while len(d) < n:
            d.add(max(1, min(dmax, rng.choice(centres) + rng.randint(-2, 2))))
        d = sorted(d)
        c = [rng.randint(0, 60) for _ in range(n)]
    elif family == "offset":
        a, b = rng.randint(1, 6), rng.randint(1, 3)
        d = [a + b * i for i in range(n)]
        base = rng.randint(2, 4)
        c = [max(0, base * (d[-1] + 2) - base * x + rng.randint(-2, 2)) for x in d]
    else:
        raise ValueError(family)
    pairs = sorted(zip(d, c))  # increasing durations: avoids the data reader's 2016 swap quirk
    return [x for x, _ in pairs], [y for _, y in pairs], t, p


def work(args):
    seed, family, nmax, tmax, pmin, pmax, dmax, limit, table = args
    rng = random.Random(seed)
    d, c, t, p = gen(rng, family, nmax, tmax, pmin, pmax, dmax)
    E, forest = zeno_front(d, c, t, p)
    D = tight_table(d)
    if table == "below":
        for i in range(len(d)):
            for j in range(i + 1, len(d)):
                D[i][j] = D[j][i] = rng.randint(1, D[i][j])
    res = {"d": d, "c": c, "t": t, "p": p, "D": D, "gaps": len(forest), "solved": 0, "timeouts": 0, "found": []}
    for i in forest:
        cost, nextM = E[i][0], E[i + 1][1]
        try:
            r = min_cost(d, d, c, D, t, p, nextM - 1, time_limit=limit)
        except RuntimeError:
            res["timeouts"] += 1
            continue
        res["solved"] += 1
        if r is not None and r[0] < cost:
            sim = simulate(d, d, c, D, t, p, r[1], r[2])
            res["found"].append({"gap": i, "E": cost, "makespan": nextM - 1, "plan": r[0], "sim": sim,
                                 "routes": r[1], "journeys": r[2]})
    return res


def main():
    global ZENO
    ZENO = sys.argv[1]
    family, trials, seed = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    nmax, tmax, pmin, pmax, dmax = (int(v) for v in sys.argv[5:10])
    workers = int(sys.argv[10]) if len(sys.argv) > 10 else 8
    limit = int(sys.argv[11]) if len(sys.argv) > 11 else 300
    table = sys.argv[12] if len(sys.argv) > 12 else "tight"
    jobs = [(seed * 1000003 + k, family, nmax, tmax, pmin, pmax, dmax, limit, table) for k in range(trials)]
    inst = with_gap = gaps = solved = timeouts = found = 0
    t0 = time.time()
    with mp.Pool(workers, initializer=_init, initargs=(ZENO,)) as pool:
        for res in pool.imap_unordered(work, jobs, chunksize=2):
            inst += 1
            with_gap += res["gaps"] > 0
            gaps += res["gaps"]
            solved += res["solved"]
            timeouts += res["timeouts"]
            if res["found"]:
                found += len(res["found"])
                print("BEATEN", json.dumps(res), flush=True)
    print(f"{family} {table} seed={seed} n<={nmax} t<={tmax} {pmin}<=p<={pmax} d<={dmax}: {inst} instances, {with_gap} with a "
          f"forest gap, {gaps} forest gaps, {solved} solved exactly, {timeouts} timeouts, {found} beaten; "
          f"{time.time() - t0:.0f}s", flush=True)


def _init(zeno):
    global ZENO
    ZENO = zeno


if __name__ == "__main__":
    main()
