"""Least cost of a plan with makespan at most M within a class of segments, by integer flows (§6.4).

The flow model of flowplan.py, with the plane units moving in a layered copy of the time-expanded network:
at a central city a plane also records the hub its current segment started from and how many central
landings that segment has made so far. The class says which segments may land in two or more central
cities. Tokens, joined by '+': none; all; <s><e><m> with hubs s, e in {I, G} and a bound m from 1 to 9 (or
a, for no bound) on the central landings of the segments from s to e (GI2: shuttles C_G -> x -> y -> C_I; IG2: crossings
C_I -> x -> y -> C_G); a trailing e, as in IG2e, keeps the central flights of the segments that start at s
empty (split crossings); segK = IIK+IGK+GIK+GGK, e.g. seg2. Passengers ride the physical flights; on every flight arc
at most as many passengers as planes, over all layers (and none on the arcs of empty central flights).
Every returned plan is decomposed, re-simulated with flowplan.simulate, and its segments and journeys are
checked against the class.

usage: python3 segclass_flow.py front <dW> <dE> <c> <t> <p> <table> <class> [Mmax]
         table: upper triangle d12,d13,...,d23,... (0 = no flight), or tight
       python3 segclass_flow.py xval <bin dir> <trials> <seed>
         compares fronts with bin/segclass_truth on tiny instances, for several classes
       python3 segclass_flow.py search <trials> <seed> <mode> <maxN> <maxT> <minP> <maxP> <maxD> [workers [classes]]
         random instances with (AΔ) tables violating (A1-NS) (mode tight|random|mixed|sparse, or comono:
         mixed tables on hub durations d and dbar that order the cities alike); for each, the
         least cost of all plans and of each class at every makespan up to a bound; prints the levels at
         which a class is dearer than all plans
Needs highspy. One solver per process (see flowplan.py).
"""
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flowplan as fp  # noqa: E402

UNL = 99  # no bound on the number of central landings (class "all")


def expand(cls):
    """segK: every segment with at most K central landings."""
    if len(cls) == 4 and cls.startswith("seg"):
        return "+".join(f"{a}{b}{cls[3]}" for a in "IG" for b in "IG")
    return cls


def parse_class(cls):
    cls = expand(cls)
    allow = [[1, 1], [1, 1]]  # [start is G][end is G]
    empty = [False, False]    # [start is G]: central flights of such segments carry no passenger
    for tok in cls.split("+"):
        if tok == "all":
            allow = [[UNL, UNL], [UNL, UNL]]
        elif tok == "none":
            pass
        else:
            assert len(tok) in (3, 4) and tok[0] in "IG" and tok[1] in "IG" and tok[2] in "123456789a", tok
            assert len(tok) == 3 or tok[3] == "e", tok
            s, e = tok[0] == "G", tok[1] == "G"
            allow[s][e] = max(allow[s][e], UNL if tok[2] == "a" else int(tok[2]))
            if len(tok) == 4:
                empty[s] = True  # e.g. IG2e: split crossings C_I -> x -> y -> C_G with an empty middle leg
    return allow, empty


def segment_ok(allow, start_is_G, end_is_G, m):
    return m <= 1 or m <= allow[start_is_G][end_is_G]


def parse_table(spec, dW, dE):
    n = len(dW)
    D = [[0] * n for _ in range(n)]
    if spec == "tight":
        for i in range(n):
            for j in range(n):
                if i != j:
                    D[i][j] = max(abs(dW[i] - dW[j]), abs(dE[i] - dE[j]), 1)
        return D
    if spec == "none":
        return D
    v = list(map(int, spec.split(",")))
    k = 0
    for i in range(n):
        for j in range(i + 1, n):
            D[i][j] = D[j][i] = v[k]
            k += 1
    return D


def layers(allow, empty):
    """Central layers (start_is_G, m); merged when the class does not distinguish them."""
    unrestricted = all(x == UNL for r in allow for x in r)
    start_matters = allow[0] != allow[1] or empty[0] != empty[1]
    maxm = 1 if unrestricted else mcap_of(allow)

    def norm(s, m):
        if unrestricted:
            return (0, 1)
        return (s if start_matters else 0, min(m, maxm))
    L = sorted({norm(s, m) for s in (0, 1) for m in range(1, maxm + 1)})
    return L, norm, unrestricted


def mcap_of(allow):
    """Largest landing count a layer records; with an unbounded type, the top layer means 'more than any finite bound'."""
    finite = [x for r in allow for x in r if x < UNL]
    top = max(finite + [1])
    return top + 1 if any(x == UNL for r in allow for x in r) else top


def min_cost(dW, dE, c, D, t, p, M, cls, time_limit=600):
    import highspy
    allow, empty = parse_class(cls)
    n = len(dW)
    G = n + 1
    dur = fp.durations(dW, dE, D)
    Ls, norm, unrestricted = layers(allow, empty)
    start_matters = allow[0] != allow[1] or empty[0] != empty[1]
    max_start = [max(allow[s]) for s in (0, 1)]
    has_unl = any(v == UNL for r in allow for v in r)
    top = mcap_of(allow)
    # plane nodes: (loc, layer, time), layer None at hubs
    plane_arcs = []  # (u, v, phys) with phys = (a, ta, b, tb) for flights, None for waits
    for tau in range(M):
        for x in (0, G):
            plane_arcs.append(((x, None, tau), (x, None, tau + 1), None))
        for x in range(1, n + 1):
            for L in Ls:
                plane_arcs.append(((x, L, tau), (x, L, tau + 1), None))
    for tau in range(M + 1):
        for h in (0, G):
            for x in range(1, n + 1):
                dd = dur(h, x)
                if tau + dd <= M:
                    plane_arcs.append(((h, None, tau), (x, norm(h == G, 1), tau + dd), (h, tau, x, tau + dd)))
        for x in range(1, n + 1):
            for L in Ls:
                s, m = L
                starts = (s,) if (not unrestricted and start_matters) else (0, 1)
                for h in (0, G):
                    dd = dur(x, h)
                    if tau + dd > M:
                        continue
                    if unrestricted or any(segment_ok(allow, st, h == G, m) for st in starts):
                        plane_arcs.append(((x, L, tau), (h, None, tau + dd), (x, tau, h, tau + dd)))
                for y in range(1, n + 1):
                    dd = dur(x, y)
                    if dd is None or tau + dd > M:
                        continue
                    m2 = min(m + 1, top) if has_unl else m + 1  # with no bound, the top layer stands for all larger counts
                    if unrestricted:
                        L2 = L
                    else:
                        if not any(m2 <= max_start[st] for st in starts):
                            continue
                        L2 = norm(s, m2)
                    plane_arcs.append(((x, L, tau), (y, L2, tau + dd), (x, tau, y, tau + dd)))
    # passenger arcs on physical nodes
    pax_arcs = []
    for tau in range(M):
        for a in range(n + 2):
            pax_arcs.append(((a, tau), (a, tau + 1), None))
    phys_flights = sorted({ph for _, _, ph in plane_arcs if ph is not None})
    for ph in phys_flights:
        a, ta, b, tb = ph
        if b == 0 or a == G:
            continue  # clean journeys (Lemma 3.1)
        pax_arcs.append(((a, ta), (b, tb), ph))
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    h.setOptionValue("time_limit", float(time_limit))
    h.setOptionValue("mip_rel_gap", 0.0)
    h.setOptionValue("mip_abs_gap", 0.0)
    inf = highspy.kHighsInf
    nP, nZ = len(plane_arcs), len(pax_arcs)
    for (u, v, ph) in plane_arcs:
        cost = c[ph[2] - 1] if ph is not None and 1 <= ph[2] <= n else 0
        h.addCol(cost, 0, p, 0, [], [])
    for _ in pax_arcs:
        h.addCol(0, 0, t, 0, [], [])
    h.changeColsIntegrality(nP + nZ, list(range(nP + nZ)), [highspy.HighsVarType.kInteger] * (nP + nZ))
    outs, ins = {}, {}
    for k, (u, v, ph) in enumerate(plane_arcs):
        outs.setdefault(u, []).append(k)
        ins.setdefault(v, []).append(k)
    src, snk = (0, None, 0), (G, None, M)
    for node in set(outs) | set(ins):
        o, i = outs.get(node, []), ins.get(node, [])
        rhs = p if node == src else (-p if node == snk else 0)
        h.addRow(rhs, rhs, len(o) + len(i), o + i, [1.0] * len(o) + [-1.0] * len(i))
    pouts, pins = {}, {}
    for k, (u, v, ph) in enumerate(pax_arcs):
        pouts.setdefault(u, []).append(nP + k)
        pins.setdefault(v, []).append(nP + k)
    for node in set(pouts) | set(pins):
        o, i = pouts.get(node, []), pins.get(node, [])
        rhs = t if node == (0, 0) else (-t if node == (G, M) else 0)
        h.addRow(rhs, rhs, len(o) + len(i), o + i, [1.0] * len(o) + [-1.0] * len(i))
    by_phys = {}  # plane arcs on which a passenger may ride this flight
    for k, (u, v, ph) in enumerate(plane_arcs):
        if ph is None:
            continue
        central_leg = 1 <= ph[0] <= n and 1 <= ph[2] <= n
        if central_leg and not unrestricted and start_matters and empty[u[1][0]]:
            continue
        if central_leg and not unrestricted and not start_matters and empty[0]:
            continue
        by_phys.setdefault(ph, []).append(k)
    for k, (u, v, ph) in enumerate(pax_arcs):
        if ph is not None:
            ks = by_phys.get(ph, [])
            h.addRow(-inf, 0, 1 + len(ks), [nP + k] + ks, [1.0] + [-1.0] * len(ks))
    h.run()
    st = h.getModelStatus()
    if st == highspy.HighsModelStatus.kInfeasible:
        return None
    if st != highspy.HighsModelStatus.kOptimal:
        raise RuntimeError(f"HiGHS status {h.modelStatusToString(st)}")
    sol = h.getSolution().col_value
    y = [round(v) for v in sol[:nP]]
    z = [round(v) for v in sol[nP:]]
    cost = sum(c[ph[2] - 1] * y[k] for k, (u, v, ph) in enumerate(plane_arcs) if ph is not None and 1 <= ph[2] <= n)
    routes = []
    rem = list(y)
    for _ in range(p):
        node, legs = src, []
        while node != snk:
            k = next(k for k in outs[node] if rem[k] > 0)
            rem[k] -= 1
            u, v, ph = plane_arcs[k]
            if ph is not None:
                a, ta, b, tb = ph
                legs.append((a, b, ta, tb))
            node = v
        routes.append(legs)
    flying = {}
    for q, legs in enumerate(routes):
        for j, leg in enumerate(legs):
            flying.setdefault(leg, []).append((q, j))
    remz, used, journeys = list(z), set(), []
    pouts_local = {}
    for k, (u, v, ph) in enumerate(pax_arcs):
        pouts_local.setdefault(u, []).append(k)
    for _ in range(t):
        node, legs = (0, 0), []
        while True:
            k = next(k for k in pouts_local[node] if remz[k] > 0)
            remz[k] -= 1
            u, v, ph = pax_arcs[k]
            if ph is not None:
                a, ta, b, tb = ph
                pick = next(x for x in flying[(a, b, ta, tb)] if x not in used)
                used.add(pick)
                legs.append(pick)
                if b == G:
                    break
            node = v
        journeys.append(legs)
    sc, sm = fp.simulate(dW, dE, c, D, t, p, routes, journeys)
    assert sc == cost and sm <= M, (sc, cost, sm, M)
    assert routes_in_class(routes, n, allow), routes
    if any(empty):
        for legs in journeys:
            for (q, j) in legs:
                a, b, ta, tb = routes[q][j]
                if 1 <= a <= n and 1 <= b <= n:
                    start = next((routes[q][i][0] for i in range(j, -1, -1) if routes[q][i][0] in (0, G)), 0)
                    assert not empty[start == G], "a passenger rides an empty-middle leg"
    return cost, routes, journeys


def routes_in_class(routes, n, allow):
    G = n + 1
    for legs in routes:
        start, m = 0, 0
        for (a, b, ta, tb) in legs:
            if b in (0, G):
                if not segment_ok(allow, start == G, b == G, m):
                    return False
                start, m = b, 0
            else:
                m += 1
    return True


def front(dW, dE, c, D, t, p, cls, Mmax):
    pts = []
    for M in range(1, Mmax + 1):
        r = min_cost(dW, dE, c, D, t, p, M, cls)
        if r is None:
            continue
        if not pts or r[0] < pts[-1][0]:
            pts.append((r[0], M))
    return sorted(pts)


def xval(bindir, trials, seed):
    rng = random.Random(seed)
    equal = total = 0
    while total < trials:
        n = rng.randint(2, 3)
        p = rng.randint(1, 3)
        t = rng.randint(max(p, 2), 4)
        dW = [rng.randint(1, 6) for _ in range(n)]
        dE = [rng.randint(1, 6) for _ in range(n)]
        c = [rng.randint(0, 9) for _ in range(n)]
        D = parse_table("tight", dW, dE)
        for i in range(n):
            for j in range(n):
                if i != j and D[i][j] > min(dW[i] + dW[j], dE[i] + dE[j]):
                    D[i][j] = 0
        tab = ",".join(str(D[i][j]) for i in range(n) for j in range(i + 1, n))
        cls = rng.choice(["all", "none", "GI2", "IG2", "IG2e", "IG2+GI2", "IG2e+GI2", "seg2", "seg3", "IGa", "IGa+GGa"])
        arg = expand(cls)
        out = subprocess.run([f"{bindir}/segclass_truth", ",".join(map(str, dW)), ",".join(map(str, dE)), ",".join(map(str, c)),
                              str(t), str(p), tab, arg, "0"], capture_output=True, text=True, check=True, timeout=900).stdout
        tf = sorted(tuple(map(int, l.split())) for l in out.strip().splitlines())
        ff = front(dW, dE, c, D, t, p, cls, max(m for _, m in tf))
        total += 1
        if tf == ff:
            equal += 1
        else:
            print("MISMATCH", dW, dE, c, t, p, tab, cls, tf, ff, flush=True)
    print(f"{equal} / {total} fronts equal to segclass_truth")


def random_table(dW, dE, mode, rng):
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
            v = lo if mode in ("tight", "sparse") else (rng.randint(lo, max(lo, hi - 1)) if rng.random() < 0.85 else hi)
            D[i][j] = D[j][i] = v
            useful |= v < hi
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if len({i, j, k}) == 3 and D[i][j] and D[j][k] and D[i][k] and D[i][k] > D[i][j] + D[j][k]:
                    return None
    return D if useful else None


def search_one(job):
    dW, dE, c, t, p, D, mode, classes = job
    n = len(dW)
    # makespan bound: a sequential plan through the fastest crossing city, as in truth.cpp's time cap
    Mmax = (2 * t - p) * max(dW[i] + dE[i] for i in range(n))
    allc = {}  # makespan of each point of the all-plans front -> its cost
    last = None
    for M in range(1, Mmax + 1):
        r = min_cost(dW, dE, c, D, t, p, M, "all")
        if r is None:
            continue
        if last is None or r[0] < last:
            allc[M] = r[0]
            last = r[0]
        if r[0] == min(c) * (2 * t - p):
            break  # every plan has at least 2t - p central landings (Lemma 3.2): nothing is cheaper
    # A class is a subset of all plans, so it misses the front iff it is dearer at a front point.
    res = {cls: {} for cls in classes}
    for cls in classes:
        for M in sorted(allc):
            r = min_cost(dW, dE, c, D, t, p, M, cls)
            res[cls][M] = None if r is None else r[0]
    return job, allc, res


def search(trials, seed, mode, maxN, maxT, minP, maxP, maxD, workers, classes):
    from concurrent.futures import ProcessPoolExecutor
    rng = random.Random(seed)
    jobs = []
    while len(jobs) < trials:
        n = rng.randint(2, maxN)
        p = rng.randint(minP, maxP)
        t = rng.randint(p + 1, maxT)
        dW = [rng.randint(1, maxD) for _ in range(n)]
        dE = [rng.randint(1, maxD) for _ in range(n)]
        c = [rng.randint(0, 9) for _ in range(n)]
        if mode == "comono":  # d and dbar order the cities alike
            dW, dE = sorted(dW), sorted(dE)
        m = mode if mode not in ("mixed", "comono") else rng.choice(["tight", "random"])
        D = random_table(dW, dE, m, rng)
        if D is None:
            continue
        jobs.append((dW, dE, c, t, p, D, m, classes))
    worse = {cls: 0 for cls in classes}
    levels = {cls: 0 for cls in classes}
    done = 0
    with ProcessPoolExecutor(max_workers=workers) as ex:
        for job, allc, res in ex.map(search_one, jobs):
            done += 1
            dW, dE, c, t, p, D, m, _ = job
            tab = ",".join(str(D[i][j]) for i in range(len(dW)) for j in range(i + 1, len(dW)))
            for cls in classes:
                bad = [(M, allc[M], res[cls][M]) for M in sorted(allc) if res[cls][M] is None or res[cls][M] > allc[M]]
                if bad:
                    worse[cls] += 1
                    levels[cls] += len(bad)
                    print(f"DEARER {cls}: dW={dW} dE={dE} c={c} t={t} p={p} D={tab} ({m}) levels (M, all, class)={bad}", flush=True)
    print(f"{done} instances; instances (levels) where a class is dearer than all plans: "
          + ", ".join(f"{cls}: {worse[cls]} ({levels[cls]})" for cls in classes))


if __name__ == "__main__":
    a = sys.argv
    if len(a) >= 9 and a[1] == "front":
        dW, dE, c = (list(map(int, x.split(","))) for x in a[2:5])
        t, p = int(a[5]), int(a[6])
        D = parse_table(a[7], dW, dE)
        Mmax = int(a[9]) if len(a) > 9 else (2 * t - p) * max(x + y for x, y in zip(dW, dE))
        for pt in front(dW, dE, c, D, t, p, a[8], Mmax):
            print(*pt)
    elif len(a) >= 5 and a[1] == "xval":
        xval(a[2], int(a[3]), int(a[4]))
    elif len(a) >= 10 and a[1] == "search":
        workers = int(a[10]) if len(a) > 10 else 8
        classes = a[11].split(",") if len(a) > 11 else ["IG2+GI2", "seg2"]
        search(int(a[2]), int(a[3]), a[4], int(a[5]), int(a[6]), int(a[7]), int(a[8]), int(a[9]), workers, classes)
    else:
        print(__doc__)
