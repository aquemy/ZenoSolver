"""Exact least cost of a plan with makespan at most M, by integer flows.

With integer durations of at least 1, the plans of doc/theory/exact-front.md §1.2
are exactly the pairs of integer flows in the time-expanded network: p plane units
and t passenger units from (C_I, 0) to (C_G, M), waiting allowed everywhere, and on
every flight arc at most as many passengers as planes. Planes and passengers are
indistinguishable, so a flow decomposes into routes (a flow on a DAG) and
journeys (on each flight arc, the carried passengers go to distinct planes flying
it). Passengers are restricted to clean journeys (no flight into C_I, none out of
C_G), which loses nothing by the chains of Lemma 3.2. Every returned plan is decomposed and can
be re-simulated with `simulate`, which shares no code with the model.

Locations: 0 = C_I, 1..n central, n+1 = C_G. A central table D has D[i][j] = 0 for
a missing flight. Solved with HiGHS (highspy), or with CP-SAT (ortools) for
backend="cpsat"; use one backend per process, as HiGHS crashed after OR-Tools had run.

usage: python3 flowplan.py xval <checks dir> <trials> <seed>
       compares the fronts with those of bin/truth on tiny instances, for central
       flights none, a1 and tight.
       python3 flowplan.py ex413 [highs|cpsat]
       Example 4.7 (central flights violating (AΔ)), solved and simulated; with
       cpsat, also E(19) and E(20) from the independent model of cpsat_check.py.
"""
import random
import subprocess
import sys


def durations(dW, dE, D):
    n = len(dW)
    G = n + 1

    def dur(a, b):
        if a == b:
            return None
        if a > b:
            a, b = b, a
        if a == 0 and b == G:
            return None
        if a == 0:
            return dW[b - 1]
        if b == G:
            return dE[a - 1]
        v = D[a - 1][b - 1]
        return v if v and v > 0 else None
    return dur


def build_arcs(n, dur, M):
    locs = range(n + 2)
    arcs = []  # (a, ta, b, tb, flight)
    for tau in range(M):
        for a in locs:
            arcs.append((a, tau, a, tau + 1, False))
    for tau in range(M + 1):
        for a in locs:
            for b in locs:
                dd = dur(a, b)
                if dd is not None and tau + dd <= M:
                    arcs.append((a, tau, b, tau + dd, True))
    return arcs


def tight_table(d):
    """The least central table allowed by (AΔ) under (S): D[i][j] = |d_i - d_j|."""
    n = len(d)
    return [[abs(d[i] - d[j]) if i != j else 0 for j in range(n)] for i in range(n)]


def min_cost(dW, dE, c, D, t, p, M, time_limit=600, arc_cost=None, backend="highs"):
    """Least cost of a feasible plan with makespan <= M, and one such plan.

    Returns (cost, routes, journeys), or None if no plan exists. With arc_cost, a
    function of (a, ta, b, tb, flight), plane arcs are weighted by it instead of
    the landing costs (to draw diverse plans); the returned cost is still the
    plan's landing cost."""
    # One backend per process: HiGHS 1.16 segfaulted after OR-Tools 9.15 had run in the same process.
    if backend == "cpsat":
        return _solve_cpsat(dW, dE, c, D, t, p, M, time_limit)
    for presolve in ("choose", "off"):  # HiGHS 1.16 reports a solve error on some trivial models
        try:
            return _solve_highs(dW, dE, c, D, t, p, M, time_limit, presolve, arc_cost)
        except SolveError:
            continue
    raise RuntimeError("HiGHS failed")


class SolveError(RuntimeError):
    pass


def _structure(dW, dE, D, t, p, M):
    n = len(dW)
    arcs = build_arcs(n, durations(dW, dE, D), M)
    out_arcs, in_arcs = {}, {}
    for k, (a, ta, b, tb, fl) in enumerate(arcs):
        out_arcs.setdefault((a, ta), []).append(k)
        in_arcs.setdefault((b, tb), []).append(k)
    nodes = set(out_arcs) | set(in_arcs)
    return n, arcs, out_arcs, in_arcs, nodes


def _landing_cost(c, n, arc):
    a, ta, b, tb, fl = arc
    return c[b - 1] if fl and 1 <= b <= n else 0


def _solve_highs(dW, dE, c, D, t, p, M, time_limit, presolve, arc_cost):
    import highspy
    n, arcs, out_arcs, in_arcs, nodes = _structure(dW, dE, D, t, p, M)
    G = n + 1
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    h.setOptionValue("presolve", presolve)
    h.setOptionValue("time_limit", float(time_limit))
    h.setOptionValue("mip_rel_gap", 0.0)
    h.setOptionValue("mip_abs_gap", 0.0)
    inf = highspy.kHighsInf
    nA = len(arcs)
    for arc in arcs:  # plane arcs
        h.addCol(arc_cost(*arc) if arc_cost else _landing_cost(c, n, arc), 0, p, 0, [], [])
    for (a, ta, b, tb, fl) in arcs:  # passenger arcs
        h.addCol(0, 0, 0 if fl and (b == 0 or a == G) else t, 0, [], [])
    h.changeColsIntegrality(2 * nA, list(range(2 * nA)), [highspy.HighsVarType.kInteger] * (2 * nA))
    for off, units in ((0, p), (nA, t)):
        for node in nodes:
            o, i = out_arcs.get(node, []), in_arcs.get(node, [])
            rhs = units if node == (0, 0) else (-units if node == (G, M) else 0)
            h.addRow(rhs, rhs, len(o) + len(i), [off + k for k in o] + [off + k for k in i], [1.0] * len(o) + [-1.0] * len(i))
    for k, arc in enumerate(arcs):
        if arc[4]:
            h.addRow(-inf, 0, 2, [nA + k, k], [1.0, -1.0])
    h.run()
    st = h.getModelStatus()
    if st == highspy.HighsModelStatus.kInfeasible:
        return None
    if st == highspy.HighsModelStatus.kSolveError:
        raise SolveError("HiGHS solve error")
    if st != highspy.HighsModelStatus.kOptimal:
        raise RuntimeError(f"HiGHS status {h.modelStatusToString(st)}")
    sol = h.getSolution().col_value
    y = [round(v) for v in sol[:nA]]
    z = [round(v) for v in sol[nA:]]
    return _finish(n, arcs, y, z, c, t, p, M)


def _solve_cpsat(dW, dE, c, D, t, p, M, time_limit):
    from ortools.sat.python import cp_model
    n, arcs, out_arcs, in_arcs, nodes = _structure(dW, dE, D, t, p, M)
    G = n + 1
    m = cp_model.CpModel()
    y = [m.NewIntVar(0, p, f"y{k}") for k in range(len(arcs))]
    z = [m.NewIntVar(0, 0 if fl and (b == 0 or a == G) else t, f"z{k}") for k, (a, ta, b, tb, fl) in enumerate(arcs)]
    for var, units in ((y, p), (z, t)):
        for node in nodes:
            rhs = units if node == (0, 0) else (-units if node == (G, M) else 0)
            m.Add(sum(var[k] for k in out_arcs.get(node, [])) - sum(var[k] for k in in_arcs.get(node, [])) == rhs)
    for k, arc in enumerate(arcs):
        if arc[4]:
            m.Add(z[k] <= y[k])
    m.Minimize(sum(_landing_cost(c, n, arc) * y[k] for k, arc in enumerate(arcs)))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = 8
    st = solver.Solve(m)
    if st == cp_model.INFEASIBLE:
        return None
    if st != cp_model.OPTIMAL:
        raise RuntimeError("CP-SAT did not finish")
    return _finish(n, arcs, [solver.Value(v) for v in y], [solver.Value(v) for v in z], c, t, p, M)


def _finish(n, arcs, y, z, c, t, p, M):
    cost = sum(_landing_cost(c, n, arc) * y[k] for k, arc in enumerate(arcs))
    routes, journeys = decompose(n, arcs, y, z, p, t, M)
    return cost, routes, journeys


def decompose(n, arcs, y, z, p, t, M):
    """Routes (lists of legs (a, b, depart, arrive)) and journeys (lists of (plane, leg index))."""
    G = n + 1
    out = {}
    for k, (a, ta, b, tb, fl) in enumerate(arcs):
        out.setdefault((a, ta), []).append(k)
    rem = list(y)
    routes = []
    for _ in range(p):  # every arc moves forward in time, so each walk ends in (C_G, M)
        node, legs = (0, 0), []
        while node != (G, M):
            k = next(k for k in out[node] if rem[k] > 0)
            rem[k] -= 1
            a, ta, b, tb, fl = arcs[k]
            if fl:
                legs.append((a, b, ta, tb))
            node = (b, tb)
        routes.append(legs)
    flying = {}
    for q, legs in enumerate(routes):
        for j, leg in enumerate(legs):
            flying.setdefault(leg, []).append((q, j))
    remz, used, journeys = list(z), set(), []
    for _ in range(t):
        node, legs = (0, 0), []
        while True:
            k = next(k for k in out[node] if remz[k] > 0)
            remz[k] -= 1
            a, ta, b, tb, fl = arcs[k]
            if fl:
                pick = next(x for x in flying[(a, b, ta, tb)] if x not in used)
                used.add(pick)
                legs.append(pick)
                if b == G:
                    break
            node = (b, tb)
        journeys.append(legs)
    return routes, journeys


def simulate(dW, dE, c, D, t, p, routes, journeys):
    """Check a plan against §1.2; return (cost, makespan) or raise AssertionError."""
    n = len(dW)
    G = n + 1
    dur = durations(dW, dE, D)
    assert len(routes) == p
    cost = makespan = 0
    for legs in routes:
        assert legs, "empty route"
        here, clock = 0, 0
        for (a, b, ta, tb) in legs:
            assert a == here, "route not contiguous"
            dd = dur(a, b)
            assert dd is not None, "no such flight"
            assert ta >= clock and tb == ta + dd, "bad timing"
            here, clock = b, tb
            if 1 <= b <= n:
                cost += c[b - 1]
        assert here == G, "route does not end in C_G"
        makespan = max(makespan, clock)
    assert len(journeys) == t
    seen = set()
    for legs in journeys:
        assert legs
        prev = None
        for (q, j) in legs:
            assert (q, j) not in seen, "capacity"
            seen.add((q, j))
            a, b, ta, tb = routes[q][j]
            if prev is None:
                assert a == 0, "journey does not start in C_I"
            else:
                pa, pb, pta, ptb = routes[prev[0]][prev[1]]
                assert pb == a and ta >= ptb, "journey not contiguous"
                if prev[0] == q:
                    assert j > prev[1], "journey goes back along a route"
            prev = (q, j)
        assert routes[prev[0]][prev[1]][1] == G, "journey does not end in C_G"
    return cost, makespan


def front(d, c, t, p, D, Mmax):
    """Pareto front (cost, makespan) of all plans with makespan <= Mmax, symmetric durations."""
    pts = []
    for M in range(1, Mmax + 1):
        r = min_cost(d, d, c, D, t, p, M)
        if r is None:
            continue
        cost, routes, journeys = r
        cc, mm = simulate(d, d, c, D, t, p, routes, journeys)
        assert cc == cost and mm <= M
        if not pts or cost < pts[-1][0]:
            pts.append((cost, M))
    return pts


def xval(checks, trials, seed):
    rng = random.Random(seed)
    equal = 0
    for _ in range(trials):
        p = rng.randint(1, 3)
        t = rng.randint(p, 4)
        n = rng.randint(1, 3)
        d = sorted(rng.sample(range(1, 7), n))
        c = [rng.randint(0, 12) for _ in range(n)]
        mode = rng.choice(["tight", "a1", "none"])
        if mode == "tight":  # truth's tight table: max(|d_i - d_j|, 1)
            D = [[max(abs(d[i] - d[j]), 1) if i != j else 0 for j in range(n)] for i in range(n)]
        elif mode == "a1":   # truth's a1 table: d_i + d_j + 1
            D = [[d[i] + d[j] + 1 if i != j else 0 for j in range(n)] for i in range(n)]
        else:
            D = [[0] * n for _ in range(n)]
        args = [f"{checks}/bin/truth", ",".join(map(str, d)), ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p), mode, "0"]
        out = subprocess.run(args, capture_output=True, text=True, timeout=900, check=True).stdout
        tf = sorted(((int(a), int(b)) for a, b in (l.split() for l in out.strip().splitlines())), key=lambda x: x[1])
        ff = front(d, c, t, p, D, max(m for _, m in tf))
        if tf == ff:
            equal += 1
        else:
            print("MISMATCH", d, c, t, p, mode, tf, ff, flush=True)
    print(f"{equal} / {trials} fronts equal to truth")


EX413 = dict(d=[2, 3, 9, 11], c=[50, 44, 17, 0], t=6, p=3,
             D=[[0, 1, 5, 6], [1, 0, 3, 6], [5, 3, 0, 1], [6, 6, 1, 0]])


def example413(backend):
    """Example 4.7: central flights violating (AΔ); a plan of makespan 39 costs 260 < E(19) = 264."""
    e = EX413
    d, c, t, p, D = e["d"], e["c"], e["t"], e["p"], e["D"]
    for M in (38, 39):
        cost, routes, journeys = min_cost(d, d, c, D, t, p, M, backend=backend)
        print(f"least cost of a plan with makespan <= {M}: {cost}; simulated (cost, makespan):",
              simulate(d, d, c, D, t, p, routes, journeys))
    for q, legs in enumerate(routes):
        print(f"  plane {q + 1}:", "  ".join(f"{a}->{b} [{x},{y}]" for a, b, x, y in legs))
    for k, legs in enumerate(journeys):
        print(f"  passenger {k + 1}:", "  ".join(f"plane {q + 1} leg {j + 1}" for q, j in legs))
    if backend == "cpsat":
        from cpsat_check import level_cost
        print("E(19) and E(20) by the CP-SAT model of cpsat_check.py:", level_cost(d, c, t, p, 19), level_cost(d, c, t, p, 20))


if __name__ == "__main__":
    if len(sys.argv) >= 5 and sys.argv[1] == "xval":
        xval(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
    elif len(sys.argv) >= 2 and sys.argv[1] == "ex413":
        example413(sys.argv[2] if len(sys.argv) > 2 else "highs")
    else:
        print(__doc__)
