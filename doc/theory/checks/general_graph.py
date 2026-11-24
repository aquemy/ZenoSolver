"""General flight graphs (arXiv 2304.14659 §2.4): the reduction to the clique model against the exact front.

A general instance is a connected graph on I (0), central vertices 1..n and G (n+1), with integer edge
durations >= 1, no edge I-G, landing costs c_1..c_n (hubs free), p planes and t passengers in I, capacity
one, hand-offs anywhere, planes ending in G. Its exact front is computed by bin/graph_truth (exhaustive
search over time) and, for cross-checks, by a time-expanded integer flow model solved with HiGHS, whose
plans are decomposed and re-simulated by `simulate`, which shares no code with either model.

The reduction f of §2.4 makes one virtual city v = (w, e) for every central vertex i, every simple path w
from I to i and every simple path e from i to G (paths may pass through a hub): cost omega(w) + omega(e),
where omega sums the landing costs of a path except its first vertex, C_I-side duration phi(w), C_G-side
duration phi(e), no central flights. Cities dominated in (d, dbar, c) are dropped, which keeps the clique
front (exact-front.md, Proposition 6.14), and the clique instance is solved by zeno; only instances on
which zeno reports an exact front are compared.

By Propositions 6.12 and 6.13 of exact-front.md, every point of the reduced front is attained by a plan of
the graph and both fronts have the same least cost, so the exact front of the graph lies at makespans up
to that of the reduced front's cheapest point, which is the time cap given to graph_truth.

usage:
  python3 general_graph.py example <checks dir> <zeno>
      three instances of §6.6. Example 6.11: both fronts (also with planes ending anywhere), the reduced front
      also by graph_truth on the star graph of the virtual cities, the note's plan simulated (one plane flies
      I a b a b G; every passenger changes planes at most once) and a relay assignment on the same routes, and
      the front of f(U) with its central flights back. The bucket brigade (path with unit durations, t = 4,
      p = 3): the same. The inner point (two spokes): both fronts, the reduced one missing (31, 11). With
      highspy, the flow model as a second oracle on all three, every flow plan simulated
  python3 general_graph.py validate <checks dir> <zeno> <trials> <seed>
      graph_truth on clique instances against bin/truth (central flights none, a1, tight) and, without
      central flights, against zeno on the reduced instance
  python3 general_graph.py sweep <checks dir> <zeno> <trials> <seed> [family]
      reduced front against the exact front on random tiny graphs; family in
      line, spokes, cycle, random, hubadj, brigade, all (default)
  python3 general_graph.py xflow <checks dir> <trials> <seed>
      graph_truth against the flow model on random tiny graphs, every flow plan simulated (needs highspy)
  python3 general_graph.py subpath <checks dir> <zeno> <trials> <seed>
      the reduced front with all virtual cities, with Pareto paths only (the paper's second claim), and
      after dominance pruning, by zeno; and by graph_truth on the star graph when it is small enough
"""
import os
import random
import subprocess
import sys
import tempfile

# ---------------------------------------------------------------- graphs


def name(v, n):
    return "I" if v == 0 else ("G" if v == n + 1 else str(v))


def edge_arg(n, edges):
    return ",".join(f"{name(u, n)}-{name(v, n)}:{d}" for (u, v), d in sorted(edges.items()))


def neighbours(n, edges):
    adj = {v: [] for v in range(n + 2)}
    for (u, v), d in edges.items():
        adj[u].append((v, d))
        adj[v].append((u, d))
    return adj


def connected(n, edges):
    adj = neighbours(n, edges)
    seen, stack = {0}, [0]
    while stack:
        u = stack.pop()
        for v, _ in adj[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == n + 2


def landing(c, n, v):
    return c[v - 1] if 1 <= v <= n else 0


def simple_paths(n, edges, src, dst):
    adj = neighbours(n, edges)
    out = []

    def go(path, dur):
        u = path[-1]
        if u == dst:
            out.append((tuple(path), dur))
            return
        for v, d in adj[u]:
            if v not in path:
                path.append(v)
                go(path, dur + d)
                path.pop()
    go([src], 0)
    return out


def omega(path, c, n):
    return sum(landing(c, n, v) for v in path[1:])


def pareto_paths(paths, c, n):
    pts = [(omega(w, c, n), dur, w) for w, dur in paths]
    return [(w, dw) for (cw, dw, w) in pts
            if not any((cx <= cw and dx <= dw) and (cx, dx) != (cw, dw) for (cx, dx, _) in pts)]


def reduce(n, edges, c, pareto=False):
    """Virtual cities (d, dbar, cost, w, e) of §2.4, central vertices only."""
    cities = []
    for i in range(1, n + 1):
        W = simple_paths(n, edges, 0, i)
        E = simple_paths(n, edges, i, n + 1)
        if pareto:
            W, E = pareto_paths(W, c, n), pareto_paths(E, c, n)
        for w, dw in W:
            for e, de in E:
                cities.append((dw, de, omega(w, c, n) + omega(e, c, n), w, e))
    return cities


def prune(cities):
    """Drop cities dominated in (d, dbar, c); keep one of each class of equal cities."""
    keys = sorted({(d, db, cc) for d, db, cc, *_ in cities})
    return [k for k in keys
            if not any(o != k and o[0] <= k[0] and o[1] <= k[1] and o[2] <= k[2] for o in keys)]


# ---------------------------------------------------------------- solvers


def parse_front(out):
    return [tuple(map(int, l.split())) for l in out.strip().splitlines() if l.strip()]


def zeno_front(zeno, cities, t, p):
    """Front of the clique instance with these cities and no central flights; (front, exact)."""
    cities = sorted((d, db, cc) for d, db, cc in cities)  # by C_I-side duration, as the other check scripts do
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "r.dat")
        with open(path, "w") as f:
            for col in range(3):
                f.write(" ".join(str(x[col]) for x in cities) + "\n")
        r = subprocess.run([zeno, "-n", str(len(cities)), "-t", str(t), "-p", str(p), "-d", path],
                           capture_output=True, text=True, timeout=900, check=True)
    exact = "the front is a bracket" not in r.stderr
    return sorted(parse_front(r.stdout), key=lambda x: x[1]), exact


def graph_front(checks, n, edges, c, t, p, cap, anywhere=False):
    env = dict(os.environ)
    if anywhere:
        env["ANYWHERE"] = "1"
    r = subprocess.run([f"{checks}/bin/graph_truth", edge_arg(n, edges), ",".join(map(str, c)), str(t), str(p), str(cap)],
                       capture_output=True, text=True, timeout=1800, check=True, env=env)
    return sorted(parse_front(r.stdout), key=lambda x: x[1])


def star(cities):
    """The clique instance of the cities as a graph: I - v - G for every city v."""
    m = len(cities)
    edges = {}
    for k, (d, db, _cc) in enumerate(cities, start=1):
        edges[(0, k)] = d
        edges[(k, m + 1)] = db
    return m, edges, [cc for _d, _db, cc in cities]


def with_central(n, edges, cities):
    """The star graph of the cities (d, dbar, c, w, e) plus, between cities at distinct vertices i and i',
    a central flight lasting the distance from i to i' in the graph: f(U) with its central flights back."""
    adj = neighbours(n, edges)

    def dist(src):
        best, todo = {src: 0}, [src]
        while todo:  # Bellman-Ford style relaxation; the graphs are tiny
            u = todo.pop()
            for v, d in adj[u]:
                if best[u] + d < best.get(v, 1 << 30):
                    best[v] = best[u] + d
                    todo.append(v)
        return best
    m, star_edges, costs = star([x[:3] for x in cities])
    for a in range(m):
        da = dist(cities[a][3][-1])
        for b in range(a + 1, m):
            i2 = cities[b][3][-1]
            if i2 != cities[a][3][-1]:
                star_edges[(a + 1, b + 1)] = da[i2]
    return m, star_edges, costs


def dominated_by(a, front):
    """Is the point a weakly dominated by a point of front?"""
    return any(f[0] <= a[0] and f[1] <= a[1] for f in front)


# ---------------------------------------------------------------- flow model (second oracle)


def flow_min_cost(n, edges, c, t, p, M):
    """Least cost of a plan of makespan <= M, and one such plan (routes, journeys); None if none.

    Plans with integer durations >= 1 are the integer flows of the time-expanded network: p plane units
    and t passenger units from (I, 0) to (G, M), waiting arcs everywhere, at most as many passengers as
    planes on every flight arc, no passenger flight into I or out of G (clean journeys, Lemma 3.1)."""
    import highspy
    G = n + 1
    arcs = []  # (a, ta, b, tb, flight)
    for tau in range(M):
        for a in range(n + 2):
            arcs.append((a, tau, a, tau + 1, False))
    for tau in range(M + 1):
        for (u, v), d in edges.items():
            for a, b in ((u, v), (v, u)):
                if tau + d <= M:
                    arcs.append((a, tau, b, tau + d, True))
    out_arcs, in_arcs = {}, {}
    for k, (a, ta, b, tb, fl) in enumerate(arcs):
        out_arcs.setdefault((a, ta), []).append(k)
        in_arcs.setdefault((b, tb), []).append(k)
    nodes = set(out_arcs) | set(in_arcs)
    for presolve in ("choose", "off"):
        h = highspy.Highs()
        h.setOptionValue("output_flag", False)
        h.setOptionValue("presolve", presolve)
        h.setOptionValue("mip_rel_gap", 0.0)
        h.setOptionValue("mip_abs_gap", 0.0)
        inf = highspy.kHighsInf
        nA = len(arcs)
        for (a, ta, b, tb, fl) in arcs:
            h.addCol(landing(c, n, b) if fl else 0, 0, p, 0, [], [])
        for (a, ta, b, tb, fl) in arcs:
            h.addCol(0, 0, 0 if fl and (b == 0 or a == G) else t, 0, [], [])
        h.changeColsIntegrality(2 * nA, list(range(2 * nA)), [highspy.HighsVarType.kInteger] * (2 * nA))
        for off, units in ((0, p), (nA, t)):
            for node in nodes:
                o, i = out_arcs.get(node, []), in_arcs.get(node, [])
                rhs = units if node == (0, 0) else (-units if node == (G, M) else 0)
                h.addRow(rhs, rhs, len(o) + len(i), [off + k for k in o] + [off + k for k in i],
                         [1.0] * len(o) + [-1.0] * len(i))
        for k, arc in enumerate(arcs):
            if arc[4]:
                h.addRow(-inf, 0, 2, [nA + k, k], [1.0, -1.0])
        h.run()
        st = h.getModelStatus()
        if st == highspy.HighsModelStatus.kInfeasible:
            return None
        if st == highspy.HighsModelStatus.kOptimal:
            break
    else:
        raise RuntimeError("HiGHS failed")
    sol = h.getSolution().col_value
    y = [round(v) for v in sol[:nA]]
    z = [round(v) for v in sol[nA:]]
    cost = sum(landing(c, n, arc[2]) * y[k] for k, arc in enumerate(arcs) if arc[4])
    return cost, *decompose(n, arcs, y, z, p, t, M)


def decompose(n, arcs, y, z, p, t, M):
    G = n + 1
    out = {}
    for k, (a, ta, b, tb, fl) in enumerate(arcs):
        out.setdefault((a, ta), []).append(k)
    rem, routes = list(y), []
    for _ in range(p):
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


def flow_front(n, edges, c, t, p, Mmax):
    pts, plans = [], []
    for M in range(1, Mmax + 1):
        r = flow_min_cost(n, edges, c, t, p, M)
        if r is None:
            continue
        cost, routes, journeys = r
        cc, mm = simulate(n, edges, c, t, p, routes, journeys)
        assert cc == cost and mm <= M, (cc, cost, mm, M)
        if not pts or cost < pts[-1][0]:
            pts.append((cost, M))
            plans.append((routes, journeys))
    return pts, plans


# ---------------------------------------------------------------- simulation


def simulate(n, edges, c, t, p, routes, journeys):
    """Check a plan against §1.2 on the graph; return (cost, makespan) or raise AssertionError.

    routes[q] is a list of legs (a, b, depart, arrive); journeys[k] a list of (plane, leg index)."""
    G = n + 1
    dur = {}
    for (u, v), d in edges.items():
        dur[(u, v)] = dur[(v, u)] = d
    assert len(routes) == p
    cost = makespan = 0
    for legs in routes:
        assert legs, "empty route"
        here, clock = 0, 0
        for (a, b, ta, tb) in legs:
            assert a == here, "route not contiguous"
            assert (a, b) in dur, "no such flight"
            assert ta >= clock and tb == ta + dur[(a, b)], "bad timing"
            here, clock = b, tb
            cost += landing(c, n, b)
        assert here == G, "route does not end in G"
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
                assert a == 0, "journey does not start in I"
            else:
                pa, pb, pta, ptb = routes[prev[0]][prev[1]]
                assert pb == a and ta >= ptb, "journey not contiguous"
                if prev[0] == q:
                    assert j > prev[1], "journey goes back along a route"
            prev = (q, j)
        assert routes[prev[0]][prev[1]][1] == G, "journey does not end in G"
    return cost, makespan


def show_plan(n, routes, journeys):
    for q, legs in enumerate(routes):
        print(f"    plane {q + 1}:", "  ".join(f"{name(a, n)}->{name(b, n)}[{x},{y}]" for a, b, x, y in legs))
    for k, legs in enumerate(journeys):
        print(f"    passenger {k + 1}:", ", ".join(f"plane {q + 1} {name(routes[q][j][0], n)}->{name(routes[q][j][1], n)}" for q, j in legs))


# ---------------------------------------------------------------- the counterexample

# Line I - a - b - G with durations 1, 2, 1 and costs 1, 1; t = 3, p = 2 (Example 6.11). Plane 1 flies
# I a b a b G: one segment that drops a passenger at b, flies the central edge b -> a and picks another up
# at a, which f(U), without central flights, cannot do.
EX = dict(n=2, edges={(0, 1): 1, (1, 2): 2, (2, 3): 1}, c=[1, 1], t=3, p=2)
EX_ROUTES = [
    [(0, 1, 0, 1), (1, 2, 1, 3), (2, 1, 3, 5), (1, 2, 5, 7), (2, 3, 7, 8)],
    [(0, 1, 0, 1), (1, 0, 1, 2), (0, 1, 2, 3), (1, 2, 3, 5), (2, 3, 5, 6), (3, 2, 6, 7), (2, 3, 7, 8)],
]
# The note's witness: every passenger changes planes at most once.
EX_JOURNEYS = [
    [(1, 2), (1, 3), (1, 4)],
    [(0, 0), (0, 1), (1, 6)],
    [(1, 0), (0, 3), (0, 4)],
]
# The same routes with a relay: passenger 3 rides plane 2 from I to a, plane 1 from a to b, plane 2 to G.
EX_JOURNEYS_RELAY = [
    [(0, 0), (0, 3), (0, 4)],
    [(1, 2), (1, 3), (1, 4)],
    [(1, 0), (0, 1), (1, 6)],
]
# Bucket brigade: the same line with durations 1, 1, 1, t = 4, p = 3. Plane 2 flies I a b a b G.
BRIG = dict(n=2, edges={(0, 1): 1, (1, 2): 1, (2, 3): 1}, c=[1, 1], t=4, p=3)
BRIG_ROUTES = [
    [(0, 1, 0, 1), (1, 0, 1, 2), (0, 1, 2, 3), (1, 2, 3, 4), (2, 3, 4, 5)],
    [(0, 1, 0, 1), (1, 2, 1, 2), (2, 1, 2, 3), (1, 2, 3, 4), (2, 3, 4, 5)],
    [(0, 1, 0, 1), (1, 2, 1, 2), (2, 3, 2, 3), (3, 2, 3, 4), (2, 3, 4, 5)],
]
# At most one change per passenger.
BRIG_JOURNEYS = [
    [(2, 0), (2, 1), (2, 2)],
    [(1, 0), (1, 1), (2, 4)],
    [(0, 0), (1, 3), (1, 4)],
    [(0, 2), (0, 3), (0, 4)],
]
# A relay through all three planes: passenger 4 rides plane 1 to a, plane 2 to b and plane 3 to G.
BRIG_JOURNEYS_RELAY = [
    [(0, 2), (0, 3), (0, 4)],
    [(1, 0), (1, 3), (1, 4)],
    [(2, 0), (2, 1), (2, 2)],
    [(0, 0), (1, 1), (2, 4)],
]


def changes(journeys):
    """Largest number of plane changes of a passenger."""
    return max(sum(1 for k in range(1, len(j)) if j[k][0] != j[k - 1][0]) for j in journeys)
# An inner point: spokes I-1-2-G (durations 1, 2, 3) and I-3-4-G (1, 1, 1); the reduced front misses (31, 11).
INNER = dict(n=4, edges={(0, 1): 1, (1, 2): 2, (2, 5): 3, (0, 3): 1, (3, 4): 1, (4, 5): 1}, c=[3, 4, 5, 5], t=3, p=2)


def have_highspy():
    try:
        import highspy  # noqa: F401
        return True
    except ImportError:
        return False


def example(checks, zeno):
    e = EX
    n, edges, c, t, p = e["n"], e["edges"], e["c"], e["t"], e["p"]
    print("graph:", edge_arg(n, edges), " costs", c, f" t={t} p={p}")
    cities = reduce(n, edges, c)
    print("virtual cities (d, dbar, c, w, e):")
    for d, db, cc, w, ee in cities:
        print(f"    ({d}, {db}, {cc})  w = {'-'.join(name(v, n) for v in w)}  e = {'-'.join(name(v, n) for v in ee)}")
    red, exact = zeno_front(zeno, prune(cities), t, p)
    print("reduced front by zeno:", red, "exact" if exact else "BRACKET")
    m, se, sc = star(prune(cities))
    print("reduced front by graph_truth on the star graph:", graph_front(checks, m, se, sc, t, p, 30))
    print("  planes ending anywhere:", graph_front(checks, m, se, sc, t, p, 30, anywhere=True))
    print("exact front of the graph by graph_truth (time cap 30):", graph_front(checks, n, edges, c, t, p, 30))
    print("  planes ending anywhere:", graph_front(checks, n, edges, c, t, p, 30, anywhere=True))
    print("plan of the note, simulated (cost, makespan):", simulate(n, edges, c, t, p, EX_ROUTES, EX_JOURNEYS),
          " most changes per passenger:", changes(EX_JOURNEYS))
    show_plan(n, EX_ROUTES, EX_JOURNEYS)
    print("same routes with a relay, simulated:", simulate(n, edges, c, t, p, EX_ROUTES, EX_JOURNEYS_RELAY),
          " most changes per passenger:", changes(EX_JOURNEYS_RELAY))
    m, se, sc = with_central(n, edges, cities)
    print("f(U) with central flights back, by graph_truth:", graph_front(checks, m, se, sc, t, p, 30))
    if have_highspy():
        pts, plans = flow_front(n, edges, c, t, p, 12)
        print("exact front of the graph by the flow model (makespan <= 12), plans simulated:", pts)
        for (cc, mm), (routes, journeys) in zip(pts, plans):
            print(f"  flow plan for ({cc}, {mm}):")
            show_plan(n, routes, journeys)
    else:
        print("(highspy not installed: flow model skipped)")
    b = BRIG
    n, edges, c, t, p = b["n"], b["edges"], b["c"], b["t"], b["p"]
    print("\nbucket brigade:", edge_arg(n, edges), " costs", c, f" t={t} p={p}")
    cities = reduce(n, edges, c)
    red, exact = zeno_front(zeno, prune(cities), t, p)
    print("reduced front by zeno:", red, "exact" if exact else "BRACKET")
    print("exact front of the graph by graph_truth:", graph_front(checks, n, edges, c, t, p, 30))
    print("plan of the note, simulated (cost, makespan):", simulate(n, edges, c, t, p, BRIG_ROUTES, BRIG_JOURNEYS),
          " most changes per passenger:", changes(BRIG_JOURNEYS))
    show_plan(n, BRIG_ROUTES, BRIG_JOURNEYS)
    print("same routes with a relay through three planes, simulated:",
          simulate(n, edges, c, t, p, BRIG_ROUTES, BRIG_JOURNEYS_RELAY), " most changes per passenger:", changes(BRIG_JOURNEYS_RELAY))
    m, se, sc = with_central(n, edges, cities)
    print("f(U) with central flights back, by graph_truth:", graph_front(checks, m, se, sc, t, p, 30))
    if have_highspy():
        print("flow model (makespan <= 8):", flow_front(n, edges, c, t, p, 8)[0])
    q = INNER
    n, edges, c, t, p = q["n"], q["edges"], q["c"], q["t"], q["p"]
    print("\ninner point:", edge_arg(n, edges), " costs", c, f" t={t} p={p}")
    red, exact = zeno_front(zeno, prune(reduce(n, edges, c)), t, p)
    print("reduced front by zeno:", red, "exact" if exact else "BRACKET")
    print("exact front of the graph by graph_truth:", graph_front(checks, n, edges, c, t, p, red[-1][1]))
    if have_highspy():
        pts, plans = flow_front(n, edges, c, t, p, red[-1][1])
        print("flow model, plans simulated:", pts)
        for (cc, mm), (routes, journeys) in zip(pts, plans):
            if not dominated_by((cc, mm), red):
                print(f"  flow plan for ({cc}, {mm}), which the reduced front misses:")
                show_plan(n, routes, journeys)


# ---------------------------------------------------------------- random instances


def rand_costs(rng, n):
    return [rng.choice([0, rng.randint(0, 6)]) if rng.random() < 0.2 else rng.randint(1, 6) for _ in range(n)]


def gen(rng, family, maxD=3):
    """(n, edges) for a random graph of the family; vertices 0 = I, 1..n, n+1 = G."""
    D = lambda: rng.randint(1, maxD)
    if family == "line":
        n = rng.randint(2, 4)
        return n, {(k, k + 1): D() for k in range(n + 1)}
    if family == "brigade":  # a line with one long inner edge, or two lines in parallel
        n = rng.randint(2, 4)
        edges = {(k, k + 1): rng.randint(1, 2) for k in range(n + 1)}
        k = rng.randint(1, n - 1)
        edges[(k, k + 1)] = rng.randint(2, 5)
        if n == 4 and rng.random() < 0.5:  # I-1-2-G and I-3-4-G
            edges = {(0, 1): D(), (1, 2): rng.randint(2, 5), (2, 5): D(), (0, 3): D(), (3, 4): D(), (4, 5): D()}
        return n, edges
    if family == "spokes":  # parallel I-G routes with one or two central vertices
        while True:
            lens = []
            while sum(lens) < 4 and (not lens or rng.random() < 0.8):
                lens.append(rng.choice([1, 2]))
            if sum(lens) <= 4 and 2 in lens:
                break
        n = sum(lens)
        edges, v = {}, 1
        for L in lens:
            if L == 1:
                edges[(0, v)] = D(); edges[(v, n + 1)] = D(); v += 1
            else:
                edges[(0, v)] = D(); edges[(v, v + 1)] = D(); edges[(v + 1, n + 1)] = D(); v += 2
        return n, edges
    if family == "cycle":
        n = rng.randint(2, 4)
        n1 = rng.randint(1, n - 1)
        order = [0] + list(range(1, n1 + 1)) + [n + 1] + list(range(n1 + 1, n + 1))
        return n, {tuple(sorted((order[k], order[(k + 1) % len(order)]))): D() for k in range(len(order))}
    if family == "random":
        while True:
            n = rng.randint(2, 4)
            q = rng.uniform(0.3, 0.8)
            edges = {}
            for u in range(n + 2):
                for v in range(u + 1, n + 2):
                    if (u, v) != (0, n + 1) and rng.random() < q:
                        edges[(u, v)] = D()
            if connected(n, edges):
                return n, edges
    if family == "hubadj":  # every central vertex joined to both hubs, central edges under (A1-NS)
        n = rng.randint(2, 4)
        edges = {}
        for i in range(1, n + 1):
            edges[(0, i)] = D(); edges[(i, n + 1)] = D()
        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):
                if rng.random() < 0.5:
                    lo = min(edges[(0, i)] + edges[(0, j)], edges[(i, n + 1)] + edges[(j, n + 1)])
                    edges[(i, j)] = lo + rng.randint(0, 1)
        return n, edges
    raise ValueError(family)


FAMILIES = ["line", "spokes", "cycle", "random", "hubadj", "brigade"]


def sweep(checks, zeno, trials, seed, family="all"):
    rng = random.Random(seed)
    fams = FAMILIES if family == "all" else [family]
    stats = {f: [0, 0, 0, 0, 0] for f in fams}  # instances, reduced exact, compared, p >= 2 and t > p, differ
    examples, inner = [], []
    predicted = 0
    for k in range(trials):
        fam = fams[k % len(fams)]
        n, edges = gen(rng, fam)
        c = rand_costs(rng, n)
        p = rng.randint(1, 3)
        t = rng.randint(p, 4)
        stats[fam][0] += 1
        cities = prune(reduce(n, edges, c))
        red, exact = zeno_front(zeno, cities, t, p)
        if not exact:
            continue
        stats[fam][1] += 1
        cap = red[-1][1]  # makespan of the reduced front's cheapest point
        real = graph_front(checks, n, edges, c, t, p, cap)
        stats[fam][2] += 1
        # Proposition 6.12: the reduced points are attained; Proposition 6.13: same least cost.
        assert all(dominated_by(a, real) for a in red), ("reduced point not attained", n, edges, c, t, p, red, real)
        assert real[-1][0] == red[-1][0], ("least costs differ", n, edges, c, t, p, red, real)
        if fam == "hubadj" or p == 1 or t == p:  # Proposition 6.15
            predicted += 1
            assert real == red, ("Proposition 6.15 fails", n, edges, c, t, p, red, real)
        if p >= 2 and t > p:
            stats[fam][3] += 1
        if real != red:
            stats[fam][4] += 1
            item = (n + t + p + sum(edges.values()), fam, n, edges, c, t, p, red, real)
            examples.append(item)
            if any(not dominated_by(a, red) for a in real if a[0] > real[-1][0]):
                inner.append(item)  # the reduced front misses a point other than the cheapest one
        if (k + 1) % 50 == 0:
            print(f"  {k + 1} / {trials}", flush=True)
    for f in fams:
        a, b, cmp, rest, d = stats[f]
        print(f"{f:8s} instances {a:5d}  reduced front exact {b:5d}  compared {cmp:5d}  "
              f"with p >= 2 and t > p {rest:5d}  fronts differ {d:5d}")
    print(f"every reduced point attained and equal least costs on all compared instances; "
          f"Proposition 6.15 cases (hub-adjacent, p = 1 or t = p): {predicted}, all equal; "
          f"{len(inner)} of the differing fronts miss a point other than the cheapest one")
    for _, fam, n, edges, c, t, p, red, real in sorted(examples, key=lambda x: x[0])[:6]:
        print(f"  [{fam}] {edge_arg(n, edges)} c={c} t={t} p={p}: reduced {red}  exact {real}")
    print("smallest fronts missing a point other than the cheapest one:")
    for _, fam, n, edges, c, t, p, red, real in sorted(inner, key=lambda x: x[0])[:3]:
        print(f"  [{fam}] {edge_arg(n, edges)} c={c} t={t} p={p}: reduced {red}  exact {real}")


def validate(checks, zeno, trials, seed):
    """graph_truth on clique graphs against bin/truth, and (no central flights) against zeno on f(Π)."""
    rng = random.Random(seed)
    eq_truth = eq_red = n_red = 0
    for _ in range(trials):
        p = rng.randint(1, 3)
        t = rng.randint(p, 4)
        n = rng.randint(1, 3)
        west = [rng.randint(1, 4) for _ in range(n)]
        east = list(west) if rng.random() < 0.5 else [rng.randint(1, 4) for _ in range(n)]
        c = [rng.randint(0, 6) for _ in range(n)]
        mode = rng.choice(["none", "a1", "tight"])
        edges = {}
        for i in range(1, n + 1):
            edges[(0, i)] = west[i - 1]
            edges[(i, n + 1)] = east[i - 1]
        for i in range(n):
            for j in range(i + 1, n):
                if mode == "a1":
                    edges[(i + 1, j + 1)] = max(west[i] + west[j], east[i] + east[j]) + 1
                elif mode == "tight":
                    edges[(i + 1, j + 1)] = max(abs(west[i] - west[j]), abs(east[i] - east[j]), 1)
        s = 2 * t - p
        cap = s * max(west[i] + east[i] for i in range(n))  # truth's time cap
        out = subprocess.run([f"{checks}/bin/truth", ",".join(map(str, west)), ",".join(map(str, east)),
                              ",".join(map(str, c)), str(t), str(p), mode, str(2 * t)],
                             capture_output=True, text=True, timeout=1800, check=True).stdout
        tf = sorted(parse_front(out), key=lambda x: x[1])
        gf = graph_front(checks, n, edges, c, t, p, cap)
        if tf == gf:
            eq_truth += 1
        else:
            print("MISMATCH truth", edge_arg(n, edges), c, t, p, mode, tf, gf, flush=True)
        if mode != "tight":  # (A1-NS) holds: Proposition 6.15 predicts equal fronts
            red, exact = zeno_front(zeno, prune(reduce(n, edges, c)), t, p)
            if exact:
                n_red += 1
                if red == gf:
                    eq_red += 1
                else:
                    print("MISMATCH reduced", edge_arg(n, edges), c, t, p, mode, red, gf, flush=True)
    print(f"graph_truth = truth on {eq_truth} / {trials} clique instances; "
          f"= reduced front (zeno, exact) on {eq_red} / {n_red} of them without useful central flights")


def xflow(checks, trials, seed):
    rng = random.Random(seed)
    equal = 0
    for k in range(trials):
        fam = FAMILIES[k % len(FAMILIES)]
        n, edges = gen(rng, fam)
        c = rand_costs(rng, n)
        p = rng.randint(1, 3)
        t = rng.randint(p, 3)
        cap = 2 * (2 * t - p) * max(edges.values()) + 4
        gf = graph_front(checks, n, edges, c, t, p, cap)
        ff, _plans = flow_front(n, edges, c, t, p, cap)
        if gf == ff:
            equal += 1
        else:
            print("MISMATCH", fam, edge_arg(n, edges), c, t, p, gf, ff, flush=True)
    print(f"graph_truth = flow model on {equal} / {trials} graphs (every flow plan simulated)")


def subpath(checks, zeno, trials, seed):
    rng = random.Random(seed)
    same = small = star_same = star_n = 0
    for k in range(trials):
        fam = FAMILIES[k % len(FAMILIES)]
        n, edges = gen(rng, fam)
        c = rand_costs(rng, n)
        p = rng.randint(1, 3)
        t = rng.randint(p, 4)
        full = sorted({x[:3] for x in reduce(n, edges, c)})
        par = sorted({x[:3] for x in reduce(n, edges, c, pareto=True)})
        pr = prune(full)
        if len(full) > 40:
            continue
        small += 1
        fa, ea = zeno_front(zeno, full, t, p)
        fb, eb = zeno_front(zeno, par, t, p)
        fc, ec = zeno_front(zeno, pr, t, p)
        if ea and eb and ec and fa == fb == fc:
            same += 1
        else:
            print("DIFF", fam, edge_arg(n, edges), c, t, p, fa, ea, fb, eb, fc, ec, flush=True)
        if len(pr) <= 4:
            star_n += 1
            m, se, sc = star(pr)
            if graph_front(checks, m, se, sc, t, p, fc[-1][1]) == fc:
                star_same += 1
            else:
                print("STAR DIFF", fam, edge_arg(n, edges), c, t, p, fc, flush=True)
    print(f"all cities = Pareto paths = pruned on {same} / {small} reduced instances with at most 40 cities; "
          f"star graph by graph_truth = zeno on {star_same} / {star_n} of them with at most 4 cities after pruning")


if __name__ == "__main__":
    a = sys.argv
    if len(a) >= 4 and a[1] == "example":
        example(a[2], a[3])
    elif len(a) >= 6 and a[1] == "validate":
        validate(a[2], a[3], int(a[4]), int(a[5]))
    elif len(a) >= 6 and a[1] == "sweep":
        sweep(a[2], a[3], int(a[4]), int(a[5]), a[6] if len(a) > 6 else "all")
    elif len(a) >= 5 and a[1] == "xflow":
        xflow(a[2], int(a[3]), int(a[4]))
    elif len(a) >= 6 and a[1] == "subpath":
        subpath(a[2], a[3], int(a[4]), int(a[5]))
    else:
        print(__doc__)
