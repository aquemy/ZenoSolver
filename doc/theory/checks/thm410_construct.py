"""The construction in the proof of Theorem 4.10 (converse under (S) and (AΔ)), run on plans.

`construct` follows the proof step by step on a feasible plan (routes as legs
(a, b, depart, arrive), journeys as lists of (plane, leg index)) and returns an
admissible partition X_1..X_p of a multiset of size s = 2t - p in which every
element is paid by a distinct central landing of the plan at the same city, with
2 d(X_k) <= F_k. Every claim of the proof is asserted on the way: F(γ) >= 2R(γ),
journeys inside sharing components, sigma_K >= 2t_K - q_K and the parity of N_K, a
plane with two segments in odd components, the T-join, the invariants of the
re-pairing (cities within R, exclusive payments at the right city, an own landing
kept by every segment), the integer parity matrix, the shrinking, cost and loads.

The driver draws plans with the flow model (flowplan.py): random symmetric
instances, random central tables satisfying (AΔ) (or the tightest one), a random
makespan bound, and either the landing costs or random arc weights that favour
central flights (wasteful plans with many central legs). To exercise the
re-pairing, the T-join is extended by random closed walks of the sharing graph,
which keep every plane's parity.

usage: python3 thm410_construct.py <trials> <seed>
"""
import random
import sys
import traceback
from collections import defaultdict

from flowplan import min_cost, simulate


class Failure(Exception):
    pass


def check(cond, what):
    if not cond:
        raise Failure(what)


def segments_of(route, n):
    """Segments of a route: (landings as (leg index, city), flight time), split at hub arrivals."""
    segs, cur, curF = [], [], 0
    for j, (a, b, ta, tb) in enumerate(route):
        curF += tb - ta
        if 1 <= b <= n:
            cur.append((j, b))
        else:
            segs.append((cur, curF))
            cur, curF = [], 0
    check(not cur, "route does not end in a hub")
    return segs


def clean_journeys(routes, journeys, n):
    """Lemma 3.1: from the last leg departing C_I to the first later leg arriving in C_G."""
    out = []
    for legs in journeys:
        last_i = max(i for i, (q, j) in enumerate(legs) if routes[q][j][0] == 0)
        first_g = next(i for i in range(last_i, len(legs)) if routes[legs[i][0]][legs[i][1]][1] == n + 1)
        out.append(legs[last_i:first_g + 1])
    return out


def construct(d, c, t, p, routes, journeys, rng=None, extra_walks=0):
    n, s = len(d), 2 * t - p
    dd = lambda y: d[y - 1]
    rng = rng or random.Random(0)
    # ---- segments, R(γ), flight times ----
    seg_plane, seg_land, seg_F, landings = [], [], [], []
    plane_segs = [[] for _ in range(p)]
    for k, route in enumerate(routes):
        for lands, f in segments_of(route, n):
            check(lands, "segment without a central landing")
            g = len(seg_plane)
            seg_plane.append(k)
            seg_land.append([])
            for (j, y) in lands:
                seg_land[g].append(len(landings))
                landings.append((k, j, y))
            seg_F.append(f)
            plane_segs[k].append(g)
    nseg = len(seg_plane)
    R = [max(dd(landings[l][2]) for l in seg_land[g]) for g in range(nseg)]
    for g in range(nseg):
        check(seg_F[g] >= 2 * R[g], "F(γ) < 2R(γ): Lemma 3.3(b) needs (S) and (AΔ)")
    sigma = [len(plane_segs[k]) for k in range(p)]
    check(sum(sigma) >= s, "Lemma 3.2")
    # ---- Step 1: sharing components, counting, T ----
    parent = list(range(p))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    visits = defaultdict(list)  # city -> [(segment, landing)]
    for g in range(nseg):
        for l in seg_land[g]:
            visits[landings[l][2]].append((g, l))
    for lst in visits.values():
        for (g, l) in lst[1:]:
            parent[find(seg_plane[g])] = find(seg_plane[lst[0][0]])
    comps = defaultdict(list)
    for k in range(p):
        comps[find(k)].append(k)
    tK = defaultdict(int)
    for legs in clean_journeys(routes, journeys, n):
        roots = {find(q) for q, j in legs}
        check(len(roots) == 1, "a clean journey leaves its sharing component")
        tK[roots.pop()] += 1
    T = {k for k in range(p) if sigma[k] % 2 == 0}
    dropped_planes = []
    for r, ks in comps.items():
        deltaK = sum(sigma[k] for k in ks) - (2 * tK[r] - len(ks))
        check(deltaK >= 0, "sigma_K >= 2 t_K - q_K")
        check(sum(1 for k in ks if sigma[k] % 2 == 0) % 2 == deltaK % 2, "N_K and delta_K have the same parity")
        if deltaK % 2:
            cand = [k for k in ks if sigma[k] >= 2]
            check(cand, "an odd component has a plane with two segments")
            k0 = rng.choice(cand)
            dropped_planes.append(k0)
            T ^= {k0}
    # ---- Step 2: T-join in a spanning forest of the sharing graph, with witnesses ----
    wit = defaultdict(list)
    for y, lst in visits.items():
        for (g1, l1) in lst:
            for (g2, l2) in lst:
                if seg_plane[g1] != seg_plane[g2]:
                    wit[(seg_plane[g1], seg_plane[g2])].append((g1, g2, y))
    nbrs = defaultdict(set)
    for (u, w) in wit:
        nbrs[u].add(w)
    seen, order, par = set(), [], {}
    for r in rng.sample(range(p), p):
        if r in seen:
            continue
        seen.add(r)
        par[r] = None
        stack = [r]
        while stack:
            u = stack.pop()
            order.append(u)
            for w in rng.sample(sorted(nbrs[u]), len(nbrs[u])):
                if w not in seen:
                    seen.add(w)
                    par[w] = u
                    stack.append(w)
    odd = {k: k in T for k in range(p)}
    J = []
    for u in reversed(order):
        if par[u] is not None and odd[u]:
            J.append((u, par[u]))
            odd[u], odd[par[u]] = False, not odd[par[u]]
    check(not any(odd.values()), "every tree has an even number of T-planes")
    links, at, counter = {}, defaultdict(set), [0]  # link: [city, [seg, seg], [pay, pay]]

    def add(y, ga, pa, gb, pb):
        if seg_plane[ga] == seg_plane[gb]:
            return  # a loop at a plane changes its degree by 2: dropped
        e = counter[0]
        counter[0] += 1
        links[e] = [y, [ga, gb], [pa, pb]]
        at[ga].add(e)
        at[gb].add(e)

    def remove(e):
        _, (ga, gb), _ = links.pop(e)
        at[ga].discard(e)
        at[gb].discard(e)

    def side(e, g):
        return 0 if links[e][1][0] == g else 1

    def other(e, g):
        o = 1 - side(e, g)
        return links[e][1][o], links[e][2][o]

    for (u, w) in J:
        g1, g2, y = rng.choice(wit[(u, w)])
        add(y, g1, None, g2, None)
    for _ in range(extra_walks):  # closed walks: every plane's degree changes by an even number
        walk = [rng.randrange(p)]
        if not nbrs[walk[0]]:
            continue
        for _ in range(rng.randint(1, 5)):
            walk.append(rng.choice(sorted(nbrs[walk[-1]])))
        walk += list(reversed(walk[:-1]))
        for u, w in zip(walk, walk[1:]):
            g1, g2, y = rng.choice(wit[(u, w)])
            add(y, g1, None, g2, None)
    # pre-step: two ends of a segment at one city are re-paired; both partners visit that city
    changed = True
    while changed:
        changed = False
        for g in range(nseg):
            bycity = defaultdict(list)
            for e in at[g]:
                bycity[links[e][0]].append(e)
            for y, es in bycity.items():
                while len(es) >= 2:
                    e1, e2 = es.pop(), es.pop()
                    (ga, _), (gb, _) = other(e1, g), other(e2, g)
                    remove(e1)
                    remove(e2)
                    if ga != gb:
                        add(y, ga, None, gb, None)
                    changed = True
    # payments: each end gets an own landing at its city (distinct: one end per segment and city)
    for e, (y, ends, pays) in links.items():
        for i, g in enumerate(ends):
            own = [l for l in seg_land[g] if landings[l][2] == y]
            check(own, "an initial end at a city its segment does not visit")
            pays[i] = own[0]
    own_R = {g: next(l for l in seg_land[g] if dd(landings[l][2]) == R[g]) for g in range(nseg)}
    dropped = set()

    def invariants():
        held = {}
        for e, (y, ends, pays) in links.items():
            for g, l in zip(ends, pays):
                check(landings[l][2] == y, "payment at the wrong city")
                check(l not in held, "a landing pays two ends")
                check(dd(y) <= R[g], "an end violates R")
                held[l] = g
        for g in range(nseg):
            if g not in dropped:
                check(own_R[g] not in held or held[own_R[g]] == g, "a segment lost its R-landing")
        return held
    invariants()

    def repair(g, e1, e2):
        """Re-pair the ends e1 (city y1) and e2 of g, with d(y1) <= d(y2): the partner of e2 moves to y1."""
        y1 = links[e1][0]
        ga, pa = other(e1, g)
        gb, _ = other(e2, g)
        pay = links[e1][2][side(e1, g)]
        check(dd(y1) <= dd(links[e2][0]) <= R[gb], "the moved end stays within R")
        remove(e1)
        remove(e2)
        if ga != gb:
            add(y1, ga, pa, gb, pay)

    # ---- Step 3: one end per segment ----
    processed = set()
    while True:
        g = next((g for g in range(nseg) if len(at[g]) >= 2), None)
        if g is None:
            break
        check(g not in processed, "a segment processed twice")
        processed.add(g)
        es = sorted(at[g], key=lambda e: (dd(links[e][0]), links[e][2][side(e, g)] == own_R[g]))
        for i in range(0, len(es) - 1, 2):
            repair(g, es[i], es[i + 1])
        invariants()
    # ---- Step 4: leave out a segment of each chosen plane ----
    busy = 0
    for k0 in dropped_planes:
        free = [g for g in plane_segs[k0] if not at[g]]
        if free:
            dropped.add(free[0])
            continue
        busy += 1
        g1, g2 = plane_segs[k0][0], plane_segs[k0][1]
        e1, e2 = next(iter(at[g1])), next(iter(at[g2]))
        if dd(links[e1][0]) > dd(links[e2][0]):
            g1, g2, e1, e2 = g2, g1, e2, e1
        y1 = links[e1][0]
        ga, pa = other(e1, g1)
        gb, _ = other(e2, g2)
        pay = links[e1][2][side(e1, g1)]
        check(dd(y1) <= R[gb], "step C stays within R")
        remove(e1)
        remove(e2)
        if ga != gb:
            add(y1, ga, pa, gb, pay)
        dropped.add(g1)
    held = invariants()
    # ---- Step 5: selection and the integer parity matrix ----
    X = [[] for _ in range(p)]
    slot = {}
    hcount = defaultdict(int)
    for g in range(nseg):
        if g in dropped:
            check(not at[g], "a dropped segment holds an end")
            continue
        check(len(at[g]) <= 1, "a segment with two ends")
        if at[g]:
            e = next(iter(at[g]))
            y, pay = links[e][0], links[e][2][side(e, g)]
            hcount[(seg_plane[g], y)] += 1
        else:
            check(own_R[g] not in held, "a segment without a free own landing")
            pay = own_R[g]
            y = landings[pay][2]
        check(pay not in slot, "a landing pays two slots")
        slot[pay] = g
        check(dd(y) <= R[g], "a slot violates R")
        X[seg_plane[g]].append(y)
    for k in range(p):
        check(len(X[k]) >= 1, "an empty group")
        row = sum(v for (kk, y), v in hcount.items() if kk == k)
        check(row % 2 == (len(X[k]) + 1) % 2, "row parity")
        for (kk, y), v in hcount.items():
            if kk == k:
                check(v <= X[k].count(y), "h exceeds X")
    for y in range(1, n + 1):
        check(sum(v for (kk, yy), v in hcount.items() if yy == y) % 2 == 0, "column parity")
    size = sum(len(x) for x in X)
    check(size >= s and (size - s) % 2 == 0, "size before shrinking")
    check(admissible(X, n), "the component form disagrees")
    # ---- Lemma 4.11: shrink to size s ----
    Xs = shrink(X, n, s)
    check(sum(len(x) for x in Xs) == s and admissible(Xs, n), "shrinking")
    F = [sum(b - a for (_, _, a, b) in route) for route in routes]
    for k in range(p):
        check(all(Xs[k].count(y) <= X[k].count(y) for y in Xs[k]), "shrinking keeps sub-multisets")
        check(2 * sum(dd(y) for y in Xs[k]) <= F[k], "load exceeds flight time")
    check(sum(c[y - 1] for x in Xs for y in x) <= sum(c[y - 1] for (_, _, y) in landings), "cost")
    return Xs, {"central": any(len(seg_land[g]) > 1 for g in range(nseg)), "processed": len(processed),
                "dropped": len(dropped_planes), "busy": busy}


def admissible(X, n):
    """Lemma 2.4(a): non-empty groups, every component of H has an even number of even planes."""
    p = len(X)
    if any(not x for x in X):
        return False
    parent = list(range(p + n + 1))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for k in range(p):
        for y in X[k]:
            parent[find(k)] = find(p + y)
    count = defaultdict(int)
    for k in range(p):
        if len(X[k]) % 2 == 0:
            count[find(k)] += 1
    return all(v % 2 == 0 for v in count.values())


def parity_matrix(X, n):
    """A 0/1 parity matrix (Definition 2.2), by elimination over GF(2), or None."""
    p = len(X)
    cols = [(k, y) for k in range(p) for y in sorted(set(X[k]))]
    rows = [[1 if kk == k else 0 for (kk, y) in cols] + [(len(X[k]) + 1) % 2] for k in range(p)]
    rows += [[1 if yy == y else 0 for (kk, yy) in cols] + [0] for y in range(1, n + 1)]
    m, r, piv = len(cols), 0, []
    for col in range(m):
        pr = next((i for i in range(r, len(rows)) if rows[i][col]), None)
        if pr is None:
            continue
        rows[r], rows[pr] = rows[pr], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][col]:
                rows[i] = [a ^ b for a, b in zip(rows[i], rows[r])]
        piv.append(col)
        r += 1
    if any(not any(row[:m]) and row[m] for row in rows):
        return None
    return {cols[col] for i, col in enumerate(piv) if rows[i][m]}


def shrink(X, n, s):
    """Lemma 4.11: remove two landings at a time, keeping an admissible partition."""
    X = [list(x) for x in X]
    while sum(len(x) for x in X) > s:
        h = parity_matrix(X, n)
        check(h is not None, "no parity matrix")
        f = [len(X[k]) - sum(1 for (kk, y) in h if kk == k) for k in range(len(X))]
        k = next((k for k in range(len(X)) if f[k] >= 3), None)
        if k is not None:
            free = list(X[k])
            for (kk, y) in h:
                if kk == k:
                    free.remove(y)
            X[k].remove(free[0])
            X[k].remove(free[1])
            continue
        y = next(y for (k, y) in sorted(h))
        u, v = [k for (k, yy) in sorted(h) if yy == y][:2]
        X[u].remove(y)
        X[v].remove(y)
    return X


def random_table(rng, d, mode):
    n = len(d)
    if mode == "tight":
        return [[abs(d[i] - d[j]) if i != j else 0 for j in range(n)] for i in range(n)]
    D = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < 0.15:
                continue  # no flight
            lo = max(1, abs(d[i] - d[j]))
            D[i][j] = D[j][i] = rng.randint(lo, max(lo, d[i] + d[j]))
    for k in range(n):  # triangle inequality among existing central flights
        for i in range(n):
            for j in range(n):
                if i != j and D[i][k] and D[k][j] and D[i][j] and D[i][j] > D[i][k] + D[k][j]:
                    D[i][j] = D[i][k] + D[k][j]
    return D


def main():
    trials, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    ok = fail = none = central = processed = dropped = busy = 0
    for _ in range(trials):
        p = rng.randint(1, 6)
        t = rng.randint(p, 9)
        n = rng.randint(1, 5)
        d = sorted(rng.sample(range(1, 11), n))
        c = [rng.randint(0, 20) for _ in range(n)]
        D = random_table(rng, d, rng.choice(["tight", "tight", "random"]))
        kappa = -(-(2 * t - p) // p)
        M = rng.randint(2 * d[0] * kappa, 2 * d[-1] * kappa + 6)
        arc_cost = None
        if rng.random() < 0.7:
            w = {}

            def arc_cost(a, ta, b, tb, fl, w=w):
                if not fl:
                    return 0
                if (a, ta, b) not in w:
                    w[(a, ta, b)] = rng.randint(-6, 1) if 1 <= a <= n and 1 <= b <= n else rng.randint(-1, 6)
                return w[(a, ta, b)]
        try:
            r = min_cost(d, d, c, D, t, p, M, time_limit=120, arc_cost=arc_cost)
        except RuntimeError:
            r = None
        if r is None:
            none += 1
            continue
        cost, routes, journeys = r
        simulate(d, d, c, D, t, p, routes, journeys)
        try:
            X, st = construct(d, c, t, p, routes, journeys, rng=rng, extra_walks=rng.randint(0, 4))
            ok += 1
            central += st["central"]
            processed += st["processed"] > 0
            dropped += st["dropped"] > 0
            busy += st["busy"] > 0
        except Exception as exc:
            fail += 1
            if not isinstance(exc, Failure):
                traceback.print_exc()
            print("FAIL", exc, d, c, t, p, D, routes, journeys, flush=True)
    print(f"{ok} plans pass, {fail} fail ({none} draws without a plan); {central} plans with central flights, "
          f"{processed} needed re-pairing at a segment, {dropped} left out a segment for parity "
          f"({busy} of them after re-pairing two ends of the plane, Step 4)")


if __name__ == "__main__":
    main()
