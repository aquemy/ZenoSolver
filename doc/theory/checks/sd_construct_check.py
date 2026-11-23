"""Check the construction in the proof of Theorem 6.9 (schedulable domination) on random simple plans
with clean journeys (doc/theory/exact-front.md, §6.2). For each plan:
  1. exchange futures while some hand-off overlaps (both planes in the city at a common moment, in event
     order); check that routes stay valid, cost, leg times and makespan are unchanged, and that the number
     of journeys spread over two segments drops;
  2. check that afterwards no hand-off overlaps, the hand-off graph of each city has no cycle, and along
     every chain the drop-off arrival is no later than the final pick-up departure;
  3. build the configuration (all A and Abar as crossings, a link per chain from a B to a Bbar), check its
     passenger count >= t, cost <= C, role loads <= flight times, and that its template, with the plan's
     orders and the chain links, has makespan <= M.
Durations are positive, so ordering legs by departure time is an event order.
usage: python3 sd_construct_check.py <trials> <seed>"""
import random, sys
from collections import Counter

A, AB, B, BB = 0, 1, 2, 3     # A, Abar, B, Bbar

def gen(rng):
    n = rng.randint(1, 3); p = rng.randint(1, 4)
    d = [rng.randint(1, 9) for _ in range(n)]; db = [rng.randint(1, 9) for _ in range(n)]
    c = [rng.randint(0, 5) for _ in range(n)]
    routes = []
    for _ in range(p):
        segs, west = [], True
        while True:
            if west:
                ty = A if rng.random() < 0.5 else B
            else:
                if any(s[0] == A for s in segs) and rng.random() < 0.3: break
                ty = AB if rng.random() < 0.5 else BB
            segs.append((ty, rng.randrange(n)))
            if ty == A: west = False
            elif ty == AB: west = True
            if len(segs) > 7 and not west: break
        routes.append(segs)
    # legs: (plane, seg, half); first half of A/B departs C_I, second half of A/Bbar arrives C_G
    outs = [(k, j) for k, r in enumerate(routes) for j, s in enumerate(r) if s[0] in (A, B)]
    ins = [(k, j) for k, r in enumerate(routes) for j, s in enumerate(r) if s[0] in (A, BB)]
    rng.shuffle(outs); used = set(); journeys = []
    for o in outs:
        if rng.random() < 0.15: continue
        cand = [q for q in ins if q not in used and routes[q[0]][q[1]][1] == routes[o[0]][o[1]][1]
                and not (q[0] == o[0] and q[1] < o[1])]
        if not cand: continue
        q = rng.choice(cand); used.add(q); journeys.append((o, q))
    return n, p, d, db, c, routes, journeys

def dur(seg, half, d, db):
    ty, x = seg
    if half == 0: return d[x] if ty in (A, B) else db[x]
    return db[x] if ty in (A, BB) else d[x]

def schedule(rng, routes, journeys, d, db):
    """earliest start with random extra waits; returns dep[(k,j,h)], arr[...] or None on deadlock"""
    src = {}   # second leg (k,j,1) -> first leg (k',j',0) of its handed passenger
    for o, q in journeys:
        if o != q: src[(q[0], q[1], 1)] = (o[0], o[1], 0)
    waits = {(k, j, h): (rng.choice([0, 0, 0, 1, 2, 5]) if rng.random() < 0.3 else 0)
             for k, r in enumerate(routes) for j in range(len(r)) for h in (0, 1)}
    dep, arr = {}, {}
    nxt = [0] * len(routes); time = [0] * len(routes)
    legs = [[(j, h) for j in range(len(r)) for h in (0, 1)] for r in routes]
    progress = True
    while progress:
        progress = False
        for k in range(len(routes)):
            while nxt[k] < len(legs[k]):
                j, h = legs[k][nxt[k]]
                e = time[k] + waits[(k, j, h)]
                s = src.get((k, j, h))
                if s is not None:
                    if s not in arr: break
                    e = max(e, arr[s])
                dep[(k, j, h)] = e; arr[(k, j, h)] = e + dur(routes[k][j], h, d, db)
                time[k] = arr[(k, j, h)]; nxt[k] += 1; progress = True
    if any(nxt[k] < len(legs[k]) for k in range(len(routes))): return None
    return dep, arr

def check(rng):
    n, p, d, db, c, routes, journeys = gen(rng)
    t = len(journeys)
    if t < p: return "skip"
    sch = schedule(rng, routes, journeys, d, db)
    if sch is None: return "skip"
    dep, arr = sch
    # flatten into plane-indexed leg lists with explicit leg objects
    leg_info = {}   # leg id -> (seg type, city, half, dep, arr)
    planes = []
    for k, r in enumerate(routes):
        lst = []
        for j, sg in enumerate(r):
            for h in (0, 1):
                lid = (k, j, h); leg_info[lid] = (sg[0], sg[1], h, dep[lid], arr[lid]); lst.append(lid)
        planes.append(lst)
    jour = [((o[0], o[1], 0), (q[0], q[1], 1)) for o, q in journeys]
    cost0 = sum(c[x] for r in routes for _, x in r)
    M0 = max(arr[pl[-1]] for pl in planes)
    order = {lid: i for i, lid in enumerate(sorted(leg_info, key=lambda l: (leg_info[l][3], l)))}
    def plane_of(): return {lid: (k, i) for k, pl in enumerate(planes) for i, lid in enumerate(pl)}
    def spread():   # journeys whose two legs are not consecutive legs of one plane forming one segment
        po = plane_of(); cnt = 0
        for a, b in jour:
            (ka, ia), (kb, ib) = po[a], po[b]
            if not (ka == kb and ib == ia + 1 and ia % 2 == 0): cnt += 1
        return cnt
    # 1. exchanges
    nex = 0
    for _ in range(1000):
        po = plane_of(); found = None
        for a, b in jour:
            (u, ia), (v, ib) = po[a], po[b]
            if u == v: continue
            bp = planes[u][ia + 1]; ap = planes[v][ib - 1]   # u's leg after a, v's leg before b
            if order[ap] < order[bp] and leg_info[bp][3] >= leg_info[ap][4]:
                found = (u, ia, v, ib); break
        if not found: break
        u, ia, v, ib = found
        before = spread()
        fu, fv = planes[u][ia + 1:], planes[v][ib:]
        planes[u] = planes[u][:ia + 1] + fv; planes[v] = planes[v][:ib] + fu
        nex += 1
        if spread() >= before: return "FAIL_measure"
    else:
        return "FAIL_loop"
    # routes valid (times, locations by segment halves), makespan unchanged
    for pl in planes:
        for i in range(1, len(pl)):
            if leg_info[pl[i]][3] < leg_info[pl[i - 1]][4]: return "FAIL_route_time"
        for i in range(len(pl) - 1):
            if order[pl[i]] > order[pl[i + 1]]: return "FAIL_route_order"
    if max(leg_info[pl[-1]][4] for pl in planes) != M0: return "FAIL_makespan"
    # segments of the new routes: consecutive leg pairs (each route alternates hub, central)
    segs = []   # (plane, index, type, city, first leg, second leg)
    for k, pl in enumerate(planes):
        for i in range(0, len(pl), 2):
            l0, l1 = pl[i], pl[i + 1]
            if leg_info[l0][1] != leg_info[l1][1]: return "FAIL_city"
            from_I = leg_info[l0][0] in (A, B) if leg_info[l0][2] == 0 else None
            to_G = leg_info[l1][0] in (A, BB)
            # type of the new segment from its two halves
            first_from_I = (leg_info[l0][0] in (A, B))
            ty = (A if to_G else B) if first_from_I else (BB if to_G else AB)
            segs.append((k, i // 2, ty, leg_info[l0][1], l0, l1))
    seg_of_leg = {}
    for sidx, s in enumerate(segs): seg_of_leg[s[4]] = sidx; seg_of_leg[s[5]] = sidx
    # 2. hand-off graph at each city: edge seg(first leg) -> seg(second leg)
    out_edge, in_edge = {}, {}
    through = 0
    for a, b in jour:
        sa, sb = seg_of_leg[a], seg_of_leg[b]
        if sa == sb: through += 1; continue
        out_edge[sa] = sb; in_edge[sb] = sa
        # non-overlap: dropper's second leg vs picker's first leg
        bp, ap = segs[sa][5], segs[sb][4]
        if not (order[bp] < order[ap] or leg_info[bp][3] < leg_info[ap][4]): return "FAIL_overlap_left"
    # chains
    links = []
    seen = set(); longest = 0
    for sidx in range(len(segs)):
        if sidx in in_edge or sidx not in out_edge: continue
        chain = [sidx]
        while chain[-1] in out_edge:
            nx = out_edge[chain[-1]]
            if nx in chain: return "FAIL_cycle"
            chain.append(nx)
        seen.update(chain); longest = max(longest, len(chain))
        s0, f = segs[chain[0]], segs[chain[-1]]
        for mid in chain[1:-1]:
            if segs[mid][2] != A: return "FAIL_internal_not_A"
        if leg_info[s0[4]][4] > leg_info[f[5]][3]: return "FAIL_chain_time"
        if s0[2] == B and f[2] == BB: links.append((chain[0], chain[-1]))
    if any(s in out_edge or s in in_edge for s in range(len(segs)) if s not in seen): return "FAIL_cycle"
    # 3. configuration
    nA = sum(1 for s in segs if s[2] == A)
    tcfg = len(links) + nA
    if tcfg < t: return "FAIL_count"
    linked = {s for l in links for s in l}
    sel = [s for i, s in enumerate(segs) if s[2] in (A, AB) or i in linked]
    cost = sum(c[s[3]] for s in sel)
    if cost > cost0: return "FAIL_cost"
    for k, pl in enumerate(planes):
        lam = sum((d[s[3]] + db[s[3]]) if s[2] in (A, AB) else (2 * d[s[3]] if s[2] == B else 2 * db[s[3]])
                  for s in sel if s[0] == k)
        if lam > leg_info[pl[-1]][4]: return "FAIL_load"
    # template with plan orders and chain links
    lam_max = 0; terms = 0
    for k in range(len(planes)):
        drops = [i for i, s in enumerate(segs) if s[0] == k and i in linked and s[2] == B]
        picks = [i for i, s in enumerate(segs) if s[0] == k and i in linked and s[2] == BB]
        cr = [s for s in sel if s[0] == k and s[2] in (A, AB)]
        lam = sum(2 * d[segs[i][3]] for i in drops) + sum(2 * db[segs[i][3]] for i in picks) + sum(d[s[3]] + db[s[3]] for s in cr)
        lam_max = max(lam_max, lam)
    pos = {}
    for k in range(len(planes)):
        ds = sorted([i for i, s in enumerate(segs) if s[0] == k and i in linked and s[2] == B], key=lambda i: segs[i][1])
        ps = sorted([i for i, s in enumerate(segs) if s[0] == k and i in linked and s[2] == BB], key=lambda i: segs[i][1])
        for r, i in enumerate(ds): pos[i] = sum(2 * d[segs[j][3]] for j in ds[:r])
        for r, i in enumerate(ps): pos[i] = sum(2 * db[segs[j][3]] for j in ps[r + 1:])
    mt = lam_max
    for s0, f in links:
        x = segs[s0][3]
        mt = max(mt, pos[s0] + d[x] + db[x] + pos[f])
    if mt > M0: return "FAIL_template"
    return "ok" + ("_exchanged" if nex else "") + ("_swapchain" if longest >= 3 else "") + ("_linked" if links else "")

rng = random.Random(int(sys.argv[2]))
res = Counter(check(rng) for _ in range(int(sys.argv[1])))
print(dict(res))
