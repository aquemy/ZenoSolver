"""Schedulable domination (Theorem 6.9) without the event order, on instances with cities of
d_x = dbar_x = 0 (the open case at the end of §6.2 of doc/theory/exact-front.md).

Random simple plans with clean journeys (after Step 1 every plan is one, whatever its event order)
on instances with zero-duration cities, and passengers matched to a leg C_I -> x and a later leg
x -> C_G. The generator is biased towards the cities of d = dbar = 0 (so that many legs share an
instant) and towards zero-time hand-offs between planes; in half of the plans with two planes
and a city of d = dbar = 0, every plane starts with zero-time crossings at that city and two
passengers are handed across in opposite directions, a cycle of dependencies. The run reports
how many plans are not event-ordered. Journeys
follow the note's semantics (two legs of one plane in route order) or, with `loose`, only time
(the Lean model's `Feasible`).

Step 2 without an order, three moves, each raising the number of visits that carry their
passenger through (so it ends):
  exchange: a hand-off between two planes overlaps in time (the receiving plane is in x before
            the delivering one leaves): the planes exchange their futures;
  cut:      a hand-off goes backwards on one plane: everything between the two legs is a closed
            zero-time walk at a zero-duration city; it is cut out as a free loop, the plane keeps
            its route, and the passenger rides through the loop's visit (alpha, beta);
  splice:   a hand-off between a free loop's visit F and a route's visit delta fails
            e(src) <= a(dst): the loop is spliced into the route at delta, so the passenger rides
            through.
Then every hand-off has e(src) <= a(dst), and Steps 3-5 run with the free visits (weight 0) as
drop-offs ordered first and pick-ups ordered last. Every step is re-validated: routes, loops,
cost and makespan unchanged, arrows, the count, the closed form <= M, Step 6, and the template
simulated as an event-ordered plan.

usage: python3 sd_zero_check.py <trials> <seed> [strict|loose] [maxPlanes maxSegments]"""
import random, sys
from collections import Counter, defaultdict

I, G = 'I', 'G'
MAXP, MAXSEG = 3, 5


class Fail(Exception):
    pass


def need(c, msg):
    if not c:
        raise Fail(msg)


def gen_instance(rng):
    n = rng.randint(1, 3)
    d, db = [], []
    for _ in range(n):
        r = rng.random()
        if r < 0.45: d.append(0); db.append(0)
        elif r < 0.6: d.append(0); db.append(rng.randint(1, 3))
        elif r < 0.75: d.append(rng.randint(1, 3)); db.append(0)
        else: d.append(rng.randint(1, 3)); db.append(rng.randint(1, 3))
    if all(d[i] + db[i] > 0 for i in range(n)):
        i = rng.randrange(n); d[i] = db[i] = 0
    c = [rng.randint(0, 4) for _ in range(n)]
    return n, d, db, c


def dur(inst, a, b):
    n, d, db, c = inst
    if a == I: return d[b]
    if b == I: return d[a]
    if a == G: return db[b]
    return db[a]


def gen_plan(rng, inst, loose):
    """simple plan: legs id -> [frm, to, dep, arr]; routes alternate hub -> city -> hub"""
    n, d, db, c = inst
    zero = [i for i in range(n) if d[i] == 0 and db[i] == 0]
    p = rng.randint(1, MAXP)
    legs, routes, lid = {}, [], 0
    # with probability 1/2, every plane starts with zero-time crossings at one city of
    # d = dbar = 0 (C_I -> z -> C_G -> z2 -> C_I, at time 0), where cycles are injected below
    burst = bool(zero) and p >= 2 and rng.random() < 0.5
    z0 = rng.choice(zero) if zero else None
    heads = []   # per plane: (entry, exit) legs of its zero-time crossings C_I -> z0 -> C_G
    for k in range(p):
        cur, T, r = I, 0, []
        hk = []
        if burst:
            for _ in range(rng.randint(2, 3)):
                legs[lid] = [I, z0, 0, 0]; legs[lid + 1] = [z0, G, 0, 0]
                hk.append((lid, lid + 1)); r += [lid, lid + 1]; lid += 2
                z2 = rng.choice(zero)
                legs[lid] = [G, z2, 0, 0]; legs[lid + 1] = [z2, I, 0, 0]
                r += [lid, lid + 1]; lid += 2
        heads.append(hk)
        nseg = rng.randint(1, MAXSEG)
        for sgi in range(nseg):
            # biased towards the cities of d = dbar = 0, so that many legs share an instant
            x = rng.choice(zero) if zero and rng.random() < 0.6 else rng.randrange(n)
            w = 0 if rng.random() < 0.8 else rng.randint(1, 2)
            e = T + w; a = e + dur(inst, cur, x)
            legs[lid] = [cur, x, e, a]; r.append(lid); lid += 1
            last = sgi == nseg - 1
            h = G if last else rng.choice([I, G])
            w = 0 if rng.random() < 0.8 else rng.randint(1, 2)
            e = a + w; a2 = e + dur(inst, x, h)
            legs[lid] = [x, h, e, a2]; r.append(lid); lid += 1
            cur, T = h, a2
        routes.append(r)
    pos = {l: (k, i) for k, r in enumerate(routes) for i, l in enumerate(r)}
    used_b, used_a, journeys = set(), set(), []
    if burst:
        # a cycle: A rides v's later crossing in and u's earlier one out, B the converse
        u, v = rng.sample(range(p), 2)
        for (src, dst) in ((v, u), (u, v)):
            al, be = heads[src][1][0], heads[dst][0][1]
            journeys.append([al, be]); used_a.add(al); used_b.add(be)
    alphas = [l for l in legs if legs[l][0] == I and l not in used_a]
    rng.shuffle(alphas)
    for al in alphas:
        if rng.random() < 0.15: continue
        x, T = legs[al][1], legs[al][3]
        cand = [b for b in legs if b not in used_b and legs[b][0] == x and legs[b][1] == G
                and legs[b][2] >= T]
        if not loose:
            cand = [b for b in cand if not (pos[b][0] == pos[al][0] and pos[b][1] < pos[al][1])]
        if not cand: continue
        # biased towards zero-time hand-offs between planes, which make cycles
        zt = [b for b in cand if legs[b][2] == T and pos[b][0] != pos[al][0]]
        b = rng.choice(zt) if zt and rng.random() < 0.75 else rng.choice(cand)
        used_b.add(b); journeys.append([al, b])
    return p, legs, routes, journeys


def event_ordered(legs, routes, journeys):
    E = defaultdict(set)
    for r in routes:
        for a, b in zip(r, r[1:]): E[a].add(b)
    for a, b in journeys: E[a].add(b)
    indeg = Counter()
    for a in E:
        for b in E[a]: indeg[b] += 1
    avail = [l for l in legs if indeg[l] == 0]; seen = 0
    while avail:
        l = avail.pop(); seen += 1
        for b in E[l]:
            indeg[b] -= 1
            if indeg[b] == 0: avail.append(b)
    return seen == len(legs)


def check_state(inst, legs, routes, loops, journeys, C, M):
    """routes valid, loops closed zero-time walks, every leg used once, cost and makespan kept"""
    used = Counter()
    for r in routes:
        need(len(r) >= 2 and len(r) % 2 == 0, "route length")
        need(legs[r[0]][0] == I and legs[r[0]][2] >= 0 and legs[r[-1]][1] == G, "route ends")
        for i, l in enumerate(r):
            used[l] += 1
            need((legs[l][0] in (I, G)) == (i % 2 == 0), "route alternates")
        for a, b in zip(r, r[1:]):
            need(legs[a][1] == legs[b][0] and legs[b][2] >= legs[a][3], "route validity")
    for (tau, L) in loops:
        need(len(L) >= 2 and len(L) % 2 == 0, "loop length")
        for i, l in enumerate(L):
            used[l] += 1
            need(legs[l][2] == tau and legs[l][3] == tau, "loop not zero-time")
            need((legs[l][0] in (I, G)) == (i % 2 == 0), "loop alternates")
        for a, b in zip(L, L[1:] + L[:1]):
            need(legs[a][1] == legs[b][0], "loop not closed")
    need(all(used[l] == 1 for l in legs) and len(used) == len(legs), "legs not partitioned")
    c = inst[3]
    need(sum(c[legs[l][1]] for l in legs if legs[l][1] not in (I, G)) == C, "cost changed")
    need(max(legs[r[-1]][3] for r in routes) <= M, "makespan grew")
    for a, b in journeys:
        need(legs[a][3] <= legs[b][2] and legs[a][1] == legs[b][0], "journey")


def nodes(legs, routes, loops):
    """visit of each leg: ('r', plane, idx) or ('f', loop, idx); and (a, e, entry, exit, city)"""
    where, info = {}, {}
    for k, r in enumerate(routes):
        for i in range(0, len(r), 2):
            nd = ('r', k, i // 2); where[r[i]] = where[r[i + 1]] = nd
            info[nd] = (legs[r[i]][3], legs[r[i + 1]][2], r[i], r[i + 1], legs[r[i]][1])
    for q, (tau, L) in enumerate(loops):
        for i in range(0, len(L), 2):
            nd = ('f', q, i // 2); where[L[i]] = where[L[i + 1]] = nd
            info[nd] = (tau, tau, L[i], L[i + 1], legs[L[i]][1])
    return where, info


def step2(rng, legs, routes, journeys):
    routes = [list(r) for r in routes]; loops = []
    origin = {}  # loop index -> plane it is attached to (for the crossing parity)
    moves = Counter()
    while True:
        where, info = nodes(legs, routes, loops)
        thr = sum(1 for a, b in journeys if where[a] == where[b])
        acts = []
        for a, b in journeys:
            s, t_ = where[a], where[b]
            if s == t_: continue
            es, at = info[s][1], info[t_][0]
            if s[0] == 'r' and t_[0] == 'r':
                if s[1] != t_[1]:
                    if at <= es: acts.append(('exchange', s, t_))
                elif t_[2] < s[2]:
                    acts.append(('cut', s, t_))
            elif s[0] != t_[0]:
                if es > at: acts.append(('splice', s, t_))
        if not acts: break
        kind, s, t_ = rng.choice(acts)
        moves[kind] += 1
        if kind == 'exchange':
            u, i = s[1], s[2]; v, j = t_[1], t_[2]
            fu = routes[u][2 * i + 1:]; fv = routes[v][2 * j + 1:]
            routes[u] = routes[u][:2 * i + 1] + fv; routes[v] = routes[v][:2 * j + 1] + fu
        elif kind == 'cut':
            u, i, j = s[1], s[2], t_[2]   # alpha at visit i, beta at visit j < i
            r = routes[u]
            al, be = r[2 * i], r[2 * j + 1]
            loop = [al, be] + r[2 * j + 2: 2 * i]
            tau = legs[be][2]
            routes[u] = r[:2 * j + 1] + r[2 * i + 1:]
            loops.append((tau, loop)); origin[len(loops) - 1] = u
        else:
            f, rt = (s, t_) if s[0] == 'f' else (t_, s)
            q, fi = f[1], f[2]; k, m = rt[1], rt[2]
            tau, L = loops[q]
            rot = L[2 * fi:] + L[:2 * fi]          # F first
            r = routes[k]
            routes[k] = r[:2 * m] + [r[2 * m], rot[1]] + rot[2:] + [rot[0], r[2 * m + 1]] + r[2 * m + 2:]
            loops.pop(q)
            origin = {(qq if qq < q else qq - 1): w for qq, w in origin.items() if qq != q}
        where2, info2 = nodes(legs, routes, loops)
        need(sum(1 for a, b in journeys if where2[a] == where2[b]) > thr, "measure did not grow")
        need(sum(moves.values()) < 5000, "loop")
    return routes, loops, origin, moves


def run(rng, loose):
    inst = gen_instance(rng)
    p, legs, routes, journeys = gen_plan(rng, inst, loose)
    t = len(journeys)
    if t < p: return "skip_t"
    eo = event_ordered(legs, routes, journeys)
    n, d, db, c = inst
    C0 = sum(c[legs[l][1]] for l in legs if legs[l][1] not in (I, G))
    M0 = max(legs[r[-1]][3] for r in routes)
    check_state(inst, legs, routes, [], journeys, C0, M0)
    routes, loops, origin, moves = step2(rng, legs, routes, journeys)
    check_state(inst, legs, routes, loops, journeys, C0, M0)
    where, info = nodes(legs, routes, loops)
    plane_of = {nd: (nd[1] if nd[0] == 'r' else origin[nd[1]]) for nd in info}
    def typ(nd):
        a, e, en, ex, x = info[nd]
        fromI = legs[en][0] == I; toG = legs[ex][1] == G
        return ('A' if toG else 'B') if fromI else ('Bb' if toG else 'Ab')
    # Step 3: arrows with e(src) <= a(dst)
    out, inn = {}, {}
    for a, b in journeys:
        s, t_ = where[a], where[b]
        if s == t_: continue
        need(info[s][4] == info[t_][4], "arrow city")
        need(info[s][1] <= info[t_][0], "e<=a")
        need(s not in out and t_ not in inn, "degree")
        out[s] = t_; inn[t_] = s
    chains = []
    for s in info:
        if s in out and s not in inn:
            ch = [s]
            while ch[-1] in out:
                ch.append(out[ch[-1]]); need(len(ch) <= len(info), "cycle")
            chains.append(ch)
    for ch in chains:
        for s in ch[1:-1]: need(typ(s) == 'A', "inner not A")
        need(info[ch[0]][0] <= info[ch[-1]][1], "chain time")
    # Step 4: selection
    links = [(ch[0], ch[-1]) for ch in chains if typ(ch[0]) == 'B' and typ(ch[-1]) == 'Bb']
    nA = sum(1 for s in info if typ(s) == 'A')
    need(len(links) + nA >= t, "count")
    Cr = defaultdict(list); Dr = defaultdict(list); Pk = defaultdict(list)
    for s in info:
        if typ(s) in ('A', 'Ab'): Cr[plane_of[s]].append(info[s][4])
    # drop-offs: free ones first, then the route's in order; pick-ups: route's in order, free last
    def key_dr(s): return (0, 0) if s[0] == 'f' else (1, s[2])
    def key_pk(s): return (1, 0) if s[0] == 'f' else (0, s[2])
    for s0, s1 in links:
        Dr[plane_of[s0]].append(s0); Pk[plane_of[s1]].append(s1)
    for k in range(p):
        Dr[k].sort(key=key_dr); Pk[k].sort(key=key_pk)
        need(len(Cr[k]) % 2 == 1, "odd")
    for s in info:
        if s[0] == 'f':
            need(d[info[s][4]] * (legs[info[s][2]][0] == I) + db[info[s][4]] * (legs[info[s][2]][0] == G) == 0
                 and info[s][0] == info[s][1], "free visit not zero")
    cost = sum(c[x] for k in range(p) for x in Cr[k]) + sum(c[info[s][4]] for s0, s1 in links for s in (s0, s1))
    need(cost <= C0, "cost")
    linkof = {s0: s1 for s0, s1 in links}
    def closed_form():
        lam = []
        for k in range(p):
            lam.append(sum(2 * d[info[s][4]] for s in Dr[k]) + sum(2 * db[info[s][4]] for s in Pk[k])
                       + sum(d[x] + db[x] for x in Cr[k]))
        best = max(lam)
        for s0, s1 in linkof.items():
            u, v = plane_of[s0], plane_of[s1]; x = info[s0][4]
            j = Dr[u].index(s0); l = Pk[v].index(s1)
            pre = sum(2 * d[info[s][4]] for s in Dr[u][:j]); suf = sum(2 * db[info[s][4]] for s in Pk[v][l + 1:])
            best = max(best, pre + d[x] + db[x] + suf)
        return lam, best
    lam, mt = closed_form()
    for k in range(p):
        F = sum(legs[l][3] - legs[l][2] for l in routes[k])
        need(lam[k] <= F <= M0, "load")
    need(mt <= M0, "template step5")
    # Step 6
    tc = len(linkof) + sum((len(Cr[k]) + 1) // 2 for k in range(p))
    while tc > t:
        big = [k for k in range(p) if len(Cr[k]) >= 3]
        if big:
            k = rng.choice(big); rng.shuffle(Cr[k]); Cr[k] = Cr[k][2:]
        else:
            s0 = rng.choice(list(linkof)); s1 = linkof.pop(s0)
            Dr[plane_of[s0]].remove(s0); Pk[plane_of[s1]].remove(s1)
        tc -= 1
        _, mt2 = closed_form()
        need(mt2 <= mt, "shrink increased"); mt = mt2
    # the template, simulated
    tl, tr, tj, nid, arrdrop = {}, [], [], 0, {}
    for k in range(p):
        T, r = 0, []
        for s in Dr[k]:
            x = info[s][4]
            tl[nid] = [I, x, T, T + d[x]]; arrdrop[s] = (nid, T + d[x]); r.append(nid); nid += 1; T += d[x]
            tl[nid] = [x, I, T, T + d[x]]; r.append(nid); nid += 1; T += d[x]
        crs = list(Cr[k]); rng.shuffle(crs)
        for i, x in enumerate(crs):
            if i % 2 == 0:
                tl[nid] = [I, x, T, T + d[x]]; r.append(nid); nid += 1; T += d[x]
                tl[nid] = [x, G, T, T + db[x]]; r.append(nid); nid += 1; T += db[x]
                tj.append([nid - 2, nid - 1])
            else:
                tl[nid] = [G, x, T, T + db[x]]; r.append(nid); nid += 1; T += db[x]
                tl[nid] = [x, I, T, T + d[x]]; r.append(nid); nid += 1; T += d[x]
        tr.append(r)
    for k in range(p):
        T = tl[tr[k][-1]][3]
        for s in Pk[k]:
            x = info[s][4]
            src = [s0 for s0, s1 in linkof.items() if s1 == s][0]
            tl[nid] = [G, x, T, T + db[x]]; tr[k].append(nid); nid += 1; T += db[x]
            e = max(T, arrdrop[src][1])
            tl[nid] = [x, G, e, e + db[x]]; tr[k].append(nid); tj.append([arrdrop[src][0], nid]); nid += 1
            T = e + db[x]
    need(len(tj) == t, "template passengers")
    need(event_ordered(tl, tr, tj), "template not event-ordered")
    for r in tr:
        for a, b in zip(r, r[1:]):
            need(tl[a][1] == tl[b][0] and tl[b][2] >= tl[a][3], "template route")
    tm = max(tl[r[-1]][3] for r in tr)
    need(tm == mt, "template makespan != closed form")
    need(tm <= M0, "final")
    tags = ("eo" if eo else "NONEO") + "".join(sorted("_" + k for k in moves)) + ("_link" if linkof else "")
    return tags


if __name__ == "__main__":
    trials, seed = int(sys.argv[1]), int(sys.argv[2])
    loose = len(sys.argv) > 3 and sys.argv[3] == "loose"
    if len(sys.argv) > 5:
        MAXP, MAXSEG = int(sys.argv[4]), int(sys.argv[5])
    rng = random.Random(seed)
    res = Counter()
    for _ in range(trials):
        try:
            res[run(rng, loose)] += 1
        except Fail as ex:
            res["FAIL:" + str(ex)] += 1
    for k, v in sorted(res.items(), key=lambda kv: -kv[1]):
        print(f"{v:7d}  {k}")
