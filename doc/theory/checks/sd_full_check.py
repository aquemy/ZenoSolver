"""Full-pipeline check of Theorem 5.3 (schedulable domination) and Lemma 6.8 of revision 2 of doc/theory/exact-front.md,
zero durations allowed. General plans with central flights under (A1-NS), multi-leg journeys, a random event
order with ties. Step 1 (split central flights and clean, with the note's sort key), Step 2 (exchanges, with
the plan re-validated after each, including the same-plane route-order condition), Step 3 (arrows, e <= a,
no cycle), Step 4 (selection, count, cost, loads), Step 5 (closed form <= M), Step 6 (shrink), and the
template simulated as a plan (valid, event-ordered, makespan = closed form).
Modes: eo (event-ordered plans); noneo (plans that are not event-ordered: Step 1 without an order, then the
pipeline if the simple plan is event-ordered); noneo_noZ (the same on instances where no central city has
d_x = dbar_x = 0: Lemma 6.8(b) says the simple plan must then be event-ordered).
usage: python3 sd_full_check.py <trials> <seed> <zero probability> [eo|noneo|noneo_noZ]"""
import random, sys
from collections import Counter, defaultdict

I, G = 'I', 'G'

class Fail(Exception):
    pass

def need(c, msg):
    if not c:
        raise Fail(msg)

def gen_instance(rng, zp):
    n = rng.randint(1, 3)
    def dd():
        return 0 if rng.random() < zp else rng.randint(1, 5)
    d = [dd() for _ in range(n)]; db = [dd() for _ in range(n)]
    c = [rng.randint(0, 4) for _ in range(n)]
    dc = {}
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < 0.6:
                lo = min(d[i] + d[j], db[i] + db[j])
                dc[(i, j)] = dc[(j, i)] = lo + (0 if rng.random() < 0.5 else rng.randint(0, 3))
    return n, d, db, c, dc

def dur(inst, a, b):
    n, d, db, c, dc = inst
    if a == I: return d[b]
    if b == I: return d[a]
    if a == G: return db[b]
    if b == G: return db[a]
    return dc[(a, b)]

def nbrs(inst, a):
    n, d, db, c, dc = inst
    if a in (I, G): return list(range(n))
    return [I, G] + [j for j in range(n) if (a, j) in dc]

# plan: legs dict id -> [plane, frm, to, dep, arr]; routes: plane -> list of ids; journeys: list of lists
def gen_plan(rng, inst, zp):
    p = rng.randint(1, 4)
    legs = {}; routes = []; lid = 0
    for k in range(p):
        cur, T, r = I, 0, []
        steps = 0
        while True:
            nb = nbrs(inst, cur)
            nxt = rng.choice(nb)
            w = 0 if rng.random() < 0.6 else rng.randint(0, 3)
            e = T + w; a = e + dur(inst, cur, nxt)
            legs[lid] = [k, cur, nxt, e, a]; r.append(lid); lid += 1
            cur, T = nxt, a; steps += 1
            if cur == G and (steps >= 10 or rng.random() < 0.35):
                break
            if steps > 14:
                # force to G
                if cur == I:
                    x = rng.randrange(inst[0]); e = T; a = e + dur(inst, I, x)
                    legs[lid] = [k, I, x, e, a]; r.append(lid); lid += 1; cur, T = x, a
                if cur != G:
                    e = T; a = e + dur(inst, cur, G)
                    legs[lid] = [k, cur, G, e, a]; r.append(lid); lid += 1; cur, T = G, a
                break
        routes.append(r)
    pos = {l: (legs[l][0], i) for k, r in enumerate(routes) for i, l in enumerate(r)}
    used = set(); journeys = []
    starts = [l for l in legs if legs[l][1] == I]
    rng.shuffle(starts)
    for s in starts:
        if s in used or rng.random() < 0.1: continue
        j = [s]; ok = False
        for _ in range(8):
            cur = j[-1]; city, T = legs[cur][2], legs[cur][4]
            if city == G and (rng.random() < 0.8): ok = True; break
            k, i = pos[cur]
            cand = [l for l in legs if l not in used and l not in j and legs[l][1] == city and legs[l][3] >= T
                    and not (legs[l][0] == k and pos[l][1] <= i)]
            if not cand:
                if city == G: ok = True
                break
            same = [l for l in cand if legs[l][0] == k and pos[l][1] == i + 1]
            l = same[0] if same and rng.random() < 0.5 else rng.choice(cand)
            j.append(l)
        else:
            ok = legs[j[-1]][2] == G
        if ok and legs[j[-1]][2] == G:
            journeys.append(j); used.update(j)
    return p, legs, routes, journeys

def deps(legs, routes, journeys):
    E = defaultdict(set)
    for r in routes:
        for a, b in zip(r, r[1:]): E[a].add(b)
    for j in journeys:
        for a, b in zip(j, j[1:]): E[a].add(b)
    return E

def random_event_order(rng, legs, routes, journeys):
    E = deps(legs, routes, journeys)
    indeg = Counter()
    for a in E:
        for b in E[a]: indeg[b] += 1
    avail = [l for l in legs if indeg[l] == 0]
    out = []; keys = {l: rng.random() for l in legs}
    while avail:
        avail.sort(key=lambda l: (legs[l][3], keys[l]))
        l = avail.pop(0); out.append(l)
        for b in E[l]:
            indeg[b] -= 1
            if indeg[b] == 0: avail.append(b)
    if len(out) < len(legs): return None
    return {l: i for i, l in enumerate(out)}

def check_plan(inst, legs, routes, journeys, order, simple_clean=False):
    """full validity: routes, journeys (incl. same-plane later position), capacity, event order"""
    pos = {}
    for k, r in enumerate(routes):
        need(len(r) >= 1, "empty route")
        need(legs[r[0]][1] == I and legs[r[0]][3] >= 0, "route start")
        need(legs[r[-1]][2] == G, "route end")
        for i, l in enumerate(r):
            pos[l] = (k, i)
            need(legs[l][4] == legs[l][3] + dur(inst, legs[l][1], legs[l][2]), "leg duration")
        for a, b in zip(r, r[1:]):
            need(legs[a][2] == legs[b][1], "route city")
            need(legs[b][3] >= legs[a][4], "route time")
    need(len(pos) == len(legs), "leg on no/multiple routes")
    seen = set()
    for j in journeys:
        need(len(j) >= 1 and legs[j[0]][1] == I and legs[j[-1]][2] == G, "journey ends")
        for a, b in zip(j, j[1:]):
            need(legs[a][2] == legs[b][1], "journey city")
            need(legs[b][3] >= legs[a][4], "journey time")
            if pos[a][0] == pos[b][0]:
                need(pos[b][1] > pos[a][1], "journey same-plane order")
        for l in j:
            need(l not in seen, "capacity"); seen.add(l)
    if order is not None:
        for r in list(routes) + list(journeys):
            for a, b in zip(r, r[1:]):
                need(order[a] < order[b], "order does not extend")
        srt = sorted(legs, key=lambda l: order[l])
        for a, b in zip(srt, srt[1:]):
            need(legs[a][3] <= legs[b][3], "order dep decreasing")
    if simple_clean:
        for r in routes:
            for l in r:
                need((legs[l][1] in (I, G)) != (legs[l][2] in (I, G)), "not simple")
        for j in journeys:
            need(len(j) == 2 and legs[j[0]][1] == I and legs[j[1]][2] == G, "journey shape")
    return pos

def cost_of(inst, legs):
    c = inst[3]
    return sum(c[legs[l][2]] for l in legs if legs[l][2] not in (I, G))

def makespan(legs, routes):
    return max(legs[r[-1]][4] for r in routes)

def step1(rng, inst, legs, routes, journeys, order):
    nl = {}; nr = []; key = {}; repl = {}
    nid = [0]
    def add(info, k):
        i = nid[0]; nid[0] += 1; nl[i] = info; key[i] = k; return i
    for k, r in enumerate(routes):
        rr = []
        for l in r:
            _, a, b, e, ar = legs[l]
            if a not in (I, G) and b not in (I, G):
                hs = [h for h in (I, G) if dur(inst, a, h) + dur(inst, h, b) <= dur(inst, a, b)]
                need(hs, "A1-NS violated")
                h = rng.choice(hs)
                m = e + dur(inst, a, h)
                x1 = add([k, a, h, e, m], (e, order[l], 0))
                x2 = add([k, h, b, m, m + dur(inst, h, b)], (m, order[l], 1))
                need(m + dur(inst, h, b) <= ar, "split later")
                repl[l] = [x1, x2]; rr += [x1, x2]
            else:
                x = add([k, a, b, e, ar], (e, order[l], 0)); repl[l] = [x]; rr.append(x)
        nr.append(rr)
    nj = []
    for j in journeys:
        jj = [x for l in j for x in repl[l]]
        # clean: last leg departing from I, first later leg arriving in G
        s = max(i for i, l in enumerate(jj) if nl[l][1] == I)
        f = min(i for i, l in enumerate(jj) if i >= s and nl[l][2] == G)
        nj.append(jj[s:f + 1])
    srt = sorted(nl, key=lambda l: key[l])
    norder = {l: i for i, l in enumerate(srt)}
    return nl, nr, nj, norder

def segments(legs, routes):
    seg = {}   # leg -> (plane, segindex)
    info = {}  # (plane, segidx) -> (type, city, first, second)
    for k, r in enumerate(routes):
        for i in range(0, len(r), 2):
            l0, l1 = r[i], r[i + 1]
            x = legs[l0][2]
            fromI = legs[l0][1] == I; toG = legs[l1][2] == G
            ty = ('A' if toG else 'B') if fromI else ('Bb' if toG else 'Ab')
            info[(k, i // 2)] = (ty, x, l0, l1)
            seg[l0] = seg[l1] = (k, i // 2)
    return seg, info

def handoffs(legs, routes, journeys):
    seg, info = segments(legs, routes)
    return [j for j in journeys if seg[j[0]] != seg[j[1]]], seg, info

def run(rng, zp, mode="eo"):
    while True:
        inst = gen_instance(rng, zp)
        if mode != "noneo_noZ" or all(inst[1][x] + inst[2][x] > 0 for x in range(inst[0])): break
    p, legs, routes, journeys = gen_plan(rng, inst, zp)
    t = len(journeys)
    if t < p: return "skip_t"
    order = random_event_order(rng, legs, routes, journeys)
    if mode == "eo":
        if order is None: return "skip_notEO"
        check_plan(inst, legs, routes, journeys, order)
    else:
        if order is not None: return "skip_EO"
        check_plan(inst, legs, routes, journeys, None)
    C0, M0 = cost_of(inst, legs), makespan(legs, routes)
    # Step 1
    if mode == "eo":
        legs, routes, journeys, order = step1(rng, inst, legs, routes, journeys, order)
    else:
        legs, routes, journeys, _ = step1(rng, inst, legs, routes, journeys, {l: 0 for l in legs})
        order = random_event_order(rng, legs, routes, journeys)
        if order is None:
            need(mode != "noneo_noZ", "still not event-ordered without a zero city (Lemma 6.8(b))")
            return "skip_still_notEO"
    check_plan(inst, legs, routes, journeys, order, simple_clean=True)
    need(cost_of(inst, legs) <= C0 and makespan(legs, routes) <= M0, "step1 cost/makespan")
    C1, M1 = cost_of(inst, legs), makespan(legs, routes)
    # Step 2
    nex = 0
    while True:
        ho, seg, info = handoffs(legs, routes, journeys)
        pos = {l: (k, i) for k, r in enumerate(routes) for i, l in enumerate(r)}
        cands = []
        for (al, be) in ho:
            u, ia = pos[al]; v, ib = pos[be]
            if u == v: continue
            bp = routes[u][ia + 1]; ap = routes[v][ib - 1]
            if order[ap] < order[bp] and legs[bp][3] >= legs[ap][4]:
                cands.append((u, ia, v, ib))
        if not cands: break
        u, ia, v, ib = rng.choice(cands)
        before = len(ho)
        fu, fv = routes[u][ia + 1:], routes[v][ib:]
        routes[u] = routes[u][:ia + 1] + fv; routes[v] = routes[v][:ib] + fu
        for l in routes[u]: legs[l][0] = u
        for l in routes[v]: legs[l][0] = v
        nex += 1
        check_plan(inst, legs, routes, journeys, order, simple_clean=True)
        need(cost_of(inst, legs) == C1 and makespan(legs, routes) == M1, "step2 cost/makespan")
        need(len(handoffs(legs, routes, journeys)[0]) < before, "step2 measure")
        need(nex < 10000, "loop")
    # Step 3
    ho, seg, info = handoffs(legs, routes, journeys)
    a_ = {s: legs[info[s][2]][4] for s in info}; e_ = {s: legs[info[s][3]][3] for s in info}
    out, inn = {}, {}
    for (al, be) in ho:
        g, g2 = seg[al], seg[be]
        need(al == info[g][2] and be == info[g2][3], "arrow legs")
        need(info[g][1] == info[g2][1], "arrow city")
        need(e_[g] <= a_[g2], "e<=a")
        need(g not in out and g2 not in inn, "degree")
        out[g] = g2; inn[g2] = g
        need(info[g2][0] not in ('B', 'Ab'), "B incoming")
        need(info[g][0] not in ('Bb', 'Ab'), "Bb outgoing")
    chains = []
    for s in info:
        if s in out and s not in inn:
            ch = [s]
            while ch[-1] in out:
                ch.append(out[ch[-1]]); need(len(ch) <= len(info), "cycle")
            chains.append(ch)
    onchain = {s for ch in chains for s in ch}
    need(all(s in onchain for s in list(out) + list(inn)), "cycle (unreached)")
    for ch in chains:
        for s in ch[1:-1]: need(info[s][0] == 'A', "inner not A")
        need(a_[ch[0]] <= e_[ch[-1]], "chain time")
    # Step 4
    links = [(ch[0], ch[-1]) for ch in chains if info[ch[0]][0] == 'B' and info[ch[-1]][0] == 'Bb']
    nA = sum(1 for s in info if info[s][0] == 'A')
    need(len(links) + nA >= t, "count")
    n, d, db, c, dc = inst
    Cr = defaultdict(list); Dr = defaultdict(list); Pk = defaultdict(list)
    for s in sorted(info):
        if info[s][0] in ('A', 'Ab'): Cr[s[0]].append(info[s][1])
    for s0, s1 in links:
        Dr[s0[0]].append(s0); Pk[s1[0]].append(s1)
    for k in range(p):
        Dr[k].sort(); Pk[k].sort()
        need(len(Cr[k]) % 2 == 1, "odd")
    cost = sum(c[x] for k in range(p) for x in Cr[k]) + sum(c[info[s][1]] for s0, s1 in links for s in (s0, s1))
    need(cost <= C1, "cost")
    linkof = {s0: s1 for s0, s1 in links}
    def closed_form(Dr, Pk, Cr, linkof):
        lam = []
        for k in range(p):
            lam.append(sum(2 * d[info[s][1]] for s in Dr[k]) + sum(2 * db[info[s][1]] for s in Pk[k])
                       + sum(d[x] + db[x] for x in Cr[k]))
        best = max(lam)
        for s0, s1 in linkof.items():
            u, v = s0[0], s1[0]; x = info[s0][1]
            j = Dr[u].index(s0); l = Pk[v].index(s1)
            pre = sum(2 * d[info[s][1]] for s in Dr[u][:j]); suf = sum(2 * db[info[s][1]] for s in Pk[v][l + 1:])
            best = max(best, pre + d[x] + db[x] + suf)
        return lam, best
    lam, mt = closed_form(Dr, Pk, Cr, linkof)
    for k in range(p):
        F = sum(legs[l][4] - legs[l][3] for l in routes[k])
        need(lam[k] <= F <= M1, "load")
    need(mt <= M1, "template step5")
    # Step 6
    tc = len(linkof) + sum((len(Cr[k]) + 1) // 2 for k in range(p))
    while tc > t:
        big = [k for k in range(p) if len(Cr[k]) >= 3]
        if big:
            k = rng.choice(big); rng.shuffle(Cr[k]); Cr[k] = Cr[k][2:]
        else:
            s0 = rng.choice(list(linkof)); s1 = linkof.pop(s0)
            Dr[s0[0]].remove(s0); Pk[s1[0]].remove(s1)
        tc -= 1
        _, mt2 = closed_form(Dr, Pk, Cr, linkof)
        need(mt2 <= mt, "shrink increased"); mt = mt2
    # simulate template as a plan
    tl = {}; tr = []; tj = []; nid = 0
    arrdrop = {}
    for k in range(p):
        T = 0; r = []
        for s in Dr[k]:
            x = info[s][1]
            tl[nid] = [k, I, x, T, T + d[x]]; arrdrop[s] = (nid, T + d[x]); r.append(nid); nid += 1; T += d[x]
            tl[nid] = [k, x, I, T, T + d[x]]; r.append(nid); nid += 1; T += d[x]
        crs = list(Cr[k]); rng.shuffle(crs)
        for i, x in enumerate(crs):
            if i % 2 == 0:
                tl[nid] = [k, I, x, T, T + d[x]]; r.append(nid); nid += 1; T += d[x]
                tl[nid] = [k, x, G, T, T + db[x]]; r.append(nid); nid += 1; T += db[x]
                tj.append([nid - 2, nid - 1])
            else:
                tl[nid] = [k, G, x, T, T + db[x]]; r.append(nid); nid += 1; T += db[x]
                tl[nid] = [k, x, I, T, T + d[x]]; r.append(nid); nid += 1; T += d[x]
        tr.append(r)
    picks = {}
    for k in range(p):
        for s in Pk[k]: picks[s] = k
    # pick-ups in order, need drop arrival
    for k in range(p):
        T = tl[tr[k][-1]][4]
        for s in Pk[k]:
            x = info[s][1]
            src = [s0 for s0, s1 in linkof.items() if s1 == s][0]
            tl[nid] = [k, G, x, T, T + db[x]]; tr[k].append(nid); nid += 1; T += db[x]
            e = max(T, arrdrop[src][1])
            tl[nid] = [k, x, G, e, e + db[x]]; tr[k].append(nid); tj.append([arrdrop[src][0], nid]); nid += 1
            T = e + db[x]
    need(len(tj) == t, "template passengers")
    to = random_event_order(rng, tl, tr, tj)
    need(to is not None, "template not event-ordered")
    check_plan(inst, tl, tr, tj, to, simple_clean=True)
    need(makespan(tl, tr) == mt, "template makespan != closed form")
    need(mt <= M0, "final")
    return "ok" + ("_ex" if nex else "") + ("_link" if linkof else "")

if __name__ == "__main__":
    trials, seed, zp = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    mode = sys.argv[4] if len(sys.argv) > 4 else "eo"
    rng = random.Random(seed)
    res = Counter()
    for it in range(trials):
        try:
            res[run(rng, zp, mode)] += 1
        except Fail as ex:
            res["FAIL:" + str(ex)] += 1
    print(dict(res))
