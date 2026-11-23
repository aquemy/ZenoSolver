"""Randomised check of DS -> SH -> PAR (doc/theory/exact-front.md, section 4.2).

A simple configuration: per plane, a sequence of simple segments (A, Abar, B, Bbar) starting on the
C_I side and ending on the C_G side, each with a central city. Passengers: an out-slot (first flight
of an A or B) and an in-slot (second flight of an A or Bbar) at the same city, each slot used once.
DS is timing-free, so random configurations cover it. Checks:
  count  : sum_k (|Dr_k| + a'_k) >= t
  balance: per city, #drops = #picks
  after SH and PAR: |X| = 2t - p, admissible (component form), X_k <= landings of plane k,
           |Cr_k| odd, load(X_k) <= flight time of plane k (2 d per simple segment).
Also the non-symmetric role loads (crossing d+db, drop 2d, pick 2db) <= flight time."""
import random, sys
from collections import Counter, defaultdict

def admissible(groups, n):
    p = len(groups); par = list(range(p + n))
    def f(v):
        while par[v] != v: par[v] = par[par[v]]; v = par[v]
        return v
    for k, g in enumerate(groups):
        for c in set(g): par[f(k)] = f(p + c)
    ev = Counter(f(k) for k, g in enumerate(groups) if len(g) % 2 == 0)
    return all(v % 2 == 0 for v in ev.values())

def trial(rng):
    p = rng.randint(1, 5); n = rng.randint(1, 4)
    d = [rng.randint(0, 9) for _ in range(n)]; db = [rng.randint(0, 9) for _ in range(n)]
    segs = []                                     # (plane, type, city)
    for k in range(p):
        side, hasA, L = 'I', False, 0
        while True:
            L += 1
            if side == 'I':
                if rng.random() < 0.55: segs.append((k, 'A', rng.randrange(n))); side = 'G'; hasA = True
                else: segs.append((k, 'B', rng.randrange(n)))
            else:
                if hasA and (rng.random() < 0.35 or L > 9): break
                if rng.random() < 0.5: segs.append((k, 'Ab', rng.randrange(n))); side = 'I'
                else: segs.append((k, 'Bb', rng.randrange(n)))
    out_free = defaultdict(list); in_free = defaultdict(list)
    for idx, (k, ty, x) in enumerate(segs):
        if ty in ('A', 'B'): out_free[x].append(idx)
        if ty in ('A', 'Bb'): in_free[x].append(idx)
    o = {}; nn = {}
    target = rng.randint(1, 12); pax = 0
    for _ in range(60):
        if pax >= target: break
        xs = [x for x in range(n) if out_free[x] and in_free[x]]
        if not xs: break
        x = rng.choice(xs)
        a = out_free[x].pop(rng.randrange(len(out_free[x])))
        # prefer a through A sometimes
        if segs[a][1] == 'A' and a in in_free[x] and rng.random() < 0.4: b = a; in_free[x].remove(a)
        else:
            cand = [b for b in in_free[x]]
            b = cand[rng.randrange(len(cand))]; in_free[x].remove(b)
        o[pax] = a; nn[pax] = b; pax += 1
    t = pax
    if t < p: return None
    o_of = {v: k for k, v in o.items()}; n_of = {v: k for k, v in nn.items()}
    # DS
    beta = defaultdict(list); betab = defaultdict(list)
    A_nonempty = defaultdict(list); A_empty = defaultdict(list); Abar = defaultdict(list)
    for idx, (k, ty, x) in enumerate(segs):
        if ty == 'B' and idx in o_of: beta[x].append(idx)
        if ty == 'Bb' and idx in n_of: betab[x].append(idx)
        if ty == 'A': (A_nonempty if (idx in o_of or idx in n_of) else A_empty)[k].append(idx)
        if ty == 'Ab': Abar[k].append(idx)
    Dr = defaultdict(list); Pk = defaultdict(list); Cr = defaultdict(list)
    for x in range(n):
        mm = min(len(beta[x]), len(betab[x]))
        for idx in beta[x][:mm]: Dr[segs[idx][0]].append(x)
        for idx in betab[x][:mm]: Pk[segs[idx][0]].append(x)
    used = Counter()
    for k in range(p):
        a = len(A_nonempty[k]); ap = max(a, 1)
        chosen = list(A_nonempty[k]) + Abar[k][:ap - 1] + (A_empty[k][:1] if a == 0 else [])
        if len(chosen) != 2 * ap - 1: return 'unavailable'
        Cr[k] = [segs[i][2] for i in chosen]
    total = sum(len(Dr[k]) + (len(Cr[k]) + 1) // 2 for k in range(p))
    if total < t: return 'count'
    for x in range(n):
        if sum(Dr[k].count(x) for k in range(p)) != sum(Pk[k].count(x) for k in range(p)): return 'balance'
    # role loads (NS form) <= flight time
    for k in range(p):
        ft = sum((d[x] + db[x]) if ty in ('A', 'Ab') else (2 * d[x] if ty == 'B' else 2 * db[x]) for (kk, ty, x) in segs if kk == k)
        lam = sum(2 * d[x] for x in Dr[k]) + sum(2 * db[x] for x in Pk[k]) + sum(d[x] + db[x] for x in Cr[k])
        if lam > ft: return 'nsload'
    # SH
    while total > t:
        k2 = next((k for k in range(p) if len(Cr[k]) >= 3), None)
        if k2 is not None: Cr[k2] = Cr[k2][:-2]
        else:
            k = next(k for k in range(p) if Dr[k]); x = Dr[k].pop()
            v = next(v for v in range(p) if x in Pk[v]); Pk[v].remove(x)
        total -= 1
    X = [Dr[k] + Pk[k] + Cr[k] for k in range(p)]
    if sum(map(len, X)) != 2 * t - p: return 'size'
    if not admissible(X, n): return 'admissible'
    for k in range(p):
        if len(Cr[k]) % 2 == 0: return 'odd'
        land = Counter(x for (kk, ty, x) in segs if kk == k)
        if Counter(X[k]) - land: return 'subset'
        if 2 * sum(d[x] for x in X[k]) > sum(2 * d[x] for (kk, ty, x) in segs if kk == k): return 'load'
    return 'ok'

rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
res = Counter(trial(rng) for _ in range(int(sys.argv[1])))
print(dict(res))
