"""Checks for the non-symmetric scheduling lemmas of doc/theory/exact-front.md, section 6.2.

Role configuration: per plane drops Dr_k, picks Pk_k, crossings Cr_k (odd); links = matching of
drops to picks at the same city. Segment durations: drop 2d_i, pick 2db_i, crossing d_i + db_i.
W1 : if every plane has <= 1 pick and AD-path holds (db_i <= d_i + d_z + db_z), the template
     schedule (drops from time 0, crossings, picks) has makespan max_k lambda_k.
N3 : for a fixed matching and fixed relative orders of drops and of picks on each plane,
     (a) the template's simulated makespan equals the closed form
         max(max_k lambda_k, max over links of Pre_u(j) + d_i + db_i + Suf_v(l));
     (b) no other interleaving of the plane's segments (any side-consistent order with the same
         relative drop and pick orders) has a smaller makespan.
usage: python3 ns_sched_check.py <trials> <seed>"""
import itertools, random, sys
from collections import Counter

def simulate(planes, link_of_pick, d, db):
    """planes[k] = list of (type, city, tag); type in 'B' (drop), 'Bb' (pick), 'A', 'Ab'.
    link_of_pick[(k, tag)] = (u, tag_u) of the matched drop. Returns makespan or None (deadlock)."""
    nodes = [(k, j) for k in range(len(planes)) for j in range(len(planes[k]))]
    pos = {}
    for k, seq in enumerate(planes):
        for j, (ty, x, tag) in enumerate(seq): pos[(k, tag)] = j
    preds = {v: [] for v in nodes}
    for k, seq in enumerate(planes):
        for j, (ty, x, tag) in enumerate(seq):
            if j > 0: preds[(k, j)].append((k, j - 1))
            if ty == 'Bb':
                u, tu = link_of_pick[(k, tag)]; preds[(k, j)].append((u, pos[(u, tu)]))
    indeg = {v: len(preds[v]) for v in nodes}; succ = {v: [] for v in nodes}
    for v in nodes:
        for w in preds[v]: succ[w].append(v)
    order = [v for v in nodes if indeg[v] == 0]; done = []
    while order:
        v = order.pop(); done.append(v)
        for w in succ[v]:
            indeg[w] -= 1
            if indeg[w] == 0: order.append(w)
    if len(done) != len(nodes): return None
    start, arr, end = {}, {}, {}
    for v in done:
        k, j = v; ty, x, tag = planes[k][j]
        s = end[(k, j - 1)] if j > 0 else 0
        start[v] = s
        if ty == 'B': arr[v] = s + d[x]; end[v] = s + 2 * d[x]
        elif ty == 'Bb':
            u, tu = link_of_pick[(k, tag)]; drop_arr = arr[(u, pos[(u, tu)])]
            end[v] = max(s + db[x], drop_arr) + db[x]
        elif ty == 'A': end[v] = s + d[x] + db[x]
        else: end[v] = s + db[x] + d[x]
    return max(end[(k, len(planes[k]) - 1)] for k in range(len(planes)))

def template(Dr, Pk, Cr):
    planes = []
    for k in range(len(Dr)):
        seq = [('B', x, ('d', j)) for j, x in enumerate(Dr[k])]
        for j, x in enumerate(Cr[k]): seq.append(('A' if j % 2 == 0 else 'Ab', x, ('c', j)))
        seq += [('Bb', x, ('p', j)) for j, x in enumerate(Pk[k])]
        planes.append(seq)
    return planes

def lam(k, Dr, Pk, Cr, d, db):
    return sum(2 * d[x] for x in Dr[k]) + sum(2 * db[x] for x in Pk[k]) + sum(d[x] + db[x] for x in Cr[k])

def closed_form(Dr, Pk, Cr, links, d, db):
    p = len(Dr); best = max(lam(k, Dr, Pk, Cr, d, db) for k in range(p))
    for (u, j, v, l) in links:
        x = Dr[u][j]
        pre = sum(2 * d[y] for y in Dr[u][:j]); suf = sum(2 * db[y] for y in Pk[v][l + 1:])
        best = max(best, pre + d[x] + db[x] + suf)
    return best

def interleavings(seq_drops, seq_picks, crossings_cities):
    """All side-consistent sequences from C_I to C_G using the given drops (in order), picks (in order)
    and an odd number of crossings (in any assignment of cities to the A/Abar slots)."""
    nd, npk, nc = len(seq_drops), len(seq_picks), len(crossings_cities)
    out = []
    def rec(i, j, c, side, acc):
        if i == nd and j == npk and c == nc:
            if side == 'G': out.append(list(acc))
            return
        if side == 'I' and i < nd: acc.append(seq_drops[i]); rec(i + 1, j, c, side, acc); acc.pop()
        if side == 'G' and j < npk: acc.append(seq_picks[j]); rec(i, j + 1, c, side, acc); acc.pop()
        if c < nc:
            ty = 'A' if side == 'I' else 'Ab'
            acc.append((ty, crossings_cities[c], ('c', c))); rec(i, j, c + 1, 'G' if side == 'I' else 'I', acc); acc.pop()
    rec(0, 0, 0, 'I', [])
    return out

def random_config(rng, max_picks_per_plane):
    p = rng.randint(1, 3); n = rng.randint(1, 3)
    while True:
        d = [rng.randint(0, 8) for _ in range(n)]; db = [rng.randint(0, 8) for _ in range(n)]
        if all(db[i] <= d[i] + d[z] + db[z] and d[i] <= db[i] + db[z] + d[z] for i in range(n) for z in range(n)): break
    Dr = [[] for _ in range(p)]; Pk = [[] for _ in range(p)]; Cr = [[rng.randrange(n) for _ in range(rng.choice([1, 1, 3]))] for _ in range(p)]
    raw = []
    for _ in range(rng.randint(0, 3)):
        u = rng.randrange(p); cand = [v for v in range(p) if len(Pk[v]) < max_picks_per_plane]
        if not cand: break
        v = rng.choice(cand); x = rng.randrange(n)
        Dr[u].append(x); Pk[v].append(x); raw.append((u, len(Dr[u]) - 1, v, len(Pk[v]) - 1))
    return p, n, d, db, Dr, Pk, Cr, raw

def link_map(links):
    return {(v, ('p', l)): (u, ('d', j)) for (u, j, v, l) in links}

def main():
    trials = int(sys.argv[1]); rng = random.Random(int(sys.argv[2]))
    res = Counter()
    for _ in range(trials):
        # W1
        p, n, d, db, Dr, Pk, Cr, links = random_config(rng, 1)
        m = simulate(template(Dr, Pk, Cr), link_map(links), d, db)
        res['W1_ok' if m == max(lam(k, Dr, Pk, Cr, d, db) for k in range(p)) else 'W1_FAIL'] += 1
        # N3 with several picks allowed
        p, n, d, db, Dr, Pk, Cr, links = random_config(rng, 3)
        lm = link_map(links)
        mt = simulate(template(Dr, Pk, Cr), lm, d, db)
        res['N3a_ok' if mt == closed_form(Dr, Pk, Cr, links, d, db) else 'N3a_FAIL'] += 1
        per_plane = []
        for k in range(p):
            drops = [('B', x, ('d', j)) for j, x in enumerate(Dr[k])]
            picks = [('Bb', x, ('p', j)) for j, x in enumerate(Pk[k])]
            per_plane.append(interleavings(drops, picks, Cr[k]))
        if 1 <= max(len(v) for v in per_plane) and all(per_plane):
            total = 1
            for v in per_plane: total *= len(v)
            if total > 4000: res['N3b_skipped'] += 1; continue
            best = None
            for combo in itertools.product(*per_plane):
                mm = simulate(list(combo), lm, d, db)
                if mm is not None and (best is None or mm < best): best = mm
            res['N3b_ok' if best is not None and best >= mt else 'N3b_FAIL'] += 1
            if best is not None and best > mt: res['N3b_template_strictly_better'] += 1
    print(dict(res))

main()
