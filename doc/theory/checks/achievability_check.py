"""Executable check of the achievability construction (symmetric case).

Given landing multisets X_1..X_p forming an admissible partition, build:
  1. H = bipartite graph planes x cities (edge if the city is in the plane's multiset);
  2. a spanning forest of H and, on it, the T-join J for T = planes with an even number of landings;
  3. at each city, pair its J-edges: (parent plane, first child) and then children two by two;
     in each pair the first drops off (B, at the start of its schedule), the second picks up (B-bar, at the end);
  4. every plane: its drop-offs, then its remaining landings as alternating crossings E W E ... E, then its pick-up.
Then simulate (a pick-up waits for its drop-off) and check that the makespan equals the largest load,
that every plane has an odd number >= 1 of crossings and at most one pick-up, and that t passengers are delivered."""
import random, sys
from collections import defaultdict

def admissible(groups, n):
    p = len(groups); parent = list(range(p + n))
    def find(v):
        while parent[v] != v: parent[v] = parent[parent[v]]; v = parent[v]
        return v
    for k, g in enumerate(groups):
        for city in set(g): parent[find(k)] = find(p + city)
    even = defaultdict(int)
    for k, g in enumerate(groups):
        if len(g) % 2 == 0: even[find(k)] += 1
    return all(v % 2 == 0 for v in even.values())

def construct_and_simulate(groups, d, t):
    p = len(groups); cities = sorted({c for g in groups for c in g})
    adj = defaultdict(list)                       # nodes: ('P', k) and ('C', city)
    for k, g in enumerate(groups):
        for city in set(g): adj[('P', k)].append(('C', city)); adj[('C', city)].append(('P', k))
    # spanning forest by DFS, rooted at planes
    parentOf, order, seen = {}, [], set()
    for k in range(p):
        root = ('P', k)
        if root in seen: continue
        seen.add(root); parentOf[root] = None; stack = [root]
        while stack:
            v = stack.pop(); order.append(v)
            for w in adj[v]:
                if w not in seen: seen.add(w); parentOf[w] = v; stack.append(w)
    # T-join on the forest: edge (v, parent) is in J iff v's subtree holds an odd number of T vertices
    inT = {('P', k): len(g) % 2 == 0 for k, g in enumerate(groups)}
    oddCount = {}; J = set()
    for v in reversed(order):
        cnt = (1 if inT.get(v, False) else 0) + sum(oddCount[w] for w in adj[v] if parentOf.get(w) == v)
        oddCount[v] = cnt % 2
        if parentOf[v] is not None and cnt % 2 == 1: J.add((v, parentOf[v]))
    # pair J-edges at each city
    links = []                                    # (city, dropping plane, picking plane)
    for c in cities:
        node = ('C', c)
        if node not in parentOf: continue
        kids = [w[1] for w in adj[node] if parentOf.get(w) == node and (w, node) in J]
        par = parentOf[node]
        seq = ([par[1]] if (node, par) in J else []) + kids
        assert len(seq) % 2 == 0, "odd J-degree at a city"
        for a in range(0, len(seq), 2): links.append((c, seq[a], seq[a + 1]))
    drops = defaultdict(list); picks = defaultdict(list)
    for idx, (c, u, v) in enumerate(links): drops[u].append((c, idx)); picks[v].append((c, idx))
    # schedules
    dropTime = {}; finish = [0] * p; loads = []; totalEast = 0; totalB = len(links)
    plan = []
    for k, g in enumerate(groups):
        rest = list(g)
        for c, _ in drops[k] + picks[k]: rest.remove(c)        # one landing per link
        assert len(rest) % 2 == 1 and len(rest) >= 1, f"plane {k}: {len(rest)} crossings"
        assert len(picks[k]) <= 1, f"plane {k} picks {len(picks[k])} times"
        totalEast += (len(rest) + 1) // 2
        clock = 0
        for c, idx in drops[k]:
            dropTime[idx] = clock + d[c]; clock += 2 * d[c]
        for c in rest: clock += 2 * d[c]
        plan.append((clock, picks[k])); loads.append(sum(2 * d[c] for c in g))
    for k, (clock, pk) in enumerate(plan):
        for c, idx in pk:                                         # at most one
            arrival = clock + d[c]
            clock = max(arrival, dropTime[idx]) + d[c]
        finish[k] = clock
    assert totalEast + totalB == t, "passengers taken out of C_I != t"
    return max(finish), max(loads)

random.seed(17)
checked = chains = 0
for _ in range(20000):
    p = random.randint(1, 6); t = random.randint(p, p + 6); s = 2 * t - p; n = random.randint(1, 6)
    d = [random.randint(1, 20) for _ in range(n)]
    # random partition of a random multiset into p non-empty groups
    X = [random.randrange(n) for _ in range(s)]
    random.shuffle(X)
    cuts = sorted(random.sample(range(1, s), p - 1)) if p > 1 else []
    groups = [X[a:b] for a, b in zip([0] + cuts, cuts + [s])]
    if not admissible(groups, n): continue
    mk, ml = construct_and_simulate(groups, d, t)
    assert mk == ml, (groups, d, mk, ml)
    checked += 1
    evens = [k for k, g in enumerate(groups) if len(g) % 2 == 0]
    if any(not (set(groups[a]) & set(groups[b])) for a in evens for b in evens if a < b): chains += 1
print(f"admissible partitions checked: {checked}; makespan == largest load on all of them")
print(f"  of which {chains} have two even planes that share no city (linked through other planes)")
