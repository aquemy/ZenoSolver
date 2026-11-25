#!/usr/bin/env python3
"""Data of the algorithm page (site/solver/algorithm.qmd).

The page follows one worked example, the instance of the Problem page (site/problem/example.dat,
n = 3, t = 3, p = 2), and contrasts it with a second instance whose bracket leaves levels open.
For both, this script recomputes from the definitions of doc/theory/exact-front.md:

- the one-plane table G (Lemma 6.1);
- per level T, the relaxation L (Lemma 3.5), the pairs bound U (Proposition 6.4) and the chains
  bound U3 of the C++ solver (checked here; the note states nothing about U3), from their gadgets and from the link-forest DP with trees of at most 2 and 3 planes), E by the
  link-forest DP (Theorem 6.7), by the sigma-DP (Theorem 6.8), and by brute force over all
  multisets and partitions, with the parity matrix of Definition 2.1 deciding admissibility;
- the breakpoints of E (Proposition 6.3), the certificate gap kinds (§8), and the levels the
  breakpoint search of include/zeno/breakpoints.hpp evaluates.

It checks that these agree with each other and with `zeno`: the breakpoints of E are the front
zeno prints, the levels the bracket closes are those `--stats` counts, the gap kinds are those of
the certificate zeno writes, and every number the page quotes (PAGE_FACTS) holds.

Writes into site/algorithm/: data.json (figures 3 to 5), contrast.dat, and the Markdown partials
_run.md, _levels-example.md, _levels-contrast.md, _table-g.md, _gaps-example.md and
_gaps-contrast.md. Deterministic; needs only python3 and build/release/zeno.

    python3 site/gen_algorithm.py [--zeno PATH]
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import re
import subprocess
import sys
import tempfile
from functools import reduce as fold
from pathlib import Path

INF = math.inf
SITE = Path(__file__).resolve().parent
REPO = SITE.parent
OUT = SITE / "algorithm"

# The contrast instance of figure 4: three cities, four passengers, two planes. Its relaxation L
# is below the pairs bound U on two levels, which the worked example never is.
CONTRAST = {"n": 3, "t": 4, "p": 2, "d": [3, 5, 7], "c": [10, 5, 1]}


# ---------------------------------------------------------------------------------------------
# The quantities of doc/theory/exact-front.md, from their definitions.


class Instance:
    """A symmetric instance with integer durations, divided by their gcd g (§6)."""

    def __init__(self, n: int, t: int, p: int, d: list[int], c: list[int]):
        assert len(d) == len(c) == n and 1 <= p <= t
        self.n, self.t, self.p, self.c = n, t, p, list(c)
        self.g = fold(math.gcd, d) or 1
        self.d = [x // self.g for x in d]
        self.s = 2 * t - p                     # landings (Notation)
        self.kappa = -(-self.s // p)           # ceil(s / p)
        self.mhat = self.s - p + 1             # largest group
        self.qmax = min(p, t - p + 1)          # the C++ DP's cap on the planes of a tree
        self.w = min(p - 1, t - p)             # Lemma 2.7, Theorem 6.8
        cheap = min(range(n), key=lambda i: (self.c[i], self.d[i]))
        self.T_lo = min(self.d) * self.kappa   # Proposition 3.6
        self.T_hi = self.d[cheap] * self.kappa
        self.cheapest_cost = self.s * self.c[cheap]

    def dominated(self) -> list[int]:
        """Cities that Proposition 6.5 removes (dominated by, or equal to an earlier, city)."""
        out = []
        for i in range(self.n):
            for j in range(self.n):
                if i != j and self.d[j] <= self.d[i] and self.c[j] <= self.c[i] and \
                        ((self.d[j], self.c[j]) != (self.d[i], self.c[i]) or j < i):
                    out.append(i)
                    break
        return out


def one_plane_table(inst: Instance, M: int, Tmax: int):
    """G[m][tau] of Lemma 6.1, with the city of the first optimal choice of each cell."""
    G = [[INF] * (Tmax + 1) for _ in range(M + 1)]
    pred = [[None] * (Tmax + 1) for _ in range(M + 1)]
    G[0] = [0] * (Tmax + 1)
    for m in range(1, M + 1):
        for tau in range(Tmax + 1):
            for i in range(inst.n):
                if inst.d[i] <= tau and inst.c[i] + G[m - 1][tau - inst.d[i]] < G[m][tau]:
                    G[m][tau] = inst.c[i] + G[m - 1][tau - inst.d[i]]
                    pred[m][tau] = i
    return G, pred


def table_lookup(G):
    def g(m: int, tau: int) -> float:
        if m < 0 or tau < 0 or m >= len(G):
            return INF
        assert tau < len(G[m]), "the one-plane table does not cover the level"
        return G[m][tau]
    return g


def witness(inst: Instance, G, pred, m: int, tau: int) -> list[int]:
    out = []
    while m > 0:
        i = pred[m][tau]
        out.append(i)
        m, tau = m - 1, tau - inst.d[i]
    return sorted(out)


def knapsack(inst: Instance, gadgets) -> float:
    """For[p][s] over gadgets (q planes, j landings, cost), §6."""
    F = {(0, 0): 0}
    for P in range(1, inst.p + 1):
        for J in range(1, inst.s + 1):
            best = INF
            for q, j, cost in gadgets:
                if q <= P and j <= J and (P - q, J - j) in F:
                    best = min(best, F[(P - q, J - j)] + cost)
            if best < INF:
                F[(P, J)] = best
    return F.get((inst.p, inst.s), INF)


def relaxed_bound(inst: Instance, g, T: int) -> float:
    """L(T): single planes of any size, no admissibility (Lemma 3.5, §6)."""
    return knapsack(inst, [(1, m, g(m, T)) for m in range(1, inst.mhat + 1)])


def gadget_bound(inst: Instance, g, T: int, chains: bool) -> float:
    """U(T) (single odd planes and pairs) or U3(T) (also chains), §6."""
    n, mh, d, c = inst.n, inst.mhat, inst.d, inst.c
    gs = [(1, m, g(m, T)) for m in range(1, mh + 1, 2)]
    for a in range(2, mh + 1, 2):
        for b in range(2, mh + 1, 2):
            for i in range(n):
                gs.append((2, a + b, 2 * c[i] + g(a - 1, T - d[i]) + g(b - 1, T - d[i])))
    if chains:
        for a in range(2, mh + 1, 2):
            for b in range(3, mh + 1, 2):
                for b2 in range(2, mh + 1, 2):
                    for i in range(n):
                        for j in range(n):
                            gs.append((3, a + b + b2, 2 * c[i] + 2 * c[j] + g(a - 1, T - d[i])
                                       + g(b - 2, T - d[i] - d[j]) + g(b2 - 1, T - d[j])))
    return knapsack(inst, gs)


def forest_dp(inst: Instance, g, T: int, Q: int):
    """The link-forest DP of Theorem 6.7 with trees of at most Q planes, dense in tau.

    Returns (For[p][s], tables) with tables Ch[q][(tau, j)], Sub[(a, q, j)], Root[(q, j)]."""
    n, s, d, c = inst.n, inst.s, inst.d, inst.c
    Ch = {0: {(0, 0): 0}}
    Sub: dict = {}
    Root: dict = {}
    for q in range(1, Q + 1):
        for (tau, jp), cost in Ch[q - 1].items():
            for r in range(1, s + 1, 2):
                if jp + r <= s:
                    v = cost + g(r, T - tau)
                    if v < Root.get((q, jp + r), INF):
                        Root[(q, jp + r)] = v
                if jp + 1 + r <= s:
                    for a in range(n):
                        v = c[a] + cost + g(r, T - d[a] - tau)
                        if v < Sub.get((a, q, jp + 1 + r), INF):
                            Sub[(a, q, jp + 1 + r)] = v
        if q < Q:
            cur: dict = {}
            for qp in range(1, q + 1):
                for (tau0, j0), cost0 in Ch[q - qp].items():
                    for (a, qq, jj), sv in Sub.items():
                        tau, j = tau0 + d[a], j0 + 1 + jj
                        if qq == qp and tau <= T and j <= s and sv < INF:
                            v = cost0 + c[a] + sv
                            if v < cur.get((tau, j), INF):
                                cur[(tau, j)] = v
            Ch[q] = cur
    For = {(0, 0): 0}
    for P in range(1, inst.p + 1):
        for J in range(1, s + 1):
            best = INF
            for q in range(1, min(P, Q) + 1):
                for j in range(1, J + 1):
                    if (P - q, J - j) in For and (q, j) in Root:
                        best = min(best, For[(P - q, J - j)] + Root[(q, j)])
            if best < INF:
                For[(P, J)] = best
    return For.get((inst.p, s), INF), {"Ch": Ch, "Sub": Sub, "Root": Root, "For": For}


def sigma_dp(inst: Instance, g, T: int) -> float:
    """The sigma-DP of Theorem 6.8: planes in order, sigma = the cities of odd column so far."""
    n, s, w, d, c = inst.n, inst.s, inst.w, inst.d, inst.c
    sets = [frozenset(x) for u in range(w + 1) for x in itertools.combinations(range(n), u)]
    layer = {(0, frozenset()): 0}
    for _ in range(inst.p):
        nxt: dict = {}
        for (j, sigma), v in layer.items():
            for m in range(1, inst.mhat + 1):
                if j + m > s:
                    break
                for eta in sets:
                    if len(eta) % 2 != (m + 1) % 2 or len(eta) > min(m - 1, w):
                        continue
                    ns = sigma ^ eta
                    if len(ns) > w:
                        continue
                    wt = sum(c[i] for i in eta) + g(m - len(eta), T - sum(d[i] for i in eta))
                    if wt < INF and v + wt < nxt.get((j + m, ns), INF):
                        nxt[(j + m, ns)] = v + wt
        layer = nxt
    return layer.get((s, frozenset()), INF)


def parity_matrix(groups, n: int):
    """A parity matrix of Definition 2.1 for the groups, as one set of cities per plane, or None.

    (h1) a row marks only cities of its group; (h2) row k has |X_k| + 1 entries mod 2;
    (h3) every column is even."""
    options = []
    for X in groups:
        support = sorted(set(X))
        need = (len(X) + 1) % 2
        options.append([frozenset(e) for r in range(need, len(support) + 1, 2)
                        for e in itertools.combinations(support, r)])
    for rows in itertools.product(*options):
        column = [0] * n
        for row in rows:
            for i in row:
                column[i] ^= 1
        if not any(column):
            return [sorted(row) for row in rows]
    return None


def partitions(inst: Instance):
    """Every partition of every multiset of s cities into p groups, up to the order of planes."""
    seen = set()
    for X in itertools.combinations_with_replacement(range(inst.n), inst.s):
        mult = [X.count(i) for i in range(inst.n)]
        spread = [list(itertools.product(range(inst.p), repeat=k)) for k in mult]
        for choice in itertools.product(*spread):
            groups = [[] for _ in range(inst.p)]
            for i, planes in enumerate(choice):
                for k in planes:
                    groups[k].append(i)
            key = tuple(sorted(tuple(sorted(x)) for x in groups))
            if key not in seen:
                seen.add(key)
                yield [list(x) for x in key]


def brute_force(inst: Instance, levels):
    """E(T) and L(T) by enumeration, with a cheapest witness (then fastest, then smallest)."""
    rows = []
    for groups in partitions(inst):
        if any(not x for x in groups):
            continue
        cost = sum(inst.c[i] for x in groups for i in x)
        load = max(sum(inst.d[i] for i in x) for x in groups)
        rows.append((cost, load, sorted(groups, key=lambda x: (len(x), x)),
                     parity_matrix(groups, inst.n) is not None))
    rows.sort(key=lambda r: (r[0], r[1], r[2]))
    E, L = {}, {}
    for T in levels:
        E[T] = next(((r[0], r[2]) for r in rows if r[3] and r[1] <= T), (INF, None))
        L[T] = next(((r[0], r[2]) for r in rows if r[1] <= T), (INF, None))
    return E, L


def search_rounds(lo: int, flo, hi: int, fhi, f):
    """The levels breakpoints() (include/zeno/breakpoints.hpp) evaluates with one thread,
    round by round."""
    rounds = []
    open_ = [(lo, hi, flo, fhi)] if flo > fhi else []
    while open_:
        probes, first = [], []
        for a, b, _, _ in open_:
            first.append(len(probes))
            if b == a + 1:
                continue
            k = max(1, min(1 // len(open_), b - a - 1))
            probes += [a + j * (b - a) // (k + 1) for j in range(1, k + 1)]
        first.append(len(probes))
        if probes:
            rounds.append(probes)
        values = [f(T) for T in probes]
        nxt = []
        for k, (a, b, fa, fb) in enumerate(open_):
            if b == a + 1:
                continue
            for i in range(first[k], first[k + 1] + 1):
                end = i == first[k + 1]
                bb, fbb = (b, fb) if end else (probes[i], values[i])
                if fbb < fa:
                    nxt.append((a, bb, fa, fbb))
                a, fa = bb, fbb
        open_ = nxt
    return rounds


# ---------------------------------------------------------------------------------------------
# zeno


def zeno_run(zeno: str, inst: dict, dat: Path, *extra: str):
    cmd = [zeno, "-n", str(inst["n"]), "-t", str(inst["t"]), "-p", str(inst["p"]), "-d", str(dat), *extra]
    res = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return res.stdout, res.stderr


def parse_front(stdout: str):
    front = []
    for line in stdout.splitlines():
        if not line.strip():
            break
        cost, makespan = line.split()
        front.append((int(cost), int(makespan)))
    return sorted(front, key=lambda x: x[1])


def parse_plans(stdout: str):
    plans, current = {}, None
    for line in stdout.splitlines():
        m = re.match(r"# cost (\d+), makespan (\d+)", line)
        if m:
            current = (int(m.group(1)), int(m.group(2)))
            plans[current] = []
        elif current and line.startswith("plane "):
            plans[current].append(line)
    return plans


def parse_settled(stderr: str) -> dict:
    m = re.search(r"settled: (.*)", stderr)
    assert m, stderr
    return {k: int(v) for k, v in (part.split() for part in m.group(1).split(", "))}


def certificate_gaps(zeno: str, inst: dict, dat: Path) -> list[str]:
    with tempfile.TemporaryDirectory() as tmp:
        cert = Path(tmp) / "front.cert"
        zeno_run(zeno, inst, dat, "--certificate", str(cert))
        lines = cert.read_text().splitlines()
    start = next(i for i, x in enumerate(lines) if x.startswith("lower-bounds"))
    count = int(lines[start].split()[1])
    return [lines[start + 1 + k].split()[1] for k in range(count)]


# ---------------------------------------------------------------------------------------------


def num(x):
    return None if x == INF else int(x)


def show(x) -> str:
    return "∞" if x == INF or x is None else str(int(x))


def groups_text(groups, sep: str = " | ") -> str:
    return sep.join("{" + ", ".join(str(i + 1) for i in x) + "}" for x in groups) if groups else ""


def solve(zeno: str, spec: dict, dat: Path, label: str):
    inst = Instance(spec["n"], spec["t"], spec["p"], spec["d"], spec["c"])
    top = inst.T_hi + 1
    G, pred = one_plane_table(inst, inst.s, top)
    g = table_lookup(G)
    levels = list(range(0, top + 1))
    E_bf, L_bf = brute_force(inst, levels)

    stdout, stderr = zeno_run(zeno, spec, dat, "--plans", "--stats")
    front = parse_front(stdout)
    settled = parse_settled(stderr)

    rows, E_prev = [], INF
    for T in levels:
        L = relaxed_bound(inst, g, T)
        U = gadget_bound(inst, g, T, chains=False)
        U3 = gadget_bound(inst, g, T, chains=True)
        E, _ = forest_dp(inst, g, T, inst.qmax)
        assert forest_dp(inst, g, T, 2)[0] == U, (label, T, "U = forest DP with trees of <= 2 planes")
        assert forest_dp(inst, g, T, 3)[0] == U3, (label, T, "U3 = forest DP with trees of <= 3 planes")
        assert sigma_dp(inst, g, T) == E, (label, T, "Theorem 6.8: the sigma-DP gives E")
        assert E_bf[T][0] == E, (label, T, "Theorem 6.7: the forest DP gives E (brute force)")
        assert L_bf[T][0] == L, (label, T, "L is the cheapest partition, admissible or not")
        assert L <= E <= U3 <= U, (label, T, "Proposition 6.4")
        # The C++ shortcuts E = U (q_max <= 2) and E = U3 (q_max <= 3): checked here on the page's
        # instances, and per run by the certificates; the note claims nothing about them.
        if inst.qmax <= 2:
            assert E == U, (label, T, "E = U when q_max <= 2")
        if inst.qmax <= 3:
            assert E == U3, (label, T, "E = U3 when q_max <= 3")
        assert (E < INF) == (T >= inst.T_lo) and (E == inst.cheapest_cost) == (T >= inst.T_hi), \
            (label, T, "E is infinite below T_lo (Lemma 6.2) and cheapest from T_hi on")
        in_range = inst.T_lo <= T <= inst.T_hi
        how = None
        if in_range:
            how = "bracket" if L == U else "pairs" if inst.qmax <= 2 else "open"
        rows.append({
            "T": T, "makespan": 2 * inst.g * T, "L": num(L), "U": num(U), "U3": num(U3), "E": num(E),
            "settled": how, "breakpoint": E < E_prev,
            "partition": [[i + 1 for i in x] for x in E_bf[T][1]] if E_bf[T][1] else None,
            "relaxed": [[i + 1 for i in x] for x in L_bf[T][1]] if L_bf[T][1] else None,
            "relaxedAdmissible": L_bf[T][1] is not None and parity_matrix(L_bf[T][1], inst.n) is not None,
        })
        E_prev = E

    # Proposition 6.3: the front is the set of breakpoints (E(T), 2gT).
    ours = [(r["E"], r["makespan"]) for r in rows if r["breakpoint"]]
    assert ours == front, (label, "the breakpoints of E are the front zeno prints", ours, front)
    # The bracket closes the levels --stats counts (q_max <= 2: the others are settled by pairs).
    counts = {k: sum(1 for r in rows if r["settled"] == k) for k in ("bracket", "pairs")}
    assert settled.get("bracket") == counts["bracket"], (label, settled, counts)
    if inst.qmax <= 2:
        assert settled.get("pairs") == counts["pairs"], (label, settled, counts)
    assert not inst.dominated(), (label, "the page says that the reduction removes no city")

    # §8: gap i is `relaxed` when L at level T*_i = T_{i+1} - 1 reaches C_i, `forest` otherwise.
    by_T = {r["T"]: r for r in rows}
    gaps = []
    for (C_i, M_i), (C_next, M_next) in zip(front, front[1:]):
        Tstar = (M_next - 1) // 2 // inst.g
        L_star = by_T[Tstar]["L"]
        gaps.append({"from": [C_i, M_i], "to": [C_next, M_next], "level": Tstar,
                     "L": L_star, "need": C_i, "kind": "relaxed" if L_star >= C_i else "forest"})
    assert [x["kind"] for x in gaps] == certificate_gaps(zeno, spec, dat), (label, "certificate gap kinds")

    stair = [[m > 0 and G[m][T] < INF and (T == 0 or G[m][T] < G[m][T - 1]) for T in range(top + 1)]
             for m in range(inst.mhat + 1)]
    data = {
        "label": label, "n": inst.n, "t": inst.t, "p": inst.p, "d": spec["d"], "c": spec["c"],
        "s": inst.s, "kappa": inst.kappa, "g": inst.g, "Tlo": inst.T_lo, "Thi": inst.T_hi,
        "qmax": inst.qmax, "mhat": inst.mhat, "w": inst.w,
        "front": [list(x) for x in front], "levels": rows,
        "stats": re.search(r"settled: .*", stderr).group(0), "gaps": gaps,
        "G": {
            "values": [[num(G[m][T]) for T in range(inst.T_hi + 1)] for m in range(inst.mhat + 1)],
            "pred": [[(pred[m][T] + 1 if pred[m][T] is not None else None) for T in range(inst.T_hi + 1)]
                     for m in range(inst.mhat + 1)],
            "witness": [[([i + 1 for i in witness(inst, G, pred, m, T)] if G[m][T] < INF else None)
                         for T in range(inst.T_hi + 1)] for m in range(inst.mhat + 1)],
            "stair": [row[: inst.T_hi + 1] for row in stair],
        },
    }
    return inst, data, (G, g), stdout, stderr


def levels_table(data: dict) -> str:
    out = ["| level $T$ | makespan $2gT$ | $L(T)$ | $E(T)$ | $U(T)$ | settled by | cheapest admissible groups | front point |",
           "|---:|---:|---:|---:|---:|---|---|---|"]
    for r in data["levels"]:
        if r["T"] < data["Tlo"] - 1:
            continue
        point = f"({r['E']}, {r['makespan']})" if r["breakpoint"] else ""
        groups = groups_text([[i - 1 for i in x] for x in r["partition"]], " \\| ") if r["partition"] else "none"
        how = {"bracket": "$L = U$", "pairs": "$U$ (exact, $q_{\\max} \\le 2$)"}.get(r["settled"], "")
        if r["T"] > data["Thi"]:
            how = "above $T_{\\rm hi}$"
        elif r["T"] < data["Tlo"]:
            how = "below $T_{\\rm lo}$"
        out.append(f"| {r['T']} | {r['makespan']} | {show(r['L'])} | {show(r['E'])} | {show(r['U'])} | {how} | {groups} | {point} |")
    return "\n".join(out) + "\n"


def g_table(data: dict) -> str:
    G = data["G"]["values"]
    width = len(G[0])
    out = ["| $m$ / $\\tau$ | " +" | ".join(str(T) for T in range(width)) + " |",
           "|---|" + "---:|" * width]
    for m, row in enumerate(G):
        out.append(f"| {m} | " + " | ".join(show(x) for x in row) + " |")
    return "\n".join(out) + "\n"


def gaps_table(data: dict) -> str:
    out = ["| gap | between | level $T^\\star$ | $L(T^\\star)$ | needed $C_i$ | kind |",
           "|---:|---|---:|---:|---:|---|"]
    for k, x in enumerate(data["gaps"], 1):
        out.append(f"| {k} | ({x['from'][0]}, {x['from'][1]}) and ({x['to'][0]}, {x['to'][1]}) | {x['level']} | "
                   f"{x['L']} | {x['need']} | `{x['kind']}` |")
    return "\n".join(out) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--zeno", default=os.environ.get("ZENO", str(REPO / "build" / "release" / "zeno")))
    zeno = ap.parse_args().zeno
    if not Path(zeno).is_file():
        print(f"gen_algorithm: {zeno} not found (build zeno first, or pass --zeno)", file=sys.stderr)
        return 1
    OUT.mkdir(exist_ok=True)

    example_dat = SITE / "problem" / "example.dat"
    d, c = ([int(x) for x in line.split()] for line in example_dat.read_text().split("\n")[:2])
    example = {"n": len(d), "t": 3, "p": 2, "d": d, "c": c}
    contrast_dat = OUT / "contrast.dat"
    contrast_dat.write_text(" ".join(map(str, CONTRAST["d"])) + "\n" + " ".join(map(str, CONTRAST["c"])) + "\n")

    inst, ex, (G, g), stdout, stderr = solve(zeno, example, example_dat, "Worked example")
    cinst, co, (_, cg), _, _ = solve(zeno, CONTRAST, contrast_dat, "Contrast instance")

    # The numbers the page quotes. If the example changes, this fails and the page needs editing.
    plans = parse_plans(stdout)
    lv = {r["T"]: r for r in ex["levels"]}
    clv = {r["T"]: r for r in co["levels"]}
    _, tab = forest_dp(inst, g, 8, inst.qmax)
    facts = {
        "example instance": (example["d"], example["c"]) == ([2, 3, 5], [9, 6, 1]),
        "s, kappa, g, T_lo, T_hi, q_max, w, mhat": (inst.s, inst.kappa, inst.g, inst.T_lo, inst.T_hi,
                                                     inst.qmax, inst.w, inst.mhat) == (4, 2, 1, 4, 10, 2, 1, 3),
        "front": ex["front"] == [[36, 8], [30, 10], [24, 12], [20, 14], [14, 16], [4, 20]],
        "E on the levels": [lv[T]["E"] for T in range(4, 11)] == [36, 30, 24, 20, 14, 14, 4],
        "L = U on every level": all(lv[T]["L"] == lv[T]["U"] for T in range(4, 11)),
        "stats": ex["stats"] == "settled: bracket 7, pairs 0, chains 0, monotone 0, exact 0",
        "figure 1: {2,3}|{2,3}": parity_matrix([[1, 2], [1, 2]], 3) is not None
        and sorted(parity_matrix([[1, 2], [1, 2]], 3)) in ([[1], [1]], [[2], [2]]),
        "figure 1: {1,3}|{2,2} is not admissible": parity_matrix([[0, 2], [1, 1]], 3) is None,
        "figure 1: cost and loads": (sum(c[i] for i in [0, 2, 1, 1]), d[0] + d[2], 2 * d[1]) == (22, 7, 6),
        "E(8) partition": lv[8]["partition"] == [[2, 3], [2, 3]],
        "G[2][8] = 7, {2, 3}": G[2][8] == 7 and ex["G"]["witness"][2][8] == [2, 3],
        "G[3][8] = 21, G[1][8] = 1, G[1][5] = 1": (G[3][8], G[1][8], G[1][5]) == (21, 1, 1),
        "forest DP at T = 8": (tab["Root"][(1, 1)], tab["Root"][(1, 3)], tab["Sub"][(1, 1, 2)],
                               tab["Ch"][1][(3, 3)], tab["Root"][(2, 4)], tab["For"][(2, 4)]) == (1, 21, 7, 13, 14, 14),
        "plan of (14, 16)": plans[(14, 16)] == [
            "plane 1: CI->c2[0,3]p1 c2->CI[3,6] CI->c3[6,11]p2 c3->CG[11,16]p2",
            "plane 2: CI->c3[0,5]p3 c3->CG[5,10]p3 CG->c2[10,13] c2->CG[13,16]p1"],
        "all example gaps relaxed": [x["kind"] for x in ex["gaps"]] == ["relaxed"] * 5,
        "contrast levels": (cinst.T_lo, cinst.T_hi, cinst.s, cinst.qmax) == (9, 21, 6, 2),
        "contrast open levels": [T for T in range(9, 22) if clv[T]["L"] < clv[T]["U"]] == [12, 14],
        "contrast T = 12": (clv[12]["L"], clv[12]["E"], clv[12]["relaxed"], clv[12]["partition"])
        == (46, 50, [[2, 3], [1, 1, 1, 1]], [[1, 1, 2], [1, 1, 2]]),
        "contrast T = 14": (clv[14]["L"], clv[14]["E"], clv[14]["relaxed"]) == (37, 40, [[3, 3], [1, 1, 1, 2]]),
        "contrast stats": co["stats"] == "settled: bracket 11, pairs 2, chains 0, monotone 0, exact 0",
        "contrast gaps": [x["kind"] for x in co["gaps"]] == ["relaxed", "forest", "forest", "relaxed", "relaxed", "relaxed"],
    }
    # Breakpoint search with one thread (include/zeno/breakpoints.hpp), checked against zeno.
    E_of = {r["T"]: r["E"] for r in ex["levels"]}
    rounds = search_rounds(inst.T_lo, E_of[inst.T_lo], inst.T_hi, E_of[inst.T_hi], lambda T: E_of[T])
    _, search_err = zeno_run(zeno, example, example_dat, "--levels", "search", "--threads", "1", "--stats")
    facts["search rounds"] = rounds == [[7], [5, 8], [6, 9]]
    facts["search evaluations"] = sum(parse_settled(search_err).values()) == 1 + sum(map(len, rounds))
    failed = [k for k, ok in facts.items() if not ok]
    if failed:
        print("gen_algorithm: page facts that no longer hold: " + "; ".join(failed), file=sys.stderr)
        return 1
    ex["searchRounds"] = rounds

    data = {"generatedBy": "site/gen_algorithm.py", "example": ex, "contrast": co}
    (OUT / "data.json").write_text(json.dumps(data, separators=(",", ":"), ensure_ascii=False) + "\n")
    (OUT / "_levels-example.md").write_text(levels_table(ex))
    (OUT / "_levels-contrast.md").write_text(levels_table(co))
    (OUT / "_table-g.md").write_text(g_table(ex))
    (OUT / "_gaps-example.md").write_text(gaps_table(ex))
    (OUT / "_gaps-contrast.md").write_text(gaps_table(co))
    (OUT / "_run.md").write_text(
        "```sh\n$ zeno -n 3 -t 3 -p 2 -d site/problem/example.dat --plans --stats\n" + stdout + stderr + "```\n")
    print(f"gen_algorithm: {len(ex['levels'])} + {len(co['levels'])} levels checked against {zeno}; wrote {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
