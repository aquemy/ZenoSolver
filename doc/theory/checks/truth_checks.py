"""Compare the all-plans oracle `truth` with the theory (symmetric instances).
  cor45 : central in {none, a1}: truth front (planes end in C_G) == breakpoints (E(T), 2T)
  B3    : central in {none, a1}: truth front with ANYWHERE=1 == truth front
  R     : every central regime: each truth point (C, M) has C >= L(floor(M/2))
  ach   : every regime: each (E(T), 2T) breakpoint is weakly dominated by a truth point
  info  : tight regime, ANYWHERE front vs C_G front (no claim)
usage: python3 truth_checks.py <scratchpad> <count> <seed>"""
import os, random, subprocess, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

S = sys.argv[1]; N = int(sys.argv[2]); random.seed(int(sys.argv[3]))

def front_of(out):
    pts = [tuple(map(int, l.split())) for l in out.strip().splitlines() if l.strip()]
    return sorted(pts)

def truth(d, c, t, p, central, anywhere):
    env = dict(os.environ)
    if anywhere: env["ANYWHERE"] = "1"
    else: env.pop("ANYWHERE", None)
    r = subprocess.run([S + "/bin/truth", ",".join(map(str, d)), ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p), central, "2"],
                       capture_output=True, text=True, timeout=300, env=env)
    return front_of(r.stdout)

def bracket(d, c, t, p):
    r = subprocess.run([S + "/bin/theorychecks", ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p), "bracket"],
                       capture_output=True, text=True, timeout=300)
    L, E = {}, {}
    for l in r.stdout.split("\n"):
        if not l.strip(): continue
        T, a, b = map(int, l.split()); L[T] = a; E[T] = b
    return L, E

jobs = []
for _ in range(N):
    p = random.randint(1, 3); t = random.randint(p, min(5, p + 3)); n = random.randint(1, 3)
    d = [random.randint(1, 6) for _ in range(n)]; c = [random.randint(0, 9) for _ in range(n)]
    for central in ("none", "a1", "tight"): jobs.append((d, c, t, p, central))

def run(j):
    d, c, t, p, central = j
    try:
        cg = truth(d, c, t, p, central, False); an = truth(d, c, t, p, central, True)
    except subprocess.TimeoutExpired:
        return j, None
    L, E = bracket(d, c, t, p)
    res = Counter()
    ef, prev = [], None
    for T in sorted(E):
        if E[T] >= 0 and (prev is None or E[T] < prev): ef.append((E[T], 2 * T)); prev = E[T]
    ef.sort()
    Tmax = max(L)
    def Lat(M):
        T = min(M // 2, Tmax); return L[T]
    if central in ("none", "a1"):
        res["cor45_ok" if cg == ef else "cor45_FAIL"] += 1
        res["B3_ok" if an == cg else "B3_FAIL"] += 1
    else:
        res["tight_anywhere_same" if an == cg else "tight_anywhere_differs"] += 1
        res["tight_front_equals_E" if cg == ef else "tight_front_differs_from_E"] += 1
    ok = all(Lat(M) >= 0 and C >= Lat(M) for (C, M) in cg)
    res["R_ok" if ok else "R_FAIL"] += 1
    ok = all(any(C2 <= C and M2 <= M for (C2, M2) in cg) for (C, M) in ef)
    res["ach_ok" if ok else "ach_FAIL"] += 1
    return j, res

tot = Counter(); fails = []
with ThreadPoolExecutor(max_workers=12) as e:
    for j, r in e.map(run, jobs):
        if r is None: tot["timeout"] += 1; continue
        tot.update(r)
        if any("FAIL" in k for k in r): fails.append((j, dict(r)))
print(dict(sorted(tot.items())))
for f in fails[:8]: print("  FAIL", f)
