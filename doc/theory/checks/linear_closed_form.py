"""Linear family: check E(T) = L(T) = alpha*s - beta*Phi(T) for d = (1..n), c_i = alpha - beta*i, where
Phi(T) = (p - rho)*min(T, n*q0) + rho*min(T, n*(q0+1)), q0 = s // p, rho = s % p, for T >= ceil(s/p).
Also probe offset progressions d_i = a + b*i (no claim). usage: python3 linear_closed_form.py <scratchpad>"""
import random, subprocess, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
S = sys.argv[1]; random.seed(3)

def table(d, c, t, p):
    r = subprocess.run([S + "/bin/theorychecks", ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p), "Eonly"],
                       capture_output=True, text=True, timeout=1200)
    out = {}
    for l in r.stdout.split("\n"):
        if l.strip(): T, L, E = map(int, l.split()); out[T] = (L, E)
    return out

jobs = []
for n in range(1, 9):
    for p in range(1, 7):
        for t in range(p, p + 7):
            if 2 * t - p > 18: continue
            beta = random.randint(0, 3); alpha = beta * n + random.randint(0, 4)
            jobs.append(("lin", n, t, p, alpha, beta, 0, 1))
for _ in range(150):
    n = random.randint(2, 6); p = random.randint(1, 5); t = random.randint(p, p + 5)
    if 2 * t - p > 16: continue
    a = random.randint(1, 4); b = random.randint(1, 3); beta = random.randint(1, 3); alpha = beta * (a + b * n) + random.randint(0, 3)
    jobs.append(("off", n, t, p, alpha, beta, a, b))

def run(j):
    kind, n, t, p, alpha, beta, a, b = j
    d = [a + b * i for i in range(1, n + 1)] if kind == "off" else list(range(1, n + 1))
    c = [alpha - beta * x for x in d]
    tab = table(d, c, t, p); s = 2 * t - p; q0, rho = divmod(s, p); cs = -(-s // p)
    res = Counter()
    for T, (L, E) in tab.items():
        if kind == "lin":
            if T < cs: ok = (L == -1 and E == -1)
            else: ok = (L == E == alpha * s - beta * ((p - rho) * min(T, n * q0) + rho * min(T, n * (q0 + 1))))
            res["lin_ok" if ok else "lin_FAIL"] += 1
        else:
            res["off_L=E" if L == E else "off_L<E"] += 1
    return j, res

tot = Counter(); ex = {}
with ThreadPoolExecutor(max_workers=12) as e:
    for j, r in e.map(run, jobs):
        tot.update(r)
        for k in r:
            if ("FAIL" in k or "L<E" in k) and k not in ex: ex[k] = j
print(len(jobs), "instances", dict(tot))
for k, v in ex.items(): print("  e.g.", k, v)
