"""Run theorychecks on random small symmetric instances and aggregate mismatches.
usage: python3 theorychecks_sweep.py <scratchpad> <count> [seed]"""
import random, subprocess, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

S = sys.argv[1]; N = int(sys.argv[2]); random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 7)
jobs = []
for idx in range(N):
    p = random.randint(1, 5); t = random.randint(p, min(p + 4, 8)); n = random.randint(1, 5)
    if 2 * t - p > 10: t = (10 + p) // 2
    lo_d = 0 if random.random() < 0.2 else 1
    d = [random.randint(lo_d, 9) for _ in range(n)]
    c = [random.randint(0 if random.random() < 0.2 else 1, 12) for _ in range(n)]
    r = random.random()
    if r < 0.15 and n >= 2:                      # duplicate city
        d[1], c[1] = d[0], c[0]
    elif r < 0.30 and n >= 2:                    # tie in cost, different durations
        c[1] = c[0]
    elif r < 0.40 and n >= 2:                    # tie in duration, different costs
        d[1] = d[0]
    elif r < 0.50:                               # linear family c + d = const
        base = random.randint(1, 3); d = [base * (i + 1) for i in range(n)]; c = [base * (n + 1) - x for x in d]
    jobs.append((d, c, t, p, idx))

def run(j):
    d, c, t, p, idx = j
    try:
        r = subprocess.run([S + "/bin/theorychecks", ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p), str(idx)],
                           capture_output=True, text=True, timeout=900)
        return j, r.stdout.split()
    except subprocess.TimeoutExpired:
        return j, None

tot = Counter(); levels = hcases = inst = to = 0; ex = {}
with ThreadPoolExecutor(max_workers=12) as e:
    for j, f in e.map(run, jobs):
        if f is None: to += 1; continue
        if not f: continue
        inst += 1; levels += int(f[0]); hcases += int(f[1].split("=")[1])
        for kv in f[2:]:
            k, v = kv.rsplit("=", 1); tot[k] += int(v)
            if int(v) and k not in ex: ex[k] = j
print(f"{inst} instances ({to} timed out), {levels} levels, {hcases} random partitions for the h checks")
for k in sorted(set(tot) | set(ex)): print(f"  {k}: {tot[k]}" + (f"   e.g. {ex[k]}" if k in ex else ""))
