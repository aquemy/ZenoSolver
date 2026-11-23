"""Anti-correlated instances (cheap cities are long) for theorychecks.
usage: python3 theorychecks_anti.py <scratchpad> <count> <seed>"""
import random, subprocess, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

S = sys.argv[1]; N = int(sys.argv[2]); random.seed(int(sys.argv[3]))
jobs = []
for idx in range(N):
    p = random.randint(2, 5); t = random.randint(p + 1, p + 4); n = random.randint(2, 5)
    while 2 * t - p > 10: t -= 1
    d = sorted(random.sample(range(1, 14), n)); c = sorted(random.sample(range(0, 20), n), reverse=True)
    jobs.append((d, c, t, p, idx))

def run(j):
    d, c, t, p, idx = j
    r = subprocess.run([S + "/bin/theorychecks", ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p), str(idx)],
                       capture_output=True, text=True, timeout=900)
    return j, r.stdout.split()

tot = Counter(); levels = inst = 0; ex = {}
with ThreadPoolExecutor(max_workers=12) as e:
    for j, f in e.map(run, jobs):
        if not f: continue
        inst += 1; levels += int(f[0])
        for kv in f[2:]:
            k, v = kv.rsplit("=", 1); tot[k] += int(v)
            if int(v) and k not in ex: ex[k] = j
print(f"{inst} instances, {levels} levels")
for k in sorted(tot): print(f"  {k}: {tot[k]}" + (f"   e.g. {ex[k]}" if k in ex else ""))
