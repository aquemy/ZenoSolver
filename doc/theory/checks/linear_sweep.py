"""Linear family d_i = r*i, c_i = r*(n+1) - d_i (the default generator): which bounds are exact?
E(T) from the tree DP (checked against enumeration elsewhere). usage: python3 linear_sweep.py <scratchpad>"""
import subprocess, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
S = sys.argv[1]
jobs = []
for n in range(2, 9):
    for p in range(2, 7):
        for t in range(p, p + 7):
            if 2 * t - p > 18: continue
            jobs.append((n, t, p))
def run(j):
    n, t, p = j
    d = list(range(1, n + 1)); c = [n + 1 - x for x in d]
    r = subprocess.run([S + "/bin/theorychecks", ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p), "nogap"],
                       capture_output=True, text=True, timeout=1200)
    f = r.stdout.split(); return j, {kv.split("=")[0]: int(kv.split("=")[1]) for kv in f[1:]}, int(f[0])
tot = Counter(); ex = {}; lv = 0
with ThreadPoolExecutor(max_workers=12) as e:
    for j, g, L in e.map(run, jobs):
        lv += L; n, t, p = j; q = min(p, t - p + 1)
        for k, v in g.items():
            key = f"{k}_qmax{q if q < 4 else '4+'}"; tot[key] += v
            if v and key not in ex: ex[key] = j
print(f"{len(jobs)} instances, {lv} levels in [T_lo, T_hi]")
for k in sorted(tot): print(f"  {k}: {tot[k]}" + (f"   e.g. (n,t,p)={ex[k]}" if k in ex else ""))
