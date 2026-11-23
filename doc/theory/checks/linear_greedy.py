"""Does the papers' per-PPP greedy reach the exact front on the linear family d=(1..n), c=n+1-d?
usage: python3 linear_greedy.py <scratchpad>"""
import subprocess, sys
from concurrent.futures import ThreadPoolExecutor
S = sys.argv[1]
jobs = [(n, t, p) for n in range(2, 7) for p in range(1, 6) for t in range(p, p + 5) if 2 * t - p <= 11]
def run(j):
    n, t, p = j; d = ",".join(str(i) for i in range(1, n + 1)); c = ",".join(str(n + 1 - i) for i in range(1, n + 1))
    a = subprocess.run([S + "/bin/scale_g", "front", d, c, str(t), str(p)], capture_output=True, text=True, timeout=1200).stdout
    b = subprocess.run([S + "/bin/scale_g", "gfront", d, c, str(t), str(p)], capture_output=True, text=True, timeout=1200).stdout
    return j, a == b, len(a.split("\n")) - 1
bad = []; tot = 0
with ThreadPoolExecutor(max_workers=12) as e:
    for j, same, npts in e.map(run, jobs):
        tot += 1
        if not same: bad.append(j)
print(f"{tot} linear instances, greedy front differs on {len(bad)}: {bad[:10]}")
