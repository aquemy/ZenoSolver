import random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
S = sys.argv[1]; random.seed(41)
jobs = []
for _ in range(int(sys.argv[2])):
    p = random.randint(1, 5); t = random.randint(p, min(p + 4, 8)); n = random.randint(1, 5)
    if 2 * t - p > 11: t = (11 + p) // 2
    d = [random.randint(0 if random.random() < 0.15 else 1, 12) for _ in range(n)]
    c = [random.randint(0 if random.random() < 0.15 else 1, 15) for _ in range(n)]
    jobs.append((d, c, t, p))
def run(j):
    d, c, t, p = j
    try:
        r = subprocess.run([S + "/bin/treedp", ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p)], capture_output=True, text=True, timeout=600)
        f = r.stdout.split()
        return j, (int(f[0]), int(f[1])) if len(f) == 2 else None
    except subprocess.TimeoutExpired:
        return j, "timeout"
levels = mism = inst = bad = to = 0; ex = []
with ThreadPoolExecutor(max_workers=12) as e:
    for j, r in e.map(run, jobs):
        if r == "timeout": to += 1; continue
        if r is None: continue
        inst += 1; levels += r[0]; mism += r[1]
        if r[1]: bad += 1; ex.append(j)
print(f"{inst} instances ({to} timed out), {levels} levels compared, {mism} mismatching levels on {bad} instances")
for j in ex[:5]: print("  mismatch:", j)
