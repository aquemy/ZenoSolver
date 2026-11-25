"""Schedulable domination, front level (doc/theory/exact-front.md, Thm 5.3): on random non-symmetric
instances, compare the front of role-configuration schedules (config_front: exact waiting, best orders
and matching) with the front of all plans (truth) or of all simple plans with clean journeys and up to
`extra` landings beyond s (simple_plans). Every configuration schedule is a plan, so the fronts are equal
iff every plan is weakly dominated by a configuration schedule. The script also reports on how many instances
waiting changes the front: the front of simple plans with exactly s landings differs from the front of the
same plans with waiting ignored (`simple_plans ... 0 nowait`).

usage: python3 sd_checks.py <checks dir> <oracle: truth|simple> <count> <seed> [family] [extra] [max s]
  family uniform : durations uniform in [1, 6] (truth) or [1, 20] (simple)
  family waiting : like Prop 5.7, one city with d_y well above dbar_y and a short cheap-to-reach city
truth runs with central = none and a1 (both satisfy (A1-NS)); simple plans have no central flights.
Prints a summary and every instance whose fronts differ."""
import random, subprocess, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

D = sys.argv[1]; oracle = sys.argv[2]; N = int(sys.argv[3]); random.seed(int(sys.argv[4]))
family = sys.argv[5] if len(sys.argv) > 5 else "uniform"
extra = int(sys.argv[6]) if len(sys.argv) > 6 else 1
smax = int(sys.argv[7]) if len(sys.argv) > 7 else None

def front(out):
    return sorted(tuple(map(int, l.split())) for l in out.strip().splitlines() if l.strip())

def instance():
    if oracle == "truth":
        p = random.randint(1, 3); t = random.randint(p + 1, min(5, p + 3)); n = random.randint(1, 2); hi = 6
    else:
        p = random.randint(1, 4); t = random.randint(p + 1, min(7, p + 3)); n = random.randint(1, 3); hi = 20
        if family == "waiting": n = max(n, 2)
        while 2 * t - p > (smax or (8 if n == 3 else 10)): t -= 1
    if family == "waiting":
        n = max(n, 2)
        d = [random.randint(1, 3)] + [random.randint(hi // 2, hi) for _ in range(n - 1)]
        db = [random.randint(1, 3)] + [random.randint(1, hi // 2) for _ in range(n - 1)]
        c = [random.randint(3, 6)] + [random.randint(0, 2) for _ in range(n - 1)]
    else:
        d = [random.randint(1, hi) for _ in range(n)]; db = [random.randint(1, hi) for _ in range(n)]
        c = [random.randint(0, 6) for _ in range(n)]
    return d, db, c, t, p

def run(job):
    d, db, c, t, p, central = job
    a = ",".join
    args = [a(map(str, d)), a(map(str, db)), a(map(str, c)), str(t), str(p)]
    try:
        if oracle == "truth":
            o = subprocess.run([D + "/bin/truth"] + args + [central, "3"], capture_output=True, text=True, timeout=600)
        else:
            o = subprocess.run([D + "/bin/simple_plans"] + args + [str(extra)], capture_output=True, text=True, timeout=600)
        cf = subprocess.run([D + "/bin/config_front"] + args, capture_output=True, text=True, timeout=600)
        nw = subprocess.run([D + "/bin/simple_plans"] + args + ["0", "nowait"], capture_output=True, text=True, timeout=600)
        ex = o if oracle == "simple" and extra == 0 else \
            subprocess.run([D + "/bin/simple_plans"] + args + ["0"], capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        return job, None, None
    if o.returncode or cf.returncode:
        return job, "error", None
    waits = front(nw.stdout) != front(ex.stdout)
    return job, front(o.stdout), (front(cf.stdout), waits)

jobs = []
for _ in range(N):
    d, db, c, t, p = instance()
    for central in (["none", "a1"] if oracle == "truth" and len(d) >= 2 else ["none"]):
        jobs.append((d, db, c, t, p, central))

res = Counter(); diffs = []; waiting = []
with ThreadPoolExecutor(max_workers=12) as e:
    for job, of, cfw in e.map(run, jobs):
        central = job[5]
        if of is None: res["timeout"] += 1; continue
        if of == "error": res["error"] += 1; continue
        cf, waits = cfw
        if waits: res["waiting_changes_front"] += 1; waiting.append(job)
        aph = all(db_i <= d_i + dz + dbz and d_i <= db_i + dbz + dz
                  for d_i, db_i in zip(job[0], job[1]) for dz, dbz in zip(job[0], job[1]))
        tag = central + ("_path" if aph else "_nopath")
        if of == cf: res[tag + "_equal"] += 1
        else: res[tag + "_DIFFER"] += 1; diffs.append((job, of, cf))
print(oracle, family, "extra=%d" % extra, dict(sorted(res.items())))
for job in waiting[:40]: print("WAITING", job)
for job, of, cf in diffs[:20]:
    print("DIFF", job, "\n   plans:  ", of, "\n   configs:", cf)
