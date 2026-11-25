"""Targeted search for counterexamples to Conjecture 4.10 of revision 2 (now Theorem 4.4).

Under symmetric durations, central flights may only beat the front of
admissible partitions (E) where the relaxation L, which needs no assumption on
central flights, is strictly below it. Those are the gaps a certificate marks
`forest`. For random tiny instances whose certificate has such a gap, compute
the true front with the shortest central flights the triangle inequality allows
(`truth ... tight`) and look for a plan inside the gap that is cheaper than E.

usage: python3 conj410_search.py <checks dir> <zeno> <trials> <seed> [maxT]
"""
import random
import subprocess
import sys
import tempfile


def front(lines):
    return sorted((int(a), int(b)) for a, b in (l.split() for l in lines.strip().splitlines() if l.strip()))


def main():
    checks, zeno, trials, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    maxT = int(sys.argv[5]) if len(sys.argv) > 5 else 5
    rng = random.Random(seed)
    candidates = tested = counterexamples = 0
    for _ in range(trials):
        p = rng.randint(2, 3)
        t = rng.randint(p + 1, maxT)
        n = rng.randint(2, 3)
        d = sorted(rng.randint(1, 9) for _ in range(n))
        c = [rng.randint(1, 30) for _ in range(n)]
        with tempfile.TemporaryDirectory() as tmp:
            data, cert = f"{tmp}/i.dat", f"{tmp}/i.cert"
            open(data, "w").write(" ".join(map(str, d)) + "\n" + " ".join(map(str, c)) + "\n")
            out = subprocess.run([zeno, "-n", str(n), "-t", str(t), "-p", str(p), "-d", data, "--certificate", cert],
                                 capture_output=True, text=True, check=True).stdout
            text = open(cert).read()
        gaps = [line.split() for line in text.split("lower-bounds")[1].splitlines()[1:-1]]
        forest = [int(g[0]) - 1 for g in gaps if g[1] == "forest"]
        if not forest:
            continue
        candidates += 1
        E = sorted(front(out), key=lambda point: point[1])  # (cost, makespan) by makespan
        args = [f"{checks}/bin/truth", ",".join(map(str, d)), ",".join(map(str, d)), ",".join(map(str, c)), str(t), str(p), "tight", "2"]
        try:
            truth = front(subprocess.run(args, capture_output=True, text=True, timeout=600, check=True).stdout)
        except (subprocess.TimeoutExpired, subprocess.CalledProcessError):
            continue
        tested += 1
        for i in forest:
            cost, nextMakespan = E[i][0], E[i + 1][1]
            better = [(tc, tm) for tc, tm in truth if tm < nextMakespan and tc < cost]
            if better:
                counterexamples += 1
                print(f"COUNTEREXAMPLE d={d} c={c} t={t} p={p}: E front {E}; with tight central flights {truth}; "
                      f"in the gap below makespan {nextMakespan}: {better}", flush=True)
    print(f"{candidates} instances with a forest gap, {tested} checked against all plans with tight central flights, "
          f"{counterexamples} counterexamples")


if __name__ == "__main__":
    main()
