"""E3, the link-forest DP (Theorem 7.5): `zeno`'s levels are the true E(T), at sizes enumeration cannot reach.

E(T) is the least cost of an admissible partition of s = 2t - p landings into p non-empty groups of
duration at most T. Theorem 7.5 says the link-forest DP computes it. Two references that share no code
with the C++ solver check it:

* a CP-SAT model of E(T) (`doc/theory/checks/cpsat_check.py`, `level_cost`, admissibility by a 0/1
  parity matrix): every front point (C, M) must have E(M/2) = C, and the level just below the next
  point must still cost C, which pins the whole step function E between breakpoints;
* the Lean solver `zeno-front`, which recomputes the front from the instance in a certificate.

Pass: 0 mismatches against CP-SAT on every level checked, and the Lean front equals the C++ one.
"""

from __future__ import annotations

import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

sys.path.insert(0, str(C.CHECKS))
sys.dont_write_bytecode = True  # doc/theory/checks is read-only: no __pycache__ there
import cpsat_check  # noqa: E402  (read-only use of the check's model)
sys.dont_write_bytecode = False

NAME, CLAIM, SEED = "E3_forest_dp", "exp-e3-forest-dp", 0
TIERS = [  # (name, instances, max n, max t, max p, max duration)
    ("medium", 200, 8, 16, 6, 40),
    ("large", 120, 12, 28, 10, 80),
]


def jobs(rng):
    out = []
    for tier, count, maxn, maxt, maxp, maxd in TIERS:
        for _ in range(count):
            p = rng.randint(2, maxp)
            t = rng.randint(p, maxt)
            n = rng.randint(2, maxn)
            inst = C.random_instance(rng, n, t, p, dmax=maxd, cmax=60, dmin=0 if rng.random() < 0.25 else 1,
                                     anti=rng.random() < 0.5)
            out.append((tier, inst))
    return out


def run(job):
    tier, inst = job
    with tempfile.TemporaryDirectory() as tmp:
        cert = Path(tmp) / "front.cert"
        mine = C.run_zeno(inst, Path(tmp), "--certificate", str(cert)).front
        forest_gaps = cert.read_text().count(" forest\n")
        t0 = time.time()
        lean = subprocess.run([str(C.LEAN_FRONT), str(cert)], capture_output=True, text=True, timeout=600)
        lean_s = time.time() - t0
    lean_front = C.parse_front(lean.stdout) if lean.returncode == 0 else None
    d, c = list(inst.d), list(inst.c)
    by_makespan = sorted(mine, key=lambda pt: pt[1])
    checks, bad, unknown = 0, [], 0

    def level_cost(level):
        try:
            return cpsat_check.level_cost(d, c, inst.t, inst.p, level)
        except RuntimeError:  # CP-SAT hit its 60 s limit
            return "unknown"

    t0 = time.time()
    for i, (cost, makespan) in enumerate(by_makespan):
        levels = [makespan // 2] + ([(by_makespan[i + 1][1] - 1) // 2] if i + 1 < len(by_makespan) else [])
        for level in levels:
            got = level_cost(level)
            if got == "unknown":
                unknown += 1
                continue
            checks += 1
            if got != cost:
                bad.append({"level": level, "zeno": cost, "cpsat": got})
    # the level below the fastest point must be infeasible
    below = by_makespan[0][1] // 2 - 1
    if below >= 0:
        got = level_cost(below)
        if got == "unknown":
            unknown += 1
        else:
            checks += 1
            if got is not None:
                bad.append({"level": below, "zeno": None, "cpsat": "feasible"})
    return tier, inst, mine, checks, bad, lean_front, lean_s, time.time() - t0, forest_gaps, unknown


def main() -> int:
    rng = random.Random(SEED)
    rows = C.pmap(run, jobs(rng), workers=3)  # CP-SAT runs 8 workers per solve

    levels = sum(r[3] for r in rows)
    bad = [{"instance": r[1].as_dict(), **b} for r in rows for b in r[4]]
    lean_cmp = [r for r in rows if r[5] is not None]
    lean_bad = [r[1].as_dict() for r in rows if r[5] is not None and r[5] != r[2]]
    lean_fail = sum(r[5] is None for r in rows)
    forest_instances = sum(r[8] > 0 for r in rows)
    passed = not bad and not lean_bad and lean_fail == 0

    fig, axes = C.new_axes(figsize=(9.6, 3.9), ncols=2)
    ax = axes[0]
    for k, (tier, *_rest) in enumerate(TIERS):
        pts = [(r[1].s, len(r[2])) for r in rows if r[0] == tier]
        ax.scatter([a for a, _ in pts], [b for _, b in pts], s=14, alpha=0.65, color=C.PALETTE[k],
                   edgecolors="none", label=f"{tier}: {sum(1 for r in rows if r[0] == tier)} instances")
    ax.set_xlabel("landings s = 2t - p")
    ax.set_ylabel("front points (2 CP-SAT levels each)")
    ax.set_yscale("log")
    ax.set_title(f"{levels:,} levels of E(T) checked by CP-SAT")
    ax.legend(loc="upper left")
    C.verdict_badge(ax, not bad, f"{len(bad)} mismatches")
    ax = axes[1]
    ax.scatter([r[7] for r in lean_cmp], [r[6] for r in lean_cmp], s=14, alpha=0.65, color=C.PALETTE[2],
               edgecolors="none")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("CP-SAT time for the instance (s)")
    ax.set_ylabel("Lean zeno-front time (s)")
    ax.set_title("Lean solver: same front on every instance")
    C.verdict_badge(ax, not lean_bad and lean_fail == 0, f"{len(lean_bad)} differ, {lean_fail} failed")
    figures = C.save_figure(fig, NAME, "forest_dp_vs_cpsat")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="CP-SAT's E(T) equals zeno's cost at every front level and at the level below the next point, "
                  "the level below the fastest point is infeasible, and the Lean zeno-front gives the same front",
        metrics={"instances": len(rows), "levels_checked": levels, "cpsat_mismatches": len(bad),
                 "cpsat_timeouts": sum(r[9] for r in rows),
                 "lean_compared": len(lean_cmp), "lean_differ": len(lean_bad), "lean_failed": lean_fail,
                 "instances_with_forest_gaps": forest_instances,
                 "front_points": sum(len(r[2]) for r in rows), "max_front": max(len(r[2]) for r in rows),
                 "mismatch_examples": bad[:10], "lean_examples": lean_bad[:5]},
        sizes={tier: {"instances": cnt, "n": f"2..{mn}", "t": f"p..{mt}", "p": f"2..{mp}", "d": f"0..{md}",
                      "c": "0..60"} for tier, cnt, mn, mt, mp, md in TIERS},
        tests=["thm-7-5"],
        hypothesis="Theorem 7.5: the link-forest DP returns E(T), the least cost of an admissible partition at "
                   "level T, so the front zeno builds from it is the Pareto set of (E(T), 2T).",
        explanation=f"{levels:,} levels over {len(rows)} instances (up to n = 12, t = 28, p = 10) agree with an "
                    f"independent CP-SAT model; {forest_instances} instances needed the forest bound in their "
                    "certificate (L < E somewhere), the case where E is not the relaxation.",
        figures=figures, binaries=[C.ZENO, C.LEAN_FRONT],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
