"""E1, achievability (Theorem 4.1): every front point `zeno` reports is reached by a real plan.

For every point of the front, `zeno --plans` prints a plan; an independent simulator (`common.simulate`,
which shares no code with the solver) replays it against the plan semantics of
doc/certificate-format.md and recomputes its cost and makespan. Theorem 4.1 says an admissible
partition yields a plan whose makespan is its largest load, so under (S) every point must be reached
exactly. Non-symmetric instances are replayed too (their achieved points come from template schedules,
Lemma 5.5), and reported separately.

Pass: every plan is feasible and has exactly the cost and makespan of its front point.
"""

from __future__ import annotations

import random
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

NAME, CLAIM, SEED = "E1_achievability", "exp-e1-achievability", 0
N_RANDOM, N_GENERATOR, N_NONSYM = 400, 150, 200


def instances(rng: random.Random) -> list[tuple[str, C.Instance]]:
    out = []
    for _ in range(N_RANDOM):
        p = rng.randint(1, 6)
        t = rng.randint(p, p + 8)
        n = rng.randint(1, 8)
        out.append(("random", C.random_instance(rng, n, t, p, anti=rng.random() < 0.5)))
    with tempfile.TemporaryDirectory() as tmp:
        while sum(f == "generator" for f, _ in out) < N_GENERATOR:
            p = rng.randint(1, 6)
            t = rng.randint(p, p + 10)
            n = rng.randint(2, 12)
            args = ["-n", str(n), "-t", str(t), "-p", str(p), "-C", str(rng.randint(1, 5)),
                    "-D", str(rng.randint(1, 5)), "-r", str(rng.choice([1, 10, 100]))]
            inst = C.generated_instance(args, Path(tmp)).canonical()
            if min(inst.d) >= 1:  # the simulator orders journeys by time: positive durations only
                out.append(("generator", inst))
    for _ in range(N_NONSYM):
        p = rng.randint(1, 4)
        t = rng.randint(p, p + 4)
        n = rng.randint(1, 4)
        out.append(("non-symmetric", C.random_instance(rng, n, t, p, dmax=20, symmetric=False)))
    return out


def check(job):
    family, inst = job
    with tempfile.TemporaryDirectory() as tmp:
        run = C.run_zeno(inst, Path(tmp), plans=True, timeout=300)
    bad = []
    for point in run.front:
        routes = run.plans.get(point)
        if routes is None:
            bad.append((point, "no plan printed"))
            continue
        try:
            got = C.simulate(inst, routes)
        except C.PlanError as err:
            bad.append((point, f"infeasible: {err}"))
            continue
        if got != point:
            bad.append((point, f"simulated {got}"))
    return family, inst, len(run.front), bad


def main() -> int:
    rng = random.Random(SEED)
    jobs = instances(rng)
    rows = C.pmap(check, jobs)

    fams = ["random", "generator", "non-symmetric"]
    per = {f: {"instances": 0, "points": 0, "failures": 0} for f in fams}
    failures = []
    for family, inst, npts, bad in rows:
        per[family]["instances"] += 1
        per[family]["points"] += npts
        per[family]["failures"] += len(bad)
        failures += [{"instance": inst.as_dict(), "point": list(pt), "why": why} for pt, why in bad]
    sym_points = per["random"]["points"] + per["generator"]["points"]
    sym_fail = per["random"]["failures"] + per["generator"]["failures"]
    passed = sym_fail == 0 and per["non-symmetric"]["failures"] == 0

    fig, axes = C.new_axes(figsize=(9.6, 3.8), ncols=2)
    ax = axes[0]
    labels = [f"{f}\n{per[f]['instances']} instances" for f in fams]
    ax.bar(labels, [per[f]["points"] for f in fams], color=C.PALETTE[0], width=0.55)
    for i, f in enumerate(fams):
        ax.text(i, per[f]["points"], f"{per[f]['points'] - per[f]['failures']:,} / {per[f]['points']:,}",
                ha="center", va="bottom", fontsize=8.5, color=C.INK2)
    ax.set_ylabel("front points replayed by the simulator")
    ax.set_title("Every front point has a plan that reaches it")
    ax.grid(axis="x", visible=False)
    ax.set_ylim(0, max(per[f]["points"] for f in fams) * 1.25)
    C.verdict_badge(ax, passed, f"{sum(per[f]['failures'] for f in fams)} mismatches", loc=(0.99, 0.9))
    ax = axes[1]
    for k, f in enumerate(fams):
        xs = [2 * inst.t - inst.p for fam, inst, _, _ in rows if fam == f]
        ys = [npts for fam, _, npts, _ in rows if fam == f]
        ax.scatter(xs, ys, s=12, alpha=0.6, color=C.PALETTE[k], label=f, edgecolors="none")
    ax.set_xlabel("landings s = 2t - p")
    ax.set_ylabel("front size (points replayed)")
    ax.set_yscale("log")
    ax.set_title("Front sizes covered")
    ax.legend(loc="upper left")
    figures = C.save_figure(fig, NAME, "achievability")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="every plan printed by `zeno --plans` is feasible under the independent simulator and has "
                  "exactly the cost and makespan of its front point (0 mismatches)",
        metrics={
            "symmetric_points_replayed": sym_points,
            "symmetric_mismatches": sym_fail,
            "nonsymmetric_points_replayed": per["non-symmetric"]["points"],
            "nonsymmetric_mismatches": per["non-symmetric"]["failures"],
            "per_family": per,
            "failures": failures[:20],
        },
        sizes={"random": "n<=8, p<=6, t<=p+8, d in [1,30], c in [0,50]; half with anti-correlated costs",
               "generator": "n<=12, p<=6, t<=p+10, -C/-D in 1..5, -r in {1,10,100}, positive durations only",
               "non-symmetric": "n<=4, p<=4, t<=p+4, d, dbar in [1,20]",
               "instances": {f: per[f]["instances"] for f in fams}},
        tests=["thm-4-1"],
        hypothesis="Theorem 4.1: under (S), an admissible partition gives a plan of makespan equal to its "
                   "largest load, so every point of the front `zeno` computes is achieved by a real plan.",
        explanation=f"{sym_points:,} symmetric front points and {per['non-symmetric']['points']:,} "
                    f"non-symmetric ones were replayed; {sym_fail + per['non-symmetric']['failures']} "
                    "plans failed the simulator or missed their point.",
        figures=figures, binaries=[C.ZENO],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
