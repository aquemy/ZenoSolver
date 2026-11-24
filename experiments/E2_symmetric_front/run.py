"""E2, the symmetric front (Theorem 4.7 and Corollary 4.8): no plan beats the admissible-partition front.

Under (S) and (A1), Theorem 4.7 says every feasible plan is weakly dominated by an admissible
partition, and Corollary 4.8 that the front is the Pareto set of (E(T), 2T). `zeno` computes that
set. Two exhaustive references, written independently of the solver, compute the true front:

* `truth` (doc/theory/checks/truth.cpp): breadth-first search over ALL plans of the planning
  problem, with no landing count, pattern or route shape assumed; central flights either absent
  (`none`) or present but useless (`a1`, so (A1) holds);
* `zenoOracle` (tests/oracle): every role-configuration schedule with its exact waiting, at sizes
  `truth` cannot reach.

Pass: `zeno`'s front equals the reference front on every instance the reference finishes.
"""

from __future__ import annotations

import random
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

NAME, CLAIM, SEED = "E2_symmetric_front", "exp-e2-symmetric-front", 0
N_TRUTH, N_ORACLE = 1000, 1000
TRUTH_TIMEOUT, ORACLE_TIMEOUT = 300, 120


def truth_jobs(rng):
    jobs = []
    for _ in range(N_TRUTH):
        p = rng.randint(1, 3)
        t = rng.randint(p, min(5, p + 3))
        n = rng.randint(1, 3)
        inst = C.random_instance(rng, n, t, p, dmax=6, cmax=9)
        jobs += [("truth-" + central, inst) for central in ("none", "a1")]
    return jobs


def oracle_jobs(rng):
    jobs = []
    for _ in range(N_ORACLE):
        p = rng.randint(1, 4)
        n = rng.randint(1, 5)
        # the oracle needs t > p and is exponential: t = 6 only for n <= 3
        t = rng.randint(p + 1, max(p + 1, 6 if n <= 3 else 5))
        jobs.append(("oracle", C.random_instance(rng, n, t, p, dmax=20, cmax=30, anti=rng.random() < 0.5)))
    return jobs


def run(job):
    kind, inst = job
    with tempfile.TemporaryDirectory() as tmp:
        mine = C.run_zeno(inst, Path(tmp)).front
        if kind == "oracle":
            try:
                ref = C.oracle_front(inst, Path(tmp), timeout=ORACLE_TIMEOUT)
            except subprocess.TimeoutExpired:
                ref = None
            except subprocess.CalledProcessError:
                ref = "error"
        else:
            ref = C.truth_front(inst, central=kind.split("-")[1], timeout=TRUTH_TIMEOUT)
    return kind, inst, mine, ref


def main() -> int:
    rng = random.Random(SEED)
    jobs = truth_jobs(rng) + oracle_jobs(rng)
    rows = C.pmap(run, jobs)

    kinds = ["truth-none", "truth-a1", "oracle"]
    stats = {k: Counter() for k in kinds}
    by_s = {k: Counter() for k in kinds}
    mismatches = []
    for kind, inst, mine, ref in rows:
        if ref == "error":
            stats[kind]["error"] += 1
            continue
        if ref is None:
            stats[kind]["timeout"] += 1
            continue
        stats[kind]["compared"] += 1
        stats[kind]["points"] += len(ref)
        by_s[kind][inst.s] += 1
        if mine != ref:
            stats[kind]["mismatch"] += 1
            mismatches.append({"reference": kind, "instance": inst.as_dict(), "zeno": mine, "reference_front": ref})
    total_mismatch = sum(s["mismatch"] for s in stats.values())
    passed = total_mismatch == 0 and all(stats[k]["compared"] > 0 and stats[k]["error"] == 0 for k in kinds)

    fig, ax = C.new_axes(figsize=(7.6, 4.0))
    smax = max(max(c) for c in by_s.values() if c)
    xs = list(range(1, smax + 1))
    width = 0.27
    labels = {"truth-none": "all plans, no central flights", "truth-a1": "all plans, useless central flights (A1)",
              "oracle": "all role-configuration schedules (oracle)"}
    for k, kind in enumerate(kinds):
        ax.bar([x + (k - 1) * width for x in xs], [by_s[kind][x] for x in xs], width=width,
               color=C.PALETTE[k], label=f"{labels[kind]}: {stats[kind]['compared'] - stats[kind]['mismatch']}"
                                         f" / {stats[kind]['compared']} equal")
    ax.set_xlabel("landings s = 2t - p")
    ax.set_ylabel("instances whose fronts were compared")
    ax.set_title("zeno's front equals the exhaustive front")
    ax.set_xticks(xs)
    ax.grid(axis="x", visible=False)
    ax.legend(loc="upper right")
    ax.set_ylim(0, max(max(c.values()) for c in by_s.values()) * 1.45)
    C.verdict_badge(ax, passed, f"{total_mismatch} mismatches", loc=(0.01, 0.9), ha="left")
    figures = C.save_figure(fig, NAME, "fronts_vs_exhaustive")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="zeno's front equals the front of the exhaustive search over all plans (central flights none "
                  "or useless) and of the role-configuration oracle on every instance they finish",
        metrics={
            **{f"{k}_{m}": stats[k][m] for k in kinds for m in ("compared", "mismatch", "timeout", "error", "points")},
            "mismatches": mismatches[:20],
        },
        sizes={"truth": f"{N_TRUTH} instances x 2 central regimes; n<=3, p<=3, t<=min(5,p+3), d in [1,6], c in [0,9]",
               "oracle": f"{N_ORACLE} instances; n<=5, p<=4, p<t<=6 (t<=5 when n>=4, the oracle needs t>p), "
                         "d in [1,20], c in [0,30], half anti-correlated",
               "timeouts_s": {"truth": TRUTH_TIMEOUT, "oracle": ORACLE_TIMEOUT}},
        tests=["thm-4-7", "cor-4-8"],
        hypothesis="Under (S) and (A1) every plan is weakly dominated by an admissible partition (Thm 4.7), so "
                   "the front is the Pareto set of (E(T), 2T) (Cor 4.8), the set zeno computes.",
        explanation=f"{stats['truth-none']['compared'] + stats['truth-a1']['compared']} comparisons against all "
                    f"plans and {stats['oracle']['compared']} against the oracle; {total_mismatch} differ. "
                    "Agreement with the all-plans search is the direct test of the converse: no plan with "
                    "extra landings, hand-offs or central flights is better.",
        figures=figures, binaries=[C.ZENO, C.ORACLE, C.check_program("truth")],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
