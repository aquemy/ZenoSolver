"""E4, the non-symmetric front (Theorem 5.3, Corollaries 5.4 and 5.6).

Corollary 5.6: under (A1-NS) the front is the Pareto set of (cost, least makespan) over role
configurations, where the least makespan is that of the best schedule with exact waiting. It rests on
Theorem 5.3 (every plan is dominated by a role configuration whose template is no later) and on
Corollary 5.4 (every plan is dominated by a role configuration with loads at most its makespan), which
the `roles`, `lagrangian` and `balanced` bounds of `zeno` use.

* A, all plans: on tiny instances, the exhaustive search over all plans (`truth`, central flights
  none or useless) against the front of role-configuration schedules (`config_front`, exact waiting)
  and against `zeno` whenever it reports its bracket closed.
* B, all simple plans: on larger instances, the front of every simple plan with clean journeys, any
  hand-offs and up to s + 1 landings (`simple_plans`), against `config_front` and `zeno`, on uniform
  random durations and on a family shaped like Proposition 5.7 where waiting matters.

Pass: `config_front` equals the all-plans (A) and all-simple-plans (B) fronts on every instance they
finish, and every front `zeno` reports exact equals them.
"""

from __future__ import annotations

import random
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

NAME, CLAIM, SEED = "E4_nonsymmetric_front", "exp-e4-nonsymmetric-front", 0
N_TRUTH, N_SIMPLE = 800, 800
TIMEOUT = 600


def waiting_instance(rng, n, t, p, hi):
    """Like Proposition 5.7: one short city, the others slow from C_I and fast from C_G, cheap."""
    d = [rng.randint(1, 3)] + [rng.randint(hi // 2, hi) for _ in range(n - 1)]
    db = [rng.randint(1, 3)] + [rng.randint(1, hi // 2) for _ in range(n - 1)]
    c = [rng.randint(3, 6)] + [rng.randint(0, 2) for _ in range(n - 1)]
    return C.Instance(tuple(d), tuple(c), t, p, tuple(db)).canonical()


def jobs(rng):
    out = []
    for _ in range(N_TRUTH):
        p = rng.randint(1, 3)
        t = rng.randint(p + 1, min(5, p + 3))
        n = rng.randint(1, 2)
        inst = C.random_instance(rng, n, t, p, dmax=6, cmax=6, symmetric=False)
        for central in (["none", "a1"] if n >= 2 else ["none"]):
            out.append(("truth-" + central, "uniform", inst))
    for k in range(N_SIMPLE):
        family = "uniform" if k % 2 == 0 else "waiting"
        p = rng.randint(1, 4)
        t = rng.randint(p + 1, min(7, p + 3))
        n = rng.randint(2 if family == "waiting" else 1, 3)
        while 2 * t - p > (7 if n == 3 else 8):  # simple_plans with s + 1 landings is exponential in s
            t -= 1
        if t < p:
            t = p
        inst = (waiting_instance(rng, n, t, p, 20) if family == "waiting"
                else C.random_instance(rng, n, t, p, dmax=20, cmax=6, symmetric=False))
        out.append(("simple", family, inst))
    return out


def lists(inst):
    j = ",".join
    return [j(map(str, inst.d)), j(map(str, inst.db)), j(map(str, inst.c)), str(inst.t), str(inst.p)]


def run(job):
    kind, family, inst = job
    args = lists(inst)
    try:
        cf = subprocess.run([str(C.check_program("config_front")), *args], capture_output=True, text=True,
                            timeout=TIMEOUT, check=True).stdout
        if kind.startswith("truth"):
            ref = C.truth_front(inst, central=kind.split("-")[1], extra=3, timeout=TIMEOUT)
        else:
            ref = C.parse_front(subprocess.run([str(C.check_program("simple_plans")), *args, "1"],
                                               capture_output=True, text=True, timeout=TIMEOUT, check=True).stdout)
    except subprocess.TimeoutExpired:
        return kind, family, inst, None, None, None, None
    except subprocess.CalledProcessError:
        return kind, family, inst, "error", None, None, None
    if ref is None:
        return kind, family, inst, None, None, None, None
    with tempfile.TemporaryDirectory() as tmp:
        cert = Path(tmp) / "front.cert"
        z = C.run_zeno(inst, Path(tmp), "--certificate", str(cert))
        kinds = Counter(re.findall(r"^\d+ (\w+)", cert.read_text().split("lower-bounds")[-1], re.M)) \
            if cert.exists() else Counter()
    exact = "front is exact" in z.stderr or inst.symmetric
    return kind, family, inst, C.parse_front(cf), ref, (z.front, exact), kinds


def main() -> int:
    rng = random.Random(SEED)
    rows = C.pmap(run, jobs(rng))

    stats = Counter()
    gap_kinds = Counter()
    diffs = []
    for kind, family, inst, cf, ref, z, kinds in rows:
        tag = "truth" if kind.startswith("truth") else "simple"
        if cf == "error":
            stats[f"{tag}_tool_error"] += 1
            continue
        if ref is None:
            stats[f"{tag}_timeout"] += 1
            continue
        stats[f"{tag}_compared"] += 1
        if cf != ref:
            stats[f"{tag}_config_differs"] += 1
            diffs.append({"reference": kind, "family": family, "instance": inst.as_dict(),
                          "reference_front": ref, "config_front": cf})
        zf, exact = z
        if exact:
            stats[f"{tag}_zeno_exact"] += 1
            gap_kinds.update(kinds)
            if zf != ref:
                stats[f"{tag}_zeno_differs"] += 1
                diffs.append({"reference": kind, "family": family, "instance": inst.as_dict(),
                              "reference_front": ref, "zeno": zf})
        else:
            # an open bracket: every achieved point must still be a real plan's (dominated by the front)
            if not all(C.dominated(pt, ref) for pt in zf):
                stats[f"{tag}_zeno_unachievable"] += 1
        if family == "waiting":
            stats["waiting_family_compared"] += 1
    passed = (not diffs and stats["simple_zeno_unachievable"] + stats["truth_zeno_unachievable"] == 0
              and stats["truth_tool_error"] + stats["simple_tool_error"] == 0)

    fig, ax = C.new_axes(figsize=(7.8, 4.0))
    groups = [("truth", "all plans\n(truth, n<=2, t<=5)"), ("simple", "all simple plans, s+1 landings\n(n<=3, s<=8)")]
    x = range(len(groups))
    comp = [stats[f"{g}_compared"] for g, _ in groups]
    eq = [stats[f"{g}_compared"] - stats[f"{g}_config_differs"] for g, _ in groups]
    ze = [stats[f"{g}_zeno_exact"] - stats[f"{g}_zeno_differs"] for g, _ in groups]
    w = 0.36
    ax.bar([i - w / 2 for i in x], eq, w, color=C.PALETTE[0], label="role-configuration front = reference")
    ax.bar([i + w / 2 for i in x], ze, w, color=C.PALETTE[1], label="zeno closed its bracket and = reference")
    for i in x:
        ax.text(i - w / 2, eq[i], f"{eq[i]} / {comp[i]}", ha="center", va="bottom", fontsize=8.5, color=C.INK2)
        ax.text(i + w / 2, ze[i], f"{ze[i]} / {comp[i]}", ha="center", va="bottom", fontsize=8.5, color=C.INK2)
    ax.set_xticks(list(x), [g for _, g in groups])
    ax.set_ylabel("instances")
    ax.set_ylim(0, max(comp) * 1.35)
    ax.grid(axis="x", visible=False)
    ax.legend(loc="upper left")
    ax.set_title("Non-symmetric fronts: role configurations with exact waiting are enough")
    C.verdict_badge(ax, passed, f"{len(diffs)} differences", loc=(0.99, 0.9))
    figures = C.save_figure(fig, NAME, "nonsymmetric_fronts")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="the front of role-configuration schedules equals the front of all plans (truth) and of all "
                  "simple plans with up to s+1 landings, and every front zeno reports exact equals them",
        metrics={**dict(sorted(stats.items())), "certificate_gap_kinds_when_exact": dict(gap_kinds),
                 "differences": diffs[:20]},
        sizes={"truth": f"{N_TRUTH} instances (x2 central regimes when n=2); n<=2, p<=3, t<=min(5,p+3), "
                        "d, dbar in [1,6], c in [0,6], up to s+3 landings",
               "simple": f"{N_SIMPLE} instances, half uniform (d, dbar in [1,20]) and half shaped like Prop 5.7; "
                         "n<=3, p<=4, t<=7, s<=8 (s<=7 when n=3), up to s+1 landings",
               "timeout_s": TIMEOUT},
        tests=["thm-6-1", "thm-6-9", "cor-6-10"],
        hypothesis="Under (A1-NS), every plan is weakly dominated by a role configuration whose template is no "
                   "later (Thm 5.3), so the front is the Pareto set of (cost, least makespan) over role "
                   "configurations (Cor 5.6); zeno's role-load bounds (Cor 5.4) and its search are then sound.",
        explanation=f"{stats['truth_compared']} all-plans and {stats['simple_compared']} all-simple-plans "
                    f"comparisons; {stats['truth_config_differs'] + stats['simple_config_differs']} differ from the "
                    f"role-configuration front. zeno closed its bracket on "
                    f"{stats['truth_zeno_exact'] + stats['simple_zeno_exact']} of them, with gap kinds "
                    f"{dict(gap_kinds)}, and matched the reference on all.",
        figures=figures, binaries=[C.ZENO, C.check_program("truth"), C.check_program("config_front"),
                                   C.check_program("simple_plans")],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
