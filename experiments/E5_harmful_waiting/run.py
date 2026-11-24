"""E5, harmful waiting (Proposition 6.5, refuting Conjecture 6.5 "no harmful waiting").

The papers' non-symmetric argument, stated as Conjecture 6.5, takes the makespan of a role
configuration to be its largest load: no schedule ever has to wait. Proposition 6.5 refutes it with
d = (3, 19), dbar = (3, 11), c = (5, 1), t = 7, p = 4: some role configuration of cost 14 has every load
at most 73, yet no plan of makespan at most 73 costs less than 18.

* A, the instance of Proposition 6.5: the front with waiting ignored (`simple_plans ... 0 nowait`:
  every simple plan with s landings, makespan = largest load) against the exact fronts (`config_front`
  and `zenoOracle`, which simulate waiting) and `zeno`'s.
* B, configuration level: `waiting_search` draws random balanced role configurations under (AΔ-path),
  with a plane picking up twice and one dropping off twice, and tries every order and matching.
* C, front level: on random instances, how often the front with waiting differs from the front that
  ignores it (Wilson 95% intervals).

Pass: on the instance of Proposition 6.5 the cheapest point with makespan <= 73 costs 14 when waiting
is ignored and 18 with exact waiting, and zeno, the oracle and config_front agree on the exact front.
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

NAME, CLAIM, SEED = "E5_harmful_waiting", "exp-e5-harmful-waiting", 0
PROP65 = C.Instance((3, 19), (5, 1), 7, 4, (3, 11))
PAPER_FRONT = [(10, 90), (14, 74), (18, 68), (22, 66), (26, 52), (34, 42), (38, 36), (42, 30), (50, 18)]
SEARCHES = [  # (label, trials per seed, maxPlanes, maxLinks, maxDuration, tight)
    ("random crossings, p<=4, <=4 links, d<=12", 200_000, 4, 4, 12, 0),
    ("one shortest crossing per plane, p<=4, <=5 links, d<=20", 200_000, 4, 5, 20, 1),
    ("one shortest crossing per plane, p<=5, <=6 links, d<=30", 100_000, 5, 6, 30, 1),
]
SEEDS = range(1, 9)
N_FRONT = 300


def lists(inst):
    j = ",".join
    return [j(map(str, inst.d)), j(map(str, inst.db)), j(map(str, inst.c)), str(inst.t), str(inst.p)]


def simple(inst, *extra, timeout=600):
    out = subprocess.run([str(C.check_program("simple_plans")), *lists(inst), *extra], capture_output=True,
                         text=True, timeout=timeout, check=True).stdout
    return C.parse_front(out)


def search(job):
    label, trials, planes, links, dmax, tight, seed = job
    out = subprocess.run([str(C.check_program("waiting_search")), str(trials), str(seed), str(planes), str(links),
                          str(dmax), str(tight)], capture_output=True, text=True, check=True).stdout
    m = re.search(r"(\d+) tested; (\d+) with harmful waiting", out)
    return label, int(m.group(1)), int(m.group(2))


def front_job(job):
    family, inst = job
    try:
        with_wait = simple(inst, "0")
        without = simple(inst, "0", "nowait")
    except (subprocess.TimeoutExpired, subprocess.CalledProcessError):
        return family, inst, None
    return family, inst, with_wait != without


def cheapest_within(front, makespan):
    return min((c for c, m in front if m <= makespan), default=None)


def main() -> int:
    rng = random.Random(SEED)

    # A. the instance of Proposition 6.5
    nowait = simple(PROP65, "0", "nowait")
    exact_simple = simple(PROP65, "0")
    config = C.parse_front(subprocess.run([str(C.check_program("config_front")), *lists(PROP65)], capture_output=True,
                                          text=True, check=True).stdout)
    with tempfile.TemporaryDirectory() as tmp:
        oracle = C.oracle_front(PROP65, Path(tmp))
        z = C.run_zeno(PROP65, Path(tmp))
    zeno_exact = "front is exact" in z.stderr
    lb73, true73 = cheapest_within(nowait, 73), cheapest_within(oracle, 73)
    part_a = lb73 == 14 and true73 == 18 and oracle == config == z.front == PAPER_FRONT and zeno_exact

    # B. configuration level
    found = Counter()
    tested = Counter()
    for label, t, h in C.pmap(search, [(*s, seed) for s in SEARCHES for seed in SEEDS]):
        tested[label] += t
        found[label] += h

    # C. front level
    jobs = []
    for k in range(N_FRONT):
        family = "uniform" if k % 2 == 0 else "waiting"
        p = rng.randint(1, 4)
        t = rng.randint(p + 1, min(7, p + 3))
        n = rng.randint(2 if family == "waiting" else 1, 3)
        while 2 * t - p > (8 if n == 3 else 10):
            t -= 1
        t = max(t, p)
        if family == "waiting":
            d = [rng.randint(1, 3)] + [rng.randint(10, 20) for _ in range(n - 1)]
            db = [rng.randint(1, 3)] + [rng.randint(1, 10) for _ in range(n - 1)]
            c = [rng.randint(3, 6)] + [rng.randint(0, 2) for _ in range(n - 1)]
            inst = C.Instance(tuple(d), tuple(c), t, p, tuple(db)).canonical()
        else:
            inst = C.random_instance(rng, n, t, p, dmax=20, cmax=6, symmetric=False)
        jobs.append((family, inst))
    changed = Counter()
    compared = Counter()
    examples = []
    for family, inst, diff in C.pmap(front_job, jobs):
        if diff is None:
            continue
        compared[family] += 1
        if diff:
            changed[family] += 1
            if len(examples) < 8:
                examples.append({"family": family, **inst.as_dict()})
    share = {f: (changed[f], compared[f], C.wilson(changed[f], compared[f])) for f in ("uniform", "waiting")}

    passed = part_a

    fig, axes = C.new_axes(figsize=(10.2, 4.0), ncols=2, gridspec_kw={"width_ratios": [1.25, 1]})
    ax = axes[0]
    for front, label, color, style in ((nowait, "waiting ignored (largest load)", C.PALETTE[1], "--"),
                                       (oracle, "exact waiting (oracle, zeno)", C.PALETTE[0], "-")):
        pts = sorted(front, key=lambda pt: pt[1])
        ax.step([m for _, m in pts], [c for c, _ in pts], where="post", color=color, linestyle=style, linewidth=1.6)
        ax.scatter([m for _, m in pts], [c for c, _ in pts], color=color, s=22, zorder=3, label=label)
    for pt in sorted(set(nowait) - set(oracle)):
        ax.annotate(f"({pt[0]}, {pt[1]})", (pt[1], pt[0]), textcoords="offset points", xytext=(-46, -12),
                    fontsize=8.5, color=C.PALETTE[1])
    ax.annotate("(14, 74)", (74, 14), textcoords="offset points", xytext=(6, -12), fontsize=8.5, color=C.PALETTE[0])
    ax.axvline(73, color=C.MUTED, linewidth=0.8, linestyle=":")
    ax.text(73.5, 33, "makespan 73", color=C.MUTED, fontsize=8.5)
    ax.set_xlabel("makespan")
    ax.set_ylabel("cost")
    ax.set_title("Prop 6.5: d=(3,19), dbar=(3,11), c=(5,1), t=7, p=4")
    ax.legend(loc="upper right")
    C.verdict_badge(ax, part_a, f"cheapest within 73: {lb73} ignoring waiting, {true73} exact", loc=(0.01, 0.02),
                    ha="left")
    ax = axes[1]
    fams = ["uniform", "waiting"]
    vals = [share[f][0] / max(1, share[f][1]) for f in fams]
    lo = [vals[i] - share[f][2][0] for i, f in enumerate(fams)]
    hi = [share[f][2][1] - vals[i] for i, f in enumerate(fams)]
    ax.bar(fams, vals, color=[C.PALETTE[0], C.PALETTE[1]], width=0.5, yerr=[lo, hi], capsize=4,
           error_kw={"ecolor": C.INK2, "elinewidth": 1})
    for i, f in enumerate(fams):
        ax.text(i, share[f][2][1] + 0.01, f"{share[f][0]} / {share[f][1]}", ha="center", va="bottom", fontsize=8.5,
                color=C.INK2)
    ax.set_ylabel("share of instances where waiting changes the front")
    ax.set_title("How often waiting matters (95% Wilson)")
    ax.grid(axis="x", visible=False)
    ax.set_ylim(0, max(0.2, max(share[f][2][1] for f in fams) * 1.3))
    figures = C.save_figure(fig, NAME, "harmful_waiting")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="on the instance of Proposition 6.5 the cheapest point with makespan <= 73 costs 14 when waiting "
                  "is ignored and 18 with exact waiting, and zeno, zenoOracle and config_front all give the "
                  "front stated in the note",
        metrics={
            "prop65_front_ignoring_waiting": nowait, "prop65_front_exact": oracle,
            "prop65_simple_plans_exact_equals_oracle": exact_simple == oracle,
            "prop65_zeno_closed_bracket": zeno_exact,
            "prop65_cheapest_within_73_ignoring_waiting": lb73, "prop65_cheapest_within_73_exact": true73,
            "points_only_without_waiting": sorted(set(nowait) - set(oracle)),
            "configuration_search": {lab: {"tested": tested[lab], "harmful": found[lab]} for lab, *_ in SEARCHES},
            "front_level": {f: {"changed": share[f][0], "compared": share[f][1],
                                "wilson95": [round(x, 4) for x in share[f][2]]} for f in fams},
            "front_level_examples": examples,
        },
        sizes={"configuration_search": {lab: f"{tr:,} trials x {len(SEEDS)} seeds" for lab, tr, *_ in SEARCHES},
               "front_level": f"{N_FRONT} instances, half uniform (d, dbar in [1,20]), half shaped like Prop 6.5; "
                              "n<=3, p<=4, t<=7, s<=10"},
        tests=["prop-6-5"], refutes=["paper-no-harmful-waiting"],
        hypothesis="Conjecture 6.5 (no harmful waiting) would make the front the Pareto set of (cost, largest "
                   "load) over role configurations; Proposition 6.5 says it is not.",
        explanation=f"Ignoring waiting gives {sorted(set(nowait) - set(oracle))} on the Prop 6.5 instance, which no "
                    f"plan reaches: the cheapest plan within makespan 73 costs {true73}, not {lb73}. Harmful waiting "
                    "is rare at the configuration level ("
                    + ", ".join(f"{found[lab]} of {tested[lab]:,}" for lab, *_ in SEARCHES)
                    + f") but changes the front of {share['waiting'][0]} of {share['waiting'][1]} instances shaped "
                      f"like Prop 6.5 and {share['uniform'][0]} of {share['uniform'][1]} uniform ones.",
        figures=figures, binaries=[C.ZENO, C.ORACLE, C.check_program("simple_plans"), C.check_program("config_front"),
                                   C.check_program("waiting_search")],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
