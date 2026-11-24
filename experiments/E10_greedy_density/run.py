"""E10, greedy exactness density: how often the papers' per-PPP greedy returns the exact front.

Both papers claim their per-PPP greedy (EvoCOP 2015, Algorithm 1) is optimal (`paper-greedy-optimal`,
refuted in §5 of the theory note). `greedy.cpp` reimplements it from the 2016 `zenoSolver` (commit
84ca92a), sharing no code with the exact solver. This experiment measures, as a function of n, t and p:

* the share of instances on which the greedy front equals the exact front (`zeno`), with Wilson 95%
  intervals;
* the share of exact front points the greedy front contains.

It samples random data files (uniform and anti-correlated costs) and the generator's families
(-C/-D in 1..5). The linear family (-C 3 -D 3, and data files d_i = r0 i, c_i = alpha - beta i) is
reported separately: Conjecture 10.2 says the greedy is exact on it (`conj-10-2`, open). A sample with
no miss on it is evidence for the conjecture, not a proof.

Validation first: on the 27 golden instances the reimplementation must differ from the golden front
exactly on `lpt-counterexample` and `n3t5p2-C1D4r10`, the two pairs on which the 2016 solver failed
(tests/golden/known-bugs.txt before its removal), and its pruning must not change any front.

Pass: the validation holds and no greedy point beats the exact front (every greedy point is reached by
a plan, so it must be weakly dominated by the front).
"""

from __future__ import annotations

import random
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

NAME, CLAIM, SEED = "E10_greedy_density", "exp-e10-greedy-density", 0
HERE = Path(__file__).resolve().parent
GREEDY = C.REPO / "build" / "experiments" / "bin" / "greedy"
GOLDEN_FAILS = {"lpt-counterexample", "n3t5p2-C1D4r10"}
NS, TS, PMAX = range(2, 9), range(2, 11), 6
PER_CELL = {"random": 3, "anti": 3, "generator": 3, "linear-generator": 1, "linear-affine": 2}
LINEAR = ("linear-generator", "linear-affine")
TIMEOUT = 300


def build_greedy() -> Path:
    src = HERE / "greedy.cpp"
    if not GREEDY.exists() or GREEDY.stat().st_mtime < src.stat().st_mtime:
        GREEDY.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["c++", "-std=c++17", "-O2", str(src), "-o", str(GREEDY)], check=True)
    return GREEDY


def greedy_front(inst: C.Instance, prune: bool = True, timeout: float = TIMEOUT):
    args = [str(GREEDY), ",".join(map(str, inst.d)), ",".join(map(str, inst.c)), str(inst.t), str(inst.p)]
    try:
        out = subprocess.run(args + ([] if prune else ["noprune"]), capture_output=True, text=True,
                             timeout=timeout, check=True).stdout
    except subprocess.TimeoutExpired:
        return None
    return C.parse_front(out)


def validate(rng) -> dict:
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        for line in (C.REPO / "tests" / "golden" / "instances.txt").read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            name, args = line.split("|")
            inst = C.generated_instance(args.replace("@DATA@", str(C.REPO / "tests/golden/data")).split(), Path(tmp))
            gold = C.parse_front((C.REPO / "tests" / "golden" / "fronts" / f"{name}.front").read_text())
            g = greedy_front(inst)
            rows.append((name, g == gold, g == greedy_front(inst, prune=False), sorted(set(gold) - set(g))))
    fails = {name for name, same, _, _ in rows if not same}
    prune_ok = all(p for _, _, p, _ in rows)
    # pruning on random instances too
    for _ in range(60):
        p = rng.randint(1, 4)
        inst = C.random_instance(rng, rng.randint(2, 5), rng.randint(p, p + 4), p, anti=rng.random() < 0.5)
        prune_ok &= greedy_front(inst) == greedy_front(inst, prune=False)
    return {"golden_instances": len(rows), "golden_differs_on": sorted(fails),
            "missed_points": {name: miss for name, same, _, miss in rows if not same},
            "expected_fails": sorted(GOLDEN_FAILS), "pruning_never_changes_front": prune_ok,
            "ok": fails == GOLDEN_FAILS and prune_ok}


def sample(rng) -> list[tuple[str, C.Instance]]:
    combos = [(cc, dd) for cc in range(1, 6) for dd in range(1, 6) if (cc, dd) != (3, 3)]
    out = []
    with tempfile.TemporaryDirectory() as tmp:
        for n in NS:
            for t in TS:
                for p in range(1, min(t, PMAX) + 1):
                    for _ in range(PER_CELL["random"]):
                        out.append(("random", C.random_instance(rng, n, t, p)))
                    for _ in range(PER_CELL["anti"]):
                        out.append(("anti", C.random_instance(rng, n, t, p, anti=True)))
                    base = ["-n", str(n), "-t", str(t), "-p", str(p)]
                    for cc, dd in rng.sample(combos, PER_CELL["generator"]):
                        r = rng.choice([1, 10, 100])
                        args = base + ["-C", str(cc), "-D", str(dd), "-r", str(r)]
                        out.append(("generator", C.generated_instance(args, Path(tmp)).canonical()))
                    for _ in range(PER_CELL["linear-generator"]):
                        args = base + ["-C", "3", "-D", "3", "-r", str(rng.choice([1, 10]))]
                        out.append(("linear-generator", C.generated_instance(args, Path(tmp)).canonical()))
                    for _ in range(PER_CELL["linear-affine"]):
                        r0, beta = rng.randint(1, 5), rng.randint(0, 5)
                        alpha = beta * n + rng.randint(0, 30)
                        out.append(("linear-affine", C.Instance(tuple(r0 * i for i in range(1, n + 1)),
                                                                tuple(alpha - beta * i for i in range(1, n + 1)), t, p)))
    return out


def run(job):
    family, inst = job
    g = greedy_front(inst)
    if g is None:
        return family, inst, None
    with tempfile.TemporaryDirectory() as tmp:
        f = C.run_zeno(inst, Path(tmp)).front
    right = len(set(g) & set(f))
    beats = [pt for pt in g if not C.dominated(pt, f)]
    return family, inst, {"exact": g == f, "right": right, "front": len(f), "beats": beats,
                          "missed": sorted(set(f) - set(g))[:5]}


def share(rows):
    k, n = sum(r["exact"] for r in rows), len(rows)
    return k, n, C.wilson(k, n)


def main() -> int:
    rng = random.Random(SEED)
    build_greedy()
    validation = validate(rng)
    if not validation["ok"]:
        print("greedy reimplementation failed its validation:", validation)

    rows = C.pmap(run, sample(rng))
    done = [(f, i, r) for f, i, r in rows if r is not None]
    timeouts = len(rows) - len(done)
    beats = [{"family": f, "instance": i.as_dict(), "points": r["beats"]} for f, i, r in done if r["beats"]]
    nonlin = [(f, i, r) for f, i, r in done if f not in LINEAR]
    lin = [(f, i, r) for f, i, r in done if f in LINEAR]

    def agg(items, key):
        cells = defaultdict(list)
        for f, i, r in items:
            cells[key(i)].append(r)
        return cells

    by_tp = agg(nonlin, lambda i: (i.t, i.p))
    by_links = agg(nonlin, lambda i: "p=1" if i.p == 1 else f"t-p={i.t - i.p}")  # t - p bounds the link count
    small = [r for key, v in by_links.items() if key == "p=1" or int(key[4:]) <= 2 for r in v]
    by_t_p = by_tp
    by_n = agg(nonlin, lambda i: i.n)
    by_fam = defaultdict(list)
    for f, i, r in done:
        by_fam[f].append(r)
    fam_stats = {f: {"exact": share(v)[0], "instances": share(v)[1], "wilson95": [round(x, 4) for x in share(v)[2]],
                     "points_right": sum(r["right"] for r in v), "front_points": sum(r["front"] for r in v)}
                 for f, v in sorted(by_fam.items())}
    lin_misses = [{"family": f, "instance": i.as_dict(), "missed": r["missed"]} for f, i, r in lin if not r["exact"]]
    k_nl, n_nl, ci_nl = share([r for _, _, r in nonlin])
    k_l, n_l, ci_l = share([r for _, _, r in lin])
    passed = validation["ok"] and not beats

    # --- figures ------------------------------------------------------------------------------
    import matplotlib.colors as mcolors

    cmap = mcolors.LinearSegmentedColormap.from_list("seq", ["#fbeee6", "#eb6834", "#7a2a0b"])
    fig, axes = C.new_axes(figsize=(11.6, 4.6), ncols=2)
    for ax, metric, title in ((axes[0], "exact", "Share of instances with the exact front"),
                              (axes[1], "points", "Share of exact front points found")):
        grid = np.full((PMAX, len(TS)), np.nan)
        for (t, p), v in by_tp.items():
            val = (sum(r["exact"] for r in v) / len(v) if metric == "exact"
                   else sum(r["right"] for r in v) / max(1, sum(r["front"] for r in v)))
            grid[p - 1, t - TS.start] = val
        im = ax.imshow(grid, origin="lower", cmap=cmap.reversed(), vmin=0, vmax=1, aspect="auto")
        for (t, p), v in by_tp.items():
            val = grid[p - 1, t - TS.start]
            label = f"{sum(r['exact'] for r in v)}/{len(v)}" if metric == "exact" else f"{val:.0%}"
            ax.text(t - TS.start, p - 1, label, ha="center", va="center", fontsize=6.5,
                    color="white" if val < 0.55 else C.INK)
        ax.set_xticks(range(len(TS)), list(TS))
        ax.set_yticks(range(PMAX), range(1, PMAX + 1))
        ax.set_xlabel("passengers t")
        ax.set_ylabel("planes p")
        ax.set_title(title, fontsize=10)
        ax.grid(False)
        fig.colorbar(im, ax=ax, fraction=0.04, pad=0.02)
    fig.suptitle(f"Papers' greedy vs exact front, n = {NS.start}..{NS.stop - 1}, random and generator families "
                 f"({n_nl:,} instances; linear family excluded)", fontsize=10.5)
    figures = C.save_figure(fig, NAME, "greedy_heatmap")

    fig, axes = C.new_axes(figsize=(11.6, 4.2), ncols=3, gridspec_kw={"width_ratios": [1.3, 1, 0.8]})
    ax = axes[0]
    for p in range(1, PMAX + 1):
        ts = [t for t in TS if (t, p) in by_t_p]
        vals = [share(by_t_p[(t, p)]) for t in ts]
        ys = [k / n for k, n, _ in vals]
        ax.plot(ts, ys, marker="o", markersize=3.5, color=C.PALETTE[p - 1], label=f"p = {p}")
        ax.fill_between(ts, [ci[0] for _, _, ci in vals], [ci[1] for _, _, ci in vals], color=C.PALETTE[p - 1],
                        alpha=0.12, linewidth=0)
    ax.set_xlabel("passengers t")
    ax.set_ylabel("share of instances exact (95% Wilson)")
    ax.set_ylim(0, 1.02)
    ax.set_title("By t and p (pooled over n)")
    ax.legend(loc="lower left", ncol=2, fontsize=7.5)
    ax = axes[1]
    ns = sorted(by_n)
    vals = [share(by_n[n]) for n in ns]
    ax.plot(ns, [k / m for k, m, _ in vals], marker="o", color=C.PALETTE[0], label="instances exact")
    ax.fill_between(ns, [c[0] for _, _, c in vals], [c[1] for _, _, c in vals], color=C.PALETTE[0], alpha=0.15,
                    linewidth=0)
    pts = [sum(r["right"] for r in by_n[n]) / sum(r["front"] for r in by_n[n]) for n in ns]
    ax.plot(ns, pts, marker="s", color=C.PALETTE[1], label="front points found")
    ax.set_xlabel("cities n")
    ax.set_ylim(0, 1.02)
    ax.set_title("By n (pooled over t, p)")
    ax.legend(loc="center left", fontsize=7.5)
    ax = axes[2]
    groups = ["random", "anti", "generator", "linear-generator", "linear-affine"]
    ys = [fam_stats[g]["exact"] / max(1, fam_stats[g]["instances"]) for g in groups]
    lo = [ys[i] - fam_stats[g]["wilson95"][0] for i, g in enumerate(groups)]
    hi = [fam_stats[g]["wilson95"][1] - ys[i] for i, g in enumerate(groups)]
    colors = [C.PALETTE[0]] * 3 + [C.PALETTE[2]] * 2
    ax.barh(range(len(groups)), ys, xerr=[lo, hi], color=colors, capsize=3, error_kw={"ecolor": C.INK2})
    for i, g in enumerate(groups):
        ax.text(0.02, i, f"{fam_stats[g]['exact']}/{fam_stats[g]['instances']}", va="center", fontsize=8,
                color="white")
    ax.set_yticks(range(len(groups)), groups)
    ax.set_xlim(0, 1.0)
    ax.set_xlabel("share exact")
    ax.set_title("By family (linear in green)")
    ax.grid(axis="y", visible=False)
    C.verdict_badge(axes[1], passed, "validated, sound", loc=(0.99, 0.02))
    fig.subplots_adjust(wspace=0.55)
    figures += C.save_figure(fig, NAME, "greedy_curves")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="the reimplemented greedy differs from the golden fronts exactly on lpt-counterexample and "
                  "n3t5p2-C1D4r10, its pruning never changes a front, and no greedy point beats the exact front",
        metrics={"validation": validation, "instances": len(done), "timeouts": timeouts,
                 "nonlinear_exact": k_nl, "nonlinear_instances": n_nl, "nonlinear_share_exact": round(k_nl / n_nl, 4),
                 "nonlinear_wilson95": [round(x, 4) for x in ci_nl],
                 "nonlinear_points_found": round(sum(r["right"] for _, _, r in nonlin)
                                                 / sum(r["front"] for _, _, r in nonlin), 4),
                 "linear_exact": k_l, "linear_instances": n_l, "linear_wilson95": [round(x, 4) for x in ci_l],
                 "linear_misses": lin_misses[:20], "by_family": fam_stats,
                 "by_t_p": {f"t{t}p{p}": {"exact": share(v)[0], "instances": share(v)[1]}
                            for (t, p), v in sorted(by_tp.items())},
                 "by_n": {str(n): {"exact": share(v)[0], "instances": share(v)[1]} for n, v in sorted(by_n.items())},
                 "by_t_minus_p": {k: {"exact": share(v)[0], "instances": share(v)[1]} for k, v in sorted(by_links.items())},
                 "exact_when_p1_or_t_minus_p_le_2": [share(small)[0], share(small)[1]],
                 "greedy_beats_front": beats[:10]},
        sizes={"grid": f"n in {NS.start}..{NS.stop - 1}, t in {TS.start}..{TS.stop - 1}, p in 1..min(t, {PMAX})",
               "per_cell": PER_CELL,
               "random": "d in [1,30], c in [0,50] (uniform or anti-correlated)",
               "generator": "3 of the 24 non-linear -C/-D pairs per cell, -r in {1,10,100}",
               "linear": "-C 3 -D 3 with -r in {1,10}; data files d_i = r0 i (r0 in 1..5), c_i = alpha - beta i "
                         "(beta in 0..5, alpha in [beta n, beta n + 30])",
               "timeout_s": TIMEOUT},
        tests=["paper-greedy-optimal", "claim-5", "conj-10-2"],
        refutes=["paper-greedy-optimal"] if k_nl < n_nl else [],
        hypothesis="The papers claim their per-PPP greedy is optimal; §5 refutes it with two counterexamples. "
                   "Conjecture 10.2 says it is exact on the linear family.",
        explanation=f"Outside the linear family the greedy is exact on {k_nl:,} of {n_nl:,} instances "
                    f"({k_nl / n_nl:.1%}, 95% CI {ci_nl[0]:.1%}-{ci_nl[1]:.1%}) and finds "
                    f"{sum(r['right'] for _, _, r in nonlin) / sum(r['front'] for _, _, r in nonlin):.1%} of the front "
                    f"points. With p = 1 or t - p <= 2 it is exact on {share(small)[0]:,} of {share(small)[1]:,} "
                    + ("instances: every miss in this sample has p >= 2 and t - p >= 3 (an observation, not a claim). "
                       if share(small)[0] == share(small)[1] else "instances. ")
                    +
                    f"On the linear family it is exact on {k_l} of {n_l} "
                    f"(95% CI {ci_l[0]:.1%}-{ci_l[1]:.1%})"
                    + (": evidence for Conjecture 10.2, not a proof." if k_l == n_l
                       else ", so Conjecture 10.2 is refuted by the listed misses."),
        figures=figures, binaries=[GREEDY, C.ZENO],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
