"""E7, scaling (Theorem 7.3): the front in pseudo-polynomial time, and how large `zeno` can go.

Theorem 7.3: the link-forest DP, with a step counter, takes a number of steps polynomial in n, t, p and
the level, so the front is computable in pseudo-polynomial time. The C++ solver's work over the level
range [T_lo, T_hi] (T_lo the bound of Proposition 3.6) is estimated here by
n q_max^2 s^2 T_hi (T_hi - T_lo + 1), a work estimate, not a theorem.
Two measurements:

* sweeps, one parameter at a time (median of 3 runs): the duration scale -r on the square-root
  family (durations without a common divisor, so the level range grows with -r), and n, t and p;
  the log-log slope of time against the level range must stay within the bound's degree 2;
* the frontier: single runs on a grid of (n, t, p), with a timeout per point, plotted against the
  instance size and against the bound, with timeouts marked.

Every run uses all cores (`zeno` default). Timings are wall clock on the host in the manifest.

Pass: every sweep point finishes, and the fitted exponent of time in the level range is at most 2.
"""

from __future__ import annotations

import math
import os
import re
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

NAME, CLAIM, SEED = "E7_scaling", "exp-e7-scaling", 0
SWEEP_TIMEOUT, FRONTIER_TIMEOUT, REPEATS = 120, 60, 3
SQRT = ["-C", "2", "-D", "2"]
SWEEPS = {
    "duration scale -r (n=20, t=12, p=4, sqrt)": [["-n", "20", "-t", "12", "-p", "4", *SQRT, "-r", str(r)]
                                                  for r in (1, 3, 10, 30, 100, 300, 1000, 3000, 10000)],
    "cities n (t=10, p=3, sqrt -r 100)": [["-n", str(n), "-t", "10", "-p", "3", *SQRT, "-r", "100"]
                                          for n in (10, 30, 100, 300, 1000)],
    "passengers t (n=50, p=5, sqrt -r 100)": [["-n", "50", "-t", str(t), "-p", "5", *SQRT, "-r", "100"]
                                              for t in (5, 10, 20, 40, 80)],
    "planes p (n=50, t=60, sqrt -r 100)": [["-n", "50", "-t", "60", "-p", str(p), *SQRT, "-r", "100"]
                                           for p in (2, 5, 10, 20, 40, 60)],
}
# (n, t, p, extra generator options); the coordinator's measurements are among them
FRONTIER = [(n, t, p, []) for n, t, p in [
    (50, 50, 2), (1000, 10, 3), (200, 100, 10), (500, 200, 20), (100, 500, 50), (1000, 1000, 100),
    (100, 100, 2), (100, 100, 10), (100, 100, 50), (1000, 100, 10), (100, 1000, 10), (100, 1000, 100),
    (1000, 200, 20), (200, 200, 100), (300, 300, 30), (2000, 50, 5), (50, 2000, 200), (5000, 20, 4),
]] + [(n, t, p, [*SQRT, "-r", str(r)]) for n, t, p, r in [
    (20, 12, 4, 1000), (50, 30, 5, 1000), (100, 60, 10, 100), (100, 60, 10, 1000), (200, 100, 10, 100),
    (200, 100, 10, 1000),
]]

_LEVELS = re.compile(r"levels (\d+)\.\.(\d+) \(x(\d+), (\d+) levels\)")
_WORK = re.compile(r"work: (\d+) states")


LOADS: list[float] = []  # 1-minute load average before every timed run: other jobs inflate wall times


def timed(args, timeout):
    """(seconds, stats dict) or (None, {"load": ...}) on timeout."""
    load = os.getloadavg()[0]
    LOADS.append(load)
    t0 = time.perf_counter()
    try:
        out = subprocess.run([str(C.require_zeno()), *args, "--stats"], capture_output=True, text=True,
                             timeout=timeout, check=True)
    except subprocess.TimeoutExpired:
        return None, {"load": round(load, 1)}
    seconds = time.perf_counter() - t0
    stats = {"front": len(C.parse_front(out.stdout)), "load": round(load, 1)}
    m = _LEVELS.search(out.stderr)
    if m:
        stats.update(T_lo=int(m.group(1)), T_hi=int(m.group(2)), g=int(m.group(3)), levels=int(m.group(4)))
    w = _WORK.search(out.stderr)
    if w:
        stats["states"] = int(w.group(1))
    return seconds, stats


def bound(args):
    """n, s, q_max and the level range from the generated data (durations over their gcd; T_lo the bound
    of Prop 3.6), and the work estimate n q_max^2 s^2 T_hi (T_hi - T_lo + 1) of the C++ link-forest DP."""
    with tempfile.TemporaryDirectory() as tmp:
        inst = C.generated_instance(args, Path(tmp))
    n, t, p = inst.n, inst.t, inst.p
    s, kappa = 2 * t - p, -(-(2 * t - p) // p)
    g = math.gcd(*inst.d) or 1
    d = [x // g for x in inst.d]
    cmin = min(inst.c)
    t_lo = min(d) * kappa
    t_hi = min(x for x, c in zip(d, inst.c) if c == cmin) * kappa
    q = min(p, t - p + 1)
    return {"n": n, "t": t, "p": p, "s": s, "T_lo": t_lo, "T_hi": t_hi,
            "bound": n * q * q * s * s * max(1, t_hi) * (t_hi - t_lo + 1)}


def slope(xs, ys):
    xs, ys = np.log(np.asarray(xs, float)), np.log(np.asarray(ys, float))
    return float(np.polyfit(xs, ys, 1)[0]) if len(xs) >= 2 else float("nan")


def plot(sweeps, frontier, exponent, passed, load) -> list[str]:
    """The four panels: duration sweep, one-parameter sweeps, and the frontier against size and bound."""
    pts = [(r["levels"], r["seconds"]) for r in sweeps[next(iter(SWEEPS))] if r.get("seconds") and r.get("levels")]
    fig, axes = C.new_axes(figsize=(11.0, 8.4), nrows=2, ncols=2)
    ax = axes[0][0]
    ax.plot([a for a, _ in pts], [b for _, b in pts], marker="o", color=C.PALETTE[0])
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("levels in the range [T_lo, T_hi]")
    ax.set_ylabel("wall time (s, median of 3)")
    ax.set_title(f"Duration scale: time ~ levels^{exponent:.2f} (bound: degree 2)")
    C.verdict_badge(ax, passed, f"exponent {exponent:.2f} <= 2")
    ax = axes[0][1]
    for k, label in enumerate(list(SWEEPS)[1:]):
        rows = [r for r in sweeps[label] if r["seconds"]]
        key = label.split()[1]
        ax.plot([r[key] for r in rows], [r["seconds"] for r in rows], marker="o", color=C.PALETTE[k + 1])
        ax.annotate(label.split(" (")[0], (rows[-1][key], rows[-1]["seconds"]), textcoords="offset points",
                    xytext=(6, -3), fontsize=8, color=C.PALETTE[k + 1])
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(right=ax.get_xlim()[1] * 4)
    ax.set_xlabel("swept parameter: n (t=10, p=3), t (n=50, p=5), p (n=50, t=60); sqrt -r 100")
    ax.set_ylabel("wall time (s, median of 3)")
    ax.set_title("One parameter at a time")
    for ax, xkey, xlabel in ((axes[1][0], "nt", "instance size n x t"),
                             (axes[1][1], "bound", "work estimate n q^2 s^2 T_hi (T_hi - T_lo + 1)")):
        xv = (lambda r: r["n"] * r["t"]) if xkey == "nt" else (lambda r: r["bound"])
        for k, fam in enumerate(["identity", "sqrt"]):
            done = [r for r in frontier if r["family"] == fam and not r["timeout"]]
            late = [r for r in frontier if r["family"] == fam and r["timeout"]]
            ax.scatter([xv(r) for r in done], [r["seconds"] for r in done], s=28, color=C.PALETTE[k],
                       label=f"{fam} family, finished", zorder=3)
            ax.scatter([xv(r) for r in late], [FRONTIER_TIMEOUT] * len(late), s=46, marker="x", color=C.PALETTE[k],
                       label=f"{fam} family, timeout ({FRONTIER_TIMEOUT} s)", zorder=3)
            for r in done:
                ax.annotate(f"{r['n']},{r['t']},{r['p']}", (xv(r), r["seconds"]), fontsize=6.5, color=C.INK2,
                            textcoords="offset points", xytext=(3, 3))
        ax.axhline(FRONTIER_TIMEOUT, color=C.MUTED, linewidth=0.8, linestyle=":")
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.set_ylim(top=FRONTIER_TIMEOUT * 4)
        if xkey == "nt":
            ax.set_xlim(right=ax.get_xlim()[1] * 10)  # room for the legend
        ax.set_xlabel(xlabel)
        ax.set_ylabel("wall time (s)")
        ax.set_title("How large can we go (labels: n,t,p)")
        ax.legend(loc="lower right", fontsize=7.5)
    late = sorted((r for r in frontier if r["timeout"]), key=lambda r: (r["family"], r["n"] * r["t"]))
    names = [f"{r['n']},{r['t']},{r['p']}" + (" sqrt" if r["family"] == "sqrt" else "") for r in late]
    rows = ["; ".join(names[i:i + 4]) for i in range(0, len(names), 4)]
    axes[1][0].text(0.01, 0.99, "timeouts (n,t,p):\n" + "\n".join(rows), transform=axes[1][0].transAxes,
                    fontsize=6.5, color=C.INK2, va="top")
    busy = load["median"] > 0.5 * (load["cpus"] or 1)
    fig.suptitle(f"zeno wall times, all {load['cpus']} cores; host load average {load['min']}-{load['max']} "
                 f"(median {load['median']})" + (": other jobs were running, times are upper bounds" if busy else ""),
                 fontsize=10)
    fig.subplots_adjust(hspace=0.38, wspace=0.25)
    return C.save_figure(fig, NAME, "scaling")


def replot() -> int:
    """Redraw the figure from results/E7_scaling/summary.json without measuring again."""
    import json

    s = json.loads((C.RESULTS / NAME / "summary.json").read_text())
    m = s["metrics"]
    plot(m["sweeps"], m["frontier"], m["duration_exponent"], s["passed"], m["host_load_1min"])
    return 0


def main() -> int:
    sweeps = {}
    for label, runs in SWEEPS.items():
        rows = []
        for args in runs:
            times, stats = [], {}
            for _ in range(REPEATS):
                sec, stats = timed(args, SWEEP_TIMEOUT)
                times.append(sec)
            ok = all(x is not None for x in times)
            rows.append({"args": " ".join(args), "seconds": statistics.median(times) if ok else None, **stats,
                         **{k: v for k, v in bound(args).items() if k in ("n", "t", "p", "s", "bound")}})
        sweeps[label] = rows
    frontier = []
    for n, t, p, extra in FRONTIER:
        args = ["-n", str(n), "-t", str(t), "-p", str(p), *extra]
        sec, stats = timed(args, FRONTIER_TIMEOUT)
        frontier.append({"args": " ".join(args), "family": "sqrt" if extra else "identity", "seconds": sec,
                         "timeout": sec is None, **stats, **bound(args)})
        print(f"  frontier {' '.join(args)}: {'timeout' if sec is None else f'{sec:.2f} s'}", flush=True)

    dscale = sweeps[next(iter(SWEEPS))]
    pts = [(r["levels"], r["seconds"]) for r in dscale if r.get("seconds") and r.get("levels")]
    big = [(a, b) for a, b in pts if b >= 0.02] or pts
    exponent = slope([a for a, _ in big], [b for _, b in big])
    all_finished = all(r["seconds"] is not None for rows in sweeps.values() for r in rows)
    passed = all_finished and exponent <= 2.0
    load = {"min": round(min(LOADS), 1), "median": round(statistics.median(LOADS), 1), "max": round(max(LOADS), 1),
            "cpus": os.cpu_count()}
    figures = plot(sweeps, frontier, exponent, passed, load)

    finished = [r for r in frontier if not r["timeout"]]
    busy = load["median"] > 0.5 * (load["cpus"] or 1)
    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="every sweep point finishes within its timeout, and on the duration-scale sweep the log-log slope "
                  "of time against the number of levels is at most 2, the degree of the pseudo-polynomial bound",
        metrics={"duration_exponent": round(exponent, 3), "host_load_1min": load, "sweeps": sweeps, "frontier": frontier,
                 "frontier_finished": len(finished), "frontier_timeouts": len(frontier) - len(finished),
                 "largest_finished": max(finished, key=lambda r: r["n"] * r["t"])["args"] if finished else None},
        sizes={"sweeps": {k: len(v) for k, v in SWEEPS.items()}, "repeats": REPEATS,
               "frontier_points": len(FRONTIER), "timeouts_s": {"sweep": SWEEP_TIMEOUT, "frontier": FRONTIER_TIMEOUT}},
        tests=["cor-8-3"],
        hypothesis="Theorem 7.3: the front is computable in time polynomial in n, s and the level range; the "
                   "running time should grow at most polynomially with the duration scale.",
        explanation=f"On the duration sweep the time grows as levels^{exponent:.2f}. The frontier finished "
                    f"{len(finished)} of {len(frontier)} grid points within {FRONTIER_TIMEOUT} s; see the metrics for "
                    "each point's time, level range and bound. The 1-minute load average before the runs was "
                    f"{load['min']}-{load['max']} (median {load['median']}) on {load['cpus']} cores"
                    + (": other jobs shared the machine, so the wall times are upper bounds and the frontier is "
                       "conservative." if busy else "."),
        figures=figures, binaries=[C.ZENO],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(replot() if "--replot" in sys.argv else main())
