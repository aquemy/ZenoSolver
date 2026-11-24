"""Shared helpers for the seeded validation campaign (E1-E10).

Every experiment `EN_name/run.py` is deterministic (`SEED = 0`), calls the existing binaries and
scripts of the repository (the C++ solver `zeno`, the brute-force oracle `zenoOracle`, the Lean
`zeno-check` and `zeno-front`, and the research programs of `doc/theory/checks`), and writes three
kinds of artifacts under `experiments/results/<name>/`:

* `summary.json`, the verdict (`Result.write`): passed, criterion, metrics, sizes, hypothesis,
  explanation, figures;
* `manifest.json`, the provenance: git sha, time, seed, host, versions, hashes of the binaries used;
* `*.png` + `*.svg`, the figures (`save_figure`).

`doc/theory/checks` is read-only here: its C++ programs are compiled into `build/checks/bin`
(`check_program`), and its Python scripts are run as they are (`run_check_script`).

The module also holds an independent plan simulator (`simulate`) for the plans `zeno --plans`
prints, so that achievability claims are checked by code that shares nothing with the solver.
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import re
import socket
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

# --- paths ------------------------------------------------------------------------------------

EXPERIMENTS = Path(__file__).resolve().parent
REPO = EXPERIMENTS.parent
RESULTS = EXPERIMENTS / "results"
CHECKS = REPO / "doc" / "theory" / "checks"  # read-only: another workstream owns it
CHECKS_BUILD = REPO / "build" / "checks"  # programs of CHECKS compiled here (bin/<program>)
BENCH = REPO / "bench"
ZENO = Path(os.environ.get("ZENO", REPO / "build" / "release" / "zeno"))
ORACLE = Path(os.environ.get("ZENO_ORACLE", REPO / "build" / "release" / "zenoOracle"))
LEAN_BIN = REPO / "lean" / ".lake" / "build" / "bin"
LEAN_CHECK = Path(os.environ.get("ZENO_LEAN_CHECK", LEAN_BIN / "zeno-check"))
LEAN_FRONT = Path(os.environ.get("ZENO_LEAN_FRONT", LEAN_BIN / "zeno-front"))

WORKERS = int(os.environ.get("ZS_EXPERIMENT_WORKERS", max(1, (os.cpu_count() or 2) - 2)))
_STARTED = time.time()


# --- building the tools -----------------------------------------------------------------------


def require_zeno() -> Path:
    """The C++ solver (and the oracle next to it), built with the release preset if missing."""
    if not ZENO.exists() or not ORACLE.exists():
        print(f"building {ZENO.relative_to(REPO)} (cmake --preset release)", flush=True)
        subprocess.run(["cmake", "--preset", "release"], cwd=REPO, check=True, capture_output=True)
        subprocess.run(["cmake", "--build", "--preset", "release", "-j"], cwd=REPO, check=True, capture_output=True)
    return ZENO


def require_lean() -> tuple[Path, Path]:
    """The Lean checker and solver, built with `lake build` if missing (slow without a Mathlib cache)."""
    if not LEAN_CHECK.exists() or not LEAN_FRONT.exists():
        print("building lean/ zeno-check and zeno-front (lake build)", flush=True)
        subprocess.run(["lake", "build", "zeno-check", "zeno-front"], cwd=REPO / "lean", check=True)
    return LEAN_CHECK, LEAN_FRONT


def check_program(name: str) -> Path:
    """Compile doc/theory/checks/<name>.cpp into build/checks/bin/<name> (as checks/build.sh does),
    unless the binary is newer than its sources. The checks directory itself is never written."""
    src = CHECKS / f"{name}.cpp"
    out = CHECKS_BUILD / "bin" / name
    deps = [src, REPO / "tests" / "oracle" / "bruteForce.hpp"]
    if not out.exists() or out.stat().st_mtime < max(p.stat().st_mtime for p in deps if p.exists()):
        out.parent.mkdir(parents=True, exist_ok=True)
        cxx = os.environ.get("CXX", "c++")
        subprocess.run([cxx, "-std=c++17", "-O2", str(src), "-o", str(out)], check=True)
    return out


def run_check_script(script: str, *args: object, timeout: float | None = None) -> str:
    """Run doc/theory/checks/<script> with this environment's interpreter; return its stdout."""
    cmd = [sys.executable, str(CHECKS / script), *map(str, args)]
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, check=True)
    return out.stdout


# --- instances --------------------------------------------------------------------------------


@dataclass(frozen=True)
class Instance:
    """A MultiZenoTravel instance: central cities with C_I-side durations d, C_G-side durations
    dbar (None = symmetric, dbar = d) and landing costs c; t passengers, p planes."""

    d: tuple[int, ...]
    c: tuple[int, ...]
    t: int
    p: int
    dbar: tuple[int, ...] | None = None

    @property
    def n(self) -> int:
        return len(self.d)

    @property
    def symmetric(self) -> bool:
        return self.dbar is None or tuple(self.dbar) == tuple(self.d)

    @property
    def db(self) -> tuple[int, ...]:
        return self.d if self.dbar is None else self.dbar

    @property
    def s(self) -> int:
        return 2 * self.t - self.p

    def canonical(self) -> "Instance":
        """Cities sorted by (d, dbar, c): the same instance up to relabelling the cities."""
        rows = sorted(zip(self.d, self.db, self.c))
        d = tuple(r[0] for r in rows)
        db = tuple(r[1] for r in rows)
        c = tuple(r[2] for r in rows)
        return Instance(d, c, self.t, self.p, None if self.dbar is None else db)

    def write(self, path: Path) -> Path:
        """A data file as `zeno -d` reads it: durations (C_I side, then C_G side if non-symmetric), costs."""
        lines = [self.d] if self.dbar is None else [self.d, self.dbar]
        lines.append(self.c)
        Path(path).write_text("\n".join(" ".join(map(str, row)) for row in lines) + "\n")
        return Path(path)

    def args(self, path: Path) -> list[str]:
        return ["-n", str(self.n), "-t", str(self.t), "-p", str(self.p), "-d", str(path)]

    def label(self) -> str:
        if self.symmetric:
            return f"d={list(self.d)} c={list(self.c)} t={self.t} p={self.p}"
        return f"d={list(self.d)} dbar={list(self.db)} c={list(self.c)} t={self.t} p={self.p}"

    def as_dict(self) -> dict:
        out = {"d": list(self.d), "c": list(self.c), "t": self.t, "p": self.p}
        if not self.symmetric:
            out["dbar"] = list(self.db)
        return out


def read_data(path: Path, t: int, p: int) -> Instance:
    """Read a 2-line (d, c) or 3-line (d, dbar, c) data file as written by `zeno generate`."""
    rows = [list(map(int, line.split())) for line in Path(path).read_text().splitlines() if line.strip()]
    if len(rows) == 2:
        return Instance(tuple(rows[0]), tuple(rows[1]), t, p)
    return Instance(tuple(rows[0]), tuple(rows[2]), t, p, tuple(rows[1]))


def generated_instance(args: list[str], tmp: Path) -> Instance:
    """The data `zeno` builds from generator options (`zeno generate`), as an Instance."""
    out = subprocess.run([str(require_zeno()), "generate", *args], capture_output=True, text=True, check=True).stdout
    path = Path(tmp) / "generated.dat"
    path.write_text(out)
    t = int(args[args.index("-t") + 1])
    p = int(args[args.index("-p") + 1])
    return read_data(path, t, p)


# --- fronts -----------------------------------------------------------------------------------

Point = tuple[int, int]  # (cost, makespan)


def parse_front(text: str) -> list[Point]:
    """`cost makespan` lines up to the first blank line, sorted by cost."""
    pts = []
    for line in text.splitlines():
        if not line.strip():
            break
        if line.startswith("#"):
            continue
        a, b = line.split()[:2]
        pts.append((int(a), int(b)))
    return sorted(pts)


def pareto(points) -> list[Point]:
    """Minimal points of a finite set of (cost, makespan), sorted by cost."""
    out: list[Point] = []
    for c, m in sorted(set(points)):
        if not out or m < out[-1][1]:
            out.append((c, m))
    return out


def dominated(point: Point, front) -> bool:
    """True when some point of `front` weakly dominates `point`."""
    return any(c <= point[0] and m <= point[1] for c, m in front)


# --- running the solvers ----------------------------------------------------------------------


@dataclass
class Leg:
    frm: int  # 0 = C_I, 1..n central, n+1 = C_G
    to: int
    dep: int
    arr: int
    pax: int  # 0 = empty


@dataclass
class ZenoRun:
    front: list[Point]
    stderr: str
    plans: dict[Point, list[list[Leg]]] = field(default_factory=dict)


_LEG = re.compile(r"(CI|CG|c\d+)->(CI|CG|c\d+)\[(-?\d+),(-?\d+)\](?:p(\d+))?")


def _loc(name: str, n: int) -> int:
    return 0 if name == "CI" else n + 1 if name == "CG" else int(name[1:])


def parse_plans(text: str, n: int) -> dict[Point, list[list[Leg]]]:
    """The plans of `zeno --plans`: '# cost C, makespan M' then one 'plane k: legs' line per plane."""
    plans: dict[Point, list[list[Leg]]] = {}
    current = None
    for line in text.splitlines():
        head = re.match(r"# cost (\d+), makespan (\d+)", line)
        if head:
            current = (int(head.group(1)), int(head.group(2)))
            plans[current] = []
        elif line.startswith("plane") and current is not None:
            legs = [Leg(_loc(a, n), _loc(b, n), int(e), int(r), int(k or 0)) for a, b, e, r, k in _LEG.findall(line)]
            plans[current].append(legs)
    return plans


def run_zeno(inst: Instance, tmp: Path, *extra: str, plans: bool = False, timeout: float = 600) -> ZenoRun:
    data = inst.write(Path(tmp) / "instance.dat")
    cmd = [str(require_zeno()), *inst.args(data), *extra] + (["--plans"] if plans else [])
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, check=True)
    return ZenoRun(parse_front(out.stdout), out.stderr, parse_plans(out.stdout, inst.n) if plans else {})


def oracle_front(inst: Instance, tmp: Path, timeout: float = 600) -> list[Point]:
    """The brute-force oracle of the tests (role-configuration schedules with exact waiting)."""
    data = inst.write(Path(tmp) / "oracle.dat")
    out = subprocess.run([str(ORACLE), *inst.args(data)], capture_output=True, text=True, timeout=timeout, check=True)
    return parse_front(out.stdout)


def truth_front(inst: Instance, central: str = "none", extra: int = 2, timeout: float = 120,
                anywhere: bool = False) -> list[Point] | None:
    """Exhaustive search over ALL plans (doc/theory/checks/truth.cpp): no 2t-p landings, no
    patterns, central flights none / a1 (useless) / tight (shortest the triangle inequality allows).
    None on timeout. Needs durations >= 1, n <= 4, t <= 7, p <= 4."""
    env = dict(os.environ)
    env.pop("ANYWHERE", None)
    if anywhere:
        env["ANYWHERE"] = "1"
    cmd = [str(check_program("truth")), ",".join(map(str, inst.d)), ",".join(map(str, inst.db)),
           ",".join(map(str, inst.c)), str(inst.t), str(inst.p), central, str(extra)]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env, check=True)
    except subprocess.TimeoutExpired:
        return None
    return parse_front(out.stdout)


# --- independent plan simulator ---------------------------------------------------------------


class PlanError(ValueError):
    pass


def simulate(inst: Instance, routes: list[list[Leg]]) -> Point:
    """Check a plan against the semantics of doc/certificate-format.md and return (cost, makespan).

    Every plane starts in C_I at time >= 0, each leg leaves where the previous one arrived and no
    earlier, lasts exactly d (C_I side) or dbar (C_G side), joins a hub and a central city, and the
    route ends in C_G. Every passenger 1..t rides a chain of legs from C_I to C_G, each leaving where
    the previous one arrived and no earlier. Written independently of the solver; assumes positive
    durations (legs of a journey are ordered by time)."""
    n = inst.n
    if len(routes) != inst.p:
        raise PlanError(f"{len(routes)} routes for {inst.p} planes")
    cost, makespan = 0, 0
    journeys: dict[int, list[Leg]] = {}
    for k, legs in enumerate(routes):
        if not legs:
            raise PlanError(f"plane {k + 1} has no leg")
        where, clock = 0, 0
        for leg in legs:
            if leg.frm != where:
                raise PlanError(f"plane {k + 1}: leg leaves {leg.frm}, plane is in {where}")
            if leg.dep < clock:
                raise PlanError(f"plane {k + 1}: leg departs at {leg.dep} before arrival at {clock}")
            hub, city = (leg.frm, leg.to) if leg.frm in (0, n + 1) else (leg.to, leg.frm)
            if hub not in (0, n + 1) or not 1 <= city <= n:
                raise PlanError(f"plane {k + 1}: leg {leg.frm}->{leg.to} is not hub-central")
            duration = inst.d[city - 1] if hub == 0 else inst.db[city - 1]
            if leg.arr - leg.dep != duration:
                raise PlanError(f"plane {k + 1}: leg {leg.frm}->{leg.to} lasts {leg.arr - leg.dep}, not {duration}")
            if 1 <= leg.to <= n:
                cost += inst.c[leg.to - 1]
            if leg.pax:
                journeys.setdefault(leg.pax, []).append(leg)
            where, clock = leg.to, leg.arr
        if where != n + 1:
            raise PlanError(f"plane {k + 1} ends in {where}, not C_G")
        makespan = max(makespan, clock)
    if sorted(journeys) != list(range(1, inst.t + 1)):
        raise PlanError(f"passengers carried: {sorted(journeys)}")
    for pax, legs in journeys.items():
        legs = sorted(legs, key=lambda leg: (leg.dep, leg.arr))
        where, clock = 0, 0
        for leg in legs:
            if leg.frm != where or leg.dep < clock:
                raise PlanError(f"passenger {pax}: broken journey at {leg.frm}->{leg.to}[{leg.dep},{leg.arr}]")
            where, clock = leg.to, leg.arr
        if where != n + 1:
            raise PlanError(f"passenger {pax} ends in {where}")
    return cost, makespan


# --- small utilities --------------------------------------------------------------------------


def pmap(fn, items, workers: int | None = None) -> list:
    """Order-preserving parallel map (threads; the work is in subprocesses)."""
    items = list(items)
    with ThreadPoolExecutor(max_workers=workers or WORKERS) as pool:
        return list(pool.map(fn, items))


def wilson(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    """Wilson score interval (95% by default) for a proportion k / n; (0, 1) when n = 0."""
    if n == 0:
        return 0.0, 1.0
    phat = k / n
    denom = 1 + z * z / n
    centre = (phat + z * z / (2 * n)) / denom
    half = z * ((phat * (1 - phat) / n + z * z / (4 * n * n)) ** 0.5) / denom
    return max(0.0, centre - half), min(1.0, centre + half)


def random_instance(rng, n: int, t: int, p: int, dmax: int = 30, cmax: int = 50, dmin: int = 1,
                    symmetric: bool = True, anti: bool = False) -> Instance:
    """A random instance in canonical order. `anti` makes costs decrease with duration (no city is
    dominated by a faster cheaper one, the regime of the generator)."""
    d = [rng.randint(dmin, dmax) for _ in range(n)]
    if anti:
        d.sort()
        top = rng.randint(cmax // 2, cmax)
        c = sorted((rng.randint(0, top) for _ in range(n)), reverse=True)
    else:
        c = [rng.randint(0, cmax) for _ in range(n)]
    dbar = None if symmetric else tuple(rng.randint(dmin, dmax) for _ in range(n))
    return Instance(tuple(d), tuple(c), t, p, dbar).canonical()


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# --- plotting ---------------------------------------------------------------------------------
# Static figures for the report: the reference categorical palette in fixed order, thin marks,
# hairline grid, recessive axes; status colours only for pass / fail, always with a text label.

PALETTE = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300", "#6250d6", "#e34948"]
GOOD, CRITICAL = "#0ca30c", "#d03b3b"
INK, INK2, MUTED, GRID, AXIS, SURFACE = "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#c3c2b7", "#fcfcfb"


def new_axes(figsize=(6.4, 4.2), nrows=1, ncols=1, **kwargs):
    """Create (fig, ax[es]) on the non-interactive Agg backend, in the campaign's style."""
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    plt.rcParams.update({
        "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
        "axes.edgecolor": AXIS, "axes.labelcolor": INK2, "axes.titlecolor": INK, "axes.titlesize": 10.5,
        "axes.labelsize": 9.5, "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.6,
        "axes.spines.top": False, "axes.spines.right": False, "xtick.color": MUTED, "ytick.color": MUTED,
        "xtick.labelsize": 8.5, "ytick.labelsize": 8.5, "legend.frameon": False, "legend.fontsize": 8.5,
        "lines.linewidth": 2.0, "lines.markersize": 6, "font.family": "sans-serif", "svg.hashsalt": "zeno",
        "axes.prop_cycle": matplotlib.cycler(color=PALETTE), "text.color": INK,
    })
    return plt.subplots(nrows=nrows, ncols=ncols, figsize=figsize, **kwargs)


def save_figure(fig, exp_name: str, stem: str) -> list[str]:
    """Save `fig` as PNG + SVG under results/<exp_name>/; return paths relative to results/."""
    import matplotlib.pyplot as plt

    d = RESULTS / exp_name
    d.mkdir(parents=True, exist_ok=True)
    rels = []
    for ext in ("png", "svg"):
        p = d / f"{stem}.{ext}"
        meta = {"Date": None} if ext == "svg" else {"Software": None}
        fig.savefig(p, bbox_inches="tight", dpi=150, metadata=meta)
        rels.append(str(p.relative_to(RESULTS)))
    plt.close(fig)
    return rels


def verdict_badge(ax, passed: bool, text: str, loc=(0.99, 0.02), ha="right"):
    """A pass / fail label in the corner of an axis: colour plus words, never colour alone."""
    ax.text(*loc, ("PASS  " if passed else "FAIL  ") + text, transform=ax.transAxes, ha=ha, va="bottom",
            fontsize=8.5, color="white", fontweight="bold",
            bbox=dict(boxstyle="round,pad=0.35", fc=GOOD if passed else CRITICAL, ec="none"))


# --- verdict + provenance ---------------------------------------------------------------------


def _git(*args: str) -> str:
    try:
        return subprocess.check_output(["git", *args], cwd=REPO, stderr=subprocess.DEVNULL, text=True).strip()
    except Exception:
        return "unknown"


def _versions() -> dict[str, str]:
    import matplotlib

    v = {"python": sys.version.split()[0], "numpy": np.__version__, "matplotlib": matplotlib.__version__}
    try:
        import ortools

        v["ortools"] = ortools.__version__
    except ImportError:
        pass
    try:
        v["cxx"] = subprocess.check_output([os.environ.get("CXX", "c++"), "--version"], text=True).splitlines()[0]
    except Exception:
        pass
    toolchain = REPO / "lean" / "lean-toolchain"
    if toolchain.exists():
        v["lean"] = toolchain.read_text().strip()
    return v


@dataclass
class Result:
    """A seeded experiment verdict, written to results/<name>/ as CKC evidence.

    `claim` is the experiment's own claim (`claim:exp-eN-name`, closed by its science commit);
    `tests` and `refutes` list the claims.toml slugs it bears on. `sizes` documents every sample
    size. `hypothesis` / `explanation` carry the narrative; `figures` the saved plots (relative to
    results/). `binaries` are hashed into the manifest."""

    name: str
    claim: str
    seed: int
    passed: bool
    criterion: str
    metrics: dict[str, object]
    sizes: dict[str, object] = field(default_factory=dict)
    tests: list[str] = field(default_factory=list)
    refutes: list[str] = field(default_factory=list)
    hypothesis: str = ""
    explanation: str = ""
    figures: list[str] = field(default_factory=list)
    binaries: list[Path] = field(default_factory=list)
    started: float = field(default_factory=lambda: _STARTED)  # the experiment's start (module import)

    def write(self) -> Path:
        d = RESULTS / self.name
        d.mkdir(parents=True, exist_ok=True)
        summary = {
            "experiment": self.name,
            "claim": self.claim,
            "tests": self.tests,
            "refutes": self.refutes,
            "seed": self.seed,
            "passed": bool(self.passed),
            "criterion": self.criterion,
            "hypothesis": self.hypothesis,
            "explanation": self.explanation,
            "metrics": self.metrics,
            "sizes": self.sizes,
            "figures": self.figures,
        }
        path = d / "summary.json"
        path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        manifest = {
            "experiment": self.name,
            "claim": self.claim,
            "seed": self.seed,
            "passed": bool(self.passed),
            "git_sha": _git("rev-parse", "HEAD"),
            "git_dirty": _git("status", "--porcelain", "--", "src", "include", "lean", "doc/theory/checks") != "",
            "created_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "runtime_s": round(time.time() - self.started, 1),
            "host": socket.gethostname(),
            "platform": platform.platform(),
            "cpus": os.cpu_count(),
            "versions": _versions(),
            "binaries": {str(Path(b).resolve().relative_to(REPO)): sha256(Path(b)) for b in self.binaries
                         if Path(b).exists()},
            "figures": self.figures,
        }
        (d / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        return path


def announce(result: Result) -> int:
    """Print the verdict and return the process exit code (0 pass, 1 fail)."""
    verdict = "PASS" if result.passed else "FAIL"
    print(f"[{verdict}] {result.name} ({result.claim})")
    print(f"  criterion: {result.criterion}")
    for k, v in result.metrics.items():
        print(f"  {k} = {v}")
    return 0 if result.passed else 1
