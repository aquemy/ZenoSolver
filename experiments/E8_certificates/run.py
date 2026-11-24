"""E8, certificates (Theorem 9.1): an accepted certificate always states the true front.

Theorem 9.1: if a certificate's four obligations hold (plans reach their points, nothing faster than
the first point, nothing cheaper inside a gap, nothing cheaper than the last point), its list is the
Pareto front. Two checkers verify the obligations: the C++ reference `zeno check` and the Lean
`zeno-check`, whose soundness is proved in Lean. Three tests:

* A, the corpus of lean/test/certificates: every `accepted/` file accepted and every `rejected/` file
  rejected, by both checkers;
* B, fresh certificates written by `zeno --certificate` on random instances (version 1 when
  symmetric, version 2 otherwise): all accepted by both;
* C, mutants of the corpus and of the fresh certificates: drop a point, lower a cost or a makespan,
  shift a leg, change a passenger, weaken a gap's bound to `relaxed`, drop an assumption. A mutant
  MUST be rejected when its front differs from the true one, when one of its plans fails the
  independent simulator (`common.simulate`), or when it lacks an assumption a bound needs; otherwise
  either verdict is allowed.

Pass: A and B as stated, and no checker accepts a mutant that must be rejected.
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

NAME, CLAIM, SEED = "E8_certificates", "exp-e8-certificates", 0
CORPUS = C.REPO / "lean" / "test" / "certificates"
N_SYM, N_NONSYM = 400, 300
CHECK_TIMEOUT = 300
NEEDS_A1NS = {"roles", "lagrangian", "balanced", "search"}


# --- certificates as line lists ---------------------------------------------------------------


class Cert:
    def __init__(self, text: str):
        self.lines = [ln.strip() for ln in text.splitlines() if ln.strip() and not ln.lstrip().startswith("#")]

    def text(self) -> str:
        return "\n".join(self.lines) + "\n"

    def index(self, prefix: str) -> int:
        return next(i for i, ln in enumerate(self.lines) if ln.split()[0] == prefix)

    @property
    def version(self) -> int:
        return int(self.lines[0].split()[1])

    def front(self) -> list[tuple[int, int]]:
        i = self.index("front")
        r = int(self.lines[i].split()[1])
        return [tuple(map(int, self.lines[i + 1 + k].split())) for k in range(r)]

    def instance(self) -> C.Instance:
        n, t, p = map(int, self.lines[self.index("instance")].split()[1:])
        d = tuple(map(int, self.lines[self.index("d")].split()[1:]))
        db = tuple(map(int, self.lines[self.index("dbar")].split()[1:]))
        c = tuple(map(int, self.lines[self.index("c")].split()[1:]))
        return C.Instance(d, c, t, p, None if d == db else db)

    def assumptions(self) -> list[str]:
        return self.lines[self.index("assume")].split()[1:]

    def plan_blocks(self) -> list[tuple[int, int]]:
        """(start, end) line ranges of the plan blocks, in order."""
        starts = [i for i, ln in enumerate(self.lines) if ln.startswith("plan ")]
        stop = self.index("lower-bounds")
        return [(s, (starts[k + 1] if k + 1 < len(starts) else stop)) for k, s in enumerate(starts)]

    def gap_lines(self) -> list[int]:
        i = self.index("lower-bounds")
        return list(range(i + 1, i + 1 + int(self.lines[i].split()[1])))

    def leg_lines(self) -> list[int]:
        return [i for s, e in self.plan_blocks() for i in range(s, e) if self.lines[i].split()[0].isdigit()]

    def plans(self, inst: C.Instance) -> list[list[list[C.Leg]]]:
        out = []
        for s, e in self.plan_blocks():
            routes = []
            for ln in self.lines[s + 1:e]:
                if ln.startswith("plane"):
                    routes.append([])
                else:
                    a, b, dep, arr, pax = map(int, ln.split())
                    routes[-1].append(C.Leg(a, b, dep, arr, pax))
            out.append(routes)
        return out

    def copy(self) -> "Cert":
        c = Cert("")
        c.lines = list(self.lines)
        return c


def plans_valid(cert: Cert) -> bool:
    """Obligation 1, by the independent simulator: every plan reaches exactly its point."""
    try:
        inst = cert.instance()
        front = cert.front()
        plans = cert.plans(inst)
        if len(plans) != len(front):
            return False
        return all(C.simulate(inst, routes) == pt for routes, pt in zip(plans, front))
    except (C.PlanError, ValueError, IndexError, StopIteration):
        return False


# --- mutations: each returns (mutant, must_reject) or None when it does not apply ---------------


def drop_point(cert, rng):
    front = cert.front()
    if len(front) < 2:
        return None
    k = rng.randrange(len(front))
    m = cert.copy()
    i = m.index("front")
    m.lines[i] = f"front {len(front) - 1}"
    del m.lines[i + 1 + k]
    s, e = m.plan_blocks()[k]
    del m.lines[s:e]
    for j, (s, _) in enumerate(m.plan_blocks()):
        m.lines[s] = f"plan {j + 1} {m.lines[s].split()[2]}"
    gaps = m.gap_lines()
    del m.lines[gaps[min(k, len(gaps) - 1)]]
    i = m.index("lower-bounds")
    m.lines[i] = f"lower-bounds {len(front) - 2}"
    for j, g in enumerate(m.gap_lines()):
        m.lines[g] = " ".join([str(j + 1), *m.lines[g].split()[1:]])
    return m, True


def shift_point(which):
    def mutate(cert, rng):
        front = cert.front()
        k = rng.randrange(len(front))
        if front[k][which] == 0:
            return None
        m = cert.copy()
        pt = list(front[k])
        pt[which] -= 1
        m.lines[m.index("front") + 1 + k] = f"{pt[0]} {pt[1]}"
        return m, True
    return mutate


def simulable(cert) -> bool:
    """The simulator orders journeys by time, so it needs positive durations; judge plan mutations only on
    bases it validates."""
    inst = cert.instance()
    return min(inst.d + inst.db) >= 1 and plans_valid(cert)


def shift_leg(cert, rng):
    legs = cert.leg_lines()
    if not legs or not simulable(cert):
        return None
    m = cert.copy()
    i = rng.choice(legs)
    a, b, dep, arr, pax = map(int, m.lines[i].split())
    delta = rng.choice([-1, 1]) if dep > 0 else 1
    m.lines[i] = f"{a} {b} {dep + delta} {arr + delta} {pax}"
    return m, not plans_valid(m)


def change_passenger(cert, rng):
    legs = [i for i in cert.leg_lines() if cert.lines[i].split()[4] != "0"]
    t = cert.instance().t
    if not legs or t < 2 or not simulable(cert):
        return None
    m = cert.copy()
    i = rng.choice(legs)
    a, b, dep, arr, pax = map(int, m.lines[i].split())
    m.lines[i] = f"{a} {b} {dep} {arr} {rng.choice([q for q in range(1, t + 1) if q != pax])}"
    return m, not plans_valid(m)


def weaken_gap(cert, rng):
    gaps = [g for g in cert.gap_lines() if cert.lines[g].split()[1] != "relaxed"]
    if not gaps:
        return None
    m = cert.copy()
    g = rng.choice(gaps)
    m.lines[g] = f"{m.lines[g].split()[0]} relaxed"
    return m, False  # the relaxed bound may or may not close the gap: either verdict is allowed


def drop_assumption(cert, rng):
    have = cert.assumptions()
    kinds = {cert.lines[g].split()[1] for g in cert.gap_lines()}
    if cert.version == 2:
        fastest = cert.lines[cert.index("fastest")].split()[1]
        kinds.add(fastest)
    needed = set()
    if cert.version == 1 and "S" in have:
        needed.add("S")  # obligation 2 (fastest point) and every gap bound use (S)
    if "forest" in kinds and "A1" in have:
        needed.add("A1")
    if kinds & NEEDS_A1NS and "A1-NS" in have:
        needed.add("A1-NS")
    if not needed:
        return None
    drop = rng.choice(sorted(needed))
    m = cert.copy()
    m.lines[m.index("assume")] = " ".join(["assume", *[a for a in have if a != drop]])
    return m, True


MUTATIONS = {"drop-point": drop_point, "lower-cost": shift_point(0), "lower-makespan": shift_point(1),
             "shift-leg": shift_leg, "change-passenger": change_passenger, "weaken-gap": weaken_gap,
             "drop-assumption": drop_assumption}


# --- checkers ---------------------------------------------------------------------------------


def verdicts(path: Path) -> dict[str, bool | None]:
    out = {}
    for name, cmd in (("cpp", [str(C.ZENO), "check", str(path)]), ("lean", [str(C.LEAN_CHECK), str(path)])):
        try:
            out[name] = subprocess.run(cmd, capture_output=True, text=True, timeout=CHECK_TIMEOUT).returncode == 0
        except subprocess.TimeoutExpired:
            out[name] = None
    return out


def check_text(text: str) -> dict[str, bool | None]:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "c.cert"
        path.write_text(text)
        return verdicts(path)


def fresh(job):
    kind, inst = job
    with tempfile.TemporaryDirectory() as tmp:
        cert = Path(tmp) / "front.cert"
        C.run_zeno(inst, Path(tmp), "--certificate", str(cert))
        if not cert.exists():  # non-symmetric bracket not closed: no certificate
            return kind, inst, None, None
        return kind, inst, cert.read_text(), verdicts(cert)


def mutate(job):
    origin, text, mutation, seed = job
    rng = random.Random(seed)
    made = MUTATIONS[mutation](Cert(text), rng)
    if made is None:
        return origin, mutation, None, None
    mutant, must_reject = made
    return origin, mutation, must_reject, check_text(mutant.text())


def main() -> int:
    rng = random.Random(SEED)
    C.require_lean()

    # A. corpus
    corpus = [(f.name, want, f) for want, sub in ((True, "accepted"), (False, "rejected"))
              for f in sorted((CORPUS / sub).glob("*.cert"))]
    corpus_rows = C.pmap(lambda job: (job[0], job[1], verdicts(job[2])), corpus)
    corpus_bad = [{"file": name, "expected": want, **v} for name, want, v in corpus_rows
                  if v["cpp"] != want or v["lean"] != want]

    # B. fresh certificates
    jobs = []
    for _ in range(N_SYM):
        p = rng.randint(1, 5)
        t = rng.randint(p, p + 6)
        jobs.append(("symmetric", C.random_instance(rng, rng.randint(1, 6), t, p, dmax=25, anti=rng.random() < 0.5)))
    for _ in range(N_NONSYM):
        p = rng.randint(1, 3)
        t = rng.randint(p, p + 3)
        jobs.append(("non-symmetric", C.random_instance(rng, rng.randint(1, 3), t, p, dmax=15, cmax=10,
                                                         symmetric=False)))
    fresh_rows = C.pmap(fresh, jobs)
    written = [r for r in fresh_rows if r[2] is not None]
    fresh_bad = [{"kind": k, "instance": i.as_dict(), **v} for k, i, _, v in written if not (v["cpp"] and v["lean"])]

    # C. mutants of every accepted certificate
    bases = [(f"corpus:{f.name}", f.read_text()) for f in sorted((CORPUS / "accepted").glob("*.cert"))]
    bases += [(f"fresh:{k}", text) for k, _, text, _ in written]
    mjobs = [(origin, text, mutation, rng.randrange(1 << 30)) for origin, text in bases for mutation in MUTATIONS]
    mrows = [r for r in C.pmap(mutate, mjobs) if r[2] is not None]
    table = {m: Counter() for m in MUTATIONS}
    unsound, disagree = [], []
    for origin, mutation, must_reject, v in mrows:
        tab = table[mutation]
        tab["mutants"] += 1
        tab["must_reject"] += must_reject
        for checker in ("cpp", "lean"):
            tab[f"{checker}_rejected"] += v[checker] is False
            tab[f"{checker}_timeout"] += v[checker] is None
            if must_reject and v[checker]:
                unsound.append({"origin": origin, "mutation": mutation, "checker": checker})
        if v["cpp"] != v["lean"]:
            disagree.append({"origin": origin, "mutation": mutation, **v})
    passed = not corpus_bad and not fresh_bad and not unsound

    fig, ax = C.new_axes(figsize=(9.0, 4.2))
    names = list(MUTATIONS)
    x = range(len(names))
    w = 0.27
    must = [table[m]["must_reject"] for m in names]
    for k, checker in enumerate(("cpp", "lean")):
        ax.bar([i + (k - 0.5) * w for i in x], [table[m][f"{checker}_rejected"] for m in names], w,
               color=C.PALETTE[k], label=f"rejected by {'zeno check (C++)' if checker == 'cpp' else 'zeno-check (Lean)'}")
    ax.scatter(list(x), must, marker="_", s=420, color=C.INK, linewidths=2, zorder=3, label="must be rejected")
    for i, m in enumerate(names):
        ax.text(i, max(must[i], table[m]["cpp_rejected"], table[m]["lean_rejected"]) + 4, f"{table[m]['mutants']}",
                ha="center", fontsize=8, color=C.MUTED)
    ax.set_xticks(list(x), names, rotation=15)
    ax.set_ylabel("mutants (count above: generated)")
    ax.set_title(f"Mutants of {len(bases)} accepted certificates; corpus {len(corpus)} files, "
                 f"{len(written)} fresh certificates")
    ax.grid(axis="x", visible=False)
    ax.legend(loc="upper right", fontsize=8)
    ax.set_ylim(0, max(table[m]["mutants"] for m in names) * 1.35)
    C.verdict_badge(ax, passed, f"{len(unsound)} unsound acceptances", loc=(0.01, 0.9), ha="left")
    figures = C.save_figure(fig, NAME, "certificate_mutants")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="both checkers give the expected verdict on the 41 corpus files, accept every fresh certificate, "
                  "and never accept a mutant whose front is false, whose plans fail the independent simulator, or "
                  "which lacks an assumption a bound needs",
        metrics={"corpus_files": len(corpus), "corpus_wrong_verdicts": corpus_bad,
                 "fresh_written": {k: sum(1 for r in written if r[0] == k) for k in ("symmetric", "non-symmetric")},
                 "fresh_not_written_open_bracket": sum(1 for r in fresh_rows if r[2] is None),
                 "fresh_rejected": fresh_bad, "mutation_bases": len(bases),
                 "mutants": {m: dict(table[m]) for m in names},
                 "unsound_acceptances": len(unsound), "unsound_examples": unsound[:10],
                 "checker_disagreements": len(disagree), "disagreement_examples": disagree[:10]},
        sizes={"corpus": "lean/test/certificates (accepted/, rejected/)",
               "fresh": f"{N_SYM} symmetric (n<=6, p<=5, t<=p+6, d in [1,25]) and {N_NONSYM} non-symmetric "
                        "(n<=3, p<=3, t<=p+3, d, dbar in [1,15]) instances",
               "mutants": f"{len(MUTATIONS)} mutation kinds per accepted certificate, where applicable"},
        tests=["thm-9-1"],
        hypothesis="Theorem 9.1: a certificate whose obligations 1-4 hold lists exactly the Pareto front; a sound "
                   "checker therefore never accepts a false front.",
        explanation=f"{sum(t['mutants'] for t in table.values())} mutants; {sum(t['must_reject'] for t in table.values())} "
                    f"had to be rejected and {len(unsound)} were accepted. The checkers disagree on {len(disagree)} "
                    "mutants (allowed only where either verdict is correct).",
        figures=figures, binaries=[C.ZENO, C.LEAN_CHECK],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
