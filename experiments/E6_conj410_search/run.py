"""E6, targeted search for counterexamples to the converse without (A1) (now Theorem 4.4).

Under (S) alone, central flights may be shorter than a detour through a hub, so the converse under
(A1) (Theorem 4.7 of revision 2) does not apply. The note now proves the converse under the hub
triangles (H), which (AΔ) implies (Theorem 4.4; Conjecture 4.10, then Theorem 4.10, of revision 2),
and Lean checks it; this search is independent of that proof. A plan can beat the
admissible-partition front E only where the relaxation L, valid for every plan under (S) alone
(Lemma 3.5), lies strictly below E: the gaps that a certificate must mark `forest`. Everywhere else
L = E closes the gap without the converse.

The search draws random tiny symmetric instances, keeps those whose certificate has a `forest` gap,
and computes their true front with the shortest central flights the triangle inequality allows
(`truth ... tight`: every central flight a -> b lasts |d_a - d_b|, up to s + 2 landings). A
counterexample is a plan inside a forest gap (makespan below the next point) cheaper than E.

This is a targeted search, not a proof: it reports how many gaps were tested and how many
counterexamples were found. Its result stands on its own, with or without the written proof.

Pass: 0 counterexamples among the forest gaps tested.
"""

from __future__ import annotations

import random
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

NAME, CLAIM, SEED = "E6_conj410_search", "exp-e6-conj410-search", 0
TRIALS = 100_000
TRUTH_TIMEOUT = 900


def draw(rng):
    p = rng.randint(2, 3)
    t = rng.randint(p + 1, 6)
    n = rng.randint(2, 3)
    d = sorted(rng.randint(1, 9) for _ in range(n))
    c = [rng.randint(1, 30) for _ in range(n)]
    return C.Instance(tuple(d), tuple(c), t, p)


def screen(inst):
    """zeno's front and the indices (by increasing makespan) of the gaps its certificate marks forest."""
    with tempfile.TemporaryDirectory() as tmp:
        cert = Path(tmp) / "front.cert"
        front = C.run_zeno(inst, Path(tmp), "--certificate", str(cert)).front
        text = cert.read_text()
    gaps = [line.split() for line in text.split("lower-bounds")[1].splitlines()[1:] if line.strip() != "end"]
    forest = [int(g[0]) - 1 for g in gaps if len(g) > 1 and g[1] == "forest"]
    return front, forest


def test(job):
    inst, front, forest = job
    truth = C.truth_front(inst, central="tight", extra=2, timeout=TRUTH_TIMEOUT)
    if truth is None:
        return inst, None
    by_m = sorted(front, key=lambda pt: pt[1])
    out = []
    for i in forest:
        cost, next_m = by_m[i][0], by_m[i + 1][1]
        inside = [(c, m) for c, m in truth if m < next_m]
        best = min((c for c, _ in inside), default=None)
        out.append({"gap": i + 1, "E_cost": cost, "next_makespan": next_m, "cheapest_plan_in_gap": best,
                    "counterexample": best is not None and best < cost})
    return inst, out


def main() -> int:
    rng = random.Random(SEED)
    insts = [draw(rng) for _ in range(TRIALS)]
    screened = C.pmap(screen, insts)
    candidates = [(inst, front, forest) for inst, (front, forest) in zip(insts, screened) if forest]
    tested = C.pmap(test, candidates)

    gaps = [(inst, g) for inst, res in tested if res is not None for g in res]
    timeouts = sum(res is None for _, res in tested)
    cex = [{"instance": inst.as_dict(), **g} for inst, g in gaps if g["counterexample"]]
    passed = not cex and len(gaps) > 0

    missing = [{"instance": inst.as_dict(), **g} for inst, g in gaps if g["cheapest_plan_in_gap"] is None]
    passed = passed and not missing  # E's own point lies in the gap, so the exhaustive search must find a plan
    fig, ax = C.new_axes(figsize=(6.4, 4.4))
    xs = [g["E_cost"] for _, g in gaps if g["cheapest_plan_in_gap"] is not None]
    ys = [g["cheapest_plan_in_gap"] for _, g in gaps if g["cheapest_plan_in_gap"] is not None]
    lim = (min(xs + ys) - 5, max(xs + ys) + 5) if gaps else (0, 1)
    ax.plot(lim, lim, color=C.MUTED, linewidth=0.8, linestyle="--", label="plan as cheap as E")
    ax.scatter(xs, ys, s=16, alpha=0.6, color=C.PALETTE[0], edgecolors="none",
               label=f"{len(gaps)} forest gaps (L < E) tested")
    ax.fill_between(lim, [lim[0]] * 2, lim, color=C.CRITICAL, alpha=0.06, label="counterexample region")
    ax.set_xlim(lim)
    ax.set_ylim(lim)
    ax.set_xlabel("E: cheapest admissible partition in the gap")
    ax.set_ylabel("cheapest plan in the gap, shortest central flights")
    ax.set_title(f"Converse without (A1), targeted search: {len(candidates)} of {TRIALS:,} instances have a "
                 "forest gap", fontsize=9.5)
    ax.legend(loc="upper left")
    C.verdict_badge(ax, passed, f"{len(cex)} counterexamples")
    figures = C.save_figure(fig, NAME, "conj410_gaps")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="no plan with the shortest central flights the triangle inequality allows lies inside a forest "
                  "gap (L < E) and costs less than E (0 counterexamples); a targeted search, not a proof",
        metrics={"instances_drawn": TRIALS, "instances_with_forest_gap": len(candidates),
                 "instances_tested": len(candidates) - timeouts, "truth_timeouts": timeouts,
                 "forest_gaps_tested": len(gaps), "counterexamples": len(cex),
                 "gaps_without_any_plan": len(missing),
                 "gaps_where_a_plan_matches_E": sum(g["cheapest_plan_in_gap"] == g["E_cost"] for _, g in gaps),
                 "counterexample_list": cex[:10]},
        sizes={"instances": f"{TRIALS:,} random symmetric instances, n in 2..3, p in 2..3, t in p+1..6, "
                            "d sorted in [1,9], c in [1,30]",
               "truth": f"central flights |d_a - d_b|, up to s+2 landings, timeout {TRUTH_TIMEOUT} s"},
        tests=["thm-4-10"],  # formerly conj-4-10
        hypothesis="Theorem 4.4 (Conjecture 4.10 of revision 2): under (S) and (AΔ), without (A1), every plan is still "
                   "weakly dominated by an admissible partition. A counterexample can only sit in a gap where L < E.",
        explanation=f"{len(candidates)} of {TRIALS:,} instances have a forest gap; on the "
                    f"{len(candidates) - timeouts} the exhaustive search finished, {len(gaps)} gaps were tested "
                    f"and {len(cex)} contain a plan cheaper than E. A targeted search on tiny instances, "
                    "independent of the written proof of Theorem 4.4.",
        figures=figures, binaries=[C.ZENO, C.check_program("truth")],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
