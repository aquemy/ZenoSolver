"""E9, the linear family (Theorem 10.1): the default generator's front in closed form.

With d_i = r0 * i and c_i = alpha - beta * i (beta >= 0, alpha >= beta * n), Theorem 10.1 gives, with
s = 2t - p, kappa = ceil(s / p), q0 = floor(s / p) and rho = s - p * q0,

    F = {(alpha * s - beta * Phi(T), 2 * r0 * T) : kappa <= T <= n * kappa}   if beta > 0,
    F = {(alpha * s, 2 * r0 * kappa)}                                          if beta = 0,
    Phi(T) = (p - rho) * min(T, n * q0) + rho * min(T, n * (q0 + 1)),

with (n - 1) * kappa + 1 points when beta > 0, and L = E at every level, so the front holds under (S)
alone, whatever the central flights. The default generator (-C 3 -D 3, any -r) is this family with
alpha = r0 (n + 1) and beta = r0.

Pass: `zeno`'s front equals the closed form on every instance, and every certificate closes all its
gaps with the relaxation alone (no `forest` gap, so no use of (A1)).
"""

from __future__ import annotations

import random
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

NAME, CLAIM, SEED = "E9_linear_family", "exp-e9-linear-family", 0
N_GENERATOR, N_AFFINE = 300, 300
ANCHORS = [(100, 60, 10, 1090), (50, 60, 10, 540), (200, 3, 2, 399)]  # front sizes quoted in the note


def closed_form(n, t, p, r0, alpha, beta):
    s = 2 * t - p
    kappa = -(-s // p)
    q0, rho = divmod(s, p)
    if beta == 0:
        return [(alpha * s, 2 * r0 * kappa)]

    def phi(T):
        return (p - rho) * min(T, n * q0) + rho * min(T, n * (q0 + 1))

    return sorted((alpha * s - beta * phi(T), 2 * r0 * T) for T in range(kappa, n * kappa + 1))


def linear_params(inst):
    """(r0, alpha, beta) if the canonical instance is in the family, else None."""
    d, c, n = inst.d, inst.c, inst.n
    r0 = d[0]
    if r0 < 1 or any(d[i] != r0 * (i + 1) for i in range(n)):
        return None
    beta = c[0] - c[1] if n > 1 else 0
    alpha = c[0] + beta
    if beta < 0 or any(c[i] != alpha - beta * (i + 1) for i in range(n)) or alpha < beta * n:
        return None
    return r0, alpha, beta


def jobs(rng):
    out = []
    with tempfile.TemporaryDirectory() as tmp:
        for n, t, p, _ in ANCHORS:
            out.append(("generator", C.generated_instance(["-n", str(n), "-t", str(t), "-p", str(p)], Path(tmp))
                        .canonical()))
        for _ in range(N_GENERATOR):
            p = rng.randint(1, 10)
            t = rng.randint(p, 30)
            n = rng.randint(2, 40)
            r = rng.choice([1, 10])
            args = ["-n", str(n), "-t", str(t), "-p", str(p), "-C", "3", "-D", "3", "-r", str(r)]
            out.append(("generator", C.generated_instance(args, Path(tmp)).canonical()))
    for _ in range(N_AFFINE):
        p = rng.randint(1, 8)
        t = rng.randint(p, 25)
        n = rng.randint(2, 30)
        r0 = rng.randint(1, 7)
        beta = 0 if rng.random() < 0.1 else rng.randint(1, 6)
        alpha = beta * n + rng.randint(0, 40)
        d = tuple(r0 * i for i in range(1, n + 1))
        c = tuple(alpha - beta * i for i in range(1, n + 1))
        out.append(("affine", C.Instance(d, c, t, p)))
    return out


def run(job):
    family, inst = job
    params = linear_params(inst)
    with tempfile.TemporaryDirectory() as tmp:
        cert = Path(tmp) / "front.cert"
        front = C.run_zeno(inst, Path(tmp), "--certificate", str(cert), timeout=900).front
        forest = cert.read_text().count(" forest\n")
    expected = closed_form(inst.n, inst.t, inst.p, *params) if params else None
    return family, inst, params, front, expected, forest


def main() -> int:
    rng = random.Random(SEED)
    rows = C.pmap(run, jobs(rng))

    not_linear = [r[1].as_dict() for r in rows if r[2] is None]
    checked = [r for r in rows if r[2] is not None]
    differ = [{"family": r[0], "instance": r[1].as_dict(), "zeno_size": len(r[3]), "closed_form_size": len(r[4])}
              for r in checked if r[3] != r[4]]
    forest = [r[1].as_dict() for r in checked if r[5] > 0]
    anchors = {f"n{n}t{t}p{p}": {"zeno": len(rows[k][3]), "note": size} for k, (n, t, p, size) in enumerate(ANCHORS)}
    anchors_ok = all(v["zeno"] == v["note"] for v in anchors.values())
    passed = not differ and not forest and not not_linear and anchors_ok

    fig, ax = C.new_axes(figsize=(6.4, 4.4))
    for k, fam in enumerate(["generator", "affine"]):
        pts = [(r[1].n - 1) * -(-r[1].s // r[1].p) + 1 if r[2][2] > 0 else 1 for r in checked if r[0] == fam]
        got = [len(r[3]) for r in checked if r[0] == fam]
        ax.scatter(pts, got, s=16, alpha=0.6, color=C.PALETTE[k], edgecolors="none",
                   label=f"{fam}: {sum(1 for r in checked if r[0] == fam)} instances")
    top = max(len(r[3]) for r in checked)
    ax.plot([1, top], [1, top], color=C.MUTED, linewidth=0.8, linestyle="--", label="(n - 1) kappa + 1")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("front size predicted by Theorem 10.1")
    ax.set_ylabel("front size computed by zeno")
    ax.set_title("Linear family: zeno's front = the closed form")
    ax.legend(loc="upper left")
    C.verdict_badge(ax, passed, f"{len(differ)} differ, {len(forest)} need A1")
    figures = C.save_figure(fig, NAME, "linear_closed_form")

    result = C.Result(
        name=NAME, claim=CLAIM, seed=SEED, passed=passed,
        criterion="zeno's front equals the closed form of Theorem 10.1 point for point on every instance, every "
                  "certificate closes its gaps with the relaxation alone (no forest gap), and the front sizes "
                  "quoted in the note are reproduced",
        metrics={"instances": len(rows), "closed_form_checked": len(checked), "differ": len(differ),
                 "certificates_with_forest_gaps": len(forest), "not_in_family": len(not_linear),
                 "points_checked": sum(len(r[3]) for r in checked), "largest_front": top,
                 "beta_zero_instances": sum(r[2][2] == 0 for r in checked), "anchors": anchors,
                 "differences": differ[:10]},
        sizes={"generator": f"{N_GENERATOR} instances of -C 3 -D 3 with -r in {{1,10}}, n in 2..40, p in 1..10, "
                            f"t in p..30, plus the note's 3 anchors",
               "affine": f"{N_AFFINE} data files d_i = r0 i (r0 in 1..7), c_i = alpha - beta i (beta in 0..6, 10% "
                         "zero; alpha in [beta n, beta n + 40]), n in 2..30, p in 1..8, t in p..25"},
        tests=["thm-10-1"],
        hypothesis="Theorem 10.1: on the linear family L = E at every level and the front is the closed form, "
                   "exact under (S) alone.",
        explanation=f"{len(checked)} instances, {sum(len(r[3]) for r in checked):,} front points (up to {top}), all "
                    "equal to the closed form; no certificate needed the forest bound, so these fronts hold without "
                    "(A1). The note's sizes 1,090, 540 and 399 are reproduced.",
        figures=figures, binaries=[C.ZENO],
    )
    result.write()
    return C.announce(result)


if __name__ == "__main__":
    sys.exit(main())
