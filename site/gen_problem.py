#!/usr/bin/env python3
"""Generate the data of the Problem page from zeno.

    python3 site/gen_problem.py [--zeno build/release/zeno]

Runs `zeno generate` and `zeno --plans` on the example instance (`site/problem/example.dat`,
n = 3, t = 3, p = 2) and writes

* `site/problem/plans.json`: the instance (durations, costs), its Pareto front, and for every
  front point the plan zeno prints (one route per plane, legs `from->to[depart,arrive]pK`), with
  its landings and its hand-offs (a passenger who changes planes);
* `site/_problem-example.md`: the instance and its front as Markdown tables, included by
  `problem.qmd`, so the page states the numbers without JavaScript.

Nothing is typed: every number comes from zeno. Each plan is checked against the instance: legs
chain in time, last the duration of their flight, carry each passenger from C_I to C_G at most one
at a time, and give back the cost (landing costs summed) and makespan (last arrival) of its front
point.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

SITE = Path(__file__).resolve().parent
ROOT = SITE.parent
DATA = "site/problem/example.dat"
N, T, P = 3, 3, 2
OUT = SITE / "problem" / "plans.json"
PARTIAL = SITE / "_problem-example.md"

LEG = re.compile(r"(CI|CG|c\d+)->(CI|CG|c\d+)\[(\d+),(\d+)\](?:p(\d+))?$")
HEAD = re.compile(r"# cost (\d+), makespan (\d+)$")


def zeno(binary: str, *args: str) -> str:
    return subprocess.run([binary, *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout


def instance(binary: str) -> dict:
    """Durations and costs, as `zeno generate` writes them: durations then costs (2 lines), or
    C_I-side durations, C_G-side durations, costs (3 lines), then optionally a central block."""
    lines = [l.split() for l in zeno(binary, "generate", "-n", str(N), "-t", str(T), "-p", str(P),
                                     "-d", DATA).splitlines() if l.strip()]
    cut = next((i for i, l in enumerate(lines) if l == ["central"]), len(lines))
    rows = [[int(x) for x in l] for l in lines[:cut]]
    d, dbar, c = (rows[0], rows[0], rows[1]) if len(rows) == 2 else rows[:3]
    central = [[int(x) for x in l] for l in lines[cut + 1:]] if cut < len(lines) else None
    return {"n": N, "t": T, "p": P, "d": d, "dbar": dbar, "c": c, "central": central}


def duration(inst: dict, a: str, b: str) -> int:
    hub = {"CI": inst["d"], "CG": inst["dbar"]}
    if a in hub:
        return hub[a][int(b[1:]) - 1]
    if b in hub:
        return hub[b][int(a[1:]) - 1]
    i, j = int(a[1:]) - 1, int(b[1:]) - 1
    if inst["central"]:
        return inst["central"][i][j]
    m = lambda k: max(inst["d"][k], inst["dbar"][k])  # noqa: E731, zeno's default central table
    return m(i) + m(j) + 100


def parse_plans(text: str) -> tuple[list[list[int]], list[dict]]:
    front, plans = [], []
    for line in text.splitlines():
        parts = line.split()
        if not parts:
            continue
        if len(parts) == 2 and all(p.isdigit() for p in parts) and not plans:
            front.append([int(parts[0]), int(parts[1])])
        elif m := HEAD.match(line):
            plans.append({"cost": int(m[1]), "makespan": int(m[2]), "planes": []})
        elif line.startswith("plane "):
            k, legs = line.split(":", 1)
            assert int(k.split()[1]) == len(plans[-1]["planes"]) + 1, line
            route = []
            for tok in legs.split():
                m = LEG.match(tok)
                assert m, f"unparsed leg {tok!r}"
                route.append({"from": m[1], "to": m[2], "dep": int(m[3]), "arr": int(m[4]),
                              "pax": int(m[5]) if m[5] else None})
            plans[-1]["planes"].append(route)
    return front, plans


def check_and_annotate(inst: dict, plan: dict) -> None:
    """Check the plan against the instance and add its landings and hand-offs."""
    cost, last, journeys = 0, 0, {}
    plan["landings"] = []
    for k, route in enumerate(plan["planes"], 1):
        at, free = "CI", 0
        for leg in route:
            assert leg["from"] == at and leg["dep"] >= free, (k, leg)
            assert leg["arr"] - leg["dep"] == duration(inst, leg["from"], leg["to"]), (k, leg)
            at, free = leg["to"], leg["arr"]
            if at.startswith("c"):
                cost += inst["c"][int(at[1:]) - 1]
                plan["landings"].append({"plane": k, "city": at, "time": leg["arr"],
                                         "cost": inst["c"][int(at[1:]) - 1]})
            if leg["pax"]:
                journeys.setdefault(leg["pax"], []).append({**leg, "plane": k})
        assert at == "CG", f"plane {k} ends in {at}"
        last = max(last, free)
    assert cost == plan["cost"] and last == plan["makespan"], (cost, last, plan["cost"], plan["makespan"])
    assert sorted(journeys) == list(range(1, inst["t"] + 1)), sorted(journeys)
    plan["handoffs"] = []
    for pax, legs in sorted(journeys.items()):
        legs.sort(key=lambda l: l["dep"])
        assert legs[0]["from"] == "CI" and legs[-1]["to"] == "CG", (pax, legs)
        for a, b in zip(legs, legs[1:]):
            assert a["to"] == b["from"] and b["dep"] >= a["arr"], (pax, a, b)
            if a["plane"] != b["plane"]:
                plan["handoffs"].append({"pax": pax, "city": a["to"], "from": a["plane"], "to": b["plane"],
                                         "drop": a["arr"], "pick": b["dep"]})
    plan["landings"].sort(key=lambda l: (l["time"], l["plane"]))


def partial(inst: dict, front: list[list[int]]) -> str:
    cities = " | ".join(f"city {i}" for i in range(1, inst["n"] + 1))
    sep = "|".join(["---"] * (inst["n"] + 1))
    rows = [f"| | {cities} |", f"|{sep}|",
            "| flight to or from a hub, $d_i$ | " + " | ".join(map(str, inst["d"])) + " |",
            "| landing cost, $c_i$ | " + " | ".join(map(str, inst["c"])) + " |"]
    if inst["dbar"] != inst["d"]:
        rows.insert(3, "| flight to $C_G$, $\\bar d_i$ | " + " | ".join(map(str, inst["dbar"])) + " |")
    pts = ", ".join(f"({c}, {m})" for c, m in front)
    return ("<!-- Generated by site/gen_problem.py from zeno; do not edit. -->\n\n"
            + "\n".join(rows) + "\n\n: The example instance, as `zeno generate` reads it from "
            f"`{DATA}`: $n = {inst['n']}$ central cities, $t = {inst['t']}$ passengers, "
            f"$p = {inst['p']}$ planes. {{#tbl-example}}\n\n"
            f"<p class=\"zs-front-static\">Front, as (cost, makespan): {pts}.</p>\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--zeno", default=str(ROOT / "build/release/zeno"))
    opt = ap.parse_args()
    inst = instance(opt.zeno)
    args = ["-n", str(N), "-t", str(T), "-p", str(P), "-d", DATA, "--plans"]
    front, plans = parse_plans(zeno(opt.zeno, *args))
    assert [[p["cost"], p["makespan"]] for p in plans] == front, "one plan per front point"
    for plan in plans:
        check_and_annotate(inst, plan)
    data = {"generator": "site/gen_problem.py",
            "command": "build/release/zeno " + " ".join(args),
            "instance": inst, "front": front, "plans": plans}
    OUT.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    PARTIAL.write_text(partial(inst, front))
    print(f"{OUT.relative_to(ROOT)}: {len(plans)} plans, "
          f"{sum(len(p['handoffs']) for p in plans)} hand-offs; {PARTIAL.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
