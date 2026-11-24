#!/usr/bin/env python3
"""Generate the data-driven partials of the website (everything but the blueprint).

    python3 site/gen_pages.py [--zeno build/release/zeno]

* `site/_results-*.md`: the figures of the results page, computed from the committed baselines
  (`bench/baselines/*/apple-m4-max/*.json`), never typed by hand;
* `site/solver/_zeno-help.md`: the output of `zeno --help`, when a built `zeno` is found (the
  committed copy is kept otherwise);
* `site/solver/_certificate-format.md`: `doc/certificate-format.md` without its title;
* `site/instances/_suites*.md`, `_golden.md`, `_table1.md`: the benchmark suites
  (`bench/instances/*.txt`), the golden instances (`tests/golden`) and the Table 1 front sizes;
* `site/instances/_pddl-*.md`: the PDDL domain file, and a problem written by `zeno pddl`.
"""

from __future__ import annotations

import argparse
import json
import re
import statistics
import subprocess
import tempfile
from pathlib import Path

SITE = Path(__file__).resolve().parent
ROOT = SITE.parent
BASE = ROOT / "bench" / "baselines"
MACHINE = "apple-m4-max"
SUITES = ["quick", "paper-table1", "regimes", "families", "adversarial",
          "scaling-n", "scaling-t", "scaling-p", "scaling-D", "scaling-distinct"]


def load(solver: str, name: str) -> tuple[dict, list[dict]]:
    data = json.loads((BASE / solver / MACHINE / f"{name}.json").read_text())
    return data["context"], data["benchmarks"]


def seconds(ms: float) -> str:
    if ms < 1000:
        return f"{ms:.0f} ms" if ms >= 10 else f"{ms:.1f} ms"
    return f"{ms / 1000:.1f} s" if ms < 100_000 else f"{ms / 1000:.0f} s"


def suite_args() -> dict[str, str]:
    """name -> zeno arguments, from bench/instances/*.txt."""
    out = {}
    for suite in SUITES:
        for line in (ROOT / "bench" / "instances" / f"{suite}.txt").read_text().splitlines():
            if line.strip() and not line.startswith("#"):
                name, args = line.split("|", 1)
                out[f"{suite}/{name}"] = args.replace("@DATA@/", "")
    return out


def results() -> None:
    _, zeno = load("zeno", "zeno")
    zctx = load("zeno", "zeno")[0]
    fctx, front = load("lean", "zeno-front-suite")
    _, check = load("lean", "zeno-check-suite")
    by = lambda rows: {r["name"]: r for r in rows}
    z, f, c = by(zeno), by(front), by(check)
    n = len(zeno)

    def ok(rows, key="status", good="ok"):
        return [r for r in rows if r.get(key) == good]

    zt = [r["real_time"] for r in ok(zeno)]
    ft = [r["real_time"] for r in front if r.get("verdict") == "accepted"]
    ct = [r["real_time"] for r in ok(check, "verdict", "accepted")]
    slow_z = max(zeno, key=lambda r: r["real_time"])
    slow_f = max(front, key=lambda r: r["real_time"])
    slow_c = max(check, key=lambda r: r["real_time"])
    equal = sum(1 for r in front if r.get("front_equals_zeno"))
    lines = [
        "| Solver | Finished | Median | Slowest | Conditions |",
        "|---|---|---|---|---|",
        f"| `zeno` (C++, all cores) | {len(zt)} of {n} | {seconds(statistics.median(zt))} | "
        f"{seconds(slow_z['real_time'])} (`{slow_z['name']}`) | {zctx.get('zs_timeout_s', 30):.0f} s timeout, median of 3 runs |",
    ]
    lines.append(f"| Lean `zeno-front` (verified solver) | {len(ft)} of {n} | {seconds(statistics.median(ft))} | "
                 f"{seconds(slow_f['real_time'])} (`{slow_f['name']}`) | 60 s timeout, one run; front equal to "
                 f"`zeno front` on {equal} of {n} |")
    lines.append(f"| Lean `zeno-check` on `zeno`'s certificates | {len(ct)} of {n} accepted | "
                 f"{seconds(statistics.median(ct))} | {seconds(slow_c['real_time'])} (`{slow_c['name']}`) | "
                 f"{seconds(sum(ct))} in total |")
    (SITE / "_results-summary.md").write_text("\n".join(lines) + "\n")

    # per instance
    args = suite_args()
    rows = ["| Instance | Arguments | Front | `zeno` | `zeno-front` | `zeno-check` | Certificate |",
            "|---|---|--:|--:|--:|--:|--:|"]
    for r in zeno:
        name = r["name"]
        fr = f.get(name, {})
        fr_t = seconds(fr["real_time"]) + ("" if fr.get("front_equals_zeno") else " (differs)") if fr else "—"
        ch = c.get(name, {})
        ch_t = seconds(ch["real_time"]) if ch.get("verdict") == "accepted" else ch.get("verdict", "—")
        size = ch.get("certificate_bytes")
        size_s = f"{size / 1e6:.1f} MB" if size and size >= 1e6 else (f"{size / 1e3:.0f} kB" if size else "—")
        rows.append(f"| `{name}` | `{args.get(name, r.get('arguments', ''))}` | {r.get('front_size', '')} | "
                    f"{seconds(r['real_time'])} | {fr_t} | {ch_t} | {size_s} |")
    (SITE / "_results-instances.md").write_text("\n".join(rows) + "\n")

    # the Lean checker on its own test sets
    sets = [("zeno-check", "test certificates (`lean/test/certificates`, versions 1 and 2)"),
            ("zeno-check-v2", "version 2 certificates of random non-symmetric instances"),
            ("zeno-check-many-cities", "certificates whose cities all survive the dominance merge")]
    def verdicts(b: list[dict]) -> str:
        acc = sum(1 for x in b if x.get("verdict") == "accepted")
        text = f"{acc} accepted, {len(b) - acc} rejected"
        # the test set is split into accepted/ and rejected/ by expected verdict
        expected = [x for x in b if x["name"].split("/")[0] in ("accepted", "rejected")]
        if expected and len(expected) == len(b):
            got = lambda x: "accepted" if x.get("verdict") == "accepted" else "rejected"
            wrong = [x["name"] for x in b if x["name"].split("/")[0] != got(x)]
            text += " (each as expected)" if not wrong else f" ({len(wrong)} unexpected)"
        return text

    out = ["| Set | Certificates | Verdicts | Median | Slowest |", "|---|--:|---|--:|---|"]
    for name, what in sets:
        _, b = load("lean", name)
        slow = max(b, key=lambda x: x["real_time"])
        out.append(f"| Lean `zeno-check`, {what} | {len(b)} | {verdicts(b)} | "
                   f"{seconds(statistics.median(x['real_time'] for x in b))} | "
                   f"{seconds(slow['real_time'])} (`{slow['name']}`) |")
    _, cpp = load("zeno", "zeno-check-cpp")
    slow = max(cpp, key=lambda x: x["real_time"])
    out.append(f"| C++ `zeno check`, test certificates | {len(cpp)} | {verdicts(cpp)} | "
               f"{seconds(statistics.median(x['real_time'] for x in cpp))} | "
               f"{seconds(slow['real_time'])} (`{slow['name']}`) |")
    (SITE / "_results-checker.md").write_text("\n".join(out) + "\n")

    # time against the level range: -n 10 -t 8 -p 3 -C 2 -D 2 -r R (bm-core)
    _, core = load("zeno", "bm-core")
    rows = ["| `-r` | Levels | Levels evaluated | Front size | Median time |", "|--:|--:|--:|--:|--:|"]
    for x in core:
        if x["name"].startswith("BM_SolveLargeDurations/") and x.get("aggregate_name") == "median":
            r = int(x["name"].split("/")[1].split("_")[0])
            ms = x["real_time"] * {"ms": 1, "us": 1e-3, "ns": 1e-6}[x["time_unit"]]
            rows.append(f"| {r:,} | {int(x['levels']):,} | {int(x['evaluations']):,} | "
                        f"{int(x['front_size'])} | {seconds(ms)} |")
    (SITE / "_results-largedurations.md").write_text("\n".join(rows) + "\n")

    dates = sorted({ctx["date"][:10] for ctx in (zctx, fctx)})
    (SITE / "_results-meta.md").write_text(
        f"Apple M4 Max, 16 cores, macOS, Release builds; recorded {', '.join(dates)}. "
        f"Source: `bench/baselines/*/{MACHINE}/`.\n")


def zeno_help(exe: Path | None) -> None:
    target = SITE / "solver" / "_zeno-help.md"
    candidates = [exe] if exe else [ROOT / "build" / p / "zeno" for p in ("release", "bench", "default")]
    for c in candidates:
        if c and c.exists():
            text = subprocess.run([str(c), "--help"], capture_output=True, text=True, check=True).stdout
            target.write_text("```text\n$ zeno --help\n" + text.rstrip() + "\n```\n")
            print(f"pages: zeno --help from {c}")
            return
    if not target.exists():
        raise SystemExit("pages: no built zeno and no committed solver/_zeno-help.md")
    print("pages: no built zeno; keeping solver/_zeno-help.md")


def certificate_format() -> None:
    text = (ROOT / "doc" / "certificate-format.md").read_text().splitlines()
    if text and text[0].startswith("# "):
        text = text[1:]
    # nest the document's sections under the page's "The specification"
    fence = False
    for k, line in enumerate(text):
        if line.startswith("```"):
            fence = not fence
        elif not fence and line.startswith("#"):
            text[k] = "#" + line
    (SITE / "solver" / "_certificate-format.md").write_text("\n".join(text).lstrip() + "\n")


def comments(path: Path) -> list[str]:
    return [l[1:].strip() for l in path.read_text().splitlines() if l.startswith("#")]


def suites() -> None:
    """The benchmark suites and the golden instances, from their files."""
    _, zeno = load("zeno", "zeno")
    sizes = {r["name"]: r.get("front_size") for r in zeno}
    out = ["| Suite | Instances | Content (from the file's header) |", "|---|--:|---|"]
    detail = []
    for suite in SUITES:
        path = ROOT / "bench" / "instances" / f"{suite}.txt"
        entries = [l.split("|", 1) for l in path.read_text().splitlines() if l.strip() and not l.startswith("#")]
        head = " ".join(c for c in comments(path)[1:])  # the first line documents the syntax
        head = re.sub(r"Table 1 of [^:]*: ", "", head)  # the site does not cite the earlier papers
        out.append(f"| [`{suite}`](#suite-{suite}) | {len(entries)} | {head} |")
        detail += [f"### `{suite}` {{#suite-{suite}}}", "", "| Name | Arguments | Front size |", "|---|---|--:|"]
        for name, args in entries:
            detail.append(f"| `{name}` | `{args.replace('@DATA@/', '')}` | {sizes.get(f'{suite}/{name}', '')} |")
        detail.append("")
    total = sum(int(l.split("|")[2]) for l in out[2:])
    out.append(f"| **all** | **{total}** | |")
    (SITE / "instances" / "_suites.md").write_text("\n".join(out) + "\n")
    (SITE / "instances" / "_suites-detail.md").write_text("\n".join(detail) + "\n")

    golden = ROOT / "tests" / "golden"
    rows = ["| Name | Arguments | Front size |", "|---|---|--:|"]
    for line in (golden / "instances.txt").read_text().splitlines():
        if line.strip() and not line.startswith("#"):
            name, args = line.split("|", 1)
            front = golden / "fronts" / f"{name}.front"
            size = sum(1 for l in front.read_text().splitlines() if l.strip()) if front.exists() else "—"
            rows.append(f"| `{name}` | `{args.replace('@DATA@/', '')}` | {size} |")
    (SITE / "instances" / "_golden.md").write_text("\n".join(rows) + "\n")

    # Table 1 of EvoCOP 2015: -n N -t N -p 2 has (N - 1)^2 + 1 points (Theorem 10.1)
    rows = ["| $N$ | $(N-1)^2+1$ | `zeno` front size (`bench/baselines`) |", "|--:|--:|--:|"]
    for r in zeno:
        if r["name"].startswith("paper-table1/"):
            n = int(r["name"].split("/n")[1].split("t")[0])
            mark = "" if r["front_size"] == (n - 1) ** 2 + 1 else " (differs)"
            rows.append(f"| {n} | {(n - 1) ** 2 + 1} | {r['front_size']}{mark} |")
    (SITE / "instances" / "_table1.md").write_text("\n".join(rows) + "\n")


def pddl(exe: Path | None) -> None:
    domain = (ROOT / "pddl" / "multi-zeno-travel.pddl").read_text()
    (SITE / "instances" / "_pddl-domain.md").write_text("```lisp\n" + domain.rstrip() + "\n```\n")
    target = SITE / "instances" / "_pddl-problem.md"
    candidates = [exe] if exe else [ROOT / "build" / p / "zeno" for p in ("release", "bench", "default")]
    for c in candidates:
        if c and c.exists():
            with tempfile.TemporaryDirectory() as tmp:
                out = Path(tmp) / "example.pddl"
                subprocess.run([str(c), "pddl", "-n", "2", "-t", "2", "-p", "1", "-O", str(out)], check=True)
                text = out.read_text()
            target.write_text("```text\n$ zeno pddl -n 2 -t 2 -p 1 -O example.pddl\n```\n\n```lisp\n"
                              + text.rstrip() + "\n```\n")
            return
    if not target.exists():
        raise SystemExit("pages: no built zeno and no committed instances/_pddl-problem.md")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--zeno", type=Path, help="path of a built zeno (default: build/*/zeno)")
    a = ap.parse_args()
    (SITE / "solver").mkdir(exist_ok=True)
    (SITE / "instances").mkdir(exist_ok=True)
    results()
    zeno_help(a.zeno)
    certificate_format()
    suites()
    pddl(a.zeno)
    print("pages: results, help, certificate format, suites and PDDL written")


if __name__ == "__main__":
    main()
