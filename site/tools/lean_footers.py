#!/usr/bin/env python3
"""Add Lean declarations to site/lean-status.json without building Lean.

    python3 site/tools/lean_footers.py [--ref origin/master]

When the Mathlib cache cannot be installed (it needs several GB), the blueprint can still cover
declarations newer than lean-status.json: their axioms are read from the `Axioms:` footers of the
`formalize` commits (literal `#print axioms` output, re-checked by CI's "Build and audit ZenoFront"
job on every push), and their source ranges from the Lean files. Each such entry is marked with
`provenance`, which the blueprint shows under the listing. A Lean-enabled run of gen_blueprint.py
replaces these entries with ones read from Lean itself.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

SITE = Path(__file__).resolve().parent.parent
ROOT = SITE.parent
STATUS = SITE / "lean-status.json"
FOOTER = re.compile(r"^Axioms: '([^']+)' depends on axioms: \[([^\]]*)\]\s*$")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s:({\[]+)")
TOP = re.compile(r"^(?:/--|@\[|theorem |lemma |def |abbrev |structure |inductive |instance |"
                 r"private |protected |noncomputable |namespace |end |section |open |variable |/-!|#)")


def footers(ref: str) -> dict[str, tuple[list[str], str]]:
    """name -> (axioms, commit) from the newest footer that states it."""
    out = subprocess.run(["git", "log", "--format=%H%x1f%B%x1e", ref], cwd=ROOT, capture_output=True,
                         text=True, check=True).stdout
    found: dict[str, tuple[list[str], str]] = {}
    for rec in out.split("\x1e"):
        if "\x1f" not in rec:
            continue
        sha, body = rec.split("\x1f", 1)
        for line in body.splitlines():
            m = FOOTER.match(line.strip())
            if m and m.group(1) not in found:
                axioms = [a.strip() for a in m.group(2).split(",") if a.strip()]
                found[m.group(1)] = (axioms, sha.strip())
    return found


def namespaces(lines: list[str], upto: int) -> list[str]:
    """The namespace at line `upto`: `namespace A.B` opens A and B, `section S` (named or not)
    opens a scope that adds nothing, and `end` closes the innermost scope."""
    stack: list[tuple[str, str]] = []  # (kind, name)
    for line in lines[:upto]:
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            stack.extend(("namespace", part) for part in m.group(1).split("."))
            continue
        m = re.match(r"^(?:noncomputable\s+)?section\b\s*(\S*)", line)
        if m:
            stack.append(("section", m.group(1)))
            continue
        m = re.match(r"^end\b\s*(\S*)\s*$", line)
        if m and stack:
            if stack[-1][0] == "section":
                stack.pop()
            else:
                for _ in (m.group(1).split(".") if m.group(1) else [""]):
                    if stack and stack[-1][0] == "namespace":
                        stack.pop()
    return [name for kind, name in stack if kind == "namespace"]


def locate(name: str) -> dict | None:
    for path in sorted((ROOT / "lean" / "ZenoFront").glob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m:
                continue
            full = ".".join(namespaces(lines, i) + [m.group(2)])
            if full != name:
                continue
            start = i
            while start > 0 and (lines[start - 1].startswith(("/--", "  ", "@[")) or lines[start - 1].endswith("-/")) \
                    and not lines[start - 1].startswith("-/") and lines[start - 1].strip():
                start -= 1
                if lines[start].startswith("/--"):
                    break
            end = i
            for j in range(i + 1, len(lines)):
                if TOP.match(lines[j]):
                    break
                if lines[j].strip():
                    end = j
            module = "ZenoFront." + path.stem
            kind = {"lemma": "theorem", "abbrev": "def"}.get(m.group(1), m.group(1))
            return {"name": name, "module": module, "kind": kind,
                    "range": {"start": [start + 1, 0], "end": [end + 1, len(lines[end])],
                              "name": [i + 1, line.index(m.group(2))]}}
    return None


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--ref", default="HEAD")
    args = ap.parse_args()
    status = json.loads(STATUS.read_text(encoding="utf-8"))
    added = []
    for name, (axioms, sha) in footers(args.ref).items():
        if name in status["decls"] and "provenance" not in status["decls"][name]:
            continue  # read from Lean itself: keep
        entry = locate(name)
        if entry is None:
            continue
        entry["axioms"] = axioms
        entry["provenance"] = {"source": "axioms from the CI-audited commit footer", "commit": sha}
        status["decls"][name] = entry
        added.append(name)
    STATUS.write_text(json.dumps(status, indent=1, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    print(f"lean_footers: {len(added)} declarations from commit footers: {', '.join(sorted(added))}")


if __name__ == "__main__":
    main()
