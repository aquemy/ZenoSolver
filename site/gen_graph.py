#!/usr/bin/env python3
"""Generate the claim graph and the history pages' artefacts from the git history.

    uv run --no-project --python 3.13 --with-editable "$CLAIMGRAPH_SRC" python site/gen_graph.py

(`bash site/build.sh` does this when the `claimgraph` package is available, and keeps the committed
artefacts otherwise.) It reads the Conventional Knowledge Commits of the repository and the claim
registry `claims.toml` with [claimgraph](https://github.com/hotherio/claimgraph), and writes into
`site/graph/`, which Quarto copies into `docs/graph/`:

* `claimgraph-viewer.html`: the interactive viewer (end-state graph and commit replay);
* `history-timeline.html`: the compact SVG timeline of the same replay;
* (the viewer embeds the graph and the replay frames; no separate JSON is published);

and `site/_history-table.md` (the knowledge-commit log) and `site/_graph-stats.md` (the counts
quoted on the pages).
"""

from __future__ import annotations

import tomllib
from collections import Counter
from pathlib import Path

import claimgraph as cg
from ckc_lint.data import profile_of
from claimgraph import export_html, svg_timeline
from claimgraph.build import read_git_dated
from claimgraph.emit import to_dict
from claimgraph.timeline import build_timeline

SITE = Path(__file__).resolve().parent
ROOT = SITE.parent
OUT = SITE / "graph"
REPO = "https://github.com/aquemy/ZenoSolver"
TITLE = "ZenoSolver"

STATUS_LABEL = {
    "math.machine-checked": "machine-checked",
    "math.proved-informal": "proof in the note",
    "math.conjectured": "conjectured",
    "math.disproved": "disproved",
}


def is_knowledge(commit) -> bool:
    """A knowledge commit: its type belongs to a CKC profile (proof, science, or shared), not to the
    plain Conventional Commits types (feat, fix, docs, ...)."""
    try:
        return bool(commit.type) and profile_of(commit.type) != "conventional"
    except (KeyError, ValueError):
        return False


def hide_paper_claims(graph) -> set[str]:
    """Drop from the site's view the claims of the earlier papers (`paper-*` in claims.toml) and
    the refutation nodes whose only purpose is to disprove them. Effective statuses are computed
    before, so the theory's own claims keep theirs. Returns the hidden node ids."""
    hidden = {nid for nid in graph.nodes if nid.startswith("paper-")}
    disproves: dict[str, set[str]] = {}
    for e in graph.edges:
        if e.relation == "Disproves":
            disproves.setdefault(e.source, set()).add(e.target)
    hidden |= {src for src, targets in disproves.items() if targets <= hidden}
    graph.nodes = {k: v for k, v in graph.nodes.items() if k not in hidden}
    graph.edges = [e for e in graph.edges if e.source not in hidden and e.target not in hidden]
    return hidden


def _mentions(value, hidden: set[str]) -> bool:
    if isinstance(value, str):
        # node ids, "claim:<id>" references, and replay edges written "source|Relation|target"
        parts = value.split("|") if value.count("|") == 2 else [value]
        return any(p.removeprefix("claim:").removeprefix("conjecture:") in hidden for p in parts)
    if isinstance(value, dict):
        return any(_mentions(v, hidden) for v in value.values())
    if isinstance(value, (list, tuple)):
        return any(_mentions(v, hidden) for v in value)
    return False


def frame_is_hidden(frame: dict, hidden: set[str]) -> bool:
    """A replay step whose focus is only hidden claims (a refutation of a paper's claim)."""
    focus = frame.get("focus")
    items = focus if isinstance(focus, (list, tuple)) else ([focus] if focus else [])
    return bool(items) and all(_mentions(f, hidden) for f in items)


def strip_frame(frame: dict, hidden: set[str]) -> dict:
    """Remove the hidden nodes from one replay step."""
    out = dict(frame)
    if isinstance(out.get("present"), list):
        out["present"] = [p for p in out["present"] if not _mentions(p, hidden)]
    if isinstance(out.get("edges"), list):
        out["edges"] = [e for e in out["edges"] if not _mentions(e, hidden)]
    if isinstance(out.get("state"), dict):
        out["state"] = {k: v for k, v in out["state"].items() if not _mentions(k, hidden)}
    focus = out.get("focus")
    if isinstance(focus, list):
        out["focus"] = [f for f in focus if not _mentions(f, hidden)]
    return out


def cell(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", " ").strip()


def history_table(frames: list[dict]) -> str:
    """The knowledge commits, oldest first: date, commit, subject (which starts with the type),
    and the claims touched."""
    rows = ["| # | Date | Commit | Subject | Claims touched |", "|--:|---|---|---|---|"]
    for k, fr in enumerate(frames, 1):
        sha = str(fr.get("hash") or "")
        short = sha[:7]
        link = f"[`{short}`]({REPO}/commit/{sha})" if sha else ""
        focus = fr.get("focus")
        items = focus if isinstance(focus, (list, tuple)) else ([focus] if focus else [])
        claims = ", ".join(f"`{str(s).split(':', 1)[-1]}`" for s in items if s) or "—"
        rows.append(f"| {k} | {str(fr.get('date', ''))[:10]} | {link} "
                    f"| {cell(str(fr.get('subject') or ''))} | {claims} |")
    return "\n".join(rows) + "\n"


def check_status_cache(nodes: list[dict]) -> None:
    """The blueprint's badges read the `status` field of claims.toml, a cache of the effective
    status. Fail if the history gives any claim another status, so the badges cannot drift."""
    cache = {slug: entry.get("status")
             for slug, entry in tomllib.loads((ROOT / "claims.toml").read_text(encoding="utf-8"))["claims"].items()}
    stale = sorted(f"{n['id']} (cache {cache[n['id']]}, history {n['effective_status']})"
                   for n in nodes if n["id"] in cache and cache[n["id"]] != n["effective_status"])
    if stale:
        raise SystemExit("graph: the status cache of claims.toml disagrees with the history for "
                         + ", ".join(stale) + "; regenerate it with `claimgraph status`")


def main() -> None:
    claims = ROOT / "claims.toml"
    if not claims.exists():
        raise SystemExit("graph: no claims.toml at the repository root")
    registry = cg.load_registry(str(claims))
    history = read_git_dated(str(ROOT))
    # Compact: only the knowledge commits. Plain feat/fix/docs/... commits would add a node per
    # scope (bench, cli, site, ...) and a replay frame each, with no claim status to show.
    dated = [d for d in history if is_knowledge(d.commit)]
    graph = cg.compute(cg.build_graph([d.commit for d in dated], registry))
    frames = build_timeline(dated, registry)
    hidden = hide_paper_claims(graph)
    frames = [strip_frame(fr, hidden) for fr in frames if not frame_is_hidden(fr, hidden)]
    for k, fr in enumerate(frames):
        fr["i"] = k
    payload = to_dict(graph, timeline=frames)

    OUT.mkdir(exist_ok=True)
    # The viewer embeds the payload; a separate JSON copy would double the size of docs/.
    (OUT / "claimgraph.json").unlink(missing_ok=True)
    (OUT / "claimgraph-viewer.html").write_text(
        export_html.render(payload, shape="page", title=TITLE), encoding="utf-8")
    (OUT / "history-timeline.html").write_text(
        svg_timeline.render(graph, frames, title=f"{TITLE}: history",
                            hint="Drag the slider through the knowledge commits; each claim's colour "
                                 "is its status as of that commit."),
        encoding="utf-8")
    (SITE / "_history-table.md").write_text(history_table(frames), encoding="utf-8")

    nodes = payload["nodes"]
    kinds = Counter(n["kind"] for n in nodes)
    claims_n = sum(v for k, v in kinds.items() if k not in ("formalize", "refute"))
    statuses = Counter(n["effective_status"] for n in nodes if n["kind"] not in ("formalize", "refute"))
    parts = [f"**{statuses[s]}** {label}" for s, label in STATUS_LABEL.items() if statuses.get(s)]
    relations = Counter(e["relation"] for e in payload["edges"])
    first = str(frames[0].get("date", ""))[:10] if frames else ""
    last = str(frames[-1].get("date", ""))[:10] if frames else ""
    (SITE / "_graph-stats.md").write_text(
        f"The graph has **{claims_n} claims**, {kinds.get('formalize', 0)} Lean declarations that "
        f"close them and {kinds.get('refute', 0)} refutations, joined by "
        + ", ".join(f"{v} `{k}`" for k, v in sorted(relations.items())) + " edges. "
        "By effective status, the claims are " + ", ".join(parts) + ". "
        f"The replay has **{len(frames)} knowledge commits**, "
        + (f"all of {first}" if first == last else f"from {first} to {last}") + "; the other "
        f"{len(history) - len(dated):,} commits of the history (features, fixes, documentation) are left "
        "out.\n",
        encoding="utf-8")
    check_status_cache(nodes)
    sizes = {p.name: p.stat().st_size for p in OUT.iterdir()}
    print(f"graph: {len(graph.nodes)} claims, {len(frames)} frames, {sizes}")


if __name__ == "__main__":
    main()
