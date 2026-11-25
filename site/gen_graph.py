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

Claims are shown by their `label` (the current number in the theory note) next to their slug.
Archived claims (`removed` in claims.toml: results that revision 3 of the note removed or merged)
are left out of the graph and of the replay; the commits that touched them stay in the log. The
status cache of claims.toml is checked against the history for every claim, archived or not.
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


def hide_claims(graph, archived: set[str]) -> set[str]:
    """Drop from the site's view the claims of the earlier papers (`paper-*` in claims.toml), the
    archived claims, and the refutations and Lean declarations whose only purpose is to disprove
    or close them. Effective
    statuses are computed before, so the theory's own claims keep theirs. Returns the hidden node
    ids. An archived experiment `exp-<id>-…` takes its commit-level node `<id>` with it."""
    short = {slug.split("-")[1] for slug in archived if slug.startswith("exp-")}
    hidden = {nid for nid in graph.nodes
              if nid.startswith("paper-") or nid in archived or nid in short}
    # the refutations of hidden claims, and the Lean declarations that only close hidden claims
    disproves: dict[str, set[str]] = {}
    closes: dict[str, set[str]] = {}
    for e in graph.edges:
        if e.relation == "Disproves":
            disproves.setdefault(e.source, set()).add(e.target)
        elif e.relation == "Closes" and graph.nodes[e.source].kind == "formalize":
            closes.setdefault(e.source, set()).add(e.target)
    hidden |= {src for src, targets in disproves.items() if targets <= hidden}
    hidden |= {src for src, targets in closes.items() if targets <= hidden}
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


def history_table(frames: list[dict], labels: dict[str, str], archived: set[str]) -> str:
    """The knowledge commits, oldest first: date, commit, subject (which starts with the type),
    and the claims touched, by slug with their current label (archived claims marked so)."""
    def claim(item) -> str:
        sid = str(item).split(":", 1)[-1]
        if sid in archived:
            return f"`{sid}` (archived)"
        return f"`{sid}` ({labels[sid]})" if sid in labels else f"`{sid}`"

    rows = ["| # | Date | Commit | Subject | Claims touched |", "|--:|---|---|---|---|"]
    for k, fr in enumerate(frames, 1):
        sha = str(fr.get("hash") or "")
        short = sha[:7]
        link = f"[`{short}`]({REPO}/commit/{sha})" if sha else ""
        focus = fr.get("focus")
        items = focus if isinstance(focus, (list, tuple)) else ([focus] if focus else [])
        claims = ", ".join(claim(s) for s in items if s) or "—"
        rows.append(f"| {k} | {str(fr.get('date', ''))[:10]} | {link} "
                    f"| {cell(str(fr.get('subject') or ''))} | {claims} |")
    return "\n".join(rows) + "\n"


def check_status_cache(graph, claims: dict[str, dict]) -> None:
    """The blueprint's badges read the `status` field of claims.toml, a cache of the effective
    status. Fail if the history gives any claim, archived or not, another status, so the badges
    cannot drift."""
    stale = sorted(f"{slug} (cache {entry.get('status')}, history "
                   f"{graph.nodes[slug].effective_status if slug in graph.nodes else 'none'})"
                   for slug, entry in claims.items()
                   if (graph.nodes[slug].effective_status if slug in graph.nodes else None)
                   != entry.get("status"))
    if stale:
        raise SystemExit("graph: the status cache of claims.toml disagrees with the history for "
                         + ", ".join(stale) + "; regenerate it with `claimgraph status`")


def main() -> None:
    claims = ROOT / "claims.toml"
    if not claims.exists():
        raise SystemExit("graph: no claims.toml at the repository root")
    registry = cg.load_registry(str(claims))
    archived = {slug for slug, entry in registry.items() if "removed" in entry}
    labels = {slug: entry["label"] for slug, entry in registry.items()
              if "label" in entry and slug not in archived}
    history = read_git_dated(str(ROOT))
    # Compact: only the knowledge commits. Plain feat/fix/docs/... commits would add a node per
    # scope (bench, cli, site, ...) and a replay frame each, with no claim status to show.
    dated = [d for d in history if is_knowledge(d.commit)]
    graph = cg.compute(cg.build_graph([d.commit for d in dated], registry))
    check_status_cache(graph, registry)
    frames = build_timeline(dated, registry)
    papers = {nid for nid in graph.nodes if nid.startswith("paper-")}
    before = {nid: node.effective_status for nid, node in graph.nodes.items()}
    hidden = hide_claims(graph, archived)
    # Recompute without the archived claims, so that nothing shown takes its effective status from
    # a hidden node (the commit-level node of experiment E10 depended on Conjecture 10.2). The
    # ledger's claims must keep the status the history gives them.
    cg.compute(graph)
    moved = sorted(nid for nid in registry if nid in graph.nodes
                   and graph.nodes[nid].effective_status != before[nid])
    if moved:
        raise SystemExit(f"graph: hiding the archived claims changes the status of {moved}")
    # The log keeps the commits on archived claims; the replay leaves them out.
    log = [fr for fr in frames if not frame_is_hidden(fr, papers)]
    frames = [strip_frame(fr, hidden) for fr in log if not frame_is_hidden(fr, hidden)]
    for k, fr in enumerate(frames):
        fr["i"] = k
    # Show the current label: in the statement the viewer prints, and as the timeline's node name.
    for nid, node in graph.nodes.items():
        if nid in labels:
            node.label = labels[nid]
            if node.statement and not node.statement.startswith(labels[nid]):
                node.statement = f"{labels[nid]}: {node.statement}"
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
    (SITE / "_history-table.md").write_text(history_table(log, labels, archived), encoding="utf-8")

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
        f"out, and so are the {len(archived)} claims that revision 3 of the theory note archived.\n",
        encoding="utf-8")
    sizes = {p.name: p.stat().st_size for p in OUT.iterdir()}
    print(f"graph: {len(graph.nodes)} claims, {len(frames)} frames, {sizes}")


if __name__ == "__main__":
    main()
