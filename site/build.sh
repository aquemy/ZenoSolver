#!/usr/bin/env bash
# Build the website into docs/, which GitHub Pages serves from master /docs.
#
#   bash site/build.sh            # query Lean (lean/ built with `lake build`)
#   bash site/build.sh --no-lean  # reuse site/lean-status.json
#
# Needs Python >= 3.11, Quarto, and XeLaTeX for docs/blueprint.pdf. A built `zeno`
# (build/release/zeno) refreshes the help text and the PDDL example; without one the committed
# copies are kept. The claim graph is rebuilt from the git history with the `claimgraph` package
# (Python 3.13, through uv) from $CLAIMGRAPH_SRC (default ~/projects/hother/claimgraph), or from the
# pip requirement in $CLAIMGRAPH_SPEC; without either the committed graph is kept.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"

blueprint_args=()
if [[ "${1:-}" == "--no-lean" ]]; then
    blueprint_args+=(--no-lean)
fi

python3 "$here/gen_blueprint.py" "${blueprint_args[@]+"${blueprint_args[@]}"}"
python3 "$here/gen_pages.py"

claimgraph_src="${CLAIMGRAPH_SRC:-$HOME/projects/hother/claimgraph}"
if command -v uv >/dev/null && [[ -d "$claimgraph_src" ]]; then
    uv run --no-project --python 3.13 --with-editable "$claimgraph_src" python "$here/gen_graph.py"
elif command -v uv >/dev/null && [[ -n "${CLAIMGRAPH_SPEC:-}" ]]; then
    uv run --no-project --python 3.13 --with "$CLAIMGRAPH_SPEC" python "$here/gen_graph.py"
else
    echo "graph: claimgraph not available; keeping the committed site/graph/" >&2
fi
sh "$here/fonts/fetch.sh"
quarto render "$here"
touch "$root/docs/.nojekyll"

# docs/ must be self-contained: no link may leave it (repository files are linked on GitHub).
if grep -rlE '(href|src)="(\.\./)+(doc|lean|src|include|bench|tests|site)/' "$root/docs" --include='*.html'; then
    echo "build: the pages above link outside docs/" >&2
    exit 1
fi
for f in blueprint.pdf graph/claimgraph-viewer.html graph/history-timeline.html; do
    test -f "$root/docs/$f" || { echo "build: docs/$f is missing" >&2; exit 1; }
done
echo "site: docs/ is ready ($(find "$root/docs" -type f | wc -l | tr -d ' ') files)"
