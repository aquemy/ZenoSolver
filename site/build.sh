#!/usr/bin/env bash
# Build the website into docs/, which GitHub Pages serves from master /docs.
#
#   bash site/build.sh            # query Lean (lean/ built with `lake build`)
#   bash site/build.sh --no-lean  # reuse site/lean-status.json
#
# Needs Python >= 3.11, Quarto, and XeLaTeX for docs/blueprint.pdf. A built `zeno`
# (build/release/zeno) refreshes the help text and the PDDL example; without one the committed
# copies are kept.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"

blueprint_args=()
if [[ "${1:-}" == "--no-lean" ]]; then
    blueprint_args+=(--no-lean)
fi

python3 "$here/gen_blueprint.py" "${blueprint_args[@]+"${blueprint_args[@]}"}"
python3 "$here/gen_pages.py"
sh "$here/fonts/fetch.sh"
quarto render "$here"
touch "$root/docs/.nojekyll"

# docs/ must be self-contained: no link may leave it (repository files are linked on GitHub).
if grep -rlE '(href|src)="(\.\./)+(doc|lean|src|include|bench|tests|site)/' "$root/docs" --include='*.html'; then
    echo "build: the pages above link outside docs/" >&2
    exit 1
fi
test -f "$root/docs/blueprint.pdf" || { echo "build: docs/blueprint.pdf is missing" >&2; exit 1; }
echo "site: docs/ is ready ($(find "$root/docs" -type f | wc -l | tr -d ' ') files)"
