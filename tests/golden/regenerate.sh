#!/usr/bin/env bash
# Regenerate the golden Pareto fronts with the brute-force oracle.
# Usage: tests/golden/regenerate.sh <path/to/zenoOracle>
set -euo pipefail
oracle="${1:?usage: $0 <path/to/zenoOracle>}"
here="$(cd "$(dirname "$0")" && pwd)"
grep -v '^#' "$here/instances.txt" | grep -v '^$' | while IFS='|' read -r name args; do
    args="${args//@DATA@/$here/data}"
    # shellcheck disable=SC2086
    "$oracle" $args > "$here/fronts/$name.front"
    echo "$name: $(wc -l < "$here/fronts/$name.front" | tr -d ' ') points"
done
