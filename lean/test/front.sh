#!/usr/bin/env bash
# The verified solver against the C++ one: for every instance of the given lists (default: the
# golden instances, tests/golden/instances.txt), write the instance with `zeno --certificate`,
# solve it with `zeno-front`, and require the same front as `zeno front` (cost makespan lines by
# increasing cost).
# Usage, from the repository root:
#   bash lean/test/front.sh ZENO ZENO_FRONT [OUT_DIR] [LIST|DATA_DIR ...]
# Each extra argument is a list file and its @DATA@ directory, separated by '|'.
set -u
zeno=$1
front=$2
out=${3:-$(mktemp -d)}
shift 3 2>/dev/null || shift $#
lists=("$@")
if [ ${#lists[@]} -eq 0 ]; then
    lists=("tests/golden/instances.txt|tests/golden/data")
fi
mkdir -p "$out"
status=0
total=0

for entry in "${lists[@]}"; do
    list=${entry%%|*}
    data=${entry#*|}
    while IFS='|' read -r name args; do
        case "$name" in ''|'#'*) continue ;; esac
        args=${args//@DATA@/$data}
        cert="$out/$name.cert"
        # shellcheck disable=SC2086
        if ! "$zeno" $args --certificate "$cert" > "$out/$name.expected"; then
            echo "FAIL  $name: zeno $args failed"
            status=1
            continue
        fi
        total=$((total + 1))
        if ! "$front" "$cert" > "$out/$name.actual"; then
            echo "FAIL  $name: zeno-front failed"
            status=1
            continue
        fi
        if cmp -s "$out/$name.expected" "$out/$name.actual"; then
            echo "ok    $name: $(wc -l < "$out/$name.actual" | tr -d ' ') points"
        else
            echo "FAIL  $name: the fronts differ"
            diff "$out/$name.expected" "$out/$name.actual" | head -10
            status=1
        fi
    done < "$list"
done
echo "$total fronts compared"
exit $status
