#!/usr/bin/env bash
# End to end: solve every golden instance (tests/golden/instances.txt) and every random instance
# (lean/test/instances/instances.txt) with the C++ solver, write its certificate, and check it
# with the Lean checker. Every certificate must be accepted. This guards against format drift
# between the C++ writer and the Lean parser and checker.
# Usage, from the repository root: bash lean/test/e2e.sh ZENO ZENO_CHECK [OUT_DIR]
set -u
zeno=$1
check=$2
out=${3:-$(mktemp -d)}
mkdir -p "$out"
status=0
total=0
forest=0

run_list() {
    local list=$1 data=$2 name args cert result code
    while IFS='|' read -r name args; do
        case "$name" in ''|'#'*) continue ;; esac
        args=${args//@DATA@/$data}
        cert="$out/$name.cert"
        # shellcheck disable=SC2086
        if ! "$zeno" $args --certificate "$cert" > /dev/null; then
            echo "FAIL  $name: zeno $args failed"
            status=1
            continue
        fi
        total=$((total + 1))
        if grep -q ' forest$' "$cert"; then forest=$((forest + 1)); fi
        if ! "$zeno" check "$cert" > /dev/null; then
            echo "FAIL  $name: the C++ checker rejects its own certificate"
            status=1
        fi
        result=$("$check" "$cert")
        code=$?
        if [ "$code" -eq 0 ]; then
            echo "ok    $name: $result"
        else
            echo "FAIL  $name (exit $code): $result"
            status=1
        fi
    done < "$list"
}

run_list tests/golden/instances.txt tests/golden/data
run_list lean/test/instances/instances.txt lean/test/instances
echo "$total certificates checked, $forest with a forest gap"
if [ "$forest" -eq 0 ]; then
    echo "FAIL  no certificate has a forest gap: the forest path is not exercised"
    status=1
fi
exit $status
