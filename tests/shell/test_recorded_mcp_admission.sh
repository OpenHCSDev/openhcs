#!/bin/bash
# Real util-linux script, controlled external guard/client contracts; no MCP.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.."; pwd)
scratch=${1:?new persistent validation directory}
test ! -e "$scratch"
mkdir -p "$scratch/operations"
fixtures="$repo/tests/shell/fixtures/recorded_mcp"
ln -s "$repo/scripts/blind_analysis/operations/recorded-mcp.sh" "$scratch/operations/recorded-mcp.sh"
for file in slot-env.sh resource-check.sh mcp-client.sh; do
  ln -s "$fixtures/$file" "$scratch/operations/$file"
done
export FLEET_PARENT_RELEASED=1
run() {
  local expected=$1 slot=$2 observation=$3 status
  set +e
  bash "$scratch/operations/recorded-mcp.sh" "$scratch" "$slot" "$observation"
  status=$?
  set -e
  test "$status" = "$expected"
}
printf '76\n' > "$scratch/resource-status"
printf '0\n' > "$scratch/client-status"
run 76 FIRST_LEAF rejected01
runtime="$scratch/FIRST_LEAF/author-workspace/output/runtime"
for file in mcp.stdin mcp.stdout mcp.timing first-mcp-started.epoch; do
  test ! -e "$runtime/$file"
done
test "$(<"$scratch/rejected01.receipt")" = 76
test "$(wc -l < "$scratch/calls")" = 2
printf 'PASS known prestart rejection preserves76 and creates no MCP journals\n'

printf '0\n' > "$scratch/resource-status"
run 0 FIRST_LEAF admitted02
test "$(<"$scratch/rejected01.receipt")" = 76
test "$(<"$scratch/admitted02.receipt")" = 0
test "$(wc -l < "$scratch/calls")" = 5
for file in mcp.stdin mcp.stdout mcp.timing; do test -f "$runtime/$file"; done
sha256sum "$runtime"/mcp.* > "$scratch/closed-journals.sha256"
run 1 FIRST_LEAF forbidden03
test ! -e "$scratch/forbidden03.receipt"
test "$(wc -l < "$scratch/calls")" = 5
sha256sum --check --quiet "$scratch/closed-journals.sha256"
printf 'PASS fresh checkpoint admitted once; existing logs prohibit replay\n'

# Another leaf needs only its identity; no generic recorder edit.
printf '42\n' > "$scratch/client-status"
run 42 INDEPENDENT_LEAF admitted01
test "$(wc -l < "$scratch/calls")" = 8
run 1 INDEPENDENT_LEAF forbidden02
test ! -e "$scratch/forbidden02.receipt"
test "$(wc -l < "$scratch/calls")" = 8
printf 'PASS independent leaf, exact child42 and no second guard/client\n'

# A startup marker alone is already lifetime custody, not admission rejection.
mkdir -p "$scratch/MARKER_LEAF/author-workspace/output/runtime"
printf '1\n' > "$scratch/MARKER_LEAF/author-workspace/output/runtime/first-mcp-started.epoch"
run 1 MARKER_LEAF forbidden04
test ! -e "$scratch/forbidden04.receipt"
test "$(wc -l < "$scratch/calls")" = 8
printf 'PASS startup marker prohibits replay without journal reinterpretation\n'
