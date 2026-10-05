#!/bin/bash
# Recording owns the one admission transition before any client journal exists.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "${1:?root}" "${2:?slot}"
observation=${3:?unique startup observation}
runtime="$FLEET_WORKSPACE/output/runtime"
mkdir -p "$runtime"
test ! -e "$runtime/mcp.stdin"
test ! -e "$runtime/mcp.stdout"
test ! -e "$runtime/mcp.timing"
test ! -e "$runtime/first-mcp-started.epoch"
fleet_require_writer_release
bash "$FLEET_OPERATIONS/resource-check.sh" "$FLEET_ROOT" "$FLEET_SLOT" "$observation" replacement
# Failed admission leaves its original unique receipts but consumes no journal.
# After script starts, retain this ONE handle/journal even on child failure.
cd "$FLEET_WORKSPACE/output"
printf -v command '%q ' bash "$FLEET_OPERATIONS/mcp-client.sh" "$FLEET_ROOT" "$FLEET_SLOT"
exec /usr/bin/script --quiet --flush --return --log-in "$runtime/mcp.stdin" --log-out "$runtime/mcp.stdout" --log-timing "$runtime/mcp.timing" --command "$command"
