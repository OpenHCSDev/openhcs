#!/bin/bash
set -euo pipefail
root=${1:?root}
slot=${2:?slot}
runtime="$root/$slot/author-workspace/output/runtime"
test -f "$runtime/mcp.stdin"
test -f "$runtime/mcp.stdout"
test -f "$runtime/mcp.timing"
printf 'client %s\n' "$slot" >> "$root/calls"
printf 'controlled child: %s\n' "$slot"
exit "$(<"$root/client-status")"
