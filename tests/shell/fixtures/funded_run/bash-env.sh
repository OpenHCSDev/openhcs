#!/bin/bash
# Controlled external systemctl/X11/exec boundaries; no real scope or client.
systemctl() {
  if [[ "$2" == is-active ]]; then return 0; fi
  test "$2" = show
  case "$5" in
    LoadState) printf 'not-found\n';;
    InvocationID) printf '11111111111111111111111111111111\n';;
    Slice) printf '%s\n' "$FLEET_SLICE";;
    MemoryMax) printf '1048576\n';;
    MemorySwapMax|MemoryCurrent) printf '0\n';;
    *) return 64;;
  esac
}
function /usr/bin/xprop() { printf 'WINDOW controlled external X owner\n'; }
# Execute the actual client up to its external exec, then model terminal42.
trap 'if [[ "$BASH_COMMAND" == "exec /usr/bin/env "* ]]; then
  printf "CONTROLLED_EXEC cap=%s cpu=%s install=%s run=%s funding=%s\n" "$cap" "$cpu" "$FLEET_INSTALL" "$FLEET_RUN_ROOT" "$FLEET_ROOT"
  exit 42
fi' DEBUG
