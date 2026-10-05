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
    MemorySwapMax|MemorySwapCurrent|MemoryCurrent) printf '0\n';;
    ControlGroup) printf '/controlled-funded-fixture\n';;
    *) return 64;;
  esac
}
find() {
  if [[ "$1" == /sys/fs/cgroup/controlled-funded-fixture ]]; then printf '%s\n' "$$"
  else command find "$@"; fi
}
function /usr/bin/xprop() { printf 'WINDOW controlled external X owner\n'; }
# Execute the actual client up to its external exec, then model terminal42.
trap 'if [[ "$BASH_COMMAND" == "exec /usr/bin/env "* ]]; then
  printf "CONTROLLED_EXEC cpu=%s install=%s run=%s funding=%s\n" "$cpu" "$FLEET_INSTALL" "$FLEET_RUN_ROOT" "$FLEET_ROOT"
  printf "CONTROLLED_PATHS read=%s write=%s temp=%s data=%s runtime=%s\n" "$OPENHCS_AGENT_READ_ROOTS" "$OPENHCS_AGENT_WRITE_ROOTS" "$TMPDIR" "$XDG_DATA_HOME" "$XDG_RUNTIME_DIR"
  exit 42
fi' DEBUG
