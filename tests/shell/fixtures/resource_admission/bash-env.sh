#!/bin/bash
# Only external host observations are controlled; original admission runs intact.
systemctl() {
  if [[ "$2" == is-active ]]; then return 0; fi
  test "$2" = show
  case "$5" in
    MemoryMax) printf '%s\n' "$CONTROLLED_COMMON_MAX" ;;
    MemoryCurrent) printf '%s\n' "$CONTROLLED_COMMON_CURRENT" ;;
    MemorySwapMax) printf '%s\n' "$CONTROLLED_COMMON_SWAP" ;;
    *) return 64 ;;
  esac
}
df() { printf 'Avail\n%s\n' "$CONTROLLED_HOME_BYTES"; }
awk() {
  local args=() argument
  for argument in "$@"; do
    case "$argument" in
      /proc/meminfo) args+=("$CONTROLLED_HOST/meminfo") ;;
      /proc/pressure/memory) args+=("$CONTROLLED_HOST/pressure") ;;
      *) args+=("$argument") ;;
    esac
  done
  command awk "${args[@]}"
}
function /home/ts/bin/agent-resource-check() {
  printf '{"level":"warning","controlled_host_observation":true}\n'
  return 2
}
