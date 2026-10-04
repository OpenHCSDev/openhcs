#!/bin/bash
# Only external host observations are controlled; original admission runs intact.
systemctl() {
  if [[ "$2" == is-active ]]; then
    if [[ "$4" == *-mcp.scope ]]; then
      test "${CONTROLLED_MCP_ACTIVE:-1}" = 1
      test "${CONTROLLED_PROCESS_STATE:-loaded}" = loaded
    fi
    return
  fi
  test "$2" = show
  if [[ "$3" != controlled.slice ]]; then
    local role
    case "$3" in *-mcp.scope) role=SCI ;; *-author.scope) role=CLI ;; *-x94.scope|*-wm94.scope|*-vnc94.scope) role=HELPER ;; *) return 64 ;; esac
    case "$5" in
      LoadState)
        if [[ "$role" == CLI && "$CONTROLLED_CLI_MAX" == 0 ]]; then printf 'not-found\n'
        else printf '%s\n' "${CONTROLLED_PROCESS_STATE:-loaded}"; fi ;;
      ActiveState) printf 'active\n' ;;
      InvocationID) printf '11111111111111111111111111111111\n' ;;
      Slice) printf 'controlled.slice\n' ;;
      MemoryMax) local variable="CONTROLLED_${role}_MAX"; printf '%s\n' "${!variable}" ;;
      MemoryCurrent) local variable="CONTROLLED_${role}_CURRENT"; printf '%s\n' "${!variable}" ;;
      MemorySwapMax) printf '0\n' ;;
      *) return 64 ;;
    esac
    return
  fi
  case "$5" in
    MemoryCurrent) printf '%s\n' "$CONTROLLED_COMMON_CURRENT" ;;
    MemorySwapCurrent) printf '%s\n' "$CONTROLLED_COMMON_SWAP" ;;
    ControlGroup) printf '/controlled-resource-fixture\n' ;;
    *) return 64 ;;
  esac
}
find() {
  if [[ "$1" == /sys/fs/cgroup/controlled-resource-fixture ]]; then
    printf '%s\n' "$$"
  else command find "$@"; fi
}
df() { printf 'Avail\n%s\n' "$CONTROLLED_HOME_BYTES"; }
du() {
  # No retired bytes may be recursively inventoried by operation admission.
  local argument
  for argument in "$@"; do
    case "$argument" in */retired-output|*/closed-no-longer-local) return 99 ;; esac
  done
  command du "$@"
}
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
