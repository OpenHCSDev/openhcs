#!/bin/bash
# NEXT revision of the original programme/slot projection owner.
set -euo pipefail
FLEET_ROOT=${1:?programme root}
# One read of the original current programme; this is a request-local view,
# never another persisted roster or current-head file.
FLEET_PROGRAM=$(<"$FLEET_ROOT/program.json")

fleet_member() {
  local reference owner
  reference=$(jq -ce --arg member "$1" '[.authors[] | select(.slot == $member)] |
    if length == 1 then .[0] else error("missing or ambiguous funded member") end' <<< "$FLEET_PROGRAM") || return
  owner=$(jq -er '.run_owner_root' <<< "$reference") || return
  test "$(jq -er '.funding_root' "$owner/program.json")" = "$FLEET_ROOT" || {
    printf 'Canonical funding root required; refused run snapshot %s\n' "$FLEET_ROOT" >&2
    return 64
  }
  # Funding owns membership; the immutable run owns its actual declaration.
  jq -ce --arg member "$1" --arg owner "$owner" '[.authors[] |
    select(.slot==$member and .run_owner_root==$owner)] |
    if length==1 then .[0] else error("missing or ambiguous run declaration") end' "$owner/program.json"
}

fleet_limits_for() {
  local member owner
  member=$(fleet_member "$1") || return
  owner=$(jq -er '.run_owner_root' <<< "$member") || return
  jq -ce '.proposed_resource_envelope' "$owner/program.json"
}

fleet_funded_slots() {
  jq -er '.authors[].slot' <<< "$FLEET_PROGRAM"
}

fleet_workspace_for() {
  local member
  member=$(fleet_member "$1") || return
  jq -er '.run_owner_root + "/" + .slot + "/author-workspace"' <<< "$member"
}

fleet_unit_for() {
  local member owner phase
  member=$(fleet_member "$1") || return
  owner=$(jq -er '.run_owner_root' <<< "$member") || return
  phase=$(jq -er '.phase' "$owner/program.json") || return
  printf '%s-%s\n' "$phase" "${1,,}"
}

# Admission and launch share these original process-performer declarations.
fleet_process_limit_mib() {
  local field
  case "${1:?process performer}" in
    mcp) field=per_author_science_mib ;;
    author) field=per_author_cli_mib ;;
    *) return 64 ;;
  esac
  fleet_limits_for "$FLEET_SLOT" | jq -er --arg field "$field" '
    .[$field] | select(type=="number" and .>=0 and .==floor)'
}

# Exact residual for a live declared scope; conservative ceiling for an absent
# scope. The unit namespace comes from fleet_unit_for, not caller PIDs/ports.
fleet_process_growth_bound_bytes() {
  local role=${1:?process performer} limit unit state current observed invocation
  limit=$(fleet_process_limit_mib "$role") || return
  limit=$((limit*1048576))
  unit="$FLEET_UNIT-$role.scope"
  state=$(systemctl --user show "$unit" -p LoadState --value) || return
  if [[ "$state" == not-found ]]; then
    printf 'Process %s absent; declared ceiling bound=%s bytes (not measured residual)\n' "$unit" "$limit" >&2
    printf '%s\n' "$limit"
    return
  fi
  test "$state" = loaded || return
  state=$(systemctl --user show "$unit" -p ActiveState --value) || return
  if [[ "$state" == inactive || "$state" == failed ]]; then
    printf 'Process %s %s; declared ceiling bound=%s bytes (not measured residual)\n' "$unit" "$state" "$limit" >&2
    printf '%s\n' "$limit"
    return
  fi
  test "$state" = active || return
  invocation=$(systemctl --user show "$unit" -p InvocationID --value) || return
  [[ "$invocation" =~ ^[a-f0-9]{32}$ ]] || return 1
  test "$(systemctl --user show "$unit" -p Slice --value)" = "$FLEET_SLICE" || return
  observed=$(systemctl --user show "$unit" -p MemoryMax --value) || return
  test "$observed" = "$limit" || return
  test "$(systemctl --user show "$unit" -p MemorySwapMax --value)" = 0 || return
  current=$(systemctl --user show "$unit" -p MemoryCurrent --value) || return
  [[ "$current" =~ ^[0-9]+$ ]] || return 1
  test "$current" -le "$limit" || return
  printf 'Process %s invocation=%s cap=%s charge=%s residual=%s bytes\n' "$unit" "$invocation" "$limit" "$current" "$((limit-current))" >&2
  printf '%s\n' "$((limit-current))"
}

# The original declaration projector asks this owner for the complete family.
# This is a projection command, not another catalog or a persisted roster.
if [[ "${2:-}" == --project-members ]]; then
  selected=$(jq -ce '.authors | map(.slot)' <<< "$FLEET_PROGRAM")
  projected='[]'
  while IFS= read -r member_name; do
    declaration=$(fleet_member "$member_name") || exit
    projected=$(jq -ce --argjson member "$declaration" '. + [$member]' <<< "$projected")
  done < <(jq -r '.[]' <<< "$selected")
  printf '%s\n' "$projected"
  exit
fi

FLEET_SLOT=${2:?declared slot}
slot=$(fleet_member "$FLEET_SLOT") || exit
FLEET_RUN_ROOT=$(jq -er '.run_owner_root' <<< "$slot")
FLEET_RUN_PROGRAM=$(<"$FLEET_RUN_ROOT/program.json")
FLEET_WORKSPACE=$(fleet_workspace_for "$FLEET_SLOT")
FLEET_SLICE=$(jq -er '.scope_slice' <<< "$FLEET_PROGRAM")
FLEET_INSTALL=$(jq -er '.source_install' "$FLEET_RUN_ROOT/program.json")
FLEET_PYTHON=$(jq -er '.python' "$FLEET_RUN_ROOT/program.json")
FLEET_OPERATIONS=$(jq -er '.operation_owner_root' "$FLEET_RUN_ROOT/program.json")
FLEET_PHASE=$(jq -er '.phase' "$FLEET_RUN_ROOT/program.json")
FLEET_DISPLAY=$(jq -er '.display' <<< "$slot")
FLEET_CPU=$(jq -er '.cpu' <<< "$slot")
FLEET_INPUT=$(jq -er '.input_root' <<< "$slot")
FLEET_NATIVE=$(jq -er '.native_port' <<< "$slot")
FLEET_NATIVE_ACK=$(jq -er '.native_ack_port' <<< "$slot")
FLEET_VIEWER=$(jq -er '.viewer_port' <<< "$slot")
FLEET_VIEWER_ACK=$(jq -er '.viewer_ack_port' <<< "$slot")
FLEET_VNC=$(jq -er '.vnc_port' <<< "$slot")
FLEET_UNIT=$(fleet_unit_for "$FLEET_SLOT")
FLEET_AGGREGATE_BYTES=$(jq -er '.proposed_resource_envelope.aggregate_memory_max_bytes | select(type=="number" and .>0 and .%1048576==0)' <<< "$FLEET_PROGRAM")
FLEET_COMBINED_MIB=$((FLEET_AGGREGATE_BYTES/1048576))
export FLEET_ROOT FLEET_SLOT FLEET_RUN_ROOT FLEET_RUN_PROGRAM FLEET_WORKSPACE FLEET_SLICE FLEET_INSTALL FLEET_PYTHON FLEET_OPERATIONS FLEET_PHASE
export FLEET_DISPLAY FLEET_CPU FLEET_INPUT FLEET_NATIVE FLEET_NATIVE_ACK FLEET_VIEWER FLEET_VIEWER_ACK FLEET_VNC FLEET_UNIT FLEET_COMBINED_MIB
helper_root=$(jq -er '.helper_custody.program_root' <<< "$slot")
helper_slot=$(jq -er '.helper_custody.slot' <<< "$slot")
jq -e --arg member "$helper_slot" --argjson display "$FLEET_DISPLAY" \
  '[.authors[]|select(.slot==$member)] | length==1 and .[0].display==$display' "$helper_root/program.json" >/dev/null

fleet_helper_unit_for() {
  local member root predecessor phase
  member=$(fleet_member "$1") || return
  root=$(jq -er '.helper_custody.program_root' <<< "$member") || return
  predecessor=$(jq -er '.helper_custody.slot' <<< "$member") || return
  phase=$(jq -er '.phase' "$root/program.json") || return
  printf '%s-%s\n' "$phase" "${predecessor,,}"
}

FLEET_HELPER_UNIT=$(fleet_helper_unit_for "$FLEET_SLOT")
export FLEET_HELPER_UNIT

fleet_require_joint_slice() {
  systemctl --user is-active --quiet "$FLEET_SLICE"
  test "$(systemctl --user show "$FLEET_SLICE" -p MemoryMax --value)" = "$((FLEET_COMBINED_MIB*1048576))"
  test "$(systemctl --user show "$FLEET_SLICE" -p MemorySwapMax --value)" = 0
}

fleet_require_helper() {
  local role=${1:?declared helper role} receipt expected observed unit cap
  cap=$(jq -er --arg role "$role" '.proposed_resource_envelope.helper_caps_mib[$role]' "$FLEET_RUN_ROOT/program.json")
  receipt=$(jq -er '.helper_custody.parent_handoff_receipt' <<< "$slot")
  test -f "$receipt"
  jq -e --arg root "$helper_root" --arg member "$helper_slot" \
    '.program_root==$root and .slot==$member and (.terminal_custody_receipt|type=="string")' "$receipt" >/dev/null
  test -f "$(jq -er '.terminal_custody_receipt' "$receipt")"
  # Helper identity is independent of the scientific writer. Its release is
  # checked by fleet_require_writer_release at the existing launch owner.
  expected=$(jq -er --arg role "$role" '.helper_invocations[$role] | select(type=="string" and test("^[a-f0-9]{32}$"))' "$receipt")
  unit="$FLEET_HELPER_UNIT-$role$FLEET_DISPLAY.scope"
  systemctl --user is-active --quiet "$unit"
  observed=$(systemctl --user show "$unit" -p InvocationID --value)
  printf 'Helper %s expected=%s observed=%s\n' "$unit" "$expected" "$observed"
  test "$observed" = "$expected"
  test "$(systemctl --user show "$unit" -p Slice --value)" = "$FLEET_SLICE"
  test "$(systemctl --user show "$unit" -p MemoryMax --value)" = "$((cap*1048576))"
  test "$(systemctl --user show "$unit" -p MemorySwapMax --value)" = 0
}

fleet_require_helpers() {
  local role
  while IFS= read -r role; do fleet_require_helper "$role"; done \
    < <(jq -er '.proposed_resource_envelope.helper_caps_mib|keys[]' "$FLEET_RUN_ROOT/program.json")
}


# The scientific writer's predecessor is independent of inherited helper identity.
fleet_require_writer_release() {
  local retirements retirement predecessor_root predecessor_slot predecessor_phase predecessor_unit state
  retirements=$(jq -ce '.writer_handoff | select(type=="array")' <<< "$slot")
  while IFS= read -r retirement; do
    predecessor_root=$(jq -er '.program_root' <<< "$retirement")
    predecessor_slot=$(jq -er '.slot|ascii_downcase' <<< "$retirement")
    test -f "$(jq -er '.terminal_custody_receipt' <<< "$retirement")"
    predecessor_phase=$(jq -er '.phase' "$predecessor_root/program.json")
    for predecessor_unit in "$predecessor_phase-$predecessor_slot-author.scope" "$predecessor_phase-$predecessor_slot-mcp.scope"; do
      state=$(systemctl --user show "$predecessor_unit" -p LoadState --value)
      if [[ "$state" != not-found ]]; then
        test "$state" = loaded
        state=$(systemctl --user show "$predecessor_unit" -p ActiveState --value)
        [[ "$state" == inactive || "$state" == failed ]]
      fi
      printf 'Retired scientific writer %s inactive\n' "$predecessor_unit"
    done
  done < <(jq -c '.[]' <<< "$retirements")
}

# Cold helper admission is owned here; lifecycle performers remain original.
fleet_require_bootstrap_custody() {
  local receipt units unit state ports listeners
  receipt=$(jq -er '.helper_custody.bootstrap_custody_receipt' <<< "$slot")
  test -f "$receipt"
  units=$(jq -ce '.helper_custody.retired_owner_units | select(type=="array" and length>0)' <<< "$slot")
  while IFS= read -r unit; do
    state=$(systemctl --user show "$unit" -p LoadState --value)
    if [[ "$state" != not-found ]]; then
      state=$(systemctl --user show "$unit" -p ActiveState --value)
      [[ "$state" == inactive || "$state" == failed ]]
    fi
    printf 'Retired helper owner %s inactive\n' "$unit"
  done < <(jq -r '.[]' <<< "$units")
  for unit in $(jq -er '.proposed_resource_envelope.helper_caps_mib|keys[]' "$FLEET_RUN_ROOT/program.json"); do
    state=$(systemctl --user show "$FLEET_HELPER_UNIT-$unit$FLEET_DISPLAY.scope" -p LoadState --value)
    if [[ "$state" != not-found ]]; then
      state=$(systemctl --user show "$FLEET_HELPER_UNIT-$unit$FLEET_DISPLAY.scope" -p ActiveState --value)
      [[ "$state" == inactive || "$state" == failed ]]
    fi
  done
  test ! -e "/tmp/.X11-unix/X$FLEET_DISPLAY"
  test ! -e "/tmp/.X$FLEET_DISPLAY-lock"
  ports="( sport = :$FLEET_VNC or sport = :$FLEET_NATIVE or sport = :$FLEET_NATIVE_ACK or sport = :$FLEET_VIEWER or sport = :$FLEET_VIEWER_ACK )"
  listeners=$(ss -H -ltn "$ports")
  test -z "$listeners"
  printf 'Cold assigned display/endpoints absent; fresh helpers not launched\n'
}

# External inspection operations, no helper/provider/runtime launches.
if [[ "${3:-}" == --print-workspace ]]; then printf '%s\n' "$FLEET_WORKSPACE"; fi
if [[ "${3:-}" == --verify-helpers ]]; then fleet_require_joint_slice; fleet_require_helpers; fi
