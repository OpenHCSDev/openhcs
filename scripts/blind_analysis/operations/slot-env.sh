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

# The immutable member owns payload placement. Control/source/history remain
# in its existing workspace; absent declarations retain the original location.
fleet_artifact_root_for() {
  local member
  member=$(fleet_member "$1") || return
  jq -er '.artifact_destination.path //
    (.run_owner_root + "/" + .slot + "/author-workspace/output")' <<< "$member"
}

fleet_member_output_roots() {
  jq -er '(.run_owner_root+"/"+.slot+"/author-workspace/output") as $control |
    [$control, (.artifact_destination.path // $control)] | unique[]' <<< "$1"
}

fleet_output_roots_for() {
  local member
  member=$(fleet_member "$1") || return
  fleet_member_output_roots "$member"
}

fleet_require_artifact_destination() {
  local member mount
  member=$(fleet_member "$1") || return
  if jq -e '.artifact_destination != null' <<< "$member" >/dev/null; then
    mount=$(jq -er '.artifact_destination.mount' <<< "$member") || return
    mountpoint --quiet "$mount" || return
    local path
    path=$(fleet_artifact_root_for "$1") || return
    [[ "$path" == "$mount/"* ]] || return
    # Never admit a missing mount through a symlink or silently create payloads
    # on its backing HOME/root filesystem. Provision the ordinary directory first.
    test -d "$path" && test -w "$path" || return
    test "$(realpath -e "$path")" = "$path" || return
    test "$(findmnt -n -T "$path" -o TARGET)" = "$mount" || return
  fi
}

fleet_unit_for() {
  local member owner phase
  member=$(fleet_member "$1") || return
  owner=$(jq -er '.run_owner_root' <<< "$member") || return
  phase=$(jq -er '.phase' "$owner/program.json") || return
  printf '%s-%s\n' "$phase" "${1,,}"
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
FLEET_ARTIFACT_ROOT=$(fleet_artifact_root_for "$FLEET_SLOT")
FLEET_SCRATCH="$FLEET_ARTIFACT_ROOT/runtime/scratch"
FLEET_SLICE=$(jq -er '.scope_slice' <<< "$FLEET_PROGRAM")
FLEET_INSTALL=$(jq -er '.source_install' "$FLEET_RUN_ROOT/program.json")
FLEET_PYTHON=$(jq -er '.python' "$FLEET_RUN_ROOT/program.json")
FLEET_OPERATIONS=$(jq -er '.operation_owner_root' "$FLEET_RUN_ROOT/program.json")
FLEET_PHASE=$(jq -er '.phase' "$FLEET_RUN_ROOT/program.json")
# The immutable qualification owns the complete source closure. Never inherit
# an operator's PYTHONPATH or let a performer reconstruct package locations.
qualification=$(jq -er '.qualification_receipt' <<< "$FLEET_RUN_PROGRAM")
test "$(jq -er '.target' "$qualification")" = "$FLEET_INSTALL"
PYTHONPATH=$(jq -er --arg root "$FLEET_INSTALL" '
  .python_source_roots | select(type=="array" and length>0 and .[0]==$root) |
  if all(.[]; type=="string" and startswith("/") and
    (contains(":")|not) and (contains("\n")|not))
  then join(":") else error("invalid qualified Python roots") end' "$qualification")
export PYTHONPATH
while IFS= read -r source_root; do test -d "$source_root"; done \
  < <(tr ':' '\n' <<< "$PYTHONPATH")
software_paths=$("$FLEET_PYTHON" -B - "$qualification" <<'PY'
import json
import sys
from pathlib import Path
from openhcs.agent.skill_sync import installed_skill_bundle
from openhcs.agent.knowledge_manifest import (
    default_repo_root, default_knowledge_base_manifest_path,
    knowledge_base_source_paths_from_manifest,
)
from openhcs.agent.knowledge_manifest_schema import (
    DEFAULT_KNOWLEDGE_BASE_MANIFEST_PATH,
    PackagedComparisonManifestSnapshot, knowledge_source_projections,
)
qualification = json.loads(Path(sys.argv[1]).read_text())
bundle = installed_skill_bundle()
skill, = (root for root in bundle.skill_roots() if root.name == "use-openhcs")
source_root = default_repo_root().resolve()
projection_root = Path(qualification["knowledge_projection_root"])
originals = knowledge_source_projections(
    default_knowledge_base_manifest_path(), source_root=source_root)
frozen = knowledge_source_projections(
    projection_root / DEFAULT_KNOWLEDGE_BASE_MANIFEST_PATH,
    source_root=projection_root, recipe_type=PackagedComparisonManifestSnapshot)
assert originals.keys() == frozen.keys(), "Knowledge projections disagree"
mounts = []
for relative, original in originals.items():
    if not original.resolve().is_relative_to(source_root):
        retained = frozen[relative]
        assert retained.is_file(), retained
        mounts.append({"source": str(retained), "target": str(original)})
print(json.dumps({
    "skill": str(skill.resolve()),
    "knowledge_root": str(default_repo_root().resolve()),
    "knowledge_manifest": str(default_knowledge_base_manifest_path().resolve()),
    "knowledge_read_roots": [str(path) for path in dict.fromkeys(
        (*knowledge_base_source_paths_from_manifest(), *bundle.source_paths()))],
    "knowledge_mounts": mounts,
}))
PY
)
FLEET_SKILL=$(jq -er '.skill' <<< "$software_paths")
FLEET_KNOWLEDGE_ROOT=$(jq -er '.knowledge_root' <<< "$software_paths")
FLEET_KNOWLEDGE_MANIFEST=$(jq -er '.knowledge_manifest' <<< "$software_paths")
FLEET_KNOWLEDGE_READ_ROOTS=$(jq -er '.knowledge_read_roots | join(":")' <<< "$software_paths")
FLEET_KNOWLEDGE_MOUNTS=$(jq -ce '.knowledge_mounts' <<< "$software_paths")
export FLEET_SKILL FLEET_KNOWLEDGE_ROOT FLEET_KNOWLEDGE_MANIFEST FLEET_KNOWLEDGE_READ_ROOTS FLEET_KNOWLEDGE_MOUNTS
FLEET_DISPLAY=$(jq -er '.display' <<< "$slot")
FLEET_CPU=$(jq -er '.cpu' <<< "$slot")
FLEET_INPUT=$(jq -er '.input_root' <<< "$slot")
FLEET_NATIVE=$(jq -er '.native_port' <<< "$slot")
FLEET_NATIVE_ACK=$(jq -er '.native_ack_port' <<< "$slot")
FLEET_VIEWER=$(jq -er '.viewer_port' <<< "$slot")
FLEET_VIEWER_ACK=$(jq -er '.viewer_ack_port' <<< "$slot")
FLEET_VNC=$(jq -er '.vnc_port' <<< "$slot")
FLEET_UNIT=$(fleet_unit_for "$FLEET_SLOT")
export FLEET_ROOT FLEET_SLOT FLEET_RUN_ROOT FLEET_RUN_PROGRAM FLEET_WORKSPACE FLEET_SLICE FLEET_INSTALL FLEET_PYTHON FLEET_OPERATIONS FLEET_PHASE
export FLEET_ARTIFACT_ROOT FLEET_SCRATCH
export FLEET_DISPLAY FLEET_CPU FLEET_INPUT FLEET_NATIVE FLEET_NATIVE_ACK FLEET_VIEWER FLEET_VIEWER_ACK FLEET_VNC FLEET_UNIT
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

# A named observation replaces only a positively closed controller. The funded
# member, native roots and first-start clock remain the original owners.
FLEET_RECORD_RUNTIME="$FLEET_WORKSPACE/output/runtime"
FLEET_CLIENT_UNIT="$FLEET_UNIT-mcp"
FLEET_AUTHOR_UNIT="$FLEET_UNIT-author"
FLEET_PREDECESSOR_RECORD_RUNTIME="$FLEET_RECORD_RUNTIME"
FLEET_PREDECESSOR_AUTHOR_UNIT="$FLEET_AUTHOR_UNIT"
if [[ -n "${FLEET_RECOVERY_OBSERVATION:-}" ]]; then
  [[ "$FLEET_RECOVERY_OBSERVATION" =~ ^[a-zA-Z0-9_-]+$ ]] || exit 64
  if [[ -n "${FLEET_RECOVERY_PREDECESSOR:-}" ]]; then
    [[ "$FLEET_RECOVERY_PREDECESSOR" =~ ^[a-zA-Z0-9_-]+$ ]] || exit 64
    test "$FLEET_RECOVERY_PREDECESSOR" != "$FLEET_RECOVERY_OBSERVATION" || exit 64
    FLEET_PREDECESSOR_RECORD_RUNTIME+="/$FLEET_RECOVERY_PREDECESSOR"
    FLEET_PREDECESSOR_AUTHOR_UNIT+="-$FLEET_RECOVERY_PREDECESSOR"
  fi
  FLEET_RECORD_RUNTIME+="/$FLEET_RECOVERY_OBSERVATION"
  FLEET_CLIENT_UNIT+="-$FLEET_RECOVERY_OBSERVATION"
  FLEET_AUTHOR_UNIT+="-$FLEET_RECOVERY_OBSERVATION"
  # Explicit operational revision: one complete family, not frozen-file edits.
  FLEET_OPERATIONS=$(cd "$(dirname "${BASH_SOURCE[0]}")"; pwd)
fi
export FLEET_RECORD_RUNTIME FLEET_CLIENT_UNIT FLEET_AUTHOR_UNIT FLEET_OPERATIONS
export FLEET_PREDECESSOR_RECORD_RUNTIME FLEET_PREDECESSOR_AUTHOR_UNIT

fleet_require_closed_controllers() {
  local runtime="$FLEET_PREDECESSOR_RECORD_RUNTIME" journal state controller
  test -f "$FLEET_WORKSPACE/output/runtime/first-mcp-started.epoch" || return
  for journal in author-events.typescript mcp.stdin mcp.stdout; do
    tail -n 3 "$runtime/$journal" | rg -q '^Script done .*COMMAND_EXIT_CODE="[0-9]+"' || return
    if fuser "$runtime/$journal" >/dev/null 2>&1; then return 75; fi
  done
  state=$(systemctl --user show "$FLEET_PREDECESSOR_AUTHOR_UNIT.scope" -p ActiveState --value) || return
  [[ "$state" == inactive || "$state" == failed || -z "$state" ]] || return 75
  # systemd owns current controllers. A new observation name must not bypass
  # a live recovery; its native descendants in the original MCP scope remain.
  while read -r controller _; do
    [[ "$controller" == "$FLEET_AUTHOR_UNIT.scope" || "$controller" == "$FLEET_CLIENT_UNIT.scope" ]] && continue
    printf 'Recovery controller still active: %s\n' "$controller" >&2
    return 75
  done < <(systemctl --user list-units --type=scope --state=active,activating \
    --no-legend --plain --no-pager "$FLEET_UNIT-author-*.scope" "$FLEET_UNIT-mcp-*.scope")
}

fleet_require_joint_slice() {
  systemctl --user is-active --quiet "$FLEET_SLICE"
}

fleet_require_live_client() {
  local runtime="$FLEET_RECORD_RUNTIME" unit="$FLEET_CLIENT_UNIT.scope" invocation
  # The recorder creates these only after its startup admission. Never infer
  # an ongoing client from a port, a helper, or a requested tool name.
  test -f "$FLEET_WORKSPACE/output/runtime/first-mcp-started.epoch"
  test -f "$runtime/mcp.stdin"
  test -f "$runtime/mcp.stdout"
  test -f "$runtime/mcp.timing"
  systemctl --user is-active --quiet "$unit"
  invocation=$(systemctl --user show "$unit" -p InvocationID --value)
  [[ "$invocation" =~ ^[a-f0-9]{32}$ ]]
  test "$(systemctl --user show "$unit" -p Slice --value)" = "$FLEET_SLICE"
  printf 'Existing recorded client %s InvocationID=%s; no startup permission\n' "$unit" "$invocation"
}

fleet_require_helper() {
  local role=${1:?declared helper role} receipt expected observed unit
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
}

fleet_helper_roles() {
  # The existing performers declare the family; headless endpoints have none.
  [[ "$FLEET_VNC" != 0 ]] || return 0
  local performer
  for performer in "$FLEET_OPERATIONS"/*-helper.sh; do
    test -f "$performer" || return
    performer=${performer##*/}
    printf '%s\n' "${performer%-helper.sh}"
  done
}

fleet_require_helpers() {
  local role
  while IFS= read -r role; do fleet_require_helper "$role"; done \
    < <(fleet_helper_roles)
}


# The scientific writer's predecessor is independent of inherited helper identity.
fleet_require_writer_release() {
  local retirements retirement predecessor_root predecessor_slot predecessor_phase predecessor_unit state
  retirements=$(jq -ce '.writer_handoff | select(type=="array")' <<< "$slot") || return
  while IFS= read -r retirement; do
    predecessor_root=$(jq -er '.program_root' <<< "$retirement") || return
    predecessor_slot=$(jq -er '.slot|ascii_downcase' <<< "$retirement") || return
    test -f "$(jq -er '.terminal_custody_receipt' <<< "$retirement")" || return
    predecessor_phase=$(jq -er '.phase' "$predecessor_root/program.json") || return
    for predecessor_unit in "$predecessor_phase-$predecessor_slot-author.scope" "$predecessor_phase-$predecessor_slot-mcp.scope"; do
      state=$(systemctl --user show "$predecessor_unit" -p LoadState --value) || return
      if [[ "$state" != not-found ]]; then
        test "$state" = loaded || return
        state=$(systemctl --user show "$predecessor_unit" -p ActiveState --value) || return
        [[ "$state" == inactive || "$state" == failed ]] || return
      fi
      printf 'Retired scientific writer %s inactive\n' "$predecessor_unit"
    done
  done < <(jq -c '.[]' <<< "$retirements")
}

# The immutable continuation declaration owns both native ancestry and access
# to its closed predecessors' scientific material. Fresh authors inherit neither.
# Launcher mounts and MCP path policy consume this same request-local projection.
fleet_author_context() {
  local context predecessor predecessor_root predecessor_slot predecessor_member
  local history_roots='[]' read_roots='[]' predecessors output_roots output_root physical_root
  if [[ -n "${FLEET_RECOVERY_OBSERVATION:-}" ]]; then
    fleet_require_closed_controllers >&2 || return
    local original_history="$FLEET_WORKSPACE/output/native-sessions" session_ids
    # The original launcher journal owns the started thread, not a guessed
    # newest rollout. Later recovery children cannot change this ancestry.
    session_ids=$(rg '^\{"type":"thread.started"' "$FLEET_PREDECESSOR_RECORD_RUNTIME/author-events.typescript" |
      jq -sce 'map(.thread_id)|unique') || return
    jq -ce --arg history "$original_history" '
      if length==1 then {argv:["fork",.[0]], history_roots:[$history],read_roots:[]}
      else error("recovery requires one original saved author context") end' <<< "$session_ids"
    return
  fi
  context=$(jq -ce '
    if .fresh_history==true and .native_thread_id==null then {argv:[]}
    elif .fresh_history==false and (.native_thread_id|type)=="string"
      and (.native_thread_id|length)>0 and (.writer_handoff|type)=="array"
      and (.writer_handoff|length)>0 then {argv:["resume",.native_thread_id]}
    else error("inconsistent author context declaration") end' <<< "$slot") || return
  fleet_require_writer_release >&2 || return
  if jq -e '.argv|length>0' <<< "$context" >/dev/null; then
    predecessors=$(jq -c '.writer_handoff[]' <<< "$slot") || return
    while IFS= read -r predecessor; do
      predecessor_root=$(jq -er '.program_root' <<< "$predecessor") || return
      predecessor_slot=$(jq -er '.slot' <<< "$predecessor") || return
      test "$predecessor_root" != "$FLEET_RUN_ROOT" || return
      test "$(jq -er '.funding_root' "$predecessor_root/program.json")" = "$FLEET_ROOT" || return
      predecessor_member=$(jq -ce --arg owner "$predecessor_root" --arg member "$predecessor_slot" '
        [.authors[]|select(.slot==$member and .run_owner_root==$owner)] |
        if length==1 then .[0] else error("missing or ambiguous ancestry declaration") end' \
        "$predecessor_root/program.json") || return
      history_roots=$(jq -ce --arg root "$predecessor_root/$predecessor_slot/author-workspace/output/native-sessions" '. + [$root] | unique' <<< "$history_roots") || return
      output_roots=$(fleet_member_output_roots "$predecessor_member") || return
      while IFS= read -r output_root; do
        physical_root=$(realpath -e "$output_root") || return
        test -d "$physical_root" || return
        [[ "$physical_root" != *:* && "$physical_root" != *$'\n'* ]] || return
        read_roots=$(jq -ce --arg root "$physical_root" '. + [$root] | unique' <<< "$read_roots") || return
      done <<< "$output_roots"
    done <<< "$predecessors"
  fi
  jq -ce --argjson history "$history_roots" --argjson reads "$read_roots" \
    '. + {history_roots:$history,read_roots:$reads}' <<< "$context"
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
  for unit in $(fleet_helper_roles); do
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
