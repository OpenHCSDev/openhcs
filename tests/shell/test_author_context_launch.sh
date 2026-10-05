#!/bin/bash
# Exercise the original launcher preflight only: no provider/scope/client start.
set -euo pipefail
scratch=${1:?new persistent controlled fixture directory}
operations=${2:?exact original operations source artifact}
test ! -e "$scratch"
mkdir -p "$scratch/fund" "$scratch/run" "$scratch/closed/OLD/author-workspace/output/native-sessions/2026/10/03"
printf 'Inert controlled fixture, never consumed by native Codex.\n' > "$scratch/closed/OLD/author-workspace/output/native-sessions/2026/10/03/rollout-controlled.jsonl"
jq -n --arg root "$scratch" --arg operations "$operations" '{
  phase:"controlled-context", funding_root:($root+"/fund"),
  authors:[{slot:"A",run_owner_root:($root+"/run"),display:96,cpu:1,
    input_root:"/controlled/input",native_port:6016,native_ack_port:7016,
    viewer_port:6017,viewer_ack_port:7017,vnc_port:6007,
    fresh_history:true,native_thread_id:null,
    writer_handoff:[{program_root:($root+"/closed"),slot:"OLD"}],
    helper_custody:{program_root:($root+"/run"),slot:"A"}}],
  scope_slice:"controlled-unstarted.slice", source_install:"/controlled/never-imported",
  python:"/controlled/python",operation_owner_root:$operations,
  author_config:"/controlled/config",cli:"/controlled/never-invoked-cli",
  model:"configured-unchanged",model_provider:"configured-unchanged",
  reasoning_effort:"configured-unchanged",proposed_resource_envelope:{
    aggregate_memory_max_bytes:1048576,science_workers_per_author:1}
}' > "$scratch/run/program.json"
jq '{authors:[.authors[]|{slot,run_owner_root}],scope_slice,proposed_resource_envelope}' \
  "$scratch/run/program.json" > "$scratch/fund/program.json"
invoke() { bash "$operations/launch-author.sh" "$scratch/fund" A --preflight; }
invoke > "$scratch/fresh.log"
rg -F 'history_args=[]' "$scratch/fresh.log"
original=$(sha256sum "$scratch/fund/program.json" | cut -d' ' -f1)
# The immutable run is not current funding. Failure must survive both a
# command substitution and a caller conditional (which disable errexit).
set +e
bash "$operations/launch-author.sh" "$scratch/run" A --preflight > "$scratch/wrong-root.stdout" 2> "$scratch/wrong-root.stderr"
status=$?
set -e
test "$status" = 64
test ! -s "$scratch/wrong-root.stdout"
rg -F 'Canonical funding root required' "$scratch/wrong-root.stderr"
bash -c '
  source "$1/slot-env.sh" "$2/fund" A
  FLEET_ROOT="$2/run"
  for consumer in fleet_member fleet_limits_for fleet_workspace_for fleet_unit_for fleet_helper_unit_for; do
    if result=$("$consumer" A); then exit 91; else status=$?; fi
    test "$status" = 64
    test -z "$result"
  done
' _ "$operations" "$scratch" > "$scratch/consumer-rejection.stdout" 2> "$scratch/consumer-rejection.stderr"
test ! -s "$scratch/consumer-rejection.stdout"
set +e
bash "$operations/slot-env.sh" "$scratch/run" --project-members > "$scratch/wrong-projection.stdout" 2> "$scratch/wrong-projection.stderr"
status=$?
set -e
test "$status" = 64
test ! -s "$scratch/wrong-projection.stdout"
printf 'PASS canonical-root owner rejects run snapshots through launcher, projection and five conditional consumers\n'
set_context() {
  jq --argjson fresh "$1" --argjson id "$2" \
    '.authors[0].fresh_history=$fresh | .authors[0].native_thread_id=$id' \
    "$scratch/run/program.json" > "$scratch/run/pending.json"
  mv "$scratch/run/pending.json" "$scratch/run/program.json"
}
set_context false '"01a10338-3c5f-7bf0-8090-02663cdea84b"'
invoke > "$scratch/resume.log"
rg -F 'history_args=["resume","01a10338-3c5f-7bf0-8090-02663cdea84b"]' "$scratch/resume.log"
rg -F -- '--ro-bind' "$scratch/resume.log"
rg -F '/home/ts/.codex/sessions/2026/10/03/rollout-controlled.jsonl' "$scratch/resume.log"
reject() {
  local label=$1 status
  shift
  set_context "$@"
  set +e
  invoke > "$scratch/$label.stdout" 2> "$scratch/$label.stderr"
  status=$?
  set -e
  test "$status" != 0
  test ! -s "$scratch/$label.stdout"
  rg -F 'inconsistent author context declaration' "$scratch/$label.stderr"
}
reject fresh_with_id true '"unexpected"'
reject resume_without_id false null
reject resume_empty_id false '""'
reject resume_numeric_id false 1
reject unknown_mode '"fresh"' null
reject missing_mode null null
test "$(sha256sum "$scratch/fund/program.json" | cut -d' ' -f1)" = "$original"
test ! -d "$scratch/run/A/author-workspace/output"
printf 'PASS original launcher: fresh, retained, six invalid states; no provider, scope, client, journals or funding mutation\n'
