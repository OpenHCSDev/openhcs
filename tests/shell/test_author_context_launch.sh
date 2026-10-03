#!/bin/bash
# Exercise the original launcher preflight only: no provider/scope/client start.
set -euo pipefail
scratch=${1:?new persistent controlled fixture directory}
operations=${2:?exact original operations source artifact}
test ! -e "$scratch"
mkdir -p "$scratch/fund" "$scratch/run"
jq -n --arg root "$scratch" --arg operations "$operations" '{
  phase:"controlled-context", funding_root:($root+"/fund"),
  authors:[{slot:"A",run_owner_root:($root+"/run"),display:96,cpu:1,
    input_root:"/controlled/input",native_port:6016,native_ack_port:7016,
    viewer_port:6017,viewer_ack_port:7017,vnc_port:6007,
    fresh_history:true,native_thread_id:null,
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
set_context() {
  jq --argjson fresh "$1" --argjson id "$2" \
    '.authors[0].fresh_history=$fresh | .authors[0].native_thread_id=$id' \
    "$scratch/run/program.json" > "$scratch/run/pending.json"
  mv "$scratch/run/pending.json" "$scratch/run/program.json"
}
set_context false '"01a10338-3c5f-7bf0-8090-02663cdea84b"'
invoke > "$scratch/resume.log"
rg -F 'history_args=["resume","01a10338-3c5f-7bf0-8090-02663cdea84b"]' "$scratch/resume.log"
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
