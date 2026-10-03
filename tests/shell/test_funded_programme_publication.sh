#!/bin/bash
# Controlled original programme declarations, no real scope/client/scientist.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.."; pwd)
scratch=${1:?new persistent controlled validation directory}
test ! -e "$scratch"
mkdir -p "$scratch/funding" "$scratch/next" "$scratch/old-a" "$scratch/old-b"
operations="$repo/scripts/blind_analysis/operations"
owner="$operations/project-program.sh"
jq -n --arg root "$scratch" --arg operations "$operations" '{
  phase:"controlled-funding", authors:([
    {slot:"A",run_owner_root:($root+"/old-a"),display:94,native_port:6012,native_ack_port:7012,viewer_port:6013,viewer_ack_port:7013,vnc_port:5998},
    {slot:"B",run_owner_root:($root+"/old-b"),display:96,native_port:6016,native_ack_port:7016,viewer_port:6017,viewer_ack_port:7017,vnc_port:6007}
  ] | map(. + {cpu:0,input_root:"/controlled/input",writer_handoff:[],
    helper_custody:{program_root:.run_owner_root,slot:.slot,parent_handoff_receipt:($root+"/helper-"+.slot+".json")}})),
  scope_slice:"controlled-unstarted.slice",source_install:"/controlled/old-install",python:"/controlled/python",
  operation_owner_root:$operations,funding_root:($root+"/funding"),task_minutes_from_first_mcp_start:75,
  author_config:"/controlled/original-config",cli:"/controlled/never-invoked-cli",
  model:"controlled-model",model_provider:"controlled-provider",reasoning_effort:"controlled-effort",
  retained_output_roots:[],proposed_resource_envelope:{total_output_and_scratch_mib:10240,
    minimum_home_ongoing_gib:0,aggregate_memory_max_bytes:1048576,
    output_per_author_mib:1,scratch_per_author_mib:1,science_workers_per_author:1,
    per_author_science_mib:7,per_author_cli_mib:3,cpu_quota_per_author_percent:25,
    helper_caps_mib:{x:1,wm:1,vnc:1},desktop_growth_reserve_mib:0,full_memory_psi_max_percent:100}
}' > "$scratch/funding/program.json"
for controlled_owner in old-a old-b; do
  jq --arg owner "$scratch/$controlled_owner" '.authors |= map(select(.run_owner_root==$owner))' "$scratch/funding/program.json" > "$scratch/$controlled_owner/program.json"
done
jq -n --arg root "$scratch" '{
  phase:"controlled-next", predecessor_program_root:($root+"/funding"),
  run_template_root:($root+"/old-a"),
  resource_policy:{total_output_and_scratch_mib:10240,output_per_author_mib:3},members:[],
  retired_members:[{slot:"B",terminal_custody_receipt:($root+"/terminal-b.rst")}],
  additional_authors:[{slot:"INDEPENDENT_C",run_owner_root:($root+"/next"),display:96,
    native_port:6016,native_ack_port:7016,viewer_port:6017,viewer_ack_port:7017,vnc_port:6007,
    cpu:0,input_root:"/controlled/new-input",helper_custody:{program_root:($root+"/next"),slot:"INDEPENDENT_C"}}]
}' > "$scratch/next/successor-declaration.json"
printf '{"target":"/controlled/unimported","source_head":"controlled"}\n' > "$scratch/qualification.json"
expected=$(sha256sum "$scratch/funding/program.json" | cut -d' ' -f1)
bash "$owner" prepare "$scratch/funding" "$scratch/next" "$scratch/qualification.json"
jq -e --arg root "$scratch" '(.funded_members|map(.slot))==["A","INDEPENDENT_C"] and
  (.authors|map(.slot))==["INDEPENDENT_C"] and
  .retained_output_roots==[($root+"/old-b/B/author-workspace/output")]' "$scratch/next/program.json" >/dev/null
printf 'PASS original projection: independent declaration replaces retired membership and retains FULL output once\n'

# These are inert test fixtures, not production parent releases or custody.
printf 'Controlled parent-release fixture; no actual client/native launch.\n' > "$scratch/next/PARENT-RELEASE.rst"
(cd "$scratch/next"; sha256sum program.json successor-declaration.json PARENT-RELEASE.rst > READY-FREEZE.sha256)
refuse() {
  local status
  set +e
  "$@"
  status=$?
  set -e
  test "$status" != 0
  test "$(sha256sum "$scratch/funding/program.json" | cut -d' ' -f1)" = "$expected"
  test ! -e "$scratch/next/publication-before.json"
}
refuse bash "$owner" publish "$scratch/funding" "$scratch/next" "$expected"
refuse env FLEET_PARENT_RELEASED=1 bash "$owner" publish "$scratch/funding" "$scratch/next" stale
refuse env FLEET_PARENT_RELEASED=1 bash "$owner" publish "$scratch/funding" "$scratch/next" "$expected"
printf 'PASS no release, stale current revision, and absent/UNKNOWN terminal custody leave funding unchanged\n'

printf 'Controlled exact terminal/borrower custody fixture.\n' > "$scratch/terminal-b.rst"
FLEET_PARENT_RELEASED=1 bash "$owner" publish "$scratch/funding" "$scratch/next" "$expected"
jq -e 'all(.authors[]; keys==["run_owner_root","slot"]) and
  (has("source_install")|not) and (has("author_config")|not) and
  (.proposed_resource_envelope|has("output_per_author_mib")|not)' "$scratch/funding/program.json" >/dev/null
test "$(sha256sum "$scratch/next/publication-before.json" | cut -d' ' -f1)" = "$expected"
jq -e --arg root "$scratch" '.authors[0].run_owner_root==($root+"/old-a") and (.authors|length)==2' "$scratch/funding/program.json" >/dev/null
printf 'PASS one current programme atomically transitions roster+history; continuing run identity unchanged\n'
set +e
FLEET_PARENT_RELEASED=1 bash "$owner" publish "$scratch/funding" "$scratch/next" "$expected"
status=$?
set -e
test "$status" != 0
jq -e '(.authors|map(.slot))==["A","INDEPENDENT_C"]' "$scratch/funding/program.json" >/dev/null
printf 'PASS original expected revision prohibits a second publication/replay\n'

# Read current funding through the actual member/ledger owners. No host admission,
# helper, scope, import, client or scientist is started by ledger mode.
mkdir -p "$scratch/old-a/A/author-workspace/output" "$scratch/old-b/B/author-workspace/output" "$scratch/next/INDEPENDENT_C/author-workspace/output"
bash "$operations/resource-check.sh" "$scratch/funding" A current_funding01 ledger > "$scratch/ledger01.log" 2>&1
rg -q 'reservedCurrent=6291456 ' "$scratch/ledger01.log"
test "$(rg -c '^Retained ' "$scratch/ledger01.log")" = 1
bash -c 'source "$1" "$2" A; test "$FLEET_INSTALL" = /controlled/old-install; test "$FLEET_OPERATIONS" = "$3"; test "$(fleet_limits_for A | jq -er .output_per_author_mib)" = 1' \
  _ "$operations/slot-env.sh" "$scratch/funding" "$operations"
bash "$operations/launch-author.sh" "$scratch/funding" A --preflight > "$scratch/preflight-a.log"
rg -q 'config=/controlled/original-config.*cli=/controlled/never-invoked-cli' "$scratch/preflight-a.log"
rg -q 'model=controlled-model provider=controlled-provider effort=controlled-effort' "$scratch/preflight-a.log"
printf 'PASS original launcher uses immutable run config/model/CLI with no provider turn\n'
printf 'PASS current reservations sum immutable own caps (2+4MiB), full retired bytes once; continuing source/operations/cap unchanged\n'

cp "$scratch/funding/program.json" "$scratch/funding-before-overlap.json"
jq --arg output "$scratch/old-a/A/author-workspace/output" '.retained_output_roots += [$output]' "$scratch/funding-before-overlap.json" > "$scratch/funding/program.json"
set +e
bash "$operations/resource-check.sh" "$scratch/funding" A overlap01 ledger > "$scratch/overlap01.log" 2>&1
status=$?
set -e
test "$status" = 79
cp "$scratch/funding-before-overlap.json" "$scratch/funding/program.json"
mkdir "$scratch/missing-owner-funding"
jq --arg owner "$scratch/absent-run" '.authors[0].run_owner_root=$owner' "$scratch/funding/program.json" > "$scratch/missing-owner-funding/program.json"
set +e
bash "$operations/slot-env.sh" "$scratch/missing-owner-funding" --project-members > "$scratch/missing-owner01.log" 2>&1
status=$?
set -e
test "$status" != 0
printf 'PASS overlap and missing original run owner rejected without host admission or fabricated identity\n'

# Unknown and ambiguous declarations fail in the original JQ, not a leaf switch.
for negative in unknown ambiguous; do
  mkdir "$scratch/$negative"
  if [[ "$negative" == unknown ]]; then
    jq '.retired_members[0].slot="MISSING"' "$scratch/next/successor-declaration.json" > "$scratch/$negative/successor-declaration.json"
  else
    jq '.additional_authors[0].slot="A"' "$scratch/next/successor-declaration.json" > "$scratch/$negative/successor-declaration.json"
  fi
  # Restore the original reviewed INPUT only in this controlled funding owner.
  cp "$scratch/next/publication-before.json" "$scratch/funding/program.json"
  set +e
  bash "$owner" prepare "$scratch/funding" "$scratch/$negative" "$scratch/qualification.json"
  status=$?
  set -e
  test "$status" != 0
done
cp "$scratch/funding-before-overlap.json" "$scratch/funding/program.json"
printf 'PASS unknown retirement and ambiguous family membership rejected; failed attempts retained\n'

# Retirement-only transition in the SAME owner releases C's entire unused
# future reservation. A's run, operations, clock and source remain untouched.
mkdir "$scratch/retirement"
printf 'Controlled exact terminal C fixture.\n' > "$scratch/terminal-c.rst"
jq --arg root "$scratch" '.phase="controlled-retirement" |
  .members=[] | .additional_authors=[] |
  .retired_members=[{slot:"INDEPENDENT_C",terminal_custody_receipt:($root+"/terminal-c.rst")}]' \
  "$scratch/next/successor-declaration.json" > "$scratch/retirement/successor-declaration.json"
expected=$(sha256sum "$scratch/funding/program.json" | cut -d' ' -f1)
bash "$owner" prepare "$scratch/funding" "$scratch/retirement" "$scratch/qualification.json"
printf 'Controlled release.\n' > "$scratch/retirement/PARENT-RELEASE.rst"
(cd "$scratch/retirement"; sha256sum program.json successor-declaration.json PARENT-RELEASE.rst > READY-FREEZE.sha256)
FLEET_PARENT_RELEASED=1 bash "$owner" publish "$scratch/funding" "$scratch/retirement" "$expected"
bash "$operations/resource-check.sh" "$scratch/funding" A after_retirement02 ledger > "$scratch/ledger02.log" 2>&1
rg -q 'reservedCurrent=2097152 ' "$scratch/ledger02.log"
test "$(rg -c '^Retained ' "$scratch/ledger02.log")" = 2
set +e
bash "$operations/slot-env.sh" "$scratch/funding" INDEPENDENT_C > "$scratch/retired-c.log" 2>&1
status=$?
set -e
test "$status" != 0
printf 'PASS one continuing author sees current retirement without run/permission/clock edits; removed author loses funding\n'

# Actual recorder/guard/slot/client; only external X/systemctl/exec controlled.
printf 'Controlled helper terminal custody, not production authority.\n' > "$scratch/helper-terminal.rst"
jq -n --arg root "$scratch" '{program_root:($root+"/old-a"),slot:"A",
  terminal_custody_receipt:($root+"/helper-terminal.rst"),
  helper_invocations:{x:"11111111111111111111111111111111",
    wm:"11111111111111111111111111111111",vnc:"11111111111111111111111111111111"}}' > "$scratch/helper-A.json"
mkdir -p "$scratch/controlled-install/openhcs/mcp"
touch "$scratch/controlled-install/openhcs/mcp/server.py"
jq --arg install "$scratch/controlled-install" '.source_install=$install' "$scratch/old-a/program.json" > "$scratch/old-a/fixture-complete.json"
mv "$scratch/old-a/fixture-complete.json" "$scratch/old-a/program.json"
printf 'Controlled immutable run release.\n' > "$scratch/old-a/PARENT-RELEASE.rst"
(cd "$scratch/old-a"; sha256sum program.json PARENT-RELEASE.rst > READY-FREEZE.sha256)
FLEET_PARENT_RELEASED=1 bash "$operations/launch-author.sh" "$scratch/funding" A --preflight > "$scratch/preflight-after.log"
export BASH_ENV="$repo/tests/shell/fixtures/funded_run/bash-env.sh"
set +e
FLEET_PARENT_RELEASED=1 bash "$operations/recorded-mcp.sh" "$scratch/funding" A startup01
status=$?
set -e
test "$status" = 42
runtime="$scratch/old-a/A/author-workspace/output/runtime"
rg -q 'CONTROLLED_EXEC cap=7 cpu=25' "$runtime/mcp.stdout"
test -f "$runtime/first-mcp-started.epoch"
test ! -e "$scratch/funding/A"
(cd "$scratch/old-a"; sha256sum --check --quiet READY-FREEZE.sha256)
sha256sum "$runtime"/mcp.* "$runtime/first-mcp-started.epoch" > "$scratch/retained-startup.sha256"
set +e
FLEET_PARENT_RELEASED=1 bash "$operations/recorded-mcp.sh" "$scratch/funding" A forbidden02
status=$?
set -e
test "$status" = 1
test ! -e "$runtime/resources-forbidden02.output"
sha256sum --check --quiet "$scratch/retained-startup.sha256"
printf 'PASS original recorded path: own cap7/CPU25, exact child42, run-local clock/journals, no replay\n'

# Initial publication uses the SAME writer, not a manually copied head/store.
mkdir "$scratch/initial-run"
jq --arg root "$scratch" '.funding_root=($root+"/initial-funding") |
  .authors |= map(.run_owner_root=($root+"/initial-run")) |
  .funded_members=[.authors[]|{slot,run_owner_root}]' "$scratch/old-a/program.json" > "$scratch/initial-run/program.json"
printf 'Controlled initial parent release.\n' > "$scratch/initial-run/PARENT-RELEASE.rst"
(cd "$scratch/initial-run"; sha256sum program.json PARENT-RELEASE.rst > READY-FREEZE.sha256)
FLEET_PARENT_RELEASED=1 bash "$owner" initialize "$scratch/initial-funding" "$scratch/initial-run" absent
jq -e '(.authors|length)==1 and (has("python")|not) and
  (.proposed_resource_envelope|has("per_author_science_mib")|not)' "$scratch/initial-funding/program.json" >/dev/null
before=$(sha256sum "$scratch/initial-funding/program.json")
set +e
FLEET_PARENT_RELEASED=1 bash "$owner" initialize "$scratch/initial-funding" "$scratch/initial-run" absent
status=$?
set -e
test "$status" != 0
test "$before" = "$(sha256sum "$scratch/initial-funding/program.json")"
printf 'PASS initial funding published by same owner once, no permission mirror or replay\n'

mkdir "$scratch/last-retirement"
printf 'Controlled exact terminal A fixture.\n' > "$scratch/terminal-a.rst"
jq --arg root "$scratch" '.phase="controlled-empty-funding" |
  .retired_members=[{slot:"A",terminal_custody_receipt:($root+"/terminal-a.rst")}]' \
  "$scratch/retirement/successor-declaration.json" > "$scratch/last-retirement/successor-declaration.json"
expected=$(sha256sum "$scratch/funding/program.json" | cut -d' ' -f1)
bash "$owner" prepare "$scratch/funding" "$scratch/last-retirement" "$scratch/qualification.json"
printf 'Controlled last-terminal release.\n' > "$scratch/last-retirement/PARENT-RELEASE.rst"
(cd "$scratch/last-retirement"; sha256sum program.json successor-declaration.json PARENT-RELEASE.rst > READY-FREEZE.sha256)
FLEET_PARENT_RELEASED=1 bash "$owner" publish "$scratch/funding" "$scratch/last-retirement" "$expected"
jq -e '(.authors|length)==0 and (.retained_output_roots|length)==3' "$scratch/funding/program.json" >/dev/null
(cd "$scratch/old-a"; sha256sum --check --quiet READY-FREEZE.sha256)
sha256sum --check --quiet "$scratch/retained-startup.sha256"
printf 'PASS last terminal writer releases all future growth; complete output and original run/journals remain\n'
