#!/bin/bash
# Controlled original programme declarations, no real scope/client/scientist.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.."; pwd)
scratch=${1:?new persistent controlled validation directory}
test ! -e "$scratch"
mkdir -p "$scratch/funding" "$scratch/next" "$scratch/old-a" "$scratch/old-b"
owner="$repo/scripts/blind_analysis/project-program.sh"
jq -n --arg root "$scratch" '{
  phase:"controlled-funding", authors:([
    {slot:"A",run_owner_root:($root+"/old-a"),display:94,native_port:6012,native_ack_port:7012,viewer_port:6013,viewer_ack_port:7013,vnc_port:5998},
    {slot:"B",run_owner_root:($root+"/old-b"),display:96,native_port:6016,native_ack_port:7016,viewer_port:6017,viewer_ack_port:7017,vnc_port:6007}
  ] | map(. + {cpu:0,input_root:"/controlled/input",helper_custody:{program_root:.run_owner_root,slot:.slot}})),
  scope_slice:"controlled-unstarted.slice",source_install:"/controlled/old-install",python:"/controlled/python",
  operation_owner_root:"/controlled/old-operations",
  retained_output_roots:[],proposed_resource_envelope:{total_output_and_scratch_mib:10240,
    minimum_home_ongoing_gib:0,aggregate_memory_max_bytes:1048576,
    output_per_author_mib:1,scratch_per_author_mib:1}
}' > "$scratch/funding/program.json"
for controlled_owner in old-a old-b; do
  jq --arg owner "$scratch/$controlled_owner" '.authors |= map(select(.run_owner_root==$owner))' "$scratch/funding/program.json" > "$scratch/$controlled_owner/program.json"
done
jq -n --arg root "$scratch" '{
  phase:"controlled-next", predecessor_program_root:($root+"/funding"),
  resource_policy:{total_output_and_scratch_mib:10240,output_per_author_mib:3},members:[],
  retired_members:[{slot:"B",terminal_custody_receipt:($root+"/terminal-b.rst")}],
  additional_authors:[{slot:"INDEPENDENT_C",run_owner_root:($root+"/next"),display:96,
    native_port:6016,native_ack_port:7016,viewer_port:6017,viewer_ack_port:7017,vnc_port:6007,
    cpu:0,input_root:"/controlled/new-input",helper_custody:{program_root:($root+"/next"),slot:"INDEPENDENT_C"}}]
}' > "$scratch/next/successor-declaration.json"
printf '{"target":"/controlled/unimported","source_head":"controlled"}\n' > "$scratch/qualification.json"
expected=$(sha256sum "$scratch/funding/program.json" | cut -d' ' -f1)
bash "$owner" prepare "$scratch/funding" "$scratch/next" "$scratch/qualification.json"
jq -e --arg root "$scratch" '(.authors|map(.slot))==["A","INDEPENDENT_C"] and
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
jq -e 'all(.authors[]; keys==["run_owner_root","slot"])' "$scratch/funding/program.json" >/dev/null
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
bash "$repo/scripts/blind_analysis/resource-check.sh" "$scratch/funding" A current_funding01 ledger > "$scratch/ledger01.log" 2>&1
rg -q 'reservedCurrent=6291456 ' "$scratch/ledger01.log"
test "$(rg -c '^Retained ' "$scratch/ledger01.log")" = 1
bash -c 'source "$1" "$2" A; test "$FLEET_INSTALL" = /controlled/old-install; test "$FLEET_OPERATIONS" = /controlled/old-operations; test "$(fleet_limits_for A | jq -er .output_per_author_mib)" = 1' \
  _ "$repo/scripts/blind_analysis/slot-env.sh" "$scratch/funding"
printf 'PASS current reservations sum immutable own caps (2+4MiB), full retired bytes once; continuing source/operations/cap unchanged\n'

mkdir "$scratch/overlap-funding"
jq --arg output "$scratch/old-a/A/author-workspace/output" '.retained_output_roots += [$output]' "$scratch/funding/program.json" > "$scratch/overlap-funding/program.json"
set +e
bash "$repo/scripts/blind_analysis/resource-check.sh" "$scratch/overlap-funding" A overlap01 ledger > "$scratch/overlap01.log" 2>&1
status=$?
set -e
test "$status" = 79
mkdir "$scratch/missing-owner-funding"
jq --arg owner "$scratch/absent-run" '.authors[0].run_owner_root=$owner' "$scratch/funding/program.json" > "$scratch/missing-owner-funding/program.json"
set +e
bash "$repo/scripts/blind_analysis/slot-env.sh" "$scratch/missing-owner-funding" --project-members > "$scratch/missing-owner01.log" 2>&1
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
  # Restore the reviewed initial INPUT in an independent controlled programme.
  mkdir "$scratch/$negative-funding"
  cp "$scratch/next/publication-before.json" "$scratch/$negative-funding/program.json"
  jq --arg root "$scratch/$negative-funding" '.predecessor_program_root=$root' "$scratch/$negative/successor-declaration.json" > "$scratch/$negative/changed.json"
  mv "$scratch/$negative/changed.json" "$scratch/$negative/successor-declaration.json"
  set +e
  bash "$owner" prepare "$scratch/$negative-funding" "$scratch/$negative" "$scratch/qualification.json"
  status=$?
  set -e
  test "$status" != 0
done
printf 'PASS unknown retirement and ambiguous family membership rejected; failed attempts retained\n'
