#!/bin/bash
# Controlled original programme declarations, no real scope/client/scientist.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.."; pwd)
scratch=${1:?new persistent controlled validation directory}
test ! -e "$scratch"
mkdir -p "$scratch/funding" "$scratch/next" "$scratch/old-a" "$scratch/old-b"
owner="$repo/scripts/blind_analysis/project-program.sh"
jq -n --arg root "$scratch" '{
  phase:"controlled-funding", authors:[
    {slot:"A",run_owner_root:($root+"/old-a"),display:94,native_port:6012,native_ack_port:7012,viewer_port:6013,viewer_ack_port:7013,vnc_port:5998},
    {slot:"B",run_owner_root:($root+"/old-b"),display:96,native_port:6016,native_ack_port:7016,viewer_port:6017,viewer_ack_port:7017,vnc_port:6007}
  ], retained_output_roots:[],proposed_resource_envelope:{total_output_and_scratch_mib:10240}
}' > "$scratch/funding/program.json"
jq -n --arg root "$scratch" '{
  phase:"controlled-next", predecessor_program_root:($root+"/funding"),
  resource_policy:{total_output_and_scratch_mib:10240},members:[],
  retired_members:[{slot:"B",terminal_custody_receipt:($root+"/terminal-b.rst")}],
  additional_authors:[{slot:"INDEPENDENT_C",run_owner_root:($root+"/next"),display:96,
    native_port:6016,native_ack_port:7016,viewer_port:6017,viewer_ack_port:7017,vnc_port:6007}]
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
cmp "$scratch/funding/program.json" "$scratch/next/program.json"
test "$(sha256sum "$scratch/next/publication-before.json" | cut -d' ' -f1)" = "$expected"
jq -e --arg root "$scratch" '.authors[0].run_owner_root==($root+"/old-a") and (.authors|length)==2' "$scratch/funding/program.json" >/dev/null
printf 'PASS one current programme atomically transitions roster+history; continuing run identity unchanged\n'
set +e
FLEET_PARENT_RELEASED=1 bash "$owner" publish "$scratch/funding" "$scratch/next" "$expected"
status=$?
set -e
test "$status" != 0
cmp "$scratch/funding/program.json" "$scratch/next/program.json"
printf 'PASS original expected revision prohibits a second publication/replay\n'

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
