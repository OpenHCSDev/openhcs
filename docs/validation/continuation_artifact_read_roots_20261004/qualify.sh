#!/bin/bash
# Bounded source/namespace acceptance only: no FUND publication or paid turn.
set -euo pipefail
checkout=$(git rev-parse --show-toplevel)
operations="$checkout/scripts/blind_analysis/operations"
programme=/home/ts/wt/openhcs-issue-batch-20260929
funding="$programme/next-three-taskonly539543-20261003/FUND"
source "$operations/slot-env.sh" "$funding" R0010_FRESH636_96
context=$(fleet_author_context)
jq -e '.argv==[] and .read_roots==[] and .history_roots==[]' <<< "$context" >/dev/null
printf 'PASS fresh author: no predecessor history/artifact access\n'

# These are inputs to the original pure projection, not a generated programme
# or another funded member. All predecessor/custody files are the actual originals.
original_slot=$slot
parent="$programme/next-h002-h004-p001-hdd-20261004"
slot=$(jq -ce --arg parent "$parent" '
  .fresh_history=false |
  .native_thread_id="01a107ad-3b9a-7383-83fe-003aaea06fa1" |
  .writer_handoff=[{program_root:$parent,slot:"P001_NINE_HDD_95",
    terminal_custody_receipt:($parent+"/OWNER-P00195-CAPACITY-TERMINAL.rst")}]' <<< "$original_slot")
continuation_slot=$slot
context=$(fleet_author_context)
jq -e '.argv==["resume","01a107ad-3b9a-7383-83fe-003aaea06fa1"] and
  (.history_roots|length)==1 and (.read_roots|length)==2' <<< "$context" >/dev/null
printf 'PASS real closed P001 ancestry: original HOME and HDD roots\n'

slot=$(jq -c '.native_thread_id=null' <<< "$continuation_slot")
if fleet_author_context; then printf 'invalid context admitted\n' >&2; exit 1; fi
printf 'PASS malformed context refused\n'
slot=$(jq -c '.writer_handoff[0].terminal_custody_receipt="/nonexistent-ancestry-proof"' <<< "$continuation_slot")
if fleet_author_context; then printf 'missing custody admitted\n' >&2; exit 1; fi
printf 'PASS absent terminal custody refused\n'
slot=$(jq -c '.writer_handoff[0].slot="ABSENT_PREDECESSOR"' <<< "$continuation_slot")
if fleet_author_context; then printf 'missing member admitted\n' >&2; exit 1; fi
printf 'PASS missing original declaration refused\n'
slot=$(jq -c --arg owner "$FLEET_RUN_ROOT" '.writer_handoff[0].program_root=$owner |
  .writer_handoff[0].slot="R0010_FRESH636_96"' <<< "$continuation_slot")
if fleet_author_context; then printf 'live predecessor admitted\n' >&2; exit 1; fi
printf 'PASS actual live predecessor refused (no fake systemctl outcome)\n'
slot=$(jq -c --arg owner "$programme/blind-sol3-phase03-preparation-20261002" '
  .writer_handoff[0].program_root=$owner | .writer_handoff[0].slot="H001"' <<< "$continuation_slot")
if fleet_author_context; then printf 'foreign programme admitted\n' >&2; exit 1; fi
printf 'PASS original foreign/nonfunded programme refused\n'

slot=$continuation_slot
context=$(fleet_author_context)
mounts=()
while IFS= read -r root; do mounts+=(--ro-bind "$root" "$root"); done \
  < <(jq -r '.read_roots[]' <<< "$context")
reads=$(jq -r '.read_roots|join(":")' <<< "$context")
image="/run/media/ts/hdd/openhcs-science/next-h002-h004-p001-hdd-20261004/P001_NINE_HDD_95/stitch02/P001_openhcs/images/A01_s001_w2_z001_t001.tif"
original_hash=$(sha256sum "$image")
qualification=$(<"$programme/engineering-pre-first-routing-20261004/receiving03/READY.json")
target=$(jq -er '.target' <<< "$qualification")
python=$(jq -er '.python' <<< "$qualification")
PYTHONPATH="$target" PYTHONDONTWRITEBYTECODE=1 \
OPENHCS_AGENT_READ_ROOTS="$reads" OPENHCS_AGENT_WRITE_ROOTS="$checkout/docs/validation/continuation_artifact_read_roots_20261004" \
  bwrap --bind / / --proc /proc --dev-bind /dev /dev "${mounts[@]}" \
  "$python" -B "$checkout/docs/validation/continuation_artifact_read_roots_20261004/path_policy.py" "$image" "$parent"
test "$(sha256sum "$image")" = "$original_hash"
printf 'PASS original saved mosaic SHA unchanged after ordinary installed policy/OS check\n'

bash "$operations/launch-author.sh" "$funding" H002_CAPACITY_DEV94 --preflight
printf 'PASS actual production launcher preflight: retained child + readonly ancestor mounts\n'
