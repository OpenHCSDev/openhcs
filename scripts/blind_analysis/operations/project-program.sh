#!/bin/bash
# Original programme projector: prepare a run; publish current funding atomically.
set -euo pipefail
operations=$(cd "$(dirname "${BASH_SOURCE[0]}")"; pwd)
mode=${1:?initialize, prepare or publish}
funding=${2:?fixed programme owner root}
run=${3:?immutable prepared run root}
test "$(realpath -m "$funding")" != "$(realpath -m "$run")"
mkdir -p "$funding"
# The same lock is held shared by a complete admission, exclusive by publication.
exec 9>"$funding/program.lock"
flock --exclusive 9
case "$mode" in
  prepare)
    qualification=${4:?authoritative package qualification}
    test ! -e "$run/program.json"
    test ! -e "$run/READY-FREEZE.sha256"
    previous=$(jq -er '.predecessor_program_root' "$run/successor-declaration.json")
    test "$(realpath -m "$previous")" = "$(realpath -m "$funding")"
    # Membership references come from funding; physical declarations come from
    # their immutable run owner through the original slot projection.
    members=$(bash "$operations/slot-env.sh" "$funding" --project-members)
    original=$(jq -ce --argjson members "$members" '.authors=$members' "$funding/program.json")
    template=$(jq -er '.run_template_root' "$run/successor-declaration.json")
    test "$(jq -er '.funding_root' "$template/program.json")" = "$funding"
    jq --slurpfile replacement <(jq --arg proof "$qualification" '.package_qualification=$proof' "$run/successor-declaration.json") \
      --slurpfile funding <(printf '%s\n' "$original") \
      --arg operation_owner_root "$operations" --arg successor_root "$run" \
      --arg source_install "$(jq -er '.target' "$qualification")" \
      --arg source_head "$(jq -er '.source_head' "$qualification")" \
      -f "$operations/successor-program.jq" "$template/program.json" > "$run/program.json"
    exit
    ;;
  initialize|publish)
    expected=${4:?reviewed current programme SHA256}
    test "${FLEET_PARENT_RELEASED:-0}" = 1
    test -f "$run/PARENT-RELEASE.rst"
    test -f "$run/READY-FREEZE.sha256"
    (cd "$run"; sha256sum --check --quiet READY-FREEZE.sha256)
    test "$(jq -er '.funding_root' "$run/program.json")" = "$funding"
    if [[ "$mode" == initialize ]]; then
      test "$expected" = absent
      test ! -e "$funding/program.json"
    else
      observed=$(sha256sum "$funding/program.json" | cut -d' ' -f1)
      test "$observed" = "$expected"
    # A proposal must account for EVERY removed run, never infer closure from PIDs.
    jq -e --arg funding "$funding" --slurpfile next "$run/program.json" --slurpfile declaration "$run/successor-declaration.json" '
      all(.authors[]; . as $old |
        any($next[0].funded_members[]; .slot==$old.slot and .run_owner_root==$old.run_owner_root)
        or any($declaration[0].members[]; .predecessor_slot==$old.slot)
        or any($declaration[0].retired_members[]; .slot==$old.slot))
      and all($next[0].funded_members[]; .run_owner_root!=$funding)
    ' "$funding/program.json" >/dev/null
      receipts=$(jq -ce '[.members[].terminal_custody_receipt, .retired_members[].terminal_custody_receipt] |
        if all(.[]; type=="string" and length>0) then . else error("missing terminal custody") end' "$run/successor-declaration.json")
      while IFS= read -r receipt; do test -f "$receipt"; done < <(jq -r '.[]' <<< "$receipts")
    # Parent's exact terminal/borrower evidence and release are the authority.
    # No scope disappearance, failed client or UNKNOWN automatically retires a run.
    test ! -e "$run/publication-before.json"
    fi
    members=$(jq -ce '.funded_members | select(type=="array") |
      if (map(.slot)|unique|length)!=length then error("ambiguous funded member") else . end' "$run/program.json")
    # Resolve every reference through its original declaration before admission
    # can see it. No missing/foreign permissions enter the funded programme.
    while IFS= read -r reference; do
      owner=$(jq -er '.run_owner_root' <<< "$reference")
      member=$(jq -er '.slot' <<< "$reference")
      test "$owner" != "$funding"
      test "$(jq -er '.funding_root' "$owner/program.json")" = "$funding"
      jq -e --arg member "$member" --arg owner "$owner" '[.authors[] |
        select(.slot==$member and .run_owner_root==$owner)] | length==1' "$owner/program.json" >/dev/null
    done < <(jq -c '.[]' <<< "$members")
    if [[ "$mode" == publish ]]; then cp "$funding/program.json" "$run/publication-before.json"; fi
    pending=$(mktemp "$funding/.program.XXXXXXXX")
    trap 'test ! -e "$pending" || unlink "$pending"' EXIT
    # Never mirror physical run declarations into the mutable membership owner.
    jq '{scope_slice, retained_output_roots, authors:.funded_members,
      proposed_resource_envelope:(.proposed_resource_envelope | {
        aggregate_memory_max_bytes, total_output_and_scratch_mib,
        minimum_home_ongoing_gib, desktop_growth_reserve_mib, full_memory_psi_max_percent})
    }' "$run/program.json" > "$pending"
    mv "$pending" "$funding/program.json"
    sha256sum "$funding/program.json"
    ;;
  *) exit 64 ;;
esac
