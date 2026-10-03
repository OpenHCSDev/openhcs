#!/bin/bash
# Original programme projector: prepare a run; publish current funding atomically.
set -euo pipefail
operations=$(cd "$(dirname "${BASH_SOURCE[0]}")"; pwd)
mode=${1:?prepare or publish}
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
    jq --slurpfile replacement <(jq --arg proof "$qualification" '.package_qualification=$proof' "$run/successor-declaration.json") \
      --arg operation_owner_root "$operations" --arg successor_root "$run" \
      --arg source_install "$(jq -er '.target' "$qualification")" \
      --arg source_head "$(jq -er '.source_head' "$qualification")" \
      -f "$operations/successor-program.jq" "$funding/program.json" > "$run/program.json"
    ;;
  publish)
    expected=${4:?reviewed current programme SHA256}
    test "${FLEET_PARENT_RELEASED:-0}" = 1
    test -f "$run/PARENT-RELEASE.rst"
    test -f "$run/READY-FREEZE.sha256"
    (cd "$run"; sha256sum --check --quiet READY-FREEZE.sha256)
    observed=$(sha256sum "$funding/program.json" | cut -d' ' -f1)
    test "$observed" = "$expected"
    # A proposal must account for EVERY removed run, never infer closure from PIDs.
    jq -e --arg funding "$funding" --slurpfile next "$run/program.json" --slurpfile declaration "$run/successor-declaration.json" '
      all(.authors[]; . as $old |
        any($next[0].authors[]; .slot==$old.slot and .run_owner_root==$old.run_owner_root)
        or any($declaration[0].members[]; .predecessor_slot==$old.slot)
        or any($declaration[0].retired_members[]; .slot==$old.slot))
      and all($next[0].authors[]; .run_owner_root!=$funding)
    ' "$funding/program.json" >/dev/null
    while IFS= read -r receipt; do test -f "$receipt"; done < <(
      jq -er '.members[].terminal_custody_receipt, .retired_members[].terminal_custody_receipt' "$run/successor-declaration.json")
    # Parent's exact terminal/borrower evidence and release are the authority.
    # No scope disappearance, failed client or UNKNOWN automatically retires a run.
    test ! -e "$run/publication-before.json"
    cp "$funding/program.json" "$run/publication-before.json"
    pending=$(mktemp "$funding/.program.XXXXXXXX")
    trap 'test ! -e "$pending" || unlink "$pending"' EXIT
    cp "$run/program.json" "$pending"
    mv "$pending" "$funding/program.json"
    sha256sum "$funding/program.json"
    ;;
  *) exit 64 ;;
esac
