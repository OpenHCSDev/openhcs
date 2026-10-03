#!/bin/bash
set -euo pipefail
root=${1:?root}
observation=${3:?observation}
test "${4:?mode}" = replacement
test ! -e "$root/$observation.receipt"
printf 'admission %s\n' "$observation" >> "$root/calls"
status=$(<"$root/resource-status")
printf '%s\n' "$status" > "$root/$observation.receipt"
exit "$status"
