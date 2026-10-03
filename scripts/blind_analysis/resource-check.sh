#!/bin/bash
# NEXT revision of the original admission/ledger owner, not a second gate.
set -euo pipefail
# Publication and one complete admission cannot observe half a transition.
exec 9>"${1:?root}/program.lock"
flock --shared 9
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "$1" "${2:?slot}"
phase=${3:?unique observation}
case "$phase" in ''|*[!a-zA-Z0-9_-]*) exit 64;; esac
mode=${4:-ongoing}
case "$mode" in ongoing|full|replacement|bootstrap|ledger) ;; *) exit 64;; esac
runtime="$FLEET_WORKSPACE/output/runtime"
mkdir -p "$runtime"
if [[ -e "$runtime/first-mcp-started.epoch" ]]; then
  started=$(<"$runtime/first-mcp-started.epoch")
  minutes=$(jq -er '.task_minutes_from_first_mcp_start' "$FLEET_RUN_ROOT/program.json")
  elapsed=$(($(date -u +%s)-started))
  printf 'Deadline elapsed=%s allowed=%s seconds\n' "$elapsed" "$((minutes*60))"
  test "$elapsed" -lt "$((minutes*60))"
fi
receipt="$runtime/resources-$phase"
test ! -e "$receipt.output"
total_cap=$(jq -er '.proposed_resource_envelope.total_output_and_scratch_mib*1048576' <<< "$FLEET_PROGRAM")

# Canonicalize membership once and reject overlaps before counting any bytes.
outputs=()
retained_roots=$(jq -ce '.retained_output_roots | select(type=="array")' <<< "$FLEET_PROGRAM")
while IFS= read -r output; do outputs+=("$(realpath -m "$output")"); done \
  < <(jq -er '.[]' <<< "$retained_roots")
old_count=${#outputs[@]}
funded_slots=$(fleet_funded_slots)
authors=()
while IFS= read -r author; do
  authors+=("$author")
  outputs+=("$(realpath -m "$(fleet_workspace_for "$author")/output")")
done <<< "$funded_slots"
for ((i=0;i<${#outputs[@]};i++)); do
  for ((j=i+1;j<${#outputs[@]};j++)); do
    if [[ "${outputs[i]}" == "${outputs[j]}" || "${outputs[i]}" == "${outputs[j]}/"* || "${outputs[j]}" == "${outputs[i]}/"* ]]; then
      printf 'Overlapping ledger roots: %s / %s\n' "${outputs[i]}" "${outputs[j]}" >&2
      exit 79
    fi
  done
done
old=0
for ((i=0;i<old_count;i++)); do
  test -d "${outputs[i]}"
  bytes=$(du -s -B1 "${outputs[i]}" | cut -f1)
  printf 'Retained %s %s bytes\n' "${outputs[i]}" "$bytes" | tee -a "$receipt.output"
  old=$((old+bytes))
done
total=0
reserved=0
for ((i=old_count;i<${#outputs[@]};i++)); do
  limits=$(fleet_limits_for "${authors[i-old_count]}")
  scratch_cap=$(jq -er '.scratch_per_author_mib*1048576' <<< "$limits")
  output_cap=$(jq -er '.output_per_author_mib*1048576' <<< "$limits")
  reserved=$((reserved+output_cap+scratch_cap))
  output=${outputs[i]}
  bytes=0; scratch=0
  if [[ -d "$output" ]]; then bytes=$(du -s -B1 "$output" | cut -f1); fi
  if [[ -d "$output/runtime/scratch" ]]; then scratch=$(du -s -B1 "$output/runtime/scratch" | cut -f1); fi
  printf 'Current %s total=%s scratch=%s retained=%s limits=%s/%s\n' "$output" "$bytes" "$scratch" "$((bytes-scratch))" "$output_cap" "$scratch_cap" | tee -a "$receipt.output"
  test "$scratch" -le "$scratch_cap"
  test "$((bytes-scratch))" -le "$output_cap"
  total=$((total+bytes))
done
printf 'Programme old=%s current=%s reservedCurrent=%s totalLimit=%s\n' "$old" "$total" "$reserved" "$total_cap" | tee -a "$receipt.output"
test "$((old+reserved))" -le "$total_cap"
test "$((old+total))" -le "$total_cap"
remaining=$((reserved-total))
test "$remaining" -ge 0
home_floor=$(jq -er '.proposed_resource_envelope.minimum_home_ongoing_gib*1073741824' <<< "$FLEET_PROGRAM")
df --output=avail -B1 /home/ts | awk -v floor="$((home_floor+remaining))" 'NR==2 {printf "HomeAvailable %.3f GiB; required %.3f GiB\n",$1/1073741824,floor/1073741824; if($1<floor) exit 78}' | tee "$receipt.disk"
if [[ "$mode" == ledger ]]; then printf 'Ledger-only PASS; not SCI admission\n'; exit; fi

fleet_require_joint_slice
test ! -e "$receipt.json"
set +e
/home/ts/bin/agent-resource-check --assert-headroom > "$receipt.json"
status=$?
set -e
printf '%s\n' "$status" > "$receipt.helper-exit"
printf 'Host helper diagnostic only (status %s):\n' "$status"
cat "$receipt.json"
floor=$(jq -er '.proposed_resource_envelope.desktop_growth_reserve_mib' <<< "$FLEET_PROGRAM")
if [[ "$mode" == full ]]; then floor=$((floor+FLEET_COMBINED_MIB)); fi

# The existing common slice is the aggregate RAM owner. Its current charge
# already includes continuing runs and inherited helpers, so do not sum them again.
if [[ "$mode" == replacement || "$mode" == bootstrap ]]; then
  if [[ "$mode" == bootstrap ]]; then fleet_require_bootstrap_custody; else fleet_require_helpers; fi
  maximum=$(systemctl --user show "$FLEET_SLICE" -p MemoryMax --value)
  current=$(systemctl --user show "$FLEET_SLICE" -p MemoryCurrent --value)
  [[ "$current" =~ ^[0-9]+$ ]]
  test "$current" -le "$maximum"
  growth=$((maximum-current))
  printf 'Joint slice %s charge=%s cap=%s remaining=%s\n' "$FLEET_SLICE" "$current" "$maximum" "$growth" | tee "$receipt.ram-scopes"
  floor=$((floor+(growth+1048575)/1048576))
fi
psi_max=$(jq -er '.proposed_resource_envelope.full_memory_psi_max_percent' <<< "$FLEET_PROGRAM")
awk -v floor="$floor" '/MemAvailable:/ {printf "MemAvailable %.3f GiB; required %d MiB\n",$2/1048576,floor; if($2<floor*1024) exit 76}' /proc/meminfo | tee "$receipt.ram"
awk -v limit="$psi_max" '/^full / {print; for(i=2;i<=NF;i++){split($i,a,"="); if((a[1]=="avg60" || a[1]=="avg300") && a[2]>limit) exit 77}}' /proc/pressure/memory | tee "$receipt.psi"
printf 'Admission PASS\n'
